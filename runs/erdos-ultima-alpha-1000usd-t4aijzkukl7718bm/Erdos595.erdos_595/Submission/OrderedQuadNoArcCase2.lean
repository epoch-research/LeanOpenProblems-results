import Submission.OrderedQuadRight

/-!
A kernel-checked finite order-constraint certificate excluding arc(K4).
The generated proof uses only equality, transitivity, and irreflexivity.
It does not establish non-coverability of the resulting right adjoint.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.unusedVariables false
open SimpleGraph Set
namespace Erdos595OrderedQuadRight
open Erdos595ArcAdjoint
variable {A : Type*} [LinearOrder A]

theorem no_diagram_2 (v : Fin 12 → Quad A)
    (c0 : Tri (v 4) (v 0) (v 6))
    (c1 : TriOptions (v 0) (v 5) (v 9))
    (c2 : TriOptions (v 1) (v 3) (v 7))
    (c3 : TriOptions (v 1) (v 8) (v 9))
    (c4 : TriOptions (v 2) (v 3) (v 10))
    (c5 : TriOptions (v 2) (v 6) (v 11))
    (c6 : TriOptions (v 4) (v 8) (v 10))
    (c7 : TriOptions (v 5) (v 7) (v 11))
    (c8 : Adj (v 0) (v 3))
    (c9 : Adj (v 1) (v 6))
    (c10 : Adj (v 2) (v 9))
    (c11 : Adj (v 4) (v 7))
    (c12 : Adj (v 5) (v 10))
    (c13 : Adj (v 8) (v 11))
    : False := by
  rcases c0 with ⟨h0_0,h0_1,h0_2,h0_3,h0_4,h0_5,h0_6,h0_7,h0_8,h0_9,h0_10⟩
  rcases c1 with c1 | c1 | c1 | c1 | c1 | c1
  · rcases c1 with ⟨h1_0,h1_1,h1_2,h1_3,h1_4,h1_5,h1_6,h1_7,h1_8,h1_9,h1_10⟩
    rcases c2 with c2 | c2 | c2 | c2 | c2 | c2
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 1 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_10 (le_of_eq h3_3)) (le_of_eq h1_3.symm)) (le_of_eq h0_2.symm)) (le_of_eq h6_2)) (le_of_eq h3_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3)) (le_of_eq h3_2.symm)) h2_10) (le_of_eq h3_3)) (le_of_eq h1_3.symm)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h8_0)) (le_of_eq h2_1.symm)) (le_of_eq h3_5)) (le_of_eq h1_5.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 1 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h2_10 (le_of_eq h3_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_3.symm)) (le_of_eq h8_1)) (le_of_eq h2_2.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h8_0.symm)) h2_8) (le_of_eq h3_5)) (le_of_eq h1_5.symm)) h1_8)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 5 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h1_6 (le_of_eq h8_0)) h2_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h8_0.symm)) h2_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h8_1.symm)) h2_8) (le_of_eq h3_5)) (le_of_eq h1_5.symm)) h1_8)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_5.symm)) h6_8)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_7) (le_of_eq h1_0.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_7) h3_8) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) h3_8) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 1 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_10 (le_of_eq h3_3)) (le_of_eq h1_3.symm)) (le_of_eq h0_2.symm)) (le_of_eq h6_2)) (le_of_eq h3_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3)) (le_of_eq h3_2.symm)) h2_10) (le_of_eq h3_3)) (le_of_eq h1_3.symm)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 5 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_6 h8_3) (le_of_eq h2_0.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 5 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_6 (le_of_eq h8_0)) (le_of_eq h2_0.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h8_4) (le_of_eq h2_0.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 5 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_6 h8_2) (le_of_eq h2_0.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_9) h8_4) (le_of_eq h2_0.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h8_3) (le_of_eq h2_0.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_5.symm)) h6_8)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_7) (le_of_eq h1_0.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_7) h3_8) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) h3_8) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 3 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_9 (le_of_eq h2_2)) (le_of_eq h3_3)) (le_of_eq h1_3.symm)) (le_of_eq h0_2.symm)) (le_of_eq h6_2)) (le_of_eq h3_2.symm)) (le_of_eq h2_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3)) (le_of_eq h3_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_3.symm)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_1)) (le_of_eq h3_2)) (le_of_eq h2_2.symm)) (le_of_eq h8_0.symm))
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_1)) (le_of_eq h2_1.symm)) (le_of_eq h8_0.symm))
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h8_1.symm)) (le_of_eq h2_2)) (le_of_eq h3_2.symm)) (le_of_eq h6_1.symm))
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_1)) (le_of_eq h3_2)) (le_of_eq h2_2.symm)) (le_of_eq h8_1.symm))
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h1_8 (le_of_eq h8_0.symm)) h2_7) (le_of_eq h3_5)) (le_of_eq h1_5.symm))
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 3 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_9 (le_of_eq h2_2)) (le_of_eq h3_2.symm)) (le_of_eq h6_1.symm)) (le_of_eq h0_1)) (le_of_eq h8_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3)) (le_of_eq h3_3)) (le_of_eq h1_3.symm)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_0)) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_0)) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_0)) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_0)) (le_of_eq h1_0.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_5.symm)) h6_8)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_7) (le_of_eq h1_0.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_7) h3_8) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) h3_8) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 7 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_9 (le_of_eq h2_2)) (le_of_eq h3_3)) (le_of_eq h1_3.symm)) (le_of_eq h0_2.symm)) (le_of_eq h6_2)) (le_of_eq h3_2.symm)) (le_of_eq h2_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3)) (le_of_eq h3_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_3.symm)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          rcases c9 with c9 | c9 | c9 | c9 | c9 | c9
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 4 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h0_3)) (le_of_eq h9_1.symm)) (le_of_eq h3_1.symm)) h6_8)
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h0_0)) (le_of_eq h9_0.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_1)) (le_of_eq h3_2)) (le_of_eq h9_1.symm)) (le_of_eq h0_5.symm))
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 5 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_6 (le_of_eq h0_4)) (le_of_eq h9_0.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h0_3)) (le_of_eq h9_1)) (le_of_eq h3_2.symm)) (le_of_eq h6_1.symm))
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h0_3)) h9_6) (le_of_eq h3_2.symm)) (le_of_eq h6_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3)) (le_of_eq h3_3)) (le_of_eq h1_3.symm)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_0)) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_0)) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_0)) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_0)) (le_of_eq h1_0.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_5.symm)) h6_8)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_7) (le_of_eq h1_0.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_7) h3_8) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) h3_8) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 7 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h2_8 h2_9) h2_10) (le_of_eq h2_3)) (le_of_eq h3_3)) (le_of_eq h1_3.symm)) (le_of_eq h0_2.symm)) (le_of_eq h6_2)) (le_of_eq h3_2.symm)) (le_of_eq h2_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3)) (le_of_eq h3_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_3.symm)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h1_5)) (le_of_eq h3_5.symm)) (le_of_eq h2_0.symm)) h8_2)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h1_5)) (le_of_eq h3_5.symm)) (le_of_eq h2_0.symm)) h8_2)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 3 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h2_10 (le_of_eq h2_3)) (le_of_eq h3_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_3.symm)) (le_of_eq h8_1.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h1_5)) (le_of_eq h3_5.symm)) (le_of_eq h2_0.symm)) (le_of_eq h8_0.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h8_0.symm)) (le_of_eq h2_0)) (le_of_eq h3_5)) (le_of_eq h1_5.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h1_5)) (le_of_eq h3_5.symm)) (le_of_eq h2_0.symm)) (le_of_eq h8_0))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_5.symm)) h6_8)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_7) (le_of_eq h1_0.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_7) h3_8) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) h3_8) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 3 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h2_8 h2_9) h2_10) (le_of_eq h2_3)) (le_of_eq h3_3)) (le_of_eq h1_3.symm)) (le_of_eq h0_2.symm)) (le_of_eq h6_2)) (le_of_eq h3_2.symm)) (le_of_eq h2_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3)) (le_of_eq h3_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_3.symm)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) (le_of_eq h1_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c11 with c11 | c11 | c11 | c11 | c11 | c11
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 8 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h3_10 (le_of_eq h3_3)) (le_of_eq h1_3.symm)) (le_of_eq h0_2.symm)) (le_of_eq h11_1)) (le_of_eq h2_3)) (le_of_eq h3_2.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h11_1)) (le_of_eq h2_3)) (le_of_eq h3_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_3.symm)) (le_of_eq h0_2.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_10 (le_of_eq h11_1.symm)) h2_10) (le_of_eq h2_3)) (le_of_eq h3_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_3.symm)) (le_of_eq h0_2.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_10 h11_6) (le_of_eq h2_3)) (le_of_eq h3_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_3.symm)) (le_of_eq h0_2.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h11_0.symm)) (le_of_eq h2_0)) (le_of_eq h3_5)) (le_of_eq h1_5.symm)) h1_8)
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 7 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h2_9 h2_10) (le_of_eq h2_3)) (le_of_eq h3_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_3.symm)) (le_of_eq h0_2.symm)) (le_of_eq h11_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_5.symm)) h6_8)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_7) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_7) (le_of_eq h1_0.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_7) h3_8) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) h3_8) (le_of_eq h1_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) (le_of_eq h1_4.symm)) h1_6)
  · rcases c1 with ⟨h1_0,h1_1,h1_2,h1_3,h1_4,h1_5,h1_6,h1_7,h1_8,h1_9,h1_10⟩
    rcases c2 with c2 | c2 | c2 | c2 | c2 | c2
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h6_2)) (le_of_eq h3_2.symm)) h2_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_1)) (le_of_eq h3_5.symm)) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_1)) (le_of_eq h3_5.symm)) h1_8)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          rcases c4 with c4 | c4 | c4 | c4 | c4 | c4
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_1)) (le_of_eq h4_5.symm)) h2_8) (le_of_eq h3_1)) (le_of_eq h1_1.symm))
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h6_2)) (le_of_eq h4_2.symm)) h4_10) (le_of_eq h4_3)) (le_of_eq h2_2.symm)) (le_of_eq h3_2)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_1)) (le_of_eq h4_5.symm)) h4_8) h2_8) (le_of_eq h3_1)) (le_of_eq h1_1.symm))
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) h2_7) (le_of_eq h4_0.symm)) (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h1_6)
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_1)) (le_of_eq h4_1.symm)) h2_8) (le_of_eq h3_1)) (le_of_eq h1_1.symm))
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_1.symm)) (le_of_eq h2_1)) (le_of_eq h4_1.symm)) (le_of_eq h6_5)) (le_of_eq h3_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h6_2)) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_1)) (le_of_eq h3_5.symm)) h3_8) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h6_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h6_2.symm)) h6_10) (le_of_eq h6_3)) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) (le_of_eq h3_0)) h1_8)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_9 (le_of_eq h6_5.symm)) h3_9) h3_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h8_1)) (le_of_eq h2_2.symm)) (le_of_eq h3_5.symm)) h1_8)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) h1_10) (le_of_eq h8_1)) (le_of_eq h2_2.symm)) (le_of_eq h3_5.symm)) h1_8)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h8_0.symm)) h2_8) h2_9) (le_of_eq h3_5.symm)) h1_8)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) h1_10) h8_6) (le_of_eq h2_2.symm)) (le_of_eq h3_5.symm)) h1_8)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h8_0.symm)) h2_6) (le_of_eq h3_4.symm)) h1_6)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h8_1.symm)) h2_8) h2_9) (le_of_eq h3_5.symm)) h1_8)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_1)) (le_of_eq h3_1.symm)) h1_8)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_8 h0_9) h0_10) (le_of_eq h6_3)) (le_of_eq h3_2.symm)) (le_of_eq h1_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_trans h0_6 h6_6) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) h1_6)
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h6_2)) (le_of_eq h3_2.symm)) h2_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_1)) (le_of_eq h3_5.symm)) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c11 with c11 | c11 | c11 | c11 | c11 | c11
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h11_0)) (le_of_eq h2_1.symm)) (le_of_eq h3_1)) (le_of_eq h1_1.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h11_1)) (le_of_eq h2_2.symm)) (le_of_eq h3_2)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_8 h11_4) h2_8) (le_of_eq h3_1)) (le_of_eq h1_1.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h11_1)) (le_of_eq h2_1.symm)) (le_of_eq h3_1)) (le_of_eq h1_1.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_trans (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h11_0.symm)) h2_6) h3_7) h1_8)
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_8 h11_3) h2_8) (le_of_eq h3_1)) (le_of_eq h1_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h6_2)) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_1)) (le_of_eq h3_5.symm)) h3_8) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h6_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h6_2.symm)) h6_10) (le_of_eq h6_3)) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) (le_of_eq h3_0)) h1_8)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_9 (le_of_eq h6_5.symm)) h3_9) h3_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_6 h8_3) (le_of_eq h2_0.symm)) (le_of_eq h3_4.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_6 (le_of_eq h8_0)) (le_of_eq h2_0.symm)) (le_of_eq h3_4.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h8_4) (le_of_eq h2_0.symm)) (le_of_eq h3_4.symm)) h1_6)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_6 h8_2) (le_of_eq h2_0.symm)) (le_of_eq h3_4.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_9) h8_4) (le_of_eq h2_0.symm)) (le_of_eq h3_4.symm)) h1_6)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h8_3) (le_of_eq h2_0.symm)) (le_of_eq h3_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_1)) (le_of_eq h3_1.symm)) h1_8)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_8 h0_9) h0_10) (le_of_eq h6_3)) (le_of_eq h3_2.symm)) (le_of_eq h1_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_trans h0_6 h6_6) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) h1_6)
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h6_2)) (le_of_eq h3_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_1)) (le_of_eq h3_5.symm)) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_1)) (le_of_eq h3_5.symm)) h1_8)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          rcases c4 with c4 | c4 | c4 | c4 | c4 | c4
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) h2_6) (le_of_eq h4_4)) (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h1_6)
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) h2_6) (le_of_eq h4_4.symm)) (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h1_6)
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3)) (le_of_eq h3_3.symm)) (le_of_eq h2_2.symm)) h2_10) (le_of_eq h4_3)) (le_of_eq h6_2.symm))
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_1)) (le_of_eq h3_1.symm)) h2_8) (le_of_eq h4_0.symm)) (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h1_6)
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3)) (le_of_eq h3_3.symm)) (le_of_eq h2_2.symm)) (le_of_eq h4_2)) (le_of_eq h6_2.symm))
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) h2_6) h4_6) (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h6_2)) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_1)) (le_of_eq h3_5.symm)) h3_8) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h6_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h6_2.symm)) h6_10) (le_of_eq h6_3)) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) (le_of_eq h3_0)) h1_8)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_9 (le_of_eq h6_5.symm)) h3_9) h3_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_2)) (le_of_eq h3_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h2_2.symm)) (le_of_eq h8_0.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_2)) (le_of_eq h3_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h2_2.symm)) h8_4)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h8_0.symm)) (le_of_eq h2_1)) (le_of_eq h3_5.symm)) h1_8)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_2)) (le_of_eq h3_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h2_2.symm)) (le_of_eq h8_1.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) h8_4) (le_of_eq h2_1)) (le_of_eq h3_5.symm)) h1_8)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h8_1.symm)) (le_of_eq h2_1)) (le_of_eq h3_5.symm)) h1_8)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_1)) (le_of_eq h3_1.symm)) h1_8)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_8 h0_9) h0_10) (le_of_eq h6_3)) (le_of_eq h3_2.symm)) (le_of_eq h1_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_trans h0_6 h6_6) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) h1_6)
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h6_2)) (le_of_eq h3_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_1)) (le_of_eq h3_5.symm)) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c11 with c11 | c11 | c11 | c11 | c11 | c11
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 7 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_9 (le_of_eq h11_0.symm)) (le_of_eq h0_1)) (le_of_eq h1_2)) (le_of_eq h3_2.symm)) (le_of_eq h2_1.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_1)) (le_of_eq h3_1.symm)) h2_8) (le_of_eq h11_0.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h11_0.symm)) (le_of_eq h2_1)) (le_of_eq h3_2)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 7 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_9 (le_of_eq h11_1.symm)) (le_of_eq h0_1)) (le_of_eq h1_2)) (le_of_eq h3_2.symm)) (le_of_eq h2_1.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h11_0.symm)) h2_7) (le_of_eq h3_1)) (le_of_eq h1_1.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h11_1.symm)) (le_of_eq h2_1)) (le_of_eq h3_2)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h6_2)) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_1)) (le_of_eq h3_5.symm)) h3_8) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h6_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h6_2.symm)) h6_10) (le_of_eq h6_3)) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) (le_of_eq h3_0)) h1_8)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_9 (le_of_eq h6_5.symm)) h3_9) h3_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c11 with c11 | c11 | c11 | c11 | c11 | c11
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 8 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h3_10 (le_of_eq h3_3)) (le_of_eq h2_2.symm)) (le_of_eq h11_0.symm)) (le_of_eq h0_1)) (le_of_eq h1_2)) (le_of_eq h3_2.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 8 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h3_10 (le_of_eq h3_3)) (le_of_eq h2_2.symm)) h11_4) (le_of_eq h0_1)) (le_of_eq h1_2)) (le_of_eq h3_2.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h11_4) (le_of_eq h2_1)) (le_of_eq h3_5.symm)) h1_8)
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 8 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h3_10 (le_of_eq h3_3)) (le_of_eq h2_2.symm)) (le_of_eq h11_1.symm)) (le_of_eq h0_1)) (le_of_eq h1_2)) (le_of_eq h3_2.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_8 h0_9) h11_4) (le_of_eq h2_1)) (le_of_eq h3_5.symm)) h1_8)
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h11_3) (le_of_eq h2_1)) (le_of_eq h3_5.symm)) h1_8)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_1)) (le_of_eq h3_1.symm)) h1_8)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_8 h0_9) h0_10) (le_of_eq h6_3)) (le_of_eq h3_2.symm)) (le_of_eq h1_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_trans h0_6 h6_6) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) h1_6)
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h6_2)) (le_of_eq h3_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_1)) (le_of_eq h3_5.symm)) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c11 with c11 | c11 | c11 | c11 | c11 | c11
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 7 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_8 (le_of_eq h2_1)) (le_of_eq h11_0.symm)) (le_of_eq h0_1)) (le_of_eq h1_2)) (le_of_eq h3_2.symm)) (le_of_eq h2_5.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_1)) (le_of_eq h3_1.symm)) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h11_0.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h11_0.symm)) (le_of_eq h2_5)) (le_of_eq h3_2)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 7 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_8 (le_of_eq h2_1)) (le_of_eq h11_1.symm)) (le_of_eq h0_1)) (le_of_eq h1_2)) (le_of_eq h3_2.symm)) (le_of_eq h2_5.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h11_0.symm)) (le_of_eq h2_4)) h3_7) h1_8)
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h11_1.symm)) (le_of_eq h2_5)) (le_of_eq h3_2)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h6_2)) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_1)) (le_of_eq h3_5.symm)) h3_8) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h6_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h6_2.symm)) h6_10) (le_of_eq h6_3)) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) (le_of_eq h3_0)) h1_8)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_9 (le_of_eq h6_5.symm)) h3_9) h3_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h3_5)) (le_of_eq h2_5.symm)) h7_8) (le_of_eq h1_0.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_6 h1_7) (le_of_eq h3_5)) (le_of_eq h2_5.symm)) (le_of_eq h7_0.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 5 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h7_6 (le_of_eq h2_4)) (le_of_eq h3_4.symm)) (le_of_eq h1_4))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h3_5)) (le_of_eq h2_5.symm)) (le_of_eq h7_0.symm)) h7_7) (le_of_eq h1_0.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_6 (le_of_eq h1_0)) (le_of_eq h7_0.symm)) (le_of_eq h2_4)) (le_of_eq h3_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          rcases c11 with c11 | c11 | c11 | c11 | c11 | c11
          · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
            exact (lt_irrefl (v 11 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h7_10 (le_of_eq h7_3)) (le_of_eq h1_3.symm)) (le_of_eq h0_2.symm)) (le_of_eq h11_1)) (le_of_eq h7_2.symm))
          · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
            exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h11_1)) (le_of_eq h7_2.symm)) h7_10) (le_of_eq h7_3)) (le_of_eq h1_3.symm)) (le_of_eq h0_2.symm))
          · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
            exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h11_2) (le_of_eq h2_4)) (le_of_eq h3_4.symm)) h1_6)
          · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
            exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h11_0)) (le_of_eq h2_4)) (le_of_eq h3_4.symm)) h1_6)
          · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
            exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h11_2) (le_of_eq h2_4)) (le_of_eq h3_4.symm)) h1_6)
          · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
            exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h11_0.symm)) (le_of_eq h2_4)) (le_of_eq h3_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_1)) (le_of_eq h3_1.symm)) h1_8)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_8 h0_9) h0_10) (le_of_eq h6_3)) (le_of_eq h3_2.symm)) (le_of_eq h1_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_trans h0_6 h6_6) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) h1_6)
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h6_2)) (le_of_eq h3_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_1)) (le_of_eq h3_5.symm)) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_1)) (le_of_eq h3_1.symm)) (le_of_eq h2_0.symm)) h7_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_1)) (le_of_eq h3_1.symm)) (le_of_eq h2_0.symm)) (le_of_eq h7_4.symm)) h7_6) (le_of_eq h1_4.symm)) h1_6)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_1)) (le_of_eq h3_1.symm)) (le_of_eq h2_0.symm)) h7_7) (le_of_eq h1_0.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_1)) (le_of_eq h3_1.symm)) (le_of_eq h2_0.symm)) (le_of_eq h7_4.symm)) (le_of_eq h1_4.symm)) h1_6)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_1)) (le_of_eq h3_1.symm)) (le_of_eq h2_0.symm)) (le_of_eq h7_0)) (le_of_eq h1_0.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_1)) (le_of_eq h3_1.symm)) (le_of_eq h2_0.symm)) (le_of_eq h7_4)) (le_of_eq h1_4.symm)) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h6_2)) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_1)) (le_of_eq h3_5.symm)) h3_8) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h6_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h6_2.symm)) h6_10) (le_of_eq h6_3)) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) (le_of_eq h3_0)) h1_8)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_9 (le_of_eq h6_5.symm)) h3_9) h3_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) (le_of_eq h0_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) h1_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_1)) (le_of_eq h3_1.symm)) h3_9) h3_10) (le_of_eq h3_3)) (le_of_eq h2_3.symm)) (le_of_eq h7_2.symm)) (le_of_eq h1_5.symm)) (le_of_eq h3_5)) (le_of_eq h2_5.symm)) h2_8) h7_8) (le_of_eq h1_0.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_6 h1_7) (le_of_eq h3_5)) (le_of_eq h2_5.symm)) h2_8) (le_of_eq h7_0.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 3 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_8 (le_of_eq h7_1)) (le_of_eq h1_5.symm)) (le_of_eq h3_5)) (le_of_eq h2_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h3_5)) (le_of_eq h2_5.symm)) h2_8) h2_9) (le_of_eq h7_5.symm)) (le_of_eq h1_0.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          rcases c9 with c9 | c9 | c9 | c9 | c9 | c9
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h0_0)) h9_4) (le_of_eq h2_0.symm)) (le_of_eq h7_0)) (le_of_eq h1_0.symm))
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h0_0)) (le_of_eq h9_0.symm)) (le_of_eq h3_4.symm)) h1_6)
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_2)) (le_of_eq h3_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h9_1.symm)) (le_of_eq h0_5.symm))
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h0_0)) h9_3) (le_of_eq h2_0.symm)) (le_of_eq h7_0)) (le_of_eq h1_0.symm))
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h0_3)) (le_of_eq h9_1)) (le_of_eq h2_3.symm)) (le_of_eq h7_3)) (le_of_eq h1_3.symm)) (le_of_eq h0_2.symm))
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_10 (le_of_eq h0_3)) h9_6) (le_of_eq h2_3.symm)) (le_of_eq h7_3)) (le_of_eq h1_3.symm)) (le_of_eq h0_2.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 3 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_6 (le_of_eq h7_4)) (le_of_eq h1_4.symm)) (le_of_eq h3_4)) (le_of_eq h2_4.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_1)) (le_of_eq h3_1.symm)) h1_8)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_8 h0_9) h0_10) (le_of_eq h6_3)) (le_of_eq h3_2.symm)) (le_of_eq h1_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_trans h0_6 h6_6) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) h1_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) h1_6)
  · rcases c1 with ⟨h1_0,h1_1,h1_2,h1_3,h1_4,h1_5,h1_6,h1_7,h1_8,h1_9,h1_10⟩
    rcases c2 with c2 | c2 | c2 | c2 | c2 | c2
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_1)) (le_of_eq h3_1.symm)) (le_of_eq h2_1)) (le_of_eq h8_0.symm))
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_1)) (le_of_eq h3_1.symm)) (le_of_eq h2_1)) h8_4)
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h8_1.symm)) (le_of_eq h2_1.symm)) (le_of_eq h3_1)) (le_of_eq h6_1.symm))
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_1)) (le_of_eq h3_1.symm)) (le_of_eq h2_1)) (le_of_eq h8_1.symm))
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 5 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h1_7 (le_of_eq h8_0.symm)) h2_6) (le_of_eq h3_0)) (le_of_eq h1_0.symm))
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 3 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_8 (le_of_eq h3_1)) (le_of_eq h6_1.symm)) (le_of_eq h0_1)) (le_of_eq h8_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_5)) (le_of_eq h3_5.symm)) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h7_1)) (le_of_eq h2_5.symm)) h2_8) (le_of_eq h3_1)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 1 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_10 (le_of_eq h2_3)) (le_of_eq h7_3.symm)) (le_of_eq h1_3)) (le_of_eq h3_2.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h7_8) (le_of_eq h2_0.symm)) h3_7) (le_of_eq h1_0.symm)) h1_7)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h7_5)) (le_of_eq h2_5.symm)) h2_8) (le_of_eq h3_1)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h7_0.symm)) (le_of_eq h2_4.symm)) h2_6) h3_7) (le_of_eq h1_0.symm)) h1_7)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) (le_of_eq h7_5.symm)) (le_of_eq h2_0.symm)) h3_7) (le_of_eq h1_0.symm)) h1_7)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h7_1)) (le_of_eq h2_5.symm)) h2_8) (le_of_eq h3_5)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_6 (le_of_eq h7_0)) (le_of_eq h2_0.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h7_8) (le_of_eq h2_0.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h7_5)) (le_of_eq h2_5.symm)) h2_8) (le_of_eq h3_5)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h7_0.symm)) (le_of_eq h2_4.symm)) h2_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h1_9) (le_of_eq h7_5.symm)) (le_of_eq h2_0.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_5)) (le_of_eq h3_1.symm)) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h6_8) (le_of_eq h3_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) h3_7) (le_of_eq h1_0.symm)) h1_7)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h0_9) (le_of_eq h6_5.symm)) (le_of_eq h3_1)) (le_of_eq h1_5.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h0_9) (le_of_eq h6_2)) (le_of_eq h3_2.symm)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_8 h0_9) h0_10) (le_of_eq h6_3)) (le_of_eq h3_2.symm)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) (le_of_eq h1_4.symm))
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          rcases c4 with c4 | c4 | c4 | c4 | c4 | c4
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 5 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h1_5)) (le_of_eq h3_5.symm)) (le_of_eq h6_5)) (le_of_eq h4_5.symm)) (le_of_eq h2_0.symm)) (le_of_eq h3_0)) (le_of_eq h1_0.symm))
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
            · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
              exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h8_0)) (le_of_eq h4_5.symm)) (le_of_eq h6_0.symm))
            · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
              exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3)) (le_of_eq h4_2.symm)) h4_10) (le_of_eq h4_3)) (le_of_eq h8_1.symm)) (le_of_eq h0_2.symm))
            · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
              exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_7 h8_4) (le_of_eq h4_0.symm)) h4_7) (le_of_eq h6_0.symm))
            · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
              exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h8_1)) (le_of_eq h4_5.symm)) (le_of_eq h6_0.symm))
            · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
              exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h8_0.symm)) (le_of_eq h4_4.symm)) (le_of_eq h6_4.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
            · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
              exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_7 h8_3) (le_of_eq h4_0.symm)) h4_7) (le_of_eq h6_0.symm))
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 5 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h1_5)) (le_of_eq h3_5.symm)) (le_of_eq h6_5)) (le_of_eq h4_5.symm)) h4_8) (le_of_eq h2_0.symm)) (le_of_eq h3_0)) (le_of_eq h1_0.symm))
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_6 (le_of_eq h1_0)) (le_of_eq h3_0.symm)) (le_of_eq h2_0)) (le_of_eq h4_0.symm)) (le_of_eq h6_4.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h6_3)) (le_of_eq h4_2.symm)) (le_of_eq h2_5.symm)) h2_8) (le_of_eq h3_1)) (le_of_eq h6_1.symm))
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h0_9) (le_of_eq h6_2)) (le_of_eq h3_2.symm)) h2_10) (le_of_eq h2_3)) (le_of_eq h4_2.symm)) (le_of_eq h6_5.symm)) (le_of_eq h3_5)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_5)) (le_of_eq h3_5.symm)) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) h2_10) (le_of_eq h2_3)) (le_of_eq h8_1.symm)) (le_of_eq h0_1.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 5 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h3_2.symm)) h2_10) (le_of_eq h2_3)) (le_of_eq h8_1.symm)) (le_of_eq h1_2.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h8_0.symm)) (le_of_eq h2_0.symm)) h3_7) (le_of_eq h1_0.symm)) h1_7)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 7 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_8 (le_of_eq h3_1)) (le_of_eq h1_5.symm)) (le_of_eq h8_1)) (le_of_eq h2_5.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) h8_4) (le_of_eq h2_0.symm)) h3_7) (le_of_eq h1_0.symm)) h1_7)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h8_1.symm)) (le_of_eq h2_0.symm)) h3_7) (le_of_eq h1_0.symm)) h1_7)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h7_1)) (le_of_eq h2_1.symm)) (le_of_eq h3_5)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 1 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h2_10 (le_of_eq h3_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_3.symm)) (le_of_eq h7_3)) (le_of_eq h2_2.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h7_8) h2_8) (le_of_eq h3_5)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h7_5)) (le_of_eq h2_1.symm)) (le_of_eq h3_5)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h7_0.symm)) h2_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) (le_of_eq h7_5.symm)) h2_8) (le_of_eq h3_5)) (le_of_eq h1_5.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_5)) (le_of_eq h3_1.symm)) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h6_8) (le_of_eq h3_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) h3_7) (le_of_eq h1_0.symm)) h1_7)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h0_9) (le_of_eq h6_5.symm)) (le_of_eq h3_1)) (le_of_eq h1_5.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h0_9) (le_of_eq h6_2)) (le_of_eq h3_2.symm)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_8 h0_9) h0_10) (le_of_eq h6_3)) (le_of_eq h3_2.symm)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) (le_of_eq h1_4.symm))
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h3_3.symm)) (le_of_eq h2_2.symm)) (le_of_eq h8_0.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_5)) (le_of_eq h3_5.symm)) h3_8) h2_8) (le_of_eq h8_0.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 5 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h3_3.symm)) (le_of_eq h2_2.symm)) (le_of_eq h8_1)) (le_of_eq h1_2.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h3_3.symm)) (le_of_eq h2_2.symm)) (le_of_eq h8_1.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 5 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h3_3.symm)) (le_of_eq h2_2.symm)) h2_10) (le_of_eq h8_1)) (le_of_eq h1_2.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_6 (le_of_eq h1_0)) (le_of_eq h3_0.symm)) h2_6) (le_of_eq h8_0))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h7_1)) (le_of_eq h2_5.symm)) (le_of_eq h3_1)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 3 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h2_9 h2_10) (le_of_eq h2_3)) (le_of_eq h7_3.symm)) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h2_1.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h7_8) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h3_1)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h7_5)) (le_of_eq h2_5.symm)) (le_of_eq h3_1)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h7_0.symm)) (le_of_eq h2_4.symm)) h3_7) (le_of_eq h1_0.symm)) h1_7)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) (le_of_eq h7_5.symm)) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h3_1)) (le_of_eq h1_5.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h7_1)) (le_of_eq h2_5.symm)) (le_of_eq h3_5)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          rcases c5 with c5 | c5 | c5 | c5 | c5 | c5
          · rcases c5 with ⟨h5_0,h5_1,h5_2,h5_3,h5_4,h5_5,h5_6,h5_7,h5_8,h5_9,h5_10⟩
            exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_7 h1_8) (le_of_eq h7_1)) (le_of_eq h5_5.symm)) (le_of_eq h0_0.symm))
          · rcases c5 with ⟨h5_0,h5_1,h5_2,h5_3,h5_4,h5_5,h5_6,h5_7,h5_8,h5_9,h5_10⟩
            rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
            · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
              exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h7_3)) (le_of_eq h2_3.symm)) (le_of_eq h8_1.symm)) (le_of_eq h0_1.symm))
            · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
              exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_5)) (le_of_eq h3_5.symm)) h2_8) (le_of_eq h8_0.symm))
            · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
              rcases c4 with c4 | c4 | c4 | c4 | c4 | c4
              · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
                exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h8_1.symm)) (le_of_eq h4_1.symm)) (le_of_eq h5_1)) (le_of_eq h7_1.symm)) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
              · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
                exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_7 h8_4) (le_of_eq h4_0.symm)) (le_of_eq h5_0)) (le_of_eq h0_0.symm))
              · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
                exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) (le_of_eq h7_2)) (le_of_eq h5_2.symm)) (le_of_eq h4_1.symm)) (le_of_eq h8_0)) (le_of_eq h0_1.symm))
              · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
                exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h8_1.symm)) (le_of_eq h4_5.symm)) (le_of_eq h5_1)) (le_of_eq h7_1.symm)) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
              · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
                exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h7_1)) (le_of_eq h5_1.symm)) (le_of_eq h4_0.symm)) h8_3)
              · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
                exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) (le_of_eq h7_2)) (le_of_eq h5_2.symm)) (le_of_eq h4_5.symm)) (le_of_eq h8_0)) (le_of_eq h0_1.symm))
            · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
              exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_6 (le_of_eq h7_0)) (le_of_eq h2_0.symm)) (le_of_eq h8_0.symm))
            · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
              exact (lt_irrefl (v 5 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h8_0.symm)) (le_of_eq h2_0)) (le_of_eq h7_0.symm))
            · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
              exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_6 (le_of_eq h7_0)) (le_of_eq h2_0.symm)) (le_of_eq h8_0))
          · rcases c5 with ⟨h5_0,h5_1,h5_2,h5_3,h5_4,h5_5,h5_6,h5_7,h5_8,h5_9,h5_10⟩
            exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_5)) (le_of_eq h3_5.symm)) (le_of_eq h2_5)) (le_of_eq h7_5.symm)) (le_of_eq h5_0.symm)) (le_of_eq h0_4.symm))
          · rcases c5 with ⟨h5_0,h5_1,h5_2,h5_3,h5_4,h5_5,h5_6,h5_7,h5_8,h5_9,h5_10⟩
            exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h0_0)) (le_of_eq h5_0.symm)) (le_of_eq h7_4)) (le_of_eq h2_4.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
          · rcases c5 with ⟨h5_0,h5_1,h5_2,h5_3,h5_4,h5_5,h5_6,h5_7,h5_8,h5_9,h5_10⟩
            exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_7 h1_8) (le_of_eq h7_1)) (le_of_eq h5_1.symm)) (le_of_eq h0_0.symm))
          · rcases c5 with ⟨h5_0,h5_1,h5_2,h5_3,h5_4,h5_5,h5_6,h5_7,h5_8,h5_9,h5_10⟩
            exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h0_3)) (le_of_eq h5_2.symm)) (le_of_eq h7_1.symm)) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h7_8) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h3_5)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h7_5)) (le_of_eq h2_5.symm)) (le_of_eq h3_5)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h7_0.symm)) (le_of_eq h2_4.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) (le_of_eq h7_5.symm)) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h3_5)) (le_of_eq h1_5.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_5)) (le_of_eq h3_1.symm)) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h6_8) (le_of_eq h3_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) h3_7) (le_of_eq h1_0.symm)) h1_7)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h0_9) (le_of_eq h6_5.symm)) (le_of_eq h3_1)) (le_of_eq h1_5.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h0_9) (le_of_eq h6_2)) (le_of_eq h3_2.symm)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_8 h0_9) h0_10) (le_of_eq h6_3)) (le_of_eq h3_2.symm)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) (le_of_eq h1_4.symm))
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_1)) (le_of_eq h3_1.symm)) (le_of_eq h2_5)) (le_of_eq h8_0.symm))
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_1)) (le_of_eq h3_1.symm)) (le_of_eq h2_5)) h8_4)
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h8_1.symm)) (le_of_eq h2_5.symm)) (le_of_eq h3_1)) (le_of_eq h6_1.symm))
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_1)) (le_of_eq h3_1.symm)) (le_of_eq h2_5)) (le_of_eq h8_1.symm))
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 5 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h8_0.symm)) (le_of_eq h2_4.symm)) (le_of_eq h3_0)) (le_of_eq h1_0.symm))
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_6 (le_of_eq h1_0)) (le_of_eq h3_0.symm)) (le_of_eq h2_4)) (le_of_eq h8_0))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_5)) (le_of_eq h3_5.symm)) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h2_1.symm)) h7_8) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h2_1.symm)) (le_of_eq h7_0.symm)) h1_7)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 5 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h2_1.symm)) (le_of_eq h7_1))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h2_1.symm)) h2_9) (le_of_eq h7_5.symm)) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h7_0.symm)) h2_7) (le_of_eq h3_1)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 5 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h2_1.symm)) (le_of_eq h7_5))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 3 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h8_2 (le_of_eq h1_4)) (le_of_eq h3_4.symm)) (le_of_eq h2_4))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_6 (le_of_eq h2_0)) (le_of_eq h8_0.symm)) (le_of_eq h1_4)) (le_of_eq h3_4.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h8_0.symm)) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h3_5)) (le_of_eq h1_5.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          rcases c9 with c9 | c9 | c9 | c9 | c9 | c9
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 6 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h9_2 (le_of_eq h2_4)) (le_of_eq h8_0.symm)) (le_of_eq h0_4))
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h0_0)) (le_of_eq h9_0.symm)) (le_of_eq h2_4)) (le_of_eq h8_0.symm))
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_5)) (le_of_eq h3_5.symm)) h9_4) (le_of_eq h0_0.symm))
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
            · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
              exact (lt_irrefl (v 5 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h3_3.symm)) (le_of_eq h6_2.symm)) (le_of_eq h0_2)) (le_of_eq h1_2.symm))
            · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
              exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h0_5)) (le_of_eq h9_1.symm)) h3_8) (le_of_eq h6_0.symm))
            · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
              exact (lt_irrefl (v 1 3)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h9_6 (le_of_eq h0_3.symm)) (le_of_eq h6_2.symm)) (le_of_eq h3_2))
            · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
              rcases c4 with c4 | c4 | c4 | c4 | c4 | c4
              · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
                exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h4_4.symm)) (le_of_eq h8_0.symm))
              · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
                exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h4_4)) (le_of_eq h8_0.symm))
              · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
                exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h4_4.symm)) h4_6) (le_of_eq h8_0.symm))
              · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
                exact (lt_irrefl (v 7 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h2_7 h3_8) (le_of_eq h6_0.symm)) (le_of_eq h4_0)) (le_of_eq h2_0.symm))
              · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
                exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h4_6) (le_of_eq h8_0.symm))
              · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
                exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h6_8) (le_of_eq h4_1)) (le_of_eq h8_1.symm))
            · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
              exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) (le_of_eq h3_0)) (le_of_eq h1_0.symm)) h1_7)
            · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
              rcases c4 with c4 | c4 | c4 | c4 | c4 | c4
              · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
                exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h4_4.symm)) (le_of_eq h8_0.symm))
              · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
                exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h4_4)) (le_of_eq h8_0.symm))
              · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
                exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h4_4.symm)) h4_6) (le_of_eq h8_0.symm))
              · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
                exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) (le_of_eq h4_0)) h8_3)
              · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
                exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h4_6) (le_of_eq h8_0.symm))
              · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
                exact (lt_irrefl (v 0 1)) (lt_trans (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) h4_7) h8_3)
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_5)) (le_of_eq h3_5.symm)) (le_of_eq h9_0.symm)) (le_of_eq h0_4.symm))
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_5)) (le_of_eq h3_5.symm)) h9_3) (le_of_eq h0_0.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h8_0.symm)) (le_of_eq h2_4.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h8_1.symm)) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h3_5)) (le_of_eq h1_5.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_5)) (le_of_eq h3_1.symm)) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h6_8) (le_of_eq h3_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) h3_7) (le_of_eq h1_0.symm)) h1_7)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h0_9) (le_of_eq h6_5.symm)) (le_of_eq h3_1)) (le_of_eq h1_5.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h0_9) (le_of_eq h6_2)) (le_of_eq h3_2.symm)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_8 h0_9) h0_10) (le_of_eq h6_3)) (le_of_eq h3_2.symm)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) (le_of_eq h1_4.symm))
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_5)) (le_of_eq h3_5.symm)) h3_8) (le_of_eq h2_0.symm)) h8_2)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_5)) (le_of_eq h3_5.symm)) h3_8) (le_of_eq h2_0.symm)) h8_2)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 8 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h3_8 (le_of_eq h2_0.symm)) h8_3) (le_of_eq h1_5)) (le_of_eq h3_5.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_5)) (le_of_eq h3_5.symm)) h3_8) (le_of_eq h2_0.symm)) (le_of_eq h8_0.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 5 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h3_3.symm)) (le_of_eq h2_3.symm)) (le_of_eq h8_1)) (le_of_eq h1_2.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_5)) (le_of_eq h3_5.symm)) h3_8) (le_of_eq h2_0.symm)) (le_of_eq h8_0))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h2_5.symm)) h7_8) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h2_5.symm)) (le_of_eq h7_0.symm)) h1_7)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 5 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h2_5.symm)) (le_of_eq h7_1))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h2_5.symm)) (le_of_eq h7_0.symm)) h7_7) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h7_0.symm)) (le_of_eq h2_4)) h3_7) (le_of_eq h1_0.symm)) h1_7)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 5 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h2_5.symm)) (le_of_eq h7_5))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          rcases c5 with c5 | c5 | c5 | c5 | c5 | c5
          · rcases c5 with ⟨h5_0,h5_1,h5_2,h5_3,h5_4,h5_5,h5_6,h5_7,h5_8,h5_9,h5_10⟩
            exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_5)) (le_of_eq h3_5.symm)) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h7_5)) (le_of_eq h5_5.symm)) (le_of_eq h0_0.symm))
          · rcases c5 with ⟨h5_0,h5_1,h5_2,h5_3,h5_4,h5_5,h5_6,h5_7,h5_8,h5_9,h5_10⟩
            exact (lt_irrefl (v 5 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h0_5)) (le_of_eq h5_5.symm)) (le_of_eq h7_0.symm))
          · rcases c5 with ⟨h5_0,h5_1,h5_2,h5_3,h5_4,h5_5,h5_6,h5_7,h5_8,h5_9,h5_10⟩
            exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_5)) (le_of_eq h3_5.symm)) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h7_5)) (le_of_eq h5_5.symm)) h5_8) (le_of_eq h0_0.symm))
          · rcases c5 with ⟨h5_0,h5_1,h5_2,h5_3,h5_4,h5_5,h5_6,h5_7,h5_8,h5_9,h5_10⟩
            exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h0_0)) (le_of_eq h5_0.symm)) (le_of_eq h7_4.symm)) (le_of_eq h2_4)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
          · rcases c5 with ⟨h5_0,h5_1,h5_2,h5_3,h5_4,h5_5,h5_6,h5_7,h5_8,h5_9,h5_10⟩
            exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_5)) (le_of_eq h3_5.symm)) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h7_5)) (le_of_eq h5_1.symm)) (le_of_eq h0_0.symm))
          · rcases c5 with ⟨h5_0,h5_1,h5_2,h5_3,h5_4,h5_5,h5_6,h5_7,h5_8,h5_9,h5_10⟩
            exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h0_3)) (le_of_eq h5_2.symm)) (le_of_eq h7_5.symm)) h7_8) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 5 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h1_5)) (le_of_eq h3_5.symm)) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h7_0.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_6 h7_6) (le_of_eq h2_4)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_6 (le_of_eq h7_4)) (le_of_eq h2_4)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h7_0.symm)) (le_of_eq h2_4)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_6 (le_of_eq h7_4.symm)) (le_of_eq h2_4)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_5)) (le_of_eq h3_1.symm)) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h6_8) (le_of_eq h3_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) h3_7) (le_of_eq h1_0.symm)) h1_7)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h0_9) (le_of_eq h6_5.symm)) (le_of_eq h3_1)) (le_of_eq h1_5.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h0_9) (le_of_eq h6_2)) (le_of_eq h3_2.symm)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_8 h0_9) h0_10) (le_of_eq h6_3)) (le_of_eq h3_2.symm)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) (le_of_eq h1_4.symm))
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h0_9) (le_of_eq h6_2)) (le_of_eq h3_2.symm)) (le_of_eq h2_5.symm)) h8_4)
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_7) h3_8) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h8_0.symm))
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h6_2)) (le_of_eq h3_2.symm)) (le_of_eq h2_5.symm)) (le_of_eq h8_0)) (le_of_eq h0_1.symm))
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h0_9) (le_of_eq h6_2)) (le_of_eq h3_2.symm)) (le_of_eq h2_5.symm)) h8_3)
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 5 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h8_0.symm)) (le_of_eq h2_4)) (le_of_eq h3_0)) (le_of_eq h1_0.symm))
          · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
            exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h6_2)) (le_of_eq h3_2.symm)) (le_of_eq h2_5.symm)) (le_of_eq h8_1)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_5)) (le_of_eq h3_5.symm)) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4)) (le_of_eq h1_4.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h2_5.symm)) h2_8) h7_8) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h2_5.symm)) h2_8) (le_of_eq h7_0.symm)) h1_7)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 5 2)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h2_5.symm)) h2_8) (le_of_eq h7_1))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h2_5.symm)) h2_8) h2_9) (le_of_eq h7_5.symm)) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h7_0.symm)) (le_of_eq h2_0)) (le_of_eq h3_1)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 5 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h1_5)) (le_of_eq h3_1.symm)) (le_of_eq h2_0.symm)) (le_of_eq h7_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 5 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h1_5)) (le_of_eq h3_5.symm)) (le_of_eq h2_0.symm)) h7_6)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 5 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h1_5)) (le_of_eq h3_5.symm)) (le_of_eq h2_0.symm)) (le_of_eq h7_4.symm)) h7_6)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 7 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h2_10 (le_of_eq h2_3)) (le_of_eq h3_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_3.symm)) (le_of_eq h7_2.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 5 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h1_5)) (le_of_eq h3_5.symm)) (le_of_eq h2_0.symm)) (le_of_eq h7_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h7_0.symm)) (le_of_eq h2_0)) (le_of_eq h3_5)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 5 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h1_5)) (le_of_eq h3_5.symm)) (le_of_eq h2_0.symm)) (le_of_eq h7_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_5)) (le_of_eq h3_1.symm)) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h6_8) (le_of_eq h3_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h3_2.symm)) (le_of_eq h6_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) h3_7) (le_of_eq h1_0.symm)) h1_7)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h0_9) (le_of_eq h6_5.symm)) (le_of_eq h3_1)) (le_of_eq h1_5.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h0_9) (le_of_eq h6_2)) (le_of_eq h3_2.symm)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_8 h0_9) h0_10) (le_of_eq h6_3)) (le_of_eq h3_2.symm)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) (le_of_eq h1_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) (le_of_eq h1_4.symm))
  · rcases c1 with ⟨h1_0,h1_1,h1_2,h1_3,h1_4,h1_5,h1_6,h1_7,h1_8,h1_9,h1_10⟩
    rcases c2 with c2 | c2 | c2 | c2 | c2 | c2
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_0.symm)) h2_7) h8_4)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_0.symm)) h2_7) (le_of_eq h8_0.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_7 (le_of_eq h8_0)) (le_of_eq h1_1.symm)) (le_of_eq h3_0.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_0.symm)) h2_7) h8_3)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 1 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_9 (le_of_eq h2_2)) (le_of_eq h8_1)) (le_of_eq h1_2.symm)) (le_of_eq h3_5.symm)) h3_8)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_7 (le_of_eq h8_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_0.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h3_8) h2_9) h2_10) (le_of_eq h2_3)) (le_of_eq h7_2.symm)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_6 h3_6) (le_of_eq h2_0)) (le_of_eq h7_0.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 9 2)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h7_2.symm)) (le_of_eq h2_5.symm)) h2_8) (le_of_eq h3_1))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 1 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_7 (le_of_eq h2_5)) (le_of_eq h7_5.symm)) (le_of_eq h1_0.symm)) h3_6)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 1 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_10 (le_of_eq h2_3)) (le_of_eq h7_3)) (le_of_eq h1_3.symm)) (le_of_eq h3_2.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 1 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h2_10 (le_of_eq h2_3)) (le_of_eq h7_2.symm)) h7_10) (le_of_eq h7_3)) (le_of_eq h1_3.symm)) (le_of_eq h3_2.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) (le_of_eq h3_5.symm)) h2_9) h2_10) (le_of_eq h2_3)) (le_of_eq h7_2.symm)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_6 (le_of_eq h3_4.symm)) (le_of_eq h2_0)) (le_of_eq h7_0.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h1_5)) (le_of_eq h7_1.symm)) (le_of_eq h2_0.symm)) (le_of_eq h3_4))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_7 (le_of_eq h2_5)) (le_of_eq h7_5.symm)) (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h1_5)) (le_of_eq h7_5.symm)) h7_8) (le_of_eq h2_0.symm)) (le_of_eq h3_4))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h1_5)) (le_of_eq h7_5.symm)) (le_of_eq h2_0.symm)) (le_of_eq h3_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) (le_of_eq h3_2)) (le_of_eq h2_3)) (le_of_eq h7_2.symm)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 9 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h7_3)) (le_of_eq h2_3.symm)) (le_of_eq h3_2.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h7_2.symm)) (le_of_eq h2_5.symm)) h2_8) h3_8) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 9 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h7_2.symm)) h7_10) (le_of_eq h7_3)) (le_of_eq h2_3.symm)) (le_of_eq h3_2.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 9 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h1_5)) (le_of_eq h7_5.symm)) h7_8) (le_of_eq h2_0.symm)) h3_6)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 9 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h1_5)) (le_of_eq h7_5.symm)) (le_of_eq h2_0.symm)) h3_6)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_5)) h2_10) (le_of_eq h2_3)) (le_of_eq h7_2.symm)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_6 (le_of_eq h3_4)) (le_of_eq h2_0)) (le_of_eq h7_0.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h7_2.symm)) (le_of_eq h2_5.symm)) h2_8) h2_9) (le_of_eq h3_5.symm)) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_7 (le_of_eq h2_5)) (le_of_eq h7_5.symm)) (le_of_eq h1_0.symm)) (le_of_eq h3_4))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h1_5)) (le_of_eq h7_5.symm)) h7_8) (le_of_eq h2_0.symm)) (le_of_eq h3_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h1_5)) (le_of_eq h7_5.symm)) (le_of_eq h2_0.symm)) (le_of_eq h3_4.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h8_0)) (le_of_eq h2_1.symm)) (le_of_eq h3_0.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h8_1)) (le_of_eq h2_2.symm)) (le_of_eq h3_5.symm)) h3_8) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h8_0.symm)) h2_8) (le_of_eq h3_0.symm)) h1_7)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) h8_6) (le_of_eq h2_2.symm)) (le_of_eq h3_5.symm)) h3_8) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) h8_4) h2_8) (le_of_eq h3_0.symm)) h1_7)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h8_1.symm)) h2_8) (le_of_eq h3_0.symm)) h1_7)
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_0.symm)) h2_7) h7_8) (le_of_eq h1_0.symm)) h1_7)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_0.symm)) h2_7) (le_of_eq h7_0.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_0.symm)) h2_7) (le_of_eq h7_1)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_0.symm)) h2_7) (le_of_eq h7_0.symm)) h7_7) (le_of_eq h1_0.symm)) h1_7)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 1 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_10 (le_of_eq h3_3)) (le_of_eq h1_3)) (le_of_eq h7_3.symm)) (le_of_eq h2_2.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_0.symm)) h2_7) (le_of_eq h7_5)) (le_of_eq h1_5.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c11 with c11 | c11 | c11 | c11 | c11 | c11
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) (le_of_eq h3_1.symm)) (le_of_eq h2_1)) (le_of_eq h11_0.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) (le_of_eq h3_1.symm)) (le_of_eq h2_1)) h11_4)
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h11_1.symm)) (le_of_eq h2_1.symm)) (le_of_eq h3_1)) (le_of_eq h1_2)) (le_of_eq h0_2.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) (le_of_eq h3_1.symm)) (le_of_eq h2_1)) (le_of_eq h11_1.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 7 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h2_6 h3_7) (le_of_eq h1_1)) (le_of_eq h0_1.symm)) (le_of_eq h11_0.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 7 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_8 (le_of_eq h3_1)) (le_of_eq h1_2)) (le_of_eq h0_2.symm)) (le_of_eq h11_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c11 with c11 | c11 | c11 | c11 | c11 | c11
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) (le_of_eq h3_5.symm)) (le_of_eq h2_1)) (le_of_eq h11_0.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) (le_of_eq h3_5.symm)) (le_of_eq h2_1)) h11_4)
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h11_1.symm)) (le_of_eq h2_1.symm)) (le_of_eq h3_5)) (le_of_eq h1_2)) (le_of_eq h0_2.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) (le_of_eq h3_5.symm)) (le_of_eq h2_1)) (le_of_eq h11_1.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h11_0.symm)) h2_6) (le_of_eq h3_4)) h1_7)
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 7 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_8 (le_of_eq h3_5)) (le_of_eq h1_2)) (le_of_eq h0_2.symm)) (le_of_eq h11_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c11 with c11 | c11 | c11 | c11 | c11 | c11
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h11_1)) (le_of_eq h2_2.symm)) (le_of_eq h3_1.symm)) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h11_1)) (le_of_eq h2_2.symm)) (le_of_eq h3_1.symm)) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_9 (le_of_eq h11_0.symm)) h2_8) h3_8) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_9 h0_10) h11_6) (le_of_eq h2_2.symm)) (le_of_eq h3_1.symm)) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_trans (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h11_0.symm)) h2_6) h3_6) h1_7)
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_9 (le_of_eq h11_1.symm)) h2_8) h3_8) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c11 with c11 | c11 | c11 | c11 | c11 | c11
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h11_1)) (le_of_eq h2_2.symm)) (le_of_eq h3_5.symm)) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h11_1)) (le_of_eq h2_2.symm)) (le_of_eq h3_5.symm)) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_9 (le_of_eq h11_0.symm)) h2_8) h2_9) (le_of_eq h3_5.symm)) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_9 h0_10) h11_6) (le_of_eq h2_2.symm)) (le_of_eq h3_5.symm)) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h11_0.symm)) h2_6) (le_of_eq h3_4.symm)) h1_7)
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_9 (le_of_eq h11_1.symm)) h2_8) h2_9) (le_of_eq h3_5.symm)) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h3_3)) (le_of_eq h2_3)) (le_of_eq h8_1.symm)) (le_of_eq h0_1.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 9 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h3_3)) (le_of_eq h2_3)) (le_of_eq h8_1.symm)) (le_of_eq h1_2.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h8_0.symm)) (le_of_eq h2_0.symm)) (le_of_eq h3_4.symm)) h3_6) h1_7)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h8_1)) (le_of_eq h2_5.symm)) h2_8) (le_of_eq h3_0.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) h8_4) (le_of_eq h2_0.symm)) (le_of_eq h3_4.symm)) h3_6) h1_7)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h8_1.symm)) (le_of_eq h2_0.symm)) (le_of_eq h3_4.symm)) h3_6) h1_7)
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_0.symm)) (le_of_eq h2_4)) h7_6) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_0.symm)) (le_of_eq h2_4)) (le_of_eq h7_4.symm)) h7_6) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_0.symm)) (le_of_eq h2_4)) h7_7) (le_of_eq h1_0.symm)) h1_7)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_0.symm)) (le_of_eq h2_4)) (le_of_eq h7_4.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_0.symm)) (le_of_eq h2_4)) (le_of_eq h7_0)) (le_of_eq h1_0.symm)) h1_7)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_0.symm)) (le_of_eq h2_4)) (le_of_eq h7_4)) (le_of_eq h1_4.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h3_8) (le_of_eq h2_5)) (le_of_eq h7_1.symm)) (le_of_eq h1_0.symm)) h3_6) (le_of_eq h2_4)) h7_6) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h3_8) (le_of_eq h2_5)) (le_of_eq h7_5.symm)) h7_8) (le_of_eq h1_0.symm)) h3_6) (le_of_eq h2_4)) (le_of_eq h7_4.symm)) h7_6) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 9 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h7_2.symm)) (le_of_eq h2_5.symm)) (le_of_eq h3_1))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h3_8) (le_of_eq h2_5)) (le_of_eq h7_5.symm)) (le_of_eq h1_0.symm)) h3_6) (le_of_eq h2_4)) (le_of_eq h7_4.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 3 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h2_9 h2_10) (le_of_eq h2_3)) (le_of_eq h7_3)) (le_of_eq h1_3.symm)) (le_of_eq h3_2.symm)) (le_of_eq h2_1.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_6 h3_6) (le_of_eq h2_4)) (le_of_eq h7_4)) (le_of_eq h1_4.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) (le_of_eq h3_5.symm)) h2_8) h8_4)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h1_9) (le_of_eq h3_5.symm)) h2_8) (le_of_eq h8_0.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) (le_of_eq h3_5.symm)) h2_8) (le_of_eq h8_0)) (le_of_eq h0_1.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) (le_of_eq h3_5.symm)) h2_8) h8_3)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 1 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h2_8 h2_9) h2_10) (le_of_eq h8_1)) (le_of_eq h1_2.symm)) (le_of_eq h3_5.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) (le_of_eq h3_5.symm)) h2_8) (le_of_eq h8_1)) (le_of_eq h0_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h3_3)) (le_of_eq h6_2.symm)) (le_of_eq h0_2)) (le_of_eq h1_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          rcases c4 with c4 | c4 | c4 | c4 | c4 | c4
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_6 (le_of_eq h4_4)) (le_of_eq h6_4)) (le_of_eq h3_4.symm))
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 4 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) (le_of_eq h3_2)) (le_of_eq h2_2.symm)) (le_of_eq h4_5.symm)) h6_8)
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 3 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_7 (le_of_eq h3_5)) (le_of_eq h6_5.symm)) (le_of_eq h4_0.symm))
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_7 h1_8) (le_of_eq h3_1)) (le_of_eq h2_1.symm)) (le_of_eq h4_0.symm)) h6_6)
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            rcases c5 with c5 | c5 | c5 | c5 | c5 | c5
            · rcases c5 with ⟨h5_0,h5_1,h5_2,h5_3,h5_4,h5_5,h5_6,h5_7,h5_8,h5_9,h5_10⟩
              exact (lt_irrefl (v 4 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h0_3)) (le_of_eq h5_2.symm)) (le_of_eq h4_5.symm)) h6_8)
            · rcases c5 with ⟨h5_0,h5_1,h5_2,h5_3,h5_4,h5_5,h5_6,h5_7,h5_8,h5_9,h5_10⟩
              exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h3_6 (le_of_eq h3_0)) (le_of_eq h6_0.symm)) (le_of_eq h0_0)) (le_of_eq h5_0.symm)) (le_of_eq h4_4.symm)) (le_of_eq h6_4)) (le_of_eq h3_4.symm))
            · rcases c5 with ⟨h5_0,h5_1,h5_2,h5_3,h5_4,h5_5,h5_6,h5_7,h5_8,h5_9,h5_10⟩
              exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h0_9) (le_of_eq h6_2)) (le_of_eq h4_2.symm)) h2_10) (le_of_eq h4_3)) (le_of_eq h5_2.symm)) (le_of_eq h0_5.symm))
            · rcases c5 with ⟨h5_0,h5_1,h5_2,h5_3,h5_4,h5_5,h5_6,h5_7,h5_8,h5_9,h5_10⟩
              rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
              · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
                exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h0_0)) (le_of_eq h5_0.symm)) h5_7) (le_of_eq h4_0.symm)) h8_2)
              · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
                exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_7) h4_8) (le_of_eq h8_0.symm))
              · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
                exact (lt_irrefl (v 3 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h8_3 (le_of_eq h0_5)) (le_of_eq h5_5.symm)) (le_of_eq h4_0.symm))
              · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
                exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h0_0)) (le_of_eq h5_0.symm)) h5_7) (le_of_eq h4_0.symm)) (le_of_eq h8_0.symm))
              · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
                exact (lt_irrefl (v 3 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_10 (le_of_eq h8_1)) (le_of_eq h0_2.symm)) (le_of_eq h6_2)) (le_of_eq h4_2.symm))
              · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
                exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h0_0)) (le_of_eq h5_0.symm)) h5_7) (le_of_eq h4_0.symm)) (le_of_eq h8_0))
            · rcases c5 with ⟨h5_0,h5_1,h5_2,h5_3,h5_4,h5_5,h5_6,h5_7,h5_8,h5_9,h5_10⟩
              exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h3_7 (le_of_eq h3_5)) (le_of_eq h6_5.symm)) (le_of_eq h4_5)) (le_of_eq h5_5.symm)) h5_8) (le_of_eq h0_0.symm)) (le_of_eq h6_0)) (le_of_eq h3_0.symm))
            · rcases c5 with ⟨h5_0,h5_1,h5_2,h5_3,h5_4,h5_5,h5_6,h5_7,h5_8,h5_9,h5_10⟩
              exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h3_7 (le_of_eq h3_5)) (le_of_eq h6_5.symm)) (le_of_eq h4_5)) (le_of_eq h5_5.symm)) (le_of_eq h0_0.symm)) (le_of_eq h6_0)) (le_of_eq h3_0.symm))
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 4 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) (le_of_eq h3_2)) (le_of_eq h2_2.symm)) (le_of_eq h4_1.symm)) h6_8)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans h0_8 h6_8) (le_of_eq h3_0.symm)) h1_7)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 1 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_8 (le_of_eq h2_1)) (le_of_eq h3_1.symm)) (le_of_eq h1_1)) (le_of_eq h0_1.symm)) (le_of_eq h6_5)) (le_of_eq h3_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) (le_of_eq h3_4.symm)) h3_6) h1_7)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_8 h0_9) (le_of_eq h6_5.symm)) (le_of_eq h3_0.symm)) h1_7)
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_5)) (le_of_eq h2_1.symm)) h2_9) h2_10) (le_of_eq h2_3)) (le_of_eq h7_2.symm)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_6 (le_of_eq h3_4)) (le_of_eq h2_4)) (le_of_eq h7_4.symm)) h7_6) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h7_2.symm)) (le_of_eq h2_5.symm)) (le_of_eq h3_0.symm)) h3_7) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_6 (le_of_eq h3_4)) (le_of_eq h2_4)) (le_of_eq h7_4.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 3 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_10 (le_of_eq h2_3)) (le_of_eq h7_3)) (le_of_eq h1_3.symm)) (le_of_eq h3_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h2_2.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_6 (le_of_eq h3_4)) (le_of_eq h2_4)) (le_of_eq h7_4)) (le_of_eq h1_4.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) h1_10) (le_of_eq h3_3)) (le_of_eq h2_2.symm)) (le_of_eq h8_0.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) h1_10) (le_of_eq h3_3)) (le_of_eq h2_2.symm)) h8_4)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 9 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h3_3)) (le_of_eq h2_2.symm)) (le_of_eq h8_1)) (le_of_eq h1_2.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) h1_10) (le_of_eq h3_3)) (le_of_eq h2_2.symm)) (le_of_eq h8_1.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h1_7 (le_of_eq h8_0.symm)) h2_7) (le_of_eq h3_0.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 9 2)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h3_3)) (le_of_eq h2_2.symm)) h2_10) h8_6) (le_of_eq h1_2.symm))
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_0.symm)) h2_6) h7_6) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_0.symm)) h2_6) (le_of_eq h7_4.symm)) h7_6) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_0.symm)) h2_6) h7_7) (le_of_eq h1_0.symm)) h1_7)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_0.symm)) h2_6) (le_of_eq h7_4.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_0.symm)) h2_6) (le_of_eq h7_0)) (le_of_eq h1_0.symm)) h1_7)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_0.symm)) h2_6) (le_of_eq h7_4)) (le_of_eq h1_4.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h3_8) h2_8) h7_8) (le_of_eq h1_0.symm)) h3_6) h2_6) h7_6) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h3_8) h2_8) (le_of_eq h7_0.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h3_8) h2_8) (le_of_eq h7_1)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h3_8) h2_8) h2_9) (le_of_eq h7_5.symm)) (le_of_eq h1_0.symm)) h3_6) h2_6) (le_of_eq h7_4.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 1 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h2_6 (le_of_eq h7_0)) (le_of_eq h1_0.symm)) h3_6)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h3_8) h2_8) (le_of_eq h7_5)) (le_of_eq h1_5.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h1_9) (le_of_eq h3_5.symm)) h2_8) h7_8) (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h2_6) h7_6) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h1_9) (le_of_eq h3_5.symm)) h2_8) (le_of_eq h7_0.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) (le_of_eq h3_5.symm)) h2_8) (le_of_eq h7_1)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h1_9) (le_of_eq h3_5.symm)) h2_8) h2_9) (le_of_eq h7_5.symm)) (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h2_6) (le_of_eq h7_4.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_6 (le_of_eq h7_0)) (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) (le_of_eq h3_5.symm)) h2_8) (le_of_eq h7_5)) (le_of_eq h1_5.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c11 with c11 | c11 | c11 | c11 | c11 | c11
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) (le_of_eq h3_2)) (le_of_eq h2_2.symm)) (le_of_eq h11_0.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_7 h1_8) (le_of_eq h3_1)) (le_of_eq h2_1.symm)) (le_of_eq h11_0.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h11_0.symm)) (le_of_eq h2_1)) (le_of_eq h3_1.symm)) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) (le_of_eq h3_2)) (le_of_eq h2_2.symm)) (le_of_eq h11_1.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_9 h11_4) (le_of_eq h2_1)) (le_of_eq h3_1.symm)) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h11_1.symm)) (le_of_eq h2_1)) (le_of_eq h3_1.symm)) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_5)) (le_of_eq h2_1.symm)) h7_8) (le_of_eq h1_0.symm)) (le_of_eq h3_4)) h2_6) h7_6) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_5)) (le_of_eq h2_1.symm)) (le_of_eq h7_0.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_5)) (le_of_eq h2_1.symm)) (le_of_eq h7_1)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_5)) (le_of_eq h2_1.symm)) h2_9) (le_of_eq h7_5.symm)) (le_of_eq h1_0.symm)) (le_of_eq h3_4)) h2_6) (le_of_eq h7_4.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_6 (le_of_eq h7_0)) (le_of_eq h1_0.symm)) (le_of_eq h3_4))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_5)) (le_of_eq h2_1.symm)) (le_of_eq h7_5)) (le_of_eq h1_5.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_9 (le_of_eq h0_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h3_3)) (le_of_eq h2_2.symm)) h2_10) (le_of_eq h2_3)) (le_of_eq h8_1.symm)) (le_of_eq h0_1.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 9 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h3_3)) (le_of_eq h2_2.symm)) h2_10) (le_of_eq h2_3)) (le_of_eq h8_1.symm)) (le_of_eq h1_2.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h8_0.symm)) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h3_0.symm)) h1_7)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h8_1)) (le_of_eq h2_5.symm)) (le_of_eq h3_0.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) h8_4) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h3_0.symm)) h1_7)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h8_1.symm)) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h3_0.symm)) h1_7)
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_0.symm)) (le_of_eq h2_4.symm)) h7_6) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_0.symm)) (le_of_eq h2_4.symm)) (le_of_eq h7_4.symm)) h7_6) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_0.symm)) (le_of_eq h2_4.symm)) h7_7) (le_of_eq h1_0.symm)) h1_7)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_0.symm)) (le_of_eq h2_4.symm)) (le_of_eq h7_4.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_0.symm)) (le_of_eq h2_4.symm)) (le_of_eq h7_0)) (le_of_eq h1_0.symm)) h1_7)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_0.symm)) (le_of_eq h2_4.symm)) (le_of_eq h7_4)) (le_of_eq h1_4.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h3_8) (le_of_eq h2_0.symm)) h2_7) h7_8) (le_of_eq h1_0.symm)) h3_6) (le_of_eq h2_4.symm)) h7_6) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h3_8) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h7_0.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h3_8) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h7_1)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h3_8) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h7_0.symm)) h7_7) (le_of_eq h1_0.symm)) h3_6) (le_of_eq h2_4.symm)) (le_of_eq h7_4.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 7 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h2_8 (le_of_eq h2_1)) h7_10) (le_of_eq h7_3)) (le_of_eq h1_3.symm)) (le_of_eq h3_2.symm)) (le_of_eq h2_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h3_8) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h7_5)) (le_of_eq h1_5.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h1_9) (le_of_eq h3_5.symm)) (le_of_eq h2_0.symm)) h2_7) h7_8) (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h2_4.symm)) h7_6) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h1_9) (le_of_eq h3_5.symm)) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h7_0.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) (le_of_eq h3_5.symm)) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h7_1)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h1_9) (le_of_eq h3_5.symm)) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h7_0.symm)) h7_7) (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h2_4.symm)) (le_of_eq h7_4.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 3 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h2_10 (le_of_eq h2_3)) (le_of_eq h3_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_3)) (le_of_eq h7_3.symm)) (le_of_eq h2_2.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) (le_of_eq h3_5.symm)) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h7_5)) (le_of_eq h1_5.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_1)) (le_of_eq h2_5.symm)) h7_8) (le_of_eq h1_0.symm)) h1_7)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_1)) (le_of_eq h2_5.symm)) (le_of_eq h7_0.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_1)) (le_of_eq h2_5.symm)) (le_of_eq h7_1)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_1)) (le_of_eq h2_5.symm)) (le_of_eq h7_0.symm)) h7_7) (le_of_eq h1_0.symm)) h1_7)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 9 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h7_3.symm)) (le_of_eq h2_2.symm)) h2_10) (le_of_eq h2_3)) (le_of_eq h3_2.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_1)) (le_of_eq h2_5.symm)) (le_of_eq h7_5)) (le_of_eq h1_5.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_5)) (le_of_eq h2_5.symm)) h2_8) h8_4)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_5)) (le_of_eq h2_5.symm)) h2_8) (le_of_eq h8_0.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 7 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_8 (le_of_eq h8_0)) (le_of_eq h1_1.symm)) (le_of_eq h3_5)) (le_of_eq h2_5.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_5)) (le_of_eq h2_5.symm)) h2_8) h8_3)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 9 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h1_10 (le_of_eq h3_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h2_3.symm)) (le_of_eq h8_1)) (le_of_eq h1_2.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_6 (le_of_eq h3_4)) (le_of_eq h2_4.symm)) h2_6) (le_of_eq h8_0))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          rcases c9 with c9 | c9 | c9 | c9 | c9 | c9
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 4 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h0_3)) (le_of_eq h9_1.symm)) (le_of_eq h3_5.symm)) h6_8)
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h1_7 (le_of_eq h0_5)) h9_4) (le_of_eq h3_0.symm))
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) h1_10) (le_of_eq h3_3)) (le_of_eq h9_1.symm)) (le_of_eq h0_5.symm))
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h0_5)) (le_of_eq h9_1.symm)) (le_of_eq h3_0.symm))
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_6 (le_of_eq h3_0)) (le_of_eq h9_0.symm)) (le_of_eq h0_4.symm))
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h6_7 (le_of_eq h3_5)) (le_of_eq h9_1.symm)) (le_of_eq h0_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3)) (le_of_eq h3_2.symm)) (le_of_eq h1_2)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_9 (le_of_eq h6_1.symm)) h3_8) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) h6_10) (le_of_eq h6_3)) (le_of_eq h3_2.symm)) (le_of_eq h1_2)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) h3_6) h1_7)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_9 (le_of_eq h6_5.symm)) h3_8) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_0.symm)) (le_of_eq h2_4.symm)) h2_6) h7_6) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_0.symm)) (le_of_eq h2_4.symm)) h2_6) (le_of_eq h7_4.symm)) h7_6) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_0.symm)) (le_of_eq h2_4.symm)) h2_6) h7_7) (le_of_eq h1_0.symm)) h1_7)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_0.symm)) (le_of_eq h2_4.symm)) h2_6) (le_of_eq h7_4.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_0.symm)) (le_of_eq h2_4.symm)) h2_6) (le_of_eq h7_0)) (le_of_eq h1_0.symm)) h1_7)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_0.symm)) (le_of_eq h2_4.symm)) h2_6) (le_of_eq h7_4)) (le_of_eq h1_4.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h3_8) (le_of_eq h2_0.symm)) h7_6) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h3_8) (le_of_eq h2_0.symm)) (le_of_eq h7_4.symm)) h7_6) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h3_8) (le_of_eq h2_0.symm)) h7_7) (le_of_eq h1_0.symm)) h1_7)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h3_8) (le_of_eq h2_0.symm)) (le_of_eq h7_4.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h3_8) (le_of_eq h2_0.symm)) (le_of_eq h7_0)) (le_of_eq h1_0.symm)) h1_7)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h3_8) (le_of_eq h2_0.symm)) (le_of_eq h7_4)) (le_of_eq h1_4.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h1_9) (le_of_eq h3_5.symm)) (le_of_eq h2_0.symm)) h7_6) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h1_9) (le_of_eq h3_5.symm)) (le_of_eq h2_0.symm)) (le_of_eq h7_4.symm)) h7_6) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) (le_of_eq h3_5.symm)) (le_of_eq h2_0.symm)) h7_7) (le_of_eq h1_0.symm)) h1_7)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h1_9) (le_of_eq h3_5.symm)) (le_of_eq h2_0.symm)) (le_of_eq h7_4.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) (le_of_eq h3_5.symm)) (le_of_eq h2_0.symm)) (le_of_eq h7_0)) (le_of_eq h1_0.symm)) h1_7)
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans h0_6 h0_7) h1_8) h1_9) (le_of_eq h3_5.symm)) (le_of_eq h2_0.symm)) (le_of_eq h7_4)) (le_of_eq h1_4.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_1)) (le_of_eq h2_5.symm)) h2_8) h7_8) (le_of_eq h1_0.symm)) h3_7) (le_of_eq h2_0.symm)) h7_6) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_1)) (le_of_eq h2_5.symm)) h2_8) (le_of_eq h7_0.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_1)) (le_of_eq h2_5.symm)) h2_8) (le_of_eq h7_1)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_1)) (le_of_eq h2_5.symm)) h2_8) h2_9) (le_of_eq h7_5.symm)) (le_of_eq h1_0.symm)) h3_7) (le_of_eq h2_0.symm)) (le_of_eq h7_4.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 9 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h7_3.symm)) (le_of_eq h2_3)) (le_of_eq h3_2.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_1)) (le_of_eq h2_5.symm)) h2_8) (le_of_eq h7_5)) (le_of_eq h1_5.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c7 with c7 | c7 | c7 | c7 | c7 | c7
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_5)) (le_of_eq h2_5.symm)) h2_8) h7_8) (le_of_eq h1_0.symm)) (le_of_eq h3_4)) (le_of_eq h2_4.symm)) h2_6) h7_6) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_5)) (le_of_eq h2_5.symm)) h2_8) (le_of_eq h7_0.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_5)) (le_of_eq h2_5.symm)) h2_8) (le_of_eq h7_1)) (le_of_eq h1_5.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h0_7) h1_8) (le_of_eq h3_5)) (le_of_eq h2_5.symm)) h2_8) h2_9) (le_of_eq h7_5.symm)) (le_of_eq h1_0.symm)) (le_of_eq h3_4)) (le_of_eq h2_4.symm)) h2_6) (le_of_eq h7_4.symm)) (le_of_eq h1_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 3 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_6 (le_of_eq h7_0)) (le_of_eq h1_0.symm)) (le_of_eq h3_4)) (le_of_eq h2_4.symm))
        · rcases c7 with ⟨h7_0,h7_1,h7_2,h7_3,h7_4,h7_5,h7_6,h7_7,h7_8,h7_9,h7_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) (le_of_eq h3_5)) (le_of_eq h2_5.symm)) h2_8) (le_of_eq h7_5)) (le_of_eq h1_5.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          rcases c9 with c9 | c9 | c9 | c9 | c9 | c9
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 4 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_9 h0_10) (le_of_eq h0_3)) (le_of_eq h9_1.symm)) (le_of_eq h3_5.symm)) h6_8)
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h1_7 (le_of_eq h0_5)) h9_4) (le_of_eq h3_0.symm))
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_1.symm)) h1_9) h1_10) (le_of_eq h3_3)) (le_of_eq h9_1.symm)) (le_of_eq h0_5.symm))
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_7 (le_of_eq h0_5)) (le_of_eq h9_1.symm)) (le_of_eq h3_0.symm))
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_6 (le_of_eq h3_0)) (le_of_eq h9_0.symm)) (le_of_eq h0_4.symm))
          · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
            exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h6_7 (le_of_eq h3_5)) (le_of_eq h9_1.symm)) (le_of_eq h0_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3)) (le_of_eq h3_2.symm)) (le_of_eq h1_2)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_9 (le_of_eq h6_1.symm)) h3_8) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) h6_10) (le_of_eq h6_3)) (le_of_eq h3_2.symm)) (le_of_eq h1_2)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) h3_6) h1_7)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_9 (le_of_eq h6_5.symm)) h3_8) (le_of_eq h1_1)) (le_of_eq h0_1.symm))
  · rcases c1 with ⟨h1_0,h1_1,h1_2,h1_3,h1_4,h1_5,h1_6,h1_7,h1_8,h1_9,h1_10⟩
    rcases c2 with c2 | c2 | c2 | c2 | c2 | c2
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_5.symm)) h6_8) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) h3_7) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4)) (le_of_eq h1_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          rcases c4 with c4 | c4 | c4 | c4 | c4 | c4
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h2_7 (le_of_eq h4_5)) (le_of_eq h6_5.symm)) (le_of_eq h3_0.symm))
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) h3_8) (le_of_eq h2_1)) (le_of_eq h4_5.symm)) (le_of_eq h6_0.symm))
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3)) (le_of_eq h4_3.symm)) (le_of_eq h2_2.symm)) h2_10) (le_of_eq h3_3)) (le_of_eq h6_2.symm))
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) h2_7) (le_of_eq h4_0.symm)) (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) (le_of_eq h1_4))
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3)) (le_of_eq h4_2.symm)) (le_of_eq h2_1.symm)) h2_9) h2_10) (le_of_eq h3_3)) (le_of_eq h6_2.symm))
          · rcases c4 with ⟨h4_0,h4_1,h4_2,h4_3,h4_4,h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩
            exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) h3_8) (le_of_eq h2_1)) (le_of_eq h4_1.symm)) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 10 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h6_8 (le_of_eq h0_1)) (le_of_eq h1_5.symm)) (le_of_eq h3_5)) (le_of_eq h6_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) (le_of_eq h1_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3.symm)) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_1.symm)) h6_8) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) h3_8) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_1.symm)) h3_9) (le_of_eq h6_5.symm)) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) h6_8) (le_of_eq h3_1)) (le_of_eq h1_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) (le_of_eq h3_1)) (le_of_eq h1_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_2)) (le_of_eq h3_2.symm)) (le_of_eq h1_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3)) (le_of_eq h3_2.symm)) (le_of_eq h1_1.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) (le_of_eq h1_4))
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_5.symm)) h6_8) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) h3_7) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4)) (le_of_eq h1_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c11 with c11 | c11 | c11 | c11 | c11 | c11
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_1.symm)) (le_of_eq h2_1)) (le_of_eq h11_0.symm)) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h11_1)) (le_of_eq h2_2.symm)) (le_of_eq h3_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h11_1.symm)) (le_of_eq h2_1.symm)) h2_9) (le_of_eq h3_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_10 h11_6) (le_of_eq h2_2.symm)) (le_of_eq h3_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h11_1.symm)) (le_of_eq h2_2.symm)) (le_of_eq h3_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h11_1.symm)) h2_8) (le_of_eq h3_1)) (le_of_eq h1_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3.symm)) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_1.symm)) h6_8) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) h3_8) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_1.symm)) h3_9) (le_of_eq h6_5.symm)) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) h6_8) (le_of_eq h3_1)) (le_of_eq h1_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) (le_of_eq h3_1)) (le_of_eq h1_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_2)) (le_of_eq h3_2.symm)) (le_of_eq h1_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3)) (le_of_eq h3_2.symm)) (le_of_eq h1_1.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) (le_of_eq h1_4))
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_5.symm)) h6_8) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) h3_7) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4)) (le_of_eq h1_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c11 with c11 | c11 | c11 | c11 | c11 | c11
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_1.symm)) (le_of_eq h2_5)) (le_of_eq h11_0.symm)) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_1.symm)) (le_of_eq h2_5)) h11_4) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h11_1.symm)) (le_of_eq h2_5.symm)) (le_of_eq h3_1)) (le_of_eq h1_1.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_1.symm)) (le_of_eq h2_5)) (le_of_eq h11_1.symm)) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) h11_4) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h3_1)) (le_of_eq h1_1.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h11_1.symm)) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h3_1)) (le_of_eq h1_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3.symm)) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_1.symm)) h6_8) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) h3_8) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_1.symm)) h3_9) (le_of_eq h6_5.symm)) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) h6_8) (le_of_eq h3_1)) (le_of_eq h1_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) (le_of_eq h3_1)) (le_of_eq h1_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_2)) (le_of_eq h3_2.symm)) (le_of_eq h1_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3)) (le_of_eq h3_2.symm)) (le_of_eq h1_1.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) (le_of_eq h1_4))
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_5.symm)) h6_8) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) h3_7) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4)) (le_of_eq h1_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c11 with c11 | c11 | c11 | c11 | c11 | c11
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_1.symm)) h2_8) h11_4) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) h3_8) h2_8) (le_of_eq h11_0.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 5 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h11_0.symm)) (le_of_eq h2_1)) (le_of_eq h3_2)) (le_of_eq h1_2.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_1.symm)) h2_8) h11_3) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 5 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h0_2.symm)) h11_4) (le_of_eq h2_1)) (le_of_eq h3_2)) (le_of_eq h1_2.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 5 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h11_1.symm)) (le_of_eq h2_1)) (le_of_eq h3_2)) (le_of_eq h1_2.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3.symm)) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_1.symm)) h6_8) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) h3_8) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_1.symm)) h3_9) (le_of_eq h6_5.symm)) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) h6_8) (le_of_eq h3_1)) (le_of_eq h1_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) (le_of_eq h3_1)) (le_of_eq h1_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_2)) (le_of_eq h3_2.symm)) (le_of_eq h1_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3)) (le_of_eq h3_2.symm)) (le_of_eq h1_1.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) (le_of_eq h1_4))
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_5.symm)) h6_8) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) h3_7) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4)) (le_of_eq h1_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_0.symm)) h1_7) h3_8) (le_of_eq h2_0.symm)) h8_2)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_0.symm)) h1_7) h3_8) (le_of_eq h2_0.symm)) h8_2)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_5.symm)) h3_8) (le_of_eq h2_0.symm)) h8_3)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_0.symm)) h1_7) h3_8) (le_of_eq h2_0.symm)) (le_of_eq h8_0.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_5.symm)) h3_8) (le_of_eq h2_0.symm)) (le_of_eq h8_0))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_0.symm)) h1_7) h3_8) (le_of_eq h2_0.symm)) (le_of_eq h8_0))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3.symm)) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_1.symm)) h6_8) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) h3_8) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_1.symm)) h3_9) (le_of_eq h6_5.symm)) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) h6_8) (le_of_eq h3_1)) (le_of_eq h1_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) (le_of_eq h3_1)) (le_of_eq h1_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_2)) (le_of_eq h3_2.symm)) (le_of_eq h1_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3)) (le_of_eq h3_2.symm)) (le_of_eq h1_1.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) (le_of_eq h1_4))
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_5.symm)) h6_8) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) h3_7) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4)) (le_of_eq h1_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c11 with c11 | c11 | c11 | c11 | c11 | c11
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) h3_8) (le_of_eq h2_0.symm)) h11_2)
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) h3_8) (le_of_eq h2_0.symm)) h11_2)
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_1.symm)) (le_of_eq h2_0.symm)) h11_3) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) h3_8) (le_of_eq h2_0.symm)) (le_of_eq h11_0.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_1.symm)) (le_of_eq h2_0.symm)) (le_of_eq h11_0)) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c11 with ⟨h11_0,h11_1,h11_2,h11_3,h11_4,h11_5,h11_6⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) h3_8) (le_of_eq h2_0.symm)) (le_of_eq h11_0))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3.symm)) (le_of_eq h3_3)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) (le_of_eq h3_0.symm)) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h0_6 h6_7) (le_of_eq h3_0.symm)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_0)) (le_of_eq h3_0.symm)) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h1_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_1.symm)) h6_8) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h1_7) h3_8) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_2)) (le_of_eq h1_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h1_1)) (le_of_eq h3_1.symm)) h3_9) (le_of_eq h6_5.symm)) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) h6_8) (le_of_eq h3_1)) (le_of_eq h1_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) (le_of_eq h3_1)) (le_of_eq h1_1.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_2)) (le_of_eq h3_2.symm)) (le_of_eq h1_1.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3)) (le_of_eq h3_2.symm)) (le_of_eq h1_1.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans h0_6 h6_6) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4)) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h6_6) h3_6) (le_of_eq h1_4))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_6 (le_of_eq h6_4.symm)) h3_6) (le_of_eq h1_4))
  · rcases c1 with ⟨h1_0,h1_1,h1_2,h1_3,h1_4,h1_5,h1_6,h1_7,h1_8,h1_9,h1_10⟩
    rcases c2 with c2 | c2 | c2 | c2 | c2 | c2
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_1.symm)) h2_9) h2_10) (le_of_eq h3_3)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) (le_of_eq h3_4)) (le_of_eq h1_0))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_5.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h1_0))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3.symm)) (le_of_eq h3_3)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c9 with c9 | c9 | c9 | c9 | c9 | c9
        · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h0_3)) (le_of_eq h9_1.symm)) h2_10) (le_of_eq h3_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h0_3)) (le_of_eq h9_1.symm)) (le_of_eq h3_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_7) h9_4) (le_of_eq h0_0.symm))
        · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
          exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h3_7 (le_of_eq h9_1)) (le_of_eq h0_5.symm)) (le_of_eq h1_0.symm))
        · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_0.symm)) h3_7) (le_of_eq h9_0.symm)) (le_of_eq h0_4.symm))
        · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_7) h9_3) (le_of_eq h0_0.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_2)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 2)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) h6_8) (le_of_eq h3_1))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h3_1)) (le_of_eq h6_1.symm)) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_7) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_1.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) h6_10) (le_of_eq h6_3)) (le_of_eq h3_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) h3_6) (le_of_eq h1_0))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) h3_8)
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_1.symm)) h2_9) h2_10) (le_of_eq h3_3)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) (le_of_eq h3_4)) (le_of_eq h1_0))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_5.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h1_0))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3.symm)) (le_of_eq h3_3)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_8 h1_9) (le_of_eq h3_2)) (le_of_eq h2_3)) (le_of_eq h8_1.symm)) (le_of_eq h1_5.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 9 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h8_1)) (le_of_eq h2_3.symm)) (le_of_eq h3_2.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h8_0.symm)) (le_of_eq h2_0.symm)) h3_6) (le_of_eq h1_0))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 9 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) h8_6) (le_of_eq h2_3.symm)) (le_of_eq h3_2.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) h8_4) (le_of_eq h2_0.symm)) h3_6) (le_of_eq h1_0))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h8_1.symm)) (le_of_eq h2_0.symm)) h3_6) (le_of_eq h1_0))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_2)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 2)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) h6_8) (le_of_eq h3_1))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h3_1)) (le_of_eq h6_1.symm)) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_7) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_1.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) h6_10) (le_of_eq h6_3)) (le_of_eq h3_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) h3_6) (le_of_eq h1_0))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) h3_8)
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_1.symm)) h3_9) h3_10) (le_of_eq h3_3)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) (le_of_eq h3_4)) (le_of_eq h1_0))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_5.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h1_0))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3.symm)) (le_of_eq h3_3)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c9 with c9 | c9 | c9 | c9 | c9 | c9
        · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h0_3)) (le_of_eq h9_1.symm)) (le_of_eq h3_1.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h0_3)) (le_of_eq h9_1.symm)) (le_of_eq h3_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_7) h9_4) (le_of_eq h0_0.symm))
        · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
          exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h3_7 (le_of_eq h9_1)) (le_of_eq h0_5.symm)) (le_of_eq h1_0.symm))
        · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_0.symm)) h3_7) (le_of_eq h9_0.symm)) (le_of_eq h0_4.symm))
        · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_7) h9_3) (le_of_eq h0_0.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_2)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 2)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) h6_8) (le_of_eq h3_1))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h3_1)) (le_of_eq h6_1.symm)) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_7) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_1.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) h6_10) (le_of_eq h6_3)) (le_of_eq h3_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) h3_6) (le_of_eq h1_0))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) h3_8)
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_1.symm)) h3_9) h3_10) (le_of_eq h3_3)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) (le_of_eq h3_4)) (le_of_eq h1_0))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_5.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h1_0))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3.symm)) (le_of_eq h3_3)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c9 with c9 | c9 | c9 | c9 | c9 | c9
        · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h0_3)) (le_of_eq h9_1.symm)) (le_of_eq h3_1.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h0_3)) (le_of_eq h9_1.symm)) (le_of_eq h3_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_7) h9_4) (le_of_eq h0_0.symm))
        · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
          exact (lt_irrefl (v 9 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h3_7 (le_of_eq h9_1)) (le_of_eq h0_5.symm)) (le_of_eq h1_0.symm))
        · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_0.symm)) h3_7) (le_of_eq h9_0.symm)) (le_of_eq h0_4.symm))
        · rcases c9 with ⟨h9_0,h9_1,h9_2,h9_3,h9_4,h9_5,h9_6⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_7) h9_3) (le_of_eq h0_0.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_2)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 2)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) h6_8) (le_of_eq h3_1))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h3_1)) (le_of_eq h6_1.symm)) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_7) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_1.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) h6_10) (le_of_eq h6_3)) (le_of_eq h3_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) h3_6) (le_of_eq h1_0))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) h3_8)
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_1.symm)) h3_9) h3_10) (le_of_eq h3_3)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) (le_of_eq h3_4)) (le_of_eq h1_0))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_5.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h1_0))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3.symm)) (le_of_eq h3_3)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_0.symm)) h3_7) (le_of_eq h2_0.symm)) h8_2)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_0.symm)) h3_7) (le_of_eq h2_0.symm)) h8_2)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h3_1)) (le_of_eq h2_5.symm)) h2_8) (le_of_eq h8_0)) (le_of_eq h1_5.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_0.symm)) h3_7) (le_of_eq h2_0.symm)) (le_of_eq h8_0.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 9 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h8_1.symm)) (le_of_eq h2_3)) (le_of_eq h3_2.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_0.symm)) h3_7) (le_of_eq h2_0.symm)) (le_of_eq h8_0))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_2)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 2)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) h6_8) (le_of_eq h3_1))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h3_1)) (le_of_eq h6_1.symm)) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_7) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_1.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) h6_10) (le_of_eq h6_3)) (le_of_eq h3_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) h3_6) (le_of_eq h1_0))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) h3_8)
    · rcases c2 with ⟨h2_0,h2_1,h2_2,h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩
      rcases c3 with c3 | c3 | c3 | c3 | c3 | c3
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_1.symm)) h3_9) h3_10) (le_of_eq h3_3)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) (le_of_eq h3_4)) (le_of_eq h1_0))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_5.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) (le_of_eq h3_4.symm)) (le_of_eq h1_0))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4)) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) h3_10) (le_of_eq h3_3)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_3.symm)) (le_of_eq h3_3)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) (le_of_eq h3_4.symm)) h3_6) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c8 with c8 | c8 | c8 | c8 | c8 | c8
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_5.symm)) h1_8) (le_of_eq h3_1)) (le_of_eq h2_5.symm)) h8_4)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans h0_6 h0_7) (le_of_eq h1_0.symm)) h3_7) (le_of_eq h2_0.symm)) h2_7) (le_of_eq h8_0.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h3_1)) (le_of_eq h2_5.symm)) (le_of_eq h8_0)) (le_of_eq h1_5.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_8 (le_of_eq h0_1)) (le_of_eq h1_5.symm)) h1_8) (le_of_eq h3_1)) (le_of_eq h2_5.symm)) h8_3)
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 9 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h8_1.symm)) (le_of_eq h2_2.symm)) h2_10) (le_of_eq h2_3)) (le_of_eq h3_2.symm))
        · rcases c8 with ⟨h8_0,h8_1,h8_2,h8_3,h8_4,h8_5,h8_6⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h3_1)) (le_of_eq h2_5.symm)) (le_of_eq h8_1)) (le_of_eq h1_5.symm))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) (le_of_eq h6_4.symm)) h6_6)
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_2)) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) (le_of_eq h6_4.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 2)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_10 (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) h6_8) (le_of_eq h3_1))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_6) (le_of_eq h6_4))
      · rcases c3 with ⟨h3_0,h3_1,h3_2,h3_3,h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩
        rcases c6 with c6 | c6 | c6 | c6 | c6 | c6
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 5 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le h1_8 (le_of_eq h3_1)) (le_of_eq h6_1.symm)) (le_of_eq h0_1)) (le_of_eq h1_5.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_7 (le_of_eq h1_0.symm)) h3_7) (le_of_eq h6_0.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) (le_of_eq h3_1.symm)) h1_9) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 4 2)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_10 (le_of_eq h6_2.symm)) h6_10) (le_of_eq h6_3)) (le_of_eq h3_2.symm)) h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le h0_8 (le_of_eq h6_0.symm)) h3_6) (le_of_eq h1_0))
        · rcases c6 with ⟨h6_0,h6_1,h6_2,h6_3,h6_4,h6_5,h6_6,h6_7,h6_8,h6_9,h6_10⟩
          exact (lt_irrefl (v 9 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans h1_9 h1_10) (le_of_eq h1_3)) (le_of_eq h0_2.symm)) (le_of_eq h6_5.symm)) h3_8)

end Erdos595OrderedQuadRight
