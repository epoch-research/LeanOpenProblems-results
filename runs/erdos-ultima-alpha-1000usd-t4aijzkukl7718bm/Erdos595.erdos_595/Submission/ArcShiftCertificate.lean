import Submission.ArcAdjoint
import Submission.MiddleCornerObstruction

/-!
An exact symbolic certificate excluding a homomorphism from the arc graph
of K4 into the shift-square graph, over ANY linear order. All branches end
in explicit transitivity contradictions. There is no numerical search
assumption in the Lean theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 4096

open SimpleGraph
namespace Erdos595ArcShift
open Erdos595ArcAdjoint Erdos595MiddleCorner

private theorem symbolic_certificate (A : Type*) [LinearOrder A]
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 : A)
    (b0 : x0 < x1)
    (b1 : x3 < x4)
    (b2 : x6 < x7)
    (b3 : x9 < x10)
    (b4 : x12 < x13)
    (b5 : x15 < x16)
    (b6 : x18 < x19)
    (b7 : x21 < x22)
    (b8 : x24 < x25)
    (b9 : x27 < x28)
    (b10 : x30 < x31)
    (b11 : x33 < x34)
    (b12 : x1 < x2)
    (b13 : x4 < x5)
    (b14 : x7 < x8)
    (b15 : x10 < x11)
    (b16 : x13 < x14)
    (b17 : x16 < x17)
    (b18 : x19 < x20)
    (b19 : x22 < x23)
    (b20 : x25 < x26)
    (b21 : x28 < x29)
    (b22 : x31 < x32)
    (b23 : x34 < x35)
    (b24 : x0 < x9)
    (b25 : x0 < x12)
    (b26 : x0 < x15)
    (b27 : x0 < x18)
    (b28 : x0 < x27)
    (h0 : (x1 = x9 ∧ x2 = x10 ∨ x2 = x9) ∨
      (x10 = x0 ∧ x11 = x1 ∨ x11 = x0))
    (h1 : (x1 = x12 ∧ x2 = x13 ∨ x2 = x12) ∨
      (x13 = x0 ∧ x14 = x1 ∨ x14 = x0))
    (h2 : (x1 = x15 ∧ x2 = x16 ∨ x2 = x15) ∨
      (x16 = x0 ∧ x17 = x1 ∨ x17 = x0))
    (h3 : (x1 = x18 ∧ x2 = x19 ∨ x2 = x18) ∨
      (x19 = x0 ∧ x20 = x1 ∨ x20 = x0))
    (h4 : (x1 = x27 ∧ x2 = x28 ∨ x2 = x27) ∨
      (x28 = x0 ∧ x29 = x1 ∨ x29 = x0))
    (h5 : (x4 = x9 ∧ x5 = x10 ∨ x5 = x9) ∨
      (x10 = x3 ∧ x11 = x4 ∨ x11 = x3))
    (h6 : (x4 = x18 ∧ x5 = x19 ∨ x5 = x18) ∨
      (x19 = x3 ∧ x20 = x4 ∨ x20 = x3))
    (h7 : (x4 = x21 ∧ x5 = x22 ∨ x5 = x21) ∨
      (x22 = x3 ∧ x23 = x4 ∨ x23 = x3))
    (h8 : (x4 = x24 ∧ x5 = x25 ∨ x5 = x24) ∨
      (x25 = x3 ∧ x26 = x4 ∨ x26 = x3))
    (h9 : (x4 = x27 ∧ x5 = x28 ∨ x5 = x27) ∨
      (x28 = x3 ∧ x29 = x4 ∨ x29 = x3))
    (h10 : (x7 = x9 ∧ x8 = x10 ∨ x8 = x9) ∨
      (x10 = x6 ∧ x11 = x7 ∨ x11 = x6))
    (h11 : (x7 = x18 ∧ x8 = x19 ∨ x8 = x18) ∨
      (x19 = x6 ∧ x20 = x7 ∨ x20 = x6))
    (h12 : (x7 = x27 ∧ x8 = x28 ∨ x8 = x27) ∨
      (x28 = x6 ∧ x29 = x7 ∨ x29 = x6))
    (h13 : (x7 = x30 ∧ x8 = x31 ∨ x8 = x30) ∨
      (x31 = x6 ∧ x32 = x7 ∨ x32 = x6))
    (h14 : (x7 = x33 ∧ x8 = x34 ∨ x8 = x33) ∨
      (x34 = x6 ∧ x35 = x7 ∨ x35 = x6))
    (h15 : (x10 = x21 ∧ x11 = x22 ∨ x11 = x21) ∨
      (x22 = x9 ∧ x23 = x10 ∨ x23 = x9))
    (h16 : (x10 = x30 ∧ x11 = x31 ∨ x11 = x30) ∨
      (x31 = x9 ∧ x32 = x10 ∨ x32 = x9))
    (h17 : (x13 = x18 ∧ x14 = x19 ∨ x14 = x18) ∨
      (x19 = x12 ∧ x20 = x13 ∨ x20 = x12))
    (h18 : (x13 = x21 ∧ x14 = x22 ∨ x14 = x21) ∨
      (x22 = x12 ∧ x23 = x13 ∨ x23 = x12))
    (h19 : (x13 = x24 ∧ x14 = x25 ∨ x14 = x24) ∨
      (x25 = x12 ∧ x26 = x13 ∨ x26 = x12))
    (h20 : (x13 = x30 ∧ x14 = x31 ∨ x14 = x30) ∨
      (x31 = x12 ∧ x32 = x13 ∨ x32 = x12))
    (h21 : (x16 = x21 ∧ x17 = x22 ∨ x17 = x21) ∨
      (x22 = x15 ∧ x23 = x16 ∨ x23 = x15))
    (h22 : (x16 = x27 ∧ x17 = x28 ∨ x17 = x27) ∨
      (x28 = x15 ∧ x29 = x16 ∨ x29 = x15))
    (h23 : (x16 = x30 ∧ x17 = x31 ∨ x17 = x30) ∨
      (x31 = x15 ∧ x32 = x16 ∨ x32 = x15))
    (h24 : (x16 = x33 ∧ x17 = x34 ∨ x17 = x33) ∨
      (x34 = x15 ∧ x35 = x16 ∨ x35 = x15))
    (h25 : (x19 = x33 ∧ x20 = x34 ∨ x20 = x33) ∨
      (x34 = x18 ∧ x35 = x19 ∨ x35 = x18))
    (h26 : (x22 = x33 ∧ x23 = x34 ∨ x23 = x33) ∨
      (x34 = x21 ∧ x35 = x22 ∨ x35 = x21))
    (h27 : (x25 = x27 ∧ x26 = x28 ∨ x26 = x27) ∨
      (x28 = x24 ∧ x29 = x25 ∨ x29 = x24))
    (h28 : (x25 = x30 ∧ x26 = x31 ∨ x26 = x30) ∨
      (x31 = x24 ∧ x32 = x25 ∨ x32 = x24))
    (h29 : (x25 = x33 ∧ x26 = x34 ∨ x26 = x33) ∨
      (x34 = x24 ∧ x35 = x25 ∨ x35 = x24))
    : False := by
  exact (by
    rcases h0 with (⟨e0a, e0b⟩ | e0a) | (⟨e0a, e0b⟩ | e0a)
    ·
      rcases h1 with (⟨e1a, e1b⟩ | e1a) | (⟨e1a, e1b⟩ | e1a)
      ·
        rcases h2 with (⟨e2a, e2b⟩ | e2a) | (⟨e2a, e2b⟩ | e2a)
        ·
          rcases h3 with (⟨e3a, e3b⟩ | e3a) | (⟨e3a, e3b⟩ | e3a)
          ·
            rcases h17 with (⟨e4a, e4b⟩ | e4a) | (⟨e4a, e4b⟩ | e4a)
            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1b)) (e4a)) (e3a.symm)) (e0a))
            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1b)) (b16)) (e4a)) (e3a.symm)) (e0a))
            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e3b)) (e4a)) (e1a.symm)) (e0a))
            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e3b)) (b18)) (e4a)) (e1a.symm)) (e0a))
          ·
            rcases h17 with (⟨e4a, e4b⟩ | e4a) | (⟨e4a, e4b⟩ | e4a)
            ·
              rcases h4 with (⟨e5a, e5b⟩ | e5a) | (⟨e5a, e5b⟩ | e5a)
              ·
                rcases h22 with (⟨e6a, e6b⟩ | e6a) | (⟨e6a, e6b⟩ | e6a)
                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e2b)) (e6a)) (e5a.symm)) (e0a))
                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e2b)) (b17)) (e6a)) (e5a.symm)) (e0a))
                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5b)) (e6a)) (e2a.symm)) (e0a))
                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5b)) (b21)) (e6a)) (e2a.symm)) (e0a))
              ·
                rcases h22 with (⟨e6a, e6b⟩ | e6a) | (⟨e6a, e6b⟩ | e6a)
                ·
                  rcases h5 with (⟨e7a, e7b⟩ | e7a) | (⟨e7a, e7b⟩ | e7a)
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e3a)) (e8a.symm)) (e7a))
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5a)) (e9a.symm)) (e7a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e10a.symm)) (e7a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11a)) (e10a.symm)) (e7a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e10b)) (e11a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e10b)) (b19)) (e11a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            ·
                              rcases h21 with (⟨e13a, e13b⟩ | e13a) | (⟨e13a, e13b⟩ | e13a)
                              ·
                                rcases h8 with (⟨e14a, e14b⟩ | e14a) | (⟨e14a, e14b⟩ | e14a)
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1b)) (e15a)) (e14a.symm)) (e7a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11b)) (e12b.symm)) (e15a)) (e14a.symm)) (e7a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14b)) (e15a)) (e1a.symm)) (e0a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14b)) (b20)) (e15a)) (e1a.symm)) (e0a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e15b)) (e16a)) (e5a.symm)) (e3a))
                                    · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e15b)) (b20)) (e16a)) (e5a.symm)) (e3a))
                                    · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e12b)) (e13b.symm)) (e6b)) (e16a)) (e14a.symm)) (e8a))
                                    · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e12b)) (e13b.symm)) (e6b)) (b21)) (e16a)) (e14a.symm)) (e8a))
                                  · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e15a)) (e14a.symm)) (e8a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14a)) (b8)) (e15a)) (e1a.symm)) (e0a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14a)) (b8)) (b20)) (e15a)) (e1a.symm)) (e0a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (e4b.symm)) (e15b)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (e4b.symm)) (e15a)) (b8)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e0a.symm)) (e1a)) (e15a.symm)) (e14a))
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (e16a.symm)) (e14a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5a)) (e16a.symm)) (e14b)) (e7a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (b9)) (b21)) (e16b)) (e14a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (b9)) (b21)) (e16a)) (b8)) (e14a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (e4b.symm)) (e15b)) (b20)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (e4b.symm)) (e15a)) (b8)) (b20)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (e4a.symm)) (e15b.symm)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e0a.symm)) (e1a)) (e15a.symm)) (e14a))
                              · exact (lt_irrefl x27) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b9) (e6b.symm)) (e13a)) (e10a.symm)) (e9a))
                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11b)) (e13a)) (e2a.symm)) (e0a))
                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11b)) (b19)) (e13a)) (e2a.symm)) (e0a))
                            · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e12a)) (e10a.symm)) (e8a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11b)) (e12a)) (e1a.symm)) (e0a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11b)) (b19)) (e12a)) (e1a.symm)) (e0a))
                          · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e11a)) (e10a.symm)) (e7b))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e10a)) (b7)) (e11a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e10a)) (b7)) (b19)) (e11a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e11b)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e11a)) (b7)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e11a.symm)) (e10a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (e4b.symm)) (e12b)) (e10a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (e4b.symm)) (e12a)) (b7)) (e10a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e0a.symm)) (e1a)) (e12a.symm)) (e10a))
                            ·
                              rcases h21 with (⟨e13a, e13b⟩ | e13a) | (⟨e13a, e13b⟩ | e13a)
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (b9)) (e6b.symm)) (e13b)) (e10a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (b9)) (e6b.symm)) (e13a)) (b7)) (e10a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e0a.symm)) (e2a)) (e13a.symm)) (e10a))
                              ·
                                rcases h8 with (⟨e14a, e14b⟩ | e14a) | (⟨e14a, e14b⟩ | e14a)
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1b)) (e15a)) (e14a.symm)) (e7a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1b)) (b16)) (e15a)) (e14a.symm)) (e7a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14b)) (e15a)) (e1a.symm)) (e0a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14b)) (b20)) (e15a)) (e1a.symm)) (e0a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e15b)) (e16a)) (e5a.symm)) (e3a))
                                    · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e15b)) (b20)) (e16a)) (e5a.symm)) (e3a))
                                    · exact (lt_irrefl x27) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b9) (e16a)) (e14a.symm)) (e9a))
                                    · exact (lt_irrefl x27) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b9) (b21)) (e16a)) (e14a.symm)) (e9a))
                                  · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e15a)) (e14a.symm)) (e8a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14a)) (b8)) (e15a)) (e1a.symm)) (e0a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14a)) (b8)) (b20)) (e15a)) (e1a.symm)) (e0a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (e4b.symm)) (e15b)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (e4b.symm)) (e15a)) (b8)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12a)) (e15a.symm)) (e14a))
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (e16a.symm)) (e14a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5a)) (e16a.symm)) (e14b)) (e7a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (b9)) (b21)) (e16b)) (e14a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (b9)) (b21)) (e16a)) (b8)) (e14a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (e4b.symm)) (e15b)) (b20)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (e4b.symm)) (e15a)) (b8)) (b20)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (e4a.symm)) (e15b.symm)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12a)) (e15a.symm)) (e14a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e11b)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e11a)) (b7)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e11b.symm)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e11a.symm)) (e10a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e0b.symm)) (e5a)) (b9)) (e9a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e0b.symm)) (e5a)) (b9)) (b21)) (e9a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e0b.symm)) (e3a)) (b6)) (e8a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e0b.symm)) (e3a)) (b6)) (b18)) (e8a))
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e3a)) (b6)) (e8b.symm)) (e7a))
                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e3a)) (e8a.symm)) (e7a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (e0b.symm)) (e3a)) (b6)) (e8a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (e0b.symm)) (e3a)) (b6)) (b18)) (e8a))
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8a)) (e3a.symm)) (e0b)) (e7a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (e3a.symm)) (e0b)) (e7a))
                    · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e8a)) (e7a.symm)) (e0b.symm)) (e3a))
                    · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b6) (b18)) (e8a)) (e7a.symm)) (e0b.symm)) (e3a))
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8a)) (e3a.symm)) (e0b)) (b15)) (e7a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (e3a.symm)) (e0b)) (b15)) (e7a))
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9a)) (e5a.symm)) (e0b)) (b15)) (e7a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (e5a.symm)) (e0b)) (b15)) (e7a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            ·
                              rcases h21 with (⟨e13a, e13b⟩ | e13a) | (⟨e13a, e13b⟩ | e13a)
                              ·
                                rcases h8 with (⟨e14a, e14b⟩ | e14a) | (⟨e14a, e14b⟩ | e14a)
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (e15b.symm)) (e4b)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14a)) (e15a.symm)) (e4b)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e15b)) (b16)) (e4b)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e15a)) (b4)) (b16)) (e4b)) (e8a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (e15b.symm)) (e4b)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (e15a.symm)) (e4b)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (b20)) (e15b)) (b16)) (e4b)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (b20)) (e15a)) (b4)) (b16)) (e4b)) (e8a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e16b)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e16a)) (b9)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e16b)) (e14a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e16a)) (b8)) (e14a))
                                  · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b8) (e14a)) (e8a.symm)) (e4b.symm)) (e15a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e15b)) (b16)) (e4b)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e15a)) (b4)) (b16)) (e4b)) (e8a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x25) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b20) (e14a)) (e8a.symm)) (e4b.symm)) (e15b))
                                  · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b8) (b20)) (e14a)) (e8a.symm)) (e4b.symm)) (e15a))
                                  · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e8a)) (e14a.symm)) (e15b)) (e4a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e14a.symm)) (e15a)) (e1a.symm)) (e0a))
                              · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e8a)) (e9a.symm)) (e6b.symm)) (e13a)) (e12a.symm)) (e4a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e13b)) (b17)) (e6b)) (e9a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e13a)) (b5)) (b17)) (e6b)) (e9a))
                            · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e12a)) (e11a.symm)) (e0b.symm)) (e3a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12b)) (b16)) (e4b)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12a)) (b4)) (b16)) (e4b)) (e8a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x22) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b19) (e10a)) (e7a.symm)) (e11b))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e8a)) (e10a.symm)) (e11b)) (e0b.symm)) (e3a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e10a.symm)) (e11a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            ·
                              rcases h21 with (⟨e13a, e13b⟩ | e13a) | (⟨e13a, e13b⟩ | e13a)
                              · exact (lt_irrefl x28) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b21) (e9a)) (e10a.symm)) (e13b.symm)) (e6b))
                              · exact (lt_irrefl x27) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b9) (e6b.symm)) (e13a)) (e11a.symm)) (e0b.symm)) (e5a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e13b)) (b17)) (e6b)) (b21)) (e9a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e13a)) (b5)) (b17)) (e6b)) (b21)) (e9a))
                            · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e12a)) (e11a.symm)) (e0b.symm)) (e3a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12b)) (b16)) (e4b)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12a)) (b4)) (b16)) (e4b)) (e8a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x22) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b19) (e10a)) (e7a.symm)) (e11b))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e8a)) (e10a.symm)) (e11b)) (e0b.symm)) (e3a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e10a.symm)) (e11a))
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9a)) (e5a.symm)) (e0b)) (b15)) (e7a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (e5a.symm)) (e0b)) (b15)) (e7a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x19) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b18) (e8a)) (e10a.symm)) (e12b.symm)) (e4b))
                            · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e12a)) (e11a.symm)) (e0b.symm)) (e3a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12b)) (b16)) (e4b)) (b18)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12a)) (b4)) (b16)) (e4b)) (b18)) (e8a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x22) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b19) (e10a)) (e7a.symm)) (e11b))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b6) (b18)) (e8a)) (e10a.symm)) (e11b)) (e0b.symm)) (e3a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e10a.symm)) (e11a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x19) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b18) (e8a)) (e10a.symm)) (e12b.symm)) (e4b))
                            · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e12a)) (e11a.symm)) (e0b.symm)) (e3a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12b)) (b16)) (e4b)) (b18)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12a)) (b4)) (b16)) (e4b)) (b18)) (e8a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x22) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b19) (e10a)) (e7a.symm)) (e11b))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b6) (b18)) (e8a)) (e10a.symm)) (e11b)) (e0b.symm)) (e3a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e10a.symm)) (e11a))
                · exact (lt_irrefl x16) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b17) (e6a)) (e5a.symm)) (e2b))
                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5a)) (b9)) (e6a)) (e2a.symm)) (e0a))
                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5a)) (b9)) (b21)) (e6a)) (e2a.symm)) (e0a))
              · exact (lt_irrefl x27) (lt_trans (lt_of_lt_of_eq (b9) (e5a)) (b28))
              · exact (lt_irrefl x27) (lt_trans (lt_of_lt_of_eq (lt_trans (b9) (b21)) (e5a)) (b28))
            · exact (lt_irrefl x13) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b16) (e4a)) (e3a.symm)) (e1b))
            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e3a)) (b6)) (e4a)) (e1a.symm)) (e0a))
            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e3a)) (b6)) (b18)) (e4a)) (e1a.symm)) (e0a))
          · exact (lt_irrefl x18) (lt_trans (lt_of_lt_of_eq (b6) (e3a)) (b27))
          · exact (lt_irrefl x18) (lt_trans (lt_of_lt_of_eq (lt_trans (b6) (b18)) (e3a)) (b27))
        ·
          rcases h3 with (⟨e3a, e3b⟩ | e3a) | (⟨e3a, e3b⟩ | e3a)
          ·
            rcases h17 with (⟨e4a, e4b⟩ | e4a) | (⟨e4a, e4b⟩ | e4a)
            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1b)) (e4a)) (e3a.symm)) (e0a))
            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1b)) (b16)) (e4a)) (e3a.symm)) (e0a))
            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e3b)) (e4a)) (e1a.symm)) (e0a))
            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e3b)) (b18)) (e4a)) (e1a.symm)) (e0a))
          ·
            rcases h17 with (⟨e4a, e4b⟩ | e4a) | (⟨e4a, e4b⟩ | e4a)
            ·
              rcases h4 with (⟨e5a, e5b⟩ | e5a) | (⟨e5a, e5b⟩ | e5a)
              ·
                rcases h22 with (⟨e6a, e6b⟩ | e6a) | (⟨e6a, e6b⟩ | e6a)
                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e2a)) (b5)) (e6a)) (e5a.symm)) (e0a))
                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e2a)) (b5)) (b17)) (e6a)) (e5a.symm)) (e0a))
                ·
                  rcases h5 with (⟨e7a, e7b⟩ | e7a) | (⟨e7a, e7b⟩ | e7a)
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e3a)) (e8a.symm)) (e7a))
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e10a.symm)) (e7a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11a)) (e10a.symm)) (e7a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e10b)) (e11a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e10b)) (b19)) (e11a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            ·
                              rcases h21 with (⟨e13a, e13b⟩ | e13a) | (⟨e13a, e13b⟩ | e13a)
                              · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b5) (e13a)) (e10a.symm)) (e9b)) (e6a))
                              · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b5) (b17)) (e13a)) (e10a.symm)) (e9b)) (e6a))
                              · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e12b)) (e13a)) (e2a.symm)) (e3a))
                              · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e12b)) (b19)) (e13a)) (e2a.symm)) (e3a))
                            · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e12a)) (e10a.symm)) (e8a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11b)) (e12a)) (e1a.symm)) (e0a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11b)) (b19)) (e12a)) (e1a.symm)) (e0a))
                          · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e11a)) (e10a.symm)) (e7b))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e10a)) (b7)) (e11a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e10a)) (b7)) (b19)) (e11a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e11b)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e11a)) (b7)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e11a.symm)) (e10a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (e4b.symm)) (e12b)) (e10a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (e4b.symm)) (e12a)) (b7)) (e10a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e0a.symm)) (e1a)) (e12a.symm)) (e10a))
                            ·
                              rcases h21 with (⟨e13a, e13b⟩ | e13a) | (⟨e13a, e13b⟩ | e13a)
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (b21)) (e6b)) (b17)) (e13b)) (e10a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (b21)) (e6b)) (b17)) (e13a)) (b7)) (e10a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (e6a)) (e13a.symm)) (e10a))
                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e2a)) (e13a.symm)) (e11a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e11b)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e11a)) (b7)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e11b.symm)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e11a.symm)) (e10a))
                      · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e9a)) (e5a.symm)) (e0a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e0b.symm)) (e5b)) (e9a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e0b.symm)) (e5b)) (b21)) (e9a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e0b.symm)) (e3a)) (b6)) (e8a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e0b.symm)) (e3a)) (b6)) (b18)) (e8a))
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e3a)) (b6)) (e8b.symm)) (e7a))
                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e3a)) (e8a.symm)) (e7a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (e0b.symm)) (e3a)) (b6)) (e8a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (e0b.symm)) (e3a)) (b6)) (b18)) (e8a))
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8a)) (e3a.symm)) (e0b)) (e7a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (e3a.symm)) (e0b)) (e7a))
                    · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e8a)) (e7a.symm)) (e0b.symm)) (e3a))
                    · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b6) (b18)) (e8a)) (e7a.symm)) (e0b.symm)) (e3a))
                  ·
                    rcases h9 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e5b.symm)) (e0b)) (b15)) (e7a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b9)) (e5b.symm)) (e0b)) (b15)) (e7a))
                    · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e7a)) (e8a.symm)) (e5b.symm)) (e0b))
                    ·
                      rcases h6 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9a)) (e3a.symm)) (e0b)) (b15)) (e7a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (e3a.symm)) (e0b)) (b15)) (e7a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            ·
                              rcases h21 with (⟨e13a, e13b⟩ | e13a) | (⟨e13a, e13b⟩ | e13a)
                              · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b5) (e13a)) (e11a.symm)) (e0b.symm)) (e2a))
                              · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b5) (b17)) (e13a)) (e11a.symm)) (e0b.symm)) (e2a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e13b)) (e6b.symm)) (e8a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e13a)) (b5)) (e6b.symm)) (e8a))
                            · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b5) (e6b.symm)) (e8a)) (e9a.symm)) (e4b.symm)) (e12a)) (e11a.symm)) (e0b.symm)) (e2a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12b)) (b16)) (e4b)) (e9a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12a)) (b4)) (b16)) (e4b)) (e9a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x22) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b19) (e10a)) (e7a.symm)) (e11b))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b5) (e6b.symm)) (e8a)) (e10a.symm)) (e11b)) (e0b.symm)) (e2a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e10a.symm)) (e11a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x19) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b18) (e9a)) (e10a.symm)) (e12b.symm)) (e4b))
                            · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e12a)) (e11a.symm)) (e0b.symm)) (e3a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12b)) (b16)) (e4b)) (b18)) (e9a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12a)) (b4)) (b16)) (e4b)) (b18)) (e9a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x22) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b19) (e10a)) (e7a.symm)) (e11b))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b5) (e6b.symm)) (e8a)) (e10a.symm)) (e11b)) (e0b.symm)) (e2a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e10a.symm)) (e11a))
                · exact (lt_irrefl x28) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b21) (e6a)) (e2a.symm)) (e5b))
              ·
                rcases h22 with (⟨e6a, e6b⟩ | e6a) | (⟨e6a, e6b⟩ | e6a)
                · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b5) (e6a)) (e5a.symm)) (e2a))
                · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b5) (b17)) (e6a)) (e5a.symm)) (e2a))
                · exact (lt_irrefl x27) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b9) (e6a)) (e2a.symm)) (e5a))
                · exact (lt_irrefl x27) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b9) (b21)) (e6a)) (e2a.symm)) (e5a))
              · exact (lt_irrefl x27) (lt_trans (lt_of_lt_of_eq (b9) (e5a)) (b28))
              · exact (lt_irrefl x27) (lt_trans (lt_of_lt_of_eq (lt_trans (b9) (b21)) (e5a)) (b28))
            · exact (lt_irrefl x13) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b16) (e4a)) (e3a.symm)) (e1b))
            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e3a)) (b6)) (e4a)) (e1a.symm)) (e0a))
            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e3a)) (b6)) (b18)) (e4a)) (e1a.symm)) (e0a))
          · exact (lt_irrefl x18) (lt_trans (lt_of_lt_of_eq (b6) (e3a)) (b27))
          · exact (lt_irrefl x18) (lt_trans (lt_of_lt_of_eq (lt_trans (b6) (b18)) (e3a)) (b27))
        · exact (lt_irrefl x15) (lt_trans (lt_of_lt_of_eq (b5) (e2a)) (b26))
        · exact (lt_irrefl x15) (lt_trans (lt_of_lt_of_eq (lt_trans (b5) (b17)) (e2a)) (b26))
      ·
        rcases h2 with (⟨e2a, e2b⟩ | e2a) | (⟨e2a, e2b⟩ | e2a)
        ·
          rcases h3 with (⟨e3a, e3b⟩ | e3a) | (⟨e3a, e3b⟩ | e3a)
          ·
            rcases h17 with (⟨e4a, e4b⟩ | e4a) | (⟨e4a, e4b⟩ | e4a)
            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (b4)) (e4a)) (e3a.symm)) (e0a))
            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (b4)) (b16)) (e4a)) (e3a.symm)) (e0a))
            ·
              rcases h4 with (⟨e5a, e5b⟩ | e5a) | (⟨e5a, e5b⟩ | e5a)
              ·
                rcases h22 with (⟨e6a, e6b⟩ | e6a) | (⟨e6a, e6b⟩ | e6a)
                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e2b)) (e6a)) (e5a.symm)) (e0a))
                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e2b)) (b17)) (e6a)) (e5a.symm)) (e0a))
                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5b)) (e6a)) (e2a.symm)) (e0a))
                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5b)) (b21)) (e6a)) (e2a.symm)) (e0a))
              ·
                rcases h22 with (⟨e6a, e6b⟩ | e6a) | (⟨e6a, e6b⟩ | e6a)
                ·
                  rcases h5 with (⟨e7a, e7b⟩ | e7a) | (⟨e7a, e7b⟩ | e7a)
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5a)) (e9a.symm)) (e7a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e10a.symm)) (e7a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11a)) (e10a.symm)) (e7a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e10b)) (e11a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e10b)) (b19)) (e11a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e12a)) (e10a.symm)) (e8b)) (e4a))
                            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e12a)) (e10a.symm)) (e8b)) (e4a))
                            · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e12a)) (e1a.symm)) (e0b)) (e11a))
                            · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e12a)) (e1a.symm)) (e0b)) (e11a))
                          · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e11a)) (e10a.symm)) (e7b))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e10a)) (b7)) (e11a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e10a)) (b7)) (b19)) (e11a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e11b)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e11a)) (b7)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e11a.symm)) (e10a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (b18)) (e4b)) (b16)) (e12b)) (e10a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (b18)) (e4b)) (b16)) (e12a)) (b7)) (e10a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e4a)) (e12a.symm)) (e10a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (e12a.symm)) (e11a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e11b)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e11a)) (b7)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e11b.symm)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e11a.symm)) (e10a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e0b.symm)) (e5a)) (b9)) (e9a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e0b.symm)) (e5a)) (b9)) (b21)) (e9a))
                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e8a)) (e3a.symm)) (e0a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e0b.symm)) (e3b)) (e8a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e0b.symm)) (e3b)) (b18)) (e8a))
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e3b)) (e8b.symm)) (e7a))
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5a)) (b9)) (e9b.symm)) (e7a))
                      · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5a)) (e9a.symm)) (e7a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (e0b.symm)) (e5a)) (b9)) (e9a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (e0b.symm)) (e5a)) (b9)) (b21)) (e9a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (e0b.symm)) (e3b)) (e8a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (e0b.symm)) (e3b)) (b18)) (e8a))
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e3b.symm)) (e0b)) (e7a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (e3b.symm)) (e0b)) (e7a))
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9a)) (e5a.symm)) (e0b)) (e7a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (e5a.symm)) (e0b)) (e7a))
                      · exact (lt_irrefl x27) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b9) (e9a)) (e7a.symm)) (e0b.symm)) (e5a))
                      · exact (lt_irrefl x27) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b9) (b21)) (e9a)) (e7a.symm)) (e0b.symm)) (e5a))
                    · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e4b.symm)) (e8a)) (e7a.symm)) (e0b.symm)) (e1a))
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e3b.symm)) (e0b)) (b15)) (e7a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (e3b.symm)) (e0b)) (b15)) (e7a))
                    · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e7a)) (e8a.symm)) (e3b.symm)) (e0b))
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9a)) (e5a.symm)) (e0b)) (b15)) (e7a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (e5a.symm)) (e0b)) (b15)) (e7a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e12a)) (e11a.symm)) (e0b.symm)) (e1a))
                            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e12a)) (e11a.symm)) (e0b.symm)) (e1a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12b)) (e4b.symm)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12a)) (b4)) (e4b.symm)) (e8a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x22) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b19) (e10a)) (e7a.symm)) (e11b))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e4b.symm)) (e8a)) (e10a.symm)) (e11b)) (e0b.symm)) (e1a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e10a.symm)) (e11a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e12a)) (e11a.symm)) (e0b.symm)) (e1a))
                            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e12a)) (e11a.symm)) (e0b.symm)) (e1a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12b)) (e4b.symm)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12a)) (b4)) (e4b.symm)) (e8a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x22) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b19) (e10a)) (e7a.symm)) (e11b))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e4b.symm)) (e8a)) (e10a.symm)) (e11b)) (e0b.symm)) (e1a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e10a.symm)) (e11a))
                · exact (lt_irrefl x16) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b17) (e6a)) (e5a.symm)) (e2b))
                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5a)) (b9)) (e6a)) (e2a.symm)) (e0a))
                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5a)) (b9)) (b21)) (e6a)) (e2a.symm)) (e0a))
              · exact (lt_irrefl x27) (lt_trans (lt_of_lt_of_eq (b9) (e5a)) (b28))
              · exact (lt_irrefl x27) (lt_trans (lt_of_lt_of_eq (lt_trans (b9) (b21)) (e5a)) (b28))
            · exact (lt_irrefl x19) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b18) (e4a)) (e1a.symm)) (e3b))
          ·
            rcases h17 with (⟨e4a, e4b⟩ | e4a) | (⟨e4a, e4b⟩ | e4a)
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e4a)) (e3a.symm)) (e1a))
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e4a)) (e3a.symm)) (e1a))
            · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4a)) (e1a.symm)) (e3a))
            · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b6) (b18)) (e4a)) (e1a.symm)) (e3a))
          · exact (lt_irrefl x18) (lt_trans (lt_of_lt_of_eq (b6) (e3a)) (b27))
          · exact (lt_irrefl x18) (lt_trans (lt_of_lt_of_eq (lt_trans (b6) (b18)) (e3a)) (b27))
        ·
          rcases h3 with (⟨e3a, e3b⟩ | e3a) | (⟨e3a, e3b⟩ | e3a)
          ·
            rcases h17 with (⟨e4a, e4b⟩ | e4a) | (⟨e4a, e4b⟩ | e4a)
            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (b4)) (e4a)) (e3a.symm)) (e0a))
            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (b4)) (b16)) (e4a)) (e3a.symm)) (e0a))
            ·
              rcases h4 with (⟨e5a, e5b⟩ | e5a) | (⟨e5a, e5b⟩ | e5a)
              ·
                rcases h22 with (⟨e6a, e6b⟩ | e6a) | (⟨e6a, e6b⟩ | e6a)
                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e2a)) (b5)) (e6a)) (e5a.symm)) (e0a))
                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e2a)) (b5)) (b17)) (e6a)) (e5a.symm)) (e0a))
                ·
                  rcases h5 with (⟨e7a, e7b⟩ | e7a) | (⟨e7a, e7b⟩ | e7a)
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e10a.symm)) (e7a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11a)) (e10a.symm)) (e7a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e10b)) (e11a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e10b)) (b19)) (e11a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e12a)) (e10a.symm)) (e8b)) (e4a))
                            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e12a)) (e10a.symm)) (e8b)) (e4a))
                            · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e12a)) (e1a.symm)) (e0b)) (e11a))
                            · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e12a)) (e1a.symm)) (e0b)) (e11a))
                          · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e11a)) (e10a.symm)) (e7b))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e10a)) (b7)) (e11a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e10a)) (b7)) (b19)) (e11a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e11b)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e11a)) (b7)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e11a.symm)) (e10a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (b18)) (e4b)) (b16)) (e12b)) (e10a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (b18)) (e4b)) (b16)) (e12a)) (b7)) (e10a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e4a)) (e12a.symm)) (e10a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (e12a.symm)) (e11a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e11b)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e11a)) (b7)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e11b.symm)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e11a.symm)) (e10a))
                      · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e9a)) (e5a.symm)) (e0a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e0b.symm)) (e5b)) (e9a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e0b.symm)) (e5b)) (b21)) (e9a))
                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e8a)) (e3a.symm)) (e0a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e0b.symm)) (e3b)) (e8a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e0b.symm)) (e3b)) (b18)) (e8a))
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e3b)) (e8b.symm)) (e7a))
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5b)) (e9b.symm)) (e7a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11b)) (e10b.symm)) (e7a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11a)) (b7)) (e10b.symm)) (e7a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (b4)) (b16)) (e12b)) (e11a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (b4)) (b16)) (e12a)) (b7)) (e11a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (e12a.symm)) (e11a))
                            ·
                              rcases h21 with (⟨e13a, e13b⟩ | e13a) | (⟨e13a, e13b⟩ | e13a)
                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e2a)) (b5)) (b17)) (e13b)) (e11a))
                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e2a)) (b5)) (b17)) (e13a)) (b7)) (e11a))
                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e2a)) (e13a.symm)) (e11a))
                              ·
                                rcases h8 with (⟨e14a, e14b⟩ | e14a) | (⟨e14a, e14b⟩ | e14a)
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (b4)) (b16)) (e15b)) (e14b.symm)) (e7a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (b4)) (b16)) (e15a)) (b8)) (e14b.symm)) (e7a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (e15a.symm)) (e14b.symm)) (e7a))
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    ·
                                      rcases h10 with (⟨e17a, e17b⟩ | e17a) | (⟨e17a, e17b⟩ | e17a)
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20b)) (e21a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20b)) (b22)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e22a)) (e20a.symm)) (e18b)) (e4a))
                                                · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e22a)) (e20a.symm)) (e18b)) (e4a))
                                                · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b10) (e22a)) (e1a.symm)) (e0b)) (e21a))
                                                · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b10) (b22)) (e22a)) (e1a.symm)) (e0b)) (e21a))
                                              · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e21a)) (e20a.symm)) (e17b))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20a)) (b10)) (e21a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20a)) (b10)) (b22)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21b)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21a)) (b10)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17a)) (e21a.symm)) (e20a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (b18)) (e4b)) (b16)) (e22b)) (e20a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (b18)) (e4b)) (b16)) (e22a)) (b10)) (e20a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (e4a)) (e22a.symm)) (e20a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (e22a.symm)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21b)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21a)) (b10)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e21b.symm)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17a)) (e21a.symm)) (e20a))
                                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e19a)) (e5a.symm)) (e0a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e0b.symm)) (e5b)) (e19a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e0b.symm)) (e5b)) (b21)) (e19a))
                                        · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e18a)) (e3a.symm)) (e0a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e0b.symm)) (e3b)) (e18a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e0b.symm)) (e3b)) (b18)) (e18a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e3b)) (e18b.symm)) (e17a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5b)) (e19b.symm)) (e17a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21b)) (e20b.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21a)) (b10)) (e20b.symm)) (e17a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (b4)) (b16)) (e22b)) (e21a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (b4)) (b16)) (e22a)) (b10)) (e21a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (e22a.symm)) (e21a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e2a)) (b5)) (b17)) (e23b)) (e21a))
                                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e2a)) (b5)) (b17)) (e23a)) (b10)) (e21a))
                                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e2a)) (e23a.symm)) (e21a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (e15a.symm)) (e24b)) (e21a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (e15a.symm)) (e24a)) (b10)) (e21a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21b.symm)) (e24b)) (e14b.symm)) (e7a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21b.symm)) (e24a)) (b8)) (e14b.symm)) (e7a))
                                              · exact (lt_irrefl x31) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b22) (e21a)) (e17a.symm)) (e20b))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b10) (e21a)) (e17a.symm)) (e20a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b10) (b22)) (e21a)) (e17a.symm)) (e20a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21b)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21a)) (b10)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (e21a.symm)) (e20a))
                                              · exact (lt_irrefl x7) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b14) (e17a)) (e21a.symm)) (e20b))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21b)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21a)) (b10)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e21b.symm)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (e21a.symm)) (e20a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e0b.symm)) (e5b)) (e19a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e0b.symm)) (e5b)) (b21)) (e19a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e0b.symm)) (e3b)) (e18a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e0b.symm)) (e3b)) (b18)) (e18a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (e3b.symm)) (e0b)) (e17a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18a)) (b6)) (e3b.symm)) (e0b)) (e17a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19b)) (e5b.symm)) (e0b)) (e17a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19a)) (b9)) (e5b.symm)) (e0b)) (e17a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20a)) (e21a.symm)) (e17a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (e24b.symm)) (e16b)) (e19a))
                                                    · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20a)) (e24a.symm)) (e16b)) (e19a))
                                                    · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e24b)) (b20)) (e16b)) (e19a))
                                                    · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e24a)) (b8)) (b20)) (e16b)) (e19a))
                                                  · exact (lt_irrefl x16) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b17) (e23a)) (e20a.symm)) (e19b.symm)) (e6b))
                                                  · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (e23a)) (e6a.symm)) (e19a))
                                                  · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e23a)) (e6a.symm)) (e19a))
                                                · exact (lt_irrefl x13) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b16) (e22a)) (e20a.symm)) (e18b.symm)) (e4b))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (e22a)) (e4a.symm)) (e18a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e22a)) (e4a.symm)) (e18a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21b)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21a)) (b3)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x7) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b14) (e20a)) (e21a.symm)) (e17b))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21b)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21a)) (b3)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21b)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21a)) (b10)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21b)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21a)) (b3)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21b)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21a)) (b10)) (b22)) (e20a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e18b.symm)) (e4b)) (b16)) (e22b)) (b22)) (e20a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e18b.symm)) (e4b)) (b16)) (e22a)) (b10)) (b22)) (e20a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e18b.symm)) (e4b)) (e22b.symm)) (e20a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e19b.symm)) (e6b)) (b17)) (e23b)) (b22)) (e20a))
                                                  · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e19b.symm)) (e6b)) (b17)) (e23a)) (b10)) (b22)) (e20a))
                                                  · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e19b.symm)) (e6b)) (e23b.symm)) (e20a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (e15a.symm)) (e24b)) (e21a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (e15a.symm)) (e24a)) (b10)) (e21a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21b.symm)) (e24b)) (e14b.symm)) (e7a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21b.symm)) (e24a)) (b8)) (e14b.symm)) (e7a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17a)) (e20a.symm)) (e21a))
                                          · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b5) (e6b.symm)) (e19a)) (e17a.symm)) (e0b.symm)) (e2a))
                                        · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e4b.symm)) (e18a)) (e17a.symm)) (e0b.symm)) (e1a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (e3b.symm)) (e0b)) (b15)) (e17a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18a)) (b6)) (e3b.symm)) (e0b)) (b15)) (e17a))
                                        · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e17a)) (e18a.symm)) (e3b.symm)) (e0b))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19b)) (e5b.symm)) (e0b)) (b15)) (e17a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19a)) (b9)) (e5b.symm)) (e0b)) (b15)) (e17a))
                                          · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e4b.symm)) (e18a)) (e19a.symm)) (e5b.symm)) (e1a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (e21b.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21b)) (b15)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21a)) (b3)) (b15)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (e21b.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21b)) (b15)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21a)) (b3)) (b15)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e22a)) (e21a.symm)) (e0b.symm)) (e1a))
                                                · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e22a)) (e21a.symm)) (e0b.symm)) (e1a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e22b)) (e4b.symm)) (e18a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e22a)) (b4)) (e4b.symm)) (e18a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b10) (e20a)) (e17a.symm)) (e21a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21b)) (b15)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21a)) (b3)) (b15)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x31) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b22) (e20a)) (e17a.symm)) (e21b))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b10) (b22)) (e20a)) (e17a.symm)) (e21a))
                                              · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e4b.symm)) (e18a)) (e20a.symm)) (e21b)) (e0b.symm)) (e1a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e17a)) (e20a.symm)) (e21a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (e15a.symm)) (e16a)) (e5a.symm)) (e0a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5b)) (b21)) (e16b)) (e14b.symm)) (e7a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5b)) (b21)) (e16a)) (b8)) (e14b.symm)) (e7a))
                                ·
                                  rcases h27 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b8) (e15a)) (e9a.symm)) (e14a))
                                  · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b8) (b20)) (e15a)) (e9a.symm)) (e14a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5b)) (e15a)) (e14a.symm)) (e7a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5b)) (b21)) (e15a)) (e14a.symm)) (e7a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (b18)) (e4b)) (b16)) (e15b)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (b18)) (e4b)) (b16)) (e15a)) (b8)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (e4a)) (e15a.symm)) (e14a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (e15a.symm)) (e14b)) (b13)) (e7a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (b18)) (e4b)) (b16)) (e15b)) (b20)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (b18)) (e4b)) (b16)) (e15a)) (b8)) (b20)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (b18)) (e4b)) (e15b.symm)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (e4a)) (e15a.symm)) (e14a))
                          · exact (lt_irrefl x22) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b19) (e11a)) (e7a.symm)) (e10b))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e10a.symm)) (e7a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11a)) (e10a.symm)) (e7a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e11a)) (e7a.symm)) (e10a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e11a)) (e7a.symm)) (e10a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (b15)) (e11b)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (b15)) (e11a)) (b7)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e11a.symm)) (e10a))
                          · exact (lt_irrefl x4) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b13) (e7a)) (e11a.symm)) (e10b))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (b15)) (e11b)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (b15)) (e11a)) (b7)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (e11b.symm)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e11a.symm)) (e10a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (e0b.symm)) (e5b)) (e9a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (e0b.symm)) (e5b)) (b21)) (e9a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (e0b.symm)) (e3b)) (e8a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (e0b.symm)) (e3b)) (b18)) (e8a))
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e3b.symm)) (e0b)) (e7a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (e3b.symm)) (e0b)) (e7a))
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (e5b.symm)) (e0b)) (e7a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (b9)) (e5b.symm)) (e0b)) (e7a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            ·
                              rcases h21 with (⟨e13a, e13b⟩ | e13a) | (⟨e13a, e13b⟩ | e13a)
                              ·
                                rcases h8 with (⟨e14a, e14b⟩ | e14a) | (⟨e14a, e14b⟩ | e14a)
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e16b)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e16a)) (b9)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14a)) (e16a.symm)) (e9a))
                                    ·
                                      rcases h10 with (⟨e17a, e17b⟩ | e17a) | (⟨e17a, e17b⟩ | e17a)
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (e20b.symm)) (e17b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (e20b.symm)) (e17b)) (e7a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20b)) (e21a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20b)) (b22)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (e22a)) (e21a.symm)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e22a)) (e21a.symm)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (e22a)) (e4a.symm)) (e8a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e22a)) (e4a.symm)) (e8a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (e20a.symm)) (e17b)) (e7a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20a)) (b10)) (e21a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20a)) (b10)) (b22)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e20b)) (b14)) (e17b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e20b)) (b14)) (e17b)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17a)) (e21a.symm)) (e20a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e22b)) (b22)) (e21a)) (b3)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e22a)) (b10)) (b22)) (e21a)) (b3)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (e22b.symm)) (e21a)) (b3)) (e7a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (e22a.symm)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e20a)) (b2)) (b14)) (e17b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e20a)) (b2)) (b14)) (e17b)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e21b.symm)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17a)) (e21a.symm)) (e20a))
                                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e19a)) (e5a.symm)) (e0a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e19b)) (b14)) (e17b)) (e7a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e19a)) (b2)) (b14)) (e17b)) (e7a))
                                        · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e18a)) (e3a.symm)) (e0a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e18b)) (b14)) (e17b)) (e7a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e18a)) (b2)) (b14)) (e17b)) (e7a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e3b)) (e18b.symm)) (e17a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5b)) (e19b.symm)) (e17a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (e20b.symm)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (e20b.symm)) (e17a)) (b3)) (e7a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e22b)) (b22)) (e21b)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e22a)) (b10)) (b22)) (e21b)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (e22b.symm)) (e21b)) (e7a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e13b.symm)) (e23b)) (b22)) (e21b)) (e7a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e13b.symm)) (e23a)) (b10)) (b22)) (e21b)) (e7a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e6b)) (e23b.symm)) (e21b)) (e7a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e24b)) (b22)) (e21b)) (e7a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e24a)) (b10)) (b22)) (e21b)) (e7a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (e24b.symm)) (e21b)) (e7a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14a)) (e24a.symm)) (e21b)) (e7a))
                                              · exact (lt_irrefl x31) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b22) (e21a)) (e17a.symm)) (e20b))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (e20a.symm)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b10) (e21a)) (e17a.symm)) (e20a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b10) (b22)) (e21a)) (e17a.symm)) (e20a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e20b)) (b14)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e20b)) (b14)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (e21a.symm)) (e20a))
                                              · exact (lt_irrefl x7) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b14) (e17a)) (e21a.symm)) (e20b))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e20a)) (b2)) (b14)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e20a)) (b2)) (b14)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e21b.symm)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (e21a.symm)) (e20a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e19b)) (b14)) (e17a)) (b3)) (e7a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e19a)) (b2)) (b14)) (e17a)) (b3)) (e7a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e18b)) (b14)) (e17a)) (b3)) (e7a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e18a)) (b2)) (b14)) (e17a)) (b3)) (e7a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e18b)) (e8a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e18a)) (b6)) (e8a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e19b)) (e9a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e19a)) (b9)) (e9a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (e20a)) (e21a.symm)) (e7a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10b.symm)) (e14b)) (e24a)) (e21a.symm)) (e11a))
                                                    · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10b.symm)) (e14b)) (b20)) (e24a)) (e21a.symm)) (e11a))
                                                    · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e12b.symm)) (e22b)) (e24a)) (e14a.symm)) (e10a))
                                                    · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e12b.symm)) (e22b)) (b22)) (e24a)) (e14a.symm)) (e10a))
                                                  · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e13b.symm)) (e23a)) (e21a.symm)) (e11a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (e23a)) (e6a.symm)) (e9a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e23a)) (e6a.symm)) (e9a))
                                                · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e12b.symm)) (e22a)) (e21a.symm)) (e11a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (e22a)) (e4a.symm)) (e8a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e22a)) (e4a.symm)) (e8a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e20b)) (b22)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e20b)) (b22)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e20a)) (e21a.symm)) (e7a))
                                              · exact (lt_irrefl x7) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b14) (e20a)) (e21a.symm)) (e17b))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e20a)) (b10)) (b22)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e20a)) (b10)) (b22)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (e20a)) (e17a.symm)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (e20a)) (e17a.symm)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (e20b.symm)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (e20b.symm)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e20a)) (e17a.symm)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e20a)) (e17a.symm)) (e7a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e22b)) (b22)) (e21b)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e22a)) (b10)) (b22)) (e21b)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (e22b.symm)) (e21b)) (e7a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e13b.symm)) (e23b)) (b22)) (e21b)) (e7a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e13b.symm)) (e23a)) (b10)) (b22)) (e21b)) (e7a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e6b)) (e23b.symm)) (e21b)) (e7a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e24b)) (b22)) (e21b)) (e7a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e24a)) (b10)) (b22)) (e21b)) (e7a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (e24b.symm)) (e21b)) (e7a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14a)) (e24a.symm)) (e21b)) (e7a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17a)) (e20a.symm)) (e21a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e19a)) (e17a.symm)) (e7a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e18a)) (e17a.symm)) (e7a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e18b)) (e8a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e18a)) (b6)) (e8a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (e18a.symm)) (e8a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e19b)) (e9a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e19a)) (b9)) (e9a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (e19a.symm)) (e9a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (e20a)) (e21a.symm)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e20b)) (b22)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e20b)) (b22)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e20a)) (e21a.symm)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e20a)) (b10)) (b22)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e20a)) (b10)) (b22)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (e22a)) (e21a.symm)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e22a)) (e21a.symm)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (e22a)) (e4a.symm)) (e8a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e22a)) (e4a.symm)) (e8a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b10) (e20a)) (e17a.symm)) (e21a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (e20b.symm)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (e20b.symm)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x31) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b22) (e20a)) (e17a.symm)) (e21b))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b10) (b22)) (e20a)) (e17a.symm)) (e21a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (e20a.symm)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (e20a.symm)) (e21a)) (b3)) (e7a))
                                  · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e12b.symm)) (e15a)) (e14a.symm)) (e10a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (e15a)) (e4a.symm)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e15a)) (e4a.symm)) (e8a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10b.symm)) (e14a)) (e15a.symm)) (e12a))
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (b20)) (e16b)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (b20)) (e16a)) (b9)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (e16a.symm)) (e9a))
                                    · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10b.symm)) (e14a)) (e16a.symm)) (e6b)) (e13a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (e15a)) (e4a.symm)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (b20)) (e15a)) (e4a.symm)) (e8a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e15b)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e15a)) (b8)) (e14a))
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e16b)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e16a)) (b9)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e16b)) (e14a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e16a)) (b8)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e15a)) (e4a.symm)) (e8a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e15b)) (b20)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e15a)) (b8)) (b20)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (e15b.symm)) (e14a))
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    ·
                                      rcases h10 with (⟨e17a, e17b⟩ | e17a) | (⟨e17a, e17b⟩ | e17a)
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (e20b.symm)) (e17b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (e20b.symm)) (e17b)) (e7a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20b)) (e21a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20b)) (b22)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (e22a)) (e21a.symm)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e22a)) (e21a.symm)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (e22a)) (e4a.symm)) (e8a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e22a)) (e4a.symm)) (e8a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (e20a.symm)) (e17b)) (e7a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20a)) (b10)) (e21a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20a)) (b10)) (b22)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e20b)) (b14)) (e17b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e20b)) (b14)) (e17b)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17a)) (e21a.symm)) (e20a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e22b)) (b22)) (e21a)) (b3)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e22a)) (b10)) (b22)) (e21a)) (b3)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (e22b.symm)) (e21a)) (b3)) (e7a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (e22a.symm)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e20a)) (b2)) (b14)) (e17b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e20a)) (b2)) (b14)) (e17b)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e21b.symm)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17a)) (e21a.symm)) (e20a))
                                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e19a)) (e5a.symm)) (e0a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e19b)) (b14)) (e17b)) (e7a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e19a)) (b2)) (b14)) (e17b)) (e7a))
                                        · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e18a)) (e3a.symm)) (e0a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e18b)) (b14)) (e17b)) (e7a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e18a)) (b2)) (b14)) (e17b)) (e7a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e3b)) (e18b.symm)) (e17a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5b)) (e19b.symm)) (e17a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (e20b.symm)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (e20b.symm)) (e17a)) (b3)) (e7a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e22b)) (b22)) (e21b)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e22a)) (b10)) (b22)) (e21b)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (e22b.symm)) (e21b)) (e7a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e13b.symm)) (e23b)) (b22)) (e21b)) (e7a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e13b.symm)) (e23a)) (b10)) (b22)) (e21b)) (e7a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e6b)) (e23b.symm)) (e21b)) (e7a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e14a.symm)) (e24b)) (e21a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e14a.symm)) (e24a)) (b10)) (e21a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21b.symm)) (e24b)) (e16a)) (e5a.symm)) (e0a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21b.symm)) (e24a)) (b8)) (e16a)) (e5a.symm)) (e0a))
                                              · exact (lt_irrefl x31) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b22) (e21a)) (e17a.symm)) (e20b))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (e20a.symm)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b10) (e21a)) (e17a.symm)) (e20a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b10) (b22)) (e21a)) (e17a.symm)) (e20a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e20b)) (b14)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e20b)) (b14)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (e21a.symm)) (e20a))
                                              · exact (lt_irrefl x7) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b14) (e17a)) (e21a.symm)) (e20b))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e20a)) (b2)) (b14)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e20a)) (b2)) (b14)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e21b.symm)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (e21a.symm)) (e20a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e19b)) (b14)) (e17a)) (b3)) (e7a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e19a)) (b2)) (b14)) (e17a)) (b3)) (e7a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e18b)) (b14)) (e17a)) (b3)) (e7a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e18a)) (b2)) (b14)) (e17a)) (b3)) (e7a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e18b)) (e8a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e18a)) (b6)) (e8a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e19b)) (e9a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e19a)) (b9)) (e9a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (e20a)) (e21a.symm)) (e7a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (e24b.symm)) (e14a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (e24a.symm)) (e14a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e24b)) (b20)) (e14a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e24a)) (b8)) (b20)) (e14a))
                                                  · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e13b.symm)) (e23a)) (e21a.symm)) (e11a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (e23a)) (e6a.symm)) (e9a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e23a)) (e6a.symm)) (e9a))
                                                · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e12b.symm)) (e22a)) (e21a.symm)) (e11a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (e22a)) (e4a.symm)) (e8a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e22a)) (e4a.symm)) (e8a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e20b)) (b22)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e20b)) (b22)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e20a)) (e21a.symm)) (e7a))
                                              · exact (lt_irrefl x7) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b14) (e20a)) (e21a.symm)) (e17b))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e20a)) (b10)) (b22)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e20a)) (b10)) (b22)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (e20a)) (e17a.symm)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (e20a)) (e17a.symm)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (e20b.symm)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (e20b.symm)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e20a)) (e17a.symm)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e20a)) (e17a.symm)) (e7a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e22b)) (b22)) (e21b)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e22a)) (b10)) (b22)) (e21b)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (e22b.symm)) (e21b)) (e7a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e13b.symm)) (e23b)) (b22)) (e21b)) (e7a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e13b.symm)) (e23a)) (b10)) (b22)) (e21b)) (e7a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e6b)) (e23b.symm)) (e21b)) (e7a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e14a.symm)) (e24b)) (e21a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e14a.symm)) (e24a)) (b10)) (e21a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21b.symm)) (e24b)) (e16a)) (e5a.symm)) (e0a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21b.symm)) (e24a)) (b8)) (e16a)) (e5a.symm)) (e0a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17a)) (e20a.symm)) (e21a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e19a)) (e17a.symm)) (e7a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e18a)) (e17a.symm)) (e7a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e18b)) (e8a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e18a)) (b6)) (e8a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (e18a.symm)) (e8a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e19b)) (e9a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e19a)) (b9)) (e9a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (e19a.symm)) (e9a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (e20a)) (e21a.symm)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e20b)) (b22)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e20b)) (b22)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e20a)) (e21a.symm)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e20a)) (b10)) (b22)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e20a)) (b10)) (b22)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (e22a)) (e21a.symm)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e22a)) (e21a.symm)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (e22a)) (e4a.symm)) (e8a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e22a)) (e4a.symm)) (e8a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b10) (e20a)) (e17a.symm)) (e21a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (e20b.symm)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (e20b.symm)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x31) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b22) (e20a)) (e17a.symm)) (e21b))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b10) (b22)) (e20a)) (e17a.symm)) (e21a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (e20a.symm)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (e20a.symm)) (e21a)) (b3)) (e7a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e14a.symm)) (e16a)) (e5a.symm)) (e0a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e16b)) (b20)) (e14a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e16a)) (b8)) (b20)) (e14a))
                              · exact (lt_irrefl x16) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b17) (e13a)) (e10a.symm)) (e9b.symm)) (e6b))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e13a)) (e6a.symm)) (e9a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e13a)) (e6a.symm)) (e9a))
                            · exact (lt_irrefl x13) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b16) (e12a)) (e10a.symm)) (e8b.symm)) (e4b))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12a)) (e4a.symm)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e12a)) (e4a.symm)) (e8a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x4) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b13) (e10a)) (e11a.symm)) (e7b))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11b)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11a)) (b7)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11b)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11a)) (b7)) (b19)) (e10a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (b16)) (e12b)) (b19)) (e10a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (b16)) (e12a)) (b7)) (b19)) (e10a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (e12b.symm)) (e10a))
                            ·
                              rcases h21 with (⟨e13a, e13b⟩ | e13a) | (⟨e13a, e13b⟩ | e13a)
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e6b)) (b17)) (e13b)) (b19)) (e10a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e6b)) (b17)) (e13a)) (b7)) (b19)) (e10a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e6b)) (e13b.symm)) (e10a))
                              ·
                                rcases h8 with (⟨e14a, e14b⟩ | e14a) | (⟨e14a, e14b⟩ | e14a)
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e16b)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e16a)) (b9)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14a)) (e16a.symm)) (e9a))
                                    ·
                                      rcases h10 with (⟨e17a, e17b⟩ | e17a) | (⟨e17a, e17b⟩ | e17a)
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (e20b.symm)) (e17b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (e20b.symm)) (e17b)) (e7a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20b)) (e21a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20b)) (b22)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (e22a)) (e21a.symm)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (e15b.symm)) (e22a)) (e21a.symm)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (e22a)) (e4a.symm)) (e8a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e22a)) (e4a.symm)) (e8a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (e20a.symm)) (e17b)) (e7a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20a)) (b10)) (e21a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20a)) (b10)) (b22)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e20b)) (b14)) (e17b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e20b)) (b14)) (e17b)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17a)) (e21a.symm)) (e20a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (e15b.symm)) (e22b)) (b22)) (e21a)) (b3)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (e15b.symm)) (e22a)) (b10)) (b22)) (e21a)) (b3)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (e22b.symm)) (e21a)) (b3)) (e7a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (e22a.symm)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e20a)) (b2)) (b14)) (e17b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e20a)) (b2)) (b14)) (e17b)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e21b.symm)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17a)) (e21a.symm)) (e20a))
                                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e19a)) (e5a.symm)) (e0a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e19b)) (b14)) (e17b)) (e7a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e19a)) (b2)) (b14)) (e17b)) (e7a))
                                        · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e18a)) (e3a.symm)) (e0a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e18b)) (b14)) (e17b)) (e7a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e18a)) (b2)) (b14)) (e17b)) (e7a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e3b)) (e18b.symm)) (e17a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5b)) (e19b.symm)) (e17a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (e20b.symm)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (e20b.symm)) (e17a)) (b3)) (e7a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (e15b.symm)) (e22b)) (b22)) (e21b)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (e15b.symm)) (e22a)) (b10)) (b22)) (e21b)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (e22b.symm)) (e21b)) (e7a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e6b)) (b17)) (e23b)) (b22)) (e21b)) (e7a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e6b)) (b17)) (e23a)) (b10)) (b22)) (e21b)) (e7a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e6b)) (e23b.symm)) (e21b)) (e7a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e24b)) (b22)) (e21b)) (e7a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e24a)) (b10)) (b22)) (e21b)) (e7a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (e24b.symm)) (e21b)) (e7a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14a)) (e24a.symm)) (e21b)) (e7a))
                                              · exact (lt_irrefl x31) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b22) (e21a)) (e17a.symm)) (e20b))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (e20a.symm)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b10) (e21a)) (e17a.symm)) (e20a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b10) (b22)) (e21a)) (e17a.symm)) (e20a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e20b)) (b14)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e20b)) (b14)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (e21a.symm)) (e20a))
                                              · exact (lt_irrefl x7) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b14) (e17a)) (e21a.symm)) (e20b))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e20a)) (b2)) (b14)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e20a)) (b2)) (b14)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e21b.symm)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (e21a.symm)) (e20a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e19b)) (b14)) (e17a)) (b3)) (e7a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e19a)) (b2)) (b14)) (e17a)) (b3)) (e7a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e18b)) (b14)) (e17a)) (b3)) (e7a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e18a)) (b2)) (b14)) (e17a)) (b3)) (e7a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e18b)) (e8a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e18a)) (b6)) (e8a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e19b)) (e9a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e19a)) (b9)) (e9a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (e20a)) (e21a.symm)) (e7a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b8) (e24a)) (e22a.symm)) (e15a))
                                                    · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b8) (b20)) (e24a)) (e22a.symm)) (e15a))
                                                    · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b8) (e15b.symm)) (e22b)) (e24a))
                                                    · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b8) (e15b.symm)) (e22b)) (b22)) (e24a))
                                                  · exact (lt_irrefl x16) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b17) (e23a)) (e20a.symm)) (e19b.symm)) (e6b))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (e23a)) (e6a.symm)) (e9a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e23a)) (e6a.symm)) (e9a))
                                                · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b8) (e15b.symm)) (e22a)) (e20a.symm)) (e19b.symm)) (e16a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (e22a)) (e4a.symm)) (e8a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e22a)) (e4a.symm)) (e8a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e20b)) (b22)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e20b)) (b22)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e20a)) (e21a.symm)) (e7a))
                                              · exact (lt_irrefl x7) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b14) (e20a)) (e21a.symm)) (e17b))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e20a)) (b10)) (b22)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e20a)) (b10)) (b22)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (e20a)) (e17a.symm)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (e20a)) (e17a.symm)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (e20b.symm)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (e20b.symm)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e20a)) (e17a.symm)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e20a)) (e17a.symm)) (e7a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (e15b.symm)) (e22b)) (b22)) (e21b)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (e15b.symm)) (e22a)) (b10)) (b22)) (e21b)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (e22b.symm)) (e21b)) (e7a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e6b)) (b17)) (e23b)) (b22)) (e21b)) (e7a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e6b)) (b17)) (e23a)) (b10)) (b22)) (e21b)) (e7a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e6b)) (e23b.symm)) (e21b)) (e7a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e24b)) (b22)) (e21b)) (e7a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e24a)) (b10)) (b22)) (e21b)) (e7a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (e24b.symm)) (e21b)) (e7a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14a)) (e24a.symm)) (e21b)) (e7a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17a)) (e20a.symm)) (e21a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e19a)) (e17a.symm)) (e7a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e18a)) (e17a.symm)) (e7a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e18b)) (e8a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e18a)) (b6)) (e8a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (e18a.symm)) (e8a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e19b)) (e9a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e19a)) (b9)) (e9a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (e19a.symm)) (e9a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (e20a)) (e21a.symm)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e20b)) (b22)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e20b)) (b22)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e20a)) (e21a.symm)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e20a)) (b10)) (b22)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e20a)) (b10)) (b22)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (e22a)) (e21a.symm)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (e15b.symm)) (e22a)) (e21a.symm)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (e22a)) (e4a.symm)) (e8a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e22a)) (e4a.symm)) (e8a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b10) (e20a)) (e17a.symm)) (e21a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (e20b.symm)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (e20b.symm)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x31) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b22) (e20a)) (e17a.symm)) (e21b))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b10) (b22)) (e20a)) (e17a.symm)) (e21a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (e20a.symm)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (e20a.symm)) (e21a)) (b3)) (e7a))
                                  · exact (lt_irrefl x13) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b16) (e15a)) (e14a.symm)) (e8b.symm)) (e4b))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (e15a)) (e4a.symm)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e15a)) (e4a.symm)) (e8a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x4) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b13) (e14a)) (e15a.symm)) (e4b.symm)) (e8b))
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (b20)) (e16b)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (b20)) (e16a)) (b9)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (e16a.symm)) (e9a))
                                    · exact (lt_irrefl x4) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b13) (e14a)) (e16a.symm)) (e9b))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (e15a)) (e4a.symm)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (b20)) (e15a)) (e4a.symm)) (e8a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (b16)) (e15b)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (b16)) (e15a)) (b8)) (e14a))
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e16b)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e16a)) (b9)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e16b)) (e14a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e16a)) (b8)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e15a)) (e4a.symm)) (e8a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (b16)) (e15b)) (b20)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (b16)) (e15a)) (b8)) (b20)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (e15b.symm)) (e14a))
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    ·
                                      rcases h10 with (⟨e17a, e17b⟩ | e17a) | (⟨e17a, e17b⟩ | e17a)
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (e20b.symm)) (e17b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (e20b.symm)) (e17b)) (e7a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20b)) (e21a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20b)) (b22)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (e22a)) (e21a.symm)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (b16)) (e22a)) (e21a.symm)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (e22a)) (e4a.symm)) (e8a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e22a)) (e4a.symm)) (e8a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (e20a.symm)) (e17b)) (e7a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20a)) (b10)) (e21a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20a)) (b10)) (b22)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e20b)) (b14)) (e17b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e20b)) (b14)) (e17b)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17a)) (e21a.symm)) (e20a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (b16)) (e22b)) (b22)) (e21a)) (b3)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (b16)) (e22a)) (b10)) (b22)) (e21a)) (b3)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (e22b.symm)) (e21a)) (b3)) (e7a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e1a)) (e22a.symm)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e20a)) (b2)) (b14)) (e17b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e20a)) (b2)) (b14)) (e17b)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e21b.symm)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17a)) (e21a.symm)) (e20a))
                                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e19a)) (e5a.symm)) (e0a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e19b)) (b14)) (e17b)) (e7a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e19a)) (b2)) (b14)) (e17b)) (e7a))
                                        · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e18a)) (e3a.symm)) (e0a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e18b)) (b14)) (e17b)) (e7a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e18a)) (b2)) (b14)) (e17b)) (e7a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e3b)) (e18b.symm)) (e17a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e0b.symm)) (e5b)) (e19b.symm)) (e17a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (e20b.symm)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (e20b.symm)) (e17a)) (b3)) (e7a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (b16)) (e22b)) (b22)) (e21b)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (b16)) (e22a)) (b10)) (b22)) (e21b)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (e22b.symm)) (e21b)) (e7a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e6b)) (b17)) (e23b)) (b22)) (e21b)) (e7a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e6b)) (b17)) (e23a)) (b10)) (b22)) (e21b)) (e7a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e6b)) (e23b.symm)) (e21b)) (e7a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e14a.symm)) (e24b)) (e21a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e14a.symm)) (e24a)) (b10)) (e21a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21b.symm)) (e24b)) (e16a)) (e5a.symm)) (e0a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21b.symm)) (e24a)) (b8)) (e16a)) (e5a.symm)) (e0a))
                                              · exact (lt_irrefl x31) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b22) (e21a)) (e17a.symm)) (e20b))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (e20a.symm)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b10) (e21a)) (e17a.symm)) (e20a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b10) (b22)) (e21a)) (e17a.symm)) (e20a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e20b)) (b14)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e20b)) (b14)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (e21a.symm)) (e20a))
                                              · exact (lt_irrefl x7) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b14) (e17a)) (e21a.symm)) (e20b))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e20a)) (b2)) (b14)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e20a)) (b2)) (b14)) (e17a)) (b3)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e21b.symm)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (e21a.symm)) (e20a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e19b)) (b14)) (e17a)) (b3)) (e7a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e19a)) (b2)) (b14)) (e17a)) (b3)) (e7a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e18b)) (b14)) (e17a)) (b3)) (e7a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e18a)) (b2)) (b14)) (e17a)) (b3)) (e7a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e18b)) (e8a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e18a)) (b6)) (e8a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e19b)) (e9a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e19a)) (b9)) (e9a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (e20a)) (e21a.symm)) (e7a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (e24b.symm)) (e14a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (e24a.symm)) (e14a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e24b)) (b20)) (e14a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e24a)) (b8)) (b20)) (e14a))
                                                  · exact (lt_irrefl x16) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b17) (e23a)) (e20a.symm)) (e19b.symm)) (e6b))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (e23a)) (e6a.symm)) (e9a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e23a)) (e6a.symm)) (e9a))
                                                · exact (lt_irrefl x13) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b16) (e22a)) (e20a.symm)) (e18b.symm)) (e4b))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (e22a)) (e4a.symm)) (e8a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e22a)) (e4a.symm)) (e8a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e20b)) (b22)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e20b)) (b22)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e20a)) (e21a.symm)) (e7a))
                                              · exact (lt_irrefl x7) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b14) (e20a)) (e21a.symm)) (e17b))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e20a)) (b10)) (b22)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (b14)) (e20a)) (b10)) (b22)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (e20a)) (e17a.symm)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (e20a)) (e17a.symm)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (e20b.symm)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17b)) (e20b.symm)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e20a)) (e17a.symm)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21a)) (b10)) (b22)) (e20a)) (e17a.symm)) (e7a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (b16)) (e22b)) (b22)) (e21b)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (b16)) (e22a)) (b10)) (b22)) (e21b)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (e22b.symm)) (e21b)) (e7a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e6b)) (b17)) (e23b)) (b22)) (e21b)) (e7a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e6b)) (b17)) (e23a)) (b10)) (b22)) (e21b)) (e7a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e6b)) (e23b.symm)) (e21b)) (e7a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e14a.symm)) (e24b)) (e21a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e14a.symm)) (e24a)) (b10)) (e21a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21b.symm)) (e24b)) (e16a)) (e5a.symm)) (e0a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21b.symm)) (e24a)) (b8)) (e16a)) (e5a.symm)) (e0a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17a)) (e20a.symm)) (e21a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e19a)) (e17a.symm)) (e7a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e18a)) (e17a.symm)) (e7a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e18b)) (e8a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e18a)) (b6)) (e8a))
                                        · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (e18a.symm)) (e8a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e19b)) (e9a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e19a)) (b9)) (e9a))
                                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (e19a.symm)) (e9a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (e20a)) (e21a.symm)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e20b)) (b22)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e20b)) (b22)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e20a)) (e21a.symm)) (e7a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e20a)) (b10)) (b22)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (b14)) (e20a)) (b10)) (b22)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (e22a)) (e21a.symm)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8b.symm)) (e4b)) (b16)) (e22a)) (e21a.symm)) (e7a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (e22a)) (e4a.symm)) (e8a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e21b)) (b22)) (e22a)) (e4a.symm)) (e8a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b10) (e20a)) (e17a.symm)) (e21a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (e20b.symm)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (b2)) (e20b.symm)) (e21a)) (b3)) (e7a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x31) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b22) (e20a)) (e17a.symm)) (e21b))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b10) (b22)) (e20a)) (e17a.symm)) (e21a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (e20a.symm)) (e21b)) (e7a))
                                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e17a)) (e20a.symm)) (e21a)) (b3)) (e7a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e14a.symm)) (e16a)) (e5a.symm)) (e0a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e16b)) (b20)) (e14a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9b.symm)) (e16a)) (b8)) (b20)) (e14a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e10a.symm)) (e11a))
                      · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b5) (e6b.symm)) (e9a)) (e7a.symm)) (e0b.symm)) (e2a))
                    · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e4b.symm)) (e8a)) (e7a.symm)) (e0b.symm)) (e1a))
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e3b.symm)) (e0b)) (b15)) (e7a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (e3b.symm)) (e0b)) (b15)) (e7a))
                    · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e7a)) (e8a.symm)) (e3b.symm)) (e0b))
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (e5b.symm)) (e0b)) (b15)) (e7a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (b9)) (e5b.symm)) (e0b)) (b15)) (e7a))
                      · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e4b.symm)) (e8a)) (e9a.symm)) (e5b.symm)) (e1a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e12a)) (e11a.symm)) (e0b.symm)) (e1a))
                            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e12a)) (e11a.symm)) (e0b.symm)) (e1a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12b)) (e4b.symm)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12a)) (b4)) (e4b.symm)) (e8a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x22) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b19) (e10a)) (e7a.symm)) (e11b))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e4b.symm)) (e8a)) (e10a.symm)) (e11b)) (e0b.symm)) (e1a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e10a.symm)) (e11a))
                · exact (lt_irrefl x28) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b21) (e6a)) (e2a.symm)) (e5b))
              ·
                rcases h22 with (⟨e6a, e6b⟩ | e6a) | (⟨e6a, e6b⟩ | e6a)
                · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b5) (e6a)) (e5a.symm)) (e2a))
                · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b5) (b17)) (e6a)) (e5a.symm)) (e2a))
                · exact (lt_irrefl x27) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b9) (e6a)) (e2a.symm)) (e5a))
                · exact (lt_irrefl x27) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b9) (b21)) (e6a)) (e2a.symm)) (e5a))
              · exact (lt_irrefl x27) (lt_trans (lt_of_lt_of_eq (b9) (e5a)) (b28))
              · exact (lt_irrefl x27) (lt_trans (lt_of_lt_of_eq (lt_trans (b9) (b21)) (e5a)) (b28))
            · exact (lt_irrefl x19) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b18) (e4a)) (e1a.symm)) (e3b))
          ·
            rcases h17 with (⟨e4a, e4b⟩ | e4a) | (⟨e4a, e4b⟩ | e4a)
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e4a)) (e3a.symm)) (e1a))
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e4a)) (e3a.symm)) (e1a))
            · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4a)) (e1a.symm)) (e3a))
            · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b6) (b18)) (e4a)) (e1a.symm)) (e3a))
          · exact (lt_irrefl x18) (lt_trans (lt_of_lt_of_eq (b6) (e3a)) (b27))
          · exact (lt_irrefl x18) (lt_trans (lt_of_lt_of_eq (lt_trans (b6) (b18)) (e3a)) (b27))
        · exact (lt_irrefl x15) (lt_trans (lt_of_lt_of_eq (b5) (e2a)) (b26))
        · exact (lt_irrefl x15) (lt_trans (lt_of_lt_of_eq (lt_trans (b5) (b17)) (e2a)) (b26))
      · exact (lt_irrefl x12) (lt_trans (lt_of_lt_of_eq (b4) (e1a)) (b25))
      · exact (lt_irrefl x12) (lt_trans (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e1a)) (b25))
    ·
      rcases h1 with (⟨e1a, e1b⟩ | e1a) | (⟨e1a, e1b⟩ | e1a)
      ·
        rcases h2 with (⟨e2a, e2b⟩ | e2a) | (⟨e2a, e2b⟩ | e2a)
        ·
          rcases h3 with (⟨e3a, e3b⟩ | e3a) | (⟨e3a, e3b⟩ | e3a)
          ·
            rcases h17 with (⟨e4a, e4b⟩ | e4a) | (⟨e4a, e4b⟩ | e4a)
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e4a)) (e3a.symm)) (e1a))
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e4a)) (e3a.symm)) (e1a))
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e1b.symm)) (e3b)) (e4a))
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e1b.symm)) (e3b)) (b18)) (e4a))
          ·
            rcases h17 with (⟨e4a, e4b⟩ | e4a) | (⟨e4a, e4b⟩ | e4a)
            ·
              rcases h4 with (⟨e5a, e5b⟩ | e5a) | (⟨e5a, e5b⟩ | e5a)
              ·
                rcases h22 with (⟨e6a, e6b⟩ | e6a) | (⟨e6a, e6b⟩ | e6a)
                · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e1b.symm)) (e2b)) (e6a)) (e5a.symm)) (e1a))
                · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e1b.symm)) (e2b)) (b17)) (e6a)) (e5a.symm)) (e1a))
                · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e1b.symm)) (e5b)) (e6a)) (e2a.symm)) (e1a))
                · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e1b.symm)) (e5b)) (b21)) (e6a)) (e2a.symm)) (e1a))
              ·
                rcases h22 with (⟨e6a, e6b⟩ | e6a) | (⟨e6a, e6b⟩ | e6a)
                ·
                  rcases h5 with (⟨e7a, e7b⟩ | e7a) | (⟨e7a, e7b⟩ | e7a)
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e10a.symm)) (e7a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11a)) (e10a.symm)) (e7a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e10b)) (e11a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e10b)) (b19)) (e11a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e12a.symm)) (e1b.symm)) (e0a))
                            ·
                              rcases h21 with (⟨e13a, e13b⟩ | e13a) | (⟨e13a, e13b⟩ | e13a)
                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e13a.symm)) (e2b.symm)) (e0a))
                              ·
                                rcases h8 with (⟨e14a, e14b⟩ | e14a) | (⟨e14a, e14b⟩ | e14a)
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14b)) (e16a)) (e5a.symm)) (e0a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14b)) (b20)) (e16a)) (e5a.symm)) (e0a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e9b)) (e16a)) (e14a.symm)) (e7a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e9b)) (b21)) (e16a)) (e14a.symm)) (e7a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e12a.symm)) (e15a)) (e14a.symm)) (e7a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14b)) (b20)) (e15b)) (e1b.symm)) (e0a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14b)) (b20)) (e15a)) (b4)) (e1b.symm)) (e0a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14a)) (e15a.symm)) (e1b.symm)) (e0a))
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14a)) (b8)) (e16a)) (e5a.symm)) (e0a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14a)) (b8)) (b20)) (e16a)) (e5a.symm)) (e0a))
                                    ·
                                      rcases h10 with (⟨e17a, e17b⟩ | e17a) | (⟨e17a, e17b⟩ | e17a)
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20b)) (e21a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20b)) (b22)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e22a.symm)) (e1b.symm)) (e0a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e23a.symm)) (e2b.symm)) (e0a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b8) (e24a)) (e22a.symm)) (e15a))
                                                    · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b8) (b20)) (e24a)) (e22a.symm)) (e15a))
                                                    · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e11b.symm)) (e21b)) (e24a)) (e14a.symm)) (e10a))
                                                    · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e11b.symm)) (e21b)) (b22)) (e24a)) (e14a.symm)) (e10a))
                                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21b)) (b22)) (e23b)) (e2b.symm)) (e0a))
                                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21b)) (b22)) (e23a)) (b5)) (e2b.symm)) (e0a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21b)) (b22)) (e22b)) (e1b.symm)) (e0a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21b)) (b22)) (e22a)) (b4)) (e1b.symm)) (e0a))
                                              · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e11b.symm)) (e21a)) (e20a.symm)) (e17b)) (e11a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20a)) (b10)) (e21a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20a)) (b10)) (b22)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21b)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21a)) (b10)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17a)) (e21a.symm)) (e20a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (e4b.symm)) (e22b)) (e20a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (e4b.symm)) (e22a)) (b10)) (e20a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19b)) (e6b.symm)) (e23b)) (e20a))
                                                  · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19b)) (e6b.symm)) (e23a)) (b10)) (e20a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19b)) (b21)) (e16b)) (b20)) (e24b)) (e20a))
                                                    · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19b)) (b21)) (e16b)) (b20)) (e24a)) (b10)) (e20a))
                                                    · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19b)) (e16a)) (e24a.symm)) (e20a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14a)) (e24a.symm)) (e21a))
                                                  · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e23a)) (e2a.symm)) (e1a)) (e22a.symm)) (e20a))
                                                · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e1b.symm)) (e0a)) (e21a.symm)) (e22a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21b)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21a)) (b10)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e21b.symm)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17a)) (e21a.symm)) (e20a))
                                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e19a)) (e5a.symm)) (e0a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e7b.symm)) (e9b)) (e19a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e7b.symm)) (e9b)) (b21)) (e19a))
                                        · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e18a)) (e3a.symm)) (e0a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e7b.symm)) (e8b)) (e18a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e7b.symm)) (e8b)) (b18)) (e18a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e8b)) (e18b.symm)) (e17a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e9b)) (e19b.symm)) (e17a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21b)) (e20b.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21a)) (b10)) (e20b.symm)) (e17a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e12a.symm)) (e22b)) (e21a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e12a.symm)) (e22a)) (b10)) (e21a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21b.symm)) (e22b)) (e1b.symm)) (e0a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21b.symm)) (e22a)) (b4)) (e1b.symm)) (e0a))
                                              · exact (lt_irrefl x31) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b22) (e21a)) (e17a.symm)) (e20b))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b10) (e21a)) (e17a.symm)) (e20a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b10) (b22)) (e21a)) (e17a.symm)) (e20a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21b)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21a)) (b10)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (e21a.symm)) (e20a))
                                              · exact (lt_irrefl x7) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b14) (e17a)) (e21a.symm)) (e20b))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21b)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21a)) (b10)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e21b.symm)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (e21a.symm)) (e20a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e7b.symm)) (e9b)) (e19a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e7b.symm)) (e9b)) (b21)) (e19a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e7b.symm)) (e8b)) (e18a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e7b.symm)) (e8b)) (b18)) (e18a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (e8b.symm)) (e7b)) (e17a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18a)) (b6)) (e8b.symm)) (e7b)) (e17a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19b)) (e9b.symm)) (e7b)) (e17a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19a)) (b9)) (e9b.symm)) (e7b)) (e17a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20a)) (e21a.symm)) (e17a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (e22b.symm)) (e4b)) (e18a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20a)) (e22a.symm)) (e4b)) (e18a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e22b)) (b16)) (e4b)) (e18a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e22a)) (b4)) (b16)) (e4b)) (e18a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21b)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21a)) (b3)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x7) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b14) (e20a)) (e21a.symm)) (e17b))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21b)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21a)) (b3)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21b)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21a)) (b10)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21b)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21a)) (b3)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21b)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21a)) (b10)) (b22)) (e20a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e12a.symm)) (e22b)) (e21a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e12a.symm)) (e22a)) (b10)) (e21a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21b.symm)) (e22b)) (e1b.symm)) (e0a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21b.symm)) (e22a)) (b4)) (e1b.symm)) (e0a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17a)) (e20a.symm)) (e21a))
                                          · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b8) (e16b.symm)) (e19a)) (e17a.symm)) (e7b.symm)) (e14a))
                                        · exact (lt_irrefl x19) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b18) (e18a)) (e17a.symm)) (e7b.symm)) (e8b))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (e8b.symm)) (e7b)) (b15)) (e17a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18a)) (b6)) (e8b.symm)) (e7b)) (b15)) (e17a))
                                        · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e11b.symm)) (e17a)) (e18a.symm)) (e4b.symm)) (e12a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19b)) (e9b.symm)) (e7b)) (b15)) (e17a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19a)) (b9)) (e9b.symm)) (e7b)) (b15)) (e17a))
                                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e11b.symm)) (e17a)) (e19a.symm)) (e6b.symm)) (e13a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (e21b.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21b)) (b15)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21a)) (b3)) (b15)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (e21b.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21b)) (b15)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21a)) (b3)) (b15)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e22a.symm)) (e1b.symm)) (e0a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e23a.symm)) (e2b.symm)) (e0a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e11b.symm)) (e17a)) (e19a.symm)) (e16b)) (e24a)) (e21a.symm)) (e11a))
                                                    · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e11b.symm)) (e17a)) (e19a.symm)) (e16b)) (b20)) (e24a)) (e21a.symm)) (e11a))
                                                    · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e24b)) (e16b.symm)) (e19a))
                                                    · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e24a)) (b8)) (e16b.symm)) (e19a))
                                                  · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e23b)) (b17)) (e6b)) (b21)) (e19a))
                                                  · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e23a)) (b5)) (b17)) (e6b)) (b21)) (e19a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e22b)) (b16)) (e4b)) (b18)) (e18a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e22a)) (b4)) (b16)) (e4b)) (b18)) (e18a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b10) (e20a)) (e17a.symm)) (e21a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21b)) (b15)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21a)) (b3)) (b15)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x31) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b22) (e20a)) (e17a.symm)) (e21b))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b10) (b22)) (e20a)) (e17a.symm)) (e21a))
                                              · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e11b.symm)) (e17a)) (e20a.symm)) (e21b)) (e11a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e17a)) (e20a.symm)) (e21a))
                                    · exact (lt_irrefl x28) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b21) (e16a)) (e14a.symm)) (e9b))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14a)) (b8)) (b20)) (e15b)) (e1b.symm)) (e0a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14a)) (b8)) (b20)) (e15a)) (b4)) (e1b.symm)) (e0a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e4b.symm)) (e15b)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e4b.symm)) (e15a)) (b8)) (e14a))
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9a)) (e16a.symm)) (e14a))
                                    ·
                                      rcases h10 with (⟨e17a, e17b⟩ | e17a) | (⟨e17a, e17b⟩ | e17a)
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20b)) (e21a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20b)) (b22)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e22a.symm)) (e1b.symm)) (e0a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e23a.symm)) (e2b.symm)) (e0a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e21a)) (e24a.symm)) (e14a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e24a.symm)) (e14b)) (e7a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (b22)) (e24b)) (e14a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (b22)) (e24a)) (b8)) (e14a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (e23a)) (e2a.symm)) (e1a)) (e15a.symm)) (e14a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (b22)) (e23a)) (e2a.symm)) (e1a)) (e15a.symm)) (e14a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (e22a)) (e15a.symm)) (e14a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (b22)) (e22a)) (e15a.symm)) (e14a))
                                              · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e11b.symm)) (e21a)) (e20a.symm)) (e17b)) (e11a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20a)) (b10)) (e21a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20a)) (b10)) (b22)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21b)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21a)) (b10)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17a)) (e21a.symm)) (e20a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (e4b.symm)) (e22b)) (e20a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (e4b.symm)) (e22a)) (b10)) (e20a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (e6b.symm)) (e23b)) (e22a)) (e15a.symm)) (e14a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (e6b.symm)) (e23a)) (b10)) (e22a)) (e15a.symm)) (e14a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e24b)) (e22a)) (e15a.symm)) (e14a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e24a)) (b10)) (e22a)) (e15a.symm)) (e14a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e21a.symm)) (e24b)) (e14a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e21a.symm)) (e24a)) (b8)) (e14a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e21a.symm)) (e23a)) (e2a.symm)) (e1a)) (e15a.symm)) (e14a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e21a.symm)) (e22a)) (e15a.symm)) (e14a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21b)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21a)) (b10)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e21b.symm)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17a)) (e21a.symm)) (e20a))
                                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e19a)) (e5a.symm)) (e0a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e7b.symm)) (e9b)) (e19a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e7b.symm)) (e9b)) (b21)) (e19a))
                                        · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e18a)) (e3a.symm)) (e0a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e7b.symm)) (e8b)) (e18a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e7b.symm)) (e8b)) (b18)) (e18a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e8b)) (e18b.symm)) (e17a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e9b)) (e19b.symm)) (e17a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21b)) (e20b.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21a)) (b10)) (e20b.symm)) (e17a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e12a.symm)) (e22b)) (e21a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e12a.symm)) (e22a)) (b10)) (e21a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e21a.symm)) (e22a)) (e15a.symm)) (e14a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e21b.symm)) (e22a)) (e15a.symm)) (e14a))
                                              · exact (lt_irrefl x31) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b22) (e21a)) (e17a.symm)) (e20b))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b10) (e21a)) (e17a.symm)) (e20a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b10) (b22)) (e21a)) (e17a.symm)) (e20a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21b)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21a)) (b10)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (e21a.symm)) (e20a))
                                              · exact (lt_irrefl x7) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b14) (e17a)) (e21a.symm)) (e20b))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21b)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21a)) (b10)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e21b.symm)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (e21a.symm)) (e20a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e7b.symm)) (e9b)) (e19a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e7b.symm)) (e9b)) (b21)) (e19a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e7b.symm)) (e8b)) (e18a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e7b.symm)) (e8b)) (b18)) (e18a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (e8b.symm)) (e7b)) (e17a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18a)) (b6)) (e8b.symm)) (e7b)) (e17a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19b)) (e9b.symm)) (e7b)) (e17a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19a)) (b9)) (e9b.symm)) (e7b)) (e17a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20a)) (e21a.symm)) (e17a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (e22b.symm)) (e4b)) (e18a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20a)) (e22a.symm)) (e4b)) (e18a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21a)) (b10)) (e22a)) (e15a.symm)) (e14a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21a)) (b10)) (b22)) (e22a)) (e15a.symm)) (e14a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21b)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21a)) (b3)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x7) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b14) (e20a)) (e21a.symm)) (e17b))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21b)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21a)) (b3)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21b)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21a)) (b10)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21b)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21a)) (b3)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21b)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21a)) (b10)) (b22)) (e20a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e12a.symm)) (e22b)) (e21a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e12a.symm)) (e22a)) (b10)) (e21a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e21a.symm)) (e22a)) (e15a.symm)) (e14a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e21b.symm)) (e22a)) (e15a.symm)) (e14a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17a)) (e20a.symm)) (e21a))
                                          · exact (lt_irrefl x28) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b21) (e19a)) (e17a.symm)) (e7b.symm)) (e9b))
                                        · exact (lt_irrefl x19) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b18) (e18a)) (e17a.symm)) (e7b.symm)) (e8b))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (e8b.symm)) (e7b)) (b15)) (e17a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18a)) (b6)) (e8b.symm)) (e7b)) (b15)) (e17a))
                                        · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e11b.symm)) (e17a)) (e18a.symm)) (e4b.symm)) (e12a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19b)) (e9b.symm)) (e7b)) (b15)) (e17a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19a)) (b9)) (e9b.symm)) (e7b)) (b15)) (e17a))
                                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e11b.symm)) (e17a)) (e19a.symm)) (e6b.symm)) (e13a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (e21b.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21b)) (b15)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21a)) (b3)) (b15)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (e21b.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21b)) (b15)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21a)) (b3)) (b15)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e22a.symm)) (e1b.symm)) (e0a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e23a.symm)) (e2b.symm)) (e0a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e21a)) (e24a.symm)) (e14a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e24a.symm)) (e14b)) (e7a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (b22)) (e24b)) (e14a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (b22)) (e24a)) (b8)) (e14a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (e23a)) (e2a.symm)) (e1a)) (e15a.symm)) (e14a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (b22)) (e23a)) (e2a.symm)) (e1a)) (e15a.symm)) (e14a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (e22a)) (e15a.symm)) (e14a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (b22)) (e22a)) (e15a.symm)) (e14a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b10) (e20a)) (e17a.symm)) (e21a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21b)) (b15)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21a)) (b3)) (b15)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x31) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b22) (e20a)) (e17a.symm)) (e21b))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b10) (b22)) (e20a)) (e17a.symm)) (e21a))
                                              · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e11b.symm)) (e17a)) (e20a.symm)) (e21b)) (e11a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e17a)) (e20a.symm)) (e21a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (b21)) (e16b)) (e14a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (b21)) (e16a)) (b8)) (e14a))
                                  · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e4a)) (e8a.symm)) (e14b.symm)) (e15a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e4b.symm)) (e15b)) (b20)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e4b.symm)) (e15a)) (b8)) (b20)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8a)) (e4a.symm)) (e15b.symm)) (e14a))
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (e16b.symm)) (e14a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9a)) (e16a.symm)) (e14a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (b21)) (e16b)) (b20)) (e14a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (b21)) (e16a)) (b8)) (b20)) (e14a))
                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11b)) (b19)) (e13b)) (e2b.symm)) (e0a))
                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11b)) (b19)) (e13a)) (b5)) (e2b.symm)) (e0a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11b)) (b19)) (e12b)) (e1b.symm)) (e0a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11b)) (b19)) (e12a)) (b4)) (e1b.symm)) (e0a))
                          · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e11a)) (e10a.symm)) (e7b))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e10a)) (b7)) (e11a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e10a)) (b7)) (b19)) (e11a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e11b)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e11a)) (b7)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e11a.symm)) (e10a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e4b.symm)) (e12b)) (e10a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e4b.symm)) (e12a)) (b7)) (e10a))
                            ·
                              rcases h21 with (⟨e13a, e13b⟩ | e13a) | (⟨e13a, e13b⟩ | e13a)
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (e6b.symm)) (e13b)) (e10a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (e6b.symm)) (e13a)) (b7)) (e10a))
                              ·
                                rcases h8 with (⟨e14a, e14b⟩ | e14a) | (⟨e14a, e14b⟩ | e14a)
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14b)) (e16a)) (e5a.symm)) (e0a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14b)) (b20)) (e16a)) (e5a.symm)) (e0a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e9b)) (e16a)) (e14a.symm)) (e7a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e9b)) (b21)) (e16a)) (e14a.symm)) (e7a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e8b)) (e4b.symm)) (e15a)) (e14a.symm)) (e7a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (e15a)) (e12a.symm)) (e10a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e15a)) (e12a.symm)) (e10a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14a)) (e15a.symm)) (e1b.symm)) (e0a))
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14a)) (b8)) (e16a)) (e5a.symm)) (e0a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14a)) (b8)) (b20)) (e16a)) (e5a.symm)) (e0a))
                                    ·
                                      rcases h10 with (⟨e17a, e17b⟩ | e17a) | (⟨e17a, e17b⟩ | e17a)
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20b)) (e21a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20b)) (b22)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e22a.symm)) (e1b.symm)) (e0a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e23a.symm)) (e2b.symm)) (e0a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b8) (e24a)) (e22a.symm)) (e15a))
                                                    · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b8) (b20)) (e24a)) (e22a.symm)) (e15a))
                                                    · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b10) (e24a)) (e15a.symm)) (e22a))
                                                    · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b10) (b22)) (e24a)) (e15a.symm)) (e22a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (e23a)) (e13a.symm)) (e10a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (b22)) (e23a)) (e13a.symm)) (e10a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (e22a)) (e12a.symm)) (e10a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (b22)) (e22a)) (e12a.symm)) (e10a))
                                              · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e21a)) (e20a.symm)) (e17b))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20a)) (b10)) (e21a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20a)) (b10)) (b22)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21b)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21a)) (b10)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17a)) (e21a.symm)) (e20a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (e4b.symm)) (e22b)) (e20a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (e4b.symm)) (e22a)) (b10)) (e20a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (e6b.symm)) (e23b)) (e22a)) (e12a.symm)) (e10a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (e6b.symm)) (e23a)) (b10)) (e22a)) (e12a.symm)) (e10a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (b20)) (e24b)) (e22a)) (e12a.symm)) (e10a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (b20)) (e24a)) (b10)) (e22a)) (e12a.symm)) (e10a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (e24a.symm)) (e22a)) (e12a.symm)) (e10a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e14a)) (e24a.symm)) (e21a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e21a.symm)) (e23a)) (e13a.symm)) (e10a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e21a.symm)) (e22a)) (e12a.symm)) (e10a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21b)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21a)) (b10)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e21b.symm)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17a)) (e21a.symm)) (e20a))
                                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e19a)) (e5a.symm)) (e0a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e7b.symm)) (e9b)) (e19a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e7b.symm)) (e9b)) (b21)) (e19a))
                                        · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e18a)) (e3a.symm)) (e0a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e7b.symm)) (e8b)) (e18a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e7b.symm)) (e8b)) (b18)) (e18a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e8b)) (e18b.symm)) (e17a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e9b)) (e19b.symm)) (e17a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21b)) (e20b.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21a)) (b10)) (e20b.symm)) (e17a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e8b)) (e4b.symm)) (e22b)) (e21a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e8b)) (e4b.symm)) (e22a)) (b10)) (e21a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e21a.symm)) (e22a)) (e12a.symm)) (e10a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e21b.symm)) (e22a)) (e12a.symm)) (e10a))
                                              · exact (lt_irrefl x31) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b22) (e21a)) (e17a.symm)) (e20b))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b10) (e21a)) (e17a.symm)) (e20a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b10) (b22)) (e21a)) (e17a.symm)) (e20a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21b)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21a)) (b10)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (e21a.symm)) (e20a))
                                              · exact (lt_irrefl x7) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b14) (e17a)) (e21a.symm)) (e20b))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21b)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21a)) (b10)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e21b.symm)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (e21a.symm)) (e20a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e7b.symm)) (e9b)) (e19a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e7b.symm)) (e9b)) (b21)) (e19a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e7b.symm)) (e8b)) (e18a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e7b.symm)) (e8b)) (b18)) (e18a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (e8b.symm)) (e7b)) (e17a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18a)) (b6)) (e8b.symm)) (e7b)) (e17a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19b)) (e9b.symm)) (e7b)) (e17a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19a)) (b9)) (e9b.symm)) (e7b)) (e17a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20a)) (e21a.symm)) (e17a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (e22b.symm)) (e4b)) (e18a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20a)) (e22a.symm)) (e4b)) (e18a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21a)) (b10)) (e22a)) (e12a.symm)) (e10a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21a)) (b10)) (b22)) (e22a)) (e12a.symm)) (e10a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21b)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21a)) (b3)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x7) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b14) (e20a)) (e21a.symm)) (e17b))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21b)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21a)) (b3)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21b)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21a)) (b10)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21b)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21a)) (b3)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21b)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21a)) (b10)) (b22)) (e20a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e8b)) (e4b.symm)) (e22b)) (e21a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e8b)) (e4b.symm)) (e22a)) (b10)) (e21a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e21a.symm)) (e22a)) (e12a.symm)) (e10a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e21b.symm)) (e22a)) (e12a.symm)) (e10a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17a)) (e20a.symm)) (e21a))
                                          · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b8) (e16b.symm)) (e19a)) (e17a.symm)) (e7b.symm)) (e14a))
                                        · exact (lt_irrefl x19) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b18) (e18a)) (e17a.symm)) (e7b.symm)) (e8b))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (e8b.symm)) (e7b)) (b15)) (e17a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18a)) (b6)) (e8b.symm)) (e7b)) (b15)) (e17a))
                                        · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e17a)) (e18a.symm)) (e8b.symm)) (e7b))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19b)) (e9b.symm)) (e7b)) (b15)) (e17a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19a)) (b9)) (e9b.symm)) (e7b)) (b15)) (e17a))
                                          · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e17a)) (e19a.symm)) (e9b.symm)) (e7b))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (e21b.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21b)) (b15)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21a)) (b3)) (b15)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (e21b.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21b)) (b15)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21a)) (b3)) (b15)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e22a.symm)) (e1b.symm)) (e0a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e23a.symm)) (e2b.symm)) (e0a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b8) (e24a)) (e22a.symm)) (e15a))
                                                    · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b8) (b20)) (e24a)) (e22a.symm)) (e15a))
                                                    · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e24b)) (e16b.symm)) (e19a))
                                                    · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e24a)) (b8)) (e16b.symm)) (e19a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (e23a)) (e13a.symm)) (e10a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (b22)) (e23a)) (e13a.symm)) (e10a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (e22a)) (e12a.symm)) (e10a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (b22)) (e22a)) (e12a.symm)) (e10a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b10) (e20a)) (e17a.symm)) (e21a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21b)) (b15)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21a)) (b3)) (b15)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x31) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b22) (e20a)) (e17a.symm)) (e21b))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b10) (b22)) (e20a)) (e17a.symm)) (e21a))
                                              · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b8) (e16b.symm)) (e19a)) (e20a.symm)) (e21b)) (e7b.symm)) (e14a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e17a)) (e20a.symm)) (e21a))
                                    · exact (lt_irrefl x28) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b21) (e16a)) (e14a.symm)) (e9b))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (e15a)) (e12a.symm)) (e10a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (b20)) (e15a)) (e12a.symm)) (e10a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e4b.symm)) (e15b)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e4b.symm)) (e15a)) (b8)) (e14a))
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9a)) (e16a.symm)) (e14a))
                                    ·
                                      rcases h10 with (⟨e17a, e17b⟩ | e17a) | (⟨e17a, e17b⟩ | e17a)
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20b)) (e21a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20b)) (b22)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e22a.symm)) (e1b.symm)) (e0a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e23a.symm)) (e2b.symm)) (e0a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e21a)) (e24a.symm)) (e14a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e24a.symm)) (e14b)) (e7a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (b22)) (e24b)) (e14a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (b22)) (e24a)) (b8)) (e14a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (e23a)) (e13a.symm)) (e10a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (b22)) (e23a)) (e13a.symm)) (e10a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (e22a)) (e12a.symm)) (e10a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (b22)) (e22a)) (e12a.symm)) (e10a))
                                              · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e21a)) (e20a.symm)) (e17b))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20a)) (b10)) (e21a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20a)) (b10)) (b22)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21b)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21a)) (b10)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17a)) (e21a.symm)) (e20a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (e4b.symm)) (e22b)) (e20a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (e4b.symm)) (e22a)) (b10)) (e20a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (e6b.symm)) (e23b)) (e22a)) (e12a.symm)) (e10a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (e6b.symm)) (e23a)) (b10)) (e22a)) (e12a.symm)) (e10a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e24b)) (e22a)) (e12a.symm)) (e10a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e24a)) (b10)) (e22a)) (e12a.symm)) (e10a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e21a.symm)) (e24b)) (e14a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e21a.symm)) (e24a)) (b8)) (e14a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e21a.symm)) (e23a)) (e13a.symm)) (e10a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e21a.symm)) (e22a)) (e12a.symm)) (e10a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21b)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21a)) (b10)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e21b.symm)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17a)) (e21a.symm)) (e20a))
                                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e19a)) (e5a.symm)) (e0a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e7b.symm)) (e9b)) (e19a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e7b.symm)) (e9b)) (b21)) (e19a))
                                        · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e18a)) (e3a.symm)) (e0a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e7b.symm)) (e8b)) (e18a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e7b.symm)) (e8b)) (b18)) (e18a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e8b)) (e18b.symm)) (e17a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e9b)) (e19b.symm)) (e17a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21b)) (e20b.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21a)) (b10)) (e20b.symm)) (e17a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e8b)) (e4b.symm)) (e22b)) (e21a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e8b)) (e4b.symm)) (e22a)) (b10)) (e21a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e21a.symm)) (e22a)) (e12a.symm)) (e10a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e21b.symm)) (e22a)) (e12a.symm)) (e10a))
                                              · exact (lt_irrefl x31) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b22) (e21a)) (e17a.symm)) (e20b))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b10) (e21a)) (e17a.symm)) (e20a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b10) (b22)) (e21a)) (e17a.symm)) (e20a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21b)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21a)) (b10)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (e21a.symm)) (e20a))
                                              · exact (lt_irrefl x7) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b14) (e17a)) (e21a.symm)) (e20b))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21b)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21a)) (b10)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e21b.symm)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (e21a.symm)) (e20a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e7b.symm)) (e9b)) (e19a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e7b.symm)) (e9b)) (b21)) (e19a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e7b.symm)) (e8b)) (e18a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e7b.symm)) (e8b)) (b18)) (e18a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (e8b.symm)) (e7b)) (e17a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18a)) (b6)) (e8b.symm)) (e7b)) (e17a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19b)) (e9b.symm)) (e7b)) (e17a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19a)) (b9)) (e9b.symm)) (e7b)) (e17a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20a)) (e21a.symm)) (e17a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (e22b.symm)) (e4b)) (e18a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20a)) (e22a.symm)) (e4b)) (e18a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21a)) (b10)) (e22a)) (e12a.symm)) (e10a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21a)) (b10)) (b22)) (e22a)) (e12a.symm)) (e10a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21b)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21a)) (b3)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x7) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b14) (e20a)) (e21a.symm)) (e17b))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21b)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21a)) (b3)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21b)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21a)) (b10)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21b)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21a)) (b3)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21b)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21a)) (b10)) (b22)) (e20a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e8b)) (e4b.symm)) (e22b)) (e21a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e8b)) (e4b.symm)) (e22a)) (b10)) (e21a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e21a.symm)) (e22a)) (e12a.symm)) (e10a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e21b.symm)) (e22a)) (e12a.symm)) (e10a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17a)) (e20a.symm)) (e21a))
                                          · exact (lt_irrefl x28) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b21) (e19a)) (e17a.symm)) (e7b.symm)) (e9b))
                                        · exact (lt_irrefl x19) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b18) (e18a)) (e17a.symm)) (e7b.symm)) (e8b))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (e8b.symm)) (e7b)) (b15)) (e17a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18a)) (b6)) (e8b.symm)) (e7b)) (b15)) (e17a))
                                        · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e17a)) (e18a.symm)) (e8b.symm)) (e7b))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19b)) (e9b.symm)) (e7b)) (b15)) (e17a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19a)) (b9)) (e9b.symm)) (e7b)) (b15)) (e17a))
                                          · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e17a)) (e19a.symm)) (e9b.symm)) (e7b))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (e21b.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21b)) (b15)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21a)) (b3)) (b15)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (e21b.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21b)) (b15)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21a)) (b3)) (b15)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e22a.symm)) (e1b.symm)) (e0a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e23a.symm)) (e2b.symm)) (e0a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e21a)) (e24a.symm)) (e14a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e24a.symm)) (e14b)) (e7a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (b22)) (e24b)) (e14a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (b22)) (e24a)) (b8)) (e14a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (e23a)) (e13a.symm)) (e10a))
                                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (b22)) (e23a)) (e13a.symm)) (e10a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (e22a)) (e12a.symm)) (e10a))
                                                · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e21b)) (b22)) (e22a)) (e12a.symm)) (e10a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b10) (e20a)) (e17a.symm)) (e21a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21b)) (b15)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21a)) (b3)) (b15)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x31) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b22) (e20a)) (e17a.symm)) (e21b))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b10) (b22)) (e20a)) (e17a.symm)) (e21a))
                                              · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e17a)) (e20a.symm)) (e21b))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e17a)) (e20a.symm)) (e21a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (b21)) (e16b)) (e14a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (b21)) (e16a)) (b8)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e15a)) (e12a.symm)) (e10a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e4b.symm)) (e15b)) (b20)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e4b.symm)) (e15a)) (b8)) (b20)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8a)) (e4a.symm)) (e15b.symm)) (e14a))
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (e16b.symm)) (e14a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9a)) (e16a.symm)) (e14a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (b21)) (e16b)) (b20)) (e14a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (b21)) (e16a)) (b8)) (b20)) (e14a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e13a)) (e2a.symm)) (e1a)) (e12a.symm)) (e10a))
                            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e1b.symm)) (e0a)) (e11a.symm)) (e12a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e11b)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (b15)) (e11a)) (b7)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7b)) (e11b.symm)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e11a.symm)) (e10a))
                      · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e9a)) (e5a.symm)) (e0a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e0a.symm)) (e5a)) (b9)) (e9a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e0a.symm)) (e5a)) (b9)) (b21)) (e9a))
                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e8a)) (e3a.symm)) (e0a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e0a.symm)) (e3a)) (b6)) (e8a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e0a.symm)) (e3a)) (b6)) (b18)) (e8a))
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e8b.symm)) (e7a)) (e0a.symm)) (e3a))
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x27) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b9) (e9b.symm)) (e7a)) (e0a.symm)) (e5a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11b)) (e10b.symm)) (e7a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11a)) (b7)) (e10b.symm)) (e7a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e12b)) (e10b.symm)) (e8a))
                            · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e12a)) (b7)) (e10b.symm)) (e8a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12b)) (e1b.symm)) (e0a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12a)) (b4)) (e1b.symm)) (e0a))
                          · exact (lt_irrefl x22) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b19) (e11a)) (e7a.symm)) (e10b))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e10a.symm)) (e7a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11a)) (e10a.symm)) (e7a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e11a)) (e7a.symm)) (e10a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e11a)) (e7a.symm)) (e10a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (b15)) (e11b)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (b15)) (e11a)) (b7)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e11a.symm)) (e10a))
                          · exact (lt_irrefl x4) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b13) (e7a)) (e11a.symm)) (e10b))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (b15)) (e11b)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (b15)) (e11a)) (b7)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (e11b.symm)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e11a.symm)) (e10a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e0a.symm)) (e5a)) (b9)) (e9a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e0a.symm)) (e5a)) (b9)) (b21)) (e9a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e0a.symm)) (e3a)) (b6)) (e8a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e0a.symm)) (e3a)) (b6)) (b18)) (e8a))
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8a)) (e3a.symm)) (e0a)) (b3)) (e7a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (e3a.symm)) (e0a)) (b3)) (e7a))
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9a)) (e5a.symm)) (e0a)) (b3)) (e7a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (e5a.symm)) (e0a)) (b3)) (e7a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e4b)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e12a.symm)) (e4b)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e12b)) (b16)) (e4b)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e12a)) (b4)) (b16)) (e4b)) (e8a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x4) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b13) (e10a)) (e11a.symm)) (e7b))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11b)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11a)) (b7)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11b)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11a)) (b7)) (b19)) (e10a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e8a.symm)) (e4b.symm)) (e12b)) (e11a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e8a.symm)) (e4b.symm)) (e12a)) (b7)) (e11a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12b)) (e1b.symm)) (e0a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12a)) (b4)) (e1b.symm)) (e0a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e10a.symm)) (e11a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e4b)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e12a.symm)) (e4b)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e12b)) (b16)) (e4b)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e12a)) (b4)) (b16)) (e4b)) (e8a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x4) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b13) (e10a)) (e11a.symm)) (e7b))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11b)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11a)) (b7)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11b)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11a)) (b7)) (b19)) (e10a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e8a.symm)) (e4b.symm)) (e12b)) (e11a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e8a.symm)) (e4b.symm)) (e12a)) (b7)) (e11a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12b)) (e1b.symm)) (e0a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12a)) (b4)) (e1b.symm)) (e0a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e10a.symm)) (e11a))
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9a)) (e5a.symm)) (e0a)) (b3)) (e7a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (e5a.symm)) (e0a)) (b3)) (e7a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e4b)) (b18)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e12a.symm)) (e4b)) (b18)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e12b)) (b16)) (e4b)) (b18)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e12a)) (b4)) (b16)) (e4b)) (b18)) (e8a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x4) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b13) (e10a)) (e11a.symm)) (e7b))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11b)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11a)) (b7)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11b)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11a)) (b7)) (b19)) (e10a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e12b)) (e11a)) (e0a.symm)) (e3a))
                            · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e12a)) (b7)) (e11a)) (e0a.symm)) (e3a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12b)) (e1b.symm)) (e0a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12a)) (b4)) (e1b.symm)) (e0a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e10a.symm)) (e11a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e4b)) (b18)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e12a.symm)) (e4b)) (b18)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e12b)) (b16)) (e4b)) (b18)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e12a)) (b4)) (b16)) (e4b)) (b18)) (e8a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x4) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b13) (e10a)) (e11a.symm)) (e7b))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11b)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11a)) (b7)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11b)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11a)) (b7)) (b19)) (e10a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e12b)) (e11a)) (e0a.symm)) (e3a))
                            · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e12a)) (b7)) (e11a)) (e0a.symm)) (e3a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12b)) (e1b.symm)) (e0a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12a)) (b4)) (e1b.symm)) (e0a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e10a.symm)) (e11a))
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e8a)) (e3a.symm)) (e0a)) (b3)) (b15)) (e7a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (e3a.symm)) (e0a)) (b3)) (b15)) (e7a))
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9a)) (e5a.symm)) (e3a)) (b6)) (e8a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (e5a.symm)) (e3a)) (b6)) (e8a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e12a.symm)) (e1b.symm)) (e0a))
                            · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e8a.symm)) (e4b.symm)) (e12a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12b)) (b16)) (e4b)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12a)) (b4)) (b16)) (e4b)) (e8a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x22) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b19) (e10a)) (e7a.symm)) (e11b))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e7a)) (e10a.symm)) (e11b))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e10a.symm)) (e11a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e12a.symm)) (e1b.symm)) (e0a))
                            · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e8a.symm)) (e4b.symm)) (e12a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12b)) (b16)) (e4b)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12a)) (b4)) (b16)) (e4b)) (e8a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x22) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b19) (e10a)) (e7a.symm)) (e11b))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e7a)) (e10a.symm)) (e11b))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e10a.symm)) (e11a))
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9a)) (e5a.symm)) (e0a)) (b3)) (b15)) (e7a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (e5a.symm)) (e0a)) (b3)) (b15)) (e7a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e12a.symm)) (e1b.symm)) (e0a))
                            ·
                              rcases h21 with (⟨e13a, e13b⟩ | e13a) | (⟨e13a, e13b⟩ | e13a)
                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e13a.symm)) (e2b.symm)) (e0a))
                              · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e9a.symm)) (e6b.symm)) (e13a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e13b)) (b17)) (e6b)) (e9a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e13a)) (b5)) (b17)) (e6b)) (e9a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12b)) (b16)) (e4b)) (b18)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12a)) (b4)) (b16)) (e4b)) (b18)) (e8a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x22) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b19) (e10a)) (e7a.symm)) (e11b))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e7a)) (e10a.symm)) (e11b))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e10a.symm)) (e11a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e12a.symm)) (e1b.symm)) (e0a))
                            ·
                              rcases h21 with (⟨e13a, e13b⟩ | e13a) | (⟨e13a, e13b⟩ | e13a)
                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e13a.symm)) (e2b.symm)) (e0a))
                              ·
                                rcases h8 with (⟨e14a, e14b⟩ | e14a) | (⟨e14a, e14b⟩ | e14a)
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (e15b.symm)) (e4b)) (b18)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14a)) (e15a.symm)) (e4b)) (b18)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e15b)) (b16)) (e4b)) (b18)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e15a)) (b4)) (b16)) (e4b)) (b18)) (e8a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (e15b.symm)) (e4b)) (b18)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (e15a.symm)) (e4b)) (b18)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (b20)) (e15b)) (b16)) (e4b)) (b18)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (b20)) (e15a)) (b4)) (b16)) (e4b)) (b18)) (e8a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e14a.symm)) (e15b.symm)) (e12a))
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e16b)) (b21)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e16a)) (b9)) (b21)) (e9a))
                                    ·
                                      rcases h10 with (⟨e17a, e17b⟩ | e17a) | (⟨e17a, e17b⟩ | e17a)
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20b)) (e21a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20b)) (b22)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e22a.symm)) (e1b.symm)) (e0a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e23a.symm)) (e2b.symm)) (e0a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e24b)) (e21b.symm)) (e7a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e24a)) (b10)) (e21b.symm)) (e7a))
                                                    · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e11b.symm)) (e21b)) (e24a)) (e15a.symm)) (e12a))
                                                    · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e11b.symm)) (e21b)) (b22)) (e24a)) (e15a.symm)) (e12a))
                                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21b)) (b22)) (e23b)) (e2b.symm)) (e0a))
                                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21b)) (b22)) (e23a)) (b5)) (e2b.symm)) (e0a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21b)) (b22)) (e22b)) (e1b.symm)) (e0a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21b)) (b22)) (e22a)) (b4)) (e1b.symm)) (e0a))
                                              · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e11b.symm)) (e21a)) (e20a.symm)) (e17b)) (e11a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20a)) (b10)) (e21a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e20a)) (b10)) (b22)) (e21a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21b)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21a)) (b10)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17a)) (e21a.symm)) (e20a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (e4b.symm)) (e22b)) (e20a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (e4b.symm)) (e22a)) (b10)) (e20a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19b)) (e6b.symm)) (e23b)) (e20a))
                                                  · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19b)) (e6b.symm)) (e23a)) (b10)) (e20a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e24b)) (b22)) (e21a)) (b3)) (b15)) (e7a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e24a)) (b10)) (b22)) (e21a)) (b3)) (b15)) (e7a))
                                                    · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19b)) (e16a)) (e24a.symm)) (e20a))
                                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e12a.symm)) (e15a)) (e24a.symm)) (e21a))
                                                  · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e23a)) (e2a.symm)) (e1a)) (e22a.symm)) (e20a))
                                                · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e1b.symm)) (e0a)) (e21a.symm)) (e22a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21b)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e21a)) (b10)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (e21b.symm)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17a)) (e21a.symm)) (e20a))
                                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e19a)) (e5a.symm)) (e0a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17a)) (e0a.symm)) (e5a)) (b9)) (e19a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e7a)) (e9a.symm)) (e19a))
                                        · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17b.symm)) (e18a)) (e3a.symm)) (e0a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17a)) (e0a.symm)) (e3a)) (b6)) (e18a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17b)) (b15)) (e7a)) (e8a.symm)) (e18a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e12a.symm)) (e4b)) (e18b.symm)) (e17a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e13a.symm)) (e6b)) (e19b.symm)) (e17a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21b)) (e20b.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21a)) (b10)) (e20b.symm)) (e17a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e12a.symm)) (e22b)) (e21a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e12a.symm)) (e22a)) (b10)) (e21a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21b.symm)) (e22b)) (e1b.symm)) (e0a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21b.symm)) (e22a)) (b4)) (e1b.symm)) (e0a))
                                              · exact (lt_irrefl x31) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b22) (e21a)) (e17a.symm)) (e20b))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e21a)) (e20a.symm)) (e17a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b10) (e21a)) (e17a.symm)) (e20a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b10) (b22)) (e21a)) (e17a.symm)) (e20a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21b)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21a)) (b10)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (e21a.symm)) (e20a))
                                              · exact (lt_irrefl x7) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b14) (e17a)) (e21a.symm)) (e20b))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21b)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e21a)) (b10)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (e21b.symm)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (e21a.symm)) (e20a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (e0a.symm)) (e5a)) (b9)) (e19a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e7a)) (e9a.symm)) (e19a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (e0a.symm)) (e3a)) (b6)) (e18a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e17a)) (b3)) (b15)) (e7a)) (e8a.symm)) (e18a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e18a)) (e3a.symm)) (e0a)) (b3)) (e17a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18a)) (e3a.symm)) (e0a)) (b3)) (e17a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e19a)) (e5a.symm)) (e0a)) (b3)) (e17a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19a)) (e5a.symm)) (e0a)) (b3)) (e17a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20a)) (e21a.symm)) (e17a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (e22b.symm)) (e4b)) (e18a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20a)) (e22a.symm)) (e4b)) (e18a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e22b)) (b16)) (e4b)) (e18a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e22a)) (b4)) (b16)) (e4b)) (e18a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21b)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21a)) (b3)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x7) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b14) (e20a)) (e21a.symm)) (e17b))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21b)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21a)) (b3)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21b)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21a)) (b10)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21b)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21a)) (b3)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21b)) (b22)) (e20a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e21a)) (b10)) (b22)) (e20a))
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e12a.symm)) (e22b)) (e21a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e12a.symm)) (e22a)) (b10)) (e21a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21b.symm)) (e22b)) (e1b.symm)) (e0a))
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21b.symm)) (e22a)) (b4)) (e1b.symm)) (e0a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e17a)) (e20a.symm)) (e21a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e7a)) (e9a.symm)) (e19a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e17b.symm)) (e7a)) (e8a.symm)) (e18a))
                                      ·
                                        rcases h11 with (⟨e18a, e18b⟩ | e18a) | (⟨e18a, e18b⟩ | e18a)
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18b)) (b18)) (e8a)) (e7a.symm)) (e17a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e18a)) (b6)) (b18)) (e8a)) (e7a.symm)) (e17a))
                                        · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e18b.symm)) (e8a)) (e7a.symm)) (e17a))
                                        ·
                                          rcases h12 with (⟨e19a, e19b⟩ | e19a) | (⟨e19a, e19b⟩ | e19a)
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19b)) (b21)) (e9a)) (e7a.symm)) (e17a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e19a)) (b9)) (b21)) (e9a)) (e7a.symm)) (e17a))
                                          · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e19b.symm)) (e9a)) (e7a.symm)) (e17a))
                                          ·
                                            rcases h13 with (⟨e20a, e20b⟩ | e20a) | (⟨e20a, e20b⟩ | e20a)
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (e21b.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21b)) (b15)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20b)) (b22)) (e21a)) (b3)) (b15)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (e21b.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (e21a.symm)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21b)) (b15)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b2) (b14)) (e20a)) (b10)) (b22)) (e21a)) (b3)) (b15)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              ·
                                                rcases h20 with (⟨e22a, e22b⟩ | e22a) | (⟨e22a, e22b⟩ | e22a)
                                                · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e22a.symm)) (e1b.symm)) (e0a))
                                                ·
                                                  rcases h23 with (⟨e23a, e23b⟩ | e23a) | (⟨e23a, e23b⟩ | e23a)
                                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e21a)) (e23a.symm)) (e2b.symm)) (e0a))
                                                  ·
                                                    rcases h28 with (⟨e24a, e24b⟩ | e24a) | (⟨e24a, e24b⟩ | e24a)
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e24b)) (e21b.symm)) (e7a))
                                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e24a)) (b10)) (e21b.symm)) (e7a))
                                                    · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e24b)) (e16b.symm)) (e19a))
                                                    · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e24a)) (b8)) (e16b.symm)) (e19a))
                                                  · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e23b)) (b17)) (e6b)) (b21)) (e19a))
                                                  · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e23a)) (b5)) (b17)) (e6b)) (b21)) (e19a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e22b)) (b16)) (e4b)) (b18)) (e18a))
                                                · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e22a)) (b4)) (b16)) (e4b)) (b18)) (e18a))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b10) (e20a)) (e17a.symm)) (e21a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21b)) (b15)) (e17a))
                                              · exact (lt_irrefl x6) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b2) (e20b.symm)) (e21a)) (b3)) (b15)) (e17a))
                                            ·
                                              rcases h16 with (⟨e21a, e21b⟩ | e21a) | (⟨e21a, e21b⟩ | e21a)
                                              · exact (lt_irrefl x31) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b22) (e20a)) (e17a.symm)) (e21b))
                                              · exact (lt_irrefl x30) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b10) (b22)) (e20a)) (e17a.symm)) (e21a))
                                              · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e11b.symm)) (e17a)) (e20a.symm)) (e21b)) (e11a))
                                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e17a)) (e20a.symm)) (e21a))
                                    · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e9a.symm)) (e16a)) (e15a.symm)) (e12a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e15b)) (b16)) (e4b)) (b18)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e15a)) (b4)) (b16)) (e4b)) (b18)) (e8a))
                                ·
                                  rcases h27 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e14a.symm)) (e15b)) (e6b.symm)) (e13a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e14a.symm)) (e15a)) (e5a.symm)) (e0a))
                                  · exact (lt_irrefl x25) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b20) (e14a)) (e9a.symm)) (e15b))
                                  · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b8) (b20)) (e14a)) (e9a.symm)) (e15a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e13b)) (b17)) (e6b)) (b21)) (e9a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e13a)) (b5)) (b17)) (e6b)) (b21)) (e9a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12b)) (b16)) (e4b)) (b18)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12a)) (b4)) (b16)) (e4b)) (b18)) (e8a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x22) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b19) (e10a)) (e7a.symm)) (e11b))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e7a)) (e10a.symm)) (e11b))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e10a.symm)) (e11a))
                · exact (lt_irrefl x16) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b17) (e6a)) (e5a.symm)) (e2b))
                · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e1b.symm)) (e5a)) (b9)) (e6a)) (e2a.symm)) (e1a))
                · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e1b.symm)) (e5a)) (b9)) (b21)) (e6a)) (e2a.symm)) (e1a))
              · exact (lt_irrefl x27) (lt_trans (lt_of_lt_of_eq (b9) (e5a)) (b28))
              · exact (lt_irrefl x27) (lt_trans (lt_of_lt_of_eq (lt_trans (b9) (b21)) (e5a)) (b28))
            · exact (lt_irrefl x13) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b16) (e4a)) (e3a.symm)) (e1b))
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e1b.symm)) (e3a)) (b6)) (e4a))
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e1b.symm)) (e3a)) (b6)) (b18)) (e4a))
          · exact (lt_irrefl x18) (lt_trans (lt_of_lt_of_eq (b6) (e3a)) (b27))
          · exact (lt_irrefl x18) (lt_trans (lt_of_lt_of_eq (lt_trans (b6) (b18)) (e3a)) (b27))
        ·
          rcases h3 with (⟨e3a, e3b⟩ | e3a) | (⟨e3a, e3b⟩ | e3a)
          ·
            rcases h17 with (⟨e4a, e4b⟩ | e4a) | (⟨e4a, e4b⟩ | e4a)
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e4a)) (e3a.symm)) (e1a))
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e4a)) (e3a.symm)) (e1a))
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e1b.symm)) (e3b)) (e4a))
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e1b.symm)) (e3b)) (b18)) (e4a))
          ·
            rcases h17 with (⟨e4a, e4b⟩ | e4a) | (⟨e4a, e4b⟩ | e4a)
            ·
              rcases h4 with (⟨e5a, e5b⟩ | e5a) | (⟨e5a, e5b⟩ | e5a)
              ·
                rcases h22 with (⟨e6a, e6b⟩ | e6a) | (⟨e6a, e6b⟩ | e6a)
                · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e1b.symm)) (e2a)) (b5)) (e6a)) (e5a.symm)) (e1a))
                · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e1b.symm)) (e2a)) (b5)) (b17)) (e6a)) (e5a.symm)) (e1a))
                ·
                  rcases h5 with (⟨e7a, e7b⟩ | e7a) | (⟨e7a, e7b⟩ | e7a)
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e9b)) (e5b.symm)) (e0a))
                      · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e9a)) (b9)) (e5b.symm)) (e0a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e0a.symm)) (e5b)) (e9a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e0a.symm)) (e5b)) (b21)) (e9a))
                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e8a)) (e3a.symm)) (e0a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e0a.symm)) (e3a)) (b6)) (e8a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e0a.symm)) (e3a)) (b6)) (b18)) (e8a))
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e8b.symm)) (e7a)) (e0a.symm)) (e3a))
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11b)) (e10b.symm)) (e7a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11a)) (b7)) (e10b.symm)) (e7a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e12a)) (e10a.symm)) (e9a)) (e5a.symm)) (e1a))
                            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e12a)) (e10a.symm)) (e9a)) (e5a.symm)) (e1a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12b)) (e1b.symm)) (e0a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12a)) (b4)) (e1b.symm)) (e0a))
                          · exact (lt_irrefl x22) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b19) (e11a)) (e7a.symm)) (e10b))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e10a.symm)) (e7a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11a)) (e10a.symm)) (e7a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e11a)) (e7a.symm)) (e10a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e11a)) (e7a.symm)) (e10a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (b15)) (e11b)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (b15)) (e11a)) (b7)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e11a.symm)) (e10a))
                          · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e1b.symm)) (e0a)) (e11a.symm)) (e10b)) (e9a)) (e5a.symm)) (e1a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (b15)) (e11b)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (b15)) (e11a)) (b7)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (e11b.symm)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e11a.symm)) (e10a))
                      · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e4a)) (e8a.symm)) (e9a)) (e5a.symm)) (e1a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e0a.symm)) (e5b)) (e9a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e0a.symm)) (e5b)) (b21)) (e9a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e0a.symm)) (e3a)) (b6)) (e8a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e0a.symm)) (e3a)) (b6)) (b18)) (e8a))
                  ·
                    rcases h9 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e5b.symm)) (e0a)) (b3)) (e7a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b9)) (e5b.symm)) (e0a)) (b3)) (e7a))
                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e8a.symm)) (e5b.symm)) (e0a))
                    ·
                      rcases h6 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9a)) (e3a.symm)) (e0a)) (b3)) (e7a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (e3a.symm)) (e0a)) (b3)) (e7a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e4b)) (e9a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e12a.symm)) (e4b)) (e9a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e12b)) (b16)) (e4b)) (e9a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e12a)) (b4)) (b16)) (e4b)) (e9a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x4) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b13) (e10a)) (e11a.symm)) (e7b))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11b)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11a)) (b7)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11b)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11a)) (b7)) (b19)) (e10a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e9a.symm)) (e4b.symm)) (e12b)) (e11a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e9a.symm)) (e4b.symm)) (e12a)) (b7)) (e11a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12b)) (e1b.symm)) (e0a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12a)) (b4)) (e1b.symm)) (e0a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e10a.symm)) (e11a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e12b.symm)) (e4b)) (b18)) (e9a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e12a.symm)) (e4b)) (b18)) (e9a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e12b)) (b16)) (e4b)) (b18)) (e9a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e12a)) (b4)) (b16)) (e4b)) (b18)) (e9a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x4) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b13) (e10a)) (e11a.symm)) (e7b))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11b)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11a)) (b7)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11b)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11a)) (b7)) (b19)) (e10a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e12b)) (e11a)) (e0a.symm)) (e3a))
                            · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4b.symm)) (e12a)) (b7)) (e11a)) (e0a.symm)) (e3a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12b)) (e1b.symm)) (e0a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12a)) (b4)) (e1b.symm)) (e0a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e10a.symm)) (e11a))
                  ·
                    rcases h9 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e5b.symm)) (e0a)) (b3)) (b15)) (e7a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b9)) (e5b.symm)) (e0a)) (b3)) (b15)) (e7a))
                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e8a.symm)) (e5b.symm)) (e0a))
                    ·
                      rcases h6 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9a)) (e3a.symm)) (e5b)) (b21)) (e8a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (e3a.symm)) (e5b)) (b21)) (e8a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e12a.symm)) (e1b.symm)) (e0a))
                            · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e9a.symm)) (e4b.symm)) (e12a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12b)) (b16)) (e4b)) (e9a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12a)) (b4)) (b16)) (e4b)) (e9a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x22) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b19) (e10a)) (e7a.symm)) (e11b))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e7a)) (e10a.symm)) (e11b))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e10a.symm)) (e11a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e12a.symm)) (e1b.symm)) (e0a))
                            ·
                              rcases h21 with (⟨e13a, e13b⟩ | e13a) | (⟨e13a, e13b⟩ | e13a)
                              · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e8a.symm)) (e6b)) (e13a))
                              · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e8a.symm)) (e6b)) (b17)) (e13a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e13b)) (e6b.symm)) (e8a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e13a)) (b5)) (e6b.symm)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12b)) (b16)) (e4b)) (b18)) (e9a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12a)) (b4)) (b16)) (e4b)) (b18)) (e9a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x22) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b19) (e10a)) (e7a.symm)) (e11b))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e7a)) (e10a.symm)) (e11b))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e10a.symm)) (e11a))
                · exact (lt_irrefl x28) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b21) (e6a)) (e2a.symm)) (e5b))
              ·
                rcases h22 with (⟨e6a, e6b⟩ | e6a) | (⟨e6a, e6b⟩ | e6a)
                · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b5) (e6a)) (e5a.symm)) (e2a))
                · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b5) (b17)) (e6a)) (e5a.symm)) (e2a))
                · exact (lt_irrefl x27) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b9) (e6a)) (e2a.symm)) (e5a))
                · exact (lt_irrefl x27) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b9) (b21)) (e6a)) (e2a.symm)) (e5a))
              · exact (lt_irrefl x27) (lt_trans (lt_of_lt_of_eq (b9) (e5a)) (b28))
              · exact (lt_irrefl x27) (lt_trans (lt_of_lt_of_eq (lt_trans (b9) (b21)) (e5a)) (b28))
            · exact (lt_irrefl x13) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b16) (e4a)) (e3a.symm)) (e1b))
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e1b.symm)) (e3a)) (b6)) (e4a))
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e1b.symm)) (e3a)) (b6)) (b18)) (e4a))
          · exact (lt_irrefl x18) (lt_trans (lt_of_lt_of_eq (b6) (e3a)) (b27))
          · exact (lt_irrefl x18) (lt_trans (lt_of_lt_of_eq (lt_trans (b6) (b18)) (e3a)) (b27))
        · exact (lt_irrefl x15) (lt_trans (lt_of_lt_of_eq (b5) (e2a)) (b26))
        · exact (lt_irrefl x15) (lt_trans (lt_of_lt_of_eq (lt_trans (b5) (b17)) (e2a)) (b26))
      ·
        rcases h2 with (⟨e2a, e2b⟩ | e2a) | (⟨e2a, e2b⟩ | e2a)
        ·
          rcases h3 with (⟨e3a, e3b⟩ | e3a) | (⟨e3a, e3b⟩ | e3a)
          ·
            rcases h17 with (⟨e4a, e4b⟩ | e4a) | (⟨e4a, e4b⟩ | e4a)
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e4b)) (e3b.symm)) (e1a))
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e4a)) (b6)) (e3b.symm)) (e1a))
            ·
              rcases h4 with (⟨e5a, e5b⟩ | e5a) | (⟨e5a, e5b⟩ | e5a)
              ·
                rcases h22 with (⟨e6a, e6b⟩ | e6a) | (⟨e6a, e6b⟩ | e6a)
                · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b5) (e6a)) (e5a.symm)) (e2a))
                · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b5) (b17)) (e6a)) (e5a.symm)) (e2a))
                · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b5) (e2b.symm)) (e5b)) (e6a))
                · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b5) (e2b.symm)) (e5b)) (b21)) (e6a))
              ·
                rcases h22 with (⟨e6a, e6b⟩ | e6a) | (⟨e6a, e6b⟩ | e6a)
                ·
                  rcases h5 with (⟨e7a, e7b⟩ | e7a) | (⟨e7a, e7b⟩ | e7a)
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e8b)) (e3b.symm)) (e0a))
                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e8a)) (b6)) (e3b.symm)) (e0a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e0a.symm)) (e3b)) (e8a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e0a.symm)) (e3b)) (b18)) (e8a))
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b5) (e6a)) (e9a.symm)) (e8a)) (e3a.symm)) (e2a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11b)) (e10b.symm)) (e7a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11a)) (b7)) (e10b.symm)) (e7a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e12b)) (e10b.symm)) (e8b)) (e4a))
                            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e12a)) (b7)) (e10b.symm)) (e8b)) (e4a))
                            ·
                              rcases h21 with (⟨e13a, e13b⟩ | e13a) | (⟨e13a, e13b⟩ | e13a)
                              · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b5) (e13a)) (e10a.symm)) (e8a)) (e3a.symm)) (e2a))
                              · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b5) (b17)) (e13a)) (e10a.symm)) (e8a)) (e3a.symm)) (e2a))
                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e13b)) (e2b.symm)) (e0a))
                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e13a)) (b5)) (e2b.symm)) (e0a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12a)) (e1a.symm)) (e0a))
                          · exact (lt_irrefl x22) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b19) (e11a)) (e7a.symm)) (e10b))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e10a.symm)) (e7a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11a)) (e10a.symm)) (e7a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e11a)) (e7a.symm)) (e10a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e11a)) (e7a.symm)) (e10a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (b15)) (e11b)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (b15)) (e11a)) (b7)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e11a.symm)) (e10a))
                          · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b5) (e2b.symm)) (e0a)) (e11a.symm)) (e10b)) (e8a)) (e3a.symm)) (e2a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (b15)) (e11b)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (b15)) (e11a)) (b7)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (e11b.symm)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e11a.symm)) (e10a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e0a.symm)) (e5a)) (b9)) (e9a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e0a.symm)) (e5a)) (b9)) (b21)) (e9a))
                    · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b5) (e2b.symm)) (e0a)) (e7a.symm)) (e8a)) (e3a.symm)) (e2a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e0a.symm)) (e3b)) (e8a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e0a.symm)) (e3b)) (b18)) (e8a))
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e3b.symm)) (e0a)) (b3)) (e7a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (e3b.symm)) (e0a)) (b3)) (e7a))
                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e8a.symm)) (e3b.symm)) (e0a))
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9a)) (e5a.symm)) (e0a)) (b3)) (e7a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (e5a.symm)) (e0a)) (b3)) (e7a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e12a.symm)) (e4b.symm)) (e8a))
                            ·
                              rcases h21 with (⟨e13a, e13b⟩ | e13a) | (⟨e13a, e13b⟩ | e13a)
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e13b.symm)) (e6b)) (e9a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e13a.symm)) (e6b)) (e9a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e13b)) (b17)) (e6b)) (e9a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e13a)) (b5)) (b17)) (e6b)) (e9a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e12b)) (e4b.symm)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e12a)) (b4)) (e4b.symm)) (e8a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x4) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b13) (e10a)) (e11a.symm)) (e7b))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11b)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11a)) (b7)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11b)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11a)) (b7)) (b19)) (e10a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e8a.symm)) (e4b)) (b16)) (e12b)) (e11a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e8a.symm)) (e4b)) (b16)) (e12a)) (b7)) (e11a))
                            ·
                              rcases h21 with (⟨e13a, e13b⟩ | e13a) | (⟨e13a, e13b⟩ | e13a)
                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e9a.symm)) (e6b.symm)) (e13b)) (e11a))
                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e9a.symm)) (e6b.symm)) (e13a)) (b7)) (e11a))
                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e13b)) (e2b.symm)) (e0a))
                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e13a)) (b5)) (e2b.symm)) (e0a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12a)) (e1a.symm)) (e0a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e10a.symm)) (e11a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e12a.symm)) (e4b.symm)) (e8a))
                            ·
                              rcases h21 with (⟨e13a, e13b⟩ | e13a) | (⟨e13a, e13b⟩ | e13a)
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e13b.symm)) (e6b)) (b21)) (e9a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e13a.symm)) (e6b)) (b21)) (e9a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e13b)) (b17)) (e6b)) (b21)) (e9a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e13a)) (b5)) (b17)) (e6b)) (b21)) (e9a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e12b)) (e4b.symm)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e12a)) (b4)) (e4b.symm)) (e8a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x4) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b13) (e10a)) (e11a.symm)) (e7b))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11b)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11a)) (b7)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11b)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11a)) (b7)) (b19)) (e10a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e8a.symm)) (e4b)) (b16)) (e12b)) (e11a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e8a.symm)) (e4b)) (b16)) (e12a)) (b7)) (e11a))
                            ·
                              rcases h21 with (⟨e13a, e13b⟩ | e13a) | (⟨e13a, e13b⟩ | e13a)
                              · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e11a)) (e0a.symm)) (e2b)) (e13a))
                              · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e11a)) (e0a.symm)) (e2b)) (b17)) (e13a))
                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e13b)) (e2b.symm)) (e0a))
                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e13a)) (b5)) (e2b.symm)) (e0a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12a)) (e1a.symm)) (e0a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e10a.symm)) (e11a))
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e3b.symm)) (e0a)) (b3)) (b15)) (e7a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (e3b.symm)) (e0a)) (b3)) (b15)) (e7a))
                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e8a.symm)) (e3b.symm)) (e0a))
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e9a)) (e5a.symm)) (e3b)) (b18)) (e8a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (e5a.symm)) (e3b)) (b18)) (e8a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e8a.symm)) (e4b)) (e12a))
                            · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e8a.symm)) (e4b)) (b16)) (e12a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12b)) (e4b.symm)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12a)) (b4)) (e4b.symm)) (e8a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x22) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b19) (e10a)) (e7a.symm)) (e11b))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e7a)) (e10a.symm)) (e11b))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e10a.symm)) (e11a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e8a.symm)) (e4b)) (e12a))
                            · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e8a.symm)) (e4b)) (b16)) (e12a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12b)) (e4b.symm)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12a)) (b4)) (e4b.symm)) (e8a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x22) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b19) (e10a)) (e7a.symm)) (e11b))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e7a)) (e10a.symm)) (e11b))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e10a.symm)) (e11a))
                · exact (lt_irrefl x16) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b17) (e6a)) (e5a.symm)) (e2b))
                · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b5) (e2b.symm)) (e5a)) (b9)) (e6a))
                · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b5) (e2b.symm)) (e5a)) (b9)) (b21)) (e6a))
              · exact (lt_irrefl x27) (lt_trans (lt_of_lt_of_eq (b9) (e5a)) (b28))
              · exact (lt_irrefl x27) (lt_trans (lt_of_lt_of_eq (lt_trans (b9) (b21)) (e5a)) (b28))
            · exact (lt_irrefl x19) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b18) (e4a)) (e1a.symm)) (e3b))
          ·
            rcases h17 with (⟨e4a, e4b⟩ | e4a) | (⟨e4a, e4b⟩ | e4a)
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e4a)) (e3a.symm)) (e1a))
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e4a)) (e3a.symm)) (e1a))
            · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4a)) (e1a.symm)) (e3a))
            · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b6) (b18)) (e4a)) (e1a.symm)) (e3a))
          · exact (lt_irrefl x18) (lt_trans (lt_of_lt_of_eq (b6) (e3a)) (b27))
          · exact (lt_irrefl x18) (lt_trans (lt_of_lt_of_eq (lt_trans (b6) (b18)) (e3a)) (b27))
        ·
          rcases h3 with (⟨e3a, e3b⟩ | e3a) | (⟨e3a, e3b⟩ | e3a)
          ·
            rcases h17 with (⟨e4a, e4b⟩ | e4a) | (⟨e4a, e4b⟩ | e4a)
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e4b)) (e3b.symm)) (e1a))
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e4a)) (b6)) (e3b.symm)) (e1a))
            ·
              rcases h4 with (⟨e5a, e5b⟩ | e5a) | (⟨e5a, e5b⟩ | e5a)
              ·
                rcases h22 with (⟨e6a, e6b⟩ | e6a) | (⟨e6a, e6b⟩ | e6a)
                · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b5) (b17)) (e6b)) (e5b.symm)) (e2a))
                · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b5) (b17)) (e6a)) (b9)) (e5b.symm)) (e2a))
                ·
                  rcases h5 with (⟨e7a, e7b⟩ | e7a) | (⟨e7a, e7b⟩ | e7a)
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e8b)) (e3b.symm)) (e0a))
                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7b.symm)) (e8a)) (b6)) (e3b.symm)) (e0a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e0a.symm)) (e3b)) (e8a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7a)) (e0a.symm)) (e3b)) (b18)) (e8a))
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11b)) (e10b.symm)) (e7a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11a)) (b7)) (e10b.symm)) (e7a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e12b)) (e10b.symm)) (e8b)) (e4a))
                            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e12a)) (b7)) (e10b.symm)) (e8b)) (e4a))
                            ·
                              rcases h21 with (⟨e13a, e13b⟩ | e13a) | (⟨e13a, e13b⟩ | e13a)
                              · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b5) (b17)) (e13b)) (e10b.symm)) (e9b)) (e6a))
                              · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b5) (b17)) (e13a)) (b7)) (e10b.symm)) (e9b)) (e6a))
                              ·
                                rcases h8 with (⟨e14a, e14b⟩ | e14a) | (⟨e14a, e14b⟩ | e14a)
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12b)) (b16)) (e15b)) (e14b.symm)) (e7a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12b)) (b16)) (e15a)) (b8)) (e14b.symm)) (e7a))
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12b)) (e15b.symm)) (e16b)) (e5b.symm)) (e0a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12b)) (e15b.symm)) (e16a)) (b9)) (e5b.symm)) (e0a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e13b)) (e6b.symm)) (e16b)) (e14b.symm)) (e7a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e13b)) (e6b.symm)) (e16a)) (b8)) (e14b.symm)) (e7a))
                                  · exact (lt_irrefl x25) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b20) (e15a)) (e4a.symm)) (e8b.symm)) (e14b))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12b)) (e15a)) (e14a.symm)) (e7a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12b)) (b16)) (e15a)) (e14a.symm)) (e7a))
                                  · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b8) (e15a)) (e4a.symm)) (e8b.symm)) (e14a))
                                  · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b8) (b20)) (e15a)) (e4a.symm)) (e8b.symm)) (e14a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (b18)) (e4b)) (b16)) (e15b)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (b18)) (e4b)) (b16)) (e15a)) (b8)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e4a)) (e15a.symm)) (e14a))
                                  · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4a)) (e15a.symm)) (e14b)) (e8a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (b18)) (e4b)) (b16)) (e15b)) (b20)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (b18)) (e4b)) (b16)) (e15a)) (b8)) (b20)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (b18)) (e4b)) (e15b.symm)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e4a)) (e15a.symm)) (e14a))
                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e13a)) (e2a.symm)) (e0a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12a)) (e1a.symm)) (e0a))
                          · exact (lt_irrefl x22) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b19) (e11a)) (e7a.symm)) (e10b))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11a)) (e10a.symm)) (e7a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e11a)) (e10a.symm)) (e7a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e11a)) (e7a.symm)) (e10a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e11a)) (e7a.symm)) (e10a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (b15)) (e11b)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (b15)) (e11a)) (b7)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e11a.symm)) (e10a))
                          · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e3b.symm)) (e0a)) (e11a.symm)) (e10b)) (e8a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (b15)) (e11b)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (b15)) (e11a)) (b7)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (b3)) (e11b.symm)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e11a.symm)) (e10a))
                      · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e8b.symm)) (e9a)) (e5a.symm)) (e3a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e0a.symm)) (e5b)) (e9a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e0a.symm)) (e5b)) (b21)) (e9a))
                    · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e3b.symm)) (e0a)) (e7a.symm)) (e8a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e0a.symm)) (e3b)) (e8a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e7a)) (e0a.symm)) (e3b)) (b18)) (e8a))
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e3b.symm)) (e0a)) (b3)) (e7a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (e3b.symm)) (e0a)) (b3)) (e7a))
                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e8a.symm)) (e3b.symm)) (e0a))
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (e5b.symm)) (e0a)) (b3)) (e7a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (b9)) (e5b.symm)) (e0a)) (b3)) (e7a))
                      · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e9a.symm)) (e5b.symm)) (e0a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e12a.symm)) (e4b.symm)) (e8a))
                            ·
                              rcases h21 with (⟨e13a, e13b⟩ | e13a) | (⟨e13a, e13b⟩ | e13a)
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e13a.symm)) (e6b.symm)) (e9a))
                              ·
                                rcases h8 with (⟨e14a, e14b⟩ | e14a) | (⟨e14a, e14b⟩ | e14a)
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14a)) (e15a.symm)) (e4b.symm)) (e8a))
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e16b)) (b21)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e16a)) (b9)) (b21)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (e16b.symm)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14a)) (e16a.symm)) (e9a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e15b)) (e4b.symm)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e15a)) (b4)) (e4b.symm)) (e8a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (e15a.symm)) (e4b.symm)) (e8a))
                                  · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10b.symm)) (e14a)) (e15a.symm)) (e12a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (b20)) (e15b)) (e4b.symm)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (b20)) (e15a)) (b4)) (e4b.symm)) (e8a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e12a.symm)) (e15b)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e12a.symm)) (e15a)) (b8)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e15b)) (e4b.symm)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e15a)) (b4)) (e4b.symm)) (e8a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e12a.symm)) (e15b)) (b20)) (e14a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e12a.symm)) (e15a)) (b8)) (b20)) (e14a))
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e14a.symm)) (e16b)) (e5b.symm)) (e0a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e14a.symm)) (e16a)) (b9)) (e5b.symm)) (e0a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e9a.symm)) (e16b)) (e15a)) (e1a.symm)) (e0a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e9a.symm)) (e16a)) (b8)) (e15a)) (e1a.symm)) (e0a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e14a.symm)) (e15a)) (e1a.symm)) (e0a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e13b)) (e6b.symm)) (e9a))
                              · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e13a)) (b5)) (e6b.symm)) (e9a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e12b)) (e4b.symm)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e12a)) (b4)) (e4b.symm)) (e8a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x4) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b13) (e10a)) (e11a.symm)) (e7b))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11b)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11a)) (b7)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11b)) (b19)) (e10a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e7b.symm)) (e11a)) (b7)) (b19)) (e10a))
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e8a.symm)) (e4b)) (b16)) (e12b)) (e11a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e8a.symm)) (e4b)) (b16)) (e12a)) (b7)) (e11a))
                            ·
                              rcases h21 with (⟨e13a, e13b⟩ | e13a) | (⟨e13a, e13b⟩ | e13a)
                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e9a.symm)) (e6b)) (b17)) (e13b)) (e11a))
                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e9a.symm)) (e6b)) (b17)) (e13a)) (b7)) (e11a))
                              ·
                                rcases h8 with (⟨e14a, e14b⟩ | e14a) | (⟨e14a, e14b⟩ | e14a)
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14a)) (e15a.symm)) (e4b.symm)) (e8a))
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e16b)) (b21)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e16a)) (b9)) (b21)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (e16b.symm)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14a)) (e16a.symm)) (e9a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e15b)) (e4b.symm)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14b)) (b20)) (e15a)) (b4)) (e4b.symm)) (e8a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (e15a.symm)) (e4b.symm)) (e8a))
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (b20)) (e16b)) (b21)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (b20)) (e16a)) (b9)) (b21)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (e16b.symm)) (e9a))
                                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (e16a.symm)) (e9a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (b20)) (e15b)) (e4b.symm)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e14a)) (b8)) (b20)) (e15a)) (b4)) (e4b.symm)) (e8a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b8) (e14a)) (e8a.symm)) (e4b)) (e15a))
                                  · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b8) (e14a)) (e8a.symm)) (e4b)) (b16)) (e15a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e15b)) (e4b.symm)) (e8a))
                                  · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e14b.symm)) (e15a)) (b4)) (e4b.symm)) (e8a))
                                ·
                                  rcases h19 with (⟨e15a, e15b⟩ | e15a) | (⟨e15a, e15b⟩ | e15a)
                                  · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b8) (b20)) (e14a)) (e8a.symm)) (e4b)) (e15a))
                                  · exact (lt_irrefl x24) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b8) (b20)) (e14a)) (e8a.symm)) (e4b)) (b16)) (e15a))
                                  ·
                                    rcases h27 with (⟨e16a, e16b⟩ | e16a) | (⟨e16a, e16b⟩ | e16a)
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e14a.symm)) (e16b)) (e5b.symm)) (e0a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e14a.symm)) (e16a)) (b9)) (e5b.symm)) (e0a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e9a.symm)) (e16b)) (e15a)) (e1a.symm)) (e0a))
                                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e9a.symm)) (e16a)) (b8)) (e15a)) (e1a.symm)) (e0a))
                                  · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e14a.symm)) (e15a)) (e1a.symm)) (e0a))
                              · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e13a)) (e2a.symm)) (e0a))
                            · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e11b.symm)) (e12a)) (e1a.symm)) (e0a))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b3) (e7a)) (e10a.symm)) (e11a))
                  ·
                    rcases h6 with (⟨e8a, e8b⟩ | e8a) | (⟨e8a, e8b⟩ | e8a)
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8b)) (e3b.symm)) (e0a)) (b3)) (b15)) (e7a))
                    · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e8a)) (b6)) (e3b.symm)) (e0a)) (b3)) (b15)) (e7a))
                    · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e8a.symm)) (e3b.symm)) (e0a))
                    ·
                      rcases h9 with (⟨e9a, e9b⟩ | e9a) | (⟨e9a, e9b⟩ | e9a)
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9b)) (e5b.symm)) (e3b)) (b18)) (e8a))
                      · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e9a)) (b9)) (e5b.symm)) (e3b)) (b18)) (e8a))
                      · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e9a.symm)) (e5b.symm)) (e0a))
                      ·
                        rcases h7 with (⟨e10a, e10b⟩ | e10a) | (⟨e10a, e10b⟩ | e10a)
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10b)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (e11b.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (e11a.symm)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_trans (b1) (b13)) (e10a)) (b7)) (b19)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          ·
                            rcases h18 with (⟨e12a, e12b⟩ | e12a) | (⟨e12a, e12b⟩ | e12a)
                            · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e8a.symm)) (e4b)) (e12a))
                            · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e8a.symm)) (e4b)) (b16)) (e12a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12b)) (e4b.symm)) (e8a))
                            · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e12a)) (b4)) (e4b.symm)) (e8a))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b7) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11b)) (b15)) (e7a))
                          · exact (lt_irrefl x3) (lt_of_lt_of_eq (lt_trans (lt_trans (lt_of_lt_of_eq (lt_of_lt_of_eq (b1) (e10b.symm)) (e11a)) (b3)) (b15)) (e7a))
                        ·
                          rcases h15 with (⟨e11a, e11b⟩ | e11a) | (⟨e11a, e11b⟩ | e11a)
                          · exact (lt_irrefl x22) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b19) (e10a)) (e7a.symm)) (e11b))
                          · exact (lt_irrefl x21) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b7) (b19)) (e10a)) (e7a.symm)) (e11a))
                          · exact (lt_irrefl x10) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b15) (e7a)) (e10a.symm)) (e11b))
                          · exact (lt_irrefl x9) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e7a)) (e10a.symm)) (e11a))
                · exact (lt_irrefl x28) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b21) (e6a)) (e2a.symm)) (e5b))
              ·
                rcases h22 with (⟨e6a, e6b⟩ | e6a) | (⟨e6a, e6b⟩ | e6a)
                · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b5) (e6a)) (e5a.symm)) (e2a))
                · exact (lt_irrefl x15) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b5) (b17)) (e6a)) (e5a.symm)) (e2a))
                · exact (lt_irrefl x27) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b9) (e6a)) (e2a.symm)) (e5a))
                · exact (lt_irrefl x27) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b9) (b21)) (e6a)) (e2a.symm)) (e5a))
              · exact (lt_irrefl x27) (lt_trans (lt_of_lt_of_eq (b9) (e5a)) (b28))
              · exact (lt_irrefl x27) (lt_trans (lt_of_lt_of_eq (lt_trans (b9) (b21)) (e5a)) (b28))
            · exact (lt_irrefl x19) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b18) (e4a)) (e1a.symm)) (e3b))
          ·
            rcases h17 with (⟨e4a, e4b⟩ | e4a) | (⟨e4a, e4b⟩ | e4a)
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b4) (e4a)) (e3a.symm)) (e1a))
            · exact (lt_irrefl x12) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e4a)) (e3a.symm)) (e1a))
            · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (b6) (e4a)) (e1a.symm)) (e3a))
            · exact (lt_irrefl x18) (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_of_lt_of_eq (lt_trans (b6) (b18)) (e4a)) (e1a.symm)) (e3a))
          · exact (lt_irrefl x18) (lt_trans (lt_of_lt_of_eq (b6) (e3a)) (b27))
          · exact (lt_irrefl x18) (lt_trans (lt_of_lt_of_eq (lt_trans (b6) (b18)) (e3a)) (b27))
        · exact (lt_irrefl x15) (lt_trans (lt_of_lt_of_eq (b5) (e2a)) (b26))
        · exact (lt_irrefl x15) (lt_trans (lt_of_lt_of_eq (lt_trans (b5) (b17)) (e2a)) (b26))
      · exact (lt_irrefl x12) (lt_trans (lt_of_lt_of_eq (b4) (e1a)) (b25))
      · exact (lt_irrefl x12) (lt_trans (lt_of_lt_of_eq (lt_trans (b4) (b16)) (e1a)) (b25))
    · exact (lt_irrefl x9) (lt_trans (lt_of_lt_of_eq (b3) (e0a)) (b24))
    · exact (lt_irrefl x9) (lt_trans (lt_of_lt_of_eq (lt_trans (b3) (b15)) (e0a)) (b24))
    : False)

#print axioms symbolic_certificate

private theorem no_arc_four_min (A : Type*) [LinearOrder A]
    (f : arcGraph (⊤ : SimpleGraph (Fin 4)) →g graph A)
    (hmin : ∀ p, (f ⟨(0,1), by decide⟩).a ≤ (f p).a) : False := by
  exact (by
    let x0 := (f ⟨(0, 1), by decide⟩).a
    let x1 := (f ⟨(0, 1), by decide⟩).b
    let x2 := (f ⟨(0, 1), by decide⟩).c
    let x3 := (f ⟨(0, 2), by decide⟩).a
    let x4 := (f ⟨(0, 2), by decide⟩).b
    let x5 := (f ⟨(0, 2), by decide⟩).c
    let x6 := (f ⟨(0, 3), by decide⟩).a
    let x7 := (f ⟨(0, 3), by decide⟩).b
    let x8 := (f ⟨(0, 3), by decide⟩).c
    let x9 := (f ⟨(1, 0), by decide⟩).a
    let x10 := (f ⟨(1, 0), by decide⟩).b
    let x11 := (f ⟨(1, 0), by decide⟩).c
    let x12 := (f ⟨(1, 2), by decide⟩).a
    let x13 := (f ⟨(1, 2), by decide⟩).b
    let x14 := (f ⟨(1, 2), by decide⟩).c
    let x15 := (f ⟨(1, 3), by decide⟩).a
    let x16 := (f ⟨(1, 3), by decide⟩).b
    let x17 := (f ⟨(1, 3), by decide⟩).c
    let x18 := (f ⟨(2, 0), by decide⟩).a
    let x19 := (f ⟨(2, 0), by decide⟩).b
    let x20 := (f ⟨(2, 0), by decide⟩).c
    let x21 := (f ⟨(2, 1), by decide⟩).a
    let x22 := (f ⟨(2, 1), by decide⟩).b
    let x23 := (f ⟨(2, 1), by decide⟩).c
    let x24 := (f ⟨(2, 3), by decide⟩).a
    let x25 := (f ⟨(2, 3), by decide⟩).b
    let x26 := (f ⟨(2, 3), by decide⟩).c
    let x27 := (f ⟨(3, 0), by decide⟩).a
    let x28 := (f ⟨(3, 0), by decide⟩).b
    let x29 := (f ⟨(3, 0), by decide⟩).c
    let x30 := (f ⟨(3, 1), by decide⟩).a
    let x31 := (f ⟨(3, 1), by decide⟩).b
    let x32 := (f ⟨(3, 1), by decide⟩).c
    let x33 := (f ⟨(3, 2), by decide⟩).a
    let x34 := (f ⟨(3, 2), by decide⟩).b
    let x35 := (f ⟨(3, 2), by decide⟩).c
    have b0 : x0 < x1 := (f ⟨(0, 1), by decide⟩).ab
    have b1 : x3 < x4 := (f ⟨(0, 2), by decide⟩).ab
    have b2 : x6 < x7 := (f ⟨(0, 3), by decide⟩).ab
    have b3 : x9 < x10 := (f ⟨(1, 0), by decide⟩).ab
    have b4 : x12 < x13 := (f ⟨(1, 2), by decide⟩).ab
    have b5 : x15 < x16 := (f ⟨(1, 3), by decide⟩).ab
    have b6 : x18 < x19 := (f ⟨(2, 0), by decide⟩).ab
    have b7 : x21 < x22 := (f ⟨(2, 1), by decide⟩).ab
    have b8 : x24 < x25 := (f ⟨(2, 3), by decide⟩).ab
    have b9 : x27 < x28 := (f ⟨(3, 0), by decide⟩).ab
    have b10 : x30 < x31 := (f ⟨(3, 1), by decide⟩).ab
    have b11 : x33 < x34 := (f ⟨(3, 2), by decide⟩).ab
    have b12 : x1 < x2 := (f ⟨(0, 1), by decide⟩).bc
    have b13 : x4 < x5 := (f ⟨(0, 2), by decide⟩).bc
    have b14 : x7 < x8 := (f ⟨(0, 3), by decide⟩).bc
    have b15 : x10 < x11 := (f ⟨(1, 0), by decide⟩).bc
    have b16 : x13 < x14 := (f ⟨(1, 2), by decide⟩).bc
    have b17 : x16 < x17 := (f ⟨(1, 3), by decide⟩).bc
    have b18 : x19 < x20 := (f ⟨(2, 0), by decide⟩).bc
    have b19 : x22 < x23 := (f ⟨(2, 1), by decide⟩).bc
    have b20 : x25 < x26 := (f ⟨(2, 3), by decide⟩).bc
    have b21 : x28 < x29 := (f ⟨(3, 0), by decide⟩).bc
    have b22 : x31 < x32 := (f ⟨(3, 1), by decide⟩).bc
    have b23 : x34 < x35 := (f ⟨(3, 2), by decide⟩).bc
    have b24 : x0 < x9 := lt_of_le_of_ne (hmin ⟨(1, 0), by decide⟩)
      (first_ne (f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(0, 1), by decide⟩ ⟨(1, 0), by decide⟩ from by simp [arcGraph])))
    have b25 : x0 < x12 := lt_of_le_of_ne (hmin ⟨(1, 2), by decide⟩)
      (first_ne (f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(0, 1), by decide⟩ ⟨(1, 2), by decide⟩ from by simp [arcGraph])))
    have b26 : x0 < x15 := lt_of_le_of_ne (hmin ⟨(1, 3), by decide⟩)
      (first_ne (f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(0, 1), by decide⟩ ⟨(1, 3), by decide⟩ from by simp [arcGraph])))
    have b27 : x0 < x18 := lt_of_le_of_ne (hmin ⟨(2, 0), by decide⟩)
      (first_ne (f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(0, 1), by decide⟩ ⟨(2, 0), by decide⟩ from by simp [arcGraph])))
    have b28 : x0 < x27 := lt_of_le_of_ne (hmin ⟨(3, 0), by decide⟩)
      (first_ne (f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(0, 1), by decide⟩ ⟨(3, 0), by decide⟩ from by simp [arcGraph])))
    have h0 : (x1 = x9 ∧ x2 = x10 ∨ x2 = x9) ∨
        (x10 = x0 ∧ x11 = x1 ∨ x11 = x0) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(0, 1), by decide⟩ ⟨(1, 0), by decide⟩ from by simp [arcGraph])
    have h1 : (x1 = x12 ∧ x2 = x13 ∨ x2 = x12) ∨
        (x13 = x0 ∧ x14 = x1 ∨ x14 = x0) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(0, 1), by decide⟩ ⟨(1, 2), by decide⟩ from by simp [arcGraph])
    have h2 : (x1 = x15 ∧ x2 = x16 ∨ x2 = x15) ∨
        (x16 = x0 ∧ x17 = x1 ∨ x17 = x0) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(0, 1), by decide⟩ ⟨(1, 3), by decide⟩ from by simp [arcGraph])
    have h3 : (x1 = x18 ∧ x2 = x19 ∨ x2 = x18) ∨
        (x19 = x0 ∧ x20 = x1 ∨ x20 = x0) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(0, 1), by decide⟩ ⟨(2, 0), by decide⟩ from by simp [arcGraph])
    have h4 : (x1 = x27 ∧ x2 = x28 ∨ x2 = x27) ∨
        (x28 = x0 ∧ x29 = x1 ∨ x29 = x0) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(0, 1), by decide⟩ ⟨(3, 0), by decide⟩ from by simp [arcGraph])
    have h5 : (x4 = x9 ∧ x5 = x10 ∨ x5 = x9) ∨
        (x10 = x3 ∧ x11 = x4 ∨ x11 = x3) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(0, 2), by decide⟩ ⟨(1, 0), by decide⟩ from by simp [arcGraph])
    have h6 : (x4 = x18 ∧ x5 = x19 ∨ x5 = x18) ∨
        (x19 = x3 ∧ x20 = x4 ∨ x20 = x3) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(0, 2), by decide⟩ ⟨(2, 0), by decide⟩ from by simp [arcGraph])
    have h7 : (x4 = x21 ∧ x5 = x22 ∨ x5 = x21) ∨
        (x22 = x3 ∧ x23 = x4 ∨ x23 = x3) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(0, 2), by decide⟩ ⟨(2, 1), by decide⟩ from by simp [arcGraph])
    have h8 : (x4 = x24 ∧ x5 = x25 ∨ x5 = x24) ∨
        (x25 = x3 ∧ x26 = x4 ∨ x26 = x3) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(0, 2), by decide⟩ ⟨(2, 3), by decide⟩ from by simp [arcGraph])
    have h9 : (x4 = x27 ∧ x5 = x28 ∨ x5 = x27) ∨
        (x28 = x3 ∧ x29 = x4 ∨ x29 = x3) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(0, 2), by decide⟩ ⟨(3, 0), by decide⟩ from by simp [arcGraph])
    have h10 : (x7 = x9 ∧ x8 = x10 ∨ x8 = x9) ∨
        (x10 = x6 ∧ x11 = x7 ∨ x11 = x6) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(0, 3), by decide⟩ ⟨(1, 0), by decide⟩ from by simp [arcGraph])
    have h11 : (x7 = x18 ∧ x8 = x19 ∨ x8 = x18) ∨
        (x19 = x6 ∧ x20 = x7 ∨ x20 = x6) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(0, 3), by decide⟩ ⟨(2, 0), by decide⟩ from by simp [arcGraph])
    have h12 : (x7 = x27 ∧ x8 = x28 ∨ x8 = x27) ∨
        (x28 = x6 ∧ x29 = x7 ∨ x29 = x6) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(0, 3), by decide⟩ ⟨(3, 0), by decide⟩ from by simp [arcGraph])
    have h13 : (x7 = x30 ∧ x8 = x31 ∨ x8 = x30) ∨
        (x31 = x6 ∧ x32 = x7 ∨ x32 = x6) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(0, 3), by decide⟩ ⟨(3, 1), by decide⟩ from by simp [arcGraph])
    have h14 : (x7 = x33 ∧ x8 = x34 ∨ x8 = x33) ∨
        (x34 = x6 ∧ x35 = x7 ∨ x35 = x6) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(0, 3), by decide⟩ ⟨(3, 2), by decide⟩ from by simp [arcGraph])
    have h15 : (x10 = x21 ∧ x11 = x22 ∨ x11 = x21) ∨
        (x22 = x9 ∧ x23 = x10 ∨ x23 = x9) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(1, 0), by decide⟩ ⟨(2, 1), by decide⟩ from by simp [arcGraph])
    have h16 : (x10 = x30 ∧ x11 = x31 ∨ x11 = x30) ∨
        (x31 = x9 ∧ x32 = x10 ∨ x32 = x9) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(1, 0), by decide⟩ ⟨(3, 1), by decide⟩ from by simp [arcGraph])
    have h17 : (x13 = x18 ∧ x14 = x19 ∨ x14 = x18) ∨
        (x19 = x12 ∧ x20 = x13 ∨ x20 = x12) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(1, 2), by decide⟩ ⟨(2, 0), by decide⟩ from by simp [arcGraph])
    have h18 : (x13 = x21 ∧ x14 = x22 ∨ x14 = x21) ∨
        (x22 = x12 ∧ x23 = x13 ∨ x23 = x12) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(1, 2), by decide⟩ ⟨(2, 1), by decide⟩ from by simp [arcGraph])
    have h19 : (x13 = x24 ∧ x14 = x25 ∨ x14 = x24) ∨
        (x25 = x12 ∧ x26 = x13 ∨ x26 = x12) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(1, 2), by decide⟩ ⟨(2, 3), by decide⟩ from by simp [arcGraph])
    have h20 : (x13 = x30 ∧ x14 = x31 ∨ x14 = x30) ∨
        (x31 = x12 ∧ x32 = x13 ∨ x32 = x12) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(1, 2), by decide⟩ ⟨(3, 1), by decide⟩ from by simp [arcGraph])
    have h21 : (x16 = x21 ∧ x17 = x22 ∨ x17 = x21) ∨
        (x22 = x15 ∧ x23 = x16 ∨ x23 = x15) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(1, 3), by decide⟩ ⟨(2, 1), by decide⟩ from by simp [arcGraph])
    have h22 : (x16 = x27 ∧ x17 = x28 ∨ x17 = x27) ∨
        (x28 = x15 ∧ x29 = x16 ∨ x29 = x15) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(1, 3), by decide⟩ ⟨(3, 0), by decide⟩ from by simp [arcGraph])
    have h23 : (x16 = x30 ∧ x17 = x31 ∨ x17 = x30) ∨
        (x31 = x15 ∧ x32 = x16 ∨ x32 = x15) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(1, 3), by decide⟩ ⟨(3, 1), by decide⟩ from by simp [arcGraph])
    have h24 : (x16 = x33 ∧ x17 = x34 ∨ x17 = x33) ∨
        (x34 = x15 ∧ x35 = x16 ∨ x35 = x15) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(1, 3), by decide⟩ ⟨(3, 2), by decide⟩ from by simp [arcGraph])
    have h25 : (x19 = x33 ∧ x20 = x34 ∨ x20 = x33) ∨
        (x34 = x18 ∧ x35 = x19 ∨ x35 = x18) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(2, 0), by decide⟩ ⟨(3, 2), by decide⟩ from by simp [arcGraph])
    have h26 : (x22 = x33 ∧ x23 = x34 ∨ x23 = x33) ∨
        (x34 = x21 ∧ x35 = x22 ∨ x35 = x21) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(2, 1), by decide⟩ ⟨(3, 2), by decide⟩ from by simp [arcGraph])
    have h27 : (x25 = x27 ∧ x26 = x28 ∨ x26 = x27) ∨
        (x28 = x24 ∧ x29 = x25 ∨ x29 = x24) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(2, 3), by decide⟩ ⟨(3, 0), by decide⟩ from by simp [arcGraph])
    have h28 : (x25 = x30 ∧ x26 = x31 ∨ x26 = x30) ∨
        (x31 = x24 ∧ x32 = x25 ∨ x32 = x24) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(2, 3), by decide⟩ ⟨(3, 1), by decide⟩ from by simp [arcGraph])
    have h29 : (x25 = x33 ∧ x26 = x34 ∨ x26 = x33) ∨
        (x34 = x24 ∧ x35 = x25 ∨ x35 = x24) :=
      f.map_adj (show (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj
        ⟨(2, 3), by decide⟩ ⟨(3, 2), by decide⟩ from by simp [arcGraph])
    exact symbolic_certificate A
      x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35
      b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28
      h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29
    : False)


private theorem pair_permutation : ∀ u v : Fin 4, u ≠ v →
    ∃ e : Fin 4 → Fin 4, Function.Bijective e ∧ e 0 = u ∧ e 1 = v := by
  decide +kernel

/-- Symmetry of the four source vertices lets us normalize a least image. -/
theorem no_arc_four (A : Type*) [LinearOrder A] :
    IsEmpty (arcGraph (⊤ : SimpleGraph (Fin 4)) →g graph A) := by
  classical
  refine ⟨?_⟩
  intro f
  let z : Arc (⊤ : SimpleGraph (Fin 4)) := ⟨(0,1), by decide⟩
  have hu : (Finset.univ : Finset (Arc (⊤ : SimpleGraph (Fin 4)))).Nonempty :=
    ⟨z, Finset.mem_univ z⟩
  obtain ⟨p, _, hmin⟩ := Finset.exists_min_image Finset.univ (fun p => (f p).a) hu
  obtain ⟨e, he, he0, he1⟩ := pair_permutation p.1.1 p.1.2 p.2
  let g : arcGraph (⊤ : SimpleGraph (Fin 4)) →g graph A :=
    { toFun := fun q => f ⟨(e q.1.1, e q.1.2), fun h => q.2 (he.1 h)⟩
      map_rel' := by
        intro q r hqr
        apply f.map_adj
        rcases hqr with h | h
        · exact Or.inl (congrArg e h)
        · exact Or.inr (congrArg e h) }
  have hg : g z = f p := by
    apply congrArg f
    exact Subtype.ext (Prod.ext he0 he1)
  apply no_arc_four_min A g
  intro q
  change (g z).a ≤ _
  rw [hg]
  exact hmin _ (Finset.mem_univ _)

/-- The right adjoint of the shift-square graph is K4-free. Non-coverability
of this candidate is NOT asserted here. -/
theorem right_shift_cliqueFree (A : Type*) [LinearOrder A] :
    (right (graph A)).CliqueFree 4 := by
  by_contra h
  obtain ⟨f⟩ := (right_not_cliqueFree_iff (graph A) 4).mp h
  exact (no_arc_four A).false f

#print axioms no_arc_four
#print axioms right_shift_cliqueFree
end Erdos595ArcShift
