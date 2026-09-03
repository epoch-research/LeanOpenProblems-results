import Submission.OrderedQuadRight

/-! Finite order patterns for the ordered-quadruple right-adjoint candidate. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
open SimpleGraph Set
namespace Erdos595OrderedQuadRight
variable {A : Type*} [LinearOrder A]

def Slide (x y : Quad A) : Prop :=
  x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 3 ∧ x 0 < x 1 ∧
    y 1 < y 2 ∧ y 2 < y 3 ∧ y 3 < x 3

theorem slide_common_first {x y w : Quad A} (h : Slide x y)
    (hx : Adj x w) (hy : Adj y w) : w 0 = x 0 := by
  rcases h with ⟨s0,s1,s2,s3,s4,s5,s6⟩
  rcases hx with hx | hx | hx | hx | hx | hx
  · rcases hy with hy | hy | hy | hy | hy | hy
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
  · rcases hy with hy | hy | hy | hy | hy | hy
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
  · rcases hy with hy | hy | hy | hy | hy | hy
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
  · rcases hy with hy | hy | hy | hy | hy | hy
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exact h0.symm
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
  · rcases hy with hy | hy | hy | hy | hy | hy
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
  · rcases hy with hy | hy | hy | hy | hy | hy
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order
    · rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6⟩
      rcases hy with ⟨k0,k1,k2,k3,k4,k5,k6⟩
      exfalso
      order

def Pattern (k : Fin 6) (x y : Quad A) : Prop :=
  ![AB x y,AC x y,AB y x,BC x y,AC y x,BC y x] k

lemma pattern_exists {x y : Quad A} (h : Adj x y) : ∃ k, Pattern k x y := by
  rcases h with h | h | h | h | h | h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩
  · exact ⟨2,h⟩
  · exact ⟨3,h⟩
  · exact ⟨4,h⟩
  · exact ⟨5,h⟩

/-- Four residual diagrams suffice once the three opposite witness pairs
have the same directed order type. -/
theorem mono_shape (v : Fin 6 → Quad A) (k : Fin 6)
    (t : TriOptions (v 0) (v 1) (v 2))
    (u : TriOptions (v 3) (v 4) (v 5))
    (h : Pattern k (v 0) (v 3))
    (j : Pattern k (v 5) (v 2))
    (l : Pattern k (v 1) (v 4)) :
    v 0 0 ≠ v 4 0 ∧ v 1 0 ≠ v 3 0 ∧
      (Slide (v 1) (v 5) ∨ Slide (v 4) (v 2) ∨
       Slide (v 0) (v 5) ∨ Slide (v 3) (v 2)) := by
  fin_cases k
  · rcases t with t | t | t | t | t | t
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t7 (le_of_eq t5)) (le_of_eq j0.symm)) (le_of_eq u0.symm)) h2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t9 (le_of_eq h1)) (le_of_eq u3)) (le_of_eq l1.symm)) (le_of_eq t1.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le t6 (le_of_eq t0)) j4) (le_of_eq u0.symm)) l2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t8 (le_of_eq h0)) (le_of_eq u1.symm)) (le_of_eq j0)) (le_of_eq t5.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_trans (lt_of_lt_of_le (lt_trans t6 h3) (le_of_eq u0.symm)) l2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t8 (le_of_eq h0)) (le_of_eq u5.symm)) l4)
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans t7 j4) (le_of_eq u0.symm)) h2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t7 j4) (le_of_eq u5)) (le_of_eq l0.symm)) (le_of_eq t0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans t6 t7) j4) (le_of_eq u0.symm)) l2) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t8 (le_of_eq t1)) (le_of_eq j0.symm)) u9) u10) (le_of_eq u3)) (le_of_eq l1.symm)) (le_of_eq t5.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans t6 h3) (le_of_eq u0.symm)) l2) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t7 j4) (le_of_eq u1)) (le_of_eq l0.symm)) (le_of_eq t0.symm))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le t6 (le_of_eq t0)) j4) (le_of_eq u0.symm)) h2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans t6 l3) (le_of_eq u0.symm)) h2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t7 (le_of_eq t5)) (le_of_eq j0.symm)) (le_of_eq u0.symm)) l2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t8 (le_of_eq l0)) (le_of_eq u5.symm)) h4)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t9 (le_of_eq l1)) (le_of_eq u3)) (le_of_eq h1.symm)) (le_of_eq t1.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t8 (le_of_eq l0)) (le_of_eq u1.symm)) (le_of_eq j0)) (le_of_eq t5.symm))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans t6 j2) (le_of_eq u4.symm)) u6) h2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_trans t6 j2) u6) h2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans t6 j2) (le_of_eq u4.symm)) h2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t8 j4) (le_of_eq u1)) (le_of_eq h0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans t6 j2) (le_of_eq u4)) h2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t7 (le_of_eq h0)) (le_of_eq u5.symm)) l4) (le_of_eq t0.symm))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans (lt_trans t6 t7) j4) (le_of_eq u0.symm)) h2) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans t6 l3) (le_of_eq u0.symm)) h2) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_trans (lt_of_lt_of_le (lt_trans t7 j4) (le_of_eq u0.symm)) l2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t7 j4) (le_of_eq u1)) (le_of_eq h0.symm)) (le_of_eq t0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t7 j4) (le_of_eq u5)) (le_of_eq h0.symm)) (le_of_eq t0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t8 (le_of_eq t1)) (le_of_eq j0.symm)) u9) u10) (le_of_eq u3)) (le_of_eq h1.symm)) (le_of_eq t5.symm))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_trans (lt_of_lt_of_le (lt_trans t6 j2) (le_of_eq u4.symm)) l2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_trans (lt_of_lt_of_le (lt_trans t6 j2) (le_of_eq u4)) l2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans t6 j2) (le_of_eq u4.symm)) u6) l2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t7 (le_of_eq l0)) (le_of_eq u5.symm)) h4) (le_of_eq t0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_trans (lt_trans (lt_trans t6 j2) u6) l2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t8 j4) (le_of_eq u1)) (le_of_eq l0.symm))
  · rcases t with t | t | t | t | t | t
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq t0)) (le_of_eq j0.symm)) (le_of_eq u4.symm)) l2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq t0)) (le_of_eq j0.symm)) (le_of_eq u4)) l2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le t6 (le_of_eq h0)) u8) (le_of_eq l0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq t0)) (le_of_eq j0.symm)) (le_of_eq u0)) (le_of_eq l0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq h0)) (le_of_eq u0.symm)) l2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t6 h3) (le_of_eq u5.symm)) (le_of_eq l0.symm))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t6 t7) (le_of_eq j0.symm)) (le_of_eq u4.symm)) l2) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t6 t7) (le_of_eq j0.symm)) (le_of_eq u4)) l2) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le t6 (le_of_eq h0)) u8) (le_of_eq l0.symm)) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t6 t7) (le_of_eq j0.symm)) (le_of_eq u0)) (le_of_eq l0.symm)) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq h0)) (le_of_eq u0.symm)) l2) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t6 h3) (le_of_eq u5.symm)) (le_of_eq l0.symm)) (le_of_eq t4.symm))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le t6 (le_of_eq l0)) u8) (le_of_eq h0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq l0)) (le_of_eq u0.symm)) h2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq t0)) (le_of_eq j0.symm)) (le_of_eq u4.symm)) h2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t6 l3) (le_of_eq u5.symm)) (le_of_eq h0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq t0)) (le_of_eq j0.symm)) (le_of_eq u4)) h2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq t0)) (le_of_eq j0.symm)) (le_of_eq u0)) (le_of_eq h0.symm))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans t6 j2) (le_of_eq u4.symm)) u6) h2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_trans (lt_trans (lt_trans t6 j2) u6) h2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans t6 j2) (le_of_eq u4.symm)) h2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans t6 j2) u7) (le_of_eq h0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_trans (lt_of_lt_of_le (lt_trans t6 j2) (le_of_eq u4)) h2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t6 j2) (le_of_eq u0)) (le_of_eq h0.symm))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le t6 (le_of_eq l0)) u8) (le_of_eq h0.symm)) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq l0)) (le_of_eq u0.symm)) h2) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t6 t7) (le_of_eq j0.symm)) (le_of_eq u4.symm)) h2) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t6 l3) (le_of_eq u5.symm)) (le_of_eq h0.symm)) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t6 t7) (le_of_eq j0.symm)) (le_of_eq u4)) h2) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t6 t7) (le_of_eq j0.symm)) (le_of_eq u0)) (le_of_eq h0.symm)) (le_of_eq t4.symm))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_trans (lt_of_lt_of_le (lt_trans t6 j2) (le_of_eq u4.symm)) l2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_trans (lt_of_lt_of_le (lt_trans t6 j2) (le_of_eq u4)) l2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans t6 j2) (le_of_eq u4.symm)) u6) l2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t6 j2) (le_of_eq u0)) (le_of_eq l0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_trans (lt_trans (lt_trans t6 j2) u6) l2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_trans (lt_trans t6 j2) u7) (le_of_eq l0.symm))
  · rcases t with t | t | t | t | t | t
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t7 l4) (le_of_eq u5)) (le_of_eq j0.symm)) (le_of_eq t0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans t7 t8) h4) (le_of_eq u1)) (le_of_eq j0.symm)) (le_of_eq t0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans t6 h2) (le_of_eq u4)) j2) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans t6 h2) u6) j2) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans t6 h2) (le_of_eq u4.symm)) j2) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans t6 h2) (le_of_eq u4.symm)) u6) j2) (le_of_eq t4.symm))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans t9 t10) (le_of_eq h1.symm)) u10) (le_of_eq u3)) (le_of_eq j1.symm)) (le_of_eq t1.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t8 h4) (le_of_eq u1)) (le_of_eq j0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_of_lt_of_le (lt_trans t6 h2) (le_of_eq u4)) j2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_trans (lt_trans t6 h2) u6) j2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_of_lt_of_le (lt_trans t6 h2) (le_of_eq u4.symm)) j2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans t6 h2) (le_of_eq u4.symm)) u6) j2)
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans t6 l2) (le_of_eq u4)) j2) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans t6 l2) (le_of_eq u4.symm)) j2) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t7 h4) (le_of_eq u5)) (le_of_eq j0.symm)) (le_of_eq t0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans t6 l2) (le_of_eq u4.symm)) u6) j2) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans t7 t8) l4) (le_of_eq u1)) (le_of_eq j0.symm)) (le_of_eq t0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans t6 l2) u6) j2) (le_of_eq t4.symm))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t8 (le_of_eq j0)) (le_of_eq u5.symm)) (le_of_eq l0)) (le_of_eq t5.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t9 t10) (le_of_eq t3)) (le_of_eq l1.symm)) (le_of_eq u5.symm)) j4)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t8 (le_of_eq t1)) (le_of_eq h0.symm)) u8) (le_of_eq l0)) (le_of_eq t5.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t7 (le_of_eq t5)) (le_of_eq l0.symm)) (le_of_eq u0.symm)) j2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans t7 h4) (le_of_eq u0.symm)) l3) (le_of_eq t0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_of_lt_of_le (lt_trans t7 h4) (le_of_eq u0.symm)) j2)
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_of_lt_of_le (lt_trans t6 l2) (le_of_eq u4)) j2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_of_lt_of_le (lt_trans t6 l2) (le_of_eq u4.symm)) j2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans t9 t10) (le_of_eq l1.symm)) u10) (le_of_eq u3)) (le_of_eq j1.symm)) (le_of_eq t1.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans t6 l2) (le_of_eq u4.symm)) u6) j2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t8 l4) (le_of_eq u1)) (le_of_eq j0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_trans (lt_trans t6 l2) u6) j2)
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t8 (le_of_eq t1)) (le_of_eq l0.symm)) u8) (le_of_eq h0)) (le_of_eq t5.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans t7 l4) (le_of_eq u0.symm)) h3) (le_of_eq t0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t8 (le_of_eq j0)) (le_of_eq u5.symm)) (le_of_eq h0)) (le_of_eq t5.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_of_lt_of_le (lt_trans t7 l4) (le_of_eq u0.symm)) j2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 1)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t9 t10) (le_of_eq t3)) (le_of_eq h1.symm)) (le_of_eq u5.symm)) j4)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t7 (le_of_eq t5)) (le_of_eq h0.symm)) (le_of_eq u0.symm)) j2)
  · rcases t with t | t | t | t | t | t
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t7 (le_of_eq t5)) (le_of_eq j1.symm)) (le_of_eq u0.symm)) (le_of_eq h0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        refine ⟨?_,?_,Or.inl (?_)⟩
        · order
        · order
        · refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> (first | assumption | order)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le t6 (le_of_eq h0)) u6) (le_of_eq l0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq h0)) (le_of_eq u4)) (le_of_eq l0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t6 h2) (le_of_eq u0.symm)) (le_of_eq l0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq h0)) (le_of_eq u4.symm)) (le_of_eq l0.symm))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t7 j3) (le_of_eq u0.symm)) (le_of_eq h0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t7 j3) (le_of_eq u5)) (le_of_eq l1.symm)) (le_of_eq t0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq h0)) (le_of_eq u4)) (le_of_eq j0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le t6 (le_of_eq h0)) u6) (le_of_eq j0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq h0)) (le_of_eq u4.symm)) (le_of_eq j0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t6 h2) (le_of_eq u0.symm)) (le_of_eq j0))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le t6 (le_of_eq l0)) u6) (le_of_eq h0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t6 l2) (le_of_eq u0.symm)) (le_of_eq h0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t7 (le_of_eq t5)) (le_of_eq j1.symm)) (le_of_eq u0.symm)) (le_of_eq l0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq l0)) (le_of_eq u4.symm)) (le_of_eq h0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        refine ⟨?_,?_,Or.inr (Or.inr (Or.inl (?_)))⟩
        · order
        · order
        · refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> (first | assumption | order)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq l0)) (le_of_eq u4)) (le_of_eq h0.symm))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq j0.symm)) (le_of_eq u4.symm)) u6) (le_of_eq h0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le t6 (le_of_eq j0.symm)) u6) (le_of_eq h0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq j0.symm)) (le_of_eq u4.symm)) (le_of_eq h0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t8 j3) (le_of_eq u1)) (le_of_eq h1.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq j0.symm)) (le_of_eq u4)) (le_of_eq h0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t7 (le_of_eq h1)) (le_of_eq u5.symm)) l3) (le_of_eq t0.symm))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq l0)) (le_of_eq u4)) (le_of_eq j0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq l0)) (le_of_eq u4.symm)) (le_of_eq j0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t7 j3) (le_of_eq u0.symm)) (le_of_eq l0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t6 l2) (le_of_eq u0.symm)) (le_of_eq j0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t7 j3) (le_of_eq u5)) (le_of_eq h1.symm)) (le_of_eq t0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le t6 (le_of_eq l0)) u6) (le_of_eq j0))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq j0.symm)) (le_of_eq u4.symm)) (le_of_eq l0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq j0.symm)) (le_of_eq u4)) (le_of_eq l0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq j0.symm)) (le_of_eq u4.symm)) u6) (le_of_eq l0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t7 (le_of_eq l1)) (le_of_eq u5.symm)) h3) (le_of_eq t0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le t6 (le_of_eq j0.symm)) u6) (le_of_eq l0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 1)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t8 j3) (le_of_eq u1)) (le_of_eq l1.symm))
  · rcases t with t | t | t | t | t | t
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t6 h2) (le_of_eq u0)) (le_of_eq j0.symm)) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans t6 h2) u7) (le_of_eq j0.symm)) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans t6 h2) (le_of_eq u4)) j2) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans t6 h2) u6) j2) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans t6 h2) (le_of_eq u4.symm)) j2) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans t6 t7) (le_of_eq l0.symm)) u6) j2) (le_of_eq t4.symm))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t6 h2) (le_of_eq u0)) (le_of_eq j0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_trans t6 h2) u7) (le_of_eq j0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_of_lt_of_le (lt_trans t6 h2) (le_of_eq u4)) j2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_trans (lt_trans t6 h2) u6) j2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_of_lt_of_le (lt_trans t6 h2) (le_of_eq u4.symm)) j2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq t0)) (le_of_eq l0.symm)) u6) j2)
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans t6 l2) (le_of_eq u4)) j2) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_trans t6 l2) (le_of_eq u4.symm)) j2) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t6 l2) (le_of_eq u0)) (le_of_eq j0.symm)) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le (lt_trans t6 t7) (le_of_eq h0.symm)) u6) j2) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans (lt_trans t6 l2) u7) (le_of_eq j0.symm)) (le_of_eq t4.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_trans t6 l2) u6) j2) (le_of_eq t4.symm))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t7 (le_of_eq h0.symm)) (le_of_eq u0)) (le_of_eq j0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le t7 (le_of_eq h0.symm)) u7) (le_of_eq j0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t7 (le_of_eq h0.symm)) (le_of_eq u4)) j2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_trans (lt_of_lt_of_le t7 (le_of_eq h0.symm)) u6) j2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t7 (le_of_eq h0.symm)) (le_of_eq u4.symm)) j2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le t7 (le_of_eq t5)) l4) u8) (le_of_eq j0.symm))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_of_lt_of_le (lt_trans t6 l2) (le_of_eq u4)) j2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_of_lt_of_le (lt_trans t6 l2) (le_of_eq u4.symm)) j2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t6 l2) (le_of_eq u0)) (le_of_eq j0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq t0)) (le_of_eq h0.symm)) u6) j2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_trans t6 l2) u7) (le_of_eq j0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_trans (lt_trans t6 l2) u6) j2)
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t7 (le_of_eq l0.symm)) (le_of_eq u4)) j2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t7 (le_of_eq l0.symm)) (le_of_eq u4.symm)) j2)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t7 (le_of_eq l0.symm)) (le_of_eq u0)) (le_of_eq j0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_trans (lt_of_lt_of_le t7 (le_of_eq t5)) h4) u8) (le_of_eq j0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le t7 (le_of_eq l0.symm)) u7) (le_of_eq j0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_trans (lt_trans (lt_of_lt_of_le t7 (le_of_eq l0.symm)) u6) j2)
  · rcases t with t | t | t | t | t | t
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t7 l3) (le_of_eq u5)) (le_of_eq j1.symm)) (le_of_eq t0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t7 l3) (le_of_eq u0.symm)) (le_of_eq h0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le t6 (le_of_eq h0.symm)) u6) (le_of_eq l0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq h0.symm)) (le_of_eq u4)) (le_of_eq l0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq h0.symm)) (le_of_eq u4.symm)) u6) (le_of_eq l0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq h0.symm)) (le_of_eq u4.symm)) (le_of_eq l0))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        refine ⟨?_,?_,Or.inr (Or.inl (?_))⟩
        · order
        · order
        · refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> (first | assumption | order)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t7 (le_of_eq t5)) (le_of_eq l1.symm)) (le_of_eq u0.symm)) (le_of_eq h0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq h0.symm)) (le_of_eq u4)) (le_of_eq j0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le t6 (le_of_eq h0.symm)) u6) (le_of_eq j0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq h0.symm)) (le_of_eq u4.symm)) (le_of_eq j0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq h0.symm)) (le_of_eq u4.symm)) u6) (le_of_eq j0.symm))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le t6 (le_of_eq l0.symm)) u6) (le_of_eq h0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq l0.symm)) (le_of_eq u4.symm)) u6) (le_of_eq h0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t7 h3) (le_of_eq u5)) (le_of_eq j1.symm)) (le_of_eq t0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq l0.symm)) (le_of_eq u4.symm)) (le_of_eq h0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t7 h3) (le_of_eq u0.symm)) (le_of_eq l0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq l0.symm)) (le_of_eq u4)) (le_of_eq h0))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t6 j2) (le_of_eq u0.symm)) (le_of_eq h0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le t6 (le_of_eq j0)) u6) (le_of_eq h0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq j0)) (le_of_eq u4.symm)) (le_of_eq h0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t7 (le_of_eq t5)) (le_of_eq l1.symm)) (le_of_eq u0.symm)) (le_of_eq j0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 0 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq j0)) (le_of_eq u4)) (le_of_eq h0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t7 h3) (le_of_eq u0.symm)) (le_of_eq j0.symm))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq l0.symm)) (le_of_eq u4)) (le_of_eq j0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq l0.symm)) (le_of_eq u4.symm)) (le_of_eq j0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        refine ⟨?_,?_,Or.inr (Or.inr (Or.inr (?_)))⟩
        · order
        · order
        · refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> (first | assumption | order)
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq l0.symm)) (le_of_eq u4.symm)) u6) (le_of_eq j0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t7 (le_of_eq t5)) (le_of_eq h1.symm)) (le_of_eq u0.symm)) (le_of_eq l0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le t6 (le_of_eq l0.symm)) u6) (le_of_eq j0.symm))
    · rcases u with u | u | u | u | u | u
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq j0)) (le_of_eq u4.symm)) (le_of_eq l0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t6 (le_of_eq j0)) (le_of_eq u4)) (le_of_eq l0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t6 j2) (le_of_eq u0.symm)) (le_of_eq l0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_trans t7 l3) (le_of_eq u0.symm)) (le_of_eq j0.symm))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 1 0)) (lt_of_lt_of_le (lt_trans (lt_of_lt_of_le t6 (le_of_eq j0)) u6) (le_of_eq l0))
      · rcases t with ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10⟩
        rcases u with ⟨u0,u1,u2,u3,u4,u5,u6,u7,u8,u9,u10⟩
        rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
        rcases j with ⟨j0,j1,j2,j3,j4,j5,j6⟩
        rcases l with ⟨l0,l1,l2,l3,l4,l5,l6⟩
        exfalso
        exact (lt_irrefl (v 2 0)) (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le t7 (le_of_eq t5)) (le_of_eq h1.symm)) (le_of_eq u0.symm)) (le_of_eq j0.symm))

#print axioms slide_common_first
#print axioms mono_shape
end Erdos595OrderedQuadRight
