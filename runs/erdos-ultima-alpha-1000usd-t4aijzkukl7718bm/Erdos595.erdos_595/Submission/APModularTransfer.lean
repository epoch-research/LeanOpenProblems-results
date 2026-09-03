import Submission.ArithmeticProgressionObstruction

/-! A modular rank test that rules out all choices of arithmetic-progression
midpoints at once. This is auxiliary to Erdős 595. -/
set_option autoImplicit false
open scoped BigOperators Matrix
namespace Erdos595APModularTransfer
open Erdos595ArithmeticProgression
variable {n : ℕ}

/-- Remove column zero, since constant edge labels are always a solution. -/
def mat (T : Fin n → Fin 3 → Fin (n+1)) (m : Fin n → Fin 3)
    (R : Type*) [Ring R] : Matrix (Fin n) (Fin n) R := fun i j =>
  ∑ k : Fin 3, (if k = m i then -2 else 1) * (if j.succ = T i k then 1 else 0)

def incidence (T : Fin n → Fin 3 → Fin (n+1)) : Matrix (Fin n) (Fin n) (ZMod 3) :=
  fun i j => ∑ k : Fin 3, if j.succ = T i k then 1 else 0

lemma map_mat (T : Fin n → Fin 3 → Fin (n+1)) (m : Fin n → Fin 3)
    {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    (mat T m R).map f = mat T m S := by
  ext i j
  simp only [Matrix.map_apply,mat,map_sum,map_mul]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> norm_num
  exact map_ofNat f 2

lemma mod_three (T : Fin n → Fin 3 → Fin (n+1)) (m : Fin n → Fin 3) :
    mat T m (ZMod 3) = incidence T := by
  ext i j
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> decide

lemma det_ne_zero (T : Fin n → Fin 3 → Fin (n+1)) (m : Fin n → Fin 3)
    (h : (incidence T).det ≠ 0) : (mat T m ℚ).det ≠ 0 := by
  have h3 := (Int.castRingHom (ZMod 3)).map_det (mat T m ℤ)
  change (Int.castRingHom (ZMod 3)) (mat T m ℤ).det =
    ((mat T m ℤ).map (Int.castRingHom (ZMod 3))).det at h3
  rw [map_mat,mod_three] at h3
  have hz : (mat T m ℤ).det ≠ 0 := by
    intro he
    apply h
    rw [← h3,he,map_zero]
  have he := (Int.castRingHom ℚ).map_det (mat T m ℤ)
  change (Int.castRingHom ℚ) (mat T m ℤ).det =
    ((mat T m ℤ).map (Int.castRingHom ℚ)).det at he
  rw [map_mat] at he
  rw [← he]
  change ((mat T m ℤ).det : ℚ) ≠ 0
  exact Int.cast_ne_zero.mpr hz

lemma row_formula (T : Fin n → Fin 3 → Fin (n+1)) (m : Fin n → Fin 3)
    (g : Fin (n+1) → ℚ) (hg : g 0 = 0) (i : Fin n) :
    ((mat T m ℚ).mulVec (fun j => g j.succ)) i =
      defect (m i) (g (T i 0)) (g (T i 1)) (g (T i 2)) := by
  have hs (a : Fin (n+1)) :
      (∑ j : Fin n, (if j.succ = a then (1 : ℚ) else 0) * g j.succ) = g a := by
    refine Fin.cases ?_ (fun k => ?_) a
    · simp [hg]
    · simp
  change (∑ j : Fin n, (∑ k : Fin 3,
      (if k = m i then (-2 : ℚ) else 1) * (if j.succ = T i k then 1 else 0)) * g j.succ) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc,← Finset.mul_sum,hs]
  generalize m i = z
  fin_cases z <;> simp [Fin.sum_univ_succ,defect] <;> ring

/-- A nonsingular reduced incidence matrix modulo three forces rational
AP labels to be constant, independently of all midpoint choices. -/
theorem rational_constant (T : Fin n → Fin 3 → Fin (n+1))
    (hT : (incidence T).det ≠ 0) (m : Fin n → Fin 3)
    (f : Fin (n+1) → ℚ)
    (hf : ∀ i, defect (m i) (f (T i 0)) (f (T i 1)) (f (T i 2)) = 0) :
    ∀ j, f j = f 0 := by
  let g : Fin (n+1) → ℚ := fun j => f j - f 0
  have hg : g 0 = 0 := sub_self _
  have he : (mat T m ℚ).mulVec (fun j => g j.succ) = 0 := by
    funext i
    rw [row_formula T m g hg i]
    have hi := hf i
    dsimp only [g]
    generalize m i = z at hi ⊢
    fin_cases z <;> simp [defect] at hi ⊢ <;> linarith
  have hz := Matrix.eq_zero_of_mulVec_eq_zero (det_ne_zero T m hT) he
  intro j
  refine Fin.cases rfl (fun k => ?_) j
  exact sub_eq_zero.mp (congrFun hz k)

/-- The same obstruction applies in every rational vector space, without
a dimension bound. -/
theorem vector_constant (T : Fin n → Fin 3 → Fin (n+1))
    (hT : (incidence T).det ≠ 0) (m : Fin n → Fin 3)
    {E : Type*} [AddCommGroup E] [Module ℚ E] (f : Fin (n+1) → E)
    (hf : ∀ i, defect (m i) (f (T i 0)) (f (T i 1)) (f (T i 2)) = 0) :
    ∀ j, f j = f 0 := by
  classical
  let b := Module.Free.chooseBasis ℚ E
  intro j
  apply b.repr.injective
  ext a
  apply rational_constant T hT m (fun k => (b.repr (f k)) a) ?_ j
  intro i
  have hi := congrArg (fun v : E => (b.repr v) a) (hf i)
  generalize m i = z at hi ⊢
  fin_cases z <;> simpa [defect] using hi

#print axioms rational_constant
#print axioms vector_constant
end Erdos595APModularTransfer
