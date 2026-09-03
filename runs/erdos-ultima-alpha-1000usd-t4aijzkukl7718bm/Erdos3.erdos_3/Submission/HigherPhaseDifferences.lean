import Submission.QuadraticRecurrenceExtraction
import Submission.LocalQuadraticProgressions

/-! Algebraic finite differences for higher-degree unit phases. These results
supply recurrence structure, not a higher Gowers inverse theorem. -/
namespace Erdos3HigherPhaseDifferences
open Finset
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 2000000

abbrev diffIter {G : Type*} [AddCommGroup G] (k : ℕ) (f : ℕ → G) : ℕ → G :=
  (fwdDiff (1 : ℕ))^[k] f

lemma diffIter_map {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (φ : G →+ H) (f : ℕ → G) (k : ℕ) :
    diffIter k (fun n ↦ φ (f n)) = fun n ↦ φ (diffIter k f n) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    rw [diffIter,Function.iterate_succ_apply]
    have he : fwdDiff (1 : ℕ) (fun n ↦ φ (f n)) = fun n ↦ φ (fwdDiff 1 f n) := by
      funext n
      exact (map_sub φ _ _).symm
    rw [he]
    exact ih (fwdDiff 1 f)

lemma diffIter_sub {G : Type*} [AddCommGroup G] (f g : ℕ → G) (k : ℕ) :
    diffIter k (f-g) = diffIter k f-diffIter k g := by
  simpa only [fwdDiff_aux.coe_fwdDiffₗ_pow] using
    map_sub ((fwdDiff_aux.fwdDiffₗ ℕ G 1)^k) f g

lemma diffIter_shifted_sub {G : Type*} [AddCommGroup G] (f : ℕ → G) (k i j n : ℕ) :
    diffIter k (fun n ↦ f (n+i)-f (n+j)) n = diffIter k f (n+i)-diffIter k f (n+j) := by
  have he : (fun n ↦ f (n+i)-f (n+j)) = (fun n ↦ f (n+i))-(fun n ↦ f (n+j)) := rfl
  rw [he,diffIter_sub]
  simp only [Pi.sub_apply,diffIter,fwdDiff_iter_comp_add]

lemma constant_step_shift {G : Type*} [AddCommGroup G] (f : ℕ → G) (z : G)
    (hf : ∀ n, f (n+1)-f n = z) (n h : ℕ) : f (n+h) = f n+h • z := by
  induction h with
  | zero => simp
  | succ h ih =>
    have hh := hf (n+h)
    rw [show n+(h+1) = n+h+1 by omega]
    rw [sub_eq_iff_eq_add.mp hh,ih,add_nsmul,one_nsmul]
    abel

/-- A constant kth unit-step difference controls all shifted (k-1)st differences.
The scale factor is the positive difference between the two shifts. -/
lemma shifted_difference_top {G : Type*} [AddCommGroup G] (f : ℕ → G) (z : G)
    (k : ℕ) (hf : diffIter (k+1) f = fun _ ↦ z) {i j : ℕ} (hji : j ≤ i) :
    diffIter k (fun n ↦ f (n+i)-f (n+j)) = fun _ ↦ (i-j) • z := by
  have hstep (n : ℕ) : diffIter k f (n+1)-diffIter k f n = z := by
    have hh := congr_fun hf n
    simpa only [diffIter,Function.iterate_succ_apply',fwdDiff] using hh
  funext n
  rw [diffIter_shifted_sub]
  have hh := constant_step_shift (diffIter k f) z hstep (n+j) (i-j)
  rw [Nat.add_assoc, Nat.add_sub_of_le hji] at hh
  rw [hh]
  abel

lemma diffIter_natCast {G : Type*} [AddCommGroup G] (f : ℤ → G) (k n : ℕ) :
    diffIter k (fun n : ℕ ↦ f (n : ℤ)) n = (fwdDiff (1 : ℤ))^[k] f (n : ℤ) := by
  induction k generalizing f n with
  | zero => rfl
  | succ k ih =>
    simp only [diffIter,Function.iterate_succ_apply']
    change diffIter k (fun n : ℕ ↦ f (n : ℤ)) (n+1)-diffIter k (fun n : ℕ ↦ f (n : ℤ)) n = _
    rw [ih,ih]
    simp only [fwdDiff,Nat.cast_add,Nat.cast_one]

/-- The kth difference of n↦n^k•z is the constant k!•z in any abelian group. -/
lemma diffIter_monomial {G : Type*} [AddCommGroup G] (z : G) (k : ℕ) :
    diffIter k (fun n : ℕ ↦ (n^k) • z) = fun _ ↦ (k.factorial) • z := by
  let φ : ℤ →+ G := zmultiplesHom G z
  have he : (fun n : ℕ ↦ (n^k) • z) = fun n : ℕ ↦ φ ((n : ℤ)^k) := by
    funext n
    change (n^k) • z = ((n : ℤ)^k) • z
    rw [← Nat.cast_pow,natCast_zsmul]
  rw [he,diffIter_map]
  funext n
  have hh := diffIter_natCast (fun n : ℤ ↦ n^k) k n
  rw [fwdDiff_iter_eq_factorial] at hh
  rw [hh]
  change ((k.factorial : ℕ) : ℤ) • z = k.factorial • z
  exact natCast_zsmul _ _

/-- A circle-valued additive phase, exposed as a unit complex number. -/
noncomputable def phase (x : Additive Circle) : ℂ := (Additive.toMul x : Circle)

lemma phase_norm (x : Additive Circle) : ‖phase x‖ = 1 := Circle.norm_coe _
lemma phase_add (x y : Additive Circle) : phase (x+y) = phase x*phase y := rfl
lemma phase_sub (x y : Additive Circle) : phase (x-y) = phase x*conj (phase y) := by
  change ((Additive.toMul x / Additive.toMul y : Circle) : ℂ) = _
  rw [div_eq_mul_inv,Circle.coe_mul,Circle.coe_inv_eq_conj]
  rfl

lemma phase_nsmul (n : ℕ) (x : Additive Circle) : phase (n • x) = (phase x)^n :=
  Circle.coeHom.map_pow _ _

/-- A first-order phase is a geometric sequence with a unit prefactor. -/
lemma first_difference_phase (f : ℕ → Additive Circle) (z : Additive Circle)
    (hf : diffIter 1 f = fun _ ↦ z) (n : ℕ) :
    phase (f n) = phase (f 0)*(phase z)^n := by
  have hstep (n : ℕ) : f (n+1)-f n = z := congr_fun hf n
  have hh := constant_step_shift f z hstep 0 n
  rw [Nat.zero_add] at hh
  rw [hh,phase_add,phase_nsmul]

#print axioms shifted_difference_top
#print axioms diffIter_monomial
end Erdos3HigherPhaseDifferences
