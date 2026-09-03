import Submission.GaussianSmoothedSieve
import Submission.PrimePathCounting

/-! Smoothed counts still detect the linearly many vertices forced by a
prime ray. This supplies the lower bound needed to compare with a smoothed
sieve; it does not assert that a contradictory sieve upper bound exists. -/
namespace Erdos952Investigation.GaussianSmoothedPathCounts
open GaussianIdealBoxCounts GaussianSmoothedPolynomialCounts PrimePathCounting
open SievePeriodicDrift
open scoped BigOperators Classical
set_option maxHeartbeats 0
noncomputable section

/-- Each point within coordinate distance T of the center has triangular
weight at least 1/9 when the two boxes have side 3T. -/
theorem enclosed_finset_le_smoothed (E : Finset GaussianInt) (p : GaussianInt → Prop)
    (a : GaussianInt) (T : ℕ) (hT : 0 < T) (hp : ∀ z ∈ E, p z)
    (hbox : ∀ z ∈ E, |z.re-a.re| ≤ (T : ℤ) ∧ |z.im-a.im| ≤ (T : ℤ)) :
    (E.card : ℝ) ≤ 9*smoothedCount p a 0 (3*T) := by
  let H : GaussianInt := ⟨T,T⟩
  let f : E × Box 0 T → {uv : Box a (3*T) × Box 0 (3*T) // p (uv.1.val-uv.2.val)} := fun zw =>
    ⟨(⟨zw.1.val+H+zw.2.val,by
      have hz := hbox zw.1.val zw.1.property
      have hzr := abs_le.mp hz.1
      have hzi := abs_le.mp hz.2
      have hw := zw.2.property
      dsimp [InBox] at hw
      dsimp [InBox,H]
      omega⟩,
     ⟨H+zw.2.val,by
      have hw := zw.2.property
      dsimp [InBox] at hw
      dsimp [InBox,H]
      omega⟩),by
      change p (zw.1.val+H+zw.2.val-(H+zw.2.val))
      have he : zw.1.val+H+zw.2.val-(H+zw.2.val) = zw.1.val := by abel
      rw [he]
      exact hp zw.1.val zw.1.property⟩
  have hf : Function.Injective f := by
    intro u v he
    have hz := congrArg (fun uv : {uv : Box a (3*T) × Box 0 (3*T) // p (uv.1.val-uv.2.val)} =>
      uv.val.1.val-uv.val.2.val) he
    have hw := congrArg (fun uv : {uv : Box a (3*T) × Box 0 (3*T) // p (uv.1.val-uv.2.val)} =>
      uv.val.2.val) he
    change u.1.val+H+u.2.val-(H+u.2.val) = v.1.val+H+v.2.val-(H+v.2.val) at hz
    change H+u.2.val = H+v.2.val at hw
    apply Prod.ext
    · apply Subtype.ext
      linear_combination hz
    · exact Subtype.ext (add_left_cancel hw)
  have hh := Nat.card_le_card_of_injective f hf
  have hE : Nat.card E = E.card := by simp
  rw [Nat.card_prod,hE,box_card] at hh
  have hc : (E.card : ℝ)*(T : ℝ)^2 ≤ (pairPredicateCount p a 0 (3*T) : ℝ) := by
    exact_mod_cast hh
  have hTp : 0 < (T : ℝ)^2 := sq_pos_of_pos (by exact_mod_cast hT)
  have he : 9*smoothedCount p a 0 (3*T) = (pairPredicateCount p a 0 (3*T) : ℝ)/(T : ℝ)^2 := by
    dsimp [smoothedCount]
    push_cast
    field_simp
    ring
  rw [he]
  exact (le_div_iff₀ hTp).mpr hc

/-- Smoothing does not lose the forced linear count: every vertex of the
initial segment is a start of a prime path of any prescribed length. -/
theorem ray_forces_smoothed_linear_count (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C)
    (M L : ℕ) (hM : 0 < M) :
    (M : ℝ)+1 ≤ 9*smoothedCount (Starts C L) (x 0) 0 (3*(M*C.toNat)) := by
  have hC : 0 < C := (GaussianInt.norm_nonneg _).trans_lt (h 0).2
  have hCn : 0 < C.toNat := by omega
  let T : ℕ := M*C.toNat
  let E : Finset GaussianInt := Finset.univ.image (fun i : Fin (M+1) => x i.val)
  have hE : E.card = M+1 := by
    have hi : Function.Injective (fun i : Fin (M+1) => x i.val) := hx.comp Fin.val_injective
    dsimp [E]
    rw [Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_fin]
  have hp : ∀ z ∈ E, Starts C L z := by
    intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    exact starts_of_prime_ray x C hx h i.val L
  have hb : ∀ z ∈ E, |z.re-(x 0).re| ≤ (T : ℤ) ∧ |z.im-(x 0).im| ≤ (T : ℤ) := by
    intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    have ht := taxicab_drift_le x C (fun n => (h n).2) 0 i.val
    simp only [Nat.zero_add,taxicab,Zsqrtd.re_sub,Zsqrtd.im_sub] at ht
    have hi : (i.val : ℤ) ≤ M := by exact_mod_cast (show i.val ≤ M by omega)
    have hm := mul_le_mul_of_nonneg_right hi hC.le
    have hT : (T : ℤ) = (M : ℤ)*C := by simp [T,Int.toNat_of_nonneg hC.le]
    rw [← hT] at hm
    have hr := abs_nonneg ((x i.val).re-(x 0).re)
    have him := abs_nonneg ((x i.val).im-(x 0).im)
    constructor <;> omega
  have hh := enclosed_finset_le_smoothed E (Starts C L) (x 0) T
    (Nat.mul_pos hM hCn) hp hb
  rw [hE,Nat.cast_add,Nat.cast_one] at hh
  exact hh

#print axioms enclosed_finset_le_smoothed
#print axioms ray_forces_smoothed_linear_count
end
end Erdos952Investigation.GaussianSmoothedPathCounts
