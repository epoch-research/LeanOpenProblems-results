import Submission.GaussianLargerSieve

/-! Sharp quadratic displacement bounds for bounded-step Gaussian paths,
and their substitution into the finite larger-sieve budget. These are
necessary conditions on a prime or admissible path, not a contradiction. -/
namespace Erdos952Investigation.GaussianPathLargerSieve
open GaussianCollisionDiscriminant GaussianLargerSieve
open scoped BigOperators Classical
set_option maxHeartbeats 0
noncomputable section

lemma sum_re {ι : Type*} (S : Finset ι) (z : ι → GaussianInt) :
    (∑ i ∈ S, z i).re = ∑ i ∈ S, (z i).re := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp [Finset.sum_insert hi,ih]

lemma sum_im {ι : Type*} (S : Finset ι) (z : ι → GaussianInt) :
    (∑ i ∈ S, z i).im = ∑ i ∈ S, (z i).im := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp [Finset.sum_insert hi,ih]

/-- Integer-coordinate Cauchy-Schwarz gives the squared Euclidean bound,
without replacing each jump by its squared norm in a taxicab estimate. -/
theorem norm_sum_le_card_mul_sum_norm {ι : Type*} (S : Finset ι) (z : ι → GaussianInt) :
    (∑ i ∈ S, z i).norm ≤ (S.card : ℤ)*(∑ i ∈ S, (z i).norm) := by
  have hr := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℤ)) (fun i => (z i).re)
  have hi := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℤ)) (fun i => (z i).im)
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hr hi
  rw [gaussian_norm_sq,sum_re,sum_im]
  calc
    _ ≤ (S.card : ℤ)*(∑ i ∈ S, (z i).re^2)+(S.card : ℤ)*(∑ i ∈ S, (z i).im^2) := add_le_add hr hi
    _ = _ := by simp only [gaussian_norm_sq,Finset.sum_add_distrib,mul_add]

theorem norm_forward_displacement_le (x : ℕ → GaussianInt) (C : ℤ)
    (hs : ∀ n, (x (n+1)-x n).norm ≤ C) (i h : ℕ) :
    (x (i+h)-x i).norm ≤ C*(h : ℤ)^2 := by
  have he := Finset.sum_range_sub (fun j => x (i+j)) h
  simp only [Nat.add_zero] at he
  have hh := norm_sum_le_card_mul_sum_norm (Finset.range h)
    (fun j => x (i+(j+1))-x (i+j))
  rw [he,Finset.card_range] at hh
  have hb : (∑ j ∈ Finset.range h, (x (i+(j+1))-x (i+j)).norm) ≤ (h : ℤ)*C := by
    calc
      _ ≤ ∑ _j ∈ Finset.range h, C := Finset.sum_le_sum (fun j _ => by simpa only [Nat.add_assoc] using hs (i+j))
      _ = _ := by simp
  calc
    _ ≤ (h : ℤ)*(∑ j ∈ Finset.range h, (x (i+(j+1))-x (i+j)).norm) := hh
    _ ≤ (h : ℤ)*((h : ℤ)*C) := mul_le_mul_of_nonneg_left hb (Int.natCast_nonneg h)
    _ = _ := by ring

lemma norm_sub_swap (z w : GaussianInt) : (z-w).norm = (w-z).norm := by
  rw [← Zsqrtd.norm_neg (z-w),neg_sub]

/-- With squared jump bound C, squared displacement is at most C times the
square of the index gap. -/
theorem norm_displacement_le (x : ℕ → GaussianInt) (C : ℤ)
    (hs : ∀ n, (x (n+1)-x n).norm ≤ C) (i j : ℕ) :
    (x i-x j).norm ≤ C*((i : ℤ)-(j : ℤ))^2 := by
  rcases le_total i j with hij | hji
  · calc
      _ = (x j-x i).norm := norm_sub_swap _ _
      _ ≤ C*((j-i : ℕ) : ℤ)^2 := by
        simpa only [Nat.add_sub_of_le hij] using norm_forward_displacement_le x C hs i (j-i)
      _ = _ := by rw [Nat.cast_sub hij]; ring
  · calc
      _ ≤ C*((i-j : ℕ) : ℤ)^2 := by
        simpa only [Nat.add_sub_of_le hji] using norm_forward_displacement_le x C hs j (i-j)
      _ = _ := by rw [Nat.cast_sub hji]

/-- Bounded jumps supply an explicit product budget for every finite path
window, and for every finite family of coprime Gaussian moduli. -/
theorem path_collision_product_bound {J : Type*}
    (x : ℕ → GaussianInt) (hx : Function.Injective x) (C : ℤ)
    (hs : ∀ n, (x (n+1)-x n).norm ≤ C) (k : ℕ)
    (g : J → GaussianInt) (S : Finset J)
    (hc : (S : Set J).Pairwise (fun i j => IsCoprime (g i) (g j))) :
    (∏ j ∈ S, (g j).norm^(collisionCount (fun i : Fin (k+1) => x i.val) (g j))) ≤
      ∏ ij ∈ (Finset.univ : Finset (Fin (k+1))).offDiag,
        C*((ij.1.val : ℤ)-(ij.2.val : ℤ))^2 := by
  exact collision_norm_product_le_bounds (fun i : Fin (k+1) => x i.val)
    (hx.comp Fin.val_injective) g S hc
    (fun ij => C*((ij.1.val : ℤ)-(ij.2.val : ℤ))^2)
    (fun i j _ => norm_displacement_le x C hs i.val j.val)

/-- The larger-sieve inequality with the path's index-gap budget inserted.
No asymptotic estimate of either side is asserted here. -/
theorem path_larger_sieve_inequality {J : Type*}
    (x : ℕ → GaussianInt) (hx : Function.Injective x) (C : ℤ)
    (hs : ∀ n, (x (n+1)-x n).norm ≤ C) (k : ℕ)
    (g : J → GaussianInt) (S : Finset J) (hg : ∀ j ∈ S, g j ≠ 0)
    (hc : (S : Set J).Pairwise (fun i j => IsCoprime (g i) (g j))) :
    ((k : ℝ)+1)^2*(∑ j ∈ S, Real.log ((g j).norm : ℝ)/
      (classes (fun i : Fin (k+1) => x i.val) (g j)).card) ≤
      (∑ ij ∈ (Finset.univ : Finset (Fin (k+1))).offDiag,
        Real.log ((C : ℝ)*((ij.1.val : ℝ)-(ij.2.val : ℝ))^2))+
      ((k : ℝ)+1)*(∑ j ∈ S, Real.log ((g j).norm : ℝ)) := by
  have hh := larger_sieve_distance_inequality (fun i : Fin (k+1) => x i.val)
    (hx.comp Fin.val_injective) g S hg hc
  simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] at hh
  have hp : (∑ ij ∈ (Finset.univ : Finset (Fin (k+1))).offDiag,
      Real.log ((x ij.1.val-x ij.2.val).norm : ℝ)) ≤
      ∑ ij ∈ (Finset.univ : Finset (Fin (k+1))).offDiag,
        Real.log ((C : ℝ)*((ij.1.val : ℝ)-(ij.2.val : ℝ))^2) := by
    apply Finset.sum_le_sum
    intro ij hij
    have hne := (Finset.mem_offDiag.mp hij).2.2
    have hxne : x ij.1.val-x ij.2.val ≠ 0 :=
      sub_ne_zero.mpr (fun he => hne (Fin.ext (hx he)))
    apply Real.log_le_log
    · exact_mod_cast GaussianInt.norm_pos.mpr hxne
    · exact_mod_cast norm_displacement_le x C hs ij.1.val ij.2.val
  linarith

#print axioms norm_sum_le_card_mul_sum_norm
#print axioms norm_displacement_le
#print axioms path_collision_product_bound
#print axioms path_larger_sieve_inequality
end
end Erdos952Investigation.GaussianPathLargerSieve
