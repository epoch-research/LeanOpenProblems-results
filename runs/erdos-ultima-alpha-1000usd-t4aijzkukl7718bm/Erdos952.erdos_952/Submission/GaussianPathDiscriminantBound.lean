import Submission.GaussianPathLargerSieve

/-! The exact index-gap product is a fourth power of a superfactorial.
This preserves the factorial-scale constant in the bounded-path collision
budget, rather than replacing every gap by the full path diameter. -/
namespace Erdos952Investigation.GaussianPathDiscriminantBound
open GaussianCollisionDiscriminant GaussianLargerSieve GaussianPathLargerSieve
open scoped BigOperators Classical
set_option maxHeartbeats 0
noncomputable section

lemma symmetric_offDiag_product {M : Type*} [CommMonoid M] (k : ℕ)
    (F : Fin k × Fin k → M) (hF : ∀ i j, F (i,j) = F (j,i)) :
    (∏ ij ∈ (Finset.univ : Finset (Fin k)).offDiag, F ij) =
      (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, F (i,j))^2 := by
  let U := (Finset.univ : Finset (Fin k)).offDiag
  let A := U.filter (fun ij => ij.1 < ij.2)
  let B := U.filter (fun ij => ¬ ij.1 < ij.2)
  have hswap : (∏ ij ∈ B, F ij) = ∏ ij ∈ A, F ij := by
    apply Finset.prod_equiv (Equiv.prodComm (Fin k) (Fin k))
    · intro ij
      simp only [A,B,U,Finset.mem_filter,Finset.mem_offDiag,Finset.mem_univ,true_and,
        Equiv.prodComm_apply]
      constructor
      · rintro ⟨hne,hle⟩
        exact ⟨hne.symm,lt_of_le_of_ne (le_of_not_gt hle) hne.symm⟩
      · rintro ⟨hne,hlt⟩
        exact ⟨hne.symm,not_lt_of_ge hlt.le⟩
    · intro ij _
      exact hF ij.1 ij.2
  have hA : A = (Finset.univ : Finset (Fin k × Fin k)).filter (fun ij => ij.1 < ij.2) := by
    ext ij
    simp only [A,U,Finset.mem_filter,Finset.mem_offDiag,Finset.mem_univ,true_and]
    exact ⟨And.right,fun h => ⟨h.ne,h⟩⟩
  have hprod : (∏ ij ∈ A, F ij) = ∏ i : Fin k, ∏ j ∈ Finset.Ioi i, F (i,j) := by
    rw [hA,Finset.prod_filter,← Finset.univ_product_univ,Finset.prod_product]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  have hh := Finset.prod_filter_mul_prod_filter_not U (fun ij => ij.1 < ij.2) F
  change (∏ ij ∈ A, F ij)*(∏ ij ∈ B, F ij) = _ at hh
  rw [hswap,hprod,← pow_two] at hh
  exact hh.symm

/-- For k+1 consecutive indices, the product of all ordered squared gaps
is (1! 2! ... k!)^4. -/
theorem ordered_gap_product (k : ℕ) :
    (∏ ij ∈ (Finset.univ : Finset (Fin (k+1))).offDiag,
      ((ij.1.val : ℤ)-(ij.2.val : ℤ))^2) = (k.superFactorial : ℤ)^4 := by
  rw [symmetric_offDiag_product (k+1) (fun ij => ((ij.1.val : ℤ)-(ij.2.val : ℤ))^2)
    (by intro i j; ring)]
  have he : (∏ i : Fin (k+1), ∏ j ∈ Finset.Ioi i, ((i.val : ℤ)-(j.val : ℤ))^2) =
      (k.superFactorial : ℤ)^2 := by
    have hsq (i j : Fin (k+1)) : ((i.val : ℤ)-(j.val : ℤ))^2 = ((j.val : ℤ)-(i.val : ℤ))^2 := by ring
    calc
      _ = ∏ i : Fin (k+1), ∏ j ∈ Finset.Ioi i,
          ((j.val : ℤ)-(i.val : ℤ))^2 := by
        apply Finset.prod_congr rfl
        intro i _
        exact Finset.prod_congr rfl (fun j _ => hsq i j)
      _ = (∏ i : Fin (k+1), ∏ j ∈ Finset.Ioi i,
          ((j.val : ℤ)-(i.val : ℤ)))^2 := by simp only [Finset.prod_pow]
      _ = _ := by
        rw [← Matrix.det_vandermonde (fun i : Fin (k+1) => (i.val : ℤ)),
          Matrix.det_vandermonde_id_eq_superFactorial]
  rw [he]
  ring

lemma offDiag_fin_card (k : ℕ) :
    ((Finset.univ : Finset (Fin (k+1))).offDiag).card = k*(k+1) := by
  rw [Finset.offDiag_card,Finset.card_univ,Fintype.card_fin]
  calc
    _ = (k*(k+1)+(k+1))-(k+1) := by congr 1; ring
    _ = _ := Nat.add_sub_cancel _ _

/-- A path with squared jumps <=C has ordered discriminant norm at most
C^(k(k+1))*(k.superFactorial)^4 on its first k+1 vertices. -/
theorem path_discriminant_bound (x : ℕ → GaussianInt) (C : ℤ)
    (hs : ∀ n, (x (n+1)-x n).norm ≤ C) (k : ℕ) :
    (discriminant (fun i : Fin (k+1) => x i.val)).norm ≤
      C^(k*(k+1))*(k.superFactorial : ℤ)^4 := by
  rw [norm_discriminant]
  calc
    _ ≤ ∏ ij ∈ (Finset.univ : Finset (Fin (k+1))).offDiag,
        C*((ij.1.val : ℤ)-(ij.2.val : ℤ))^2 := by
      apply Finset.prod_le_prod (fun _ _ => GaussianInt.norm_nonneg _)
      exact fun ij _ => norm_displacement_le x C hs ij.1.val ij.2.val
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,offDiag_fin_card,ordered_gap_product]

/-- Collision exponents for any coprime family fit in this factorial budget.
The jump bound C remains present; this does not force C to be unbounded. -/
theorem path_collision_factorial_bound {J : Type*}
    (x : ℕ → GaussianInt) (hx : Function.Injective x) (C : ℤ)
    (hs : ∀ n, (x (n+1)-x n).norm ≤ C) (k : ℕ)
    (g : J → GaussianInt) (S : Finset J)
    (hc : (S : Set J).Pairwise (fun i j => IsCoprime (g i) (g j))) :
    (∏ j ∈ S, (g j).norm^(collisionCount (fun i : Fin (k+1) => x i.val) (g j))) ≤
      C^(k*(k+1))*(k.superFactorial : ℤ)^4 := by
  have hh := collision_norm_product_le (fun i : Fin (k+1) => x i.val)
    (hx.comp Fin.val_injective) g S hc
  have hb := path_discriminant_bound x C hs k
  rw [norm_discriminant] at hb
  exact hh.trans hb

lemma superFactorial_pos (k : ℕ) : 0 < k.superFactorial := by
  induction k with
  | zero => simp [Nat.superFactorial]
  | succ k ih => exact Nat.mul_pos (Nat.factorial_pos _) ih

lemma jump_bound_pos (x : ℕ → GaussianInt) (hx : Function.Injective x) (C : ℤ)
    (hs : ∀ n, (x (n+1)-x n).norm ≤ C) : 0 < C := by
  have hne : x 1-x 0 ≠ 0 := sub_ne_zero.mpr (fun he => by
    have := hx he
    omega)
  exact (GaussianInt.norm_pos.mpr hne).trans_le (hs 0)

/-- The logarithmic factorial budget retains the jump-bound term explicitly. -/
theorem path_collision_log_factorial_bound {J : Type*}
    (x : ℕ → GaussianInt) (hx : Function.Injective x) (C : ℤ)
    (hs : ∀ n, (x (n+1)-x n).norm ≤ C) (k : ℕ)
    (g : J → GaussianInt) (S : Finset J) (hg : ∀ j ∈ S, g j ≠ 0)
    (hc : (S : Set J).Pairwise (fun i j => IsCoprime (g i) (g j))) :
    (∑ j ∈ S, (collisionCount (fun i : Fin (k+1) => x i.val) (g j) : ℝ)*
      Real.log ((g j).norm : ℝ)) ≤
      (k : ℝ)*((k : ℝ)+1)*Real.log (C : ℝ)+
        4*Real.log (k.superFactorial : ℝ) := by
  have hC : (0 : ℝ) < C := by exact_mod_cast jump_bound_pos x hx C hs
  have hF : (0 : ℝ) < k.superFactorial := by exact_mod_cast superFactorial_pos k
  have hgp (j) (hj : j ∈ S) : (0 : ℝ) < (g j).norm := by
    exact_mod_cast GaussianInt.norm_pos.mpr (hg j hj)
  have hb : (∏ j ∈ S, ((g j).norm : ℝ)^
      (collisionCount (fun i : Fin (k+1) => x i.val) (g j))) ≤
      (C : ℝ)^(k*(k+1))*(k.superFactorial : ℝ)^4 := by
    exact_mod_cast path_collision_factorial_bound x hx C hs k g S hc
  have hh := Real.log_le_log (Finset.prod_pos (fun j hj =>
    pow_pos (hgp j hj) _)) hb
  rw [Real.log_prod (fun j hj => (pow_pos (hgp j hj) _).ne'),
    Real.log_mul (pow_pos hC _).ne' (pow_pos hF _).ne'] at hh
  simpa only [Real.log_pow,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    using hh

#print axioms path_collision_log_factorial_bound
#print axioms ordered_gap_product
#print axioms path_discriminant_bound
#print axioms path_collision_factorial_bound
end
end Erdos952Investigation.GaussianPathDiscriminantBound
