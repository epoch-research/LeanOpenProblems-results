import FormalConjecturesUtil
import Submission.FiniteOccupancy

/-! Uniform finite permutations give negatively correlated occupancy
indicators. All averages below are finite sums. -/
open Finset
open scoped BigOperators Classical
namespace Erdos713FinitePermutationOccupancy
variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
set_option maxHeartbeats 1500000

noncomputable def hit (S : Finset X) (x : X) (σ : Equiv.Perm X) : ℝ :=
  if σ x ∈ S then 1 else 0

omit [Fintype X] [Nonempty X] in
lemma hit_sq (S : Finset X) (x : X) (σ : Equiv.Perm X) :
    (hit S x σ)^2 = hit S x σ := by
  unfold hit
  split_ifs <;> norm_num

omit [Fintype X] [Nonempty X] in
lemma hit_nonneg (S : Finset X) (x : X) (σ : Equiv.Perm X) : 0 ≤ hit S x σ := by
  unfold hit
  split_ifs <;> norm_num

omit [Nonempty X] in
lemma sum_hit (S : Finset X) (σ : Equiv.Perm X) :
    (∑ x : X, hit S x σ) = (S.card : ℝ) := by
  unfold hit
  calc
    _ = ∑ z : X, if z ∈ S then (1 : ℝ) else 0 :=
      Fintype.sum_equiv σ _ _ (fun _ => rfl)
    _ = _ := by simp

omit [Nonempty X] in
lemma expect_hit_eq (S : Finset X) (x y : X) :
    (𝔼 σ : Equiv.Perm X, hit S x σ) = 𝔼 σ : Equiv.Perm X, hit S y σ := by
  apply Fintype.expect_equiv (Equiv.mulRight (Equiv.swap x y))
  intro σ
  simp [hit,Equiv.Perm.mul_apply]

lemma expect_hit (S : Finset X) (x : X) :
    (𝔼 σ : Equiv.Perm X, hit S x σ) = (S.card : ℝ)/Fintype.card X := by
  have hc : (0 : ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  have hsum : (Fintype.card X : ℝ)*(𝔼 σ : Equiv.Perm X, hit S x σ) = S.card := by
    calc
      _ = ∑ y : X, 𝔼 σ : Equiv.Perm X, hit S y σ := by
        simp_rw [← expect_hit_eq S x]
        simp
      _ = 𝔼 σ : Equiv.Perm X, ∑ y : X, hit S y σ := by rw [expect_sum_comm]
      _ = _ := by simp only [sum_hit,Fintype.expect_const]
  apply (eq_div_iff hc.ne').mpr
  simpa only [mul_comm] using hsum

omit [Nonempty X] in
lemma expect_pair_eq (S : Finset X) (x : X) {y z : X}
    (hy : y ≠ x) (hz : z ≠ x) :
    (𝔼 σ : Equiv.Perm X, hit S x σ*hit S y σ) =
      𝔼 σ : Equiv.Perm X, hit S x σ*hit S z σ := by
  apply Fintype.expect_equiv (Equiv.mulRight (Equiv.swap y z))
  intro σ
  simp [hit,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hy.symm hz.symm]

omit [Nonempty X] in
lemma sum_pair (S : Finset X) (x : X) (σ : Equiv.Perm X) :
    (∑ y ∈ (univ : Finset X).erase x, hit S x σ*hit S y σ) =
      ((S.card : ℝ)-1)*hit S x σ := by
  have hsum := sum_erase_add (s := (univ : Finset X))
    (f := fun y => hit S x σ*hit S y σ) (mem_univ x)
  have htotal : (∑ y : X, hit S x σ*hit S y σ) = (S.card : ℝ)*hit S x σ := by
    rw [← mul_sum,sum_hit,mul_comm]
  dsimp only at hsum
  rw [htotal,← pow_two,hit_sq] at hsum
  linarith only [hsum]

lemma pair_identity (S : Finset X) {x y : X} (hxy : x ≠ y) :
    ((Fintype.card X : ℝ)-1)*(𝔼 σ : Equiv.Perm X, hit S x σ*hit S y σ) =
      ((S.card : ℝ)-1)*((S.card : ℝ)/Fintype.card X) := by
  have hcard : (((univ : Finset X).erase x).card : ℝ) = (Fintype.card X : ℝ)-1 := by
    rw [card_erase_of_mem (mem_univ x),card_univ,Nat.cast_sub Fintype.card_pos]
    norm_num
  calc
    _ = ∑ z ∈ (univ : Finset X).erase x,
        𝔼 σ : Equiv.Perm X, hit S x σ*hit S z σ := by
      rw [← hcard]
      have he (z : X) (hz : z ∈ (univ : Finset X).erase x) :
          (𝔼 σ : Equiv.Perm X, hit S x σ*hit S z σ) =
            𝔼 σ : Equiv.Perm X, hit S x σ*hit S y σ :=
        expect_pair_eq S x (mem_erase.mp hz).1 hxy.symm
      simp_rw [sum_congr rfl he]
      simp
    _ = 𝔼 σ : Equiv.Perm X,
        ∑ z ∈ (univ : Finset X).erase x, hit S x σ*hit S z σ := by rw [expect_sum_comm]
    _ = _ := by simp_rw [sum_pair]; rw [← mul_expect,expect_hit]

lemma expect_pair_le (S : Finset X) {x y : X} (hxy : x ≠ y) :
    (𝔼 σ : Equiv.Perm X, hit S x σ*hit S y σ) ≤
      ((S.card : ℝ)/Fintype.card X)^2 := by
  have htwo : 2 ≤ Fintype.card X := Fintype.one_lt_card_iff.mpr ⟨x,y,hxy⟩
  have hn : (1 : ℝ) < Fintype.card X := by exact_mod_cast htwo
  have hs : (S.card : ℝ) ≤ Fintype.card X := by exact_mod_cast card_le_card (subset_univ S)
  have hS : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hId := pair_identity S hxy
  have he : (Fintype.card X : ℝ)*((S.card : ℝ)/Fintype.card X) = S.card :=
    mul_div_cancel₀ _ (ne_of_gt (lt_trans (by norm_num) hn))
  have hp : 0 ≤ (S.card : ℝ)/Fintype.card X := div_nonneg hS (by linarith)
  have hp1 : (S.card : ℝ)/Fintype.card X ≤ 1 := by
    apply (div_le_one (by linarith)).mpr
    exact hs
  have hineq : ((S.card : ℝ)/Fintype.card X)*((S.card : ℝ)/Fintype.card X) ≤
      (S.card : ℝ)/Fintype.card X := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp1 hp
  have hep := congrArg (fun z : ℝ => z*((S.card : ℝ)/Fintype.card X)) he
  nlinarith only [hId,hep,hineq,hn]

#print axioms expect_hit
#print axioms pair_identity
#print axioms expect_pair_le
end Erdos713FinitePermutationOccupancy
