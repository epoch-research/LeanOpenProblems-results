import FormalConjecturesUtil
import Submission.ThetaCappedPolynomial

/-! A small fixed-power loss does not rescue the auxiliary capped
unbalanced theta bound. This is not a negation of Erdos 713. -/
open Finset
namespace Erdos713ThetaPowerLoss
open Erdos713ThetaGram Erdos713ThetaCappedPolynomial
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 10000

lemma choose_scale (K C p : ℕ) :
    ∃ N : ℕ, 0 < N ∧ C*(K*(N+1)^p) < N^(p+1) := by
  let N := C*K*2^p+1
  have hN : 0 < N := by dsimp [N]; omega
  have h1 : N+1 ≤ 2*N := by omega
  have hBig : C*K*2^p < N := by dsimp [N]; omega
  refine ⟨N,hN,?_⟩
  calc
    C*(K*(N+1)^p) ≤ C*(K*(2*N)^p) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 p))
    _ = (C*K*2^p)*N^p := by rw [mul_pow]; ac_rfl
    _ < N*N^p := Nat.mul_lt_mul_of_pos_right hBig (Nat.pow_pos hN)
    _ = N^(p+1) := (pow_succ' N p).symm

lemma powered_gap {e N S n C p : ℕ} (hp : 0 < p) (hS : 0 < S)
    (he : N*S < e) (hn : C*n < N^p) : C*n*S^p < e^p := by
  calc
    _ < N^p*S^p := Nat.mul_lt_mul_of_pos_right hn (Nat.pow_pos hS)
    _ = (N*S)^p := (mul_pow N S p).symm
    _ < e^p := Nat.pow_lt_pow_left he (by omega)

lemma exists_power_counterexample (C : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop),
      ¬ HasTheta R ∧ 0 < Nat.card A ∧ Nat.card A ≤ (Nat.card B)^2 ∧
      (∀ b, Nat.card {a // R a b} ≤ Nat.card B) ∧
      C*(Nat.card A+Nat.card B)*
        (Nat.card A+Nat.card B*(Nat.sqrt (Nat.card A)+1))^8894 <
        (Nat.card {p : A × B // R p.1 p.2})^8894 := by
  obtain ⟨N,hN,hBig⟩ := choose_scale sizeConstant C 8893
  obtain ⟨A,B,instA,instB,R,hFree,hm,hSize,hCap,hOrder,hGap⟩ := exists_capped_examples N
  refine ⟨A,B,instA,instB,R,hFree,hm,hSize,hCap,?_⟩
  apply powered_gap (by decide) (by omega) hGap
  exact (Nat.mul_le_mul_left C hOrder).trans_lt hBig

lemma rpow_root_power (n : ℝ) (hn : 0 ≤ n) :
    (n^((1 : ℝ)/8894))^8894 = n := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hn]
  norm_num

lemma no_capped_power_loss_bound :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
      ¬ HasTheta R → Nat.card A ≤ (Nat.card B)^2 →
      (∀ b, Nat.card {a // R a b} ≤ Nat.card B) →
        (Nat.card {p : A × B // R p.1 p.2} : ℝ) ≤
          C*((Nat.card A : ℝ)+(Nat.card B : ℝ))^((1 : ℝ)/8894)*
            ((Nat.card A : ℝ)+(Nat.card B : ℝ)*Real.sqrt (Nat.card A)) := by
  rintro ⟨C,hC,hBound⟩
  obtain ⟨L,hL⟩ := exists_nat_gt (C^8894)
  obtain ⟨A,B,instA,instB,R,hFree,hm,hSize,hCap,hGap⟩ := exists_power_counterexample L
  let m : ℝ := Nat.card A
  let k : ℝ := Nat.card B
  let e : ℝ := Nat.card {p : A × B // R p.1 p.2}
  let S : ℝ := Nat.card A+Nat.card B*(Nat.sqrt (Nat.card A)+1)
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hs : Real.sqrt m ≤ (Nat.sqrt (Nat.card A) : ℝ)+1 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hh : Nat.card A ≤ (Nat.sqrt (Nat.card A)+1)^2 := by
      simpa only [Nat.succ_eq_add_one,pow_two] using (Nat.lt_succ_sqrt (Nat.card A)).le
    dsimp [m]
    exact_mod_cast hh
  have hS : m+k*Real.sqrt m ≤ S := by
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hs hk0)
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hu : e ≤ C*(m+k)^((1 : ℝ)/8894)*S := by
    exact (hBound A B R hFree hSize hCap).trans
      (mul_le_mul_of_nonneg_left hS (mul_nonneg hC.le (Real.rpow_nonneg (add_nonneg hm0 hk0) _)))
  have hPow := pow_le_pow_left₀ (show (0 : ℝ) ≤ e from Nat.cast_nonneg _) hu 8894
  rw [mul_pow,mul_pow,rpow_root_power (m+k) (add_nonneg hm0 hk0)] at hPow
  have hCmp : C^8894*(m+k)*S^8894 ≤ (L : ℝ)*(m+k)*S^8894 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL.le (add_nonneg hm0 hk0))
      (pow_nonneg hS0 _)
  have hGap' : (L : ℝ)*(m+k)*S^8894 < e^8894 := by
    dsimp [m,k,S,e]
    exact_mod_cast hGap
  exact (not_lt_of_ge (hPow.trans hCmp)) hGap'

#print axioms exists_power_counterexample
#print axioms no_capped_power_loss_bound
end Erdos713ThetaPowerLoss
