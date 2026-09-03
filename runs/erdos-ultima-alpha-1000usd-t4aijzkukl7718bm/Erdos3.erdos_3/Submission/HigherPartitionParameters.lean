import Submission.SimultaneousPolynomialRecurrence

/-! Recursive quantitative costs for an almost-complete higher-degree flat
progression partition. Each degree step splits both error budgets in half. -/
namespace Erdos3HigherPartitionParameters
open Erdos3SimultaneousPolynomialRecurrence
open scoped Classical
set_option maxHeartbeats 2000000

def higherPartitionThreshold : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0,_,L,s => L*2^s
  | k+1,m,L,s =>
      let M := higherPartitionThreshold k m L (s+1)
      let t := s+1+(k+1)*Nat.clog 2 M
      let B := 2^(simultaneousPowerConstant (k+1) m*(t+1))
      B*M*2^(s+1)

def higherCoarseLength (k m L s : ℕ) : ℕ := higherPartitionThreshold k m L (s+1)
def higherTopAccuracy (k m L s : ℕ) : ℕ := s+1+(k+1)*Nat.clog 2 (higherCoarseLength k m L s)
def higherTopStride (k m L s : ℕ) : ℕ :=
  2^(simultaneousPowerConstant (k+1) m*(higherTopAccuracy k m L s+1))

def higherPartitionStride : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0,_,_,_ => 1
  | k+1,m,L,s => higherPartitionStride k m L (s+1)*higherTopStride k m L s

lemma higherPartitionThreshold_succ (k m L s : ℕ) :
    higherPartitionThreshold (k+1) m L s =
      higherTopStride k m L s*higherCoarseLength k m L s*2^(s+1) := rfl

lemma higherPartitionThreshold_pos (k m L s : ℕ) (hL : 0 < L) :
    0 < higherPartitionThreshold k m L s := by
  induction k generalizing s with
  | zero => exact Nat.mul_pos hL (Nat.two_pow_pos _)
  | succ k ih =>
    rw [higherPartitionThreshold_succ]
    exact Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) (ih (s+1))) (Nat.two_pow_pos _)

lemma higherCoarseLength_pos (k m L s : ℕ) (hL : 0 < L) :
    0 < higherCoarseLength k m L s := higherPartitionThreshold_pos k m L (s+1) hL

lemma higherTopStride_pos (k m L s : ℕ) : 0 < higherTopStride k m L s := Nat.two_pow_pos _

lemma higherPartitionStride_pos (k m L s : ℕ) : 0 < higherPartitionStride k m L s := by
  induction k generalizing s with
  | zero => exact Nat.zero_lt_one
  | succ k ih => exact Nat.mul_pos (ih (s+1)) (higherTopStride_pos k m L s)

lemma top_accuracy_error (k M s : ℕ) :
    (M : ℝ)^(k+1)*(1/2 : ℝ)^(s+1+(k+1)*Nat.clog 2 M) ≤ (1/2 : ℝ)^(s+1) := by
  have hM : (M : ℝ) ≤ (2 : ℝ)^(Nat.clog 2 M) := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) M
  calc
    _ ≤ ((2 : ℝ)^(Nat.clog 2 M))^(k+1)*(1/2 : ℝ)^(s+1+(k+1)*Nat.clog 2 M) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg M) hM (k+1)) (by positivity)
    _ = _ := by
      rw [pow_add (1/2 : ℝ) (s+1) ((k+1)*Nat.clog 2 M),
        Nat.mul_comm (k+1) (Nat.clog 2 M),pow_mul (1/2 : ℝ) (Nat.clog 2 M) (k+1)]
      simp only [div_pow,one_pow]
      field_simp

lemma block_loss_dyadic {d B M N s : ℕ} (hN0 : 0 < N) (hdB : d ≤ B)
    (hN : B*M*2^s ≤ N) : (d : ℝ)*(M : ℝ)/(N : ℝ) ≤ (1/2 : ℝ)^s := by
  rw [div_pow,one_pow]
  apply (div_le_div_iff₀ (Nat.cast_pos.mpr hN0) (pow_pos (by norm_num : (0 : ℝ) < 2) s)).mpr
  have hh : d*M*2^s ≤ N := (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right M hdB)).trans hN
  simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,one_mul] using
    (show ((d*M*2^s : ℕ) : ℝ) ≤ N by exact_mod_cast hh)

lemma dyadic_halves (s : ℕ) : (1/2 : ℝ)^(s+1)+(1/2 : ℝ)^(s+1) = (1/2 : ℝ)^s := by
  rw [pow_succ]
  ring

#print axioms top_accuracy_error
#print axioms block_loss_dyadic
end Erdos3HigherPartitionParameters
