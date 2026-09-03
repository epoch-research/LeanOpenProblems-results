import Submission.HigherPartitionParameters

/-! Progression-partition costs parameterized by a simultaneous monomial
recurrence exponent. This separates the geometric induction from the choice
of recurrence theorem. -/
namespace Erdos3ParameterizedPartitionCosts
set_option maxHeartbeats 3000000

def flatThreshold (C : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0,L,s => L*2^s
  | k+1,L,s =>
      let M := flatThreshold C k L (s+1)
      let u := s+1+(k+1)*Nat.clog 2 M
      2^(C k*(u+1))*M*2^(s+1)

def coarseLength (C : ℕ → ℕ) (k L s : ℕ) := flatThreshold C k L (s+1)
def topAccuracy (C : ℕ → ℕ) (k L s : ℕ) := s+1+(k+1)*Nat.clog 2 (coarseLength C k L s)
def topStride (C : ℕ → ℕ) (k L s : ℕ) := 2^(C k*(topAccuracy C k L s+1))

def flatStride (C : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0,_,_ => 1
  | k+1,L,s => flatStride C k L (s+1)*topStride C k L s

lemma flatThreshold_succ (C : ℕ → ℕ) (k L s : ℕ) :
    flatThreshold C (k+1) L s = topStride C k L s*coarseLength C k L s*2^(s+1) := rfl

lemma flatThreshold_pos (C : ℕ → ℕ) (k L s : ℕ) (hL : 0 < L) :
    0 < flatThreshold C k L s := by
  induction k generalizing s with
  | zero => exact Nat.mul_pos hL (Nat.two_pow_pos _)
  | succ k ih => exact Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) (ih (s+1))) (Nat.two_pow_pos _)

lemma flatStride_le_threshold (C : ℕ → ℕ) (k L s : ℕ) (hL : 0 < L) :
    flatStride C k L s ≤ flatThreshold C k L s := by
  induction k generalizing s with
  | zero =>
    exact Nat.mul_pos hL (Nat.two_pow_pos _)
  | succ k ih =>
    rw [flatStride,flatThreshold_succ]
    calc
      _ ≤ coarseLength C k L s*topStride C k L s := Nat.mul_le_mul_right _ (ih (s+1))
      _ ≤ _ := by
        have hh := Nat.mul_le_mul_left (topStride C k L s*coarseLength C k L s)
          (Nat.one_le_two_pow (n := s+1))
        simpa only [mul_one,mul_comm] using hh

def flatExponent (C : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | k+1 => flatExponent C k*((k+1)*C k+1)+C k+1

/-- The complete threshold has an explicit logarithmic upper bound. -/
theorem flatThreshold_exponential_bound (C : ℕ → ℕ) (k L s : ℕ) :
    flatThreshold C k L s ≤ 2^(flatExponent C k*(s+k+1+Nat.clog 2 L)) := by
  induction k generalizing s with
  | zero =>
    calc
      _ ≤ 2^(Nat.clog 2 L)*2^s := Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) L)
      _ = 2^(Nat.clog 2 L+s) := (pow_add _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by simp only [flatExponent]; omega)
  | succ k ih =>
    let M := coarseLength C k L s
    let A := flatExponent C k
    let t := s+(k+1)+1+Nat.clog 2 L
    have hM : M ≤ 2^(A*t) := by
      simpa only [M,coarseLength,A,t,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (s+1)
    have hlog : Nat.clog 2 M ≤ A*t := Nat.clog_le_of_le_pow hM
    have hs2 : s+2 ≤ t := by dsimp only [t]; omega
    have hs1 : s+1 ≤ t := by omega
    have hu : C k*(topAccuracy C k L s+1) ≤ C k*(1+(k+1)*A)*t := by
      have hh := Nat.mul_le_mul_left (k+1) hlog
      change C k*(s+1+(k+1)*Nat.clog 2 M+1) ≤ _
      have ht : s+1+(k+1)*Nat.clog 2 M+1 ≤ (1+(k+1)*A)*t := by nlinarith only [hs2,hh]
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (C k) ht
    rw [flatThreshold_succ]
    calc
      _ ≤ 2^(C k*(1+(k+1)*A)*t)*2^(A*t)*2^t :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hu) hM)
          (Nat.pow_le_pow_right (by decide) hs1)
      _ = _ := by
        rw [← pow_add,← pow_add]
        congr 1
        change _ = (A*((k+1)*C k+1)+C k+1)*t
        ring

#print axioms flatThreshold_exponential_bound
end Erdos3ParameterizedPartitionCosts
