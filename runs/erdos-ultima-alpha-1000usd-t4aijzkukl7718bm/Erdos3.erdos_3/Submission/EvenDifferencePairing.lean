import Submission.HigherPhaseDifferences

/-! The odd-order finite-difference relation is a paired equation. In an
arithmetic progression of even length, its coefficients occur in opposite
pairs. This identifies the algebraic relation behind even polynomial models. -/
namespace Erdos3EvenDifferencePairing
open Finset Erdos3HigherPhaseDifferences
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G]

def alternatingBinomial (n i : ℕ) : ℤ := (-1)^i*(n.choose i : ℤ)

lemma sign_reflection {n i : ℕ} (hn : Odd n) (hi : i ≤ n) :
    (-1 : ℤ)^(n-i) = -(-1 : ℤ)^i := by
  have hp : (-1 : ℤ)^(n-i)*(-1 : ℤ)^i = -1 := by
    rw [← pow_add,Nat.sub_add_cancel hi,hn.neg_one_pow]
  have hs : (-1 : ℤ)^i*(-1 : ℤ)^i = 1 := by
    rw [← pow_add]
    exact (show Even (i+i) from ⟨i,rfl⟩).neg_one_pow
  calc
    _ = ((-1 : ℤ)^(n-i)*(-1 : ℤ)^i)*(-1 : ℤ)^i := by rw [mul_assoc,hs,mul_one]
    _ = _ := by rw [hp]; ring

lemma alternatingBinomial_reflection {n i : ℕ} (hn : Odd n) (hi : i ≤ n) :
    alternatingBinomial n (n-i) = -alternatingBinomial n i := by
  unfold alternatingBinomial
  rw [sign_reflection hn hi,Nat.choose_symm hi]
  ring

lemma odd_difference_sum (q : ℕ → G) {n : ℕ} (hn : Odd n) :
    diffIter n q 0 = -(∑ i ∈ range (n+1), alternatingBinomial n i • q i) := by
  rw [diffIter,fwdDiff_iter_eq_sum_shift]
  simp only [nsmul_eq_mul,mul_one,zero_add,Nat.cast_id,← sum_neg_distrib]
  apply sum_congr rfl
  intro i hi
  rw [sign_reflection hn (by simpa only [mem_range] using (Nat.le_of_lt_succ (mem_range.mp hi)))]
  simp only [alternatingBinomial,neg_mul,neg_smul]

lemma antisymmetric_sum_pair (m : ℕ) (c : ℕ → ℤ) (q : ℕ → G)
    (hc : ∀ i ≤ 2*m+1, c (2*m+1-i) = -c i) :
    (∑ i ∈ range (2*m+2), c i • q i) =
      ∑ i ∈ range (m+1), c i • (q i-q (2*m+1-i)) := by
  rw [show 2*m+2 = (m+1)+(m+1) by omega,sum_range_add]
  have hr : (∑ j ∈ range (m+1), c (m+1+j) • q (m+1+j)) =
      ∑ i ∈ range (m+1), -(c i • q (2*m+1-i)) := by
    rw [← sum_range_reflect (fun j ↦ c (m+1+j) • q (m+1+j)) (m+1)]
    apply sum_congr rfl
    intro i hi
    have hi' : i ≤ m := Nat.le_of_lt_succ (mem_range.mp hi)
    have he : m+1+(m+1-1-i) = 2*m+1-i := by omega
    rw [he,hc i (by omega),neg_smul]
  rw [hr,← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [smul_sub,sub_eq_add_neg]

/-- Splitting an odd finite difference at its midpoint pairs the first and
last values, the second and penultimate values, and so on. -/
theorem even_difference_paired (m : ℕ) (q : ℕ → G)
    (hq : diffIter (2*m+1) q 0 = 0) :
    (∑ i ∈ range (m+1), alternatingBinomial (2*m+1) i • (q i-q (2*m+1-i))) = 0 := by
  have hn : Odd (2*m+1) := ⟨m,by omega⟩
  have he := odd_difference_sum q hn
  rw [hq,eq_comm,neg_eq_zero] at he
  rw [← antisymmetric_sum_pair m (alternatingBinomial (2*m+1)) q
    (fun i hi ↦ alternatingBinomial_reflection hn hi)]
  exact he

/-- Solves the finite-difference relation for the final value. -/
theorem even_difference_last (m : ℕ) (q : ℕ → G)
    (hq : diffIter (2*m+1) q 0 = 0) :
    q (2*m+1) = q 0+
      (∑ i ∈ range m, alternatingBinomial (2*m+1) (i+1) • q (i+1))-
      (∑ i ∈ range m, alternatingBinomial (2*m+1) (i+1) • q (2*m-i)) := by
  have he := even_difference_paired m q hq
  rw [sum_range_succ'] at he
  simp only [alternatingBinomial,Nat.choose_zero_right,pow_zero,Nat.cast_one,mul_one,
    one_smul,Nat.sub_zero] at he
  have hi (i : ℕ) : 2*m+1-(i+1) = 2*m-i := by omega
  simp only [hi,smul_sub,sum_sub_distrib] at he
  let L : G := ∑ i ∈ range m, alternatingBinomial (2*m+1) (i+1) • q (i+1)
  let R : G := ∑ i ∈ range m, alternatingBinomial (2*m+1) (i+1) • q (2*m-i)
  have hh : L-R+(q 0-q (2*m+1)) = 0 := by
    simpa only [L,R,alternatingBinomial] using he
  change q (2*m+1) = q 0+L-R
  apply eq_of_sub_eq_zero
  calc
    _ = -(L-R+(q 0-q (2*m+1))) := by abel
    _ = 0 := by rw [hh,neg_zero]

theorem even_difference_zero_iff_last (m : ℕ) (q : ℕ → G) :
    diffIter (2*m+1) q 0 = 0 ↔
      q (2*m+1) = q 0+
        (∑ i ∈ range m, alternatingBinomial (2*m+1) (i+1) • q (i+1))-
        (∑ i ∈ range m, alternatingBinomial (2*m+1) (i+1) • q (2*m-i)) := by
  constructor
  · exact even_difference_last m q
  · intro hlast
    have hn : Odd (2*m+1) := ⟨m,by omega⟩
    rw [odd_difference_sum q hn,neg_eq_zero,
      antisymmetric_sum_pair m (alternatingBinomial (2*m+1)) q
        (fun i hi ↦ alternatingBinomial_reflection hn hi),sum_range_succ']
    have hi (i : ℕ) : 2*m+1-(i+1) = 2*m-i := by omega
    simp only [hi,smul_sub,sum_sub_distrib,Nat.sub_zero,
      show alternatingBinomial (2*m+1) 0 = 1 by simp [alternatingBinomial],one_smul]
    rw [hlast]
    abel

#print axioms even_difference_paired
#print axioms even_difference_last
end Erdos3EvenDifferencePairing
