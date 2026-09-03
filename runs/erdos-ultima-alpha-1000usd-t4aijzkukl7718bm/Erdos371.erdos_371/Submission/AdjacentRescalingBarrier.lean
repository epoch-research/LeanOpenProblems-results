import FormalConjecturesUtil

/-! A size barrier for swapping adjacent endpoints by two rational
rescalings. This does not disprove the largest-prime-factor conjecture. -/
namespace Erdos371

/-- If a*n=b*(m+1) and c*(n+1)=d*m, the positive determinant forces
n≤b*(c+d). In particular, uniformly small coefficients cannot swap a
large adjacent pair. No assertion about smooth coefficients of large
numerical size is made. -/
theorem reversed_adjacent_rescaling_bound (n m a b c d B : ℕ)
    (hb : 0<b) (hd : 0<d) (hbB : b≤B) (hcB : c≤B) (hdB : d≤B)
    (h₁ : a*n=b*(m+1)) (h₂ : c*(n+1)=d*m) : n≤2*B^2 := by
  have he : (a*d)*n=(b*c)*n+b*c+b*d := by
    calc
      _ = d*(a*n) := by ring
      _ = d*(b*(m+1)) := by rw [h₁]
      _ = b*(d*m)+b*d := by ring
      _ = b*(c*(n+1))+b*d := by rw [← h₂]
      _ = _ := by ring
  have hdet : b*c<a*d := by
    by_contra h
    have hm := Nat.mul_le_mul_right n (not_lt.mp h)
    have hp := Nat.mul_pos hb hd
    omega
  have hgap := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hdet)
  have hn : n≤b*c+b*d := by nlinarith
  have hbc := Nat.mul_le_mul hbB hcB
  have hbd := Nat.mul_le_mul hbB hdB
  nlinarith

/-- With all four positive coefficients bounded by B, both indices are
at most 2*B². The argument is symmetric in the two adjacent pairs. -/
theorem reversed_adjacent_rescaling_both_bounds (n m a b c d B : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d)
    (haB : a≤B) (hbB : b≤B) (hcB : c≤B) (hdB : d≤B)
    (h₁ : a*n=b*(m+1)) (h₂ : c*(n+1)=d*m) :
    n≤2*B^2 ∧ m≤2*B^2 := by
  exact ⟨reversed_adjacent_rescaling_bound n m a b c d B hb hd hbB hcB hdB h₁ h₂,
    reversed_adjacent_rescaling_bound m n d c b a B hc ha hcB hbB haB h₂.symm h₁.symm⟩

#print axioms reversed_adjacent_rescaling_bound
#print axioms reversed_adjacent_rescaling_both_bounds
end Erdos371
