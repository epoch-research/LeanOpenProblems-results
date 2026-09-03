import FormalConjecturesUtil

/-!
# A height obstruction to reversing an adjacent pair

A rational rescaling of each endpoint of `(n,n+1)` can give the reversed
adjacent pair `(m+1,m)` only if at least one rescaling numerator or denominator
has square-root size. This concerns exact endpoint transport, not just equality
of largest prime factors. It is not a disproof of Erdős 371.
-/

namespace Erdos371RationalReversalHeight

/-- Cross-multiplication gives a positive integer determinant. -/
lemma reverse_determinant {n m a b c d : ℕ}
    (hb : 0 < b) (hd : 0 < d)
    (hleft : a*n = b*(m+1)) (hright : c*(n+1) = d*m) :
    b*c < a*d ∧ (a*d)*n = (b*c)*n + b*(c+d) := by
  have he : (a*d)*n = (b*c)*n + b*(c+d) := by
    calc
      (a*d)*n = d*(a*n) := by ring
      _ = d*(b*(m+1)) := by rw [hleft]
      _ = b*(d*m) + b*d := by ring
      _ = b*(c*(n+1)) + b*d := by rw [← hright]
      _ = (b*c)*n + b*(c+d) := by ring
  refine ⟨?_,he⟩
  by_contra h
  have hle : a*d ≤ b*c := by omega
  have hh := Nat.mul_le_mul_right n hle
  have hp : 0 < b*(c+d) := Nat.mul_pos hb (by omega)
  omega

/-- The determinant is a positive integer, so it is at least one. -/
theorem reverse_height_barrier {n m a b c d : ℕ}
    (hb : 0 < b) (hd : 0 < d)
    (hleft : a*n = b*(m+1)) (hright : c*(n+1) = d*m) :
    n ≤ b*(c+d) := by
  obtain ⟨hlt,he⟩ := reverse_determinant hb hd hleft hright
  have hle : b*c+1 ≤ a*d := by omega
  have hh := Nat.mul_le_mul_right n hle
  nlinarith

/-- Four rational-rescaling components bounded by `K` cannot reverse an
adjacent pair starting beyond `2*K^2`. Only three component bounds are needed
for this direction of the estimate. -/
theorem reverse_height_bound {n m a b c d K : ℕ}
    (hb : 0 < b) (hd : 0 < d)
    (hbK : b ≤ K) (hcK : c ≤ K) (hdK : d ≤ K)
    (hleft : a*n = b*(m+1)) (hright : c*(n+1) = d*m) :
    n ≤ 2*K^2 := by
  apply (reverse_height_barrier hb hd hleft hright).trans
  have hsum : c+d ≤ K+K := Nat.add_le_add hcK hdK
  have hh := Nat.mul_le_mul hbK hsum
  nlinarith

theorem no_small_rational_reversal {n K : ℕ} (hlarge : 2*K^2 < n) :
    ¬ ∃ m a b c d : ℕ, 0 < b ∧ 0 < d ∧
      a ≤ K ∧ b ≤ K ∧ c ≤ K ∧ d ≤ K ∧
      a*n = b*(m+1) ∧ c*(n+1) = d*m := by
  rintro ⟨m,a,b,c,d,hb,hd,_,hbK,hcK,hdK,hl,hr⟩
  exact (not_le_of_gt hlarge) (reverse_height_bound hb hd hbK hcK hdK hl hr)

/-- A convenient elementary subpower regime. -/
theorem no_cube_root_reversal {n K : ℕ} (hn : 9 ≤ n) (hK : K^3 ≤ n) :
    ¬ ∃ m a b c d : ℕ, 0 < b ∧ 0 < d ∧
      a ≤ K ∧ b ≤ K ∧ c ≤ K ∧ d ≤ K ∧
      a*n = b*(m+1) ∧ c*(n+1) = d*m := by
  apply no_small_rational_reversal
  by_cases hk : K ≤ 2
  · have hh : K^2 ≤ 4 := by nlinarith
    nlinarith
  · have hkpos : 0 < K := by omega
    have hpos : 0 < K^2 := by positivity
    have hh : 3*K^2 ≤ K^3 := by nlinarith
    omega

/-- An explicit family showing that square-root size really can suffice.
Here `K=t+3`; the input is `(t+3)*(2*t+3)`, asymptotic to `2*K^2`. -/
theorem reversal_family (t : ℕ) :
    let K := t+3
    let n := (t+3)*(2*t+3)
    let m := (t+1)*(2*t+5)
    let a := t+2
    let b := t+3
    let c := t+1
    let d := t+2
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
    a ≤ K ∧ b ≤ K ∧ c ≤ K ∧ d ≤ K ∧
    a*n = b*(m+1) ∧ c*(n+1) = d*m ∧
    n = 2*K^2-3*K := by
  dsimp only
  refine ⟨by omega,by omega,by omega,by omega,
    by omega,by omega,by omega,by omega,?_,?_,?_⟩
  · ring
  · ring
  · have he : (t+3)*(2*t+3)+3*(t+3) = 2*(t+3)^2 := by ring
    omega

end Erdos371RationalReversalHeight

#print axioms Erdos371RationalReversalHeight.reverse_height_bound
#print axioms Erdos371RationalReversalHeight.no_cube_root_reversal
#print axioms Erdos371RationalReversalHeight.reversal_family
