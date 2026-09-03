import FormalConjecturesUtil

/-! Three rational linear fifth powers cannot absorb the two specified weights.
This is an algebraic obstruction for a particular construction only. -/
namespace Erdos322Research.QuinticThreeLinearAbsorption
set_option maxHeartbeats 0

private theorem no_fifth_six (x : ℚ) : x^5 ≠ 6 := by
  intro hx
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hx0 : x ≠ 0 := by intro hz; simp [hz] at hx
  have h3 : padicValRat 3 (3 : ℚ) = 1 := padicValRat.self (by decide)
  have h2 : padicValRat 3 (2 : ℚ) = 0 := by
    change padicValRat 3 (↑(2 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2)]
    rfl
  have h6 : padicValRat 3 (6 : ℚ) = 1 := by
    rw [show (6 : ℚ) = 2*3 by norm_num,
      padicValRat.mul (by norm_num : (2 : ℚ) ≠ 0) (by norm_num : (3 : ℚ) ≠ 0), h2, h3]
    norm_num
  have h := congrArg (padicValRat 3) hx
  rw [padicValRat.pow hx0, h6] at h
  omega

private theorem no_fifth_eight (x : ℚ) : x^5 ≠ 8 := by
  intro hx
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hx0 : x ≠ 0 := by intro hz; simp [hz] at hx
  have h2 : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by decide)
  have h8 : padicValRat 2 (8 : ℚ) = 3 := by
    rw [show (8 : ℚ) = 2^3 by norm_num,
      padicValRat.pow (by norm_num : (2 : ℚ) ≠ 0), h2]
    norm_num
  have h := congrArg (padicValRat 2) hx
  rw [padicValRat.pow hx0, h8] at h
  omega

private theorem zero_first_impossible (u v x y z : ℚ)
    (h0 : u^5+v^5=6) (h1 : u^4*y+v^4*z=0)
    (h2 : u^3*y^2+v^3*z^2=0) (h5 : x^5+y^5+z^5=8) : False := by
  have hu : u ≠ 0 := by intro hz; rw [hz] at h0; norm_num at h0; exact no_fifth_six v h0
  have hv : v ≠ 0 := by intro hz; rw [hz] at h0; norm_num at h0; exact no_fifth_six u h0
  have hy : y = 0 := by
    by_contra hy
    have hp : (u^3*y)*(v*y-u*z) = 0 := by linear_combination v*h2-z*h1
    have hd : v*y-u*z = 0 :=
      (mul_eq_zero.mp hp).resolve_left (mul_ne_zero (pow_ne_zero 3 hu) hy)
    have hz : 6*y = 0 := by linear_combination u*h1-y*h0+v^4*hd
    exact hy (by linarith)
  have hz : z = 0 := by
    rw [hy] at h1
    norm_num at h1
    exact h1.resolve_left hv
  rw [hy, hz] at h5
  norm_num at h5
  exact no_fifth_eight x h5

private theorem axis_moments_impossible (u v : Fin 3 → ℚ)
    (h0 : ∑ i, (u i)^5 = 6)
    (h1 : ∑ i, (u i)^4*v i = 0)
    (h2 : ∑ i, (u i)^3*(v i)^2 = 0)
    (h5 : ∑ i, (v i)^5 = 8)
    (hp : u 0*u 1*u 2 = 0) : False := by
  simp only [Fin.sum_univ_three] at h0 h1 h2 h5
  rcases mul_eq_zero.mp hp with h01 | h2z
  · rcases mul_eq_zero.mp h01 with h0z | h1z
    · rw [h0z] at h0 h1 h2
      norm_num at h0 h1 h2
      exact zero_first_impossible (u 1) (u 2) (v 0) (v 1) (v 2) h0 h1 h2 h5
    · rw [h1z] at h0 h1 h2
      norm_num at h0 h1 h2
      apply zero_first_impossible (u 0) (u 2) (v 1) (v 0) (v 2) h0 h1 h2
      linear_combination h5
  · rw [h2z] at h0 h1 h2
    norm_num at h0 h1 h2
    apply zero_first_impossible (u 0) (u 1) (v 2) (v 0) (v 1) h0 h1 h2
    linear_combination h5

/-- The six normalized coefficient equations for the all-even quadratic case
are inconsistent over the rationals. -/
theorem coefficients_impossible (a c : Fin 3 → ℚ)
    (h0 : ∑ i, (c i)^5 = 6)
    (h1 : ∑ i, a i*(c i)^4 = -12)
    (h2 : ∑ i, (a i)^2*(c i)^3 = 24)
    (h3 : ∑ i, (a i)^3*(c i)^2 = -48)
    (h4 : ∑ i, (a i)^4*c i = 96)
    (h5 : ∑ i, (a i)^5 = 64) : False := by
  simp only [Fin.sum_univ_three] at h0 h1 h2 h3 h4 h5
  have hp : c 0*c 1*c 2 = 0 := by
    linear_combination
      -(a 0*a 1*a 2)/64*h0 +
      (a 0*a 1*c 2+a 0*c 1*a 2+c 0*a 1*a 2)/64*h1 +
      (a 0*a 1*a 2-4*(a 0*c 1*c 2+c 0*a 1*c 2+c 0*c 1*a 2))/256*h2 +
      (4*c 0*c 1*c 2-(a 0*a 1*c 2+a 0*c 1*a 2+c 0*a 1*a 2))/256*h3 +
      (a 0*c 1*c 2+c 0*a 1*c 2+c 0*c 1*a 2)/256*h4 -
      (c 0*c 1*c 2)/256*h5
  let v : Fin 3 → ℚ := fun i => c i+a i/2
  have hm1 : ∑ i, (c i)^4*v i = 0 := by
    simp only [Fin.sum_univ_three, v]
    linear_combination h0+h1/2
  have hm2 : ∑ i, (c i)^3*(v i)^2 = 0 := by
    simp only [Fin.sum_univ_three, v]
    linear_combination h0+h1+h2/4
  have hm5 : ∑ i, (v i)^5 = 8 := by
    simp only [Fin.sum_univ_three, v]
    linear_combination h0+5*h1/2+5*h2/2+5*h3/4+5*h4/16+h5/32
  exact axis_moments_impossible c v (by simpa only [Fin.sum_univ_three] using h0)
    hm1 hm2 hm5 hp

end Erdos322Research.QuinticThreeLinearAbsorption
