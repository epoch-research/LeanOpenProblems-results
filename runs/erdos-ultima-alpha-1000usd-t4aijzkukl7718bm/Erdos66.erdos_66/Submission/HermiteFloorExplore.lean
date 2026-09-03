import FormalConjecturesUtil

/-! An exact rational-grid floor-sum identity for rotation discrepancy. -/
namespace Erdos66HermiteFloor
open scoped Classical
set_option maxHeartbeats 1600000

lemma sum_int_div_block (n : ℕ) (hn : 0 < n) (a : ℤ) :
    (∑ k ∈ Finset.range n, (a+(k : ℤ))/(n : ℤ)) = a := by
  let f : ℤ → ℤ := fun a ↦ ∑ k ∈ Finset.range n, (a+(k : ℤ))/(n : ℤ)
  have hnz : (0 : ℤ) < n := by exact_mod_cast hn
  have hstep (a : ℤ) : f (a+1)=f a+1 := by
    have h1 := Finset.sum_range_succ (fun k : ℕ ↦ (a+(k : ℤ))/(n : ℤ)) n
    have h2 := Finset.sum_range_succ' (fun k : ℕ ↦ (a+(k : ℤ))/(n : ℤ)) n
    have hfun : (∑ k ∈ Finset.range n, (a+((k+1 : ℕ) : ℤ))/(n : ℤ))=f (a+1) := by
      apply Finset.sum_congr rfl
      intro k hk
      push_cast
      congr 1
      ring
    rw [hfun] at h2
    have he : (a+(n : ℤ))/(n : ℤ)=a/(n : ℤ)+1 := by
      rw [Int.add_ediv_of_dvd_right (dvd_refl _),Int.ediv_self hnz.ne']
    change _ = f a + _ at h1
    rw [he] at h1
    norm_num only [Int.natCast_zero,add_zero] at h2
    omega
  have hzero : f 0=0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp only [zero_add]
    exact Int.ediv_eq_zero_of_lt (by omega) (by exact_mod_cast Finset.mem_range.mp hk)
  change f a=a
  induction a using Int.induction_on with
  | zero => exact hzero
  | succ a ih => rw [hstep,ih]
  | pred a ih =>
    have hh := hstep (-(a : ℤ)-1)
    have he : -(a : ℤ)-1+1=-(a : ℤ) := by ring
    rw [he,ih] at hh
    omega

/-- Hermite's identity for an equally spaced grid. -/
theorem sum_floor_grid (n : ℕ) (hn : 0 < n) (x : ℝ) :
    (∑ k ∈ Finset.range n, ⌊x+(k : ℝ)/n⌋) = ⌊(n : ℝ)*x⌋ := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he (k : ℕ) : ⌊x+(k : ℝ)/n⌋ = (⌊(n : ℝ)*x⌋+(k : ℤ))/(n : ℤ) := by
    rw [show x+(k : ℝ)/n=((n : ℝ)*x+k)/n by field_simp]
    rw [Int.floor_div_natCast,Int.floor_add_natCast]
  simp_rw [he]
  exact sum_int_div_block n hn _

end Erdos66HermiteFloor
