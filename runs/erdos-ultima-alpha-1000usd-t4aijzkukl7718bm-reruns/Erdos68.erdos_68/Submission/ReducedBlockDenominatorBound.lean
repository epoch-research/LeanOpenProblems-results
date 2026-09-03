import Submission.FactorialMinusOneLcmBound

/-!
Cancellation-aware lower bounds for reduced denominators of finite reciprocal
blocks. This is auxiliary arithmetic, not a settlement of Erdős 68.
-/

namespace ReducedBlockDenominatorBound

open Finset FactorialMinusOneLcmBound

lemma denominator_product_dvd_add (x y : ℚ) :
    x.den * y.den ∣ (x + y).den * (Nat.gcd x.den y.den)^2 := by
  have hx : x.den ∣ (x + y).den * y.den := by
    simpa using Rat.sub_den_dvd (x + y) y
  have hy : y.den ∣ (x + y).den * x.den := by
    simpa using Rat.sub_den_dvd (x + y) x
  have hx' : x.den ∣ Nat.gcd x.den y.den * (x + y).den :=
    dvd_gcd_mul_of_dvd_mul (by simpa [Nat.mul_comm] using hx)
  have hy' : y.den ∣ Nat.gcd x.den y.den * (x + y).den := by
    have hh : y.den ∣ Nat.gcd y.den x.den * (x + y).den :=
      dvd_gcd_mul_of_dvd_mul (by simpa [Nat.mul_comm] using hy)
    rw [Nat.gcd_comm y.den x.den] at hh
    exact hh
  have hl := Nat.mul_dvd_mul_left (Nat.gcd x.den y.den) (Nat.lcm_dvd hx' hy')
  rw [Nat.gcd_mul_lcm] at hl
  convert hl using 1
  ring

lemma sum_den_dvd_product (q : ℕ → ℚ) (n : ℕ) :
    (∑ i ∈ range n, q i).den ∣ ∏ i ∈ range n, (q i).den := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, prod_range_succ]
    exact (Rat.add_den_dvd _ _).trans (Nat.mul_dvd_mul_right ih _)

/-- Arbitrary cancellation in a finite rational sum costs at most the
square of the product of all pairwise denominator gcds. -/
theorem product_den_dvd_sum_den_mul_pairGcd_square (q : ℕ → ℚ) (n : ℕ) :
    (∏ i ∈ range n, (q i).den) ∣
      (∑ i ∈ range n, q i).den * (pairGcd (fun i => (q i).den) n)^2 := by
  induction n with
  | zero => simp [pairGcd]
  | succ n ih =>
    let B := (∑ i ∈ range n, q i).den
    let g := Nat.gcd B (q n).den
    let R := ∏ i ∈ range n, Nat.gcd (q n).den (q i).den
    have hg : g ∣ R := by
      apply (Nat.dvd_gcd (Nat.gcd_dvd_right B (q n).den)
        ((Nat.gcd_dvd_left B (q n).den).trans (sum_den_dvd_product q n))).trans
      exact gcd_prod_dvd (fun i => (q i).den) (q n).den n
    have hs : B * (q n).den ∣ (∑ i ∈ range (n+1), q i).den * R^2 := by
      have hh := denominator_product_dvd_add (∑ i ∈ range n, q i) (q n)
      have hh' := hh.trans (Nat.mul_dvd_mul_left
        ((∑ i ∈ range n, q i) + q n).den (pow_dvd_pow_of_dvd hg 2))
      simpa only [sum_range_succ, B, g] using hh'
    have h₁ := Nat.mul_dvd_mul_right ih (q n).den
    have h₂ := Nat.mul_dvd_mul_right hs ((pairGcd (fun i => (q i).den) n)^2)
    rw [prod_range_succ, pairGcd_succ]
    apply h₁.trans
    convert h₂ using 1 <;> dsimp [B, R] <;> ring

def reciprocalBlock (k n : ℕ) : ℚ :=
  ∑ i ∈ range n, 1 / (denom (k+i) : ℚ)

lemma reciprocal_den (k i : ℕ) (hk : 2 ≤ k) :
    (1 / (denom (k+i) : ℚ)).den = denom (k+i) := by
  rw [one_div]
  exact Rat.inv_natCast_den_of_pos (denom_pos _ (by omega))

/-- Unlike a common-multiple estimate, this bounds the actual reduced
denominator of the sum. -/
theorem block_reduced_denominator_bound (k n : ℕ) (hk : 2 ≤ k) :
    (denom k)^n ≤ (reciprocalBlock k n).den * (k+n)^(2*n^3) := by
  let a : ℕ → ℕ := fun i => denom (k+i)
  have hap : ∀ i < n, 0 < a i := by
    intro i hi
    exact denom_pos _ (by omega)
  have hd : (∏ i ∈ range n, a i) ∣
      (reciprocalBlock k n).den * (pairGcd a n)^2 := by
    simpa only [reciprocal_den k _ hk] using
      product_den_dvd_sum_den_mul_pairGcd_square (fun i => 1 / (denom (k+i) : ℚ)) n
  have hp := Nat.le_of_dvd
    (Nat.mul_pos (reciprocalBlock k n).pos (pow_pos (pairGcd_pos a n hap) 2)) hd
  have hg : (pairGcd a n)^2 ≤ (k+n)^(2*n^3) := by
    have hb := pairGcd_bound a n ((k+n)^n) (Nat.one_le_pow _ _ (by omega))
      (fun i hi j hj => pair_gcd_bound k n i j hk hi hj)
    have hh := Nat.pow_le_pow_left hb 2
    convert hh using 1
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  have hlo : (denom k)^n ≤ ∏ i ∈ range n, a i := by
    simpa using prod_le_prod' (s := range n) (f := fun _ => denom k) (g := a)
      (fun i _ => Nat.sub_le_sub_right (Nat.factorial_le (by omega : k ≤ k+i)) 1)
  exact hlo.trans (hp.trans (Nat.mul_le_mul_left _ hg))

lemma wide_factorial_bound (m : ℕ) (hm : 1 ≤ m) :
    m^(8*m^2) ≤ denom (8*m^2) := by
  have he := Nat.factorial_mul_pow_le_factorial (m := 4*m^2) (n := 4*m^2)
  have hf : 1 ≤ (4*m^2).factorial := Nat.factorial_pos _
  have hpow : (m^2)^(4*m^2) < (4*m^2+1)^(4*m^2) := by
    apply Nat.pow_lt_pow_left (by nlinarith) (by positivity)
  have hl : (4*m^2+1)^(4*m^2) ≤ (8*m^2).factorial := by
    have hh := Nat.mul_le_mul_right ((4*m^2+1)^(4*m^2)) hf
    rw [show 4*m^2+4*m^2 = 8*m^2 by ring] at he
    omega
  have hh : m^(8*m^2) < (8*m^2).factorial := by
    convert hpow.trans_le hl using 1
    rw [← pow_mul]
    congr 1
    ring
  exact Nat.le_sub_one_of_lt hh

/-- A growing block has a large reduced denominator even after all
cancellation in its reciprocal sum has taken place. -/
theorem growing_block_reduced_height (m : ℕ) (hm : 9 ≤ m) :
    m^(2*m^3) ≤ (reciprocalBlock (8*m^2) m).den := by
  have hb := block_reduced_denominator_bound (8*m^2) m (by nlinarith)
  have hlo : m^(8*m^3) ≤ (denom (8*m^2))^m := by
    have hh := Nat.pow_le_pow_left (wide_factorial_bound m (by omega)) m
    convert hh using 1
    rw [← pow_mul]
    congr 1
    ring
  have hbase : 8*m^2+m ≤ m^3 := by
    have h1 := Nat.mul_le_mul_right (m^2) hm
    have h2 : m ≤ m^2 := Nat.le_self_pow (by omega) m
    nlinarith
  have hhi : (8*m^2+m)^(2*m^3) ≤ m^(6*m^3) := by
    have hh := Nat.pow_le_pow_left hbase (2*m^3)
    convert hh using 1
    rw [← pow_mul]
    congr 1
    ring
  have hall : m^(8*m^3) ≤ (reciprocalBlock (8*m^2) m).den * m^(6*m^3) :=
    hlo.trans (hb.trans (Nat.mul_le_mul_left _ hhi))
  have he : m^(8*m^3) = m^(2*m^3) * m^(6*m^3) := by
    rw [← pow_add]
    congr 1
    ring
  rw [he] at hall
  exact Nat.le_of_mul_le_mul_right hall (by positivity)

def reciprocalPrefix (N : ℕ) : ℚ :=
  ∑ i ∈ range N, 1 / (denom i : ℚ)

lemma block_eq_prefix_sub (k n : ℕ) :
    reciprocalBlock k n = reciprocalPrefix (k+n) - reciprocalPrefix k := by
  simp only [reciprocalBlock, reciprocalPrefix, sum_range_add, add_sub_cancel_left]

/-- At least one of two nearby original partial sums must have a large
reduced denominator. This does not imply irrationality of their limit. -/
theorem nearby_prefix_reduced_height (m : ℕ) (hm : 9 ≤ m) :
    m^(m^3) ≤ (reciprocalPrefix (8*m^2)).den ∨
      m^(m^3) ≤ (reciprocalPrefix (8*m^2+m)).den := by
  have hb := growing_block_reduced_height m hm
  have hd : (reciprocalBlock (8*m^2) m).den ∣
      (reciprocalPrefix (8*m^2+m)).den * (reciprocalPrefix (8*m^2)).den := by
    rw [block_eq_prefix_sub]
    exact Rat.sub_den_dvd _ _
  have hl := hb.trans (Nat.le_of_dvd
    (Nat.mul_pos (reciprocalPrefix (8*m^2+m)).pos (reciprocalPrefix (8*m^2)).pos) hd)
  have he : m^(2*m^3) = (m^(m^3))^2 := by
    rw [← pow_mul]
    congr 1
    ring
  rw [he] at hl
  by_contra h
  push_neg at h
  nlinarith [Nat.mul_lt_mul_of_lt_of_le h.2 h.1.le (by positivity : 0 < m^(m^3))]

end ReducedBlockDenominatorBound

#print axioms ReducedBlockDenominatorBound.product_den_dvd_sum_den_mul_pairGcd_square
#print axioms ReducedBlockDenominatorBound.block_reduced_denominator_bound

#print axioms ReducedBlockDenominatorBound.growing_block_reduced_height
#print axioms ReducedBlockDenominatorBound.nearby_prefix_reduced_height
