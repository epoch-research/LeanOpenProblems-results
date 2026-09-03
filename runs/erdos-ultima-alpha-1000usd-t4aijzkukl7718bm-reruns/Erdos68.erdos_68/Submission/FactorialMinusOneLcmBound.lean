import Submission.VariableRowAnnihilation

/-!
A quantitative lower bound for common multiples of blocks of factorial-minus-one
denominators. This bounds a nonzero retained coefficient of a row annihilator;
it does not prove that a retained coefficient is nonzero, or settle Spec.lean.
-/

namespace FactorialMinusOneLcmBound

open Finset

lemma gcd_prod_dvd (a : ℕ → ℕ) (b n : ℕ) :
    Nat.gcd b (∏ i ∈ range n, a i) ∣ ∏ i ∈ range n, Nat.gcd b (a i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, prod_range_succ]
    exact (gcd_mul_dvd_mul_gcd b _ _).trans (Nat.mul_dvd_mul_right ih _)

def pairGcd (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ i ∈ range n, ∏ j ∈ range i, Nat.gcd (a i) (a j)

lemma pairGcd_succ (a : ℕ → ℕ) (n : ℕ) :
    pairGcd a (n+1) = pairGcd a n * ∏ j ∈ range n, Nat.gcd (a n) (a j) := by
  exact prod_range_succ _ _

lemma product_dvd_common_mul_pairGcd (a : ℕ → ℕ) (n L : ℕ)
    (hL : ∀ i < n, a i ∣ L) :
    (∏ i ∈ range n, a i) ∣ L * pairGcd a n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨v, hv⟩ := ih (fun i hi => hL i (by omega))
    have ha : a n ∣ (∏ i ∈ range n, a i)*v := by
      rw [← hv]
      exact dvd_mul_of_dvd_left (hL n (by omega)) _
    have hh : a n ∣ (∏ j ∈ range n, Nat.gcd (a n) (a j))*v :=
      (dvd_gcd_mul_of_dvd_mul ha).trans (Nat.mul_dvd_mul_right (gcd_prod_dvd a (a n) n) v)
    rw [prod_range_succ, pairGcd_succ]
    have he : L*(pairGcd a n * ∏ j ∈ range n, Nat.gcd (a n) (a j)) =
        (∏ i ∈ range n, a i)*((∏ j ∈ range n, Nat.gcd (a n) (a j))*v) := by
      rw [← mul_assoc, hv]
      ring
    rw [he]
    exact Nat.mul_dvd_mul_left _ hh

lemma pairGcd_pos (a : ℕ → ℕ) (n : ℕ) (ha : ∀ i < n, 0 < a i) :
    0 < pairGcd a n := by
  apply prod_pos
  intro i hi
  apply prod_pos
  intro j hj
  exact Nat.gcd_pos_of_pos_left _ (ha i (mem_range.mp hi))

lemma pairGcd_bound (a : ℕ → ℕ) (n B : ℕ) (hB : 1 ≤ B)
    (h : ∀ i < n, ∀ j < i, Nat.gcd (a i) (a j) ≤ B) :
    pairGcd a n ≤ B^(n^2) := by
  have hb : ∀ i < n, (∏ j ∈ range i, Nat.gcd (a i) (a j)) ≤ B^n := by
    intro i hi
    calc
      _ ≤ B^i := by
        simpa using prod_le_pow_card (range i) (fun j => Nat.gcd (a i) (a j)) B
          (fun j hj => h i hi j (mem_range.mp hj))
      _ ≤ _ := Nat.pow_le_pow_right hB (by omega)
  calc
    _ ≤ (B^n)^n := by
      simpa [pairGcd] using prod_le_pow_card (range n)
        (fun i => ∏ j ∈ range i, Nat.gcd (a i) (a j)) (B^n)
        (fun i hi => hb i (mem_range.mp hi))
    _ = _ := by rw [← pow_mul, pow_two]

def denom (n : ℕ) : ℕ := n.factorial-1

lemma denom_pos (n : ℕ) (hn : 2 ≤ n) : 0 < denom n := by
  have h := Nat.one_lt_factorial.mpr hn
  unfold denom
  omega

lemma pair_gcd_dvd_ratio (k i j : ℕ) (hji : j < i) :
    Nat.gcd (denom (k+i)) (denom (k+j)) ∣
      (k+j+1).ascFactorial (i-j)-1 := by
  let R := (k+j+1).ascFactorial (i-j)
  have hR : 0 < R := Nat.ascFactorial_pos (k+j) (i-j)
  have hfj : 0 < (k+j).factorial := Nat.factorial_pos _
  have he : (k+i).factorial = (k+j).factorial*R := by
    dsimp [R]
    rw [Nat.factorial_mul_ascFactorial]
    congr 1
    omega
  have hid : denom (k+i) = R*denom (k+j)+(R-1) := by
    dsimp [denom]
    rw [he]
    have h1 : (k+j).factorial-1+1 = (k+j).factorial := by omega
    have h2 : R-1+1 = R := by omega
    have h3 : 0 < (k+j).factorial*R := Nat.mul_pos hfj hR
    have h4 : (k+j).factorial*R-1+1 = (k+j).factorial*R := by omega
    have hmul := congrArg (fun x : ℕ => R*x) h1
    simp only [Nat.mul_add, Nat.mul_one] at hmul
    nlinarith
  have hg := Nat.gcd_dvd_left (denom (k+i)) (denom (k+j))
  conv_rhs at hg => rw [hid]
  exact (Nat.dvd_add_right (dvd_mul_of_dvd_right
    (Nat.gcd_dvd_right (denom (k+i)) (denom (k+j))) R)).mp hg

lemma pair_gcd_bound (k n i j : ℕ) (hk : 2 ≤ k) (hi : i < n) (hji : j < i) :
    Nat.gcd (denom (k+i)) (denom (k+j)) ≤ (k+n)^n := by
  have hR : 1 < (k+j+1).ascFactorial (i-j) := by
    obtain ⟨r, hr⟩ : ∃ r, i-j = r+1 := ⟨i-j-1, by omega⟩
    rw [hr, Nat.ascFactorial_succ]
    have hpos := Nat.ascFactorial_pos (k+j) r
    nlinarith
  calc
    _ ≤ (k+j+1).ascFactorial (i-j)-1 :=
      Nat.le_of_dvd (by omega) (pair_gcd_dvd_ratio k i j hji)
    _ ≤ (k+j+1).ascFactorial (i-j) := Nat.sub_le _ _
    _ ≤ (k+j+(i-j))^(i-j) := Nat.ascFactorial_le_pow_add (k+j) (i-j)
    _ ≤ (k+n)^(i-j) := Nat.pow_le_pow_left (by omega) _
    _ ≤ (k+n)^n := Nat.pow_le_pow_right (by omega) (by omega)

/-- Any positive common multiple of this block satisfies a product-height
bound. This does not assume pairwise coprimality of its denominators. -/
theorem block_common_multiple_bound (k n L : ℕ) (hk : 2 ≤ k) (hL : 0 < L)
    (hd : ∀ i < n, denom (k+i) ∣ L) :
    (denom k)^n ≤ L*(k+n)^(n^3) := by
  let a : ℕ → ℕ := fun i => denom (k+i)
  have hap : ∀ i < n, 0 < a i := by intro i hi; exact denom_pos _ (by omega)
  have hp : (∏ i ∈ range n, a i) ≤ L*pairGcd a n :=
    Nat.le_of_dvd (Nat.mul_pos hL (pairGcd_pos a n hap))
      (product_dvd_common_mul_pairGcd a n L hd)
  have hg : pairGcd a n ≤ (k+n)^(n^3) := by
    have he := pairGcd_bound a n ((k+n)^n) (Nat.one_le_pow n (k+n) (by omega))
      (fun i hi j hj => pair_gcd_bound k n i j hk hi hj)
    simpa only [← pow_mul, show n*(n^2) = n^3 by ring] using he
  have hlo : (denom k)^n ≤ ∏ i ∈ range n, a i := by
    have hm : ∀ i ∈ range n, denom k ≤ a i := by
      intro i hi
      exact Nat.sub_le_sub_right (Nat.factorial_le (by omega : k ≤ k+i)) 1
    simpa using prod_le_prod' (s := range n) hm
  exact hlo.trans (hp.trans (Nat.mul_le_mul_left L hg))

lemma large_factorial_bound (m : ℕ) (hm : 5 ≤ m) :
    m^(4*m^2) ≤ denom (4*m^2) := by
  have he := Nat.factorial_mul_pow_le_factorial (m := 2*m^2) (n := 2*m^2)
  have hf : 1 ≤ (2*m^2).factorial := Nat.factorial_pos _
  have hpow : (m^2)^(2*m^2) < (2*m^2+1)^(2*m^2) := by
    apply Nat.pow_lt_pow_left (by nlinarith) (by positivity)
  have hl : (2*m^2+1)^(2*m^2) ≤ (4*m^2).factorial := by
    have hh := Nat.mul_le_mul_right ((2*m^2+1)^(2*m^2)) hf
    rw [show 2*m^2+2*m^2 = 4*m^2 by ring] at he
    omega
  have hh : m^(4*m^2) < (4*m^2).factorial := by
    convert hpow.trans_le hl using 1
    rw [← pow_mul]
    congr 1
    ring
  exact Nat.le_sub_one_of_lt hh

/-- An explicit superlinear logarithmic lower bound, using a block of m
rows beginning at 4m². It applies to their lcm and every positive common
multiple. -/
theorem quadratic_block_height (m L : ℕ) (hm : 5 ≤ m) (hL : 0 < L)
    (hd : ∀ i < m, denom (4*m^2+i) ∣ L) : m^(m^3) ≤ L := by
  have hb := block_common_multiple_bound (4*m^2) m L (by nlinarith) hL hd
  have hlo : m^(4*m^3) ≤ (denom (4*m^2))^m := by
    have he := Nat.pow_le_pow_left (large_factorial_bound m hm) m
    convert he using 1
    rw [← pow_mul]
    congr 1
    ring
  have hbase : 4*m^2+m ≤ m^3 := by
    have h1 := Nat.mul_le_mul_right (m^2) hm
    have h2 : m ≤ m^2 := Nat.le_self_pow (by omega) m
    nlinarith
  have hhi : (4*m^2+m)^(m^3) ≤ m^(3*m^3) := by
    have he := Nat.pow_le_pow_left hbase (m^3)
    simpa only [← pow_mul] using he
  have hall : m^(4*m^3) ≤ L*m^(3*m^3) :=
    hlo.trans (hb.trans (Nat.mul_le_mul_left L hhi))
  have he : m^(4*m^3) = m^(m^3)*m^(3*m^3) := by
    rw [← pow_add]
    congr 1
    ring
  rw [he] at hall
  exact Nat.le_of_mul_le_mul_right hall (by positivity)

/-- In particular the lcm itself has the displayed lower bound. -/
theorem quadratic_block_lcm_height (m : ℕ) (hm : 5 ≤ m) :
    m^(m^3) ≤ (range m).lcm (fun i => denom (4*m^2+i)) := by
  apply quadratic_block_height m _ hm
  · apply Nat.pos_of_ne_zero
    apply Finset.lcm_ne_zero_iff.mpr
    intro i _
    exact (denom_pos _ (by nlinarith)).ne'
  · intro i hi
    exact Finset.dvd_lcm (mem_range.mpr hi)

/-- Integer-weighted annihilation of all m rows in the indicated block has
large retained coefficient, PROVIDED that coefficient is nonzero. -/
theorem annihilator_coefficient_height {ι : Type*} (s : Finset ι)
    (z : ι → ℤ) (index : ι → ℕ) (m : ℕ) (hm : 5 ≤ m)
    (hA : (∑ i ∈ s, z i) ≠ 0)
    (hz : ∀ j < m, ∑ i ∈ s, (z i : ℚ) /
      ((((4*m^2+j).factorial : ℚ) ^ (index i / (4*m^2+j))) *
        ((4*m^2+j).factorial-1)) = 0) :
    m^(m^3) ≤ (∑ i ∈ s, z i).natAbs := by
  apply quadratic_block_height m _ hm (Int.natAbs_pos.mpr hA)
  intro j hj
  have he := VariableRowAnnihilation.factorial_row_denominator_dvd s z index
    (4*m^2+j) (by nlinarith) (hz j hj)
  apply Int.natCast_dvd.mp
  have hfac : 1 ≤ (4*m^2+j).factorial := Nat.factorial_pos _
  simpa only [denom, Nat.cast_sub hfac, Nat.cast_one] using he

/-- A weight-size consequence. This remains conditional on a nonzero sum
of the weights; zero retained coefficients are not excluded. -/
theorem annihilator_weight_height (D Q m : ℕ) (hm : 5 ≤ m)
    (z : Fin D → ℤ) (index : Fin D → ℕ)
    (hA : (∑ i, z i) ≠ 0) (hbound : ∀ i, |z i| ≤ Q)
    (hz : ∀ j < m, ∑ i, (z i : ℚ) /
      ((((4*m^2+j).factorial : ℚ) ^ (index i / (4*m^2+j))) *
        ((4*m^2+j).factorial-1)) = 0) :
    m^(m^3) ≤ D*Q := by
  have he := annihilator_coefficient_height univ z index m hm hA hz
  have hb : (∑ i, z i).natAbs ≤ D*Q := by
    have hZ : |∑ i, z i| ≤ (D : ℤ)*Q := by
      calc
        _ ≤ ∑ i, |z i| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin D, (Q : ℤ) := Finset.sum_le_sum (fun i _ => hbound i)
        _ = _ := by simp
    rw [← Int.natCast_natAbs] at hZ
    exact_mod_cast hZ
  exact he.trans hb

#print axioms pair_gcd_dvd_ratio
#print axioms block_common_multiple_bound
#print axioms quadratic_block_height
#print axioms quadratic_block_lcm_height
#print axioms annihilator_coefficient_height
#print axioms annihilator_weight_height

end FactorialMinusOneLcmBound
