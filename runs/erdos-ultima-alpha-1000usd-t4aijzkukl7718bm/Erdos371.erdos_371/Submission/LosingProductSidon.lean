import Submission.LosingProductComparison

/-! In a short winning-cofactor range, products of losing integers have
multiplicity at most two. This is an exact algebraic bound, not a signed
counting or density estimate. -/
namespace Erdos371
open Finset

private lemma int_eq_zero_of_dvd_abs_lt (p z : ℤ) (hz : |z| < p)
    (hd : p ∣ z) : z = 0 := by
  by_cases h : 0 ≤ z
  · exact Int.eq_zero_of_dvd_of_nonneg_of_lt h ((le_abs_self z).trans_lt hz) hd
  · have hn : 0 ≤ -z := by omega
    have he := Int.eq_zero_of_dvd_of_nonneg_of_lt hn
      ((neg_le_abs z).trans_lt hz) (dvd_neg.mpr hd)
    omega

/-- A bounded-coefficient affine product determines its two coefficients,
up to their order. -/
lemma short_affine_product_unique (p K x y z w : ℤ)
    (hK : 0 ≤ K) (hp : 4*K < p)
    (hx : |x| ≤ K) (hy : |y| ≤ K) (hz : |z| ≤ K) (hw : |w| ≤ K)
    (he : (p*x+1)*(p*y+1) = (p*z+1)*(p*w+1)) :
    (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
  have hp0 : p ≠ 0 := by omega
  have hf : p*(p*(x*y-z*w)+(x+y-z-w)) = 0 := by nlinarith [he]
  have hc := (mul_eq_zero.mp hf).resolve_left hp0
  have hd : p ∣ x+y-z-w := ⟨-(x*y-z*w), by nlinarith [hc]⟩
  have hb : |x+y-z-w| < p := by
    obtain ⟨hx₁,hx₂⟩ := abs_le.mp hx
    obtain ⟨hy₁,hy₂⟩ := abs_le.mp hy
    obtain ⟨hz₁,hz₂⟩ := abs_le.mp hz
    obtain ⟨hw₁,hw₂⟩ := abs_le.mp hw
    exact abs_lt.mpr ⟨by omega, by omega⟩
  have hs := int_eq_zero_of_dvd_abs_lt p (x+y-z-w) hb hd
  have hprod : x*y = z*w := by
    have hh : p*(x*y-z*w)=0 := by omega
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hp0)
  have hsx : x*(x+y-z-w)=0 := by rw [hs, mul_zero]
  have hr : (x-z)*(x-w)=0 := by nlinarith [hprod, hsx]
  rcases mul_eq_zero.mp hr with hr | hr
  · left; constructor <;> omega
  · right; constructor <;> omega

/-- The absolute values introduce no further solutions when p>2: the two
signed products both have residue one modulo p, so cannot be negatives. -/
lemma short_abs_affine_product_unique (p K x y z w : ℤ)
    (hK : 0 ≤ K) (hp : 4*K < p) (hp2 : 2 < p)
    (hx : |x| ≤ K) (hy : |y| ≤ K) (hz : |z| ≤ K) (hw : |w| ≤ K)
    (he : |p*x+1| * |p*y+1| = |p*z+1| * |p*w+1|) :
    (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
  rw [← abs_mul, ← abs_mul] at he
  rcases abs_eq_abs.mp he with he | he
  · exact short_affine_product_unique p K x y z w hK hp hx hy hz hw he
  · have hd : p ∣ (p*x+1)*(p*y+1)+(p*z+1)*(p*w+1)-2 := by
      refine ⟨p*(x*y+z*w)+x+y+z+w, ?_⟩
      ring
    have hd' : p ∣ (-2 : ℤ) := by
      convert hd using 1
      nlinarith [he]
    have hzero := int_eq_zero_of_dvd_abs_lt p (-2) (by simpa using hp2) hd'
    norm_num at hzero

/-- A losing integer is the absolute value of px+1, where |x| is its
winning cofactor. Both comparison orientations are included. -/
lemma losingNumber_short_affine_certificate (n p K : ℕ) (hn : 1 < n)
    (hnp : primeWinner n = p) (hK : winningNumber n / p ≤ K) :
    ∃ x : ℤ, |x| ≤ K ∧ |(p : ℤ)*x+1| = (losingNumber n : ℤ) := by
  have hpf := (comparison_numbers_prime_factors n hn).2.2
  have hd : p ∣ winningNumber n := by
    rw [← hnp, ← hpf]
    exact Nat.maxPrimeFac_dvd
  have he : p*(winningNumber n / p) = winningNumber n := Nat.mul_div_cancel' hd
  have her : (p : ℤ)*(winningNumber n / p : ℕ) = (winningNumber n : ℤ) := by
    exact_mod_cast he
  have hKr : ((winningNumber n / p : ℕ) : ℤ) ≤ K := by exact_mod_cast hK
  by_cases hr : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)
  · refine ⟨-((winningNumber n / p : ℕ) : ℤ), by simpa only [abs_neg, abs_of_nonneg (Int.natCast_nonneg _)] using hKr, ?_⟩
    have he' : (p : ℤ)*(-((winningNumber n / p : ℕ) : ℤ))+1 = -(n : ℤ) := by
      rw [mul_neg, her]
      simp only [winningNumber, if_pos hr, Nat.cast_add, Nat.cast_one]
      ring
    rw [he']
    simp only [abs_neg, abs_of_nonneg (Int.natCast_nonneg n), losingNumber, if_pos hr]
  · refine ⟨((winningNumber n / p : ℕ) : ℤ), by simpa only [abs_neg, abs_of_nonneg (Int.natCast_nonneg _)] using hKr, ?_⟩
    rw [her]
    simp only [winningNumber, losingNumber, if_neg hr, Nat.cast_add, Nat.cast_one]
    exact abs_of_nonneg (by omega)

/-- For a common prime winner p and cofactors at most K with 4K<p, equal
loser products imply equal unordered pairs of original comparisons. -/
theorem short_losing_product_unique (p K n m a b : ℕ)
    (hp2 : 2 < p) (hsize : 4*K < p)
    (hn : 1 < n) (hm : 1 < m) (ha : 1 < a) (hb : 1 < b)
    (hnp : primeWinner n = p) (hmp : primeWinner m = p)
    (hap : primeWinner a = p) (hbp : primeWinner b = p)
    (hnK : winningNumber n / p ≤ K) (hmK : winningNumber m / p ≤ K)
    (haK : winningNumber a / p ≤ K) (hbK : winningNumber b / p ≤ K)
    (he : losingNumber n * losingNumber m = losingNumber a * losingNumber b) :
    (n = a ∧ m = b) ∨ (n = b ∧ m = a) := by
  obtain ⟨x,hx,hex⟩ := losingNumber_short_affine_certificate n p K hn hnp hnK
  obtain ⟨y,hy,hey⟩ := losingNumber_short_affine_certificate m p K hm hmp hmK
  obtain ⟨z,hz,hez⟩ := losingNumber_short_affine_certificate a p K ha hap haK
  obtain ⟨w,hw,hew⟩ := losingNumber_short_affine_certificate b p K hb hbp hbK
  have hprod : |(p : ℤ)*x+1| * |(p : ℤ)*y+1| = |(p : ℤ)*z+1| * |(p : ℤ)*w+1| := by
    rw [hex,hey,hez,hew]
    exact_mod_cast he
  have hh := short_abs_affine_product_unique (p : ℤ) (K : ℤ) x y z w
    (by positivity) (by exact_mod_cast hsize) (by exact_mod_cast hp2) hx hy hz hw hprod
  have hinj (i j : ℕ) (hi : 1 < i) (hj : 1 < j)
      (hip : primeWinner i = p) (hjp : primeWinner j = p)
      (heij : (losingNumber i : ℤ) = (losingNumber j : ℤ)) : i = j :=
    losingNumber_injective_at_winner i j p hi hj hp2 hip hjp (by exact_mod_cast heij)
  rcases hh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact Or.inl ⟨hinj n a hn ha hnp hap (hex.symm.trans hez),
      hinj m b hm hb hmp hbp (hey.symm.trans hew)⟩
  · exact Or.inr ⟨hinj n b hn hb hnp hbp (hex.symm.trans hew),
      hinj m a hm ha hmp hap (hey.symm.trans hez)⟩

/-- Each fixed-product fibre contains at most the two orderings of one pair. -/
theorem short_losing_product_fibre_le_two (S : Finset ℕ) (p K L : ℕ)
    (hp2 : 2 < p) (hsize : 4*K < p)
    (hS : ∀ n ∈ S, 1 < n ∧ primeWinner n = p ∧ winningNumber n / p ≤ K) :
    ((S ×ˢ S).filter (fun nm => losingNumber nm.1 * losingNumber nm.2 = L)).card ≤ 2 := by
  classical
  let T := (S ×ˢ S).filter (fun nm => losingNumber nm.1 * losingNumber nm.2 = L)
  change T.card ≤ 2
  by_cases ht : T.Nonempty
  · obtain ⟨⟨n,m⟩,hnm⟩ := ht
    obtain ⟨hnmS,hnmL⟩ := mem_filter.mp hnm
    obtain ⟨hn,hm⟩ := mem_product.mp hnmS
    have hsub : T ⊆ {(n,m),(m,n)} := by
      intro ab hab
      obtain ⟨habS,habL⟩ := mem_filter.mp hab
      obtain ⟨ha,hb⟩ := mem_product.mp habS
      have hh := short_losing_product_unique p K ab.1 ab.2 n m hp2 hsize
        (hS _ ha).1 (hS _ hb).1 (hS _ hn).1 (hS _ hm).1
        (hS _ ha).2.1 (hS _ hb).2.1 (hS _ hn).2.1 (hS _ hm).2.1
        (hS _ ha).2.2 (hS _ hb).2.2 (hS _ hn).2.2 (hS _ hm).2.2
        (habL.trans hnmL.symm)
      rcases hh with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · have he : ab = (n,m) := Prod.ext h₁ h₂
        simp [he]
      · have he : ab = (m,n) := Prod.ext h₁ h₂
        simp [he]
    have hc : ({(n,m),(m,n)} : Finset (ℕ × ℕ)).card ≤ 2 := by
      rcases card_pair_eq_one_or_two (a := (n,m)) (b := (m,n)) with h | h <;> omega
    exact (card_le_card hsub).trans hc
  · simp only [not_nonempty_iff_eq_empty.mp ht,card_empty]
    omega

/-- The same bound holds for the actual output-comparison map. -/
theorem short_losingProductIndex_fibre_le_two (S : Finset ℕ) (p K r : ℕ)
    (hp2 : 2 < p) (hsize : 4*K < p)
    (hS : ∀ n ∈ S, 1 < n ∧ primeWinner n = p ∧ winningNumber n / p ≤ K) :
    ((S ×ˢ S).filter (fun nm => losingProductIndex nm.1 nm.2 = r)).card ≤ 2 := by
  have hsub : (S ×ˢ S).filter (fun nm => losingProductIndex nm.1 nm.2 = r) ⊆
      (S ×ˢ S).filter (fun nm => losingNumber nm.1 * losingNumber nm.2 = losingNumber r) := by
    intro nm hnm
    obtain ⟨hnmS,hnmR⟩ := mem_filter.mp hnm
    obtain ⟨hn,hm⟩ := mem_product.mp hnmS
    have hh := (losingProductIndex_structure nm.1 nm.2
      (hS _ hn).1 (hS _ hm).1 ((hS _ hn).2.1.trans (hS _ hm).2.1.symm)).2.1
    rw [hnmR] at hh
    exact mem_filter.mpr ⟨hnmS,hh.symm⟩
  exact (card_le_card hsub).trans
    (short_losing_product_fibre_le_two S p K (losingNumber r) hp2 hsize hS)

/-- For inputs below N, the restriction follows from 4N<p^2. -/
theorem upper_half_losingProductIndex_fibre_le_two (S : Finset ℕ) (p N r : ℕ)
    (hp2 : 2 < p) (hsize : 4*N < p^2)
    (hS : ∀ n ∈ S, 1 < n ∧ n < N ∧ primeWinner n = p) :
    ((S ×ˢ S).filter (fun nm => losingProductIndex nm.1 nm.2 = r)).card ≤ 2 := by
  have hK : 4*(N/p) < p := by
    have hd := Nat.div_mul_le_self N p
    by_contra h
    have hh := Nat.mul_le_mul_right p (show p ≤ 4*(N/p) by omega)
    nlinarith
  apply short_losingProductIndex_fibre_le_two S p (N/p) r hp2 hK
  intro n hn
  have hb := (comparison_numbers_bounds n (hS n hn).1).2.2.2
  refine ⟨(hS n hn).1,(hS n hn).2.2,?_⟩
  exact Nat.div_le_div_right (by have := (hS n hn).2.1; omega)

#print axioms short_affine_product_unique
#print axioms short_abs_affine_product_unique
#print axioms losingNumber_short_affine_certificate
#print axioms short_losing_product_unique
#print axioms short_losing_product_fibre_le_two
#print axioms short_losingProductIndex_fibre_le_two
#print axioms upper_half_losingProductIndex_fibre_le_two
end Erdos371
