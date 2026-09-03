import Submission.FactorialLambert

/-!
A prime last coefficient gives nonvanishing of finite Lambert-tail operators
under a rationality hypothesis. No small-error family is established here.
-/
namespace PrimeLeadingForms

open Finset Erdos68Development

/-- Prefix through index n of an integer-coefficient factorial series. -/
def partialSum (c : ℕ → ℤ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), (c k : ℚ) / k.factorial

def weightedTail (c w : ℕ → ℤ) (N : ℕ) (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range N, (w k : ℚ) * (x - partialSum c k)

lemma partialSum_step (c : ℕ → ℤ) (p : ℕ) (hp : 0 < p) :
    partialSum c p = partialSum c (p - 1) + (c p : ℚ) / p.factorial := by
  unfold partialSum
  rw [show p - 1 + 1 = p by omega, Finset.sum_range_succ]

lemma factorial_mul_partialSum_integer (c : ℕ → ℤ) (n m : ℕ) (hm : m ≤ n) :
    ∃ z : ℤ, (n.factorial : ℚ) * partialSum c m = z := by
  refine ⟨∑ k ∈ Finset.range (m + 1), c k * (n.factorial / k.factorial : ℕ), ?_⟩
  simp only [partialSum, Finset.mul_sum, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.cast_div_charZero (Nat.factorial_dvd_factorial (by
    have := Finset.mem_range.mp hk
    omega))]
  ring

lemma factorial_mul_rational_integer (n : ℕ) (x : ℚ) (hx : x.den ≤ n) :
    ∃ z : ℤ, (n.factorial : ℚ) * x = z := by
  obtain ⟨a, ha⟩ := Nat.dvd_factorial x.pos hx
  refine ⟨x.num * (a : ℤ), ?_⟩
  conv_lhs => rw [← Rat.num_div_den x]
  rw [ha]
  push_cast
  have hd : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  field_simp

lemma factorial_mul_tail_integer (c : ℕ → ℤ) (n m : ℕ) (hm : m ≤ n)
    (x : ℚ) (hx : x.den ≤ n) :
    ∃ z : ℤ, (n.factorial : ℚ) * (x - partialSum c m) = z := by
  obtain ⟨a, ha⟩ := factorial_mul_rational_integer n x hx
  obtain ⟨b, hb⟩ := factorial_mul_partialSum_integer c n m hm
  refine ⟨a - b, ?_⟩
  simp only [mul_sub, ha, hb, Int.cast_sub]

lemma integer_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, ∃ z : ℤ, f i = z) : ∃ z : ℤ, (∑ i ∈ s, f i) = z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨a, ha⟩ := h i (by simp)
    obtain ⟨b, hb⟩ := ih (fun j hj => h j (by simp [hj]))
    exact ⟨a + b, by simp [Finset.sum_insert hi, ha, hb]⟩

lemma factorial_mul_weightedTail_integer (c w : ℕ → ℤ) (n N : ℕ)
    (hN : N ≤ n + 1) (x : ℚ) (hx : x.den ≤ n) :
    ∃ z : ℤ, (n.factorial : ℚ) * weightedTail c w N x = z := by
  unfold weightedTail
  rw [Finset.mul_sum]
  apply integer_sum
  intro k hk
  obtain ⟨a, ha⟩ := factorial_mul_tail_integer c n k
    (by have := Finset.mem_range.mp hk; omega) x hx
  refine ⟨w k * a, ?_⟩
  rw [mul_left_comm, ha, Int.cast_mul]

/-- At a unit coefficient, a nondivisible final weight prevents vanishing.
Primality is only needed later to obtain the Lambert unit coefficient. -/
theorem unit_last_nonzero (c w : ℕ → ℤ) (p : ℕ) (hp : 0 < p)
    (hc : c p = 1) (hw : ¬ (p : ℤ) ∣ w p) (x : ℚ) (hx : x.den < p) :
    weightedTail c w (p + 1) x ≠ 0 := by
  have hx' : x.den ≤ p - 1 := by omega
  obtain ⟨a, ha⟩ := factorial_mul_weightedTail_integer c w (p - 1) p
    (by omega) x hx'
  obtain ⟨b, hb⟩ := factorial_mul_tail_integer c (p - 1) (p - 1)
    (le_refl _) x hx'
  have hfac : (p.factorial : ℚ) = p * ((p - 1).factorial : ℚ) := by
    exact_mod_cast (by simpa [show p - 1 + 1 = p by omega]
      using Nat.factorial_succ (p - 1))
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hfacQ : ((p - 1).factorial : ℚ) ≠ 0 := by positivity
  intro hz
  have hs : weightedTail c w p x + (w p : ℚ) *
      (x - partialSum c (p - 1)) = (w p : ℚ) / p.factorial := by
    unfold weightedTail at hz
    rw [Finset.sum_range_succ, partialSum_step c p hp, hc] at hz
    change weightedTail c w p x + (w p : ℚ) *
      (x - (partialSum c (p - 1) + (1 : ℚ) / p.factorial)) = 0 at hz
    linear_combination hz
  have hmul := congrArg (fun y : ℚ => (p.factorial : ℚ) * y) hs
  have hid : (p : ℚ) * ((a : ℚ) + (w p : ℚ) * (b : ℚ)) = w p := by
    rw [hfac] at hmul
    field_simp at hmul
    calc
      _ = (p : ℚ) * ((p - 1).factorial : ℚ) *
          (weightedTail c w p x + (w p : ℚ) * (x - partialSum c (p - 1))) := by
        rw [← ha, ← hb]
        ring
      _ = _ := hmul
  have hidZ : (p : ℤ) * (a + w p * b) = w p := by exact_mod_cast hid
  exact hw ⟨a + w p * b, hidZ.symm⟩

theorem lambert_prime_last_nonzero (w : ℕ → ℤ) (p : ℕ) (hp : p.Prime)
    (hw : ¬ (p : ℤ) ∣ w p) (x : ℚ) (hx : x.den < p) :
    weightedTail (fun n => (lambertCoeff n : ℤ)) w (p + 1) x ≠ 0 := by
  apply unit_last_nonzero _ w p hp.pos _ hw x hx
  simp [lambertCoeff_prime hp]


lemma prime_not_dvd_factorial_product (s : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hs : ∀ d ∈ s, d < p) : ¬ (p : ℤ) ∣ ∏ d ∈ s, (d.factorial : ℤ) := by
  have hn : ¬ p ∣ ∏ d ∈ s, d.factorial := by
    induction s using Finset.induction_on with
    | empty => simpa using hp.not_dvd_one
    | @insert d s hd ih =>
      rw [Finset.prod_insert hd]
      intro h
      rcases hp.dvd_mul.mp h with h | h
      · exact (Nat.not_le.mpr (hs d (by simp))) (hp.dvd_factorial.mp h)
      · exact ih (fun j hj => hs j (by simp [hj])) h
  exact_mod_cast hn


/-- Once the full rational operator value is integral, its last weight must
be divisible by a unit index. In particular, integral-boundary combinations
cannot automatically inherit the preceding prime nonvanishing test. -/
theorem unit_integral_value_last_dvd (c w : ℕ → ℤ) (p : ℕ) (hp : 0 < p)
    (hc : c p = 1) (x : ℚ) (hx : x.den < p) (v : ℤ)
    (hv : weightedTail c w (p + 1) x = v) : (p : ℤ) ∣ w p := by
  have hx' : x.den ≤ p - 1 := by omega
  obtain ⟨a, ha⟩ := factorial_mul_weightedTail_integer c w (p - 1) p
    (by omega) x hx'
  obtain ⟨b, hb⟩ := factorial_mul_tail_integer c (p - 1) (p - 1)
    (le_refl _) x hx'
  have hfac : (p.factorial : ℚ) = p * ((p - 1).factorial : ℚ) := by
    exact_mod_cast (by simpa [show p - 1 + 1 = p by omega]
      using Nat.factorial_succ (p - 1))
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hfacQ : ((p - 1).factorial : ℚ) ≠ 0 := by positivity
  have hs : weightedTail c w p x + (w p : ℚ) *
      (x - partialSum c (p - 1)) = (v : ℚ) + (w p : ℚ) / p.factorial := by
    unfold weightedTail at hv
    rw [Finset.sum_range_succ, partialSum_step c p hp, hc] at hv
    change weightedTail c w p x + (w p : ℚ) *
      (x - (partialSum c (p - 1) + (1 : ℚ) / p.factorial)) = v at hv
    linear_combination hv
  have hmul := congrArg (fun y : ℚ => (p.factorial : ℚ) * y) hs
  rw [hfac] at hmul
  field_simp at hmul
  have hleft : (p : ℚ) * ((a : ℚ) + (w p : ℚ) * (b : ℚ)) =
      (p : ℚ) * ((p - 1).factorial : ℚ) * (v : ℚ) + (w p : ℚ) := by
    calc
      _ = (p : ℚ) * ((p - 1).factorial : ℚ) *
          (weightedTail c w p x + (w p : ℚ) * (x - partialSum c (p - 1))) := by
        rw [← ha, ← hb]
        ring
      _ = _ := hmul
  have hid : (p : ℚ) * ((a : ℚ) + (w p : ℚ) * (b : ℚ) -
      ((p - 1).factorial : ℚ) * (v : ℚ)) = w p := by
    linear_combination hleft
  have hidZ : (p : ℤ) * (a + w p * b - ((p - 1).factorial : ℤ) * v) = w p := by
    exact_mod_cast hid
  exact ⟨a + w p * b - ((p - 1).factorial : ℤ) * v, hidZ.symm⟩

end PrimeLeadingForms

#print axioms PrimeLeadingForms.unit_last_nonzero
#print axioms PrimeLeadingForms.lambert_prime_last_nonzero

#print axioms PrimeLeadingForms.prime_not_dvd_factorial_product

#print axioms PrimeLeadingForms.unit_integral_value_last_dvd
