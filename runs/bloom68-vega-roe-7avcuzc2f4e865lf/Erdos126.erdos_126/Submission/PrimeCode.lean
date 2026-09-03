import FormalConjecturesUtil

/-!
# A prime-color baseline for Erdős problem 126

The positive elements of a finite set of natural numbers have distinct binary
codes indexed by the prime divisors of the product of their pair sums.  For an
odd prime, the bit records which half contains the leading nonzero residue;
for the prime two, it records which half contains the odd part modulo four.

Consequently, the cardinality is at most `2 ^ k + 1`, where `k` is the number
of distinct prime divisors of the ordered off-diagonal pair-sum product.  The
extra one allows the vertex zero.  This is only an exponential baseline, not
the stronger asymptotic bound asked for in the conjecture.
-/

namespace Erdos126PrimeCode

/-- The bit determined by the leading unit at `p`.  At two the modulus is four. -/
def primeColor (p a : ℕ) : Bool :=
  if p = 2 then decide (2 * (ordCompl[p] a % 4) < 4)
  else decide (2 * (ordCompl[p] a % p) < p)

/-- Opposite nonzero residues, neither at the midpoint, lie in different halves. -/
lemma half_colors_ne {m x y : ℕ} (hx : ¬ m ∣ x)
    (hmid : 2 * (x % m) ≠ m) (hxy : m ∣ x + y) :
    decide (2 * (x % m) < m) ≠ decide (2 * (y % m) < m) := by
  have hsum : x % m + y % m = m := by
    have h := Nat.add_mod_add_of_le_add_mod
      (Nat.le_mod_add_mod_of_dvd_add_of_not_dvd hxy hx)
    rw [Nat.mod_eq_zero_of_dvd hxy, zero_add] at h
    exact h.symm
  intro h
  have hiff := decide_eq_decide.mp h
  by_cases hxlt : 2 * (x % m) < m
  · have hylt := hiff.mp hxlt
    omega
  · have hynlt : ¬ 2 * (y % m) < m := fun hy => hxlt (hiff.mpr hy)
    omega

/-- If the sum has higher `p`-valuation than one summand, both summands have
exactly the same `p`-valuation. -/
lemma factorization_eq_of_lt_sum {p a b : ℕ} (hp : p.Prime)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a.factorization p < (a + b).factorization p) :
    a.factorization p = b.factorization p := by
  have hsum0 : a + b ≠ 0 := by omega
  have hs : p ^ (a.factorization p + 1) ∣ a + b :=
    (hp.pow_dvd_iff_le_factorization hsum0).mpr h
  have ha0 : p ^ a.factorization p ∣ a := Nat.ordProj_dvd a p
  have hb0 : p ^ a.factorization p ∣ b :=
    (Nat.dvd_add_iff_right ha0).mpr
      ((pow_dvd_pow p (by omega : a.factorization p ≤ a.factorization p + 1)).trans hs)
  have hle : a.factorization p ≤ b.factorization p :=
    (hp.pow_dvd_iff_le_factorization hb).mp hb0
  have hnle : ¬ a.factorization p + 1 ≤ b.factorization p := by
    intro hle'
    have hb1 : p ^ (a.factorization p + 1) ∣ b :=
      (hp.pow_dvd_iff_le_factorization hb).mpr hle'
    have ha1 : p ^ (a.factorization p + 1) ∣ a :=
      (Nat.dvd_add_iff_left hb1).mpr hs
    have := (hp.pow_dvd_iff_le_factorization ha).mp ha1
    omega
  omega

/-- Cancel the common maximal prime power in a sum. -/
lemma pow_dvd_unit_sum {p a b k : ℕ} (hp : p.Prime)
    (hab : a.factorization p = b.factorization p)
    (h : p ^ (a.factorization p + k) ∣ a + b) :
    p ^ k ∣ ordCompl[p] a + ordCompl[p] b := by
  have hsum : a + b = p ^ a.factorization p * (ordCompl[p] a + ordCompl[p] b) := by
    calc
      a + b = p ^ a.factorization p * ordCompl[p] a +
          p ^ b.factorization p * ordCompl[p] b := by
        rw [Nat.ordProj_mul_ordCompl_eq_self, Nat.ordProj_mul_ordCompl_eq_self]
      _ = p ^ a.factorization p * (ordCompl[p] a + ordCompl[p] b) := by
        rw [← hab, mul_add]
  apply Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos hp.pos)
  rw [← pow_add, ← hsum]
  exact h

/-- Equal bits prevent the valuation of a sum from exceeding that of `2 * a`.
The allowance of one extra factor of two is precisely why its bit uses modulus
four instead of modulus two. -/
lemma factorization_sum_le_of_color_eq {p a b : ℕ} (hp : p.Prime)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : primeColor p a = primeColor p b) :
    (a + b).factorization p ≤ (2 * a).factorization p := by
  by_contra hle
  have hlt : (2 * a).factorization p < (a + b).factorization p := by omega
  have hfa : (2 * a).factorization p = (2 : ℕ).factorization p + a.factorization p := by
    rw [Nat.factorization_mul (by decide) ha, Finsupp.add_apply]
  have hva : a.factorization p < (a + b).factorization p := by omega
  have hab := factorization_eq_of_lt_sum hp ha hb hva
  have hsum0 : a + b ≠ 0 := by omega
  by_cases hp2 : p = 2
  · subst p
    have htwo : (2 : ℕ).factorization 2 = 1 := Nat.prime_two.factorization_self
    have hd : 2 ^ (a.factorization 2 + 2) ∣ a + b :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hsum0).mpr (by omega)
    have h4 : 4 ∣ ordCompl[2] a + ordCompl[2] b := by
      simpa using pow_dvd_unit_sum Nat.prime_two hab hd
    have hn2 : ¬ 2 ∣ ordCompl[2] a := Nat.not_dvd_ordCompl Nat.prime_two ha
    have hn4 : ¬ 4 ∣ ordCompl[2] a := fun h => hn2 ((by decide : 2 ∣ 4).trans h)
    have hmid : 2 * (ordCompl[2] a % 4) ≠ 4 := by
      have hmod2 : ordCompl[2] a % 2 ≠ 0 := fun h => hn2 (Nat.dvd_of_mod_eq_zero h)
      have hmod4 := Nat.mod_mod_of_dvd (ordCompl[2] a) (by decide : 2 ∣ 4)
      omega
    exact half_colors_ne hn4 hmid h4 (by simpa [primeColor] using hc)
  · have hd : p ^ (a.factorization p + 1) ∣ a + b :=
      (hp.pow_dvd_iff_le_factorization hsum0).mpr hva
    have hunit : p ∣ ordCompl[p] a + ordCompl[p] b := by
      simpa using pow_dvd_unit_sum hp hab hd
    have hmid : 2 * (ordCompl[p] a % p) ≠ p := by
      have hodd := hp.mod_two_eq_one_iff_ne_two.mpr hp2
      omega
    exact half_colors_ne (Nat.not_dvd_ordCompl hp ha) hmid hunit
      (by simpa [primeColor, hp2] using hc)

/-- Agreement at every prime dividing the sum forces the sum to divide `2 * a`. -/
lemma sum_dvd_twice_of_colors_eq {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : ∀ p : ℕ, p.Prime → p ∣ a + b → primeColor p a = primeColor p b) :
    a + b ∣ 2 * a := by
  apply (Nat.factorization_prime_le_iff_dvd (by omega) (by omega)).mp
  intro p hp
  by_cases hd : p ∣ a + b
  · exact factorization_sum_le_of_color_eq hp ha hb (hc p hp hd)
  · rw [Nat.factorization_eq_zero_of_not_dvd hd]
    exact Nat.zero_le _

/-- Two positive vertices agreeing at all prime divisors of their sum are equal. -/
lemma eq_of_colors_eq {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : ∀ p : ℕ, p.Prime → p ∣ a + b → primeColor p a = primeColor p b) :
    a = b := by
  have h₁ := Nat.le_of_dvd (by omega : 0 < 2 * a)
    (sum_dvd_twice_of_colors_eq ha hb hc)
  have h₂ := Nat.le_of_dvd (by omega : 0 < 2 * b)
    (sum_dvd_twice_of_colors_eq hb ha (fun p hp hd =>
      (hc p hp (by simpa [Nat.add_comm] using hd)).symm))
  omega

/-- The product over ordered pairs of distinct vertices, as in the conjecture. -/
def sumProduct (A : Finset ℕ) : ℕ :=
  ∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)

lemma sumProduct_ne_zero (A : Finset ℕ) : sumProduct A ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  rintro ⟨a, b⟩ hab
  have hne := (Finset.mem_offDiag.mp hab).2.2
  dsimp
  omega

/-- Each prime divisor of a pair sum occurs among the indexing primes. -/
lemma prime_mem_sumProduct {A : Finset ℕ} {a b p : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) (hp : p.Prime) (hd : p ∣ a + b) :
    p ∈ (sumProduct A).primeFactors := by
  apply hp.mem_primeFactors _ (sumProduct_ne_zero A)
  exact hd.trans (Finset.dvd_prod_of_mem (fun q : ℕ × ℕ => q.1 + q.2)
    (show (a, b) ∈ A.offDiag from Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩))

/-- The binary code of a vertex, with coordinates indexed by a finite prime set. -/
def code (S : Finset ℕ) (a : ℕ) : S → Bool :=
  fun p => primeColor p a

/-- On the positive vertices, the code using the primes of the pair-sum product
is injective. -/
theorem code_injective (A : Finset ℕ) :
    Function.Injective (fun a : A.erase 0 => code (sumProduct A).primeFactors a) := by
  intro a b hcode
  apply Subtype.ext
  by_contra hne
  apply hne
  have ha := Finset.mem_erase.mp a.property
  have hb := Finset.mem_erase.mp b.property
  apply eq_of_colors_eq ha.1 hb.1
  intro p hp hd
  have hpS := prime_mem_sumProduct ha.2 hb.2 hne hp hd
  exact congrFun hcode ⟨p, hpS⟩

/-- The positive vertices fit into the space of binary codes. -/
theorem card_erase_zero_le (A : Finset ℕ) :
    (A.erase 0).card ≤ 2 ^ (sumProduct A).primeFactors.card := by
  have h := Fintype.card_le_of_injective
    (fun a : A.erase 0 => code (sumProduct A).primeFactors a) (code_injective A)
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] using h

/-- Certified exponential baseline for the ordered pair-sum prime count.
This does not assert the superlogarithmic bound of Erdős problem 126. -/
theorem card_le_two_pow_primeFactors_card_add_one (A : Finset ℕ) :
    A.card ≤ 2 ^ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card + 1 := by
  have h := card_erase_zero_le A
  change (A.erase 0).card ≤ 2 ^ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card at h
  by_cases hzero : 0 ∈ A
  · have hcard := Finset.card_erase_add_one hzero
    omega
  · rw [Finset.erase_eq_of_notMem hzero] at h
    omega

end Erdos126PrimeCode
