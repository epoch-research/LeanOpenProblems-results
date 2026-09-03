import Submission.ReciprocalDiscrepancy

/-! A sign-reversing reflection preserving the larger prime factor. This map
is not injective or involutive, so it does not prove equality of densities. -/

namespace Erdos371

lemma prime_divisor_pair_bounds (a b m : ℕ) (ha : a.Prime) (hb : b.Prime)
    (hm : 0 < m) (hmab : m < a * b) (ham : a ∣ m) (hbm : b ∣ m + 1) :
    (Nat.maxPrimeFac m < Nat.maxPrimeFac (m + 1) ↔ a < b) ∧
      max (Nat.maxPrimeFac m) (Nat.maxPrimeFac (m + 1)) = max a b ∧
      min a b ≤ min (Nat.maxPrimeFac m) (Nat.maxPrimeFac (m + 1)) := by
  have hstrict : m + 1 < a * b := by
    by_contra h
    have he : m + 1 = a * b := by omega
    have hdiv : a ∣ 1 := (Nat.dvd_add_iff_right ham).mpr (by rw [he]; exact Nat.dvd_mul_right a b)
    exact ha.not_dvd_one hdiv
  have hka : 0 < m / a := Nat.div_pos (Nat.le_of_dvd hm ham) ha.pos
  have hkb : 0 < (m + 1) / b := Nat.div_pos (Nat.le_of_dvd (by omega) hbm) hb.pos
  have hkaB : m / a < b := (Nat.div_lt_iff_lt_mul ha.pos).mpr (by nlinarith)
  have hkbA : (m + 1) / b < a := (Nat.div_lt_iff_lt_mul hb.pos).mpr (by nlinarith)
  have hma : Nat.maxPrimeFac m = max a (Nat.maxPrimeFac (m / a)) := by
    calc
      _ = Nat.maxPrimeFac (a * (m / a)) := congrArg Nat.maxPrimeFac (Nat.mul_div_cancel' ham).symm
      _ = _ := by rw [Nat.maxPrimeFac_mul ha.ne_zero hka.ne', ha.maxPrimeFac_eq_self]
  have hmb : Nat.maxPrimeFac (m + 1) = max b (Nat.maxPrimeFac ((m + 1) / b)) := by
    calc
      _ = Nat.maxPrimeFac (b * ((m + 1) / b)) := congrArg Nat.maxPrimeFac (Nat.mul_div_cancel' hbm).symm
      _ = _ := by rw [Nat.maxPrimeFac_mul hb.ne_zero hkb.ne', hb.maxPrimeFac_eq_self]
  have hpa : Nat.maxPrimeFac (m / a) < b := Nat.maxPrimeFac_le.trans_lt hkaB
  have hpb : Nat.maxPrimeFac ((m + 1) / b) < a := Nat.maxPrimeFac_le.trans_lt hkbA
  have hal : a ≤ Nat.maxPrimeFac m := by rw [hma]; exact le_max_left _ _
  have hbl : b ≤ Nat.maxPrimeFac (m + 1) := by rw [hmb]; exact le_max_left _ _
  refine ⟨?_, ?_, min_le_min hal hbl⟩
  · by_cases hab : a < b
    · have hm' : Nat.maxPrimeFac m < b := by rw [hma]; exact max_lt hab hpa
      have hm'' : Nat.maxPrimeFac (m + 1) = b := by rw [hmb, max_eq_left (by omega)]
      simp only [hab, iff_true, hm'']
      exact hm'
    · have hm' : Nat.maxPrimeFac m = a := by rw [hma, max_eq_left (by omega)]
      have hm'' : Nat.maxPrimeFac (m + 1) ≤ a := by rw [hmb]; exact max_le (by omega) hpb.le
      simp only [hab, iff_false, hm']
      omega
  · apply le_antisymm
    · rw [hma, hmb]
      exact max_le
        (max_le (le_max_left _ _) (hpa.le.trans (le_max_right _ _)))
        (max_le (le_max_right _ _) (hpb.le.trans (le_max_left _ _)))
    · exact max_le_max hal hbl

/-- Reduce to the prime-product period and reflect there. -/
def primeReflection (n : ℕ) : ℕ :=
  let d := Nat.maxPrimeFac n * Nat.maxPrimeFac (n + 1)
  d - 1 - n % d

lemma maxPrimeFac_pair_coprime (n : ℕ) :
    (Nat.maxPrimeFac n).Coprime (Nat.maxPrimeFac (n + 1)) :=
  divisor_pair_coprime n _ _ Nat.maxPrimeFac_dvd Nat.maxPrimeFac_dvd

lemma primeReflection_eq_root (n : ℕ) (hn : 1 < n) :
    primeReflection n = adjacentRoot (Nat.maxPrimeFac (n + 1)) (Nat.maxPrimeFac n)
      (maxPrimeFac_pair_coprime n).symm := by
  let p := Nat.maxPrimeFac n
  let q := Nat.maxPrimeFac (n + 1)
  have hp : p.Prime := Nat.prime_maxPrimeFac_of_one_lt n hn
  have hq : q.Prime := Nat.prime_maxPrimeFac_of_one_lt (n + 1) (by omega)
  have hc : p.Coprime q := maxPrimeFac_pair_coprime n
  have hm : Nat.ModEq (p * q) (n % (p * q)) n := Nat.mod_modEq n (p * q)
  have h₁ : p ∣ n % (p * q) :=
    (hm.dvd_iff (Nat.dvd_mul_right p q)).mpr Nat.maxPrimeFac_dvd
  have h₂ : q ∣ n % (p * q) + 1 :=
    ((hm.add_right 1).dvd_iff (Nat.dvd_mul_left q p)).mpr Nat.maxPrimeFac_dvd
  have he := adjacentRoot_unique p q hc hp.pos hq.pos (n % (p * q))
    (Nat.mod_lt _ (Nat.mul_pos hp.pos hq.pos)) h₁ h₂
  change p * q - 1 - n % (p * q) = adjacentRoot q p hc.symm
  rw [he, adjacentRoot_swap p q hc hp.one_lt hq.one_lt]

lemma primeReflection_bounds (n : ℕ) (hn : 1 < n) :
    1 < primeReflection n ∧
      primeReflection n < Nat.maxPrimeFac n * Nat.maxPrimeFac (n + 1) := by
  have hp := Nat.prime_maxPrimeFac_of_one_lt n hn
  have hq := Nat.prime_maxPrimeFac_of_one_lt (n + 1) (by omega)
  rw [primeReflection_eq_root n hn]
  constructor
  · have hpos := adjacentRoot_pos _ _ (maxPrimeFac_pair_coprime n).symm hp.one_lt
    have hdiv := adjacentRoot_dvd_left _ _ (maxPrimeFac_pair_coprime n).symm
    exact hq.one_lt.trans_le (Nat.le_of_dvd hpos hdiv)
  · simpa only [Nat.mul_comm] using adjacentRoot_lt _ _
      (maxPrimeFac_pair_coprime n).symm hq.pos hp.pos

/-- The reflection reverses the comparison, keeps the larger prime factor,
and can increase the smaller prime factor. -/
theorem primeReflection_structure (n : ℕ) (hn : 1 < n) :
    (Nat.maxPrimeFac (primeReflection n) < Nat.maxPrimeFac (primeReflection n + 1) ↔
      Nat.maxPrimeFac (n + 1) < Nat.maxPrimeFac n) ∧
    max (Nat.maxPrimeFac (primeReflection n)) (Nat.maxPrimeFac (primeReflection n + 1)) =
      max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) ∧
    min (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) ≤
      min (Nat.maxPrimeFac (primeReflection n)) (Nat.maxPrimeFac (primeReflection n + 1)) := by
  have hp := Nat.prime_maxPrimeFac_of_one_lt n hn
  have hq := Nat.prime_maxPrimeFac_of_one_lt (n + 1) (by omega)
  have he := prime_divisor_pair_bounds (Nat.maxPrimeFac (n + 1)) (Nat.maxPrimeFac n)
    (primeReflection n) hq hp (by have := (primeReflection_bounds n hn).1; omega)
    (by simpa only [Nat.mul_comm] using (primeReflection_bounds n hn).2)
    (by rw [primeReflection_eq_root n hn]; exact adjacentRoot_dvd_left _ _ _)
    (by rw [primeReflection_eq_root n hn]; exact adjacentRoot_dvd_right _ _ _ hp.pos)
  simpa only [min_comm, max_comm] using he

theorem primeReflection_sign (n : ℕ) (hn : 1 < n) :
    factorSign (primeReflection n) = -factorSign n := by
  have he := (primeReflection_structure n hn).1
  have hne := consecutive_maxPrimeFac_ne n
  unfold factorSign predicateSign
  simp only [he]
  rcases lt_or_gt_of_ne hne with h | h <;> simp [h, h.not_gt]

def pairPrimeProduct (n : ℕ) : ℕ := Nat.maxPrimeFac n * Nat.maxPrimeFac (n + 1)

lemma pairPrimeProduct_reflection_mono (n : ℕ) (hn : 1 < n) :
    pairPrimeProduct n ≤ pairPrimeProduct (primeReflection n) := by
  have h := primeReflection_structure n hn
  unfold pairPrimeProduct
  rw [← min_mul_max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)),
    ← min_mul_max (Nat.maxPrimeFac (primeReflection n)) (Nat.maxPrimeFac (primeReflection n + 1)),
    h.2.1]
  exact Nat.mul_le_mul_right _ h.2.2

lemma primeReflection_mod_free (n : ℕ) (hn : n < pairPrimeProduct n) :
    primeReflection n = pairPrimeProduct n - 1 - n := by
  change pairPrimeProduct n - 1 - n % pairPrimeProduct n = pairPrimeProduct n - 1 - n
  rw [Nat.mod_eq_of_lt hn]

lemma primeReflection_twice_eq_of_product_eq (n : ℕ) (hn : 1 < n)
    (hsmall : n < pairPrimeProduct n)
    (he : pairPrimeProduct (primeReflection n) = pairPrimeProduct n) :
    primeReflection (primeReflection n) = n := by
  have hbound : primeReflection n < pairPrimeProduct (primeReflection n) := by
    rw [he]
    exact (primeReflection_bounds n hn).2
  rw [primeReflection_mod_free _ hbound, he, primeReflection_mod_free n hsmall]
  omega

/-- Every orbit eventually enters a two-cycle. This is an orbit statement,
not a statement about the distribution of indices in natural intervals. -/
theorem primeReflection_eventually_two_periodic (n : ℕ) (hn : 1 < n) :
    ∃ k : ℕ, ∀ j ≥ k, primeReflection^[j + 2] n = primeReflection^[j] n := by
  let y (j : ℕ) := primeReflection^[j] n
  have hy (j : ℕ) : y (j + 1) = primeReflection (y j) :=
    Function.iterate_succ_apply' primeReflection j n
  have hpos (j : ℕ) : 1 < y j := by
    induction j with
    | zero => exact hn
    | succ j ih => rw [hy]; exact (primeReflection_bounds _ ih).1
  have hmax (j : ℕ) : max (Nat.maxPrimeFac (y j)) (Nat.maxPrimeFac (y j + 1)) =
      max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) := by
    induction j with
    | zero => rfl
    | succ j ih => rw [hy, (primeReflection_structure _ (hpos j)).2.1, ih]
  have hmono : Monotone (fun j => pairPrimeProduct (y j)) := by
    apply monotone_nat_of_le_succ
    intro j
    rw [hy]
    exact pairPrimeProduct_reflection_mono _ (hpos j)
  have hbounded (j : ℕ) : pairPrimeProduct (y j) ≤
      (max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)))^2 := by
    have h₁ := (le_max_left (Nat.maxPrimeFac (y j)) (Nat.maxPrimeFac (y j + 1))).trans_eq (hmax j)
    have h₂ := (le_max_right (Nat.maxPrimeFac (y j)) (Nat.maxPrimeFac (y j + 1))).trans_eq (hmax j)
    simpa only [pairPrimeProduct, pow_two] using Nat.mul_le_mul h₁ h₂
  obtain ⟨c, k, hk⟩ := converges_of_monotone_of_bounded hmono hbounded
  refine ⟨k + 1, ?_⟩
  intro j hj
  have hj1 : 1 ≤ j := by omega
  have hprev : y j = primeReflection (y (j - 1)) := by
    simpa only [Nat.sub_add_cancel hj1] using hy (j - 1)
  have hsmall : y j < pairPrimeProduct (y j) := by
    have hb := (primeReflection_bounds (y (j - 1)) (hpos (j - 1))).2
    rw [← hprev] at hb
    exact hb.trans_le (hmono (Nat.sub_le j 1))
  have he : pairPrimeProduct (primeReflection (y j)) = pairPrimeProduct (y j) := by
    rw [← hy j, hk (j + 1) (by omega), hk j (by omega)]
  have htwice := primeReflection_twice_eq_of_product_eq (y j) (hpos j) hsmall he
  change y (j + 2) = y j
  rw [show j + 2 = (j + 1) + 1 by omega, hy, hy]
  exact htwice

theorem primeReflection_ne_self (n : ℕ) (hn : 1 < n) : primeReflection n ≠ n := by
  intro he
  have hs := primeReflection_sign n hn
  rw [he] at hs
  unfold factorSign predicateSign at hs
  split_ifs at hs <;> linarith

/-- These finite failures prevent using this map as an involutive pairing. -/
theorem primeReflection_not_injective : ¬Function.Injective primeReflection := by
  intro h
  have he : primeReflection 2 = primeReflection 8 := by decide +kernel
  have hn := h he
  omega

theorem primeReflection_not_involutive : ¬Function.Involutive primeReflection := by
  intro h
  have he : primeReflection (primeReflection 6) = 20 := by decide +kernel
  have hn := h 6
  omega

theorem primeReflection_transient_example :
    primeReflection 6 = 14 ∧ primeReflection 14 = 20 ∧ primeReflection 20 = 14 := by
  decide +kernel

#print axioms primeReflection_structure
#print axioms primeReflection_sign
#print axioms primeReflection_eventually_two_periodic
#print axioms primeReflection_not_injective
#print axioms primeReflection_not_involutive
end Erdos371
