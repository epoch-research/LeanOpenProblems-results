import Submission.PrimeReflection

/-! Reflection can fail to be involutive even when the two largest prime
factors are arbitrarily far apart. These are pointwise counterexamples to a
proposed repair of the reflection map, not a density obstruction. -/

namespace Erdos371

lemma primeReflection_twice_eq_iff (n : ℕ) (hn : 1 < n) :
    primeReflection (primeReflection n) = n ↔
      n < pairPrimeProduct n ∧
        pairPrimeProduct (primeReflection n) = pairPrimeProduct n := by
  constructor
  · intro he
    have hn' := (primeReflection_bounds n hn).1
    have hm := pairPrimeProduct_reflection_mono n hn
    have hm' := pairPrimeProduct_reflection_mono (primeReflection n) hn'
    rw [he] at hm'
    have hprod := le_antisymm hm' hm
    refine ⟨?_, hprod⟩
    have hb := (primeReflection_bounds (primeReflection n) hn').2
    change primeReflection (primeReflection n) < pairPrimeProduct (primeReflection n) at hb
    rwa [he, hprod] at hb
  · rintro ⟨hs, hp⟩
    exact primeReflection_twice_eq_of_product_eq n hn hs hp

lemma maxPrimeFac_cube_add_one_le_square (x : ℕ) (hx : 2 ≤ x) :
    Nat.maxPrimeFac (x^3+1) ≤ x^2 := by
  have hsq : x ≤ x^2 := Nat.le_self_pow (by decide) x
  have hsub := Nat.sub_add_cancel hsq
  have hfac : x^3+1 = (x+1)*(x^2-x+1) := by
    nlinarith [congrArg (fun t : ℕ => x*t) hsub]
  rw [hfac, Nat.maxPrimeFac_mul (by omega) (by omega)]
  apply max_le
  · exact Nat.maxPrimeFac_le.trans (by nlinarith)
  · exact Nat.maxPrimeFac_le.trans (by omega)

/-- Exponents divisible by all small prime-minus-one values make every prime
factor of this odd number large, by Fermat's little theorem. -/
lemma prime_factor_two_pow_factorial_cube_large (B : ℕ) :
    B < Nat.maxPrimeFac ((2^B.factorial)^3+1) := by
  let L := B.factorial
  let n := (2^L)^3
  have hL : L ≠ 0 := (Nat.factorial_pos B).ne'
  have hx : 2 ≤ 2^L := by simpa using Nat.le_self_pow hL 2
  have hn : 1 < n := by dsimp [n]; nlinarith [Nat.le_self_pow (by decide : 3 ≠ 0) (2^L)]
  have hp : Nat.maxPrimeFac n = 2 := by
    dsimp [n]
    rw [Nat.maxPrimeFac_pow (by decide), Nat.maxPrimeFac_pow hL,
      Nat.prime_two.maxPrimeFac_eq_self]
  let q := Nat.maxPrimeFac (n+1)
  have hq : q.Prime := Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)
  have hc : Nat.Coprime 2 q := by
    simpa only [hp] using maxPrimeFac_pair_coprime n
  change B < q
  by_contra hb
  have hqB : q ≤ B := by omega
  have hd : q-1 ∣ L := Nat.dvd_factorial (by have := hq.two_le; omega) (by omega)
  obtain ⟨k, hk⟩ := hd
  have hF := (Nat.ModEq.pow_card_sub_one_eq_one hq hc).pow k
  have hmod : Nat.ModEq q (2^L) 1 := by
    simpa only [← pow_mul, one_pow, ← hk] using hF
  have hnmod : Nat.ModEq q (n+1) 2 := by
    have h := (hmod.pow 3).add_right 1
    simpa only [one_pow, Nat.reduceAdd] using h
  have hqd : q ∣ 2 := (hnmod.dvd_iff (dvd_refl q)).mp Nat.maxPrimeFac_dvd
  exact hq.ne_one (hc.symm.eq_one_of_dvd hqd)

/-- Arbitrarily large multiplicative separation does not force the reflection
map to be an involution. No positive-density assertion is made here. -/
theorem separated_primeReflection_not_involutive (C : ℕ) :
    ∃ n : ℕ, 1 < n ∧
      C * Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) ∧
      primeReflection (primeReflection n) ≠ n := by
  let L := (2*C).factorial
  let x := 2^L
  let n := x^3
  have hL : L ≠ 0 := (Nat.factorial_pos (2*C)).ne'
  have hx : 2 ≤ x := Nat.le_self_pow hL 2
  have hn : 1 < n := by dsimp [n]; nlinarith [Nat.le_self_pow (by decide : 3 ≠ 0) x]
  have hp : Nat.maxPrimeFac n = 2 := by
    dsimp [n,x]
    rw [Nat.maxPrimeFac_pow (by decide), Nat.maxPrimeFac_pow hL,
      Nat.prime_two.maxPrimeFac_eq_self]
  have hq : 2*C < Nat.maxPrimeFac (n+1) := prime_factor_two_pow_factorial_cube_large (2*C)
  have hsmall : pairPrimeProduct n ≤ n := by
    unfold pairPrimeProduct
    rw [hp]
    have hb : Nat.maxPrimeFac (n+1) ≤ x^2 := maxPrimeFac_cube_add_one_le_square x hx
    change 2 * Nat.maxPrimeFac (n+1) ≤ x^3
    calc
      _ ≤ 2*x^2 := Nat.mul_le_mul_left _ hb
      _ ≤ x*x^2 := Nat.mul_le_mul_right _ hx
      _ = _ := by ring
  refine ⟨n, hn, ?_, ?_⟩
  · simpa only [hp, Nat.mul_comm] using hq
  · intro he
    have hs := ((primeReflection_twice_eq_iff n hn).mp he).1
    omega

#print axioms separated_primeReflection_not_involutive
end Erdos371
