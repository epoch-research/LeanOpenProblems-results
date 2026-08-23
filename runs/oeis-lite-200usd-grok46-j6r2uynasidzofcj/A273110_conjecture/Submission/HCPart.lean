import FormalConjectures.Util.ProblemImports

/-
  Hilbert symbols and the Hasse principle for the conic
  X^2 - d Y^2 - N Z^2 = 0.
-/

open scoped NumberTheorySymbols
open Nat Int

/- Odd part and 2-adic invariants -/

/-- The odd part of a nonzero integer. -/
def oddPart (a : ℤ) : ℤ := a / (2 : ℤ) ^ padicValInt 2 a

lemma oddPart_mul_pow (a : ℤ) :
    oddPart a * (2 : ℤ) ^ padicValInt 2 a = a := by
  unfold oddPart
  exact Int.ediv_mul_cancel (padicValInt_dvd (p := 2) a)

lemma two_not_dvd_oddPart {a : ℤ} (ha : a ≠ 0) : ¬ (2 : ℤ) ∣ oddPart a := by
  intro h
  set v := padicValInt 2 a
  have hmul : oddPart a * (2 : ℤ) ^ v = a := oddPart_mul_pow a
  have hpow : (2 : ℤ) ^ (v + 1) ∣ a := by
    rw [← hmul, pow_succ, mul_comm ((2 : ℤ) ^ v) 2]
    exact mul_dvd_mul_right h _
  have hp1 : (2 : ℕ) ≠ 1 := by decide
  have hform : v = multiplicity (2 : ℤ) a :=
    padicValInt.of_ne_one_ne_zero hp1 ha
  have hf : FiniteMultiplicity (2 : ℤ) a :=
    finiteMultiplicity_iff.2 ⟨by decide, ha⟩
  have : ¬ (2 : ℤ) ^ (v + 1) ∣ a := by
    rw [hform]
    exact (hf.multiplicity_lt_iff_not_dvd).1 (Nat.lt_succ_self _)
  exact this hpow

lemma oddPart_odd {a : ℤ} (ha : a ≠ 0) : Odd (oddPart a) := by
  rw [← Int.not_even_iff_odd, even_iff_two_dvd]
  exact two_not_dvd_oddPart ha

lemma oddPart_ne_zero {a : ℤ} (ha : a ≠ 0) : oddPart a ≠ 0 := by
  intro h
  have := oddPart_mul_pow a
  simp [h] at this
  exact ha this.symm

/-- `ε(u) mod 2`, where `ε(u) = (u - 1) / 2`. -/
def hilbertε (u : ℤ) : ℕ := (((u - 1) / 2).natAbs) % 2

/-- `ω(u) mod 2`, where `ω(u) = (u^2 - 1) / 8`. -/
def hilbertω (u : ℤ) : ℕ := (((u ^ 2 - 1) / 8).natAbs) % 2

/- Hilbert symbols -/

/-- The real Hilbert symbol. -/
def hilbertInf (a b : ℤ) : ℤ := if a < 0 ∧ b < 0 then -1 else 1

/-- Unit part of `a` at an odd prime `p`. -/
def pUnit (p : ℕ) (a : ℤ) : ℤ := a / (p : ℤ) ^ padicValInt p a

/-- The odd Hilbert symbol at a prime `p`. -/
def hilbertOdd (p : ℕ) (a b : ℤ) : ℤ :=
  let α := padicValInt p a
  let β := padicValInt p b
  jacobiSym (pUnit p a) p ^ β * jacobiSym (pUnit p b) p ^ α *
    (-1 : ℤ) ^ (α * β * (p / 2))

/-- The 2-adic Hilbert symbol. -/
def hilbertTwo (a b : ℤ) : ℤ :=
  let α := padicValInt 2 a
  let β := padicValInt 2 b
  (-1 : ℤ) ^ (hilbertε (oddPart a) * hilbertε (oddPart b) +
    α * hilbertω (oddPart b) + β * hilbertω (oddPart a))

/-- Hilbert symbol `(a, b)_v`. `v = 0` is the real place. -/
def hilbert (v : ℕ) (a b : ℤ) : ℤ :=
  if a = 0 ∨ b = 0 then 0
  else if v = 0 then hilbertInf a b
  else if v = 2 then hilbertTwo a b
  else if v.Prime then hilbertOdd v a b
  else 1

lemma hilbertInf_symm (a b : ℤ) : hilbertInf a b = hilbertInf b a := by
  unfold hilbertInf
  by_cases ha : a < 0 <;> by_cases hb : b < 0 <;> simp [ha, hb]

lemma hilbertInf_of_nonneg_right {a b : ℤ} (hb : 0 ≤ b) : hilbertInf a b = 1 := by
  unfold hilbertInf
  split_ifs with h
  · exact (not_lt_of_ge hb h.2).elim
  · rfl

lemma hilbertInf_of_nonneg_left {a b : ℤ} (ha : 0 ≤ a) : hilbertInf a b = 1 := by
  unfold hilbertInf
  split_ifs with h
  · exact (not_lt_of_ge ha h.1).elim
  · rfl

lemma hilbertInf_mul {a b c : ℤ} (hb0 : b ≠ 0) (hc0 : c ≠ 0) :
    hilbertInf a (b * c) = hilbertInf a b * hilbertInf a c := by
  unfold hilbertInf
  cases' le_or_gt 0 a with ha ha
  · have : ¬ a < 0 := not_lt.mpr ha
    simp [this]
  · by_cases hb : b < 0
    · by_cases hc : c < 0
      · have : ¬ b * c < 0 := (mul_pos_of_neg_of_neg hb hc).not_gt
        simp [ha, hb, hc, this]
      · have hpos : 0 < c := lt_of_le_of_ne (le_of_not_gt hc) hc0.symm
        have : b * c < 0 := mul_neg_of_neg_of_pos hb hpos
        simp [ha, hb, hc, this]
    · by_cases hc : c < 0
      · have hpos : 0 < b := lt_of_le_of_ne (le_of_not_gt hb) hb0.symm
        have : b * c < 0 := mul_neg_of_pos_of_neg hpos hc
        simp [ha, hb, hc, this]
      · have : ¬ b * c < 0 :=
          not_lt.mpr (mul_nonneg (le_of_not_gt hb) (le_of_not_gt hc))
        simp [ha, hb, hc, this]

lemma hilbertInf_sq (a b : ℤ) : hilbertInf a (b ^ 2) = 1 := by
  have : 0 ≤ b ^ 2 := sq_nonneg b
  exact hilbertInf_of_nonneg_right this

/- p-adic units -/

lemma p_pow_dvd_self (p : ℕ) (a : ℤ) :
    (p : ℤ) ^ padicValInt p a ∣ a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hnat : p ^ padicValNat p a.natAbs ∣ a.natAbs := pow_padicValNat_dvd
  simpa [padicValInt, Int.natCast_pow] using
    Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hnat)

lemma pUnit_mul_pow (p : ℕ) (a : ℤ) :
    pUnit p a * (p : ℤ) ^ padicValInt p a = a := by
  unfold pUnit
  exact Int.ediv_mul_cancel (p_pow_dvd_self p a)

lemma pUnit_ne_zero {p : ℕ} {a : ℤ} (ha : a ≠ 0) : pUnit p a ≠ 0 := by
  intro h
  have := pUnit_mul_pow p a
  simp [h] at this
  exact ha this.symm

lemma p_not_dvd_pUnit {p : ℕ} {a : ℤ} (hp : p.Prime) (ha : a ≠ 0) :
    ¬ (p : ℤ) ∣ pUnit p a := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h
  set v := padicValInt p a
  have hmul : pUnit p a * (p : ℤ) ^ v = a := pUnit_mul_pow p a
  have hpow : (p : ℤ) ^ (v + 1) ∣ a := by
    rw [← hmul, pow_succ, mul_comm ((p : ℤ) ^ v) p]
    exact mul_dvd_mul_right h _
  have hp1 : p ≠ 1 := hp.ne_one
  have hform : v = multiplicity (p : ℤ) a :=
    padicValInt.of_ne_one_ne_zero hp1 ha
  have hf : FiniteMultiplicity (p : ℤ) a :=
    finiteMultiplicity_iff.2 ⟨by exact_mod_cast hp.one_lt.ne', ha⟩
  have : ¬ (p : ℤ) ^ (v + 1) ∣ a := by
    rw [hform]
    exact (hf.multiplicity_lt_iff_not_dvd).1 (Nat.lt_succ_self _)
  exact this hpow

lemma pUnit_mul {p : ℕ} [Fact p.Prime] {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    pUnit p (a * b) = pUnit p a * pUnit p b := by
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hval : padicValInt p (a * b) = padicValInt p a + padicValInt p b :=
    padicValInt.mul ha hb
  have hpow : (p : ℤ) ^ padicValInt p (a * b) ≠ 0 := by
    rcases eq_or_ne p 0 with rfl | hp0
    · simp [padicValInt]
    · exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hp0)
  apply mul_right_cancel₀ hpow
  rw [pUnit_mul_pow p (a * b), hval, pow_add, mul_mul_mul_comm, pUnit_mul_pow p a,
    pUnit_mul_pow p b]


/- Squares are trivial for Hilbert symbols -/

lemma jacobiSym_sq (a : ℤ) (p : ℕ) : jacobiSym (a * a) p = jacobiSym a p ^ 2 := by
  rw [pow_two]
  exact jacobiSym.mul_left a a p

lemma jacobiSym_sq' (a : ℤ) (p : ℕ) : jacobiSym (a ^ 2) p = jacobiSym a p ^ 2 := by
  simpa [pow_two] using jacobiSym_sq a p

lemma pUnit_gcd_eq_one {p : ℕ} [hp : Fact p.Prime] {a : ℤ} (ha : a ≠ 0) :
    (pUnit p a).gcd p = 1 := by
  rw [Int.gcd_def, Nat.gcd_comm]
  refine (Nat.Prime.coprime_iff_not_dvd hp.out).2 ?_
  intro h
  exact p_not_dvd_pUnit hp.out ha
    (Int.dvd_natAbs.mp (Int.natCast_dvd.mpr h))

lemma jacobiSym_pUnit_sq_eq_one {p : ℕ} [Fact p.Prime] {a : ℤ} (ha : a ≠ 0) :
    jacobiSym (pUnit p a) p ^ 2 = 1 := by
  have h := jacobiSym.eq_one_or_neg_one (pUnit_gcd_eq_one (p := p) ha)
  rcases h with h | h <;> simp [h]

lemma hilbertOdd_sq {p : ℕ} [Fact p.Prime] {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertOdd p a (b * b) = 1 := by
  unfold hilbertOdd
  have hval : padicValInt p (b * b) = 2 * padicValInt p b := by
    rw [padicValInt.mul hb hb, two_mul]
  have hunit : pUnit p (b * b) = pUnit p b * pUnit p b := pUnit_mul hb hb
  simp only [hval, hunit, jacobiSym_sq]
  have h1 : jacobiSym (pUnit p a) p ^ (2 * padicValInt p b) = 1 := by
    rw [pow_mul, jacobiSym_pUnit_sq_eq_one (p := p) ha]
    simp
  have h2 : (jacobiSym (pUnit p b) p ^ 2) ^ padicValInt p a = 1 := by
    rw [jacobiSym_pUnit_sq_eq_one hb]
    simp
  have h3 : (-1 : ℤ) ^ (padicValInt p a * (2 * padicValInt p b) * (p / 2)) = 1 := by
    have : Even (padicValInt p a * (2 * padicValInt p b) * (p / 2)) :=
      ⟨padicValInt p a * padicValInt p b * (p / 2), by ring⟩
    exact Even.neg_one_pow this
  simp [h1, h2, h3]

/-- Local solubility package: Hilbert symbols are 1 at the real place, 2, and
all odd primes. -/
def AllHilbert (d N : ℤ) : Prop :=
  d ≠ 0 ∧ N ≠ 0 ∧
    hilbertInf d N = 1 ∧
    hilbertTwo d N = 1 ∧
    ∀ p : ℕ, p.Prime → p ≠ 2 → hilbertOdd p d N = 1

lemma AllHilbert.ne_zero_left {d N : ℤ} (h : AllHilbert d N) : d ≠ 0 := h.1
lemma AllHilbert.ne_zero_right {d N : ℤ} (h : AllHilbert d N) : N ≠ 0 := h.2.1

lemma hilbertTwo_symm (a b : ℤ) : hilbertTwo a b = hilbertTwo b a := by
  unfold hilbertTwo
  have : hilbertε (oddPart a) * hilbertε (oddPart b) +
      padicValInt 2 a * hilbertω (oddPart b) +
      padicValInt 2 b * hilbertω (oddPart a) =
      hilbertε (oddPart b) * hilbertε (oddPart a) +
      padicValInt 2 b * hilbertω (oddPart a) +
      padicValInt 2 a * hilbertω (oddPart b) := by ring
  simp [this]

lemma hilbertOdd_symm (p : ℕ) (a b : ℤ) : hilbertOdd p a b = hilbertOdd p b a := by
  unfold hilbertOdd
  have : padicValInt p a * padicValInt p b * (p / 2) =
      padicValInt p b * padicValInt p a * (p / 2) := by ring
  simp [this, mul_comm]

lemma AllHilbert.swap {d N : ℤ} (h : AllHilbert d N) : AllHilbert N d :=
  ⟨h.2.1, h.1, hilbertInf_symm d N ▸ h.2.2.1,
    hilbertTwo_symm d N ▸ h.2.2.2.1,
    fun p hp hp2 => hilbertOdd_symm p d N ▸ h.2.2.2.2 p hp hp2⟩

lemma hilbertInf_s_sq_sub (a s : ℤ) : hilbertInf a (s ^ 2 - a) = 1 := by
  unfold hilbertInf
  split_ifs with h
  · rcases h with ⟨ha, ht⟩
    have : s ^ 2 < a := by linarith
    have : 0 ≤ s ^ 2 := sq_nonneg s
    linarith
  · rfl


lemma oddPart_mul {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    oddPart (a * b) = oddPart a * oddPart b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hval : padicValInt 2 (a * b) = padicValInt 2 a + padicValInt 2 b :=
    padicValInt.mul ha hb
  have hpow : (2 : ℤ) ^ padicValInt 2 (a * b) ≠ 0 := pow_ne_zero _ (by decide)
  apply mul_right_cancel₀ hpow
  rw [oddPart_mul_pow (a * b), hval, pow_add, mul_mul_mul_comm,
    oddPart_mul_pow a, oddPart_mul_pow b]

lemma hilbertε_sq_odd {u : ℤ} (hu : Odd u) : hilbertε (u * u) = 0 := by
  obtain ⟨k, rfl⟩ := hu
  have heq : ((2 * k + 1) * (2 * k + 1) - 1) / 2 = 2 * (k * (k + 1)) := by
    have : (2 * k + 1) * (2 * k + 1) - 1 = 2 * (2 * (k * (k + 1))) := by ring
    rw [this, Int.mul_ediv_cancel_left _ (by decide)]
  unfold hilbertε
  rw [heq, Int.natAbs_mul]
  simp

lemma hilbertω_sq_odd {u : ℤ} (hu : Odd u) : hilbertω (u * u) = 0 := by
  obtain ⟨k, rfl⟩ := hu
  have heq : (((2 * k + 1) * (2 * k + 1)) ^ 2 - 1) / 8 =
      k * (k + 1) * (2 * k * (k + 1) + 1) := by
    have : ((2 * k + 1) * (2 * k + 1)) ^ 2 - 1 =
        8 * (k * (k + 1) * (2 * k * (k + 1) + 1)) := by ring
    rw [this, Int.mul_ediv_cancel_left _ (by decide)]
  unfold hilbertω
  rw [heq]
  have : Even (k * (k + 1) : ℤ) := Int.even_mul_succ_self k
  have hdiv : (2 : ℤ) ∣ k * (k + 1) * (2 * k * (k + 1) + 1) :=
    dvd_mul_of_dvd_left (even_iff_two_dvd.mp this) _
  have : 2 ∣ (k * (k + 1) * (2 * k * (k + 1) + 1)).natAbs :=
    Int.natCast_dvd.mp hdiv
  exact Nat.mod_eq_zero_of_dvd this

lemma hilbertTwo_sq {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertTwo a (b * b) = 1 := by
  unfold hilbertTwo
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hval : padicValInt 2 (b * b) = 2 * padicValInt 2 b := by
    rw [padicValInt.mul hb hb, two_mul]
  have hodd : oddPart (b * b) = oddPart b * oddPart b := oddPart_mul hb hb
  rw [hval, hodd]
  have hε : hilbertε (oddPart b * oddPart b) = 0 :=
    hilbertε_sq_odd (oddPart_odd hb)
  have hω : hilbertω (oddPart b * oddPart b) = 0 :=
    hilbertω_sq_odd (oddPart_odd hb)
  have heven : Even (2 * padicValInt 2 b * hilbertω (oddPart a)) :=
    ⟨padicValInt 2 b * hilbertω (oddPart a), by ring⟩
  simp [hε, hω, Even.neg_one_pow heven]

lemma hilbertOdd_sq' {p : ℕ} [Fact p.Prime] {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertOdd p a (b ^ 2) = 1 := by
  simpa [pow_two] using hilbertOdd_sq (p := p) ha hb

lemma hilbertTwo_sq' {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertTwo a (b ^ 2) = 1 := by
  simpa [pow_two] using hilbertTwo_sq ha hb

/- Multiplicativity of Hilbert symbols -/

lemma even_iff_natAbs_even (a : ℤ) : Even a ↔ Even a.natAbs := by
  rw [Int.even_iff, Nat.even_iff]
  constructor
  · intro h
    have : (2 : ℤ) ∣ a := Int.dvd_of_emod_eq_zero h
    exact Nat.mod_eq_zero_of_dvd (Int.natCast_dvd.mp this)
  · intro h
    have : 2 ∣ a.natAbs := Nat.dvd_of_mod_eq_zero h
    exact Int.emod_eq_zero_of_dvd (Int.natCast_dvd.mpr this)

lemma hilbertε_eq_zero_iff {u : ℤ} (hu : Odd u) :
    hilbertε u = 0 ↔ u % 4 = 1 := by
  obtain ⟨k, rfl⟩ := hu
  unfold hilbertε
  have hk : ((2 * k + 1 - 1 : ℤ) / 2) = k := by omega
  rw [hk]
  have hparity : k.natAbs % 2 = 0 ↔ Even k := by
    constructor
    · intro h
      exact (even_iff_natAbs_even k).mpr (Nat.even_iff.mpr h)
    · intro h
      exact Nat.even_iff.mp ((even_iff_natAbs_even k).mp h)
  constructor
  · intro h
    have : Even k := hparity.mp h
    obtain ⟨t, ht⟩ := this
    have : k = 2 * t := by omega
    rw [this]
    have : (4 * t + 1 : ℤ) % 4 = 1 := by omega
    convert this using 2
    ring
  · intro h
    apply hparity.mpr
    -- 2k+1 ≡ 1 mod 4 ⇒ k even
    have : (2 * k + 1 : ℤ) % 4 = 1 := h
    have : k % 2 = 0 := by omega
    exact Int.even_iff.mpr this

lemma odd_mod_four {u : ℤ} (hu : Odd u) : u % 4 = 1 ∨ u % 4 = 3 := by
  have h2 : u % 2 = 1 := Int.odd_iff.mp hu
  have : u % 4 = 0 ∨ u % 4 = 1 ∨ u % 4 = 2 ∨ u % 4 = 3 := by omega
  rcases this with h | h | h | h
  · have : u % 2 = 0 := by omega
    omega
  · exact Or.inl h
  · have : u % 2 = 0 := by omega
    omega
  · exact Or.inr h

lemma hilbertε_eq_one_iff {u : ℤ} (hu : Odd u) :
    hilbertε u = 1 ↔ u % 4 = 3 := by
  have h01 : hilbertε u = 0 ∨ hilbertε u = 1 := by
    unfold hilbertε; omega
  have hmod := odd_mod_four hu
  constructor
  · intro h
    rcases hmod with hmod | hmod
    · have : hilbertε u = 0 := (hilbertε_eq_zero_iff hu).mpr hmod
      omega
    · exact hmod
  · intro h
    rcases h01 with h01 | h01
    · have : u % 4 = 1 := (hilbertε_eq_zero_iff hu).mp h01
      omega
    · exact h01

lemma hilbertε_mul_odd {u v : ℤ} (hu : Odd u) (hv : Odd v) :
    hilbertε (u * v) = (hilbertε u + hilbertε v) % 2 := by
  have huv : Odd (u * v) := hu.mul hv
  have hu4 : u % 4 = 1 ∨ u % 4 = 3 := by
    by_cases h : hilbertε u = 0
    · exact Or.inl ((hilbertε_eq_zero_iff hu).mp h)
    · have : hilbertε u = 1 := by unfold hilbertε at h ⊢; omega
      exact Or.inr ((hilbertε_eq_one_iff hu).mp this)
  have hv4 : v % 4 = 1 ∨ v % 4 = 3 := by
    by_cases h : hilbertε v = 0
    · exact Or.inl ((hilbertε_eq_zero_iff hv).mp h)
    · have : hilbertε v = 1 := by unfold hilbertε at h ⊢; omega
      exact Or.inr ((hilbertε_eq_one_iff hv).mp this)
  rcases hu4 with hu4 | hu4 <;> rcases hv4 with hv4 | hv4
  · have : (u * v) % 4 = 1 := by rw [Int.mul_emod, hu4, hv4]; decide
    have hε : hilbertε (u * v) = 0 := (hilbertε_eq_zero_iff huv).mpr this
    have h1 : hilbertε u = 0 := (hilbertε_eq_zero_iff hu).mpr hu4
    have h2 : hilbertε v = 0 := (hilbertε_eq_zero_iff hv).mpr hv4
    simp [hε, h1, h2]
  · have : (u * v) % 4 = 3 := by rw [Int.mul_emod, hu4, hv4]; decide
    have hε : hilbertε (u * v) = 1 := (hilbertε_eq_one_iff huv).mpr this
    have h1 : hilbertε u = 0 := (hilbertε_eq_zero_iff hu).mpr hu4
    have h2 : hilbertε v = 1 := (hilbertε_eq_one_iff hv).mpr hv4
    simp [hε, h1, h2]
  · have : (u * v) % 4 = 3 := by rw [Int.mul_emod, hu4, hv4]; decide
    have hε : hilbertε (u * v) = 1 := (hilbertε_eq_one_iff huv).mpr this
    have h1 : hilbertε u = 1 := (hilbertε_eq_one_iff hu).mpr hu4
    have h2 : hilbertε v = 0 := (hilbertε_eq_zero_iff hv).mpr hv4
    simp [hε, h1, h2]
  · have : (u * v) % 4 = 1 := by rw [Int.mul_emod, hu4, hv4]; decide
    have hε : hilbertε (u * v) = 0 := (hilbertε_eq_zero_iff huv).mpr this
    have h1 : hilbertε u = 1 := (hilbertε_eq_one_iff hu).mpr hu4
    have h2 : hilbertε v = 1 := (hilbertε_eq_one_iff hv).mpr hv4
    simp [hε, h1, h2]

lemma odd_mod_eight {u : ℤ} (hu : Odd u) :
    u % 8 = 1 ∨ u % 8 = 3 ∨ u % 8 = 5 ∨ u % 8 = 7 := by
  have h2 : u % 2 = 1 := Int.odd_iff.mp hu
  have : u % 8 = 0 ∨ u % 8 = 1 ∨ u % 8 = 2 ∨ u % 8 = 3 ∨
         u % 8 = 4 ∨ u % 8 = 5 ∨ u % 8 = 6 ∨ u % 8 = 7 := by omega
  rcases this with h | h | h | h | h | h | h | h
  · omega
  · exact Or.inl h
  · omega
  · exact Or.inr (Or.inl h)
  · omega
  · exact Or.inr (Or.inr (Or.inl h))
  · omega
  · exact Or.inr (Or.inr (Or.inr h))

lemma eight_dvd_odd_sq_sub_one {u : ℤ} (hu : Odd u) : (8 : ℤ) ∣ u ^ 2 - 1 := by
  obtain ⟨k, rfl⟩ := hu
  have heven : Even (k * (k + 1) : ℤ) := Int.even_mul_succ_self k
  obtain ⟨t, ht⟩ := heven
  have ht' : k * (k + 1) = 2 * t := by omega
  refine ⟨t, ?_⟩
  have : (2 * k + 1 : ℤ) ^ 2 - 1 = 4 * (k * (k + 1)) := by ring
  rw [this, ht']; ring

lemma hilbertω_eq_zero_iff {u : ℤ} (hu : Odd u) :
    hilbertω u = 0 ↔ u % 8 = 1 ∨ u % 8 = 7 := by
  have h8 : (8 : ℤ) ∣ u ^ 2 - 1 := eight_dvd_odd_sq_sub_one hu
  unfold hilbertω
  have hdiv : ((u ^ 2 - 1) / 8) * 8 = u ^ 2 - 1 := Int.ediv_mul_cancel h8
  have hparity : ((u ^ 2 - 1) / 8).natAbs % 2 = 0 ↔ Even ((u ^ 2 - 1) / 8) := by
    constructor
    · intro h; exact (even_iff_natAbs_even _).mpr (Nat.even_iff.mpr h)
    · intro h; exact Nat.even_iff.mp ((even_iff_natAbs_even _).mp h)
  have heven16 : Even ((u ^ 2 - 1) / 8) ↔ (16 : ℤ) ∣ u ^ 2 - 1 := by
    constructor
    · intro h
      obtain ⟨t, ht⟩ := h
      have ht2 : (u ^ 2 - 1) / 8 = 2 * t := by omega
      refine ⟨t, ?_⟩
      calc u ^ 2 - 1 = ((u ^ 2 - 1) / 8) * 8 := hdiv.symm
        _ = (2 * t) * 8 := by rw [ht2]
        _ = 16 * t := by ring
    · intro ⟨t, ht⟩
      have : (u ^ 2 - 1) / 8 = 2 * t := by
        have hmul : u ^ 2 - 1 = 8 * (2 * t) := by rw [ht]; ring
        rw [hmul, Int.mul_ediv_cancel_left _ (by decide)]
      exact ⟨t, by omega⟩
  -- u^2 ≡ 1 mod 16 iff u ≡ 1 or 7 or 9 or 15 mod 16, which for odd u is ≡1 or 7 mod 8
  have h16 : (16 : ℤ) ∣ u ^ 2 - 1 ↔ u % 8 = 1 ∨ u % 8 = 7 := by
    have hmod := odd_mod_eight hu
    constructor
    · intro hdvd
      have : u ^ 2 % 16 = 1 := by
        have := Int.emod_eq_zero_of_dvd hdvd
        have : (u ^ 2 - 1) % 16 = 0 := this
        omega
      rcases hmod with h8 | h8 | h8 | h8
      · exact Or.inl h8
      · -- u ≡ 3 mod 8 ⇒ u ≡ 3 or 11 mod 16, square ≡ 9
        have : u % 16 = 3 ∨ u % 16 = 11 := by omega
        have hsq : u ^ 2 % 16 = 9 := by
          rw [pow_two, Int.mul_emod]
          rcases this with hu16 | hu16 <;> rw [hu16] <;> decide
        omega
      · -- u ≡ 5 mod 8 ⇒ u ≡ 5 or 13 mod 16, square ≡ 9
        have : u % 16 = 5 ∨ u % 16 = 13 := by omega
        have hsq : u ^ 2 % 16 = 9 := by
          rw [pow_two, Int.mul_emod]
          rcases this with hu16 | hu16 <;> rw [hu16] <;> decide
        omega
      · exact Or.inr h8
    · intro h
      rcases h with h8 | h8
      · -- u ≡ 1 mod 8 ⇒ u ≡ 1 or 9 mod 16, square ≡ 1
        have : u % 16 = 1 ∨ u % 16 = 9 := by omega
        have hsq : u ^ 2 % 16 = 1 := by
          rw [pow_two, Int.mul_emod]
          rcases this with hu16 | hu16 <;> rw [hu16] <;> decide
        exact Int.dvd_of_emod_eq_zero (by omega)
      · -- u ≡ 7 mod 8 ⇒ u ≡ 7 or 15 mod 16, square ≡ 1
        have : u % 16 = 7 ∨ u % 16 = 15 := by omega
        have hsq : u ^ 2 % 16 = 1 := by
          rw [pow_two, Int.mul_emod]
          rcases this with hu16 | hu16 <;> rw [hu16] <;> decide
        exact Int.dvd_of_emod_eq_zero (by omega)
  exact hparity.trans (heven16.trans h16)

lemma hilbertω_eq_one_iff {u : ℤ} (hu : Odd u) :
    hilbertω u = 1 ↔ u % 8 = 3 ∨ u % 8 = 5 := by
  have h01 : hilbertω u = 0 ∨ hilbertω u = 1 := by
    unfold hilbertω; omega
  have hmod := odd_mod_eight hu
  constructor
  · intro h
    rcases hmod with h8 | h8 | h8 | h8
    · have : hilbertω u = 0 := (hilbertω_eq_zero_iff hu).mpr (Or.inl h8)
      omega
    · exact Or.inl h8
    · exact Or.inr h8
    · have : hilbertω u = 0 := (hilbertω_eq_zero_iff hu).mpr (Or.inr h8)
      omega
  · intro h
    rcases h01 with h01 | h01
    · have : u % 8 = 1 ∨ u % 8 = 7 := (hilbertω_eq_zero_iff hu).mp h01
      omega
    · exact h01

lemma hilbertω_mul_odd {u v : ℤ} (hu : Odd u) (hv : Odd v) :
    hilbertω (u * v) = (hilbertω u + hilbertω v) % 2 := by
  have huv : Odd (u * v) := hu.mul hv
  have fu : hilbertω u = 0 ∨ hilbertω u = 1 := by unfold hilbertω; omega
  have fv : hilbertω v = 0 ∨ hilbertω v = 1 := by unfold hilbertω; omega
  -- multiply residues mod 8
  have hu8 := odd_mod_eight hu
  have hv8 := odd_mod_eight hv
  rcases hu8 with hu8 | hu8 | hu8 | hu8 <;> rcases hv8 with hv8 | hv8 | hv8 | hv8
  all_goals
    have hmul : (u * v) % 8 = (u % 8 * (v % 8)) % 8 := Int.mul_emod _ _ _
    try simp [hu8, hv8] at hmul
  · -- 1*1=1
    have hε : hilbertω (u * v) = 0 :=
      (hilbertω_eq_zero_iff huv).mpr (Or.inl (by omega))
    have h1 : hilbertω u = 0 := (hilbertω_eq_zero_iff hu).mpr (Or.inl hu8)
    have h2 : hilbertω v = 0 := (hilbertω_eq_zero_iff hv).mpr (Or.inl hv8)
    simp [hε, h1, h2]
  · -- 1*3=3
    have hε : hilbertω (u * v) = 1 :=
      (hilbertω_eq_one_iff huv).mpr (Or.inl (by omega))
    have h1 : hilbertω u = 0 := (hilbertω_eq_zero_iff hu).mpr (Or.inl hu8)
    have h2 : hilbertω v = 1 := (hilbertω_eq_one_iff hv).mpr (Or.inl hv8)
    simp [hε, h1, h2]
  · -- 1*5=5
    have hε : hilbertω (u * v) = 1 :=
      (hilbertω_eq_one_iff huv).mpr (Or.inr (by omega))
    have h1 : hilbertω u = 0 := (hilbertω_eq_zero_iff hu).mpr (Or.inl hu8)
    have h2 : hilbertω v = 1 := (hilbertω_eq_one_iff hv).mpr (Or.inr hv8)
    simp [hε, h1, h2]
  · -- 1*7=7
    have hε : hilbertω (u * v) = 0 :=
      (hilbertω_eq_zero_iff huv).mpr (Or.inr (by omega))
    have h1 : hilbertω u = 0 := (hilbertω_eq_zero_iff hu).mpr (Or.inl hu8)
    have h2 : hilbertω v = 0 := (hilbertω_eq_zero_iff hv).mpr (Or.inr hv8)
    simp [hε, h1, h2]
  · -- 3*1=3
    have hε : hilbertω (u * v) = 1 :=
      (hilbertω_eq_one_iff huv).mpr (Or.inl (by omega))
    have h1 : hilbertω u = 1 := (hilbertω_eq_one_iff hu).mpr (Or.inl hu8)
    have h2 : hilbertω v = 0 := (hilbertω_eq_zero_iff hv).mpr (Or.inl hv8)
    simp [hε, h1, h2]
  · -- 3*3=9≡1
    have hε : hilbertω (u * v) = 0 :=
      (hilbertω_eq_zero_iff huv).mpr (Or.inl (by omega))
    have h1 : hilbertω u = 1 := (hilbertω_eq_one_iff hu).mpr (Or.inl hu8)
    have h2 : hilbertω v = 1 := (hilbertω_eq_one_iff hv).mpr (Or.inl hv8)
    simp [hε, h1, h2]
  · -- 3*5=15≡7
    have hε : hilbertω (u * v) = 0 :=
      (hilbertω_eq_zero_iff huv).mpr (Or.inr (by omega))
    have h1 : hilbertω u = 1 := (hilbertω_eq_one_iff hu).mpr (Or.inl hu8)
    have h2 : hilbertω v = 1 := (hilbertω_eq_one_iff hv).mpr (Or.inr hv8)
    simp [hε, h1, h2]
  · -- 3*7=21≡5
    have hε : hilbertω (u * v) = 1 :=
      (hilbertω_eq_one_iff huv).mpr (Or.inr (by omega))
    have h1 : hilbertω u = 1 := (hilbertω_eq_one_iff hu).mpr (Or.inl hu8)
    have h2 : hilbertω v = 0 := (hilbertω_eq_zero_iff hv).mpr (Or.inr hv8)
    simp [hε, h1, h2]
  · -- 5*1=5
    have hε : hilbertω (u * v) = 1 :=
      (hilbertω_eq_one_iff huv).mpr (Or.inr (by omega))
    have h1 : hilbertω u = 1 := (hilbertω_eq_one_iff hu).mpr (Or.inr hu8)
    have h2 : hilbertω v = 0 := (hilbertω_eq_zero_iff hv).mpr (Or.inl hv8)
    simp [hε, h1, h2]
  · -- 5*3=15≡7
    have hε : hilbertω (u * v) = 0 :=
      (hilbertω_eq_zero_iff huv).mpr (Or.inr (by omega))
    have h1 : hilbertω u = 1 := (hilbertω_eq_one_iff hu).mpr (Or.inr hu8)
    have h2 : hilbertω v = 1 := (hilbertω_eq_one_iff hv).mpr (Or.inl hv8)
    simp [hε, h1, h2]
  · -- 5*5=25≡1
    have hε : hilbertω (u * v) = 0 :=
      (hilbertω_eq_zero_iff huv).mpr (Or.inl (by omega))
    have h1 : hilbertω u = 1 := (hilbertω_eq_one_iff hu).mpr (Or.inr hu8)
    have h2 : hilbertω v = 1 := (hilbertω_eq_one_iff hv).mpr (Or.inr hv8)
    simp [hε, h1, h2]
  · -- 5*7=35≡3
    have hε : hilbertω (u * v) = 1 :=
      (hilbertω_eq_one_iff huv).mpr (Or.inl (by omega))
    have h1 : hilbertω u = 1 := (hilbertω_eq_one_iff hu).mpr (Or.inr hu8)
    have h2 : hilbertω v = 0 := (hilbertω_eq_zero_iff hv).mpr (Or.inr hv8)
    simp [hε, h1, h2]
  · -- 7*1=7
    have hε : hilbertω (u * v) = 0 :=
      (hilbertω_eq_zero_iff huv).mpr (Or.inr (by omega))
    have h1 : hilbertω u = 0 := (hilbertω_eq_zero_iff hu).mpr (Or.inr hu8)
    have h2 : hilbertω v = 0 := (hilbertω_eq_zero_iff hv).mpr (Or.inl hv8)
    simp [hε, h1, h2]
  · -- 7*3=21≡5
    have hε : hilbertω (u * v) = 1 :=
      (hilbertω_eq_one_iff huv).mpr (Or.inr (by omega))
    have h1 : hilbertω u = 0 := (hilbertω_eq_zero_iff hu).mpr (Or.inr hu8)
    have h2 : hilbertω v = 1 := (hilbertω_eq_one_iff hv).mpr (Or.inl hv8)
    simp [hε, h1, h2]
  · -- 7*5=35≡3
    have hε : hilbertω (u * v) = 1 :=
      (hilbertω_eq_one_iff huv).mpr (Or.inl (by omega))
    have h1 : hilbertω u = 0 := (hilbertω_eq_zero_iff hu).mpr (Or.inr hu8)
    have h2 : hilbertω v = 1 := (hilbertω_eq_one_iff hv).mpr (Or.inr hv8)
    simp [hε, h1, h2]
  · -- 7*7=49≡1
    have hε : hilbertω (u * v) = 0 :=
      (hilbertω_eq_zero_iff huv).mpr (Or.inl (by omega))
    have h1 : hilbertω u = 0 := (hilbertω_eq_zero_iff hu).mpr (Or.inr hu8)
    have h2 : hilbertω v = 0 := (hilbertω_eq_zero_iff hv).mpr (Or.inr hv8)
    simp [hε, h1, h2]

lemma hilbertOdd_mul {p : ℕ} [Fact p.Prime] {a b c : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    hilbertOdd p a (b * c) = hilbertOdd p a b * hilbertOdd p a c := by
  unfold hilbertOdd
  have hval : padicValInt p (b * c) = padicValInt p b + padicValInt p c :=
    padicValInt.mul hb hc
  have hunit : pUnit p (b * c) = pUnit p b * pUnit p c := pUnit_mul hb hc
  simp only [hval, hunit, jacobiSym.mul_left]
  ring

lemma neg_one_pow_nat_mod_two (n : ℕ) : (-1 : ℤ) ^ n = (-1 : ℤ) ^ (n % 2) := by
  calc (-1 : ℤ) ^ n = (-1 : ℤ) ^ (2 * (n / 2) + n % 2) := by rw [Nat.div_add_mod]
    _ = ((-1 : ℤ) ^ 2) ^ (n / 2) * (-1 : ℤ) ^ (n % 2) := by rw [pow_add, pow_mul]
    _ = 1 ^ (n / 2) * (-1 : ℤ) ^ (n % 2) := by rw [neg_one_pow_two]
    _ = (-1 : ℤ) ^ (n % 2) := by simp

lemma neg_one_pow_nat_congr {m n : ℕ} (h : m % 2 = n % 2) :
    (-1 : ℤ) ^ m = (-1 : ℤ) ^ n := by
  rw [neg_one_pow_nat_mod_two m, neg_one_pow_nat_mod_two n, h]

lemma hilbertTwo_mul {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    hilbertTwo a (b * c) = hilbertTwo a b * hilbertTwo a c := by
  unfold hilbertTwo
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hval : padicValInt 2 (b * c) = padicValInt 2 b + padicValInt 2 c :=
    padicValInt.mul hb hc
  have hodd : oddPart (b * c) = oddPart b * oddPart c := oddPart_mul hb hc
  rw [hval, hodd]
  have hε : hilbertε (oddPart b * oddPart c) =
      (hilbertε (oddPart b) + hilbertε (oddPart c)) % 2 :=
    hilbertε_mul_odd (oddPart_odd hb) (oddPart_odd hc)
  have hω : hilbertω (oddPart b * oddPart c) =
      (hilbertω (oddPart b) + hilbertω (oddPart c)) % 2 :=
    hilbertω_mul_odd (oddPart_odd hb) (oddPart_odd hc)
  set εa := hilbertε (oddPart a) with hεa
  set εb := hilbertε (oddPart b) with hεb
  set εc := hilbertε (oddPart c) with hεc
  set ωa := hilbertω (oddPart a) with hωa
  set ωb := hilbertω (oddPart b) with hωb
  set ωc := hilbertω (oddPart c) with hωc
  set α := padicValInt 2 a
  set βb := padicValInt 2 b
  set βc := padicValInt 2 c
  have hpar : (εa * ((εb + εc) % 2) + α * ((ωb + ωc) % 2) + (βb + βc) * ωa) % 2 =
      (εa * εb + α * ωb + βb * ωa + (εa * εc + α * ωc + βc * ωa)) % 2 := by
    change _ ≡ _ [MOD 2]
    have h1 : εa * ((εb + εc) % 2) ≡ εa * (εb + εc) [MOD 2] :=
      Nat.ModEq.mul_left _ (Nat.mod_modEq _ 2)
    have h2 : α * ((ωb + ωc) % 2) ≡ α * (ωb + ωc) [MOD 2] :=
      Nat.ModEq.mul_left _ (Nat.mod_modEq _ 2)
    have h3 : (βb + βc) * ωa ≡ βb * ωa + βc * ωa [MOD 2] := by
      rw [add_mul]
    have hsum := (h1.add h2).add h3
    have hr : εa * (εb + εc) + α * (ωb + ωc) + (βb * ωa + βc * ωa) =
        εa * εb + α * ωb + βb * ωa + (εa * εc + α * ωc + βc * ωa) := by ring
    rwa [hr] at hsum
  have hpow1 : (-1 : ℤ) ^ (εa * hilbertε (oddPart b * oddPart c) +
      α * hilbertω (oddPart b * oddPart c) + (βb + βc) * ωa) =
      (-1 : ℤ) ^ (εa * εb + α * ωb + βb * ωa + (εa * εc + α * ωc + βc * ωa)) := by
    rw [hε, hω]
    exact neg_one_pow_nat_congr hpar
  have hpow2 : (-1 : ℤ) ^ (εa * εb + α * ωb + βb * ωa + (εa * εc + α * ωc + βc * ωa)) =
      (-1 : ℤ) ^ (εa * εb + α * ωb + βb * ωa) *
      (-1 : ℤ) ^ (εa * εc + α * ωc + βc * ωa) :=
    pow_add (-1 : ℤ) _ _
  rw [hpow1, hpow2]

lemma padicValInt_eq_zero_of_not_dvd {p : ℕ} [Fact p.Prime] {z : ℤ}
    (hz : z ≠ 0) (h : ¬ (p : ℤ) ∣ z) : padicValInt p z = 0 := by
  rw [padicValInt.eq_zero_iff]
  exact Or.inr (Or.inr h)

lemma not_dvd_of_padicValInt_eq_zero {p : ℕ} [Fact p.Prime] {z : ℤ}
    (hz : z ≠ 0) (h : padicValInt p z = 0) : ¬ (p : ℤ) ∣ z := by
  have := padicValInt.eq_zero_iff.mp h
  rcases this with hp1 | hz0 | hnd
  · exact absurd hp1 (Fact.out : p.Prime).ne_one
  · exact absurd hz0 hz
  · exact hnd

lemma dvd_of_padicValInt_ne_zero {p : ℕ} [Fact p.Prime] {z : ℤ}
    (h : padicValInt p z ≠ 0) : (p : ℤ) ∣ z := by
  have := padicValInt.eq_zero_iff (p := p) (z := z)
  have : ¬ (p = 1 ∨ z = 0 ∨ ¬ (p : ℤ) ∣ z) := by
    rw [← this]; exact h
  push_neg at this
  exact this.2.2

lemma pUnit_eq_self_of_val_zero {p : ℕ} {z : ℤ} (h : padicValInt p z = 0) :
    pUnit p z = z := by
  unfold pUnit
  rw [h, pow_zero]
  exact Int.ediv_one z

lemma jacobiSym_of_emodeq {p : ℕ} {x y : ℤ} (h : x % p = y % p) :
    jacobiSym x p = jacobiSym y p :=
  jacobiSym.mod_left' h

lemma jacobiSym_sq_unit (p : ℕ) [hp : Fact p.Prime] {s : ℤ} (hs : ¬ (p : ℤ) ∣ s) :
    jacobiSym (s ^ 2) p = 1 := by
  have hgcd : s.gcd p = 1 := by
    rw [Int.gcd_def, Nat.gcd_comm]
    refine (Nat.Prime.coprime_iff_not_dvd hp.out).2 ?_
    intro hd
    exact hs (Int.natCast_dvd.mpr hd)
  exact jacobiSym.sq_one' hgcd

lemma one_emod_of_one_lt {p : ℕ} (hp : 1 < p) : (1 : ℤ) % p = 1 :=
  Int.emod_eq_of_lt (by omega) (by omega)

lemma emod_eq_one_of_sub_dvd {p : ℕ} {a : ℤ}
    (h : (p : ℤ) ∣ (1 - a)) : a % p = 1 % p := by
  have : a ≡ (1 : ℤ) [ZMOD p] := (Int.modEq_iff_dvd).mpr h
  exact Int.ModEq.eq this

lemma emod_sub_of_dvd_right {p : ℕ} {x a : ℤ} (h : (p : ℤ) ∣ a) :
    (x - a) % p = x % p := by
  have : a % p = 0 := Int.emod_eq_zero_of_dvd h
  rw [Int.sub_emod, this, sub_zero, Int.emod_emod]

lemma hilbertOdd_steinberg {p : ℕ} [hp : Fact p.Prime]
    {a : ℤ} (ha : a ≠ 0) (ha1 : 1 - a ≠ 0) :
    hilbertOdd p a (1 - a) = 1 := by
  unfold hilbertOdd
  set α := padicValInt p a
  set β := padicValInt p (1 - a)
  have hnotboth : ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ (1 - a)) := by
    intro ⟨h1, h2⟩
    have : (p : ℤ) ∣ (1 : ℤ) := by
      convert h1.add h2 using 1; ring
    exact (Fact.out : p.Prime).not_dvd_one (Int.natCast_dvd_natCast.mp (by simpa using this))
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  by_cases hα : α = 0
  · simp [hα]
    by_cases hβ : β = 0
    · simp [hβ]
    · have hpd : (p : ℤ) ∣ (1 - a) := dvd_of_padicValInt_ne_zero hβ
      have hjac : jacobiSym (pUnit p a) p = jacobiSym 1 p := by
        rw [pUnit_eq_self_of_val_zero hα]
        exact jacobiSym_of_emodeq (emod_eq_one_of_sub_dvd hpd)
      simp [hjac, jacobiSym.one_left]
  · have hpd : (p : ℤ) ∣ a := dvd_of_padicValInt_ne_zero hα
    have hnd : ¬ (p : ℤ) ∣ (1 - a) := fun h => hnotboth ⟨hpd, h⟩
    have hβ : β = 0 := padicValInt_eq_zero_of_not_dvd ha1 hnd
    simp [hβ]
    have hjac : jacobiSym (pUnit p (1 - a)) p = jacobiSym 1 p := by
      rw [pUnit_eq_self_of_val_zero hβ]
      have : (1 - a) % p = 1 % p := by
        have : a % p = 0 := Int.emod_eq_zero_of_dvd hpd
        rw [Int.sub_emod, this, sub_zero, Int.emod_emod]
      exact jacobiSym_of_emodeq this
    simp [hjac, jacobiSym.one_left]

lemma padicValInt_neg (p : ℕ) (a : ℤ) : padicValInt p (-a) = padicValInt p a := by
  simp [padicValInt]

lemma pUnit_neg {p : ℕ} {a : ℤ} (ha : a ≠ 0) :
    pUnit p (-a) = -pUnit p a := by
  unfold pUnit
  rw [padicValInt_neg]
  exact Int.neg_ediv_of_dvd (p_pow_dvd_self p a)

lemma jacobiSym_neg (a : ℤ) (p : ℕ) :
    jacobiSym (-a) p = jacobiSym (-1) p * jacobiSym a p := by
  simpa using jacobiSym.mul_left (-1) a p

lemma jacobiSym_neg_one_odd_prime {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    jacobiSym (-1) p = (-1 : ℤ) ^ (p / 2) := by
  have hodd : Odd p := Nat.Prime.odd_of_ne_two Fact.out hp2
  rw [jacobiSym.at_neg_one hodd]
  exact ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hodd)

lemma padicValInt_pow {p : ℕ} [Fact p.Prime] {a : ℤ} (ha : a ≠ 0) (n : ℕ) :
    padicValInt p (a ^ n) = n * padicValInt p a := by
  induction n with
  | zero => simp [padicValInt]
  | succ n ih =>
    rw [pow_succ, padicValInt.mul (pow_ne_zero n ha) ha, ih, Nat.succ_mul, add_comm]

lemma padicValInt_add_eq_of_lt {p : ℕ} [Fact p.Prime] {x y : ℤ}
    (hx : x ≠ 0) (hxy : x + y ≠ 0)
    (h : padicValInt p x < padicValInt p y ∨ y = 0) :
    padicValInt p (x + y) = padicValInt p x := by
  rcases h with hlt | rfl
  · have hvx : (p : ℤ) ^ padicValInt p x ∣ x := p_pow_dvd_self p x
    have hvx1 : ¬ (p : ℤ) ^ (padicValInt p x + 1) ∣ x := by
      intro hd
      have : padicValInt p x + 1 ≤ padicValInt p x :=
        (padicValInt_dvd_iff (p := p) (padicValInt p x + 1) x).mp hd |>.resolve_left hx
      omega
    have hvy : (p : ℤ) ^ (padicValInt p x + 1) ∣ y := by
      have : padicValInt p x + 1 ≤ padicValInt p y := Nat.succ_le_of_lt hlt
      exact (padicValInt_dvd_iff (p := p) (padicValInt p x + 1) y).mpr (Or.inr this)
    have hsum : (p : ℤ) ^ padicValInt p x ∣ (x + y) :=
      dvd_add hvx ((pow_dvd_pow (p : ℤ) (Nat.le_succ _)).trans hvy)
    have hsum1 : ¬ (p : ℤ) ^ (padicValInt p x + 1) ∣ (x + y) := by
      intro hd
      exact hvx1 (by
        have := dvd_sub hd hvy
        simpa [add_sub_cancel_right] using this)
    have hle : padicValInt p x ≤ padicValInt p (x + y) :=
      (padicValInt_dvd_iff (p := p) (padicValInt p x) (x + y)).mp hsum |>.resolve_left hxy
    have hnlt : ¬ padicValInt p x + 1 ≤ padicValInt p (x + y) := fun h' =>
      hsum1 ((padicValInt_dvd_iff (p := p) (padicValInt p x + 1) (x + y)).mpr (Or.inr h'))
    omega
  · simp

lemma pUnit_add_emodeq {p : ℕ} [Fact p.Prime] {x y : ℤ}
    (hx : x ≠ 0) (hxy : x + y ≠ 0)
    (h : padicValInt p x < padicValInt p y ∨ y = 0) :
    pUnit p (x + y) % p = pUnit p x % p := by
  have hval := padicValInt_add_eq_of_lt hx hxy h
  have hxpow := pUnit_mul_pow p x
  have hxy_pow := pUnit_mul_pow p (x + y)
  have hdecomp : pUnit p (x + y) * (p : ℤ) ^ padicValInt p x =
      pUnit p x * (p : ℤ) ^ padicValInt p x + y := by
    calc
      pUnit p (x + y) * (p : ℤ) ^ padicValInt p x
          = pUnit p (x + y) * (p : ℤ) ^ padicValInt p (x + y) := by rw [hval]
      _ = x + y := hxy_pow
      _ = pUnit p x * (p : ℤ) ^ padicValInt p x + y := by rw [hxpow]
  have hdiff :
      (pUnit p (x + y) - pUnit p x) * (p : ℤ) ^ padicValInt p x = y := by
    linarith
  have hpd : (p : ℤ) ∣ (pUnit p (x + y) - pUnit p x) := by
    rcases h with hlt | rfl
    · have hpy : (p : ℤ) ^ (padicValInt p x + 1) ∣ y := by
        have : padicValInt p x + 1 ≤ padicValInt p y := Nat.succ_le_of_lt hlt
        exact (padicValInt_dvd_iff (p := p) (padicValInt p x + 1) y).mpr (Or.inr this)
      obtain ⟨k, hk⟩ := hpy
      have hne : (p : ℤ) ^ padicValInt p x ≠ 0 :=
        pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
      have : pUnit p (x + y) - pUnit p x = p * k := by
        apply mul_right_cancel₀ hne
        calc
          (pUnit p (x + y) - pUnit p x) * (p : ℤ) ^ padicValInt p x
              = y := hdiff
          _ = (p : ℤ) ^ (padicValInt p x + 1) * k := hk
          _ = (p * k) * (p : ℤ) ^ padicValInt p x := by rw [pow_succ]; ring
      exact ⟨k, this⟩
    · simp
  have : pUnit p (x + y) ≡ pUnit p x [ZMOD p] :=
    (Int.modEq_iff_dvd).mpr (by
      have : (p : ℤ) ∣ (pUnit p x - pUnit p (x + y)) := by
        simpa [neg_sub] using (dvd_neg.mpr hpd)
      exact this)
  exact Int.ModEq.eq this

lemma even_mul_succ_mul (n k : ℕ) : Even (n * (n + 1) * k) :=
  (Nat.even_mul_succ_self n).mul_right k

lemma neg_one_pow_steinberg (n k : ℕ) :
    ((-1 : ℤ) ^ k) ^ n * (-1 : ℤ) ^ (n * n * k) = 1 := by
  rw [← pow_mul, ← pow_add]
  have : k * n + n * n * k = n * (n + 1) * k := by ring
  rw [this]
  exact Even.neg_one_pow (even_mul_succ_mul n k)

lemma jac_mul_neg_pow {p : ℕ} {u : ℤ} {n : ℕ}
    (hJ2 : jacobiSym u p ^ 2 = 1)
    (hχ : jacobiSym (-1) p = (-1 : ℤ) ^ (p / 2)) :
    jacobiSym u p ^ n * jacobiSym (-u) p ^ n * (-1 : ℤ) ^ (n * n * (p / 2)) = 1 := by
  rw [jacobiSym_neg u p, hχ]
  have hre :
      jacobiSym u p ^ n * ((-1 : ℤ) ^ (p / 2) * jacobiSym u p) ^ n *
        (-1 : ℤ) ^ (n * n * (p / 2)) =
      (jacobiSym u p ^ n * jacobiSym u p ^ n) *
        (((-1 : ℤ) ^ (p / 2)) ^ n * (-1 : ℤ) ^ (n * n * (p / 2))) := by
    rw [mul_pow]; ring
  rw [hre]
  have h1 : jacobiSym u p ^ n * jacobiSym u p ^ n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, hJ2]; simp
  rw [h1, neg_one_pow_steinberg, one_mul]

lemma jacobi_pow_of_even {p : ℕ} {u : ℤ} {n : ℕ}
    (hJ2 : jacobiSym u p ^ 2 = 1) (hen : Even n) :
    jacobiSym u p ^ n = 1 := by
  obtain ⟨k, hk⟩ := hen
  rw [hk, ← two_mul, pow_mul, hJ2]
  simp

lemma even_of_eq_two_mul {n k : ℕ} (h : n = 2 * k) : Even n :=
  h ▸ even_two_mul k

lemma hilbertOdd_s_sq_sub {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {a s : ℤ} (ha : a ≠ 0) (hs : s ^ 2 - a ≠ 0) :
    hilbertOdd p a (s ^ 2 - a) = 1 := by
  unfold hilbertOdd
  set α := padicValInt p a
  set β := padicValInt p (s ^ 2 - a)
  by_cases hα : α = 0
  · simp [hα]
    by_cases hβ : β = 0
    · simp [hβ]
    · have hpd : (p : ℤ) ∣ (s ^ 2 - a) := dvd_of_padicValInt_ne_zero hβ
      have hnda := not_dvd_of_padicValInt_eq_zero ha hα
      have hjac : jacobiSym (pUnit p a) p = jacobiSym (s ^ 2) p := by
        rw [pUnit_eq_self_of_val_zero hα]
        have : a % p = s ^ 2 % p := by
          have : a ≡ s ^ 2 [ZMOD p] := (Int.modEq_iff_dvd).mpr hpd
          exact Int.ModEq.eq this
        exact jacobiSym_of_emodeq this
      have hnds : ¬ (p : ℤ) ∣ s := by
        intro hds
        have : (p : ℤ) ∣ s ^ 2 := dvd_pow hds (by decide)
        exact hnda (by
          have := this.sub hpd; simpa using this)
      simp [hjac, jacobiSym_sq_unit p hnds]
  · by_cases hβ : β = 0
    · simp [hβ]
      have hnda := not_dvd_of_padicValInt_eq_zero hs hβ
      have hpd : (p : ℤ) ∣ a := dvd_of_padicValInt_ne_zero hα
      have hjac : jacobiSym (pUnit p (s ^ 2 - a)) p = jacobiSym (s ^ 2) p := by
        rw [pUnit_eq_self_of_val_zero hβ]
        exact jacobiSym_of_emodeq (emod_sub_of_dvd_right hpd)
      have hnds : ¬ (p : ℤ) ∣ s := by
        intro hds
        have : (p : ℤ) ∣ s ^ 2 := dvd_pow hds (by decide)
        exact hnda (dvd_sub this hpd)
      simp [hjac, jacobiSym_sq_unit p hnds]
    · have hpd_a : (p : ℤ) ∣ a := dvd_of_padicValInt_ne_zero hα
      have hpd_s2a : (p : ℤ) ∣ (s ^ 2 - a) := dvd_of_padicValInt_ne_zero hβ
      have hpd_s : (p : ℤ) ∣ s := by
        have hs2 : (p : ℤ) ∣ s ^ 2 := by
          have := hpd_s2a.add hpd_a
          simpa using this
        exact Int.Prime.dvd_pow' hp.out hs2
      by_cases hs0 : s = 0
      · subst hs0
        have hβeq : β = α := by
          change padicValInt p (0 ^ 2 - a) = padicValInt p a
          simp [padicValInt_neg]
        have hu : pUnit p (-a) = -pUnit p a := pUnit_neg ha
        simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_sub]
        rw [hβeq, hu]
        exact jac_mul_neg_pow (jacobiSym_pUnit_sq_eq_one ha)
          (jacobiSym_neg_one_odd_prime hp2)
      · have hγpos : padicValInt p s ≠ 0 := by
          intro h0
          exact (not_dvd_of_padicValInt_eq_zero hs0 h0) hpd_s
        have hs2ne : s ^ 2 ≠ 0 := pow_ne_zero 2 hs0
        have hvals2 : padicValInt p (s ^ 2) = 2 * padicValInt p s := by
          rw [pow_two, padicValInt.mul hs0 hs0, two_mul]
        have hunit_s : pUnit p (s ^ 2) = pUnit p s * pUnit p s := by
          simpa [pow_two] using pUnit_mul hs0 hs0
        rcases lt_trichotomy α (2 * padicValInt p s) with hlt | heq | hgt
        · -- α < 2γ: β = α and unit of s²-a ≡ -pUnit a
          have hy : padicValInt p (-a) < padicValInt p (s ^ 2) ∨ s ^ 2 = 0 := by
            left
            have hna : padicValInt p (-a) = α := padicValInt_neg p a
            omega
          have hsumne : (-a) + s ^ 2 ≠ 0 := by
            have : (-a) + s ^ 2 = s ^ 2 - a := by ring
            rwa [this]
          have hβeq : β = α := by
            have h1 : padicValInt p (s ^ 2 - a) = padicValInt p (-a + s ^ 2) := by
              congr 1; ring
            have h2 : padicValInt p (-a + s ^ 2) = padicValInt p (-a) :=
              padicValInt_add_eq_of_lt (neg_ne_zero.mpr ha) hsumne hy
            have h3 : padicValInt p (-a) = padicValInt p a := padicValInt_neg p a
            exact h1.trans (h2.trans h3)
          have hmod : pUnit p (s ^ 2 - a) % p = pUnit p (-a) % p := by
            have : s ^ 2 - a = (-a) + s ^ 2 := by ring
            rw [this]
            exact pUnit_add_emodeq (neg_ne_zero.mpr ha) hsumne hy
          have hjac : jacobiSym (pUnit p (s ^ 2 - a)) p = jacobiSym (-pUnit p a) p := by
            have : pUnit p (-a) = -pUnit p a := pUnit_neg ha
            rw [← this]
            exact jacobiSym_of_emodeq hmod
          simp only [hβeq]
          rw [hjac]
          exact jac_mul_neg_pow (jacobiSym_pUnit_sq_eq_one ha)
            (jacobiSym_neg_one_odd_prime hp2)
        · -- α = 2γ
          have hαeven : Even α := even_of_eq_two_mul heq
          have ht2u : s ^ 2 - a =
              (pUnit p s ^ 2 - pUnit p a) * (p : ℤ) ^ (2 * padicValInt p s) := by
            set γ := padicValInt p s
            set us := pUnit p s
            set ua := pUnit p a
            have hsdecomp : s = us * (p : ℤ) ^ γ := (pUnit_mul_pow p s).symm
            have hadecomp : a = ua * (p : ℤ) ^ α := (pUnit_mul_pow p a).symm
            rw [hsdecomp, hadecomp, heq]
            ring
          have hdiff0 : pUnit p s ^ 2 - pUnit p a ≠ 0 := by
            intro hz
            have : s ^ 2 - a = 0 := by
              rw [ht2u, hz]; simp
            exact hs this
          have hβform : β = padicValInt p (pUnit p s ^ 2 - pUnit p a) +
              2 * padicValInt p s := by
            have hpow0 : (p : ℤ) ^ (2 * padicValInt p s) ≠ 0 :=
              pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
            have hmul := padicValInt.mul (p := p) hdiff0 hpow0
            have hvpow : padicValInt p ((p : ℤ) ^ (2 * padicValInt p s)) =
                2 * padicValInt p s := by
              have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
              have hpow := padicValInt_pow (p := p) (a := (p : ℤ)) hp0 (2 * padicValInt p s)
              have hvself : padicValInt p (p : ℤ) = 1 := padicValInt.self hp.out.one_lt
              simpa [hvself] using hpow
            calc β = padicValInt p (s ^ 2 - a) := rfl
              _ = padicValInt p
                    ((pUnit p s ^ 2 - pUnit p a) * (p : ℤ) ^ (2 * padicValInt p s)) := by
                      rw [ht2u]
              _ = padicValInt p (pUnit p s ^ 2 - pUnit p a) +
                    padicValInt p ((p : ℤ) ^ (2 * padicValInt p s)) := hmul
              _ = padicValInt p (pUnit p s ^ 2 - pUnit p a) +
                    2 * padicValInt p s := by rw [hvpow]
          have hJ2 : jacobiSym (pUnit p a) p ^ 2 = 1 :=
            jacobiSym_pUnit_sq_eq_one ha
          have hJw2 : jacobiSym (pUnit p (s ^ 2 - a)) p ^ 2 = 1 :=
            jacobiSym_pUnit_sq_eq_one hs
          have hαpow : jacobiSym (pUnit p (s ^ 2 - a)) p ^ α = 1 :=
            jacobi_pow_of_even hJw2 hαeven
          have hsign : (-1 : ℤ) ^ (α * β * (p / 2)) = 1 :=
            Even.neg_one_pow ((hαeven.mul_right β).mul_right (p / 2))
          by_cases hEβ : Even β
          · have hupow : jacobiSym (pUnit p a) p ^ β = 1 :=
              jacobi_pow_of_even hJ2 hEβ
            simp [hαpow, hsign, hupow]
          · have hcancel : (p : ℤ) ∣ (pUnit p s ^ 2 - pUnit p a) := by
              have hpos : padicValInt p (pUnit p s ^ 2 - pUnit p a) ≠ 0 := by
                intro hz
                have : β = 2 * padicValInt p s := by
                  rw [hβform, hz, zero_add]
                exact hEβ (even_of_eq_two_mul this)
              exact dvd_of_padicValInt_ne_zero hpos
            have hmod : pUnit p a % p = (pUnit p s ^ 2) % p := by
              have : pUnit p a ≡ pUnit p s ^ 2 [ZMOD p] :=
                (Int.modEq_iff_dvd).mpr hcancel
              exact Int.ModEq.eq this
            have hnds : ¬ (p : ℤ) ∣ pUnit p s :=
              p_not_dvd_pUnit hp.out hs0
            have hjac : jacobiSym (pUnit p a) p = 1 := by
              have : jacobiSym (pUnit p a) p = jacobiSym (pUnit p s ^ 2) p :=
                jacobiSym_of_emodeq hmod
              rw [this]
              exact jacobiSym_sq_unit p hnds
            simp [hjac, hαpow, hsign]
        · -- 2γ < α: β = 2γ even, unit ≡ (pUnit s)²
          have hy : padicValInt p (s ^ 2) < padicValInt p (-a) ∨ (-a) = 0 := by
            left
            have hna : padicValInt p (-a) = α := padicValInt_neg p a
            omega
          have hsumne : s ^ 2 + (-a) ≠ 0 := by
            have : s ^ 2 + (-a) = s ^ 2 - a := by ring
            rwa [this]
          have hβeq : β = 2 * padicValInt p s := by
            have h1 : padicValInt p (s ^ 2 - a) = padicValInt p (s ^ 2 + -a) := rfl
            have h2 : padicValInt p (s ^ 2 + -a) = padicValInt p (s ^ 2) :=
              padicValInt_add_eq_of_lt hs2ne hsumne hy
            exact h1.trans (h2.trans hvals2)
          have hβeven : Even β := even_of_eq_two_mul hβeq
          have hJ2 : jacobiSym (pUnit p a) p ^ 2 = 1 :=
            jacobiSym_pUnit_sq_eq_one ha
          have hupow : jacobiSym (pUnit p a) p ^ β = 1 :=
            jacobi_pow_of_even hJ2 hβeven
          have hmod : pUnit p (s ^ 2 - a) % p = pUnit p (s ^ 2) % p := by
            have : s ^ 2 - a = s ^ 2 + (-a) := by ring
            rw [this]
            exact pUnit_add_emodeq hs2ne hsumne hy
          have hjac : jacobiSym (pUnit p (s ^ 2 - a)) p = 1 := by
            have : jacobiSym (pUnit p (s ^ 2 - a)) p = jacobiSym (pUnit p (s ^ 2)) p :=
              jacobiSym_of_emodeq hmod
            rw [this, hunit_s]
            have hnds : ¬ (p : ℤ) ∣ pUnit p s := p_not_dvd_pUnit hp.out hs0
            simpa [pow_two] using jacobiSym_sq_unit p hnds
          have hsign : (-1 : ℤ) ^ (α * β * (p / 2)) = 1 :=
            Even.neg_one_pow ((hβeven.mul_left α).mul_right (p / 2))
          simp [hupow, hjac, hsign]

lemma oddPart_neg {a : ℤ} (ha : a ≠ 0) : oddPart (-a) = -oddPart a := by
  unfold oddPart
  rw [padicValInt_neg]
  exact Int.neg_ediv_of_dvd (padicValInt_dvd (p := 2) a)

lemma hilbertε_neg {u : ℤ} (hu : Odd u) :
    hilbertε (-u) = if u % 4 = 1 then 1 else 0 := by
  have hneg : Odd (-u) := hu.neg
  have hu4 := odd_mod_four hu
  rcases hu4 with h1 | h3
  · have : (-u) % 4 = 3 := by omega
    have : hilbertε (-u) = 1 := (hilbertε_eq_one_iff hneg).mpr this
    simp [h1, this]
  · have : (-u) % 4 = 1 := by omega
    have : hilbertε (-u) = 0 := (hilbertε_eq_zero_iff hneg).mpr this
    simp [h3, this]

lemma hilbertω_neg {u : ℤ} (hu : Odd u) : hilbertω (-u) = hilbertω u := by
  unfold hilbertω
  have : (-u) ^ 2 = u ^ 2 := by ring
  rw [this]

lemma hilbertTwo_neg_self {a : ℤ} (ha : a ≠ 0) : hilbertTwo a (-a) = 1 := by
  have hu : Odd (oddPart a) := oddPart_odd ha
  have hεprod : hilbertε (oddPart a) * hilbertε (-oddPart a) = 0 := by
    have h4 := odd_mod_four hu
    rcases h4 with h1 | h3
    · have : hilbertε (oddPart a) = 0 := (hilbertε_eq_zero_iff hu).mpr h1
      simp [this]
    · have hneg : Odd (-oddPart a) := hu.neg
      have : (-oddPart a) % 4 = 1 := by omega
      have : hilbertε (-oddPart a) = 0 := (hilbertε_eq_zero_iff hneg).mpr this
      simp [this]
  have hω : hilbertω (-oddPart a) = hilbertω (oddPart a) := hilbertω_neg hu
  unfold hilbertTwo
  simp only [padicValInt_neg, oddPart_neg ha, hεprod, hω, zero_add]
  have : Even (padicValInt 2 a * hilbertω (oddPart a) +
      padicValInt 2 a * hilbertω (oddPart a)) :=
    ⟨padicValInt 2 a * hilbertω (oddPart a), by ring⟩
  exact Even.neg_one_pow this

/-- Squares modulo `n` via the Chinese Remainder Theorem. -/
lemma zmod_cast_int_fst {a b : ℕ} (hcop : a.Coprime b) (n : ℤ) :
    ((ZMod.chineseRemainder hcop) (n : ZMod (a * b))).1 = (n : ZMod a) := by
  simp [ZMod.chineseRemainder]

lemma zmod_cast_int_snd {a b : ℕ} (hcop : a.Coprime b) (n : ℤ) :
    ((ZMod.chineseRemainder hcop) (n : ZMod (a * b))).2 = (n : ZMod b) := by
  simp [ZMod.chineseRemainder]

lemma isSquare_mod_mul {a b : ℕ} (hcop : a.Coprime b) {n : ℤ}
    (h1 : IsSquare (n : ZMod a)) (h2 : IsSquare (n : ZMod b)) :
    IsSquare (n : ZMod (a * b)) := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  let e := ZMod.chineseRemainder hcop
  refine ⟨e.symm (x, y), ?_⟩
  have hprod : (x, y) * (x, y) = ((n : ZMod a), (n : ZMod b)) := by
    ext <;> simp [hx, hy]
  have : e (e.symm (x, y) * e.symm (x, y)) = e (n : ZMod (a * b)) := by
    rw [map_mul, e.apply_symm_apply, hprod]
    ext
    · simp [zmod_cast_int_fst hcop n]
    · simp [zmod_cast_int_snd hcop n]
  exact e.injective this.symm

lemma isSquare_mod_one (n : ℤ) : IsSquare (n : ZMod 1) := by
  refine ⟨0, ?_⟩
  have : Subsingleton (ZMod 1) := inferInstance
  exact Subsingleton.elim _ _

lemma exists_int_sq_mod {N : ℤ} {d : ℕ} (hd : 0 < d)
    (h : IsSquare (N : ZMod d)) :
    ∃ s : ℤ, s ^ 2 ≡ N [ZMOD d] ∧ 2 * |s| ≤ d := by
  obtain ⟨x, hx⟩ := h
  haveI : NeZero d := ⟨hd.ne'⟩
  let s0 : ℤ := x.val
  have hs0 : (s0 : ZMod d) = x := by
    unfold s0
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val x
  have hsq : ((s0 ^ 2 : ℤ) : ZMod d) = (N : ZMod d) := by
    rw [pow_two, Int.cast_mul, hs0, hx]
  have hmod : s0 ^ 2 ≡ N [ZMOD d] :=
    (ZMod.intCast_eq_intCast_iff (s0 ^ 2) N d).mp hsq
  have hs0_nonneg : 0 ≤ s0 := by unfold s0; exact Int.natCast_nonneg _
  have hs0_lt : s0 < (d : ℤ) := by
    unfold s0
    exact Int.ofNat_lt.mpr (ZMod.val_lt x)
  by_cases hle : 2 * s0 ≤ d
  · exact ⟨s0, hmod, by rwa [abs_of_nonneg hs0_nonneg]⟩
  · refine ⟨s0 - d, ?_, ?_⟩
    · have : (s0 - (d : ℤ)) ^ 2 ≡ s0 ^ 2 [ZMOD d] := by
        refine Int.modEq_iff_dvd.mpr ?_
        refine ⟨2 * s0 - d, ?_⟩
        ring
      exact this.trans hmod
    · have hneg : s0 - (d : ℤ) ≤ 0 := by linarith
      rw [abs_of_nonpos hneg]
      linarith

lemma isSquare_mod_of_primes {n : ℕ} {a : ℤ} (hn : 0 < n)
    (hsq : Squarefree n)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → IsSquare (a : ZMod p)) :
    IsSquare (a : ZMod n) := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    rcases n.eq_zero_or_pos with rfl | hn'
    · exact (lt_irrefl 0 hn).elim
    rcases eq_or_ne n 1 with rfl | hn1
    · exact isSquare_mod_one a
    obtain ⟨p, hp, hpdvd⟩ := n.exists_prime_and_dvd hn1
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨m, hm⟩ := hpdvd
    have hmpos : 0 < m :=
      Nat.pos_of_ne_zero fun hm0 => by
        subst hm0
        simp at hm
        exact hn'.ne' hm
    have hp_ndvd : ¬ p ∣ m := by
      intro hpm
      have : p * p ∣ n := by
        rw [hm]; exact mul_dvd_mul_left p hpm
      exact (squarefree_iff_prime_squarefree.mp hsq) p hp this
    have hcop : p.Coprime m := hp.coprime_iff_not_dvd.mpr hp_ndvd
    have hsfm : Squarefree m := by
      have : m ∣ n := ⟨p, by rw [hm, mul_comm]⟩
      exact hsq.squarefree_of_dvd this
    have hsp : IsSquare (a : ZMod p) := h p hp (by rw [hm]; exact dvd_mul_right _ _)
    have hsm : IsSquare (a : ZMod m) := by
      refine ih m ?_ hmpos hsfm ?_
      · rw [hm]; exact (Nat.lt_mul_iff_one_lt_left hmpos).mpr hp.one_lt
      · intro q hq hqd
        exact h q hq (hqd.trans ⟨p, by rw [hm, mul_comm]⟩)
    have := isSquare_mod_mul hcop hsp hsm
    rwa [hm]

lemma conic_identity (s N x z : ℤ) :
    (s ^ 2 - N) * (x ^ 2 - N * z ^ 2) =
      (s * x + N * z) ^ 2 - N * (s * z + x) ^ 2 := by
  ring

lemma conic_compose (s N x z m y d : ℤ)
    (hs : s ^ 2 - N = d * m) (hx : x ^ 2 - N * z ^ 2 = m * y ^ 2) :
    (s * x + N * z) ^ 2 - d * (m * y) ^ 2 = N * (s * z + x) ^ 2 := by
  have hid := conic_identity s N x z
  have : (s * x + N * z) ^ 2 - N * (s * z + x) ^ 2 = d * (m * y) ^ 2 := by
    calc
      (s * x + N * z) ^ 2 - N * (s * z + x) ^ 2
          = (s ^ 2 - N) * (x ^ 2 - N * z ^ 2) := hid.symm
      _ = (d * m) * (m * y ^ 2) := by rw [hs, hx]
      _ = d * (m * y) ^ 2 := by ring
  linarith

def sqFreeKernel (n : ℕ) : ℕ := n / floorRoot 2 n ^ 2

lemma n_eq_sqFreeKernel_mul_sq (n : ℕ) :
    sqFreeKernel n * floorRoot 2 n ^ 2 = n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [sqFreeKernel]
  simpa [sqFreeKernel] using Nat.div_mul_cancel (floorRoot_pow_dvd (n := 2) (a := n))

lemma sqFreeKernel_ne_zero {n : ℕ} (hn : n ≠ 0) : sqFreeKernel n ≠ 0 := by
  intro hz
  have := n_eq_sqFreeKernel_mul_sq n
  simp [hz] at this
  exact hn this.symm

lemma factorization_sqFreeKernel (n : ℕ) (hn : n ≠ 0) (p : ℕ) :
    (sqFreeKernel n).factorization p = n.factorization p % 2 := by
  set K := sqFreeKernel n
  set F := floorRoot 2 n
  have h : K * F ^ 2 = n := n_eq_sqFreeKernel_mul_sq n
  have hk : K ≠ 0 := sqFreeKernel_ne_zero hn
  have hfr : F ≠ 0 := floorRoot_ne_zero.mpr ⟨by decide, hn⟩
  have hfr2 : F ^ 2 ≠ 0 := pow_ne_zero 2 hfr
  have hsum : n.factorization = K.factorization + 2 • F.factorization := by
    rw [← h, Nat.factorization_mul hk hfr2, Nat.factorization_pow]
  have hp : n.factorization p = K.factorization p + 2 * F.factorization p := by
    simpa [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
      using congrArg (fun f : ℕ →₀ ℕ => f p) hsum
  have hdiv : F.factorization p = n.factorization p / 2 := by
    simp [F, factorization_floorRoot, Finsupp.floorDiv_apply, Nat.floorDiv_eq_div]
  rw [hdiv] at hp
  simp [K] at hp ⊢
  omega

lemma squarefree_sqFreeKernel_of_pos {n : ℕ} (hn : 0 < n) :
    Squarefree (sqFreeKernel n) := by
  refine (squarefree_iff_factorization_le_one (sqFreeKernel_ne_zero hn.ne')).2 ?_
  intro p
  have := factorization_sqFreeKernel n hn.ne' p
  omega

def intSqFactor (n : ℤ) : ℤ := floorRoot 2 n.natAbs

def sqFreeInt (n : ℤ) : ℤ := n.sign * sqFreeKernel n.natAbs

lemma n_eq_sqFreeInt_mul_sq (n : ℤ) :
    n = sqFreeInt n * intSqFactor n ^ 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [sqFreeInt, intSqFactor, sqFreeKernel]
  calc
    n = n.sign * n.natAbs := (Int.sign_mul_natAbs n).symm
    _ = n.sign * (sqFreeKernel n.natAbs * floorRoot 2 n.natAbs ^ 2 : ℕ) := by
        congr 1
        exact_mod_cast (n_eq_sqFreeKernel_mul_sq n.natAbs).symm
    _ = (n.sign * (sqFreeKernel n.natAbs : ℤ)) * (floorRoot 2 n.natAbs : ℤ) ^ 2 := by
        push_cast; ring
    _ = sqFreeInt n * intSqFactor n ^ 2 := rfl

lemma sqFreeInt_natAbs (n : ℤ) (hn : n ≠ 0) :
    (sqFreeInt n).natAbs = sqFreeKernel n.natAbs := by
  rw [sqFreeInt, Int.natAbs_mul, Int.natAbs_sign, if_neg hn]
  simp

lemma squarefree_sqFreeInt {n : ℤ} (hn : n ≠ 0) :
    Squarefree (sqFreeInt n).natAbs := by
  rw [sqFreeInt_natAbs n hn]
  exact squarefree_sqFreeKernel_of_pos (Int.natAbs_pos.mpr hn)

lemma sqFreeInt_ne_zero {n : ℤ} (hn : n ≠ 0) : sqFreeInt n ≠ 0 := by
  intro hz
  have := n_eq_sqFreeInt_mul_sq n
  simp [hz] at this
  exact hn this

lemma hilbertOdd_sq_right {p : ℕ} [Fact p.Prime] {a b : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertOdd p a (b ^ 2) = 1 :=
  hilbertOdd_sq' ha hb

lemma AllHilbert_sq_right {d n k : ℤ} (hd : d ≠ 0) (hn : n ≠ 0) (hk : k ≠ 0) :
    AllHilbert d (n * k ^ 2) ↔ AllHilbert d n := by
  constructor
  · intro h
    refine ⟨hd, hn, ?_, ?_, ?_⟩
    · have hinf := h.2.2.1
      rwa [hilbertInf_mul hn (pow_ne_zero 2 hk), hilbertInf_sq d k, mul_one] at hinf
    · have h2 := h.2.2.2.1
      have : hilbertTwo d (n * k ^ 2) = hilbertTwo d n * hilbertTwo d (k ^ 2) :=
        hilbertTwo_mul hd hn (pow_ne_zero 2 hk)
      rw [this, hilbertTwo_sq' hd hk, mul_one] at h2
      exact h2
    · intro p hp hp2
      haveI : Fact p.Prime := ⟨hp⟩
      have ho := h.2.2.2.2 p hp hp2
      have : hilbertOdd p d (n * k ^ 2) = hilbertOdd p d n * hilbertOdd p d (k ^ 2) :=
        hilbertOdd_mul hd hn (pow_ne_zero 2 hk)
      rw [this, hilbertOdd_sq' hd hk, mul_one] at ho
      exact ho
  · intro h
    refine ⟨hd, mul_ne_zero hn (pow_ne_zero 2 hk), ?_, ?_, ?_⟩
    · rw [hilbertInf_mul hn (pow_ne_zero 2 hk), hilbertInf_sq d k, mul_one]
      exact h.2.2.1
    · rw [hilbertTwo_mul hd hn (pow_ne_zero 2 hk), hilbertTwo_sq' hd hk, mul_one]
      exact h.2.2.2.1
    · intro p hp hp2
      haveI : Fact p.Prime := ⟨hp⟩
      rw [hilbertOdd_mul hd hn (pow_ne_zero 2 hk), hilbertOdd_sq' hd hk, mul_one]
      exact h.2.2.2.2 p hp hp2

lemma AllHilbert_sqFreeInt {d n : ℤ} (hd : d ≠ 0) (hn : n ≠ 0)
    (h : AllHilbert d n) : AllHilbert d (sqFreeInt n) := by
  have hn' := n_eq_sqFreeInt_mul_sq n
  have hk : intSqFactor n ≠ 0 := by
    intro hz
    have : n = 0 := by
      have := n_eq_sqFreeInt_mul_sq n
      simp [hz] at this
      exact this
    exact hn this
  have heq : AllHilbert d (sqFreeInt n * intSqFactor n ^ 2) ↔ AllHilbert d (sqFreeInt n) :=
    AllHilbert_sq_right hd (sqFreeInt_ne_zero hn) hk
  rw [← hn'] at heq
  exact heq.mp h

/-- Lexicographic measure encoded as a single natural:
`(max |d| |N|) * (max |d| |N| + 1) + min |d| |N|`. -/
def conicMeasure (d N : ℤ) : ℕ :=
  max d.natAbs N.natAbs * (max d.natAbs N.natAbs + 1) + min d.natAbs N.natAbs

lemma conicMeasure_swap (d N : ℤ) : conicMeasure d N = conicMeasure N d := by
  unfold conicMeasure
  rw [max_comm, min_comm]

lemma conic_sol_of_isSquare_N {d N : ℤ} (hN : IsSquare N) :
    ∃ X Y Z : ℤ, X ^ 2 - d * Y ^ 2 = N * Z ^ 2 ∧ (X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0) := by
  obtain ⟨s, hs⟩ := hN
  refine ⟨s, 0, 1, ?_, by simp⟩
  simp [hs, sq]

lemma conic_sol_of_N_eq_one (d : ℤ) :
    ∃ X Y Z : ℤ, X ^ 2 - d * Y ^ 2 = (1 : ℤ) * Z ^ 2 ∧ (X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0) :=
  ⟨1, 0, 1, by ring, by simp⟩

lemma conic_sol_of_N_eq_neg_one {d : ℤ} (hdpos : 0 < d)
    (h : ∀ q : ℕ, q.Prime → q ∣ d.natAbs → q % 4 ≠ 3) :
    ∃ X Y Z : ℤ, X ^ 2 - d * Y ^ 2 = (-1 : ℤ) * Z ^ 2 ∧ (X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0) := by
  have hsq : ∃ a b : ℕ, d.natAbs = a ^ 2 + b ^ 2 := by
    refine (Nat.eq_sq_add_sq_iff).2 ?_
    intro q hq hq3
    have hqP := Nat.prime_of_mem_primeFactors hq
    have hqd : q ∣ d.natAbs := Nat.dvd_of_mem_primeFactors hq
    exact absurd hq3 (h q hqP hqd)
  obtain ⟨a, b, hab⟩ := hsq
  refine ⟨a, 1, b, ?_, by simp⟩
  have hnat : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = d.natAbs := by exact_mod_cast hab.symm
  have hdabs : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg hdpos.le
  linarith

lemma squarefree_padicValNat {n p : ℕ} (hp : p.Prime) (hsf : Squarefree n)
    (hdvd : p ∣ n) : n.factorization p = 1 := by
  have hn : n ≠ 0 := hsf.ne_zero
  have hle : n.factorization p ≤ 1 :=
    (squarefree_iff_factorization_le_one hn).1 hsf p
  have hpos : 0 < n.factorization p := hp.factorization_pos_of_dvd hn hdvd
  omega

lemma squarefree_padicValInt {a : ℤ} {p : ℕ} [Fact p.Prime]
    (hsf : Squarefree a.natAbs) (ha : a ≠ 0) (hdvd : (p : ℤ) ∣ a) :
    padicValInt p a = 1 := by
  have hpd : p ∣ a.natAbs := Int.natCast_dvd.mp hdvd
  have hfac : a.natAbs.factorization p = 1 :=
    squarefree_padicValNat Fact.out hsf hpd
  rw [padicValInt, ← Nat.factorization_def a.natAbs Fact.out, hfac]


lemma odd_sq_emod_eight {s : ℤ} (hs : Odd s) : s ^ 2 % 8 = 1 := by
  obtain ⟨k, rfl⟩ := hs
  have he : Even (k * (k + 1) : ℤ) := Int.even_mul_succ_self k
  obtain ⟨t, ht⟩ := he
  have ht' : (k * (k + 1) : ℤ) = 2 * t := by omega
  have : (2 * k + 1 : ℤ) ^ 2 = 8 * t + 1 := by
    have : (2 * k + 1 : ℤ) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    rw [this, ht']; ring
  omega

lemma padicValInt_two_eq_zero_iff {a : ℤ} (ha : a ≠ 0) :
    padicValInt 2 a = 0 ↔ Odd a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro h
    rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    exact not_dvd_of_padicValInt_eq_zero ha h
  · intro ho
    refine padicValInt_eq_zero_of_not_dvd ha ?_
    have : ¬ Even a := Int.not_even_iff_odd.mpr ho
    exact fun hdvd => this (even_iff_two_dvd.mpr hdvd)

lemma oddPart_eq_self_of_odd {a : ℤ} (ha : a ≠ 0) (ho : Odd a) : oddPart a = a := by
  unfold oddPart
  have : padicValInt 2 a = 0 := (padicValInt_two_eq_zero_iff ha).mpr ho
  rw [this, pow_zero, Int.ediv_one]

lemma hilbertTwo_eq_one_of_even {a b : ℤ}
    (h : Even (hilbertε (oddPart a) * hilbertε (oddPart b) +
      padicValInt 2 a * hilbertω (oddPart b) +
      padicValInt 2 b * hilbertω (oddPart a))) :
    hilbertTwo a b = 1 := by
  unfold hilbertTwo
  exact Even.neg_one_pow h

lemma padicValInt_two_mul_odd {u : ℤ} (hu : Odd u) (hu0 : u ≠ 0) :
    padicValInt 2 (2 * u) = 1 ∧ oddPart (2 * u) = u := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2u : (2 * u : ℤ) ≠ 0 := mul_ne_zero (by decide) hu0
  have hdiv2 : (2 : ℤ) ∣ 2 * u := dvd_mul_right _ _
  have hndiv4 : ¬ (4 : ℤ) ∣ 2 * u := by
    intro ⟨v, hv⟩
    have : u = 2 * v := by linarith
    have : Even u := ⟨v, by omega⟩
    exact Int.not_even_iff_odd.mpr hu this
  have hpos : 0 < padicValInt 2 (2 * u) := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact not_dvd_of_padicValInt_eq_zero h2u hz hdiv2
  have hlt : padicValInt 2 (2 * u) < 2 := by
    apply Nat.not_le.mp
    intro hle
    have : (4 : ℤ) ∣ 2 * u :=
      (padicValInt_dvd_iff (p := 2) 2 (2 * u)).mpr (Or.inr hle)
    exact hndiv4 this
  have hv : padicValInt 2 (2 * u) = 1 := by omega
  refine ⟨hv, ?_⟩
  unfold oddPart
  rw [hv]
  simpa using (Int.mul_ediv_cancel_left u (by decide : (2 : ℤ) ≠ 0))

lemma padicValInt_two_of_emod_two {n : ℤ} (hn : n ≠ 0) (h : n % 8 = 2) :
    padicValInt 2 n = 1 ∧ oddPart n % 4 = 1 := by
  have : n = 2 * ((n / 2)) := by omega
  have hodd : Odd (n / 2) := by
    have : n / 2 = 4 * (n / 8) + 1 := by omega
    exact ⟨2 * (n / 8), by omega⟩
  have hu0 : n / 2 ≠ 0 := by
    intro hz; omega
  have ⟨hv, hop⟩ := padicValInt_two_mul_odd hodd hu0
  have hn2 : n = 2 * (n / 2) := by omega
  rw [← hn2] at hv hop
  refine ⟨hv, ?_⟩
  rw [hop]
  omega

lemma padicValInt_two_of_emod_six {n : ℤ} (hn : n ≠ 0) (h : n % 8 = 6) :
    padicValInt 2 n = 1 ∧ oddPart n % 4 = 3 := by
  have hodd : Odd (n / 2) := by
    have : n / 2 = 4 * (n / 8) + 3 := by omega
    exact ⟨2 * (n / 8) + 1, by omega⟩
  have hu0 : n / 2 ≠ 0 := by intro hz; omega
  have ⟨hv, hop⟩ := padicValInt_two_mul_odd hodd hu0
  have hn2 : n = 2 * (n / 2) := by omega
  rw [← hn2] at hv hop
  refine ⟨hv, ?_⟩
  rw [hop]
  omega

lemma padicValInt_two_of_emod_four {n : ℤ} (hn : n ≠ 0) (h : n % 8 = 4) :
    padicValInt 2 n = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdiv4 : (4 : ℤ) ∣ n := by
    have : n = 8 * (n / 8) + 4 := by omega
    refine ⟨2 * (n / 8) + 1, by linarith⟩
  have hndiv8 : ¬ (8 : ℤ) ∣ n := by
    intro hd
    have : n % 8 = 0 := Int.emod_eq_zero_of_dvd hd
    omega
  have hge : 2 ≤ padicValInt 2 n :=
    (padicValInt_dvd_iff (p := 2) 2 n).mp hdiv4 |>.resolve_left hn
  have hlt : ¬ 3 ≤ padicValInt 2 n := by
    intro hle
    have : (8 : ℤ) ∣ n :=
      (padicValInt_dvd_iff (p := 2) 3 n).mpr (Or.inr hle)
    exact hndiv8 this
  omega

lemma ε_mul_of_opp_mod4 {u v : ℤ} (hu : Odd u) (hv : Odd v)
    (h : u % 4 ≠ v % 4) :
    hilbertε u * hilbertε v = 0 := by
  have hu4 := odd_mod_four hu
  have hv4 := odd_mod_four hv
  rcases hu4 with hu4 | hu4 <;> rcases hv4 with hv4 | hv4
  · exact absurd (hu4.trans hv4.symm) h
  · have : hilbertε u = 0 := (hilbertε_eq_zero_iff hu).mpr hu4
    simp [this]
  · have : hilbertε v = 0 := (hilbertε_eq_zero_iff hv).mpr hv4
    simp [this]
  · exact absurd (hu4.trans hv4.symm) h

/-- The 2-adic Steinberg identity when the first argument is odd. -/
lemma hilbertTwo_s_sq_sub_of_odd {a s : ℤ} (ha : a ≠ 0) (hs : s ^ 2 - a ≠ 0)
    (hodd : Odd a) : hilbertTwo a (s ^ 2 - a) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hα : padicValInt 2 a = 0 := (padicValInt_two_eq_zero_iff ha).mpr hodd
  have hopa : oddPart a = a := oddPart_eq_self_of_odd ha hodd
  by_cases hse : Even s
  · -- s even ⇒ s² ≡ 0 mod 4, so s²-a is odd and opposite to a mod 4
    have hs2even : Even (s ^ 2) := by
      obtain ⟨k, hk⟩ := hse
      refine ⟨2 * k * k, ?_⟩
      have : s = 2 * k := by omega
      rw [this]; ring
    have hsa_odd : Odd (s ^ 2 - a) := by
      rw [← Int.not_even_iff_odd]
      intro he
      have : Even a := by
        have haeq : a = s ^ 2 - (s ^ 2 - a) := by ring
        rw [haeq]
        exact hs2even.sub he
      exact Int.not_even_iff_odd.mpr hodd this
    have hopsa : oddPart (s ^ 2 - a) = s ^ 2 - a :=
      oddPart_eq_self_of_odd hs hsa_odd
    have hβ : padicValInt 2 (s ^ 2 - a) = 0 :=
      (padicValInt_two_eq_zero_iff hs).mpr hsa_odd
    have hmod4 : a % 4 ≠ (s ^ 2 - a) % 4 := by
      have ha4 := odd_mod_four hodd
      have hs24 : s ^ 2 % 4 = 0 := by
        obtain ⟨k, hk⟩ := hse
        have hs2 : s = 2 * k := by omega
        have : s ^ 2 = 4 * k ^ 2 := by rw [hs2]; ring
        omega
      rcases ha4 with ha4 | ha4 <;> omega
    have hε0 : hilbertε a * hilbertε (s ^ 2 - a) = 0 :=
      ε_mul_of_opp_mod4 hodd hsa_odd hmod4
    refine hilbertTwo_eq_one_of_even ?_
    simp [hopa, hopsa, hα, hβ, hε0]
  · -- s odd
    have hsodd : Odd s := Int.not_even_iff_odd.mp hse
    have hs2 : s ^ 2 % 8 = 1 := odd_sq_emod_eight hsodd
    have ha8 := odd_mod_eight hodd
    rcases ha8 with ha1 | ha3 | ha5 | ha7
    · -- a ≡ 1 mod 8: ε=0, ω=0
      have hε : hilbertε a = 0 :=
        (hilbertε_eq_zero_iff hodd).mpr (by omega)
      have hω : hilbertω a = 0 :=
        (hilbertω_eq_zero_iff hodd).mpr (Or.inl ha1)
      refine hilbertTwo_eq_one_of_even ?_
      simp [hopa, hα, hε, hω]
    · -- a ≡ 3 mod 8: s²-a ≡ 6 mod 8
      have hsa8 : (s ^ 2 - a) % 8 = 6 := by omega
      have ⟨hβ, hop4⟩ := padicValInt_two_of_emod_six hs hsa8
      have hop_odd : Odd (oddPart (s ^ 2 - a)) := oddPart_odd hs
      have hεa : hilbertε a = 1 := (hilbertε_eq_one_iff hodd).mpr (by omega)
      have hωa : hilbertω a = 1 := (hilbertω_eq_one_iff hodd).mpr (Or.inl ha3)
      have hεv : hilbertε (oddPart (s ^ 2 - a)) = 1 :=
        (hilbertε_eq_one_iff hop_odd).mpr hop4
      refine hilbertTwo_eq_one_of_even ?_
      simp [hopa, hα, hβ, hεa, hωa, hεv]
    · -- a ≡ 5 mod 8: s²-a ≡ 4 mod 8, β=2 even
      have hsa8 : (s ^ 2 - a) % 8 = 4 := by omega
      have hβ : padicValInt 2 (s ^ 2 - a) = 2 := padicValInt_two_of_emod_four hs hsa8
      have hεa : hilbertε a = 0 := (hilbertε_eq_zero_iff hodd).mpr (by omega)
      have hωa : hilbertω a = 1 := (hilbertω_eq_one_iff hodd).mpr (Or.inr ha5)
      refine hilbertTwo_eq_one_of_even ?_
      simp [hopa, hα, hβ, hεa, hωa]
    · -- a ≡ 7 mod 8: s²-a ≡ 2 mod 8
      have hsa8 : (s ^ 2 - a) % 8 = 2 := by omega
      have ⟨hβ, hop4⟩ := padicValInt_two_of_emod_two hs hsa8
      have hop_odd : Odd (oddPart (s ^ 2 - a)) := oddPart_odd hs
      have hεa : hilbertε a = 1 := (hilbertε_eq_one_iff hodd).mpr (by omega)
      have hωa : hilbertω a = 0 := (hilbertω_eq_zero_iff hodd).mpr (Or.inr ha7)
      have hεv : hilbertε (oddPart (s ^ 2 - a)) = 0 :=
        (hilbertε_eq_zero_iff hop_odd).mpr hop4
      refine hilbertTwo_eq_one_of_even ?_
      simp [hopa, hα, hβ, hεa, hωa, hεv]

lemma padicValInt_two_pow (k : ℕ) : padicValInt 2 ((2 : ℤ) ^ k) = k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : ℤ) ≠ 0 := by decide
  have := padicValInt_pow (p := 2) (a := (2 : ℤ)) h2 k
  have hv : padicValInt 2 (2 : ℤ) = 1 := padicValInt.self (by decide)
  simpa [hv] using this

lemma oddPart_pow_two (k : ℕ) : oddPart ((2 : ℤ) ^ k) = 1 := by
  unfold oddPart
  rw [padicValInt_two_pow]
  exact Int.ediv_self (pow_ne_zero _ (by decide))

lemma oddPart_two_pow_mul {w : ℤ} (hw : w ≠ 0) (k : ℕ) :
    oddPart ((2 : ℤ) ^ k * w) = oddPart w := by
  have h2k : (2 : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by decide)
  rw [oddPart_mul h2k hw, oddPart_pow_two, one_mul]


lemma even_zpow_two {k : ℕ} (hk : 0 < k) : Even ((2 : ℤ) ^ k) := by
  cases k with
  | zero => exact (Nat.not_lt_zero 0 hk).elim
  | succ k =>
    refine ⟨(2 : ℤ) ^ k, ?_⟩
    rw [pow_succ]
    ring

lemma pow_two_emod8_of_ge {k : ℕ} (h : 3 ≤ k) : ((2 : ℤ) ^ k) % 8 = 0 := by
  have hk' : k = 3 + (k - 3) := by omega
  rw [hk', pow_add]
  simp

lemma hilbertε_of_mod4 {x : ℤ} (hx : Odd x) :
    hilbertε x = if x % 4 = 3 then 1 else 0 := by
  by_cases h : x % 4 = 3
  · simp [h, (hilbertε_eq_one_iff hx).mpr h]
  · have : x % 4 = 1 := (odd_mod_four hx).resolve_right h
    simp [h, (hilbertε_eq_zero_iff hx).mpr this]

lemma hilbertω_of_mod8 {x : ℤ} (hx : Odd x) :
    hilbertω x = if x % 8 = 3 ∨ x % 8 = 5 then 1 else 0 := by
  by_cases h : x % 8 = 3 ∨ x % 8 = 5
  · simp [h, (hilbertω_eq_one_iff hx).mpr h]
  · have : x % 8 = 1 ∨ x % 8 = 7 := by
      have := odd_mod_eight hx
      omega
    simp [h, (hilbertω_eq_zero_iff hx).mpr this]

lemma odd_of_odd_sub_even {x y : ℤ} (hx : Odd x) (hy : Even y) : Odd (x - y) := by
  rw [← Int.not_even_iff_odd]
  intro he
  have : Even x := by
    have : x = (x - y) + y := by ring
    rw [this]; exact he.add hy
  exact Int.not_even_iff_odd.mpr hx this

lemma odd_of_even_sub_odd {x y : ℤ} (hx : Even x) (hy : Odd y) : Odd (x - y) := by
  rw [← Int.not_even_iff_odd]
  intro he
  have : Even y := by
    have : y = x - (x - y) := by ring
    rw [this]; exact hx.sub he
  exact Int.not_even_iff_odd.mpr hy this

lemma odd_sq_of_odd {t : ℤ} (ht : Odd t) : Odd (t ^ 2) := by
  obtain ⟨k, hk⟩ := ht
  refine ⟨2 * k * (k + 1), ?_⟩
  have : t = 2 * k + 1 := hk
  rw [this]; ring

lemma hilbertTwo_s_sq_sub_mixed {a s : ℤ} (ha : a ≠ 0) (hs : s ^ 2 - a ≠ 0)
    (heven : Even a) (hsodd : Odd s) :
    hilbertTwo a (s ^ 2 - a) = 1 := by
  have hs2odd : Odd (s ^ 2) := odd_sq_of_odd hsodd
  have hsa_odd : Odd (s ^ 2 - a) := odd_of_odd_sub_even hs2odd heven
  rw [hilbertTwo_symm a (s ^ 2 - a)]
  have haeq : a = s ^ 2 - (s ^ 2 - a) := by ring
  nth_rw 2 [haeq]
  refine hilbertTwo_s_sq_sub_of_odd hs ?_ hsa_odd
  have : s ^ 2 - (s ^ 2 - a) = a := by ring
  rwa [this]


lemma hilbertTwo_mul_four_left {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertTwo ((4 : ℤ) * a) b = hilbertTwo a b := by
  have h4 : (4 : ℤ) ≠ 0 := by decide
  rw [hilbertTwo_symm, hilbertTwo_mul hb h4 ha]
  have : hilbertTwo b 4 = 1 := by
    have hsq : (4 : ℤ) = (2 : ℤ) ^ 2 := by decide
    rw [hsq]
    exact hilbertTwo_sq' hb (by decide)
  rw [this, one_mul, hilbertTwo_symm]

lemma hilbertTwo_mul_four_right {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertTwo a ((4 : ℤ) * b) = hilbertTwo a b := by
  rw [hilbertTwo_symm, hilbertTwo_mul_four_left hb ha, hilbertTwo_symm]

lemma four_dvd_of_val_ge_two {a : ℤ} (ha : a ≠ 0)
    (h : 2 ≤ padicValInt 2 a) : (4 : ℤ) ∣ a :=
  (padicValInt_dvd_iff (p := 2) 2 a).mpr (Or.inr h)

/-- The remaining 2-adic identity when `v₂(a) = 1` and `s` is even. -/
lemma hilbertTwo_s_sq_sub_val_one {a s : ℤ} (ha : a ≠ 0) (hs : s ^ 2 - a ≠ 0)
    (hs0 : s ≠ 0) (hα : padicValInt 2 a = 1) (hse : Even s) :
    hilbertTwo a (s ^ 2 - a) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set u := oddPart a
  have hu0 : u ≠ 0 := oddPart_ne_zero ha
  have huodd : Odd u := oddPart_odd ha
  have hadecomp : a = u * 2 := by
    have := oddPart_mul_pow a
    simpa [hα] using this.symm
  set γ := padicValInt 2 s
  set t := oddPart s
  have ht0 : t ≠ 0 := oddPart_ne_zero hs0
  have htodd : Odd t := oddPart_odd hs0
  have hsdecomp : s = t * (2 : ℤ) ^ γ := (oddPart_mul_pow s).symm
  have hγpos : 0 < γ := by
    have : ¬ Odd s := Int.not_odd_iff_even.mpr hse
    exact Nat.pos_of_ne_zero fun hz =>
      this ((padicValInt_two_eq_zero_iff hs0).mp hz)
  have ht2 : t ^ 2 % 8 = 1 := odd_sq_emod_eight htodd
  -- s² - a = 2^{2γ} t² - 2u = 2 (2^{2γ-1} t² - u)
  have hsa_eq : s ^ 2 - a =
      (2 : ℤ) * (t ^ 2 * (2 : ℤ) ^ (2 * γ - 1) - u) := by
    have hs2 : s ^ 2 = t ^ 2 * (2 : ℤ) ^ (2 * γ) := by rw [hsdecomp]; ring
    have hpow : (2 : ℤ) ^ (2 * γ) = 2 * (2 : ℤ) ^ (2 * γ - 1) := by
      have hexp : 2 * γ = (2 * γ - 1) + 1 := by omega
      conv => lhs; rw [hexp]
      rw [pow_succ]
      ring
    rw [hs2, hadecomp, hpow]; ring
  have hdiff : t ^ 2 * (2 : ℤ) ^ (2 * γ - 1) - u ≠ 0 := by
    intro hz; apply hs; rw [hsa_eq, hz]; simp
  have hgap : 0 < 2 * γ - 1 := by omega
  have hdiff_odd : Odd (t ^ 2 * (2 : ℤ) ^ (2 * γ - 1) - u) :=
    odd_of_even_sub_odd ((even_zpow_two hgap).mul_left _) huodd
  have hβ : padicValInt 2 (s ^ 2 - a) = 1 := by
    have hmul := padicValInt.mul (p := 2)
      (by decide : (2 : ℤ) ≠ 0) hdiff
    have hv2 : padicValInt 2 (2 : ℤ) = 1 := padicValInt.self (by decide)
    have hv0 : padicValInt 2 (t ^ 2 * (2 : ℤ) ^ (2 * γ - 1) - u) = 0 :=
      (padicValInt_two_eq_zero_iff hdiff).mpr hdiff_odd
    rw [hsa_eq, hmul, hv2, hv0]
  have hopa : oddPart a = u := rfl
  have hop : oddPart (s ^ 2 - a) = t ^ 2 * (2 : ℤ) ^ (2 * γ - 1) - u := by
    have := oddPart_two_pow_mul hdiff 1
    have h2 : (2 : ℤ) ^ 1 = 2 := by decide
    rw [h2] at this
    rw [← hsa_eq] at this
    rw [this, oddPart_eq_self_of_odd hdiff hdiff_odd]
  set v := t ^ 2 * (2 : ℤ) ^ (2 * γ - 1) - u
  have hvodd : Odd v := hdiff_odd
  refine hilbertTwo_eq_one_of_even ?_
  rw [hopa, hop, hα, hβ]
  -- exponent: ε(u)ε(v) + 1·ω(v) + 1·ω(u)
  rcases Nat.eq_or_lt_of_le hγpos with hγ1 | hγgt
  · -- γ = 1: v = 2 t² - u ≡ 2-u (mod 8)
    have hv8 : v % 8 = (2 - u % 8) % 8 := by
      have : 2 * γ - 1 = 1 := by omega
      change (t ^ 2 * (2 : ℤ) ^ (2 * γ - 1) - u) % 8 = _
      rw [this, Int.sub_emod, Int.mul_emod, ht2]
      norm_num
    have hu8 := odd_mod_eight huodd
    rcases hu8 with hu1 | hu3 | hu5 | hu7
    · have hεu : hilbertε u = 0 := (hilbertε_eq_zero_iff huodd).mpr (by omega)
      have hωu : hilbertω u = 0 := (hilbertω_eq_zero_iff huodd).mpr (Or.inl hu1)
      have hv1 : v % 8 = 1 := by omega
      have hεv : hilbertε v = 0 := (hilbertε_eq_zero_iff hvodd).mpr (by omega)
      have hωv : hilbertω v = 0 := (hilbertω_eq_zero_iff hvodd).mpr (Or.inl hv1)
      simp [hεu, hωu, hεv, hωv]
    · have hεu : hilbertε u = 1 := (hilbertε_eq_one_iff huodd).mpr (by omega)
      have hωu : hilbertω u = 1 := (hilbertω_eq_one_iff huodd).mpr (Or.inl hu3)
      have hv7 : v % 8 = 7 := by omega
      have hεv : hilbertε v = 1 := (hilbertε_eq_one_iff hvodd).mpr (by omega)
      have hωv : hilbertω v = 0 := (hilbertω_eq_zero_iff hvodd).mpr (Or.inr hv7)
      simp [hεu, hωu, hεv, hωv]
    · have hεu : hilbertε u = 0 := (hilbertε_eq_zero_iff huodd).mpr (by omega)
      have hωu : hilbertω u = 1 := (hilbertω_eq_one_iff huodd).mpr (Or.inr hu5)
      have hv5 : v % 8 = 5 := by omega
      have hεv : hilbertε v = 0 := (hilbertε_eq_zero_iff hvodd).mpr (by omega)
      have hωv : hilbertω v = 1 := (hilbertω_eq_one_iff hvodd).mpr (Or.inr hv5)
      simp [hεu, hωu, hεv, hωv]
    · have hεu : hilbertε u = 1 := (hilbertε_eq_one_iff huodd).mpr (by omega)
      have hωu : hilbertω u = 0 := (hilbertω_eq_zero_iff huodd).mpr (Or.inr hu7)
      have hv3 : v % 8 = 3 := by omega
      have hεv : hilbertε v = 1 := (hilbertε_eq_one_iff hvodd).mpr (by omega)
      have hωv : hilbertω v = 1 := (hilbertω_eq_one_iff hvodd).mpr (Or.inl hv3)
      simp [hεu, hωu, hεv, hωv]
  · -- γ ≥ 2: 2γ-1 ≥ 3, v ≡ -u (mod 8)
    have hge : 3 ≤ 2 * γ - 1 := by omega
    have hv8 : v % 8 = (0 - u % 8) % 8 := by
      have hpow : ((2 : ℤ) ^ (2 * γ - 1)) % 8 = 0 := pow_two_emod8_of_ge hge
      change (t ^ 2 * (2 : ℤ) ^ (2 * γ - 1) - u) % 8 = (0 - u % 8) % 8
      rw [Int.sub_emod, Int.mul_emod, ht2, hpow]
      simp
    have hεprod : hilbertε u * hilbertε v = 0 := by
      have hneq : u % 4 ≠ v % 4 := by
        have hu4 := odd_mod_four huodd
        rcases hu4 with hu4 | hu4 <;> omega
      exact ε_mul_of_opp_mod4 huodd hvodd hneq
    have hωeq : hilbertω v = hilbertω u := by
      rw [hilbertω_of_mod8 hvodd, hilbertω_of_mod8 huodd]
      have hu8 := odd_mod_eight huodd
      rcases hu8 with hu8 | hu8 | hu8 | hu8 <;> simp [hu8, hv8]
    simp [hεprod, hωeq]

lemma hilbertTwo_s_sq_sub_both_even {a s : ℤ} (ha : a ≠ 0) (hs : s ^ 2 - a ≠ 0)
    (hs0 : s ≠ 0) (hae : Even a) (hse : Even s) :
    hilbertTwo a (s ^ 2 - a) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- induction on v₂(a) + v₂(s)
  induction hsum : padicValInt 2 a + padicValInt 2 s using Nat.strong_induction_on generalizing a s with
  | h n ih =>
    subst hsum
    have hαpos : 0 < padicValInt 2 a := by
      have : ¬ Odd a := Int.not_odd_iff_even.mpr hae
      exact Nat.pos_of_ne_zero fun hz =>
        this ((padicValInt_two_eq_zero_iff ha).mp hz)
    have hγpos : 0 < padicValInt 2 s := by
      have : ¬ Odd s := Int.not_odd_iff_even.mpr hse
      exact Nat.pos_of_ne_zero fun hz =>
        this ((padicValInt_two_eq_zero_iff hs0).mp hz)
    by_cases hα1 : padicValInt 2 a = 1
    · exact hilbertTwo_s_sq_sub_val_one ha hs hs0 hα1 hse
    · -- v₂(a) ≥ 2, so 4 ∣ a; also 2 ∣ s, write a=4a', s=2s'
      have hαge : 2 ≤ padicValInt 2 a := by omega
      obtain ⟨a', ha'⟩ := four_dvd_of_val_ge_two ha hαge
      obtain ⟨s', hs'⟩ := (even_iff_two_dvd.mp hse)
      have hs'2 : s = 2 * s' := by omega
      have ha'0 : a' ≠ 0 := by
        intro hz; apply ha; rw [ha', hz]; simp
      have hs'0 : s' ≠ 0 := by
        intro hz; apply hs0; rw [hs'2, hz]; simp
      have hsa' : s' ^ 2 - a' ≠ 0 := by
        intro hz
        have : s ^ 2 - a = 4 * (s' ^ 2 - a') := by
          rw [hs'2, ha']; ring
        apply hs; rw [this, hz]; simp
      have hred : hilbertTwo a (s ^ 2 - a) = hilbertTwo a' (s' ^ 2 - a') := by
        have haeq : a = 4 * a' := ha'
        have hsaeq : s ^ 2 - a = 4 * (s' ^ 2 - a') := by
          rw [hs'2, ha']; ring
        rw [hsaeq, haeq, hilbertTwo_mul_four_left ha'0 (mul_ne_zero (by decide : (4 : ℤ) ≠ 0) hsa'),
          hilbertTwo_mul_four_right ha'0 hsa']
      rw [hred]
      -- a' may be odd: then use the odd or mixed case
      by_cases hodd' : Odd a'
      · exact hilbertTwo_s_sq_sub_of_odd ha'0 hsa' hodd'
      · have he' : Even a' := Int.not_odd_iff_even.mp hodd'
        by_cases hsodd' : Odd s'
        · exact hilbertTwo_s_sq_sub_mixed ha'0 hsa' he' hsodd'
        · have hse' : Even s' := Int.not_odd_iff_even.mp hsodd'
          refine ih (padicValInt 2 a' + padicValInt 2 s') ?_ ha'0 hsa' hs'0 he' hse' rfl
          -- valuations drop by 2 and 1
          have ha4 : padicValInt 2 a = padicValInt 2 a' + 2 := by
            have h4 : (4 : ℤ) = (2 : ℤ) ^ 2 := by decide
            have := padicValInt.mul (p := 2) (by decide : (4 : ℤ) ≠ 0) ha'0
            rw [← ha', h4, padicValInt_two_pow] at this
            linarith
          have hs2v : padicValInt 2 s = padicValInt 2 s' + 1 := by
            have := padicValInt.mul (p := 2) (by decide : (2 : ℤ) ≠ 0) hs'0
            have hv : padicValInt 2 (2 : ℤ) = 1 := padicValInt.self (by decide)
            rw [← hs'2, hv] at this
            linarith
          omega

lemma hilbertTwo_s_sq_sub {a s : ℤ} (ha : a ≠ 0) (hs : s ^ 2 - a ≠ 0) :
    hilbertTwo a (s ^ 2 - a) = 1 := by
  by_cases hs0 : s = 0
  · subst hs0
    simpa [zero_pow (by decide : (2 : ℕ) ≠ 0)] using hilbertTwo_neg_self ha
  by_cases hodd : Odd a
  · exact hilbertTwo_s_sq_sub_of_odd ha hs hodd
  have heven : Even a := Int.not_odd_iff_even.mp hodd
  by_cases hsodd : Odd s
  · exact hilbertTwo_s_sq_sub_mixed ha hs heven hsodd
  · exact hilbertTwo_s_sq_sub_both_even ha hs hs0 heven
      (Int.not_odd_iff_even.mp hsodd)

lemma AllHilbert_s_sq_sub {a s : ℤ} (ha : a ≠ 0) (hs : s ^ 2 - a ≠ 0) :
    AllHilbert a (s ^ 2 - a) :=
  ⟨ha, hs, hilbertInf_s_sq_sub a s, hilbertTwo_s_sq_sub ha hs,
    fun p hp hp2 => by
      haveI : Fact p.Prime := ⟨hp⟩
      exact hilbertOdd_s_sq_sub hp2 ha hs⟩

lemma hilbertOdd_of_val_one_zero {p : ℕ} [Fact p.Prime] {d N : ℤ}
    (hd : d ≠ 0) (hN : N ≠ 0)
    (hα : padicValInt p d = 1) (hβ : padicValInt p N = 0) :
    hilbertOdd p d N = jacobiSym N p := by
  unfold hilbertOdd
  simp [hα, hβ, pUnit_eq_self_of_val_zero hβ]

lemma isSquare_zmod_two (a : ZMod 2) : IsSquare a := by
  revert a
  decide

lemma isSquare_of_AllHilbert_mod {d N : ℤ}
    (h : AllHilbert d N) (hsf : Squarefree d.natAbs) (hdabs : 0 < d.natAbs) :
    IsSquare (N : ZMod d.natAbs) := by
  refine isSquare_mod_of_primes hdabs hsf ?_
  intro p hp hpd
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst hp2
    exact isSquare_zmod_two _
  · have hd0 : d ≠ 0 := h.1
    have hN0 : N ≠ 0 := h.2.1
    have hα : padicValInt p d = 1 :=
      squarefree_padicValInt hsf hd0 (Int.natCast_dvd.mpr hpd)
    by_cases hpN : (p : ℤ) ∣ N
    · refine ⟨0, ?_⟩
      have h0 : (N : ZMod p) = 0 := by
        have := (ZMod.intCast_eq_intCast_iff N 0 p).mpr (Int.modEq_zero_iff_dvd.mpr hpN)
        simpa using this
      simp [h0]
    · have hβ : padicValInt p N = 0 :=
        padicValInt_eq_zero_of_not_dvd hN0 hpN
      have hsym : hilbertOdd p d N = jacobiSym N p :=
        hilbertOdd_of_val_one_zero hd0 hN0 hα hβ
      have h1 : hilbertOdd p d N = 1 := h.2.2.2.2 p hp hp2
      have : jacobiSym N p = 1 := by rw [← hsym, h1]
      exact ZMod.isSquare_of_jacobiSym_eq_one this

lemma oddPart_squarefree {a : ℤ} (ha : a ≠ 0) (hsf : Squarefree a.natAbs) :
    Squarefree (oddPart a).natAbs := by
  have hdiv : (oddPart a).natAbs ∣ a.natAbs := by
    have hmul := oddPart_mul_pow a
    refine ⟨2 ^ padicValInt 2 a, ?_⟩
    have := congrArg Int.natAbs hmul
    simpa [Int.natAbs_mul, Int.natAbs_pow] using this.symm
  exact hsf.squarefree_of_dvd hdiv

lemma even_squarefree_eq_two_mul_oddPart {d : ℤ} (hd : d ≠ 0)
    (hsf : Squarefree d.natAbs) (he : Even d) :
    d = 2 * oddPart d := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : ℤ) ∣ d := even_iff_two_dvd.1 he
  have hv : padicValInt 2 d = 1 := squarefree_padicValInt hsf hd h2
  have := oddPart_mul_pow d
  have : oddPart d * 2 = d := by simpa [hv] using this
  linarith

lemma sqFreeInt_natAbs_le (n : ℤ) : (sqFreeInt n).natAbs ≤ n.natAbs := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [sqFreeInt, sqFreeKernel]
  rw [sqFreeInt_natAbs n hn]
  have h := n_eq_sqFreeKernel_mul_sq n.natAbs
  have : sqFreeKernel n.natAbs ∣ n.natAbs := ⟨floorRoot 2 n.natAbs ^ 2, h.symm⟩
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hn) this

lemma intSqFactor_ne_zero {n : ℤ} (hn : n ≠ 0) : intSqFactor n ≠ 0 := by
  intro hz
  have := n_eq_sqFreeInt_mul_sq n
  simp [hz] at this
  exact hn this

lemma exists_m_of_modEq {s N d : ℤ} (hd : d ≠ 0)
    (h : s ^ 2 ≡ N [ZMOD d.natAbs]) :
    ∃ m : ℤ, s ^ 2 - N = d * m := by
  have hdiv0 : (d.natAbs : ℤ) ∣ N - s ^ 2 := Int.modEq_iff_dvd.mp h
  have hdiv : (d.natAbs : ℤ) ∣ s ^ 2 - N := by
    have := dvd_neg.mpr hdiv0
    simpa [neg_sub] using this
  obtain ⟨t, ht⟩ := hdiv
  refine ⟨d.sign * t, ?_⟩
  have hsign : d * d.sign = d.natAbs := by
    rw [mul_comm]
    exact Int.sign_mul_self_eq_natAbs d
  calc
    s ^ 2 - N = d.natAbs * t := ht
    _ = (d * d.sign) * t := by rw [hsign]
    _ = d * (d.sign * t) := by ring

lemma m_natAbs_lt {s N d m : ℤ} (hd : 2 ≤ d.natAbs)
    (hN : N.natAbs ≤ d.natAbs) (hs : 2 * |s| ≤ d.natAbs)
    (heq : s ^ 2 - N = d * m) :
    m.natAbs < d.natAbs := by
  have hd0 : d ≠ 0 := Int.natAbs_ne_zero.mp (by omega)
  have hD : (d.natAbs : ℤ) = |d| := Int.natCast_natAbs d
  have hNabs : (N.natAbs : ℤ) = |N| := Int.natCast_natAbs N
  have hs' : 2 * |s| ≤ |d| := by
    have : (2 * |s| : ℤ) ≤ d.natAbs := hs
    rwa [hD] at this
  have hNle : |N| ≤ |d| := by
    have : (N.natAbs : ℤ) ≤ d.natAbs := Nat.cast_le.mpr hN
    rwa [hNabs, hD] at this
  have hsq : 4 * |s| ^ 2 ≤ |d| ^ 2 := by
    nlinarith [abs_nonneg s]
  have habs : |s ^ 2 - N| = |d| * |m| := by
    rw [heq, abs_mul]
  have hbound : |s ^ 2 - N| ≤ |s| ^ 2 + |N| := by
    have h1 : |s ^ 2 - N| ≤ s ^ 2 + |N| := by
      rw [sub_eq_add_neg]
      have hle := abs_add_le (s ^ 2) (-N)
      rwa [abs_of_nonneg (sq_nonneg s), abs_neg] at hle
    have h2 : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
    linarith
  have h4 : 4 * |s ^ 2 - N| ≤ |d| ^ 2 + 4 * |d| := by
    nlinarith [hsq, hbound, hNle]
  have h4' : 4 * (|d| * |m|) ≤ |d| ^ 2 + 4 * |d| := by
    rwa [habs] at h4
  have hdpos : 0 < |d| := abs_pos.mpr hd0
  have hle : 4 * |m| ≤ |d| + 4 := by nlinarith
  by_cases h2 : d.natAbs = 2
  · have hd2 : |d| = 2 := by
      have : (d.natAbs : ℤ) = 2 := by exact_mod_cast h2
      rwa [hD] at this
    have : 4 * |m| ≤ 6 := by linarith
    have hm1 : |m| ≤ 1 := by nlinarith [abs_nonneg m]
    have : m.natAbs ≤ 1 := by
      have hm : (m.natAbs : ℤ) = |m| := Int.natCast_natAbs m
      exact_mod_cast (hm ▸ hm1)
    omega
  · have hge : 3 ≤ d.natAbs := by omega
    have hge' : (3 : ℤ) ≤ |d| := by
      have : (3 : ℤ) ≤ d.natAbs := Nat.cast_le.mpr hge
      rwa [hD] at this
    have : 4 * |m| ≤ 4 * (|d| - 1) := by
      have : |d| + 4 ≤ 4 * (|d| - 1) := by nlinarith
      linarith
    have hmle : |m| ≤ |d| - 1 := by nlinarith [abs_nonneg m]
    have : (m.natAbs : ℤ) + 1 ≤ d.natAbs := by
      have hm : (m.natAbs : ℤ) = |m| := Int.natCast_natAbs m
      linarith
    omega

lemma conicMeasure_child_lt {s N d m : ℤ}
    (hd : 2 ≤ d.natAbs) (hNle : N.natAbs ≤ d.natAbs)
    (hs : 2 * |s| ≤ d.natAbs) (heq : s ^ 2 - N = d * m) (_hm0 : m ≠ 0) :
    conicMeasure N (sqFreeInt m) < conicMeasure d N := by
  have hm : m.natAbs < d.natAbs := m_natAbs_lt hd hNle hs heq
  have hmk : (sqFreeInt m).natAbs ≤ m.natAbs := sqFreeInt_natAbs_le m
  have hmk' : (sqFreeInt m).natAbs < d.natAbs := lt_of_le_of_lt hmk hm
  set Md := d.natAbs with hMd
  set MN := N.natAbs with hMN
  set Mm := (sqFreeInt m).natAbs with hMm
  clear_value Md MN Mm
  unfold conicMeasure
  rw [← hMd, ← hMN, ← hMm]
  have hmax : max Md MN = Md := max_eq_left hNle
  have hmin : min Md MN = MN := min_eq_right hNle
  rw [hmax, hmin]
  rcases lt_or_eq_of_le hNle with hlt | heqN
  · have hMx : max MN Mm < Md := max_lt hlt hmk'
    have hminle : min MN Mm ≤ max MN Mm := min_le_max
    have hleft : max MN Mm * (max MN Mm + 1) + min MN Mm
        ≤ max MN Mm * (max MN Mm + 2) := by
      have : max MN Mm * (max MN Mm + 1) + max MN Mm
          = max MN Mm * (max MN Mm + 2) := by ring
      exact this ▸ Nat.add_le_add_left hminle _
    have hmul : max MN Mm * (max MN Mm + 2) < Md * (Md + 1) :=
      Nat.mul_lt_mul_of_lt_of_le hMx (by omega) (by omega)
    have : max MN Mm * (max MN Mm + 2) < Md * (Md + 1) + MN :=
      lt_of_lt_of_le hmul (Nat.le_add_right _ _)
    exact lt_of_le_of_lt hleft this
  · rw [heqN]
    have hmax' : max Md Mm = Md := max_eq_left hmk'.le
    have hmin' : min Md Mm = Mm := min_eq_right hmk'.le
    rw [hmax', hmin']
    omega

lemma AllHilbert_mul_right {d n m : ℤ} (hd : d ≠ 0) (hn : n ≠ 0) (hm : m ≠ 0)
    (hnm : AllHilbert d (n * m)) (hn1 : AllHilbert d n) :
    AllHilbert d m := by
  refine ⟨hd, hm, ?_, ?_, ?_⟩
  · have hmul := hilbertInf_mul (a := d) hn hm
    have hnm1 : hilbertInf d (n * m) = 1 := hnm.2.2.1
    have hn11 : hilbertInf d n = 1 := hn1.2.2.1
    rw [hnm1, hn11, one_mul] at hmul
    exact hmul.symm
  · have hmul := hilbertTwo_mul hd hn hm
    have hnm1 : hilbertTwo d (n * m) = 1 := hnm.2.2.2.1
    have hn11 : hilbertTwo d n = 1 := hn1.2.2.2.1
    rw [hnm1, hn11, one_mul] at hmul
    exact hmul.symm
  · intro p hp hp2
    haveI : Fact p.Prime := ⟨hp⟩
    have hmul := hilbertOdd_mul (p := p) hd hn hm
    have hnm1 : hilbertOdd p d (n * m) = 1 := hnm.2.2.2.2 p hp hp2
    have hn11 : hilbertOdd p d n = 1 := hn1.2.2.2.2 p hp hp2
    rw [hnm1, hn11, one_mul] at hmul
    exact hmul.symm

lemma AllHilbert_inherit_child {N d m s : ℤ} (hN0 : N ≠ 0) (hd0 : d ≠ 0)
    (hm0 : m ≠ 0) (hm' : s ^ 2 - N = d * m)
    (hAH : AllHilbert N (s ^ 2 - N)) (hNd : AllHilbert N d) :
    AllHilbert N (sqFreeInt m) := by
  have hNm : AllHilbert N m := by
    have hprod : AllHilbert N (d * m) := by
      rwa [hm'.symm]
    exact AllHilbert_mul_right hN0 hd0 hm0 hprod hNd
  exact AllHilbert_sqFreeInt hN0 hm0 hNm

/-- Compose a child solution of `(N, m)` with `s² - N = d m` to a solution of `(d, N)`. -/
lemma conic_from_child {N d s m x y z k : ℤ}
    (hm' : s ^ 2 - N = d * m) (hdec : m = sqFreeInt m * k ^ 2)
    (hsol : x ^ 2 - N * y ^ 2 = sqFreeInt m * z ^ 2)
    (hm0 : m ≠ 0) (hd0 : d ≠ 0) (hk0 : k ≠ 0)
    (hnz : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    ∃ X Y Z : ℤ, X ^ 2 - d * Y ^ 2 = N * Z ^ 2 ∧ (X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0) := by
  set x1 := x * k
  set z1 := y * k
  set y1 := z
  have hx1 : x1 ^ 2 - N * z1 ^ 2 = m * y1 ^ 2 := by
    have h1 : x1 ^ 2 - N * z1 ^ 2 = k ^ 2 * (x ^ 2 - N * y ^ 2) := by
      simp [x1, z1]; ring
    have h2 : k ^ 2 * (x ^ 2 - N * y ^ 2) = k ^ 2 * (sqFreeInt m * z ^ 2) := by
      rw [hsol]
    have h3 : k ^ 2 * (sqFreeInt m * z ^ 2) = (sqFreeInt m * k ^ 2) * z ^ 2 := by
      ring
    have h4 : (sqFreeInt m * k ^ 2) * z ^ 2 = m * z ^ 2 := by
      rw [← hdec]
    simpa [y1] using (h1.trans (h2.trans (h3.trans h4)))
  have hcomp := conic_compose s N x1 z1 m y1 d hm' hx1
  refine ⟨s * x1 + N * z1, m * y1, s * z1 + x1, hcomp, ?_⟩
  by_contra hzero
  push_neg at hzero
  rcases hzero with ⟨hX, hY, hZ⟩
  have hy0 : y1 = 0 := (mul_eq_zero.mp hY).resolve_left hm0
  have hxeq : x1 = -s * z1 := by
    have : s * z1 + x1 = 0 := hZ
    linarith
  have hdet : s ^ 2 - N ≠ 0 := by
    intro hz
    have : d * m = 0 := by rw [← hm', hz]
    exact hm0 ((mul_eq_zero.mp this).resolve_left hd0)
  have hz1' : z1 = 0 := by
    have hX' : s * x1 + N * z1 = 0 := hX
    have : s * (-s * z1) + N * z1 = 0 := by
      simpa [hxeq] using hX'
    have : -(s ^ 2 - N) * z1 = 0 := by linarith
    have : (s ^ 2 - N) * z1 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hdet
    · exact h
  have hx1' : x1 = 0 := by simp [hxeq, hz1']
  have hx0 : x = 0 :=
    (mul_eq_zero.mp (show x * k = 0 by simpa [x1] using hx1')).resolve_right hk0
  have hy0' : y = 0 :=
    (mul_eq_zero.mp (show y * k = 0 by simpa [z1] using hz1')).resolve_right hk0
  have hz0 : z = 0 := hy0
  have hcontra : ¬ (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) := by
    push_neg
    exact ⟨hx0, hy0', hz0⟩
  exact hcontra hnz

lemma conic_from_child_exists {N d s m : ℤ}
    (hm' : s ^ 2 - N = d * m)
    (hsol : ∃ x y z : ℤ, x ^ 2 - N * y ^ 2 = sqFreeInt m * z ^ 2 ∧
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0))
    (hm0 : m ≠ 0) (hd0 : d ≠ 0) :
    ∃ X Y Z : ℤ, X ^ 2 - d * Y ^ 2 = N * Z ^ 2 ∧ (X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0) := by
  obtain ⟨x, y, z, hsol', hnz⟩ := hsol
  have hdec := n_eq_sqFreeInt_mul_sq m
  exact conic_from_child hm' hdec hsol' hm0 hd0 (intSqFactor_ne_zero hm0) hnz

lemma q_mod_four_of_jacobi_neg_one {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    (h : jacobiSym (-1) q = 1) : q % 4 = 1 := by
  have hpow : (-1 : ℤ) ^ (q / 2) = 1 := by
    rwa [jacobiSym_neg_one_odd_prime hq2] at h
  have hodd : Odd q := Nat.Prime.odd_of_ne_two Fact.out hq2
  have hmod : q % 4 = 1 ∨ q % 4 = 3 := by
    have : q % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  rcases hmod with h1 | h3
  · exact h1
  · have hodd2 : (q / 2) % 2 = 1 := by omega
    have : Odd (q / 2) := Nat.odd_iff.mpr hodd2
    have : (-1 : ℤ) ^ (q / 2) = -1 := Odd.neg_one_pow this
    have : (-1 : ℤ) = 1 := by
      rw [← this, hpow]
    exact absurd this (by decide)

lemma primes_mod_four_of_AllHilbert_neg_one {d : ℤ}
    (h : AllHilbert d (-1)) (hsf : Squarefree d.natAbs) :
    ∀ q : ℕ, q.Prime → q ∣ d.natAbs → q % 4 ≠ 3 := by
  intro q hq hqd h3
  haveI : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := by
    intro h2
    subst h2
    simp at h3
  have hα : padicValInt q d = 1 :=
    squarefree_padicValInt hsf h.1 (Int.natCast_dvd.mpr hqd)
  have hβ : padicValInt q (-1) = 0 := by
    refine padicValInt_eq_zero_of_not_dvd (by decide) ?_
    intro hdvd
    have : (q : ℤ) ∣ 1 := by simpa using hdvd
    have : q ∣ 1 := Int.natCast_dvd.mp this
    exact hq.ne_one (Nat.dvd_one.mp this)
  have hsym : hilbertOdd q d (-1) = jacobiSym (-1) q :=
    hilbertOdd_of_val_one_zero h.1 (by decide) hα hβ
  have h1 : hilbertOdd q d (-1) = 1 := h.2.2.2.2 q hq hq2
  have : jacobiSym (-1) q = 1 := by rw [← hsym, h1]
  have : q % 4 = 1 := q_mod_four_of_jacobi_neg_one hq2 this
  omega

lemma pos_of_AllHilbert_neg_one {d : ℤ} (h : AllHilbert d (-1)) : 0 < d := by
  have hd0 : d ≠ 0 := h.1
  by_contra hnot
  have hneg : d < 0 := lt_of_le_of_ne (le_of_not_gt hnot) hd0
  have hinf := h.2.2.1
  unfold hilbertInf at hinf
  rw [if_pos ⟨hneg, by decide⟩] at hinf
  exact absurd hinf (by decide)

lemma AllHilbert_sqFreeInt_both {d N : ℤ} (h : AllHilbert d N) :
    AllHilbert (sqFreeInt d) (sqFreeInt N) := by
  have hd0 := h.1
  have hN0 := h.2.1
  have h1 := AllHilbert_sqFreeInt hd0 hN0 h
  have h2 := h1.swap
  have h3 := AllHilbert_sqFreeInt (sqFreeInt_ne_zero hN0) hd0 h2
  exact h3.swap

/-- Hasse principle for the conic `X² - d Y² - N Z² = 0`, square-free case. -/
lemma conic_of_AllHilbert (d N : ℤ) (hAH : AllHilbert d N)
    (hsfd : Squarefree d.natAbs) (hsfN : Squarefree N.natAbs) :
    ∃ X Y Z : ℤ, X ^ 2 - d * Y ^ 2 = N * Z ^ 2 ∧ (X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0) := by
  induction hm : conicMeasure d N using Nat.strong_induction_on generalizing d N with
  | h μ ih =>
    subst hm
    have hd0 := hAH.1
    have hN0 := hAH.2.1
    have hdabs : 0 < d.natAbs := Int.natAbs_pos.mpr hd0
    have hNabs : 0 < N.natAbs := Int.natAbs_pos.mpr hN0
    by_cases hNsq : IsSquare N
    · exact conic_sol_of_isSquare_N hNsq
    by_cases hdsq : IsSquare d
    · obtain ⟨X, Y, Z, hsol, hnz⟩ := conic_sol_of_isSquare_N (d := N) (N := d) hdsq
      refine ⟨X, Z, Y, ?_, ?_⟩
      · linarith
      · tauto
    by_cases hN1 : N.natAbs ≤ 1
    · have hNabs1 : N.natAbs = 1 := by omega
      rcases Int.natAbs_eq_iff.mp hNabs1 with rfl | rfl
      · exact conic_sol_of_N_eq_one d
      · exact conic_sol_of_N_eq_neg_one (pos_of_AllHilbert_neg_one hAH)
          (primes_mod_four_of_AllHilbert_neg_one hAH hsfd)
    have hNge : 2 ≤ N.natAbs := by omega
    by_cases hle : N.natAbs ≤ d.natAbs
    · have hdge : 2 ≤ d.natAbs := le_trans hNge hle
      have hsqN := isSquare_of_AllHilbert_mod hAH hsfd hdabs
      obtain ⟨s, hsmod, hsle⟩ := exists_int_sq_mod hdabs hsqN
      obtain ⟨m, hm'⟩ := exists_m_of_modEq hd0 hsmod
      by_cases hm0 : m = 0
      · have : s ^ 2 = N := by
          have := hm'
          simp [hm0] at this
          linarith
        exact absurd ⟨s, by rw [← this, sq]⟩ hNsq
      have hsn : s ^ 2 - N ≠ 0 := by
        intro hz
        have : d * m = 0 := by rw [← hm', hz]
        exact hm0 ((mul_eq_zero.mp this).resolve_left hd0)
      have hAHchild : AllHilbert N (sqFreeInt m) :=
        AllHilbert_inherit_child hN0 hd0 hm0 hm'
          (AllHilbert_s_sq_sub hN0 hsn) hAH.swap
      have hlt := conicMeasure_child_lt hdge hle hsle hm' hm0
      have hchild := ih (conicMeasure N (sqFreeInt m)) hlt N (sqFreeInt m)
        hAHchild hsfN (squarefree_sqFreeInt hm0) rfl
      exact conic_from_child_exists hm' hchild hm0 hd0
    · have hle' : d.natAbs ≤ N.natAbs := by omega
      have hsqd := isSquare_of_AllHilbert_mod hAH.swap hsfN hNabs
      obtain ⟨s, hsmod, hsle⟩ := exists_int_sq_mod hNabs hsqd
      obtain ⟨m, hm'⟩ := exists_m_of_modEq hN0 hsmod
      by_cases hm0 : m = 0
      · have : s ^ 2 = d := by
          have := hm'
          simp [hm0] at this
          linarith
        exact absurd ⟨s, by rw [← this, sq]⟩ hdsq
      have hsd : s ^ 2 - d ≠ 0 := by
        intro hz
        have : N * m = 0 := by rw [← hm', hz]
        exact hm0 ((mul_eq_zero.mp this).resolve_left hN0)
      have hAHchild : AllHilbert d (sqFreeInt m) :=
        AllHilbert_inherit_child hd0 hN0 hm0 hm'
          (AllHilbert_s_sq_sub hd0 hsd) hAH
      have hlt0 := conicMeasure_child_lt hNge hle' hsle hm' hm0
      have hlt : conicMeasure d (sqFreeInt m) < conicMeasure d N := by
        rwa [conicMeasure_swap N d] at hlt0
      have hchild := ih (conicMeasure d (sqFreeInt m)) hlt d (sqFreeInt m)
        hAHchild hsfd (squarefree_sqFreeInt hm0) rfl
      obtain ⟨X, Y, Z, hsol, hnz⟩ := conic_from_child_exists hm' hchild hm0 hN0
      refine ⟨X, Z, Y, ?_, ?_⟩
      · linarith
      · tauto

/-- Hasse principle for the conic, without a square-free hypothesis. -/
lemma conic_of_AllHilbert' (d N : ℤ) (hAH : AllHilbert d N) :
    ∃ X Y Z : ℤ, X ^ 2 - d * Y ^ 2 = N * Z ^ 2 ∧ (X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0) := by
  have hd0 := hAH.1
  have hN0 := hAH.2.1
  obtain ⟨X, Y, Z, hsol, hnz⟩ :=
    conic_of_AllHilbert (sqFreeInt d) (sqFreeInt N) (AllHilbert_sqFreeInt_both hAH)
      (squarefree_sqFreeInt hd0) (squarefree_sqFreeInt hN0)
  set kd := intSqFactor d
  set kN := intSqFactor N
  refine ⟨X * kd * kN, Y * kN, Z * kd, ?_, ?_⟩
  · have hexp : (X * kd * kN) ^ 2 - (sqFreeInt d * kd ^ 2) * (Y * kN) ^ 2
        = (sqFreeInt N * kN ^ 2) * (Z * kd) ^ 2 := by
      have hring : (X * kd * kN) ^ 2 - (sqFreeInt d * kd ^ 2) * (Y * kN) ^ 2
          = kN ^ 2 * kd ^ 2 * (X ^ 2 - sqFreeInt d * Y ^ 2) := by ring
      rw [hring, hsol]
      ring
    have hd' : sqFreeInt d * kd ^ 2 = d := by
      simpa [kd] using (n_eq_sqFreeInt_mul_sq d).symm
    have hN' : sqFreeInt N * kN ^ 2 = N := by
      simpa [kN] using (n_eq_sqFreeInt_mul_sq N).symm
    rwa [hd', hN'] at hexp
  · have hkd : kd ≠ 0 := intSqFactor_ne_zero hd0
    have hkN : kN ≠ 0 := intSqFactor_ne_zero hN0
    rcases hnz with hX | hY | hZ
    · exact Or.inl (mul_ne_zero (mul_ne_zero hX hkd) hkN)
    · exact Or.inr (Or.inl (mul_ne_zero hY hkN))
    · exact Or.inr (Or.inr (mul_ne_zero hZ hkd))



