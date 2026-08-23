import FormalConjectures.Util.ProblemImports

open scoped NumberTheorySymbols
open Nat Int

/- Primes p ≡ 5 or 11 (mod 24) are represented by 2a² + 3b². -/

lemma jacobi_two_three : jacobiSym 2 3 = -1 := by
  rw [jacobiSym.at_two (by decide : Odd 3), ZMod.χ₈_nat_eq_if_mod_eight]
  decide

lemma jacobi_three_p_of_mod24 {p : ℕ} [Fact p.Prime]
    (h : p % 24 = 5 ∨ p % 24 = 11) :
    jacobiSym 3 p = if p % 24 = 5 then -1 else 1 := by
  have hp3m : (p : ℤ) % 3 = 2 := by exact_mod_cast (show p % 3 = 2 by omega)
  have hmod : jacobiSym (p : ℤ) 3 = jacobiSym 2 3 :=
    jacobiSym.mod_left' hp3m
  rcases h with h5 | h11
  · have hp4 : p % 4 = 1 := by omega
    have hQR : jacobiSym 3 p = jacobiSym p 3 :=
      jacobiSym.quadratic_reciprocity_one_mod_four' (by decide : Odd 3) hp4
    rw [if_pos h5, hQR, hmod, jacobi_two_three]
  · have hp4 : p % 4 = 3 := by omega
    have hQR : jacobiSym 3 p = -jacobiSym p 3 :=
      jacobiSym.quadratic_reciprocity_three_mod_four (by decide : (3 : ℕ) % 4 = 3) hp4
    rw [if_neg (by omega), hQR, hmod, jacobi_two_three]
    ring

lemma chi4_eval {p : ℕ} (h : p % 24 = 5 ∨ p % 24 = 11) :
    ZMod.χ₄ p = if p % 24 = 5 then 1 else -1 := by
  rcases h with h5 | h11
  · have : p % 4 = 1 := by omega
    rw [if_pos h5, ZMod.χ₄_nat_one_mod_four this]
  · have : p % 4 = 3 := by omega
    rw [if_neg (by omega), ZMod.χ₄_nat_three_mod_four this]

lemma chi8_eval {p : ℕ} (h : p % 24 = 5 ∨ p % 24 = 11) :
    ZMod.χ₈ p = -1 := by
  rw [ZMod.χ₈_nat_eq_if_mod_eight]
  rcases h with h5 | h11
  · have : p % 8 = 5 := by omega
    split_ifs <;> omega
  · have : p % 8 = 3 := by omega
    split_ifs <;> omega

lemma legendre_neg_six_eq_one {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (h : p % 24 = 5 ∨ p % 24 = 11) :
    legendreSym p (-6) = 1 := by
  have hfac : (-6 : ℤ) = (-1) * 2 * 3 := by ring
  rw [hfac, legendreSym.mul, legendreSym.mul, legendreSym.at_neg_one hp2,
    legendreSym.at_two hp2, jacobiSym.legendreSym.to_jacobiSym]
  rw [chi4_eval h, chi8_eval h, jacobi_three_p_of_mod24 h]
  rcases h with h5 | h11
  · simp [h5]
  · simp [h11]

lemma not_dvd_six_of_mod24 {p : ℕ} [hp : Fact p.Prime]
    (h : p % 24 = 5 ∨ p % 24 = 11) : ¬ p ∣ 6 := by
  intro hd
  have : p = 2 ∨ p = 3 := by
    have := (hp.out.dvd_mul (m := 2) (n := 3)).mp (by simpa using hd)
    rcases this with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h2)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp.out (by decide : Nat.Prime 3)).mp h3)
  rcases this with rfl | rfl <;> omega

lemma exists_sq_neg_six {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (h : p % 24 = 5 ∨ p % 24 = 11) : IsSquare (-6 : ZMod p) := by
  have h0 : ((-6 : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    have : (6 : ZMod p) = 0 := by
      have := congrArg Neg.neg hz
      simpa using this
    have : p ∣ 6 := (ZMod.natCast_eq_zero_iff 6 p).mp this
    exact not_dvd_six_of_mod24 h this
  have : IsSquare ((-6 : ℤ) : ZMod p) :=
    (legendreSym.eq_one_iff p h0).mp (legendre_neg_six_eq_one hp2 h)
  simpa using this

lemma two_ne_zero_zmod {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro hz
  have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hz)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)

lemma exists_t_two_mul_sq_add_three {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (h : p % 24 = 5 ∨ p % 24 = 11) :
    ∃ t : ZMod p, (2 : ZMod p) * t ^ 2 + 3 = 0 := by
  obtain ⟨s, hs⟩ := exists_sq_neg_six (p := p) hp2 h
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  refine ⟨s * 2⁻¹, ?_⟩
  have hs2 : s ^ 2 = (-6 : ZMod p) := by
    simpa [pow_two] using hs.symm
  have hinv : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  have : (s * 2⁻¹) ^ 2 = s ^ 2 * (2⁻¹) ^ 2 := by ring
  rw [this, hs2]
  have h4 : (2 : ZMod p) * (2⁻¹) ^ 2 = 2⁻¹ := by
    calc
      (2 : ZMod p) * (2⁻¹) ^ 2 = (2 * 2⁻¹) * 2⁻¹ := by ring
      _ = 1 * 2⁻¹ := by rw [hinv]
      _ = 2⁻¹ := by ring
  calc
    (2 : ZMod p) * ((-6) * (2⁻¹) ^ 2) + 3
        = -12 * (2⁻¹) ^ 2 + 3 := by ring
    _ = -6 * (2 * (2⁻¹) ^ 2) + 3 := by ring
    _ = -6 * 2⁻¹ + 3 := by rw [h4]
    _ = -3 * (2 * 2⁻¹) + 3 := by ring
    _ = -3 * 1 + 3 := by rw [hinv]
    _ = 0 := by ring


lemma six_mul_sq_mod24 (b : ℕ) :
    6 * b ^ 2 % 24 = 0 ∨ 6 * b ^ 2 % 24 = 6 := by
  by_cases hb : Even b
  · obtain ⟨k, hk⟩ := even_iff_two_dvd.mp hb
    have : 6 * b ^ 2 = 24 * k ^ 2 := by
      rw [hk]; ring
    left
    rw [this, Nat.mul_mod_right]
  · have hodd : Odd b := Nat.not_even_iff_odd.mp hb
    have hlt : b % 24 < 24 := Nat.mod_lt b (by decide)
    have : b ^ 2 % 24 = 1 ∨ b ^ 2 % 24 = 9 := by
      have hm : b ^ 2 % 24 = (b % 24) ^ 2 % 24 := Nat.pow_mod b 2 24
      rw [hm]
      have : (b % 24) % 2 = 1 := by
        have : b % 2 = 1 := Nat.odd_iff.mp hodd
        omega
      interval_cases b % 24 <;> first | decide | omega
    rcases this with h1 | h9 <;> omega

lemma sq_mod24 (a : ℕ) :
    a ^ 2 % 24 = 0 ∨ a ^ 2 % 24 = 1 ∨ a ^ 2 % 24 = 4 ∨ a ^ 2 % 24 = 9 ∨
    a ^ 2 % 24 = 12 ∨ a ^ 2 % 24 = 13 ∨ a ^ 2 % 24 = 16 := by
  have : a ^ 2 % 24 = (a % 24) ^ 2 % 24 := Nat.pow_mod a 2 24
  rw [this]
  have : a % 24 < 24 := Nat.mod_lt a (by decide)
  interval_cases a % 24 <;> decide

lemma not_eq_sq_add_six_sq_of_mod24 {p a b : ℕ}
    (h : p % 24 = 5 ∨ p % 24 = 11) (heq : p = a ^ 2 + 6 * b ^ 2) : False := by
  have hsum : (a ^ 2 + 6 * b ^ 2) % 24 = p % 24 := by rw [heq]
  have ha := sq_mod24 a
  have hb := six_mul_sq_mod24 b
  have hval : (a ^ 2 + 6 * b ^ 2) % 24 ≠ 5 ∧ (a ^ 2 + 6 * b ^ 2) % 24 ≠ 11 := by
    rcases ha with ha | ha | ha | ha | ha | ha | ha <;>
      rcases hb with hb | hb <;> omega
  rcases h with h5 | h11
  · exact hval.1 (hsum.trans h5)
  · exact hval.2 (hsum.trans h11)

lemma prime_not_sq {p k : ℕ} (hp : p.Prime) (heq : p = k ^ 2) : False := by
  have hk1 : 1 < k := by
    by_contra hle
    have : k ≤ 1 := Nat.not_lt.mp hle
    interval_cases k
    · simp at heq; exact hp.ne_zero heq
    · simp at heq; exact hp.ne_one heq
  have : ¬ p.Prime := by
    rw [heq, pow_two]
    exact Nat.not_prime_mul (by omega) (by omega)
  exact this hp

lemma prime_sqrt_lt {p : ℕ} (hp : p.Prime) : p.sqrt ^ 2 < p := by
  have hle : p.sqrt ^ 2 ≤ p := Nat.sqrt_le' p
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exact (prime_not_sq hp h.symm).elim

lemma abs_sub_of_lt_succ {a b s : ℕ} (ha : a < s + 1) (hb : b < s + 1) :
    |((a : ℤ) - (b : ℤ))| ≤ (s : ℤ) := by
  have ha' : (a : ℤ) ≤ s := by exact_mod_cast (Nat.lt_succ_iff.mp ha)
  have hb' : (b : ℤ) ≤ s := by exact_mod_cast (Nat.lt_succ_iff.mp hb)
  cases le_total a b with
  | inl h =>
    have : (b : ℤ) - a ≤ s := by
      have : b - a ≤ s := by omega
      exact_mod_cast this
    rw [abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr h))]
    linarith
  | inr h =>
    have : (a : ℤ) - b ≤ s := by
      have : a - b ≤ s := by omega
      exact_mod_cast this
    rw [abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h))]
    linarith

lemma two_sq_three_sq_le_of_abs {u v : ℤ} {s : ℕ}
    (hu : |u| ≤ (s : ℤ)) (hv : |v| ≤ (s : ℤ)) :
    2 * u ^ 2 + 3 * v ^ 2 ≤ 5 * (s : ℤ) ^ 2 := by
  have hu2 : u ^ 2 ≤ (s : ℤ) ^ 2 :=
    sq_le_sq.mpr (by simpa [abs_of_nonneg (Int.natCast_nonneg s)] using hu)
  have hv2 : v ^ 2 ≤ (s : ℤ) ^ 2 :=
    sq_le_sq.mpr (by simpa [abs_of_nonneg (Int.natCast_nonneg s)] using hv)
  nlinarith

lemma even_of_three_mul_even {n : ℕ} (h : Even (3 * n)) : Even n := by
  rw [Nat.even_mul] at h
  exact h.resolve_left (by decide)

lemma sq_mod8 (a : ℕ) : a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4 := by
  have : a ^ 2 % 8 = (a % 8) ^ 2 % 8 := Nat.pow_mod a 2 8
  rw [this]
  have : a % 8 < 8 := Nat.mod_lt a (by decide)
  interval_cases a % 8 <;> decide

lemma even_of_sq_mod8_zero {a : ℕ} (h : a ^ 2 % 8 = 0) : Even a := by
  have hm : a ^ 2 % 8 = (a % 8) ^ 2 % 8 := Nat.pow_mod a 2 8
  rw [hm] at h
  have : a % 8 < 8 := Nat.mod_lt a (by decide)
  interval_cases h8 : a % 8
  · exact even_iff_two_dvd.mpr (Nat.dvd_of_mod_eq_zero (by omega))
  · simp at h
  · exact even_iff_two_dvd.mpr (by omega)
  · simp at h
  · exact even_iff_two_dvd.mpr (by omega)
  · simp at h
  · exact even_iff_two_dvd.mpr (by omega)
  · simp at h

lemma even_of_sq_mod8_four {a : ℕ} (h : a ^ 2 % 8 = 4) : Even a := by
  have hm : a ^ 2 % 8 = (a % 8) ^ 2 % 8 := Nat.pow_mod a 2 8
  rw [hm] at h
  have : a % 8 < 8 := Nat.mod_lt a (by decide)
  interval_cases h8 : a % 8
  · simp at h
  · simp at h
  · exact even_iff_two_dvd.mpr (by omega)
  · simp at h
  · simp at h
  · simp at h
  · exact even_iff_two_dvd.mpr (by omega)
  · simp at h

lemma odd_of_sq_mod8_one {a : ℕ} (h : a ^ 2 % 8 = 1) : Odd a := by
  have hm : a ^ 2 % 8 = (a % 8) ^ 2 % 8 := Nat.pow_mod a 2 8
  rw [hm] at h
  have : a % 8 < 8 := Nat.mod_lt a (by decide)
  interval_cases h8 : a % 8
  · simp at h
  · exact Nat.odd_iff.mpr (by omega)
  · simp at h
  · exact Nat.odd_iff.mpr (by omega)
  · simp at h
  · exact Nat.odd_iff.mpr (by omega)
  · simp at h
  · exact Nat.odd_iff.mpr (by omega)

lemma two_mul_sq_mod8_of_even {a : ℕ} (h : Even a) : 2 * a ^ 2 % 8 = 0 := by
  obtain ⟨k, hk⟩ := even_iff_two_dvd.mp h
  have : a ^ 2 = 4 * k ^ 2 := by rw [hk]; ring
  rw [this]
  omega

lemma form_four_mul {A B p : ℕ}
    (heq : 2 * A ^ 2 + 3 * B ^ 2 = 4 * p)
    (hpodd : p % 2 = 1) :
    Even A ∧ Even B := by
  have hmod : (2 * A ^ 2 + 3 * B ^ 2) % 8 = 4 := by
    rw [heq]; omega
  have hAs := sq_mod8 A
  have hBs := sq_mod8 B
  -- If A odd then A²≡1, 2A²≡2, 2+3B² ≡4 ⇒ 3B²≡2 mod 8, impossible
  have hAeven : Even A := by
    rcases hAs with hA | hA | hA
    · exact even_of_sq_mod8_zero hA
    · have : Odd A := odd_of_sq_mod8_one hA
      have : 2 * A ^ 2 % 8 = 2 := by omega
      have : 3 * B ^ 2 % 8 = 2 := by omega
      rcases hBs with hB | hB | hB <;> omega
    · exact even_of_sq_mod8_four hA
  have hBeven : Even B := by
    have : 2 * A ^ 2 % 8 = 0 := two_mul_sq_mod8_of_even hAeven
    have : 3 * B ^ 2 % 8 = 4 := by omega
    rcases hBs with hB | hB | hB
    · omega
    · omega
    · exact even_of_sq_mod8_four hB
  exact ⟨hAeven, hBeven⟩

lemma form_four_mul_repr {A B p : ℕ}
    (heq : 2 * A ^ 2 + 3 * B ^ 2 = 4 * p)
    (hpodd : p % 2 = 1) :
    ∃ r t, p = 2 * r ^ 2 + 3 * t ^ 2 := by
  obtain ⟨hA, hB⟩ := form_four_mul heq hpodd
  obtain ⟨r, hr⟩ := even_iff_two_dvd.mp hA
  obtain ⟨t, ht⟩ := even_iff_two_dvd.mp hB
  refine ⟨r, t, ?_⟩
  have : 2 * (2 * r) ^ 2 + 3 * (2 * t) ^ 2 = 4 * p := by
    rw [← hr, ← ht]; exact heq
  nlinarith

set_option maxHeartbeats 800000

lemma two_mul_sq_add_three_mul_sq_mod {p : ℕ} [Fact p.Prime]
    {t u v : ZMod p} (ht : (2 : ZMod p) * t ^ 2 + 3 = 0) (hu : u = t * v) :
    (2 : ZMod p) * u ^ 2 + 3 * v ^ 2 = 0 := by
  rw [hu]
  have : (2 : ZMod p) * (t * v) ^ 2 + 3 * v ^ 2
      = ((2 : ZMod p) * t ^ 2 + 3) * v ^ 2 := by ring
  rw [this, ht, zero_mul]

/-- A prime `p ≡ 5 or 11 (mod 24)` is represented by the form `2a² + 3b²`. -/
lemma prime_eq_two_sq_add_three_sq {p : ℕ} (hpp : p.Prime)
    (h : p % 24 = 5 ∨ p % 24 = 11) :
    ∃ a b : ℕ, p = 2 * a ^ 2 + 3 * b ^ 2 := by
  haveI : Fact p.Prime := ⟨hpp⟩
  have hp2 : p ≠ 2 := by intro hp2; subst hp2; omega
  obtain ⟨t, ht⟩ := exists_t_two_mul_sq_add_three (p := p) hp2 h
  set s := p.sqrt
  have hs2 : s ^ 2 < p := prime_sqrt_lt hpp
  let I : Finset ℕ := Finset.range (s + 1)
  let S : Finset (ℕ × ℕ) := I ×ˢ I
  have hScard : S.card = (s + 1) ^ 2 := by
    simp [S, I, Finset.card_product, pow_two]
  have hScard_gt : p < S.card := by
    have : p < (s + 1) ^ 2 := Nat.lt_succ_sqrt' p
    rwa [hScard]
  let f : ℕ × ℕ → ZMod p := fun q => (q.1 : ZMod p) - t * (q.2 : ZMod p)
  have him : (S.image f).card ≤ p := by
    have : (S.image f).card ≤ Fintype.card (ZMod p) := Finset.card_le_univ _
    simpa [ZMod.card] using this
  have hltimg : (S.image f).card < S.card := lt_of_le_of_lt him hScard_gt
  obtain ⟨q1, hq1, q2, hq2, hneq, hfeq⟩ :=
    Finset.exists_ne_map_eq_of_card_image_lt (s := S) (f := f) hltimg
  have hq1r : q1.1 < s + 1 ∧ q1.2 < s + 1 := by
    have := Finset.mem_product.mp hq1
    exact ⟨Finset.mem_range.mp this.1, Finset.mem_range.mp this.2⟩
  have hq2r : q2.1 < s + 1 ∧ q2.2 < s + 1 := by
    have := Finset.mem_product.mp hq2
    exact ⟨Finset.mem_range.mp this.1, Finset.mem_range.mp this.2⟩
  set u : ℤ := (q1.1 : ℤ) - (q2.1 : ℤ)
  set v : ℤ := (q1.2 : ℤ) - (q2.2 : ℤ)
  have hune : ¬ (u = 0 ∧ v = 0) := by
    intro ⟨hu0, hv0⟩
    apply hneq
    apply Prod.ext
    · exact_mod_cast (sub_eq_zero.mp hu0)
    · exact_mod_cast (sub_eq_zero.mp hv0)
  have hu_b : |u| ≤ (s : ℤ) := abs_sub_of_lt_succ hq1r.1 hq2r.1
  have hv_b : |v| ≤ (s : ℤ) := abs_sub_of_lt_succ hq1r.2 hq2r.2
  have hrel : (u : ZMod p) = t * (v : ZMod p) := by
    have hf : (q1.1 : ZMod p) - t * (q1.2 : ZMod p)
        = (q2.1 : ZMod p) - t * (q2.2 : ZMod p) := hfeq
    have : (q1.1 : ZMod p) - (q2.1 : ZMod p)
        = t * ((q1.2 : ZMod p) - (q2.2 : ZMod p)) := by
      linear_combination hf
    simpa [u, v] using this
  have hformZ : (2 : ZMod p) * (u : ZMod p) ^ 2 + 3 * (v : ZMod p) ^ 2 = 0 :=
    two_mul_sq_add_three_mul_sq_mod ht hrel
  have hdiv : (p : ℤ) ∣ 2 * u ^ 2 + 3 * v ^ 2 := by
    have : ((2 * u ^ 2 + 3 * v ^ 2 : ℤ) : ZMod p) = 0 := by
      push_cast
      exact hformZ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp this
  obtain ⟨k, hk⟩ := hdiv
  have hQpos : 0 < 2 * u ^ 2 + 3 * v ^ 2 := by
    have : 0 ≤ 2 * u ^ 2 + 3 * v ^ 2 := by nlinarith [sq_nonneg u, sq_nonneg v]
    refine lt_of_le_of_ne this ?_
    intro hz
    have hu0 : u = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    have hv0 : v = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    exact hune ⟨hu0, hv0⟩
  have hQle : 2 * u ^ 2 + 3 * v ^ 2 ≤ 5 * ((p : ℤ) - 1) := by
    have h1 : 2 * u ^ 2 + 3 * v ^ 2 ≤ 5 * (s : ℤ) ^ 2 :=
      two_sq_three_sq_le_of_abs hu_b hv_b
    have h2 : (s : ℤ) ^ 2 ≤ (p : ℤ) - 1 := by
      have : (s ^ 2 : ℕ) + 1 ≤ p := Nat.succ_le_iff.mpr hs2
      have : (s ^ 2 : ℤ) + 1 ≤ p := by exact_mod_cast this
      linarith
    nlinarith
  have hkcomm : 2 * u ^ 2 + 3 * v ^ 2 = k * (p : ℤ) := by
    rw [hk, mul_comm]
  have hkpos : 0 < k := by
    have : 0 < k * (p : ℤ) := by rwa [← hkcomm]
    have : 0 < (p : ℤ) := by exact_mod_cast hpp.pos
    nlinarith
  have hk4 : k ≤ 4 := by
    have : k * (p : ℤ) ≤ 5 * ((p : ℤ) - 1) := by
      rw [← hkcomm]; exact hQle
    have hppos : (0 : ℤ) < p := by exact_mod_cast hpp.pos
    nlinarith
  have hk_nonneg : 0 ≤ k := le_of_lt hkpos
  have habs : 2 * u.natAbs ^ 2 + 3 * v.natAbs ^ 2 = k.natAbs * p := by
    have : (2 * u.natAbs ^ 2 + 3 * v.natAbs ^ 2 : ℤ) = k.natAbs * p := by
      simp [Int.natAbs_of_nonneg hk_nonneg]
      linarith [hkcomm]
    exact_mod_cast this
  have hk1_4 : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hk1_4 with hk1 | hk2 | hk3 | hk4'
  · subst hk1
    refine ⟨u.natAbs, v.natAbs, ?_⟩
    simpa using habs.symm
  · subst hk2
    have heq : 2 * u.natAbs ^ 2 + 3 * v.natAbs ^ 2 = 2 * p := by simpa using habs
    have hve : Even v.natAbs := by
      have : Even (3 * v.natAbs ^ 2) := by
        have : 3 * v.natAbs ^ 2 = 2 * (p - u.natAbs ^ 2) := by omega
        exact even_iff_two_dvd.mpr ⟨p - u.natAbs ^ 2, this⟩
      have : Even (v.natAbs ^ 2) := even_of_three_mul_even this
      exact (Nat.even_pow.mp this).1
    obtain ⟨w, hw⟩ := even_iff_two_dvd.mp hve
    have : p = u.natAbs ^ 2 + 6 * w ^ 2 := by
      have hw2 : v.natAbs = 2 * w := hw
      have : 2 * u.natAbs ^ 2 + 3 * v.natAbs ^ 2 = 2 * u.natAbs ^ 2 + 3 * (2 * w) ^ 2 := by
        rw [hw2]
      nlinarith
    exact (not_eq_sq_add_six_sq_of_mod24 h this).elim
  · subst hk3
    have heq : 2 * u.natAbs ^ 2 + 3 * v.natAbs ^ 2 = 3 * p := by simpa using habs
    have h3p : Nat.Prime 3 := by decide
    have : 3 ∣ 2 * u.natAbs ^ 2 := by
      have : 2 * u.natAbs ^ 2 = 3 * (p - v.natAbs ^ 2) := by omega
      exact ⟨p - v.natAbs ^ 2, this⟩
    have : 3 ∣ u.natAbs ^ 2 :=
      ((Nat.Prime.dvd_mul h3p).mp this).resolve_left (by decide)
    have hu3 : 3 ∣ u.natAbs := h3p.dvd_of_dvd_pow this
    obtain ⟨w, hw⟩ := hu3
    have : p = v.natAbs ^ 2 + 6 * w ^ 2 := by
      have : 2 * u.natAbs ^ 2 + 3 * v.natAbs ^ 2 = 2 * (3 * w) ^ 2 + 3 * v.natAbs ^ 2 := by
        rw [hw]
      nlinarith
    exact (not_eq_sq_add_six_sq_of_mod24 h this).elim
  · subst hk4'
    have heq : 2 * u.natAbs ^ 2 + 3 * v.natAbs ^ 2 = 4 * p := by simpa using habs
    have hpodd : p % 2 = 1 := by omega
    exact form_four_mul_repr heq hpodd

set_option maxHeartbeats 400000

/- Family-2 algebraic identities -/

lemma dickson_to_sum {y z w : ℕ} :
    ((y + z) ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) * 2
      = (2 * y + z) ^ 2 + 2 * w ^ 2 + 3 * z ^ 2 := by
  ring

lemma sum_to_dickson {u v w : ℕ} (hpar : u % 2 = v % 2) (hge : v ≤ u) :
    let y := (u - v) / 2
    ((y + v) ^ 2 + y ^ 2 + v ^ 2 + w ^ 2) * 2
      = u ^ 2 + 2 * w ^ 2 + 3 * v ^ 2 := by
  intro y
  have h2 : 2 ∣ u - v := by
    have : u % 2 = v % 2 := hpar
    omega
  have hy : 2 * y = u - v := Nat.mul_div_cancel' h2
  have : y + v = (u + v) / 2 := by
    have : 2 * (y + v) = u + v := by
      have : 2 * y + 2 * v = u - v + 2 * v := by rw [hy]
      have : u - v + 2 * v = u + v := by omega
      omega
    omega
  have hsum : 2 * ((y + v) ^ 2 + y ^ 2 + v ^ 2 + w ^ 2)
      = (2 * y + v) ^ 2 + 2 * w ^ 2 + 3 * v ^ 2 := by
    ring
  have : 2 * y + v = u := by omega
  rw [mul_comm, hsum, this]

lemma eisenstein_mul (u v : ℤ) :
    (u + 3 * v) ^ 2 + 3 * (u - v) ^ 2 = 4 * (u ^ 2 + 3 * v ^ 2) := by
  ring

lemma eisenstein_int {u v : ℤ} (hpar : u % 2 = v % 2) :
    ((u + 3 * v) / 2) ^ 2 + 3 * ((u - v) / 2) ^ 2 = u ^ 2 + 3 * v ^ 2 := by
  have h1 : 2 ∣ u + 3 * v := by
    have : (u + 3 * v) % 2 = 0 := by omega
    exact Int.dvd_iff_emod_eq_zero.mpr this
  have h2 : 2 ∣ u - v := by
    have : (u - v) % 2 = 0 := by omega
    exact Int.dvd_iff_emod_eq_zero.mpr this
  have := eisenstein_mul u v
  have : 4 * (((u + 3 * v) / 2) ^ 2 + 3 * ((u - v) / 2) ^ 2)
      = (u + 3 * v) ^ 2 + 3 * (u - v) ^ 2 := by
    have ha : 2 * ((u + 3 * v) / 2) = u + 3 * v := Int.mul_ediv_cancel' h1
    have hb : 2 * ((u - v) / 2) = u - v := Int.mul_ediv_cancel' h2
    have : 4 * ((u + 3 * v) / 2) ^ 2 = (u + 3 * v) ^ 2 := by
      have : (2 * ((u + 3 * v) / 2)) ^ 2 = (u + 3 * v) ^ 2 := by rw [ha]
      have : 4 * ((u + 3 * v) / 2) ^ 2 = (2 * ((u + 3 * v) / 2)) ^ 2 := by ring
      linarith
    have : 4 * (3 * ((u - v) / 2) ^ 2) = 3 * (u - v) ^ 2 := by
      have : (2 * ((u - v) / 2)) ^ 2 = (u - v) ^ 2 := by rw [hb]
      nlinarith
    nlinarith
  nlinarith

lemma two_n_of_family2 {y z w n : ℕ}
    (h : (y + z) ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n) :
    (2 * y + z) ^ 2 + 2 * w ^ 2 + 3 * z ^ 2 = 2 * n := by
  have := dickson_to_sum (y := y) (z := z) (w := w)
  linarith

lemma family2_of_dickson {u v w n : ℕ}
    (h : u ^ 2 + 2 * w ^ 2 + 3 * v ^ 2 = 2 * n)
    (hpar : u % 2 = v % 2) (hge : v ≤ u) :
    let y := (u - v) / 2
    (y + v) ^ 2 + y ^ 2 + v ^ 2 + w ^ 2 = n := by
  intro y
  have := sum_to_dickson (u := u) (v := v) (w := w) hpar hge
  simp at this
  have : 2 * ((y + v) ^ 2 + y ^ 2 + v ^ 2 + w ^ 2) = 2 * n := by
    dsimp [y] at this ⊢
    linarith
  exact Nat.mul_left_cancel (by decide : 0 < 2) this


/- Parity for Dickson representations of N ≡ 14 (mod 16). -/

lemma sq_mod16 (a : ℤ) : a ^ 2 % 16 = 0 ∨ a ^ 2 % 16 = 1 ∨ a ^ 2 % 16 = 4 ∨
    a ^ 2 % 16 = 9 := by
  have h : a % 16 = 0 ∨ a % 16 = 1 ∨ a % 16 = 2 ∨ a % 16 = 3 ∨
      a % 16 = 4 ∨ a % 16 = 5 ∨ a % 16 = 6 ∨ a % 16 = 7 ∨
      a % 16 = 8 ∨ a % 16 = 9 ∨ a % 16 = 10 ∨ a % 16 = 11 ∨
      a % 16 = 12 ∨ a % 16 = 13 ∨ a % 16 = 14 ∨ a % 16 = 15 := by omega
  have hm : a ^ 2 % 16 = (a % 16) ^ 2 % 16 := by
    have := Int.mul_emod a a 16
    simpa [pow_two] using this
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    simp [hm, h]

lemma odd_sq_mod16 {a : ℤ} (h : Odd a) : a ^ 2 % 16 = 1 ∨ a ^ 2 % 16 = 9 := by
  have ha := sq_mod16 a
  have : a % 2 = 1 := Int.odd_iff.mp h
  have : ¬ (a ^ 2 % 16 = 0) ∧ ¬ (a ^ 2 % 16 = 4) := by
    have hsq : a ^ 2 % 2 = 1 := by
      have := Int.mul_emod a a 2
      have : a % 2 = 1 := this
      simp [pow_two]
      omega
    omega
  omega

lemma dickson_mod16_of_odd {a b c : ℤ} (ha : Odd a) (hb : Odd b) (hc : Odd c) :
    (a ^ 2 + 2 * b ^ 2 + 3 * c ^ 2) % 16 = 6 ∨
    (a ^ 2 + 2 * b ^ 2 + 3 * c ^ 2) % 16 = 14 := by
  have ha2 := odd_sq_mod16 ha
  have hb2 := odd_sq_mod16 hb
  have hc2 := odd_sq_mod16 hc
  have h2 : (2 * b ^ 2) % 16 = 2 := by
    rcases hb2 with h | h <;> omega
  have h3 : (3 * c ^ 2) % 16 = 3 ∨ (3 * c ^ 2) % 16 = 11 := by
    rcases hc2 with h | h <;> omega
  rcases ha2 with h1 | h1 <;> rcases h3 with h3 | h3 <;> omega

lemma even_of_even_sq {a : ℤ} (h : Even (a ^ 2)) : Even a := by
  rw [even_iff_two_dvd, pow_two] at h ⊢
  exact Int.Prime.dvd_of_dvd_pow Int.prime_two h

lemma odd_of_dickson_denom {N : ℕ} {a b c d : ℤ}
    (hN : (N : ℤ) % 16 = 14)
    (h : a ^ 2 + 2 * b ^ 2 + 3 * c ^ 2 = N * d ^ 2)
    (hd0 : d ≠ 0)
    (hprim : Int.gcd (Int.gcd (Int.gcd a.natAbs b.natAbs) c.natAbs) d.natAbs = 1) :
    Odd d := by
  by_contra he
  have hde : Even d := Nat.not_odd_iff_even.mp (by
    rw [Int.odd_iff_natAbs_odd] at he
    exact he)
  obtain ⟨d2, hd2⟩ := even_iff_two_dvd.mp hde
  have : (N : ℤ) * d ^ 2 % 16 = (a ^ 2 + 2 * b ^ 2 + 3 * c ^ 2) % 16 := by
    rw [h]
  -- d even: d = 2 d2, d^2 ≡ 0 or 4 mod 16
  have hd4 : (4 : ℤ) ∣ d ^ 2 := by
    have : d = 2 * d2 := by linarith
    rw [this]; ring_nf; exact ⟨d2 ^ 2, by ring⟩
  have : (N : ℤ) * d ^ 2 % 8 = 0 := by
    have : (8 : ℤ) ∣ N * d ^ 2 := by
      have h4 : (4 : ℤ) ∣ d ^ 2 := hd4
      have hN2 : (2 : ℤ) ∣ N := by omega
      obtain ⟨k, hk⟩ := h4
      obtain ⟨m, hm⟩ := hN2
      refine ⟨m * k, ?_⟩
      rw [hm, hk]; ring
    omega
  have hQ8 : (a ^ 2 + 2 * b ^ 2 + 3 * c ^ 2) % 8 = 0 := by omega
  -- analyze a,b,c mod 2
  have : Even a ∧ Even b ∧ Even c := by
    -- squares mod 8: 0,1,4; 2b^2: 0,2; 3c^2: 0,3,4
    have ha2 := Int.emod_two_eq_zero_or_one a
    have hb2 := Int.emod_two_eq_zero_or_one b
    have hc2 := Int.emod_two_eq_zero_or_one c
    -- if any is odd we get Q ≢ 0 mod 8 when d≡0 mod 2 and N≡14 mod 16
    -- d even: if d ≡ 2 mod 4 then d^2 ≡ 4 mod 16, N d^2 ≡ 14*4 = 56 ≡ 8 mod 16, wait
    -- we'll do a coarser mod 8 argument
    sorry
  -- then gcd ≥ 2, contradiction
  sorry

