import Submission.CoprimeIntervals
import Submission.ShiftedParity
import Submission.LocalObstructions

/-!
# Finite-divisor obstructions for shifted rational slopes

Auxiliary work for Erdős 972. Coprimality with prescribed divisors is not
simultaneous primality.

The final theorem rules out irrational limits of positive reduced rational
models whose shifted outputs at all sufficiently large prime inputs are
covered by a fixed finite set of prime divisors. Both the shift and the finite
set may vary from one model to the next. This obstruction hypothesis is
stronger than merely having composite outputs, so the result does not settle
the original conjecture.
-/

namespace Explore972

lemma linear_pair_admissible_of_coprime_det (a b r s k : ℤ)
    (hdet : a * r - b * s = k) (hkc : IsCoprime k (a * b))
    (hro : Odd r) (hso : Odd s) :
    ∀ l : ℕ, l.Prime → ∃ t : ℤ,
      ¬ (l : ℤ) ∣ b * t + r ∧ ¬ (l : ℤ) ∣ a * t + s := by
  intro l hl
  by_cases hl2 : l = 2
  · subst l
    refine ⟨0, ?_, ?_⟩
    · simpa using (show ¬ (2 : ℤ) ∣ r from fun h =>
        (Int.not_even_iff_odd.mpr hro) (even_iff_two_dvd.mpr h))
    · simpa using (show ¬ (2 : ℤ) ∣ s from fun h =>
        (Int.not_even_iff_odd.mpr hso) (even_iff_two_dvd.mpr h))
  letI : Fact l.Prime := ⟨hl⟩
  have hlarge : 2 < l := by have := hl.two_le; omega
  have hdetz : (a : ZMod l) * r - b * s = k := by
    simpa using congrArg (fun z : ℤ => (z : ZMod l)) hdet
  have hcz : IsCoprime (k : ZMod l) ((a : ZMod l) * b) := by
    simpa using (hkc.intCast (R := ZMod l))
  have hbr : (b : ZMod l) ≠ 0 ∨ (r : ZMod l) ≠ 0 := by
    by_contra! h
    have hkz : (k : ZMod l) = 0 := by simpa [h.1, h.2] using hdetz.symm
    have hn := hcz.ne_zero_or_ne_zero
    simp [hkz, h.1] at hn
  have has : (a : ZMod l) ≠ 0 ∨ (s : ZMod l) ≠ 0 := by
    by_contra! h
    have hkz : (k : ZMod l) = 0 := by simpa [h.1, h.2] using hdetz.symm
    have hn := hcz.ne_zero_or_ne_zero
    simp [hkz, h.1] at hn
  obtain ⟨t, ht₁, ht₂⟩ := exists_affine_pair_ne_zero
    (by simpa only [ZMod.card] using hlarge) (b : ZMod l) a r s hbr has
  refine ⟨(t.val : ℤ), ?_, ?_⟩
  · intro hdiv
    have he := (ZMod.intCast_zmod_eq_zero_iff_dvd (b * t.val + r) l).mpr hdiv
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] at he
    exact ht₁ he
  · intro hdiv
    have he := (ZMod.intCast_zmod_eq_zero_iff_dvd (a * t.val + s) l).mpr hdiv
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] at he
    exact ht₂ he

lemma shifted_prime_indices_coprime_of_model (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (β : ℝ) (r s : ℤ)
    (hfloor : ∀ t : ℤ,
      ⌊(a : ℝ) / b * ((b * t + r : ℤ) : ℝ) + β⌋ = (a : ℤ) * t + s)
    (hlocal : ∀ l : ℕ, l.Prime → ∃ t : ℤ,
      ¬ (l : ℤ) ∣ (b : ℤ) * t + r ∧ ¬ (l : ℤ) ∣ (a : ℤ) * t + s)
    (M : ℕ) (hM : 0 < M) (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ (⌊(a : ℝ) / b * p + β⌋₊).Coprime M := by
  have hα : (0 : ℝ) < (a : ℝ) / b := by positivity
  obtain ⟨L, hL⟩ := exists_nat_gt (-β / ((a : ℝ) / b))
  let Q : ℕ := b * M
  have hQ : Q ≠ 0 := mul_ne_zero hb.ne' hM.ne'
  obtain ⟨t₀, _, ht₀⟩ := locally_admissible_avoids_finite_primes a b r s hlocal
    Q.primeFactors (fun l hl => Nat.prime_of_mem_primeFactors hl) 0
  let v : ℤ := b * t₀ + r
  have hcop : IsCoprime v (Q : ℤ) := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simp only [Int.natAbs_natCast]
    by_contra h
    obtain ⟨l, hl, hlv, hlQ⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    exact (ht₀ l (Nat.mem_primeFactors.mpr ⟨hl, hlQ, hQ⟩)).1 (Int.natCast_dvd.mpr hlv)
  obtain ⟨p, hNp, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq (max N L) hQ hcop
  obtain ⟨k, hk⟩ := hmod.symm.dvd
  let t : ℤ := t₀ + M * k
  have hpeq : (p : ℤ) = b * t + r := by
    dsimp [v, Q] at hk
    dsimp [t]
    push_cast at hk
    nlinarith
  have hfl : ⌊(a : ℝ) / b * p + β⌋ = (a : ℤ) * t + s := by
    convert hfloor t using 1
    rw [← hpeq]
    simp only [Int.cast_natCast]
  have hpL : (L : ℝ) < p := by exact_mod_cast (lt_of_le_of_lt (le_max_right N L) hNp)
  have hx : 0 ≤ (a : ℝ) / b * p + β := by
    have h := (div_lt_iff₀ hα).mp (hL.trans hpL)
    nlinarith
  have hflnat : (⌊(a : ℝ) / b * p + β⌋₊ : ℤ) = (a : ℤ) * t + s := by
    rw [Int.natCast_floor_eq_floor hx, hfl]
  refine ⟨p, lt_of_le_of_lt (le_max_left N L) hNp, hp, ?_⟩
  by_contra h
  obtain ⟨l, hl, hlq, hlM⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hlQ : l ∈ Q.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hl, hlM.trans (dvd_mul_left M b), hQ⟩
  have hMm : (M : ℤ) ≡ 0 [ZMOD (l : ℤ)] :=
    (Int.natCast_dvd_natCast.mpr hlM).modEq_zero_int
  have htm : t ≡ (t₀ : ℤ) [ZMOD (l : ℤ)] := by
    simpa [t] using (hMm.mul_right k).add_left (t₀ : ℤ)
  apply (ht₀ l hlQ).2
  apply ((htm.mul_left (a : ℤ)).add_right s).dvd_iff.mp
  rw [← hflnat]
  exact Int.natCast_dvd_natCast.mpr hlq

lemma admissible_determinant_in_real_window (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b)
    (hlarge : 2 * ((4 : ℕ) ^ (2 * a * b).primeFactors.card + 2) ≤ b) (x : ℝ) :
    ∃ k : ℤ, x ≤ k ∧ (k : ℝ) < x + b ∧
      IsCoprime k ((a : ℤ) * b) ∧ k % 2 = ((a : ℤ) - b) % 2 := by
  let n : ℕ := 2 * a * b
  have hn : 0 < n := by dsimp [n]; positivity
  have hlargeR : 2 * ((4 : ℝ) ^ n.primeFactors.card + 2) ≤ b := by
    exact_mod_cast hlarge
  have hsplit {j : ℤ} (hj : IsCoprime j (n : ℤ)) :
      IsCoprime j (2 * ((a : ℤ) * b)) := by simpa [n, mul_assoc] using hj
  by_cases hoo : Odd a ∧ Odd b
  · obtain ⟨j, hjlo, hjhi, hjc⟩ := exists_coprime_in_real_interval n hn (x / 2)
    have hjab := (hsplit hjc).of_mul_right_right
    have h2 : IsCoprime (2 : ℤ) ((a : ℤ) * b) := by
      exact_mod_cast (hoo.1.mul hoo.2).coprime_two_left
    refine ⟨2 * j, ?_, ?_, h2.mul_left hjab, ?_⟩
    · push_cast
      linarith
    · push_cast
      linarith
    · have hamod : (a : ℤ) % 2 = 1 := Int.odd_iff.mp (by exact_mod_cast hoo.1)
      have hbmod : (b : ℤ) % 2 = 1 := Int.odd_iff.mp (by exact_mod_cast hoo.2)
      omega
  · obtain ⟨j, hjlo, hjhi, hjc⟩ := exists_coprime_in_real_interval n hn x
    have hj2 := (hsplit hjc).of_mul_right_left
    have hjo : Odd j := by
      apply Int.not_even_iff_odd.mp
      intro hj
      have hu := hj2.isUnit_of_dvd' (even_iff_two_dvd.mp hj) (dvd_refl (2 : ℤ))
      norm_num [Int.isUnit_iff] at hu
    have hdis : Odd a ∨ Odd b := by
      by_contra! h
      have hae : Even a := Nat.not_odd_iff_even.mp h.1
      have hbe : Even b := Nat.not_odd_iff_even.mp h.2
      have he := Nat.eq_one_of_dvd_coprimes hab
        (even_iff_two_dvd.mp hae) (even_iff_two_dvd.mp hbe)
      norm_num at he
    have hdiff : Odd ((a : ℤ) - b) := by
      rcases hdis with hao | hbo
      · have hbe : Even b := Nat.not_odd_iff_even.mp (fun hbo => hoo ⟨hao, hbo⟩)
        exact (show Odd (a : ℤ) by exact_mod_cast hao).sub_even
          (by exact_mod_cast hbe)
      · have hae : Even a := Nat.not_odd_iff_even.mp (fun hao => hoo ⟨hao, hbo⟩)
        exact (show Even (a : ℤ) by exact_mod_cast hae).sub_odd
          (by exact_mod_cast hbo)
    refine ⟨j, hjlo, ?_, (hsplit hjc).of_mul_right_right, ?_⟩
    · have hp : (0 : ℝ) ≤ (4 : ℝ) ^ n.primeFactors.card := by positivity
      linarith
    · rw [Int.odd_iff.mp hjo, Int.odd_iff.mp hdiff]

/-- A sufficiently large reduced denominator guarantees locally admissible,
floor-compatible affine forms for every real shift. -/
theorem large_denominator_shift_admissible (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b)
    (hlarge : 2 * ((4 : ℕ) ^ (2 * a * b).primeFactors.card + 2) ≤ b) (β : ℝ) :
    ∃ r s : ℤ,
      (∀ t : ℤ, ⌊(a : ℝ) / b * ((b * t + r : ℤ) : ℝ) + β⌋ = (a : ℤ) * t + s) ∧
      ∀ l : ℕ, l.Prime → ∃ t : ℤ,
        ¬ (l : ℤ) ∣ (b : ℤ) * t + r ∧ ¬ (l : ℤ) ∣ (a : ℤ) * t + s := by
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  obtain ⟨k, hklo, hkhi, hkc, hkpar⟩ :=
    admissible_determinant_in_real_window a b ha hb hab hlarge (-(b : ℝ) * β)
  obtain ⟨r, s, hdet, _, hro, hso⟩ :=
    shifted_odd_affine_model a b hab k hkc.of_mul_right_right hkpar
  refine ⟨r, s, ?_, linear_pair_admissible_of_coprime_det a b r s k hdet hkc hro hso⟩
  intro t
  apply floor_shifted_rational_affine a b r s k β (by exact_mod_cast hb)
  · push_cast
    have hk := (le_div_iff₀ hbr).mpr (show -β * b ≤ (k : ℝ) by nlinarith [hklo])
    linarith
  · push_cast
    have hk := (div_lt_iff₀ hbr).mpr (show (k : ℝ) < (1 - β) * b by nlinarith [hkhi])
    linarith
  · exact hdet

/-- Such shifted rational slopes avoid every prescribed finite set of prime
divisors at arbitrarily large prime inputs. -/
theorem large_denominator_shift_prime_indices_coprime (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b)
    (hlarge : 2 * ((4 : ℕ) ^ (2 * a * b).primeFactors.card + 2) ≤ b)
    (β : ℝ) (M : ℕ) (hM : 0 < M) (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ (⌊(a : ℝ) / b * p + β⌋₊).Coprime M := by
  obtain ⟨r, s, hfloor, hlocal⟩ := large_denominator_shift_admissible a b ha hb hab hlarge β
  exact shifted_prime_indices_coprime_of_model a b ha hb β r s hfloor hlocal M hM N

#print axioms large_denominator_shift_prime_indices_coprime

/-- A stronger property than mere compositeness: one fixed finite set of prime
divisors covers the outputs at every sufficiently large prime input. -/
def HasShiftedFiniteDivisorObstruction (a b : ℕ) : Prop :=
  ∃ β : ℝ, ∃ M : ℕ, 0 < M ∧ ∃ N : ℕ, ∀ p : ℕ, N < p → p.Prime →
    ¬ (⌊(a : ℝ) / b * p + β⌋₊).Coprime M

lemma shifted_obstruction_denominator_small (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (hobs : HasShiftedFiniteDivisorObstruction a b) :
    b < 2 * ((4 : ℕ) ^ (2 * a * b).primeFactors.card + 2) := by
  by_contra! hlarge
  obtain ⟨β, M, hM, N, hN⟩ := hobs
  obtain ⟨p, hNp, hp, hc⟩ :=
    large_denominator_shift_prime_indices_coprime a b ha hb hab hlarge β M hM N
  exact hN p hNp hp hc

/-- Within a bounded slope range, shifted finite-divisor obstructions have a
uniformly bounded reduced denominator. The numerical constant is crude. -/
theorem shifted_obstruction_denominator_bound (a b T : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (haT : a ≤ T * b) (hobs : HasShiftedFiniteDivisorObstruction a b) :
    b ≤ 2592 * (256 : ℕ) ^ 256 * T := by
  let R : ℕ := 4 ^ (2 * a * b).primeFactors.card
  let C : ℕ := 256 ^ 256
  let D : ℕ := 2592 * C * T
  have hR : 1 ≤ R := by
    have hpos : 0 < R := by dsimp [R]; positivity
    omega
  have hsmall : b < 2 * (R + 2) := shifted_obstruction_denominator_small a b ha hb hab hobs
  have h6 : b ≤ 6 * R := by omega
  have hR4 : R ^ 4 ≤ C * (2 * a * b) :=
    fourth_power_prime_factor_bound (2 * a * b) (by positivity)
  have hquart : b ^ 4 ≤ D * b ^ 2 := by
    calc
      b ^ 4 ≤ (6 * R) ^ 4 := Nat.pow_le_pow_left h6 4
      _ = 1296 * R ^ 4 := by ring
      _ ≤ 1296 * (C * (2 * a * b)) := Nat.mul_le_mul_left _ hR4
      _ = (2592 * C * b) * a := by ring
      _ ≤ (2592 * C * b) * (T * b) := Nat.mul_le_mul_left _ haT
      _ = D * b ^ 2 := by dsimp [D]; ring
  have hsq : b ^ 2 ≤ D := by
    apply Nat.le_of_mul_le_mul_right (a := b ^ 2) (b := D) (c := b ^ 2)
    · nlinarith only [hquart]
    · positivity
  change b ≤ D
  exact (show b ≤ b ^ 2 by nlinarith).trans hsq

open Filter in
open scoped Topology in
/-- A limit of rational slopes with uniformly bounded positive denominators
is rational. No assumptions about prime values are needed. -/
lemma bounded_denominator_limit_not_irrational {α : ℝ} (a b : ℕ → ℕ) (D : ℕ)
    (hb : ∀ n, 0 < b n) (hbd : ∀ n, b n ≤ D)
    (hlim : Tendsto (fun n => (a n : ℝ) / b n) atTop (𝓝 α)) : ¬ Irrational α := by
  have hmem : ∀ n, (D.factorial : ℝ) * ((a n : ℝ) / b n) ∈
      Set.range ((↑) : ℤ → ℝ) := by
    intro n
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (hb n) (hbd n)
    refine ⟨((c * a n : ℕ) : ℤ), ?_⟩
    have hbr : (b n : ℝ) ≠ 0 := by exact_mod_cast (hb n).ne'
    have hcr : (D.factorial : ℝ) = (b n : ℝ) * c := by exact_mod_cast hc
    push_cast
    rw [hcr]
    field_simp
  obtain ⟨z, hz⟩ := Int.isClosedEmbedding_coe_real.isClosed_range.mem_of_tendsto
    (hlim.const_mul (D.factorial : ℝ)) (Eventually.of_forall hmem)
  intro hi
  exact (hi.natCast_mul (Nat.factorial_ne_zero D)).ne_int z hz.symm

open Filter in
open scoped Topology in
/-- A sequence of bounded, reduced rational slopes with shifted finite-divisor
obstructions cannot converge to an irrational number. The shifts and covering
moduli may vary with the sequence index. -/
theorem shifted_finite_divisor_models_limit_not_irrational {α : ℝ} (a b : ℕ → ℕ) (T : ℕ)
    (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n) (hab : ∀ n, (a n).Coprime (b n))
    (haT : ∀ n, a n ≤ T * b n)
    (hobs : ∀ n, HasShiftedFiniteDivisorObstruction (a n) (b n))
    (hlim : Tendsto (fun n => (a n : ℝ) / b n) atTop (𝓝 α)) : ¬ Irrational α := by
  apply bounded_denominator_limit_not_irrational a b (2592 * (256 : ℕ) ^ 256 * T) hb _ hlim
  intro n
  exact shifted_obstruction_denominator_bound (a n) (b n) T (ha n) (hb n)
    (hab n) (haT n) (hobs n)

#print axioms shifted_obstruction_denominator_bound
#print axioms shifted_finite_divisor_models_limit_not_irrational

open Filter in
open scoped Topology in
/-- No convergent sequence of positive reduced rational slopes with shifted
finite-divisor obstructions has an irrational limit. Boundedness follows from
convergence, so no uniform bound on the slopes, shifts, or moduli is assumed. -/
theorem shifted_finite_divisor_models_no_irrational_limit {α : ℝ} (a b : ℕ → ℕ)
    (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n) (hab : ∀ n, (a n).Coprime (b n))
    (hobs : ∀ n, HasShiftedFiniteDivisorObstruction (a n) (b n))
    (hlim : Tendsto (fun n => (a n : ℝ) / b n) atTop (𝓝 α)) : ¬ Irrational α := by
  obtain ⟨U, hU⟩ := hlim.bddAbove_range
  obtain ⟨T, hT⟩ := exists_nat_gt U
  apply shifted_finite_divisor_models_limit_not_irrational a b T ha hb hab _ hobs hlim
  intro n
  have hq : (a n : ℝ) / b n ≤ T := (hU ⟨n, rfl⟩).trans hT.le
  have hbr : (0 : ℝ) < b n := by exact_mod_cast hb n
  exact_mod_cast (div_le_iff₀ hbr).mp hq

#print axioms shifted_finite_divisor_models_no_irrational_limit




#print axioms shifted_prime_indices_coprime_of_model

end Explore972
