import Submission.Certificates

/-!
# Finite divisor bounds for Carmichael numbers

For a fixed divisor `d`, the cofactors of its Carmichael multiples all have
one residue modulo `λ(d)`. The canonical floor quotient `(n / d) / λ(d)`
is therefore injective on those multiples. For `n ≤ X` its value lies in
`[0, X / (d * λ(d))]`, giving the exact natural-number upper bound
`1 + X / (d * λ(d))`. Unlike the prime-factor bound, the index can be zero,
so the extra `1` must not be discarded.

Taking a finite union over divisors `1 ≤ d ≤ D` with `V ≤ λ(d)` gives the
sum of these exact natural bounds. For `1 ≤ V`, its real cardinality is at
most `D + (X / V) * ∑_{d=1}^D 1 / d`, hence at most
`D + (X / V) * (1 + Real.log D)`. The quotients in these last two bounds
are real quotients.

Cover corollaries make the required divisor-witness hypothesis explicit.
These are finite large-`λ` upper reductions, not density assertions; no
admitted counting statement is used. Only the verified certificate module
is imported.
-/

open scoped BigOperators

namespace Erdos1057.CarmichaelCertificates

/-- The canonical floor quotient of the cofactor by the divisor's Carmichael function.
It is allowed to be zero, even for a positive divisor of a Carmichael number. -/
def divisorCofactorIndex (d n : ℕ) : ℕ := (n / d) / ArithmeticFunction.Carmichael d

/-- Equal indices force equal Carmichael multiples of a common divisor:
the cofactor remainders agree by the divisor certificates. -/
theorem divisor_cofactor_index_inj {d n₁ n₂ : ℕ}
    (h₁ : IsCarmichael n₁) (h₂ : IsCarmichael n₂) (hd₁ : d ∣ n₁) (hd₂ : d ∣ n₂)
    (hindex : divisorCofactorIndex d n₁ = divisorCofactorIndex d n₂) : n₁ = n₂ := by
  have hrem : (n₁ / d) % ArithmeticFunction.Carmichael d =
      (n₂ / d) % ArithmeticFunction.Carmichael d := cofactor_modEq h₁ h₂ hd₁ hd₂
  change (n₁ / d) / ArithmeticFunction.Carmichael d =
    (n₂ / d) / ArithmeticFunction.Carmichael d at hindex
  have hcofactor : n₁ / d = n₂ / d := by
    calc
      n₁ / d = (n₁ / d) % ArithmeticFunction.Carmichael d +
          ArithmeticFunction.Carmichael d * ((n₁ / d) / ArithmeticFunction.Carmichael d) :=
        (Nat.mod_add_div _ _).symm
      _ = (n₂ / d) % ArithmeticFunction.Carmichael d +
          ArithmeticFunction.Carmichael d * ((n₂ / d) / ArithmeticFunction.Carmichael d) := by
        rw [hrem, hindex]
      _ = n₂ / d := Nat.mod_add_div _ _
  calc
    n₁ = d * (n₁ / d) := (Nat.mul_div_cancel' hd₁).symm
    _ = d * (n₂ / d) := by rw [hcofactor]
    _ = n₂ := Nat.mul_div_cancel' hd₂

/-- The cofactor index is bounded using natural division, including its rounding.
This arithmetic statement does not require `n` to be Carmichael. -/
theorem divisor_cofactor_index_le {d n X : ℕ} (hnX : n ≤ X) :
    divisorCofactorIndex d n ≤ X / (d * ArithmeticFunction.Carmichael d) := by
  simpa only [divisorCofactorIndex, Nat.div_div_eq_div_mul] using
    (Nat.div_le_div_right hnX : n / (d * ArithmeticFunction.Carmichael d) ≤
      X / (d * ArithmeticFunction.Carmichael d))

/-- The finite set of Carmichael numbers at most `X` divisible by `d`. -/
noncomputable def carmichaelsWithDivisorUpTo (d X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (X + 1)).filter (fun n => IsCarmichael n ∧ d ∣ n)

@[simp]
theorem mem_carmichaelsWithDivisorUpTo {d X n : ℕ} :
    n ∈ carmichaelsWithDivisorUpTo d X ↔ n ≤ X ∧ IsCarmichael n ∧ d ∣ n := by
  classical
  simp only [carmichaelsWithDivisorUpTo, Finset.mem_filter, Finset.mem_range_succ_iff]

/-- The finset agrees exactly with the bounded set in the counting statement. -/
theorem coe_carmichaelsWithDivisorUpTo (d X : ℕ) :
    (carmichaelsWithDivisorUpTo d X : Set ℕ) =
      {n : ℕ | n ≤ X ∧ IsCarmichael n ∧ d ∣ n} := by
  ext n
  exact mem_carmichaelsWithDivisorUpTo

/-- Finiteness for every natural divisor, including `d = 0`. -/
theorem carmichaels_with_divisor_finite (d X : ℕ) :
    {n : ℕ | n ≤ X ∧ IsCarmichael n ∧ d ∣ n}.Finite := by
  rw [← coe_carmichaelsWithDivisorUpTo d X]
  exact Finset.finite_toSet _

/-- The exact finite fixed-divisor bound. The quotient injection lands in an
interval containing zero, so the right side has an essential `+ 1`.
Positivity of `d` and `λ(d)` follows from any member via the certificate APIs;
if there is no member, the bound still holds without additional hypotheses. -/
theorem card_carmichaelsWithDivisorUpTo_le (d X : ℕ) :
    (carmichaelsWithDivisorUpTo d X).card ≤
      1 + X / (d * ArithmeticFunction.Carmichael d) := by
  classical
  have hcard : (carmichaelsWithDivisorUpTo d X).card ≤
      (Finset.range (X / (d * ArithmeticFunction.Carmichael d) + 1)).card := by
    apply Finset.card_le_card_of_injOn (divisorCofactorIndex d)
    · intro n hnmem
      exact Finset.mem_range_succ_iff.mpr
        (divisor_cofactor_index_le (mem_carmichaelsWithDivisorUpTo.mp hnmem).1)
    · intro n₁ hn₁ n₂ hn₂ hindex
      obtain ⟨_, h₁, hd₁⟩ := mem_carmichaelsWithDivisorUpTo.mp hn₁
      obtain ⟨_, h₂, hd₂⟩ := mem_carmichaelsWithDivisorUpTo.mp hn₂
      exact divisor_cofactor_index_inj h₁ h₂ hd₁ hd₂ hindex
  simpa only [Finset.card_range, Nat.add_comm] using hcard

/-- The exact fixed-divisor bound as a set cardinality, with natural division. -/
theorem ncard_carmichaels_with_divisor_le (d X : ℕ) :
    {n : ℕ | n ≤ X ∧ IsCarmichael n ∧ d ∣ n}.ncard ≤
      1 + X / (d * ArithmeticFunction.Carmichael d) := by
  rw [← coe_carmichaelsWithDivisorUpTo d X, Set.ncard_coe_finset]
  exact card_carmichaelsWithDivisorUpTo_le d X

/-- At `1` the Carmichael function is `1`, not `0`. Thus the witness `d = 1`
is eligible at threshold `V = 1`, and must not be silently excluded. -/
@[simp]
theorem carmichael_one : ArithmeticFunction.Carmichael 1 = 1 := by
  apply Nat.dvd_one.mp
  simpa using ArithmeticFunction.carmichael_dvd_totient 1

@[simp]
theorem divisorCofactorIndex_one (n : ℕ) : divisorCofactorIndex 1 n = n := by
  simp [divisorCofactorIndex]

/-- Zero divides no Carmichael number, so this endpoint is empty. -/
@[simp]
theorem carmichaelsWithDivisorUpTo_zero (X : ℕ) :
    carmichaelsWithDivisorUpTo 0 X = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hnmem
  obtain ⟨_, hn, hd⟩ := mem_carmichaelsWithDivisorUpTo.mp hnmem
  exact (Nat.lt_irrefl 0) (divisor_pos hn hd)

/-- At `d = 1`, positivity of Carmichael numbers sharpens the generic bound to `X`. -/
theorem card_carmichaelsWithDivisorUpTo_one_le (X : ℕ) :
    (carmichaelsWithDivisorUpTo 1 X).card ≤ X := by
  have hsub : carmichaelsWithDivisorUpTo 1 X ⊆ Finset.Icc 1 X := by
    intro n hnmem
    obtain ⟨hnX, hn, _⟩ := mem_carmichaelsWithDivisorUpTo.mp hnmem
    exact Finset.mem_Icc.mpr ⟨divisor_pos hn (dvd_refl n), hnX⟩
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hsub

/-- If the full modulus `d * λ(d)` exceeds `X`, there is at most one such number. -/
theorem ncard_carmichaels_with_divisor_le_one {d X : ℕ}
    (hX : X < d * ArithmeticFunction.Carmichael d) :
    {n : ℕ | n ≤ X ∧ IsCarmichael n ∧ d ∣ n}.ncard ≤ 1 := by
  simpa only [Nat.div_eq_of_lt hX, Nat.add_zero] using
    ncard_carmichaels_with_divisor_le d X

/-- The modulus in the counterexample to omitting `+ 1`. -/
theorem carmichael_51_eq_sixteen : ArithmeticFunction.Carmichael 51 = 16 := by
  have heq : 51 = 3 * 17 := by norm_num
  rw [heq, ArithmeticFunction.carmichael_mul (by norm_num : Nat.Coprime 3 17),
    CarmichaelKorselt.carmichael_prime (by norm_num : Nat.Prime 3),
    CarmichaelKorselt.carmichael_prime (by norm_num : Nat.Prime 17)]
  norm_num

/-- `561 = 51 * 11` has cofactor `11 < λ(51) = 16`, so its index is zero. -/
theorem divisor_cofactor_index_561_51 :
    561 / 51 = 11 ∧ divisorCofactorIndex 51 561 = 0 := by
  norm_num [divisorCofactorIndex, carmichael_51_eq_sixteen]

/-- A kernel-checked counterexample to the general bound without `+ 1`:
there is exactly one Carmichael multiple of `51` at most `561`, while the
natural quotient `561 / (51 * λ(51))` is zero. -/
theorem fixed_divisor_add_one_necessary :
    {n : ℕ | n ≤ 561 ∧ IsCarmichael n ∧ 51 ∣ n}.ncard = 1 ∧
      561 / (51 * ArithmeticFunction.Carmichael 51) = 0 := by
  have hzero : 561 / (51 * ArithmeticFunction.Carmichael 51) = 0 := by
    norm_num [carmichael_51_eq_sixteen]
  have hle := ncard_carmichaels_with_divisor_le 51 561
  rw [hzero, Nat.add_zero] at hle
  have hpos : 0 < {n : ℕ | n ≤ 561 ∧ IsCarmichael n ∧ 51 ∣ n}.ncard :=
    (Set.ncard_pos (carmichaels_with_divisor_finite 51 561)).mpr
      ⟨561, le_rfl, CarmichaelKorselt.isCarmichael_561, by norm_num⟩
  exact ⟨by omega, hzero⟩

/-- The real version of the fixed-divisor bound, obtained by bounding the
natural quotient by the corresponding real quotient. -/
theorem card_carmichaelsWithDivisorUpTo_le_real (d X : ℕ) :
    ((carmichaelsWithDivisorUpTo d X).card : ℝ) ≤
      1 + (X : ℝ) / ((d : ℝ) * (ArithmeticFunction.Carmichael d : ℝ)) := by
  calc
    _ ≤ (1 : ℝ) + ((X / (d * ArithmeticFunction.Carmichael d) : ℕ) : ℝ) := by
      exact_mod_cast card_carmichaelsWithDivisorUpTo_le d X
    _ ≤ _ := add_le_add_right (by
      simpa only [Nat.cast_mul] using
        (Nat.cast_div_le (α := ℝ) (m := X) (n := d * ArithmeticFunction.Carmichael d))) 1

/-- Carmichael numbers at most `X` having a positive divisor at most `D`
whose Carmichael function is at least the natural threshold `V`. -/
noncomputable def carmichaelsWithLargeLambdaDivisorUpTo (D V X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (X + 1)).filter (fun n => IsCarmichael n ∧
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ D ∧ V ≤ ArithmeticFunction.Carmichael d ∧ d ∣ n)

@[simp]
theorem mem_carmichaelsWithLargeLambdaDivisorUpTo {D V X n : ℕ} :
    n ∈ carmichaelsWithLargeLambdaDivisorUpTo D V X ↔
      n ≤ X ∧ IsCarmichael n ∧
        ∃ d : ℕ, 1 ≤ d ∧ d ≤ D ∧ V ≤ ArithmeticFunction.Carmichael d ∧ d ∣ n := by
  classical
  simp only [carmichaelsWithLargeLambdaDivisorUpTo, Finset.mem_filter,
    Finset.mem_range_succ_iff]

/-- The finset represents exactly the bounded set with a large-`λ` witness. -/
theorem coe_carmichaelsWithLargeLambdaDivisorUpTo (D V X : ℕ) :
    (carmichaelsWithLargeLambdaDivisorUpTo D V X : Set ℕ) =
      {n : ℕ | n ≤ X ∧ IsCarmichael n ∧
        ∃ d : ℕ, 1 ≤ d ∧ d ≤ D ∧ V ≤ ArithmeticFunction.Carmichael d ∧ d ∣ n} := by
  ext n
  exact mem_carmichaelsWithLargeLambdaDivisorUpTo

/-- Finiteness requires no positivity assumptions on the three cutoffs. -/
theorem carmichaels_with_large_lambda_divisor_finite (D V X : ℕ) :
    {n : ℕ | n ≤ X ∧ IsCarmichael n ∧
      ∃ d : ℕ, 1 ≤ d ∧ d ≤ D ∧ V ≤ ArithmeticFunction.Carmichael d ∧ d ∣ n}.Finite := by
  rw [← coe_carmichaelsWithLargeLambdaDivisorUpTo D V X]
  exact Finset.finite_toSet _

/-- The exact finite witness union; repeated witnesses do not require a choice. -/
theorem carmichaelsWithLargeLambdaDivisorUpTo_eq_biUnion (D V X : ℕ) :
    carmichaelsWithLargeLambdaDivisorUpTo D V X =
      ((Finset.Icc 1 D).filter (fun d => V ≤ ArithmeticFunction.Carmichael d)).biUnion
        (fun d => carmichaelsWithDivisorUpTo d X) := by
  classical
  ext n
  simp only [mem_carmichaelsWithLargeLambdaDivisorUpTo, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_Icc, mem_carmichaelsWithDivisorUpTo]
  constructor
  · rintro ⟨hnX, hn, d, hd1, hdD, hL, hd⟩
    exact ⟨d, ⟨⟨hd1, hdD⟩, hL⟩, hnX, hn, hd⟩
  · rintro ⟨d, ⟨⟨hd1, hdD⟩, hL⟩, hnX, hn, hd⟩
    exact ⟨hnX, hn, d, hd1, hdD, hL, hd⟩

/-- The witness interval includes `1` precisely when the cutoff allows it
and `V ≤ 1`, since `λ(1) = 1`. -/
theorem one_mem_large_lambda_divisors_iff (D V : ℕ) :
    1 ∈ (Finset.Icc 1 D).filter (fun d => V ≤ ArithmeticFunction.Carmichael d) ↔
      1 ≤ D ∧ V ≤ 1 := by
  classical
  simp only [Finset.mem_filter, Finset.mem_Icc, le_refl, carmichael_one, true_and]

@[simp]
theorem carmichaelsWithLargeLambdaDivisorUpTo_zero (V X : ℕ) :
    carmichaelsWithLargeLambdaDivisorUpTo 0 V X = ∅ := by
  classical
  rw [carmichaelsWithLargeLambdaDivisorUpTo_eq_biUnion]
  simp

/-- The exact natural finite-union bound, retaining both the `+ 1` and natural division.
It is valid even at threshold `V = 0`; the real harmonic bound will require `1 ≤ V`. -/
theorem card_carmichaelsWithLargeLambdaDivisorUpTo_le_sum (D V X : ℕ) :
    (carmichaelsWithLargeLambdaDivisorUpTo D V X).card ≤
      ∑ d ∈ (Finset.Icc 1 D).filter (fun d => V ≤ ArithmeticFunction.Carmichael d),
        (1 + X / (d * ArithmeticFunction.Carmichael d)) := by
  classical
  rw [carmichaelsWithLargeLambdaDivisorUpTo_eq_biUnion]
  exact Finset.card_biUnion_le.trans
    (Finset.sum_le_sum (fun d _ => card_carmichaelsWithDivisorUpTo_le d X))

/-- The exact natural witness-union bound stated directly for a bounded set. -/
theorem ncard_carmichaels_with_large_lambda_divisor_le_sum (D V X : ℕ) :
    {n : ℕ | n ≤ X ∧ IsCarmichael n ∧
      ∃ d : ℕ, 1 ≤ d ∧ d ≤ D ∧ V ≤ ArithmeticFunction.Carmichael d ∧ d ∣ n}.ncard ≤
      ∑ d ∈ (Finset.Icc 1 D).filter (fun d => V ≤ ArithmeticFunction.Carmichael d),
        (1 + X / (d * ArithmeticFunction.Carmichael d)) := by
  rw [← coe_carmichaelsWithLargeLambdaDivisorUpTo D V X, Set.ncard_coe_finset]
  exact card_carmichaelsWithLargeLambdaDivisorUpTo_le_sum D V X

/-- Each rounded natural quotient is bounded by its harmonic weight at threshold `V`. -/
theorem cast_divisor_quotient_le {d V X : ℕ} (hd : 1 ≤ d) (hV : 1 ≤ V)
    (hL : V ≤ ArithmeticFunction.Carmichael d) :
    ((X / (d * ArithmeticFunction.Carmichael d) : ℕ) : ℝ) ≤
      (X : ℝ) / (V : ℝ) * (1 / (d : ℝ)) := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hVpos : 0 < (V : ℝ) := by exact_mod_cast (by omega : 0 < V)
  have hLreal : (V : ℝ) ≤ (ArithmeticFunction.Carmichael d : ℝ) := by exact_mod_cast hL
  calc
    _ ≤ (X : ℝ) / ((d : ℝ) * (ArithmeticFunction.Carmichael d : ℝ)) := by
      simpa only [Nat.cast_mul] using
        (Nat.cast_div_le (α := ℝ) (m := X) (n := d * ArithmeticFunction.Carmichael d))
    _ ≤ (X : ℝ) / ((d : ℝ) * (V : ℝ)) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg X) (mul_pos hdpos hVpos)
        (mul_le_mul_of_nonneg_left hLreal hdpos.le)
    _ = (X : ℝ) / (V : ℝ) * (1 / (d : ℝ)) := by
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      ring

/-- The real harmonic finite-union bound. There are at most `D` witnesses,
and their reciprocal weights sum to at most the full harmonic sum. -/
theorem card_carmichaelsWithLargeLambdaDivisorUpTo_le_harmonic {D V X : ℕ}
    (hV : 1 ≤ V) :
    ((carmichaelsWithLargeLambdaDivisorUpTo D V X).card : ℝ) ≤
      (D : ℝ) + (X : ℝ) / (V : ℝ) * (∑ d ∈ Finset.Icc 1 D, (1 : ℝ) / (d : ℝ)) := by
  classical
  calc
    _ ≤ ∑ d ∈ (Finset.Icc 1 D).filter (fun d => V ≤ ArithmeticFunction.Carmichael d),
        ((1 + X / (d * ArithmeticFunction.Carmichael d) : ℕ) : ℝ) := by
      exact_mod_cast card_carmichaelsWithLargeLambdaDivisorUpTo_le_sum D V X
    _ ≤ ∑ d ∈ (Finset.Icc 1 D).filter (fun d => V ≤ ArithmeticFunction.Carmichael d),
        ((1 : ℝ) + (X : ℝ) / (V : ℝ) * (1 / (d : ℝ))) := by
      apply Finset.sum_le_sum
      intro d hdmem
      obtain ⟨hdIcc, hL⟩ := Finset.mem_filter.mp hdmem
      simp only [Nat.cast_add, Nat.cast_one]
      exact add_le_add_right (cast_divisor_quotient_le (Finset.mem_Icc.mp hdIcc).1 hV hL) 1
    _ ≤ ∑ d ∈ Finset.Icc 1 D, ((1 : ℝ) + (X : ℝ) / (V : ℝ) * (1 / (d : ℝ))) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun d _ _ => by positivity)
    _ = (D : ℝ) + (X : ℝ) / (V : ℝ) * (∑ d ∈ Finset.Icc 1 D, (1 : ℝ) / (d : ℝ)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]

/-- The real harmonic bound in set-cardinality form. -/
theorem ncard_carmichaels_with_large_lambda_divisor_le_harmonic {D V X : ℕ}
    (hV : 1 ≤ V) :
    ({n : ℕ | n ≤ X ∧ IsCarmichael n ∧
      ∃ d : ℕ, 1 ≤ d ∧ d ≤ D ∧ V ≤ ArithmeticFunction.Carmichael d ∧ d ∣ n}.ncard : ℝ) ≤
      (D : ℝ) + (X : ℝ) / (V : ℝ) * (∑ d ∈ Finset.Icc 1 D, (1 : ℝ) / (d : ℝ)) := by
  rw [← coe_carmichaelsWithLargeLambdaDivisorUpTo D V X, Set.ncard_coe_finset]
  exact card_carmichaelsWithLargeLambdaDivisorUpTo_le_harmonic hV

/-- Mathlib's harmonic estimate in the reciprocal-sum notation used here.
It also holds at `D = 0`, with an empty sum and `Real.log 0 = 0`. -/
theorem sum_Icc_one_div_le_one_add_log (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, (1 : ℝ) / (d : ℝ)) ≤ 1 + Real.log (D : ℝ) := by
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div] using
    harmonic_le_one_add_log D

/-- The logarithmic finite-union bound, for a positive natural threshold. -/
theorem card_carmichaelsWithLargeLambdaDivisorUpTo_le_log {D V X : ℕ} (hV : 1 ≤ V) :
    ((carmichaelsWithLargeLambdaDivisorUpTo D V X).card : ℝ) ≤
      (D : ℝ) + (X : ℝ) / (V : ℝ) * (1 + Real.log (D : ℝ)) := by
  refine (card_carmichaelsWithLargeLambdaDivisorUpTo_le_harmonic hV).trans ?_
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left (sum_Icc_one_div_le_one_add_log D)
      (div_nonneg (Nat.cast_nonneg X) (Nat.cast_nonneg V))) (D : ℝ)

/-- The logarithmic finite-union bound in set-cardinality form. -/
theorem ncard_carmichaels_with_large_lambda_divisor_le_log {D V X : ℕ} (hV : 1 ≤ V) :
    ({n : ℕ | n ≤ X ∧ IsCarmichael n ∧
      ∃ d : ℕ, 1 ≤ d ∧ d ≤ D ∧ V ≤ ArithmeticFunction.Carmichael d ∧ d ∣ n}.ncard : ℝ) ≤
      (D : ℝ) + (X : ℝ) / (V : ℝ) * (1 + Real.log (D : ℝ)) := by
  rw [← coe_carmichaelsWithLargeLambdaDivisorUpTo D V X, Set.ncard_coe_finset]
  exact card_carmichaelsWithLargeLambdaDivisorUpTo_le_log hV

/-- Any collection of bounded Carmichael numbers covered by such divisor witnesses
is a subset of the witness count. No finiteness assumption on `s` is needed,
since its boundedness supplies one. This is an upper reduction, not a claim
that all Carmichael numbers have these witnesses. -/
theorem ncard_le_count_of_large_lambda_divisor_cover {s : Set ℕ} {D V X : ℕ}
    (hbounded : ∀ n ∈ s, n ≤ X ∧ IsCarmichael n)
    (hcover : ∀ n ∈ s, ∃ d : ℕ,
      1 ≤ d ∧ d ≤ D ∧ V ≤ ArithmeticFunction.Carmichael d ∧ d ∣ n) :
    s.ncard ≤ {n : ℕ | n ≤ X ∧ IsCarmichael n ∧
      ∃ d : ℕ, 1 ≤ d ∧ d ≤ D ∧ V ≤ ArithmeticFunction.Carmichael d ∧ d ∣ n}.ncard := by
  apply Set.ncard_le_ncard _ (carmichaels_with_large_lambda_divisor_finite D V X)
  intro n hn
  exact ⟨(hbounded n hn).1, (hbounded n hn).2, hcover n hn⟩

/-- Exact natural upper reduction for any set with the stated divisor cover. -/
theorem ncard_le_sum_of_large_lambda_divisor_cover {s : Set ℕ} {D V X : ℕ}
    (hbounded : ∀ n ∈ s, n ≤ X ∧ IsCarmichael n)
    (hcover : ∀ n ∈ s, ∃ d : ℕ,
      1 ≤ d ∧ d ≤ D ∧ V ≤ ArithmeticFunction.Carmichael d ∧ d ∣ n) :
    s.ncard ≤ ∑ d ∈ (Finset.Icc 1 D).filter (fun d => V ≤ ArithmeticFunction.Carmichael d),
      (1 + X / (d * ArithmeticFunction.Carmichael d)) :=
  (ncard_le_count_of_large_lambda_divisor_cover hbounded hcover).trans
    (ncard_carmichaels_with_large_lambda_divisor_le_sum D V X)

/-- Real harmonic upper reduction, conditional only on the explicit finite cover. -/
theorem ncard_le_harmonic_of_large_lambda_divisor_cover {s : Set ℕ} {D V X : ℕ}
    (hV : 1 ≤ V) (hbounded : ∀ n ∈ s, n ≤ X ∧ IsCarmichael n)
    (hcover : ∀ n ∈ s, ∃ d : ℕ,
      1 ≤ d ∧ d ≤ D ∧ V ≤ ArithmeticFunction.Carmichael d ∧ d ∣ n) :
    (s.ncard : ℝ) ≤
      (D : ℝ) + (X : ℝ) / (V : ℝ) * (∑ d ∈ Finset.Icc 1 D, (1 : ℝ) / (d : ℝ)) :=
  (Nat.cast_le.mpr (ncard_le_count_of_large_lambda_divisor_cover hbounded hcover)).trans
    (ncard_carmichaels_with_large_lambda_divisor_le_harmonic hV)

/-- Real logarithmic upper reduction for a set with the stated divisor cover.
The hypotheses assert the cover explicitly; no asymptotic or density theorem
is inferred from this finite counting estimate. -/
theorem ncard_le_log_of_large_lambda_divisor_cover {s : Set ℕ} {D V X : ℕ}
    (hV : 1 ≤ V) (hbounded : ∀ n ∈ s, n ≤ X ∧ IsCarmichael n)
    (hcover : ∀ n ∈ s, ∃ d : ℕ,
      1 ≤ d ∧ d ≤ D ∧ V ≤ ArithmeticFunction.Carmichael d ∧ d ∣ n) :
    (s.ncard : ℝ) ≤ (D : ℝ) + (X : ℝ) / (V : ℝ) * (1 + Real.log (D : ℝ)) :=
  (Nat.cast_le.mpr (ncard_le_count_of_large_lambda_divisor_cover hbounded hcover)).trans
    (ncard_carmichaels_with_large_lambda_divisor_le_log hV)

end Erdos1057.CarmichaelCertificates
