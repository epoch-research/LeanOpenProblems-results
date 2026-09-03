import Submission.Valuation

/-!
# Removing a prime factor from inverse-totient supports

These upper bounds restrict possible witnesses to Erdős 821. They are not a
proof or disproof of the conjecture.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

lemma admissibleSupport_filter_card_le_valuation {n q : ℕ}
    (hn : 0 < n) (hq : q.Prime) {S : Finset ℕ}
    (hS : S ∈ admissibleSupports n) :
    (S.filter (fun p => q ∣ p - 1)).card ≤ n.factorization q := by
  have hpow : q ^ (S.filter (fun p => q ∣ p - 1)).card ∣
      ∏ p ∈ S.filter (fun p => q ∣ p - 1), (p - 1) := by
    rw [← Finset.prod_const]
    apply Finset.prod_dvd_prod_of_dvd
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  exact (hq.pow_dvd_iff_le_factorization hn.ne').mp
    (hpow.trans ((Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans
      (Finset.mem_filter.mp hS).2.1))

lemma admissibleSupport_prime_free_part {n q : ℕ} (hn : 0 < n) (hq : q.Prime)
    {S : Finset ℕ} (hS : S ∈ admissibleSupports n) :
    S.filter (fun p => ¬q ∣ p - 1) ∈
      (ordCompl[q] n).divisors.biUnion admissibleSupports := by
  let U := S.filter (fun p => ¬q ∣ p - 1)
  let d := ∏ p ∈ U, (p - 1)
  have hSpr : ∀ p ∈ S, p.Prime := fun p hp =>
    (Finset.mem_filter.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1) hp)).2.1
  have hUpr : ∀ p ∈ U, p.Prime := fun p hp => hSpr p (Finset.mem_filter.mp hp).1
  have hdpos : 0 < d := Finset.prod_pos (fun p hp => Nat.sub_pos_of_lt (hUpr p hp).one_lt)
  have hdn : d ∣ n :=
    (Finset.prod_dvd_prod_of_subset U S _ (Finset.filter_subset _ _)).trans
      (Finset.mem_filter.mp hS).2.1
  have hqd : ¬q ∣ d := by
    intro h
    obtain ⟨p, hp, hqp⟩ := (hq.prime.dvd_finset_prod_iff _).mp h
    exact (Finset.mem_filter.mp hp).2 hqp
  have hdr : d ∣ ordCompl[q] n := Nat.dvd_ordCompl_of_dvd_not_dvd hdn hqd
  have hUad : U ∈ admissibleSupports d := by
    have h := primeFactors_mem_admissibleSupports hdpos (totient_prod_primes U hUpr)
    simpa only [Nat.primeFactors_prod hUpr] using h
  exact Finset.mem_biUnion.mpr ⟨d,
    Nat.mem_divisors.mpr ⟨hdr, (Nat.ordCompl_pos q hn.ne').ne'⟩, hUad⟩

/-- Separate the support primes whose predecessors contain `q`. Only a bounded
number can occur when the `q`-adic valuation is bounded. The rest form an
admissible support for a divisor of the `q`-free part of the output. -/
lemma g_le_valuation_factor_mul_sum_ordCompl (n q K : ℕ) (hn : 0 < n)
    (hq : q.Prime) (hK : n.factorization q ≤ K) :
    g n ≤ (K + 1) * (n.divisors.card + 1) ^ K *
      ∑ d ∈ (ordCompl[q] n).divisors, g d := by
  let F := admissibleSupports n
  let T : Finset ℕ → Finset ℕ := fun S => S.filter (fun p => q ∣ p - 1)
  let U : Finset ℕ → Finset ℕ := fun S => S.filter (fun p => ¬q ∣ p - 1)
  let A := F.image T
  let B := (ordCompl[q] n).divisors.biUnion admissibleSupports
  have hA : A.card ≤ (K + 1) * (n.divisors.card + 1) ^ K := by
    calc
      A.card ≤ (K + 1) * ((shiftedPrimeDivisors n).card + 1) ^ K := by
        apply card_bounded_subset_family_le
        intro X hX
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hX
        refine ⟨(Finset.filter_subset _ _).trans
          (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1), ?_⟩
        exact (admissibleSupport_filter_card_le_valuation hn hq hS).trans hK
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
        (Nat.add_le_add_right (shiftedPrimeDivisors_card_le_divisors_card hn) 1) K)
  have hB : B.card ≤ ∑ d ∈ (ordCompl[q] n).divisors, g d := by
    apply (Finset.card_biUnion_le).trans
    apply Finset.sum_le_sum
    intro d hd
    rw [← g_eq_card_admissibleSupports (Nat.pos_of_mem_divisors hd)]
  have hcount : F.card ≤ A.card * B.card := by
    rw [← Finset.card_product]
    apply Finset.card_le_card_of_injOn (fun S => (T S, U S))
    · intro S hS
      exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨S, hS, rfl⟩,
        admissibleSupport_prime_free_part hn hq hS⟩
    · intro S hS R hR h
      have ht : T S = T R := congrArg Prod.fst h
      have hu : U S = U R := congrArg Prod.snd h
      ext p
      by_cases hp : q ∣ p - 1
      · simpa only [T, Finset.mem_filter, hp, and_true] using Finset.ext_iff.mp ht p
      · simpa only [U, Finset.mem_filter, hp, not_false_eq_true, and_true]
          using Finset.ext_iff.mp hu p
  rw [g_eq_card_admissibleSupports hn]
  exact hcount.trans (Nat.mul_le_mul hA hB)

lemma exists_g_le_constant_mul_rpow (e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 0 < d → (g d : ℝ) ≤ C * (d : ℝ) ^ (1 + e) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_g_le_rpow e he)
  let C : ℝ := (((Finset.range N).sup g : ℕ) : ℝ) + 1
  have hC : 1 ≤ C := by dsimp [C]; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  refine ⟨C, by linarith, ?_⟩
  intro d hd
  have hpow : 1 ≤ (d : ℝ) ^ (1 + e) :=
    Real.one_le_rpow (by exact_mod_cast hd) (by linarith)
  by_cases hdN : N ≤ d
  · exact (hN d hdN).trans (le_mul_of_one_le_left (by positivity) hC)
  · have hgd : (g d : ℝ) ≤ C := by
      have h := Finset.le_sup (f := g) (Finset.mem_range.mpr (Nat.lt_of_not_ge hdN))
      dsimp [C]
      exact (by exact_mod_cast h : (g d : ℝ) ≤ (((Finset.range N).sup g : ℕ) : ℝ)).trans
        (le_add_of_nonneg_right (by norm_num))
    exact hgd.trans (le_mul_of_one_le_right (by linarith) hpow)

lemma eventually_const_mul_divisors_pow_le_rpow (K : ℕ) (C e : ℝ)
    (hC : 0 ≤ C) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop,
      C * ((n.divisors.card : ℝ) + 1) ^ K ≤ (n : ℝ) ^ e := by
  let a : ℝ := e / (2 * ((K : ℝ) + 1))
  have ha : 0 < a := div_pos he (by positivity)
  have heq : a * ((K : ℝ) + 1) = e / 2 := by dsimp [a]; field_simp
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (e / 2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos he)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_card_divisors_le_rpow a ha,
    hlim.eventually (eventually_ge_atTop (C * 2 ^ K)), eventually_ge_atTop 1]
      with n hnD hnC hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hna : 1 ≤ (n : ℝ) ^ a := Real.one_le_rpow hnR ha.le
  have hpower : ((n : ℝ) ^ a) ^ (K + 1) = (n : ℝ) ^ (e / 2) := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ a) (K + 1), ← Real.rpow_mul (Nat.cast_nonneg n)]
    push_cast
    rw [heq]
  calc
    C * ((n.divisors.card : ℝ) + 1) ^ K ≤ C * (2 * (n : ℝ) ^ a) ^ K := by
      gcongr
      linarith
    _ = (C * 2 ^ K) * ((n : ℝ) ^ a) ^ K := by rw [mul_pow]; ring
    _ ≤ (C * 2 ^ K) * ((n : ℝ) ^ a) ^ (K + 1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_right₀ hna (Nat.le_succ K)
    _ = (C * 2 ^ K) * (n : ℝ) ^ (e / 2) := by rw [hpower]
    _ ≤ (n : ℝ) ^ (e / 2) * (n : ℝ) ^ (e / 2) := by gcongr
    _ = (n : ℝ) ^ e := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < n)]
      congr 1
      ring

lemma g_le_constant_mul_divisors_pow_mul_ordCompl_rpow (K : ℕ) (e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ n q : ℕ, 0 < n → q.Prime → n.factorization q ≤ K →
      (g n : ℝ) ≤ C * ((n.divisors.card : ℝ) + 1) ^ (K + 1) *
        ((ordCompl[q] n : ℕ) : ℝ) ^ (1 + e) := by
  obtain ⟨C, hC, hgd⟩ := exists_g_le_constant_mul_rpow e he
  refine ⟨((K : ℝ) + 1) * C, by positivity, ?_⟩
  intro n q hn hq hK
  let r := ordCompl[q] n
  have hrpos : 0 < r := Nat.ordCompl_pos q hn.ne'
  have hD : r.divisors.card ≤ n.divisors.card :=
    Finset.card_le_card (Nat.divisors_subset_of_dvd hn.ne' (Nat.ordCompl_dvd n q))
  have hsum : (∑ d ∈ r.divisors, (g d : ℝ)) ≤
      ((n.divisors.card : ℝ) + 1) * C * (r : ℝ) ^ (1 + e) := by
    calc
      (∑ d ∈ r.divisors, (g d : ℝ)) ≤ ∑ _d ∈ r.divisors, C * (r : ℝ) ^ (1 + e) := by
        apply Finset.sum_le_sum
        intro d hd
        exact (hgd d (Nat.pos_of_mem_divisors hd)).trans
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg d)
            (by exact_mod_cast Nat.le_of_dvd hrpos (Nat.dvd_of_mem_divisors hd)) (by linarith)) hC.le)
      _ = (r.divisors.card : ℝ) * C * (r : ℝ) ^ (1 + e) := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ _ := by gcongr; exact (by exact_mod_cast hD : (r.divisors.card : ℝ) ≤ n.divisors.card).trans (by linarith)
  have hg : (g n : ℝ) ≤ ((K : ℝ) + 1) * ((n.divisors.card : ℝ) + 1) ^ K *
      ∑ d ∈ r.divisors, (g d : ℝ) := by
    exact_mod_cast g_le_valuation_factor_mul_sum_ordCompl n q K hn hq hK
  calc
    (g n : ℝ) ≤ ((K : ℝ) + 1) * ((n.divisors.card : ℝ) + 1) ^ K *
      (((n.divisors.card : ℝ) + 1) * C * (r : ℝ) ^ (1 + e)) :=
      hg.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
    _ = _ := by rw [pow_succ]; ring

lemma ordCompl_le_rpow_of_le_prime_pow {n q K : ℕ} (hn : 0 < n)
    (hq : q.Prime) (hqd : q ∣ n) (hK : 1 ≤ K) (hnq : n ≤ q ^ K) :
    ((ordCompl[q] n : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 - 1 / (K : ℝ)) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hroot : (n : ℝ) ^ (1 / (K : ℝ)) ≤ q := by
    calc
      (n : ℝ) ^ (1 / (K : ℝ)) ≤ ((q : ℝ) ^ K) ^ (1 / (K : ℝ)) :=
        Real.rpow_le_rpow hnR.le (by exact_mod_cast hnq) (by positivity)
      _ = q := by rw [← Real.rpow_natCast_mul hqR.le, mul_one_div_cancel hKR.ne', Real.rpow_one]
  have hmul : q * ordCompl[q] n ≤ n := by
    calc
      _ ≤ ordProj[q] n * ordCompl[q] n := Nat.mul_le_mul_right _
        (Nat.le_of_dvd (Nat.ordProj_pos n q) (Nat.dvd_ordProj_of_dvd hn.ne' hq hqd))
      _ = n := Nat.ordProj_mul_ordCompl_eq_self n q
  have hmulR : ((ordCompl[q] n : ℕ) : ℝ) * (n : ℝ) ^ (1 / (K : ℝ)) ≤ n := by
    calc
      _ ≤ ((ordCompl[q] n : ℕ) : ℝ) * q :=
        mul_le_mul_of_nonneg_left hroot (Nat.cast_nonneg _)
      _ ≤ n := by exact_mod_cast (show ordCompl[q] n * q ≤ n by simpa [mul_comm] using hmul)
  calc
    ((ordCompl[q] n : ℕ) : ℝ) ≤ (n : ℝ) / (n : ℝ) ^ (1 / (K : ℝ)) :=
      (le_div_iff₀ (Real.rpow_pos_of_pos hnR _)).mpr hmulR
    _ = (n : ℝ) ^ (1 - 1 / (K : ℝ)) := by rw [Real.rpow_sub hnR, Real.rpow_one]

/-- A prime divisor at least the `K`-th root of the output forces a loss of
`1/K` in the multiplicity exponent, up to an arbitrary positive error. -/
lemma eventually_g_le_rpow_of_large_prime_factor (K : ℕ) (hK : 1 ≤ K)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ q : ℕ, q.Prime → q ∣ n → n ≤ q ^ K →
      (g n : ℝ) ≤ (n : ℝ) ^ (1 - 1 / (K : ℝ) + η) := by
  let e := η / 2
  have he : 0 < e := half_pos hη
  obtain ⟨C, hC, hg⟩ := g_le_constant_mul_divisors_pow_mul_ordCompl_rpow K e he
  filter_upwards [eventually_const_mul_divisors_pow_le_rpow (K + 1) C e hC.le he,
    eventually_ge_atTop 1] with n hnC hn q hq hqd hnq
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hKR : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hcomp := ordCompl_le_rpow_of_le_prime_pow hnpos hq hqd hK hnq
  have hexp : e + (1 - 1 / (K : ℝ)) * (1 + e) ≤ 1 - 1 / (K : ℝ) + η := by
    have hterm : 0 ≤ (1 / (K : ℝ)) * e := mul_nonneg (by positivity) he.le
    dsimp [e] at *
    nlinarith
  calc
    (g n : ℝ) ≤ C * ((n.divisors.card : ℝ) + 1) ^ (K + 1) *
        ((ordCompl[q] n : ℕ) : ℝ) ^ (1 + e) :=
      hg n q hnpos hq (Nat.factorization_le_of_le_pow hnq)
    _ ≤ (n : ℝ) ^ e * ((n : ℝ) ^ (1 - 1 / (K : ℝ))) ^ (1 + e) := by
      apply mul_le_mul hnC
      · exact Real.rpow_le_rpow (Nat.cast_nonneg _) hcomp (by linarith)
      · positivity
      · positivity
    _ = (n : ℝ) ^ (e + (1 - 1 / (K : ℝ)) * (1 + e)) := by
      rw [← Real.rpow_mul hnR.le, ← Real.rpow_add hnR]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hnR1 hexp

lemma finite_large_prime_factor_g_gt_rpow (K : ℕ) (hK : 1 ≤ K)
    (η : ℝ) (hη : 0 < η) :
    {n : ℕ | (∃ q : ℕ, q.Prime ∧ q ∣ n ∧ n ≤ q ^ K) ∧
      (g n : ℝ) > (n : ℝ) ^ (1 - 1 / (K : ℝ) + η)}.Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_g_le_rpow_of_large_prime_factor K hK η hη)
  apply (Set.finite_Iio N).subset
  rintro n ⟨⟨q, hq, hqd, hnq⟩, hg⟩
  change n < N
  by_contra h
  exact (not_lt_of_ge (hN n (Nat.le_of_not_gt h) q hq hqd hnq)) hg

#print axioms g_le_valuation_factor_mul_sum_ordCompl
#print axioms g_le_constant_mul_divisors_pow_mul_ordCompl_rpow
#print axioms eventually_g_le_rpow_of_large_prime_factor
#print axioms finite_large_prime_factor_g_gt_rpow

end Erdos821
