import Submission.LocalRootUpperScaling
import Submission.DivisorBound

/-! Subpolynomial upper bounds for normalized congruence densities at moduli
coprime to the exponent. These are not pointwise upper bounds for the exact
representation count. -/
namespace Erdos322Research.LocalRootUpper
noncomputable section
open Finset LocalPeakCounting LocalRootUpperBasic LocalRootUpperScaling LocalCRTConcentration
open scoped Classical
set_option maxHeartbeats 0
set_option Elab.async false

/-- Normalized density at a good prime grows at most linearly in depth. -/
theorem prime_power_upper (k p e : ℕ) [Fact p.Prime] (hk : ¬p ∣ k+2) :
    rootCount (k+2) (p^e) ≤ ((k+2)^2+1)*(e+1)*p^(e*(k+1)) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hp1 : 1 ≤ p := by omega
  induction e using Nat.strong_induction_on with
  | h e ih =>
    cases e with
    | zero => simp [rootCount,Roots]
    | succ e =>
      have hc := root_cover_upper k p e hk
      rw [← pow_mul] at hc
      by_cases he : e+1 ≤ k+2
      · have hd := divisible_box_upper k p e hp
        have hpow : p^(e*(k+2)) ≤ p^((e+1)*(k+1)) := by
          apply Nat.pow_le_pow_right hp1
          nlinarith
        have hh := hd.trans hpow
        calc
          rootCount (k+2) (p^(e+1)) ≤ _ := hc
          _ ≤ p^((e+1)*(k+1))+(k+2)^2*p^((e+1)*(k+1)) := by gcongr
          _ = ((k+2)^2+1)*1*p^((e+1)*(k+1)) := by ring
          _ ≤ _ := by gcongr; omega
      · let m := e+1-(k+2)
        have hm : m+(k+2)=e+1 := Nat.sub_add_cancel (by omega)
        have hmlt : m<e+1 := by omega
        have hi := ih m hmlt
        have hd := divisible_scaling_upper k p (p^m) hp (pow_pos hp _)
        rw [← pow_add,show k+2+m=e+1 by omega] at hd
        have hd' : Fintype.card (DivRoots k p (p^(e+1))) ≤
            ((k+2)^2+1)*(m+1)*p^((e+1)*(k+1)) := by
          calc
            Fintype.card (DivRoots k p (p^(e+1))) ≤ _ := hd
            _ ≤ (((k+2)^2+1)*(m+1)*p^(m*(k+1)))*p^((k+2)*(k+1)) := by gcongr
            _ = ((k+2)^2+1)*(m+1)*p^((e+1)*(k+1)) := by
              rw [mul_assoc (((k+2)^2+1)*(m+1)),← pow_add]
              congr 2
              nlinarith [hm]
        calc
          rootCount (k+2) (p^(e+1)) ≤ _ := hc
          _ ≤ ((k+2)^2+1)*(m+1)*p^((e+1)*(k+1))+
              (k+2)^2*p^((e+1)*(k+1)) := by gcongr
          _ = (((k+2)^2+1)*(m+1)+(k+2)^2)*p^((e+1)*(k+1)) := by ring
          _ ≤ _ := by
            apply Nat.mul_le_mul_right
            have hme : m ≤ e := by omega
            nlinarith

/-- A divisor-function bound for all moduli coprime to the degree. -/
theorem coprime_modulus_upper (k q : ℕ) : 0 < q → q.Coprime (k+2) →
    rootCount (k+2) q ≤ q.divisors.card^((k+2)^2+2)*q^(k+1) := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp [rootCount,Roots]
  | prime_pow p e hp he =>
    intro _ hcop
    letI : Fact p.Prime := ⟨hp⟩
    have hk : ¬p ∣ k+2 := hp.coprime_iff_not_dvd.mp
      ((Nat.coprime_pow_left_iff he p (k+2)).mp hcop)
    have hc : (k+2)^2+1 ≤ (e+1)^((k+2)^2+1) := by
      calc
        (k+2)^2+1 ≤ 2^((k+2)^2+1) := (Nat.lt_two_pow_self).le
        _ ≤ _ := Nat.pow_le_pow_left (by omega) _
    have hh := prime_power_upper k p e hk
    calc
      rootCount (k+2) (p^e) ≤ ((k+2)^2+1)*(e+1)*p^(e*(k+1)) := hh
      _ ≤ (e+1)^((k+2)^2+1)*(e+1)*p^(e*(k+1)) := by gcongr
      _ = (p^e).divisors.card^((k+2)^2+2)*(p^e)^(k+1) := by
        simp only [Nat.divisors_prime_pow hp,Finset.card_map,Finset.card_range,← pow_mul]
        simp only [pow_succ]
  | coprime a b ha hb hab ia ib =>
    intro _ hcop
    obtain ⟨hak,hbk⟩ := Nat.coprime_mul_iff_left.mp hcop
    have hh := Nat.mul_le_mul (ia (by omega) hak) (ib (by omega) hbk)
    rw [rootCount_mul _ _ _ (by omega) (by omega) hab,hab.card_divisors_mul,mul_pow,mul_pow]
    convert hh using 1; ring

/-- Normalized modular densities are subpolynomial, uniformly over all
moduli coprime to the degree. -/
theorem normalized_density_subpolynomial_aux (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ q : ℕ, 0 < q → q.Coprime (k+2) →
      (rootCount (k+2) q : ℝ) ≤ C*(q : ℝ)^ε*(q : ℝ)^(k+1) := by
  let D : ℕ := (k+2)^2+2
  have hD : (0 : ℝ) < D := by dsimp [D]; positivity
  obtain ⟨C,hC,hbound⟩ := divisor_count_subpolynomial (ε/(D : ℝ)) (div_pos hε hD)
  refine ⟨C^D,pow_pos hC _,?_⟩
  intro q hq hcop
  have hn := coprime_modulus_upper k q hq hcop
  have hcast : (rootCount (k+2) q : ℝ) ≤ (q.divisors.card : ℝ)^D*(q : ℝ)^(k+1) := by
    exact_mod_cast hn
  have hp : ((q : ℝ)^(ε/(D : ℝ)))^D=(q : ℝ)^ε := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg q)]
    congr 1
    exact div_mul_cancel₀ ε (ne_of_gt hD)
  calc
    (rootCount (k+2) q : ℝ) ≤ _ := hcast
    _ ≤ (C*(q : ℝ)^(ε/(D : ℝ)))^D*(q : ℝ)^(k+1) := by
      gcongr
      exact hbound q hq
    _ = C^D*(q : ℝ)^ε*(q : ℝ)^(k+1) := by rw [mul_pow,hp]

/-- The public version uses the actual exponent k rather than k+2. -/
theorem normalized_density_subpolynomial (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ q : ℕ, 0 < q → q.Coprime k →
      (rootCount k q : ℝ) ≤ C*(q : ℝ)^ε*(q : ℝ)^(k-1) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa only [Nat.add_comm 2 j,Nat.add_sub_cancel] using normalized_density_subpolynomial_aux j ε hε

/-- Even after comparing the density with a positive exact target divisible
by the modulus, the density alone is at most subpolynomial in that target.
This bounds the local-density certificate, NOT the actual representation count. -/
theorem density_certificate_subpolynomial (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ q n : ℕ, 0 < q → q.Coprime k → 0 < n → q ∣ n →
      (rootCount k q : ℝ)/(q : ℝ)^(k-1) ≤ C*(n : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := normalized_density_subpolynomial k hk ε hε
  refine ⟨C,hC,?_⟩
  intro q n hq hcop hn hqn
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hle : (q : ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd hn hqn
  have hh : (rootCount k q : ℝ)/(q : ℝ)^(k-1) ≤ C*(q : ℝ)^ε := by
    apply (div_le_iff₀ (pow_pos hqr _)).mpr
    exact hbound q hq hcop
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hqr.le hle hε.le) hC.le)

/-- For every fixed positive power, the modular-density certificate is
uniformly below that power at every sufficiently large compatible exact target. -/
theorem density_certificate_eventually_le_power (k : ℕ) (hk : 2 ≤ k)
    (c : ℝ) (hc : 0 < c) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℕ,
      0 < q → q.Coprime k → 0 < n → q ∣ n →
      (rootCount k q : ℝ)/(q : ℝ)^(k-1) ≤ (n : ℝ)^c := by
  have he : 0 < c/2 := half_pos hc
  obtain ⟨C,hC,hbound⟩ := density_certificate_subpolynomial k hk (c/2) he
  have ht : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)^(c/2)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (ht.eventually_ge_atTop C)
  refine ⟨N,?_⟩
  intro n hn q hq hcop hnp hqn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnp
  calc
    (rootCount k q : ℝ)/(q : ℝ)^(k-1) ≤ C*(n : ℝ)^(c/2) := hbound q n hq hcop hnp hqn
    _ ≤ (n : ℝ)^(c/2)*(n : ℝ)^(c/2) :=
      mul_le_mul_of_nonneg_right (hN n hn) (Real.rpow_nonneg hnr.le _)
    _ = (n : ℝ)^c := by rw [← Real.rpow_add hnr]; congr 1; ring

end
end Erdos322Research.LocalRootUpper
