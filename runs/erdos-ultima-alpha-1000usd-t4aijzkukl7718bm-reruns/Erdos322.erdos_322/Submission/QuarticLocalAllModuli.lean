import Submission.QuarticReduction
import Submission.LocalRootUpper

/-! Quartic congruence density bounds including the prime 2. These bounds
concern modular roots, not the exact representation count. -/
namespace Erdos322Research.QuarticLocalAllModuli
noncomputable section
open Finset LocalPeakCounting LocalRootUpperScaling LocalRootUpper LocalCRTConcentration
open scoped Classical
set_option maxHeartbeats 0
set_option Elab.async false

/-- Every root modulo 16q is even in every coordinate; critical scaling is exact. -/
theorem rootCount_sixteen_mul (q : ℕ) (hq : 0 < q) :
    rootCount 4 (16*q)=4096*rootCount 4 q := by
  classical
  let f : Roots 4 (16*q) → DivRoots 2 2 (16*q) := fun x ↦ ⟨x,by
    apply two_dvd_all_of_fourth_sum rfl
    exact dvd_trans (dvd_mul_right 16 q) x.property⟩
  have hf : Function.Injective f := fun x y h ↦ congrArg Subtype.val h
  have h1 := Fintype.card_le_of_injective f hf
  have h2 := divisible_scaling_upper 2 2 q (by omega) hq
  have h3 := scaled_rootCount_le (k := 4) (p := 2) (q := q) (by omega) hq (by omega)
  norm_num only [show 2+2=4 by omega,show 2+1=3 by omega,Nat.reducePow,
    Nat.reduceMul,show 4-1=3 by omega] at h2 h3
  change rootCount 4 (16*q) ≤ Fintype.card (DivRoots 2 2 (16*q)) at h1
  omega

/-- Four additional binary digits repeat the normalized density. -/
theorem rootCount_two_step (e : ℕ) :
    rootCount 4 (2^(e+4))=2^12*rootCount 4 (2^e) := by
  rw [pow_add,pow_succ]
  have hh := rootCount_sixteen_mul (2^e) (pow_pos (by omega) _)
  norm_num only [Nat.reducePow] at hh ⊢
  simpa only [mul_comm] using hh

/-- The four initial dyadic counts. -/
theorem rootCount_two_initial :
    rootCount 4 1=1 ∧ rootCount 4 2=8 ∧ rootCount 4 4=32 ∧ rootCount 4 8=256 := by
  decide +kernel

/-- An exact formula reducing arbitrary dyadic depth to four initial cases. -/
theorem rootCount_two_blocks (d r : ℕ) :
    rootCount 4 (2^(4*d+r))=2^(12*d)*rootCount 4 (2^r) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show 4*(d+1)+r=(4*d+r)+4 by ring,rootCount_two_step,ih]
    rw [show 12*(d+1)=12+12*d by ring,pow_add]
    ring

/-- At the bad prime 2 the quartic normalized density is at most one. -/
theorem rootCount_two_pow_upper (e : ℕ) : rootCount 4 (2^e) ≤ 2^(3*e) := by
  have hbase : ∀ r : ℕ, r < 4 → rootCount 4 (2^r) ≤ 2^(3*r) := by
    intro r hr
    interval_cases r <;> norm_num [rootCount_two_initial.1,rootCount_two_initial.2.1,
      rootCount_two_initial.2.2.1,rootCount_two_initial.2.2.2]
  calc
    rootCount 4 (2^e) = rootCount 4 (2^(4*(e/4)+e%4)) := by rw [Nat.div_add_mod]
    _ = 2^(12*(e/4))*rootCount 4 (2^(e%4)) := rootCount_two_blocks _ _
    _ ≤ 2^(12*(e/4))*2^(3*(e%4)) := by gcongr; exact hbase _ (Nat.mod_lt _ (by omega))
    _ = 2^(3*e) := by
      rw [← pow_add]
      congr 1
      have hh := Nat.div_add_mod e 4
      omega

/-- A quartic divisor bound valid at EVERY positive modulus, without a
coprimality restriction on the degree. -/
theorem quartic_all_moduli_upper (q : ℕ) : 0 < q →
    rootCount 4 q ≤ q.divisors.card^18*q^3 := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p e hp =>
    intro hq
    by_cases hp2 : p=2
    · subst p
      have htau : 1 ≤ (2^e).divisors.card^18 := by
        simp only [Nat.divisors_prime_pow (by decide : Nat.Prime 2),Finset.card_map,Finset.card_range]
        exact one_le_pow₀ (by omega)
      calc
        rootCount 4 (2^e) ≤ 2^(3*e) := rootCount_two_pow_upper e
        _ = 1*(2^e)^3 := by rw [one_mul,← pow_mul]; congr 1; omega
        _ ≤ _ := Nat.mul_le_mul_right _ htau
    · have hpk : p.Coprime 4 := by
        apply hp.coprime_iff_not_dvd.mpr
        intro hd
        have hpdiv : p ∣ 2 := hp.dvd_of_dvd_pow (n := 2) (by simpa using hd)
        exact hp2 (Nat.le_antisymm (Nat.le_of_dvd (by omega) hpdiv) hp.two_le)
      exact coprime_modulus_upper 2 (p^e) hq (hpk.pow_left e)
  | coprime a b ha hb hab ia ib =>
    intro _
    have hh := Nat.mul_le_mul (ia (by omega)) (ib (by omega))
    rw [rootCount_mul _ _ _ (by omega) (by omega) hab,hab.card_divisors_mul,mul_pow,mul_pow]
    convert hh using 1; ring

/-- Quartic normalized congruence densities are subpolynomial at all moduli. -/
theorem quartic_all_moduli_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ q : ℕ, 0 < q →
      (rootCount 4 q : ℝ) ≤ C*(q : ℝ)^ε*(q : ℝ)^3 := by
  obtain ⟨C,hC,hbound⟩ := divisor_count_subpolynomial (ε/18) (by positivity)
  refine ⟨C^18,pow_pos hC _,?_⟩
  intro q hq
  have hcast : (rootCount 4 q : ℝ) ≤ (q.divisors.card : ℝ)^18*(q : ℝ)^3 := by
    exact_mod_cast quartic_all_moduli_upper q hq
  have hp : ((q : ℝ)^(ε/18))^18=(q : ℝ)^ε := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg q)]
    congr 1
    norm_num
  calc
    (rootCount 4 q : ℝ) ≤ _ := hcast
    _ ≤ (C*(q : ℝ)^(ε/18))^18*(q : ℝ)^3 := by gcongr; exact hbound q hq
    _ = C^18*(q : ℝ)^ε*(q : ℝ)^3 := by rw [mul_pow,hp]

/-- The local certificate is subpolynomial in any positive target divisible
by its modulus, now with no restriction on the modulus. -/
theorem quartic_certificate_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ q n : ℕ, 0 < q → 0 < n → q ∣ n →
      (rootCount 4 q : ℝ)/(q : ℝ)^3 ≤ C*(n : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := quartic_all_moduli_subpolynomial ε hε
  refine ⟨C,hC,?_⟩
  intro q n hq hn hqn
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hle : (q : ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd hn hqn
  have hh : (rootCount 4 q : ℝ)/(q : ℝ)^3 ≤ C*(q : ℝ)^ε :=
    (div_le_iff₀ (pow_pos hqr _)).mpr (hbound q hq)
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hqr.le hle hε.le) hC.le)

/-- No choice of modulus makes this certificate exceed a fixed positive
power at arbitrarily large compatible targets. This does not bound the full
exact representation count. -/
theorem quartic_certificate_eventually_le_power (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℕ, 0 < q → 0 < n → q ∣ n →
      (rootCount 4 q : ℝ)/(q : ℝ)^3 ≤ (n : ℝ)^c := by
  obtain ⟨C,hC,hbound⟩ := quartic_certificate_subpolynomial (c/2) (half_pos hc)
  have ht : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)^(c/2)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (half_pos hc)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (ht.eventually_ge_atTop C)
  refine ⟨N,?_⟩
  intro n hn q hq hnp hqn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnp
  calc
    (rootCount 4 q : ℝ)/(q : ℝ)^3 ≤ C*(n : ℝ)^(c/2) := hbound q n hq hnp hqn
    _ ≤ (n : ℝ)^(c/2)*(n : ℝ)^(c/2) :=
      mul_le_mul_of_nonneg_right (hN n hn) (Real.rpow_nonneg hnr.le _)
    _ = (n : ℝ)^c := by rw [← Real.rpow_add hnr]; congr 1; ring

end
end Erdos322Research.QuarticLocalAllModuli
