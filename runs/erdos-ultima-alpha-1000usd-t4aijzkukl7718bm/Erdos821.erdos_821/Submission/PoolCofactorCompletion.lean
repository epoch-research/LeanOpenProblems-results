import Submission.PoolCofactorConductorSplit

/-!
# All-modulus completion on unit-supported multiplier pools

The set of sieve moduli can be any subset of [1,Q] on which the two unit-
support hypotheses hold. No lifting-error term or condition Q<N is used.
-/
open Nat Finset ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

lemma poolLargeConductor_le_divisor_sum (f : ArithmeticFunction ℝ) (P : Finset ℕ) (d R Q B N : ℕ) (hdQ : d ≤ Q) :
    poolLargeConductor f P d R B N ≤
      ∑ c ∈ Icc (R+1) Q, if c ∣ d then
        ∑ ψ ∈ Erdos821.primitiveCharacters c, ‖∑ z ∈ P, ψ (z : ZMod c)‖*cofactorMaxPrefix ψ B*‖twistedArithmeticSum ψ f N‖ else 0 := by
  rw [← sum_filter]
  apply sum_le_sum_of_subset_of_nonneg
  · intro c hc
    obtain ⟨hcD,hcR⟩ := mem_filter.mp hc
    have hcdiv := (mem_erase.mp hcD).2
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hcR,(Nat.divisor_le hcdiv).trans hdQ⟩,
      Nat.dvd_of_mem_divisors hcdiv⟩
  · intro c hc hnot
    exact sum_nonneg (fun ψ _ => mul_nonneg (mul_nonneg (norm_nonneg (∑ z ∈ P, ψ (z : ZMod c))) (cofactorMaxPrefix_nonneg ψ B)) (norm_nonneg _))

lemma poolLargeConductor_harmonic_mean (f : ArithmeticFunction ℝ) (P : Finset ℕ) (Q R B N : ℕ) :
    (∑ d ∈ Icc 1 Q, poolLargeConductor f P d R B N/(d : ℝ)) ≤
      (harmonic Q : ℝ)*primitivePoolCofactorMean f (Ioc R Q) P B N := by
  let S : ℕ → ℝ := fun c => ∑ ψ ∈ Erdos821.primitiveCharacters c, ‖∑ z ∈ P, ψ (z : ZMod c)‖*cofactorMaxPrefix ψ B*‖twistedArithmeticSum ψ f N‖
  have hS : ∀ c, 0 ≤ S c := fun c => sum_nonneg (fun ψ _ => mul_nonneg (mul_nonneg (norm_nonneg (∑ z ∈ P, ψ (z : ZMod c))) (cofactorMaxPrefix_nonneg ψ B)) (norm_nonneg _))
  have hH : 0 ≤ (harmonic Q : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    exact sum_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n))
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, (∑ c ∈ Icc (R+1) Q, if c ∣ d then S c else 0)/(d : ℝ) := by
      apply sum_le_sum
      intro d hd
      exact div_le_div_of_nonneg_right
        (poolLargeConductor_le_divisor_sum f P d R Q B N (mem_Icc.mp hd).2)
        (Nat.cast_nonneg d)
    _ = ∑ c ∈ Icc (R+1) Q, S c*(∑ d ∈ Icc 1 Q with c ∣ d, (d : ℝ)⁻¹) := by
      simp only [sum_div]
      rw [sum_comm]
      apply sum_congr rfl
      intro c hc
      rw [sum_filter,mul_sum]
      apply sum_congr rfl
      intro d hd
      split_ifs <;> simp [div_eq_mul_inv]
    _ ≤ ∑ c ∈ Icc (R+1) Q, S c*((c : ℝ)⁻¹*(harmonic Q : ℝ)) := by
      apply sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left
        (Sieve.sum_inv_multiples_le_harmonic Q c (by have := (mem_Icc.mp hc).1; omega)) (hS c)
    _ = (harmonic Q : ℝ)*∑ c ∈ Icc (R+1) Q, S c/(c : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro c hc
      ring
    _ ≤ (harmonic Q : ℝ)*∑ c ∈ Icc (R+1) Q, S c/(c.totient : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hH
      apply sum_le_sum
      intro c hc
      have hc0 : 0 < c := by have := (mem_Icc.mp hc).1; omega
      exact div_le_div_of_nonneg_left (hS c) (by exact_mod_cast Nat.totient_pos.mpr hc0)
        (by exact_mod_cast Nat.totient_le c)
    _ = _ := by rw [show Icc (R+1) Q = Ioc R Q by ext n; simp]; rfl

lemma pool_conductor_mean_of_local_weight (f : ArithmeticFunction ℝ) (P : Finset ℕ) (Q R B N : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (H : ∀ d ∈ Icc 1 Q, (2 : ℝ)^d.primeFactors.card/(d.totient : ℝ) ≤ K/(d : ℝ)) :
    (∑ d ∈ Icc 1 Q, (2 : ℝ)^d.primeFactors.card/(d.totient : ℝ)*poolLargeConductor f P d R B N) ≤
      K*(harmonic Q : ℝ)*primitivePoolCofactorMean f (Ioc R Q) P B N := by
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, K/(d : ℝ)*poolLargeConductor f P d R B N := by
      apply sum_le_sum
      intro d hd
      have hh := mul_le_mul_of_nonneg_right (H d hd)
        (poolLargeConductor_nonneg f P d R B N)
      exact hh
    _ = K*∑ d ∈ Icc 1 Q, poolLargeConductor f P d R B N/(d : ℝ) := by
      rw [mul_sum]
      exact sum_congr rfl (fun d _ => by ring)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (poolLargeConductor_harmonic_mean f P Q R B N) hK
      convert hh using 1; ring

/-- Complete the discrepancy only over moduli on which both supports are units.
The nonnegative conductor majorants, but not the unit hypotheses, are extended
from S to the full interval. -/
theorem pool_unit_all_modulus_mean_of_local_weight (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (P S : Finset ℕ) (Q R B N : ℕ)
    (hS : S ⊆ Icc 1 Q) (u : ∀ d : ℕ, (ZMod d)ˣ)
    (hP : ∀ d ∈ S, ∀ c ∈ P, c.Coprime d)
    (hunit : ∀ d ∈ S, ∀ n ∈ Icc 1 N, f n ≠ 0 → n.Coprime d)
    (K : ℝ) (hK : 0 ≤ K)
    (H : ∀ d ∈ Icc 1 Q, (2 : ℝ)^d.primeFactors.card/(d.totient : ℝ) ≤ K/(d : ℝ)) :
    (∑ d ∈ S, |poolCofactorWeight f P d (u d) 0 B N-poolCofactorPrincipal f P d 0 B N|) ≤
      K*((P.card : ℝ)*restrictedMass f N*(harmonic Q : ℝ)*(R : ℝ)*(Real.sqrt R*(1+Real.log R))+
        (harmonic Q : ℝ)*primitivePoolCofactorMean f (Ioc R Q) P B N) := by
  let F : ℝ := (P.card : ℝ)*restrictedMass f N
  let M : ℕ → ℝ := fun d =>
    F*((2 : ℝ)^d.primeFactors.card/(d.totient : ℝ)*smallConductorCofactorWeight d R)+
      (2 : ℝ)^d.primeFactors.card/(d.totient : ℝ)*poolLargeConductor f P d R B N
  have hF : 0 ≤ F := mul_nonneg (Nat.cast_nonneg _) (restrictedMass_nonneg f hf N)
  have hM : ∀ d, 0 ≤ M d := by
    intro d
    dsimp [M]
    positivity [smallConductorCofactorWeight_nonneg d R,
      poolLargeConductor_nonneg f P d R B N]
  have hpoint (d : ℕ) (hd : d ∈ S) :
      |poolCofactorWeight f P d (u d) 0 B N-poolCofactorPrincipal f P d 0 B N| ≤ M d := by
    letI : NeZero d := ⟨by have := (mem_Icc.mp (hS hd)).1; omega⟩
    have hh := pool_unit_progression_split f hf P d (u d) R B N (hP d hd) (hunit d hd)
    convert hh using 1; dsimp [M,F]; ring
  have hh := (sum_le_sum hpoint).trans
    (sum_le_sum_of_subset_of_nonneg hS (fun d _ _ => hM d))
  dsimp only [M] at hh
  simp only [sum_add_distrib,← mul_sum] at hh
  have hs := mul_le_mul_of_nonneg_left (small_conductor_mean_of_local_weight Q R K hK H) hF
  have hl := pool_conductor_mean_of_local_weight f P Q R B N K hK H
  apply (hh.trans (_root_.add_le_add hs hl)).trans_eq
  dsimp [F]
  ring

/-- The principal-density replacement has no nonunit correction on the
supported moduli. -/
lemma pool_unit_principal_density_error (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (P : Finset ℕ) (d A B N : ℕ) (hd : 0 < d)
    (hunit : ∀ n ∈ Icc 1 N, f n ≠ 0 → n.Coprime d) :
    |poolCofactorPrincipal f P d A B N-
      (P.card : ℝ)*((B-A : ℕ) : ℝ)*restrictedMass f N/(d : ℝ)| ≤
      (P.card : ℝ)*restrictedMass f N*((3 : ℝ)^d.primeFactors.card/(d.totient : ℝ)) := by
  have hh := restricted_principal_density_error f hf d A B N hd
  have hz := unit_supported_nonunitMass_zero f d N hunit
  rw [hz,mul_zero,zero_div,add_zero] at hh
  have he : poolCofactorPrincipal f P d A B N-
      (P.card : ℝ)*((B-A : ℕ) : ℝ)*restrictedMass f N/(d : ℝ) =
      (P.card : ℝ)*(restrictedCofactorPrincipal f d A B N-
        ((B-A : ℕ) : ℝ)*restrictedMass f N/(d : ℝ)) := by
    dsimp [poolCofactorPrincipal,restrictedCofactorPrincipal]
    rw [hz]
    ring
  rw [he,abs_mul,abs_of_nonneg (Nat.cast_nonneg P.card)]
  apply (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg P.card)).trans_eq
  ring

lemma pool_unit_principal_mean_of_local_weight (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (P S : Finset ℕ) (Q A B N : ℕ)
    (hS : S ⊆ Icc 1 Q)
    (hunit : ∀ d ∈ S, ∀ n ∈ Icc 1 N, f n ≠ 0 → n.Coprime d)
    (K : ℝ) (hK : 0 ≤ K)
    (H : ∀ d ∈ Icc 1 Q, (3 : ℝ)^d.primeFactors.card/(d.totient : ℝ) ≤ K/(d : ℝ)) :
    (∑ d ∈ S, |poolCofactorPrincipal f P d A B N-
      (P.card : ℝ)*((B-A : ℕ) : ℝ)*restrictedMass f N/(d : ℝ)|) ≤
      K*(harmonic Q : ℝ)*((P.card : ℝ)*restrictedMass f N) := by
  have hF := mul_nonneg (Nat.cast_nonneg P.card) (restrictedMass_nonneg f hf N)
  calc
    _ ≤ ∑ d ∈ S, (P.card : ℝ)*restrictedMass f N*(K/(d : ℝ)) := by
      apply sum_le_sum
      intro d hd
      exact (pool_unit_principal_density_error f hf P d A B N
        (mem_Icc.mp (hS hd)).1 (hunit d hd)).trans
          (mul_le_mul_of_nonneg_left (H d (hS hd)) hF)
    _ ≤ ∑ d ∈ Icc 1 Q, (P.card : ℝ)*restrictedMass f N*(K/(d : ℝ)) := by
      apply sum_le_sum_of_subset_of_nonneg hS
      intro d hd hnot
      exact mul_nonneg hF (div_nonneg hK (Nat.cast_nonneg d))
    _ = _ := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rw [mul_sum,sum_mul]
      apply sum_congr rfl
      intro d hd
      ring

/-- Natural-density completion, with no B*Q lifting term. -/
theorem pool_unit_natural_mean_of_local_weight (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (P S : Finset ℕ) (Q R B N : ℕ)
    (hS : S ⊆ Icc 1 Q) (u : ∀ d : ℕ, (ZMod d)ˣ)
    (hP : ∀ d ∈ S, ∀ c ∈ P, c.Coprime d)
    (hunit : ∀ d ∈ S, ∀ n ∈ Icc 1 N, f n ≠ 0 → n.Coprime d)
    (K : ℝ) (hK : 0 ≤ K)
    (H : ∀ d ∈ Icc 1 Q, (3 : ℝ)^d.primeFactors.card/(d.totient : ℝ) ≤ K/(d : ℝ)) :
    (∑ d ∈ S, |poolCofactorWeight f P d (u d) 0 B N-
      (P.card : ℝ)*(B : ℝ)*restrictedMass f N/(d : ℝ)|) ≤
      K*(harmonic Q : ℝ)*((P.card : ℝ)*restrictedMass f N*
        (1+(R : ℝ)*(Real.sqrt R*(1+Real.log R)))+
          primitivePoolCofactorMean f (Ioc R Q) P B N) := by
  have H2 (d : ℕ) (hd : d ∈ Icc 1 Q) :
      (2 : ℝ)^d.primeFactors.card/(d.totient : ℝ) ≤ K/(d : ℝ) := by
    apply (div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 3) _)
        (Nat.cast_nonneg _)).trans (H d hd)
  have h1 := pool_unit_all_modulus_mean_of_local_weight f hf P S Q R B N hS u hP hunit K hK H2
  have h2 := pool_unit_principal_mean_of_local_weight f hf P S Q 0 B N hS hunit K hK H
  simp only [Nat.sub_zero] at h2
  have hh : (∑ d ∈ S, |poolCofactorWeight f P d (u d) 0 B N-
      (P.card : ℝ)*(B : ℝ)*restrictedMass f N/(d : ℝ)|) ≤
      (∑ d ∈ S, |poolCofactorWeight f P d (u d) 0 B N-poolCofactorPrincipal f P d 0 B N|)+
        (∑ d ∈ S, |poolCofactorPrincipal f P d 0 B N-
          (P.card : ℝ)*(B : ℝ)*restrictedMass f N/(d : ℝ)|) := by
    rw [← sum_add_distrib]
    exact sum_le_sum (fun d hd => abs_sub_le _ _ _)
  apply (hh.trans (_root_.add_le_add h1 h2)).trans_eq
  ring

/-- The constant is uniform in both supports and in the set of unit moduli. -/
theorem exists_pool_unit_natural_mean_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ArithmeticFunction ℝ,
      (∀ n, 0 ≤ f n) → ∀ P S : Finset ℕ, ∀ Q R B N : ℕ,
      S ⊆ Icc 1 Q → ∀ u : ∀ d : ℕ, (ZMod d)ˣ,
      (∀ d ∈ S, ∀ c ∈ P, c.Coprime d) →
      (∀ d ∈ S, ∀ n ∈ Icc 1 N, f n ≠ 0 → n.Coprime d) →
      (∑ d ∈ S, |poolCofactorWeight f P d (u d) 0 B N-
        (P.card : ℝ)*(B : ℝ)*restrictedMass f N/(d : ℝ)|) ≤
        C*(Q : ℝ)^ε*(harmonic Q : ℝ)*((P.card : ℝ)*restrictedMass f N*
          (1+(R : ℝ)*(Real.sqrt R*(1+Real.log R)))+
            primitivePoolCofactorMean f (Ioc R Q) P B N) := by
  obtain ⟨C,hC,HC⟩ := exists_uniform_local_factor_div_totient 3 ε (by norm_num) hε
  refine ⟨C,hC,?_⟩
  intro f hf P S Q R B N hS u hP hunit
  exact pool_unit_natural_mean_of_local_weight f hf P S Q R B N hS u hP hunit
    (C*(Q : ℝ)^ε) (by positivity)
      (fun d hd => HC Q d (mem_Icc.mp hd).1 (mem_Icc.mp hd).2)

end Erdos821.AnalyticSieve
