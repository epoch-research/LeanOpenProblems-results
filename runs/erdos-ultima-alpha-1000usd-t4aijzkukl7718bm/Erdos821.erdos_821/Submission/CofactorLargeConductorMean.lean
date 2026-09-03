import Submission.CofactorSmallConductorMean
import Submission.WideConductorScales

/-!
# Large-conductor completion and the strict half-level mean

Conductor divisibility reduces completion over all moduli to a harmonic
factor. Logarithmic blocks allow the existing primitive Vaughan estimate
to cover the entire large-conductor interval, not only rough moduli.
-/
open Nat Finset ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

lemma largePrimitiveConductorMangoldt_le_divisor_sum (d R Q N : ℕ) (hdQ : d ≤ Q) :
    largePrimitiveConductorMangoldt d R N ≤
      ∑ c ∈ Icc (R+1) Q, if c ∣ d then
        ∑ ψ ∈ Erdos821.primitiveCharacters c, ‖twistedArithmeticSum ψ vonMangoldt N‖ else 0 := by
  rw [← sum_filter]
  apply sum_le_sum_of_subset_of_nonneg
  · intro c hc
    obtain ⟨hcD,hcR⟩ := mem_filter.mp hc
    have hcdiv := (mem_erase.mp hcD).2
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hcR,(Nat.divisor_le hcdiv).trans hdQ⟩,
      Nat.dvd_of_mem_divisors hcdiv⟩
  · intro c hc hnot
    exact sum_nonneg (fun ψ _ => norm_nonneg _)

lemma largePrimitiveConductorMangoldt_harmonic_mean (Q R N : ℕ) :
    (∑ d ∈ Icc 1 Q, largePrimitiveConductorMangoldt d R N/(d : ℝ)) ≤
      (harmonic Q : ℝ)*primitivePoolMean (Ioc R Q) N := by
  let S : ℕ → ℝ := fun c => ∑ ψ ∈ Erdos821.primitiveCharacters c, ‖twistedArithmeticSum ψ vonMangoldt N‖
  have hS : ∀ c, 0 ≤ S c := fun c => sum_nonneg (fun ψ _ => norm_nonneg _)
  have hH : 0 ≤ (harmonic Q : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    exact sum_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n))
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, (∑ c ∈ Icc (R+1) Q, if c ∣ d then S c else 0)/(d : ℝ) := by
      apply sum_le_sum
      intro d hd
      exact div_le_div_of_nonneg_right
        (largePrimitiveConductorMangoldt_le_divisor_sum d R Q N (mem_Icc.mp hd).2)
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

/-- Uniform completion over every positive modulus up to Q. -/
theorem exists_large_conductor_mean_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q R N : ℕ,
      (∑ d ∈ Icc 1 Q, largePrimitiveConductorMangoldt d R N/(d.totient : ℝ)) ≤
        C*(Q : ℝ)^ε*(harmonic Q : ℝ)*primitivePoolMean (Ioc R Q) N := by
  obtain ⟨C,hC,HC⟩ := exists_uniform_two_pow_primeFactors_div_totient ε hε
  refine ⟨C,hC,?_⟩
  intro Q R N
  have hlocal (d : ℕ) (hd : d ∈ Icc 1 Q) :
      1/(d.totient : ℝ) ≤ C*(Q : ℝ)^ε/(d : ℝ) := by
    apply le_trans _ (HC Q d (mem_Icc.mp hd).1 (mem_Icc.mp hd).2)
    exact div_le_div_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ)≤2)) (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, (C*(Q : ℝ)^ε/(d : ℝ))*largePrimitiveConductorMangoldt d R N := by
      apply sum_le_sum
      intro d hd
      have hh := mul_le_mul_of_nonneg_right (hlocal d hd) (largePrimitiveConductorMangoldt_nonneg d R N)
      simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one,one_mul] using hh
    _ = C*(Q : ℝ)^ε*∑ d ∈ Icc 1 Q, largePrimitiveConductorMangoldt d R N/(d : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d hd
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (largePrimitiveConductorMangoldt_harmonic_mean Q R N)
        (show 0 ≤ C*(Q : ℝ)^ε by positivity)
      convert hh using 1; ring

lemma primitive_interval_mean_blocks (a n t m : ℕ) (ha : 1 ≤ a) (ht : 22 ≤ t)
    (hlevel : 2*(a+n)+5 ≤ t) :
    primitivePoolMean (Ioc (progressionScaleN (a*m)) (progressionScaleN ((a+n)*m)))
      (progressionScaleN (t*m)) ≤
        (n : ℝ)*(wideMeanConstant t : ℝ)*((m : ℝ)+1)^5*(2 : ℝ)^((64*t-1)*m) := by
  induction n with
  | zero => simp [primitivePoolMean]
  | succ n ih =>
    have hlow := ih (by omega : 2*(a+n)+5 ≤ t)
    have hmid := wide_primitive_mean_bound
      (Ioc (progressionScaleN ((a+n)*m)) (progressionScaleN ((a+(n+1))*m)))
      (a+n) (a+(n+1)) t m (by omega) (by omega) (by omega) (by omega) (by omega) (by
        intro d hd
        have hh := mem_Ioc.mp hd
        have hone : 1 ≤ progressionScaleN ((a+n)*m) := by unfold progressionScaleN; exact Nat.one_le_pow _ _ (by decide)
        exact ⟨by omega,hh.1.le,hh.2⟩)
    have h1 : progressionScaleN (a*m) ≤ progressionScaleN ((a+n)*m) :=
      progressionScaleN_monotone (Nat.mul_le_mul_right m (by omega))
    have h2 : progressionScaleN ((a+n)*m) ≤ progressionScaleN ((a+(n+1))*m) :=
      progressionScaleN_monotone (Nat.mul_le_mul_right m (by omega))
    have he : primitivePoolMean
        (Ioc (progressionScaleN (a*m)) (progressionScaleN ((a+(n+1))*m))) (progressionScaleN (t*m)) =
        primitivePoolMean (Ioc (progressionScaleN (a*m)) (progressionScaleN ((a+n)*m))) (progressionScaleN (t*m))+
        primitivePoolMean (Ioc (progressionScaleN ((a+n)*m)) (progressionScaleN ((a+(n+1))*m))) (progressionScaleN (t*m)) := by
      unfold primitivePoolMean
      rw [← Finset.Ioc_union_Ioc_eq_Ioc h1 h2,sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]
    rw [he]
    have hh := _root_.add_le_add hlow hmid
    convert hh using 1; push_cast; ring

/-- The interval can start at any positive fixed power, however small. The
upper endpoint remains strictly below the square-root distribution level. -/
theorem primitive_full_interval_mean_bound (a b t m : ℕ) (ha : 1 ≤ a) (hab : a ≤ b)
    (ht : 22 ≤ t) (hlevel : 2*b+5 ≤ t) :
    primitivePoolMean (Ioc (progressionScaleN (a*m)) (progressionScaleN (b*m)))
      (progressionScaleN (t*m)) ≤
        ((b-a : ℕ) : ℝ)*(wideMeanConstant t : ℝ)*((m : ℝ)+1)^5*(2 : ℝ)^((64*t-1)*m) := by
  have he : a+(b-a)=b := Nat.add_sub_of_le hab
  simpa only [he] using primitive_interval_mean_blocks a (b-a) t m ha ht (by omega)

end Erdos821.AnalyticSieve
