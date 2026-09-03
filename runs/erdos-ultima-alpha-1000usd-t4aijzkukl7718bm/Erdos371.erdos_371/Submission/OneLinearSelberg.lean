import Submission.RoughSelbergBound

/-! A one-linear-form Selberg sieve with an exact totient slope factor and
an error independent of the slope and intercept. This is a finite unsigned
upper bound; it does not assert prime cancellation. -/
namespace Erdos371.FiniteSieve
open Finset
set_option autoImplicit false

lemma exp_slopePrimeMass_le_totient_ratio (a : ℕ) (ha : 0 < a) :
    Real.exp (slopePrimeMass a) ≤ (a : ℝ)/a.totient := by
  have hprod : (∏ p ∈ a.primeFactors, (1-(1 : ℝ)/p)) ≤ Real.exp (-slopePrimeMass a) := by
    simp only [slopePrimeMass,← sum_neg_distrib,Real.exp_sum]
    apply prod_le_prod
    · intro p hp
      have hp' := (Nat.mem_primeFactors.mp hp).1
      exact sub_nonneg.mpr ((div_le_one (by exact_mod_cast hp'.pos)).mpr (by exact_mod_cast hp'.one_le))
    · intro p _
      simpa only [neg_div,neg_add_eq_sub] using Real.add_one_le_exp (-(1 : ℝ)/p)
  have he := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors a)
  push_cast at he
  simp only [← one_div] at he
  have hphi : (0 : ℝ) < a.totient := by exact_mod_cast Nat.totient_pos.mpr ha
  apply (le_div_iff₀ hphi).mpr
  have hh := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
  rw [← he] at hh
  have ht := mul_le_mul_of_nonneg_left hh (Real.exp_pos (slopePrimeMass a)).le
  have hx : Real.exp (slopePrimeMass a)*((a : ℝ)*Real.exp (-slopePrimeMass a)) = a := by
    rw [mul_left_comm,← Real.exp_add]
    simp
  rwa [hx] at ht

lemma goodSievingPrimes_one_exp_bound (z a : ℕ) (hz : 1 ≤ z) (ha : 0 < a) :
    Real.exp (-(∑ p ∈ goodSievingPrimes z a, (1 : ℝ)/p)) ≤
      Real.exp 1*((a : ℝ)/a.totient)/Real.log (z+1 : ℝ) := by
  have hlog : 0 < Real.log (z+1 : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < z+1 by omega))
  have hm := goodSievingPrimes_mass_lower z a ha.ne'
  calc
    _ ≤ Real.exp (-primeHarmonic z+slopePrimeMass a) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-primeHarmonic z)*Real.exp (slopePrimeMass a) := Real.exp_add _ _
    _ ≤ (Real.exp 1/Real.log (z+1 : ℝ))*((a : ℝ)/a.totient) :=
      mul_le_mul (exp_neg_primeHarmonic_le z hz) (exp_slopePrimeMass_le_totient_ratio a ha)
        (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

lemma mod_mem_linearResidues (p a b n : ℕ) (hp : 0 < p) :
    n%p ∈ linearResidues p a b ↔ p ∣ a*n+b := by
  simp [linearResidues,Nat.mod_lt n hp,Nat.dvd_iff_mod_eq_zero,Nat.add_mod,Nat.mul_mod]

lemma oneLinear_selberg_upper_bound (S : Finset ℕ) (a b N z : ℕ) (hz : 1 ≤ z)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ z) (ha : ∀ p ∈ S, a.Coprime p) :
    (avoidanceCount (range N) (fun p n => p ∣ a*n+b) S : ℝ) ≤
      2*N*Real.exp (-(∑ p ∈ S, (1 : ℝ)/p))+2*(z+1 : ℝ)^32 := by
  have hlocal (p : ℕ) (hp : p ∈ S) : (linearResidues p a b).card = 1 :=
    linearResidues_card p a b (hS p hp).1.pos (ha p hp)
  have hcop : (↑S : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hS p hp).1 (hS q hq).1).mpr hpq
  have hZ : (1 : ℝ) < (z+1 : ℝ)^8 := one_lt_pow₀
    (by exact_mod_cast (show 1 < z+1 by omega)) (by decide)
  have hm : (∑ p ∈ S, Real.log p*((linearResidues p a b).card : ℝ)/(p : ℝ)) ≤
      Real.log ((z+1 : ℝ)^8)/2 := by
    have he : (∑ p ∈ S, Real.log p/(p : ℝ)) ≤ 4*Real.log (z+1 : ℝ) := by
      calc
        _ ≤ ∑ p ∈ (z+1).primesBelow, Real.log p/((p : ℝ)-1) := by
          apply (sum_le_sum ?_).trans (sum_le_sum_of_subset_of_nonneg ?_ ?_)
          · intro p hp
            have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).1.two_le
            exact div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) (by linarith) (by linarith)
          · intro p hp
            exact Nat.mem_primesBelow.mpr ⟨by have := (hS p hp).2; omega,(hS p hp).1⟩
          · intro p hp _
            have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.two_le
            exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
        _ ≤ _ := by simpa only [Nat.cast_add,Nat.cast_one] using prime_log_div_pred_sum_le (z+1)
    have heloc : (∑ p ∈ S, Real.log p*((linearResidues p a b).card : ℝ)/p) =
        ∑ p ∈ S, Real.log p/(p : ℝ) := by
      apply sum_congr rfl
      intro p hp
      rw [hlocal p hp]
      simp
    rw [heloc,Real.log_pow]
    norm_num
    linarith
  have hh := residue_selberg_upper_bound S id (fun p => linearResidues p a b)
    (fun p hp => (hS p hp).1.ne_zero) hcop (fun p _ => filter_subset _ _)
    (fun p hp => by rw [hlocal p hp]; exact ⟨by decide,(hS p hp).1.one_lt⟩)
    ((z+1 : ℝ)^8) hZ hm N
  have havoid : avoidanceCount (range N) (fun p n => n%p ∈ linearResidues p a b) S =
      avoidanceCount (range N) (fun p n => p ∣ a*n+b) S := by
    unfold avoidanceCount
    congr 1
    ext n
    simp only [mem_filter]
    exact and_congr_right (fun _ => forall₂_congr (fun p hp =>
      not_congr (mod_mem_linearResidues p a b n (hS p hp).1.pos)))
  simp only [id_eq,← pow_mul,Nat.reduceMul] at hh
  rw [havoid] at hh
  convert hh using 1
  congr 4
  apply sum_congr rfl
  intro p hp
  rw [hlocal p hp,Nat.cast_one]

/-- The sieve is performed on the index n, not on the values a*n+b. Thus
its polynomial error does not contain a power of the modulus a. -/
theorem oneLinear_prime_count_selberg_bound (a b N z : ℕ) (ha : 0 < a) (hz : 1 ≤ z) :
    (((range N).filter (fun n => (a*n+b).Prime ∧ z<a*n+b)).card : ℝ) ≤
      2*Real.exp 1*((a : ℝ)/a.totient)*N/Real.log (z+1 : ℝ)+2*(z+1 : ℝ)^32 := by
  let S := goodSievingPrimes z a
  have hS (p : ℕ) (hp : p ∈ S) : p.Prime ∧ p ≤ z ∧ ¬p ∣ a := mem_goodSievingPrimes.mp hp
  have hc (p : ℕ) (hp : p ∈ S) : a.Coprime p :=
    ((hS p hp).1.coprime_iff_not_dvd.mpr (hS p hp).2.2).symm
  have hcount : ((range N).filter (fun n => (a*n+b).Prime ∧ z<a*n+b)).card ≤
      avoidanceCount (range N) (fun p n => p ∣ a*n+b) S := by
    classical
    unfold avoidanceCount
    conv_rhs => rw [filter_congr_decidable]
    apply card_le_card
    intro n hn
    obtain ⟨hn,hprime,hlarge⟩ := mem_filter.mp hn
    refine mem_filter.mpr ⟨hn,?_⟩
    intro p hp hd
    have he := (hprime.dvd_iff_eq (hS p hp).1.ne_one).mp hd
    have hz' := (hS p hp).2.1
    omega
  have hb := oneLinear_selberg_upper_bound S a b N z hz (fun p hp => ⟨(hS p hp).1,(hS p hp).2.1⟩) hc
  have hm := mul_le_mul_of_nonneg_left (goodSievingPrimes_one_exp_bound z a hz ha)
    (show (0 : ℝ) ≤ 2*N by positivity)
  apply ((Nat.cast_le (α := ℝ)).mpr hcount).trans (hb.trans _)
  apply add_le_add _ le_rfl
  convert hm using 1; ring

lemma oneLinear_small_prime_count (a b N z : ℕ) (ha : 0 < a) :
    ((range N).filter (fun n => (a*n+b).Prime ∧ a*n+b ≤ z)).card ≤ z := by
  have hc : ((range N).filter (fun n => (a*n+b).Prime ∧ a*n+b ≤ z)).card ≤ (Icc 1 z).card := by
    apply card_le_card_of_injOn (fun n => a*n+b)
    · intro n hn
      change n ∈ (range N).filter (fun n => (a*n+b).Prime ∧ a*n+b ≤ z) at hn
      obtain ⟨_,hp,hz⟩ := mem_filter.mp hn
      exact mem_Icc.mpr ⟨hp.pos,hz⟩
    · intro n _ m _ he
      exact Nat.eq_of_mul_eq_mul_left ha (Nat.add_right_cancel he)
  simpa only [Nat.card_Icc,Nat.add_sub_cancel] using hc

/-- Restores the small prime exceptions, costing at most z indices. -/
theorem oneLinear_all_prime_count_bound (a b N z : ℕ) (ha : 0 < a) (hz : 1 ≤ z) :
    (((range N).filter (fun n => (a*n+b).Prime)).card : ℝ) ≤
      2*Real.exp 1*((a : ℝ)/a.totient)*N/Real.log (z+1 : ℝ)+2*(z+1 : ℝ)^32+z := by
  let P := (range N).filter (fun n => (a*n+b).Prime ∧ z<a*n+b)
  let Q := (range N).filter (fun n => (a*n+b).Prime ∧ a*n+b ≤ z)
  have hsub : (range N).filter (fun n => (a*n+b).Prime) ⊆ P ∪ Q := by
    intro n hn
    obtain ⟨hn,hp⟩ := mem_filter.mp hn
    by_cases hz : z<a*n+b
    · exact mem_union_left _ (mem_filter.mpr ⟨hn,hp,hz⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hn,hp,le_of_not_gt hz⟩)
  have hc := (card_le_card hsub).trans ((card_union_le P Q).trans
    (Nat.add_le_add_left (oneLinear_small_prime_count a b N z ha) P.card))
  have hcr : (((range N).filter (fun n => (a*n+b).Prime)).card : ℝ) ≤ (P.card : ℝ)+z := by
    exact_mod_cast hc
  exact hcr.trans (add_le_add (oneLinear_prime_count_selberg_bound a b N z ha hz) le_rfl)

#print axioms oneLinear_prime_count_selberg_bound
end Erdos371.FiniteSieve
