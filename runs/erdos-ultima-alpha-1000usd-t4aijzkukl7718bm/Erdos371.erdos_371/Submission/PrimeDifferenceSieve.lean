import Submission.TwoLinearSelberg

/-! A Selberg upper bound for prime pairs of arbitrary nonzero difference.
The difference is retained in its singular factor, not in the error. -/
namespace Erdos371.FiniteSieve
open Finset
set_option autoImplicit false

lemma twoLinear_selberg_upper_bound_of_roots (S : Finset ℕ) (a b c d N z : ℕ)
    (hz : 1 ≤ z) (hS : ∀ p ∈ S, p.Prime ∧ 2 < p ∧ p ≤ z)
    (hlocal : ∀ p ∈ S, (twoLinearResidues p a b c d).card = 2) :
    (avoidanceCount (range N) (fun p n => p ∣ a*n+b ∨ p ∣ c*n+d) S : ℝ) ≤
      2*N*Real.exp (-2*(∑ p ∈ S, (1 : ℝ)/p)) + 2*(z+1 : ℝ)^64 := by
  have hcop : (↑S : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hS p hp).1 (hS q hq).1).mpr hpq
  have hZ : (1 : ℝ) < (z+1 : ℝ)^16 := one_lt_pow₀ (by exact_mod_cast (show 1 < z+1 by omega)) (by decide)
  have hmass : (∑ p ∈ S, ((twoLinearResidues p a b c d).card : ℝ)/(p : ℝ)) =
      2*(∑ p ∈ S, (1 : ℝ)/p) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p hp
    rw [hlocal p hp]
    push_cast
    ring
  have hm : (∑ p ∈ S, Real.log p*((twoLinearResidues p a b c d).card : ℝ)/(p : ℝ)) ≤
      Real.log ((z+1 : ℝ)^16)/2 := by
    have hsmall : (∑ p ∈ S, Real.log p/(p : ℝ)) ≤ 4*Real.log (z+1 : ℝ) := by
      calc
        _ ≤ ∑ p ∈ (z+1).primesBelow, Real.log p/((p : ℝ)-1) := by
          apply (sum_le_sum ?_).trans
            (sum_le_sum_of_subset_of_nonneg (t := (z+1).primesBelow) ?_ ?_)
          · intro p hp
            have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).1.two_le
            exact div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) (by linarith) (by linarith)
          · intro p hp
            exact Nat.mem_primesBelow.mpr ⟨by have := (hS p hp).2.2; omega,(hS p hp).1⟩
          · intro p hp _
            have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.two_le
            exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
        _ ≤ _ := by simpa only [Nat.cast_add,Nat.cast_one] using prime_log_div_pred_sum_le (z+1)
    have he : (∑ p ∈ S, Real.log p*((twoLinearResidues p a b c d).card : ℝ)/(p : ℝ)) =
        2*(∑ p ∈ S, Real.log p/(p : ℝ)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      rw [hlocal p hp]
      push_cast
      ring
    rw [he,Real.log_pow]
    norm_num
    linarith
  have h := residue_selberg_upper_bound S id (fun p => twoLinearResidues p a b c d)
    (fun p hp => (hS p hp).1.ne_zero) hcop
    (fun p _ => twoLinearResidues_subset p a b c d)
    (fun p hp => by rw [hlocal p hp]; exact ⟨by decide,(hS p hp).2.1⟩)
    ((z+1 : ℝ)^16) hZ hm N
  have havoid : avoidanceCount (range N) (fun p n => n%p ∈ twoLinearResidues p a b c d) S =
      avoidanceCount (range N) (fun p n => p ∣ a*n+b ∨ p ∣ c*n+d) S := by
    unfold avoidanceCount
    congr 1
    ext n
    simp only [mem_filter]
    apply and_congr_right
    intro hn
    exact forall₂_congr fun p hp => not_congr (mod_mem_twoLinearResidues p a b c d n (hS p hp).1.pos)
  simp only [id_eq] at h
  rw [havoid,hmass] at h
  simpa only [neg_mul,← pow_mul,Nat.reduceMul] using h

lemma primeDifference_roots_card (p k : ℕ) (hp : 0 < p) (hk : ¬p ∣ k) :
    (twoLinearResidues p 1 0 1 k).card = 2 := by
  have hd : Disjoint (linearResidues p 1 0) (linearResidues p 1 k) := by
    apply disjoint_left.mpr
    intro n hn hn'
    have h₁ : p ∣ n := by simpa only [linearResidues,mem_filter,one_mul,add_zero] using (mem_filter.mp hn).2
    have h₂ : p ∣ n+k := by simpa only [one_mul] using (mem_filter.mp hn').2
    have hh := Nat.dvd_sub h₂ h₁
    simp only [Nat.add_sub_cancel_left] at hh
    exact hk hh
  rw [twoLinearResidues,card_union_of_disjoint hd,linearResidues_card p 1 0 hp (by simp : Nat.Coprime 1 p),
    linearResidues_card p 1 k hp (by simp : Nat.Coprime 1 p)]

lemma primeDifference_selberg_bound (k N z : ℕ) (hk : 0 < k) (hz : 1 ≤ z) :
    (((range N).filter (fun n => n.Prime ∧ (n+k).Prime ∧ z<n)).card : ℝ) ≤
      2*Real.exp 2*slopeSieveFactor (2*k)*N/(Real.log (z+1 : ℝ))^2+2*(z+1 : ℝ)^64 := by
  let S := goodSievingPrimes z (2*k)
  have hS (p : ℕ) (hp : p ∈ S) : p.Prime ∧ 2 < p ∧ p ≤ z := by
    obtain ⟨hpp,hpz,hnot⟩ := mem_goodSievingPrimes.mp hp
    have hne : p≠2 := by intro he; subst p; exact hnot (dvd_mul_right 2 k)
    exact ⟨hpp,by have := hpp.two_le; omega,hpz⟩
  have hlocal (p : ℕ) (hp : p ∈ S) : (twoLinearResidues p 1 0 1 k).card = 2 :=
    primeDifference_roots_card p k (hS p hp).1.pos
      (fun h => (mem_goodSievingPrimes.mp hp).2.2 (dvd_mul_of_dvd_right h 2))
  have hcount := twoLinear_prime_count_le_avoidance S 1 0 1 k N z
    (fun p hp => ⟨(hS p hp).1,(hS p hp).2.2⟩)
  have heq : (range N).filter (fun n => (1*n+0).Prime ∧ (1*n+k).Prime ∧ z<1*n+0 ∧ z<1*n+k) =
      (range N).filter (fun n => n.Prime ∧ (n+k).Prime ∧ z<n) := by
    ext n
    simp only [mem_filter,one_mul,add_zero]
    constructor
    · rintro ⟨hn,hnp,hkp,hzn,hzkn⟩
      exact ⟨hn,hnp,hkp,hzn⟩
    · rintro ⟨hn,hnp,hkp,hzn⟩
      exact ⟨hn,hnp,hkp,hzn,by omega⟩
  rw [heq] at hcount
  have hb := twoLinear_selberg_upper_bound_of_roots S 1 0 1 k N z hz hS hlocal
  have he := goodSievingPrimes_exp_bound z (2*k) hz (by positivity)
  have hm := mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ 2*N by positivity)
  apply ((Nat.cast_le (α := ℝ)).mpr hcount).trans
  apply hb.trans
  apply add_le_add _ le_rfl
  convert hm using 1 <;> ring

lemma primeDifference_all_count_bound (k N z : ℕ) (hk : 0 < k) (hz : 1 ≤ z) :
    (((range N).filter (fun n => n.Prime ∧ (n+k).Prime)).card : ℝ) ≤
      2*Real.exp 2*slopeSieveFactor (2*k)*N/(Real.log (z+1 : ℝ))^2+2*(z+1 : ℝ)^64+(z+1) := by
  have hsub : (range N).filter (fun n => n.Prime ∧ (n+k).Prime) ⊆
      ((range N).filter (fun n => n.Prime ∧ (n+k).Prime ∧ z<n)) ∪ range (z+1) := by
    intro n hn
    by_cases hzn : z<n
    · exact mem_union_left _ (mem_filter.mpr ⟨(mem_filter.mp hn).1,(mem_filter.mp hn).2.1,
        (mem_filter.mp hn).2.2,hzn⟩)
    · exact mem_union_right _ (mem_range.mpr (by omega))
  have hh := (card_le_card hsub).trans (card_union_le _ _)
  rw [card_range] at hh
  have hc : (((range N).filter (fun n => n.Prime ∧ (n+k).Prime)).card : ℝ) ≤
      (((range N).filter (fun n => n.Prime ∧ (n+k).Prime ∧ z<n)).card : ℝ)+(z+1) := by exact_mod_cast hh
  exact hc.trans (add_le_add (primeDifference_selberg_bound k N z hk hz) le_rfl)

#print axioms primeDifference_all_count_bound
end Erdos371.FiniteSieve
