import FormalConjecturesUtil
import Submission.WeightedSmoothCount

/-! An elementary Rankin bound for smooth integers, obtained from the
squarefree-part decomposition. This does not give signed cancellation. -/

namespace Erdos371RankinSmoothCount

open Finset

lemma reciprocal_rpow_step {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (k : ℕ) :
    1 / ((k+1:ℕ):ℝ)^σ ≤
      (((k+1:ℕ):ℝ)^(1-σ)-(k:ℝ)^(1-σ))/(1-σ) := by
  let y : ℝ := k+1
  have hy : 0 < y := by dsimp [y]; positivity
  have hy1 : 1 ≤ y := by dsimp [y]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hr : 0 < 1-σ := by linarith
  have hh := rpow_one_add_le_one_add_mul_self
    (s := -(1/y)) (p := 1-σ)
    (show -1 ≤ -(1/y) by have := (div_le_one hy).mpr hy1; linarith)
    hr.le (by linarith)
  have he : 1 + -(1/y) = (k:ℝ)/y := by dsimp [y]; field_simp; ring
  rw [he,Real.div_rpow (Nat.cast_nonneg k) hy.le] at hh
  have hm := (div_le_iff₀ (Real.rpow_pos_of_pos hy (1-σ))).mp hh
  have hp : y^(1-σ)*y^σ = y := by
    rw [← Real.rpow_add hy]; simp
  have he' : (1-(1-σ)/y)*y^(1-σ) = y^(1-σ)-(1-σ)/y^σ := by
    have hn : y^σ ≠ 0 := (Real.rpow_pos_of_pos hy σ).ne'
    field_simp
    nlinarith [hp]
  have hm' : (k:ℝ)^(1-σ) ≤ y^(1-σ)-(1-σ)/y^σ := by
    convert hm using 1 <;> (rw [← he']; ring)
  push_cast
  change 1/y^σ ≤ (y^(1-σ)-(k:ℝ)^(1-σ))/(1-σ)
  apply (le_div_iff₀ hr).mpr
  have heq : (1-σ)/y^σ = 1/y^σ*(1-σ) := by ring
  rw [heq] at hm'
  linarith

lemma reciprocal_rpow_sum {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (K : ℕ) :
    (∑ p ∈ Icc 1 K, 1/(p:ℝ)^σ) ≤ (K:ℝ)^(1-σ)/(1-σ) := by
  induction K with
  | zero => simp [Real.zero_rpow (by linarith : 1-σ ≠ 0)]
  | succ K ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hh := reciprocal_rpow_step hσ0 hσ1 K
    rw [sub_div] at hh
    linarith

lemma product_bound {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (K : ℕ) :
    (∏ p ∈ Icc 1 K, (1+1/(p:ℝ)^σ)) ≤ Real.exp ((K:ℝ)^(1-σ)/(1-σ)) := by
  calc
    _ ≤ ∏ p ∈ Icc 1 K, Real.exp (1/(p:ℝ)^σ) := by
      apply prod_le_prod
      · intro p hp; positivity
      · intro p hp
        simpa [add_comm] using Real.add_one_le_exp (1/(p:ℝ)^σ)
    _ = Real.exp (∑ p ∈ Icc 1 K, 1/(p:ℝ)^σ) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (reciprocal_rpow_sum hσ0 hσ1 K)

lemma weighted_quotient {σ : ℝ} (hσ : 1/2 ≤ σ) (N : ℕ) {a : ℕ} (ha : 0 < a) :
    ((Nat.sqrt (N/a):ℕ):ℝ) ≤ (N:ℝ)^σ/(a:ℝ)^σ := by
  by_cases h : a ≤ N
  · have hx : (1:ℝ) ≤ (N:ℝ)/a := (le_div_iff₀ (Nat.cast_pos.mpr ha)).mpr (by simpa using (Nat.cast_le (α := ℝ)).mpr h)
    calc
      _ ≤ Real.sqrt (N/a:ℕ) := Real.nat_sqrt_le_real_sqrt
      _ ≤ Real.sqrt ((N:ℝ)/a) := Real.sqrt_le_sqrt Nat.cast_div_le
      _ = ((N:ℝ)/a)^(1/2:ℝ) := Real.sqrt_eq_rpow _
      _ ≤ ((N:ℝ)/a)^σ := Real.rpow_le_rpow_of_exponent_le hx hσ
      _ = _ := Real.div_rpow (Nat.cast_nonneg N) (Nat.cast_nonneg a) σ
  · rw [Nat.div_eq_of_lt (by omega : N<a)]
    simp only [Nat.sqrt_zero,Nat.cast_zero]
    positivity

lemma positive_smooth_count_bound {σ : ℝ} (hσ : 1/2 ≤ σ) (K N : ℕ) :
    (((range N).filter (fun n => n ≠ 0 ∧ Nat.maxPrimeFac n ≤ K)).card:ℝ) ≤
      (N:ℝ)^σ*(∏ p ∈ Icc 1 K, (1+1/(p:ℝ)^σ)) := by
  let S := Icc 1 K
  let F (t : Finset ℕ) := (Icc 1 (Nat.sqrt (N/(∏ p ∈ t,p)))).image
    (fun b => b^2*(∏ p ∈ t,p))
  let G := (range N).filter (fun n => n ≠ 0 ∧ Nat.maxPrimeFac n ≤ K)
  have htpos (t : Finset ℕ) (ht : t ∈ S.powerset) : 0 < ∏ p ∈ t,p := by
    apply prod_pos
    intro p hp
    exact (mem_Icc.mp (mem_powerset.mp ht hp)).1
  have hsub : G ⊆ S.powerset.biUnion F := by
    intro n hn
    obtain ⟨hnN,hn0,hnK⟩ := mem_filter.mp hn
    obtain ⟨a,b,hab,ha⟩ := Nat.sq_mul_squarefree n
    have hadvd : a ∣ n := hab ▸ dvd_mul_left a (b^2)
    have hsuba : a.primeFactors ⊆ S := by
      intro p hp
      obtain ⟨hpp,hpd,_⟩ := Nat.mem_primeFactors.mp hp
      exact mem_Icc.mpr ⟨hpp.one_lt.le,(Nat.le_maxPrimeFac hn0 hpp (hpd.trans hadvd)).trans hnK⟩
    have hprod : (∏ p ∈ a.primeFactors,p) = a := Nat.prod_primeFactors_of_squarefree ha
    have hbpos : 0 < b := by
      by_contra hh
      have hb0 : b=0 := by omega
      simp [hb0] at hab
      exact hn0 hab.symm
    have hbnd : b ≤ Nat.sqrt (N/a) := by
      apply Nat.le_sqrt'.mpr
      apply (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero ha.ne_zero)).mpr
      rw [hab]
      exact (mem_range.mp hnN).le
    apply mem_biUnion.mpr
    refine ⟨a.primeFactors,mem_powerset.mpr hsuba,mem_image.mpr ⟨b,?_,?_⟩⟩
    · rw [hprod]; exact mem_Icc.mpr ⟨hbpos,hbnd⟩
    · simpa [hprod] using hab
  have hcount : G.card ≤ ∑ t ∈ S.powerset, Nat.sqrt (N/(∏ p ∈ t,p)) := by
    calc
      _ ≤ (S.powerset.biUnion F).card := card_le_card hsub
      _ ≤ ∑ t ∈ S.powerset,(F t).card := card_biUnion_le
      _ ≤ _ := sum_le_sum (fun t ht => by
        simpa [F] using card_image_le (s := Icc 1 (Nat.sqrt (N/(∏ p ∈ t,p)))))
  change (G.card:ℝ) ≤ _
  calc
    _ ≤ ∑ t ∈ S.powerset,((Nat.sqrt (N/(∏ p ∈ t,p)):ℕ):ℝ) := by exact_mod_cast hcount
    _ ≤ ∑ t ∈ S.powerset,(N:ℝ)^σ/((∏ p ∈ t,p:ℕ):ℝ)^σ :=
      sum_le_sum (fun t ht => weighted_quotient hσ N (htpos t ht))
    _ = (N:ℝ)^σ*∑ t ∈ S.powerset,∏ p ∈ t,(1/(p:ℝ)^σ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro t ht
      rw [prod_div_distrib]
      simp only [prod_const_one,mul_one_div]
      congr 2
      push_cast
      exact (Real.finset_prod_rpow t (fun p => (p:ℝ)) (fun p hp => Nat.cast_nonneg p) σ).symm
    _ = _ := by rw [← prod_one_add]

/-- The smooth counting bound is valid uniformly in the cutoff and endpoint. -/
theorem smooth_count_rankin_bound {σ : ℝ} (hσ0 : 1/2 ≤ σ) (hσ1 : σ < 1) (K N : ℕ) :
    (((range N).filter (fun n => Nat.maxPrimeFac n ≤ K)).card:ℝ) ≤
      1+(N:ℝ)^σ*Real.exp ((K:ℝ)^(1-σ)/(1-σ)) := by
  let G := (range N).filter (fun n => n ≠ 0 ∧ Nat.maxPrimeFac n ≤ K)
  have hsub : (range N).filter (fun n => Nat.maxPrimeFac n ≤ K) ⊆ insert 0 G := by
    intro n hn
    by_cases hz : n=0
    · simp [hz]
    · exact mem_insert_of_mem (mem_filter.mpr ⟨(mem_filter.mp hn).1,hz,(mem_filter.mp hn).2⟩)
  have hc : ((range N).filter (fun n => Nat.maxPrimeFac n ≤ K)).card ≤ 1+G.card := by
    have hh := (card_le_card hsub).trans (card_insert_le 0 G)
    omega
  have hg : (G.card:ℝ) ≤ (N:ℝ)^σ*Real.exp ((K:ℝ)^(1-σ)/(1-σ)) :=
    (positive_smooth_count_bound hσ0 K N).trans
      (mul_le_mul_of_nonneg_left (product_bound (by linarith) hσ1 K) (Real.rpow_nonneg (Nat.cast_nonneg N) σ))
  have hc' : (((range N).filter (fun n => Nat.maxPrimeFac n ≤ K)).card:ℝ) ≤ 1+(G.card:ℝ) := by exact_mod_cast hc
  linarith

end Erdos371RankinSmoothCount

#print axioms Erdos371RankinSmoothCount.smooth_count_rankin_bound
