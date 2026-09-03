import Submission.DampedPrimePairs

/-! The exact finite-degree expansion of the damping polynomial. -/
namespace Erdos371
open Finset

noncomputable def dampedCoefficient (k : ℕ) (c : ℕ → ℝ) (P : Finset ℕ) : ℝ :=
  -∑ E ∈ P.powersetCard k, subsetMinTerm c E

lemma dampedColour_degree_expansion (t : ℝ) (c : ℕ → ℝ) (P : Finset ℕ) :
    dampedColour t c P = ∑ k ∈ range (P.card+1), t^k*dampedCoefficient k c P := by
  unfold dampedColour dampedCoefficient
  rw [sum_powerset,← sum_neg_distrib]
  apply sum_congr rfl
  intro k hk
  rw [mul_neg, mul_sum]
  congr 1
  apply sum_congr rfl
  intro E hE
  rw [(mem_powersetCard.mp hE).2]

lemma dampedCoefficient_zero (c : ℕ → ℝ) (P : Finset ℕ) :
    dampedCoefficient 0 c P = 0 := by
  simp [dampedCoefficient,subsetMinTerm]

lemma dampedCoefficient_one (c : ℕ → ℝ) (P : Finset ℕ) :
    dampedCoefficient 1 c P = ∑ p ∈ P, c p := by
  simp [dampedCoefficient,powersetCard_one,subsetMinTerm]

lemma prime_side_sum (n : ℕ) (hn : 0 < n) :
    (∑ p ∈ (n*(n+1)).primeFactors, (if p ∣ n+1 then (1 : ℝ) else -1)) =
      ((n+1).primeFactors.card : ℝ) - n.primeFactors.card := by
  have hd : Disjoint n.primeFactors (n+1).primeFactors := by
    apply disjoint_left.mpr
    intro p hp hq
    exact (Nat.prime_of_mem_primeFactors hp).not_dvd_one
      ((Nat.dvd_add_iff_right (Nat.dvd_of_mem_primeFactors hp)).mpr
        (Nat.dvd_of_mem_primeFactors hq))
  rw [Nat.primeFactors_mul (by omega) (by omega),sum_union hd]
  have h1 (p : ℕ) (hp : p ∈ n.primeFactors) : ¬p ∣ n+1 := by
    intro h
    exact (Nat.prime_of_mem_primeFactors hp).not_dvd_one
      ((Nat.dvd_add_iff_right (Nat.dvd_of_mem_primeFactors hp)).mpr h)
  have h2 (p : ℕ) (hp : p ∈ (n+1).primeFactors) : p ∣ n+1 := Nat.dvd_of_mem_primeFactors hp
  rw [sum_congr rfl (fun p hp => if_neg (h1 p hp)),
    sum_congr rfl (fun p hp => if_pos (h2 p hp))]
  simp only [sum_const,nsmul_eq_mul,mul_neg_one,mul_one]
  ring

lemma dampedFactorSign_linear_coefficient (n : ℕ) (hn : 0 < n) :
    dampedCoefficient 1 (fun p => if p ∣ n+1 then 1 else -1) (n*(n+1)).primeFactors =
      ((n+1).primeFactors.card : ℝ) - n.primeFactors.card := by
  rw [dampedCoefficient_one,prime_side_sum n hn]

/-- The degree-one coefficient telescopes exactly. This alone supplies no
fixed-parameter cancellation for the full damping polynomial. -/
lemma dampedFactorSign_linear_prefix (N : ℕ) :
    (∑ n ∈ range N, dampedCoefficient 1 (fun p => if p ∣ n+2 then 1 else -1)
      ((n+1)*(n+2)).primeFactors) = ((N+1).primeFactors.card : ℝ) := by
  have he (n : ℕ) : dampedCoefficient 1 (fun p => if p ∣ n+2 then 1 else -1)
      ((n+1)*(n+2)).primeFactors = ((n+2).primeFactors.card : ℝ) - (n+1).primeFactors.card := by
    exact dampedFactorSign_linear_coefficient (n+1) (by omega)
  simp_rw [he]
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ,ih]; ring

lemma powersetCard_two_min_sum (c : ℕ → ℝ) (P : Finset ℕ) :
    (∑ E ∈ P.powersetCard 2, subsetMinTerm c E) =
      ∑ pq ∈ (P ×ˢ P).filter (fun pq => pq.1 < pq.2), c pq.1 := by
  symm
  apply sum_bij (fun pq _ => ({pq.1,pq.2} : Finset ℕ))
  · intro pq hpq
    obtain ⟨hm,hl⟩ := mem_filter.mp hpq
    obtain ⟨hp,hq⟩ := mem_product.mp hm
    apply mem_powersetCard.mpr
    exact ⟨by simp [insert_subset_iff,hp,hq],by simp [ne_of_lt hl]⟩
  · intro a ha b hb he
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    have ha1 : a.1 = b.1 ∨ a.1 = b.2 := by
      have hh : a.1 ∈ ({b.1,b.2} : Finset ℕ) := he ▸ mem_insert_self _ _
      simpa only [mem_insert,mem_singleton] using hh
    have ha2 : a.2 = b.1 ∨ a.2 = b.2 := by
      have hh : a.2 ∈ ({b.1,b.2} : Finset ℕ) := he ▸ mem_insert_of_mem (mem_singleton_self _)
      simpa only [mem_insert,mem_singleton] using hh
    apply Prod.ext <;> omega
  · intro E hE
    obtain ⟨hEP,hcard⟩ := mem_powersetCard.mp hE
    obtain ⟨a,b,hab,he⟩ := card_eq_two.mp hcard
    have ha : a ∈ P := hEP (he ▸ mem_insert_self _ _)
    have hb : b ∈ P := hEP (he ▸ mem_insert_of_mem (mem_singleton_self _))
    rcases lt_or_gt_of_ne hab with hab | hab
    · exact ⟨(a,b),mem_filter.mpr ⟨mem_product.mpr ⟨ha,hb⟩,hab⟩,he.symm⟩
    · exact ⟨(b,a),mem_filter.mpr ⟨mem_product.mpr ⟨hb,ha⟩,hab⟩,by simp only [he,pair_comm]⟩
  · intro pq hpq
    have hl := (mem_filter.mp hpq).2
    simp [subsetMinTerm,ne_of_lt hl,min_eq_left hl.le]

lemma dampedCoefficient_two (c : ℕ → ℝ) (P : Finset ℕ) :
    dampedCoefficient 2 c P =
      -∑ pq ∈ (P ×ˢ P).filter (fun pq => pq.1 < pq.2), c pq.1 := by
  rw [dampedCoefficient,powersetCard_two_min_sum]

#print axioms dampedColour_degree_expansion
#print axioms dampedFactorSign_linear_prefix
end Erdos371
