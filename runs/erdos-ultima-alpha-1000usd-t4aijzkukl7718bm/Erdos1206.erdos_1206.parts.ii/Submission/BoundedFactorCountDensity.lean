import Submission.Compactness

/-! Positive lower density forces unbounded numbers of distinct prime factors.
The proof uses bounded multiplicity of prime dilations and divergence of the
prime reciprocal series. No assertion about cubic collisions is made here. -/
namespace Erdos1206.BoundedFactorCountDensity
open Finset
open scoped Classical

lemma prime_dilations_count {A : Set ℕ} {K : ℕ}
    (hpos : ∀ n ∈ A, 0 < n) (hcount : ∀ n ∈ A, n.primeFactors.card ≤ K)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    (∑ p ∈ P, ((range (N/p)).filter (· ∈ A)).card) ≤ (K+1)*N := by
  let F := P.sigma (fun p => (range (N/p)).filter (· ∈ A))
  let f : (Σ _ : ℕ, ℕ) → ℕ := fun x => x.1*x.2
  have hmap : ∀ x ∈ F, f x ∈ range N := by
    intro x hx
    obtain ⟨hp, ha⟩ := mem_sigma.mp hx
    have hxN := mem_range.mp (mem_filter.mp ha).1
    exact mem_range.mpr ((Nat.mul_lt_mul_of_pos_left hxN (hP x.1 hp).pos).trans_le
      (Nat.mul_div_le N x.1))
  have hfiber (n : ℕ) (_hn : n ∈ range N) : (F.filter (fun x => f x=n)).card ≤ K+1 := by
    by_cases he : (F.filter (fun x => f x=n)).Nonempty
    · obtain ⟨x, hx⟩ := he
      obtain ⟨hxF, hxn⟩ := mem_filter.mp hx
      obtain ⟨hxp, hxa⟩ := mem_sigma.mp hxF
      have hxaA := (mem_filter.mp hxa).2
      have hxpP := hP x.1 hxp
      have hx0 := hpos x.2 hxaA
      have hn0 : n ≠ 0 := by
        rw [←hxn]
        exact Nat.ne_of_gt (Nat.mul_pos hxpP.pos hx0)
      have hncount : n.primeFactors.card ≤ K+1 := by
        rw [←hxn]
        change (x.1*x.2).primeFactors.card ≤ _
        rw [Nat.primeFactors_mul hxpP.ne_zero hx0.ne']
        have hh := card_union_le x.1.primeFactors x.2.primeFactors
        rw [hxpP.primeFactors, card_singleton] at hh
        rw [hxpP.primeFactors]
        have hc := hcount x.2 hxaA
        omega
      have hi : (F.filter (fun x => f x=n)).card ≤ n.primeFactors.card := by
        apply card_le_card_of_injOn (fun z : (Σ _ : ℕ, ℕ) => z.1)
        · intro z hz
          obtain ⟨hzF, hzn⟩ := mem_filter.mp hz
          obtain ⟨hzp, _⟩ := mem_sigma.mp hzF
          apply Nat.mem_primeFactors.mpr
          refine ⟨hP z.1 hzp, ?_, hn0⟩
          rw [←hzn]
          exact dvd_mul_right z.1 z.2
        · intro z hz w hw heq
          obtain ⟨hzF, hzn⟩ := mem_filter.mp hz
          obtain ⟨hwF, hwn⟩ := mem_filter.mp hw
          change z.1 = w.1 at heq
          have hp := (hP z.1 (mem_sigma.mp hzF).1).pos
          have hh : z.1*z.2 = z.1*w.2 := by
            change z.1*z.2=n at hzn
            change w.1*w.2=n at hwn
            rw [←heq] at hwn
            exact hzn.trans hwn.symm
          have ha := Nat.eq_of_mul_eq_mul_left hp hh
          cases z
          cases w
          simp only [Sigma.mk.inj_iff]
          exact ⟨heq, heq_of_eq ha⟩
      exact hi.trans hncount
    · simp only [not_nonempty_iff_eq_empty] at he
      simp [he]
  have hh := card_le_mul_card_image_of_maps_to hmap (K+1) hfiber
  simpa only [F, card_sigma, card_range] using hh

private lemma coefficient_le {a b C : ℝ}
    (h : ∀ N : ℕ, a*N ≤ b*N+C) : a ≤ b := by
  by_contra hn
  have hab : 0 < a-b := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨N,hN⟩ := exists_nat_gt (C/(a-b))
  have hh := (div_lt_iff₀ hab).mp hN
  nlinarith [h N]

/-- A positive-lower-density set of positive integers cannot have a uniform
bound on the number of distinct prime factors. -/
theorem exists_large_count {A : Set ℕ} (hpos : ∀ n ∈ A, 0 < n)
    (hden : 0 < A.lowerDensity) (K : ℕ) :
    ∃ n ∈ A, K < n.primeFactors.card := by
  by_contra hh
  push_neg at hh
  obtain ⟨δ,hδ,C,hpre⟩ := Erdos1206.prefix_bound_of_positive_lowerDensity hden
  have hc (n : ℕ) : δ*n ≤ (((range n).filter (· ∈ A)).card : ℝ)+C := by
    have he : A ∩ Set.Iio n = ((range n).filter (· ∈ A) : Set ℕ) := by
      ext a
      simp [and_comm]
    simpa only [he, Set.ncard_coe_finset] using hpre n
  have hfinite (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
      (∑ p ∈ P, (1:ℝ)/p) ≤ (K+1)/δ := by
    have hb : δ*(∑ p ∈ P, (1:ℝ)/p) ≤ K+1 := by
      apply coefficient_le (C := (P.card:ℝ)*(C+δ))
      intro N
      have hterm (p : ℕ) (hp : p ∈ P) :
          δ*N/p ≤ (((range (N/p)).filter (· ∈ A)).card : ℝ)+C+δ := by
        have hpR : (0:ℝ) < p := by exact_mod_cast (hP p hp).pos
        have hf : (N:ℝ) < (p:ℝ)*((N/p:ℕ)+1) := by
          exact_mod_cast Nat.lt_mul_div_succ N (hP p hp).pos
        have hd : (N:ℝ)/p ≤ (N/p:ℕ)+1 :=
          ((div_lt_iff₀ hpR).mpr (by nlinarith)).le
        have hm := mul_le_mul_of_nonneg_left hd hδ.le
        have hpref := hc (N/p)
        rw [←mul_div_assoc] at hm
        nlinarith
      have hsum := sum_le_sum hterm
      have hd : (∑ p ∈ P, (((range (N/p)).filter (· ∈ A)).card : ℝ)) ≤ (K+1)*N := by
        exact_mod_cast prime_dilations_count hpos hh P hP N
      have he : (∑ p ∈ P, δ*N/p) = δ*(∑ p ∈ P, (1:ℝ)/p)*N := by
        rw [mul_sum, sum_mul]
        apply sum_congr rfl
        intro p hp
        ring
      rw [he] at hsum
      simp only [sum_add_distrib, sum_const, nsmul_eq_mul] at hsum
      nlinarith
    exact (le_div_iff₀ hδ).mpr (by nlinarith)
  apply not_summable_one_div_on_primes
  have hs : Summable (fun p : ℕ => if p.Prime then (1:ℝ)/p else 0) := by
    apply summable_of_sum_range_le (c := (K+1)/δ)
    · intro p
      split_ifs <;> positivity
    · intro N
      rw [←sum_filter]
      exact hfinite _ (fun p hp => (mem_filter.mp hp).2)
  apply hs.congr
  intro p
  by_cases hp : p.Prime <;> simp [hp]

#print axioms exists_large_count
end Erdos1206.BoundedFactorCountDensity
