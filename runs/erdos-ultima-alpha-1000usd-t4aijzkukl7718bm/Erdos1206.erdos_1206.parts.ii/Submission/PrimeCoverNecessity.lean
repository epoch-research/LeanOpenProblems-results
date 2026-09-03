import Submission.WeightedDivisorCover

/-!
Necessary conditions for the divisor-closed and weighted-cover construction
routes. No prime cover is constructed, and the unrestricted conjecture is not
settled by these results.
-/

set_option maxHeartbeats 1000000

namespace Erdos1206
open Finset
open scoped Classical

/-- A set meeting every nontrivial collision with four prime roots. -/
def IsPrimeCubeCover (P : Set ℕ) : Prop :=
  ∀ a b c d : ℕ, Nat.Prime a → Nat.Prime b → Nat.Prime c → Nat.Prime d →
    a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3 → a ≠ c → a ≠ d →
    a ∈ P ∨ b ∈ P ∨ c ∈ P ∨ d ∈ P

lemma divisorWeight_prime {w : ℕ → ℝ} (h1 : w 1 = 0)
    {p : ℕ} (hp : Nat.Prime p) : divisorWeight w p = w p := by
  simp [divisorWeight, hp.divisors, hp.ne_one.symm, h1]

lemma prime_cover_of_weighted_cover {w : ℕ → ℝ} (h1 : w 1 = 0)
    (hc : IsWeightedCubeDivisorCover w) :
    IsPrimeCubeCover {p | Nat.Prime p ∧ 1 / 4 ≤ w p} := by
  intro a b c d ha hb hc' hd he hac had
  have hh := hc a b c d ha.pos hb.pos hc'.pos hd.pos he hac had
  rw [divisorWeight_prime h1 ha, divisorWeight_prime h1 hb,
    divisorWeight_prime h1 hc', divisorWeight_prime h1 hd] at hh
  by_contra hn
  simp only [Set.mem_setOf_eq, ha, hb, hc', hd, true_and, not_or] at hn
  rcases hn with ⟨h₁, h₂, h₃, h₄⟩
  push_neg at h₁ h₂ h₃ h₄
  linarith

lemma summable_heavy_primes {w : ℕ → ℝ} (hw : ∀ d, 0 ≤ w d)
    (hs : Summable (fun d : ℕ => w d / d)) :
    Summable (fun p : ℕ => if Nat.Prime p ∧ 1 / 4 ≤ w p then (1 : ℝ) / p else 0) := by
  apply Summable.of_nonneg_of_le (fun p => by split_ifs <;> positivity)
      (fun p => ?_) (hs.mul_left 4)
  by_cases hp : Nat.Prime p ∧ 1 / 4 ≤ w p
  · simp only [if_pos hp]
    have hh : (1 : ℝ) ≤ 4 * w p := by linarith [hp.2]
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right hh (Nat.cast_nonneg p)
  · simp only [if_neg hp]
    exact mul_nonneg (by norm_num) (div_nonneg (hw p) (Nat.cast_nonneg p))

lemma summable_prime_cover_of_weighted_cover {w : ℕ → ℝ}
    (hw : ∀ d, 0 ≤ w d) (h1 : w 1 = 0)
    (hs : Summable (fun d : ℕ => w d / d)) (hc : IsWeightedCubeDivisorCover w) :
    ∃ P : Set ℕ, (∀ p ∈ P, Nat.Prime p) ∧ IsPrimeCubeCover P ∧
      Summable (fun p : ℕ => if p ∈ P then (1 : ℝ) / p else 0) := by
  exact ⟨{p | Nat.Prime p ∧ 1 / 4 ≤ w p}, fun _ hp => hp.1,
    prime_cover_of_weighted_cover h1 hc,
    by
      apply (summable_heavy_primes hw hs).congr
      intro p
      by_cases hp : Nat.Prime p ∧ 1 / 4 ≤ w p <;> simp [hp]⟩

/-- Distinct excluded primes give disjoint dilations of a divisor-closed set. -/
lemma excluded_prime_dilations_injective {A : Set ℕ} (hA : PositiveDivisorClosed A)
    {p q a b : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpA : p ∉ A) (hb : b ∈ A) (he : p * a = q * b) : p = q ∧ a = b := by
  have hpd : p ∣ q * b := he ▸ dvd_mul_right p a
  have hpq : p = q := by
    rcases hp.dvd_mul.mp hpd with hh | hh
    · exact (Nat.prime_dvd_prime_iff_eq hp hq).mp hh
    · exact (hpA (hA b hb p hh hp.pos)).elim
  subst q
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hp.pos he⟩

lemma excluded_prime_dilations_count {A : Set ℕ} (hA : PositiveDivisorClosed A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ p ∉ A) (N : ℕ) :
    (∑ p ∈ P, ((range (N / p)).filter (· ∈ A)).card) ≤ N := by
  classical
  let F := P.sigma (fun p => (range (N / p)).filter (· ∈ A))
  have hinj : Set.InjOn (fun x : (Σ _ : ℕ, ℕ) => x.1 * x.2) (F : Set _) := by
    intro x hx y hy he
    obtain ⟨hxP, hxA⟩ := mem_sigma.mp hx
    obtain ⟨hyP, hyA⟩ := mem_sigma.mp hy
    obtain ⟨hpq, hab⟩ := excluded_prime_dilations_injective hA
      (hP x.1 hxP).1 (hP y.1 hyP).1 (hP x.1 hxP).2 (mem_filter.mp hyA).2 he
    cases x
    cases y
    simp only [Sigma.mk.inj_iff]
    exact ⟨hpq, heq_of_eq hab⟩
  have hmap : ∀ x ∈ F, x.1 * x.2 ∈ range N := by
    intro x hx
    obtain ⟨hxP, hxA⟩ := mem_sigma.mp hx
    have hxN := mem_range.mp (mem_filter.mp hxA).1
    exact mem_range.mpr ((Nat.mul_lt_mul_of_pos_left hxN (hP x.1 hxP).1.pos).trans_le
      (Nat.mul_div_le N x.1))
  have hh := card_le_card_of_injOn (s := F) (t := range N)
    (fun x : (Σ _ : ℕ, ℕ) => x.1 * x.2) (by exact hmap) hinj
  simpa [F, card_sigma] using hh

private lemma coefficient_le_of_nat_mul_bound {a b C : ℝ}
    (h : ∀ N : ℕ, a * N ≤ b * N + C) : a ≤ b := by
  by_contra hn
  have hab : 0 < a - b := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨N, hN⟩ := exists_nat_gt (C / (a - b))
  have hh := (div_lt_iff₀ hab).mp hN
  nlinarith [h N]

/-- A positive-density divisor-closed set can exclude only a harmonically
summable set of primes. No Sidon hypothesis is needed. -/
lemma summable_excluded_primes_of_divisorClosed {A : Set ℕ}
    (hA : PositiveDivisorClosed A) (hden : 0 < A.lowerDensity) :
    Summable (fun p : ℕ => if Nat.Prime p ∧ p ∉ A then (1 : ℝ) / p else 0) := by
  classical
  obtain ⟨δ, hδ, C, hpre⟩ := prefix_bound_of_positive_lowerDensity hden
  have hc (n : ℕ) : δ * n ≤ (((range n).filter (· ∈ A)).card : ℝ) + C := by
    have he : A ∩ Set.Iio n = ((range n).filter (· ∈ A) : Set ℕ) := by
      ext a
      simp [and_comm]
    simpa only [he, Set.ncard_coe_finset] using hpre n
  have hfinite (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ p ∉ A) :
      (∑ p ∈ P, (1 : ℝ) / p) ≤ 1 / δ := by
    have hb : δ * (∑ p ∈ P, (1 : ℝ) / p) ≤ 1 := by
      apply coefficient_le_of_nat_mul_bound (C := (P.card : ℝ) * (C + δ))
      intro N
      have hterm (p : ℕ) (hp : p ∈ P) :
          δ * N / p ≤ (((range (N / p)).filter (· ∈ A)).card : ℝ) + C + δ := by
        have hpR : (0 : ℝ) < p := by exact_mod_cast (hP p hp).1.pos
        have hf : (N : ℝ) < (p : ℝ) * ((N / p : ℕ) + 1) := by
          exact_mod_cast Nat.lt_mul_div_succ N (hP p hp).1.pos
        have hd : (N : ℝ) / p ≤ (N / p : ℕ) + 1 :=
          ((div_lt_iff₀ hpR).mpr (by nlinarith)).le
        have hm := mul_le_mul_of_nonneg_left hd hδ.le
        have hpref := hc (N / p)
        rw [← mul_div_assoc] at hm
        nlinarith
      have hsum := sum_le_sum hterm
      have hcount : (∑ p ∈ P, (((range (N / p)).filter (· ∈ A)).card : ℝ)) ≤ N := by
        exact_mod_cast excluded_prime_dilations_count hA P hP N
      have heq : (∑ p ∈ P, δ * N / p) = δ * (∑ p ∈ P, (1 : ℝ) / p) * N := by
        rw [mul_sum, sum_mul]
        apply sum_congr rfl
        intro p hp
        ring
      rw [heq] at hsum
      simp only [sum_add_distrib, sum_const, nsmul_eq_mul] at hsum
      nlinarith
    exact (le_div_iff₀ hδ).mpr (by nlinarith)
  apply summable_of_sum_range_le (c := 1 / δ)
  · intro p
    split_ifs <;> positivity
  · intro N
    rw [← sum_filter]
    exact hfinite _ (fun p hp => (mem_filter.mp hp).2)

lemma prime_cover_of_cube_sidon {A : Set ℕ}
    (hs : IsSidon ((fun n : ℕ => n ^ 3) '' A)) :
    IsPrimeCubeCover {p | Nat.Prime p ∧ p ∉ A} := by
  intro a b c d ha hb hc hd he hac had
  by_contra hn
  simp only [Set.mem_setOf_eq, ha, hb, hc, hd, true_and, not_or, not_not] at hn
  have hh := hs _ ⟨a, hn.1, rfl⟩ _ ⟨c, hn.2.2.1, rfl⟩
    _ ⟨b, hn.2.1, rfl⟩ _ ⟨d, hn.2.2.2, rfl⟩ he
  rcases hh with hh | hh
  · exact hac (Nat.pow_left_injective (by decide : 3 ≠ 0) hh.1)
  · exact had (Nat.pow_left_injective (by decide : 3 ≠ 0) hh.1)

lemma summable_prime_cover_of_divisorClosed_cube_sidon {A : Set ℕ}
    (hA : PositiveDivisorClosed A) (hden : 0 < A.lowerDensity)
    (hs : IsSidon ((fun n : ℕ => n ^ 3) '' A)) :
    ∃ P : Set ℕ, (∀ p ∈ P, Nat.Prime p) ∧ IsPrimeCubeCover P ∧
      Summable (fun p : ℕ => if p ∈ P then (1 : ℝ) / p else 0) := by
  exact ⟨{p | Nat.Prime p ∧ p ∉ A}, fun _ hp => hp.1,
    prime_cover_of_cube_sidon hs,
    by
      apply (summable_excluded_primes_of_divisorClosed hA hden).congr
      intro p
      by_cases hp : Nat.Prime p ∧ p ∉ A <;> simp [hp]⟩

#print axioms summable_prime_cover_of_weighted_cover
#print axioms summable_excluded_primes_of_divisorClosed
#print axioms summable_prime_cover_of_divisorClosed_cube_sidon

end Erdos1206
