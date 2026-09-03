import Submission.RemainderPositiveMass
import Submission.PrimeReciprocalBands

/-! Lower bounds for the positive mass of the genuine signed Vaughan
remainder. No two-coordinate correlation estimate is claimed. -/
namespace Erdos972RemainderPositiveBudget

open Finset ArithmeticFunction
open Erdos972DoubleVaughan Erdos972RemainderPositiveMass
open Erdos972PrimeIntervalCounts Erdos972PrimeReciprocalBands

set_option maxHeartbeats 1000000

noncomputable def positiveMass (W N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, max (typeIIPart W W n) 0

lemma three_prime_product_inj {r s q r' s' q' W : ℕ}
    (hr : r.Prime) (_hs : s.Prime) (hq : q.Prime)
    (hr' : r'.Prime) (hs' : s'.Prime) (hq' : q'.Prime)
    (hrs : r < s) (hrs' : r' < s') (_hsW : s ≤ W) (hsW' : s' ≤ W)
    (hWq : W < q) (_hWq' : W < q') (he : r*s*q = r'*s'*q') :
    r = r' ∧ s = s' ∧ q = q' := by
  have hdq : q ∣ r'*s'*q' := he ▸ dvd_mul_left q (r*s)
  have hqe : q = q' := by
    rcases hq.dvd_mul.mp hdq with hd | hd
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have hh := Nat.le_of_dvd hr'.pos hd
        omega
      · have hh := Nat.le_of_dvd hs'.pos hd
        omega
    · exact ((Nat.dvd_prime hq').mp hd).resolve_left hq.ne_one
  have hprod : r*s = r'*s' := Nat.mul_right_cancel hq.pos (by simpa only [← hqe] using he)
  have hdr : r ∣ r'*s' := hprod ▸ dvd_mul_right r s
  have hre : r = r' := by
    rcases hr.dvd_mul.mp hdr with hd | hd
    · exact ((Nat.dvd_prime hr').mp hd).resolve_left hr.ne_one
    · have he₁ : r = s' := ((Nat.dvd_prime hs').mp hd).resolve_left hr.ne_one
      have he₂ : s = r' := Nat.mul_left_cancel hr.pos (by
        simpa only [← he₁, mul_comm r' r] using hprod)
      omega
  have hse : s = s' := Nat.mul_left_cancel hr.pos (by simpa only [← hre] using hprod)
  exact ⟨hre, hse, hqe⟩

noncomputable def cofactorBand (N : ℕ) (rs : ℕ×ℕ) : Finset ℕ :=
  primesBetween (N/(2*(rs.1*rs.2))) (2*(N/(2*(rs.1*rs.2))))

lemma cofactorBand_bounds {r s W B N : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hrW : r ≤ W) (hsW : s ≤ W) (hN : 4*W^2*max W B ≤ N) :
    max W B ≤ N/(2*(r*s)) ∧ (N : ℝ) ≤ 4*(r : ℝ)*s*(N/(2*(r*s)) : ℕ) := by
  have ht : 0 < r*s := Nat.mul_pos hr hs
  have hW : 0 < W := hr.trans_le hrW
  have htW : r*s ≤ W^2 := by simpa only [pow_two] using Nat.mul_le_mul hrW hsW
  have hQ : max W B ≤ N/(2*(r*s)) := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    have hh := Nat.mul_le_mul_left (2*max W B) htW
    nlinarith only [hh, hN]
  refine ⟨hQ, ?_⟩
  have hQ0 : 0 < N/(2*(r*s)) := hW.trans_le ((le_max_left W B).trans hQ)
  have hh := Nat.lt_mul_div_succ N (show 0 < 2*(r*s) by positivity)
  have hb : N ≤ 4*r*s*(N/(2*(r*s))) := by
    have hm := Nat.mul_le_mul_left (2*(r*s)) (show N/(2*(r*s))+1 ≤ 2*(N/(2*(r*s))) by omega)
    nlinarith only [hh, hm]
  exact_mod_cast hb

lemma cofactorBand_log_mass {r s W B N : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hrW : r ≤ W) (hsW : s ≤ W) (hN : 4*W^2*max W B ≤ N)
    (hθ : ∀ Q : ℕ, B ≤ Q → (Q : ℝ)/2 ≤ Chebyshev.theta (2*Q : ℕ)-Chebyshev.theta Q) :
    (N : ℝ)/(8*(r : ℝ)*s) ≤ ∑ q ∈ cofactorBand N (r,s), Real.log q := by
  obtain ⟨hQ, hcover⟩ := cofactorBand_bounds hr hs hrW hsW hN
  rw [cofactorBand, theta_interval_sum (by omega : N/(2*(r*s)) ≤ 2*(N/(2*(r*s))))]
  apply le_trans _ (hθ _ ((le_max_right W B).trans hQ))
  apply (div_le_iff₀ (show (0:ℝ) < 8*(r:ℝ)*s by positivity)).mpr
  nlinarith only [hcover]

/-- The contribution of an injectively parametrized family of positive
remainder values. Both reciprocal-prime factors remain explicit. -/
theorem positiveMass_lower {A C : Finset ℕ} {W B N : ℕ}
    (hA : ∀ r ∈ A, r.Prime ∧ r ≤ W) (hC : ∀ s ∈ C, s.Prime ∧ s ≤ W)
    (hsep : ∀ r ∈ A, ∀ s ∈ C, r < s)
    (hprod : ∀ r ∈ A, ∀ s ∈ C, W < r*s)
    (hN : 4*W^2*max W B ≤ N)
    (hθ : ∀ Q : ℕ, B ≤ Q → (Q : ℝ)/2 ≤ Chebyshev.theta (2*Q : ℕ)-Chebyshev.theta Q) :
    (N : ℝ)/8*(∑ r ∈ A, (1:ℝ)/r)*(∑ s ∈ C, (1:ℝ)/s) ≤ positiveMass W N := by
  classical
  let S := (A ×ˢ C).sigma (cofactorBand N)
  let f : (Σ _rs : ℕ×ℕ, ℕ) → ℕ := fun t => t.1.1*t.1.2*t.2
  have hmem {t : Σ _rs : ℕ×ℕ, ℕ} (ht : t ∈ S) :
      t.1.1 ∈ A ∧ t.1.2 ∈ C ∧ t.2.Prime ∧ W < t.2 ∧ f t ≤ N := by
    obtain ⟨hrs, hq⟩ := mem_sigma.mp ht
    obtain ⟨hr, hs⟩ := mem_product.mp hrs
    obtain ⟨hQq, hq2Q, hqp⟩ := mem_primesBetween.mp hq
    have hQr := (cofactorBand_bounds (hA _ hr).1.pos (hC _ hs).1.pos (hA _ hr).2 (hC _ hs).2 hN).1
    refine ⟨hr, hs, hqp, ((le_max_left W B).trans hQr).trans_lt hQq, ?_⟩
    have hh := Nat.mul_le_mul_left (t.1.1*t.1.2) hq2Q
    have hb := Nat.mul_div_le N (2*(t.1.1*t.1.2))
    dsimp only [f]
    nlinarith only [hh, hb]
  have hf : Set.InjOn f (↑S : Set (Σ _rs : ℕ×ℕ, ℕ)) := by
    intro x hx y hy hxy
    obtain ⟨hxr, hxs, hxq, hxWq, _⟩ := hmem hx
    obtain ⟨hyr, hys, hyq, hyWq, _⟩ := hmem hy
    obtain ⟨hr, hs, hq⟩ := three_prime_product_inj (hA _ hxr).1 (hC _ hxs).1 hxq
      (hA _ hyr).1 (hC _ hys).1 hyq (hsep _ hxr _ hxs) (hsep _ hyr _ hys)
      (hC _ hxs).2 (hC _ hys).2 hxWq hyWq hxy
    exact Sigma.ext (Prod.ext hr hs) (heq_of_eq hq)
  have hsub : S.image f ⊆ Ioc 0 N := by
    intro n hn
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hn
    obtain ⟨hr, hs, hq, _, hn⟩ := hmem ht
    exact mem_Ioc.mpr ⟨Nat.mul_pos (Nat.mul_pos (hA _ hr).1.pos (hC _ hs).1.pos) hq.pos, hn⟩
  have hval : ∀ t ∈ S, max (typeIIPart W W (f t)) 0 = Real.log t.2 := by
    intro t ht
    obtain ⟨hr, hs, hq, hWq, _⟩ := hmem ht
    rw [typeIIPart_three_primes (hA _ hr).1 (hC _ hs).1 hq (ne_of_lt (hsep _ hr _ hs))
      (hA _ hr).2 (hC _ hs).2 (hprod _ hr _ hs) hWq]
    exact max_eq_left (Real.log_natCast_nonneg _)
  calc
    _ = ∑ r ∈ A, ∑ s ∈ C, (N : ℝ)/(8*(r:ℝ)*s) := by
      simp only [mul_sum, sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro r hr
      apply sum_congr rfl
      intro s hs
      ring
    _ ≤ ∑ r ∈ A, ∑ s ∈ C, ∑ q ∈ cofactorBand N (r,s), Real.log q := by
      apply sum_le_sum
      intro r hr
      apply sum_le_sum
      intro s hs
      exact cofactorBand_log_mass (hA _ hr).1.pos (hC _ hs).1.pos (hA _ hr).2 (hC _ hs).2 hN hθ
    _ = ∑ t ∈ S, Real.log t.2 := by rw [sum_sigma, sum_product]
    _ = ∑ n ∈ S.image f, max (typeIIPart W W n) 0 := by
      rw [sum_image hf]
      exact sum_congr rfl (fun t ht => (hval t ht).symm)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => le_max_right _ _)

#print axioms positiveMass_lower

end Erdos972RemainderPositiveBudget
