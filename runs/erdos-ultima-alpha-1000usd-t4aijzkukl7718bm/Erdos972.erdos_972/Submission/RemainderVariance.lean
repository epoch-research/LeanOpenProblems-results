import Submission.RemainderSemiprimes
import Submission.PrimeIntervalCounts

/-! A lower variance estimate from a rectangular family of rough semiprimes.
The estimate is for the actual signed Vaughan remainder. -/
namespace Erdos972RemainderVariance

open Finset ArithmeticFunction
open Erdos972RemainderSemiprimes Erdos972PrimeIntervalCounts
open Erdos972DoubleVaughan Erdos972LogarithmicCovariance

set_option maxHeartbeats 1000000

lemma semiprime_rectangle_injective {W Q : ℕ} (hsep : 2*W < Q) :
    Set.InjOn (fun pq : ℕ×ℕ => pq.1*pq.2)
      (↑(primesBetween W (2*W) ×ˢ primesBetween Q (2*Q)) : Set (ℕ×ℕ)) := by
  intro x hx y hy hxy
  obtain ⟨hx₁, hx₂⟩ := mem_product.mp hx
  obtain ⟨hy₁, hy₂⟩ := mem_product.mp hy
  obtain ⟨hxp, hxpW, hxPrime⟩ := mem_primesBetween.mp hx₁
  obtain ⟨hxq, hxqQ, hxqPrime⟩ := mem_primesBetween.mp hx₂
  obtain ⟨hyp, hypW, hyPrime⟩ := mem_primesBetween.mp hy₁
  obtain ⟨hyq, hyqQ, hyqPrime⟩ := mem_primesBetween.mp hy₂
  change x.1*x.2 = y.1*y.2 at hxy
  have hd : x.1 ∣ y.1*y.2 := hxy ▸ dvd_mul_right x.1 x.2
  have hfirst : x.1 = y.1 := by
    rcases hxPrime.dvd_mul.mp hd with hh | hh
    · exact (Nat.dvd_prime hyPrime).mp hh |>.resolve_left hxPrime.ne_one
    · have he : x.1 = y.2 := (Nat.dvd_prime hyqPrime).mp hh |>.resolve_left hxPrime.ne_one
      omega
  have hsecond : x.2 = y.2 := Nat.mul_left_cancel hxPrime.pos (by simpa only [← hfirst] using hxy)
  exact Prod.ext hfirst hsecond

/-- One dyadic band of small prime factors already forces a variance of
order N log N / log W. Both value clusters are counted without any assertion
about a two-prime Beatty correlation. -/
theorem remainder_variance_lower {N W Q : ℕ} (hW : 0 < W) (hN : 0 < N)
    (hsep : 2*W < Q) (hprod : 4*W*Q ≤ N) (hcover : N ≤ 8*W*Q)
    (hlogW : 1 ≤ Real.log (2*W : ℕ)) (hlogN : 2*Real.log 8 ≤ Real.log N)
    (hcountN : (N : ℝ)/(2*Real.log N) ≤ (primesBetween 0 N).card)
    (hcountW : (W : ℝ)/(2*Real.log (2*W : ℕ)) ≤ (primesBetween W (2*W)).card)
    (hcountQ : (Q : ℝ)/(2*Real.log (2*Q : ℕ)) ≤ (primesBetween Q (2*Q)).card) :
    (N : ℝ)*Real.log N/(512*Real.log (2*W : ℕ)) ≤
      covariance N (fun n => typeIIPart W W n) (fun n => typeIIPart W W n) := by
  classical
  have hQ : 0 < Q := (Nat.zero_le (2*W)).trans_lt hsep
  have hQ2 : 1 < 2*Q := by omega
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hlogW0 : 0 < Real.log (2*W : ℕ) := by linarith only [hlogW]
  have hlogN0 : 0 < Real.log N := (show 0 < 2*Real.log 8 by positivity).trans_le hlogN
  have hlogQ0 : 0 < Real.log (2*Q : ℕ) := Real.log_pos (by exact_mod_cast hQ2)
  have hQN : 2*Q ≤ N := (show 2*Q ≤ 4*W*Q by nlinarith).trans hprod
  have hlogQN : Real.log (2*Q : ℕ) ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast (show 0 < 2*Q by omega)) (Nat.cast_le.mpr hQN)
  let P := primesBetween 0 N
  let A := primesBetween W (2*W)
  let B := primesBetween Q (2*Q)
  let S := (A ×ˢ B).image (fun pq : ℕ×ℕ => pq.1*pq.2)
  let m : ℝ := (N : ℝ)/(32*Real.log (2*W : ℕ)*Real.log N)
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hPcard : m ≤ (P.card : ℝ) := by
    apply le_trans _ hcountN
    dsimp [m]
    apply div_le_div_of_nonneg_left hNR.le (by positivity : 0 < 2*Real.log N)
    nlinarith only [mul_le_mul_of_nonneg_right hlogW hlogN0.le, hlogN0]
  have hScard : m ≤ (S.card : ℝ) := by
    have hcard : S.card = A.card*B.card := by
      dsimp only [S]
      rw [card_image_of_injOn (semiprime_rectangle_injective hsep), card_product]
    rw [hcard, Nat.cast_mul]
    apply (div_le_iff₀ (show 0 < 32*Real.log (2*W : ℕ)*Real.log N by positivity)).mpr
    have ha : (W : ℝ) ≤ (A.card : ℝ)*(2*Real.log (2*W : ℕ)) :=
      (div_le_iff₀ (by positivity)).mp hcountW
    have hb₀ : (Q : ℝ) ≤ (B.card : ℝ)*(2*Real.log (2*Q : ℕ)) :=
      (div_le_iff₀ (by positivity)).mp hcountQ
    have hb : (Q : ℝ) ≤ (B.card : ℝ)*(2*Real.log N) :=
      hb₀.trans (mul_le_mul_of_nonneg_left (by linarith only [hlogQN]) (Nat.cast_nonneg _))
    have hh := mul_le_mul ha hb (Nat.cast_nonneg Q) (by positivity : 0 ≤ (A.card : ℝ)*(2*Real.log (2*W : ℕ)))
    have hc : (N : ℝ) ≤ 8*(W : ℝ)*Q := by exact_mod_cast hcover
    nlinarith only [hh, hc]
  have hPN : P ⊆ Ioc 0 N := by
    intro n hn
    exact (mem_filter.mp hn).1
  have hSN : S ⊆ Ioc 0 N := by
    intro n hn
    obtain ⟨pq, hpq, rfl⟩ := mem_image.mp hn
    obtain ⟨hp, hq⟩ := mem_product.mp hpq
    obtain ⟨hpW, hp2W, hpPrime⟩ := mem_primesBetween.mp hp
    obtain ⟨hqQ, hq2Q, hqPrime⟩ := mem_primesBetween.mp hq
    refine mem_Ioc.mpr ⟨Nat.mul_pos hpPrime.pos hqPrime.pos, ?_⟩
    have hh := Nat.mul_le_mul hp2W hq2Q
    nlinarith only [hh, hprod]
  have hPval : ∀ n ∈ P, typeIIPart W W n = 0 := by
    intro n hn
    exact typeIIPart_prime hW hW (mem_primesBetween.mp hn).2.2
  have hSval : ∀ n ∈ S, typeIIPart W W n ≤ -(Real.log N/2) := by
    intro n hn
    obtain ⟨pq, hpq, rfl⟩ := mem_image.mp hn
    obtain ⟨hp, hq⟩ := mem_product.mp hpq
    obtain ⟨hpW, hp2W, hpPrime⟩ := mem_primesBetween.mp hp
    obtain ⟨hqQ, hq2Q, hqPrime⟩ := mem_primesBetween.mp hq
    have hWq : W < pq.2 := by omega
    have hpqne : pq.1 ≠ pq.2 := by omega
    rw [typeIIPart_rough_semiprime hpPrime hqPrime hpqne hW hpW hWq hpW hWq]
    have hnR : (0 : ℝ) < (pq.1*pq.2 : ℕ) := by exact_mod_cast Nat.mul_pos hpPrime.pos hqPrime.pos
    have hlow : N ≤ 8*(pq.1*pq.2) := by
      have hh := Nat.mul_le_mul hpW.le hqQ.le
      nlinarith only [hh, hcover]
    have hh := Real.log_le_log hNR (show (N : ℝ) ≤ 8*(pq.1*pq.2 : ℕ) by exact_mod_cast hlow)
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hnR.ne'] at hh
    linarith only [hh, hlogN]
  have hh := covariance_self_two_clusters hN (fun n => typeIIPart W W n) P S hPN hSN
    (L := Real.log N/2) (by positivity) hm hPcard hScard hPval hSval
  calc
    _ = m*(Real.log N/2)^2/4 := by dsimp [m]; field_simp; ring
    _ ≤ _ := hh

#print axioms remainder_variance_lower

end Erdos972RemainderVariance
