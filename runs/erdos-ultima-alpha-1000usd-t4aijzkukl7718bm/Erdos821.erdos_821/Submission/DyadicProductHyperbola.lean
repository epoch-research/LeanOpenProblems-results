import Submission.DyadicProductRectangles
import Submission.DyadicHyperbolicPrimePairs

/-!
# The product-half-level sieve on a dyadic hyperbola

The additional bound H <= 2^(2*k) keeps the cofactor prefix below the
ambient scale on the prime-variable side.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

/-- The last hypothesis ensures that even the shortest cofactor prefix
in the rectangle cover is long enough for the progression mean. -/
theorem eventually_dyadic_product_hyperbolic_prime_pairs (a b t l r : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ b) (ht : b+1 ≤ t) (hlevel : 2*b+1 ≤ l+t) (hl : 2*a+1 ≤ l)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ c H : ℕ, 0 < c → H ≤ 2^(2*k) →
      cofactorScale l (2*cofactorDyadicIndex t (k+1)) ≤ H/2^(k+1) →
        ((hyperbolicPrimePairPool c H (2^k) (2^(k+1))).card : ℝ) ≤
          (2*(t : ℝ)/(b : ℝ))*(1+1/(2 : ℝ)^r)*(H : ℝ)*((c : ℝ)/(c.totient : ℝ))*
            dyadicMangoldtMass k/((k : ℝ)*Real.log 2)^2+
              η*(H : ℝ)/((k : ℝ)*Real.log 2)^2 := by
  let R : ℕ := 2^r
  let δ : ℝ := η/(2*(R : ℝ))
  have hR : 0 < R := by dsimp [R]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    (eventually_dyadic_product_prime_pair_rectangles a b t l ha hab ht hlevel hl δ hδ)
  filter_upwards [eventually_ge_atTop (max K (r+2))] with k hk
  intro c H hc hH hlong
  have hkr : r ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  let s : ℕ := 2^(k-r)
  let M : ℕ → ℕ := fun j => (R+j)*s
  let N : ℕ → ℕ := fun j => (R+j+1)*s
  let B : ℕ → ℕ := fun j => H/M j
  let S : ℝ := (k : ℝ)*Real.log 2
  let A : ℝ := 2*(t : ℝ)/(b : ℝ)
  let F : ℝ := (c : ℝ)/(c.totient : ℝ)
  have hs : 0 < s := by dsimp [s]; positivity
  have hS : 0 < S := by dsimp [S]; exact mul_pos (by exact_mod_cast (show 0<k by omega)) (Real.log_pos (by norm_num))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hRs : R*s=2^k := by
    dsimp [R,s]
    rw [← pow_add,Nat.add_sub_of_le hkr]
  have hRs2 : 2*R*s=2^(k+1) := by rw [mul_assoc,hRs,pow_succ]; ring
  have hM (j : ℕ) : 2^k ≤ M j := by
    rw [← hRs]
    exact Nat.mul_le_mul_right s (by omega)
  have hMN (j : ℕ) : M j ≤ N j := Nat.mul_le_mul_right s (by omega)
  have hN (j : ℕ) (hj : j ∈ range R) : N j ≤ 2^(k+1) := by
    rw [← hRs2]
    exact Nat.mul_le_mul_right s (by have := mem_range.mp hj; omega)
  have hMpos (j : ℕ) : 0 < M j := (Nat.pow_pos (by decide)).trans_le (hM j)
  have hlogM (j : ℕ) : S ≤ Real.log (M j : ℝ) := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ)<((2^k : ℕ) : ℝ)) (Nat.cast_le.mpr (hM j))
    simpa only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,S] using hh
  have hST : S ≤ ((k+1 : ℕ) : ℝ)*Real.log 2 := by
    dsimp [S]
    gcongr
    exact_mod_cast Nat.le_succ k
  have hS2 : S ≤ ((k+1 : ℕ) : ℝ)+1 := by
    have hl2 : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hh := mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg k)
    dsimp [S]
    push_cast
    linarith only [hh]
  have hpoint (j : ℕ) (hj : j ∈ range R) :
      ((cofactorPrimePairPool c 0 (B j) (M j) (N j)).card : ℝ) ≤
        A*(H : ℝ)*F/S^2*((mangoldtSum (N j)-mangoldtSum (M j))/(M j : ℝ))+
          2*δ*(H : ℝ)/S^2 := by
    have hshort : cofactorScale l (2*cofactorDyadicIndex t (k+1)) ≤ B j :=
      hlong.trans (Nat.div_le_div_left ((hMN j).trans (hN j hj)) (hMpos j))
    have hBup : B j ≤ 2^(k+1) := by
      calc
        B j ≤ H/2^k := Nat.div_le_div_left (hM j) (by positivity)
        _ ≤ 2^(2*k)/2^k := Nat.div_le_div_right hH
        _ = 2^k := by
          rw [show 2*k=k+k by omega,pow_add,Nat.mul_div_cancel _ (by positivity : 0 < (2 : ℕ)^k)]
        _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
    have hh := hK (k+1) (by omega) (B j) c (M j) (N j) hc
      (by simpa only [Nat.add_sub_cancel] using hM j) (hMN j) (hN j hj) hshort hBup
    have hV : 0 ≤ mangoldtSum (N j)-mangoldtSum (M j) := sub_nonneg.mpr
      (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl (hMN j)) (fun _ _ _ => vonMangoldt_nonneg))
    have hmR : (0 : ℝ)<M j := by exact_mod_cast hMpos j
    have hmain := rectangle_main_upper A (B j) (mangoldtSum (N j)-mangoldtSum (M j)) F H (M j) S
      (((k+1 : ℕ) : ℝ)*Real.log 2) (Real.log (M j)) hA (Nat.cast_nonneg _) hV hF (Nat.cast_nonneg _) hmR hS
      (Nat.cast_div_le (α := ℝ) (m := H) (n := M j)) hST (hlogM j)
    have herr := rectangle_error_upper δ (B j) H ((2^k : ℕ) : ℝ) (M j) S
      (((k+1 : ℕ) : ℝ)+1) (Real.log (M j)) hδ.le (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      hS (Nat.cast_le.mpr (hM j)) (by exact_mod_cast Nat.div_mul_le_self H (M j)) hS2 (hlogM j)
    apply hh.trans
    convert _root_.add_le_add hmain herr using 1
    simp only [Nat.cast_pow,Nat.cast_ofNat,pow_succ]
    ring
  have hcover := hyperbolic_prime_pair_card_le_sum (range R) c H (2^k) (2^(k+1)) M N B
    (fun j _ => hMpos j) (fun _ _ => le_rfl) (by
      intro q hq
      obtain ⟨j,hj,hqj⟩ := refined_interval_cover R s q hs (by simpa only [hRs,hRs2] using hq)
      exact ⟨j,hj,hqj⟩)
  have hreal := Nat.cast_le (α := ℝ).mpr hcover
  rw [Nat.cast_sum] at hreal
  apply (hreal.trans (sum_le_sum hpoint)).trans
  have hmass : (∑ j ∈ range R, (mangoldtSum (N j)-mangoldtSum (M j))/(M j : ℝ)) ≤
      (1+1/(R : ℝ))*dyadicMangoldtMass k := by
    have he (j : ℕ) : mangoldtSum (N j)-mangoldtSum (M j) =
        ∑ q ∈ Icc (M j+1) (N j), vonMangoldt q := (sum_natural_interval_sub _ _ _ (hMN j)).symm
    simp_rw [he]
    have hh := weighted_refined_interval_upper R s hR hs vonMangoldt (fun _ => vonMangoldt_nonneg)
    simpa only [M,N,hRs,hRs2,← dyadicMangoldtMass_eq_interval] using hh
  rw [sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul,card_range]
  have hmass' := mul_le_mul_of_nonneg_left hmass (show 0 ≤ A*(H : ℝ)*F/S^2 by positivity)
  apply (_root_.add_le_add hmass' le_rfl).trans_eq
  dsimp [A,F,S,δ,R]
  push_cast
  field_simp


end Erdos821.AnalyticSieve
