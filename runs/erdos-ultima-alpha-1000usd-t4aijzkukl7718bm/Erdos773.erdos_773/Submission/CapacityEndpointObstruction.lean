import Submission.DenseGenericCapacityObstruction

/-! Ordinary-integer bounded-capacity obstructions at the exact alteration
exponent g/(2g+1) relative to ambient length. No value set here is asserted
to consist of squares. -/
namespace Erdos773.CapacityEndpointObstruction
open Finset Filter IntegerDifferenceCapacity
set_option maxHeartbeats 3000000
noncomputable section

theorem polynomial_obstruction {n g : ℕ} (hn : 1000≤n) (hg : 1≤g)
    (hlog : 5≤Real.log (n:ℝ)) :
    ∃ B ⊆ Icc 1 (n^(100*(2*g+1))), n^(100*g) ≤ 8*B.card ∧
      ThreeAPFree (B:Set ℕ) ∧ (∀ D, 0<D → (reps B D).card ≤ g) ∧
      (∀ S ⊆ B, IsSidon (S:Set ℕ) → S.card<n^(40*(2*g+1))) := by
  have hn1 : 1≤n := by omega
  have hn50 : n≤n^50 := by simpa using Nat.pow_le_pow_right hn1 (show 1≤50 by omega)
  have hnR : n≤n^(2*g+1) := by
    simpa using Nat.pow_le_pow_right hn1 (show 1≤2*g+1 by omega)
  have he : ((n^(2*g+1):ℕ):ℝ)^50=((n^50:ℕ):ℝ)^(2*g+1) := by
    push_cast
    rw [← pow_mul,← pow_mul,Nat.mul_comm (2*g+1)]
  have hlog50 : 5≤Real.log ((n^50:ℕ):ℝ) := by
    push_cast
    rw [Real.log_pow]
    norm_num
    linarith only [hlog]
  obtain ⟨B,hB,hcard,hAP,hcap,hSid⟩ :=
    DenseGenericCapacityObstruction.finite_endpoint_obstruction
      (hn.trans hn50) (hn.trans hnR) hg hlog50 he
  have hB' : B ⊆ Icc 1 (n^(100*(2*g+1))) := by
    simpa only [← pow_mul,Nat.mul_comm (2*g+1) 100] using hB
  have hSid' : ∀ S ⊆ B, IsSidon (S:Set ℕ) → S.card<n^(40*(2*g+1)) := by
    simpa only [← pow_mul,Nat.mul_comm (2*g+1) 40] using hSid
  refine ⟨B,hB',?_,hAP,hcap,hSid'⟩
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hcR := (div_le_iff₀ (show (0:ℝ)<8*(n^50:ℕ) by positivity)).mp hcard
  have hc : (n^(2*g+1))^50 ≤ (8*n^50)*B.card := by
    exact_mod_cast (show ((n^(2*g+1):ℕ):ℝ)^50 ≤ (8*(n^50:ℕ))*(B.card:ℝ) by
      nlinarith only [hcR])
  have hp : (n^(2*g+1))^50=n^(100*g)*n^50 := by
    rw [← pow_mul,← pow_add]
    congr 1
    omega
  rw [hp] at hc
  apply Nat.le_of_mul_le_mul_right (c := n^50) _ (by positivity)
  nlinarith only [hc]

/-- At arbitrarily large root-scale heights N, the cardinality has the exact
bounded-capacity exponent, while the Sidon maximum still satisfies M^5≤N^4.
For every fixed g≥3 this is a genuine fixed-power gap. -/
theorem eventual_endpoint_obstruction (g : ℕ) (hg : 1≤g) :
    ∀ᶠ n : ℕ in atTop,
    ∃ N ≥ n, ∃ B ⊆ Icc 1 (N^2), N^(2*g) ≤ 8^(2*g+1)*B.card^(2*g+1) ∧
      ThreeAPFree (B:Set ℕ) ∧ (∀ D, 0<D → (reps B D).card ≤ g) ∧
      B.maxSidonSubsetCard^5 ≤ N^4 := by
  have hlog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 5
  filter_upwards [eventually_ge_atTop 1000,hlog] with n hn hl
  obtain ⟨B,hB,hcard,hAP,hcap,hSid⟩ := polynomial_obstruction hn hg hl
  have hmax : B.maxSidonSubsetCard ≤ n^(40*(2*g+1)) := by
    apply Finset.sup_le
    intro S hS
    obtain ⟨hSsub,hSidon⟩ := mem_filter.mp hS
    exact (hSid S (mem_powerset.mp hSsub) hSidon).le
  let N := n^(50*(2*g+1))
  have hNn : n≤N := by
    simpa [N] using Nat.pow_le_pow_right (by omega : 1≤n)
      (show 1≤50*(2*g+1) by omega)
  have hB' : B ⊆ Icc 1 (N^2) := by
    simpa only [N,← pow_mul,show 50*(2*g+1)*2=100*(2*g+1) by omega] using hB
  refine ⟨N,hNn,B,hB',?_,hAP,hcap,?_⟩
  · have he : N^(2*g)=(n^(100*g))^(2*g+1) := by
      dsimp [N]
      rw [← pow_mul,← pow_mul]
      congr 1
      ring
    rw [he]
    exact (Nat.pow_le_pow_left hcard (2*g+1)).trans_eq (by rw [mul_pow])
  · apply (Nat.pow_le_pow_left hmax 5).trans_eq
    dsimp [N]
    rw [← pow_mul,← pow_mul]
    congr 1
    omega

#print axioms polynomial_obstruction
#print axioms eventual_endpoint_obstruction
end
end Erdos773.CapacityEndpointObstruction
