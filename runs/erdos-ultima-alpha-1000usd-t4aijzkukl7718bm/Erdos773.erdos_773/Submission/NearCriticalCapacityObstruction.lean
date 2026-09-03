import Submission.DenseGenericCapacityObstruction

/-!
Generic bounded-capacity obstructions arbitrarily close to square-root
ambient density. The values are not claimed to be squares, so this is NOT
a disproof of Erdős 773.
-/
namespace Erdos773.NearCriticalCapacityObstruction
open Finset Filter IntegerDifferenceCapacity
set_option maxHeartbeats 3000000
noncomputable section

/-- The capacity is fixed as n grows. By taking k large, the carrier exponent
approaches one half of the ambient exponent, while the Sidon exponent stays
at two fifths of the ambient exponent. -/
theorem polynomial_obstruction {n k : ℕ} (hn : 1000 ≤ n) (hk : 1≤k)
    (hlog : 5 ≤ Real.log (n:ℝ)) :
    ∃ B ⊆ Icc 1 (n^(100*k)), n^(50*k-1) ≤ 8*B.card ∧
      ThreeAPFree (B:Set ℕ) ∧ (∀ D, 0<D → (reps B D).card ≤ 25*k) ∧
      (∀ S ⊆ B, IsSidon (S:Set ℕ) → S.card<n^(40*k)) := by
  have hnk : n ≤ n^k := by
    simpa using Nat.pow_le_pow_right (by omega : 1≤n) hk
  have he : ((n^k:ℕ):ℝ)^50=(n:ℝ)^(2*(25*k)) := by
    push_cast
    rw [← pow_mul]
    congr 1
    omega
  obtain ⟨B,hB,hcard,hAP,hcap,hSid⟩ := DenseGenericCapacityObstruction.finite_obstruction
    hn (hn.trans hnk) (show 1≤25*k by omega) hlog he
  have hB' : B ⊆ Icc 1 (n^(100*k)) := by
    simpa only [← pow_mul, Nat.mul_comm k 100] using hB
  have hS' : ∀ S ⊆ B, IsSidon (S:Set ℕ) → S.card<n^(40*k) := by
    simpa only [← pow_mul, Nat.mul_comm k 40] using hSid
  refine ⟨B,hB',?_,hAP,hcap,hS'⟩
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hcR := (div_le_iff₀ (show (0:ℝ)<8*n by positivity)).mp hcard
  have hc : (n^k)^50 ≤ 8*n*B.card := by
    exact_mod_cast (show ((n^k:ℕ):ℝ)^50 ≤ 8*n*(B.card:ℝ) by nlinarith only [hcR])
  have heN : (n^k)^50=n^(50*k-1)*n := by
    rw [← pow_mul,show k*50=(50*k-1)+1 by omega,pow_succ]
  rw [heN] at hc
  apply Nat.le_of_mul_le_mul_right (c := n) _ (by omega)
  nlinarith only [hc]

/-- A uniform fixed-power loss relative to carrier size at each displayed
polynomial scale. This is an ordinary-integer, not a square-value, example. -/
theorem polynomial_power_gap {n k : ℕ} (hn : 1000 ≤ n) (hk : 1≤k)
    (hlog : 5 ≤ Real.log (n:ℝ)) :
    ∃ B ⊆ Icc 1 (n^(100*k)), n^(50*k-1) ≤ 8*B.card ∧
      ThreeAPFree (B:Set ℕ) ∧ (∀ D, 0<D → (reps B D).card ≤ 25*k) ∧
      B.maxSidonSubsetCard ≤ n^(40*k) ∧
      B.maxSidonSubsetCard^(50*k-1) ≤ 8^(40*k)*B.card^(40*k) := by
  obtain ⟨B,hB,hcard,hAP,hcap,hSid⟩ := polynomial_obstruction hn hk hlog
  have hmax : B.maxSidonSubsetCard ≤ n^(40*k) := by
    apply Finset.sup_le
    intro S hS
    obtain ⟨hSsub,hSidon⟩ := mem_filter.mp hS
    exact (hSid S (mem_powerset.mp hSsub) hSidon).le
  refine ⟨B,hB,hcard,hAP,hcap,hmax,?_⟩
  calc
    _ ≤ (n^(40*k))^(50*k-1) := Nat.pow_le_pow_left hmax _
    _ = (n^(50*k-1))^(40*k) := by rw [← pow_mul,← pow_mul, Nat.mul_comm (40*k)]
    _ ≤ (8*B.card)^(40*k) := Nat.pow_le_pow_left hcard _
    _ = _ := by rw [mul_pow]

/-- The examples exist at every sufficiently large parameter n. -/
theorem eventual_polynomial_obstruction (k : ℕ) (hk : 1≤k) :
    ∀ᶠ n : ℕ in atTop,
    ∃ B ⊆ Icc 1 (n^(100*k)), n^(50*k-1) ≤ 8*B.card ∧
      ThreeAPFree (B:Set ℕ) ∧ (∀ D, 0<D → (reps B D).card ≤ 25*k) ∧
      B.maxSidonSubsetCard ≤ n^(40*k) ∧
      B.maxSidonSubsetCard^(50*k-1) ≤ 8^(40*k)*B.card^(40*k) := by
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 5
  filter_upwards [eventually_ge_atTop 1000,hlog] with n hn hl
  exact polynomial_power_gap hn hk hl

lemma large_carrier {n k m : ℕ} (hn : 8≤n) (hk : 1≤k)
    (hc : n^(50*k-1) ≤ 8*m) : n^(50*k-2) ≤ m := by
  have he : n^(50*k-1)=n^(50*k-2)*n := by
    rw [show 50*k-1=(50*k-2)+1 by omega,pow_succ]
  rw [he] at hc
  apply Nat.le_of_mul_le_mul_right (c := 8) _ (by omega)
  simpa only [Nat.mul_comm m 8] using (Nat.mul_le_mul_left (n^(50*k-2)) hn).trans hc

lemma near_linear_scale {n k : ℕ} (hn : 1≤n) (hk : 1≤k) (ε : ℝ)
    (he : 2 ≤ (50:ℝ)*k*ε) :
    ((n^(50*k):ℕ):ℝ)^(1-ε) ≤ ((n^(50*k-2):ℕ):ℝ) := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith only [hnR]
  push_cast
  rw [← Real.rpow_natCast (n:ℝ) (50*k),← Real.rpow_mul hn0.le,
    ← Real.rpow_natCast (n:ℝ) (50*k-2)]
  apply Real.rpow_le_rpow_of_exponent_le hnR
  rw [Nat.cast_sub (by omega : 2≤50*k)]
  push_cast
  nlinarith only [he]

/-- For every density loss ε, a FIXED capacity g admits ordinary integer
carriers in [1,N²] of size at least N^(1-ε), at unbounded heights N, whose
Sidon maximum obeys M^5 ≤ N^4. The square-specific hypothesis is absent. -/
theorem near_critical_obstruction (ε : ℝ) (hε : 0<ε) :
    ∃ g : ℕ, 0<g ∧ ∀ᶠ n : ℕ in atTop,
      ∃ N ≥ n, ∃ B ⊆ Icc 1 (N^2), (N:ℝ)^(1-ε) ≤ B.card ∧
        ThreeAPFree (B:Set ℕ) ∧ (∀ D, 0<D → (reps B D).card ≤ g) ∧
        B.maxSidonSubsetCard^5 ≤ N^4 := by
  obtain ⟨k,hk⟩ := exists_nat_gt (max (1:ℝ) (2/(50*ε)))
  have hk1 : (1:ℝ)<k := (le_max_left _ _).trans_lt hk
  have hkN : 1≤k := by exact_mod_cast hk1.le
  have hkε : 2 ≤ (50:ℝ)*k*ε := by
    have hh := (div_lt_iff₀ (show (0:ℝ)<50*ε by positivity)).mp ((le_max_right _ _).trans_lt hk)
    nlinarith only [hh]
  refine ⟨25*k,by omega,?_⟩
  filter_upwards [eventual_polynomial_obstruction k hkN,eventually_ge_atTop 1000]
    with n hex hn
  obtain ⟨B,hB,hcard,hAP,hcap,hmax,_⟩ := hex
  let N := n^(50*k)
  have hNn : n≤N := by
    simpa [N] using Nat.pow_le_pow_right (by omega : 1≤n) (show 1≤50*k by omega)
  have hB' : B ⊆ Icc 1 (N^2) := by
    simpa only [N,← pow_mul,show 50*k*2=100*k by omega] using hB
  refine ⟨N,hNn,B,hB',?_,hAP,hcap,?_⟩
  · exact (near_linear_scale (by omega) hkN ε hkε).trans
      (by exact_mod_cast large_carrier (by omega : 8≤n) hkN hcard)
  · apply (Nat.pow_le_pow_left hmax 5).trans_eq
    dsimp [N]
    rw [← pow_mul,← pow_mul]
    congr 1
    omega

#print axioms polynomial_obstruction
#print axioms polynomial_power_gap
#print axioms eventual_polynomial_obstruction
#print axioms near_critical_obstruction
end
end Erdos773.NearCriticalCapacityObstruction
