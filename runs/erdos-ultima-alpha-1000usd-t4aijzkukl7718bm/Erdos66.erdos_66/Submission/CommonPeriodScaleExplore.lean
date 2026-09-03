import Submission.RepeatedPeriodBarrierExplore

/-! Refining the repeated-period restriction to a shared gcd. This concerns
full-period averaging of literal macroscopic repetitions, not arbitrary sets. -/
namespace Erdos66CommonPeriodScale
open Filter AdditiveCombinatorics Erdos66RepeatedPeriodBarrier Erdos66Explore
open scoped Topology Classical
set_option maxHeartbeats 2200000

lemma period_product_lower (N d e : ℕ) (x : ℝ)
    (hd : (N:ℝ) ≤ x*d) (he : (N:ℝ) ≤ x*e) :
    (N:ℝ)^2 ≤ x^2*(d:ℝ)*e := by
  have hmul := mul_le_mul hd he (Nat.cast_nonneg (α := ℝ) N)
    ((Nat.cast_nonneg (α := ℝ) N).trans hd)
  nlinarith only [hmul]

lemma period_product_identity (d e : ℕ) :
    (d:ℝ)*(e:ℝ)=(Nat.gcd d e:ℝ)*(Nat.lcm d e:ℝ) := by
  exact_mod_cast (Nat.gcd_mul_lcm d e).symm

/-- Even one full common period at scale N forces a large common divisor,
when each individual period has the usual logarithmic repetition bound. -/
lemma common_period_requires_gcd (N d e : ℕ) (hN : 0<N) (x B : ℝ)
    (hd : (N:ℝ) ≤ x*d) (he : (N:ℝ) ≤ x*e)
    (hlcm : (Nat.lcm d e:ℝ) ≤ B*N) :
    (N:ℝ) ≤ B*x^2*(Nat.gcd d e:ℝ) := by
  have hprod := period_product_lower N d e x hd he
  have hid := period_product_identity d e
  have hscale := mul_le_mul_of_nonneg_left hlcm
    (show 0 ≤ x^2*(Nat.gcd d e:ℝ) by positivity)
  have hprod' : (N:ℝ)^2 ≤ x^2*(Nat.gcd d e:ℝ)*(Nat.lcm d e:ℝ) := by
    calc
      _ ≤ x^2*(d:ℝ)*e := hprod
      _ = _ := by rw [mul_assoc, hid]; ring
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  apply (mul_le_mul_iff_right₀ hn).mp
  nlinarith only [hprod',hscale]

lemma scale_div_lcm_le (N d e : ℕ) (hN : 0<N) (hdp : 0<d) (hep : 0<e)
    (x : ℝ) (hd : (N:ℝ) ≤ x*d) (he : (N:ℝ) ≤ x*e) :
    (N:ℝ)/(Nat.lcm d e:ℝ) ≤ x^2*(Nat.gcd d e:ℝ)/(N:ℝ) := by
  have hlp : (0:ℝ)<(Nat.lcm d e:ℝ) := by
    exact_mod_cast Nat.lcm_pos hdp hep
  have hnp : (0:ℝ)<N := by exact_mod_cast hN
  apply (div_le_div_iff₀ hlp hnp).mpr
  have hprod := period_product_lower N d e x hd he
  have hid := period_product_identity d e
  calc
    (N:ℝ)*(N:ℝ) = (N:ℝ)^2 := by ring
    _ ≤ x^2*(d:ℝ)*e := hprod
    _ = x^2*(Nat.gcd d e:ℝ)*(Nat.lcm d e:ℝ) := by rw [mul_assoc,hid]; ring

/-- A witness with two fully repeated macroscopic patterns can average over
an O(N)-length common period only if their gcd is Omega(N/log(N)^2). -/
theorem witness_common_period_requires_gcd {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a d K b e L : ℕ, ∀ B : ℝ,
      0<d → N ≤ a → a ≤ 2*N → N ≤ d*(K+1) → d*(K+1) ≤ 2*N →
      (∀ j ≤ K, a+d*j ∈ A) →
      0<e → N ≤ b → b ≤ 2*N → N ≤ e*(L+1) → e*(L+1) ≤ 2*N →
      (∀ j ≤ L, b+e*j ∈ A) →
      (Nat.lcm d e:ℝ) ≤ B*N →
      (N:ℝ) ≤ B*(c+1)^2*(Real.log (6*(N:ℝ)))^2*(Nat.gcd d e:ℝ) := by
  obtain ⟨N₀,hbound⟩ := progression_period_bound h
  refine ⟨max N₀ 1,fun N hN a d K b e L B hd ha ha' hs hs' hA
    he hb hb' ht ht' hB hlcm ↦ ?_⟩
  have h₁ := hbound N (by omega) a d K hd ha ha' hs hs' hA
  have h₂ := hbound N (by omega) b e L he hb hb' ht ht' hB
  have hh := common_period_requires_gcd N d e (by omega)
    ((c+1)*Real.log (6*(N:ℝ))) B h₁ h₂ hlcm
  simpa only [mul_pow,mul_assoc] using hh

/-- A small shared gcd does not rescue the full-period averaging argument.
The hypothesis explicitly retains the growing gcd in the scale budget. -/
theorem scale_div_lcm_zero_of_small_gcd {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c))
    (N a d K b e L : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hdata : ∀ᶠ k : ℕ in atTop,
      0<d k ∧ N k ≤ a k ∧ a k ≤ 2*N k ∧
      N k ≤ d k*(K k+1) ∧ d k*(K k+1) ≤ 2*N k ∧
      (∀ j ≤ K k, a k+d k*j ∈ A) ∧
      0<e k ∧ N k ≤ b k ∧ b k ≤ 2*N k ∧
      N k ≤ e k*(L k+1) ∧ e k*(L k+1) ≤ 2*N k ∧
      (∀ j ≤ L k, b k+e k*j ∈ A))
    (hgcd : Tendsto (fun k ↦ (Nat.gcd (d k) (e k):ℝ)*
      (Real.log (6*(N k:ℝ)))^2/(N k:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun k ↦ (N k:ℝ)/(Nat.lcm (d k) (e k):ℝ)) atTop (𝓝 0) := by
  obtain ⟨N₀,hbound⟩ := progression_period_bound h
  have hupper := hgcd.const_mul ((c+1)^2)
  simp only [mul_zero] at hupper
  refine squeeze_zero' (Eventually.of_forall (fun k ↦ by positivity)) ?_ hupper
  filter_upwards [hdata,hN.eventually (eventually_ge_atTop (max N₀ 1))] with k hk hNk
  obtain ⟨hd,ha,ha',hs,hs',hA,he,hb,hb',ht,ht',hB⟩ := hk
  have h₁ := hbound (N k) (by omega) (a k) (d k) (K k) hd ha ha' hs hs' hA
  have h₂ := hbound (N k) (by omega) (b k) (e k) (L k) he hb hb' ht ht' hB
  have hh := scale_div_lcm_le (N k) (d k) (e k) (by omega) hd he
    ((c+1)*Real.log (6*(N k:ℝ))) h₁ h₂
  convert hh using 1 <;> ring

end Erdos66CommonPeriodScale
