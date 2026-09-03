import Submission.LayeredDigitProgramExplore
import Submission.AutomaticCoreExplore

/-! An asymptotic consequence of the digit-box bound. The state width
must satisfy S^2<b. This file does not assume or establish digit blocking. -/
namespace Erdos66LayeredDigitAsymptotic
open Filter AdditiveCombinatorics Erdos66Counting Erdos66AutomaticCore
  Erdos66LayeredDigitProgram
open scoped Topology Classical
set_option maxHeartbeats 2600000

lemma logarithmic_digit_cap {A : Set ℕ} {b : ℕ} (hb : 1 < b)
    {K C : ℝ} (hK : 0≤K) (hC : 0≤C)
    (hu : ∀ n, (sumRep A n : ℝ)≤K+C*Real.log ((n:ℝ)+2)) :
    ∃ L : ℕ, ∀ k n : ℕ, n<2*b^k → sumRep A n≤L*(k+1) := by
  obtain ⟨L,hL⟩ := exists_nat_gt (K+C*Real.log 4+C*Real.log (b:ℝ))
  refine ⟨L,fun k n hn ↦ ?_⟩
  have hb' : (1:ℝ)≤b := by exact_mod_cast (show 1≤b by omega)
  have hb0 : (0:ℝ)<b := by linarith
  have hpow : (1:ℝ)≤(b:ℝ)^k := one_le_pow₀ hb'
  have hn' : (n:ℝ)+2≤4*(b:ℝ)^k := by
    have he : (n:ℝ)<2*(b:ℝ)^k := by exact_mod_cast hn
    linarith
  have hlog : Real.log ((n:ℝ)+2)≤Real.log 4+(k:ℝ)*Real.log (b:ℝ) := by
    have he := Real.log_le_log (by positivity : (0:ℝ)<(n:ℝ)+2) hn'
    rwa [Real.log_mul (by norm_num) (pow_pos hb0 k).ne',Real.log_pow] at he
  have h0 : 0≤K+C*Real.log 4 := by positivity
  have h1 : 0≤C*Real.log (b:ℝ) := mul_nonneg hC (Real.log_nonneg hb')
  have he : (sumRep A n:ℝ)≤(L:ℝ)*((k:ℝ)+1) := by
    have hu' : (sumRep A n:ℝ)≤K+C*(Real.log 4+(k:ℝ)*Real.log (b:ℝ)) :=
      (hu n).trans (by linarith [mul_le_mul_of_nonneg_left hlog hC])
    have hL' : K+C*Real.log 4+C*Real.log (b:ℝ)≤(L:ℝ) := hL.le
    nlinarith [mul_le_mul_of_nonneg_right hL' (Nat.cast_nonneg (α := ℝ) k)]
  exact_mod_cast he

lemma shifted_poly_ratio (d : ℕ) {r : ℝ} (hr : 1<r) :
    Tendsto (fun k : ℕ ↦ ((k:ℝ)+2)^d/r^k) atTop (𝓝 0) := by
  have hs : Tendsto (fun k : ℕ ↦ k+2) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ by change k≤k+2; omega) tendsto_id
  have ht := ((tendsto_pow_const_div_const_pow_of_one_lt d hr).comp hs).mul_const (r^2)
  simp only [zero_mul] at ht
  apply ht.congr
  intro k
  simp only [Function.comp_def,Nat.cast_add,Nat.cast_ofNat,pow_add]
  field_simp

lemma poly_geometric_count_negligible {b S : ℕ} (hb : 1 < b)
    (hS : 0<S) (hwidth : S^2<b) (B : Set ℕ) (L : ℕ)
    (hcount : ∀ k, count B (b^k)≤S^(k+1)*(L*(k+1))^b) :
    Tendsto (fun N : ℕ ↦ (count B N : ℝ)^2/N) atTop (𝓝 0) := by
  have hs0 : (0:ℝ)<S := by exact_mod_cast hS
  have hb0 : (0:ℝ)<b := by exact_mod_cast (show 0<b by omega)
  have hr : (1:ℝ)<(b:ℝ)/(S:ℝ)^2 := by
    apply (one_lt_div (sq_pos_of_pos hs0)).mpr
    exact_mod_cast hwidth
  have ht := (shifted_poly_ratio (2*b) hr).const_mul ((S:ℝ)^4*(L:ℝ)^(2*b))
  simp only [mul_zero] at ht
  have heq (k : ℕ) :
      (S:ℝ)^4*(L:ℝ)^(2*b)*(((k:ℝ)+2)^(2*b)/((b:ℝ)/(S:ℝ)^2)^k)=
        ((S:ℝ)^(k+2)*((L:ℝ)*((k:ℝ)+2))^b)^2/(b:ℝ)^k := by
    rw [show 2*b=b*2 by omega]
    simp only [div_pow,mul_pow,pow_add,pow_mul]
    field_simp
    ring
  have ht' := (ht.congr heq).comp (nat_log_tendsto hb)
  apply squeeze_zero' (Eventually.of_forall (fun N ↦ by positivity)) ?_ ht'
  filter_upwards [eventually_ge_atTop 1] with N hN
  let k := Nat.log b N
  have hlow : b^k≤N := Nat.pow_log_le_self b (by omega)
  have hhigh : N≤b^(k+1) := (Nat.lt_pow_succ_log_self hb N).le
  have hmass : count B N≤S^(k+2)*(L*(k+2))^b := by
    simpa only [Nat.add_assoc] using (count_mono_cutoff B hhigh).trans (hcount (k+1))
  have hmass' : (count B N:ℝ)^2≤((S:ℝ)^(k+2)*((L:ℝ)*((k:ℝ)+2))^b)^2 := by
    exact_mod_cast Nat.pow_le_pow_left hmass 2
  change (count B N:ℝ)^2/(N:ℝ)≤
    ((S:ℝ)^(k+2)*((L:ℝ)*((k:ℝ)+2))^b)^2/(b:ℝ)^k
  exact div_le_div₀ (by positivity) hmass' (pow_pos hb0 k) (by exact_mod_cast hlow)

/-- Independent, position-dependent, nondeterministic programs may be used
at every length. Under S^2<b they recognize only square-root-negligible
subsets of a set with a logarithmic representation envelope. -/
theorem recognized_subset_sq_negligible {b : ℕ} {σ : Type*} [Fintype σ]
    (hb : 1 < b) (hwidth : (Fintype.card σ)^2<b)
    (P : (k : ℕ) → Program b k σ) (A B : Set ℕ)
    (hBA : B⊆A) (hrec : ∀ k, accepted (P k)=cutoff B (b^k))
    {K C : ℝ} (hK : 0≤K) (hC : 0≤C)
    (hu : ∀ n, (sumRep A n:ℝ)≤K+C*Real.log ((n:ℝ)+2)) :
    Tendsto (fun N : ℕ ↦ (count B N:ℝ)^2/N) atTop (𝓝 0) := by
  obtain ⟨L,hL⟩ := logarithmic_digit_cap hb hK hC hu
  have hs : 0<Fintype.card σ := Fintype.card_pos_iff.mpr ⟨(P 0).initial⟩
  apply poly_geometric_count_negligible hb hs hwidth B L
  intro k
  have hh := accepted_card_le hb (P k) A (by
    intro n hn
    rw [hrec] at hn
    exact hBA (mem_cutoff.mp hn).2) (L*(k+1)) (hL k)
  simpa only [hrec,count] using hh

/-- The relative counting consequence for a hypothetical witness. No
recognizability assumption on the whole witness is inferred. -/
theorem recognized_subset_negligible {b : ℕ} {σ : Type*} [Fintype σ]
    (hb : 1 < b) (hwidth : (Fintype.card σ)^2<b)
    (P : (k : ℕ) → Program b k σ) (A B : Set ℕ)
    (hBA : B⊆A) (hrec : ∀ k, accepted (P k)=cutoff B (b^k))
    (c : ℝ) (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun N ↦ (count B N:ℝ)/count A N) atTop (𝓝 0) := by
  obtain ⟨K,C,hK,hC,hu⟩ := global_log_upper_bound ht
  have hB := recognized_subset_sq_negligible hb hwidth P A B hBA hrec hK hC.le hu
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    ((Erdos66Explore.sumRep_tendsto_atTop hc ht).eventually_ge_atTop 1)
  exact negligible_relative_to_basis A B hB M hM

end Erdos66LayeredDigitAsymptotic
