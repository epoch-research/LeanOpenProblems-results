import Submission.ConsecutiveRatioSubpower

/-!
A count of product-degenerate four-edge configurations with a prescribed
large shared endpoint label. This controls a nonbacktracking degeneracy
majorant, not the full signed prime-label moment. The nonzero product-
difference configurations are not estimated here.
-/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

def commonLargeEndpointPairs (B N u v : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 N) ×ˢ (Icc 1 N)).filter fun z =>
    B < Nat.maxPrimeFac (z.1+u) ∧
      Nat.maxPrimeFac (z.1+u)=Nat.maxPrimeFac (z.2+v)

lemma mem_commonLargeEndpointPairs (B N u v a b : ℕ) :
    (a,b) ∈ commonLargeEndpointPairs B N u v ↔
      a ∈ Icc 1 N ∧ b ∈ Icc 1 N ∧ B < Nat.maxPrimeFac (a+u) ∧
        Nat.maxPrimeFac (a+u)=Nat.maxPrimeFac (b+v) := by
  simp only [commonLargeEndpointPairs,mem_filter,mem_product]
  tauto

/-- Once the first edge is fixed, division by its shared label injects the
second edge into a short interval. No distributional assumption is used. -/
theorem commonLargeEndpointPairs_card_le (B N u v : ℕ) (hv : v ≤ 1) :
    (commonLargeEndpointPairs B N u v).card ≤ N*((N+1)/(B+1)+1) := by
  let K := (N+1)/(B+1)
  let f : ℕ × ℕ → ℕ × ℕ := fun z => (z.1,(z.2+v)/Nat.maxPrimeFac (z.1+u))
  have hc : (commonLargeEndpointPairs B N u v).card ≤
      ((Icc 1 N) ×ˢ range (K+1)).card := by
    apply card_le_card_of_injOn f
    · intro z hz
      obtain ⟨hzab,hp,he⟩ := mem_filter.mp hz
      obtain ⟨ha,hb⟩ := mem_product.mp hzab
      apply mem_product.mpr
      refine ⟨ha,mem_range.mpr ?_⟩
      have hpB : B+1 ≤ Nat.maxPrimeFac (z.1+u) := by omega
      have hnum : z.2+v ≤ N+1 := by have := (mem_Icc.mp hb).2; omega
      have hh := (Nat.div_le_div_right hnum).trans
        (Nat.div_le_div_left hpB (by omega) : (N+1)/Nat.maxPrimeFac (z.1+u) ≤ (N+1)/(B+1))
      change (z.2+v)/Nat.maxPrimeFac (z.1+u) < K+1
      omega
    · intro z hz w hw he
      dsimp only [f] at he
      have ha : z.1=w.1 := (Prod.mk.inj he).1
      have hq : (z.2+v)/Nat.maxPrimeFac (z.1+u)=
          (w.2+v)/Nat.maxPrimeFac (w.1+u) := (Prod.mk.inj he).2
      have hzd : Nat.maxPrimeFac (z.1+u) ∣ z.2+v := by
        rw [(mem_filter.mp hz).2.2]
        exact Nat.maxPrimeFac_dvd
      have hwd : Nat.maxPrimeFac (w.1+u) ∣ w.2+v := by
        rw [(mem_filter.mp hw).2.2]
        exact Nat.maxPrimeFac_dvd
      have hzm := Nat.mul_div_cancel' hzd
      have hwm := Nat.mul_div_cancel' hwd
      rw [ha] at hq hzm
      rw [hq,hwm] at hzm
      exact Prod.ext ha (by omega)
  simpa only [card_product,Nat.card_Icc,Nat.add_sub_cancel,card_range,K] using hc

noncomputable def endpointCompletionSum (B N u v : ℕ) (F : ℕ → ℕ → ℕ) : ℕ :=
  ∑ z ∈ commonLargeEndpointPairs B N u v, F z.1 z.2

lemma endpointCompletionSum_bound (B N u v : ℕ) (hv : v ≤ 1)
    (F : ℕ → ℕ → ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N, (F a b : ℝ) ≤ M) :
    (endpointCompletionSum B N u v F : ℝ) ≤
      M*(N : ℝ)*((N+1)/(B+1)+1 : ℕ) := by
  have hs : (endpointCompletionSum B N u v F : ℝ) ≤
      ((commonLargeEndpointPairs B N u v).card : ℝ)*M := by
    unfold endpointCompletionSum
    push_cast
    calc
      _ ≤ ∑ _ ∈ commonLargeEndpointPairs B N u v, M := by
        apply sum_le_sum
        intro z hz
        obtain ⟨hzab,_⟩ := mem_filter.mp hz
        obtain ⟨ha,hb⟩ := mem_product.mp hzab
        exact hF z.1 ha z.2 hb
      _ = _ := by simp
  have hc : ((commonLargeEndpointPairs B N u v).card : ℝ) ≤
      (N : ℝ)*((N+1)/(B+1)+1 : ℕ) := by
    exact_mod_cast commonLargeEndpointPairs_card_le B N u v hv
  exact hs.trans ((mul_le_mul_of_nonneg_right hc hM).trans_eq (by ring))

noncomputable def balancedEndpointDegeneracies (B N u v : ℕ) : ℕ :=
  endpointCompletionSum B N u v (fun a b => balancedFourCompletionCount a b N)

noncomputable def threeForwardEndpointDegeneracies (B N u v : ℕ) : ℕ :=
  endpointCompletionSum B N u v (fun a b => threeForwardCompletionCount a b N)

/-- The alternating immediate-backtracking case a=b is omitted, not assigned
the subpower fibre bound. Its unrestricted completion count is N. -/
noncomputable def alternatingEndpointDegeneracies (B N u v : ℕ) : ℕ :=
  endpointCompletionSum B N u v (fun a b =>
    if a=b then 0 else alternatingFourCompletionCount a b N)

/-- Uniform in the threshold B and both chosen endpoint offsets (v<=1).
The result counts all product-equality completions of a shared-label pair,
so extra prime-cycle closure conditions can only reduce the count. -/
theorem endpoint_degeneracies_uniform_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ B u v : ℕ, v ≤ 1 →
      (balancedEndpointDegeneracies B N u v : ℝ) ≤
        (N : ℝ)^ε*N*((N+1)/(B+1)+1 : ℕ) ∧
      (threeForwardEndpointDegeneracies B N u v : ℝ) ≤
        (N : ℝ)^ε*N*((N+1)/(B+1)+1 : ℕ) ∧
      (alternatingEndpointDegeneracies B N u v : ℝ) ≤
        (N : ℝ)^ε*N*((N+1)/(B+1)+1 : ℕ) := by
  filter_upwards [four_ratio_completion_uniform_subpower ε hε] with N hN
  intro B u v hv
  have hpow : 0 ≤ (N : ℝ)^ε := Real.rpow_nonneg (Nat.cast_nonneg N) ε
  refine ⟨?_,?_,?_⟩
  · exact endpointCompletionSum_bound B N u v hv _ _ hpow
      (fun a ha b hb => (hN a ha b hb).1)
  · exact endpointCompletionSum_bound B N u v hv _ _ hpow
      (fun a ha b hb => (hN a ha b hb).2.1)
  · apply endpointCompletionSum_bound B N u v hv _ _ hpow
    intro a ha b hb
    split_ifs with hab
    · simpa using hpow
    · exact (hN a ha b hb).2.2 hab

#print axioms commonLargeEndpointPairs_card_le
#print axioms endpoint_degeneracies_uniform_bound

lemma endpoint_degeneracy_budget_power_bound (N B : ℕ) (hN : 1 ≤ N)
    (β ε : ℝ) (hβ : β ≤ 1) (hB : (N : ℝ)^β ≤ B+1) :
    (N : ℝ)^ε*N*((N+1)/(B+1)+1 : ℕ) ≤ 3*(N : ℝ)^(2-β+ε) := by
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
  have hP : 0 < (N : ℝ)^β := Real.rpow_pos_of_pos hNr β
  have hdiv : (((N+1)/(B+1) : ℕ) : ℝ) ≤ 2*N/(N : ℝ)^β := by
    calc
      _ ≤ ((N+1 : ℕ) : ℝ)/(B+1 : ℕ) := Nat.cast_div_le
      _ ≤ (2*N : ℝ)/(B+1 : ℕ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        push_cast
        linarith
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left (by positivity) hP
        simpa only [Nat.cast_add,Nat.cast_one] using hB
  have he : (N : ℝ)^(2-β+ε)=(N : ℝ)^ε*N*N/(N : ℝ)^β := by
    calc
      _ = (N : ℝ)^(ε+2)/(N : ℝ)^β := by
        rw [← Real.rpow_sub hNr]
        congr 1
        ring
      _ = _ := by rw [Real.rpow_add hNr,Real.rpow_two]; ring
  have he1 : (N : ℝ)^(1+ε)=(N : ℝ)^ε*N := by
    rw [add_comm,Real.rpow_add hNr,Real.rpow_one]
  have hp : (N : ℝ)^(1+ε) ≤ (N : ℝ)^(2-β+ε) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  calc
    _ ≤ (N : ℝ)^ε*N*(2*N/(N : ℝ)^β+1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      push_cast
      linarith [hdiv]
    _ = 2*(N : ℝ)^(2-β+ε)+(N : ℝ)^(1+ε) := by rw [he,he1]; ring
    _ ≤ _ := by linarith

/-- A uniform N^(2-beta+epsilon) bound for the product-degenerate completion
majorants above a power-sized shared label. It does not bound the remaining
nondegenerate signed walks. -/
theorem endpoint_degeneracies_uniform_power_bound (β ε : ℝ)
    (hβ : β ≤ 1) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ B u v : ℕ, v ≤ 1 → (N : ℝ)^β ≤ B+1 →
      (balancedEndpointDegeneracies B N u v : ℝ) ≤ 3*(N : ℝ)^(2-β+ε) ∧
      (threeForwardEndpointDegeneracies B N u v : ℝ) ≤ 3*(N : ℝ)^(2-β+ε) ∧
      (alternatingEndpointDegeneracies B N u v : ℝ) ≤ 3*(N : ℝ)^(2-β+ε) := by
  filter_upwards [endpoint_degeneracies_uniform_bound ε hε,
    eventually_ge_atTop (1 : ℕ)] with N hbound hN
  intro B u v hv hB
  have hb := hbound B u v hv
  have hpow := endpoint_degeneracy_budget_power_bound N B hN β ε hβ hB
  exact ⟨hb.1.trans hpow,hb.2.1.trans hpow,hb.2.2.trans hpow⟩

#print axioms endpoint_degeneracies_uniform_power_bound

end Erdos371
