import Submission.Hypergraph

/-!
Weighted sampling with a prescribed cardinality. This is a finite averaging
lemma, proved by deleting one vertex at a time and using Bernoulli's inequality.
It does not assert that any selected hypergraph is independent.
-/
namespace Erdos773.FixedCardinalitySampling
open Finset
set_option maxHeartbeats 1000000
variable {α : Type*} [DecidableEq α]

/-- The survival probability after one uniformly averaged deletion is at
most the corresponding independent-sampling power. -/
lemma one_step_power (n k r : ℕ) (hn : 2 ≤ n) (hr : r ≤ n) :
    ((n-r:ℕ):ℝ)*((k:ℝ)/(n-1:ℕ))^r ≤ (n:ℝ)*((k:ℝ)/n)^r := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hn1 : (0:ℝ) < n-1 := by linarith
  have hi : (1:ℝ)/n ≤ 1 := (div_le_one hn0).mpr (by linarith)
  have hB := one_add_mul_le_pow (show (-2:ℝ) ≤ -(1/(n:ℝ)) by linarith) r
  have hfactor : (n:ℝ)-r ≤ (n:ℝ)*(1-1/(n:ℝ))^r := by
    have hh := mul_le_mul_of_nonneg_left hB hn0.le
    have he : (n:ℝ)*(1+(r:ℝ)*(-1/(n:ℝ)))=(n:ℝ)-r := by field_simp; ring
    rw [show -(1/(n:ℝ)) = -1/(n:ℝ) by ring,he] at hh
    convert hh using 1
    ring
  have hq : 0 ≤ ((k:ℝ)/(n-1))^r := by positivity
  have hh := mul_le_mul_of_nonneg_right hfactor hq
  have he : ((k:ℝ)/(n-1))*(1-1/(n:ℝ))=(k:ℝ)/n := by field_simp
  rw [Nat.cast_sub hr,Nat.cast_sub (show 1 ≤ n by omega),Nat.cast_one]
  calc
    _ ≤ (n:ℝ)*(1-1/(n:ℝ))^r*((k:ℝ)/(n-1))^r := hh
    _ = (n:ℝ)*(((k:ℝ)/(n-1))*(1-1/(n:ℝ)))^r := by rw [mul_pow]; ring
    _ = _ := by rw [he]

/-- Sum over all one-vertex deletions, counting each edge by its surviving
vertices. The weights may depend arbitrarily on the edges. -/
lemma deletion_sum (A : Finset α) (H : Finset (Finset α))
    (hsub : ∀ e ∈ H, e ⊆ A) (W : Finset α → ℝ) :
    (∑ a ∈ A, ∑ e ∈ H.filter (fun e => a ∉ e), W e) =
      ∑ e ∈ H, ((A.card-e.card:ℕ):ℝ)*W e := by
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  have hf : A.filter (fun a => a ∉ e) = A\e := by ext a; simp
  rw [← sum_filter,hf]
  simp only [sum_const,nsmul_eq_mul,card_sdiff_of_subset (hsub e he)]

/-- For nonnegative edge weights, an actual k-element subset has weighted
induced cost at most the independent-sampling expectation at density k/|A|.
There is no fluctuation in the selected cardinality. -/
theorem weighted_selection (A : Finset α) (H : Finset (Finset α))
    (hsub : ∀ e ∈ H, e ⊆ A) (W : Finset α → ℝ) (hW : ∀ e ∈ H, 0 ≤ W e)
    (k : ℕ) (hk : k ≤ A.card) :
    ∃ B ⊆ A, B.card=k ∧
      (∑ e ∈ H.filter (fun e => e ⊆ B), W e) ≤
        ∑ e ∈ H, W e*((k:ℝ)/A.card)^e.card := by
  induction A using Finset.strongInductionOn generalizing H k
  rename_i A ih
  by_cases hk0 : k=0
  · subst k
    refine ⟨∅,empty_subset _,rfl,?_⟩
    simp only [Nat.cast_zero,zero_div,sum_filter]
    apply sum_le_sum
    intro e he
    by_cases he0 : e=∅
    · subst e
      simp
    · have hc : e.card ≠ 0 := by simpa using he0
      simp [he0,hc]
  by_cases hkeq : k=A.card
  · refine ⟨A,Subset.refl _,hkeq.symm,?_⟩
    have hA0 : (A.card:ℝ) ≠ 0 := by exact_mod_cast (show A.card≠0 by omega)
    have hf : H.filter (fun e => e ⊆ A)=H := filter_eq_self.mpr hsub
    rw [hf,hkeq,div_self hA0]
    simp
  have hn : 2 ≤ A.card := by omega
  let q : ℝ := (k:ℝ)/(A.card-1:ℕ)
  let p : ℝ := (k:ℝ)/A.card
  let cost (a : α) : ℝ := ∑ e ∈ H.filter (fun e => a ∉ e), W e*q^e.card
  let target : ℝ := ∑ e ∈ H, W e*p^e.card
  have hsum : (∑ a ∈ A, cost a) ≤ ∑ _a ∈ A, target := by
    rw [sum_const,nsmul_eq_mul]
    dsimp [cost,target]
    rw [deletion_sum A H hsub,mul_sum]
    apply sum_le_sum
    intro e he
    have hb := one_step_power A.card k e.card hn (card_le_card (hsub e he))
    have hh := mul_le_mul_of_nonneg_left hb (hW e he)
    dsimp [p,q]
    nlinarith only [hh]
  obtain ⟨a,ha,hcost⟩ := exists_le_of_sum_le (card_pos.mp (by omega : 0<A.card)) hsum
  let H' := H.filter (fun e => a ∉ e)
  have hsub' : ∀ e ∈ H', e ⊆ A.erase a := by
    intro e he
    obtain ⟨he,hea⟩ := mem_filter.mp he
    intro x hx
    exact mem_erase.mpr ⟨fun h => hea (h ▸ hx),hsub e he hx⟩
  have hW' : ∀ e ∈ H', 0 ≤ W e := fun e he => hW e (mem_filter.mp he).1
  have hk' : k ≤ (A.erase a).card := by rw [card_erase_of_mem ha]; omega
  obtain ⟨B,hB,hBc,hbound⟩ := ih (A.erase a) (erase_ssubset ha) H' hsub' hW' k hk'
  have hfilter : H'.filter (fun e => e ⊆ B) = H.filter (fun e => e ⊆ B) := by
    ext e
    simp only [H',mem_filter]
    constructor
    · tauto
    · rintro ⟨he,heB⟩
      refine ⟨⟨he,?_⟩,heB⟩
      intro hae
      exact notMem_erase a A (hB (heB hae))
  rw [hfilter,card_erase_of_mem ha] at hbound
  refine ⟨B,hB.trans (erase_subset _ _),hBc,hbound.trans ?_⟩
  exact hcost

/-- Two uniform edge families can be controlled simultaneously while the
sample cardinality is kept exact. -/
theorem two_uniform_selection (A : Finset α) (H G : Finset (Finset α))
    (hH : ∀ e ∈ H, e ⊆ A) (hG : ∀ e ∈ G, e ⊆ A)
    (r s : ℕ) (hr : ∀ e ∈ H, e.card=r) (hs : ∀ e ∈ G, e.card=s)
    (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m) (k : ℕ) (hk : k ≤ A.card) :
    ∃ B ⊆ A, B.card=k ∧
      l*(H.filter (fun e => e ⊆ B)).card+m*(G.filter (fun e => e ⊆ B)).card ≤
        l*((k:ℝ)/A.card)^r*H.card+m*((k:ℝ)/A.card)^s*G.card := by
  classical
  let W : Finset α → ℝ := fun e => (if e ∈ H then l else 0)+(if e ∈ G then m else 0)
  have hsub : ∀ e ∈ H∪G, e ⊆ A := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact hH e he
    · exact hG e he
  have hW : ∀ e ∈ H∪G, 0 ≤ W e := by
    intro e he
    dsimp [W]
    split_ifs <;> linarith
  obtain ⟨B,hBA,hBk,hcost⟩ := weighted_selection A (H∪G) hsub W hW k hk
  have hfH : ((H∪G).filter (fun e => e ⊆ B)).filter (fun e => e ∈ H) =
      H.filter (fun e => e ⊆ B) := by
    ext e
    simp only [mem_filter,mem_union]
    tauto
  have hfG : ((H∪G).filter (fun e => e ⊆ B)).filter (fun e => e ∈ G) =
      G.filter (fun e => e ⊆ B) := by
    ext e
    simp only [mem_filter,mem_union]
    tauto
  have hleft : (∑ e ∈ (H∪G).filter (fun e => e ⊆ B), W e) =
      l*(H.filter (fun e => e ⊆ B)).card+m*(G.filter (fun e => e ⊆ B)).card := by
    simp only [W,sum_add_distrib,← sum_filter,hfH,hfG,sum_const,nsmul_eq_mul]
    ring
  have hfH' : (H∪G).filter (fun e => e ∈ H) = H := by
    ext e
    simp only [mem_filter,mem_union]
    tauto
  have hfG' : (H∪G).filter (fun e => e ∈ G) = G := by
    ext e
    simp only [mem_filter,mem_union]
    tauto
  have hright : (∑ e ∈ H∪G, W e*((k:ℝ)/A.card)^e.card) =
      l*((k:ℝ)/A.card)^r*H.card+m*((k:ℝ)/A.card)^s*G.card := by
    simp only [W,add_mul,ite_mul,zero_mul,sum_add_distrib,← sum_filter,hfH',hfG']
    congr 1
    · rw [sum_congr rfl (fun e he => by rw [hr e he])]
      simp [mul_comm]
    · rw [sum_congr rfl (fun e he => by rw [hs e he])]
      simp [mul_comm]
  rw [hleft,hright] at hcost
  exact ⟨B,hBA,hBk,hcost⟩

/-- A simple two-threshold consequence. The strict cost inequality provides
room for both constraints at once, without any variance estimates. -/
theorem simultaneous_selection (A : Finset α) (H G : Finset (Finset α))
    (hH : ∀ e ∈ H, e ⊆ A) (hG : ∀ e ∈ G, e ⊆ A)
    (r s : ℕ) (hr : ∀ e ∈ H, e.card=r) (hs : ∀ e ∈ G, e.card=s)
    (T U : ℝ) (hT : 0 < T) (hU : 0 < U) (k : ℕ) (hk : k ≤ A.card)
    (hcost : ((k:ℝ)/A.card)^r*H.card/T+((k:ℝ)/A.card)^s*G.card/U < 1) :
    ∃ B ⊆ A, B.card=k ∧
      ((H.filter (fun e => e ⊆ B)).card : ℝ) < T ∧
      ((G.filter (fun e => e ⊆ B)).card : ℝ) < U := by
  obtain ⟨B,hBA,hBk,hb⟩ := two_uniform_selection A H G hH hG r s hr hs
    (1/T) (1/U) (by positivity) (by positivity) k hk
  have hleft : ((H.filter (fun e => e ⊆ B)).card : ℝ)/T+
      ((G.filter (fun e => e ⊆ B)).card : ℝ)/U < 1 := by
    have hb' : ((H.filter (fun e => e ⊆ B)).card : ℝ)/T+
        ((G.filter (fun e => e ⊆ B)).card : ℝ)/U ≤
        ((k:ℝ)/A.card)^r*H.card/T+((k:ℝ)/A.card)^s*G.card/U := by
      convert hb using 1 <;> ring
    exact hb'.trans_lt hcost
  have hhn : (0:ℝ) ≤ (H.filter (fun e => e ⊆ B)).card/T := by positivity
  have hgn : (0:ℝ) ≤ (G.filter (fun e => e ⊆ B)).card/U := by positivity
  refine ⟨B,hBA,hBk,?_,?_⟩
  · exact (div_lt_one hT).mp (by linarith)
  · exact (div_lt_one hU).mp (by linarith)

#print axioms one_step_power
#print axioms deletion_sum
#print axioms weighted_selection
#print axioms two_uniform_selection
#print axioms simultaneous_selection
end Erdos773.FixedCardinalitySampling
