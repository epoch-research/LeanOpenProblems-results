import Submission.LargeEndpointDegenerateWalks
import Submission.MixedDivisorCycleDichotomy

/-!
Counts of actual closed four-edge configurations satisfying endpoint-product
equality. The alternating diagonal is bounded using its additional closure
condition; it is not put into the subpower completion estimate. These are
initially restricted to the product-equality case. The final estimates
cover all closed walks of these two traversal types above an explicit
high-label threshold; no full matrix-moment or density theorem is asserted.
-/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

abbrev FourWalkData := Σ _ : ℕ × ℕ, ℕ × ℕ

def balancedClosedFourFibre (B N a b : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 N) ×ˢ (Icc 1 N)).filter fun cd =>
    (a+1)*(b+1)*cd.1*cd.2=a*b*(cd.1+1)*(cd.2+1) ∧
    B < Nat.maxPrimeFac a ∧ B < Nat.maxPrimeFac (b+1) ∧ B < Nat.maxPrimeFac cd.1 ∧
    Nat.maxPrimeFac (b+1)=Nat.maxPrimeFac (cd.1+1) ∧
    Nat.maxPrimeFac cd.1=Nat.maxPrimeFac (cd.2+1) ∧
    Nat.maxPrimeFac cd.2=Nat.maxPrimeFac a

/-- Traversal pattern forward, forward, backward, backward. The first
shared label and its lower bound are encoded by the base finset. -/
def balancedClosedDegenerateFourWalks (B N : ℕ) : Finset FourWalkData :=
  (commonLargeEndpointPairs B N 1 0).sigma fun ab => balancedClosedFourFibre B N ab.1 ab.2

def alternatingClosedFourFibre (B N a b : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 N) ×ˢ (Icc 1 N)).filter fun cd =>
    (a+1)*b*(cd.1+1)*cd.2=a*(b+1)*cd.1*(cd.2+1) ∧
    B < Nat.maxPrimeFac a ∧ B < Nat.maxPrimeFac b ∧ B < Nat.maxPrimeFac (cd.1+1) ∧
    Nat.maxPrimeFac b=Nat.maxPrimeFac cd.1 ∧
    Nat.maxPrimeFac (cd.1+1)=Nat.maxPrimeFac (cd.2+1) ∧
    Nat.maxPrimeFac cd.2=Nat.maxPrimeFac a

/-- Traversal pattern forward, backward, forward, backward, including
immediate backtracking. -/
def alternatingClosedDegenerateFourWalks (B N : ℕ) : Finset FourWalkData :=
  (commonLargeEndpointPairs B N 1 1).sigma fun ab => alternatingClosedFourFibre B N ab.1 ab.2

lemma balancedClosedFourFibre_card_le (B N a b : ℕ) :
    (balancedClosedFourFibre B N a b).card ≤ balancedFourCompletionCount a b N := by
  apply card_le_card
  intro cd hcd
  obtain ⟨hbox,heq,_⟩ := mem_filter.mp hcd
  exact mem_filter.mpr ⟨hbox,heq⟩

lemma alternatingClosedFourFibre_card_le (B N a b : ℕ) :
    (alternatingClosedFourFibre B N a b).card ≤ alternatingFourCompletionCount a b N := by
  apply card_le_card
  intro cd hcd
  obtain ⟨hbox,heq,_⟩ := mem_filter.mp hcd
  exact mem_filter.mpr ⟨hbox,heq⟩

lemma balancedClosedDegenerateFourWalks_card_le (B N : ℕ) :
    (balancedClosedDegenerateFourWalks B N).card ≤ balancedEndpointDegeneracies B N 1 0 := by
  rw [balancedClosedDegenerateFourWalks,card_sigma]
  exact sum_le_sum fun ab _ => balancedClosedFourFibre_card_le B N ab.1 ab.2

/-- On the alternating diagonal, product equality gives c=d, while
prime-label closure also forces the remaining shared label P(a)=P(c). -/
lemma alternatingClosedFourFibre_diagonal (B N a c d : ℕ) (ha : 0 < a)
    (h : (c,d) ∈ alternatingClosedFourFibre B N a a) :
    c=d ∧ B < Nat.maxPrimeFac a ∧ Nat.maxPrimeFac a=Nat.maxPrimeFac c := by
  obtain ⟨_,heq,hBa,_,_,hac,_,_⟩ := mem_filter.mp h
  exact ⟨(alternating_equal_ratio_iff a c d ha).mp heq,hBa,hac⟩

lemma alternatingClosedDegenerateFourWalks_diagonal_card_le (B N : ℕ) :
    ((alternatingClosedDegenerateFourWalks B N).filter fun w => w.1.1=w.1.2).card ≤
      (commonLargeEndpointPairs B N 0 0).card := by
  let f : FourWalkData → ℕ × ℕ := fun w => (w.1.1,w.2.1)
  have hdata (w : FourWalkData)
      (hw : w ∈ (alternatingClosedDegenerateFourWalks B N).filter fun w => w.1.1=w.1.2) :
      w.1.1 ∈ Icc 1 N ∧ w.2.1 ∈ Icc 1 N ∧ w.1.1=w.1.2 ∧ w.2.1=w.2.2 ∧
      B < Nat.maxPrimeFac w.1.1 ∧ Nat.maxPrimeFac w.1.1=Nat.maxPrimeFac w.2.1 := by
    obtain ⟨hw,hab⟩ := mem_filter.mp hw
    obtain ⟨habmem,hcd⟩ := mem_sigma.mp hw
    have ha := (mem_commonLargeEndpointPairs B N 1 1 _ _).mp habmem
    have hc := (mem_product.mp (mem_filter.mp hcd).1).1
    have hcd' : (w.2.1,w.2.2) ∈ alternatingClosedFourFibre B N w.1.1 w.1.1 := by
      simpa only [hab] using hcd
    have hd := alternatingClosedFourFibre_diagonal B N _ _ _ (mem_Icc.mp ha.1).1 hcd'
    exact ⟨ha.1,hc,hab,hd.1,hd.2⟩
  apply card_le_card_of_injOn f
  · intro w hw
    obtain ⟨ha,hc,_,_,hBa,hac⟩ := hdata w hw
    apply (mem_commonLargeEndpointPairs B N 0 0 _ _).mpr
    simpa only [f,Nat.add_zero] using And.intro ha (And.intro hc (And.intro hBa hac))
  · intro z hz w hw he
    have hz' := hdata z hz
    have hw' := hdata w hw
    dsimp only [f] at he
    have ha := (Prod.mk.inj he).1
    have hc := (Prod.mk.inj he).2
    apply Sigma.ext
    · exact Prod.ext ha (by omega)
    · exact heq_of_eq (Prod.ext hc (by omega))

lemma alternatingClosedDegenerateFourWalks_offDiagonal_card_le (B N : ℕ) :
    ((alternatingClosedDegenerateFourWalks B N).filter fun w => w.1.1≠w.1.2).card ≤
      alternatingEndpointDegeneracies B N 1 1 := by
  have he : (alternatingClosedDegenerateFourWalks B N).filter (fun w => w.1.1≠w.1.2) =
      (commonLargeEndpointPairs B N 1 1).sigma (fun ab =>
        if ab.1=ab.2 then ∅ else alternatingClosedFourFibre B N ab.1 ab.2) := by
    ext w
    by_cases h : w.1.1=w.1.2 <;>
      simp [alternatingClosedDegenerateFourWalks,mem_sigma,h]
  rw [he,card_sigma]
  unfold alternatingEndpointDegeneracies endpointCompletionSum
  apply sum_le_sum
  intro ab _
  dsimp only
  split_ifs with hab
  · simp
  · exact alternatingClosedFourFibre_card_le B N ab.1 ab.2

/-- The previously omitted diagonal is now controlled by genuine closure.
It costs a shared-label pair count, not N completions for every base pair. -/
theorem alternatingClosedDegenerateFourWalks_card_le (B N : ℕ) :
    (alternatingClosedDegenerateFourWalks B N).card ≤
      alternatingEndpointDegeneracies B N 1 1+N*((N+1)/(B+1)+1) := by
  have hc := card_filter_add_card_filter_not
    (s := alternatingClosedDegenerateFourWalks B N) (fun w => w.1.1=w.1.2)
  have hd := (alternatingClosedDegenerateFourWalks_diagonal_card_le B N).trans
    (commonLargeEndpointPairs_card_le B N 0 0 (by omega))
  have ho := alternatingClosedDegenerateFourWalks_offDiagonal_card_le B N
  simp only [ne_eq] at ho
  omega

/-- Uniform completion estimates for these actual closed configurations,
still with the endpoint-product-equality condition retained. -/
theorem closedDegenerateFourWalks_uniform_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ B : ℕ,
      ((balancedClosedDegenerateFourWalks B N).card : ℝ) ≤
        (N : ℝ)^ε*N*((N+1)/(B+1)+1 : ℕ) ∧
      ((alternatingClosedDegenerateFourWalks B N).card : ℝ) ≤
        ((N : ℝ)^ε+1)*N*((N+1)/(B+1)+1 : ℕ) := by
  filter_upwards [endpoint_degeneracies_uniform_bound ε hε] with N hN
  intro B
  constructor
  · exact (Nat.cast_le.mpr (balancedClosedDegenerateFourWalks_card_le B N)).trans
      (hN B 1 0 (by omega)).1
  · have hb := (hN B 1 1 (by omega)).2.2
    have hc := Nat.cast_le (α := ℝ).mpr (alternatingClosedDegenerateFourWalks_card_le B N)
    push_cast at hc hb ⊢
    nlinarith

private lemma rotate_four_values :
    finRotate 4 (0 : Fin 4)=1 ∧ finRotate 4 (1 : Fin 4)=2 ∧
      finRotate 4 (2 : Fin 4)=3 ∧ finRotate 4 (3 : Fin 4)=0 := by decide

/-- Above the four-cycle product threshold, actual closure implies the
product identity used in the balanced fibre count. -/
lemma balanced_four_closure_product_eq (B N a b c d : ℕ)
    (hn : a≤N ∧ b≤N ∧ c≤N ∧ d≤N)
    (hB : B < Nat.maxPrimeFac a ∧ B < Nat.maxPrimeFac b ∧
      B < Nat.maxPrimeFac (c+1) ∧ B < Nat.maxPrimeFac (d+1))
    (hclose : Nat.maxPrimeFac (a+1)=Nat.maxPrimeFac b ∧
      Nat.maxPrimeFac (b+1)=Nat.maxPrimeFac (c+1) ∧
      Nat.maxPrimeFac c=Nat.maxPrimeFac (d+1) ∧ Nat.maxPrimeFac d=Nat.maxPrimeFac a)
    (hsize : 4*(N+1)^3 < (B+1)^4) :
    (a+1)*(b+1)*c*d=a*b*(c+1)*(d+1) := by
  let v : Fin 4 → ℕ := ![a,b,c,d]
  let e : Fin 4 → Bool := ![true,true,false,false]
  obtain ⟨hr0,hr1,hr2,hr3⟩ := rotate_four_values
  have hv : ∀ i, v i≤N := by
    intro i
    fin_cases i <;> simp [v] <;> omega
  have hc : ∀ i, Nat.maxPrimeFac (mixedCycleTarget (v i) (e i)) =
      Nat.maxPrimeFac (mixedCycleSource (v (finRotate 4 i)) (e (finRotate 4 i))) := by
    intro i
    fin_cases i <;> simp [hr0,hr1,hr2,hr3,v,e,mixedCycleSource,mixedCycleTarget] <;> tauto
  have hb : ∀ i, B < Nat.maxPrimeFac (mixedCycleSource (v i) (e i)) := by
    intro i
    fin_cases i <;> simp [v,e,mixedCycleSource] <;> tauto
  have he := actual_mixed_cycle_product_equality_of_label_cutoff (finRotate 4) v e N B hv hc hb
    (by simpa using hsize)
  simp [v,e,mixedCycleSource,mixedCycleTarget,Fin.prod_univ_succ] at he
  nlinarith only [he]

lemma alternating_four_closure_product_eq (B N a b c d : ℕ)
    (hn : a≤N ∧ b≤N ∧ c≤N ∧ d≤N)
    (hB : B < Nat.maxPrimeFac a ∧ B < Nat.maxPrimeFac (b+1) ∧
      B < Nat.maxPrimeFac c ∧ B < Nat.maxPrimeFac (d+1))
    (hclose : Nat.maxPrimeFac (a+1)=Nat.maxPrimeFac (b+1) ∧
      Nat.maxPrimeFac b=Nat.maxPrimeFac c ∧
      Nat.maxPrimeFac (c+1)=Nat.maxPrimeFac (d+1) ∧ Nat.maxPrimeFac d=Nat.maxPrimeFac a)
    (hsize : 4*(N+1)^3 < (B+1)^4) :
    (a+1)*b*(c+1)*d=a*(b+1)*c*(d+1) := by
  let v : Fin 4 → ℕ := ![a,b,c,d]
  let e : Fin 4 → Bool := ![true,false,true,false]
  obtain ⟨hr0,hr1,hr2,hr3⟩ := rotate_four_values
  have hv : ∀ i, v i≤N := by
    intro i
    fin_cases i <;> simp [v] <;> omega
  have hc : ∀ i, Nat.maxPrimeFac (mixedCycleTarget (v i) (e i)) =
      Nat.maxPrimeFac (mixedCycleSource (v (finRotate 4 i)) (e (finRotate 4 i))) := by
    intro i
    fin_cases i <;> simp [hr0,hr1,hr2,hr3,v,e,mixedCycleSource,mixedCycleTarget] <;> tauto
  have hb : ∀ i, B < Nat.maxPrimeFac (mixedCycleSource (v i) (e i)) := by
    intro i
    fin_cases i <;> simp [v,e,mixedCycleSource] <;> tauto
  have he := actual_mixed_cycle_product_equality_of_label_cutoff (finRotate 4) v e N B hv hc hb
    (by simpa using hsize)
  simp [v,e,mixedCycleSource,mixedCycleTarget,Fin.prod_univ_succ] at he
  nlinarith only [he]

/-- The same balanced closed walks, without imposing product equality. -/
def balancedClosedFourWalks (B N : ℕ) : Finset FourWalkData :=
  (commonLargeEndpointPairs B N 1 0).sigma fun ab =>
    ((Icc 1 N) ×ˢ (Icc 1 N)).filter fun cd =>
      B < Nat.maxPrimeFac ab.1 ∧ B < Nat.maxPrimeFac (ab.2+1) ∧ B < Nat.maxPrimeFac cd.1 ∧
      Nat.maxPrimeFac (ab.2+1)=Nat.maxPrimeFac (cd.1+1) ∧
      Nat.maxPrimeFac cd.1=Nat.maxPrimeFac (cd.2+1) ∧
      Nat.maxPrimeFac cd.2=Nat.maxPrimeFac ab.1

def alternatingClosedFourWalks (B N : ℕ) : Finset FourWalkData :=
  (commonLargeEndpointPairs B N 1 1).sigma fun ab =>
    ((Icc 1 N) ×ˢ (Icc 1 N)).filter fun cd =>
      B < Nat.maxPrimeFac ab.1 ∧ B < Nat.maxPrimeFac ab.2 ∧ B < Nat.maxPrimeFac (cd.1+1) ∧
      Nat.maxPrimeFac ab.2=Nat.maxPrimeFac cd.1 ∧
      Nat.maxPrimeFac (cd.1+1)=Nat.maxPrimeFac (cd.2+1) ∧
      Nat.maxPrimeFac cd.2=Nat.maxPrimeFac ab.1

lemma balancedClosedFourWalks_eq_degenerate (B N : ℕ)
    (hsize : 4*(N+1)^3 < (B+1)^4) :
    balancedClosedFourWalks B N = balancedClosedDegenerateFourWalks B N := by
  apply Subset.antisymm
  · intro w hw
    obtain ⟨hbase,hcd⟩ := mem_sigma.mp hw
    obtain ⟨ha,hb,hBp,hAB⟩ := (mem_commonLargeEndpointPairs B N 1 0 _ _).mp hbase
    simp only [Nat.add_zero] at hAB
    obtain ⟨hbox,hBa,hBb,hBc,hBC,hCD,hDA⟩ := mem_filter.mp hcd
    obtain ⟨hc,hd⟩ := mem_product.mp hbox
    have he := balanced_four_closure_product_eq B N w.1.1 w.1.2 w.2.1 w.2.2
      ⟨(mem_Icc.mp ha).2,(mem_Icc.mp hb).2,(mem_Icc.mp hc).2,(mem_Icc.mp hd).2⟩
      ⟨hBa,hAB ▸ hBp,hBC ▸ hBb,hCD ▸ hBc⟩ ⟨hAB,hBC,hCD,hDA⟩ hsize
    exact mem_sigma.mpr ⟨hbase,mem_filter.mpr ⟨hbox,he,hBa,hBb,hBc,hBC,hCD,hDA⟩⟩
  · intro w hw
    obtain ⟨hbase,hcd⟩ := mem_sigma.mp hw
    obtain ⟨hbox,_,hrest⟩ := mem_filter.mp hcd
    exact mem_sigma.mpr ⟨hbase,mem_filter.mpr ⟨hbox,hrest⟩⟩

lemma alternatingClosedFourWalks_eq_degenerate (B N : ℕ)
    (hsize : 4*(N+1)^3 < (B+1)^4) :
    alternatingClosedFourWalks B N = alternatingClosedDegenerateFourWalks B N := by
  apply Subset.antisymm
  · intro w hw
    obtain ⟨hbase,hcd⟩ := mem_sigma.mp hw
    obtain ⟨ha,hb,hBp,hAB⟩ := (mem_commonLargeEndpointPairs B N 1 1 _ _).mp hbase
    obtain ⟨hbox,hBa,hBb,hBc,hBC,hCD,hDA⟩ := mem_filter.mp hcd
    obtain ⟨hc,hd⟩ := mem_product.mp hbox
    have he := alternating_four_closure_product_eq B N w.1.1 w.1.2 w.2.1 w.2.2
      ⟨(mem_Icc.mp ha).2,(mem_Icc.mp hb).2,(mem_Icc.mp hc).2,(mem_Icc.mp hd).2⟩
      ⟨hBa,hAB ▸ hBp,hBC ▸ hBb,hCD ▸ hBc⟩ ⟨hAB,hBC,hCD,hDA⟩ hsize
    exact mem_sigma.mpr ⟨hbase,mem_filter.mpr ⟨hbox,he,hBa,hBb,hBc,hBC,hCD,hDA⟩⟩
  · intro w hw
    obtain ⟨hbase,hcd⟩ := mem_sigma.mp hw
    obtain ⟨hbox,_,hrest⟩ := mem_filter.mp hcd
    exact mem_sigma.mpr ⟨hbase,mem_filter.mpr ⟨hbox,hrest⟩⟩

/-- At this explicit high-label threshold, the bounds apply to all closed
walks of these two traversal patterns, not just a product-equality subset. -/
theorem closedFourWalks_high_label_uniform_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ B : ℕ, 4*(N+1)^3 < (B+1)^4 →
      ((balancedClosedFourWalks B N).card : ℝ) ≤
        (N : ℝ)^ε*N*((N+1)/(B+1)+1 : ℕ) ∧
      ((alternatingClosedFourWalks B N).card : ℝ) ≤
        ((N : ℝ)^ε+1)*N*((N+1)/(B+1)+1 : ℕ) := by
  filter_upwards [closedDegenerateFourWalks_uniform_bound ε hε] with N hN
  intro B hsize
  rw [balancedClosedFourWalks_eq_degenerate B N hsize,
    alternatingClosedFourWalks_eq_degenerate B N hsize]
  exact hN B

lemma four_cycle_threshold_eventually (β : ℝ) (hβ : 3/4 < β) :
    ∀ᶠ N : ℕ in atTop, ∀ B : ℕ, (N : ℝ)^β ≤ B+1 →
      4*(N+1)^3 < (B+1)^4 := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^(4*β-3)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 4*β-3)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_gt_atTop 32,eventually_ge_atTop (1 : ℕ)] with N hpow hN
  intro B hB
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have he : (N : ℝ)^3*(N : ℝ)^(4*β-3)=((N : ℝ)^β)^4 := by
    rw [← Real.rpow_mul_natCast hNr.le,← Real.rpow_natCast,← Real.rpow_add hNr]
    congr 1
    norm_num
    ring
  have hmul := mul_lt_mul_of_pos_left hpow (pow_pos hNr 3)
  have hcube : (N+1 : ℝ)^3 ≤ (2*N)^3 := by gcongr; linarith
  have hBP : ((N : ℝ)^β)^4 ≤ (B+1 : ℝ)^4 :=
    pow_le_pow_left₀ (Real.rpow_nonneg hNr.le β) hB 4
  have hresult : 4*(N+1 : ℝ)^3 < (B+1 : ℝ)^4 := by
    rw [he] at hmul
    nlinarith
  exact_mod_cast hresult

/-- A power-sized bound for actual closed walks of the two balanced
traversal types in the range beta>3/4. The trace-to-operator exponent
obstruction is not removed by this count. -/
theorem closedFourWalks_high_label_uniform_power_bound (β ε : ℝ)
    (hβ0 : 3/4 < β) (hβ1 : β ≤ 1) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ B : ℕ, (N : ℝ)^β ≤ B+1 →
      ((balancedClosedFourWalks B N).card : ℝ) ≤ 3*(N : ℝ)^(2-β+ε) ∧
      ((alternatingClosedFourWalks B N).card : ℝ) ≤ 6*(N : ℝ)^(2-β+ε) := by
  filter_upwards [closedFourWalks_high_label_uniform_bound ε hε,
    four_cycle_threshold_eventually β hβ0,eventually_ge_atTop (1 : ℕ)] with N hcount hsize hN
  intro B hB
  have hc := hcount B (hsize B hB)
  have hb := endpoint_degeneracy_budget_power_bound N B hN β ε hβ1 hB
  have hp : (1 : ℝ) ≤ (N : ℝ)^ε := Real.one_le_rpow (by exact_mod_cast hN) hε.le
  constructor
  · exact hc.1.trans hb
  · have hm := mul_le_mul_of_nonneg_right (show (N : ℝ)^ε+1 ≤ 2*(N : ℝ)^ε by linarith)
      (show (0 : ℝ) ≤ N*((N+1)/(B+1)+1 : ℕ) by positivity)
    nlinarith [hc.2]

#print axioms alternatingClosedDegenerateFourWalks_diagonal_card_le
#print axioms closedDegenerateFourWalks_uniform_bound
#print axioms alternating_four_closure_product_eq
#print axioms closedFourWalks_high_label_uniform_bound
#print axioms closedFourWalks_high_label_uniform_power_bound
end Erdos371
