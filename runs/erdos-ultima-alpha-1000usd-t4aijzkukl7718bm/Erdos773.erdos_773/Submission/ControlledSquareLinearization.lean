import Submission.SquareCollisionLinearization
import Submission.PenalizedAlteration

/-!
Linearized square-collision hypergraphs with simultaneous cardinality and
retained-edge control. The remaining collision count is explicit; no
near-linear Sidon extraction is claimed.
-/
namespace Erdos773.ControlledSquareLinearization
open Finset Filter SquareCollisionCodegrees SquareCollisionIntersections
open SquareCollisionLinearization
set_option maxHeartbeats 1000000

lemma edges_restrict {A B : Finset ℕ} (hBA : B ⊆ A) :
    edges B = (edges A).filter (fun e => e ⊆ B) := by
  classical
  ext e
  constructor
  · intro he
    exact mem_filter.mpr ⟨edges_mono hBA he,mem_powerset.mp (mem_filter.mp he).1⟩
  · intro he
    obtain ⟨heA,heB⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_powerset.mpr heB,(mem_filter.mp heA).2⟩

/-- A coarse global edge bound obtained by covering with pair fibers. -/
lemma edges_card_le {N : ℕ} (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N, a ≠ b →
      ((pairEdges (Icc 1 N) a b).card : ℝ) ≤ K) :
    ((edges (Icc 1 N)).card : ℝ) ≤ (N : ℝ)^2*K := by
  classical
  let F (ab : ℕ × ℕ) := if ab.1 ≠ ab.2 then pairEdges (Icc 1 N) ab.1 ab.2 else ∅
  have hcover : edges (Icc 1 N) ⊆ ((Icc 1 N) ×ˢ (Icc 1 N)).biUnion F := by
    intro e he
    obtain ⟨heA,h4,hs⟩ := mem_filter.mp he
    have heA := mem_powerset.mp heA
    obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp (show 1 < e.card by omega)
    apply mem_biUnion.mpr
    refine ⟨(a,b),mem_product.mpr ⟨heA ha,heA hb⟩,?_⟩
    dsimp [F]
    rw [if_pos hab]
    exact mem_filter.mpr ⟨he,ha,hb⟩
  have hc := (card_le_card hcover).trans (card_biUnion_le (s := (Icc 1 N) ×ˢ (Icc 1 N)) (t := F))
  calc
    _ ≤ ∑ ab ∈ (Icc 1 N) ×ˢ (Icc 1 N), ((F ab).card : ℝ) := by exact_mod_cast hc
    _ ≤ ∑ _ab ∈ (Icc 1 N) ×ˢ (Icc 1 N), K := by
      apply sum_le_sum
      intro ab hab
      obtain ⟨ha,hb⟩ := mem_product.mp hab
      dsimp [F]
      split_ifs with h
      · simpa using hK0
      · exact hK ab.1 ha ab.2 hb h
    _ = _ := by simp [pow_two]

/-- Cardinality and collision count are controlled by one certificate. -/
theorem finite_selection {A : Finset ℕ} {N : ℕ} (hA : A ⊆ Icc 1 N)
    (hAP : ThreeAPFree ((A.image (fun n : ℕ => n^2)) : Set ℕ))
    (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N, a ≠ b →
      ((pairEdges (Icc 1 N) a b).card : ℝ) ≤ K)
    (p μ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hμ : 0 ≤ μ) :
    ∃ B ⊆ A, ThreeAPFree ((B.image (fun n : ℕ => n^2)) : Set ℕ) ∧
      LinearCollisions B ∧
      p*A.card - p^6*(N : ℝ)^2*K^2 - μ*p^4*(N : ℝ)^2*K ≤
        B.card - μ*(edges B).card := by
  classical
  have hcodeg (P : Finset ℕ) (hP : P ∈ A.powersetCard 2) :
      (((edges A).filter (fun e => P ⊆ e)).card : ℝ) ≤ K := by
    obtain ⟨hPA,hPc⟩ := mem_powersetCard.mp hP
    obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hPc
    have heq : (edges A).filter (fun e => ({a,b} : Finset ℕ) ⊆ e) = pairEdges A a b := by
      ext e
      simp [pairEdges,insert_subset_iff,singleton_subset_iff]
    rw [heq]
    have hc : ((pairEdges A a b).card : ℝ) ≤ (pairEdges (Icc 1 N) a b).card := by
      exact_mod_cast card_le_card (pairEdges_mono hA a b)
    exact hc.trans (hK a (hA (hPA (by simp))) b (hA (hPA (by simp))) hab)
  obtain ⟨B,hBA,hlin,hcard⟩ := PenalizedAlteration.linearize A (edges A)
    (fun e he => mem_powerset.mp (mem_filter.mp he).1)
    (fun e he => (mem_filter.mp he).2.1)
    (fun e he f hf hne => intersection_card_le_two hAP he hf hne)
    K hcodeg p μ hp hp1 hμ
  rw [← edges_restrict hBA] at hcard
  refine ⟨B,hBA,?_,?_,?_⟩
  · exact hAP.mono (by exact_mod_cast image_subset_image hBA)
  · intro e he f hf hne
    exact hlin e (edges_mono hBA he) (mem_powerset.mp (mem_filter.mp he).1)
      f (edges_mono hBA hf) (mem_powerset.mp (mem_filter.mp hf).1) hne
  · have hcardA : (A.card : ℝ) ≤ N := by
      exact_mod_cast (show A.card ≤ N by simpa using card_le_card hA)
    have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ A.card) hcardA 2
    have hmul := mul_le_mul_of_nonneg_left hpow (show 0 ≤ p^6*K^2 by positivity)
    have hE : ((edges A).card : ℝ) ≤ (N : ℝ)^2*K := by
      have hh : ((edges A).card : ℝ) ≤ (edges (Icc 1 N)).card := by
        exact_mod_cast card_le_card (edges_mono hA)
      exact hh.trans (edges_card_le K hK0 hK)
    have hmulE := mul_le_mul_of_nonneg_left hE (show 0 ≤ μ*p^4 by positivity)
    nlinarith only [hcard,hmul,hmulE]

/-- A positive cardinality surplus after paying for every retained collision. -/
theorem controlled_four_fifths (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ B ⊆ Icc 1 N,
      ThreeAPFree ((B.image (fun n : ℕ => n^2)) : Set ℕ) ∧
      LinearCollisions B ∧
      (N : ℝ)^(4/5-ε) + (N : ℝ)^(-2/5-ε)*(edges B).card ≤ B.card := by
  have ht (r : ℝ) (hr : 0 < r) :
      Tendsto (fun N : ℕ => (N : ℝ)^(-r)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hr).comp tendsto_natCast_atTop_atTop
  have hbad := Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1/4)
    (ht (3*ε/4) (by positivity))
  have hedge := Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1/4)
    (ht (11*ε/8) (by positivity))
  have hslack := Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1/2)
    (ht (ε/2) (by positivity))
  filter_upwards [ap_free_roots (ε/4) (by positivity),
    eventually_pair_codegree_bound (ε/8) (by positivity),
    hbad,hedge,hslack,eventually_ge_atTop 1] with N hAP hcodeg hbad hedge hslack hN
  obtain ⟨A,hA,hAP,hAc⟩ := hAP
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0:ℝ) < N := by linarith
  let p : ℝ := (N : ℝ)^(-1/5-ε/4)
  let K : ℝ := (N : ℝ)^(ε/8)
  let μ : ℝ := (N : ℝ)^(-2/5-ε)
  let S : ℝ := (N : ℝ)^(4/5-ε/2)
  have hp : 0 ≤ p := Real.rpow_nonneg hNpos.le _
  have hp1 : p ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hK0 : 0 ≤ K := Real.rpow_nonneg hNpos.le _
  have hμ : 0 ≤ μ := Real.rpow_nonneg hNpos.le _
  have hS : 0 ≤ S := Real.rpow_nonneg hNpos.le _
  obtain ⟨B,hBA,hBAP,hlin,hcard⟩ := finite_selection hA hAP K hK0 hcodeg p μ hp hp1 hμ
  have hlead : S ≤ p*A.card := by
    calc
      _ = p*(N : ℝ)^(1-ε/4) := by
        dsimp [p,S]
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hAc hp
  have hcost1 : p^6*(N : ℝ)^2*K^2 = S*(N : ℝ)^(-(3*ε/4)) := by
    dsimp [p,K,S]
    rw [← Real.rpow_mul_natCast hNpos.le, ← Real.rpow_mul_natCast hNpos.le,
      ← Real.rpow_natCast (N : ℝ) 2,
      ← Real.rpow_add hNpos, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    congr 1
    push_cast
    ring
  have hcost2 : μ*p^4*(N : ℝ)^2*K = S*(N : ℝ)^(-(11*ε/8)) := by
    dsimp [μ,p,K,S]
    rw [← Real.rpow_mul_natCast hNpos.le, ← Real.rpow_natCast (N : ℝ) 2,
      ← Real.rpow_add hNpos, ← Real.rpow_add hNpos,
      ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    congr 1
    push_cast
    ring
  have htarget : (N : ℝ)^(4/5-ε) = S*(N : ℝ)^(-(ε/2)) := by
    dsimp [S]
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have herr1 := mul_le_mul_of_nonneg_left hbad hS
  have herr2 := mul_le_mul_of_nonneg_left hedge hS
  have htar := mul_le_mul_of_nonneg_left hslack hS
  rw [hcost1,hcost2] at hcard
  refine ⟨B,hBA.trans hA,hBAP,hlin,?_⟩
  rw [htarget]
  change _ + μ*(edges B).card ≤ B.card
  nlinarith only [hcard,hlead,herr1,herr2,htar]

/-- In particular the selected linear hypergraph has an explicit average
edge-density bound, not merely a cardinality bound. -/
theorem average_edge_control (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ B ⊆ Icc 1 N,
      ThreeAPFree ((B.image (fun n : ℕ => n^2)) : Set ℕ) ∧
      LinearCollisions B ∧ (N : ℝ)^(4/5-ε) ≤ B.card ∧
      ((edges B).card : ℝ) ≤ (N : ℝ)^(2/5+ε)*B.card := by
  filter_upwards [controlled_four_fifths ε hε,eventually_ge_atTop 1] with N hN hN1
  obtain ⟨B,hB,hAP,hlin,hc⟩ := hN
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
  have hnonneg : 0 ≤ (N : ℝ)^(-2/5-ε)*(edges B).card := by positivity
  have hfirst : (N : ℝ)^(4/5-ε) ≤ B.card := by linarith
  have hsecond : (N : ℝ)^(-2/5-ε)*(edges B).card ≤ B.card := by
    linarith [Real.rpow_nonneg hNpos.le (4/5-ε)]
  refine ⟨B,hB,hAP,hlin,hfirst,?_⟩
  have hm := mul_le_mul_of_nonneg_left hsecond
    (Real.rpow_nonneg hNpos.le (2/5+ε))
  have hcancel : (N : ℝ)^(2/5+ε)*(N : ℝ)^(-2/5-ε) = 1 := by
    rw [← Real.rpow_add hNpos, show (2/5+ε)+(-2/5-ε) = 0 by ring, Real.rpow_zero]
  simpa only [← mul_assoc,hcancel,one_mul] using hm

#print axioms finite_selection
#print axioms controlled_four_fifths
#print axioms average_edge_control
end Erdos773.ControlledSquareLinearization
