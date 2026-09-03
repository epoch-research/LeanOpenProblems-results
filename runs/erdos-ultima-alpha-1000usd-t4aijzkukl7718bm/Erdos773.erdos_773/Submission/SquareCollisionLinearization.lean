import Submission.SquareCollisionIntersections
import Submission.HypergraphLinearization
import Submission.APFreeExtraction

/-!
Actual square-root subsets of size N^(4/5-epsilon) whose four-root collision
hypergraph is linear. This is a relaxed selection theorem: collisions can
remain, and it does not prove the square-Sidon conjecture.
-/
namespace Erdos773.SquareCollisionLinearization
open Finset Filter SquareCollisionCodegrees SquareCollisionIntersections
set_option maxHeartbeats 1000000

/-- Distinct four-root collision supports share at most one root. -/
def LinearCollisions (A : Finset ℕ) : Prop :=
  ∀ e ∈ edges A, ∀ f ∈ edges A, e ≠ f → (e ∩ f).card ≤ 1

/-- The finite selection certificate, starting from progression-free squares. -/
theorem finite_selection {A : Finset ℕ} {N : ℕ} (hA : A ⊆ Icc 1 N)
    (hAP : ThreeAPFree ((A.image (fun n : ℕ => n^2)) : Set ℕ))
    (K : ℝ)
    (hK : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N, a ≠ b →
      ((pairEdges (Icc 1 N) a b).card : ℝ) ≤ K)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ B ⊆ A, ThreeAPFree ((B.image (fun n : ℕ => n^2)) : Set ℕ) ∧
      LinearCollisions B ∧ p*A.card - p^6*(N : ℝ)^2*K^2 ≤ B.card := by
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
  obtain ⟨B,hBA,hlin,hcard⟩ := HypergraphLinearization.finite_selection A (edges A)
    (fun e he => mem_powerset.mp (mem_filter.mp he).1)
    (fun e he => (mem_filter.mp he).2.1)
    (fun e he f hf hne => intersection_card_le_two hAP he hf hne)
    K hcodeg p hp hp1
  refine ⟨B,hBA,?_,?_,?_⟩
  · exact hAP.mono (by exact_mod_cast image_subset_image hBA)
  · intro e he f hf hne
    exact hlin e (edges_mono hBA he) (mem_powerset.mp (mem_filter.mp he).1)
      f (edges_mono hBA hf) (mem_powerset.mp (mem_filter.mp hf).1) hne
  · have hcardA : (A.card : ℝ) ≤ N := by
      exact_mod_cast (show A.card ≤ N by simpa using card_le_card hA)
    have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ A.card) hcardA 2
    have hmul := mul_le_mul_of_nonneg_left hpow (show 0 ≤ p^6*K^2 by positivity)
    nlinarith only [hcard,hmul]

lemma ap_free_roots (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ A ⊆ Icc 1 N,
      ThreeAPFree ((A.image (fun n : ℕ => n^2)) : Set ℕ) ∧
      (N : ℝ)^(1-ε) ≤ A.card := by
  filter_upwards [APFreeExtraction.square_ap_free_near_linear ε hε] with N hN
  obtain ⟨B,hB,hAP,hc⟩ := hN
  let A := (Icc 1 N).filter (fun n => n^2 ∈ B)
  have he : A.image (fun n : ℕ => n^2) = B := by
    ext b
    constructor
    · intro hb
      obtain ⟨n,hn,rfl⟩ := mem_image.mp hb
      exact (mem_filter.mp hn).2
    · intro hb
      obtain ⟨n,hn,rfl⟩ := mem_image.mp (hB hb)
      exact mem_image.mpr ⟨n,mem_filter.mpr ⟨hn,hb⟩,rfl⟩
  have hcard : B.card = A.card := by
    rw [← he]
    exact card_image_of_injective _ (Nat.pow_left_injective (by decide : (2:ℕ) ≠ 0))
  refine ⟨A,filter_subset _ _,?_,?_⟩
  · rwa [he]
  · rwa [hcard] at hc

/-- An actual integral relaxed selection result. LinearCollisions is weaker
than Sidon: it permits collision edges, provided they do not overlap twice. -/
theorem linear_collisions_four_fifths (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ B ⊆ Icc 1 N,
      ThreeAPFree ((B.image (fun n : ℕ => n^2)) : Set ℕ) ∧
      LinearCollisions B ∧ (N : ℝ)^(4/5-ε) ≤ B.card := by
  have ht (r : ℝ) (hr : 0 < r) :
      Tendsto (fun N : ℕ => (N : ℝ)^(-r)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hr).comp tendsto_natCast_atTop_atTop
  have hsmall := Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1/2)
    (ht (7*ε/4) (by positivity))
  have hslack := Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1/2)
    (ht (ε/4) (by positivity))
  filter_upwards [ap_free_roots (ε/4) (by positivity),
    eventually_pair_codegree_bound (ε/4) (by positivity),
    hsmall,hslack,eventually_ge_atTop 1] with N hAP hcodeg hsmall hslack hN
  obtain ⟨A,hA,hAP,hAc⟩ := hAP
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0:ℝ) < N := by linarith
  let p : ℝ := (N : ℝ)^(-1/5-ε/2)
  let K : ℝ := (N : ℝ)^(ε/4)
  let S : ℝ := (N : ℝ)^(4/5-3*ε/4)
  have hp : 0 ≤ p := Real.rpow_nonneg hNpos.le _
  have hp1 : p ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hS : 0 ≤ S := Real.rpow_nonneg hNpos.le _
  obtain ⟨B,hBA,hBAP,hlin,hcard⟩ := finite_selection hA hAP K hcodeg p hp hp1
  have hlead : S ≤ p*A.card := by
    calc
      _ = p*(N : ℝ)^(1-ε/4) := by
        dsimp [p,S]
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hAc hp
  have hcost : p^6*(N : ℝ)^2*K^2 = S*(N : ℝ)^(-(7*ε/4)) := by
    dsimp [p,K,S]
    rw [← Real.rpow_mul_natCast hNpos.le, ← Real.rpow_mul_natCast hNpos.le,
      ← Real.rpow_natCast (N : ℝ) 2,
      ← Real.rpow_add hNpos, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    congr 1
    push_cast
    ring
  have htarget : (N : ℝ)^(4/5-ε) = S*(N : ℝ)^(-(ε/4)) := by
    dsimp [S]
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have herr := mul_le_mul_of_nonneg_left hsmall hS
  have htar := mul_le_mul_of_nonneg_left hslack hS
  rw [hcost] at hcard
  refine ⟨B,hBA.trans hA,hBAP,hlin,?_⟩
  rw [htarget]
  nlinarith only [hcard,hlead,herr,htar]

#print axioms finite_selection
#print axioms linear_collisions_four_fifths
end Erdos773.SquareCollisionLinearization
