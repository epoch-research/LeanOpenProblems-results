import FormalConjecturesUtil
import Submission.QuadraticSupportCubicGaps

/-! Actual consecutive support gaps at the cubic curvature scale. No
rationality implication or new extremal exponent is asserted. -/
open Filter Asymptotics
open scoped Topology
namespace Erdos713QuadraticSupportGapScale
open Erdos713ExactCloneSaturation Erdos713QuadraticSupportCubicGaps
set_option maxHeartbeats 2000000

lemma consecutive_sequence_of_cofinal {P : ℕ → Prop}
    (hP : ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ P m) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ (∀ i, P (n i)) ∧
      ∀ i m : ℕ, n i < m → m < n (i+1) → ¬ P m := by
  classical
  let next (k : ℕ) : ℕ := Nat.find (hP (k+1))
  have hnext (k : ℕ) : k+1 ≤ next k ∧ P (next k) := Nat.find_spec (hP (k+1))
  let n : ℕ → ℕ := Nat.rec (next 0) (fun _ v => next v)
  have hn : StrictMono n := strictMono_nat_of_lt_succ fun i =>
    (Nat.lt_succ_self (n i)).trans_le (hnext (n i)).1
  have hnP (i : ℕ) : P (n i) := by
    cases i with
    | zero => exact (hnext 0).2
    | succ i => exact (hnext (n i)).2
  refine ⟨n,hn,hnP,?_⟩
  intro i m hlo hhi hm
  exact Nat.find_min (hP (n i+1)) hhi ⟨by omega,hm⟩

/-- Arbitrarily far out there are genuinely consecutive quadratic support
orders a<b with `a^(2-alpha) <= 4*c*(b-a)^3`. No support is skipped between
the two endpoints. The condition f(0)=0 suffices for the existing cofinal
support construction and holds for every extremal-number sequence. -/
theorem consecutive_large_gaps {f : ℕ → ℕ} (hf0 : f 0 = 0) {α c : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) (N : ℕ) :
    ∃ a b : ℕ, N ≤ a ∧ a < b ∧ (∃ ε : ℝ, QuadSupport f ε a) ∧
      (∃ ε : ℝ, QuadSupport f ε b) ∧
      (∀ m : ℕ, a < m → m < b → ∀ ε : ℝ, ¬ QuadSupport f ε m) ∧
      (a : ℝ)^(2-α) ≤ 4*c*((b-a : ℕ) : ℝ)^3 := by
  classical
  have hP : ∀ K : ℕ, ∃ m : ℕ, K ≤ m ∧ ∃ ε : ℝ, QuadSupport f ε m := by
    intro K
    obtain ⟨m,ε,hm,_,_,_,hs,_⟩ := Erdos713QuadraticSupports.cofinal_supports
      f hf0 ha ha2 hc h K 0 (by norm_num : (0 : ℝ) < 1)
    exact ⟨m,hm,ε,hs⟩
  obtain ⟨n,hn,hnP,hholes⟩ := consecutive_sequence_of_cofinal hP
  choose ε hs using hnP
  obtain ⟨I,hI⟩ := eventually_atTop.mp (hn.tendsto_atTop.eventually_ge_atTop N)
  obtain ⟨i,hi,hcube⟩ := late_cubic_gap ha hc h hn hs I
  have h01 : n i < n (i+1) := hn (by omega)
  have h12 : n (i+1) < n (i+2) := hn (by omega)
  have hNi : N ≤ n i := hI i hi
  by_cases hleft : n (i+2)-n (i+1) ≤ n (i+1)-n i
  · rw [max_eq_left hleft] at hcube
    refine ⟨n i,n (i+1),hNi,h01,⟨ε i,hs i⟩,⟨ε (i+1),hs (i+1)⟩,?_,?_⟩
    · intro m hm hm' η hη
      exact hholes i m hm hm' ⟨η,hη⟩
    · have hp : (n i : ℝ)^(2-α) ≤ (n (i+1) : ℝ)^(2-α) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h01.le) (by linarith)
      exact hp.trans hcube
  · have hright : n (i+1)-n i ≤ n (i+2)-n (i+1) := by omega
    rw [max_eq_right hright] at hcube
    refine ⟨n (i+1),n (i+2),hNi.trans h01.le,h12,
      ⟨ε (i+1),hs (i+1)⟩,⟨ε (i+2),hs (i+2)⟩,?_,hcube⟩
    intro m hm hm' η hη
    exact hholes (i+1) m hm hm' ⟨η,hη⟩

/-- The actual extremal-number specialization. Its pure-power asymptotic
remains an explicit hypothesis, not a conclusion of this theorem. -/
theorem extremal_consecutive_large_gaps {W : Type*} (H : SimpleGraph W)
    {α c : ℝ} (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (SimpleGraph.extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) (N : ℕ) :
    ∃ a b : ℕ, N ≤ a ∧ a < b ∧
      (∃ ε : ℝ, QuadSupport (fun m => SimpleGraph.extremalNumber m H) ε a) ∧
      (∃ ε : ℝ, QuadSupport (fun m => SimpleGraph.extremalNumber m H) ε b) ∧
      (∀ m : ℕ, a < m → m < b → ∀ ε : ℝ,
        ¬ QuadSupport (fun k => SimpleGraph.extremalNumber k H) ε m) ∧
      (a : ℝ)^(2-α) ≤ 4*c*((b-a : ℕ) : ℝ)^3 :=
  consecutive_large_gaps (Erdos713Cloning.extremal_zero H) ha ha2 hc h N

#print axioms consecutive_sequence_of_cofinal
#print axioms consecutive_large_gaps
#print axioms extremal_consecutive_large_gaps
end Erdos713QuadraticSupportGapScale
