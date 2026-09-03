import Submission.GreedyRecordedCrossing
import Submission.FiniteExcursion

/-!
Critical-excursion bounds for recorded degrees, allowing self-correcting
mean control only inside a critical interval. These theorems retain all
quantitative hypotheses; they do not provide a suitable guard or profile.
-/
namespace Erdos773.GreedyRecordedExcursion
open Finset GreedyHypergraphState StoppedGreedyMoments
open FiniteKernelCrossing GreedyTrackedState GreedyTrackedMoments GreedyRecordedCrossing
open GreedyLinearLocal
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Drift control is needed only after the signed profile error reaches c. -/
structure CriticalControl (H : Finset (Finset α)) (L T : ℕ)
    (G : ℕ → Tracked H T → Prop) (f : ℕ → ℝ) (j : Fin 3) (u : α)
    (sign b c : ℝ) (B v : ℕ → ℝ) : Prop extends MomentControl H L T G f j u sign b B v where
  local_drift : ∀ n < T, ∀ s, Ready H L s.chosen → s.running = true → G n s →
    c ≤ sign*error f s j u →
    sign*(survivalDrift H s.chosen (j.val+2) u-
      (safeChoices H s.chosen u).card*(f (n+1)-f n)) ≤ 0

variable {H : Finset (Finset α)} {L T : ℕ} {G : ℕ → Tracked H T → Prop}
variable {f : ℕ → ℝ} {j : Fin 3} {u : α} {sign b c : ℝ} {B v : ℕ → ℝ}

lemma CriticalControl.drift (hc : CriticalControl H L T G f j u sign b c B v)
    {n : ℕ} (hn : n < T) (s : Tracked H T) (hx : c ≤ sign*error f s j u) :
    (GreedyTrackedState.kernel H L T G n).avg
      (fun z => sign*(error f z j u-error f s j u)) s ≤ 0 := by
  rw [Kernel.avg_mul]
  by_cases hr : Ready H L s.chosen
  · by_cases hg : s.running = true ∧ G n s
    · rw [error_drift (hc.valid n hn s hg.2) hn hr hg,← mul_div_assoc]
      exact div_nonpos_of_nonpos_of_nonneg (hc.local_drift n hn s hr hg.1 hg.2 hx) (by positivity)
    · rw [error_drift_frozen hg,mul_zero]
  · rw [kernel_avg_not_ready G s hr,sub_self,mul_zero]

/-- The critical interval has width a; its entrance overshoot is at most b.
    The T+1 factor covers all possible excursion entrance times. -/
theorem first_crossing (hc : CriticalControl H L T G f j u sign b c B v)
    (a : ℝ) (hb : 0 < b) (ha : b < a)
    (hstart : sign*error f (initial H T) j u ≤ c) :
    hit (GreedyTrackedState.kernel H L T G)
      (fun _ s => a ≤ sign*error f s j u-c) 0 T (initial H T) ≤
        ((T:ℝ)+1)*Real.exp (-((a-b)^2)/(4*((∑ n ∈ range T, v n)+b*(a-b)))) := by
  let X : ℕ → Tracked H T → ℝ := fun _ s => sign*error f s j u-c
  have hdelta (n : ℕ) (s z : Tracked H T) :
      X (n+1) z-X n s = sign*(error f z j u-error f s j u) := by dsimp [X]; ring
  apply FiniteExcursion.first_crossing_bound (GreedyTrackedState.kernel H L T G)
    X v T (initial H T) b a hb ha hc.variance_nonneg
  · exact sub_nonpos.mpr hstart
  · intro n hn s z hz
    rw [hdelta n]
    exact hc.toMomentControl.increment hn hz
  · intro n hn s hx
    simp only [hdelta]
    exact hc.drift hn s (sub_nonneg.mp hx)
  · intro n hn s hx
    simp only [hdelta]
    exact hc.toMomentControl.second_moment hn s

/-- Parameters of one signed critical-interval test. -/
structure Test (α : Type*) where
  profile : ℕ → ℝ
  degreeIndex : Fin 3
  vertex : α
  sign : ℝ
  incrementCap : ℝ
  level : ℝ
  width : ℝ
  rawCap : ℕ → ℝ
  variance : ℕ → ℝ

namespace Test
variable (t : Test α)

def event {H : Finset (Finset α)} {T : ℕ} (_n : ℕ) (s : Tracked H T) : Prop :=
  t.width ≤ t.sign*error t.profile s t.degreeIndex t.vertex-t.level

def cost (T : ℕ) : ℝ := ((T:ℝ)+1)*Real.exp
  (-((t.width-t.incrementCap)^2)/
    (4*((∑ n ∈ range T, t.variance n)+t.incrementCap*(t.width-t.incrementCap))))

structure Admissible (H : Finset (Finset α)) (L T : ℕ)
    (G : ℕ → Tracked H T → Prop) : Prop where
  control : CriticalControl H L T G t.profile t.degreeIndex t.vertex t.sign
    t.incrementCap t.level t.rawCap t.variance
  increment_pos : 0 < t.incrementCap
  width_gt : t.incrementCap < t.width
  start_le : t.sign*error t.profile (initial H T) t.degreeIndex t.vertex ≤ t.level

lemma hit_le_cost (ht : t.Admissible H L T G) :
    hit (GreedyTrackedState.kernel H L T G) t.event 0 T (initial H T) ≤ t.cost T :=
  first_crossing ht.control t.width ht.increment_pos ht.width_gt ht.start_le

end Test

/-- Several degree/profile tests share one actual kernel and one avoiding
    path. The probability bound is summed, not multiplied. -/
theorem simultaneous_path (tests : Finset (Test α))
    (h : ∀ t ∈ tests, t.Admissible H L T G)
    (hcost : (∑ t ∈ tests, t.cost T) < 1) :
    GoodPath (GreedyTrackedState.kernel H L T G)
      (fun n s => ∃ t ∈ tests, t.event n s) 0 T (initial H T) := by
  exact simultaneous_goodPath (GreedyTrackedState.kernel H L T G) tests (fun t n s => t.event n s)
    (fun t => t.cost T) 0 T (initial H T) (fun t ht => t.hit_le_cost (h t ht)) hcost

/-- Degree excursions and an auxiliary carrier error event may be avoided
    simultaneously. The auxiliary estimate may come from the earlier
    all-subset common-neighbor or duplicate-error certificates. -/
theorem simultaneous_with_auxiliary (tests : Finset (Test α))
    (h : ∀ t ∈ tests, t.Admissible H L T G)
    (P : ℕ → Tracked H T → Prop) (ρ : ℝ)
    (hP : hit (GreedyTrackedState.kernel H L T G) P 0 T (initial H T) ≤ ρ)
    (hcost : ρ+(∑ t ∈ tests, t.cost T) < 1) :
    GoodPath (GreedyTrackedState.kernel H L T G)
      (fun n s => P n s ∨ ∃ t ∈ tests, t.event n s) 0 T (initial H T) := by
  apply goodPath_of_hit_lt_one
  have hu := hit_union_bound (GreedyTrackedState.kernel H L T G) tests
    (fun t n s => t.event n s) 0 T (initial H T)
  have hu' : hit (GreedyTrackedState.kernel H L T G)
      (fun n s => ∃ t ∈ tests, t.event n s) 0 T (initial H T) ≤ ∑ t ∈ tests, t.cost T :=
    hu.trans (sum_le_sum (fun t ht => t.hit_le_cost (h t ht)))
  exact (hit_or_bound (GreedyTrackedState.kernel H L T G) P
    (fun n s => ∃ t ∈ tests, t.event n s) 0 T (initial H T)).trans_lt
      ((add_le_add hP hu').trans_lt hcost)

/-- Conditional full-run certificate. The guard and final readiness
    implications must be established separately from the concentration
    estimates; the theorem does not assert them for any square hypergraph. -/
theorem simultaneous_full_run (hH : ∀ e ∈ H, e.Nonempty) (hL : 0 < L)
    (tests : Finset (Test α)) (h : ∀ t ∈ tests, t.Admissible H L T G)
    (hcost : (∑ t ∈ tests, t.cost T) < 1)
    (hguard : ∀ k < T, ∀ s, GreedyTrackedState.Reach H L T G k s → s.running = true →
      (∀ t ∈ tests, ¬t.event k s) → G k s)
    (hready : ∀ s, GreedyTrackedState.Reach H L T G T s → s.running = true →
      (∀ t ∈ tests, ¬t.event T s) → Ready H L s.chosen) :
    ∃ s, GreedyTrackedState.Reach H L T G T s ∧ s.running = true ∧ Valid H L T s ∧
      Independent H s.chosen ∧ s.chosen.card = T ∧ (∀ t ∈ tests, ¬t.event T s) := by
  have hp := simultaneous_path tests h hcost
  obtain ⟨s,hs,hr,hv,hi,hcard,hp⟩ := goodPath_full_run H hH L T hL G
    (fun n s => ∃ t ∈ tests, t.event n s)
    (fun k hk s hs hr hp => hguard k hk s hs hr (by simpa only [not_exists,not_and] using hp))
    (fun s hs hr hp => hready s hs hr (by simpa only [not_exists,not_and] using hp)) hp
  exact ⟨s,hs,hr,hv,hi,hcard,by simpa only [not_exists,not_and] using hp⟩

#print axioms CriticalControl.drift
#print axioms first_crossing
#print axioms Test.hit_le_cost
#print axioms simultaneous_with_auxiliary
#print axioms simultaneous_path
#print axioms simultaneous_full_run
end
end Erdos773.GreedyRecordedExcursion
