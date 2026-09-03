import FormalConjecturesUtil
import Submission.MergeBackward
import Submission.UniformOverlap

/-! Safe nonadjacent mergers on exact extremal hosts are exceptional.
This is a limitation on applying estimates restricted to individually safe mergers,
not a proof of rationality of extremal exponents. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713SafeMergeCounting
open Erdos713VertexMerging Erdos713MergeBackward Erdos713UniformOverlap
variable {V W : Type*}
set_option maxHeartbeats 2000000

/-- Ordered pairs of distinct nonadjacent vertices whose merger is H-free. -/
def SafePair (H : SimpleGraph W) (G : SimpleGraph V) (u v : V) : Prop :=
  u ≠ v ∧ ∃ hn : ¬ G.Adj u v, H.Free (merge G u v hn)

open scoped Classical in
noncomputable def safePairs [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) :
    Finset (V × V) := univ.filter (fun p => SafePair H G p.1 p.2)

lemma gap_le_overlap [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    {B : ℕ} (hgap : extremalNumber (Fintype.card V-1) H+B ≤ Nat.card G.edgeSet)
    {u v : V} (hs : SafePair H G u v) : B ≤ Nat.card (G.commonNeighbors u v) := by
  obtain ⟨hne,hn,hf⟩ := hs
  have hb := safe_merge_bound H G hne hn hf
  omega

open scoped Classical in
lemma safePairs_budget [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    {B : ℕ} (hgap : extremalNumber (Fintype.card V-1) H+B ≤ Nat.card G.edgeSet) :
    B*(safePairs H G).card ≤ ∑ v : V, G.degree v ^ 2 := by
  classical
  have hb := sum_le_sum (s := safePairs H G) (fun p hp =>
    gap_le_overlap H G hgap (mem_filter.mp hp).2)
  have ht := sum_le_sum_of_subset_of_nonneg
    (f := fun p : V × V => Nat.card (G.commonNeighbors p.1 p.2))
    (subset_univ (safePairs H G)) (fun _ _ _ => Nat.zero_le _)
  have he : (∑ p : V × V, Nat.card (G.commonNeighbors p.1 p.2)) =
      ∑ v : V, G.degree v ^ 2 := by
    simpa only [Nat.card_eq_fintype_card] using Erdos713DRC.sum_common_eq_sum_degree_sq G
  simp only [sum_const,smul_eq_mul] at hb
  nlinarith only [hb,ht,he]

open scoped Classical in
lemma safePairs_budget_of_degree_cap [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    {B D : ℕ} (hgap : extremalNumber (Fintype.card V-1) H+B ≤ Nat.card G.edgeSet)
    (hD : ∀ v, G.degree v ≤ D) :
    B*(safePairs H G).card ≤ Fintype.card V*D^2 := by
  calc
    _ ≤ ∑ v : V, G.degree v ^ 2 := safePairs_budget H G hgap
    _ ≤ ∑ _v : V, D^2 := sum_le_sum (fun v _ => Nat.pow_le_pow_left (hD v) 2)
    _ = _ := by simp

lemma safePairs_subset_highOverlap [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H) {t : ℝ}
    (hgap : t < (extremalNumber (Fintype.card V) H : ℝ)-
      (extremalNumber (Fintype.card V-1) H : ℝ)) :
    safePairs H G ⊆ highOverlap G t := by
  classical
  intro p hp
  obtain ⟨hne,hn,hf⟩ := (mem_filter.mp hp).2
  have hb := safe_merge_bound H G hne hn hf
  rw [he] at hb
  have hbR : (extremalNumber (Fintype.card V) H : ℝ) ≤
      (extremalNumber (Fintype.card V-1) H : ℝ)+
        (Nat.card (G.commonNeighbors p.1 p.2) : ℝ) := by exact_mod_cast hb
  exact mem_filter.mpr ⟨mem_univ _, by linarith⟩

/-- At exact orders having a positive degree-scale backward gap, only o(n²)
ordered pairs are individually safe. No maximum-degree bound is needed. -/
theorem eventually_few_safePairs (H : SimpleGraph W) {α c a ε : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c) (ha0 : 0 < a)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = n → H.Free G → Nat.card G.edgeSet = extremalNumber n H →
      a*(n : ℝ)^(α-1) < (extremalNumber n H : ℝ)-(extremalNumber (n-1) H : ℝ) →
      ((safePairs H G).card : ℝ) ≤ ε*(n : ℝ)^2 := by
  filter_upwards [few_high_overlaps H ha ha2 hc ha0 h hε] with n hn
  intro V instV G hcard hf he hgap
  have hs := safePairs_subset_highOverlap H G (t := a*(n : ℝ)^(α-1))
    (by simpa only [hcard] using he) (by simpa only [hcard] using hgap)
  exact (Nat.cast_le.mpr (card_le_card hs)).trans (hn V G hcard hf)

#print axioms safePairs_budget_of_degree_cap
#print axioms eventually_few_safePairs
end Erdos713SafeMergeCounting
