import Submission.PredecessorPacketRepairExplore

/-! Candidate-degree bounds for predecessor repairs. Deleted-point hits use
the ordinary sum-representation function, not unrestricted difference counts. -/
namespace Erdos66PredecessorCandidateDegree
open AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66PredecessorCell
  Erdos66PredecessorPacketRepair Erdos66ReflectionRoundingPatch
open scoped Classical
set_option maxHeartbeats 2200000
variable {α γ : Type*} [Fintype α]

lemma bounded_preimage_card (f : α → γ) (H : ℕ)
    (hf : ∀ r, (Finset.univ.filter (fun a ↦ f a = r)).card ≤ H) (T : Finset γ) :
    (Finset.univ.filter (fun a ↦ f a ∈ T)).card ≤ H*T.card := by
  apply Finset.card_le_mul_card_image_of_maps_to
    (f := f) (fun a ha ↦ (Finset.mem_filter.mp ha).2) H
  intro r hr
  apply le_trans (Finset.card_le_card ?_) (hf r)
  intro a ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩

lemma predecessor_hit_card (A : Finset ℕ) (f : α → ℕ) (H : ℕ)
    (hmem : ∀ a, predecessor (A : Set ℕ) (f a) ∈ A)
    (hf : ∀ r, (Finset.univ.filter (fun a ↦ predecessor (A : Set ℕ) (f a) = r)).card ≤ H)
    (z : ℕ) :
    (Finset.univ.filter (fun a ↦ predecessor (A : Set ℕ) (f a) ≤ z ∧
      z-predecessor (A : Set ℕ) (f a) ∈ A)).card ≤ H*sumRep (A : Set ℕ) z := by
  let T := A.filter (fun r ↦ r ≤ z ∧ z-r ∈ A)
  have hh := bounded_preimage_card (fun a ↦ predecessor (A : Set ℕ) (f a)) H (by intro r; convert hf r using 1 <;> congr 2) T
  have he : (Finset.univ.filter (fun a ↦ predecessor (A : Set ℕ) (f a) ∈ T)) =
      Finset.univ.filter (fun a ↦ predecessor (A : Set ℕ) (f a) ≤ z ∧
        z-predecessor (A : Set ℕ) (f a) ∈ A) := by
    ext a
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, hmem a]
  have hT : T.card = sumRep (A : Set ℕ) z := by rw [← pairs_self, pairs_eq_filter]
  rw [hT] at hh
  convert hh using 1
  congr 1
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, T, hmem a]

lemma interval_old_card (A : Set ℕ) (f : α → ℕ) (hf : Function.Injective f) (L W : ℕ)
    (hb : ∀ a, L ≤ f a ∧ f a < L+W) :
    (Finset.univ.filter (fun a ↦ f a ∈ A)).card ≤ (intervalPart A L (L+W)).card := by
  apply Finset.card_le_card_of_injOn f
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (hb a), (Finset.mem_filter.mp ha).2⟩
  · exact hf.injOn

lemma interval_hit_card (A : Set ℕ) (f : α → ℕ) (hf : Function.Injective f) (L W z : ℕ)
    (hb : ∀ a, L ≤ f a ∧ f a < L+W) :
    (Finset.univ.filter (fun a ↦ f a ≤ z ∧ z-f a ∈ A)).card ≤
      (intervalPart A (z+1-(L+W)) (z+1-(L+W)+W)).card := by
  apply Finset.card_le_card_of_injOn (fun a ↦ z-f a)
  · intro a ha
    obtain ⟨_, haz, haA⟩ := Finset.mem_filter.mp ha
    obtain ⟨hal, hau⟩ := hb a
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, haA⟩
  · intro a ha b hb he
    have ha' := (Finset.mem_filter.mp ha).2.1
    have hb' := (Finset.mem_filter.mp hb).2.1
    dsimp only at he
    exact hf (by omega)

lemma bool_union_card_bound (P Q : Bool → α → Prop) (K L : ℝ)
    (hP : ∀ b, ((Finset.univ.filter (P b)).card : ℝ) ≤ K)
    (hQ : ∀ b, ((Finset.univ.filter (Q b)).card : ℝ) ≤ L) :
    ((Finset.univ.filter (fun a ↦ ∃ b, P b a ∨ Q b a)).card : ℝ) ≤ 2*K+2*L := by
  let U : Bool → Finset α := fun b ↦ (Finset.univ.filter (P b)) ∪ (Finset.univ.filter (Q b))
  have he : Finset.univ.filter (fun a ↦ ∃ b, P b a ∨ Q b a) = Finset.univ.biUnion U := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, U,
      Finset.mem_union]
  rw [he]
  have hh := Finset.card_biUnion_le (s := Finset.univ) (t := U)
  have hh' : ((Finset.univ.biUnion U).card : ℝ) ≤ ∑ b : Bool, ((U b).card : ℝ) := by
    exact_mod_cast hh
  apply hh'.trans
  have hsum := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset Bool)) ↦
    show ((U b).card : ℝ) ≤ K+L from by
      have hc : ((U b).card : ℝ) ≤ (Finset.univ.filter (P b)).card + (Finset.univ.filter (Q b)).card :=
        by exact_mod_cast Finset.card_union_le (Finset.univ.filter (P b)) (Finset.univ.filter (Q b))
      linarith [hP b, hQ b])
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, Nat.cast_ofNat,
    nsmul_eq_mul, mul_add] using hsum

/-- A pointwise cell gap bounds the number of choices in each predecessor
fiber, provided the endpoint map itself is injective. -/
lemma endpoint_fiber_bound (A : Set ℕ) (f : α → ℕ) (hf : Function.Injective f)
    (H : ℕ) (hgap : ∀ a, f a < predecessor A (f a)+H) (r : ℕ) :
    (Finset.univ.filter (fun a ↦ predecessor A (f a) = r)).card ≤ H := by
  have hc : (Finset.univ.filter (fun a ↦ predecessor A (f a) = r)).card ≤
      (Finset.Ico r (r+H)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro a ha
      have he := (Finset.mem_filter.mp ha).2
      have hl := predecessor_le A (f a)
      have hh := hgap a
      change f a ∈ Finset.Ico r (r+H)
      rw [Finset.mem_Ico]
      constructor <;> omega
    · exact hf.injOn
  simpa only [Nat.card_Ico, Nat.add_sub_cancel_left] using hc

/-- Both forbidden and tested-hit sets have the same type of bound: local
occupancy for inserted points and H times the sum-representation count for
deleted points. No long-range difference-correlation hypothesis is used. -/
theorem predecessor_candidate_degrees (A : Finset ℕ) (n : ℕ) (x : α → ℕ)
    (H W : ℕ) (start : Bool → ℕ) (V : ℝ)
    (hinj : ∀ b, Function.Injective (endpoint n x b))
    (hwindow : ∀ b a, start b ≤ endpoint n x b a ∧ endpoint n x b a < start b+W)
    (hlocal : ∀ L, ((intervalPart (A : Set ℕ) L (L+W)).card : ℝ) ≤ V)
    (hmem : ∀ b a, predecessor (A : Set ℕ) (endpoint n x b a) ∈ A)
    (hgap : ∀ b a, endpoint n x b a < predecessor (A : Set ℕ) (endpoint n x b a)+H) :
    ((badChoices A n x).card : ℝ) ≤ 2*V+2*H*sumRep (A : Set ℕ) n ∧
      ∀ z, ((swapHits A n x z).card : ℝ) ≤ 2*V+2*H*sumRep (A : Set ℕ) z := by
  have hfiber b r := endpoint_fiber_bound (A : Set ℕ) (endpoint n x b) (hinj b) H (hgap b) r
  have hdel (b : Bool) (z : ℕ) :
      ((Finset.univ.filter (fun a ↦ predecessor (A : Set ℕ) (endpoint n x b a) ≤ z ∧
        z-predecessor (A : Set ℕ) (endpoint n x b a) ∈ A)).card : ℝ) ≤ H*sumRep (A : Set ℕ) z := by
    exact_mod_cast predecessor_hit_card A (endpoint n x b) H (hmem b) (hfiber b) z
  constructor
  · change ((Finset.univ.filter (fun a ↦ ∃ b, endpoint n x b a ∈ A ∨ _)).card : ℝ) ≤ _
    have hh := bool_union_card_bound
      (fun b a ↦ endpoint n x b a ∈ A)
      (fun b a ↦ predecessor (A : Set ℕ) (endpoint n x b a) ≤ n ∧
        n-predecessor (A : Set ℕ) (endpoint n x b a) ∈ A)
      V (H*sumRep (A : Set ℕ) n) (fun b ↦ ?_) (by intro b; convert hdel b n using 1 <;> congr 3)
    · convert hh using 1
      · congr 3
      · ring
    · have hc := interval_old_card (A : Set ℕ) (endpoint n x b) (hinj b) (start b) W (hwindow b)
      have hc' : ((Finset.univ.filter (fun a ↦ endpoint n x b a ∈ A)).card : ℝ) ≤
          (intervalPart (A : Set ℕ) (start b) (start b+W)).card := by exact_mod_cast hc
      convert hc'.trans (hlocal (start b)) using 1 <;> congr 3
  · intro z
    change ((Finset.univ.filter (fun a ↦ ∃ b, (endpoint n x b a ≤ z ∧ z-endpoint n x b a ∈ A) ∨ _)).card : ℝ) ≤ _
    have hh := bool_union_card_bound
      (fun b a ↦ endpoint n x b a ≤ z ∧ z-endpoint n x b a ∈ A)
      (fun b a ↦ predecessor (A : Set ℕ) (endpoint n x b a) ≤ z ∧
        z-predecessor (A : Set ℕ) (endpoint n x b a) ∈ A)
      V (H*sumRep (A : Set ℕ) z) (fun b ↦ ?_) (by intro b; convert hdel b z using 1 <;> congr 3)
    · convert hh using 1
      · congr 3
      · ring
    · have hc := interval_hit_card (A : Set ℕ) (endpoint n x b) (hinj b) (start b) W z (hwindow b)
      have hc' : ((Finset.univ.filter (fun a ↦ endpoint n x b a ≤ z ∧ z-endpoint n x b a ∈ A)).card : ℝ) ≤
          (intervalPart (A : Set ℕ) (z+1-(start b+W)) (z+1-(start b+W)+W)).card := by exact_mod_cast hc
      convert hc'.trans (hlocal _) using 1 <;> congr 3

end Erdos66PredecessorCandidateDegree
