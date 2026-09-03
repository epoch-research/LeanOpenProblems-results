import FormalConjecturesUtil
import Submission.Verified

/-! Sampling a set that avoids directed blocking sets of uniformly bounded size. -/

open Filter SimpleGraph Asymptotics

namespace Erdos713Blocking
open Finset

theorem card_fixed_pattern {V K : Type*} [Fintype V] [Fintype K] (S : Set V) (p : V → K) :
    Nat.card {f : V → K // ∀ v ∈ S, f v = p v} =
      Nat.card K ^ (Nat.card V - Nat.card S) := by
  classical
  let e : {f : V → K // ∀ v ∈ S, f v = p v} ≃ (↥(Sᶜ) → K) :=
    { toFun := fun f i => f.val i.val
      invFun := fun f => ⟨fun i => if h : i ∈ S then p i else f ⟨i, h⟩, by
        intro i hi
        simp only [dif_pos hi]⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext i
        by_cases hi : i ∈ S
        · simpa only [dif_pos hi] using (f.prop i hi).symm
        · simp only [dif_neg hi]
      right_inv := by
        intro f
        funext i
        simp only [dif_neg i.prop] }
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_compl_set]

def selected {V : Type*} (B : V → Finset V) (σ : V → Bool) (v : V) : Prop :=
  σ v = true ∧ ∀ w ∈ B v, σ w = false

def keep {V : Type*} (G : SimpleGraph V) (B : V → Finset V) (σ : V → Bool) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ selected B σ u ∧ selected B σ v
  symm _ _ huv := ⟨huv.1.symm, huv.2.2, huv.2.1⟩
  loopless u huv := G.loopless u huv.1

theorem keep_le {V : Type*} (G : SimpleGraph V) (B : V → Finset V) (σ : V → Bool) : keep G B σ ≤ G :=
  fun _ _ huv => huv.1

open scoped Classical in
set_option maxHeartbeats 1000000 in
theorem pair_survival {V : Type*} [Fintype V] (B : V → Finset V) (k : ℕ)
    (hk : ∀ v, (B v).card ≤ k) {u v : V}
    (huu : u ∉ B u) (hvv : v ∉ B v) (huv : v ∉ B u) (hvu : u ∉ B v) :
    Fintype.card (V → Bool) ≤ 2 ^ (2 * k + 2) *
      Nat.card {σ : V → Bool // selected B σ u ∧ selected B σ v} := by
  classical
  let T : Finset V := insert u (insert v (B u ∪ B v))
  let p : V → Bool := fun z => if z = u ∨ z = v then true else false
  have hT : T.card ≤ 2 * k + 2 := by
    have hh := card_insert_le u (insert v (B u ∪ B v))
    have hi := card_insert_le v (B u ∪ B v)
    have hj := card_union_le (B u) (B v)
    dsimp only [T]
    have hku := hk u
    have hkv := hk v
    omega
  have hTn : T.card ≤ Fintype.card V := card_le_univ _
  have hp : ∀ σ : V → Bool, (∀ z ∈ T, σ z = p z) → selected B σ u ∧ selected B σ v := by
    intro σ hσ
    have hu : σ u = true := by simpa only [p, if_pos (Or.inl rfl)] using hσ u (by simp [T])
    have hv : σ v = true := by simpa only [p, if_pos (Or.inr rfl)] using hσ v (by simp [T])
    refine ⟨⟨hu, ?_⟩, ⟨hv, ?_⟩⟩
    · intro z hz
      have hzu : z ≠ u := fun he => huu (he ▸ hz)
      have hzv : z ≠ v := fun he => huv (he ▸ hz)
      simpa only [p, hzu, hzv, or_self, if_false] using hσ z (by simp [T, hz])
    · intro z hz
      have hzu : z ≠ u := fun he => hvu (he ▸ hz)
      have hzv : z ≠ v := fun he => hvv (he ▸ hz)
      simpa only [p, hzu, hzv, or_self, if_false] using hσ z (by simp [T, hz])
  have hcard : 2 ^ (Fintype.card V - T.card) ≤
      Nat.card {σ : V → Bool // selected B σ u ∧ selected B σ v} := by
    let e : {σ : V → Bool // ∀ z ∈ T, σ z = p z} ↪
        {σ : V → Bool // selected B σ u ∧ selected B σ v} :=
      ⟨fun σ => ⟨σ.val, hp σ.val σ.prop⟩, by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun σ : {σ : V → Bool // selected B σ u ∧ selected B σ v} => σ.val) h⟩
    have hh := Fintype.card_le_of_embedding e
    simp only [Fintype.card_eq_nat_card] at hh
    have hf : Nat.card {σ : V → Bool // ∀ z ∈ T, σ z = p z} =
        2 ^ (Fintype.card V - T.card) := by
      have hfixed := card_fixed_pattern (T : Set V) p
      rw [Nat.card_coe_set_eq, Set.ncard_coe_finset] at hfixed
      simpa only [mem_coe, Nat.card_eq_fintype_card, Fintype.card_bool] using hfixed
    exact hf ▸ hh
  calc
    Fintype.card (V → Bool) = 2 ^ Fintype.card V := by simp
    _ = 2 ^ T.card * 2 ^ (Fintype.card V - T.card) := by
      rw [← pow_add, Nat.add_sub_of_le hTn]
    _ ≤ 2 ^ (2 * k + 2) * Nat.card {σ : V → Bool // selected B σ u ∧ selected B σ v} :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hT) hcard

open scoped Classical in
set_option maxHeartbeats 2000000 in
theorem edges_le_of_keep_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (B : V → Finset V) (k M : ℕ) (hb : ∀ v, v ∉ B v) (hk : ∀ v, (B v).card ≤ k)
    (hM : ∀ σ : V → Bool, (keep G B σ).edgeFinset.card ≤ M) :
    G.edgeFinset.card ≤ 2 ^ (2 * k + 2) * M + k * Fintype.card V := by
  classical
  let D : Finset (Sym2 V) := univ.biUnion (fun u => (B u).image (fun v => s(u,v)))
  let E : Finset (Sym2 V) := G.edgeFinset \ D
  let C := 2 ^ (2 * k + 2)
  let A := Fintype.card (V → Bool)
  let rel : (V → Bool) → Sym2 V → Prop := fun σ e => e ∈ (keep G B σ).edgeFinset
  have hD : D.card ≤ k * Fintype.card V := by
    calc
      D.card ≤ ∑ u, ((B u).image (fun v => s(u,v))).card := card_biUnion_le
      _ ≤ ∑ u : V, k := sum_le_sum fun u _ => card_image_le.trans (hk u)
      _ = _ := by simp [Nat.mul_comm]
  have hBelow : ∀ e ∈ E, A ≤ C * ((univ : Finset (V → Bool)).bipartiteBelow rel e).card := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have hgood : s(u,v) ∈ G.edgeFinset ∧ s(u,v) ∉ D := mem_sdiff.mp he
      have hadj : G.Adj u v := by simpa using hgood.1
      have huv : v ∉ B u := by
        intro hh
        apply hgood.2
        exact mem_biUnion.mpr ⟨u, mem_univ _, mem_image.mpr ⟨v, hh, rfl⟩⟩
      have hvu : u ∉ B v := by
        intro hh
        apply hgood.2
        exact mem_biUnion.mpr ⟨v, mem_univ _, mem_image.mpr ⟨u, hh, by simp⟩⟩
      have hrel (σ : V → Bool) : rel σ s(u,v) ↔ selected B σ u ∧ selected B σ v := by
        change (s(u,v) ∈ (keep G B σ).edgeFinset) ↔ _
        simp only [mem_edgeFinset, mem_edgeSet, keep, hadj, true_and]
      have hh := pair_survival B k hk (hb u) (hb v) huv hvu
      simpa only [A, C, Nat.card_eq_fintype_card, Fintype.card_subtype, bipartiteBelow, hrel] using hh
  have hAbove (σ : V → Bool) : (E.bipartiteAbove rel σ).card ≤ M := by
    apply (card_le_card (show E.bipartiteAbove rel σ ⊆ (keep G B σ).edgeFinset from ?_)).trans (hM σ)
    intro e he
    exact (mem_filter.mp he).2
  have hsum := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := rel) (s := (univ : Finset (V → Bool))) (t := E)
  have hCount : E.card * A ≤ C * (A * M) := by
    calc
      E.card * A = ∑ _e ∈ E, A := by simp
      _ ≤ ∑ e ∈ E, C * ((univ : Finset (V → Bool)).bipartiteBelow rel e).card :=
        sum_le_sum hBelow
      _ = C * ∑ σ : V → Bool, (E.bipartiteAbove rel σ).card := by
        rw [← mul_sum, ← hsum]
      _ ≤ C * ∑ _σ : V → Bool, M := Nat.mul_le_mul_left C (sum_le_sum fun σ _ => hAbove σ)
      _ = C * (A * M) := by simp [A]
  have hA : 0 < A := Fintype.card_pos
  have hE : E.card ≤ C * M := Nat.le_of_mul_le_mul_left
    (show A * E.card ≤ A * (C * M) by nlinarith only [hCount]) hA
  exact (card_le_card_sdiff_add_card (s := G.edgeFinset) (t := D)).trans (Nat.add_le_add hE hD)

#print axioms pair_survival
#print axioms edges_le_of_keep_bound

end Erdos713Blocking
