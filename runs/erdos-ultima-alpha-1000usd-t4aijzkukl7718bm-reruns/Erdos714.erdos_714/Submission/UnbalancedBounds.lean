import Submission.Packing

/-!
Ordered-star bounds for unbalanced bipartite graphs. These are upper bounds
used to test candidate constructions, not a resolution of Erdős 714.
-/

noncomputable section
open Finset SimpleGraph Classical
set_option maxHeartbeats 2000000

namespace Erdos714Unbalanced
open Erdos714Packing
variable {A B : Type*} [Fintype A] [Fintype B]

def starEquiv (S : A → Finset B) (r : ℕ) :
    (Σ a : A, Fin r ↪ S a) ≃
      (Σ f : Fin r ↪ B, {a : A // a ∈ common (dual S) f}) where
  toFun p := ⟨⟨fun i => (p.2 i).val, fun i j h => p.2.injective (Subtype.ext h)⟩,
    ⟨p.1, by simp only [mem_common, mem_dual]; exact fun i => (p.2 i).property⟩⟩
  invFun p := ⟨p.2.val, ⟨fun i => ⟨p.1 i, by
    have h := (mem_common (dual S) p.1 p.2.val).mp p.2.property i
    exact (mem_dual S p.2.val (p.1 i)).mp h⟩,
    fun i j h => p.1.injective (congrArg Subtype.val h)⟩⟩
  left_inv p := by rcases p with ⟨a,f⟩; rfl
  right_inv p := by rcases p with ⟨f,a,h⟩; rfl

lemma star_bound (S : A → Finset B) {r : ℕ} (hr : 0 < r)
    (hS : (completeBipartiteGraph (Fin r) (Fin r)).Free (incidence S)) :
    ∑ a, (S a).card.descFactorial r ≤ (r-1) * (Fintype.card B).descFactorial r := by
  have hc := (common_card_dual_iff S hr).mp ((free_iff_common_card S hr).mp hS)
  have hcount := Fintype.card_congr (starEquiv S r)
  simp only [Fintype.card_sigma, Fintype.card_embedding_eq, Fintype.card_fin,
    Fintype.card_coe] at hcount
  rw [hcount]
  calc
    _ ≤ ∑ _f : Fin r ↪ B, (r-1) := sum_le_sum (fun f _ => by have := hc f; omega)
    _ = _ := by simp [Nat.mul_comm]

/-- The exponent of the number of columns is r, not 2r-1. -/
theorem power_bound (S : A → Finset B) {r : ℕ} (hr : 1 ≤ r)
    (hS : (completeBipartiteGraph (Fin r) (Fin r)).Free (incidence S)) :
    ((∑ a, (S a).card) - (r-1)*Fintype.card A)^r ≤
      (r-1)*Fintype.card A^(r-1)*Fintype.card B^r := by
  have hs : (∑ a, (S a).card) ≤ (∑ a, ((S a).card+1-r)) + (r-1)*Fintype.card A := by
    calc
      _ ≤ ∑ a, ((S a).card+1-r + (r-1)) := sum_le_sum (fun a _ => by omega)
      _ = _ := by rw [sum_add_distrib]; simp [Nat.mul_comm]
  have hs' : (∑ a, (S a).card) - (r-1)*Fintype.card A ≤
      ∑ a, ((S a).card+1-r) := by omega
  have hp := pow_sum_le_card_mul_sum_pow (s := (univ : Finset A))
    (f := fun a => (S a).card+1-r) (by intros; omega) (r-1)
  rw [Nat.sub_add_cancel hr, card_univ] at hp
  have htrunc : (∑ a, ((S a).card+1-r)^r) ≤ (r-1)*Fintype.card B^r := by
    calc
      _ ≤ ∑ a, (S a).card.descFactorial r := sum_le_sum (fun a _ => Nat.pow_sub_le_descFactorial _ _)
      _ ≤ (r-1)*(Fintype.card B).descFactorial r := star_bound S (by omega) hS
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow _ _)
  calc
    _ ≤ (∑ a, ((S a).card+1-r))^r := Nat.pow_le_pow_left hs' r
    _ ≤ Fintype.card A^(r-1) * ∑ a, ((S a).card+1-r)^r := hp
    _ ≤ Fintype.card A^(r-1) * ((r-1)*Fintype.card B^r) := Nat.mul_le_mul_left _ htrunc
    _ = _ := by ring

/-- A fourth-power bound with no truncated subtraction. -/
theorem fourth_power_bound (S : A → Finset B)
    (hS : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    (∑ a, (S a).card)^4 ≤
      24*Fintype.card A^3*Fintype.card B^4 + 648*Fintype.card A^4 := by
  let e := ∑ a, (S a).card
  let m := Fintype.card A
  have h := power_bound S (by decide : 1 ≤ 4) hS
  norm_num only at h
  have hs : e ≤ (e-3*m) + 3*m := by omega
  have hp := add_pow_le (Nat.zero_le (e-3*m)) (Nat.zero_le (3*m)) 4
  norm_num only at hp
  calc
    e^4 ≤ ((e-3*m)+3*m)^4 := Nat.pow_le_pow_left hs 4
    _ ≤ 8*((e-3*m)^4+(3*m)^4) := hp
    _ ≤ 8*(3*m^3*Fintype.card B^4+(3*m)^4) := Nat.mul_le_mul_left _ (Nat.add_le_add_right h _)
    _ = _ := by dsimp [m]; ring

/-- Recover any bipartite spanning subgraph as an indexed set system. -/
def neighborhoods (H : SimpleGraph (A ⊕ B)) (a : A) : Finset B :=
  univ.filter (fun b => H.Adj (.inl a) (.inr b))

omit [Fintype A] in
lemma incidence_neighborhoods (H : SimpleGraph (A ⊕ B))
    (hH : H ≤ completeBipartiteGraph A B) : incidence (neighborhoods H) = H := by
  ext v w
  cases v with
  | inl a =>
    cases w with
    | inl b =>
      have hn : ¬ H.Adj (.inl a) (.inl b) := fun h => by simpa using hH h
      simp [hn]
    | inr b => simp [neighborhoods]
  | inr b =>
    cases w with
    | inr c =>
      have hn : ¬ H.Adj (.inr b) (.inr c) := fun h => by simpa using hH h
      simp [hn]
    | inl a => simp [neighborhoods, H.adj_comm]

/-- The count is of undirected edges, each counted once. -/
theorem graph_fourth_power (H : SimpleGraph (A ⊕ B))
    (hH : H ≤ completeBipartiteGraph A B)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 24*Fintype.card A^3*Fintype.card B^4 + 648*Fintype.card A^4 := by
  have he := incidence_neighborhoods H hH
  rw [← he, incidence_edges]
  exact fourth_power_bound (neighborhoods H) (by rwa [he])

#print axioms star_bound
#print axioms power_bound
#print axioms fourth_power_bound
#print axioms graph_fourth_power
end Erdos714Unbalanced
