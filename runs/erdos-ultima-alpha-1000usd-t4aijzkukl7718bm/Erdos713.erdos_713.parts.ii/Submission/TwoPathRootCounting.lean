import FormalConjecturesUtil

/-! Counting endpoint quadruples of two walks. This is a finite counting
ingredient for a possible multiple-merger argument, not a rationality proof.
No claim here identifies this endpoint condition with a merger obstruction. -/
open SimpleGraph Finset
namespace Erdos713TwoPathRootCounting
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

open scoped Classical in
lemma sum_walks_from_le (G : SimpleGraph V) (D : ℕ)
    (hD : ∀ v, G.degree v ≤ D) (r : ℕ) (u : V) :
    (∑ v : V, (G.adjMatrix ℕ ^ r) u v) ≤ D^r := by
  classical
  induction r generalizing u with
  | zero => simp [Matrix.one_apply]
  | succ r ih =>
    simp_rw [pow_succ',G.adjMatrix_mul_apply]
    rw [Finset.sum_comm]
    calc
      (∑ w ∈ G.neighborFinset u, ∑ v : V, (G.adjMatrix ℕ ^ r) w v) ≤
          ∑ _w ∈ G.neighborFinset u, D^r := sum_le_sum (fun w _ => ih w)
      _ = G.degree u * D^r := by simp
      _ ≤ D * D^r := Nat.mul_le_mul_right _ (hD u)

open scoped Classical in
noncomputable def walkRoots (G : SimpleGraph V) (r : ℕ) : Finset (V × V) :=
  univ.filter (fun p => Nonempty {w : G.Walk p.1 p.2 // w.length = r})

open scoped Classical in
lemma card_walkRoots_le (G : SimpleGraph V) (D : ℕ)
    (hD : ∀ v, G.degree v ≤ D) (r : ℕ) :
    (walkRoots G r).card ≤ Fintype.card V * D^r := by
  classical
  have hp (p : V × V) (h : p ∈ walkRoots G r) : 1 ≤ (G.adjMatrix ℕ ^ r) p.1 p.2 := by
    rw [G.adjMatrix_pow_apply_eq_card_walk]
    exact Fintype.card_pos_iff.mpr (mem_filter.mp h).2
  calc
    (walkRoots G r).card = ∑ _p ∈ walkRoots G r, 1 := by simp
    _ ≤ ∑ p ∈ walkRoots G r, (G.adjMatrix ℕ ^ r) p.1 p.2 := sum_le_sum hp
    _ ≤ ∑ p : V × V, (G.adjMatrix ℕ ^ r) p.1 p.2 :=
      sum_le_sum_of_subset (subset_univ _)
    _ = ∑ u : V, ∑ v : V, (G.adjMatrix ℕ ^ r) u v := Fintype.sum_prod_type _
    _ ≤ ∑ _u : V, D^r := sum_le_sum (fun u _ => sum_walks_from_le G D hD r u)
    _ = Fintype.card V * D^r := by simp

def cross (p : (V × V) × (V × V)) : (V × V) × (V × V) :=
  ((p.1.1,p.2.1),(p.1.2,p.2.2))

def crossAlt (p : (V × V) × (V × V)) : (V × V) × (V × V) :=
  ((p.1.1,p.2.1),(p.2.2,p.1.2))

open scoped Classical in
noncomputable def twoPathRoots (G : SimpleGraph V) (r s : ℕ) :
    Finset ((V × V) × (V × V)) :=
  ((walkRoots G r ×ˢ walkRoots G s).image cross) ∪
    ((walkRoots G r ×ˢ walkRoots G s).image crossAlt)

open scoped Classical in
lemma card_twoPathRoots_le (G : SimpleGraph V) (D : ℕ)
    (hD : ∀ v, G.degree v ≤ D) (r s : ℕ) :
    (twoPathRoots G r s).card ≤ 2*(Fintype.card V)^2*D^(r+s) := by
  classical
  have hb : (walkRoots G r ×ˢ walkRoots G s).card ≤ (Fintype.card V)^2*D^(r+s) := by
    rw [card_product]
    calc
      _ ≤ (Fintype.card V*D^r)*(Fintype.card V*D^s) :=
        Nat.mul_le_mul (card_walkRoots_le G D hD r) (card_walkRoots_le G D hD s)
      _ = _ := by rw [pow_add]; ring
  dsimp only [twoPathRoots]
  have h1 := (card_image_le (f := @cross V) (s := walkRoots G r ×ˢ walkRoots G s)).trans hb
  have h2 := (card_image_le (f := @crossAlt V) (s := walkRoots G r ×ˢ walkRoots G s)).trans hb
  have hu := card_union_le ((walkRoots G r ×ˢ walkRoots G s).image cross)
    ((walkRoots G r ×ˢ walkRoots G s).image crossAlt)
  calc
    _ ≤ _ := hu
    _ ≤ (Fintype.card V)^2*D^(r+s)+(Fintype.card V)^2*D^(r+s) := Nat.add_le_add h1 h2
    _ = _ := by ring

open scoped Classical in
noncomputable def totalLengthRoots (G : SimpleGraph V) (ℓ : ℕ) :
    Finset ((V × V) × (V × V)) :=
  (range (ℓ+1)).biUnion (fun r => twoPathRoots G r (ℓ-r))

open scoped Classical in
lemma card_totalLengthRoots_le (G : SimpleGraph V) (D : ℕ)
    (hD : ∀ v, G.degree v ≤ D) (ℓ : ℕ) :
    (totalLengthRoots G ℓ).card ≤ 2*(ℓ+1)*(Fintype.card V)^2*D^ℓ := by
  classical
  calc
    (totalLengthRoots G ℓ).card ≤ ∑ r ∈ range (ℓ+1), (twoPathRoots G r (ℓ-r)).card :=
      card_biUnion_le
    _ ≤ ∑ _r ∈ range (ℓ+1), 2*(Fintype.card V)^2*D^ℓ := by
      apply sum_le_sum
      intro r hr
      have hr' : r ≤ ℓ := by simpa only [mem_range,Nat.lt_succ_iff] using hr
      simpa only [Nat.add_sub_of_le hr'] using card_twoPathRoots_le G D hD r (ℓ-r)
    _ = _ := by simp only [sum_const,card_range,Nat.nsmul_eq_mul]; ring

#print axioms card_walkRoots_le
#print axioms card_totalLengthRoots_le
end Erdos713TwoPathRootCounting
