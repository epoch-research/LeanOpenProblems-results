import Submission.VoltageFusion

/-!
Product-set Cayley hosts admit an unbalanced rectangle cover. This bounds
arbitrary edge restrictions, even in noncommutative groups; no Sidon or
unique-representation hypothesis is needed. It does not settle Erdős 714.
-/

noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 2000000

namespace Erdos714RectangleCover
open Erdos714Packing
variable {X Y I A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype I] [Fintype A] [Fintype B]

def block (S : X → Finset Y) (l : I → A ↪ X) (r : I → B ↪ Y)
    (i : I) (a : A) : Finset B := univ.filter (fun b => r i b ∈ S (l i a))

omit [Fintype X] [Fintype Y] [Fintype I] [Fintype A] in
lemma block_free (S : X → Finset Y) (l : I → A ↪ X) (r : I → B ↪ Y)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) (i : I) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence (block S l r i)) := by
  rw [free_iff_no_rectangle _ (by decide)] at hf ⊢
  intro f g h
  exact hf (f.trans (l i)) (g.trans (r i)) (fun a b => (mem_filter.mp (h a b)).2)

omit [Fintype Y] in
/-- Overlaps are allowed: this is a cover, not an assumed edge partition. -/
lemma edge_count_le (S : X → Finset Y) (l : I → A ↪ X) (r : I → B ↪ Y)
    (hc : ∀ x y, y ∈ S x → ∃ i a b, l i a = x ∧ r i b = y) :
    (∑ x, (S x).card) ≤ ∑ i, ∑ a, (block S l r i a).card := by
  let f : (Σ i, Σ a, block S l r i a) → (Σ x, S x) := fun p =>
    ⟨l p.1 p.2.1, ⟨r p.1 p.2.2.val, (mem_filter.mp p.2.2.property).2⟩⟩
  have hs : Function.Surjective f := by
    rintro ⟨x,y,hy⟩
    obtain ⟨i,a,b,ha,hb⟩ := hc x y hy
    refine ⟨⟨i,a,⟨b,?_⟩⟩,?_⟩
    · apply mem_filter.mpr
      exact ⟨mem_univ _, by simpa only [ha,hb] using hy⟩
    · apply Sigma.subtype_ext ha
      exact hb
  have h := Fintype.card_le_of_surjective f hs
  simpa only [Fintype.card_sigma,Fintype.card_coe] using h

omit [Fintype Y] in
/-- The asymmetric fourth-power estimate for a uniform rectangle cover. -/
theorem fourth_power (S : X → Finset Y) (l : I → A ↪ X) (r : I → B ↪ Y)
    (hc : ∀ x y, y ∈ S x → ∃ i a b, l i a = x ∧ r i b = y)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    (∑ x, (S x).card)^4 ≤ Fintype.card I^4 *
      (24*Fintype.card A^3*Fintype.card B^4 + 648*Fintype.card A^4) := by
  have hp := pow_sum_le_card_mul_sum_pow (s := (univ : Finset I))
    (f := fun i => ∑ a, (block S l r i a).card) (by intros; omega) 3
  simp only [card_univ] at hp
  calc
    _ ≤ (∑ i, ∑ a, (block S l r i a).card)^4 :=
      Nat.pow_le_pow_left (edge_count_le S l r hc) 4
    _ ≤ Fintype.card I^3 * ∑ i, (∑ a, (block S l r i a).card)^4 := hp
    _ ≤ Fintype.card I^3 * ∑ _i : I,
        (24*Fintype.card A^3*Fintype.card B^4+648*Fintype.card A^4) := by
      apply Nat.mul_le_mul_left
      exact sum_le_sum (fun i _ => Erdos714Unbalanced.fourth_power_bound
        (block S l r i) (block_free S l r hf i))
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id]; ring

omit [Fintype Y] in
/-- Relative density form. Multiplicities in the cover are not discarded. -/
theorem relative_fourth (S : X → Finset Y) (l : I → A ↪ X) (r : I → B ↪ Y)
    (hc : ∀ x y, y ∈ S x → ∃ i a b, l i a = x ∧ r i b = y)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (L : ℕ) (hL : L ≤ Fintype.card A) (hR : L ≤ Fintype.card B) :
    L*(∑ x, (S x).card)^4 ≤
      672*(Fintype.card I*Fintype.card A*Fintype.card B)^4 := by
  by_cases hzero : L=0
  · simp [hzero]
  have h := Erdos714FusionBounds.sum_relative_fourth
    (fun i => ∑ a, (block S l r i a).card)
    (fun _i : I => Fintype.card A*Fintype.card B) L 672 (by omega)
    (fun i => Erdos714FusionBounds.relative_fourth (block S l r i)
      (block_free S l r hf i) L hL hR)
  calc
    _ ≤ L*(∑ i, ∑ a, (block S l r i a).card)^4 := by
      gcongr
      exact edge_count_le S l r hc
    _ ≤ 672*(∑ _i : I, Fintype.card A*Fintype.card B)^4 := h
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,mul_assoc]

end Erdos714RectangleCover

namespace Erdos714ProductSet
open Erdos714Packing
variable {G : Type*} [Group G]

/-- An ordered product set: commutativity is not assumed. -/
def product (A B : Finset G) : Finset G := (A.product B).image (fun p => p.1*p.2)

@[simp] lemma mem_product (A B : Finset G) (z : G) :
    z ∈ product A B ↔ ∃ a ∈ A, ∃ b ∈ B, a*b=z := by
  simp only [product,mem_image,Finset.product_eq_sprod,Finset.mem_product,Prod.exists]
  tauto

lemma product_card (A B : Finset G) : (product A B).card ≤ A.card*B.card :=
  card_image_le.trans (by simp)

variable [Fintype G]

def neighbors (T : Finset G) (x : G) : Finset G := univ.filter (fun y => x*y ∈ T)

def graph (T : Finset G) : SimpleGraph (G ⊕ G) := incidence (neighbors T)

@[simp] lemma cross_adj (T : Finset G) (x y : G) :
    (graph T).Adj (.inl x) (.inr y) ↔ x*y ∈ T := by simp [graph,neighbors]

/-- Each row has exactly the connection-set cardinality. -/
lemma degree (T : Finset G) (x : G) : (neighbors T x).card = T.card := by
  apply card_nbij (fun y => x*y)
  · intro y hy
    exact (mem_filter.mp hy).2
  · intro y hy z hz he
    exact mul_left_cancel he
  · intro t ht
    refine ⟨x⁻¹*t,?_,by group⟩
    apply mem_filter.mpr
    exact ⟨mem_univ _,by simpa using ht⟩

/-- Undirected edges are counted once, across the two disjoint group copies. -/
theorem edge_count (T : Finset G) :
    (graph T).edgeFinset.card = Fintype.card G*T.card := by
  rw [graph,incidence_edges]
  simp only [degree,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id]

def rows (A : Finset G) (g : G) : A ↪ G :=
  ⟨fun a => a.val*g⁻¹, fun _ _ h => Subtype.ext (mul_right_cancel h)⟩

def columns (B : Finset G) (g : G) : B ↪ G :=
  ⟨fun b => g*b.val, fun _ _ h => Subtype.ext (mul_left_cancel h)⟩

lemma block_incidence (A B : Finset G) (g : G) (a : A) (b : B) :
    (graph (product A B)).Adj (.inl (rows A g a)) (.inr (columns B g b)) := by
  rw [cross_adj,mem_product]
  refine ⟨a.val,a.property,b.val,b.property,?_⟩
  dsimp [rows,columns]
  group

omit [Fintype G] in
/-- Every edge lies in an actual translated product rectangle. -/
lemma cover (A B : Finset G) (x y : G) (h : x*y ∈ product A B) :
    ∃ g a b, rows A g a=x ∧ columns B g b=y := by
  obtain ⟨a,ha,b,hb,he⟩ := (mem_product A B _).mp h
  refine ⟨x⁻¹*a,⟨a,ha⟩,⟨b,hb⟩,?_,?_⟩
  · dsimp [rows]
    group
  · dsimp [columns]
    rw [mul_assoc,he]
    group

/-- Arbitrary edge restrictions of the product-set host satisfy an unbalanced bound. -/
theorem fourth_power (A B : Finset G) (H : SimpleGraph (G ⊕ G))
    (hH : H ≤ graph (product A B))
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ Fintype.card G^4*(24*A.card^3*B.card^4+648*A.card^4) := by
  let S := Erdos714Unbalanced.neighborhoods H
  have hbi : H ≤ completeBipartiteGraph G G := by
    intro x y hxy
    have hh := hH hxy
    cases x <;> cases y <;> simp_all [graph]
  have hS := Erdos714Unbalanced.incidence_neighborhoods H hbi
  have hc : ∀ x y, y ∈ S x → ∃ g a b, rows A g a=x ∧ columns B g b=y := by
    intro x y hxy
    have he : H.Adj (.inl x) (.inr y) := (mem_filter.mp hxy).2
    exact cover A B x y ((cross_adj _ _ _).mp (hH he))
  have h := Erdos714RectangleCover.fourth_power S (rows A) (columns B) hc (by rwa [hS])
  rw [← incidence_edges,hS] at h
  simpa only [Fintype.card_coe] using h

/-- Density estimate keeping track of product-representation multiplicity. -/
theorem relative_fourth (A B : Finset G) (H : SimpleGraph (G ⊕ G))
    (hH : H ≤ graph (product A B))
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (L : ℕ) (hL : L ≤ A.card) (hR : L ≤ B.card) :
    L*H.edgeFinset.card^4 ≤ 672*(Fintype.card G*A.card*B.card)^4 := by
  let S := Erdos714Unbalanced.neighborhoods H
  have hbi : H ≤ completeBipartiteGraph G G := by
    intro x y hxy
    have hh := hH hxy
    cases x <;> cases y <;> simp_all [graph]
  have hS := Erdos714Unbalanced.incidence_neighborhoods H hbi
  have hc : ∀ x y, y ∈ S x → ∃ g a b, rows A g a=x ∧ columns B g b=y := by
    intro x y hxy
    have he : H.Adj (.inl x) (.inr y) := (mem_filter.mp hxy).2
    exact cover A B x y ((cross_adj _ _ _).mp (hH he))
  have h := Erdos714RectangleCover.relative_fourth S (rows A) (columns B) hc
    (by rwa [hS]) L (by simpa using hL) (by simpa using hR)
  rw [← incidence_edges,hS] at h
  simpa only [Fintype.card_coe] using h

/-- A bounded representation count makes the retained relative density vanish
when both product factors grow. The selected graph need not be a Cayley graph. -/
theorem bounded_representations (A B : Finset G) (M L : ℕ)
    (hrep : ∀ z : G, ((A.product B).filter (fun p => p.1*p.2=z)).card ≤ M)
    (hL : L ≤ A.card) (hR : L ≤ B.card)
    (H : SimpleGraph (G ⊕ G)) (hH : H ≤ graph (product A B))
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    L*H.edgeFinset.card^4 ≤ 672*M^4*(graph (product A B)).edgeFinset.card^4 := by
  have hm : A.card*B.card ≤ M*(product A B).card := by
    have h := card_le_mul_card_image (A.product B) M (fun z _ => hrep z)
    simpa only [product,Finset.product_eq_sprod,Finset.card_product] using h
  have hc : Fintype.card G*A.card*B.card ≤
      M*(Fintype.card G*(product A B).card) := by
    nlinarith [Nat.mul_le_mul_left (Fintype.card G) hm]
  rw [edge_count]
  calc
    _ ≤ 672*(Fintype.card G*A.card*B.card)^4 := relative_fourth A B H hH hf L hL hR
    _ ≤ 672*(M*(Fintype.card G*(product A B).card))^4 := by gcongr
    _ = _ := by ring

/-- In particular the q-by-q² factorization at order q⁴ loses a quarter power. -/
theorem critical_fourth (A B : Finset G) (q : ℕ) (hq : 0<q)
    (hG : Fintype.card G ≤ q^4) (hA : A.card ≤ q) (hB : B.card ≤ q^2)
    (H : SimpleGraph (G ⊕ G)) (hH : H ≤ graph (product A B))
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 672*q^27 := by
  have h := fourth_power A B H hH hf
  have hp : q^20 ≤ q^27 := Nat.pow_le_pow_right (by omega) (by decide)
  calc
    _ ≤ Fintype.card G^4*(24*A.card^3*B.card^4+648*A.card^4) := h
    _ ≤ (q^4)^4*(24*q^3*(q^2)^4+648*q^4) := by gcongr
    _ = 24*q^27+648*q^20 := by ring
    _ ≤ 672*q^27 := by nlinarith

/-- Triple products of three sets of size at most q are included. No B₄
hypothesis is needed, so further restrictions cannot repair this host. -/
theorem triple_fourth (A B C : Finset G) (q : ℕ) (hq : 0<q)
    (hG : Fintype.card G ≤ q^4) (hA : A.card ≤ q) (hB : B.card ≤ q) (hC : C.card ≤ q)
    (H : SimpleGraph (G ⊕ G)) (hH : H ≤ graph (product A (product B C)))
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 672*q^27 := by
  apply critical_fourth A (product B C) q hq hG hA _ H hH hf
  exact (product_card B C).trans (by nlinarith)

/-- A fixed positive critical edge constant is possible only at bounded q. -/
theorem size_budget (A B : Finset G) (q K : ℕ) (hq : 0<q)
    (hG : Fintype.card G ≤ q^4) (hA : A.card ≤ q) (hB : B.card ≤ q^2)
    (H : SimpleGraph (G ⊕ G)) (hH : H ≤ graph (product A B))
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hdense : q^7 ≤ K*H.edgeFinset.card) : q ≤ 672*K^4 := by
  have he := critical_fourth A B q hq hG hA hB H hH hf
  have hlo := Nat.pow_le_pow_left hdense 4
  rw [mul_pow] at hlo
  have hmul : q*q^27 ≤ (672*K^4)*q^27 := by
    calc
      _ = (q^7)^4 := by ring
      _ ≤ K^4*H.edgeFinset.card^4 := hlo
      _ ≤ K^4*(672*q^27) := Nat.mul_le_mul_left _ he
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right hmul (pow_pos hq 27)

#print axioms edge_count
#print axioms block_incidence
#print axioms cover
#print axioms fourth_power
#print axioms relative_fourth
#print axioms bounded_representations
#print axioms critical_fourth
#print axioms triple_fourth
#print axioms size_budget
end Erdos714ProductSet

#print axioms Erdos714RectangleCover.fourth_power
#print axioms Erdos714RectangleCover.relative_fourth

namespace Erdos714SumSet
variable {G : Type*} [AddGroup G] [Fintype G]

/-- Ordered sumset, also available without commutativity. -/
def sumset (A B : Finset G) : Finset G := (A.product B).image (fun p => p.1+p.2)

def graph (T : Finset G) : SimpleGraph (G ⊕ G) :=
  Erdos714Packing.incidence fun x => univ.filter (fun y => x+y ∈ T)

/-- The same obstruction applies to arbitrary thinnings of triple-sum hosts. -/
theorem triple_fourth (A B C : Finset G) (q : ℕ) (hq : 0<q)
    (hG : Fintype.card G ≤ q^4) (hA : A.card ≤ q) (hB : B.card ≤ q) (hC : C.card ≤ q)
    (H : SimpleGraph (G ⊕ G)) (hH : H ≤ graph (sumset A (sumset B C)))
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 672*q^27 := by
  letI : Fintype (Multiplicative G) := ‹Fintype G›
  exact Erdos714ProductSet.triple_fourth (G := Multiplicative G)
    A B C q hq hG hA hB hC H hH hf

#print axioms triple_fourth
end Erdos714SumSet
