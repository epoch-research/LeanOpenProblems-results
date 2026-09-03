import Submission.UnbalancedBounds

/-!
A necessary density condition for the unresolved fourth case. A critical-scale
K44-free incidence system must have a positive proportion of ordered four-row
sets with exactly three common columns. This is not a construction or a
resolution of the conjecture.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714TripleCommonDensity
open Erdos714Packing

variable {I A B : Type*} [Fintype I] [Fintype A] [Fintype B]

/-- Hölder followed by the elementary falling-factorial bound. -/
lemma truncated_moment (d : I → ℕ) (r : ℕ) (hr : 1 ≤ r) :
    ((∑ i, d i) - (r-1)*Fintype.card I)^r ≤
      Fintype.card I^(r-1) * ∑ i, (d i).descFactorial r := by
  have hs : (∑ i, d i) ≤ (∑ i, (d i+1-r)) + (r-1)*Fintype.card I := by
    calc
      _ ≤ ∑ i, (d i+1-r+(r-1)) := sum_le_sum (fun i _ => by omega)
      _ = _ := by rw [sum_add_distrib]; simp [Nat.mul_comm]
  have hs' : (∑ i, d i) - (r-1)*Fintype.card I ≤ ∑ i, (d i+1-r) := by omega
  have hp := pow_sum_le_card_mul_sum_pow (s := (univ : Finset I))
    (f := fun i => d i+1-r) (by intros; omega) (r-1)
  rw [Nat.sub_add_cancel hr, card_univ] at hp
  calc
    _ ≤ (∑ i, (d i+1-r))^r := Nat.pow_le_pow_left hs' r
    _ ≤ Fintype.card I^(r-1) * ∑ i, (d i+1-r)^r := hp
    _ ≤ _ := Nat.mul_le_mul_left _
      (sum_le_sum (fun i _ => Nat.pow_sub_le_descFactorial _ _))

/-- Ordered complete rectangles can be counted from either side. -/
def rectangleEquiv (S : A → Finset B) (r s : ℕ) :
    (Σ f : Fin r ↪ A, Fin s ↪ common S f) ≃
      (Σ g : Fin s ↪ B, Fin r ↪ common (dual S) g) where
  toFun p :=
    ⟨⟨fun j => (p.2 j).val, fun i j h => p.2.injective (Subtype.ext h)⟩,
      ⟨fun i => ⟨p.1 i, by
        simp only [mem_common, mem_dual]
        intro j
        exact (mem_common S p.1 _).mp (p.2 j).property i⟩,
       fun i j h => p.1.injective (congrArg Subtype.val h)⟩⟩
  invFun p :=
    ⟨⟨fun i => (p.2 i).val, fun i j h => p.2.injective (Subtype.ext h)⟩,
      ⟨fun j => ⟨p.1 j, by
        simp only [mem_common]
        intro i
        exact (mem_dual S _ _).mp
          ((mem_common (dual S) p.1 _).mp (p.2 i).property j)⟩,
       fun i j h => p.1.injective (congrArg Subtype.val h)⟩⟩
  left_inv p := by rcases p with ⟨f,g⟩; rfl
  right_inv p := by rcases p with ⟨f,g⟩; rfl

lemma rectangle_count (S : A → Finset B) (r s : ℕ) :
    (∑ f : Fin r ↪ A, (common S f).card.descFactorial s) =
      ∑ g : Fin s ↪ B, (common (dual S) g).card.descFactorial r := by
  have h := Fintype.card_congr (rectangleEquiv S r s)
  simpa only [Fintype.card_sigma, Fintype.card_embedding_eq, Fintype.card_fin,
    Fintype.card_coe] using h

def triples (S : A → Finset B) : ℕ :=
  ∑ g : Fin 3 ↪ B, (common (dual S) g).card

def exactThree (S : A → Finset B) : Finset (Fin 4 ↪ A) :=
  univ.filter (fun f => (common S f).card = 3)

lemma first_star_moment (S : A → Finset B) :
    ((∑ a, (S a).card) - 2*Fintype.card A)^3 ≤
      Fintype.card A^2 * triples S := by
  have h := truncated_moment (fun a => (S a).card) 3 (by decide)
  have hc := Fintype.card_congr (Erdos714Unbalanced.starEquiv S 3)
  simp only [Fintype.card_sigma, Fintype.card_embedding_eq, Fintype.card_fin,
    Fintype.card_coe] at hc
  simpa only [Nat.reduceSub, hc, triples] using h

lemma second_star_moment (S : A → Finset B)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    (triples S - 3*Fintype.card (Fin 3 ↪ B))^4 ≤
      Fintype.card (Fin 3 ↪ B)^3 * (6*(exactThree S).card) := by
  have h := truncated_moment (fun g : Fin 3 ↪ B => (common (dual S) g).card) 4 (by decide)
  have hc : (∑ f : Fin 4 ↪ A, (common S f).card.descFactorial 3) =
      6*(exactThree S).card := by
    have hb := (free_iff_common_card S (by decide : 0 < 4)).mp hfree
    have hterm (f : Fin 4 ↪ A) : (common S f).card.descFactorial 3 =
        if (common S f).card = 3 then 6 else 0 := by
      have hh := hb f
      interval_cases hn : (common S f).card <;> norm_num
    simp_rw [hterm]
    rw [← sum_filter]
    simp [exactThree, mul_comm]
  rw [← rectangle_count S 4 3, hc] at h
  exact h

/-- Quantitative necessary condition at the critical scale. The count is of
ordered embeddings, so every unordered four-set is counted 24 times. -/
theorem critical_exact_three (S : A → Finset B) (q C : ℕ)
    (hC : 0 < C) (hq : 48*C^3 ≤ q)
    (hA : Fintype.card A ≤ q^4) (hB : Fintype.card B ≤ q^4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (he : q^7 ≤ C*(∑ a, (S a).card)) :
    q^16 ≤ 393216*C^12*(exactThree S).card := by
  let m := Fintype.card A
  let n := Fintype.card (Fin 3 ↪ B)
  let e := ∑ a, (S a).card
  let T := triples S
  let Z := (exactThree S).card
  have hq0 : 0 < q := by
    have : 0 < 48*C^3 := by positivity
    omega
  have hC3 : C ≤ C^3 := by
    simpa only [pow_one] using pow_le_pow_right' hC (by decide : 1 ≤ 3)
  have h4C : 4*C ≤ q := by omega
  have hm : m ≤ q^4 := hA
  have hn : n ≤ q^12 := by
    calc
      n = (Fintype.card B).descFactorial 3 := by simp [n]
      _ ≤ (Fintype.card B)^3 := Nat.descFactorial_le_pow _ _
      _ ≤ (q^4)^3 := Nat.pow_le_pow_left hB 3
      _ = _ := by ring
  have hoff : 4*C*m ≤ q^7 := by
    calc
      _ ≤ q*q^4 := Nat.mul_le_mul h4C hm
      _ = q^5 := by ring
      _ ≤ _ := pow_le_pow_right' hq0 (by decide)
  have he' : q^7 ≤ 2*C*(e-2*m) := by
    have ht : e ≤ (e-2*m)+2*m := by omega
    have ht' := Nat.mul_le_mul_left C ht
    dsimp [e] at ht'
    nlinarith
  have hfirst : (e-2*m)^3 ≤ m^2*T := first_star_moment S
  have hT : q^13 ≤ 8*C^3*T := by
    have hh : q^8*q^13 ≤ q^8*(8*C^3*T) := by
      calc
        _ = (q^7)^3 := by ring
        _ ≤ (2*C*(e-2*m))^3 := Nat.pow_le_pow_left he' 3
        _ = 8*C^3*(e-2*m)^3 := by ring
        _ ≤ 8*C^3*(m^2*T) := Nat.mul_le_mul_left _ hfirst
        _ ≤ 8*C^3*((q^4)^2*T) := by gcongr
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left hh (by positivity)
  have hToff : 48*C^3*n ≤ q^13 := by
    calc
      _ ≤ q*q^12 := Nat.mul_le_mul hq hn
      _ = _ := by ring
  have hT' : q^13 ≤ 16*C^3*(T-3*n) := by
    have ht : T ≤ (T-3*n)+3*n := by omega
    have ht' := Nat.mul_le_mul_left (8*C^3) ht
    nlinarith
  have hsecond : (T-3*n)^4 ≤ n^3*(6*Z) := second_star_moment S hfree
  have hh : q^36*q^16 ≤ q^36*(393216*C^12*Z) := by
    calc
      _ = (q^13)^4 := by ring
      _ ≤ (16*C^3*(T-3*n))^4 := Nat.pow_le_pow_left hT' 4
      _ = 65536*C^12*(T-3*n)^4 := by ring
      _ ≤ 65536*C^12*(n^3*(6*Z)) := Nat.mul_le_mul_left _ hsecond
      _ ≤ 65536*C^12*((q^12)^3*(6*Z)) := by gcongr
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hh (by positivity)

/-- An exceptional family of only O(q^15) four-row tuples cannot support
critical density along unbounded field-size parameters. No geometric
codimension assertion is assumed or proved by this theorem. -/
theorem exceptional_budget (S : A → Finset B) (q C D : ℕ)
    (hC : 0 < C) (hq : 48*C^3 ≤ q)
    (hA : Fintype.card A ≤ q^4) (hB : Fintype.card B ≤ q^4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (he : q^7 ≤ C*(∑ a, (S a).card))
    (X : Finset (Fin 4 ↪ A)) (hX : X.card ≤ D*q^15)
    (hgood : ∀ f, f ∉ X → (common S f).card ≤ 2) :
    q ≤ 393216*C^12*D := by
  have hsub : exactThree S ⊆ X := by
    intro f hf
    have hf3 : (common S f).card = 3 := (mem_filter.mp hf).2
    by_contra hn
    have := hgood f hn
    omega
  have hb := critical_exact_three S q C hC hq hA hB hfree he
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity : 0 < 48*C^3) hq
  have hh : q^15*q ≤ q^15*(393216*C^12*D) := by
    calc
      _ = q^16 := by ring
      _ ≤ 393216*C^12*(exactThree S).card := hb
      _ ≤ 393216*C^12*(D*q^15) :=
        Nat.mul_le_mul_left _ ((card_le_card hsub).trans hX)
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hh (by positivity)

variable {F : Type*} [Field F]

/-- A separable quartic cannot have exactly three roots in its base field.
This counts all its base-field roots, not a selected subset. -/
lemma separable_quartic_not_three (p : Polynomial F) (hd : p.natDegree = 4)
    (hs : p.Separable) : p.roots.toFinset.card ≠ 3 := by
  intro hc
  have hc' : p.roots.card = 3 := by
    simpa only [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hs)] using hc
  obtain ⟨u, _, hsum, hu⟩ := p.exists_prod_multiset_X_sub_C_mul
  have hud : u.natDegree ≤ 1 := by omega
  have hsplit := (Polynomial.Splits.of_natDegree_le_one hud).natDegree_eq_card_roots
  rw [hu, Multiset.card_zero] at hsplit
  omega

/-- Conditional exclusion of an exact separable-quartic root model outside
O(q^15) exceptional tuples. The cardinal equality must account for ALL roots;
an injection of common neighbors into roots alone does not suffice. -/
theorem quartic_model_budget (S : A → Finset B) (q C D : ℕ)
    (hC : 0 < C) (hq : 48*C^3 ≤ q)
    (hA : Fintype.card A ≤ q^4) (hB : Fintype.card B ≤ q^4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (he : q^7 ≤ C*(∑ a, (S a).card))
    (X : Finset (Fin 4 ↪ A)) (hX : X.card ≤ D*q^15)
    (p : (Fin 4 ↪ A) → Polynomial F)
    (hmodel : ∀ f, f ∉ X → (p f).natDegree = 4 ∧ (p f).Separable ∧
      (common S f).card = (p f).roots.toFinset.card) :
    q ≤ 393216*C^12*D := by
  apply exceptional_budget S q C D hC hq hA hB hfree he X hX
  intro f hf
  obtain ⟨hd, hs, hc⟩ := hmodel f hf
  have hb := (free_iff_common_card S (by decide : 0 < 4)).mp hfree f
  have hn := separable_quartic_not_three (p f) hd hs
  omega

variable {V : Type*} [Fintype V]

/-- The bipartite double cover preserves biclique freeness: an overlap between
its two projected vertex lists would force a loop in the original graph. -/
lemma neighbor_incidence_free (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : (completeBipartiteGraph (Fin 4) (Fin 4)).Free G) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (incidence (fun v => G.neighborFinset v)) := by
  apply (free_iff_no_rectangle _ (by decide : 0 < 4)).mpr
  intro f g h
  apply hG
  refine ⟨Copy.completeBipartiteGraph (univ.map f) (univ.map g)
    (by simp) (by simp) ?_⟩
  intro v hv w hw
  change v ∈ univ.map f at hv
  change w ∈ univ.map g at hw
  obtain ⟨i, _, rfl⟩ := mem_map.mp hv
  obtain ⟨j, _, rfl⟩ := mem_map.mp hw
  exact (G.mem_neighborFinset _ _).mp (h i j)

/-- The same necessary condition for arbitrary simple graphs, not only for a
chosen bipartite incidence presentation. -/
theorem graph_critical_exact_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (q C : ℕ) (hC : 0 < C) (hq : 48*C^3 ≤ q)
    (hV : Fintype.card V ≤ q^4)
    (hG : (completeBipartiteGraph (Fin 4) (Fin 4)).Free G)
    (he : q^7 ≤ C*G.edgeFinset.card) :
    q^16 ≤ 393216*C^12*(exactThree (fun v => G.neighborFinset v)).card := by
  apply critical_exact_three (fun v => G.neighborFinset v) q C hC hq hV hV
    (neighbor_incidence_free G hG)
  have hd : (∑ v, (G.neighborFinset v).card) = 2*G.edgeFinset.card := by
    simpa only [card_neighborFinset_eq_degree] using G.sum_degrees_eq_twice_card_edges
  rw [hd]
  exact he.trans (Nat.mul_le_mul_left C (by omega))

#print axioms truncated_moment
#print axioms rectangle_count
#print axioms separable_quartic_not_three
#print axioms quartic_model_budget
#print axioms critical_exact_three
#print axioms exceptional_budget
#print axioms neighbor_incidence_free
#print axioms graph_critical_exact_three
end Erdos714TripleCommonDensity
