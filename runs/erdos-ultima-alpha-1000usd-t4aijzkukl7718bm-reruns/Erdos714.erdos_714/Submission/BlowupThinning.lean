import Submission.UnbalancedBounds

/-!
An arbitrary endpoint-dependent lift still obeys an unbalanced bound on each
whole vertex fiber. This excludes certain density-preserving amplifications,
not arbitrary graphs and not the conjecture of Erdős 714.
-/

noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714Blowup
open Erdos714Packing
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The columns accessible from a fixed base row, with their lift labels. -/
def block (S : X → Finset Y) (T : X × A → Finset (Y × B)) (x : X)
    (a : A) : Finset ((S x) × B) :=
  univ.filter (fun p => (p.1.val,p.2) ∈ T (x,a))

omit [Fintype X] [Fintype Y] [Fintype A] in
lemma block_free (S : X → Finset Y) (T : X × A → Finset (Y × B))
    (x : X) {r : ℕ} (hr : 0 < r)
    (hf : (completeBipartiteGraph (Fin r) (Fin r)).Free (incidence T)) :
    (completeBipartiteGraph (Fin r) (Fin r)).Free (incidence (block S T x)) := by
  rw [free_iff_no_rectangle _ hr] at hf ⊢
  intro f g h
  let l : A ↪ X × A := ⟨fun a => (x,a), fun _ _ he => congrArg Prod.snd he⟩
  let e : (S x) × B ↪ Y × B := ⟨fun p => (p.1.val,p.2), by
    intro p q he
    exact Prod.ext (Subtype.ext (congrArg (fun t : Y × B => t.1) he)) (congrArg (fun t : Y × B => t.2) he)⟩
  apply hf (f.trans l) (g.trans e)
  intro i j
  simpa [block,l,e] using h i j

omit [Fintype X] [Fintype Y] [Fintype A] in
lemma block_card (S : X → Finset Y) (T : X × A → Finset (Y × B))
    (hT : ∀ x a y b, (y,b) ∈ T (x,a) → y ∈ S x) (x : X) (a : A) :
    (block S T x a).card = (T (x,a)).card := by
  apply card_nbij (fun p : (S x) × B => (p.1.val,p.2))
  · intro p hp
    simpa [block] using hp
  · intro p hp q hq he
    exact Prod.ext (Subtype.ext (congrArg (fun t : Y × B => t.1) he)) (congrArg (fun t : Y × B => t.2) he)
  · rintro ⟨y,b⟩ h
    exact ⟨(⟨y,hT x a y b h⟩,b),by simpa [block] using h,rfl⟩

lemma sum_dual_card {U V : Type*} [Fintype U] [Fintype V] (S : U → Finset V) :
    (∑ v, (dual S v).card) = ∑ u, (S u).card := by
  simp only [dual,card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  simp

omit [Fintype X] [Fintype Y] in
/-- No local column-degree or separability assumption is needed. -/
theorem fiber_fourth_power (S : X → Finset Y) (T : X × A → Finset (Y × B))
    (hT : ∀ x a y b, (y,b) ∈ T (x,a) → y ∈ S x)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence T)) (x : X) :
    (∑ a, (T (x,a)).card)^4 ≤
      24*((S x).card*Fintype.card B)^3*Fintype.card A^4 +
      648*((S x).card*Fintype.card B)^4 := by
  have hlocal := block_free S T x (by decide : 0 < 4) hf
  have hdual : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (incidence (dual (block S T x))) := by
    rw [free_iff_common_card _ (by decide)]
    exact (common_card_dual_iff _ (by decide)).mp
      ((free_iff_common_card _ (by decide)).mp hlocal)
  have h := Erdos714Unbalanced.fourth_power_bound (dual (block S T x)) hdual
  rw [sum_dual_card] at h
  simpa only [block_card S T hT,Fintype.card_prod,Fintype.card_coe] using h

/-- A bound for EVERY spanning edge subgraph supported over a base set system.
The edge relations inside different blocks may be completely unrelated. -/
theorem fourth_power_bound (S : X → Finset Y) (T : X × A → Finset (Y × B))
    (hT : ∀ x a y b, (y,b) ∈ T (x,a) → y ∈ S x)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence T))
    (D : ℕ) (hD : ∀ x, (S x).card ≤ D) :
    (incidence T).edgeFinset.card^4 ≤ Fintype.card X^4 *
      (24*(D*Fintype.card B)^3*Fintype.card A^4 +
       648*(D*Fintype.card B)^4) := by
  rw [incidence_edges,Fintype.sum_prod_type]
  have h := pow_sum_le_card_mul_sum_pow (s := (univ : Finset X))
    (f := fun x => ∑ a, (T (x,a)).card) (by intros; omega) 3
  norm_num only [card_univ] at h
  calc
    _ ≤ Fintype.card X^3 * ∑ x, (∑ a, (T (x,a)).card)^4 := h
    _ ≤ Fintype.card X^3 * ∑ _x : X,
        (24*(D*Fintype.card B)^3*Fintype.card A^4 +
         648*(D*Fintype.card B)^4) := by
      apply Nat.mul_le_mul_left
      apply sum_le_sum
      intro x _
      exact (fiber_fourth_power S T hT hf x).trans (by gcongr <;> exact hD x)
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id]; ring

/-- At the two-factor critical scale, the exponent is 53/4, not 14. -/
theorem critical_fourth_power (S : X → Finset Y) (T : X × A → Finset (Y × B))
    (hT : ∀ x a y b, (y,b) ∈ T (x,a) → y ∈ S x)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence T))
    (q : ℕ) (hq : 0 < q) (hX : Fintype.card X ≤ q^4)
    (hA : Fintype.card A ≤ q^4) (hB : Fintype.card B ≤ q^4)
    (hD : ∀ x, (S x).card ≤ q^3) :
    (incidence T).edgeFinset.card^4 ≤ 672*q^53 := by
  have h := fourth_power_bound S T hT hf (q^3) hD
  have hp : q^44 ≤ q^53 := Nat.pow_le_pow_right (by omega) (by decide)
  calc
    _ ≤ Fintype.card X^4 *
      (24*(q^3*Fintype.card B)^3*Fintype.card A^4 +
       648*(q^3*Fintype.card B)^4) := h
    _ ≤ (q^4)^4*(24*(q^3*q^4)^3*(q^4)^4+648*(q^3*q^4)^4) := by gcongr
    _ = 24*q^53+648*q^44 := by ring
    _ ≤ 672*q^53 := by omega

/-- A fixed multiplicative loss cannot amplify two growing critical factors. -/
theorem critical_size_budget (S : X → Finset Y) (T : X × A → Finset (Y × B))
    (hT : ∀ x a y b, (y,b) ∈ T (x,a) → y ∈ S x)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence T))
    (q K : ℕ) (hq : 0 < q) (hX : Fintype.card X ≤ q^4)
    (hA : Fintype.card A ≤ q^4) (hB : Fintype.card B ≤ q^4)
    (hD : ∀ x, (S x).card ≤ q^3)
    (he : q^14 ≤ K*(incidence T).edgeFinset.card) : q^3 ≤ 672*K^4 := by
  have hb := critical_fourth_power S T hT hf q hq hX hA hB hD
  have h : q^53*q^3 ≤ q^53*(672*K^4) := by
    calc
      _ = (q^14)^4 := by ring
      _ ≤ (K*(incidence T).edgeFinset.card)^4 := Nat.pow_le_pow_left he 4
      _ = K^4*(incidence T).edgeFinset.card^4 := mul_pow _ _ _
      _ ≤ K^4*(672*q^53) := Nat.mul_le_mul_left _ hb
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h (pow_pos hq 53)


/-- The full blowup: every base edge is replaced by a complete bipartite block. -/
def host (S : X → Finset Y) : SimpleGraph ((X × A) ⊕ (Y × B)) :=
  incidence fun p => (S p.1).product (univ : Finset B)

/-- The preceding bound applies to arbitrary simple-graph edge deletions,
not just to a prescribed local replacement relation. -/
theorem graph_fourth_power (S : X → Finset Y)
    (H : SimpleGraph ((X × A) ⊕ (Y × B))) (hH : H ≤ host S)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (D : ℕ) (hD : ∀ x, (S x).card ≤ D) :
    H.edgeFinset.card^4 ≤ Fintype.card X^4 *
      (24*(D*Fintype.card B)^3*Fintype.card A^4 +
       648*(D*Fintype.card B)^4) := by
  let T := Erdos714Unbalanced.neighborhoods H
  have hbi : H ≤ completeBipartiteGraph (X × A) (Y × B) := by
    intro v w hvw
    have hh := hH hvw
    cases v <;> cases w <;> simp_all [host]
  have he : incidence T = H := Erdos714Unbalanced.incidence_neighborhoods H hbi
  have hs : ∀ x a y b, (y,b) ∈ T (x,a) → y ∈ S x := by
    intro x a y b hb
    have hadj : H.Adj (.inl (x,a)) (.inr (y,b)) := by
      simpa [T,Erdos714Unbalanced.neighborhoods] using hb
    have hh := hH hadj
    simpa [host] using hh
  let iso : incidence T ≃g H := ⟨Equiv.refl _, by
    intro v w
    change H.Adj v w ↔ (incidence T).Adj v w
    rw [he]⟩
  rw [← iso.card_edgeFinset_eq]
  exact fourth_power_bound S T hs (by rwa [he]) D hD

omit [Fintype X] [Fintype Y] in
/-- Four-star counting within one row fiber. A local column may have any
neighbors at all; only its degree is prescribed, separately on each base edge. -/
theorem local_column_packing (S : X → Finset Y) (T : X × A → Finset (Y × B))
    {r : ℕ} (hr : 0 < r)
    (hf : (completeBipartiteGraph (Fin r) (Fin r)).Free (incidence T))
    (x : X) (d : ℕ)
    (hd : ∀ y ∈ S x, ∀ b : B,
      (univ.filter (fun a : A => (y,b) ∈ T (x,a))).card = d) :
    (S x).card*Fintype.card B*d.descFactorial r ≤
      (r-1)*(Fintype.card A).descFactorial r := by
  have hlocal := block_free S T x hr hf
  have hdual : (completeBipartiteGraph (Fin r) (Fin r)).Free
      (incidence (dual (block S T x))) := by
    rw [free_iff_common_card _ hr]
    exact (common_card_dual_iff _ hr).mp ((free_iff_common_card _ hr).mp hlocal)
  have hc (c : (S x) × B) : (dual (block S T x) c).card = d := by
    simpa [dual,block] using hd c.1.val c.1.property c.2
  have h := Erdos714Unbalanced.star_bound (dual (block S T x)) hr hdual
  simpa only [hc,sum_const,card_univ,Fintype.card_prod,Fintype.card_coe,
    nsmul_eq_mul,Nat.cast_id,mul_assoc] using h

omit [Fintype X] [Fintype Y] in
/-- In particular even arbitrarily relabelled 81-by-81 degree-27 seed blocks
cannot be placed over a base vertex with four neighbors. -/
theorem ternary_seed_degree_bound (S : X → Finset Y)
    (T : X × A → Finset (Y × B))
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence T))
    (hA : Fintype.card A = 81) (hB : Fintype.card B = 81) (x : X)
    (hd : ∀ y ∈ S x, ∀ b : B,
      (univ.filter (fun a : A => (y,b) ∈ T (x,a))).card = 27) : (S x).card ≤ 3 := by
  have h := local_column_packing S T (by decide : 0 < 4) hf x 27 hd
  norm_num [hA,hB,Nat.descFactorial] at h
  omega

end Erdos714Blowup
#print axioms Erdos714Blowup.block_free
#print axioms Erdos714Blowup.fiber_fourth_power
#print axioms Erdos714Blowup.fourth_power_bound
#print axioms Erdos714Blowup.critical_fourth_power
#print axioms Erdos714Blowup.critical_size_budget

#print axioms Erdos714Blowup.graph_fourth_power
#print axioms Erdos714Blowup.local_column_packing
#print axioms Erdos714Blowup.ternary_seed_degree_bound
