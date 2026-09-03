import Submission.EllipticFusionThinning
import Submission.UnbalancedBounds

/-!
An unbalanced refinement of the elliptic-fusion thinning obstruction. The
bounds apply to arbitrary retained edges, not just retained whole classes.
They do not settle Erdős Problem 714.
-/

noncomputable section
open Finset SimpleGraph Classical
set_option maxHeartbeats 2000000

namespace Erdos714Unbalanced

variable {V X Y : Type*} [Fintype V] [Fintype X] [Fintype Y]

/-- Intersect the pulled-back selected graph with the original bipartite block.
    This avoids assuming that the block is induced in the host. -/
lemma selected_block_fourth (H G : SimpleGraph V)
    (c : (completeBipartiteGraph X Y).Copy G)
    (hH : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) (g : G ≃g G) :
    ((univ.filter (fun e : G.edgeSet => e.val ∈ H.edgeSet)).filter
      (fun e => e ∈ Erdos714Averaging.translate (Erdos714GraphAveraging.edgeAction G) g
        (univ.map c.mapEdgeSet))).card^4 ≤
      24*Fintype.card X^3*Fintype.card Y^4 + 648*Fintype.card X^4 := by
  let f : X ⊕ Y ↪ V := c.toEmbedding.trans g.toEquiv.toEmbedding
  let J : SimpleGraph (X ⊕ Y) := completeBipartiteGraph X Y ⊓ H.comap f
  have hJ : (completeBipartiteGraph (Fin 4) (Fin 4)).Free J := by
    rintro ⟨d⟩
    apply Erdos714GraphAveraging.free_comap _ H f hH
    exact ⟨(Copy.ofLE J (H.comap f) inf_le_right).comp d⟩
  have hcount : ((univ.filter (fun e : G.edgeSet => e.val ∈ H.edgeSet)).filter
      (fun e => e ∈ Erdos714Averaging.translate (Erdos714GraphAveraging.edgeAction G) g
        (univ.map c.mapEdgeSet))).card ≤ J.edgeFinset.card := by
    rw [Erdos714Averaging.translate, Finset.map_map]
    rw [Erdos714GraphAveraging.filter_image_card (univ.filter (fun e : G.edgeSet => e.val ∈ H.edgeSet))
      univ (c.mapEdgeSet.trans ((Erdos714GraphAveraging.edgeAction G) g).toEmbedding)]
    apply Finset.card_le_card_of_injOn (fun e : (completeBipartiteGraph X Y).edgeSet => e.val)
    · intro e he
      change e.val ∈ J.edgeFinset
      rw [mem_edgeFinset]
      have hm := (mem_filter.mp he).2
      change (Erdos714GraphAveraging.edgeAction G g) (c.mapEdgeSet e) ∈
        univ.filter (fun e : G.edgeSet => e.val ∈ H.edgeSet) at hm
      have hm' := (mem_filter.mp hm).2
      change Sym2.map g (Sym2.map c e.val) ∈ H.edgeSet at hm'
      rw [Sym2.map_map] at hm'
      rcases e with ⟨e,hA⟩
      induction e using Sym2.ind with
      | _ x y => exact ⟨hA,hm'⟩
    · intro e he e' he' hh
      exact Subtype.ext hh
  have hbound : J.edgeFinset.card^4 ≤
      24*Fintype.card X^3*Fintype.card Y^4 + 648*Fintype.card X^4 := by
    convert graph_fourth_power J inf_le_left hJ using 1
    apply congrArg (fun T : Finset (Sym2 (X ⊕ Y)) => T.card^4)
    ext e
    simp
  exact (Nat.pow_le_pow_left hcount 4).trans hbound


#print axioms selected_block_fourth
end Erdos714Unbalanced

namespace Erdos714EllipticDensity
open Erdos714EllipticFusion Erdos714EllipticThinning
variable {F : Type*} [Field F] [Fintype F]

omit [Fintype F] in
lemma translate_action (S : Finset (F × F))
    (a : MatGroup (F := F) × MatGroup (F := F)) (T : Finset (graph S).edgeSet) :
    Erdos714Averaging.translate (edgeAction S) a T =
      Erdos714Averaging.translate (Erdos714GraphAveraging.edgeAction (graph S))
        (transform S a.1 a.2) T := rfl

lemma local_fourth (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c)
    (H : SimpleGraph (MatGroup (F := F) ⊕ MatGroup (F := F)))
    (hH : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (k : Ratio (F := F)) (a : MatGroup (F := F) × MatGroup (F := F)) :
    ((univ.filter (fun e : (graph S).edgeSet => e.val ∈ H.edgeSet)).filter
      (fun e => e ∈ Erdos714Averaging.translate (edgeAction S) a (block S hS k))).card^4 ≤
      192*S.card^3*(Fintype.card F-1)^4 + 10368*S.card^4 := by
  rw [block_eq, translate_action]
  have hb := Erdos714Unbalanced.selected_block_fourth H (graph S) (fiberCopy S hS k) hH
    (transform S a.1 a.2)
  rw [Fintype.card_units] at hb
  have hc := rows_card_bound S hS k
  have hs : 24*Fintype.card (Rows S hS k)^3*(Fintype.card F-1)^4 +
      648*Fintype.card (Rows S hS k)^4 ≤
      192*S.card^3*(Fintype.card F-1)^4 + 10368*S.card^4 := by
    calc
      _ ≤ 24*(2*S.card)^3*(Fintype.card F-1)^4 + 648*(2*S.card)^4 := by gcongr
      _ = _ := by ring
  apply le_trans ?_ hs
  with_reducible convert hb using 1
  all_goals first
    | exact (show Nat.instPreorder.toLE = instLENat from rfl)
    | with_reducible rfl
    | apply congrArg (fun T : Finset (graph S).edgeSet => T.card^4)
      ext e
      simp

/-- Dependence on the number of classes is cubic in the main term, rather than
    seventh-power dependence on the total block order. -/
theorem fourth_power_bound (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c)
    (hq : 2 < Fintype.card F)
    (H : SimpleGraph (MatGroup (F := F) ⊕ MatGroup (F := F))) (hHG : H ≤ graph S)
    (hH : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ (Fintype.card (MatGroup (F := F))*Fintype.card F)^4 *
      (192*S.card^3*(Fintype.card F-1)^4 + 10368*S.card^4) := by
  have hb := Erdos714MultiOrbit.fourth_power_bound (edgeAction S) (color S) (color_preserved S)
    (transitive_on_color S hS)
    (Fintype.card (MatGroup (F := F)) * Fintype.card F * (Fintype.card F - 1))
    (fun c => by
      convert color_card S hS c using 1
      congr 1
      ext e
      simp) (block S hS)
    (univ.filter (fun e : (graph S).edgeSet => e.val ∈ H.edgeSet))
    ((Fintype.card F - 2) * (Fintype.card F - 1))
    (192*S.card^3*(Fintype.card F-1)^4 + 10368*S.card^4)
    (fun c => by
      convert block_meeting_lower S hS c using 1
      apply sum_congr rfl
      intro k _
      congr 1
      ext e
      simp) (fun k a => by convert local_fourth S hS H hH k a using 1)
  simp only [Erdos714GraphAveraging.selected_edge_card H (graph S) hHG, ratio_card] at hb
  apply Nat.le_of_mul_le_mul_left (c := ((Fintype.card F-2)*(Fintype.card F-1))^4) _
    (pow_pos (Nat.mul_pos (by omega) (by omega)) 4)
  convert hb using 1 <;> ring

/-- A denominator-free density bound, valid also when the class set is empty. -/
theorem density_fourth_power (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c)
    (hq : 2 < Fintype.card F)
    (H : SimpleGraph (MatGroup (F := F) ⊕ MatGroup (F := F))) (hHG : H ≤ graph S)
    (hH : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    S.card*(Fintype.card F-1)^4*H.edgeFinset.card^4 ≤
      (192*(Fintype.card F-1)^4 + 10368*S.card)*(graph S).edgeFinset.card^4 := by
  have hb := Nat.mul_le_mul_left (S.card*(Fintype.card F-1)^4)
    (fourth_power_bound S hS hq H hHG hH)
  rw [edge_count, connection_card S hS]
  convert hb using 1
  ring


/-- At fixed retained edge fraction, sufficiently large fields allow only
    a bounded number of accepted elliptic classes. -/
theorem retained_fraction_class_bound (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c)
    (hq : 2 < Fintype.card F)
    (H : SimpleGraph (MatGroup (F := F) ⊕ MatGroup (F := F))) (hHG : H ≤ graph S)
    (hH : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (D : ℕ) (hretained : (graph S).edgeFinset.card ≤ D*H.edgeFinset.card)
    (hlarge : 12*D ≤ Fintype.card F-1) : S.card ≤ 384*D^4 := by
  by_cases hzero : S.card = 0
  · omega
  have hhost : 0 < (graph S).edgeFinset.card := by
    rw [edge_count, connection_card S hS]
    exact Nat.mul_pos Fintype.card_pos (Nat.mul_pos
      (Nat.mul_pos (Nat.pos_of_ne_zero hzero) (by omega)) (by omega))
  have he : 0 < H.edgeFinset.card := by
    by_contra! hn
    have hz : H.edgeFinset.card = 0 := by omega
    simp only [hz, mul_zero] at hretained
    omega
  have hlarge4 : 20736*D^4 ≤ (Fintype.card F-1)^4 := by
    convert Nat.pow_le_pow_left hlarge 4 using 1
    ring
  have hpow : (graph S).edgeFinset.card^4 ≤ D^4*H.edgeFinset.card^4 := by
    simpa only [mul_pow] using Nat.pow_le_pow_left hretained 4
  have hd := density_fourth_power S hS hq H hHG hH
  have hc : S.card*(Fintype.card F-1)^4 ≤
      D^4*(192*(Fintype.card F-1)^4+10368*S.card) := by
    apply Nat.le_of_mul_le_mul_right (c := H.edgeFinset.card^4) _ (pow_pos he 4)
    calc
      _ ≤ (192*(Fintype.card F-1)^4+10368*S.card)*(graph S).edgeFinset.card^4 := hd
      _ ≤ (192*(Fintype.card F-1)^4+10368*S.card)*(D^4*H.edgeFinset.card^4) :=
        Nat.mul_le_mul_left _ hpow
      _ = _ := by ring
  have hf : S.card*(Fintype.card F-1)^4 ≤ 384*D^4*(Fintype.card F-1)^4 := by
    have hl := Nat.mul_le_mul_left S.card hlarge4
    nlinarith
  exact Nat.le_of_mul_le_mul_right hf (pow_pos (by omega) 4)

/-- At fixed retained fraction, the free subgraph has the smaller q^6 scale
    once the field is larger than the explicit density-dependent threshold. -/
theorem retained_fraction_edge_bound (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c)
    (hq : 2 < Fintype.card F)
    (H : SimpleGraph (MatGroup (F := F) ⊕ MatGroup (F := F))) (hHG : H ≤ graph S)
    (hH : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (D : ℕ) (hretained : (graph S).edgeFinset.card ≤ D*H.edgeFinset.card)
    (hlarge : 12*D ≤ Fintype.card F-1) :
    H.edgeFinset.card ≤ 384*D^4*Fintype.card F^6 := by
  have hs := retained_fraction_class_bound S hS hq H hHG hH D hretained hlarge
  calc
    _ ≤ (graph S).edgeFinset.card := card_le_card (edgeFinset_subset_edgeFinset.mpr hHG)
    _ = Fintype.card (MatGroup (F := F))*(S.card*Fintype.card F*(Fintype.card F-1)) := by
      rw [edge_count, connection_card S hS]
    _ ≤ Fintype.card F^4 * ((384*D^4)*Fintype.card F*Fintype.card F) := by
      gcongr
      · exact matrix_card_bound
      · omega
    _ = _ := by ring

/-- No sparsity hypothesis on S is required here: an arbitrary constant-density
    thinning of any elliptic fusion cannot attain the critical scale for
    unbounded fields. -/
theorem retained_fraction_critical_bound (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c)
    (hq : 2 < Fintype.card F)
    (H : SimpleGraph (MatGroup (F := F) ⊕ MatGroup (F := F))) (hHG : H ≤ graph S)
    (hH : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (C D : ℕ) (hretained : (graph S).edgeFinset.card ≤ D*H.edgeFinset.card)
    (hcritical : Fintype.card F^7 ≤ C*H.edgeFinset.card) :
    Fintype.card F ≤ max (12*D+1) (384*C*D^4) := by
  by_cases hlarge : 12*D ≤ Fintype.card F-1
  · have hb := retained_fraction_edge_bound S hS hq H hHG hH D hretained hlarge
    have hc : Fintype.card F^6*Fintype.card F ≤ Fintype.card F^6*(384*C*D^4) := by
      calc
        _ = Fintype.card F^7 := by ring
        _ ≤ C*H.edgeFinset.card := hcritical
        _ ≤ C*(384*D^4*Fintype.card F^6) := Nat.mul_le_mul_left _ hb
        _ = _ := by ring
    exact (Nat.le_of_mul_le_mul_left hc (pow_pos (by omega) 6)).trans (le_max_right _ _)
  · have hc : Fintype.card F ≤ 12*D+1 := by omega
    exact hc.trans (le_max_left _ _)

#print axioms retained_fraction_class_bound
#print axioms retained_fraction_edge_bound
#print axioms retained_fraction_critical_bound

#print axioms local_fourth
#print axioms fourth_power_bound
#print axioms density_fourth_power
end Erdos714EllipticDensity
