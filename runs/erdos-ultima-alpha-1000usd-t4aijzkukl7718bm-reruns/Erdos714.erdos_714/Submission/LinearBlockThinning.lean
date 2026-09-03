import Submission.LinearBlockMoments

/-! An arbitrary-edge-thinning bound for a complementary linear-block incidence chart. -/
noncomputable section
open Finset SimpleGraph Classical Module
set_option maxHeartbeats 3000000
namespace Erdos714LinearBlocks
open Erdos714Packing

section Restriction
variable {C D : Type*} [Fintype C] [Fintype D]

def NoRectangle (E : Finset (C × D)) : Prop :=
  ∀ f : Fin 4 ↪ C, ∀ g : Fin 4 ↪ D, ¬ ∀ i j, (f i,g j) ∈ E

def blockEdges (E : Finset (C × D)) (S : Finset C) (T : Finset D) : Finset (C × D) :=
  E.filter (fun p => p.1 ∈ S ∧ p.2 ∈ T)

def blockNeighbors (E : Finset (C × D)) (S : Finset C) (T : Finset D) (c : S) : Finset T :=
  univ.filter (fun d => (c.val,d.val) ∈ E)

def blockEdgeEquiv (E : Finset (C × D)) (S : Finset C) (T : Finset D) :
    (Σ c : S, {d : T // (c.val,d.val) ∈ E}) ≃ blockEdges E S T where
  toFun p := ⟨(p.1.val,p.2.val.val), mem_filter.mpr ⟨p.2.property,p.1.property,p.2.val.property⟩⟩
  invFun p := ⟨⟨p.val.1,(mem_filter.mp p.property).2.1⟩,
    ⟨⟨p.val.2,(mem_filter.mp p.property).2.2⟩,(mem_filter.mp p.property).1⟩⟩
  left_inv p := by rcases p with ⟨⟨c,hc⟩,⟨⟨d,hd⟩,he⟩⟩; rfl
  right_inv p := by rcases p with ⟨⟨c,d⟩,hp⟩; rfl

lemma block_neighbor_sum (E : Finset (C × D)) (S : Finset C) (T : Finset D) :
    (∑ c : S, (blockNeighbors E S T c).card) = (blockEdges E S T).card := by
  have h := Fintype.card_congr (blockEdgeEquiv E S T)
  simpa only [Fintype.card_sigma, Fintype.card_subtype, Fintype.card_coe, blockNeighbors, filter_mem_eq_inter, univ_inter] using h

lemma block_power_bound (E : Finset (C × D)) (hE : NoRectangle E) (S : Finset C) (T : Finset D) :
    ((blockEdges E S T).card-3*S.card)^4 ≤ 3*S.card^3*T.card^4 := by
  have hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence (blockNeighbors E S T)) := by
    apply (free_iff_no_rectangle _ (by decide : 0 < 4)).mpr
    intro f g hfg
    apply hE (f.trans (Function.Embedding.subtype _)) (g.trans (Function.Embedding.subtype _))
    intro i j
    exact (mem_filter.mp (hfg i j)).2
  have h := Erdos714Unbalanced.power_bound (blockNeighbors E S T) (by decide : 1 ≤ 4) hf
  simpa only [block_neighbor_sum, Fintype.card_coe, Nat.reduceSub] using h
end Restriction

variable {F V C D : Type*} [Field F] [Fintype F]
  [AddCommGroup V] [Module F V] [Fintype V] [FiniteDimensional F V] [Fintype C] [Fintype D]
local instance : Fintype (End (F := F) (V := V)) := endFintype
local instance : Fintype (Module.Dual F V) := dualFintype

lemma block_edge_coverage (hd : finrank F V = 3)
    (R : C → V × V) (T : D → Module.Dual F V × Module.Dual F V)
    (hR : ∀ c, (R c).1 ≠ 0) (hT : ∀ d, (T d).1 ≠ 0)
    (E : Finset (C × D)) (hE : ∀ p ∈ E, (T p.2).1 (R p.1).2 = (T p.2).2 (R p.1).1) :
    Fintype.card F^4*E.card = ∑ f, (blockEdges E (rows R f) (columns T f)).card := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun f (p : C × D) => p.1 ∈ rows (F := F) R f ∧ p.2 ∈ columns T f)
    (s := (univ : Finset (End (F := F) (V := V)))) (t := E)
  change (∑ f, (blockEdges E (rows R f) (columns T f)).card) =
    ∑ p ∈ E, (univ.filter (fun f => p.1 ∈ rows R f ∧ p.2 ∈ columns T f)).card at h
  rw [h]
  have hc (p : C × D) (hp : p ∈ E) :
      (univ.filter (fun f => p.1 ∈ rows R f ∧ p.2 ∈ columns T f)).card = Fintype.card F^4 := by
    simpa only [rows, columns, mem_filter, mem_univ, true_and] using
      paired_count hd (R p.1).1 (R p.1).2 (T p.2).1 (T p.2).2 (hR p.1) (hT p.2) (hE p hp)
  rw [sum_congr rfl hc]
  simp [mul_comm]

/-- Integer-parameter bound, using all actual incidences and both second moments. -/
theorem chart_bound (hd : finrank F V = 3)
    (R : C → V × V) (T : D → Module.Dual F V × Module.Dual F V)
    (hR : RayInjective (F := F) R) (hT : RayInjective (F := F) T)
    (hnR : ∀ c, (R c).1 ≠ 0) (hnT : ∀ d, (T d).1 ≠ 0)
    (E : Finset (C × D)) (hfree : NoRectangle E)
    (hE : ∀ p ∈ E, (T p.2).1 (R p.1).2 = (T p.2).2 (R p.1).1)
    (hC : Fintype.card C ≤ Fintype.card F^4) (hD : Fintype.card D ≤ Fintype.card F^4)
    (u : ℕ) (hu : Fintype.card F^3 ≤ u^4) :
    E.card ≤ 13*u*Fintype.card F^6 := by
  let q := Fintype.card F
  have hq : 0 < q := Fintype.card_pos
  have hq1 : 1 ≤ q := hq
  have hu1 : 1 ≤ u := by
    by_contra! h
    have hu0 : u = 0 := by omega
    exact (not_le_of_gt (pow_pos (show 0 < Fintype.card F from Fintype.card_pos) 3)) (by simpa [hu0] using hu)
  have hm := row_moments hd R hR hnR
  have hn := column_moments hd T hT hnT
  have hcover := block_edge_coverage hd R T hnR hnT E hE
  have hb := Erdos714BlockMoment.bound
    (fun f => (blockEdges E (rows R f) (columns T f)).card)
    (fun f => (rows R f).card) (fun f => (columns T f).card)
    q u (q^4) E.card (q^6*Fintype.card C+q^3*Fintype.card C^2)
    (q^6*Fintype.card D+q^3*Fintype.card D^2) (q^6*Fintype.card C)
    (fun f => block_power_bound E hfree _ _) hu hcover.le hm.2 hn.2 hm.1
  rw [block_count hd] at hb
  have ha : q^6*Fintype.card C+q^3*Fintype.card C^2 ≤ 2*q^11 := by
    calc
      _ ≤ q^6*q^4+q^3*(q^4)^2 := by gcongr
      _ = q^10+q^11 := by ring
      _ ≤ 2*q^11 := by have : q^10 ≤ q^11 := Nat.pow_le_pow_right hq1 (by omega); omega
  have hb' : q^6*Fintype.card D+q^3*Fintype.card D^2 ≤ 2*q^11 := by
    calc
      _ ≤ q^6*q^4+q^3*(q^4)^2 := by gcongr
      _ = q^10+q^11 := by ring
      _ ≤ 2*q^11 := by have : q^10 ≤ q^11 := Nat.pow_le_pow_right hq1 (by omega); omega
  have hc : q^6*Fintype.card C ≤ q^10 := by calc
    _ ≤ q^6*q^4 := Nat.mul_le_mul_left _ hC
    _ = _ := by ring
  have he : q^5*E.card ≤ q^5*(13*u*q^6) := by
    calc
      _ = q*q^4*E.card := by ring
      _ ≤ _ := hb
      _ ≤ 3*q*q^10+2*u*(2*q^11+2*q^11+q^9*q^2) := by gcongr
      _ = (3+10*u)*q^11 := by ring
      _ ≤ (13*u)*q^11 := by gcongr; omega
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left he (by positivity)

/-- A rounded fourth root costs at most a fixed factor, even at small positive orders. -/
lemma rounded_fourth_root (q : ℕ) (hq : 0 < q) :
    ∃ u : ℕ, q^3 ≤ u^4 ∧ u^4 ≤ 16*q^3 := by
  let a := (q^3).sqrt.sqrt
  have hlow : a^4 ≤ q^3 := by
    calc
      _ = (a*a)^2 := by ring
      _ ≤ ((q^3).sqrt)^2 := Nat.pow_le_pow_left (Nat.sqrt_le _) 2
      _ = (q^3).sqrt*(q^3).sqrt := by ring
      _ ≤ _ := Nat.sqrt_le _
  have ha : 0 < a := by simp only [a, Nat.sqrt_pos]; positivity
  have hhigh : q^3 < (a+1)^4 := by
    have h₁ := Nat.lt_succ_sqrt' (q^3)
    have h₂ := Nat.lt_succ_sqrt' (q^3).sqrt
    have h₃ : (q^3).sqrt+1 ≤ (a+1)^2 := by simpa only [Nat.succ_eq_add_one] using h₂
    calc
      _ < ((q^3).sqrt+1)^2 := h₁
      _ ≤ ((a+1)^2)^2 := Nat.pow_le_pow_left h₃ 2
      _ = _ := by ring
  refine ⟨a+1, hhigh.le, ?_⟩
  calc
    _ ≤ (2*a)^4 := Nat.pow_le_pow_left (by omega) 4
    _ = 16*a^4 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hlow

/-- Every free thinning of this six-dimensional chart loses a power of q. -/
theorem chart_fourth_power (hd : finrank F V = 3)
    (R : C → V × V) (T : D → Module.Dual F V × Module.Dual F V)
    (hR : RayInjective (F := F) R) (hT : RayInjective (F := F) T)
    (hnR : ∀ c, (R c).1 ≠ 0) (hnT : ∀ d, (T d).1 ≠ 0)
    (E : Finset (C × D)) (hfree : NoRectangle E)
    (hE : ∀ p ∈ E, (T p.2).1 (R p.1).2 = (T p.2).2 (R p.1).1)
    (hC : Fintype.card C ≤ Fintype.card F^4) (hD : Fintype.card D ≤ Fintype.card F^4) :
    E.card^4 ≤ 456976*Fintype.card F^27 := by
  obtain ⟨u, hu, hu'⟩ := rounded_fourth_root (Fintype.card F) Fintype.card_pos
  have he := chart_bound hd R T hR hT hnR hnT E hfree hE hC hD u hu
  calc
    _ ≤ (13*u*Fintype.card F^6)^4 := Nat.pow_le_pow_left he 4
    _ = 13^4*u^4*Fintype.card F^24 := by ring
    _ ≤ 13^4*(16*Fintype.card F^3)*Fintype.card F^24 := by gcongr
    _ = _ := by ring

#print axioms block_power_bound
#print axioms block_edge_coverage
#print axioms chart_bound
#print axioms chart_fourth_power
end Erdos714LinearBlocks
