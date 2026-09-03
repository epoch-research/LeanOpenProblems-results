import FormalConjecturesUtil
import Submission.SuspensionRate
import Submission.ThetaLightPower

/-! This standalone transfer uses the LEGACY regularization chain.
Do not import it together with CompactEdgeAttachmentsAudit-based graph
helpers: the local graph and link declarations are intentionally reproduced
here to keep the two verified cache chains separate. No admitted main
conjecture is imported. -/

/- Exact whole-host link restrictions for the eight-vertex apex-theta
pattern. These restrictions do not yet give a sharp extremal bound. -/
open SimpleGraph Finset
namespace Erdos713GlobalTheta
set_option maxHeartbeats 2000000
open Erdos713ThetaGram Erdos713C6

/-- Rows 0,1 have the two common columns 0,1; row 2 joins columns 2,3. -/
def thetaRel (i : Fin 3) (j : Fin 4) : Prop :=
  Nat.testBit ((![7,11,12] : Fin 3 → ℕ) i) j.val = true

def apexRel (i : Option (Fin 3)) (j : Fin 4) : Prop := i.elim True (fun i => thetaRel i j)
abbrev pattern := bipGraph apexRel

def link {A B : Type*} (R : A → B → Prop) (d : A) :
    {a : A // a ≠ d} → {b : B // R d b} → Prop := fun a b => R a.val b.val

lemma pattern_contained_of_link {A B : Type*} (R : A → B → Prop) (d : A)
    (h : HasTheta (link R d)) : pattern ⊑ bipGraph R := by
  obtain ⟨a,b,ha,hb,h00,h10,h01,h11,h02,h22,h13,h23⟩ := h
  let f : Option (Fin 3) → A := fun i => i.elim d (fun i => (a i).val)
  have hf : Function.Injective f := Erdos713Theta3.option_injective d
    (fun i => (a i).val) (Subtype.val_injective.comp ha) (fun i => (a i).prop.symm)
  apply Erdos713Anchors.bipGraph_contained_of_maps apexRel (bipGraph R)
    (fun i => .inl (f i)) (fun j => .inr (b j).val)
    (Sum.inl_injective.comp hf) (Sum.inr_injective.comp (Subtype.val_injective.comp hb))
    (fun _ _ => Sum.inl_ne_inr) _
  intro i j hij
  cases i with
  | none => exact (b j).prop
  | some i =>
    change thetaRel i j at hij
    fin_cases i <;> fin_cases j <;> simp [thetaRel] at hij <;> first | contradiction | assumption

lemma no_theta_links {A B : Type*} {R : A → B → Prop} (h : pattern.Free (bipGraph R)) (d : A) :
    ¬ HasTheta (link R d) := fun hh => h (pattern_contained_of_link R d hh)

def transposeIso {A B : Type*} (R : A → B → Prop) :
    bipGraph (fun b a => R a b) ≃g bipGraph R :=
  ⟨Equiv.sumComm _ _,by rintro (a | a) (b | b) <;> rfl⟩

lemma no_theta_both_links {A B : Type*} {R : A → B → Prop} (h : pattern.Free (bipGraph R)) :
    (∀ d : A, ¬ HasTheta (link R d)) ∧
    (∀ d : B, ¬ HasTheta (link (fun b a => R a b) d)) := by
  refine ⟨no_theta_links h,?_⟩
  intro d hh
  exact h ((pattern_contained_of_link (fun b a => R a b) d hh).trans ⟨(transposeIso R).toCopy⟩)

/-- An explicit connection to row masks [3,13,14,15]. -/
def bitRel (i j : Fin 4) : Prop :=
  Nat.testBit ((![3,13,14,15] : Fin 4 → ℕ) i) j.val = true

noncomputable def bitIso : bipGraph bitRel ≃g pattern := by
  let f : Fin 4 → Option (Fin 3) := ![some 2,some 0,some 1,none]
  let g : Fin 4 → Fin 4 := ![2,3,0,1]
  let e : Fin 4 ≃ Option (Fin 3) := Equiv.ofBijective f ⟨by decide,by decide⟩
  let e' : Fin 4 ≃ Fin 4 := Equiv.ofBijective g ⟨by decide,by decide⟩
  refine ⟨Equiv.sumCongr e e',?_⟩
  rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [e,e',f,g,pattern,bipGraph,apexRel,thetaRel,bitRel] <;> decide

end Erdos713GlobalTheta

/- A conditional reduction, not an asserted local theta estimate.
The capped weighted hypothesis below remains unproved. -/
open Finset SimpleGraph
namespace Erdos713ConditionalThetaWeighted
open Erdos713GlobalLight Erdos713GlobalTheta Erdos713ThetaGram
open Erdos713ThetaCross Erdos713ThetaSplit
set_option maxHeartbeats 2000000

lemma card_restrict_ne_add_one {A : Type*} [Fintype A]
    (P : A → Prop) (d : A) (hd : P d) :
    Nat.card {a : {a : A // a ≠ d} // P a.val}+1 = Nat.card {a : A // P a} := by
  classical
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun a => a ≠ d) P)]
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have he : (univ.filter (fun a => a ≠ d ∧ P a)) = (univ.filter P).erase d := by
    ext a
    simp [and_comm]
  rw [he]
  exact card_erase_add_one (by simp [hd])

lemma link_codegree_add_one {A B : Type*} [Fintype A]
    (R : A → B → Prop) (d : A) (x y : {b : B // R d b}) :
    codegree (link R d) x y+1 = codegree R x.val y.val :=
  card_restrict_ne_add_one (fun a => R a x.val ∧ R a y.val) d ⟨x.property,y.property⟩

lemma link_column_add_one {A B : Type*} [Fintype A]
    (R : A → B → Prop) (d : A) (x : {b : B // R d b}) :
    Nat.card {a : {a : A // a ≠ d} // link R d a x}+1 = Nat.card {a : A // R a x.val} :=
  card_restrict_ne_add_one (fun a => R a x.val) d x.property

open scoped Classical in
lemma link_lightCount {A B : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) (d : A) :
    lightCount (link R d) = (lightPairs R 3 d).card := by
  classical
  let e : {p : {b : B // R d b} × {b : B // R d b} // codegree (link R d) p.1 p.2 ≤ 2} ≃
      ↥(lightPairs R 3 d) :=
    { toFun := fun p => ⟨(p.val.1.val,p.val.2.val),by
        have hc := link_codegree_add_one R d p.val.1 p.val.2
        have hp := p.property
        simp only [lightPairs,mem_filter,mem_univ,true_and]
        exact ⟨p.val.1.property,p.val.2.property,by omega⟩⟩
      invFun := fun p => by
        have hp := p.property
        simp only [lightPairs,mem_filter,mem_univ,true_and] at hp
        let x : {b : B // R d b} := ⟨p.val.1,hp.1⟩
        let y : {b : B // R d b} := ⟨p.val.2,hp.2.1⟩
        exact ⟨(x,y),by
          change codegree (link R d) x y ≤ 2
          have hc := link_codegree_add_one R d x y
          have hp' : codegree R x.val y.val ≤ 3 := hp.2.2
          omega⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (by simp)

lemma link_incidence_lower {A B : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) (a : A) (d : ℕ)
    (hrow : d ≤ Nat.card {b // R a b})
    (hcols : ∀ b, d ≤ Nat.card {a // R a b}) :
    d*(d-1) ≤ Nat.card {p : {x : A // x ≠ a} × {b : B // R a b} // link R a p.1 p.2} := by
  classical
  rw [edge_card_eq_cols]
  have hc (b : {b : B // R a b}) : d-1 ≤ Nat.card {x : {x : A // x ≠ a} // link R a x b} := by
    have hh := link_column_add_one R a b
    have hd := hcols b.val
    omega
  calc
    _ ≤ Nat.card {b // R a b}*(d-1) := Nat.mul_le_mul_right _ hrow
    _ = ∑ _b : {b : B // R a b}, (d-1) := by simp [Nat.card_eq_fintype_card]
    _ ≤ _ := sum_le_sum (fun b _ => hc b)

end Erdos713ConditionalThetaWeighted

/- An unconditional finite seventh-power degree inequality for the
apex-theta pattern. The previously proposed capped estimate is NOT used. -/
open Finset SimpleGraph
namespace Erdos713GlobalThetaSeventh
open Erdos713GlobalLight Erdos713GlobalTheta Erdos713ThetaCross
open Erdos713ConditionalThetaWeighted Erdos713ThetaLightPower
variable {A B : Type*}
set_option maxHeartbeats 2000000

lemma seventh_from_alternative {n d D K e : ℕ} (hn : 0 < n) (hdn : d ≤ n)
    (he : d*(d-1) ≤ e) (hD : D ≤ K*d)
    (halt : e ≤ 200*n ∨ e^4 ≤ 18432000*n^4*D) :
    d^7 ≤ 294912000*(K+1)*n^4 := by
  by_cases hd : 2 ≤ d
  · have hsub : d-1+1 = d := Nat.sub_add_cancel (by omega)
    have hd2 : d^2 ≤ 2*e := by nlinarith
    rcases halt with hl | hh
    · have hdsq : d^2 ≤ 400*n := by omega
      have hd6 := Nat.pow_le_pow_left hdsq 3
      calc
        d^7 = (d^2)^3*d := by ring
        _ ≤ (400*n)^3*n := Nat.mul_le_mul hd6 hdn
        _ = 64000000*n^4 := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    · have hd8 := Nat.pow_le_pow_left hd2 4
      have heD := Nat.mul_le_mul_left (18432000*n^4) hD
      have hb : d^7*d ≤ (294912000*K*n^4)*d := by
        calc
          _ = (d^2)^4 := by ring
          _ ≤ (2*e)^4 := hd8
          _ = 16*e^4 := by ring
          _ ≤ 16*(18432000*n^4*D) := Nat.mul_le_mul_left 16 hh
          _ ≤ 16*(18432000*n^4*(K*d)) := Nat.mul_le_mul_left 16 heD
          _ = _ := by ring
      have hcancel := Nat.le_of_mul_le_mul_right hb (by omega : 0 < d)
      exact hcancel.trans (by gcongr; omega)
  · interval_cases d
    · simp
    · have hn4 : 1 ≤ n^4 := Nat.one_le_pow _ _ (by omega)
      simpa only [one_pow] using hn4.trans (Nat.le_mul_of_pos_left _ (by omega))

/-- Choose the root on the larger shore. The whole-host light-pair budget,
theta exclusion in that link, and the degree bounds concern the SAME host. -/
theorem seventh_power [Fintype A] [Fintype B] [Nonempty A]
    (R : A → B → Prop) (hFree : pattern.Free (Erdos713C6.bipGraph R))
    (n d D K : ℕ) (hn : 0 < n)
    (hAB : Fintype.card B ≤ Fintype.card A) (hAn : Fintype.card A ≤ n)
    (hrows : ∀ a, d ≤ Nat.card {b // R a b})
    (hcols : ∀ b, d ≤ Nat.card {a // R a b})
    (hMax : ∀ b, Nat.card {a // R a b} ≤ D) (hRatio : D ≤ K*d) :
    d^7 ≤ 294912000*(K+1)*n^4 := by
  classical
  obtain ⟨a,ha⟩ := exists_row_with_few_light_pairs R 3
  have ht : (lightPairs R 3 a).card ≤ 3*n := by
    have hab2 := Nat.pow_le_pow_left hAB 2
    have hprod : Fintype.card A*(lightPairs R 3 a).card ≤ Fintype.card A*(3*Fintype.card A) := by
      calc
        _ ≤ 3*(Fintype.card B)^2 := ha
        _ ≤ 3*(Fintype.card A)^2 := Nat.mul_le_mul_left 3 hab2
        _ = _ := by ring
    have hh := Nat.le_of_mul_le_mul_left hprod (Fintype.card_pos (α := A))
    omega
  have htR : lightCount (link R a) ≤ 3*n := by rwa [link_lightCount]
  have hCap (b : {b // R a b}) : Nat.card {x : {x : A // x ≠ a} // link R a x b} ≤ D := by
    have hh := link_column_add_one R a b
    have hh' := hMax b.val
    omega
  have hm : Fintype.card {x : A // x ≠ a} ≤ n :=
    (Fintype.card_subtype_le _).trans hAn
  have hAlt := fourth_power_alternative (no_theta_links hFree a) n D hn hm htR hCap
  have hlo := link_incidence_lower R a d (hrows a) hcols
  have hdB : d ≤ Fintype.card B := (hrows a).trans (by
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_le (R a))
  exact seventh_from_alternative hn (hdB.trans (hAB.trans hAn)) hlo hRatio hAlt

end Erdos713GlobalThetaSeventh

/- The seventh-power estimate for ordinary bipartite graph hosts. -/
open Finset SimpleGraph
namespace Erdos713ApexThetaGraphPower
open Erdos713GlobalTheta Erdos713GlobalThetaSeventh
set_option maxHeartbeats 2000000

open scoped Classical in
lemma larger_bipartition {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hB : G.IsBipartite) :
    ∃ S : Set V, G.IsBipartiteWith S Sᶜ ∧ Nat.card ↥Sᶜ ≤ Nat.card S := by
  classical
  obtain ⟨χ⟩ := hB
  let S : Set V := {v | χ v = 0}
  have hS : G.IsBipartiteWith S Sᶜ := by
    refine ⟨disjoint_compl_right,?_⟩
    intro u v huv
    have hχ := χ.valid huv
    simp only [S,Set.mem_setOf_eq,Set.mem_compl_iff]
    omega
  by_cases hc : Nat.card ↥Sᶜ ≤ Nat.card S
  · exact ⟨S,hS,hc⟩
  · refine ⟨Sᶜ,?_,?_⟩
    · simpa only [compl_compl] using hS.symm
    · simpa only [compl_compl] using (Nat.le_of_lt (Nat.lt_of_not_ge hc))

/-- No assertion of exact extremality is needed for this finite bound. -/
theorem bipartite_power {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hfree : pattern.Free G) (hB : G.IsBipartite) (hn : 0 < Fintype.card V)
    (d K : ℕ)
    (hdeg : ∀ v, d ≤ Nat.card (G.neighborSet v) ∧ Nat.card (G.neighborSet v) ≤ K*d) :
    d^7 ≤ 294912000*(K+1)*(Fintype.card V)^4 := by
  classical
  obtain ⟨S,hS,hcard⟩ := larger_bipartition G hB
  have hcard : Fintype.card ↥Sᶜ ≤ Fintype.card S := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hsum : Fintype.card S + Fintype.card ↥Sᶜ = Fintype.card V := by
    simpa using Fintype.card_congr (Equiv.Set.sumCompl S)
  have hpos : 0 < Fintype.card S := by omega
  letI : Nonempty S := Fintype.card_pos_iff.mp hpos
  let R : S → ↥Sᶜ → Prop := fun a b => G.Adj a.val b.val
  have hcontain : Erdos713C6.bipGraph R ⊑ G :=
    Erdos713Anchors.bipGraph_contained_of_maps R G Subtype.val Subtype.val
      Subtype.val_injective Subtype.val_injective
      (fun a b h => b.property (h ▸ a.property)) (fun _ _ h => h)
  have hfreeR : pattern.Free (Erdos713C6.bipGraph R) := fun h => hfree (h.trans hcontain)
  have hrow (a : S) : d ≤ Nat.card {b : ↥Sᶜ // R a b} := by
    let f : G.neighborSet a.val → {b : ↥Sᶜ // R a b} := fun b =>
      ⟨⟨b.val,hS.mem_of_mem_adj a.property b.property⟩,b.property⟩
    have hf : Function.Injective f := by
      intro b c h
      apply Subtype.ext
      exact congrArg (fun z => z.val.val) h
    exact (hdeg a.val).1.trans (Nat.card_le_card_of_injective f hf)
  have hcol (b : ↥Sᶜ) : d ≤ Nat.card {a : S // R a b} := by
    let f : G.neighborSet b.val → {a : S // R a b} := fun a =>
      ⟨⟨a.val,hS.mem_of_mem_adj' b.property a.property.symm⟩,a.property.symm⟩
    have hf : Function.Injective f := by
      intro a c h
      apply Subtype.ext
      exact congrArg (fun z => z.val.val) h
    exact (hdeg b.val).1.trans (Nat.card_le_card_of_injective f hf)
  have hmax (b : ↥Sᶜ) : Nat.card {a : S // R a b} ≤ K*d := by
    let f : {a : S // R a b} → G.neighborSet b.val := fun a => ⟨a.val.val,a.property.symm⟩
    have hf : Function.Injective f := by
      intro a c h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : G.neighborSet b.val => z.val) h
    exact (Nat.card_le_card_of_injective f hf).trans (hdeg b.val).2
  exact seventh_power R hfreeR (Fintype.card V) d (K*d) K hn hcard
    (Fintype.card_subtype_le _) hrow hcol hmax le_rfl

/-- The real-degree formulation needed for an almost-regular transfer. -/
theorem real_bipartite_power {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hfree : pattern.Free G) (hB : G.IsBipartite) (hn : 0 < Fintype.card V)
    (R d : ℝ) (hR : 0 < R) (hd : 0 < d)
    (hdeg : ∀ v, d ≤ (Nat.card (G.neighborSet v) : ℝ) ∧
      (Nat.card (G.neighborSet v) : ℝ) ≤ R*d) :
    d^7 ≤ (128*294912000*((⌈2*R⌉₊ : ℝ)+1))*(Fintype.card V : ℝ)^4 := by
  classical
  let K := ⌈2*R⌉₊
  have hK : 2*R ≤ (K : ℝ) := Nat.le_ceil _
  have hn1 : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hn4 : (1 : ℝ) ≤ (Fintype.card V : ℝ)^4 := one_le_pow₀ hn1
  have hC : (128 : ℝ) ≤ 128*294912000*((K : ℝ)+1) := by nlinarith [Nat.cast_nonneg (α := ℝ) K]
  by_cases hd2 : 2 ≤ d
  · let k := ⌊d⌋₊
    have hk : (k : ℝ) ≤ d := Nat.floor_le hd.le
    have hk1 : 1 ≤ k := Nat.le_floor (by norm_num; linarith)
    have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hdlt : d < (k : ℝ)+1 := Nat.lt_floor_add_one d
    have hdk : d ≤ 2*(k : ℝ) := by linarith
    have hnat (v : V) : k ≤ Nat.card (G.neighborSet v) ∧ Nat.card (G.neighborSet v) ≤ K*k := by
      constructor
      · exact_mod_cast hk.trans (hdeg v).1
      · have hh : (Nat.card (G.neighborSet v) : ℝ) ≤ (K : ℝ)*(k : ℝ) := by
          calc
            _ ≤ R*d := (hdeg v).2
            _ ≤ R*(2*(k : ℝ)) := mul_le_mul_of_nonneg_left hdk hR.le
            _ = (2*R)*(k : ℝ) := by ring
            _ ≤ (K : ℝ)*(k : ℝ) := mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg _)
        exact_mod_cast hh
    have hp := bipartite_power G hfree hB hn k K hnat
    have hpR : (k : ℝ)^7 ≤ 294912000*((K : ℝ)+1)*(Fintype.card V : ℝ)^4 := by exact_mod_cast hp
    calc
      _ ≤ (2*(k : ℝ))^7 := pow_le_pow_left₀ hd.le hdk 7
      _ = 128*(k : ℝ)^7 := by ring
      _ ≤ 128*(294912000*((K : ℝ)+1)*(Fintype.card V : ℝ)^4) :=
        mul_le_mul_of_nonneg_left hpR (by positivity)
      _ = _ := by ring
  · have hsmall : d^7 ≤ (128 : ℝ) := by
      have hh := pow_le_pow_left₀ hd.le (le_of_not_ge hd2) 7
      norm_num at hh
      exact hh
    exact hsmall.trans (hC.trans (le_mul_of_one_le_right (by positivity) hn4))

end Erdos713ApexThetaGraphPower

open Filter Asymptotics SimpleGraph
namespace Erdos713ApexThetaGraphPower
/-- An unconditional extremal upper bound for the eight-vertex apex-theta. -/
theorem apex_theta_upper :
    (fun n : ℕ => (extremalNumber n Erdos713GlobalTheta.pattern : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^((11 : ℝ)/7)) := by
  have hh := Erdos713Suspension.upper_of_regular_power Erdos713GlobalTheta.pattern
    7 4 (by decide) (by decide) (by
      intro R hR
      refine ⟨128*294912000*((⌈2*R⌉₊ : ℝ)+1),by positivity,?_⟩
      intro V _ G hfree hB hn d hd hdeg
      exact real_bipartite_power G hfree hB hn R d hR hd hdeg)
  norm_num at hh ⊢
  exact hh

theorem upper_of_containment {W : Type*} {H : SimpleGraph W}
    (hH : H ⊑ Erdos713GlobalTheta.pattern) :
    (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^((11 : ℝ)/7)) :=
  (Erdos713Rate.extremal_mono_bigO hH).trans apex_theta_upper

theorem exponent_upper_of_containment {W : Type*} {H : SimpleGraph W}
    (hH : H ⊑ Erdos713GlobalTheta.pattern) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c*(n : ℝ)^a)) : a ≤ (11 : ℝ)/7 := by
  apply Erdos713Forest.exponent_le_of_isBigO
  exact ((isBigO_const_mul_left_iff hc).mp h.isBigO_symm).trans (upper_of_containment hH)

theorem rate_upper_of_containment {W : Type*} {H : SimpleGraph W}
    (hH : H ⊑ Erdos713GlobalTheta.pattern) {a : ℝ}
    (h : Erdos713Rate.HasRate H a) : a ≤ (11 : ℝ)/7 :=
  h.lower _ (by norm_num) (upper_of_containment hH)

#print axioms Erdos713ThetaAnchorPacking.root_anchor_bound
#print axioms real_bipartite_power
#print axioms apex_theta_upper
#print axioms upper_of_containment
#print axioms exponent_upper_of_containment
#print axioms rate_upper_of_containment
end Erdos713ApexThetaGraphPower
