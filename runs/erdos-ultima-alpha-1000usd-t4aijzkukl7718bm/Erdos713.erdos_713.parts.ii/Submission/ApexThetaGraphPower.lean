import FormalConjecturesUtil
import Submission.GlobalThetaSeventhPower

/-! The seventh-power estimate for ordinary bipartite graph hosts. -/
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

#print axioms larger_bipartition
#print axioms bipartite_power
#print axioms real_bipartite_power
end Erdos713ApexThetaGraphPower
