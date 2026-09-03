import FormalConjecturesUtil
import Submission.GlobalThetaNinthPower

/-! A strengthened apex-theta upper exponent, obtained from all witnesses.
This uses the legacy graph-helper chain, not the compact one. -/
open Finset SimpleGraph Filter Asymptotics
namespace Erdos713ApexThetaNinth
open Erdos713GlobalTheta Erdos713GlobalThetaNinth
open Erdos713ApexThetaGraphPower (larger_bipartition)
set_option maxHeartbeats 2000000

/-- No assertion of exact extremality is needed for this finite bound. -/
theorem bipartite_power {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hfree : pattern.Free G) (hB : G.IsBipartite) (hn : 0 < Fintype.card V)
    (d K : ℕ)
    (hdeg : ∀ v, d ≤ Nat.card (G.neighborSet v) ∧ Nat.card (G.neighborSet v) ≤ K*d) :
    d^9 ≤ 1000000000000000*(K+1)^8*(Fintype.card V)^5 := by
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
  have hrowMax (a : S) : Nat.card {b : ↥Sᶜ // R a b} ≤ K*d := by
    let f : {b : ↥Sᶜ // R a b} → G.neighborSet a.val := fun b => ⟨b.val.val,b.property⟩
    have hf : Function.Injective f := by
      intro b c h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : G.neighborSet a.val => z.val) h
    exact (Nat.card_le_card_of_injective f hf).trans (hdeg a.val).2
  exact ninth_power R hfreeR (Fintype.card V) d (K*d) K hn hcard
    (Fintype.card_subtype_le _) hrow hcol hrowMax hmax le_rfl

/-- The real-degree formulation needed for an almost-regular transfer. -/
theorem real_bipartite_power {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hfree : pattern.Free G) (hB : G.IsBipartite) (hn : 0 < Fintype.card V)
    (R d : ℝ) (hR : 0 < R) (hd : 0 < d)
    (hdeg : ∀ v, d ≤ (Nat.card (G.neighborSet v) : ℝ) ∧
      (Nat.card (G.neighborSet v) : ℝ) ≤ R*d) :
    d^9 ≤ (512*1000000000000000*((⌈2*R⌉₊ : ℝ)+1)^8)*(Fintype.card V : ℝ)^5 := by
  classical
  let K := ⌈2*R⌉₊
  have hK : 2*R ≤ (K : ℝ) := Nat.le_ceil _
  have hn1 : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hn4 : (1 : ℝ) ≤ (Fintype.card V : ℝ)^5 := one_le_pow₀ hn1
  have hK8 : (1 : ℝ) ≤ ((K : ℝ)+1)^8 := one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) K; linarith)
  have hC : (512 : ℝ) ≤ 512*1000000000000000*((K : ℝ)+1)^8 := by nlinarith only [hK8]
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
    have hpR : (k : ℝ)^9 ≤ 1000000000000000*((K : ℝ)+1)^8*(Fintype.card V : ℝ)^5 := by exact_mod_cast hp
    calc
      _ ≤ (2*(k : ℝ))^9 := pow_le_pow_left₀ hd.le hdk 9
      _ = 512*(k : ℝ)^9 := by ring
      _ ≤ 512*(1000000000000000*((K : ℝ)+1)^8*(Fintype.card V : ℝ)^5) :=
        mul_le_mul_of_nonneg_left hpR (by positivity)
      _ = _ := by ring
  · have hsmall : d^9 ≤ (512 : ℝ) := by
      have hh := pow_le_pow_left₀ hd.le (le_of_not_ge hd2) 9
      norm_num at hh
      exact hh
    exact hsmall.trans (hC.trans (le_mul_of_one_le_right (by positivity) hn4))

/-- An unconditional upper exponent of 14/9 for the eight-vertex apex-theta. -/
theorem apex_theta_upper :
    (fun n : ℕ => (extremalNumber n Erdos713GlobalTheta.pattern : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^((14 : ℝ)/9)) := by
  have hh := Erdos713Suspension.upper_of_regular_power Erdos713GlobalTheta.pattern
    9 5 (by decide) (by decide) (by
      intro R hR
      refine ⟨512*1000000000000000*((⌈2*R⌉₊ : ℝ)+1)^8,by positivity,?_⟩
      intro V _ G hfree hB hn d hd hdeg
      exact real_bipartite_power G hfree hB hn R d hR hd hdeg)
  norm_num at hh ⊢
  exact hh

theorem upper_of_containment {W : Type*} {H : SimpleGraph W}
    (hH : H ⊑ Erdos713GlobalTheta.pattern) :
    (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^((14 : ℝ)/9)) :=
  (Erdos713Rate.extremal_mono_bigO hH).trans apex_theta_upper

theorem exponent_upper_of_containment {W : Type*} {H : SimpleGraph W}
    (hH : H ⊑ Erdos713GlobalTheta.pattern) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c*(n : ℝ)^a)) : a ≤ (14 : ℝ)/9 := by
  apply Erdos713Forest.exponent_le_of_isBigO
  exact ((isBigO_const_mul_left_iff hc).mp h.isBigO_symm).trans (upper_of_containment hH)

theorem rate_upper_of_containment {W : Type*} {H : SimpleGraph W}
    (hH : H ⊑ Erdos713GlobalTheta.pattern) {a : ℝ}
    (h : Erdos713Rate.HasRate H a) : a ≤ (14 : ℝ)/9 :=
  h.lower _ (by norm_num) (upper_of_containment hH)

#print axioms bipartite_power
#print axioms real_bipartite_power
#print axioms apex_theta_upper
#print axioms exponent_upper_of_containment
#print axioms rate_upper_of_containment
end Erdos713ApexThetaNinth
