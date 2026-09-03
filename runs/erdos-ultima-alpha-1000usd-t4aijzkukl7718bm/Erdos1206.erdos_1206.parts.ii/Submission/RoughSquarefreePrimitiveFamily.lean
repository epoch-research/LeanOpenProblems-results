import Submission.RoughSquarefreeConicSieve
import Submission.NearUnitPrimitiveMass

/-! Normalized primitive members of the squarefree rough conic family.
No independence or Sidon-root-density estimate is asserted. -/
namespace Erdos1206.RoughSquarefreePrimitiveFamily
open Finset Filter RoughSquarefreeConicSetup
open PrimitiveCollisionMass (Collision)
open scoped Classical Topology

structure Progression (D : Data) where
  M : ℕ
  v : ℕ
  w : ℕ
  M_pos : 0 < M
  v_pos : 0 < v
  w_pos : 0 < w
  coprime : ∀ i t u, Nat.Coprime (D.F i (M*t+v) (M*u+w)) D.q
  many : ∀ᶠ N : ℕ in atTop, (N:ℝ)^2/2 ≤
    (((range N) ×ˢ (range N)).filter (fun x =>
      ∀ i, Squarefree (D.F i (M*x.1+v) (M*x.2+w)))).card

lemma exists_progression (D : Data) : Nonempty (Progression D) := by
  obtain ⟨M,v,w,hM,hv,hw,hc,hg⟩ := RoughSquarefreeConicSieve.exists_sieved_progression D
  exact ⟨⟨M,v,w,hM,hv,hw,hc,hg⟩⟩

namespace Progression
variable {D : Data} (P : Progression D)
def T (x : ℕ × ℕ) : ℕ := P.M*x.1+P.v
def U (x : ℕ × ℕ) : ℕ := P.M*x.2+P.w
def root (i : Fin 4) (x : ℕ × ℕ) : ℕ := D.F i (P.T x) (P.U x)
def Good (x : ℕ × ℕ) : Prop := ∀ i, Squarefree (P.root i x)
abbrev Index := {x : ℕ × ℕ // P.Good x}

lemma T_pos (x : ℕ × ℕ) : 0 < P.T x := by dsimp [T]; have := P.v_pos; omega
lemma U_pos (x : ℕ × ℕ) : 0 < P.U x := by dsimp [U]; have := P.w_pos; omega
lemma ordered (x : ℕ × ℕ) : 0 < P.root 0 x ∧ P.root 0 x < P.root 1 x ∧
    P.root 1 x < P.root 2 x ∧ P.root 2 x < P.root 3 x := D.ordered (P.T_pos x) (P.U x)
lemma root_pos (i : Fin 4) (x : ℕ × ℕ) : 0 < P.root i x := by
  obtain ⟨ha,hab,hbc,hcd⟩ := P.ordered x
  fin_cases i
  · exact ha
  · exact ha.trans hab
  · exact (ha.trans hab).trans hbc
  · exact ((ha.trans hab).trans hbc).trans hcd
lemma root_coprime (i : Fin 4) (x : ℕ × ℕ) : Nat.Coprime (P.root i x) D.q :=
  P.coprime i x.1 x.2

private lemma lift (x : P.Index) : ∃ e : Collision, ∃ g : ℕ, 0 < g ∧
    P.root 0 x.val=g*e.val.1 ∧ P.root 1 x.val=g*e.val.2.1 ∧
    P.root 2 x.val=g*e.val.2.2.1 ∧ P.root 3 x.val=g*e.val.2.2.2 := by
  obtain ⟨ha,hab,hbc,hcd⟩ := P.ordered x.val
  have he := D.identity (P.T x.val) (P.U x.val)
  obtain ⟨e,g,hg,ha',hb',hc',hd'⟩ := NearUnitPrimitiveMass.primitive_lift
    (by exact_mod_cast ha : (0:ℤ) < P.root 0 x.val)
    (by exact_mod_cast hab : (P.root 0 x.val:ℤ) < P.root 1 x.val)
    (by exact_mod_cast hbc : (P.root 1 x.val:ℤ) < P.root 2 x.val)
    (by exact_mod_cast hcd : (P.root 2 x.val:ℤ) < P.root 3 x.val)
    (by exact_mod_cast he)
  refine ⟨e,g,hg,?_,?_,?_,?_⟩
  · exact_mod_cast ha'
  · exact_mod_cast hb'
  · exact_mod_cast hc'
  · exact_mod_cast hd' 

noncomputable def collision (x : P.Index) : Collision := (P.lift x).choose
noncomputable def scale (x : P.Index) : ℕ := (P.lift x).choose_spec.choose
lemma scale_spec (x : P.Index) : 0 < P.scale x ∧
    P.root 0 x.val=P.scale x*(P.collision x).val.1 ∧
    P.root 1 x.val=P.scale x*(P.collision x).val.2.1 ∧
    P.root 2 x.val=P.scale x*(P.collision x).val.2.2.1 ∧
    P.root 3 x.val=P.scale x*(P.collision x).val.2.2.2 :=
  (P.lift x).choose_spec.choose_spec

lemma collision_injective : Function.Injective P.collision := by
  intro x y he
  obtain ⟨hg,h0,h1,h2,h3⟩ := P.scale_spec x
  obtain ⟨hh,h0',h1',h2',h3'⟩ := P.scale_spec y
  rw [←he] at h0' h1' h2' h3'
  have hF0 : P.scale y*P.root 0 x.val=P.scale x*P.root 0 y.val := by rw [h0,h0']; ring
  have hF1 : P.scale y*P.root 1 x.val=P.scale x*P.root 1 y.val := by rw [h1,h1']; ring
  have hF2 : P.scale y*P.root 2 x.val=P.scale x*P.root 2 y.val := by rw [h2,h2']; ring
  have hcross := D.scaled_parameter (P.T_pos x.val) hh hF0 hF1 hF2
  have hcx := D.coprime_parameters (x.property 0)
  have hcy := D.coprime_parameters (y.property 0)
  obtain ⟨ht,hu⟩ := Data.coprime_pair_eq (P.T_pos x.val) (P.T_pos y.val) hcx hcy hcross
  apply Subtype.ext
  apply Prod.ext
  · dsimp [T] at ht
    exact Nat.eq_of_mul_eq_mul_left P.M_pos (Nat.add_right_cancel ht)
  · dsimp [U] at hu
    exact Nat.eq_of_mul_eq_mul_left P.M_pos (Nat.add_right_cancel hu)

lemma collision_properties (x : P.Index) :
    D.H*((P.collision x).val.2.1-(P.collision x).val.1) <
      (D.H+1)*((P.collision x).val.2.2.2-(P.collision x).val.2.2.1) ∧
    (Squarefree (P.collision x).val.1 ∧ Nat.Coprime (P.collision x).val.1 D.q) ∧
    (Squarefree (P.collision x).val.2.1 ∧ Nat.Coprime (P.collision x).val.2.1 D.q) ∧
    (Squarefree (P.collision x).val.2.2.1 ∧ Nat.Coprime (P.collision x).val.2.2.1 D.q) ∧
    (Squarefree (P.collision x).val.2.2.2 ∧ Nat.Coprime (P.collision x).val.2.2.2 D.q) := by
  obtain ⟨hg,h0,h1,h2,h3⟩ := P.scale_spec x
  have hdiv (i : Fin 4) (v : ℕ) (he : P.root i x.val=P.scale x*v) :
      v ∣ P.root i x.val := by rw [he]; exact dvd_mul_left _ _
  have hs (i : Fin 4) (v : ℕ) (he : P.root i x.val=P.scale x*v) :
      Squarefree v ∧ Nat.Coprime v D.q :=
    ⟨(x.property i).squarefree_of_dvd (hdiv i v he),
      Nat.Coprime.of_dvd_left (hdiv i v he) (P.root_coprime i x.val)⟩
  refine ⟨?_,hs 0 _ h0,hs 1 _ h1,hs 2 _ h2,hs 3 _ h3⟩
  have hh := D.near_unit_gap (P.T_pos x.val) (P.U x.val)
  change D.H*(P.root 1 x.val-P.root 0 x.val) < (D.H+1)*(P.root 3 x.val-P.root 2 x.val) at hh
  rw [h0,h1,h2,h3,←Nat.mul_sub_left_distrib,←Nat.mul_sub_left_distrib] at hh
  have he : P.scale x*(D.H*((P.collision x).val.2.1-(P.collision x).val.1)) <
      P.scale x*((D.H+1)*((P.collision x).val.2.2.2-(P.collision x).val.2.2.1)) := by
    nlinarith only [hh]
  exact (Nat.mul_lt_mul_left hg).mp he

end Progression
#print axioms Progression.collision_injective
#print axioms Progression.collision_properties
end Erdos1206.RoughSquarefreePrimitiveFamily
