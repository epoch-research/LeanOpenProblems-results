import Submission.BinaryAcceptingMinplusCertificates

/-! Arithmetic simulation with a finite or infinite collection of output profiles.
A profile keeps several bounded output runs, allowing the final endpoint choice
to depend on later input. No sufficient numerical instance is asserted here. -/
namespace Erdos406BinaryProfileMinplus
open Erdos406GroupedCertificate
open Erdos406Tropical (Automaton Run)
open Erdos406BinaryAcceptingMinplus
variable {σ τ : Type*} [Fintype σ] [DecidableEq σ]

structure Construction (D : Automaton σ) (F : σ → Prop) (τ : Type*) where
  endpoints : τ → σ → Prop
  R : σ → τ → ℕ → Prop
  H : σ → τ → ℕ → σ → ℝ
  seed : ∀ c, c < 3 → ∃ p, R D.start p c ∧ ∀ t, endpoints p t →
    ∃ v, Run D D.start (Nat.digits 2 c).reverse t v ∧ v ≤ H D.start p c t
  step : ∀ s p c d e cp, c < 3 → d < 2 → e < 2 → cp < 3 →
    3*d+cp = 2*c+e → R s p c → ∀ sp, sp ∈ D.next s d →
    ∃ pp, R sp pp cp ∧ ∀ tp, endpoints pp tp →
      ∃ t, endpoints p t ∧ tp ∈ D.next t e ∧
        H s p c t + D.weight t e tp-D.weight s d sp ≤ H sp pp cp tp
  finish : ∀ s p c, c < 2 → R s p c → F s →
    ∃ t, endpoints p t ∧ F t ∧ H s p c t ≤ 1

namespace Construction
variable {D : Automaton σ} {F : σ → Prop} (C : Construction D F τ)
include C

lemma simulate (n c : ℕ) (hc : c < 3) {s v}
    (hin : Run D D.start (Nat.digits 2 n).reverse s v) :
    ∃ p, C.R s p c ∧ ∀ t, C.endpoints p t →
      ∃ u, Run D D.start (Nat.digits 2 (3*n+c)).reverse t u ∧ u-v ≤ C.H s p c t := by
  induction n using Nat.strong_induction_on generalizing c s v with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp only [Nat.digits_zero,List.reverse_nil] at hin
      cases hin
      obtain ⟨p,hr,hp⟩ := C.seed c hc
      refine ⟨p,hr,?_⟩
      intro t ht
      obtain ⟨u,hu,hh⟩ := hp t ht
      exact ⟨u,by simpa using hu,by simpa using hh⟩
    · have hp : 0 < n := Nat.pos_of_ne_zero hn
      let d := n%2
      let cp := (3*d+c)/2
      let e := (3*d+c)%2
      have hd : d < 2 := Nat.mod_lt _ (by decide)
      have he : e < 2 := Nat.mod_lt _ (by decide)
      have hcp : cp < 3 := by dsimp [cp]; omega
      have hid : 3*d+c = 2*cp+e := by dsimp [cp,e]; omega
      rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 2) hp,List.reverse_cons] at hin
      obtain ⟨s0,a,hs0,hs,hv⟩ := hin.split_last
      obtain ⟨p,hr,hp0⟩ := ih (n/2) (Nat.div_lt_self hp (by decide)) cp hcp hs0
      obtain ⟨pp,hr',hstep⟩ := C.step s0 p cp d e c hcp hd he hc hid hr s hs
      refine ⟨pp,hr',?_⟩
      intro t ht
      obtain ⟨q,hq,hqt,hw⟩ := hstep t ht
      obtain ⟨b,hb,hbound⟩ := hp0 q hq
      have hout : 0 < 3*n+c := by omega
      obtain ⟨heq,hmod⟩ := affine_div_mod 2 3 n c (by decide)
      refine ⟨b+D.weight q e t,?_,?_⟩
      · rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 2) hout,List.reverse_cons,heq,hmod]
        exact hb.snoc hqt
      · dsimp only [d] at hw
        linarith

lemma construction_bound (h : Total D F) (n d : ℕ) (hd : d < 2) :
    value D F h (3*n+d) ≤ value D F h n+1 := by
  obtain ⟨s,hs,hF⟩ := exists_min_run h n
  obtain ⟨p,hr,hp⟩ := C.simulate n d (by omega) hs
  obtain ⟨t,ht,hFt,hHt⟩ := C.finish s p d hd hr hF
  obtain ⟨u,hu,hbound⟩ := hp t ht
  have hval := value_le_run h hu hFt
  linarith
end Construction

/-- The single-output simulation is the singleton-profile special case. -/
def ofSingle {D : Automaton σ} {F : σ → Prop}
    (C : Erdos406BinaryAcceptingMinplus.Construction D F) : Construction D F σ where
  endpoints p t := t = p
  R := C.R
  H s p c _ := C.H s p c
  seed := by
    intro c hc
    obtain ⟨t,v,hv,hr,hh⟩ := C.seed c hc
    refine ⟨t,hr,?_⟩
    rintro _ rfl
    exact ⟨v,hv,hh⟩
  step := by
    intro s p c d e cp hc hd he hcp har hr sp hsp
    obtain ⟨tp,ht,hr',hw⟩ := C.step s p c d e cp hc hd he hcp har hr sp hsp
    refine ⟨tp,hr',?_⟩
    intro t ht'
    subst t
    exact ⟨p,rfl,ht,hw⟩
  finish := by
    intro s p c hc hr hs
    obtain ⟨hp,hh⟩ := C.finish s p c hc hr hs
    exact ⟨p,rfl,hp,hh⟩

/-- A profile instance at a strictly supercritical rate suffices for the exact
original conjecture. No such numerical instance is supplied here. -/
theorem profile_minplus_criterion (D : Automaton σ) (F : σ → Prop) (h : Total D F)
    (C : Construction D F τ) (P : PowerBound D F)
    (hcrit : Real.log 2 < P.a*Real.log 3) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite :=
  Erdos406BinaryWeighted.construction_potential_criterion (value D F h) P.a P.B
    (C.construction_bound h) (P.power_lower h) hcrit

end Erdos406BinaryProfileMinplus
