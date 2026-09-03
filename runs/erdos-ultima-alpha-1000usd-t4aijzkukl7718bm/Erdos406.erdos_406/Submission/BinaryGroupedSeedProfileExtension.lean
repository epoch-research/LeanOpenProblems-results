import Submission.BinaryGroupedPositivePrefixControl

/-! A seed profile may retain an extra output run, while subsequent transitions
use the old endpoint. This is a soundness control, not a strict certificate. -/
namespace Erdos406GroupedSeedProfileExtension
open Erdos406Tropical (Automaton Run)
open Erdos406BinaryGroupedProfile
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

variable {σ τ : Type*} [Fintype σ] [DecidableEq σ]

noncomputable def withExtraSeed {h : ℕ} {D : Automaton σ} {F : σ → Prop}
    (C : Construction h D F τ) (c₀ : ℕ) (p₀ : τ)
    (hr₀ : C.R D.start p₀ c₀)
    (hs₀ : ∀ t, C.endpoints p₀ t → ∃ v,
      Run D D.start (Nat.digits 2 c₀).reverse t v ∧ v ≤ C.H D.start p₀ c₀ t)
    (u : σ) (v : ℝ) (hu : Run D D.start (Nat.digits 2 c₀).reverse u v)
    (hnu : ¬ C.endpoints p₀ u) : Construction h D F (Option τ) where
  endpoints p t := match p with
    | some q => C.endpoints q t
    | none => C.endpoints p₀ t ∨ t = u
  R s p c := match p with
    | some q => C.R s q c
    | none => s = D.start ∧ c = c₀
  H s p c t := match p with
    | some q => C.H s q c t
    | none => if t = u then v else C.H D.start p₀ c₀ t
  seed := by
    intro c hc
    by_cases he : c = c₀
    · subst c
      refine ⟨none, ⟨rfl,rfl⟩, ?_⟩
      intro t ht
      rcases ht with ht | rfl
      · obtain ⟨w,hw,hb⟩ := hs₀ t ht
        have hne : t ≠ u := by rintro rfl; exact hnu ht
        exact ⟨w,hw,by simpa only [if_neg hne] using hb⟩
      · exact ⟨v,hu,by simp⟩
    · obtain ⟨p,hp,hs⟩ := C.seed c hc
      exact ⟨some p,hp,hs⟩
  step := by
    intro s p c d e cp hc hd he hcp har hr sp hsp
    cases p with
    | some p =>
      obtain ⟨pp,hpp,hs⟩ := C.step s p c d e cp hc hd he hcp har hr sp hsp
      exact ⟨some pp,hpp,hs⟩
    | none =>
      rcases hr with ⟨hs,hc'⟩
      subst s
      subst c
      obtain ⟨pp,hpp,hs⟩ := C.step D.start p₀ c₀ d e cp hc hd he hcp har hr₀ sp hsp
      refine ⟨some pp,hpp,?_⟩
      intro tp htp
      obtain ⟨t,ht,hnext,hb⟩ := hs tp htp
      have hne : t ≠ u := by rintro rfl; exact hnu ht
      exact ⟨t,Or.inl ht,hnext,by simpa only [if_neg hne] using hb⟩
  finish := by
    intro s p c hc hr hf
    cases p with
    | some p =>
      obtain ⟨t,ht,hf',hb⟩ := C.finish s p c hc hr hf
      exact ⟨t,ht,hf',hb⟩
    | none =>
      rcases hr with ⟨hs,hc'⟩
      subst s
      subst c
      obtain ⟨t,ht,hf',hb⟩ := C.finish D.start p₀ c₀ hc hr₀ hf
      have hne : t ≠ u := by rintro rfl; exact hnu ht
      exact ⟨t,Or.inl ht,hf',by simpa only [if_neg hne] using hb⟩

namespace Control
open Erdos406BinaryGroupedPositivePrefixControl

lemma extra_run : Run D D.start (Nat.digits 2 3).reverse (4 : Fin 72)
    (((W 0 1 1 + W 1 1 4 : ℤ) : ℝ) / 3000000) := by
  have hword : (Nat.digits 2 3).reverse = [1,1] := by decide +kernel
  rw [hword]
  have hr := Run.cons (by decide +kernel : (1 : Fin 72) ∈ D.next 0 1)
    (Run.cons (by decide +kernel : (4 : Fin 72) ∈ D.next 1 1) (Run.nil (D:=D) 4))
  convert hr using 1 <;> simp [D] <;> ring

noncomputable def constructionWithPair : Construction 2 D F (Option (Fin 812)) :=
  withExtraSeed construction 3 3 seed_relation_3 seed_runs_3 4
    (((W 0 1 1 + W 1 1 4 : ℤ) : ℝ) / 3000000) extra_run (by change ¬ (4 : Fin 72) ∈ ends 3; decide +kernel)

lemma two_seed_endpoints : constructionWithPair.endpoints none 3 ∧
    constructionWithPair.endpoints none 4 := by
  change (3 ∈ ends 3 ∨ (3 : Fin 72) = 4) ∧ (4 ∈ ends 3 ∨ (4 : Fin 72) = 4)
  exact ⟨Or.inl (by decide +kernel),Or.inr rfl⟩

lemma good_run_bound (n : ℕ) (hg : Nat.digits 3 n ⊆ [0,1]) :
    ∃ t v, Run D D.start (Nat.digits 2 n).reverse t v ∧ F t ∧
      v ≤ (2 : ℝ)*(Nat.digits 9 n).length :=
  constructionWithPair.exists_good_run (by decide +kernel) start_accepts n hg

end Control
end Erdos406GroupedSeedProfileExtension

#print axioms Erdos406GroupedSeedProfileExtension.withExtraSeed
#print axioms Erdos406GroupedSeedProfileExtension.Control.constructionWithPair
#print axioms Erdos406GroupedSeedProfileExtension.Control.good_run_bound
