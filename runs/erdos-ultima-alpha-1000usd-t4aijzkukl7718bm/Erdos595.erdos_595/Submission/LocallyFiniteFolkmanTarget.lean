import Submission.FixedFiniteReducedPower
import Submission.FiniteFolkman
import Submission.ExponentialChromaticFilter

/-!
A countable locally finite K4-free target contains every finite K4-free graph
and has no finite triangle-free edge palette. Nevertheless ALL its exponential
candidates have countable triangle-free edge covers. Thus finite age and
unbounded finite palette requirements alone cannot prove an exponential lower
bound. This is not a settlement of Erdős 595.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595LocallyFiniteFolkmanTarget
open Erdos595Work Erdos595FinitePalette
open Erdos595FixedFiniteReducedPower

abbrev Carrier := (n : ℕ) × Vertex n

def H : SimpleGraph Carrier where
  Adj
    | ⟨n,a⟩, ⟨m,b⟩ => ∃ h : n = m, (universal n).Adj a (h.symm ▸ b)
  symm := by
    rintro ⟨n,a⟩ ⟨m,b⟩ ⟨rfl,h⟩
    exact ⟨rfl,h.symm⟩
  loopless := by
    rintro ⟨n,a⟩ ⟨h,ha⟩
    exact (universal n).loopless a ha

lemma same (n : ℕ) (a b : Vertex n) :
    H.Adj ⟨n,a⟩ ⟨n,b⟩ ↔ (universal n).Adj a b := by
  change (∃ h : n = n, (universal n).Adj a (h.symm ▸ b)) ↔ _
  simp

def inclusion (n : ℕ) : universal n ↪g H where
  toFun := Sigma.mk n
  inj' := by
    intro a b h
    simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using h
  map_rel_iff' := same n _ _

instance : Countable Carrier := inferInstanceAs (Countable ((n : ℕ) × Vertex n))

noncomputable instance : H.LocallyFinite := by
  classical
  intro x
  have hs : (Set.range (Sigma.mk x.1 : Vertex x.1 → Carrier)).Finite := Set.finite_range _
  have hf : (H.neighborSet x).Finite := hs.subset (by
    rintro ⟨m,b⟩ ⟨he,hab⟩
    cases x with
    | mk n a =>
      dsimp at he
      subst m
      exact ⟨b,rfl⟩)
  exact hf.fintype

lemma cliqueFree : H.CliqueFree 4 := by
  have hn : ∀ a b c d : Carrier, H.Adj a b → H.Adj a c → H.Adj b c →
      H.Adj a d → H.Adj b d → H.Adj c d → False := by
    rintro ⟨n,a⟩ ⟨m,b⟩ ⟨l,c⟩ ⟨k,d⟩ ⟨rfl,hab⟩ ⟨rfl,hac⟩ hbc ⟨rfl,had⟩ hbd hcd
    exact no_adj_common_neighbors (universal_cliqueFree n)
      hab hac ((same n _ _).mp hbc) had ((same n _ _).mp hbd) ((same n _ _).mp hcd)
  classical
  by_contra hh
  let f := SimpleGraph.topEmbeddingOfNotCliqueFree hh
  exact hn (f 0) (f 1) (f 2) (f 3) (f.map_rel_iff.mpr (by decide))
    (f.map_rel_iff.mpr (by decide)) (f.map_rel_iff.mpr (by decide))
    (f.map_rel_iff.mpr (by decide)) (f.map_rel_iff.mpr (by decide)) (f.map_rel_iff.mpr (by decide))

/-- The target has the entire finite K4-free age. -/
theorem finite_universal {A : Type*} [Finite A] (G : SimpleGraph A) (hG : G.CliqueFree 4) :
    Nonempty (G ↪g H) := by
  classical
  letI := Fintype.ofFinite A
  exact ⟨(inclusion (Fintype.card A)).comp (finiteEmbedding G hG _ rfl)⟩

theorem no_finite_palette (C : Type) [Finite C] : ¬HasColoring H C := by
  obtain ⟨A,hA,G,hG,hbad⟩ := Erdos595FiniteFolkman.finite_folkman C
  letI := hA
  obtain ⟨f⟩ := finite_universal G hG
  exact fun hc => hbad (hc.comap f.toHom)

/-- No choice of uncountably chromatic domain makes this target a witness. -/
theorem all_exponentials_covered {V : Type*} (B : SimpleGraph V)
    (hB : IsEmpty (B.Coloring ℕ)) :
    IsCountableUnionOfTriangleFree (Erdos595Exponential.exponential H B hB) :=
  Erdos595ExponentialChromaticFilter.locally_finite_target H B hB

#print axioms cliqueFree
#print axioms finite_universal
#print axioms no_finite_palette
#print axioms all_exponentials_covered
end Erdos595LocallyFiniteFolkmanTarget
