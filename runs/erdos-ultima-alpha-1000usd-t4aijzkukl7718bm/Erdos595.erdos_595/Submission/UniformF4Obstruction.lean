import Submission.Work

/-!
A constant-ratio obstruction over a field of characteristic two.
This does not obstruct arbitrary varying-ratio representations of this graph,
and is not a settlement of Erdős 595.
-/
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 0
open SimpleGraph
namespace Erdos595UniformF4Obstruction

def adjacent (a b : Fin 9) : Prop :=
  (a,b) ∈ ([(0,1),(1,0),(0,3),(3,0),(0,6),(6,0),(0,8),(8,0),(1,2),(2,1),(1,3),(3,1),(1,4),(4,1),(1,6),(6,1),(1,7),(7,1),(2,3),(3,2),(2,5),(5,2),(2,6),(6,2),(3,4),(4,3),(3,5),(5,3),(3,7),(7,3),(3,8),(8,3),(4,6),(6,4),(4,8),(8,4),(5,6),(6,5),(5,8),(8,5),(6,7),(7,6),(6,8),(8,6),(7,8),(8,7)] : List (Fin 9 × Fin 9))

instance : DecidableRel adjacent := fun _ _ =>
  inferInstanceAs (Decidable (_ ∈ (_ : List (Fin 9 × Fin 9))))

def G : SimpleGraph (Fin 9) where
  Adj := adjacent
  symm := by change ∀ a b, adjacent a b → adjacent b a; decide
  loopless := by change ∀ a, ¬adjacent a a; decide

instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (adjacent _ _))

lemma cliqueFree : G.CliqueFree 4 := by
  have hn : ∀ a b c d : Fin 9,
      ¬(adjacent a b ∧ adjacent a c ∧ adjacent a d ∧
        adjacent b c ∧ adjacent b d ∧ adjacent c d) := by decide +kernel
  classical
  by_contra h
  let f := SimpleGraph.topEmbeddingOfNotCliqueFree h
  apply hn (f 0) (f 1) (f 2) (f 3)
  exact ⟨f.map_rel_iff.mpr (by decide), f.map_rel_iff.mpr (by decide),
    f.map_rel_iff.mpr (by decide), f.map_rel_iff.mpr (by decide),
    f.map_rel_iff.mpr (by decide), f.map_rel_iff.mpr (by decide)⟩

variable {K E : Type*} [Field K] [CharP K 2] [AddCommGroup E] [Module K E]

def relation (w : K) (f : Fin 9 → Fin 9 → E) (a b c : Fin 9) : E :=
  (w+1) • f a b + w • f a c + f b c

theorem collapse (w : K) (hw : w^2+w+1=0) (f : Fin 9 → Fin 9 → E)
    (h : ∀ a b c, a < b → b < c → G.Adj a b → G.Adj a c → G.Adj b c →
      relation w f a b c = 0) : f 1 2 = f 1 3 := by
  have hs : f 1 2 - f 1 3 = 0 := by
    calc
      _ = w • relation w f 0 1 3 +
          w • relation w f 0 1 6 +
          1 • relation w f 0 3 8 +
          1 • relation w f 0 6 8 +
          (w+1) • relation w f 1 2 3 +
          1 • relation w f 1 2 6 +
          1 • relation w f 1 3 4 +
          w • relation w f 1 3 7 +
          (w+1) • relation w f 1 4 6 +
          w • relation w f 1 6 7 +
          1 • relation w f 2 3 5 +
          (w+1) • relation w f 2 5 6 +
          w • relation w f 3 4 8 +
          w • relation w f 3 5 8 +
          (w+1) • relation w f 3 7 8 +
          1 • relation w f 4 6 8 +
          1 • relation w f 5 6 8 +
          (w+1) • relation w f 6 7 8 := by
        unfold relation
        match_scalars <;> ring_nf <;> reduce_mod_char!
        all_goals (linear_combination (norm := ring_nf) hw; reduce_mod_char!)
      _ = 0 := by
        rw [h 0 1 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 0 1 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 0 3 8 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 0 6 8 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 1 2 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 1 3 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 1 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 1 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 2 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 2 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 3 4 8 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 3 5 8 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 3 7 8 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 4 6 8 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 5 6 8 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [h 6 7 8 (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp
  exact sub_eq_zero.mp hs

/-- The same certificate stated directly for the affine triangle equation. -/
theorem collapse_affine (w : K) (hw : w^2+w+1=0) (f : Fin 9 → Fin 9 → E)
    (h : ∀ a b c, a < b → b < c → G.Adj a b → G.Adj a c → G.Adj b c →
      f a c = w • f a b + (1-w) • f b c) : f 1 2 = f 1 3 := by
  apply collapse w hw f
  intro a b c hab hbc h₁ h₂ h₃
  unfold relation
  rw [h a b c hab hbc h₁ h₂ h₃]
  match_scalars <;> ring_nf <;> reduce_mod_char!
  all_goals linear_combination (norm := ring_nf) hw

theorem no_uniform_affine (w : K) (hw : w^2+w+1=0)
    (f : Fin 9 → Fin 9 → E)
    (h : ∀ a b c, a < b → b < c → G.Adj a b → G.Adj a c → G.Adj b c →
      f a c = w • f a b + (1-w) • f b c)
    (hne : f 1 2 ≠ f 1 3) : False :=
  hne (collapse_affine w hw f h)

#print axioms cliqueFree
#print axioms no_uniform_affine

#print axioms collapse
end Erdos595UniformF4Obstruction
