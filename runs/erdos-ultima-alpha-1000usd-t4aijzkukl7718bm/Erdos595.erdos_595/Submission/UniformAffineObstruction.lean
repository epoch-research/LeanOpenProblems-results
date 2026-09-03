import Submission.Work

/-!
A finite ordered K4-free graph obstructs every uniform proper affine ratio,
over every field and in every vector-space dimension. This is auxiliary work,
not a proof or disproof of Erdős 595.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
open SimpleGraph
namespace Erdos595UniformAffineObstruction

def adjacent (a b : Fin 12) : Prop :=
  (a,b) ∈ ([(0,2),(2,0),(0,4),(4,0),(0,6),(6,0),(0,8),(8,0),(0,9),(9,0),(0,10),(10,0),(1,4),(4,1),(1,5),(5,1),(1,6),(6,1),(1,8),(8,1),(1,10),(10,1),(1,11),(11,1),(2,3),(3,2),(2,4),(4,2),(2,5),(5,2),(2,9),(9,2),(2,10),(10,2),(2,11),(11,2),(3,6),(6,3),(3,7),(7,3),(3,10),(10,3),(3,11),(11,3),(4,5),(5,4),(4,7),(7,4),(4,11),(11,4),(5,7),(7,5),(5,9),(9,5),(5,10),(10,5),(6,9),(9,6),(6,10),(10,6),(6,11),(11,6),(7,8),(8,7),(7,10),(10,7),(7,11),(11,7),(8,9),(9,8),(8,10),(10,8),(8,11),(11,8),(9,11),(11,9)] : List (Fin 12 × Fin 12))

instance : DecidableRel adjacent := fun _ _ =>
  inferInstanceAs (Decidable (_ ∈ (_ : List (Fin 12 × Fin 12))))

def G : SimpleGraph (Fin 12) where
  Adj := adjacent
  symm := by change ∀ a b, adjacent a b → adjacent b a; decide +kernel
  loopless := by change ∀ a, ¬adjacent a a; decide +kernel

instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (adjacent _ _))

lemma cliqueFree : G.CliqueFree 4 := by
  have hn : ∀ a b c d : Fin 12,
      ¬(adjacent a b ∧ adjacent a c ∧ adjacent a d ∧
        adjacent b c ∧ adjacent b d ∧ adjacent c d) := by decide +kernel
  classical
  by_contra h
  let f := SimpleGraph.topEmbeddingOfNotCliqueFree h
  apply hn (f 0) (f 1) (f 2) (f 3)
  exact ⟨f.map_rel_iff.mpr (by decide), f.map_rel_iff.mpr (by decide),
    f.map_rel_iff.mpr (by decide), f.map_rel_iff.mpr (by decide),
    f.map_rel_iff.mpr (by decide), f.map_rel_iff.mpr (by decide)⟩

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

def relation (t : K) (f : Fin 12 → Fin 12 → E) (a b c : Fin 12) : E :=
  t • f a b - f a c + (1-t) • f b c

/-- An integer-polynomial linear combination of 24 triangle relations. -/
theorem certificate (t : K) (f : Fin 12 → Fin 12 → E) :
    (t*(1-t)) • (f 1 6 - f 1 10) = (t) • relation t f 0 2 9 +
      (-t) • relation t f 0 2 10 +
      (-t) • relation t f 0 6 9 +
      (t) • relation t f 0 6 10 +
      (-t + t^2) • relation t f 1 4 5 +
      (t - t^2) • relation t f 1 4 11 +
      (-1 + t) • relation t f 1 5 10 +
      (3 - 2*t - 2*t^2 + t^3) • relation t f 1 6 10 +
      (-2 + t + 2*t^2 - t^3) • relation t f 1 6 11 +
      (-2 + 2*t + t^2 - t^3) • relation t f 1 8 10 +
      (2 - 2*t - t^2 + t^3) • relation t f 1 8 11 +
      (-1 + t^2) • relation t f 2 3 10 +
      (1 - t^2) • relation t f 2 3 11 +
      (t - t^2) • relation t f 2 4 5 +
      (-t + t^2) • relation t f 2 4 11 +
      (1 - t) • relation t f 2 5 10 +
      (-1 + t) • relation t f 2 9 11 +
      (-3 + t + 2*t^2 - t^3) • relation t f 3 6 10 +
      (3 - t - 2*t^2 + t^3) • relation t f 3 6 11 +
      (2 - t^2) • relation t f 3 7 10 +
      (-2 + t^2) • relation t f 3 7 11 +
      (1 - t) • relation t f 6 9 11 +
      (2 - 2*t - t^2 + t^3) • relation t f 7 8 10 +
      (-2 + 2*t + t^2 - t^3) • relation t f 7 8 11 := by
  unfold relation
  match_scalars <;> ring

/-- No assumption on the characteristic is needed. -/
theorem collapse (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (f : Fin 12 → Fin 12 → E)
    (h : ∀ a b c, a < b → b < c → G.Adj a b → G.Adj a c → G.Adj b c →
      f a c = t • f a b + (1-t) • f b c) : f 1 6 = f 1 10 := by
  have hr : ∀ a b c, a < b → b < c → G.Adj a b → G.Adj a c → G.Adj b c →
      relation t f a b c = 0 := by
    intro a b c hab hbc h₁ h₂ h₃
    unfold relation
    rw [h a b c hab hbc h₁ h₂ h₃]
    abel
  have he := certificate t f
  rw [hr 0 2 9 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  rw [hr 0 2 10 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  rw [hr 0 6 9 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  rw [hr 0 6 10 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  rw [hr 1 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  rw [hr 1 4 11 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  rw [hr 1 5 10 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  rw [hr 1 6 10 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  rw [hr 1 6 11 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  rw [hr 1 8 10 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  rw [hr 1 8 11 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  rw [hr 2 3 10 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  rw [hr 2 3 11 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  rw [hr 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  rw [hr 2 4 11 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  rw [hr 2 5 10 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  rw [hr 2 9 11 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  rw [hr 3 6 10 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  rw [hr 3 6 11 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  rw [hr 3 7 10 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  rw [hr 3 7 11 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  rw [hr 6 9 11 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  rw [hr 7 8 10 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  rw [hr 7 8 11 (by decide) (by decide) (by decide) (by decide) (by decide)] at he
  simp only [smul_zero,add_zero] at he
  have hn : t*(1-t) ≠ 0 := mul_ne_zero ht0 (sub_ne_zero.mpr ht1.symm)
  exact sub_eq_zero.mp ((smul_eq_zero.mp he).resolve_left hn)

theorem no_uniform (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (f : Fin 12 → Fin 12 → E)
    (h : ∀ a b c, a < b → b < c → G.Adj a b → G.Adj a c → G.Adj b c →
      f a c = t • f a b + (1-t) • f b c)
    (hne : f 1 6 ≠ f 6 10) : False := by
  have hc := collapse t ht0 ht1 f h
  have htri := h 1 6 10 (by decide) (by decide) (by decide) (by decide) (by decide)
  have he : (1-t) • f 1 6 = (1-t) • f 6 10 := by
    rw [← hc] at htri
    calc
      _ = f 1 6 - t • f 1 6 := by module
      _ = (t • f 1 6 + (1-t) • f 6 10) - t • f 1 6 := by rw [← htri]
      _ = _ := by abel
  exact hne (smul_right_injective E (sub_ne_zero.mpr ht1.symm) he)

#print axioms cliqueFree
#print axioms certificate
#print axioms no_uniform
end Erdos595UniformAffineObstruction
