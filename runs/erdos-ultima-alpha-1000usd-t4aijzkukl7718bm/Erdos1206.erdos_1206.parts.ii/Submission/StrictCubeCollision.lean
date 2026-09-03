import Submission.CubeAPDescent
import Submission.CubicParametrizationAllCollisions

/-!
The exact Sidon obstruction consists only of four distinct positive roots.
This is an auxiliary characterization, not a density construction.
-/

namespace Erdos1206

/-- Strictly ordered positive four-root collisions. -/
def NoStrictPositiveCubeCollision (S : Set ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    0 < a → a < b → b < c → c < d → a^3+d^3 ≠ b^3+c^3

lemma weak_cube_collision_is_strict_positive {a b c d : ℕ}
    (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (he : a^3+d^3=b^3+c^3) : 0 < a ∧ b < c := by
  have ha : 0 < a := by
    by_contra h
    have ha0 : a=0 := by omega
    rw [ha0,zero_pow (by decide : 3 ≠ 0),zero_add] at he
    exact fermatLastTheoremThree b c d (by omega : b ≠ 0) (by omega : c ≠ 0)
      (by omega : d ≠ 0) he.symm
  have hlt : b < c := by
    by_contra h
    have heq : b=c := by omega
    have hAP : a^3+d^3=2*b^3 := by rw [← heq] at he; omega
    have haeq := (CubeAPDescent.nat_cube_AP_trivial a b d hAP).1
    omega
  exact ⟨ha,hlt⟩

theorem cubeSidon_iff_no_strict_positive (S : Set ℕ) :
    IsSidon ((fun n : ℕ => n^3) '' S) ↔ NoStrictPositiveCubeCollision S := by
  rw [cubeSidon_iff_no_weak_ordered]
  constructor
  · intro h a ha b hb c hc d hd _ hab hbc hcd
    exact h a ha b hb c hc d hd hab hbc.le hcd
  · intro h a ha b hb c hc d hd hab hbc hcd he
    obtain ⟨ha0,hbc'⟩ := weak_cube_collision_is_strict_positive hab hbc hcd he
    exact h a ha b hb c hc d hd ha0 hab hbc' hcd he

theorem not_cubeSidon_iff_strict_positive_collision (S : Set ℕ) :
    ¬ IsSidon ((fun n : ℕ => n^3) '' S) ↔
      ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S,
        0 < a ∧ a < b ∧ b < c ∧ c < d ∧ a^3+d^3=b^3+c^3 := by
  rw [cubeSidon_iff_no_strict_positive]
  simp only [NoStrictPositiveCubeCollision,not_forall,not_not,exists_prop]

/-- Adjoining zero introduces no cubic Sidon obstruction. -/
theorem cubeSidon_insert_zero_iff (S : Set ℕ) :
    IsSidon ((fun n : ℕ => n^3) '' insert 0 S) ↔
      IsSidon ((fun n : ℕ => n^3) '' S) := by
  rw [cubeSidon_iff_no_strict_positive,cubeSidon_iff_no_strict_positive]
  constructor
  · intro h a ha b hb c hc d hd
    exact h a (Set.mem_insert_of_mem 0 ha) b (Set.mem_insert_of_mem 0 hb)
      c (Set.mem_insert_of_mem 0 hc) d (Set.mem_insert_of_mem 0 hd)
  · intro h a ha b hb c hc d hd ha0 hab hbc hcd
    simp only [Set.mem_insert_iff] at ha hb hc hd
    have haS : a ∈ S := ha.resolve_left (by omega)
    have hbS : b ∈ S := hb.resolve_left (by omega)
    have hcS : c ∈ S := hc.resolve_left (by omega)
    have hdS : d ∈ S := hd.resolve_left (by omega)
    exact h a haS b hbS c hcS d hdS ha0 hab hbc hcd

#print axioms weak_cube_collision_is_strict_positive
#print axioms cubeSidon_iff_no_strict_positive
#print axioms cubeSidon_insert_zero_iff

end Erdos1206
