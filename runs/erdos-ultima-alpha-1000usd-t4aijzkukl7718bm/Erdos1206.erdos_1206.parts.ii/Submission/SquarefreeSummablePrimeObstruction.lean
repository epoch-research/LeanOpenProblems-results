import Submission.SquarefreePrimeParameterSieve
import Submission.SummablePrimeConicObstruction

/-! The explicit conic has squarefree strict collisions avoiding every prime
in any reciprocally summable forbidden set. This is a restricted obstruction,
not a disproof for arbitrary positive-density root sets. -/
namespace Erdos1206.SquarefreeSummablePrimeObstruction
open SquarefreeConicFamily QuadraticSquarefreeSieve QuadraticRootLattice
open scoped Classical
set_option maxHeartbeats 2000000

lemma anisotropic_reversed (i : Fin 4) : Anisotropic (c i) (b i) (a i) := by
  apply anisotropic_of_nonsquare_discriminant
  fin_cases i <;> norm_num [a,b,c]

lemma local_units_nat (p : ℕ) (hp : p.Prime) :
    ∃ x : ℕ × ℕ, ∀ i, ¬p∣quad (a i) (b i) (c i) x.1 x.2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨z,hz⟩ := SummablePrimeConicObstruction.local_units p hp
  refine ⟨(z.2.val,z.1.val),fun i hd => hz i ?_⟩
  have he := (CharP.cast_eq_zero_iff (ZMod p) p _).mpr hd
  simp only [quad,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,ZMod.natCast_zmod_val] at he
  dsimp only [QuadraticUnitResidues.evalMod]
  push_cast
  linear_combination he

lemma ordered_of_first_pos (t u : ℕ) (ht : 0 < t) :
    0 < F 0 t u ∧ F 0 t u < F 1 t u ∧ F 1 t u < F 2 t u ∧ F 2 t u < F 3 t u := by
  have ht2 : 0 < t^2 := pow_pos ht 2
  dsimp [F,quad,a,b,c]
  constructor
  · positivity
  constructor <;> (try constructor) <;> nlinarith

/-- Prime avoidance can be combined with simultaneous squarefreeness in a
fixed strict cube-collision family. -/
theorem collision_avoiding (B : Set ℕ) (hB : ∀ p∈B, p.Prime)
    (hs : Summable (fun p : ℕ => if p∈B then (1:ℝ)/p else 0)) :
    ∃ n : Fin 4 → ℕ, (∀ i, 0 < n i ∧ Squarefree (n i)) ∧
      n 0 < n 1 ∧ n 1 < n 2 ∧ n 2 < n 3 ∧
      (n 0)^3+(n 3)^3=(n 1)^3+(n 2)^3 ∧ ∀ i p, p∈B → ¬p∣n i := by
  obtain ⟨x,hxpos,hx⟩ := SquarefreePrimeParameterSieve.exists_avoiding a b c B
    (by intro i; fin_cases i <;> norm_num [a])
    (by intro i; fin_cases i <;> norm_num [c])
    anisotropic_reversed (by intro i; fin_cases i <;> norm_num [a,b,c]) hB hs local_units_nat
  obtain ⟨h0,h01,h12,h23⟩ := ordered_of_first_pos x.1 x.2 hxpos
  refine ⟨fun i => F i x.1 x.2,?_,h01,h12,h23,identity x.1 x.2,fun i => (hx i).2⟩
  intro i
  refine ⟨?_,(hx i).1⟩
  fin_cases i <;> dsimp <;> omega

/-- The squarefree integers avoiding a summable set of prime multiples do
not have Sidon cubes. Composite-divisor exclusions are not covered. -/
theorem not_sidon (B : Set ℕ) (hB : ∀ p∈B, p.Prime)
    (hs : Summable (fun p : ℕ => if p∈B then (1:ℝ)/p else 0)) :
    ¬IsSidon ((fun n : ℕ => n^3) '' {n : ℕ | Squarefree n ∧ ∀ p∈B, ¬p∣n}) := by
  intro hsidon
  obtain ⟨n,hn,h01,h12,h23,he,havoid⟩ := collision_avoiding B hB hs
  have hm (i : Fin 4) : n i∈{n : ℕ | Squarefree n ∧ ∀ p∈B, ¬p∣n} := ⟨(hn i).2,havoid i⟩
  have hh := hsidon _ ⟨n 0,hm 0,rfl⟩ _ ⟨n 1,hm 1,rfl⟩
    _ ⟨n 3,hm 3,rfl⟩ _ ⟨n 2,hm 2,rfl⟩ he
  rcases hh with hh | hh
  · have heq := Nat.pow_left_injective (by decide : 3≠0) hh.1
    omega
  · have heq := Nat.pow_left_injective (by decide : 3≠0) hh.1
    omega

#print axioms collision_avoiding
#print axioms not_sidon
end Erdos1206.SquarefreeSummablePrimeObstruction
