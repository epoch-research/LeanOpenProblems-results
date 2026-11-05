import Submission.SmallRamsey

/-!
# Exact certificates for density-route obstructions

Kernel evaluation only: no `native_decide`, and no conjectural assumptions.
The fork certificate concerns completion, not a counterexample to `c₅`.
The rational block model refutes the unrestricted density recurrence at n=3.
-/
namespace Combinatorics.DensityRoute.Certificates

open Finset

namespace Fork

def color (e : Finset (Fin 5)) : Bool := decide (¬ ({3, 4} : Finset (Fin 5)) ⊆ e)
def seedA : Finset (Fin 5) := {0, 1, 2, 3}
def seedB : Finset (Fin 5) := {0, 1, 2, 4}
def Mono (S : Finset (Fin 5)) (b : Bool) : Prop :=
  ∀ e ∈ S.powersetCard 3, color e = b

instance (S : Finset (Fin 5)) (b : Bool) : Decidable (Mono S b) := by
  unfold Mono
  infer_instance

set_option maxRecDepth 4096 in
/-- Both seed cliques have the same colour; the full union has neither colour. -/
theorem anti_aligned_fork :
    seedA.card = 4 ∧ seedB.card = 4 ∧ Mono seedA true ∧ Mono seedB true ∧
      ¬ ∃ b : Bool, Mono (seedA ∪ seedB) b := by
  decide

/-- Every omitted triple is anti-aligned with the seed colour. -/
theorem missing_triples :
    color {0, 3, 4} = false ∧ color {1, 3, 4} = false ∧ color {2, 3, 4} = false := by
  decide

set_option maxRecDepth 4096 in
/-- The finite fork has two monochromatic quadruples, but no monochromatic five-set. -/
theorem seed_count :
    (((univ : Finset (Fin 5)).powersetCard 4).filter (fun S => ∃ b : Bool, Mono S b)).card = 2 := by
  decide

end Fork

namespace ThreeBlock

/-- Red probability for the three-block random construction. Internal and
transversal triples are red. For a repeated class i and singleton i+1 mod 3,
the red probability is 2/3; the reverse repeated type is blue. -/
def redProbability (a b c : Fin 3) : ℚ :=
  if a = b ∧ b = c then 1
  else if a ≠ b ∧ a ≠ c ∧ b ≠ c then 1
  else if (a = b ∧ c = a + 1) ∨ (a = c ∧ b = a + 1) ∨ (b = c ∧ a = b + 1)
    then 2 / 3 else 0

@[simp] lemma redProbability_000 : redProbability 0 0 0 = 1 := by rfl
@[simp] lemma redProbability_001 : redProbability 0 0 1 = 2 / 3 := by rfl
@[simp] lemma redProbability_002 : redProbability 0 0 2 = 0 := by rfl
@[simp] lemma redProbability_010 : redProbability 0 1 0 = 2 / 3 := by rfl
@[simp] lemma redProbability_011 : redProbability 0 1 1 = 0 := by rfl
@[simp] lemma redProbability_012 : redProbability 0 1 2 = 1 := by rfl
@[simp] lemma redProbability_020 : redProbability 0 2 0 = 0 := by rfl
@[simp] lemma redProbability_021 : redProbability 0 2 1 = 1 := by rfl
@[simp] lemma redProbability_022 : redProbability 0 2 2 = 2 / 3 := by rfl
@[simp] lemma redProbability_100 : redProbability 1 0 0 = 2 / 3 := by rfl
@[simp] lemma redProbability_101 : redProbability 1 0 1 = 0 := by rfl
@[simp] lemma redProbability_102 : redProbability 1 0 2 = 1 := by rfl
@[simp] lemma redProbability_110 : redProbability 1 1 0 = 0 := by rfl
@[simp] lemma redProbability_111 : redProbability 1 1 1 = 1 := by rfl
@[simp] lemma redProbability_112 : redProbability 1 1 2 = 2 / 3 := by rfl
@[simp] lemma redProbability_120 : redProbability 1 2 0 = 1 := by rfl
@[simp] lemma redProbability_121 : redProbability 1 2 1 = 2 / 3 := by rfl
@[simp] lemma redProbability_122 : redProbability 1 2 2 = 0 := by rfl
@[simp] lemma redProbability_200 : redProbability 2 0 0 = 0 := by rfl
@[simp] lemma redProbability_201 : redProbability 2 0 1 = 1 := by rfl
@[simp] lemma redProbability_202 : redProbability 2 0 2 = 2 / 3 := by rfl
@[simp] lemma redProbability_210 : redProbability 2 1 0 = 1 := by rfl
@[simp] lemma redProbability_211 : redProbability 2 1 1 = 2 / 3 := by rfl
@[simp] lemma redProbability_212 : redProbability 2 1 2 = 0 := by rfl
@[simp] lemma redProbability_220 : redProbability 2 2 0 = 2 / 3 := by rfl
@[simp] lemma redProbability_221 : redProbability 2 2 1 = 0 := by rfl
@[simp] lemma redProbability_222 : redProbability 2 2 2 = 1 := by rfl

/-- Expected monochromatic indicator for a four-tuple of block labels. -/
def quadProbability (a b c d : Fin 3) : ℚ :=
  redProbability a b c * redProbability a b d * redProbability a c d * redProbability b c d +
    (1 - redProbability a b c) * (1 - redProbability a b d) *
      (1 - redProbability a c d) * (1 - redProbability b c d)

def average : ℚ := (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
  quadProbability a b c d) / 81

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- An exact rational certificate, not a floating-point optimization. -/
theorem average_exact : average = 77 / 729 := by
  norm_num [average, Fin.sum_univ_three, quadProbability]

/-- Since `c₃ = 1`, this construction violates the n=3 instance. It says
nothing about the recurrence starting at n=4. -/
theorem average_below_random : average < 1 / 8 := by
  rw [average_exact]
  norm_num

end ThreeBlock

namespace Partite

/-- Numerator of the mono n-set density in the n-partite colouring:
red iff all three block labels are distinct. -/
def numeratorAtSeed (n : ℕ) : ℕ :=
  n.factorial + n + n.choose 2 * (2 ^ n - 2)

/-- For m>n there are no red m-sets, and a blue m-set uses at most two labels. -/
def blueNumerator (n m : ℕ) : ℕ := n + n.choose 2 * (2 ^ m - 2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 1024 in
/-- Clearing the positive denominators: the n=100 partite model satisfies
`p₁₀₂ < p₁₀₀^4`. This refutes a pointwise four-power inequality, not the
inequality between the minimum density constants. -/
theorem four_power_counterexample :
    blueNumerator 100 102 * 100 ^ 298 < numeratorAtSeed 100 ^ 4 := by
  decide

end Partite

end Combinatorics.DensityRoute.Certificates
