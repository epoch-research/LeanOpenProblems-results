import FormalConjecturesUtil

/-!
An exact unbounded common-factor family in the quartic cube parametrization.
This rules out bounded denominator cancellation, not the density conjecture.
-/

namespace Erdos1206
namespace CubeParamCancellation

/-- Parameters R=3k+3, S=1, V=R²-R+1. -/
def norm (k : ℕ) : ℕ := 9 * k ^ 2 + 15 * k + 7

def rootA (k : ℕ) : ℕ := (3 * k + 2) ^ 3

def rootB (k : ℕ) : ℕ := (3 * k + 3) ^ 3 + 2

def rootC (k : ℕ) : ℕ :=
  81 * k ^ 4 + 270 * k ^ 3 + 351 * k ^ 2 + 213 * k + 50

def rootD (k : ℕ) : ℕ := rootC k + 3

lemma norm_eq (k : ℕ) :
    norm k + (3 * k + 3) = (3 * k + 3) ^ 2 + 1 := by
  dsimp [norm]
  ring

lemma reduced_identity (k : ℕ) :
    rootA k ^ 3 + rootD k ^ 3 = rootB k ^ 3 + rootC k ^ 3 := by
  dsimp [rootA, rootB, rootC, rootD]
  ring

lemma roots_ordered (k : ℕ) :
    0 < rootA k ∧ rootA k < rootB k ∧
      rootB k < rootC k ∧ rootC k < rootD k := by
  have hAB : rootB k = rootA k + 3 * norm k := by
    dsimp [rootA, rootB, norm]
    ring
  have hBC : rootC k = rootB k +
      (81 * k ^ 4 + 243 * k ^ 3 + 270 * k ^ 2 + 132 * k + 21) := by
    dsimp [rootB, rootC]
    ring
  have hn : 0 < norm k := by dsimp [norm]; omega
  have hA : 0 < rootA k := by dsimp [rootA]; positivity
  dsimp only [rootD]
  omega

lemma roots_gcd_one (k : ℕ) :
    Nat.gcd (Nat.gcd (rootA k) (rootB k))
      (Nat.gcd (rootC k) (rootD k)) = 1 := by
  let g := Nat.gcd (Nat.gcd (rootA k) (rootB k))
      (Nat.gcd (rootC k) (rootD k))
  have hga : g ∣ rootA k :=
    (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have hgc : g ∣ rootC k :=
    (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  have hgd : g ∣ rootD k :=
    (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have hg3 : g ∣ 3 := (Nat.dvd_add_iff_right hgc).mpr hgd
  have hg : g = 1 ∨ g = 3 := (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hg3
  rcases hg with hg | hg
  · exact hg
  · rw [hg] at hga
    have hmod : rootA k % 3 = 2 := by
      simp [rootA, Nat.add_mod, Nat.pow_mod]
    have hh := Nat.mod_eq_zero_of_dvd hga
    omega

/-- The four homogeneous quartic coordinates evaluated at these parameters. -/
def rawA (k : ℕ) : ℕ := (norm k) ^ 2 + (norm k) ^ 3 * (3 * k + 1)
def rawB (k : ℕ) : ℕ := (norm k) ^ 2 + (norm k) ^ 3 * (3 * k + 4)
def rawC (k : ℕ) : ℕ := norm k * (norm k * (3 * k + 1) + (norm k) ^ 3)
def rawD (k : ℕ) : ℕ := norm k * (norm k * (3 * k + 4) + (norm k) ^ 3)

lemma raw_factorizations (k : ℕ) :
    rawA k = (norm k) ^ 2 * rootA k ∧
    rawB k = (norm k) ^ 2 * rootB k ∧
    rawC k = (norm k) ^ 2 * rootC k ∧
    rawD k = (norm k) ^ 2 * rootD k := by
  dsimp [rawA, rawB, rawC, rawD, norm, rootA, rootB, rootC, rootD]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

lemma raw_gcd_exact (k : ℕ) :
    Nat.gcd (Nat.gcd (rawA k) (rawB k))
      (Nat.gcd (rawC k) (rawD k)) = (norm k) ^ 2 := by
  obtain ⟨ha, hb, hc, hd⟩ := raw_factorizations k
  rw [ha, hb, hc, hd, Nat.gcd_mul_left, Nat.gcd_mul_left,
    Nat.gcd_mul_left, roots_gcd_one, mul_one]

lemma parameters_pairwise_coprime (k : ℕ) :
    Nat.Coprime (3 * k + 3) 1 ∧ Nat.Coprime 1 (norm k) ∧
      Nat.Coprime (3 * k + 3) (norm k) := by
  refine ⟨by simp, by simp, ?_⟩
  apply Nat.coprime_iff_gcd_eq_one.mpr
  let g := Nat.gcd (3 * k + 3) (norm k)
  have hgR : g ∣ 3 * k + 3 := Nat.gcd_dvd_left _ _
  have hgN : g ∣ norm k := Nat.gcd_dvd_right _ _
  have hgRR : g ∣ (3 * k + 3) ^ 2 := dvd_pow hgR (by decide : 2 ≠ 0)
  have hg1 : g ∣ 1 := by
    have hsum := dvd_add hgN hgR
    rw [norm_eq] at hsum
    exact (Nat.dvd_add_iff_right hgRR).mpr hsum
  exact Nat.dvd_one.mp hg1

/-- Cancellation is unbounded even for pairwise-coprime parameters, and
its removal leaves primitive, positive, strictly ordered cubic collisions. -/
theorem unbounded_primitive_cancellation (M : ℕ) :
    ∃ k : ℕ,
      Nat.Coprime (3 * k + 3) 1 ∧ Nat.Coprime 1 (norm k) ∧
      Nat.Coprime (3 * k + 3) (norm k) ∧
      M < Nat.gcd (Nat.gcd (rawA k) (rawB k))
        (Nat.gcd (rawC k) (rawD k)) ∧
      Nat.gcd (Nat.gcd (rootA k) (rootB k))
        (Nat.gcd (rootC k) (rootD k)) = 1 ∧
      0 < rootA k ∧ rootA k < rootB k ∧
      rootB k < rootC k ∧ rootC k < rootD k ∧
      rootA k ^ 3 + rootD k ^ 3 = rootB k ^ 3 + rootC k ^ 3 := by
  obtain ⟨h₁, h₂, h₃⟩ := parameters_pairwise_coprime M
  obtain ⟨ha, hab, hbc, hcd⟩ := roots_ordered M
  refine ⟨M, h₁, h₂, h₃, ?_, roots_gcd_one M,
    ha, hab, hbc, hcd, reduced_identity M⟩
  rw [raw_gcd_exact]
  have hn : M < norm M := by dsimp [norm]; omega
  have hp : norm M ≤ norm M ^ 2 := Nat.le_self_pow (by decide : 2 ≠ 0) _
  exact hn.trans_le hp

#print axioms unbounded_primitive_cancellation

end CubeParamCancellation
end Erdos1206
