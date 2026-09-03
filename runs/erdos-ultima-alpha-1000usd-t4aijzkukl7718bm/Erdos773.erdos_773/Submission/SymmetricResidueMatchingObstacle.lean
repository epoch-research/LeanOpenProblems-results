import FormalConjecturesUtil

/-! A restriction on a proposed prime-center symmetry argument.
Reflection symmetry and integer square-Sidonness do not imply modular
square-Sidonness at the reflection modulus. This is not a disproof of
Erdős 773.
-/
namespace Erdos773.SymmetricResidueMatchingObstacle
open Finset
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
set_option Elab.async false

def roots : Finset ℕ := {1, 2, 3, 10, 11, 12}

def squares : Finset ℕ := roots.image (fun n => n ^ 2)

lemma roots_symmetric : ∀ n ∈ roots, n ≤ 13 ∧ 13 - n ∈ roots := by
  decide +kernel

lemma roots_positive : roots ⊆ Icc 1 12 := by
  decide +kernel

lemma squares_sidon : IsSidon (squares : Set ℕ) := by
  change ∀ a ∈ squares, ∀ c ∈ squares, ∀ b ∈ squares, ∀ d ∈ squares,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)
  decide +kernel

lemma square_residues : squares.image (fun (n : ℕ) => (n : ZMod 13)) = {1, 4, 9} := by
  decide +kernel

lemma square_residues_not_sidon :
    ¬ IsSidon ((squares.image (fun (n : ℕ) => (n : ZMod 13))) : Set (ZMod 13)) := by
  rw [square_residues]
  intro h
  have hbad := h 1 (by decide) 9 (by decide) 4 (by decide) 9 (by decide) (by decide)
  have hne : (1 : ZMod 13) ≠ 9 := by decide
  rcases hbad with hbad | hbad <;> exact hne hbad.1

/-- The failure persists even when the reflection modulus is prime. -/
theorem symmetric_integer_sidon_need_not_be_modular_sidon :
    ∃ p : ℕ, p.Prime ∧ ∃ A : Finset ℕ,
      A ⊆ Icc 1 (p - 1) ∧
      (∀ a ∈ A, a ≤ p ∧ p - a ∈ A) ∧
      IsSidon ((A.image (fun n => n ^ 2)) : Set ℕ) ∧
      ¬ IsSidon ((A.image (fun (n : ℕ) => (n : ZMod p) ^ 2)) : Set (ZMod p)) := by
  refine ⟨13, by decide, roots, roots_positive, roots_symmetric, squares_sidon, ?_⟩
  have he : roots.image (fun (n : ℕ) => (n : ZMod 13) ^ 2) =
      squares.image (fun (n : ℕ) => (n : ZMod 13)) := by
    simp only [squares, Finset.image_image, Function.comp_def, Nat.cast_pow]
  rw [he]
  exact square_residues_not_sidon


/-- An unbounded family of reflection moduli. -/
def modulus (t : ℕ) : ℕ := 3 * t + 302

def affineData (i : Fin 6) : ℕ × ℕ :=
  match i.val with
  | 0 => (1, 95)
  | 1 => (1, 103)
  | 2 => (1, 105)
  | 3 => (2, 197)
  | 4 => (2, 199)
  | _ => (2, 207)

def value (t : ℕ) (i : Fin 6) : ℕ := (affineData i).1 * t + (affineData i).2

def familyRoots (t : ℕ) : Finset ℕ := univ.image (value t)

def pairCoefficients (i j : Fin 6) : ℕ × ℕ × ℕ :=
  ((affineData i).1 ^ 2 + (affineData j).1 ^ 2,
   2 * ((affineData i).1 * (affineData i).2 + (affineData j).1 * (affineData j).2),
   (affineData i).2 ^ 2 + (affineData j).2 ^ 2)

def Dominates (x y : ℕ × ℕ × ℕ) : Prop :=
  x.1 ≤ y.1 ∧ x.2.1 ≤ y.2.1 ∧ x.2.2 < y.2.2

instance (x y : ℕ × ℕ × ℕ) : Decidable (Dominates x y) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A finite coefficient certificate, not a numerical sampling of t. -/
lemma pair_certificate : ∀ i j k l : Fin 6,
    ((i = k ∧ j = l) ∨ (i = l ∧ j = k)) ∨
      Dominates (pairCoefficients i j) (pairCoefficients k l) ∨
      Dominates (pairCoefficients k l) (pairCoefficients i j) := by
  decide +kernel

lemma square_sum_formula (t : ℕ) (i j : Fin 6) :
    value t i ^ 2 + value t j ^ 2 =
      (pairCoefficients i j).1 * t ^ 2 +
      (pairCoefficients i j).2.1 * t + (pairCoefficients i j).2.2 := by
  unfold value pairCoefficients
  ring

lemma dominates_evaluation (t : ℕ) {x y : ℕ × ℕ × ℕ} (h : Dominates x y) :
    x.1 * t ^ 2 + x.2.1 * t + x.2.2 <
      y.1 * t ^ 2 + y.2.1 * t + y.2.2 := by
  have hq := Nat.mul_le_mul_right (t ^ 2) h.1
  have hl := Nat.mul_le_mul_right t h.2.1
  have hc := h.2.2
  omega

lemma family_sidon (t : ℕ) :
    IsSidon ((familyRoots t).image (fun n => n ^ 2) : Set ℕ) := by
  intro a ha c hc b hb d hd he
  simp only [mem_coe, familyRoots, image_image, Function.comp_def,
    mem_image, mem_univ, true_and] at ha hc hb hd
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨k, rfl⟩ := hc
  obtain ⟨j, rfl⟩ := hb
  obtain ⟨l, rfl⟩ := hd
  rcases pair_certificate i j k l with hm | hlt | hgt
  · rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · have hh := dominates_evaluation t hlt
    rw [← square_sum_formula, ← square_sum_formula] at hh
    exact (ne_of_lt hh he).elim
  · have hh := dominates_evaluation t hgt
    rw [← square_sum_formula, ← square_sum_formula] at hh
    exact (ne_of_lt hh he.symm).elim

lemma family_card (t : ℕ) : (familyRoots t).card = 6 := by
  have hi : Function.Injective (value t) := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [value, affineData] <;> omega
  rw [familyRoots, card_image_of_injective _ hi]
  simp

lemma family_positive (t : ℕ) : familyRoots t ⊆ Icc 1 (modulus t - 1) := by
  intro n hn
  obtain ⟨i, _, rfl⟩ := mem_image.mp hn
  fin_cases i <;> simp [value, affineData, modulus] <;> omega

lemma family_symmetric (t : ℕ) :
    ∀ n ∈ familyRoots t, n ≤ modulus t ∧ modulus t - n ∈ familyRoots t := by
  intro n hn
  obtain ⟨i, _, rfl⟩ := mem_image.mp hn
  refine ⟨?_, mem_image.mpr ⟨i.rev, mem_univ _, ?_⟩⟩
  · fin_cases i <;> simp [value, affineData, modulus] <;> omega
  · fin_cases i <;> norm_num [value, affineData, modulus, Fin.rev] <;> omega

lemma family_modular_identity (t : ℕ) :
    value t 0 ^ 2 + value t 1 ^ 2 + 8 * modulus t = 2 * value t 2 ^ 2 := by
  norm_num [value, affineData, modulus]
  ring

lemma family_modular_distinct (t : ℕ) :
    (value t 0 : ZMod (modulus t)) ^ 2 ≠ (value t 2 : ZMod (modulus t)) ^ 2 := by
  intro he
  have hi : 3 * value t 0 ^ 2 + 20 * modulus t = 3 * value t 2 ^ 2 + 40 := by
    norm_num [value, affineData, modulus]
    ring
  have hz := congrArg (fun n : ℕ => (n : ZMod (modulus t))) hi
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    ZMod.natCast_self, mul_zero, add_zero, he] at hz
  have h40 : (40 : ZMod (modulus t)) = 0 := by linear_combination -hz
  have hd := (ZMod.natCast_eq_zero_iff 40 (modulus t)).mp h40
  have hle := Nat.le_of_dvd (by decide : 0 < 40) hd
  unfold modulus at hle
  omega

lemma family_not_modular_sidon (t : ℕ) :
    ¬ IsSidon ((familyRoots t).image
      (fun (n : ℕ) => (n : ZMod (modulus t)) ^ 2) : Set (ZMod (modulus t))) := by
  intro hs
  have hm (i : Fin 6) : (value t i : ZMod (modulus t)) ^ 2 ∈
      ((familyRoots t).image (fun (n : ℕ) => (n : ZMod (modulus t)) ^ 2) :
        Set (ZMod (modulus t))) := by
    rw [Finset.mem_coe]
    apply Finset.mem_image.mpr
    refine ⟨value t i, ?_, rfl⟩
    exact mem_image.mpr ⟨i, mem_univ _, rfl⟩
  have he := congrArg (fun n : ℕ => (n : ZMod (modulus t))) (family_modular_identity t)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    ZMod.natCast_self, mul_zero, add_zero, two_mul] at he
  rcases hs _ (hm 0) _ (hm 2) _ (hm 1) _ (hm 2) he with hh | hh <;>
    exact family_modular_distinct t hh.1

lemma arbitrarily_large_prime_centers (B : ℕ) :
    ∃ t : ℕ, B < modulus t ∧ Nat.Prime (modulus t) := by
  obtain ⟨p, hp, hprime, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq
    (max B 302) (by decide : (3 : ℕ) ≠ 0) (by decide : Nat.Coprime 2 3)
  have hp302 : 302 ≤ p := (le_max_right B 302).trans hp.le
  have hm : p % 3 = 2 := by simpa only [Nat.ModEq] using hmod
  have he : modulus ((p - 302) / 3) = p := by unfold modulus; omega
  refine ⟨(p - 302) / 3, ?_, ?_⟩
  · rw [he]
    exact (le_max_left B 302).trans_lt hp
  · rw [he]
    exact hprime

/-- The symmetric-modular shortcut fails at arbitrarily large prime centers.
The sets here have six roots; no bound on the unrestricted maximum follows. -/
theorem unbounded_prime_obstruction (B : ℕ) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧ ∃ A : Finset ℕ,
      A ⊆ Icc 1 (p - 1) ∧
      (∀ a ∈ A, a ≤ p ∧ p - a ∈ A) ∧
      IsSidon ((A.image (fun n => n ^ 2)) : Set ℕ) ∧
      ¬ IsSidon ((A.image (fun (n : ℕ) => (n : ZMod p) ^ 2)) : Set (ZMod p)) := by
  obtain ⟨t, ht, hp⟩ := arbitrarily_large_prime_centers B
  exact ⟨modulus t, ht, hp, familyRoots t, family_positive t, family_symmetric t,
    family_sidon t, family_not_modular_sidon t⟩

#print axioms family_card
#print axioms family_sidon
#print axioms family_not_modular_sidon
#print axioms unbounded_prime_obstruction

#print axioms squares_sidon
#print axioms symmetric_integer_sidon_need_not_be_modular_sidon
end Erdos773.SymmetricResidueMatchingObstacle
