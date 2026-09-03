import FormalConjecturesUtil

/-!
# A finite prime-sumset extension trap

The seed sets `F = {8, 10, 20}` and `G = {3, 9, 21}` have a prime-only sumset
containing every prime from 8 through 31. Nevertheless, no supersets of these
seeds whose sums at least 8 are prime can represent 37.

This is an unconditional finite obstruction only. It is not a solution of the
Ostmann problem, and makes no assertion about general infinite prime sumsets or
about local admissibility of extension forms.
-/

open scoped Pointwise

namespace ExtensionTrap

/-- The left seed. -/
def F : Set ℕ := {8, 10, 20}

/-- The right seed. -/
def G : Set ℕ := {3, 9, 21}

/-- The exact seed sumset; the sum 29 has two seed representations. -/
theorem seed_add_eq :
    F + G = ({11, 13, 17, 19, 23, 29, 31, 41} : Set ℕ) := by
  ext n
  simp [F, G, Set.mem_add, or_and_right, exists_or, or_assoc, or_left_comm, eq_comm]

/-- Every old sum is prime, with no threshold exception. -/
theorem seed_add_subset_primes : F + G ⊆ {p : ℕ | Nat.Prime p} := by
  intro p hp
  rw [seed_add_eq] at hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- Every prime in the closed interval from 8 to 31 is already represented. -/
theorem prime_mem_seed_add_of_between {p : ℕ}
    (hp : Nat.Prime p) (h8 : 8 ≤ p) (h31 : p ≤ 31) : p ∈ F + G := by
  rw [seed_add_eq]
  interval_cases p <;> norm_num at hp <;> norm_num

/-- On the whole interval from 8 to 31, seed membership agrees with primality. -/
theorem seed_add_iff_prime_of_between {p : ℕ} (h8 : 8 ≤ p) (h31 : p ≤ 31) :
    p ∈ F + G ↔ Nat.Prime p := by
  exact ⟨fun hp => seed_add_subset_primes hp,
    fun hp => prime_mem_seed_add_of_between hp h8 h31⟩

/-- The target is prime. -/
theorem thirty_seven_prime : Nat.Prime 37 := by
  norm_num

/-- The target is not already a seed sum. -/
theorem thirty_seven_not_mem_seed_add : 37 ∉ F + G := by
  rw [seed_add_eq]
  norm_num

/-- The only lower members of twin-prime pairs between 8 and 45. -/
theorem twin_primes_between_eight_and_forty_five {t : ℕ}
    (h8 : 8 ≤ t) (h45 : t ≤ 45) (ht : Nat.Prime t) (ht2 : Nat.Prime (t + 2)) :
    t = 11 ∨ t = 17 ∨ t = 29 ∨ t = 41 := by
  interval_cases t <;> norm_num at ht <;> norm_num at ht2 <;> norm_num

/-- The finite obstruction only needs the four seed memberships displayed here.
A putative representation `x + y = 37` makes `t = y + 8 = 45 - x` a lower
member of a twin-prime pair. The four possible values of `t` force a composite
sum with 21 or 9. No infinitude or unproved number-theoretic hypothesis is used. -/
theorem thirty_seven_not_mem_add {A B : Set ℕ}
    (h8 : 8 ∈ A) (h10 : 10 ∈ A) (h9 : 9 ∈ B) (h21 : 21 ∈ B)
    (hprime : ∀ a ∈ A, ∀ b ∈ B, 8 ≤ a + b → Nat.Prime (a + b)) :
    37 ∉ A + B := by
  intro h37
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_add.mp h37
  have hty : Nat.Prime (y + 8) := by
    simpa only [Nat.add_comm] using hprime 8 h8 y hy (by omega)
  have hty2 : Nat.Prime ((y + 8) + 2) := by
    convert hprime 10 h10 y hy (by omega) using 1
    omega
  have ht := twin_primes_between_eight_and_forty_five
    (t := y + 8) (by omega) (by omega) hty hty2
  rcases ht with ht | ht | ht | ht
  · have hx34 : x = 34 := by omega
    have hbad := hprime x hx 21 h21 (by omega)
    norm_num [hx34] at hbad
  · have hx28 : x = 28 := by omega
    have hbad := hprime x hx 21 h21 (by omega)
    norm_num [hx28] at hbad
  · have hx16 : x = 16 := by omega
    have hbad := hprime x hx 9 h9 (by omega)
    norm_num [hx16] at hbad
  · have hx4 : x = 4 := by omega
    have hbad := hprime x hx 21 h21 (by omega)
    norm_num [hx4] at hbad

/-- Full-seed version of the obstruction. -/
theorem seed_extension_trap {A B : Set ℕ} (hF : F ⊆ A) (hG : G ⊆ B)
    (hprime : ∀ a ∈ A, ∀ b ∈ B, 8 ≤ a + b → Nat.Prime (a + b)) :
    37 ∉ A + B := by
  exact thirty_seven_not_mem_add
    (hF (by simp [F])) (hF (by simp [F]))
    (hG (by simp [G])) (hG (by simp [G])) hprime

/-- Exact bounded criterion for adjoining a representation of `p` while keeping
all sums in an allowed set `T`. The target-membership condition `p ∈ T` is
necessary: the two cross-sum conditions alone do not check the new sum `p`.
The seeds and allowed set need not be finite. -/
theorem exists_extension_iff {F₀ G₀ T : Set ℕ} {p : ℕ}
    (hFG : F₀ + G₀ ⊆ T) :
    (∃ A B : Set ℕ, F₀ ⊆ A ∧ G₀ ⊆ B ∧ p ∈ A + B ∧ A + B ⊆ T) ↔
      p ∈ T ∧ ∃ x ≤ p, ({x} : Set ℕ) + G₀ ⊆ T ∧
        ({p - x} : Set ℕ) + F₀ ⊆ T := by
  constructor
  · rintro ⟨A, B, hFA, hGB, hpAB, hAB⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_add.mp hpAB
    have hy_eq : p - x = y := by omega
    refine ⟨hAB hpAB, x, by omega, ?_, ?_⟩
    · exact (Set.add_subset_add (Set.singleton_subset_iff.mpr hx) hGB).trans hAB
    · rw [hy_eq, add_comm]
      exact (Set.add_subset_add hFA (Set.singleton_subset_iff.mpr hy)).trans hAB
  · rintro ⟨hpT, x, hxp, hxG, hyF⟩
    refine ⟨insert x F₀, insert (p - x) G₀,
      Set.subset_insert _ _, Set.subset_insert _ _, ?_, ?_⟩
    · exact Set.mem_add.mpr ⟨x, by simp, p - x, by simp, Nat.add_sub_of_le hxp⟩
    · intro z hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hz
      rcases Set.mem_insert_iff.mp ha with rfl | ha
      · rcases Set.mem_insert_iff.mp hb with rfl | hb
        · simpa only [Nat.add_sub_of_le hxp] using hpT
        · exact hxG (Set.add_mem_add (by simp) hb)
      · rcases Set.mem_insert_iff.mp hb with rfl | hb
        · have h : (p - x) + a ∈ T := hyF (Set.add_mem_add (by simp) ha)
          simpa only [Nat.add_comm] using h
        · exact hFG (Set.add_mem_add ha hb)

/-- For an allowed target, the criterion reduces to the two bounded cross-sum
checks. The converse constructs `A = insert x F₀`, `B = insert (p - x) G₀`. -/
theorem exists_extension_iff_of_mem {F₀ G₀ T : Set ℕ} {p : ℕ}
    (hFG : F₀ + G₀ ⊆ T) (hpT : p ∈ T) :
    (∃ A B : Set ℕ, F₀ ⊆ A ∧ G₀ ⊆ B ∧ p ∈ A + B ∧ A + B ⊆ T) ↔
      ∃ x ≤ p, ({x} : Set ℕ) + G₀ ⊆ T ∧ ({p - x} : Set ℕ) + F₀ ⊆ T := by
  simpa only [hpT, true_and] using exists_extension_iff (p := p) hFG

end ExtensionTrap
