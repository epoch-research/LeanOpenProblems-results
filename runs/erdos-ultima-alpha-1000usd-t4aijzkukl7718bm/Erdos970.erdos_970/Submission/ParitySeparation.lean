import Submission.TwoSurvivorReduction
import Submission.OptimalCoverCore

/-! Parity sharpens both the large-prime separation test and bounds on optimal cores. -/
namespace Erdos970.IncrementReduction

/-- Two positions avoiding the same parity class have equal parity. -/
theorem modEq_two_of_avoids {i j a : ℕ}
    (hi : ¬i ≡ a [MOD 2]) (hj : ¬j ≡ a [MOD 2]) : i ≡ j [MOD 2] := by
  have hi2 := Nat.mod_lt i (by decide : 0 < 2)
  have hj2 := Nat.mod_lt j (by decide : 0 < 2)
  have ha2 := Nat.mod_lt a (by decide : 0 < 2)
  change i % 2 = j % 2
  change ¬i % 2 = a % 2 at hi
  change ¬j % 2 = a % 2 at hj
  omega

/-- Distinct same-parity positions in one odd-prime class are separated by at least `2p`. -/
theorem two_mul_le_sub_of_modEq {i j a p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hij : i < j) (hi : ¬i ≡ a [MOD 2]) (hj : ¬j ≡ a [MOD 2])
    (hmod : i ≡ j [MOD p]) : 2 * p ≤ j - i := by
  have hd2 : 2 ∣ j - i := (Nat.modEq_iff_dvd' hij.le).mp (modEq_two_of_avoids hi hj)
  have hdp : p ∣ j - i := (Nat.modEq_iff_dvd' hij.le).mp hmod
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm
  exact Nat.le_of_dvd (Nat.sub_pos_of_lt hij) (hcop.mul_dvd_of_dvd_of_dvd hd2 hdp)

/-- When 2 is already sieving, a new prime only needs `2p > g` to reduce insertion
to the two-survivor condition. -/
theorem primeSetBound_insert_of_two_of_two_mem {P : Finset ℕ} {p g m : ℕ}
    (h2 : 2 ∈ P) (hpos : ∀ q ∈ P, 0 < q) (hp : p.Prime) (hp2 : p ≠ 2)
    (hg : PrimeSetBound P g) (hgp : g < 2 * p)
    (hm : PrimeSetTwoBound P m) : PrimeSetBound (insert p P) m := by
  classical
  intro r
  by_contra hbad
  push_neg at hbad
  have hforced (x : ℕ) (hx : x < m) (hxa : ∀ q ∈ P, ¬x ≡ r q [MOD q]) :
      x ≡ r p [MOD p] := by
    obtain ⟨q, hq, hxq⟩ := hbad x hx
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hxq
    · exact False.elim (hxa q hq hxq)
  have hsep (x y : ℕ) (hx : x < m) (hy : y < m) (hxy : x < y)
      (hxa : ∀ q ∈ P, ¬x ≡ r q [MOD q])
      (hya : ∀ q ∈ P, ¬y ≡ r q [MOD q]) : 2 * p ≤ y - x :=
    two_mul_le_sub_of_modEq hp hp2 hxy (hxa 2 h2) (hya 2 h2)
      ((hforced x hx hxa).trans (hforced y hy hya).symm)
  obtain ⟨i, hi, j, hj, hij, hia, hja⟩ := hm r
  wlog hijlt : i < j generalizing i j
  · exact this j hj i hi hij.symm hja hia (by omega)
  have hgap := hsep i j hi hj hijlt hia hja
  obtain ⟨t, ht, hta⟩ := primeSetBound_translate hpos hg r (i + 1)
  have htm : i + 1 + t < m := by omega
  have hgap' := hsep i (i + 1 + t) hi htm (by omega) hia hta
  omega

theorem primeSetBound_insert_iff_two_of_two_mem {P : Finset ℕ} {p g m : ℕ}
    (h2 : 2 ∈ P) (hpos : ∀ q ∈ P, 0 < q) (hp : p.Prime) (hpP : p ∉ P)
    (hg : PrimeSetBound P g) (hgp : g < 2 * p) :
    PrimeSetBound (insert p P) m ↔ PrimeSetTwoBound P m := by
  refine ⟨primeSetTwoBound_of_insert hpP, ?_⟩
  apply primeSetBound_insert_of_two_of_two_mem h2 hpos hp _ hg hgp
  intro hp2
  exact hpP (hp2 ▸ h2)

end Erdos970.IncrementReduction

namespace Erdos970.OptimalCoverCore
open IncrementReduction

/-- If parity is present in an optimal core, every other retained prime is below half
the interval length: its two private points both avoid the parity class. -/
theorem two_mul_used_prime_lt_length {m : ℕ} {P : Finset ℕ} {r : ℕ → ℕ}
    (h : IsOptimal m P r) (h2 : 2 ∈ P) (p : ℕ) (hp : p ∈ P) (hp2 : p ≠ 2) :
    2 * p < m := by
  classical
  have h2e : 2 ∈ P.erase p := Finset.mem_erase.mpr ⟨hp2.symm, h2⟩
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp
    (show 1 < (privatePositions m P r p).card by
      have := used_prime_private_card_ge_two h p hp
      omega)
  have hi' := Finset.mem_filter.mp hi
  have hj' := Finset.mem_filter.mp hj
  have hia := (mem_survivors m (P.erase p) r i).mp hi'.1
  have hja := (mem_survivors m (P.erase p) r j).mp hj'.1
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hh := two_mul_le_sub_of_modEq (h.1 p hp) hp2 hij
      (hia.2 2 h2e) (hja.2 2 h2e) (hi'.2.trans hj'.2.symm)
    omega
  · have hh := two_mul_le_sub_of_modEq (h.1 p hp) hp2 hji
      (hja.2 2 h2e) (hia.2 2 h2e) (hj'.2.trans hi'.2.symm)
    omega

/-- A core not using parity has at most two surviving positions. -/
theorem survivor_card_le_two_of_two_not_mem {m : ℕ} {P : Finset ℕ} {r : ℕ → ℕ}
    (h : IsOptimal m P r) (h2 : 2 ∉ P) : (survivors m P r).card ≤ 2 := by
  by_contra hs
  exact h2 (prime_lt_survivor_card_mem h 2 Nat.prime_two (by omega))

#print axioms IncrementReduction.primeSetBound_insert_iff_two_of_two_mem
#print axioms two_mul_used_prime_lt_length
end Erdos970.OptimalCoverCore
