import Submission.IntegerSieve

/-!
# Arithmetic input for integer incidence trades

This connects the abstract, covering-specific trade construction to the exact
floor counts of divisibility on `[1,L]`. It also gives an independent CRT
rounding-correlation constraint that need not hold in an abstract array.
No statement of Erdős 970 is imported or assumed.
-/

namespace IntegerSieve

open Finset

/-- Integer histogram of a finite incidence array. -/
def histogram {L : ℕ} (rows : Fin L → Finset ℕ) (T : Finset ℕ) : ℤ :=
  (Finset.univ.filter fun i => rows i = T).card

lemma histogram_nonneg {L : ℕ} (rows : Fin L → Finset ℕ) (T : Finset ℕ) :
    0 ≤ histogram rows T := by
  exact Nat.cast_nonneg _

/-- Counting a union of disjoint exact-pattern fibers recovers the intersection. -/
lemma histogram_intersections {L : ℕ} {P : Finset ℕ}
    (rows : Fin L → Finset ℕ) (hrows : ∀ i, rows i ⊆ P) (S : Finset ℕ) :
    upperCount P (histogram rows) S = (rowCount rows S : ℤ) := by
  unfold upperCount histogram rowCount
  rw [← Finset.sum_filter]
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin L)) (P.powerset.filter fun T => S ⊆ T) rows
  have heq : (Finset.univ.filter fun i : Fin L =>
      rows i ∈ P.powerset.filter (fun T => S ⊆ T)) =
      Finset.univ.filter (fun i : Fin L => S ⊆ rows i) := by
    ext i
    simp [hrows i]
  rw [heq] at h
  exact_mod_cast h

/-- The baseline consists of the prime-divisibility supports of `1,...,L`. -/
def baseRows (P : Finset ℕ) (L : ℕ) (i : Fin L) : Finset ℕ :=
  P.filter fun p => p ∣ i.val + 1

lemma baseRows_subset (P : Finset ℕ) (L : ℕ) (i : Fin L) :
    baseRows P L i ⊆ P := Finset.filter_subset _ _

lemma modulus_dvd_iff {S : Finset ℕ} (hprime : ∀ p ∈ S, Nat.Prime p) (n : ℕ) :
    modulus S ∣ n ↔ ∀ p ∈ S, p ∣ n := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem (fun q : ℕ => q) hp).trans h
  · intro h
    apply Finset.prod_dvd_of_isRelPrime ?_ h
    intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq)

lemma modulus_pos {S : Finset ℕ} (hprime : ∀ p ∈ S, Nat.Prime p) :
    0 < modulus S := by
  exact Finset.prod_pos (fun p hp => (hprime p hp).pos)

/-- No analytic remainder estimate: every baseline intersection is exactly its
integer floor, for every subset of the distinct prime labels. -/
theorem baseRows_intersections {P : Finset ℕ} (L : ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p) {S : Finset ℕ} (hSP : S ⊆ P) :
    rowCount (baseRows P L) S = L / modulus S := by
  have hSprime : ∀ p ∈ S, Nat.Prime p := fun p hp => hprime p (hSP hp)
  have heq : (Finset.univ.filter fun i : Fin L => S ⊆ baseRows P L i) =
      Finset.univ.filter (fun i : Fin L => modulus S ∣ i.val + 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [modulus_dvd_iff hSprime]
    constructor
    · intro h p hp
      exact (Finset.mem_filter.mp (h hp)).2
    · intro h p hp
      exact Finset.mem_filter.mpr ⟨hSP hp, h p hp⟩
  unfold rowCount
  rw [heq, Finset.card_filter]
  change (∑ i : Fin L, if modulus S ∣ i.val + 1 then 1 else 0) = L / modulus S
  rw [Fin.sum_univ_eq_sum_range (fun n => if modulus S ∣ n + 1 then 1 else 0)]
  rw [← Finset.card_filter]
  exact Nat.card_multiples L (modulus S)

theorem baseHistogram_intersections {P : Finset ℕ} (L : ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p) {S : Finset ℕ} (hSP : S ⊆ P) :
    upperCount P (histogram (baseRows P L)) S = ((L / modulus S : ℕ) : ℤ) := by
  rw [histogram_intersections (baseRows P L) (baseRows_subset P L),
    baseRows_intersections L hprime hSP]

/-- An elementary integer ceiling identity in the only direction needed by a trade. -/
lemma floor_lt_ceil_of_not_dvd {L d : ℕ} (hd : 0 < d) (hnd : ¬ d ∣ L) :
    L / d < (L + d - 1) / d := by
  have hle : L / d * d ≤ L := Nat.div_mul_le_self L d
  have hlt : L / d * d < L := by
    apply lt_of_le_of_ne hle
    intro heq
    apply hnd
    exact ⟨L / d, by nlinarith⟩
  apply Nat.lt_of_succ_le
  apply (Nat.le_div_iff_mul_le hd).mpr
  rw [Nat.succ_mul]
  omega

/-- A precise sufficient condition for an abstract prime-covering array, with
ALL floor/ceiling constraints. Existence of the family `F` is NOT asserted.
The conditions are finite integer capacities and the prohibition on changing
an already integral intersection count. -/
theorem prime_cube_packing_cover {P : Finset ℕ} (L : ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p) {F : Finset (Finset ℕ)}
    (hFP : ∀ R ∈ F, R ⊆ P) (hodd : ∀ R ∈ F, Odd R.card)
    (hcap : ∀ T ⊆ P, Even T.card →
      (load F T : ℤ) ≤ histogram (baseRows P L) T)
    (hsize : histogram (baseRows P L) ∅ = (F.card : ℤ))
    (hslack : ∀ R ∈ F, ¬ modulus R ∣ L) :
    ∃ w : Finset ℕ → ℤ,
      (∀ T ⊆ P, 0 ≤ w T) ∧ w ∅ = 0 ∧
        (∀ S ⊆ P,
          ((L / modulus S : ℕ) : ℤ) ≤ upperCount P w S ∧
          upperCount P w S ≤ (((L + modulus S - 1) / modulus S : ℕ) : ℤ)) := by
  let b : Finset ℕ → ℤ := histogram (baseRows P L)
  obtain ⟨hpos, hzero, _, _⟩ := odd_trade_cover b hFP hodd
    (fun T _ => histogram_nonneg (baseRows P L) T) hcap hsize
  refine ⟨traded b F, hpos, hzero, ?_⟩
  apply odd_trade_preserves_bounds b hFP hodd
    (fun S => ((L / modulus S : ℕ) : ℤ))
    (fun S => (((L + modulus S - 1) / modulus S : ℕ) : ℤ))
  · intro S hSP
    have hd : 0 < modulus S := modulus_pos (fun p hp => hprime p (hSP hp))
    have hfloor := baseHistogram_intersections L hprime hSP
    change upperCount P b S = _ at hfloor
    rw [hfloor]
    refine ⟨le_rfl, ?_⟩
    exact_mod_cast (Nat.div_le_div_right (show L ≤ L + modulus S - 1 by omega) :
      L / modulus S ≤ (L + modulus S - 1) / modulus S)
  · intro R hR
    have hd : 0 < modulus R := modulus_pos (fun p hp => hprime p (hFP R hR hp))
    have hfloor := baseHistogram_intersections L hprime (hFP R hR)
    change upperCount P b R = _ at hfloor
    rw [hfloor]
    exact_mod_cast floor_lt_ceil_of_not_dvd hd (hslack R hR)

/-- When `L ≡ 1 mod p`, the extra occurrence is possible only for residue zero
in the interval `[0,L)`. This couples rounding choices arithmetically. -/
lemma maximal_residue_count_iff {L p : ℕ} (hp : 0 < p) (hL : L % p = 1) (a : ℕ) :
    Nat.count (fun n => n ≡ a [MOD p]) L = L / p + 1 ↔ a % p = 0 := by
  rw [Nat.count_modEq_card L hp a, hL]
  split_ifs <;> omega

/-- A CRT rounding correlation absent from the positive-intersection LP:
for `L ≡ 1 mod pq`, two maximal single-column counts force a maximal joint count. -/
theorem maximal_counts_force_maximal_pair {L p q : ℕ}
    (hp : 1 < p) (hq : 1 < q) (hpq : p.Coprime q) (hL : L % (p * q) = 1)
    (a b : ℕ)
    (ha : Nat.count (fun n => n ≡ a [MOD p]) L = L / p + 1)
    (hb : Nat.count (fun n => n ≡ b [MOD q]) L = L / q + 1) :
    Nat.count (fun n => n ≡ a [MOD p] ∧ n ≡ b [MOD q]) L = L / (p * q) + 1 := by
  have hLp : L % p = 1 := by
    have h := Nat.mod_mod_of_dvd L (dvd_mul_right p q)
    rw [hL, Nat.mod_eq_of_lt hp] at h
    exact h.symm
  have hLq : L % q = 1 := by
    have h := Nat.mod_mod_of_dvd L (dvd_mul_left q p)
    rw [hL, Nat.mod_eq_of_lt hq] at h
    exact h.symm
  have ha0 := (maximal_residue_count_iff (by omega) hLp a).mp ha
  have hb0 := (maximal_residue_count_iff (by omega) hLq b).mp hb
  have heq : (fun n => n ≡ a [MOD p] ∧ n ≡ b [MOD q]) =
      (fun n => n ≡ 0 [MOD p * q]) := by
    funext n
    apply propext
    have h := Nat.modEq_and_modEq_iff_modEq_mul (a := n) (b := 0) hpq
    simpa only [Nat.ModEq, ha0, hb0, Nat.zero_mod] using h
  have hpqpos : 0 < p * q := Nat.mul_pos (by omega) (by omega)
  simpa only [heq, Nat.zero_mod, hL, Nat.zero_lt_one, if_true] using
    (Nat.count_modEq_card L hpqpos 0)

end IntegerSieve

#print axioms IntegerSieve.baseHistogram_intersections
#print axioms IntegerSieve.prime_cube_packing_cover
#print axioms IntegerSieve.maximal_counts_force_maximal_pair
