import Submission.Work
import Submission.PrimeCountingDyadicDiscrepancy

/-!
An obstruction to a local shortcut for the largest-prime increment conjecture.
A surviving point can be arbitrarily isolated compared with the number of
sieving primes. This does not disprove the quadratic Jacobsthal conjecture:
the constructed interval has one survivor, at its centre.
-/
namespace Erdos970.SymmetricIsolation
open Finset Filter

/-- The centre H is the only survivor among positions 0,...,2H. -/
def Isolated (P : Finset ℕ) (r : ℕ → ℕ) (H : ℕ) : Prop :=
  ∀ i : ℕ, i ≤ 2 * H → ((∀ p ∈ P, ¬i ≡ r p [MOD p]) ↔ i = H)

lemma core_card (H : ℕ) : (H + 2).primesBelow.card = (H + 1).primeCounting := by
  simp only [Nat.primesBelow, Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range, Nat.add_assoc]

/-- All primes at most H+1 use the class H+1. One fresh prime covers H+2.
The resulting interval has precisely its central point left uncovered. -/
theorem exists_isolated (H : ℕ) (hH : 1 ≤ H) :
    ∃ P : Finset ℕ, ∃ r : ℕ → ℕ,
      (∀ p ∈ P, p.Prime) ∧ P.card = (H + 1).primeCounting + 1 ∧ Isolated P r H := by
  classical
  let Q := (H + 2).primesBelow
  obtain ⟨q, hqbig, hq⟩ := Nat.exists_infinite_primes (2 * H + 3)
  have hqQ : q ∉ Q := by
    intro h
    have hlt := (Nat.mem_primesBelow.mp h).1
    omega
  let P := insert q Q
  let r := fun p : ℕ => if p = q then H + 2 else H + 1
  have hQ : ∀ p ∈ Q, p.Prime := fun p hp => (Nat.mem_primesBelow.mp hp).2
  have h2Q : 2 ∈ Q := Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · exact hq
    · exact hQ p hp
  have hrQ (p : ℕ) (hp : p ∈ Q) : r p = H + 1 := by
    have hpq : p ≠ q := by rintro rfl; exact hqQ hp
    simp [r, hpq]
  have hcenter : ∀ p ∈ P, ¬H ≡ r p [MOD p] := by
    intro p hp hmod
    rcases mem_insert.mp hp with hpq | hp
    · have hmod' : H ≡ H + 2 [MOD q] := by simpa [hpq, r] using hmod
      have he := hmod'.eq_of_lt_of_lt (by omega : H < q) (by omega : H + 2 < q)
      omega
    · rw [hrQ p hp] at hmod
      have hd : p ∣ 1 := by
        simpa using (Nat.modEq_iff_dvd' (by omega : H ≤ H + 1)).mp hmod
      exact (hQ p hp).not_dvd_one hd
  refine ⟨P, r, hprime, ?_, ?_⟩
  · rw [card_insert_of_notMem hqQ]
    exact congrArg (fun n => n + 1) (core_card H)
  · intro i hi
    constructor
    · intro ha
      by_contra hne
      by_cases hi2 : i = H + 2
      · apply ha q (mem_insert_self _ _)
        simp only [r, if_pos rfl, hi2]
        exact Nat.ModEq.refl _
      by_cases hi1 : i = H + 1
      · apply ha 2 (mem_insert_of_mem h2Q)
        rw [hrQ 2 h2Q, hi1]
      rcases lt_or_gt_of_ne hi1 with hlt | hgt
      · have hd2 : 2 ≤ H + 1 - i := by omega
        obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : H + 1 - i ≠ 1)
        have hple := Nat.le_of_dvd (by omega : 0 < H + 1 - i) hpd
        have hpQ : p ∈ Q := Nat.mem_primesBelow.mpr ⟨by omega, hp⟩
        apply ha p (mem_insert_of_mem hpQ)
        rw [hrQ p hpQ]
        exact (Nat.modEq_iff_dvd' hlt.le).mpr hpd
      · have hd2 : 2 ≤ i - (H + 1) := by omega
        obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : i - (H + 1) ≠ 1)
        have hple := Nat.le_of_dvd (by omega : 0 < i - (H + 1)) hpd
        have hpQ : p ∈ Q := Nat.mem_primesBelow.mpr ⟨by omega, hp⟩
        apply ha p (mem_insert_of_mem hpQ)
        rw [hrQ p hpQ]
        exact ((Nat.modEq_iff_dvd' hgt.le).mpr hpd).symm
    · rintro rfl
      exact hcenter

/-- The prime budget of the construction is sublinear in its radius. -/
lemma eventually_small_budget (A : ℕ) :
    ∀ᶠ H : ℕ in atTop, A * ((H + 1).primeCounting + 1) < H := by
  have ht : Tendsto (fun H : ℕ => H + 1) atTop atTop :=
    tendsto_atTop_mono (fun H => by omega : ∀ H : ℕ, H ≤ H + 1) tendsto_id
  have heps : (0 : ℝ) < 1 / (4 * (A + 1 : ℕ)) := by positivity
  have hev := (PrimeCountingDyadic.density_tendsto_zero.comp ht).eventually
    (gt_mem_nhds heps)
  filter_upwards [hev, eventually_ge_atTop (4 * (A + 1))] with H h Hlarge
  have hpos : (0 : ℝ) < (H + 1 : ℕ) := by positivity
  have hh := (div_lt_div_iff₀ hpos (by positivity : (0 : ℝ) < 4 * (A + 1 : ℕ))).mp h
  have hb : 4 * (A + 1) * (H + 1).primeCounting < H + 1 := by
    exact_mod_cast (show (4 : ℝ) * (A + 1 : ℕ) * (H + 1).primeCounting < (H + 1 : ℕ) by
      nlinarith [hh])
  nlinarith

/-- Both the prime budget and the ratio of the isolation radius to that budget
can be made arbitrarily large. The centre is still a genuine survivor. -/
theorem arbitrarily_isolated (A K : ℕ) :
    ∃ P : Finset ℕ, ∃ r : ℕ → ℕ, ∃ H : ℕ,
      (∀ p ∈ P, p.Prime) ∧ K ≤ P.card ∧ A * P.card < H ∧ Isolated P r H := by
  obtain ⟨H, hb, hH⟩ := ((eventually_small_budget A).and
    (eventually_ge_atTop (Nat.nth Nat.Prime K + 1))).exists
  obtain ⟨P, r, hP, hc, hi⟩ := exists_isolated H (by omega)
  have hcount := Nat.monotone_primeCounting (show Nat.nth Nat.Prime K ≤ H + 1 by omega)
  rw [PrimeCountingLower.primeCounting_nth] at hcount
  exact ⟨P, r, H, hP, by omega, by rwa [hc], hi⟩

/-- A bounded-distance companion to every survivor would be too strong.
This negates that local shortcut, not the largest-prime increment estimate. -/
theorem no_linear_companion_bound :
    ¬∃ A : ℕ, ∀ (P : Finset ℕ) (r : ℕ → ℕ) (H : ℕ),
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, ¬H ≡ r p [MOD p]) →
      ∃ i : ℕ, i ≠ H ∧ i ≤ H + A * P.card ∧ H ≤ i + A * P.card ∧
        (∀ p ∈ P, ¬i ≡ r p [MOD p]) := by
  rintro ⟨A, hA⟩
  obtain ⟨P, r, H, hP, _, hlarge, hi⟩ := arbitrarily_isolated A 1
  obtain ⟨i, hine, hiupper, _, hisurv⟩ := hA P r H hP
    ((hi H (by omega)).mpr rfl)
  exact hine ((hi i (by omega)).mp hisurv)

/-- CRT realizes every residue configuration as actual coprimality to one
positive integer, preserving the entire set of distinct prime factors. -/
lemma realize_residue_configuration (P : Finset ℕ) (r : ℕ → ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    ∃ n : ℕ, ∃ a : ℤ, 0 < n ∧ n.primeFactors = P ∧
      ∀ i : ℕ, (a + i).natAbs.Coprime n ↔ (∀ p ∈ P, ¬i ≡ r p [MOD p]) := by
  classical
  let n := ∏ p ∈ P, p
  have hn : 0 < n := prod_pos (fun p hp => (hP p hp).pos)
  have hco : Set.Pairwise (↑P : Set ℕ) Nat.Coprime :=
    fun p hp q hq hpq => (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq
  let b := Nat.chineseRemainderOfFinset r id P (fun p hp => (hP p hp).ne_zero) hco
  refine ⟨n, -(b.val : ℤ), hn, Nat.primeFactors_prod hP, fun i => ?_⟩
  constructor
  · intro hc p hp hi
    have hbpi : b.val ≡ i [MOD p] := (b.property p hp).trans hi.symm
    have hd : (p : ℤ) ∣ -(b.val : ℤ) + i := by
      convert hbpi.dvd using 1; ring
    exact Nat.not_coprime_of_dvd_of_dvd (hP p hp).one_lt
      (Int.natCast_dvd.mp hd) (dvd_prod_of_mem id hp) hc
  · intro ha
    by_contra hc
    obtain ⟨p, hp, hpi, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hpP : p ∈ P := by
      rw [← Nat.primeFactors_prod hP]
      exact Nat.mem_primeFactors.mpr ⟨hp, hpn, hn.ne'⟩
    have hd := Int.natCast_dvd.mpr hpi
    have hbi : b.val ≡ i [MOD p] := Nat.modEq_of_dvd (by convert hd using 1; ring)
    exact ha p hpP (hbi.symm.trans (b.property p hpP))

/-- The isolated-survivor obstruction is realized by actual integers, not merely
by a relaxation of residue-class moments. -/
theorem arbitrarily_isolated_integer (A K : ℕ) :
    ∃ n : ℕ, ∃ a : ℤ, ∃ H : ℕ,
      0 < n ∧ K ≤ n.primeFactors.card ∧ A * n.primeFactors.card < H ∧
      ∀ i : ℕ, i ≤ 2 * H → ((a + i).natAbs.Coprime n ↔ i = H) := by
  obtain ⟨P, r, H, hP, hK, hA, hI⟩ := arbitrarily_isolated A K
  obtain ⟨n, a, hn, hnf, hiff⟩ := realize_residue_configuration P r hP
  refine ⟨n, a, H, hn, by rwa [hnf], by rwa [hnf], fun i hi => ?_⟩
  exact (hiff i).trans (hI i hi)

/-- The same construction, now centred at an actual coprime integer and
allowing positive and negative integer offsets. -/
theorem arbitrarily_isolated_center (A K : ℕ) :
    ∃ n : ℕ, ∃ c : ℤ, ∃ H : ℕ,
      0 < n ∧ K ≤ n.primeFactors.card ∧ A * n.primeFactors.card < H ∧
      ∀ t : ℤ, t.natAbs ≤ H → ((c + t).natAbs.Coprime n ↔ t = 0) := by
  obtain ⟨n, a, H, hn, hK, hA, hI⟩ := arbitrarily_isolated_integer A K
  refine ⟨n, a + H, H, hn, hK, hA, fun t ht => ?_⟩
  have ht' : |t| ≤ (H : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast ht
  have htlo := (abs_le.mp ht').1
  have hthi := (abs_le.mp ht').2
  let i := (t + H).toNat
  have hiCast : (i : ℤ) = t + H := Int.toNat_of_nonneg (by omega)
  have hi : i ≤ 2 * H := by
    have h : (i : ℤ) ≤ (2 * H : ℕ) := by push_cast; omega
    exact_mod_cast h
  have he : a + (H : ℤ) + t = a + (i : ℤ) := by rw [hiCast]; ring
  rw [he, hI i hi]
  constructor
  · intro h
    have hh := congrArg (fun x : ℕ => (x : ℤ)) h
    dsimp only at hh
    rw [hiCast] at hh
    omega
  · intro h
    have hh : (i : ℤ) = H := by rw [hiCast, h]; simp
    exact_mod_cast hh

/-- No real constant gives a linearly close companion to every coprime integer.
This is an auxiliary obstruction, not a negation of Erdős 970. -/
theorem no_real_linear_companion_bound :
    ¬∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n → ∀ a : ℤ, a.natAbs.Coprime n →
      ∃ t : ℤ, t ≠ 0 ∧ (t.natAbs : ℝ) ≤ C * n.primeFactors.card ∧
        (a + t).natAbs.Coprime n := by
  rintro ⟨C, _, hC⟩
  obtain ⟨A, hA⟩ := exists_nat_gt C
  obtain ⟨n, c, H, hn, _, hlarge, hI⟩ := arbitrarily_isolated_center A 1
  have hc : c.natAbs.Coprime n := by
    simpa only [add_zero] using (hI 0 (by simp)).mpr rfl
  obtain ⟨t, ht, hdist, hcop⟩ := hC n hn c hc
  have hsmall : t.natAbs ≤ A * n.primeFactors.card := by
    have hh := hdist.trans (mul_le_mul_of_nonneg_right hA.le (Nat.cast_nonneg _))
    exact_mod_cast hh
  exact ht ((hI t (by omega)).mp hcop)

#print axioms exists_isolated
#print axioms arbitrarily_isolated_center
#print axioms no_real_linear_companion_bound
#print axioms arbitrarily_isolated_integer
#print axioms arbitrarily_isolated
#print axioms no_linear_companion_bound
end Erdos970.SymmetricIsolation
