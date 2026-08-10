import FormalConjectures.Util.ProblemImports

open Nat

/--
Numbers whose prime divisors all end in the same digit.
-/
def A381159_condition (n : ℕ) : Prop :=
  Finset.card (n.primeFactors.image (fun p => p % 10)) ≤ 1

/--
A381159: Numbers whose prime divisors all end in the same digit.
-/
noncomputable def A381159 (n : ℕ) : ℕ := n.nth A381159_condition

/-
A381159 51st All-Russian Mathematical Olympiad for Schoolchildren. Problem.
Let us call a natural number "lopsided" if it is greater than 1 and all its prime divisors end with the same digit.
Is there an increasing arithmetic progression with a difference not exceeding 2025,
consisting of 150 natural numbers, each of which is "lopsided"? (A. Chironov)

It turns out the answer is **no**: there is no such arithmetic progression.

Outline of the disproof.  Suppose an increasing arithmetic progression
`a, a+d, …, a+149·d` with `1 ≤ d ≤ 2025` consisted of 150 lopsided numbers.
If two primes `p ≠ q` with different last digits both fail to divide `d`, then
(since `d` is then invertible modulo `p·q`) some term `a + i·d` with
`0 ≤ i < p·q` is divisible by both `p` and `q`; if moreover `p·q ≤ 150` this index
`i` lies in `{0, …, 149}`, and that term has (at least) two prime factors with
different last digits, so it is *not* lopsided.

Hence the prime factors of `d` must form a "covering set" hitting every pair of
small different-digit primes whose product is at most `150`.  A short finite check
shows that the cheapest such covering forces `d` to be divisible by
`2·3·5·7·11 = 2310 > 2025`, which is impossible.  Concretely, for every
`d` with `1 ≤ d ≤ 2025` there is a pair of different-digit primes with product
`≤ 150`, neither dividing `d`, producing a non-lopsided term.
-/

/-- The list of "bad" prime pairs: each pair consists of two primes with
different last digits whose product is at most `150`.  For every `d` in the
range `1 … 2025` at least one of these pairs has both entries coprime to `d`. -/
def oeis_381159_pairs : List (ℕ × ℕ) :=
  [(2, 3), (2, 5), (2, 7), (2, 11), (2, 13), (2, 17), (3, 5), (3, 7), (3, 11),
   (3, 17), (5, 7), (5, 11), (5, 13), (5, 17), (7, 11), (7, 13), (11, 13)]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- For every `d` with `1 ≤ d ≤ 2025` there is a pair in `oeis_381159_pairs`
both of whose entries are coprime to `d`. -/
theorem oeis_381159_pair :
    ∀ d < 2026, 0 < d →
      ∃ pr ∈ oeis_381159_pairs, ¬ (pr.1 ∣ d) ∧ ¬ (pr.2 ∣ d) := by
  decide

/-- Every pair in `oeis_381159_pairs` consists of two primes with different
last digits whose product is at most `150`. -/
theorem oeis_381159_pairs_props :
    ∀ pr ∈ oeis_381159_pairs,
      pr.1.Prime ∧ pr.2.Prime ∧ pr.1 % 10 ≠ pr.2 % 10 ∧ pr.1 * pr.2 ≤ 150 := by
  decide

/-- If two distinct primes `p, q` are both coprime to `d`, then some term
`a + i·d` of the arithmetic progression with `i < p·q` is divisible by both
`p` and `q`. -/
theorem oeis_381159_index (a d p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpd : ¬ p ∣ d) (hqd : ¬ q ∣ d) :
    ∃ i, p ∣ (a + i * d) ∧ q ∣ (a + i * d) ∧ i < p * q := by
  have hppos : 0 < p := hp.pos
  have hqpos : 0 < q := hq.pos
  have hn : 0 < p * q := Nat.mul_pos hppos hqpos
  haveI : NeZero (p * q) := ⟨hn.ne'⟩
  have hcpd : Nat.Coprime p d := (hp.coprime_iff_not_dvd).mpr hpd
  have hcqd : Nat.Coprime q d := (hq.coprime_iff_not_dvd).mpr hqd
  have hcop : Nat.Coprime d (p * q) := (Nat.Coprime.mul_left hcpd hcqd).symm
  have hunit : IsUnit ((d : ZMod (p * q))) :=
    (ZMod.isUnit_iff_coprime d (p * q)).mpr hcop
  set D : ZMod (p * q) := (d : ZMod (p * q)) with hD
  set x : ZMod (p * q) := (-(a : ZMod (p * q))) * D⁻¹ with hx
  have hinv : D⁻¹ * D = 1 := by
    have h := ZMod.mul_inv_of_unit D hunit
    rw [mul_comm D⁻¹ D]; exact h
  have hxval : ((x.val : ℕ) : ZMod (p * q)) = x := ZMod.natCast_zmod_val x
  have hzero : ((a + x.val * d : ℕ) : ZMod (p * q)) = 0 := by
    push_cast
    rw [hxval, hx]
    rw [mul_assoc, hinv, mul_one]
    ring
  have hdvd : (p * q) ∣ (a + x.val * d) :=
    (CharP.cast_eq_zero_iff (ZMod (p * q)) (p * q) _).mp hzero
  refine ⟨x.val, ?_, ?_, ZMod.val_lt x⟩
  · exact (dvd_mul_right p q).trans hdvd
  · exact (dvd_mul_left q p).trans hdvd

/--
The disproof of the (false) positive answer: there is **no** increasing
arithmetic progression of 150 lopsided natural numbers with common difference
at most `2025`.
-/
theorem oeis_381159_conjecture_0.disproof :
    ¬ (∃ (a d : ℕ),
        2 ≤ a ∧
        1 ≤ d ∧
        d ≤ 2025 ∧
        ∀ (i : Fin 150), A381159_condition (a + i.val * d)) := by
  rintro ⟨a, d, ha, hd1, hd, hcond⟩
  obtain ⟨pr, hmem, hpd, hqd⟩ := oeis_381159_pair d (by omega) (by omega)
  obtain ⟨hp, hq, hdig, hprod⟩ := oeis_381159_pairs_props pr hmem
  obtain ⟨i, hpi, hqi, hilt⟩ := oeis_381159_index a d pr.1 pr.2 hp hq hpd hqd
  have hi150 : i < 150 := lt_of_lt_of_le hilt hprod
  set n := a + i * d with hn
  have hne0 : n ≠ 0 := by omega
  have hpm : pr.1 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpi, hne0⟩
  have hqm : pr.2 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqi, hne0⟩
  set S := n.primeFactors.image (fun p => p % 10) with hS
  have h1 : pr.1 % 10 ∈ S := Finset.mem_image_of_mem _ hpm
  have h2 : pr.2 % 10 ∈ S := Finset.mem_image_of_mem _ hqm
  have hcard : 1 < S.card :=
    Finset.one_lt_card.mpr ⟨pr.1 % 10, h1, pr.2 % 10, h2, hdig⟩
  have hc := hcond ⟨i, hi150⟩
  rw [A381159_condition] at hc
  rw [← hn, ← hS] at hc
  omega
