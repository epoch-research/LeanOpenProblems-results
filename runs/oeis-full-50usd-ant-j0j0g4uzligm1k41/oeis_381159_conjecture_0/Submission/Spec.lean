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

/-!
A381159 51st All-Russian Mathematical Olympiad for Schoolchildren. Problem.
Let us call a natural number "lopsided" if it is greater than 1 and all its prime divisors end with the same digit.
Is there an increasing arithmetic progression with a difference not exceeding 2025,
consisting of 150 natural numbers, each of which is "lopsided"? (A. Chironov)

We *disprove* the formalized positive answer.

Mathematical idea of the disproof.
Suppose `a, a+d, …, a+149 d` were all "lopsided" with `1 ≤ d ≤ 2025`.
For two distinct primes `p ≠ q` with different last digits and `p * q ≤ 150`,
if neither `p` nor `q` divides `d`, then (since `d` is invertible mod `p*q`) some index
`i < p*q ≤ 150` makes `p*q ∣ a + i*d`; that term then has the two prime divisors `p, q`
with different last digits, so it is **not** lopsided.

Thus the set `{primes dividing d}` would have to be a vertex cover of the graph whose
vertices are the primes `{2,3,5,7,11,13,19}` and whose edges are pairs with distinct last
digit and product `≤ 150`.  Every vertex cover of that graph has product `≥ 2·3·5·7·11 = 2310`,
so `d ≥ 2310 > 2025`, a contradiction.  Hence no such progression exists.
-/

set_option maxRecDepth 100000

/-- The "bad pairs": distinct primes `p < q` with different last digits and `p * q ≤ 150`,
taken from the prime set `{2,3,5,7,11,13,19}`. -/
def badpairs : List (ℕ × ℕ) :=
  [(2,3),(2,5),(2,7),(2,11),(2,13),(2,19),(3,5),(3,7),(3,11),(3,19),
   (5,7),(5,11),(5,13),(5,19),(7,11),(7,13),(7,19),(11,13)]

/-- `good d` holds iff some bad pair has neither member dividing `d`. -/
def good (d : ℕ) : Bool :=
  badpairs.any (fun pq => !(d % pq.1 == 0) && !(d % pq.2 == 0))

/-- For every `1 ≤ d ≤ 2025`, some bad pair avoids `d` (checked by `decide`). -/
lemma good_all : (List.range 2025).all (fun k => good (k+1)) = true := by decide

/-- Every bad pair consists of two primes with different last digits and product `≤ 150`. -/
lemma badpairs_props : ∀ pq ∈ badpairs,
    Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 % 10 ≠ pq.2 % 10 ∧
    pq.1 * pq.2 ≤ 150 := by decide

/-- Extract, for any `1 ≤ d ≤ 2025`, an explicit bad pair neither member of which divides `d`. -/
lemma exists_pair (d : ℕ) (h1 : 1 ≤ d) (h2 : d ≤ 2025) :
    ∃ pq ∈ badpairs, ¬ pq.1 ∣ d ∧ ¬ pq.2 ∣ d := by
  have hmem : (d - 1) ∈ List.range 2025 := List.mem_range.mpr (by omega)
  have hg := (List.all_eq_true.mp good_all) (d - 1) hmem
  have hd : d - 1 + 1 = d := by omega
  rw [hd] at hg
  unfold good at hg
  obtain ⟨pq, hpqmem, hpq⟩ := List.any_eq_true.mp hg
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at hpq
  exact ⟨pq, hpqmem, by rw [Nat.dvd_iff_mod_eq_zero]; exact hpq.1,
    by rw [Nat.dvd_iff_mod_eq_zero]; exact hpq.2⟩

/-- Since `d` is invertible modulo `m`, the residue `0` is attained by `a + i*d` for some `i < m`. -/
lemma exists_i (a d m : ℕ) (hm : 0 < m) (hco : Nat.Coprime d m) :
    ∃ i, i < m ∧ m ∣ (a + i * d) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  have hu : IsUnit (d : ZMod m) := (ZMod.isUnit_iff_coprime d m).mpr hco
  refine ⟨((-(a : ZMod m)) * (d : ZMod m)⁻¹).val, ZMod.val_lt _, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id]
  rw [mul_assoc, ZMod.inv_mul_of_unit _ hu]
  ring

/--
Disproof of the conjecture: there is **no** increasing arithmetic progression with common
difference at most `2025` consisting of `150` "lopsided" natural numbers.
-/
theorem oeis_381159_conjecture_0.disproof :
  ¬ ∃ (a d : ℕ),
    2 ≤ a ∧
    1 ≤ d ∧
    d ≤ 2025 ∧
    ∀ (i : Fin 150), A381159_condition (a + i.val * d) := by
  rintro ⟨a, d, ha, hd1, hd2, hcond⟩
  obtain ⟨pq, hmem, hp1, hp2⟩ := exists_pair d hd1 hd2
  obtain ⟨hpp, hqp, hdig, hprod⟩ := badpairs_props pq hmem
  set p := pq.1
  set q := pq.2
  have hcop : Nat.Coprime d (p * q) :=
    Nat.Coprime.mul_right (hpp.coprime_iff_not_dvd.mpr hp1).symm
      (hqp.coprime_iff_not_dvd.mpr hp2).symm
  have hmpos : 0 < p * q := Nat.mul_pos hpp.pos hqp.pos
  obtain ⟨i, hilt, hdvd⟩ := exists_i a d (p * q) hmpos hcop
  have hi150 : i < 150 := lt_of_lt_of_le hilt hprod
  have htpos : 0 < a + i * d := lt_of_lt_of_le (by omega) (Nat.le_add_right a (i * d))
  have htne : a + i * d ≠ 0 := htpos.ne'
  have hpt : p ∣ (a + i * d) := (dvd_mul_right p q).trans hdvd
  have hqt : q ∣ (a + i * d) := (dvd_mul_left q p).trans hdvd
  have hpmem : p ∈ (a + i * d).primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpt, htne⟩
  have hqmem : q ∈ (a + i * d).primeFactors := Nat.mem_primeFactors.mpr ⟨hqp, hqt, htne⟩
  have hcondt := hcond ⟨i, hi150⟩
  simp only [A381159_condition] at hcondt
  have hcard : 1 < ((a + i * d).primeFactors.image (fun x => x % 10)).card := by
    rw [Finset.one_lt_card]
    exact ⟨p % 10, Finset.mem_image.mpr ⟨p, hpmem, rfl⟩, q % 10,
      Finset.mem_image.mpr ⟨q, hqmem, rfl⟩, hdig⟩
  omega
