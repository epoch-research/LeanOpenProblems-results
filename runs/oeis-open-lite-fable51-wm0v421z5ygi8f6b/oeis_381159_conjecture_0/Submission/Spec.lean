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

/--
A381159 51st All-Russian Mathematical Olympiad for Schoolchildren. Problem.
Let us call a natural number "lopsided" if it is greater than 1 and all its prime divisors end with the same digit.
Is there an increasing arithmetic progression with a difference not exceeding 2025,
consisting of 150 natural numbers, each of which is "lopsided"? (A. Chironov)

We formalize the positive answer to the question/conjecture.
The condition for "lopsided" for n > 1 is exactly A381159_condition n.
We require the starting term a to be at least 2 to ensure all terms are > 1.
-/
theorem oeis_381159_conjecture_0 :
  ∃ (a d : ℕ),
    2 ≤ a ∧ -- The starting number 'a' must be lopsided, hence > 1. All subsequent terms will also be > 1.
    1 ≤ d ∧ -- 'd' must be positive for an increasing arithmetic progression
    d ≤ 2025 ∧ -- difference not exceeding 2025
    ∀ (i : Fin 150), A381159_condition (a + i.val * d)
  := by sorry

/-- Pairs of distinct primes with different last digits whose product is at most 150. -/
def pairList : List (ℕ × ℕ) :=
  [(2,3),(2,5),(2,7),(2,11),(2,13),(2,17),(2,19),(2,23),(2,29),(2,31),(2,37),(2,41),(2,43),(2,47),
   (2,53),(2,59),(2,61),(2,67),(2,71),(2,73),
   (3,5),(3,7),(3,11),(3,17),(3,19),(3,29),(3,31),(3,37),(3,41),(3,47),
   (5,7),(5,11),(5,13),(5,17),(5,19),(5,23),(5,29),
   (7,11),(7,13),(7,19),(11,13)]

theorem pairList_prop : ∀ pq ∈ pairList,
    pq.1.Prime ∧ pq.2.Prime ∧ pq.1 % 10 ≠ pq.2 % 10 ∧ pq.1 * pq.2 ≤ 150 := by
  decide

-- Every difference `1 ≤ d ≤ 2025` is coprime to some product `p * q` from `pairList`
-- (this is where `2025 < 2310 = 2·3·5·7·11` and `150 ≥ 143 = 11·13` matter).
set_option maxRecDepth 100000 in
theorem cover : ∀ d < 2025, ∃ pq ∈ pairList, Nat.Coprime (pq.1 * pq.2) (d + 1) := by
  decide

/-- If `m ≤ 150` is coprime to `d`, some term `a + i * d` with `i < 150` is divisible by `m`. -/
theorem exists_index (a d m : ℕ) (hm : 1 ≤ m) (hm' : m ≤ 150) (h : Nat.Coprime m d) :
    ∃ i, i < 150 ∧ m ∣ a + i * d := by
  haveI : NeZero m := ⟨by omega⟩
  have hu : Nat.Coprime d m := h.symm
  let u : (ZMod m)ˣ := ZMod.unitOfCoprime d hu
  let x : ZMod m := -(a : ZMod m) * (↑(u⁻¹) : ZMod m)
  refine ⟨x.val, lt_of_lt_of_le (ZMod.val_lt x) hm', ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [ZMod.natCast_zmod_val]
  have : ((u : (ZMod m)ˣ) : ZMod m) = (d : ZMod m) := ZMod.coe_unitOfCoprime d hu
  calc (a : ZMod m) + x * (d : ZMod m)
      = (a : ZMod m) + -(a : ZMod m) * ((↑(u⁻¹) : ZMod m) * (u : ZMod m)) := by
        rw [this]; ring
    _ = 0 := by rw [Units.inv_mul]; ring

theorem oeis_381159_conjecture_0.disproof : ¬ (type_of% @oeis_381159_conjecture_0) := by
  rintro ⟨a, d, ha, hd, hd', h⟩
  obtain ⟨⟨p, q⟩, hmem, hcop⟩ := cover (d - 1) (by omega)
  have hd1 : d - 1 + 1 = d := by omega
  rw [hd1] at hcop
  obtain ⟨hp, hq, hpq, hle⟩ := pairList_prop _ hmem
  simp only at hp hq hpq hle hcop
  have hpos : 1 ≤ p * q := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp.ne_zero hq.ne_zero)
  obtain ⟨i, hi, hdvd⟩ := exists_index a d (p * q) hpos hle hcop
  have hcond := h ⟨i, hi⟩
  simp only [A381159_condition] at hcond
  have hn : a + i * d ≠ 0 := by omega
  have hpdvd : p ∣ a + i * d := (Dvd.intro q rfl).trans hdvd
  have hqdvd : q ∣ a + i * d := (Dvd.intro_left p rfl).trans hdvd
  have hpmem : p % 10 ∈ (a + i * d).primeFactors.image (fun p => p % 10) :=
    Finset.mem_image_of_mem _ (Nat.mem_primeFactors.mpr ⟨hp, hpdvd, hn⟩)
  have hqmem : q % 10 ∈ (a + i * d).primeFactors.image (fun p => p % 10) :=
    Finset.mem_image_of_mem _ (Nat.mem_primeFactors.mpr ⟨hq, hqdvd, hn⟩)
  exact hpq (Finset.card_le_one.mp hcond _ hpmem _ hqmem)
