import Submission.ArithmeticReduction

/-! Avoiding distinct-support atomic boxes over Fermat-prime unit groups.
These are auxiliary obstructions, not a settlement of the odd covering problem. -/

namespace Erdos7FermatUnitAvoidance
open Finset

lemma binary_product (n : ℕ) :
    (∏ k ∈ range n, (1 + (1 / 2 : ℚ) ^ (2 ^ k))) =
      2 * (1 - (1 / 2 : ℚ) ^ (2 ^ n)) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [prod_range_succ, ih]
    simp only [pow_succ (2 : ℕ), pow_mul, pow_two]
    ring

lemma finite_binary_product_lt_two (s : Finset ℕ) :
    (∏ k ∈ s, (1 + (1 / 2 : ℚ) ^ (2 ^ k))) < 2 := by
  let N := s.sup id + 1
  have hs : s ⊆ range N := by
    intro k hk
    have h : k ≤ s.sup id := le_sup (f := id) hk
    exact mem_range.mpr (by dsimp [N]; omega)
  have heq : (∏ k ∈ s, (1 + (1 / 2 : ℚ) ^ (2 ^ k))) =
      ∏ k ∈ range N, if k ∈ s then 1 + (1 / 2 : ℚ) ^ (2 ^ k) else 1 := by
    rw [prod_ite_mem, inter_eq_right.mpr hs]
  have hle : (∏ k ∈ s, (1 + (1 / 2 : ℚ) ^ (2 ^ k))) ≤
      ∏ k ∈ range N, (1 + (1 / 2 : ℚ) ^ (2 ^ k)) := by
    rw [heq]
    apply prod_le_prod
    · intro k hk
      split_ifs <;> positivity
    · intro k hk
      split_ifs
      · exact le_rfl
      · exact le_add_of_nonneg_right (by positivity)
  rw [binary_product] at hle
  have hp : 0 < (1 / 2 : ℚ) ^ (2 ^ N) := by positivity
  linarith

lemma indexed_binary_product_lt_two {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (hn : Function.Injective n) :
    (∏ i, (1 + (1 / 2 : ℚ) ^ (2 ^ n i))) < 2 := by
  classical
  have h := finite_binary_product_lt_two (univ.image n)
  rwa [prod_image (fun _ _ _ _ h => hn h)] at h

lemma support_weight_sum_lt_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ι → ℕ) (hn : Function.Injective n) :
    (∑ S ∈ (univ : Finset ι).powerset.erase ∅,
      ∏ i ∈ S, (1 / 2 : ℚ) ^ (2 ^ n i)) < 1 := by
  classical
  have h := indexed_binary_product_lt_two n hn
  rw [prod_one_add] at h
  have he := sum_erase_add (univ : Finset ι).powerset
    (fun S => ∏ i ∈ S, (1 / 2 : ℚ) ^ (2 ^ n i)) (mem_powerset.mpr (empty_subset _))
  simp only [prod_empty] at he
  linarith

/-- Distinct nonempty supports cannot cover when each alphabet has the size
of a distinct Fermat-prime unit group. The alphabets need not carry any algebra. -/
theorem exists_avoiding_atomic_boxes {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → Type*) [∀ i, Fintype (A i)]
    (n : ι → ℕ) (hn : Function.Injective n)
    (hcard : ∀ i, Fintype.card (A i) = 2 ^ (2 ^ n i))
    (S : κ → Finset ι) (hS : Function.Injective S) (hne : ∀ k, (S k).Nonempty)
    (a : κ → ∀ i, A i) :
    ∃ x : ∀ i, A i, ∀ k, ∃ i ∈ S k, x i ≠ a k i := by
  classical
  let U : ∀ i, Finset (A i) := fun _ => univ
  let B : κ → ∀ i, Finset (A i) := fun k i => if i ∈ S k then {a k i} else univ
  have hU : ∀ i, (U i).Nonempty := by
    intro i
    rw [← card_pos, card_univ, hcard]
    positivity
  by_contra! hcover
  have hd := Erdos7Reduction.finite_product_cover_density A U hU univ B
    (by
      intro x hx
      obtain ⟨k, hk⟩ := hcover x
      refine ⟨k, mem_univ _, ?_⟩
      intro i
      by_cases hi : i ∈ S k
      · simpa [B, hi] using hk i hi
      · simp [B, hi])
  have hweight (k : κ) :
      (∏ i, (((U i ∩ B k i).card : ℚ) / (U i).card)) =
        ∏ i ∈ S k, (1 / 2 : ℚ) ^ (2 ^ n i) := by
    have hc (i : ι) : (Fintype.card (A i) : ℚ) ≠ 0 := by
      rw [hcard]
      positivity
    simp only [U, univ_inter, card_univ, B]
    have hi (i : ι) :
        (((if i ∈ S k then {a k i} else univ : Finset (A i)).card : ℚ) /
          Fintype.card (A i)) =
        if i ∈ S k then (1 / 2 : ℚ) ^ (2 ^ n i) else 1 := by
      split_ifs
      · simp [hcard]
      · simp [hc]
    simp_rw [hi]
    simp [prod_ite_mem]
  simp_rw [hweight] at hd
  have hsum : (∑ k, ∏ i ∈ S k, (1 / 2 : ℚ) ^ (2 ^ n i)) ≤
      ∑ T ∈ (univ : Finset ι).powerset.erase ∅,
        ∏ i ∈ T, (1 / 2 : ℚ) ^ (2 ^ n i) := by
    rw [← sum_image (f := fun T => ∏ i ∈ T, (1 / 2 : ℚ) ^ (2 ^ n i))
      (s := univ) (fun _ _ _ _ he => hS he)]
    apply sum_le_sum_of_subset_of_nonneg
    · intro T hT
      obtain ⟨k, _, rfl⟩ := mem_image.mp hT
      exact mem_erase.mpr ⟨(hne k).ne_empty, mem_powerset.mpr (subset_univ _)⟩
    · intros
      positivity
  exact (not_le_of_gt (support_weight_sum_lt_one n hn)) (hd.trans hsum)

/-- An odd prime with no odd factor in its unit-group cardinality is a Fermat prime. -/
lemma exists_fermat_index {p : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (ho : ordCompl[2] (p - 1) = 1) :
    ∃ n, p = Nat.fermatNumber n := by
  have hpow := Nat.ordProj_mul_ordCompl_eq_self (p - 1) 2
  rw [ho, mul_one] at hpow
  have he : (p - 1).factorization 2 ≠ 0 := by
    intro he
    simp only [he, pow_zero] at hpow
    omega
  obtain ⟨n, hn⟩ := Nat.pow_of_pow_add_prime (by decide : 1 < 2) he
    (show (2 ^ (p - 1).factorization 2 + 1).Prime by convert hp using 1; omega)
  refine ⟨n, ?_⟩
  dsimp [Nat.fermatNumber]
  rw [hn] at hpow
  omega

/-- In particular, every finite distinct-support family of atomic boxes on
Fermat-prime unit groups leaves a unit tuple uncovered. -/
theorem exists_avoiding_fermat_unit_boxes {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℕ) (hpi : Function.Injective p) (hp : ∀ i, (p i).Prime)
    (hp2 : ∀ i, 2 < p i) (ho : ∀ i, ordCompl[2] (p i - 1) = 1)
    (S : κ → Finset ι) (hS : Function.Injective S) (hne : ∀ k, (S k).Nonempty)
    (a : κ → ∀ i, (ZMod (p i))ˣ) :
    ∃ x : ∀ i, (ZMod (p i))ˣ, ∀ k, ∃ i ∈ S k, x i ≠ a k i := by
  classical
  letI (i : ι) : NeZero (p i) := ⟨(hp i).ne_zero⟩
  choose n hn using fun i => exists_fermat_index (hp i) (hp2 i) (ho i)
  have hni : Function.Injective n := by
    intro i j hij
    apply hpi
    rw [hn i, hn j, hij]
  apply exists_avoiding_atomic_boxes (fun i => (ZMod (p i))ˣ) n hni _ S hS hne a
  intro i
  rw [ZMod.card_units_eq_totient, Nat.totient_prime (hp i), hn i]
  simp [Nat.fermatNumber]

/-- CRT realizes the avoiding unit tuple as an integer. This is the arithmetic
avoidance result for squarefree products of Fermat primes. -/
theorem exists_integer_avoiding_support_products {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (p : ι → ℕ) (hpi : Function.Injective p) (hp : ∀ i, (p i).Prime)
    (hp2 : ∀ i, 2 < p i) (ho : ∀ i, ordCompl[2] (p i - 1) = 1)
    (S : κ → Finset ι) (hS : Function.Injective S) (hne : ∀ k, (S k).Nonempty)
    (a : κ → ℤ) (ha : ∀ k i, i ∈ S k → IsUnit (a k : ZMod (p i))) :
    ∃ x : ℤ, (∀ i, IsUnit (x : ZMod (p i))) ∧
      ∀ k, ¬ ((∏ i ∈ S k, p i : ℕ) : ℤ) ∣ x - a k := by
  classical
  letI (i : ι) : NeZero (p i) := ⟨(hp i).ne_zero⟩
  let u (k : κ) (i : ι) : (ZMod (p i))ˣ :=
    if h : IsUnit (a k : ZMod (p i)) then h.unit else 1
  have hu (k : κ) (i : ι) (hi : i ∈ S k) : (u k i : ZMod (p i)) = a k := by
    simp [u, ha k i hi, IsUnit.unit_spec]
  obtain ⟨y, hy⟩ := exists_avoiding_fermat_unit_boxes p hpi hp hp2 ho S hS hne u
  have hcop : ((univ : Finset ι) : Set ι).Pairwise (Function.onFun Nat.Coprime p) := by
    intro i _ j _ hij
    exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hpi h))
  let z := Nat.chineseRemainderOfFinset (fun i => (y i : ZMod (p i)).val) p univ
    (fun i _ => (hp i).ne_zero) hcop
  have hz (i : ι) : (z.val : ZMod (p i)) = (y i : ZMod (p i)) := by
    rw [← ZMod.natCast_zmod_val (y i : ZMod (p i))]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (mem_univ _))
  refine ⟨z.val, ?_, ?_⟩
  · intro i
    simpa only [Int.cast_natCast, hz] using (y i).isUnit
  · intro k hk
    obtain ⟨i, hi, hiy⟩ := hy k
    have hd : p i ∣ ∏ j ∈ S k, p j := dvd_prod_of_mem p hi
    have hdi : (p i : ℤ) ∣ (z.val : ℤ) - a k :=
      (show (p i : ℤ) ∣ ((∏ j ∈ S k, p j : ℕ) : ℤ) by exact_mod_cast hd).trans hk
    have he : (a k : ZMod (p i)) = (z.val : ZMod (p i)) := by
      simpa only [Int.cast_natCast] using
        (ZMod.intCast_eq_intCast_iff_dvd_sub (a k) (z.val : ℤ) (p i)).mpr hdi
    apply hiy
    apply Units.ext
    rw [hu k i hi, ← hz i, he]

/-- The odd part of a prime-power unit-group cardinality is trivial precisely
for a first power of a Fermat prime. -/
theorem prime_power_odd_totient_eq_one_iff {p e : ℕ} (hp : p.Prime)
    (hp2 : 2 < p) (he : 0 < e) :
    ordCompl[2] ((p ^ e).totient) = 1 ↔
      e = 1 ∧ ∃ n, p = Nat.fermatNumber n := by
  have hnp : ¬ 2 ∣ p := by
    intro h
    have := (hp.eq_one_or_self_of_dvd 2 h).resolve_left (by decide)
    omega
  have hnot : ¬ 2 ∣ p ^ (e - 1) := by
    exact fun h => hnp (Nat.prime_two.dvd_of_dvd_pow h)
  have hoc : ordCompl[2] (p ^ (e - 1)) = p ^ (e - 1) :=
    (Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ Nat.prime_two).mpr (Or.inr hnot)
  rw [Nat.totient_prime_pow hp he, Nat.ordCompl_mul, hoc]
  constructor
  · intro h
    have ha := Nat.eq_one_of_mul_eq_one_right h
    have hb := Nat.eq_one_of_mul_eq_one_left h
    have hz := (Nat.pow_eq_one.mp ha).resolve_left hp.ne_one
    exact ⟨by omega, exists_fermat_index hp hp2 hb⟩
  · rintro ⟨rfl, n, hn⟩
    simp only [Nat.sub_self, pow_zero, one_mul]
    rw [hn]
    simpa [Nat.fermatNumber] using
      (Nat.ordCompl_self_pow (k := 2 ^ n) Nat.prime_two)

#print axioms exists_avoiding_atomic_boxes
#print axioms exists_fermat_index
#print axioms exists_avoiding_fermat_unit_boxes
#print axioms exists_integer_avoiding_support_products
#print axioms prime_power_odd_totient_eq_one_iff

end Erdos7FermatUnitAvoidance
