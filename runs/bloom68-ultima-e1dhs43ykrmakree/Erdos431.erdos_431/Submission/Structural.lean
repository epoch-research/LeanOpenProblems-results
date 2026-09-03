import FormalConjecturesUtil

/-!
# Elementary structural consequences for an eventual prime sumset

These are partial lemmas only. They do not assert that such infinite sets exist,
or that they cannot exist.
-/

open Pointwise

namespace PrimeSumsetResearch

variable {A B : Set ℕ}

/-- A finite symmetric difference with the primes is contained below a threshold. -/
theorem exists_prime_threshold
    (hfin : (symmDiff (A + B) {p : ℕ | p.Prime}).Finite) :
    ∃ N : ℕ, ∀ n : ℕ, N < n → (n ∈ A + B ↔ n.Prime) := by
  classical
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine ⟨N, ?_⟩
  intro n hn
  have hnot : n ∉ symmDiff (A + B) {p : ℕ | p.Prime} := by
    intro hmem
    exact (not_le_of_gt hn) (hN hmem)
  constructor
  · intro hmem
    by_contra hprime
    exact hnot (Set.mem_symmDiff.mpr (Or.inl ⟨hmem, hprime⟩))
  · intro hprime
    by_contra hmem
    exact hnot (Set.mem_symmDiff.mpr (Or.inr ⟨hprime, hmem⟩))

/-- Each summand has constant parity, and the two parities are opposite.
The last conjunct gives the opposite parities as a sum of residues equal to one. -/
theorem parity_structure
    (hA : A.Infinite) (hB : B.Infinite)
    (hfin : (symmDiff (A + B) {p : ℕ | p.Prime}).Finite) :
    (∀ a ∈ A, ∀ a' ∈ A, a % 2 = a' % 2) ∧
    (∀ b ∈ B, ∀ b' ∈ B, b % 2 = b' % 2) ∧
    (∀ a ∈ A, ∀ b ∈ B, a % 2 + b % 2 = 1) := by
  obtain ⟨N, hN⟩ := exists_prime_threshold hfin
  have hlarge : ∀ a ∈ A, ∀ b ∈ B, N + 2 < a + b → (a + b) % 2 = 1 := by
    intro a ha b hb hab
    have hprime : (a + b).Prime :=
      (hN (a + b) (by omega)).mp (Set.add_mem_add ha hb)
    exact hprime.eq_two_or_odd.resolve_left (by omega)
  have hleft : ∀ a ∈ A, ∀ a' ∈ A, a % 2 = a' % 2 := by
    intro a ha a' ha'
    obtain ⟨b, hb, hNb⟩ := hB.exists_gt (N + 2)
    have hab := hlarge a ha b hb (by omega)
    have ha'b := hlarge a' ha' b hb (by omega)
    omega
  have hright : ∀ b ∈ B, ∀ b' ∈ B, b % 2 = b' % 2 := by
    intro b hb b' hb'
    obtain ⟨a, ha, hNa⟩ := hA.exists_gt (N + 2)
    have hab := hlarge a ha b hb (by omega)
    have hab' := hlarge a ha b' hb' (by omega)
    omega
  refine ⟨hleft, hright, ?_⟩
  intro a ha b hb
  obtain ⟨b', hb', hNb'⟩ := hB.exists_gt (N + 2)
  have hab' := hlarge a ha b' hb' (by omega)
  have hbb' := hright b hb b' hb'
  omega

/-- Every sum is odd, not just the sums above the threshold. -/
theorem sum_mod_two_eq_one
    (hA : A.Infinite) (hB : B.Infinite)
    (hfin : (symmDiff (A + B) {p : ℕ | p.Prime}).Finite)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ B) :
    (a + b) % 2 = 1 := by
  have h := (parity_structure hA hB hfin).2.2 a ha b hb
  omega

/-- There is no even number anywhere in the sumset. -/
theorem no_even_mem_sumset
    (hA : A.Infinite) (hB : B.Infinite)
    (hfin : (symmDiff (A + B) {p : ℕ | p.Prime}).Finite)
    {n : ℕ} (hn : n ∈ A + B) : ¬Even n := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hn
  exact Nat.not_even_iff.mpr (sum_mod_two_eq_one hA hB hfin ha hb)

/-- In particular, zero cannot be a sum; this is needed before applying `le_of_dvd`. -/
theorem sum_pos
    (hA : A.Infinite) (hB : B.Infinite)
    (hfin : (symmDiff (A + B) {p : ℕ | p.Prime}).Finite)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ B) : 0 < a + b := by
  have h := sum_mod_two_eq_one hA hB hfin ha hb
  omega

/-- For any threshold as above, a prime exceeding it can divide a sum only
when the sum equals that prime. Positivity is supplied by the parity lemma. -/
theorem sum_eq_prime_of_dvd
    (hA : A.Infinite) (hB : B.Infinite)
    (hfin : (symmDiff (A + B) {p : ℕ | p.Prime}).Finite)
    {N p a b : ℕ}
    (hN : ∀ n : ℕ, N < n → (n ∈ A + B ↔ n.Prime))
    (hp : p.Prime) (hpN : N < p)
    (ha : a ∈ A) (hb : b ∈ B) (hdvd : p ∣ a + b) : a + b = p := by
  have hpos : 0 < a + b := sum_pos hA hB hfin ha hb
  have hle : p ≤ a + b := Nat.le_of_dvd hpos hdvd
  have hprime : (a + b).Prime :=
    (hN (a + b) (lt_of_lt_of_le hpN hle)).mp (Set.add_mem_add ha hb)
  exact ((Nat.prime_dvd_prime_iff_eq hp hprime).mp hdvd).symm

/-- A representation of a prime above the threshold singles out the left summand
among all elements of `A` in its residue class modulo that prime. -/
theorem left_residue_fiber_unique
    (hA : A.Infinite) (hB : B.Infinite)
    (hfin : (symmDiff (A + B) {p : ℕ | p.Prime}).Finite)
    {N p a a' b : ℕ}
    (hN : ∀ n : ℕ, N < n → (n ∈ A + B ↔ n.Prime))
    (hp : p.Prime) (hpN : N < p)
    (hb : b ∈ B) (hab : a + b = p)
    (ha' : a' ∈ A) (hmod : a' % p = a % p) : a' = a := by
  have hdvd : p ∣ a' + b := Nat.dvd_iff_mod_eq_zero.mpr <| calc
    (a' + b) % p = (a + b) % p := by
      rw [Nat.add_mod a' b p, Nat.add_mod a b p, hmod]
    _ = 0 := by rw [hab, Nat.mod_self]
  have heq := sum_eq_prime_of_dvd hA hB hfin hN hp hpN ha' hb hdvd
  omega

/-- The symmetric residue-fiber uniqueness statement for the right summand. -/
theorem right_residue_fiber_unique
    (hA : A.Infinite) (hB : B.Infinite)
    (hfin : (symmDiff (A + B) {p : ℕ | p.Prime}).Finite)
    {N p a b b' : ℕ}
    (hN : ∀ n : ℕ, N < n → (n ∈ A + B ↔ n.Prime))
    (hp : p.Prime) (hpN : N < p)
    (ha : a ∈ A) (hab : a + b = p)
    (hb' : b' ∈ B) (hmod : b' % p = b % p) : b' = b := by
  have hdvd : p ∣ a + b' := Nat.dvd_iff_mod_eq_zero.mpr <| calc
    (a + b') % p = (a + b) % p := by
      rw [Nat.add_mod a b' p, Nat.add_mod a b p, hmod]
    _ = 0 := by rw [hab, Nat.mod_self]
  have heq := sum_eq_prime_of_dvd hA hB hfin hN hp hpN ha hb' hdvd
  omega

/-- Set-theoretic singleton formulation of the left residue fiber. -/
theorem left_residue_fiber_eq_singleton
    (hA : A.Infinite) (hB : B.Infinite)
    (hfin : (symmDiff (A + B) {p : ℕ | p.Prime}).Finite)
    {N p a b : ℕ}
    (hN : ∀ n : ℕ, N < n → (n ∈ A + B ↔ n.Prime))
    (hp : p.Prime) (hpN : N < p)
    (ha : a ∈ A) (hb : b ∈ B) (hab : a + b = p) :
    {a' : ℕ | a' ∈ A ∧ a' % p = a % p} = {a} := by
  ext a'
  constructor
  · intro h
    exact Set.mem_singleton_iff.mpr
      (left_residue_fiber_unique hA hB hfin hN hp hpN hb hab h.1 h.2)
  · intro h
    obtain rfl := Set.mem_singleton_iff.mp h
    exact ⟨ha, rfl⟩

/-- Set-theoretic singleton formulation of the right residue fiber. -/
theorem right_residue_fiber_eq_singleton
    (hA : A.Infinite) (hB : B.Infinite)
    (hfin : (symmDiff (A + B) {p : ℕ | p.Prime}).Finite)
    {N p a b : ℕ}
    (hN : ∀ n : ℕ, N < n → (n ∈ A + B ↔ n.Prime))
    (hp : p.Prime) (hpN : N < p)
    (ha : a ∈ A) (hb : b ∈ B) (hab : a + b = p) :
    {b' : ℕ | b' ∈ B ∧ b' % p = b % p} = {b} := by
  ext b'
  constructor
  · intro h
    exact Set.mem_singleton_iff.mpr
      (right_residue_fiber_unique hA hB hfin hN hp hpN ha hab h.1 h.2)
  · intro h
    obtain rfl := Set.mem_singleton_iff.mp h
    exact ⟨hb, rfl⟩

/-- A prime in the right summand above the threshold cannot divide a positive
left-summand element. This uses only the eventual prime-sumset condition. -/
theorem large_prime_right_not_dvd_left
    {N p a : ℕ}
    (hN : ∀ n : ℕ, N < n → (n ∈ A + B ↔ n.Prime))
    (hp : p.Prime) (hpN : N < p)
    (hpB : p ∈ B) (ha : a ∈ A) (ha0 : 0 < a) : ¬ p ∣ a := by
  intro hdvd
  have hprime : (a + p).Prime :=
    (hN (a + p) (by omega)).mp (Set.add_mem_add ha hpB)
  have hsumdvd : p ∣ a + p := Nat.dvd_add hdvd (dvd_refl p)
  have heq : p = a + p := (Nat.prime_dvd_prime_iff_eq hp hprime).mp hsumdvd
  omega

/-- A large prime dividing a positive left-summand element has a representation
whose left endpoint is positive and strictly smaller than that prime. -/
theorem prime_divisor_has_earlier_left_representation
    {N p a : ℕ}
    (hN : ∀ n : ℕ, N < n → (n ∈ A + B ↔ n.Prime))
    (hBpos : ∀ b ∈ B, 0 < b)
    (hp : p.Prime) (hpN : N < p)
    (ha : a ∈ A) (ha0 : 0 < a) (hdvd : p ∣ a) :
    ∃ u ∈ A, ∃ b ∈ B, 0 < u ∧ u < p ∧ u + b = p := by
  have hnot : p ∉ B := by
    intro hpB
    exact large_prime_right_not_dvd_left hN hp hpN hpB ha ha0 hdvd
  obtain ⟨u, hu, b, hb, hrep⟩ := Set.mem_add.mp ((hN p hpN).mpr hp)
  have hu0 : 0 < u := by
    by_contra h
    have heq : b = p := by omega
    exact hnot (heq ▸ hb)
  have hb0 := hBpos b hb
  exact ⟨u, hu, b, hb, hu0, by omega, hrep⟩

/-- All prime factors of the least positive left-summand element are at most
the exceptional cutoff. No assertion is made about later elements. -/
theorem least_positive_left_prime_factors_le_threshold
    {N t : ℕ}
    (hN : ∀ n : ℕ, N < n → (n ∈ A + B ↔ n.Prime))
    (hBpos : ∀ b ∈ B, 0 < b)
    (ht : t ∈ A) (ht0 : 0 < t)
    (hmin : ∀ a ∈ A, 0 < a → t ≤ a)
    {p : ℕ} (hp : p.Prime) (hdvd : p ∣ t) : p ≤ N := by
  by_contra h
  have hpN : N < p := by omega
  obtain ⟨u, hu, b, hb, hu0, hup, _⟩ :=
    prime_divisor_has_earlier_left_representation hN hBpos hp hpN ht ht0 hdvd
  have hpt : p ≤ t := Nat.le_of_dvd ht0 hdvd
  have htu : t ≤ u := hmin u hu hu0
  omega

/-- If a prime `p = u + b` is represented, every positive multiple `k*p`
in the left summand imposes the additional quotient restriction
`Coprime (k+1) u`. -/
theorem prime_multiple_quotient_coprime
    {N p u b k : ℕ}
    (hN : ∀ n : ℕ, N < n → (n ∈ A + B ↔ n.Prime))
    (hp : p.Prime) (hpN : N < p)
    (hb : b ∈ B) (hu0 : 0 < u) (hb0 : 0 < b)
    (hrep : u + b = p) (hk : 0 < k) (hka : k * p ∈ A) :
    Nat.Coprime (k + 1) u := by
  have hp0 := hp.pos
  have hbig : N < k * p + b := by nlinarith
  have hprime : (k * p + b).Prime :=
    (hN (k * p + b) hbig).mp (Set.add_mem_add hka hb)
  have hdu : Nat.gcd (k + 1) u ∣ u := Nat.gcd_dvd_right (k + 1) u
  have hdk : Nat.gcd (k + 1) u ∣ k + 1 := Nat.gcd_dvd_left (k + 1) u
  have hdtotal : Nat.gcd (k + 1) u ∣ (k * p + b) + u := by
    have heq : (k * p + b) + u = (k + 1) * p := by nlinarith
    rw [heq]
    exact dvd_mul_of_dvd_left hdk p
  have hdsum : Nat.gcd (k + 1) u ∣ k * p + b :=
    (Nat.dvd_add_iff_left hdu).mpr hdtotal
  change Nat.gcd (k + 1) u = 1
  rcases (Nat.dvd_prime hprime).mp hdsum with h | h
  · exact h
  · have hle : Nat.gcd (k + 1) u ≤ u := Nat.gcd_le_right (k + 1) hu0
    nlinarith

/-- A small illustration of the quotient obstruction, not a universal trap. -/
theorem two_hundred_eighty_two_not_mem
    {N : ℕ}
    (hN : ∀ n : ℕ, N < n → (n ∈ A + B ↔ n.Prime))
    (hN47 : N < 47) (h5 : 5 ∈ B) : 282 ∉ A := by
  intro h282
  have hcop := prime_multiple_quotient_coprime
    (p := 47) (u := 42) (b := 5) (k := 6)
    hN (by norm_num) hN47 h5 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by simpa using h282)
  norm_num [Nat.Coprime] at hcop

/-- For a fixed prime modulus, one finite bound contains a larger prime in
 every nonzero residue class. The bound need not be made effective here. -/
theorem exists_prime_residue_bound {q : ℕ} (hq : q.Prime) :
    ∃ H : ℕ, ∀ r : ℕ, 0 < r → r < q →
      ∃ p : ℕ, q < p ∧ p ≤ H ∧ p.Prime ∧ p % q = r := by
  classical
  have hex : ∀ r : ℕ, ∃ p : ℕ,
      r = 0 ∨ q ≤ r ∨ (q < p ∧ p.Prime ∧ p % q = r) := by
    intro r
    by_cases hr : 0 < r ∧ r < q
    · have hcop : r.Coprime q :=
        (hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hr.1 hr.2)).symm
      obtain ⟨p, hpq, hp, hmod⟩ :=
        Nat.forall_exists_prime_gt_and_modEq q hq.ne_zero hcop
      refine ⟨p, Or.inr (Or.inr ⟨hpq, hp, ?_⟩)⟩
      simpa [Nat.ModEq, Nat.mod_eq_of_lt hr.2] using hmod
    · exact ⟨0, by omega⟩
  choose f hf using hex
  refine ⟨(Finset.range q).sup f, ?_⟩
  intro r hr hrq
  rcases hf r with hzero | hout | ⟨hlarge, hprime, hmod⟩
  · omega
  · omega
  · exact ⟨f r, hlarge, Finset.le_sup (Finset.mem_range.mpr hrq), hprime, hmod⟩

/-- A prime residue bound controls the least positive left element plus any
 lower bound on the right elements. This uses exact prime coverage. -/
theorem first_anchor_le_prime_residue_bound
    {N q H t b₀ : ℕ}
    (hN : ∀ n : ℕ, N < n → (n ∈ A + B ↔ n.Prime))
    (hBpos : ∀ b ∈ B, 0 < b)
    (hBmin : ∀ b ∈ B, b₀ ≤ b)
    (ht : t ∈ A) (ht0 : 0 < t)
    (hmin : ∀ a ∈ A, 0 < a → t ≤ a)
    (hq : q.Prime) (hqN : N < q)
    (hH : ∀ r : ℕ, 0 < r → r < q →
      ∃ p : ℕ, q < p ∧ p ≤ H ∧ p.Prime ∧ p % q = r) :
    t + b₀ ≤ H := by
  have hndvd : ¬q ∣ t := by
    intro hdvd
    have hle := least_positive_left_prime_factors_le_threshold
      hN hBpos ht ht0 hmin hq hdvd
    omega
  have hremne : t % q ≠ 0 := by
    simpa [Nat.dvd_iff_mod_eq_zero] using hndvd
  have hremlt : t % q < q := Nat.mod_lt t hq.pos
  obtain ⟨p, hpq, hpH, hp, hpmod⟩ :=
    hH (q - t % q) (by omega) (by omega)
  have hpN : N < p := by omega
  have hdvd : q ∣ t + p := by
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod, hpmod]
    have heq : t % q + (q - t % q) = q := by omega
    rw [heq, Nat.mod_self]
  have hnot : p ∉ B := by
    intro hpB
    have hsum : (t + p).Prime :=
      (hN (t + p) (by omega)).mp (Set.add_mem_add ht hpB)
    have heq : q = t + p := (Nat.prime_dvd_prime_iff_eq hq hsum).mp hdvd
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp ((hN p hpN).mpr hp)
  have ha0 : 0 < a := by
    by_contra h
    have heq : b = p := by omega
    exact hnot (heq ▸ hb)
  have hta := hmin a ha ha0
  have hbb := hBmin b hb
  omega

/-- A bound depending only on the exceptional cutoff controls the first
 positive anchor. This does not bound the depth of possible finite extensions. -/
theorem exists_uniform_first_anchor_bound (N : ℕ) :
    ∃ H : ℕ, ∀ (A B : Set ℕ) (t b₀ : ℕ),
      (∀ n : ℕ, N < n → (n ∈ A + B ↔ n.Prime)) →
      (∀ b ∈ B, 0 < b) →
      (∀ b ∈ B, b₀ ≤ b) →
      t ∈ A → 0 < t → (∀ a ∈ A, 0 < a → t ≤ a) →
      t + b₀ ≤ H := by
  obtain ⟨q, hqN, hq⟩ := Nat.exists_infinite_primes (N + 1)
  obtain ⟨H, hH⟩ := exists_prime_residue_bound hq
  refine ⟨H, ?_⟩
  intro A B t b₀ hN hBpos hBmin ht ht0 hmin
  exact first_anchor_le_prime_residue_bound hN hBpos hBmin ht ht0 hmin
    hq (by omega) hH

end PrimeSumsetResearch
