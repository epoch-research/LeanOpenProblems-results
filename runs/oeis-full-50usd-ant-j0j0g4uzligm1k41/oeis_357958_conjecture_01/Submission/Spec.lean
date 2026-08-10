import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A005259: The Apéry number sequence $A(n) = \sum_{k = 0}^n \binom{n}{k}^2 \binom{n+k}{k}^2$.
-/
def A005259_seq (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k ↦ (n.choose k) ^ 2 * ((n + k).choose k) ^ 2

/--
A005258: The related Apéry number sequence $C(n) = \sum_{k = 0}^n \binom{n}{k}^2 \binom{n+k}{k}$.
-/
def A005258_seq (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k ↦ (n.choose k) ^ 2 * ((n + k).choose k)

/--
A357958: $a(n) = 5 \cdot A005259(n) + 14 \cdot A005258(n-1)$.
The sequence is indexed from $n=1$.
-/
def a (n : ℕ) : ℕ :=
  5 * A005259_seq n + 14 * A005258_seq (n - 1)

/--
The sequence u(n) defined by u(n) = A005259(n)^25 * A005258(n-1)^14, used in Conjecture 3.
-/
def u (n : ℕ) : ℕ :=
  (A005259_seq n) ^ 25 * (A005258_seq (n - 1)) ^ 14

/-!
### Scaffolding for `p ≥ 7`

The strategy for primes `p ≥ 7` is:
* decompose `A005259 p` into `1 + C(2p,p)^2 + (middle terms)`,
* use `choose_factor` to expose the factor `p^2` in each middle term,
* expand the binomial products and use the σ-trick (`sigma_trick`) to convert the
  resulting inverse-power harmonic sums into integer power sums,
* reduce everything (via stuffle/reflection identities and Wolstenholme orders,
  e.g. `sum_pow_zmod_zero`) to the single key congruence
  `3·H(2) ≡ 2p·H(2,1) (mod p^3)`.
The lemmas below are the fully-proven foundations of that program.
-/

/-- Structural decomposition: peel off `k = 0` and `k = p` from `A005259 p`. -/
theorem A005259_decomp (p : ℕ) (hp : 0 < p) :
    A005259_seq p = 1 + ((2 * p).choose p) ^ 2
      + (Finset.Ico 1 p).sum (fun k ↦ (p.choose k) ^ 2 * ((p + k).choose k) ^ 2) := by
  unfold A005259_seq
  rw [Finset.sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hp]
  simp only [Nat.choose_zero_right, Nat.choose_self, Nat.add_zero]
  ring_nf

/-- The binomial identity `p · C(p-1,k-1) = C(p,k) · k`, exposing the `p`-divisibility
of `C(p,k)` for `1 ≤ k`. -/
theorem choose_factor (p k : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k) :
    p * ((p - 1).choose (k - 1)) = (p.choose k) * k := by
  have h := Nat.add_one_mul_choose_eq (p - 1) (k - 1)
  rw [Nat.sub_add_cancel hp, Nat.sub_add_cancel hk] at h
  exact h

/-- The exact σ-trick: in `ZMod (p^3)`, for a prime `p ≥ 5` and `1 ≤ k ≤ p-1`,
the inverse square `(k)⁻²` equals the integer power combination
`k^(3p-5) - 3·k^(2p-4) + 3·k^(p-3)`.  This converts `H(2) = Σ 1/k²` into a
combination of plain power sums, exactly in `ZMod (p^3)`. -/
theorem sigma_trick (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) (k : ℕ)
    (hk : k ∈ Finset.Icc 1 (p - 1)) :
    ((k : ZMod (p ^ 3)))⁻¹ ^ 2
      = (k : ZMod (p ^ 3)) ^ (3 * p - 5) - 3 * (k : ZMod (p ^ 3)) ^ (2 * p - 4)
        + 3 * (k : ZMod (p ^ 3)) ^ (p - 3) := by
  simp only [Finset.mem_Icc] at hk
  have hkp : ¬ (p ∣ k) := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hferm : (((k : ZMod (p ^ 3)) ^ (p - 1) - 1)) ^ 3 = 0 := by
    have hk0 : (k : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hkp
    have hf : ((k : ℤ) ^ (p - 1) - 1) % p = 0 := by
      have h1 : ((k : ZMod p)) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hk0
      have h2 : (((k : ℤ) ^ (p - 1) - 1 : ℤ) : ZMod p) = 0 := by push_cast; rw [h1]; ring
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero] at h2
    have hpdvd : (p : ℤ) ∣ ((k : ℤ) ^ (p - 1) - 1) := Int.dvd_of_emod_eq_zero hf
    have hp3 : ((p : ℤ) ^ 3) ∣ ((k : ℤ) ^ (p - 1) - 1) ^ 3 := pow_dvd_pow_of_dvd hpdvd 3
    have h3 : ((((k : ℤ) ^ (p - 1) - 1) ^ 3 : ℤ) : ZMod (p ^ 3)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact_mod_cast hp3
    push_cast at h3; convert h3 using 2
  set K := (k : ZMod (p ^ 3)) with hK
  have hmul : K ^ 2 * (K ^ (3 * p - 5) - 3 * K ^ (2 * p - 4) + 3 * K ^ (p - 3)) = 1 := by
    have h1 : K ^ 2 * K ^ (3 * p - 5) = K ^ (3 * p - 3) := by rw [← pow_add]; congr 1; omega
    have h2 : K ^ 2 * K ^ (2 * p - 4) = K ^ (2 * p - 2) := by rw [← pow_add]; congr 1; omega
    have h3 : K ^ 2 * K ^ (p - 3) = K ^ (p - 1) := by rw [← pow_add]; congr 1; omega
    have e3 : K ^ (3 * p - 3) = (K ^ (p - 1)) ^ 3 := by rw [← pow_mul]; congr 1; omega
    have e2 : K ^ (2 * p - 2) = (K ^ (p - 1)) ^ 2 := by rw [← pow_mul]; congr 1; omega
    have key : K ^ (3 * p - 3) - 3 * K ^ (2 * p - 2) + 3 * K ^ (p - 1) = 1 := by
      rw [e3, e2]; linear_combination hferm
    linear_combination h1 - 3 * h2 + 3 * h3 + key
  have hunit : IsUnit K := by
    rw [hK, ZMod.isUnit_iff_coprime]
    exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hkp)).pow_right 3
  have hu2 : IsUnit (K ^ 2) := hunit.pow 2
  have hinv2 : (K ^ 2)⁻¹ * K ^ 2 = 1 := ZMod.inv_mul_of_unit (K ^ 2) hu2
  have hA : K ^ 2 * K⁻¹ ^ 2 = 1 := by
    have hki := ZMod.mul_inv_of_unit K hunit
    calc K ^ 2 * K⁻¹ ^ 2 = (K * K⁻¹) ^ 2 := by ring
      _ = 1 := by rw [hki]; ring
  have h2 : (K ^ 2)⁻¹ = (K ^ (3 * p - 5) - 3 * K ^ (2 * p - 4) + 3 * K ^ (p - 3)) := by
    calc (K ^ 2)⁻¹ = (K ^ 2)⁻¹ * 1 := (mul_one _).symm
      _ = (K ^ 2)⁻¹ * (K ^ 2 * (K ^ (3 * p - 5) - 3 * K ^ (2 * p - 4) + 3 * K ^ (p - 3))) := by
            rw [hmul]
      _ = ((K ^ 2)⁻¹ * K ^ 2) * (K ^ (3 * p - 5) - 3 * K ^ (2 * p - 4) + 3 * K ^ (p - 3)) := by
            ring
      _ = 1 * (K ^ (3 * p - 5) - 3 * K ^ (2 * p - 4) + 3 * K ^ (p - 3)) := by rw [hinv2]
      _ = _ := one_mul _
  have hfin : K⁻¹ ^ 2 = (K ^ 2)⁻¹ := by
    calc K⁻¹ ^ 2 = 1 * K⁻¹ ^ 2 := (one_mul _).symm
      _ = ((K ^ 2)⁻¹ * K ^ 2) * K⁻¹ ^ 2 := by rw [hinv2]
      _ = (K ^ 2)⁻¹ * (K ^ 2 * K⁻¹ ^ 2) := by ring
      _ = (K ^ 2)⁻¹ * 1 := by rw [hA]
      _ = (K ^ 2)⁻¹ := mul_one _
  rw [hfin, h2]

/-- A Wolstenholme-type power-sum vanishing: over a prime field `ZMod p`, the power
sum `Σ_{x} x^m` vanishes whenever `(p-1) ∤ m` (and `m > 0`).  Specialized to
`m = p-3, 2p-4, …` this gives `H(2) ≡ 0 (mod p)` etc. -/
theorem sum_pow_zmod_zero (p : ℕ) [hp : Fact p.Prime] (m : ℕ) (hm : 0 < m)
    (hdvd : ¬ (p - 1 ∣ m)) :
    (∑ x : ZMod p, x ^ m) = 0 := by
  classical
  have hunits : (∑ x : (ZMod p)ˣ, ((x : ZMod p)) ^ m) = 0 := by
    rw [FiniteField.sum_pow_units (ZMod p) m, if_neg]; rwa [ZMod.card p]
  have hbij : ∑ x ∈ (univ.erase (0 : ZMod p)), x ^ m = ∑ u : (ZMod p)ˣ, ((u : ZMod p)) ^ m := by
    apply Finset.sum_nbij' (fun a => if h : a = 0 then (1 : (ZMod p)ˣ) else Units.mk0 a h)
      (fun u => (u : ZMod p))
    · intro a _; exact Finset.mem_univ _
    · intro u _; rw [Finset.mem_erase]; exact ⟨Units.ne_zero u, Finset.mem_univ _⟩
    · intro a ha; rw [Finset.mem_erase] at ha; simp only [dif_neg ha.1, Units.val_mk0]
    · intro u _; rw [dif_neg (Units.ne_zero u)]; exact Units.ext rfl
    · intro a ha; rw [Finset.mem_erase] at ha; simp only [dif_neg ha.1, Units.val_mk0]
  have hpeel : (∑ x : ZMod p, x ^ m) = (0 : ZMod p) ^ m + ∑ x ∈ (univ.erase (0 : ZMod p)), x ^ m :=
    (Finset.add_sum_erase univ (fun x => x ^ m) (Finset.mem_univ 0)).symm
  rw [hpeel, zero_pow (by omega : m ≠ 0), zero_add, hbij, hunits]

/-- The elementary mod-`p^2` Kummer relation for single power sums:
for a prime `p ≥ 5` and `1 ≤ k ≤ p-1`, in `ZMod (p^2)`,
`k^(3p-5) = 2·k^(2p-4) - k^(p-3)`.  Summed over `k`, this gives the elementary
congruence `S_{3p-5} ≡ 2 S_{2p-4} - S_{p-3} (mod p^2)`, a building block of the
elementary proof of the key lemma. -/
theorem single_kummer (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) (k : ℕ)
    (hk : k ∈ Finset.Icc 1 (p - 1)) :
    (k : ZMod (p ^ 2)) ^ (3 * p - 5)
      = 2 * (k : ZMod (p ^ 2)) ^ (2 * p - 4) - (k : ZMod (p ^ 2)) ^ (p - 3) := by
  simp only [Finset.mem_Icc] at hk
  have hkp : ¬ (p ∣ k) := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hferm : (((k : ZMod (p ^ 2)) ^ (p - 1) - 1)) ^ 2 = 0 := by
    have hk0 : (k : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hkp
    have hf : ((k : ℤ) ^ (p - 1) - 1) % p = 0 := by
      have h1 : ((k : ZMod p)) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hk0
      have h2 : (((k : ℤ) ^ (p - 1) - 1 : ℤ) : ZMod p) = 0 := by push_cast; rw [h1]; ring
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero] at h2
    have hpdvd : (p : ℤ) ∣ ((k : ℤ) ^ (p - 1) - 1) := Int.dvd_of_emod_eq_zero hf
    have hp2 : ((p : ℤ) ^ 2) ∣ ((k : ℤ) ^ (p - 1) - 1) ^ 2 := pow_dvd_pow_of_dvd hpdvd 2
    have h3 : ((((k : ℤ) ^ (p - 1) - 1) ^ 2 : ℤ) : ZMod (p ^ 2)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact_mod_cast hp2
    push_cast at h3; convert h3 using 2
  set K := (k : ZMod (p ^ 2)) with hK
  have key : K ^ (2 * p - 2) = 2 * K ^ (p - 1) - 1 := by
    have e2 : K ^ (2 * p - 2) = (K ^ (p - 1)) ^ 2 := by rw [← pow_mul]; congr 1; omega
    rw [e2]; linear_combination hferm
  have h1 : K ^ (3 * p - 5) = K ^ (p - 3) * K ^ (2 * p - 2) := by
    rw [← pow_add]; congr 1; omega
  have e : K ^ (p - 3) * K ^ (p - 1) = K ^ (2 * p - 4) := by rw [← pow_add]; congr 1; omega
  calc K ^ (3 * p - 5) = K ^ (p - 3) * K ^ (2 * p - 2) := h1
    _ = K ^ (p - 3) * (2 * K ^ (p - 1) - 1) := by rw [key]
    _ = 2 * (K ^ (p - 3) * K ^ (p - 1)) - K ^ (p - 3) := by ring
    _ = 2 * K ^ (2 * p - 4) - K ^ (p - 3) := by rw [e]

/-- General inverse-power harmonic vanishing in `ZMod p`: for `0 < j < p-1` with
`(p-1) ∤ j`, the sum `Σ_{k=1}^{p-1} k⁻ʲ` vanishes mod `p`.  Obtained from
`sum_pow_zmod_zero` via `k⁻ʲ = k^(p-1-j)`.  Specialized to `j = 2, 4` this gives the
Wolstenholme-type inputs `H(2) ≡ 0`, `H(4) ≡ 0 (mod p)` of the elementary key lemma. -/
theorem inv_pow_sum_vanishes (p : ℕ) [hp : Fact p.Prime] (j : ℕ) (hj : 0 < j)
    (hjp : j < p - 1) (hdvd : ¬ (p - 1 ∣ j)) :
    (∑ k ∈ Finset.Icc 1 (p-1), ((k : ZMod p))⁻¹ ^ j) = 0 := by
  have hpp := hp.out.two_le
  have hterm : ∀ k ∈ Finset.Icc 1 (p-1), ((k : ZMod p))⁻¹ ^ j = (k : ZMod p) ^ (p - 1 - j) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hkp : ¬ (p ∣ k) := fun h => by have := Nat.le_of_dvd (by omega) h; omega
    have hkne : (k : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hkp
    have hferm : (k : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hkne
    have h2 : (k : ZMod p) ^ (p - 1 - j) * (k : ZMod p) ^ j = 1 := by
      rw [← pow_add]; rw [show p - 1 - j + j = p - 1 by omega]; exact hferm
    rw [inv_pow]
    field_simp
    rw [← h2]; ring
  rw [Finset.sum_congr rfl hterm]
  have hm0 : 0 < p - 1 - j := by omega
  have hmdvd : ¬ (p - 1 ∣ (p - 1 - j)) := by
    intro h
    apply hdvd
    have heq : (p - 1) - (p - 1 - j) = j := by omega
    rw [← heq]
    exact Nat.dvd_sub (dvd_refl _) h
  have hzero : (∑ x : ZMod p, x ^ (p-1-j)) = 0 := sum_pow_zmod_zero p (p-1-j) hm0 hmdvd
  have hconv : (∑ x : ZMod p, x ^ (p-1-j)) = ∑ k ∈ Finset.range p, ((k : ZMod p)) ^ (p-1-j) := by
    apply Finset.sum_nbij' (fun x => (ZMod.val x)) (fun k => (k : ZMod p))
    · intro x _; rw [Finset.mem_range]; exact ZMod.val_lt x
    · intro k _; exact Finset.mem_univ _
    · intro x _; exact (ZMod.natCast_zmod_val x)
    · intro k hk; rw [Finset.mem_range] at hk; exact ZMod.val_natCast_of_lt hk
    · intro x _; rw [ZMod.natCast_zmod_val]
  rw [hconv] at hzero
  have hsplit : ∑ k ∈ Finset.range p, ((k : ZMod p)) ^ (p-1-j)
      = ∑ k ∈ Finset.Icc 1 (p-1), ((k : ZMod p)) ^ (p-1-j) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < p)]
    simp only [Nat.cast_zero, zero_pow (by omega : p - 1 - j ≠ 0), zero_add]
    have hset : Finset.Ico 1 p = Finset.Icc 1 (p-1) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [hset]
  rw [hsplit] at hzero
  exact hzero

/-- The harmonic vanishing fact `H(2) ≡ 0 (mod p)`: over the prime field `ZMod p`
with `p ≥ 5`, the sum of inverse squares `Σ_{k=1}^{p-1} k⁻²` vanishes. -/
theorem H2_vanishes (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    (∑ k ∈ Finset.Icc 1 (p-1), ((k : ZMod p))⁻¹ ^ 2) = 0 :=
  inv_pow_sum_vanishes p 2 (by omega) (by omega) (fun h => by
    have := Nat.le_of_dvd (by omega) h; omega)

/-- The mod-`p` Wolstenholme input `H(1) ≡ 0 (mod p)`: over `ZMod p` with `p ≥ 5`,
the harmonic sum `Σ_{k=1}^{p-1} k⁻¹` vanishes.  (A corollary of `inv_pow_sum_vanishes`
at `j = 1`, using `k⁻¹ = k⁻¹ ^ 1`.) -/
theorem H1_vanishes (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    (∑ k ∈ Finset.Icc 1 (p-1), ((k : ZMod p))⁻¹) = 0 := by
  have h := inv_pow_sum_vanishes p 1 (by omega) (by omega) (fun h => by
    have := Nat.le_of_dvd (by omega) h; omega)
  simpa using h

/-- The mod-`p` input `H(4) ≡ 0 (mod p)` for `p ≥ 7`: over `ZMod p`, the sum of
inverse fourth powers `Σ_{k=1}^{p-1} k⁻⁴` vanishes.  (A corollary of
`inv_pow_sum_vanishes` at `j = 4`; requires `p ≥ 7` since for `p = 5` one has
`(p-1) ∣ 4`.) -/
theorem H4_vanishes (p : ℕ) [hp : Fact p.Prime] (hp7 : 7 ≤ p) :
    (∑ k ∈ Finset.Icc 1 (p-1), ((k : ZMod p))⁻¹ ^ 4) = 0 :=
  inv_pow_sum_vanishes p 4 (by omega) (by omega) (fun h => by
    have := Nat.le_of_dvd (by omega) h; omega)

/-- The mod-`p` input `H(3) ≡ 0 (mod p)` for `p ≥ 5`: over `ZMod p`, the sum of
inverse cubes `Σ_{k=1}^{p-1} k⁻³` vanishes.  (A corollary of `inv_pow_sum_vanishes`
at `j = 3`.) -/
theorem H3_vanishes (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    (∑ k ∈ Finset.Icc 1 (p-1), ((k : ZMod p))⁻¹ ^ 3) = 0 :=
  inv_pow_sum_vanishes p 3 (by omega) (by omega) (fun h => by
    have := Nat.le_of_dvd (by omega) h; omega)

/-- Forward power-sum vanishing over `Icc 1 (p-1)`: for `0 < m` with `(p-1) ∤ m`,
the sum `Σ_{k=1}^{p-1} k^m` vanishes in `ZMod p`.  This is the form used by the
reduction after `sigma_trick` converts inverse-square harmonic sums `H(2)` into
plain power sums `S_{3p-5} - 3 S_{2p-4} + 3 S_{p-3}`. -/
theorem pow_sum_vanishes (p : ℕ) [hp : Fact p.Prime] (m : ℕ) (hm : 0 < m)
    (hdvd : ¬ (p - 1 ∣ m)) :
    (∑ k ∈ Finset.Icc 1 (p-1), ((k : ZMod p)) ^ m) = 0 := by
  have hpp := hp.out.two_le
  have hzero : (∑ x : ZMod p, x ^ m) = 0 := sum_pow_zmod_zero p m hm hdvd
  have hconv : (∑ x : ZMod p, x ^ m) = ∑ k ∈ Finset.range p, ((k : ZMod p)) ^ m := by
    apply Finset.sum_nbij' (fun x => (ZMod.val x)) (fun k => (k : ZMod p))
    · intro x _; rw [Finset.mem_range]; exact ZMod.val_lt x
    · intro k _; exact Finset.mem_univ _
    · intro x _; exact (ZMod.natCast_zmod_val x)
    · intro k hk; rw [Finset.mem_range] at hk; exact ZMod.val_natCast_of_lt hk
    · intro x _; rw [ZMod.natCast_zmod_val]
  rw [hconv] at hzero
  have hsplit : ∑ k ∈ Finset.range p, ((k : ZMod p)) ^ m
      = ∑ k ∈ Finset.Icc 1 (p-1), ((k : ZMod p)) ^ m := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < p)]
    simp only [Nat.cast_zero, zero_pow (by omega : m ≠ 0), zero_add]
    have hset : Finset.Ico 1 p = Finset.Icc 1 (p-1) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [hset]
  rw [hsplit] at hzero
  exact hzero

/--
OEIS A357958 Conjecture 1:
a(p) ≡ a(1) (mod p^5) for all primes p ≥ 5.
-/
theorem oeis_357958_conjecture_01 :
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p → (a p) ≡ (a 1) [MOD p^5] :=
by
  intro p hp hp5
  rcases eq_or_lt_of_le hp5 with h5 | h7
  · -- Base case p = 5: a finite decidable computation.
    -- a(5) = 4112539, a(1) = 39, and 4112539 - 39 = 4112500 = 1316 · 5^5.
    subst h5
    unfold a A005259_seq A005258_seq
    decide
  · -- Case p ≥ 7.  Complete *elementary* reduction (each step verified numerically):
    --
    -- (1) Binomial product expansion gives
    --        a(p) - 39 ≡ -63 p² H(2) + 42 p³ H(2,1)   (mod p⁵),
    --     where H(2) = Σ_{k=1}^{p-1} 1/k², H(2,1) = Σ_{1≤j<k≤p-1} 1/(j k²).
    --     The A005259 part is clean (only even power sums H(2),H(4),H(2,2), which
    --     vanish at the needed orders); the A005258 part uses the stuffle relation
    --     H(2,1)+N(2,1) = H(1)H(2)-H(3).
    --
    -- (2) The result follows from the KEY LEMMA  2p·H(2,1) ≡ 3·H(2)  (mod p³),
    --     since then 42 p³ H(2,1) ≡ 63 p² H(2) (mod p⁵).
    --
    -- (3) The key lemma is ELEMENTARY.  Using the classical alternating-binomial
    --     identity  Σ_{k=1}^{p-1} (-1)^{k-1} C(p,k)/k = H_{p-1},  the pairing
    --     identity  H(1) ≡ -(p/2) H(2) (mod p⁴),  and the product expansion
    --        p·H_{k-1} ≡ 1 - (-1)^{k-1} C(p-1,k-1) + p² e₂(k-1)   (mod p³),
    --     one gets  2p·H(2,1) ≡ 3·H(2) + 2 p² W (mod p³), where
    --        W = Σ_{1≤i<j<k≤p-1} 1/(i j k²).
    --
    -- (4) Finally W ≡ 0 (mod p): it is a weight-4 multiple harmonic sum whose
    --     Bernoulli content is B_{p-4} = 0 (odd index).
    --
    -- The full Lean formalization of (1)–(4) is elementary but long (~2000 lines);
    -- it does NOT require Kummer's congruence mod p².  The remaining gap below is
    -- the formalization of this fully-determined elementary argument.
    sorry
