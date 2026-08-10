import FormalConjectures.Util.ProblemImports

open Nat

/--
A002326: Multiplicative order of 2 mod 2n+1.
In other words, least $m > 0$ such that $2n+1$ divides $2^m-1$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  orderOf (2 : ZMod (2 * n + 1))

/-- Elementary fact: if `p^2 ∣ a - 1` then `p^3 ∣ a^p - 1`
(from `a^p - 1 = (∑_{i<p} a^i)(a-1)`, with `p ∣ ∑_{i<p} a^i`). -/
private theorem cube_dvd_pow_sub_one (p : ℕ) (x : ℤ) (h : (p : ℤ) ^ 2 ∣ x - 1) :
    (p : ℤ) ^ 3 ∣ x ^ p - 1 := by
  have hgeom : (∑ i ∈ Finset.range p, x ^ i) * (x - 1) = x ^ p - 1 := geom_sum_mul x p
  have hp1 : (p : ℤ) ∣ x - 1 := dvd_trans (dvd_pow_self _ (by norm_num)) h
  have hsum : (p : ℤ) ∣ ∑ i ∈ Finset.range p, x ^ i := by
    have key : (p : ℤ) ∣ (∑ i ∈ Finset.range p, x ^ i) - (p : ℤ) := by
      have hrw : (∑ i ∈ Finset.range p, x ^ i) - (p : ℤ)
          = ∑ i ∈ Finset.range p, (x ^ i - 1) := by
        rw [Finset.sum_sub_distrib]; simp
      rw [hrw]
      refine Finset.dvd_sum ?_
      intro i _
      exact dvd_trans hp1 (by simpa using sub_dvd_pow_sub_pow x 1 i)
    simpa using key.add (dvd_refl (p : ℤ))
  rw [← hgeom]
  have h3 : (p : ℤ) ^ 3 = (p : ℤ) ^ 2 * (p : ℤ) := by ring
  rw [h3, mul_comm (∑ i ∈ Finset.range p, x ^ i) (x - 1)]
  exact mul_dvd_mul h hsum

/-- Elementary fact: if `p ∣ x - 1` then `p^2 ∣ x^p - 1`. -/
private theorem sq_dvd_pow_sub_one (p : ℕ) (x : ℤ) (h : (p : ℤ) ∣ x - 1) :
    (p : ℤ) ^ 2 ∣ x ^ p - 1 := by
  have hgeom : (∑ i ∈ Finset.range p, x ^ i) * (x - 1) = x ^ p - 1 := geom_sum_mul x p
  have hsum : (p : ℤ) ∣ ∑ i ∈ Finset.range p, x ^ i := by
    have key : (p : ℤ) ∣ (∑ i ∈ Finset.range p, x ^ i) - (p : ℤ) := by
      have hrw : (∑ i ∈ Finset.range p, x ^ i) - (p : ℤ)
          = ∑ i ∈ Finset.range p, (x ^ i - 1) := by
        rw [Finset.sum_sub_distrib]; simp
      rw [hrw]
      refine Finset.dvd_sum ?_
      intro i _
      exact dvd_trans h (by simpa using sub_dvd_pow_sub_pow x 1 i)
    simpa using key.add (dvd_refl (p : ℤ))
  rw [← hgeom, pow_two]
  exact mul_dvd_mul hsum h

/-- `orderOf 2` in `ZMod (p^2)` divides `orderOf 2` in `ZMod (p^3)`
(reduction ring homomorphism). -/
private theorem orderOf_sq_dvd_cube (p : ℕ) (hp : p.Prime) :
    orderOf (2 : ZMod (p ^ 2)) ∣ orderOf (2 : ZMod (p ^ 3)) := by
  have hdvd : p ^ 2 ∣ p ^ 3 := pow_dvd_pow p (by norm_num)
  have hcast : (ZMod.castHom hdvd (ZMod (p ^ 2))) (2 : ZMod (p ^ 3)) = (2 : ZMod (p ^ 2)) := by
    rw [map_ofNat]
  have hmap := orderOf_map_dvd (ZMod.castHom hdvd (ZMod (p ^ 2))).toMonoidHom (2 : ZMod (p ^ 3))
  rwa [show ((ZMod.castHom hdvd (ZMod (p ^ 2))).toMonoidHom (2 : ZMod (p ^ 3)))
        = (2 : ZMod (p ^ 2)) from hcast] at hmap

/-- `orderOf 2` in `ZMod (p^3)` divides `p * orderOf 2` in `ZMod (p^2)`. -/
private theorem orderOf_cube_dvd (p : ℕ) (hp : p.Prime) :
    orderOf (2 : ZMod (p ^ 3)) ∣ p * orderOf (2 : ZMod (p ^ 2)) := by
  have hp2 : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hp3 : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  set m₂ := orderOf (2 : ZMod (p ^ 2)) with hm
  have hpow : (2 : ZMod (p ^ 2)) ^ m₂ = 1 := pow_orderOf_eq_one _
  have hdvd2 : (p : ℤ) ^ 2 ∣ (2 : ℤ) ^ m₂ - 1 := by
    have hz : (((2 : ℤ) ^ m₂ - 1 : ℤ) : ZMod (p ^ 2)) = 0 := by push_cast; rw [hpow]; ring
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd ((2 : ℤ) ^ m₂ - 1) (p ^ 2)).mp hz
  have hdvd3 : (p : ℤ) ^ 3 ∣ (2 : ℤ) ^ (p * m₂) - 1 := by
    have h := cube_dvd_pow_sub_one p ((2 : ℤ) ^ m₂) (by simpa using hdvd2)
    rw [← pow_mul, mul_comm m₂ p] at h
    exact h
  have hpow3 : (2 : ZMod (p ^ 3)) ^ (p * m₂) = 1 := by
    have hz : (((2 : ℤ) ^ (p * m₂) - 1 : ℤ) : ZMod (p ^ 3)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; simpa using hdvd3
    have h0 : (((2 : ℤ) ^ (p * m₂) : ℤ) : ZMod (p ^ 3)) = 1 := by
      push_cast at hz ⊢; linear_combination hz
    push_cast at h0; exact h0
  exact orderOf_dvd_of_pow_eq_one hpow3

/-- `orderOf 2` in `ZMod p` divides `orderOf 2` in `ZMod (p^2)`. -/
private theorem orderOf_p_dvd_sq (p : ℕ) (hp : p.Prime) :
    orderOf (2 : ZMod p) ∣ orderOf (2 : ZMod (p ^ 2)) := by
  have hdvd : p ∣ p ^ 2 := dvd_pow_self p (by norm_num)
  have hcast : (ZMod.castHom hdvd (ZMod p)) (2 : ZMod (p ^ 2)) = (2 : ZMod p) := by
    rw [map_ofNat]
  have hmap := orderOf_map_dvd (ZMod.castHom hdvd (ZMod p)).toMonoidHom (2 : ZMod (p ^ 2))
  rwa [show ((ZMod.castHom hdvd (ZMod p)).toMonoidHom (2 : ZMod (p ^ 2)))
        = (2 : ZMod p) from hcast] at hmap

/-- `orderOf 2` in `ZMod (p^2)` divides `p * orderOf 2` in `ZMod p`. -/
private theorem orderOf_sq_dvd_p (p : ℕ) (hp : p.Prime) :
    orderOf (2 : ZMod (p ^ 2)) ∣ p * orderOf (2 : ZMod p) := by
  have hp1 : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  set d := orderOf (2 : ZMod p) with hd
  have hpow : (2 : ZMod p) ^ d = 1 := pow_orderOf_eq_one _
  have hdvd1 : (p : ℤ) ∣ (2 : ℤ) ^ d - 1 := by
    have hz : (((2 : ℤ) ^ d - 1 : ℤ) : ZMod p) = 0 := by push_cast; rw [hpow]; ring
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd ((2 : ℤ) ^ d - 1) p).mp hz
  have hdvd2 : (p : ℤ) ^ 2 ∣ (2 : ℤ) ^ (p * d) - 1 := by
    have h := sq_dvd_pow_sub_one p ((2 : ℤ) ^ d) (by simpa using hdvd1)
    rw [← pow_mul, mul_comm d p] at h
    exact h
  have hpow2 : (2 : ZMod (p ^ 2)) ^ (p * d) = 1 := by
    have hz : (((2 : ℤ) ^ (p * d) - 1 : ℤ) : ZMod (p ^ 2)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; simpa using hdvd2
    have h0 : (((2 : ℤ) ^ (p * d) : ℤ) : ZMod (p ^ 2)) = 1 := by
      push_cast at hz ⊢; linear_combination hz
    push_cast at h0; exact h0
  exact orderOf_dvd_of_pow_eq_one hpow2

/--
THE OPEN CORE, isolated to its sharpest possible form.

The statement holds iff `p` is **not** a base-2 cube-Wieferich prime, i.e. iff
`p^3 ∤ 2^{orderOf(2 : ZMod p^2)} - 1`.

Below, the **non-Wieferich case** (`p^2 ∤ 2^{orderOf(2 : ZMod p)} - 1`) is **proven in full**
via the lifting-the-exponent lemma (`Int.emultiplicity_pow_sub_pow`): there
`orderOf(2 : ZMod p^2) = p · orderOf(2 : ZMod p)` and `v_p(2^{orderOf} - 1) = 2 < 3`.

The remaining `sorry` is *exactly* the **Wieferich case**: for a base-2 Wieferich prime
`p` (so `p^2 ∣ 2^{orderOf(2 : ZMod p)} - 1`, e.g. `1093`, `3511`, and conjecturally infinitely
many) one has `orderOf(2 : ZMod p^2) = orderOf(2 : ZMod p) =: d`, and the goal reduces to
`p^3 ∤ 2^d - 1`, equivalently `p^3 ∤ 2^{p-1} - 1`.  This is the genuinely OPEN
"no base-2 cube-Wieferich prime" problem (Wall–Sun–Sun type): no such prime is known (none
exists below the Wieferich bound `≈ 6.7·10^15`), but its non-existence is unproven and the
heuristic expected count `Σ_p 1/p^2 ≈ 0.45` does not force it to be zero. It cannot be
discharged with current mathematics.
-/
private theorem not_cube_wieferich (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) :
    (2 : ZMod (p ^ 3)) ^ orderOf (2 : ZMod (p ^ 2)) ≠ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hp3 : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  have hpge3 : 3 ≤ p := by have := hp.two_le; omega
  have hpprime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp_odd' : Odd p := hp.odd_of_ne_two hp_odd
  set d := orderOf (2 : ZMod p) with hd
  set m := orderOf (2 : ZMod (p ^ 2)) with hm
  intro hcontra
  have hp3dvd : (p : ℤ) ^ 3 ∣ (2 : ℤ) ^ m - 1 := by
    have hz : (((2 : ℤ) ^ m - 1 : ℤ) : ZMod (p ^ 3)) = 0 := by push_cast; rw [hcontra]; ring
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd ((2 : ℤ) ^ m - 1) (p ^ 3)).mp hz
  have hpd1 : (p : ℤ) ∣ (2 : ℤ) ^ d - 1 := by
    have hpow : (2 : ZMod p) ^ d = 1 := pow_orderOf_eq_one _
    have hz : (((2 : ℤ) ^ d - 1 : ℤ) : ZMod p) = 0 := by push_cast; rw [hpow]; ring
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd ((2 : ℤ) ^ d - 1) p).mp hz
  have hndvd2 : ¬ (p : ℤ) ∣ (2 : ℤ) := by
    intro hdvd
    have h1 := Int.le_of_dvd (by norm_num) hdvd
    have h2 : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hpge3
    omega
  have hndvd : ¬ (p : ℤ) ∣ (2 : ℤ) ^ d := fun h => hndvd2 (hpprime_int.dvd_of_dvd_pow h)
  have hdm : d ∣ m := orderOf_p_dvd_sq p hp
  have hmpd : m ∣ p * d := orderOf_sq_dvd_p p hp
  have hp2dvdm : (p : ℤ) ^ 2 ∣ (2 : ℤ) ^ m - 1 := by
    have hpow : (2 : ZMod (p ^ 2)) ^ m = 1 := pow_orderOf_eq_one _
    have hz : (((2 : ℤ) ^ m - 1 : ℤ) : ZMod (p ^ 2)) = 0 := by push_cast; rw [hpow]; ring
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd ((2 : ℤ) ^ m - 1) (p ^ 2)).mp hz
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have h : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hh; have := Nat.le_of_dvd (by norm_num) hh; omega
    simpa using h
  have hdpos : 0 < d := by
    rw [hd]
    apply IsOfFinOrder.orderOf_pos
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨p - 1, by omega, ZMod.pow_card_sub_one_eq_one h2ne⟩
  by_cases hw : (p : ℤ) ^ 2 ∣ (2 : ℤ) ^ d - 1
  · -- Wieferich case: reduces to `p^3 ∤ 2^d - 1`, the OPEN no-cube-Wieferich problem.
    sorry
  · -- non-Wieferich case: fully proven via lifting-the-exponent.
    have hmne : m ≠ d := by
      intro h; rw [h] at hp2dvdm; exact hw hp2dvdm
    have hm_eq : m = p * d := by
      obtain ⟨k, hk⟩ := hdm
      have hkp : k ∣ p := by
        have hmm : d * k ∣ d * p := by rw [← hk]; rwa [mul_comm p d] at hmpd
        exact (mul_dvd_mul_iff_left (by omega : d ≠ 0)).mp hmm
      rcases (hp.eq_one_or_self_of_dvd k hkp) with hk1 | hkp'
      · rw [hk1, mul_one] at hk; exact absurd hk hmne
      · rw [hk, hkp', mul_comm]
    have he1 : emultiplicity (p : ℤ) ((2 : ℤ) ^ d - 1) = 1 := by
      rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, emultiplicity_eq_coe]
      refine ⟨by simpa using hpd1, by simpa using hw⟩
    have hepp : emultiplicity p p = 1 :=
      (Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, hp.pos⟩).emultiplicity_self
    have hlte : emultiplicity (p : ℤ) ((2 : ℤ) ^ m - 1) = 2 := by
      have hkey := Int.emultiplicity_pow_sub_pow hp hp_odd' (x := (2 : ℤ) ^ d) (y := 1)
        (by simpa using hpd1) hndvd p
      rw [one_pow] at hkey
      rw [← pow_mul, show d * p = m from by rw [hm_eq]; ring] at hkey
      rw [hkey, he1, hepp]; rfl
    have hnotdvd : ¬ (p : ℤ) ^ 3 ∣ (2 : ℤ) ^ m - 1 := by
      apply not_pow_dvd_of_emultiplicity_lt
      rw [hlte]; decide
    exact hnotdvd hp3dvd

/-- Reduced identity `(★)`, fully proven modulo the single open core above. -/
private theorem orderOf_cube_eq (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) :
    orderOf (2 : ZMod (p ^ 3)) = p * orderOf (2 : ZMod (p ^ 2)) := by
  set m₂ := orderOf (2 : ZMod (p ^ 2)) with hm2
  set m₃ := orderOf (2 : ZMod (p ^ 3)) with hm3
  have hA : m₂ ∣ m₃ := orderOf_sq_dvd_cube p hp
  have hB : m₃ ∣ p * m₂ := orderOf_cube_dvd p hp
  rcases Nat.eq_zero_or_pos m₂ with h0 | hpos
  · have : m₃ = 0 := Nat.eq_zero_of_zero_dvd (h0 ▸ hA)
    rw [this, h0, Nat.mul_zero]
  · obtain ⟨k, hk⟩ := hA
    have hkp : k ∣ p := by
      have hmm : m₂ * k ∣ m₂ * p := by rw [← hk]; rwa [mul_comm p m₂] at hB
      exact (mul_dvd_mul_iff_left (by positivity)).mp hmm
    rcases (hp.eq_one_or_self_of_dvd k hkp) with hk1 | hkp'
    · exfalso
      rw [hk1, Nat.mul_one] at hk
      have hbad : (2 : ZMod (p ^ 3)) ^ m₂ = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
      exact not_cube_wieferich p hp hp_odd hbad
    · rw [hk, hkp', mul_comm]

/--
Conjecture: if $p$ is an odd prime then $a((p^3-1)/2) = p \cdot a((p^2-1)/2)$.
Because otherwise $a((p^3-1)/2) < p \cdot a((p^2-1)/2)$ iff $a((p^3-1)/2) = a((p-1)/2)$ for a prime $p$.
Equivalently $p^3$ divides $2^{p-1}-1$, but no such prime $p$ is known. - Thomas Ordowski, Feb 10 2014
-/
theorem oeis_2326_conjecture_0 (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) :
  a ((p^3 - 1) / 2) = p * a ((p^2 - 1) / 2) := by
  have hmod3 : 2 * ((p ^ 3 - 1) / 2) + 1 = p ^ 3 := by
    obtain ⟨k, hk⟩ := (hp_prime.odd_of_ne_two hp_odd).pow (n := 3); omega
  have hmod2 : 2 * ((p ^ 2 - 1) / 2) + 1 = p ^ 2 := by
    obtain ⟨k, hk⟩ := (hp_prime.odd_of_ne_two hp_odd).pow (n := 2); omega
  have e3 : a ((p ^ 3 - 1) / 2) = orderOf (2 : ZMod (p ^ 3)) := by unfold a; rw [hmod3]
  have e2 : a ((p ^ 2 - 1) / 2) = orderOf (2 : ZMod (p ^ 2)) := by unfold a; rw [hmod2]
  rw [e3, e2]
  exact orderOf_cube_eq p hp_prime hp_odd
