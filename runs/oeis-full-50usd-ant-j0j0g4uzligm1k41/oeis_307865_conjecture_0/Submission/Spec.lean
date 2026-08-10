import FormalConjectures.Util.ProblemImports

open Nat Finset ZMod

/--
A307865: $a(n)$ is the number of natural bases $b < 2n+1$ such that $b^n \equiv -1 \pmod{2n+1}$.
The bases $b$ are interpreted as $b \in \{1, 2, \dots, 2n\}$. We check the condition in the ring $\mathbb{Z}/(2n+1)\mathbb{Z}$.
-/
def a (n : ℕ) : ℕ :=
  let m : ℕ := 2 * n + 1
  -- The set of bases is $\{1, 2, \dots, 2n\} = \text{Ico } 1 m$.
  (Ico 1 m).filter (fun b : ℕ => (b : ZMod m) ^ n = (-1 : ZMod m)) |>.card

variable {n : ℕ}

/--
A natural number $m > 1$ is an absolute Euler pseudoprime if it is composite and
for all $b$ coprime to $m$, $b^{(m-1)/2} \equiv \pm 1 \pmod m$.
-/
def IsAbsoluteEulerPseudoprime (m : ℕ) : Prop :=
  m > 1 ∧ ¬ Nat.Prime m ∧
  (∀ b : ℕ, Nat.Coprime b m → (b : ZMod m) ^ ((m - 1) / 2) = 1 ∨ (b : ZMod m) ^ ((m - 1) / 2) = -1)

private lemma one_add_pow_of_sq {R : Type*} [CommRing R] (t : R) (h : t * t = 0) :
    ∀ k : ℕ, (1 + t) ^ k = 1 + (k : R) * t
  | 0 => by simp
  | (k+1) => by
      have IH := one_add_pow_of_sq t h k
      rw [pow_succ]
      push_cast
      linear_combination (1 + t) * IH + (k : R) * h

private lemma dvd_two_of {k : ℕ} (h : (-1 : ZMod k) = 1) : k ∣ 2 := by
  have h2 : ((2:ℕ) : ZMod k) = 0 := by push_cast; linear_combination -h
  exact (ZMod.natCast_eq_zero_iff 2 k).mp h2

/--
oeis_307865_conjecture_0: Conjecture: if $2n+1$ is an absolute Euler pseudoprime, then $a(n) = 0$.
Note: this conjecture trivially holds for $n=0$ since $2 \cdot 0 + 1 = 1$, which is not an absolute Euler pseudoprime.
For a meaningful statement, one usually considers $n>3$.
-/
theorem oeis_307865_conjecture_0 (h : IsAbsoluteEulerPseudoprime (2 * n + 1)) : a n = 0 := by
  obtain ⟨hm1, hnp, hcop0⟩ := h
  simp only [a]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro b hb hP
  set m := 2 * n + 1 with hm
  have hexp : (m - 1) / 2 = n := by omega
  have hcop : ∀ b : ℕ, Nat.Coprime b m → (b : ZMod m) ^ n = 1 ∨ (b : ZMod m) ^ n = -1 := by
    intro b hbc
    have := hcop0 b hbc
    rwa [hexp] at this
  have hn1 : 1 ≤ n := by omega
  have hm3 : 3 ≤ m := by omega
  haveI : NeZero m := ⟨by omega⟩
  -- pick a prime factor p of m
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  set d := m / p with hd
  have hpd_m : p * d = m := Nat.mul_div_cancel' hpm
  by_cases hsq : p * p ∣ m
  · -- p^2 ∣ m : construct an element of order p, contradiction
    have hp_dvd_d : p ∣ d := by
      have : p * p ∣ p * d := by rwa [hpd_m]
      exact (Nat.mul_dvd_mul_iff_left hp.pos).mp this
    have hcopc : Nat.Coprime (1 + d) m := by
      apply Nat.coprime_of_dvd'
      intro k hk hk1 hkm
      have hkd : k ∣ d := by
        rcases (hk.dvd_mul).mp (hpd_m ▸ hkm) with hh | hh
        · have : k = p := (Nat.prime_dvd_prime_iff_eq hk hp).mp hh
          rw [this]; exact hp_dvd_d
        · exact hh
      have := Nat.dvd_sub hk1 hkd
      simpa using this
    have htsq : (d : ZMod m) * (d : ZMod m) = 0 := by
      rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
      have := mul_dvd_mul hp_dvd_d (dvd_refl d)
      rwa [hpd_m] at this
    have hpc : ((1 + d : ℕ) : ZMod m) ^ p = 1 := by
      push_cast
      rw [one_add_pow_of_sq (d : ZMod m) htsq p]
      have hz : (p : ZMod m) * (d : ZMod m) = 0 := by
        rw [← Nat.cast_mul, hpd_m]; exact ZMod.natCast_self m
      rw [hz]; ring
    have hc2n : ((1 + d : ℕ) : ZMod m) ^ (2 * n) = 1 := by
      rw [mul_comm, pow_mul]
      rcases hcop (1 + d) hcopc with h1 | h1 <;> rw [h1] <;> ring
    have hord_p := orderOf_dvd_of_pow_eq_one hpc
    have hord_2n := orderOf_dvd_of_pow_eq_one hc2n
    have hcop_p2n : Nat.Coprime p (2 * n) := by
      rw [hp.coprime_iff_not_dvd]
      intro hdvd
      have : p ∣ 1 := by
        have := Nat.dvd_sub hpm hdvd
        simpa [hm] using this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    have hord1 : orderOf (((1 + d : ℕ) : ZMod m)) ∣ 1 := by
      have := Nat.dvd_gcd hord_p hord_2n
      rwa [hcop_p2n] at this
    have hceq1 : ((1 + d : ℕ) : ZMod m) = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord1)
    have hd0 : (d : ZMod m) = 0 := by
      push_cast at hceq1
      linear_combination hceq1
    rw [ZMod.natCast_eq_zero_iff] at hd0
    have hdpos : 0 < d := Nat.div_pos (Nat.le_of_dvd (by omega) hpm) hp.pos
    have hdlt : d < m := Nat.div_lt_self (by omega) hp.one_lt
    have := Nat.le_of_dvd hdpos hd0
    omega
  · -- p^2 ∤ m : CRT contradiction
    haveI : NeZero p := ⟨hp.pos.ne'⟩
    have hcop12 : Nat.Coprime p d := by
      rw [hp.coprime_iff_not_dvd]
      intro hpd
      exact hsq (hpd_m ▸ mul_dvd_mul_left p hpd)
    have hd_pos : 0 < d := Nat.div_pos (Nat.le_of_dvd (by omega) hpm) hp.pos
    have hd_ne1 : d ≠ 1 := by
      intro h1
      rw [h1, mul_one] at hpd_m
      exact hnp (hpd_m ▸ hp)
    have hd_gt : 1 < d := by omega
    haveI : NeZero d := ⟨by omega⟩
    have hdm : d ∣ m := ⟨p, by rw [← hpd_m]; ring⟩
    have hm_odd : ¬ (2 ∣ m) := by omega
    have hd_notdvd2 : ¬ d ∣ 2 := by
      intro hd2
      have : d ≤ 2 := Nat.le_of_dvd (by norm_num) hd2
      have : d = 2 := by omega
      rw [this] at hdm
      exact hm_odd hdm
    -- b is a unit mod m
    have hbn : (b : ZMod m) * ((b : ZMod m) ^ (n - 1)) = (b : ZMod m) ^ n := by
      rw [← _root_.pow_succ']; congr 1; omega
    have hxu : IsUnit ((b : ZMod m)) := by
      refine IsUnit.of_mul_eq_one (a := (b : ZMod m)) (-(b : ZMod m) ^ (n - 1)) ?_
      rw [mul_neg, hbn, hP]; ring
    have hbcop : Nat.Coprime b m := (ZMod.isUnit_iff_coprime b m).mp hxu
    have hbcopp : Nat.Coprime b p := Nat.Coprime.coprime_dvd_right hpm hbcop
    -- reduce hP mod p
    let fp : ZMod m →+* ZMod p := ZMod.castHom hpm (ZMod p)
    let fd : ZMod m →+* ZMod d := ZMod.castHom hdm (ZMod d)
    have hbp : (b : ZMod p) ^ n = -1 := by
      have h2 := congrArg fp hP
      simp only [map_pow, map_neg, map_one, map_natCast] at h2
      exact h2
    -- CRT construct c
    obtain ⟨c, hc1, hc2⟩ := Nat.chineseRemainder hcop12 b 1
    have hccp : Nat.Coprime c p := by
      rw [← ZMod.isUnit_iff_coprime]
      rw [(ZMod.natCast_eq_natCast_iff c b p).mpr hc1]
      exact (ZMod.isUnit_iff_coprime b p).mpr hbcopp
    have hccd : Nat.Coprime c d := by
      rw [← ZMod.isUnit_iff_coprime]
      rw [(ZMod.natCast_eq_natCast_iff c 1 d).mpr hc2]
      simp
    have hccm : Nat.Coprime c m := by
      rw [← hpd_m]
      exact Nat.Coprime.mul_right hccp hccd
    rcases hcop c hccm with hC | hC
    · -- (c)^n = 1 : reduce mod p, contradiction with hbp
      have h2 := congrArg fp hC
      simp only [map_pow, map_one, map_natCast] at h2
      rw [(ZMod.natCast_eq_natCast_iff c b p).mpr hc1, hbp] at h2
      have := dvd_two_of h2
      have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) this
      omega
    · -- (c)^n = -1 : reduce mod d, contradiction
      have h2 := congrArg fd hC
      simp only [map_pow, map_neg, map_one, map_natCast] at h2
      rw [(ZMod.natCast_eq_natCast_iff c 1 d).mpr hc2, Nat.cast_one, one_pow] at h2
      exact hd_notdvd2 (dvd_two_of h2.symm)
