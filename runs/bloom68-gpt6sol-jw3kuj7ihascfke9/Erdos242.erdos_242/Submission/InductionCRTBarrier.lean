import Submission.BoundedTypeIIBarrier

/-!
# A predecessor-shift obstruction for bounded Type-I cofactors

The shift `p = 4H+1`, `x = H+t` takes the full Type-I conditions for a
cofactor `c ∣ H` to Type I at the *square numerator* `1`, which is
impossible. Combining this with the existing bounded-Type-II CRT theorem
gives arbitrarily large, **soluble** hard primes for which neither branch
has a certificate with the indicated fixed small auxiliary parameter.
This does not prove or disprove ordered Erdős–Straus; `Submission.Spec` is
not imported or edited.
-/

namespace Erdos242

/-- An elementary base-case obstruction: no positive divisor `c ∣ t²` can
satisfy `4t-1 ∣ 4c+1`. Indeed its complementary divisor `s=t²/c` also
satisfies the congruence; both must be at least `t`, so both equal `t`,
when the congruence is impossible. This avoids quadratic characters. -/
theorem no_one_predecessor_typeI (t c : ℕ) (ht : 0 < t)
    (hct : c ∣ t ^ 2) (hdiv : 4 * t - 1 ∣ 4 * c + 1) : False := by
  let a := 4 * t - 1
  let s := t ^ 2 / c
  have ha : a + 1 = 4 * t := by dsimp [a]; omega
  have hcs : c * s = t ^ 2 := Nat.mul_div_cancel' hct
  have hiden : 4 * s * (4 * c + 1) = a * (a + 2) + (4 * s + 1) := by
    calc
      4 * s * (4 * c + 1) = (4 * t) ^ 2 + 4 * s := by nlinarith [hcs]
      _ = (a + 1) ^ 2 + 4 * s := by rw [ha]
      _ = a * (a + 2) + (4 * s + 1) := by ring
  have hsdiv : a ∣ 4 * s + 1 := by
    have hsum : a ∣ a * (a + 2) + (4 * s + 1) := by
      rw [← hiden]
      exact hdiv.mul_left (4 * s)
    exact (Nat.dvd_add_iff_right (dvd_mul_right a (a + 2))).mpr hsum
  have hctge : t ≤ c := by
    have hb : a ≤ 4 * c + 1 := Nat.le_of_dvd (by omega) hdiv
    dsimp [a] at hb
    omega
  have hstge : t ≤ s := by
    have hb : a ≤ 4 * s + 1 := Nat.le_of_dvd (by omega) hsdiv
    dsimp [a] at hb
    omega
  have hcle : c ≤ t := by
    by_contra h
    have hcgt : t + 1 ≤ c := by omega
    have hmul : (t + 1) * t ≤ c * s := by
      calc
        (t + 1) * t ≤ c * t := Nat.mul_le_mul_right t hcgt
        _ ≤ c * s := Nat.mul_le_mul_left c hstge
    nlinarith [hcs]
  have hc_eq : c = t := by omega
  have ha2 : 2 < a := by dsimp [a]; omega
  have htwo : a ∣ 2 := by
    have htarget : 4 * c + 1 = a + 2 := by rw [hc_eq]; dsimp [a]; omega
    rw [htarget] at hdiv
    exact (Nat.dvd_add_iff_right (dvd_refl a)).mpr hdiv
  exact (Nat.not_dvd_of_pos_of_lt (by norm_num) ha2) htwo


/-- If `p=4H+1` and `p<4x`, any full Type-I cofactor `c ∣ x²` with
`4x-p ∣ 4c+1` must **not** divide `H`. No primality assumption is used. -/
theorem typeI_cofactor_not_dvd_predecessor (H x c : ℕ)
    (hlo : 4 * H + 1 < 4 * x)
    (hcx : c ∣ x ^ 2) (hdiv : 4 * x - (4 * H + 1) ∣ 4 * c + 1) :
    ¬ c ∣ H := by
  intro hcH
  let t := x - H
  have ht : 0 < t := by dsimp [t]; omega
  have hxt : x = H + t := by dsimp [t]; omega
  have hmod : Nat.ModEq c x t := by
    change x % c = t % c
    rw [hxt]
    simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hcH]
  have hct : c ∣ t ^ 2 := by
    have hpows := hmod.pow 2
    apply Nat.dvd_of_mod_eq_zero
    calc
      t ^ 2 % c = x ^ 2 % c := hpows.symm
      _ = 0 := Nat.mod_eq_zero_of_dvd hcx
  have ha : 4 * x - (4 * H + 1) = 4 * t - 1 := by dsimp [t]; omega
  exact no_one_predecessor_typeI t c ht hct (by simpa only [ha] using hdiv)

/-- On the indicated progression, *no* Type-I cofactor at any eligible
first denominator can be at most `B`. This is a statement about every
full `c ∣ x²` certificate, not only the restricted `c ∣ x` family. -/
theorem bounded_typeI_cofactor_excluded_on_progression (B p : ℕ)
    (hrem : p % (840 * (4 * (B + 1)).factorial) = 1)
    (x c : ℕ) (hlo : p < 4 * x) (hc : 0 < c)
    (hcB : c ≤ B) (hcx : c ∣ x ^ 2) :
    ¬ (4 * x - p ∣ 4 * c + 1) := by
  intro hdiv
  let F := (4 * (B + 1)).factorial
  let k := p / (840 * F)
  have hpform : p = 4 * (210 * F * k) + 1 := by
    have hremF : p % (840 * F) = 1 := hrem
    have hform : p = (840 * F) * k + 1 := by
      calc
        p = p % (840 * F) + (840 * F) * (p / (840 * F)) :=
          (Nat.mod_add_div p (840 * F)).symm
        _ = (840 * F) * k + 1 := by rw [hremF]; simp only [k, add_comm]
    rw [hform]
    ring
  have hcF : c ∣ F := by
    dsimp [F]
    exact Nat.dvd_factorial hc (by omega)
  have hcH : c ∣ 210 * F * k := by
    exact (dvd_mul_of_dvd_right hcF 210).mul_right k
  exact typeI_cofactor_not_dvd_predecessor (210 * F * k) x c
    (by simpa only [← hpform] using hlo) hcx
    (by simpa only [← hpform] using hdiv) hcH

/-- For any fixed simultaneous budget `B`, there are arbitrarily large
**prime**, `1 mod 840` numerators that *do* have ordered solutions, yet
all Type-I cofactors `c` are `>B` (at every eligible first denominator)
and every genuine Type-II modular parameter `m=(x+d)/(4x-p)` is `>B`.
This rules out a universal bounded-budget induction/covering argument, not
a construction of a bad prime. -/
theorem good_primes_escape_both_bounded_axes (B N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ p % 840 = 1 ∧ Good p ∧
      (∀ x c : ℕ, p < 4 * x → 0 < c → c ∣ x ^ 2 →
        4 * x - p ∣ 4 * c + 1 → B < c) ∧
      (∀ x d : ℕ, p < 4 * x → 2 * x < p → 0 < d → d < x →
        d ∣ x ^ 2 → (4 * x - p) ∣ x + d →
        B < (x + d) / (4 * x - p)) := by
  obtain ⟨p, _x, hpN, hp, hrem, _hI, hgood, hnoII⟩ :=
    typeI_primes_escaping_bounded_typeII (B + 1) N
  have hrem840 : p % 840 = 1 := by
    have hL : 840 ∣ 840 * (4 * (B + 1)).factorial := dvd_mul_right _ _
    have hbig : 1 < 840 * (4 * (B + 1)).factorial := by
      have hf := Nat.factorial_pos (4 * (B + 1))
      nlinarith
    have hmod : Nat.ModEq (840 * (4 * (B + 1)).factorial) p 1 := by
      change p % (840 * (4 * (B + 1)).factorial) =
        1 % (840 * (4 * (B + 1)).factorial)
      simpa only [Nat.mod_eq_of_lt hbig] using hrem
    have h840 := Nat.ModEq.of_dvd hL hmod
    change p % 840 = 1 % 840 at h840
    simpa using h840
  refine ⟨p, hpN, hp, hrem840, hgood, ?_, ?_⟩
  · intro x c hlo hc hcx hdiv
    by_contra hnot
    have hcB : c ≤ B := by omega
    exact (bounded_typeI_cofactor_excluded_on_progression B p hrem x c hlo hc hcB hcx) hdiv
  · intro x d hlo hhi hd hdx hdsq hadiv
    obtain ⟨hm, hdm, _hh, hmod, _hx⟩ :=
      typeII_modular_parameter p x d hp hlo hhi hd hdx hdsq hadiv
    by_contra hnot
    have hle : (x + d) / (4 * x - p) ≤ B := by omega
    exact hnoII ((x + d) / (4 * x - p)) d hm (by omega) hd hdm hmod

end Erdos242

#print axioms Erdos242.no_one_predecessor_typeI
#print axioms Erdos242.typeI_cofactor_not_dvd_predecessor
#print axioms Erdos242.bounded_typeI_cofactor_excluded_on_progression
#print axioms Erdos242.good_primes_escape_both_bounded_axes
