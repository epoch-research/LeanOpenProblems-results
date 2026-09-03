import FormalConjecturesUtil

/-! Every unfavorable affine largest-prime-factor comparison has a smaller
favorable comparison sharing a prime factor of its affine value. This supplies
edges for a proposed matching, NOT an injection or a Hall inequality. It does
not prove the density conjecture. -/

namespace Erdos371NeighborFactorMatching

abbrev P := Nat.maxPrimeFac

/-- A residue reduction for the minus affine comparison. The chosen shared
prime is the largest prime factor of the source's affine value. -/
theorem minus_favorable_predecessor {p a : ℕ} (hp : 2 ≤ p) (ha : 0 < a)
    (hbad : P (p*a-1) < P a) :
    ∃ b r : ℕ, 0 < b ∧ b < a ∧ r.Prime ∧
      r = P (p*a-1) ∧ r ∣ p*a-1 ∧ r ∣ p*b-1 ∧ P b < P (p*b-1) := by
  have ha2 : 1 < a := by
    by_contra h
    have he : a=1 := by omega
    subst a
    have hpos : 0 < P (p*1-1) :=
      Nat.pos_of_dvd_of_pos Nat.maxPrimeFac_dvd (by omega)
    change P (p*1-1) < 1 at hbad
    omega
  have hpa : 1 < p*a-1 := by
    have hh : 4 ≤ p*a := by nlinarith
    omega
  let r := P (p*a-1)
  have hr : r.Prime := Nat.prime_maxPrimeFac_of_one_lt _ hpa
  have hra : r < a := hbad.trans_le Nat.maxPrimeFac_le
  have hdiv : r ∣ p*a-1 := Nat.maxPrimeFac_dvd
  have hmod : 1 ≡ p*a [MOD r] :=
    (Nat.modEq_iff_dvd' (by nlinarith : 1 ≤ p*a)).mpr hdiv
  have hnot : ¬ r ∣ a := by
    intro hd
    have hz : p*a ≡ 0 [MOD r] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right hd p)
    exact hr.not_dvd_one (Nat.modEq_zero_iff_dvd.mp (hmod.trans hz))
  let b := a % r
  have hb : 0 < b := Nat.pos_of_ne_zero (fun h => hnot (Nat.dvd_of_mod_eq_zero h))
  have hbr : b < r := Nat.mod_lt a hr.pos
  have hpb : 0 < p*b-1 := by
    have hh : 2 ≤ p*b := by nlinarith
    omega
  have hbmod : p*b ≡ p*a [MOD r] := (Nat.mod_modEq a r).mul_left p
  have hbd : r ∣ p*b-1 :=
    (Nat.modEq_iff_dvd' (by nlinarith : 1 ≤ p*b)).mp (hmod.trans hbmod.symm)
  refine ⟨b, r, hb, hbr.trans hra, hr, rfl, hdiv, hbd, ?_⟩
  exact (Nat.maxPrimeFac_le.trans_lt hbr).trans_le (Nat.le_maxPrimeFac hpb.ne' hr hbd)

/-- The corresponding residue reduction for the plus affine comparison. -/
theorem plus_favorable_predecessor {p a : ℕ} (hp : 2 ≤ p) (ha : 0 < a)
    (hbad : P (p*a+1) < P a) :
    ∃ b r : ℕ, 0 < b ∧ b < a ∧ r.Prime ∧
      r = P (p*a+1) ∧ r ∣ p*a+1 ∧ r ∣ p*b+1 ∧ P b < P (p*b+1) := by
  have hpa : 1 < p*a+1 := by nlinarith
  let r := P (p*a+1)
  have hr : r.Prime := Nat.prime_maxPrimeFac_of_one_lt _ hpa
  have hra : r < a := hbad.trans_le Nat.maxPrimeFac_le
  have hdiv : r ∣ p*a+1 := Nat.maxPrimeFac_dvd
  have hnot : ¬ r ∣ a := by
    intro hd
    have hprod : r ∣ p*a := dvd_mul_of_dvd_right hd p
    exact hr.not_dvd_one ((Nat.dvd_add_iff_right hprod).mpr hdiv)
  let b := a % r
  have hb : 0 < b := Nat.pos_of_ne_zero (fun h => hnot (Nat.dvd_of_mod_eq_zero h))
  have hbr : b < r := Nat.mod_lt a hr.pos
  have hbmod : p*b+1 ≡ p*a+1 [MOD r] := ((Nat.mod_modEq a r).mul_left p).add_right 1
  have hbd : r ∣ p*b+1 := Nat.modEq_zero_iff_dvd.mp
    (hbmod.trans (Nat.modEq_zero_iff_dvd.mpr hdiv))
  refine ⟨b, r, hb, hbr.trans hra, hr, rfl, hdiv, hbd, ?_⟩
  exact (Nat.maxPrimeFac_le.trans_lt hbr).trans_le
    (Nat.le_maxPrimeFac (by omega) hr hbd)

/-- All residue roots obtained by allowing any prime divisor of the plus
source's affine value. These are only some of the possible favorable targets. -/
def plusRootTargets (p a : ℕ) : Finset ℕ :=
  (p*a+1).primeFactors.image (fun r => a % r)

lemma plus_sources_three_seven :
    P (5*3+1) < P 3 ∧ P (5*7+1) < P 7 := by
  decide +kernel

lemma plus_root_targets_three_seven :
    plusRootTargets 5 3 = {1} ∧ plusRootTargets 5 7 = {1} := by
  decide +kernel

/-- Even allowing every prime divisor in the residue-root construction does
not give an injective choice. This does not rule out using other favorable
inputs sharing those prime divisors. -/
theorem no_injective_plus_root_choice :
    ¬ ∃ f : ℕ → ℕ, Function.Injective f ∧
      ∀ a : ℕ, 0 < a → P (5*a+1) < P a → f a ∈ plusRootTargets 5 a := by
  rintro ⟨f, hf, hmem⟩
  have h3 := hmem 3 (by omega) plus_sources_three_seven.1
  have h7 := hmem 7 (by omega) plus_sources_three_seven.2
  rw [plus_root_targets_three_seven.1, Finset.mem_singleton] at h3
  rw [plus_root_targets_three_seven.2, Finset.mem_singleton] at h7
  have he := hf (h3.trans h7.symm)
  omega

end Erdos371NeighborFactorMatching

#print axioms Erdos371NeighborFactorMatching.minus_favorable_predecessor
#print axioms Erdos371NeighborFactorMatching.plus_favorable_predecessor

#print axioms Erdos371NeighborFactorMatching.no_injective_plus_root_choice
