import Submission.PrimeCountingDyadicDiscrepancy

/-! Square displacements of linear side length do not suffice, even from a
surviving origin. This does NOT refute the two-factor product-grid premise or
the interval conjecture: the same examples have a survivor at displacement2. -/
namespace Erdos970.NonzeroSquareGrid
open Finset Filter Real

private def core (H : ℕ) : Finset ℕ := (H+1).primesBelow

private lemma core_card (H : ℕ) : (core H).card = H.primeCounting := by
  simp only [core,Nat.primesBelow,Nat.primeCounting,Nat.primeCounting',
    Nat.count_eq_card_filter_range]

private lemma core_prime (H p : ℕ) (hp : p ∈ core H) : p.Prime :=
  (Nat.mem_primesBelow.mp hp).2

private lemma zero_avoids (H p : ℕ) (hp : p ∈ core H) : ¬0 ≡ 1 [MOD p] := by
  intro h
  have he := h.eq_of_lt_of_lt (core_prime H p hp).pos (core_prime H p hp).one_lt
  omega

private lemma two_avoids (H p : ℕ) (hp : p ∈ core H) : ¬2 ≡ 1 [MOD p] := by
  intro h
  have hd : p ∣ 1 := by
    simpa using (Nat.modEq_iff_dvd' (by omega : 1 ≤ (2 : ℕ))).mp h.symm
  exact (core_prime H p hp).not_dvd_one hd

/-- Every square in the indicated range is congruent to1 modulo a selected
prime. The cases x=1 and x=2 use2 and3; otherwise use a prime divisor of x-1. -/
private lemma squares_covered (H : ℕ) (hH : 3 ≤ H) (x : ℕ)
    (hx : 0 < x) (hxH : x ≤ H) : ∃ p ∈ core H, x^2 ≡ 1 [MOD p] := by
  by_cases hx1 : x = 1
  · subst x
    exact ⟨2,Nat.mem_primesBelow.mpr ⟨by omega,Nat.prime_two⟩,by norm_num [Nat.ModEq]⟩
  by_cases hx2 : x = 2
  · subst x
    exact ⟨3,Nat.mem_primesBelow.mpr ⟨by omega,by norm_num⟩,by norm_num [Nat.ModEq]⟩
  obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd (by omega : x-1 ≠ 1)
  have hple : p ≤ x-1 := Nat.le_of_dvd (by omega) hpd
  have hpx : x ≡ 1 [MOD p] :=
    ((Nat.modEq_iff_dvd' (by omega : 1 ≤ x)).mpr hpd).symm
  refine ⟨p,Nat.mem_primesBelow.mpr ⟨by omega,hp⟩,?_⟩
  simpa using hpx.pow 2

private lemma eventually_budget (C : ℕ) :
    ∀ᶠ H : ℕ in atTop, C * H.primeCounting ≤ H := by
  have he : (0 : ℝ) < 1 / (C+1 : ℕ) := by positivity
  have hh := PrimeCountingDyadic.density_tendsto_zero.eventually (gt_mem_nhds he)
  filter_upwards [hh,eventually_ge_atTop 1] with H hH hH1
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH1
  have hc0 : (0 : ℝ) < (C+1 : ℕ) := by positivity
  have hm := (div_lt_div_iff₀ hH0 hc0).mp hH
  have hle : (C : ℝ)*(H.primeCounting : ℝ) ≤ H := by
    push_cast at hm
    nlinarith [Nat.cast_nonneg (α := ℝ) H.primeCounting]
  exact_mod_cast hle

/-- Arbitrarily large prime budgets with nonzero forbidden residues cover all
square candidates of any prescribed fixed linear side multiplier. -/
theorem arbitrarily_large_square_cover (C K : ℕ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ K ≤ P.card ∧ 0 < P.card ∧
      (∀ p ∈ P, ¬0 ≡ 1 [MOD p]) ∧
      (∀ x : ℕ, 0 < x → x ≤ C*P.card → ∃ p ∈ P, x^2 ≡ 1 [MOD p]) ∧
      (∀ p ∈ P, ¬2 ≡ 1 [MOD p]) := by
  obtain ⟨H,hbudget,hH⟩ := ((eventually_budget C).and
    (eventually_ge_atTop (max 3 (Nat.nth Nat.Prime K)))).exists
  have hH3 : 3 ≤ H := (le_max_left _ _).trans hH
  have hcount := Nat.monotone_primeCounting ((le_max_right _ _).trans hH)
  rw [PrimeCountingLower.primeCounting_nth] at hcount
  refine ⟨core H,core_prime H,?_,?_,zero_avoids H,?_,two_avoids H⟩
  · rw [core_card]
    omega
  · rw [core_card]
    omega
  · intro x hx hxc
    rw [core_card] at hxc
    exact squares_covered H hH3 x hx (hxc.trans hbudget)

/-- Realize these examples with the actual unit starting point a=-1. No CRT
approximation is needed because every forbidden residue is exactly1. -/
theorem arbitrarily_large_integer_square_obstruction (C K : ℕ) :
    ∃ k n : ℕ, K ≤ k ∧ 0 < k ∧ 0 < n ∧ n.primeFactors.card = k ∧
      (-1 : ℤ).natAbs.Coprime n ∧
      (∀ x : ℕ, 0 < x → x ≤ C*k → ¬(-1+(x^2 : ℕ) : ℤ).natAbs.Coprime n) ∧
      (-1+(2 : ℕ) : ℤ).natAbs.Coprime n := by
  obtain ⟨P,hP,hK,hk,hzero,hcover,htwo⟩ := arbitrarily_large_square_cover C K
  let n := ∏ p ∈ P, p
  have hn : 0 < n := prod_pos (fun p hp => (hP p hp).pos)
  have hc : n.primeFactors = P := Nat.primeFactors_prod hP
  refine ⟨P.card,n,hK,hk,hn,by rw [hc],by simp,?_,by simp⟩
  intro x hx hxc hcop
  obtain ⟨p,hp,hmod⟩ := hcover x hx hxc
  have hd : (p : ℤ) ∣ -1+(x^2 : ℕ) := by
    convert hmod.symm.dvd using 1
  exact Nat.not_coprime_of_dvd_of_dvd (hP p hp).one_lt
    (Int.natCast_dvd.mp hd) (dvd_prod_of_mem id hp) hcop

/-- The diagonal-square shortcut fails even after imposing the surviving-
origin hypothesis. This is NOT the negation of the interval conjecture. -/
theorem no_fixed_linear_square_companion (C : ℕ) :
    ¬∀ k : ℕ, 0 < k → ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
      ∀ a : ℤ, a.natAbs.Coprime n →
        ∃ x : ℕ, 0 < x ∧ x ≤ C*k ∧ (a+(x^2 : ℕ)).natAbs.Coprime n := by
  intro h
  obtain ⟨k,n,hK,hk,hn,hcard,ha,hbad,hgood⟩ :=
    arbitrarily_large_integer_square_obstruction C 1
  obtain ⟨x,hx,hxc,hcop⟩ := h k hk n hn hcard.le (-1) ha
  exact hbad x hx hxc hcop

#print axioms arbitrarily_large_square_cover
#print axioms arbitrarily_large_integer_square_obstruction
#print axioms no_fixed_linear_square_companion
end Erdos970.NonzeroSquareGrid
