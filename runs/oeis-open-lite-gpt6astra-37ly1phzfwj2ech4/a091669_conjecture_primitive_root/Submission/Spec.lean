import FormalConjectures.Util.ProblemImports

open Nat BigOperators

/--
A091669: $a(n) = \frac{2^{n-1}}{n!} \prod_{k=1}^{n-1} (2^k-1)$.
The sequence $a(n)$ is composed of natural numbers, thus we define it as a function $\mathbb{N} \to \mathbb{N}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0 -- Sequence is defined for n >= 1.
  else
    let n_pred : ℕ := n.pred

    -- The numerator of the expression. Both factors are in ℕ.
    let numerator : ℕ := (2 ^ n_pred) * (Finset.Ico 1 n).prod (fun k => 2 ^ k - 1)

    -- The denominator is $n!$.
    let denominator : ℕ := n.factorial

    -- The division is exact, since the result is an integer sequence.
    numerator / denominator

namespace A091669

def P (m : ℕ) : ℕ := ∏ k ∈ Finset.Ico 1 m, (2 ^ k - 1)
def B (m : ℕ) : ℕ := 2 ^ (m - 1) * P m

lemma P_pos (m : ℕ) : 0 < P m := by
  apply Finset.prod_pos
  intro k hk
  have hk0 : k ≠ 0 := by have := (Finset.mem_Ico.mp hk).1; omega
  exact Nat.sub_pos_of_lt (Nat.one_lt_two_pow hk0)

lemma B_pos (m : ℕ) : 0 < B m := Nat.mul_pos (by positivity) (P_pos m)

lemma prime_not_dvd_two {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : ¬ p ∣ 2 := by
  intro h
  exact h2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one)

lemma two_ne_zero {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  apply prime_not_dvd_two hp h2
  exact (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)

lemma fermat_multiple {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (j : ℕ) :
    p ∣ 2 ^ ((p - 1) * j) - 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  apply (ZMod.natCast_eq_zero_iff _ p).mp
  rw [Nat.cast_sub (Nat.one_le_pow _ _ (by decide)), Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_one, pow_mul, ZMod.pow_card_sub_one_eq_one (two_ne_zero hp h2), one_pow,
    sub_self]

/-- Each positive multiple of `p-1` contributes a factor `p`. -/
lemma prime_power_dvd_P {p m t : ℕ} (hp : p.Prime) (h2 : p ≠ 2)
    (ht : (p - 1) * t < m) : p ^ t ∣ P m := by
  let f : ℕ → ℕ := fun j => (p - 1) * (j + 1)
  have hf : Function.Injective f := by
    intro i j hij
    have hp2 := hp.two_le
    have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < p - 1) hij
    omega
  have hs : (Finset.range t).image f ⊆ Finset.Ico 1 m := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    have hjt : j + 1 ≤ t := Finset.mem_range.mp hj
    have hp0 : 0 < p - 1 := by have := hp.two_le; omega
    have hpos : 0 < f j := Nat.mul_pos hp0 (by omega)
    have hle : f j ≤ (p - 1) * t := Nat.mul_le_mul_left _ hjt
    exact Finset.mem_Ico.mpr ⟨hpos, lt_of_le_of_lt hle ht⟩
  have hd : (∏ _j ∈ Finset.range t, p) ∣
      ∏ j ∈ Finset.range t, (2 ^ (f j) - 1) :=
    Finset.prod_dvd_prod_of_dvd _ _ (fun j _ => fermat_multiple hp h2 (j + 1))
  simp only [Finset.prod_const, Finset.card_range] at hd
  apply hd.trans
  rw [← Finset.prod_image (f := fun k : ℕ => 2 ^ k - 1) hf.injOn]
  exact Finset.prod_dvd_prod_of_subset _ _ _ hs

/-- The division in the definition of the sequence is exact. -/
lemma factorial_dvd_B {m : ℕ} (hm : 0 < m) : m.factorial ∣ B m := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hk
  letI : Fact p.Prime := ⟨hp⟩
  have hkval : k ≤ padicValNat p m.factorial :=
    (padicValNat_dvd_iff_le (Nat.factorial_ne_zero m)).mp hk
  have hv := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (Nat.ne_of_gt hm)
  by_cases h2 : p = 2
  · subst p
    have hk' : k ≤ m - 1 := by simp only [Nat.reduceSub, one_mul] at hv; omega
    exact (pow_dvd_pow 2 hk').trans (dvd_mul_right _ _)
  · have ht : (p - 1) * k < m :=
      lt_of_le_of_lt (Nat.mul_le_mul_left _ hkval) hv
    exact (prime_power_dvd_P hp h2 ht).trans (dvd_mul_left _ _)

lemma a_mul_factorial {m : ℕ} (hm : 0 < m) : a m * m.factorial = B m := by
  simp only [a, Nat.ne_of_gt hm, ↓reduceDIte]
  change B m / m.factorial * m.factorial = B m
  exact Nat.div_mul_cancel (factorial_dvd_B hm)

lemma padicVal_a {p m : ℕ} [Fact p.Prime] (hm : 0 < m) :
    padicValNat p (a m) = padicValNat p (B m) - padicValNat p m.factorial := by
  simp only [a, Nat.ne_of_gt hm, ↓reduceDIte]
  exact padicValNat.div_of_dvd (factorial_dvd_B hm)

lemma factorial_valuation_bound {p n : ℕ} (hp : p.Prime) (hn : 2 < n)
    (hd : p ∣ n) (hne : p ≠ n) :
    (p - 1) * (padicValNat p (n - 1).factorial + 1) < n - 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, rfl⟩ := hd
  have hp2 := hp.two_le
  have hq : 2 ≤ q := by
    by_contra h
    have : q = 0 ∨ q = 1 := by omega
    rcases this with rfl | rfl <;> simp_all
  have heq : p * q - 1 = p * (q - 1) + (p - 1) := by
    have hq' : q - 1 + 1 = q := by omega
    have hp' : p - 1 + 1 = p := by omega
    have hn' : p * q - 1 + 1 = p * q := by omega
    nlinarith
  rw [heq, padicValNat_factorial_mul_add (q - 1) (by omega : p - 1 < p),
    padicValNat_factorial_mul]
  have hv := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p
    (by omega : q - 1 ≠ 0)
  have hp' : p - 1 + 1 = p := by omega
  nlinarith

/-- A proper odd prime divisor of `n` divides `a(n-1)`. -/
lemma proper_prime_dvd_a {p n : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hn : 2 < n)
    (hd : p ∣ n) (hne : p ≠ n) : p ∣ a (n - 1) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpow := prime_power_dvd_P hp h2 (factorial_valuation_bound hp hn hd hne)
  have hpowB : p ^ (padicValNat p (n - 1).factorial + 1) ∣ B (n - 1) :=
    hpow.trans (dvd_mul_left _ _)
  have hv := (padicValNat_dvd_iff_le (Nat.ne_of_gt (B_pos (n - 1)))).mp hpowB
  apply dvd_of_one_le_padicValNat (p := p)
  rw [padicVal_a (by omega : 0 < n - 1)]
  omega

lemma P_mod_two (m : ℕ) : (P m : ZMod 2) = 1 := by
  unfold P
  rw [Nat.cast_prod]
  apply Finset.prod_eq_one
  intro k hk
  have hk0 : k ≠ 0 := by have := (Finset.mem_Ico.mp hk).1; omega
  rw [Nat.cast_sub (Nat.one_le_pow _ _ (by decide)), Nat.cast_pow]
  rw [Nat.cast_ofNat, show (2 : ZMod 2) = 0 from rfl, zero_pow hk0, Nat.cast_one]
  decide

lemma two_not_dvd_P (m : ℕ) : ¬ 2 ∣ P m := by
  intro h
  have h0 := (ZMod.natCast_eq_zero_iff (P m) 2).mpr h
  rw [P_mod_two] at h0
  exact one_ne_zero h0

lemma factorial_two_pow_val (k : ℕ) :
    padicValNat 2 (2 ^ k).factorial = 2 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', padicValNat_factorial_mul, ih]
    have : 0 < 2 ^ k := by positivity
    omega

lemma not_condition_two_pow {n : ℕ} (hn : 2 < n) (hk : ∃ k, n = 2 ^ k) :
    ¬ n ∣ a (n - 1) + 2 ^ (n - 2) := by
  intro hd
  have hf : n * (n - 1).factorial = n.factorial := by
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
      (Nat.factorial_succ (n - 1)).symm
  have ha := a_mul_factorial (by omega : 0 < n - 1)
  have hmul : n.factorial ∣ 2 ^ (n - 2) * (P (n - 1) + (n - 1).factorial) := by
    have h := Nat.mul_dvd_mul_right hd (n - 1).factorial
    rw [hf, add_mul, ha] at h
    simpa only [B, show n - 1 - 1 = n - 2 by omega, mul_add] using h
  have hpow : 2 ^ (n - 1) ∣ n.factorial := by
    apply (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mpr
    obtain ⟨k, rfl⟩ := hk
    rw [factorial_two_pow_val]
  have h := hpow.trans hmul
  nth_rw 1 [show n - 1 = (n - 2) + 1 by omega] at h
  rw [pow_succ] at h
  have h2 := Nat.dvd_of_mul_dvd_mul_left (by positivity : 0 < 2 ^ (n - 2)) h
  have hfact : 2 ∣ (n - 1).factorial := Nat.dvd_factorial (by decide) (by omega)
  apply two_not_dvd_P (n - 1)
  exact (Nat.dvd_add_iff_left hfact).mpr h2

lemma prime_of_condition {n : ℕ} (hn : 2 < n)
    (hd : n ∣ a (n - 1) + 2 ^ (n - 2)) : n.Prime := by
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd n with hk | ⟨p, hp, hpn, hodd⟩
  · exact False.elim (not_condition_two_pow hn hk hd)
  · by_cases heq : p = n
    · exact heq ▸ hp
    have h2 : p ≠ 2 := by rintro rfl; norm_num at hodd
    have ha := proper_prime_dvd_a hp h2 hn hpn heq
    have hpow : p ∣ 2 ^ (n - 2) := (Nat.dvd_add_right ha).mp (hpn.trans hd)
    exact False.elim (prime_not_dvd_two hp h2 (hp.dvd_of_dvd_pow hpow))

lemma primitiveRoot_of_condition {n : ℕ} (hn : 2 < n) (hp : n.Prime)
    (hd : n ∣ a (n - 1) + 2 ^ (n - 2)) :
    IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) := by
  letI : Fact n.Prime := ⟨hp⟩
  have h2 : n ≠ 2 := by omega
  rw [Nat.totient_prime hp]
  apply IsPrimitiveRoot.mk_of_lt _ (by omega)
    (ZMod.pow_card_sub_one_eq_one (two_ne_zero hp h2))
  intro l hl hln hpow
  have hsub : n ∣ 2 ^ l - 1 := by
    apply (ZMod.natCast_eq_zero_iff _ n).mp
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by decide)), Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one, hpow, sub_self]
  have hP : n ∣ P (n - 1) := hsub.trans
    (Finset.dvd_prod_of_mem _ (Finset.mem_Ico.mpr ⟨hl, hln⟩))
  have hB : n ∣ B (n - 1) := hP.trans (dvd_mul_left _ _)
  rw [← a_mul_factorial (by omega : 0 < n - 1)] at hB
  have ha : n ∣ a (n - 1) :=
    (hp.coprime_factorial_of_lt (by omega : n - 1 < n)).dvd_mul_right.mp hB
  have hpow' : n ∣ 2 ^ (n - 2) := (Nat.dvd_add_right ha).mp hd
  exact prime_not_dvd_two hp h2 (hp.dvd_of_dvd_pow hpow')

end A091669

-- The formalization of the conjecture C A091669 from Jan 19 2020.
/--
Conjecture A091669: (for $n > 2$), if $n \mid a(n-1) + 2^{n-2}$, then $n$ is a prime
for which 2 is a primitive root modulo $n$ (A001122).
Note: We use `ZMod n` for the modulo ring and assume `totient` is available through `Mathlib`.
-/
theorem a091669_conjecture_primitive_root (n : ℕ) (hn : n > 2) :
  n ∣ (a (n - 1) + 2 ^ (n - 2)) →
  Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) :=
by
  intro hd
  have hp := A091669.prime_of_condition hn hd
  exact ⟨hp, A091669.primitiveRoot_of_condition hn hp hd⟩

theorem a091669_conjecture_primitive_root.disproof : ¬ (type_of% @a091669_conjecture_primitive_root) := sorry
