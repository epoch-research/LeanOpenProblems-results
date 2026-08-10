import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A321576: $a(n)$ is the smallest $b > 1$ such that $b^n - (b-1)^n$ has all divisors $d \equiv 1 \pmod n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h_n : n > 0 then
    let S_n : Set ℕ :=
      { b | b > 1 ∧
          let k := b ^ n - (b - 1) ^ n
          ∀ (d : ℕ), d ∣ k → d ≡ 1 [MOD n] }
    -- sInf finds the smallest element of a set in a partial order, which for $\mathbb{N}$ is the minimum.
    sInf S_n
  else
    0

/-- For prime `n`, every prime dividing `2^n - 1` is `≡ 1 [MOD n]`. -/
private theorem prime_factor_dvd_two_pow_sub_one (n p : ℕ) (hn : n.Prime) (hp : p.Prime)
    (hdvd : p ∣ 2 ^ n - 1) : p ≡ 1 [MOD n] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (2 ^ n - 1) := by
    have : Even (2 ^ n) := (Nat.even_pow.mpr ⟨even_two, hn.pos.ne'⟩)
    exact Nat.Even.sub_odd Nat.one_le_two_pow this odd_one
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have hpdvd2 : ¬ (p ∣ 2) := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have h2n : (2 : ZMod p) ^ n = 1 := by
    have h0 : ((2 ^ n - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    have h1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
    push_cast [Nat.cast_sub h1] at h0
    linear_combination h0
  have hne : (2 : ZMod p) ≠ 0 := by
    have : ((2 : ℕ) : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpdvd2
    simpa using this
  have hdvdord : orderOf (2 : ZMod p) ∣ n := orderOf_dvd_of_pow_eq_one h2n
  rcases (Nat.Prime.eq_one_or_self_of_dvd hn _ hdvdord) with h1 | hn'
  · exfalso
    have h21 : (2 : ZMod p) = 1 := orderOf_eq_one_iff.mp h1
    exact one_ne_zero (by linear_combination h21 : (1 : ZMod p) = 0)
  · have hnp : n ∣ p - 1 := hn' ▸ ZMod.orderOf_dvd_card_sub_one hne
    exact ((Nat.modEq_iff_dvd' hp.one_lt.le).mpr hnp).symm

/-- For prime `n`, every divisor of `2^n - 1` is `≡ 1 [MOD n]`. -/
private theorem all_div_two_pow_sub_one (n : ℕ) (hn : n.Prime) :
    ∀ d, d ∣ 2 ^ n - 1 → d ≡ 1 [MOD n] := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IH =>
    intro hd
    rcases Nat.lt_or_ge d 2 with hlt | hge
    · interval_cases d
      · exfalso
        have h0 : 2 ^ n - 1 = 0 := Nat.eq_zero_of_zero_dvd hd
        have h2 : (2 : ℕ) ^ n ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn.pos
        omega
      · rfl
    · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
      have hpdvd : p ∣ 2 ^ n - 1 := hpd.trans hd
      have hpmod : p ≡ 1 [MOD n] := prime_factor_dvd_two_pow_sub_one n p hn hp hpdvd
      obtain ⟨e, he⟩ := hpd
      have hepos : 0 < e := by
        rcases Nat.eq_zero_or_pos e with h | h
        · simp [h] at he; omega
        · exact h
      have h2e : 2 * e ≤ d := by rw [he]; exact Nat.mul_le_mul_right e hp.two_le
      have helt : e < d := by omega
      have hed : e ∣ d := ⟨p, by rw [he]; ring⟩
      have hedvd : e ∣ 2 ^ n - 1 := hed.trans hd
      have hemod : e ≡ 1 [MOD n] := IH e helt hedvd
      calc d = p * e := he
        _ ≡ 1 * 1 [MOD n] := Nat.ModEq.mul hpmod hemod
        _ = 1 := by ring

/-- `b = 2` lies in the defining set for prime `n`. -/
private theorem two_mem_S (n : ℕ) (hn : n.Prime) :
    (2 : ℕ) ∈ { b | b > 1 ∧ let k := b ^ n - (b - 1) ^ n; ∀ (d : ℕ), d ∣ k → d ≡ 1 [MOD n] } := by
  refine ⟨by norm_num, ?_⟩
  intro k d hd
  have hk : k = 2 ^ n - 1 := by show (2 : ℕ) ^ n - (2 - 1) ^ n = 2 ^ n - 1; norm_num
  exact all_div_two_pow_sub_one n hn d (hk ▸ hd)

/--
If n is prime, then a(n) = 2. Conjecture: If n is composite, then a(n) > 2.
-/
theorem oeis_321576_conjecture_0 (n : ℕ) (hn : n > 1) :
  (n.Prime → a n = 2) ∧ (¬ n.Prime → a n > 2) := by
  refine ⟨fun hprime => ?_, fun _ => ?_⟩
  · -- Prime case: `a n = 2`.
    -- Since `2` is in the set and every element is `> 1` (hence `≥ 2`), the infimum is `2`.
    have hpos : n > 0 := by omega
    show a n = 2
    unfold a
    rw [dif_pos hpos]
    have hmem := two_mem_S n hprime
    exact le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨2, hmem⟩ (fun b hb => hb.1))
  · -- Composite case: `a n > 2`.
    -- This requires showing the defining set `S_n` is nonempty, i.e. that some `b > 1` makes
    -- `b^n - (b-1)^n` have all prime factors `≡ 1 [MOD n]`.  For all composite `n` other than
    -- `4` and `2·p`, this is a Bunyakovsky/Schinzel-type existence statement (open in number
    -- theory), so it cannot be settled with a complete proof at present.
    sorry
