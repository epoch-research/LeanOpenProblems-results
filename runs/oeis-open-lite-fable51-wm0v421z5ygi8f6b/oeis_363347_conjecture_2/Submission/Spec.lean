import FormalConjectures.Util.ProblemImports

open Rat Nat

/--
Helper function for A363347, which computes the denominator $R_k(n)$ of the continued fraction expression.
For $2 \le k \le n-1$, $R_k(n)$ is defined recursively:
$$R_k(n) = k - \frac{k+1}{R_{k+1}(n)}$$
The base case is $R_{n-1}(n) = (n-1) - \frac{n}{-4}$.
-/
def continued_fraction_denominator (n k : ℕ) : ℚ :=
  if n ≤ 2 then 0
  else
    -- The recursive descent involves terms from $k=n-1$ down to $k=2$.
    if 2 ≤ k ∧ k ≤ n - 1 then
      -- Base Case: k = n - 1.
      if k = n - 1 then
        -- R_{n-1} = (n-1) + n/4
        (k : ℚ) + (n : ℚ) / 4
      -- Recursive Step: 2 <= k < n - 1.
      else
        let R_next := continued_fraction_denominator n (k + 1)
        -- R_k = k - (k+1) / R_{k+1}
        (k : ℚ) - (k + 1 : ℚ) / R_next
    else 0
termination_by n - k

/--
A363347: Denominator of the continued fraction
$$\frac{1}{2 - \frac{3}{3 - \frac{4}{4 - \frac{5}{\dots - \frac{n-1}{(n-1) - \frac{n}{-4}}}}}} $$
The value of the continued fraction is $C_n = 1/R_2(n)$. If $R_2(n) = N/D$ in reduced form, $C_n = D/N$.
The sequence $a(n)$ is the denominator of the final fraction, which is $\vert N \vert$.
-/
noncomputable def A363347 (n : ℕ) : ℕ :=
  if n ≤ 2 then 0 -- The sequence is indexed starting from $n=3$.
  else
    let R2 := continued_fraction_denominator n 2
    R2.num.natAbs

namespace A363347Aux

/-- Left factorial: `G m = ∑_{i < m} i!`. -/
def G : ℕ → ℕ
  | 0 => 0
  | m + 1 => G m + m.factorial

lemma G_succ (m : ℕ) : G (m + 1) = G m + m.factorial := rfl

lemma G_mono {a b : ℕ} (h : a ≤ b) : G a ≤ G b := by
  induction b with
  | zero => simp at h; subst h; exact le_refl _
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · subst h'; exact le_refl _
    · exact le_trans (ih (by omega)) (by rw [G_succ]; omega)

lemma G_two_dvd {k : ℕ} (hk : 2 ≤ k) : 2 ∣ G k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hk with h | h
    · rw [← h]; decide
    · rw [G_succ]
      exact dvd_add (ih (by omega)) (Nat.dvd_factorial (by norm_num) (by omega))

/-- `Qf m j` is the numerator sequence: with `n = m + 3` and `M = n^2 + 2n - 4 = m^2+8m+11`. -/
noncomputable def Qf (m j : ℕ) : ℚ :=
  ((m : ℚ)^2 + 8 * m + 11) * (j * ((G (m+1) : ℚ) - G j) + (j.factorial : ℚ))
    - ((m : ℚ) + 3) * ((m+1).factorial : ℚ) * j

lemma Qf_rec (m j : ℕ) : Qf m (j + 2) = (j + 2) * (Qf m (j + 1) - Qf m j) := by
  unfold Qf
  simp only [G_succ, Nat.factorial_succ]
  push_cast
  ring

lemma Qf_pos (m : ℕ) {j : ℕ} (hj : j ≤ m + 1) : 0 < Qf m j := by
  unfold Qf
  rcases Nat.eq_or_lt_of_le hj with h | h
  · subst h
    have : (G (m+1) : ℚ) - G (m+1) = 0 := sub_self _
    rw [this]
    simp only [Nat.factorial_succ]
    push_cast
    have hf : (0:ℚ) < (m.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos m
    nlinarith
  · have hjm : j ≤ m := by omega
    have h1 : (G j : ℚ) + (m.factorial : ℚ) ≤ G (m+1) := by
      rw [G_succ]; push_cast
      have := G_mono hjm
      have : (G j : ℚ) ≤ G m := by exact_mod_cast this
      linarith
    have hf : (0:ℚ) < (m.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos m
    have hjf : (0:ℚ) < (j.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos j
    have hj0 : (0:ℚ) ≤ j := by exact_mod_cast Nat.zero_le j
    have hm0 : (0:ℚ) ≤ m := by exact_mod_cast Nat.zero_le m
    simp only [Nat.factorial_succ]
    push_cast
    set M : ℚ := (m:ℚ)^2 + 8*m + 11 with hMdef
    have hMpos : 0 < M := by positivity
    have hd : (m.factorial : ℚ) ≤ (G (m+1) : ℚ) - G j := by linarith
    have hM : M * (j * ((G (m+1) : ℚ) - G j) + (j.factorial : ℚ))
        ≥ M * (j * (m.factorial : ℚ) + (j.factorial : ℚ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have := mul_le_mul_of_nonneg_left hd hj0
      linarith
    have key : M * (j * (m.factorial : ℚ) + (j.factorial : ℚ)) - ((m:ℚ) + 3) * (((m:ℚ) + 1) * (m.factorial : ℚ)) * j
        = j * (m.factorial : ℚ) * (4 * m + 8) + M * (j.factorial : ℚ) := by
      rw [hMdef]; ring
    have t1 : 0 ≤ j * (m.factorial : ℚ) * (4 * m + 8) := by positivity
    have t2 : 0 < M * (j.factorial : ℚ) := by positivity
    linarith

theorem cfd_closed (m : ℕ) : ∀ d j, j + d = m →
    continued_fraction_denominator (m + 3) (j + 2) = (j + 2) * Qf m j / Qf m (j + 1) := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have hjm : j = m := by omega
    subst hjm
    rw [continued_fraction_denominator]
    have h1 : ¬ (j + 3 ≤ 2) := by omega
    have h2 : 2 ≤ j + 2 ∧ j + 2 ≤ j + 3 - 1 := by omega
    have h3 : j + 2 = j + 3 - 1 := by omega
    rw [if_neg h1, if_pos h2, if_pos h3]
    have hne : Qf j (j + 1) ≠ 0 := ne_of_gt (Qf_pos j (le_refl _))
    rw [eq_div_iff hne]
    unfold Qf
    simp only [G_succ, Nat.factorial_succ]
    push_cast
    ring
  | succ d ih =>
    intro j hj
    have hjm : j + 1 + d = m := by omega
    have IH := ih (j + 1) hjm
    rw [continued_fraction_denominator]
    have h1 : ¬ (m + 3 ≤ 2) := by omega
    have h2 : 2 ≤ j + 2 ∧ j + 2 ≤ m + 3 - 1 := by omega
    have h3 : ¬ (j + 2 = m + 3 - 1) := by omega
    rw [if_neg h1, if_pos h2, if_neg h3]
    have e : j + 2 + 1 = j + 1 + 2 := by ring
    rw [e, IH]
    have hp1 : 0 < Qf m (j + 1) := Qf_pos m (by omega)
    have hp2 : 0 < Qf m (j + 1 + 1) := Qf_pos m (by omega)
    have hrec := Qf_rec m j
    have e2 : j + 1 + 1 = j + 2 := by ring
    rw [e2] at hp2
    rw [e2, hrec]
    push_cast
    field_simp
    ring


lemma cfd_two (m : ℕ) : continued_fraction_denominator (m + 3) 2 =
    2 * ((m:ℚ)^2 + 8*m + 11) /
      (((m:ℚ)^2 + 8*m + 11) * (G (m+1) : ℚ) - ((m:ℚ)+3) * ((m+1).factorial : ℚ)) := by
  have := cfd_closed m m 0 (by omega)
  simp only [zero_add] at this
  rw [this]
  unfold Qf
  simp only [G, Nat.factorial_zero, Nat.factorial_one]
  push_cast
  congr 1 <;> ring

lemma A_eq (m : ℕ) : A363347 (m + 3) = (2 * ((m:ℚ)^2 + 8*m + 11) /
      (((m:ℚ)^2 + 8*m + 11) * (G (m+1) : ℚ) - ((m:ℚ)+3) * ((m+1).factorial : ℚ))).num.natAbs := by
  unfold A363347
  rw [if_neg (by omega)]
  show (continued_fraction_denominator (m+3) 2).num.natAbs = _
  rw [cfd_two]

lemma A_three : A363347 3 = 11 := by
  have := A_eq 0
  simp only [Nat.zero_add] at this
  rw [this]
  have e : (2 * ((0:ℕ):ℚ)^2 + 8*((0:ℕ):ℚ) + 11) = 11 := by norm_num
  have h : (2 * (((0:ℕ):ℚ)^2 + 8*((0:ℕ):ℚ) + 11) /
      ((((0:ℕ):ℚ)^2 + 8*((0:ℕ):ℚ) + 11) * (G (0+1) : ℚ) - (((0:ℕ):ℚ)+3) * ((0+1).factorial : ℚ)))
      = ((11:ℤ):ℚ) / ((4:ℤ):ℚ) := by
    simp [G]; norm_num
  rw [h, Rat.num_div_eq_of_coprime (by norm_num) (by decide)]
  rfl

/-- Any square root of 5 mod a prime `p ≥ 19` has value at least 6. -/
lemma sqrt5_val_ge (p : ℕ) [Fact p.Prime] (hp19 : 19 ≤ p) (z : ZMod p)
    (hz : ((5:ℕ) : ZMod p) = z * z) : 6 ≤ z.val := by
  by_contra hlt
  push_neg at hlt
  set r := z.val with hr
  have hzr : ((r : ℕ) : ZMod p) = z := ZMod.natCast_zmod_val z
  have h1 : ((5:ℕ) : ZMod p) = ((r * r : ℕ) : ZMod p) := by
    rw [hz, ← hzr]; push_cast; ring
  have h2 : 5 ≡ r * r [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ _).mp h1
  have h3 := Nat.ModEq.dvd h2
  have hp : p ≠ 0 := by omega
  have hpp : p.Prime := Fact.out
  interval_cases r <;> norm_num at h3
  all_goals
    have h4 := Int.le_of_dvd (by norm_num) h3
    first
      | omega
      | (have hp20 : p = 19 ∨ p = 20 := by omega
         rcases hp20 with hp20 | hp20
         · subst hp20; push_cast at h3
         · subst hp20; norm_num at hpp)


lemma core (p : ℕ) [Fact p.Prime] (hp19 : 19 ≤ p) (z : ZMod p)
    (hz : ((5:ℕ) : ZMod p) = z * z) (hev : Even z.val) : ∃ n, A363347 n = p := by
  have hpp : p.Prime := Fact.out
  set r := z.val with hr
  have hr6 : 6 ≤ r := sqrt5_val_ge p hp19 z hz
  have hz0 : z ≠ 0 := by
    intro h; rw [h, ZMod.val_zero] at hr; omega
  have hneg : 6 ≤ (-z).val := sqrt5_val_ge p hp19 (-z) (by rw [hz]; ring)
  rw [ZMod.neg_val, if_neg hz0] at hneg
  have hrp : r < p := ZMod.val_lt z
  have hrp6 : r + 6 ≤ p := by omega
  have hzr : ((r : ℕ) : ZMod p) = z := ZMod.natCast_zmod_val z
  have h1 : ((5:ℕ) : ZMod p) = ((r * r : ℕ) : ZMod p) := by
    rw [hz, ← hzr]; push_cast; ring
  have h2 : 5 ≡ r * r [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ _).mp h1
  have h3 : p ∣ r * r - 5 := (Nat.modEq_iff_dvd' (by nlinarith)).mp h2
  obtain ⟨c, hc⟩ := h3
  obtain ⟨m, hm⟩ : ∃ m, r = m + 4 := ⟨r - 4, by omega⟩
  have hM : m^2 + 8*m + 11 = p * c := by
    have : r * r = m^2 + 8*m + 16 := by rw [hm]; ring
    omega
  have hm2 : 2 ≤ m := by omega
  have hpm : m + 10 ≤ p := by omega
  have hmeven : Even m := by
    rw [hm] at hev
    have := Nat.even_iff.mp hev
    exact Nat.even_iff.mpr (by omega)
  have hodd : Odd (m^2 + 8*m + 11) := by
    obtain ⟨t, ht⟩ := hmeven
    exact ⟨2*t^2 + 8*t + 5, by rw [ht]; ring⟩
  have hc_odd : Odd c := (Nat.odd_mul.mp (hM ▸ hodd)).2
  have hc_pos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · exfalso; rw [h, Nat.mul_zero] at hM; omega
    · exact h
  have hcm : c ≤ m := by
    by_contra h
    push_neg at h
    have := Nat.mul_le_mul hpm h
    nlinarith
  obtain ⟨A, hA⟩ : 2 ∣ G (m+1) := G_two_dvd (by omega)
  have h2c : 2 * c ∣ m.factorial :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_two_left.mpr hc_odd)
      (Nat.dvd_factorial (by norm_num) hm2) (Nat.dvd_factorial hc_pos hcm)
  have h2c' : 2 * c ∣ (m + 3) * (m+1).factorial := by
    rw [Nat.factorial_succ, ← mul_assoc]
    exact Dvd.dvd.mul_left h2c _
  obtain ⟨B, hB⟩ := h2c'
  -- positivity of the denominator
  have hQpos : 0 < Qf m 1 := Qf_pos m (by omega)
  have hQ1 : Qf m 1 = 2 * (c:ℚ) * ((p:ℚ) * A - B) := by
    unfold Qf
    rw [show G 1 = 1 from rfl, Nat.factorial_one]
    have e1 : ((m:ℚ)^2 + 8*m + 11) = (p:ℚ) * c := by exact_mod_cast hM
    have e2 : (G (m+1) : ℚ) = 2 * A := by exact_mod_cast hA
    have e3 : ((m:ℚ) + 3) * ((m+1).factorial : ℚ) = 2 * c * B := by exact_mod_cast hB
    rw [e1, e2, e3]; push_cast; ring
  have hAB : (0:ℚ) < (p:ℚ) * A - B := by
    rw [hQ1] at hQpos
    have hc0 : (0:ℚ) < 2 * (c:ℚ) := by positivity
    exact pos_of_mul_pos_right hQpos hc0.le  -- check
  have hABz : (0:ℤ) < (p:ℤ) * A - B := by
    have : ((( (p:ℤ) * A - B : ℤ)) : ℚ) = (p:ℚ) * A - B := by push_cast; ring
    exact_mod_cast (this ▸ hAB)
  refine ⟨m + 3, ?_⟩
  rw [A_eq]
  have hval : (2 * ((m:ℚ)^2 + 8*m + 11) /
      (((m:ℚ)^2 + 8*m + 11) * (G (m+1) : ℚ) - ((m:ℚ)+3) * ((m+1).factorial : ℚ)))
      = ((p:ℤ) : ℚ) / (((p:ℤ) * A - B : ℤ) : ℚ) := by
    have e1 : ((m:ℚ)^2 + 8*m + 11) = (p:ℚ) * c := by exact_mod_cast hM
    have e2 : (G (m+1) : ℚ) = 2 * A := by exact_mod_cast hA
    have e3 : ((m:ℚ) + 3) * ((m+1).factorial : ℚ) = 2 * c * B := by exact_mod_cast hB
    rw [e1, e2, e3]
    push_cast
    have hc0 : (c:ℚ) ≠ 0 := by positivity
    have hne : (p:ℚ) * A - B ≠ 0 := ne_of_gt hAB
    field_simp
  rw [hval, Rat.num_div_eq_of_coprime hABz]
  · exact Int.natAbs_natCast p
  · rw [Int.natAbs_natCast, hpp.coprime_iff_not_dvd, ← Int.natCast_dvd]
    intro hdvd
    have hB' : (p:ℤ) ∣ (B:ℤ) := by
      have := Dvd.dvd.sub (dvd_mul_right (p:ℤ) (A:ℤ)) hdvd
      simpa using this
    rw [Int.natCast_dvd_natCast] at hB'
    have : p ∣ (m + 3) * (m+1).factorial := by
      rw [hB]; exact Dvd.dvd.mul_left hB' _
    rcases (Nat.Prime.dvd_mul hpp).mp this with h | h
    · have := Nat.le_of_dvd (by omega) h; omega
    · have := (Nat.Prime.dvd_factorial hpp).mp h; omega

theorem main_thm :
  ∀ p : ℕ,
    (p.Prime ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) →
    ∃ n : ℕ, A363347 n = p := by
  rintro p ⟨hp, hmod⟩
  by_cases h11 : p = 11
  · exact ⟨3, by rw [A_three, h11]⟩
  have hp19 : 19 ≤ p := by
    have h2 := hp.two_le
    have h9 : p ≠ 9 := by rintro rfl; norm_num at hp
    unfold Nat.ModEq at hmod
    omega
  haveI := Fact.mk hp
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hsq : IsSquare ((5:ℕ) : ZMod p) := by
    rw [← ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p) (by norm_num) (by omega)]
    rw [← ZMod.natCast_mod p 5]
    unfold Nat.ModEq at hmod
    rcases hmod with h | h
    · have : p % 5 = 1 := by omega
      rw [this]; exact ⟨1, by decide +revert⟩
    · have : p % 5 = 4 := by omega
      rw [this]; exact ⟨2, by decide +revert⟩
  obtain ⟨y, hy⟩ := hsq
  by_cases hev : Even y.val
  · exact core p hp19 y hy hev
  · apply core p hp19 (-y) (by rw [hy]; ring)
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hev
    rw [ZMod.neg_val, if_neg hy0]
    have hodd : Odd p := hp.odd_of_ne_two (by omega)
    have h1 := Nat.odd_iff.mp hodd
    have h2 : y.val % 2 = 1 := by
      rcases Nat.even_or_odd y.val with h | h
      · exact absurd h hev
      · exact Nat.odd_iff.mp h
    have h3 := ZMod.val_lt y
    exact Nat.even_iff.mpr (by omega)

end A363347Aux

/--
A363347 Conjecture 2: The sequence contains all prime numbers which end with a 1 or 9.
-/
theorem oeis_363347_conjecture_2 :
  ∀ p : ℕ,
    (p.Prime ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) →
    ∃ n : ℕ, A363347 n = p :=
  A363347Aux.main_thm

theorem oeis_363347_conjecture_2.disproof : ¬ (type_of% @oeis_363347_conjecture_2) := sorry
