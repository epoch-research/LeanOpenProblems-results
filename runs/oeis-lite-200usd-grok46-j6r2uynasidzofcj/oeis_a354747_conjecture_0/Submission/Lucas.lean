import FormalConjectures.Util.ProblemImports

/-!
Lucas sequences and the N+1 primality test (Brillhart–Lehmer–Selfridge).
-/

open Nat Int

/-- Lucas U-sequence: `U₀ = 0`, `U₁ = 1`, `Uₙ = P Uₙ₋₁ - Q Uₙ₋₂`. -/
def lucasU (P Q : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => P * lucasU P Q (n + 1) - Q * lucasU P Q n

/-- Lucas V-sequence: `V₀ = 2`, `V₁ = P`, `Vₙ = P Vₙ₋₁ - Q Vₙ₋₂`. -/
def lucasV (P Q : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => P
  | n + 2 => P * lucasV P Q (n + 1) - Q * lucasV P Q n

@[simp] theorem lucasU_zero (P Q : ℤ) : lucasU P Q 0 = 0 := rfl
@[simp] theorem lucasU_one (P Q : ℤ) : lucasU P Q 1 = 1 := rfl
@[simp] theorem lucasV_zero (P Q : ℤ) : lucasV P Q 0 = 2 := rfl
@[simp] theorem lucasV_one (P Q : ℤ) : lucasV P Q 1 = P := rfl

theorem lucasU_add_two (P Q : ℤ) (n : ℕ) :
    lucasU P Q (n + 2) = P * lucasU P Q (n + 1) - Q * lucasU P Q n := rfl

theorem lucasV_add_two (P Q : ℤ) (n : ℕ) :
    lucasV P Q (n + 2) = P * lucasV P Q (n + 1) - Q * lucasV P Q n := rfl

/-- Discriminant `D = P² - 4Q`. -/
def lucasD (P Q : ℤ) : ℤ := P ^ 2 - 4 * Q

private theorem two_mul_cancel {a b : ℤ} (h : 2 * a = 2 * b) : a = b :=
  mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h

/-- Simultaneous companion identities:
* `Vₙ + P Uₙ = 2 Uₙ₊₁`
* `D Uₙ + P Vₙ = 2 Vₙ₊₁`
-/
theorem lucas_UV_identities (P Q : ℤ) (n : ℕ) :
    lucasV P Q n + P * lucasU P Q n = 2 * lucasU P Q (n + 1) ∧
    lucasD P Q * lucasU P Q n + P * lucasV P Q n = 2 * lucasV P Q (n + 1) := by
  induction n with
  | zero =>
    constructor
    · simp
    · simp [lucasD]; ring
  | succ n ih =>
    obtain ⟨ihA, ihB⟩ := ih
    refine ⟨?A, ?B⟩
    · apply two_mul_cancel
      -- 2(V_{n+1} + P U_{n+1}) = 4 U_{n+2} = 4P U_{n+1} - 4Q U_n
      have h2V : 2 * lucasV P Q (n + 1) =
          lucasD P Q * lucasU P Q n + P * lucasV P Q n := ihB.symm
      have hPV : P * lucasV P Q n =
          2 * P * lucasU P Q (n + 1) - P ^ 2 * lucasU P Q n := by
        linear_combination P * ihA
      calc
        2 * (lucasV P Q (n + 1) + P * lucasU P Q (n + 1))
            = 2 * lucasV P Q (n + 1) + 2 * P * lucasU P Q (n + 1) := by ring
        _ = lucasD P Q * lucasU P Q n + P * lucasV P Q n
              + 2 * P * lucasU P Q (n + 1) := by rw [h2V]
        _ = lucasD P Q * lucasU P Q n
              + (2 * P * lucasU P Q (n + 1) - P ^ 2 * lucasU P Q n)
              + 2 * P * lucasU P Q (n + 1) := by rw [hPV]
        _ = 4 * P * lucasU P Q (n + 1) + (lucasD P Q - P ^ 2) * lucasU P Q n := by
            ring
        _ = 4 * P * lucasU P Q (n + 1) - 4 * Q * lucasU P Q n := by
            simp [lucasD]; ring
        _ = 2 * (2 * lucasU P Q (n + 2)) := by
            rw [lucasU_add_two]; ring
    · apply two_mul_cancel
      have h2U : 2 * lucasU P Q (n + 1) =
          lucasV P Q n + P * lucasU P Q n := ihA.symm
      have hDU : lucasD P Q * lucasU P Q n =
          2 * lucasV P Q (n + 1) - P * lucasV P Q n := by
        linear_combination ihB
      calc
        2 * (lucasD P Q * lucasU P Q (n + 1) + P * lucasV P Q (n + 1))
            = lucasD P Q * (2 * lucasU P Q (n + 1))
              + 2 * P * lucasV P Q (n + 1) := by ring
        _ = lucasD P Q * (lucasV P Q n + P * lucasU P Q n)
              + 2 * P * lucasV P Q (n + 1) := by rw [h2U]
        _ = lucasD P Q * lucasV P Q n + P * (lucasD P Q * lucasU P Q n)
              + 2 * P * lucasV P Q (n + 1) := by ring
        _ = lucasD P Q * lucasV P Q n
              + P * (2 * lucasV P Q (n + 1) - P * lucasV P Q n)
              + 2 * P * lucasV P Q (n + 1) := by rw [hDU]
        _ = 4 * P * lucasV P Q (n + 1) + (lucasD P Q - P ^ 2) * lucasV P Q n := by
            ring
        _ = 4 * P * lucasV P Q (n + 1) - 4 * Q * lucasV P Q n := by
            simp [lucasD]; ring
        _ = 2 * (2 * lucasV P Q (n + 2)) := by
            rw [lucasV_add_two]; ring

theorem lucasV_add_P_mul_U (P Q : ℤ) (n : ℕ) :
    lucasV P Q n + P * lucasU P Q n = 2 * lucasU P Q (n + 1) :=
  (lucas_UV_identities P Q n).1

theorem lucasD_mul_U_add_P_mul_V (P Q : ℤ) (n : ℕ) :
    lucasD P Q * lucasU P Q n + P * lucasV P Q n = 2 * lucasV P Q (n + 1) :=
  (lucas_UV_identities P Q n).2


/- ### Closed form in `ℤ√D` -/

/-- `ω = P + √D`. -/
def lucasω (P Q : ℤ) : ℤ√(lucasD P Q) := ⟨P, 1⟩

/-- For `n ≥ 1`, `(P+√D)ⁿ = 2^{n-1} (Vₙ + Uₙ √D)`. -/
theorem lucasω_pow (P Q : ℤ) : ∀ n : ℕ, 1 ≤ n →
    lucasω P Q ^ n =
      ⟨(2 : ℤ) ^ (n - 1) * lucasV P Q n, (2 : ℤ) ^ (n - 1) * lucasU P Q n⟩
  | n + 1, hn => by
    cases n with
    | zero =>
      simp [lucasω]
    | succ n =>
      have ih := lucasω_pow P Q (n + 1) (Nat.succ_le_succ (Nat.zero_le _))
      rw [pow_succ, ih]
      have h2 : (2 : ℤ) ^ (n + 1) = 2 * (2 : ℤ) ^ n := by rw [pow_succ, mul_comm]
      ext
      · -- real part
        rw [Zsqrtd.re_mul]
        change (2 : ℤ) ^ ((n + 1) - 1) * lucasV P Q (n + 1) * P
            + lucasD P Q * ((2 : ℤ) ^ ((n + 1) - 1) * lucasU P Q (n + 1)) * 1
            = (2 : ℤ) ^ ((n + 1 + 1) - 1) * lucasV P Q (n + 1 + 1)
        have := lucasD_mul_U_add_P_mul_V P Q (n + 1)
        simp only [Nat.add_sub_cancel]
        calc
          (2 : ℤ) ^ n * lucasV P Q (n + 1) * P
              + lucasD P Q * ((2 : ℤ) ^ n * lucasU P Q (n + 1)) * 1
              = (2 : ℤ) ^ n * (P * lucasV P Q (n + 1)
                  + lucasD P Q * lucasU P Q (n + 1)) := by ring
          _ = (2 : ℤ) ^ n * (2 * lucasV P Q (n + 2)) := by
              rw [add_comm (P * lucasV P Q (n + 1))]; exact congrArg _ this
          _ = (2 : ℤ) ^ (n + 1) * lucasV P Q (n + 2) := by rw [h2]; ring
      · rw [Zsqrtd.im_mul]
        change (2 : ℤ) ^ ((n + 1) - 1) * lucasV P Q (n + 1) * 1
            + (2 : ℤ) ^ ((n + 1) - 1) * lucasU P Q (n + 1) * P
            = (2 : ℤ) ^ ((n + 1 + 1) - 1) * lucasU P Q (n + 1 + 1)
        have := lucasV_add_P_mul_U P Q (n + 1)
        simp only [Nat.add_sub_cancel]
        calc
          (2 : ℤ) ^ n * lucasV P Q (n + 1) * 1
              + (2 : ℤ) ^ n * lucasU P Q (n + 1) * P
              = (2 : ℤ) ^ n * (lucasV P Q (n + 1) + P * lucasU P Q (n + 1)) := by
                ring
          _ = (2 : ℤ) ^ n * (2 * lucasU P Q (n + 2)) := by rw [this]
          _ = (2 : ℤ) ^ (n + 1) * lucasU P Q (n + 2) := by rw [h2]; ring

/- ### Powers of `√D` -/

theorem Zsqrtd.sqrtd_pow_even {d : ℤ} (j : ℕ) :
    (sqrtd : ℤ√d) ^ (2 * j) = ⟨d ^ j, 0⟩ := by
  induction j with
  | zero =>
    ext
    · simp
    · simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add, ih, pow_two]
    ext
    · simp [Zsqrtd.re_mul, Zsqrtd.im_mul]; ring
    · simp [Zsqrtd.re_mul, Zsqrtd.im_mul]

theorem Zsqrtd.sqrtd_pow_odd {d : ℤ} (j : ℕ) :
    (sqrtd : ℤ√d) ^ (2 * j + 1) = ⟨0, d ^ j⟩ := by
  rw [pow_succ, Zsqrtd.sqrtd_pow_even]
  ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]

/- ### Congruences modulo an odd prime -/

theorem lucasV_pow_two_mul (P Q : ℤ) {n : ℕ} (hn : 1 ≤ n) :
    (2 : ℤ) ^ (n - 1) * lucasV P Q n = (lucasω P Q ^ n).re := by
  rw [lucasω_pow P Q n hn]

theorem lucasU_pow_two_mul (P Q : ℤ) {n : ℕ} (hn : 1 ≤ n) :
    (2 : ℤ) ^ (n - 1) * lucasU P Q n = (lucasω P Q ^ n).im := by
  rw [lucasω_pow P Q n hn]




section ZsqrtdHelpers

variable {d : ℤ}

private theorem re_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ√d) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re :=
  map_sum (AddMonoidHom.mk' (fun z : ℤ√d => z.re) (fun x y => Zsqrtd.re_add x y)) f s

private theorem im_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ√d) :
    (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im :=
  map_sum (AddMonoidHom.mk' (fun z : ℤ√d => z.im) (fun x y => Zsqrtd.im_add x y)) f s

private theorem re_intCast_pow (a : ℤ) (m : ℕ) :
    ((a : ℤ√d) ^ m).re = a ^ m := by
  rw [← Int.cast_pow, Zsqrtd.re_intCast]

private theorem im_intCast_pow (a : ℤ) (m : ℕ) :
    ((a : ℤ√d) ^ m).im = 0 := by
  rw [← Int.cast_pow, Zsqrtd.im_intCast]

private theorem re_int_pow_mul_sqrtd_pow_even (a : ℤ) (m j : ℕ) (c : ℕ) :
    ((a : ℤ√d) ^ m * (Zsqrtd.sqrtd : ℤ√d) ^ (2 * j) * c).re =
      a ^ m * d ^ j * c := by
  rw [Zsqrtd.sqrtd_pow_even, Zsqrtd.re_mul, Zsqrtd.re_mul, Zsqrtd.im_mul]
  rw [re_intCast_pow, im_intCast_pow]
  simp [Zsqrtd.re_natCast, Zsqrtd.im_natCast]

private theorem re_int_pow_mul_sqrtd_pow_odd (a : ℤ) (m j : ℕ) (c : ℕ) :
    ((a : ℤ√d) ^ m * (Zsqrtd.sqrtd : ℤ√d) ^ (2 * j + 1) * c).re = 0 := by
  rw [Zsqrtd.sqrtd_pow_odd, Zsqrtd.re_mul, Zsqrtd.re_mul, Zsqrtd.im_mul]
  rw [re_intCast_pow, im_intCast_pow]
  simp

private theorem im_int_pow_mul_sqrtd_pow_even (a : ℤ) (m j : ℕ) (c : ℕ) :
    ((a : ℤ√d) ^ m * (Zsqrtd.sqrtd : ℤ√d) ^ (2 * j) * c).im = 0 := by
  rw [Zsqrtd.sqrtd_pow_even, Zsqrtd.im_mul, Zsqrtd.im_mul]
  rw [re_intCast_pow, im_intCast_pow]
  simp

private theorem im_int_pow_mul_sqrtd_pow_odd (a : ℤ) (m j : ℕ) (c : ℕ) :
    ((a : ℤ√d) ^ m * (Zsqrtd.sqrtd : ℤ√d) ^ (2 * j + 1) * c).im =
      a ^ m * d ^ j * c := by
  rw [Zsqrtd.sqrtd_pow_odd, Zsqrtd.im_mul, Zsqrtd.im_mul, Zsqrtd.re_mul]
  rw [re_intCast_pow, im_intCast_pow]
  simp [Zsqrtd.re_natCast, Zsqrtd.im_natCast]

end ZsqrtdHelpers

theorem lucasω_eq_add (P Q : ℤ) :
    lucasω P Q = (P : ℤ√(lucasD P Q)) + (Zsqrtd.sqrtd : ℤ√(lucasD P Q)) := by
  ext <;> simp [lucasω]


private theorem even_iff_two_mul (n : ℕ) : Even n ↔ ∃ j, n = 2 * j := by
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, by rw [hj, two_mul]⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, by rw [hj, two_mul]⟩

private theorem odd_iff_two_mul_add_one (n : ℕ) : Odd n ↔ ∃ j, n = 2 * j + 1 :=
  odd_iff_exists_bit1

/-- The real part of `(P+√D)^p` is `≡ P^p` modulo an odd prime `p`. -/
theorem lucasω_pow_prime_re (P Q : ℤ) {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    (lucasω P Q ^ p).re ≡ P ^ p [ZMOD p] := by
  rw [lucasω_eq_add, add_pow, re_sum]
  let term (m : ℕ) : ℤ :=
    if Even (p - m) then P ^ m * lucasD P Q ^ ((p - m) / 2) * (p.choose m : ℤ) else 0
  have hterm : ∀ m ∈ Finset.range (p + 1),
      (((P : ℤ√(lucasD P Q)) ^ m * (Zsqrtd.sqrtd : ℤ√(lucasD P Q)) ^ (p - m) *
          (p.choose m : ℕ))).re = term m := by
    intro m hm
    rcases Nat.even_or_odd (p - m) with hE | hO
    · obtain ⟨j, hj⟩ := (even_iff_two_mul _).1 hE
      simp only [term, hE, ↓reduceIte]
      rw [hj, re_int_pow_mul_sqrtd_pow_even]
      congr 1
      · congr 1
        simp [hj]
    · obtain ⟨j, hj⟩ := (odd_iff_two_mul_add_one _).1 hO
      have : ¬ Even (p - m) := Nat.not_even_iff_odd.2 hO
      simp only [term, this, ↓reduceIte]
      rw [hj, re_int_pow_mul_sqrtd_pow_odd]
  rw [Finset.sum_congr rfl hterm]
  have hcongr : ∀ m ∈ Finset.range (p + 1),
      term m ≡ (if m = p then P ^ p else 0) [ZMOD p] := by
    intro m hm
    rw [Finset.mem_range] at hm
    unfold term
    by_cases hmp : m = p
    · have hEv : Even (0 : ℕ) := ⟨0, by simp⟩
      simp [hmp, hEv]
    · by_cases hm0 : m = 0
      · subst m
        have : ¬ Even p := Nat.not_even_iff_odd.2 hodd
        simp [this, hp.ne_zero.symm]
      · have hmlt : m < p := lt_of_le_of_ne (Nat.lt_succ_iff.1 hm) hmp
        have hdiv : (p : ℤ) ∣ (p.choose m : ℤ) :=
          Int.natCast_dvd_natCast.2 (hp.dvd_choose_self hm0 hmlt)
        split_ifs
        · refine (Int.modEq_zero_iff_dvd.2 (dvd_mul_of_dvd_right hdiv _)).trans ?_
          simp [hmp]
        · simp [hmp]
  have hs := Int.ModEq.sum hcongr
  have hR : ∑ m ∈ Finset.range (p + 1), (if m = p then P ^ p else (0 : ℤ)) = P ^ p := by
    rw [Finset.sum_eq_single_of_mem p (Finset.mem_range.2 (lt_add_one p))]
    · simp
    · intro m _ hne; simp [hne]
  rwa [hR] at hs

/-- The imaginary part of `(P+√D)^p` is `≡ D^{(p-1)/2}` modulo an odd prime `p`. -/
theorem lucasω_pow_prime_im (P Q : ℤ) {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    (lucasω P Q ^ p).im ≡ lucasD P Q ^ (p / 2) [ZMOD p] := by
  rw [lucasω_eq_add, add_pow, im_sum]
  let term (m : ℕ) : ℤ :=
    if Even (p - m) then 0 else P ^ m * lucasD P Q ^ ((p - m) / 2) * (p.choose m : ℤ)
  have hterm : ∀ m ∈ Finset.range (p + 1),
      (((P : ℤ√(lucasD P Q)) ^ m * (Zsqrtd.sqrtd : ℤ√(lucasD P Q)) ^ (p - m) *
          (p.choose m : ℕ))).im = term m := by
    intro m hm
    rcases Nat.even_or_odd (p - m) with hE | hO
    · obtain ⟨j, hj⟩ := (even_iff_two_mul _).1 hE
      simp only [term, hE, ↓reduceIte]
      rw [hj, im_int_pow_mul_sqrtd_pow_even]
    · obtain ⟨j, hj⟩ := (odd_iff_two_mul_add_one _).1 hO
      have : ¬ Even (p - m) := Nat.not_even_iff_odd.2 hO
      simp only [term, this, ↓reduceIte]
      rw [hj, im_int_pow_mul_sqrtd_pow_odd]
      have hj2 : (2 * j + 1) / 2 = j := by omega
      rw [hj2]
  rw [Finset.sum_congr rfl hterm]
  have hcongr : ∀ m ∈ Finset.range (p + 1),
      term m ≡ (if m = 0 then lucasD P Q ^ (p / 2) else 0) [ZMOD p] := by
    intro m hm
    rw [Finset.mem_range] at hm
    by_cases hm0 : m = 0
    · -- m = 0: p-0 = p is odd, so term = D^{p/2}
      have hodd' : ¬ Even p := Nat.not_even_iff_odd.2 hodd
      simp [term, hm0, hodd']
    · by_cases hmp : m = p
      · have hEv : Even (p - m) := by simp [hmp]
        simp [term, hEv, hm0]
      · have hmlt : m < p := lt_of_le_of_ne (Nat.lt_succ_iff.1 hm) hmp
        have hdiv : (p : ℤ) ∣ (p.choose m : ℤ) :=
          Int.natCast_dvd_natCast.2 (hp.dvd_choose_self hm0 hmlt)
        dsimp [term]
        split_ifs
        · simp [hm0]
        · refine (Int.modEq_zero_iff_dvd.2 (dvd_mul_of_dvd_right hdiv _)).trans ?_
          simp [hm0]
  have hs := Int.ModEq.sum hcongr
  have hR : ∑ m ∈ Finset.range (p + 1),
      (if m = 0 then lucasD P Q ^ (p / 2) else (0 : ℤ)) = lucasD P Q ^ (p / 2) := by
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 (Nat.succ_pos _))]
    · simp
    · intro m _ hne; simp [hne]
  rwa [hR] at hs


/-- `2^{p-1} ≡ 1 [ZMOD p]` for an odd prime `p`. -/
theorem two_pow_prime_sub_one {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    (2 : ℤ) ^ (p - 1) ≡ 1 [ZMOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h)
    have hp2 : p = 2 := (Nat.dvd_prime Nat.prime_two).1 this |>.resolve_left hp.ne_one
    subst hp2
    exact Nat.not_odd_iff_even.2 even_two hodd
  have : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  rw [← ZMod.intCast_eq_intCast_iff]
  simpa using this

/-- `V_p ≡ P [ZMOD p]` for an odd prime `p`. -/
theorem lucasV_prime (P Q : ℤ) {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    lucasV P Q p ≡ P [ZMOD p] := by
  have hn : 1 ≤ p := hp.one_lt.le
  have hre : (2 : ℤ) ^ (p - 1) * lucasV P Q p ≡ P ^ p [ZMOD p] := by
    have := lucasω_pow_prime_re P Q hp hodd
    rwa [← lucasV_pow_two_mul P Q hn] at this
  have h2 : (2 : ℤ) ^ (p - 1) ≡ 1 [ZMOD p] := two_pow_prime_sub_one hp hodd
  haveI : Fact p.Prime := ⟨hp⟩
  have hP : P ^ p ≡ P [ZMOD p] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    simpa [ZMod.pow_card] using (rfl : (P : ZMod p) ^ p = (P : ZMod p) ^ p)
  -- actually use ZMod.pow_card : a ^ p = a
  have hP' : P ^ p ≡ P [ZMOD p] := by
    rw [← ZMod.intCast_eq_intCast_iff, Int.cast_pow]
    exact ZMod.pow_card (P : ZMod p)
  have hmul := h2.mul (Int.ModEq.refl (lucasV P Q p))
  -- 2^{p-1} * V ≡ 1 * V = V, and ≡ P^p ≡ P
  have : lucasV P Q p ≡ P [ZMOD p] := by
    have hL : (2 : ℤ) ^ (p - 1) * lucasV P Q p ≡ lucasV P Q p [ZMOD p] := by
      simpa using h2.mul_right (lucasV P Q p)
    exact hL.symm.trans (hre.trans hP')
  exact this

/-- `U_p ≡ D^{p/2} [ZMOD p]` for an odd prime `p`. -/
theorem lucasU_prime (P Q : ℤ) {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    lucasU P Q p ≡ lucasD P Q ^ (p / 2) [ZMOD p] := by
  have hn : 1 ≤ p := hp.one_lt.le
  have him : (2 : ℤ) ^ (p - 1) * lucasU P Q p ≡ lucasD P Q ^ (p / 2) [ZMOD p] := by
    have := lucasω_pow_prime_im P Q hp hodd
    rwa [← lucasU_pow_two_mul P Q hn] at this
  have h2 : (2 : ℤ) ^ (p - 1) ≡ 1 [ZMOD p] := two_pow_prime_sub_one hp hodd
  have hL : (2 : ℤ) ^ (p - 1) * lucasU P Q p ≡ lucasU P Q p [ZMOD p] := by
    simpa using h2.mul_right (lucasU P Q p)
  exact hL.symm.trans him

/-- `U_p ≡ (D/p) [ZMOD p]`. -/
theorem lucasU_prime_legendre (P Q : ℤ) {p : ℕ} [Fact p.Prime] (hodd : Odd p) :
    lucasU P Q p ≡ legendreSym p (lucasD P Q) [ZMOD p] := by
  have hp := Fact.out (p := p.Prime)
  have h1 := lucasU_prime P Q hp hodd
  have h2 : (legendreSym p (lucasD P Q) : ZMod p) = (lucasD P Q : ZMod p) ^ (p / 2) :=
    legendreSym.eq_pow (p := p) (lucasD P Q)
  rw [← ZMod.intCast_eq_intCast_iff] at h1 ⊢
  rw [Int.cast_pow] at h1
  exact h1.trans h2.symm


/-- `Vₙ = P Uₙ - 2 Q Uₙ₋₁` for `n ≥ 1`. -/
theorem lucasV_eq_of_U (P Q : ℤ) : ∀ n : ℕ, 1 ≤ n →
    lucasV P Q n = P * lucasU P Q n - 2 * Q * lucasU P Q (n - 1)
  | n + 1, _ => by
    have hA := lucasV_add_P_mul_U P Q (n + 1)
    -- V_{n+1} + P U_{n+1} = 2 U_{n+2} = 2 (P U_{n+1} - Q U_n)
    have hrec : lucasU P Q (n + 2) = P * lucasU P Q (n + 1) - Q * lucasU P Q n := rfl
    have : lucasV P Q (n + 1) + P * lucasU P Q (n + 1) =
        2 * P * lucasU P Q (n + 1) - 2 * Q * lucasU P Q n := by
      rw [hA, hrec]; ring
    have h : lucasV P Q (n + 1) =
        P * lucasU P Q (n + 1) - 2 * Q * lucasU P Q n := by
      linear_combination this
    simpa [Nat.add_sub_cancel] using h

/-- `P Uₙ - Vₙ = 2 Q Uₙ₋₁` for `n ≥ 1`. -/
theorem lucas_P_U_sub_V (P Q : ℤ) {n : ℕ} (hn : 1 ≤ n) :
    P * lucasU P Q n - lucasV P Q n = 2 * Q * lucasU P Q (n - 1) := by
  rw [lucasV_eq_of_U P Q n hn]; ring


/-- Law of appearance, case `(D/p) = 1`: `p ∣ U_{p-1}`. -/
theorem lucas_appearance_one (P Q : ℤ) {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hleg : legendreSym p (lucasD P Q) = 1)
    (hQ : ¬(p : ℤ) ∣ Q) :
    (p : ℤ) ∣ lucasU P Q (p - 1) := by
  have hp := Fact.out (p := p.Prime)
  have hn : 1 ≤ p := hp.one_lt.le
  have hU := lucasU_prime_legendre P Q hodd
  have hV := lucasV_prime P Q hp hodd
  have hUV := lucas_P_U_sub_V P Q hn
  have h0 : P * lucasU P Q p - lucasV P Q p ≡ 0 [ZMOD p] := by
    have hPU : P * lucasU P Q p ≡ P * (1 : ℤ) [ZMOD p] := by
      simpa [hleg] using (hU.mul_left P)
    have hsub := hPU.sub hV
    simpa using hsub
  have hdiv2Q : (p : ℤ) ∣ 2 * Q * lucasU P Q (p - 1) := by
    rw [← hUV]
    exact Int.modEq_zero_iff_dvd.1 h0
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp2 : ¬(p : ℤ) ∣ 2 := by
    intro h
    have : p ∣ 2 := Int.natCast_dvd_natCast.1 h
    have hp2 : p = 2 := (Nat.dvd_prime Nat.prime_two).1 this |>.resolve_left hp.ne_one
    subst hp2
    exact Nat.not_odd_iff_even.2 even_two hodd
  rcases hpp.dvd_or_dvd hdiv2Q with h2 | hU
  · rcases hpp.dvd_or_dvd h2 with hp2' | hpQ
    · exact (hp2 hp2').elim
    · exact (hQ hpQ).elim
  · exact hU

/-- Law of appearance, case `(D/p) = -1`: `p ∣ U_{p+1}`. -/
theorem lucas_appearance_neg_one (P Q : ℤ) {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hleg : legendreSym p (lucasD P Q) = -1) :
    (p : ℤ) ∣ lucasU P Q (p + 1) := by
  have hp := Fact.out (p := p.Prime)
  -- 2 U_{p+1} = V_p + P U_p ≡ P + P*(-1) = 0
  have hA := lucasV_add_P_mul_U P Q p
  have hU := lucasU_prime_legendre P Q hodd
  have hV := lucasV_prime P Q hp hodd
  have : lucasV P Q p + P * lucasU P Q p ≡ 0 [ZMOD p] := by
    have hPU : P * lucasU P Q p ≡ P * (-1 : ℤ) [ZMOD p] := by
      simpa [hleg] using hU.mul_left P
    have hsum := hV.add hPU
    simpa using hsum
  -- 2 U_{p+1} ≡ 0, p ∤ 2 ⇒ p ∣ U_{p+1}
  have h2U : 2 * lucasU P Q (p + 1) ≡ 0 [ZMOD p] := by
    rwa [← hA]
  have hp2 : ¬(p : ℤ) ∣ 2 := by
    intro h
    have : p ∣ 2 := Int.natCast_dvd_natCast.1 h
    have hp2 : p = 2 := (Nat.dvd_prime Nat.prime_two).1 this |>.resolve_left hp.ne_one
    subst hp2
    exact Nat.not_odd_iff_even.2 even_two hodd
  have h2U' : (p : ℤ) ∣ 2 * lucasU P Q (p + 1) := Int.modEq_zero_iff_dvd.1 h2U
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  exact (hpp.dvd_or_dvd h2U').resolve_left hp2


/-- Cassini-type identity: `Uₘ Vₙ - Vₘ Uₙ = 2 Qⁿ U_{m-n}` for `n ≤ m`. -/
theorem lucas_cassini (P Q : ℤ) (m n : ℕ) (hnm : n ≤ m) :
    lucasU P Q m * lucasV P Q n - lucasV P Q m * lucasU P Q n =
      2 * Q ^ n * lucasU P Q (m - n) := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    match n with
    | 0 =>
      simp; ring
    | 1 =>
      have hm : 1 ≤ m := hnm
      have := lucas_P_U_sub_V P Q hm
      simp only [lucasV_one, lucasU_one, pow_one, tsub_self] at *
      -- U_m * P - V_m * 1 = 2 Q U_{m-1}
      linear_combination this
    | n + 2 =>
      have hle1 : n + 1 ≤ m := by omega
      have hle0 : n ≤ m := by omega
      have ih1 := ih (n + 1) (by omega) m hle1
      have ih0 := ih n (by omega) m hle0
      have hV : lucasV P Q (n + 2) = P * lucasV P Q (n + 1) - Q * lucasV P Q n := rfl
      have hU : lucasU P Q (n + 2) = P * lucasU P Q (n + 1) - Q * lucasU P Q n := rfl
      have hcomb :
          lucasU P Q m * lucasV P Q (n + 2) - lucasV P Q m * lucasU P Q (n + 2) =
            P * (lucasU P Q m * lucasV P Q (n + 1) - lucasV P Q m * lucasU P Q (n + 1))
          - Q * (lucasU P Q m * lucasV P Q n - lucasV P Q m * lucasU P Q n) := by
        rw [hV, hU]; ring
      rw [hcomb, ih1, ih0]
      have hrec : lucasU P Q (m - n) =
          P * lucasU P Q (m - n - 1) - Q * lucasU P Q (m - n - 2) := by
        have h := lucasU_add_two P Q (m - n - 2)
        have e1 : m - n - 2 + 2 = m - n := by omega
        have e2 : m - n - 2 + 1 = m - n - 1 := by omega
        rwa [e1, e2] at h
      have h1 : m - (n + 1) = m - n - 1 := by omega
      have h2 : m - (n + 2) = m - n - 2 := by omega
      rw [h1, h2, pow_succ, pow_succ, hrec]
      ring


/-- If an odd prime `p ∤ Q` divides `U_a` and `U_b` (`b ≤ a`), then it divides `U_{a-b}`. -/
theorem lucasU_dvd_sub (P Q : ℤ) {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hQ : ¬(p : ℤ) ∣ Q) {a b : ℕ} (hba : b ≤ a)
    (ha : (p : ℤ) ∣ lucasU P Q a) (hb : (p : ℤ) ∣ lucasU P Q b) :
    (p : ℤ) ∣ lucasU P Q (a - b) := by
  rcases Nat.eq_zero_or_pos b with rfl | hbpos
  · simpa using ha
  have hcass := lucas_cassini P Q a b hba
  have hleft : (p : ℤ) ∣
      lucasU P Q a * lucasV P Q b - lucasV P Q a * lucasU P Q b :=
    dvd_sub (ha.mul_right _) (hb.mul_left _)
  have h2QU : (p : ℤ) ∣ 2 * Q ^ b * lucasU P Q (a - b) := by
    rwa [← hcass]
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp2 : ¬(p : ℤ) ∣ 2 := by
    intro h
    have : p ∣ 2 := Int.natCast_dvd_natCast.1 h
    have hp2 : p = 2 := (Nat.dvd_prime Nat.prime_two).1 this |>.resolve_left hp.ne_one
    subst hp2
    exact Nat.not_odd_iff_even.2 even_two hodd
  have hnotQpow : ¬(p : ℤ) ∣ Q ^ b := by
    intro h
    have : (p : ℤ) ∣ Q := hpp.dvd_of_dvd_pow h
    exact hQ this
  have hassoc : (p : ℤ) ∣ 2 * (Q ^ b * lucasU P Q (a - b)) := by
    convert h2QU using 1; ring
  rcases hpp.dvd_or_dvd hassoc with hp2' | hQU
  · exact (hp2 hp2').elim
  · rcases hpp.dvd_or_dvd hQU with hQpow | hU
    · exact (hnotQpow hQpow).elim
    · exact hU


/-- Repeated subtraction: if `p ∣ U_a` and `p ∣ U_b` then `p ∣ U_{a % b}` (for `b ≠ 0`). -/
theorem lucasU_dvd_mod (P Q : ℤ) {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hQ : ¬(p : ℤ) ∣ Q) {a b : ℕ} (hb : b ≠ 0)
    (haU : (p : ℤ) ∣ lucasU P Q a) (hbU : (p : ℤ) ∣ lucasU P Q b) :
    (p : ℤ) ∣ lucasU P Q (a % b) := by
  have step : ∀ k, k * b ≤ a → (p : ℤ) ∣ lucasU P Q (a - k * b) := by
    intro k
    induction k with
    | zero =>
      intro; simpa using haU
    | succ k ih =>
      intro hle
      have hle' : k * b ≤ a :=
        le_trans (Nat.mul_le_mul_right b k.le_succ) hle
      have ih' := ih hle'
      have hbb : b ≤ a - k * b := by
        have : b + k * b = (k + 1) * b := by rw [add_comm, ← Nat.succ_mul]
        exact Nat.le_sub_of_add_le (this ▸ hle)
      have hsub := lucasU_dvd_sub P Q hp hodd hQ hbb ih' hbU
      have : a - (k + 1) * b = a - k * b - b := by
        rw [add_mul, one_mul, Nat.sub_add_eq]
      rwa [this]
  have hle : a / b * b ≤ a := by
    rw [mul_comm]; exact Nat.mul_div_le a b
  have hstep := step (a / b) hle
  have heq : a - a / b * b = a % b := by
    have h := Nat.div_add_mod a b
    rw [mul_comm] at h
    apply Nat.add_left_cancel (n := a / b * b)
    rw [h, Nat.add_sub_of_le hle]
  rw [heq] at hstep
  exact hstep

/-- If an odd prime `p ∤ Q` divides `U_a` and `U_b`, then it divides `U_{gcd(a,b)}`. -/
theorem lucasU_dvd_gcd (P Q : ℤ) {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hQ : ¬(p : ℤ) ∣ Q) :
    ∀ a b : ℕ, (p : ℤ) ∣ lucasU P Q a → (p : ℤ) ∣ lucasU P Q b →
      (p : ℤ) ∣ lucasU P Q (Nat.gcd a b) := by
  intro a b
  induction a, b using Nat.gcd.induction with
  | H0 y =>
    intro _ hbU
    simpa using hbU
  | H1 x y hx ih =>
    intro hxU hyU
    have hmod := lucasU_dvd_mod P Q hp hodd hQ (Nat.pos_iff_ne_zero.mp hx) hyU hxU
    -- gcd x y = gcd (y % x) x
    rw [Nat.gcd_rec]
    exact ih hmod hxU

/-- Rank of apparition: the least positive `k` with `p ∣ U_k`, if it exists. -/
noncomputable def lucasRank (P Q : ℤ) (p : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ (p : ℤ) ∣ lucasU P Q k}

theorem lucasRank_pos (P Q : ℤ) {p : ℕ}
    (hex : ∃ k > 0, (p : ℤ) ∣ lucasU P Q k) :
    0 < lucasRank P Q p := by
  obtain ⟨k, hkpos, hk⟩ := hex
  have hmem : k ∈ {k : ℕ | 0 < k ∧ (p : ℤ) ∣ lucasU P Q k} := ⟨hkpos, hk⟩
  have : lucasRank P Q p ∈ {k : ℕ | 0 < k ∧ (p : ℤ) ∣ lucasU P Q k} :=
    Nat.sInf_mem ⟨k, hmem⟩
  exact this.1

theorem lucasRank_dvd_U (P Q : ℤ) {p : ℕ}
    (hex : ∃ k > 0, (p : ℤ) ∣ lucasU P Q k) :
    (p : ℤ) ∣ lucasU P Q (lucasRank P Q p) := by
  obtain ⟨k, hkpos, hk⟩ := hex
  have : lucasRank P Q p ∈ {k : ℕ | 0 < k ∧ (p : ℤ) ∣ lucasU P Q k} :=
    Nat.sInf_mem ⟨k, ⟨hkpos, hk⟩⟩
  exact this.2

theorem lucasRank_le_of_dvd (P Q : ℤ) {p k : ℕ} (hkpos : 0 < k)
    (hk : (p : ℤ) ∣ lucasU P Q k) :
    lucasRank P Q p ≤ k :=
  Nat.sInf_le ⟨hkpos, hk⟩

/-- The addition formula `U_{m+n} = U_m V_n - Q^n U_{m-n}` for `n ≤ m`. -/
theorem lucasU_add (P Q : ℤ) (m n : ℕ) (hnm : n ≤ m) :
    lucasU P Q (m + n) = lucasU P Q m * lucasV P Q n - Q ^ n * lucasU P Q (m - n) := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    match n with
    | 0 =>
      simp; ring
    | 1 =>
      have hrec : lucasU P Q (m + 1) = P * lucasU P Q m - Q * lucasU P Q (m - 1) := by
        cases m with
        | zero => omega
        | succ m => simp [lucasU_add_two]
      simpa [pow_one, lucasV_one, mul_comm] using hrec
    | n + 2 =>
      have hle1 : n + 1 ≤ m := by omega
      have hle0 : n ≤ m := by omega
      have ih1 := ih (n + 1) (by omega) m hle1
      have ih0 := ih n (by omega) m hle0
      have idx2 : m + (n + 2) = m + n + 2 := by omega
      have idx1 : m + (n + 1) = m + n + 1 := by omega
      rw [idx2, lucasU_add_two, ← idx1, ih1, ih0]
      have hV : lucasV P Q (n + 2) = P * lucasV P Q (n + 1) - Q * lucasV P Q n := rfl
      rw [hV]
      have e1 : m - (n + 1) = m - n - 1 := by omega
      have e2 : m - (n + 2) = m - n - 2 := by omega
      have hUrec : lucasU P Q (m - n) =
          P * lucasU P Q (m - n - 1) - Q * lucasU P Q (m - n - 2) := by
        have h := lucasU_add_two P Q (m - n - 2)
        have f1 : m - n - 2 + 2 = m - n := by omega
        have f2 : m - n - 2 + 1 = m - n - 1 := by omega
        rwa [f1, f2] at h
      rw [e1, e2, pow_succ, pow_succ, hUrec]
      ring

/-- The addition formula `V_{m+n} = V_m V_n - Q^n V_{m-n}` for `n ≤ m`. -/
theorem lucasV_add (P Q : ℤ) (m n : ℕ) (hnm : n ≤ m) :
    lucasV P Q (m + n) = lucasV P Q m * lucasV P Q n - Q ^ n * lucasV P Q (m - n) := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    match n with
    | 0 =>
      simp; ring
    | 1 =>
      have hrec : lucasV P Q (m + 1) = P * lucasV P Q m - Q * lucasV P Q (m - 1) := by
        cases m with
        | zero => omega
        | succ m => simp [lucasV_add_two]
      simpa [pow_one, lucasV_one, mul_comm] using hrec
    | n + 2 =>
      have hle1 : n + 1 ≤ m := by omega
      have hle0 : n ≤ m := by omega
      have ih1 := ih (n + 1) (by omega) m hle1
      have ih0 := ih n (by omega) m hle0
      have idx2 : m + (n + 2) = m + n + 2 := by omega
      have idx1 : m + (n + 1) = m + n + 1 := by omega
      rw [idx2, lucasV_add_two, ← idx1, ih1, ih0]
      have hV : lucasV P Q (n + 2) = P * lucasV P Q (n + 1) - Q * lucasV P Q n := rfl
      rw [hV]
      have e1 : m - (n + 1) = m - n - 1 := by omega
      have e2 : m - (n + 2) = m - n - 2 := by omega
      have hVrec : lucasV P Q (m - n) =
          P * lucasV P Q (m - n - 1) - Q * lucasV P Q (m - n - 2) := by
        have h := lucasV_add_two P Q (m - n - 2)
        have f1 : m - n - 2 + 2 = m - n := by omega
        have f2 : m - n - 2 + 1 = m - n - 1 := by omega
        rwa [f1, f2] at h
      rw [e1, e2, pow_succ, pow_succ, hVrec]
      ring

theorem lucasU_double (P Q : ℤ) (k : ℕ) :
    lucasU P Q (2 * k) = lucasU P Q k * lucasV P Q k := by
  have := lucasU_add P Q k k le_rfl
  simpa [two_mul, Nat.sub_self] using this

theorem lucasV_double (P Q : ℤ) (k : ℕ) :
    lucasV P Q (2 * k) = lucasV P Q k ^ 2 - 2 * Q ^ k := by
  rw [two_mul]
  have h := lucasV_add P Q k k le_rfl
  rw [h, Nat.sub_self, lucasV_zero, pow_two]
  ring

theorem lucasU_triple (P Q : ℤ) (k : ℕ) :
    lucasU P Q (3 * k) = lucasU P Q k * (lucasV P Q k ^ 2 - Q ^ k) := by
  have h2 : 2 * k = k + k := by omega
  have h3 : 3 * k = 2 * k + k := by omega
  have hle : k ≤ 2 * k := by omega
  have hadd := lucasU_add P Q (2 * k) k hle
  have h2n := lucasU_double P Q k
  have hsub : 2 * k - k = k := by omega
  rw [h3, hadd, h2n, hsub]
  ring

theorem lucasV_triple (P Q : ℤ) (k : ℕ) :
    lucasV P Q (3 * k) = lucasV P Q k * (lucasV P Q k ^ 2 - 3 * Q ^ k) := by
  have h3 : 3 * k = 2 * k + k := by omega
  have hle : k ≤ 2 * k := by omega
  have hadd := lucasV_add P Q (2 * k) k hle
  have h2n := lucasV_double P Q k
  have hsub : 2 * k - k = k := by omega
  rw [h3, hadd, h2n, hsub]
  ring

/-- `p ∣ U_{t·r}` if `p ∣ U_r`. -/
theorem lucasU_dvd_mul_index (P Q : ℤ) {p r : ℕ}
    (hr : (p : ℤ) ∣ lucasU P Q r) :
    ∀ t : ℕ, (p : ℤ) ∣ lucasU P Q (t * r) := by
  intro t
  have step : ∀ t, (p : ℤ) ∣ lucasU P Q (t * r) ∧ (p : ℤ) ∣ lucasU P Q ((t + 1) * r) := by
    intro t
    induction t with
    | zero =>
      exact ⟨by simp, by simpa using hr⟩
    | succ t ih =>
      refine ⟨ih.2, ?_⟩
      have hle : r ≤ (t + 1) * r := Nat.le_mul_of_pos_left r (Nat.succ_pos _)
      have hadd := lucasU_add P Q ((t + 1) * r) r hle
      have hidx : (t + 1 + 1) * r = (t + 1) * r + r := by ring
      have hidx2 : (t + 1) * r - r = t * r := by
        have h1 : (t + 1) * r = t * r + r := by ring
        rw [h1, Nat.add_sub_cancel]
      rw [hidx, hadd, hidx2]
      exact dvd_sub (ih.2.mul_right _) (ih.1.mul_left _)
  exact (step t).1

/-- If the rank exists, then `p ∣ U_n` iff the rank divides `n`. -/
theorem lucasRank_dvd_iff (P Q : ℤ) {p n : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hQ : ¬(p : ℤ) ∣ Q)
    (hex : ∃ k > 0, (p : ℤ) ∣ lucasU P Q k) :
    (p : ℤ) ∣ lucasU P Q n ↔ lucasRank P Q p ∣ n := by
  constructor
  · intro hn
    set z := lucasRank P Q p
    have hzpos : 0 < z := lucasRank_pos P Q hex
    have hzU : (p : ℤ) ∣ lucasU P Q z := lucasRank_dvd_U P Q hex
    have hgcd : (p : ℤ) ∣ lucasU P Q (Nat.gcd z n) :=
      lucasU_dvd_gcd P Q hp hodd hQ z n hzU hn
    have hgcdpos : 0 < Nat.gcd z n := Nat.gcd_pos_of_pos_left n hzpos
    have hle : z ≤ Nat.gcd z n := lucasRank_le_of_dvd P Q hgcdpos hgcd
    have hge : Nat.gcd z n ≤ z := Nat.gcd_le_left n hzpos
    have heq : Nat.gcd z n = z := le_antisymm hge hle
    have : Nat.gcd z n ∣ n := Nat.gcd_dvd_right z n
    rwa [heq] at this
  · intro hdiv
    obtain ⟨t, ht⟩ := hdiv
    rw [ht, mul_comm]
    exact lucasU_dvd_mul_index P Q (lucasRank_dvd_U P Q hex) t

/-- Combined law of appearance: an odd prime `p ∤ QD` divides `U_{p-1}` or `U_{p+1}`. -/
theorem lucas_appearance (P Q : ℤ) {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hD : ¬(p : ℤ) ∣ lucasD P Q) (hQ : ¬(p : ℤ) ∣ Q) :
    (p : ℤ) ∣ lucasU P Q (p - 1) ∨ (p : ℤ) ∣ lucasU P Q (p + 1) := by
  have hp := Fact.out (p := p.Prime)
  have hne : (lucasD P Q : ZMod p) ≠ 0 := by
    intro h
    exact hD ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h)
  rcases legendreSym.eq_one_or_neg_one (p := p) hne with h1 | hneg
  · exact Or.inl (lucas_appearance_one P Q hodd h1 hQ)
  · exact Or.inr (lucas_appearance_neg_one P Q hodd hneg)

/-- The rank of apparition exists and is at most `p+1`. -/
theorem lucasRank_le_succ (P Q : ℤ) {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hD : ¬(p : ℤ) ∣ lucasD P Q) (hQ : ¬(p : ℤ) ∣ Q) :
    ∃ k > 0, (p : ℤ) ∣ lucasU P Q k ∧ k ≤ p + 1 := by
  have hp := Fact.out (p := p.Prime)
  rcases lucas_appearance P Q hodd hD hQ with h | h
  · refine ⟨p - 1, ?_, h, ?_⟩
    · have : 1 < p := hp.one_lt
      omega
    · omega
  · exact ⟨p + 1, Nat.succ_pos _, h, le_rfl⟩

/-- If `d ∣ N`, `0 < d`, and `d` divides none of the `N/q` for primes `q ∣ N`, then `d = N`. -/
theorem eq_of_dvd_of_not_dvd_div {d N : ℕ} (hdpos : 0 < d) (hdvd : d ∣ N)
    (h : ∀ q : ℕ, q.Prime → q ∣ N → ¬ d ∣ N / q) : d = N := by
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    subst N
    have := h 2 Nat.prime_two (dvd_zero _)
    exact this (dvd_zero _)
  have hk1 : k = 1 := by
    by_contra hk1
    have ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hk1
    have hqN : q ∣ N := by
      rw [hk]
      exact hqd.mul_left d
    have : d ∣ N / q := by
      -- N / q = (d * k) / q = d * (k / q)
      have hqkpos : 0 < q := hq.pos
      have : N / q = d * (k / q) := by
        rw [hk, Nat.mul_div_assoc d hqd]
      rw [this]
      exact dvd_mul_right _ _
    exact h q hq hqN this
  rw [hk, hk1, mul_one]

/-- Brillhart–Lehmer–Selfridge N+1 primality test (fully factored case). -/
theorem not_prime_dvd_of_gcd_eq_one {p : ℕ} (hp : p.Prime) {a : ℤ} {n : ℕ}
    (hgcd : Int.gcd a n = 1) (hpn : p ∣ n) : ¬(p : ℤ) ∣ a := by
  intro h
  have : p ∣ Int.gcd a n := Int.dvd_gcd h (Int.natCast_dvd_natCast.2 hpn)
  rw [hgcd] at this
  exact hp.ne_one (Nat.dvd_one.1 this)

/-- Brillhart–Lehmer–Selfridge N+1 primality test (fully factored case). -/
theorem lucas_nplus1_primality (n : ℕ) (hn : 2 < n) (hodd : Odd n) (P Q : ℤ)
    (hQ : Int.gcd Q n = 1) (hD : Int.gcd (lucasD P Q) n = 1)
    (hU : (n : ℤ) ∣ lucasU P Q (n + 1))
    (hgcd : ∀ q : ℕ, q.Prime → q ∣ n + 1 →
      Int.gcd (lucasU P Q ((n + 1) / q)) n = 1) :
    n.Prime := by
  have hn1 : 1 < n := lt_trans (by decide : 1 < 2) hn
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hn1)
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := Odd.of_dvd_nat hodd hpn
  have hpQ : ¬(p : ℤ) ∣ Q := not_prime_dvd_of_gcd_eq_one hp hQ hpn
  have hpD : ¬(p : ℤ) ∣ lucasD P Q := not_prime_dvd_of_gcd_eq_one hp hD hpn
  obtain ⟨k0, hk0pos, hk0U, hk0le⟩ := lucasRank_le_succ P Q hpodd hpD hpQ
  have hex : ∃ k > 0, (p : ℤ) ∣ lucasU P Q k := ⟨k0, hk0pos, hk0U⟩
  set z := lucasRank P Q p
  have hzpos : 0 < z := lucasRank_pos P Q hex
  have hzU : (p : ℤ) ∣ lucasU P Q z := lucasRank_dvd_U P Q hex
  have hz_le : z ≤ p + 1 :=
    (lucasRank_le_of_dvd P Q hk0pos hk0U).trans hk0le
  have hp_div_U : (p : ℤ) ∣ lucasU P Q (n + 1) :=
    (Int.natCast_dvd_natCast.2 hpn).trans hU
  have hz_dvd : z ∣ n + 1 :=
    (lucasRank_dvd_iff P Q hp hpodd hpQ hex).1 hp_div_U
  have hz_eq : z = n + 1 := by
    refine eq_of_dvd_of_not_dvd_div hzpos hz_dvd ?_
    intro q hq hqd hdiv
    have hpUq : (p : ℤ) ∣ lucasU P Q ((n + 1) / q) :=
      (lucasRank_dvd_iff P Q hp hpodd hpQ hex).2 hdiv
    have hgc : Int.gcd (lucasU P Q ((n + 1) / q)) n = 1 := hgcd q hq hqd
    have hp_div_n : (p : ℤ) ∣ n := Int.natCast_dvd_natCast.2 hpn
    have : p ∣ Int.gcd (lucasU P Q ((n + 1) / q)) n :=
      Int.dvd_gcd hpUq hp_div_n
    rw [hgc] at this
    exact hp.ne_one (Nat.dvd_one.1 this)
  have : n + 1 ≤ p + 1 := hz_eq ▸ hz_le
  have hpn' : p ≤ n := Nat.le_of_dvd (lt_trans Nat.zero_lt_one hn1) hpn
  have : p = n := le_antisymm hpn' (Nat.succ_le_succ_iff.mp this)
  rwa [← this]

/-! ### Relating `U_k` to the imaginary part of `ω^k` -/

theorem lucasω_im (P Q : ℤ) {k : ℕ} (hk : 1 ≤ k) :
    (lucasω P Q ^ k).im = (2 : ℤ) ^ (k - 1) * lucasU P Q k := by
  rw [lucasω_pow P Q k hk]

theorem lucasω_re (P Q : ℤ) {k : ℕ} (hk : 1 ≤ k) :
    (lucasω P Q ^ k).re = (2 : ℤ) ^ (k - 1) * lucasV P Q k := by
  rw [lucasω_pow P Q k hk]

theorem coprime_two_of_odd {n : ℕ} (h : Odd n) : Nat.Coprime 2 n := by
  rw [Nat.prime_two.coprime_iff_not_dvd]
  intro hd
  exact Nat.not_even_iff_odd.2 h (even_iff_two_dvd.2 hd)

theorem odd_dvd_two_pow_mul {n : ℕ} (hodd : Odd n) (k : ℕ) (a : ℤ) :
    (n : ℤ) ∣ (2 : ℤ) ^ k * a ↔ (n : ℤ) ∣ a := by
  simp only [Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_pow]
  have hc : Nat.Coprime n (2 ^ k) :=
    ((coprime_two_of_odd hodd).pow_left k).symm
  constructor
  · intro h
    exact hc.dvd_of_dvd_mul_left h
  · intro h
    exact dvd_mul_of_dvd_right h _

theorem odd_gcd_two_pow_mul {n : ℕ} (hodd : Odd n) (k : ℕ) (a : ℤ) :
    Int.gcd ((2 : ℤ) ^ k * a) n = Int.gcd a n := by
  simp only [Int.gcd]
  have : ((2 : ℤ) ^ k * a).natAbs = 2 ^ k * a.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_pow]
    rfl
  rw [this]
  exact Nat.Coprime.gcd_mul_left_cancel a.natAbs ((coprime_two_of_odd hodd).pow_left k)

theorem lucasU_dvd_iff_ω_im (P Q : ℤ) {n k : ℕ} (hk : 1 ≤ k) (hodd : Odd n) :
    (n : ℤ) ∣ lucasU P Q k ↔ (n : ℤ) ∣ (lucasω P Q ^ k).im := by
  rw [lucasω_im P Q hk, odd_dvd_two_pow_mul hodd]

theorem lucasU_gcd_eq_ω_im (P Q : ℤ) {n k : ℕ} (hk : 1 ≤ k) (hodd : Odd n) :
    Int.gcd (lucasU P Q k) n = Int.gcd (lucasω P Q ^ k).im n := by
  rw [lucasω_im P Q hk, odd_gcd_two_pow_mul hodd]

/-! ### Modular arithmetic in `ℤ√D` -/

/-- Multiplication of residue pairs representing elements of `ℤ√D` modulo `N`. -/
def zsqrtMul (N D : ℕ) (x y : ℕ × ℕ) : ℕ × ℕ :=
  ((x.1 * y.1 + D * x.2 * y.2) % N, (x.1 * y.2 + x.2 * y.1) % N)

/-- Cubing a residue pair. -/
def zsqrtCube (N D : ℕ) (x : ℕ × ℕ) : ℕ × ℕ :=
  zsqrtMul N D (zsqrtMul N D x x) x

/-- Iterate cubing `k` times. -/
def zsqrtIterCube (N D : ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, s => s
  | k + 1, s => zsqrtIterCube N D k (zsqrtCube N D s)

/-- Apply `zsqrtCube` exactly `2^k` times. Recursion depth is `k`. -/
def zsqrtIterCube2pow (N D : ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, s => zsqrtCube N D s
  | k + 1, s => zsqrtIterCube2pow N D k (zsqrtIterCube2pow N D k s)

theorem zsqrtIterCube_succ_comm (N D : ℕ) (b : ℕ) (s : ℕ × ℕ) :
    zsqrtCube N D (zsqrtIterCube N D b s) = zsqrtIterCube N D b (zsqrtCube N D s) := by
  induction b generalizing s with
  | zero => rfl
  | succ b ih =>
    simp [zsqrtIterCube]
    exact ih _

theorem zsqrtIterCube_add (N D : ℕ) (a b : ℕ) (s : ℕ × ℕ) :
    zsqrtIterCube N D a (zsqrtIterCube N D b s) = zsqrtIterCube N D (a + b) s := by
  induction a generalizing b s with
  | zero => simp [zsqrtIterCube]
  | succ a ih =>
    simp [zsqrtIterCube]
    rw [zsqrtIterCube_succ_comm, ih]
    rw [show a + 1 + b = a + b + 1 by omega]
    rfl

theorem zsqrtIterCube2pow_eq (N D : ℕ) (k : ℕ) (s : ℕ × ℕ) :
    zsqrtIterCube2pow N D k s = zsqrtIterCube N D (2 ^ k) s := by
  induction k generalizing s with
  | zero => simp [zsqrtIterCube2pow, zsqrtIterCube]
  | succ k ih =>
    simp [zsqrtIterCube2pow]
    rw [ih, ih, zsqrtIterCube_add, ← two_mul, ← pow_succ']

/-- `39101 = 2^15+2^12+2^11+2^7+2^5+2^4+2^3+2^2+1`. -/
def zsqrtIterCube39101 (N D : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  zsqrtCube N D
    (zsqrtIterCube2pow N D 2
      (zsqrtIterCube2pow N D 3
        (zsqrtIterCube2pow N D 4
          (zsqrtIterCube2pow N D 5
            (zsqrtIterCube2pow N D 7
              (zsqrtIterCube2pow N D 11
                (zsqrtIterCube2pow N D 12
                  (zsqrtIterCube2pow N D 15 s))))))))

/-- `39100 = 2^15+2^12+2^11+2^7+2^5+2^4+2^3+2^2`. -/
def zsqrtIterCube39100 (N D : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  zsqrtIterCube2pow N D 2
    (zsqrtIterCube2pow N D 3
      (zsqrtIterCube2pow N D 4
        (zsqrtIterCube2pow N D 5
          (zsqrtIterCube2pow N D 7
            (zsqrtIterCube2pow N D 11
              (zsqrtIterCube2pow N D 12
                (zsqrtIterCube2pow N D 15 s)))))))

theorem zsqrtCube_eq_iter_one (N D s) :
    zsqrtCube N D s = zsqrtIterCube N D 1 s := rfl

theorem zsqrtIterCube39101_eq (N D s) :
    zsqrtIterCube39101 N D s = zsqrtIterCube N D 39101 s := by
  unfold zsqrtIterCube39101
  simp only [zsqrtIterCube2pow_eq, zsqrtCube_eq_iter_one]
  repeat rw [zsqrtIterCube_add]
  norm_num

theorem zsqrtIterCube39100_eq (N D s) :
    zsqrtIterCube39100 N D s = zsqrtIterCube N D 39100 s := by
  unfold zsqrtIterCube39100
  simp only [zsqrtIterCube2pow_eq]
  repeat rw [zsqrtIterCube_add]
  norm_num

theorem nat_mod_int (a N : ℕ) : ((a % N : ℕ) : ℤ) ≡ (a : ℤ) [ZMOD N] := by
  rw [Int.natCast_mod]
  exact Int.mod_modEq _ _

theorem zsqrtMul_spec (N D : ℕ) (x y : ℤ√(D : ℤ)) (xr xi yr yi : ℕ)
    (hxr : (xr : ℤ) ≡ x.re [ZMOD N]) (hxi : (xi : ℤ) ≡ x.im [ZMOD N])
    (hyr : (yr : ℤ) ≡ y.re [ZMOD N]) (hyi : (yi : ℤ) ≡ y.im [ZMOD N]) :
    ((zsqrtMul N D (xr, xi) (yr, yi)).1 : ℤ) ≡ (x * y).re [ZMOD N] ∧
    ((zsqrtMul N D (xr, xi) (yr, yi)).2 : ℤ) ≡ (x * y).im [ZMOD N] := by
  constructor
  · change ((xr * yr + D * xi * yi) % N : ℕ) ≡ (x * y).re [ZMOD N]
    refine (nat_mod_int _ N).trans ?_
    have hc : ((xr * yr + D * xi * yi : ℕ) : ℤ) =
        (xr : ℤ) * yr + (D : ℤ) * xi * yi := by norm_cast
    rw [hc, Zsqrtd.re_mul]
    have h1 := hxr.mul hyr
    have h2 := (Int.ModEq.refl (D : ℤ)).mul (hxi.mul hyi)
    convert h1.add h2 using 1 <;> ring
  · change ((xr * yi + xi * yr) % N : ℕ) ≡ (x * y).im [ZMOD N]
    refine (nat_mod_int _ N).trans ?_
    have hc : ((xr * yi + xi * yr : ℕ) : ℤ) = (xr : ℤ) * yi + (xi : ℤ) * yr := by
      norm_cast
    rw [hc, Zsqrtd.im_mul]
    exact hxr.mul hyi |>.add (hxi.mul hyr)

theorem zsqrtCube_spec (N D : ℕ) (x : ℤ√(D : ℤ)) (s : ℕ × ℕ)
    (hr : (s.1 : ℤ) ≡ x.re [ZMOD N]) (hi : (s.2 : ℤ) ≡ x.im [ZMOD N]) :
    ((zsqrtCube N D s).1 : ℤ) ≡ (x ^ 3).re [ZMOD N] ∧
    ((zsqrtCube N D s).2 : ℤ) ≡ (x ^ 3).im [ZMOD N] := by
  have hsq := zsqrtMul_spec N D x x s.1 s.2 s.1 s.2 hr hi hr hi
  have hcu := zsqrtMul_spec N D (x * x) x
    (zsqrtMul N D s s).1 (zsqrtMul N D s s).2 s.1 s.2 hsq.1 hsq.2 hr hi
  have hx3 : x ^ 3 = x * x * x := by ring
  rw [hx3, zsqrtCube]
  exact hcu

theorem zsqrtIterCube_spec (N D : ℕ) (x : ℤ√(D : ℤ)) (s : ℕ × ℕ)
    (hr : (s.1 : ℤ) ≡ x.re [ZMOD N]) (hi : (s.2 : ℤ) ≡ x.im [ZMOD N]) :
    ∀ k,
      ((zsqrtIterCube N D k s).1 : ℤ) ≡ (x ^ (3 ^ k)).re [ZMOD N] ∧
      ((zsqrtIterCube N D k s).2 : ℤ) ≡ (x ^ (3 ^ k)).im [ZMOD N] := by
  intro k
  induction k generalizing x s with
  | zero =>
    simpa [zsqrtIterCube, pow_zero, pow_one] using And.intro hr hi
  | succ k ih =>
    have hc := zsqrtCube_spec N D x s hr hi
    have ih' := ih (x ^ 3) (zsqrtCube N D s) hc.1 hc.2
    have hpow : (x ^ 3) ^ (3 ^ k) = x ^ (3 ^ (k + 1)) := by
      rw [← pow_mul, show 3 * 3 ^ k = 3 ^ (k + 1) from (pow_succ' 3 k).symm]
    rw [hpow] at ih'
    simpa [zsqrtIterCube] using ih'

theorem dvd_iff_of_modEq {a : ℤ} {r n : ℕ} (h : a ≡ (r : ℤ) [ZMOD n]) :
    (n : ℤ) ∣ a ↔ (n : ℤ) ∣ (r : ℤ) := by
  have hd : (n : ℤ) ∣ a - r := Int.modEq_iff_dvd.1 h.symm
  constructor
  · intro ha
    have := dvd_sub ha hd
    simpa using this
  · intro hr
    have := dvd_add hr hd
    simpa using this

theorem nat_dvd_of_lt {r n : ℕ} (hr : r < n) : n ∣ r ↔ r = 0 := by
  constructor
  · intro h
    exact Nat.eq_zero_of_dvd_of_lt h hr
  · rintro rfl
    exact dvd_zero n

theorem Int.gcd_eq_gcd_of_modEq {a : ℤ} {r n : ℕ} (h : a ≡ (r : ℤ) [ZMOD n]) :
    Int.gcd a n = Nat.gcd r n := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.1 h.symm
  have ha : a = (r : ℤ) + n * k := by linarith
  rw [ha, Int.gcd_add_mul_left_left]
  simp [Int.gcd_natCast_natCast]

/-- Residue pair `s` represents `x^e` in `ℤ√D` modulo `N`. -/
def zsqrtRep (N D : ℕ) (s : ℕ × ℕ) (x : ℤ√(D : ℤ)) (e : ℕ) : Prop :=
  (s.1 : ℤ) ≡ (x ^ e).re [ZMOD N] ∧ (s.2 : ℤ) ≡ (x ^ e).im [ZMOD N]

theorem zsqrtRep_one {N D : ℕ} {s : ℕ × ℕ} {x : ℤ√(D : ℤ)}
    (hr : (s.1 : ℤ) ≡ x.re [ZMOD N]) (hi : (s.2 : ℤ) ≡ x.im [ZMOD N]) :
    zsqrtRep N D s x 1 := by
  simpa [zsqrtRep, pow_one] using And.intro hr hi

theorem zsqrtRep_mul {N D : ℕ} {s t : ℕ × ℕ} {x : ℤ√(D : ℤ)} {a b : ℕ}
    (hs : zsqrtRep N D s x a) (ht : zsqrtRep N D t x b) :
    zsqrtRep N D (zsqrtMul N D s t) x (a + b) := by
  have h := zsqrtMul_spec N D (x ^ a) (x ^ b) s.1 s.2 t.1 t.2 hs.1 hs.2 ht.1 ht.2
  simpa [zsqrtRep, pow_add] using h

theorem zsqrtRep_sq {N D : ℕ} {s : ℕ × ℕ} {x : ℤ√(D : ℤ)} {a : ℕ}
    (hs : zsqrtRep N D s x a) :
    zsqrtRep N D (zsqrtMul N D s s) x (2 * a) := by
  have h := zsqrtRep_mul hs hs
  simpa [two_mul] using h

theorem zsqrtRep_iterCube {N D : ℕ} {s : ℕ × ℕ} {x : ℤ√(D : ℤ)}
    (hs : zsqrtRep N D s x 1) (k : ℕ) :
    zsqrtRep N D (zsqrtIterCube N D k s) x (3 ^ k) := by
  have hr : (s.1 : ℤ) ≡ x.re [ZMOD N] := by simpa [pow_one] using hs.1
  have hi : (s.2 : ℤ) ≡ x.im [ZMOD N] := by simpa [pow_one] using hs.2
  exact zsqrtIterCube_spec N D x s hr hi k

theorem zsqrtRep_iterCube_mul {N D : ℕ} {s : ℕ × ℕ} {x : ℤ√(D : ℤ)} {e k : ℕ}
    (hs : zsqrtRep N D s x e) :
    zsqrtRep N D (zsqrtIterCube N D k s) x (e * 3 ^ k) := by
  have hs1 : zsqrtRep N D s (x ^ e) 1 := by
    simpa [zsqrtRep, pow_one] using hs
  have h := zsqrtRep_iterCube (x := x ^ e) hs1 k
  simpa [zsqrtRep, pow_mul] using h

@[simp] theorem lucasω_six_three : lucasω 6 3 = ⟨6, 1⟩ := rfl

theorem lucasD_six_three : lucasD 6 3 = 24 := by
  simp [lucasD]

theorem zsqrtRep_start (N : ℕ) :
    zsqrtRep N 24 (6, 1) (lucasω 6 3) 1 := by
  refine zsqrtRep_one ?_ ?_
  · simp [lucasω]
  · simp [lucasω]

/-- `100943 = 2^16+2^15+2^11+2^9+2^6+2^3+2^2+2+1`. -/
def zsqrtPow100943 (N D : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  let b1 := zsqrtMul N D s s
  let b2 := zsqrtMul N D b1 b1
  let b3 := zsqrtMul N D b2 b2
  let b4 := zsqrtMul N D b3 b3
  let b5 := zsqrtMul N D b4 b4
  let b6 := zsqrtMul N D b5 b5
  let b7 := zsqrtMul N D b6 b6
  let b8 := zsqrtMul N D b7 b7
  let b9 := zsqrtMul N D b8 b8
  let b10 := zsqrtMul N D b9 b9
  let b11 := zsqrtMul N D b10 b10
  let b12 := zsqrtMul N D b11 b11
  let b13 := zsqrtMul N D b12 b12
  let b14 := zsqrtMul N D b13 b13
  let b15 := zsqrtMul N D b14 b14
  let b16 := zsqrtMul N D b15 b15
  zsqrtMul N D b16 (zsqrtMul N D b15 (zsqrtMul N D b11 (zsqrtMul N D b9
    (zsqrtMul N D b6 (zsqrtMul N D b3 (zsqrtMul N D b2 (zsqrtMul N D b1 s)))))))

private theorem zsqrtRep_sq_pow {N D : ℕ} {s : ℕ × ℕ} {x : ℤ√(D : ℤ)} {a k : ℕ}
    (hs : zsqrtRep N D s x (2 ^ k * a)) :
    zsqrtRep N D (zsqrtMul N D s s) x (2 ^ (k + 1) * a) := by
  have h := zsqrtRep_sq hs
  have eq : 2 * (2 ^ k * a) = 2 ^ (k + 1) * a := by
    rw [pow_succ]; ring
  rwa [eq] at h

theorem zsqrtPow100943_spec {N D : ℕ} {s : ℕ × ℕ} {x : ℤ√(D : ℤ)} {a : ℕ}
    (hs : zsqrtRep N D s x a) :
    zsqrtRep N D (zsqrtPow100943 N D s) x (100943 * a) := by
  have h0 : zsqrtRep N D s x (2 ^ 0 * a) := by simpa using hs
  have h1 := zsqrtRep_sq_pow (k := 0) h0
  have h2 := zsqrtRep_sq_pow (k := 1) h1
  have h3 := zsqrtRep_sq_pow (k := 2) h2
  have h4 := zsqrtRep_sq_pow (k := 3) h3
  have h5 := zsqrtRep_sq_pow (k := 4) h4
  have h6 := zsqrtRep_sq_pow (k := 5) h5
  have h7 := zsqrtRep_sq_pow (k := 6) h6
  have h8 := zsqrtRep_sq_pow (k := 7) h7
  have h9 := zsqrtRep_sq_pow (k := 8) h8
  have h10 := zsqrtRep_sq_pow (k := 9) h9
  have h11 := zsqrtRep_sq_pow (k := 10) h10
  have h12 := zsqrtRep_sq_pow (k := 11) h11
  have h13 := zsqrtRep_sq_pow (k := 12) h12
  have h14 := zsqrtRep_sq_pow (k := 13) h13
  have h15 := zsqrtRep_sq_pow (k := 14) h14
  have h16 := zsqrtRep_sq_pow (k := 15) h15
  have p1 := zsqrtRep_mul h1 h0
  have p2 := zsqrtRep_mul h2 p1
  have p3 := zsqrtRep_mul h3 p2
  have p6 := zsqrtRep_mul h6 p3
  have p9 := zsqrtRep_mul h9 p6
  have p11 := zsqrtRep_mul h11 p9
  have p15 := zsqrtRep_mul h15 p11
  have p16 := zsqrtRep_mul h16 p15
  have hexp :
      2 ^ 16 * a + (2 ^ 15 * a + (2 ^ 11 * a + (2 ^ 9 * a + (2 ^ 6 * a +
        (2 ^ 3 * a + (2 ^ 2 * a + (2 ^ 1 * a + 2 ^ 0 * a))))))) =
      100943 * a := by
    have : (2 : ℕ) ^ 16 + 2 ^ 15 + 2 ^ 11 + 2 ^ 9 + 2 ^ 6 + 2 ^ 3 + 2 ^ 2 + 2 ^ 1 + 2 ^ 0 =
        100943 := by decide
    nlinarith
  rw [← hexp]
  simpa [zsqrtPow100943] using p16
