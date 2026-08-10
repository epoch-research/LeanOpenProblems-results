import FormalConjectures.Util.ProblemImports

/--
A248802: Smallest prime factor of $2^{(2^n+2)} + 3$.
-/
def a (n : ℕ) : ℕ := (2 ^ (2 ^ n + 2) + 3).minFac

-- Helper definitions for the "covered" conditions based on the index k, where k = 58*n + 26.

/-- An index k is covered by Conjecture 1 if k = 10m + 2 for some m >= 0, predicting a(k)=67. -/
def covered_by_C1 (k : ℕ) : Prop := ∃ m : ℕ, k = 10 * m + 2

/-- An index k is covered by Conjecture 2 if k = 36m + 16 for some m >= 0, and m is not 1 mod 5, predicting a(k)=271. -/
def covered_by_C2 (k : ℕ) : Prop := ∃ m : ℕ, k = 36 * m + 16 ∧ m % 5 ≠ 1

/-- An index k is covered by Conjecture 3 if k = 84m + 22 for some m >= 0, and m is not 0 mod 5, predicting a(k)=523. -/
def covered_by_C3 (k : ℕ) : Prop := ∃ m : ℕ, k = 84 * m + 22 ∧ m % 5 ≠ 0

set_option maxHeartbeats 20000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 200000

lemma pow_modEq_of_mul_period (M A c : ℕ)
    (hstep : (2 : ℕ) ^ c * 2 ^ A ≡ 2 ^ c [MOD M]) :
    ∀ t : ℕ, (2 : ℕ) ^ (A * t + c) ≡ 2 ^ c [MOD M] := by
  intro t
  induction t with
  | zero => simp [Nat.ModEq.refl]
  | succ t ih =>
      have hpow : (2 : ℕ) ^ (A * (t + 1) + c) = 2 ^ (A * t + c) * 2 ^ A := by
        rw [← pow_add]
        congr 1
        ring
      rw [hpow]
      exact (ih.mul (Nat.ModEq.refl (2 ^ A))).trans hstep

def cOf (r : ℕ) : ℕ := 58 * r + 26

def eResid (q r : ℕ) : ℕ := ((2 : ℕ) ^ cOf r + 2) % (q - 1)

lemma dvd_imp_residue_zero (q T n : ℕ) (hT : 0 < T)
    (hbase : (2 : ℕ) ^ (q - 1) ≡ 1 [MOD q])
    (hstep : ∀ r : Fin T, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * T) ≡ 2 ^ cOf r.val [MOD q - 1])
    (hdiv : q ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3) :
    (2 ^ eResid q (n % T) + 3) % q = 0 := by
  let r := n % T
  have hrlt : r < T := Nat.mod_lt n hT
  let E := 2 ^ (58 * n + 26)
  have hn : n = T * (n / T) + r := by
    have hd : T * (n / T) + n % T = n := Nat.div_add_mod n T
    omega
  have hk : 58 * n + 26 = 58 * T * (n / T) + cOf r := by
    calc
      58 * n + 26 = 58 * (T * (n / T) + r) + 26 := by conv_lhs => rw [hn]
      _ = 58 * T * (n / T) + cOf r := by simp [cOf]; ring
  have hinner : E ≡ 2 ^ cOf r [MOD q - 1] := by
    change 2 ^ (58 * n + 26) ≡ 2 ^ cOf r [MOD q - 1]
    rw [hk]
    exact pow_modEq_of_mul_period (q - 1) (58 * T) (cOf r) (hstep ⟨r, hrlt⟩) (n / T)
  have hXmod : (E + 2) % (q - 1) = eResid q r := by
    have hx := hinner.add (Nat.ModEq.refl 2)
    simpa [Nat.ModEq, eResid] using hx
  have hdecomp : E + 2 = (q - 1) * ((E + 2) / (q - 1)) + eResid q r := by
    have hd : (q - 1) * ((E + 2) / (q - 1)) + (E + 2) % (q - 1) = E + 2 := Nat.div_add_mod (E + 2) (q - 1)
    omega
  have hpow : 2 ^ (E + 2) ≡ 2 ^ eResid q r [MOD q] := by
    rw [hdecomp]
    rw [show 2 ^ ((q - 1) * ((E + 2) / (q - 1)) + eResid q r) =
        (2 ^ (q - 1)) ^ ((E + 2) / (q - 1)) * 2 ^ eResid q r by
      rw [← pow_mul, ← pow_add]]
    have h1 : (2 ^ (q - 1)) ^ ((E + 2) / (q - 1)) ≡ 1 ^ ((E + 2) / (q - 1)) [MOD q] := hbase.pow _
    simpa using h1.mul (Nat.ModEq.refl (2 ^ eResid q r))
  have hzero : 2 ^ (E + 2) + 3 ≡ 0 [MOD q] := by
    exact Nat.modEq_zero_iff_dvd.mpr hdiv
  have hconst : 2 ^ eResid q r + 3 ≡ 0 [MOD q] := by
    exact (hpow.add (Nat.ModEq.refl 3)).symm.trans hzero
  simpa [Nat.ModEq] using hconst

lemma mod233_for_1399 (n : ℕ) : 2 ^ (58 * n + 26) % 233 = 204 := by
  have h58 : (2 ^ 58 : ℕ) ≡ 1 [MOD 233] := by norm_num [Nat.ModEq]
  have h58n : (2 ^ 58 : ℕ) ^ n ≡ 1 ^ n [MOD 233] := h58.pow n
  have h26 : (2 ^ 26 : ℕ) ≡ 204 [MOD 233] := by norm_num [Nat.ModEq]
  have hmul := h58n.mul h26
  have hpoweq : (2 ^ 58 : ℕ) ^ n * 2 ^ 26 = 2 ^ (58 * n + 26) := by rw [← pow_mul, ← pow_add]
  rw [hpoweq] at hmul
  simpa [Nat.ModEq] using hmul

lemma dvd1399_main (n : ℕ) : 1399 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  let E := 2 ^ (58 * n + 26)
  have hE : E % 233 = 204 := by simpa [E] using mod233_for_1399 n
  have hdecomp : E + 2 = 233 * (E / 233) + 206 := by
    have hd : 233 * (E / 233) + E % 233 = E := Nat.div_add_mod E 233
    omega
  have hbase : (2 ^ 233 : ℕ) ≡ 1 [MOD 1399] := by norm_num [Nat.ModEq]
  have hpow : 2 ^ (E + 2) ≡ 2 ^ 206 [MOD 1399] := by
    rw [hdecomp]
    rw [show 2 ^ (233 * (E / 233) + 206) = (2 ^ 233) ^ (E / 233) * 2 ^ 206 by rw [← pow_mul, ← pow_add]]
    have h1 : (2 ^ 233 : ℕ) ^ (E / 233) ≡ 1 ^ (E / 233) [MOD 1399] := hbase.pow (E / 233)
    simpa using h1.mul (Nat.ModEq.refl (2 ^ 206))
  have hsum : 2 ^ (E + 2) + 3 ≡ 0 [MOD 1399] := by
    have htail : 2 ^ 206 + 3 ≡ 0 [MOD 1399] := by norm_num [Nat.ModEq]
    exact (hpow.add (Nat.ModEq.refl 3)).trans htail
  rw [Nat.dvd_iff_mod_eq_zero]
  simpa [Nat.ModEq] using hsum

lemma no_dvd_2 (n : ℕ) : ¬ 2 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  let e := 2 ^ (58 * n + 26) + 2
  have he : 1 ≤ e := by simp [e]
  have hd : 2 ∣ 2 ^ e := by exact pow_dvd_pow 2 he
  have hone : 2 ^ e + 3 ≡ 1 [MOD 2] := by
    have h0 : 2 ^ e ≡ 0 [MOD 2] := Nat.modEq_zero_iff_dvd.mpr hd
    have h3 : (3 : ℕ) ≡ 1 [MOD 2] := by norm_num [Nat.ModEq]
    simpa using h0.add h3
  have hzero : 2 ^ e + 3 ≡ 0 [MOD 2] := Nat.modEq_zero_iff_dvd.mpr h
  have : (1 : ℕ) ≡ 0 [MOD 2] := hone.symm.trans hzero
  norm_num [Nat.ModEq] at this

lemma no_dvd_3 (n : ℕ) : ¬ 3 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 1, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 1) ≡ 2 ^ cOf r.val [MOD 3 - 1] := by decide
  have hz := dvd_imp_residue_zero 3 1 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 1, (2 ^ eResid 3 r.val + 3) % 3 ≠ 0 := by decide
  exact (hbad ⟨n % 1, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_5 (n : ℕ) : ¬ 5 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 1, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 1) ≡ 2 ^ cOf r.val [MOD 5 - 1] := by decide
  have hz := dvd_imp_residue_zero 5 1 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 1, (2 ^ eResid 5 r.val + 3) % 5 ≠ 0 := by decide
  exact (hbad ⟨n % 1, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_7 (n : ℕ) : ¬ 7 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 1, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 1) ≡ 2 ^ cOf r.val [MOD 7 - 1] := by decide
  have hz := dvd_imp_residue_zero 7 1 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 1, (2 ^ eResid 7 r.val + 3) % 7 ≠ 0 := by decide
  exact (hbad ⟨n % 1, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_11 (n : ℕ) : ¬ 11 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 2, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 2) ≡ 2 ^ cOf r.val [MOD 11 - 1] := by decide
  have hz := dvd_imp_residue_zero 11 2 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 2, (2 ^ eResid 11 r.val + 3) % 11 ≠ 0 := by decide
  exact (hbad ⟨n % 2, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_13 (n : ℕ) : ¬ 13 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 1, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 1) ≡ 2 ^ cOf r.val [MOD 13 - 1] := by decide
  have hz := dvd_imp_residue_zero 13 1 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 1, (2 ^ eResid 13 r.val + 3) % 13 ≠ 0 := by decide
  exact (hbad ⟨n % 1, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_17 (n : ℕ) : ¬ 17 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 1, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 1) ≡ 2 ^ cOf r.val [MOD 17 - 1] := by decide
  have hz := dvd_imp_residue_zero 17 1 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 1, (2 ^ eResid 17 r.val + 3) % 17 ≠ 0 := by decide
  exact (hbad ⟨n % 1, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_19 (n : ℕ) : ¬ 19 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 3, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 3) ≡ 2 ^ cOf r.val [MOD 19 - 1] := by decide
  have hz := dvd_imp_residue_zero 19 3 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 3, (2 ^ eResid 19 r.val + 3) % 19 ≠ 0 := by decide
  exact (hbad ⟨n % 3, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_23 (n : ℕ) : ¬ 23 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 5, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 5) ≡ 2 ^ cOf r.val [MOD 23 - 1] := by decide
  have hz := dvd_imp_residue_zero 23 5 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 5, (2 ^ eResid 23 r.val + 3) % 23 ≠ 0 := by decide
  exact (hbad ⟨n % 5, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_29 (n : ℕ) : ¬ 29 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 3, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 3) ≡ 2 ^ cOf r.val [MOD 29 - 1] := by decide
  have hz := dvd_imp_residue_zero 29 3 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 3, (2 ^ eResid 29 r.val + 3) % 29 ≠ 0 := by decide
  exact (hbad ⟨n % 3, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_31 (n : ℕ) : ¬ 31 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 2, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 2) ≡ 2 ^ cOf r.val [MOD 31 - 1] := by decide
  have hz := dvd_imp_residue_zero 31 2 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 2, (2 ^ eResid 31 r.val + 3) % 31 ≠ 0 := by decide
  exact (hbad ⟨n % 2, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_37 (n : ℕ) : ¬ 37 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 3, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 3) ≡ 2 ^ cOf r.val [MOD 37 - 1] := by decide
  have hz := dvd_imp_residue_zero 37 3 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 3, (2 ^ eResid 37 r.val + 3) % 37 ≠ 0 := by decide
  exact (hbad ⟨n % 3, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_41 (n : ℕ) : ¬ 41 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 2, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 2) ≡ 2 ^ cOf r.val [MOD 41 - 1] := by decide
  have hz := dvd_imp_residue_zero 41 2 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 2, (2 ^ eResid 41 r.val + 3) % 41 ≠ 0 := by decide
  exact (hbad ⟨n % 2, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_43 (n : ℕ) : ¬ 43 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 3, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 3) ≡ 2 ^ cOf r.val [MOD 43 - 1] := by decide
  have hz := dvd_imp_residue_zero 43 3 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 3, (2 ^ eResid 43 r.val + 3) % 43 ≠ 0 := by decide
  exact (hbad ⟨n % 3, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_47 (n : ℕ) : ¬ 47 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 11, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 11) ≡ 2 ^ cOf r.val [MOD 47 - 1] := by decide
  have hz := dvd_imp_residue_zero 47 11 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 11, (2 ^ eResid 47 r.val + 3) % 47 ≠ 0 := by decide
  exact (hbad ⟨n % 11, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_53 (n : ℕ) : ¬ 53 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 6, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 6) ≡ 2 ^ cOf r.val [MOD 53 - 1] := by decide
  have hz := dvd_imp_residue_zero 53 6 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 6, (2 ^ eResid 53 r.val + 3) % 53 ≠ 0 := by decide
  exact (hbad ⟨n % 6, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_59 (n : ℕ) : ¬ 59 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 14, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 14) ≡ 2 ^ cOf r.val [MOD 59 - 1] := by decide
  have hz := dvd_imp_residue_zero 59 14 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 14, (2 ^ eResid 59 r.val + 3) % 59 ≠ 0 := by decide
  exact (hbad ⟨n % 14, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_61 (n : ℕ) : ¬ 61 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 2, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 2) ≡ 2 ^ cOf r.val [MOD 61 - 1] := by decide
  have hz := dvd_imp_residue_zero 61 2 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 2, (2 ^ eResid 61 r.val + 3) % 61 ≠ 0 := by decide
  exact (hbad ⟨n % 2, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_71 (n : ℕ) : ¬ 71 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 6, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 6) ≡ 2 ^ cOf r.val [MOD 71 - 1] := by decide
  have hz := dvd_imp_residue_zero 71 6 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 6, (2 ^ eResid 71 r.val + 3) % 71 ≠ 0 := by decide
  exact (hbad ⟨n % 6, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_73 (n : ℕ) : ¬ 73 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 3, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 3) ≡ 2 ^ cOf r.val [MOD 73 - 1] := by decide
  have hz := dvd_imp_residue_zero 73 3 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 3, (2 ^ eResid 73 r.val + 3) % 73 ≠ 0 := by decide
  exact (hbad ⟨n % 3, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_79 (n : ℕ) : ¬ 79 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 6, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 6) ≡ 2 ^ cOf r.val [MOD 79 - 1] := by decide
  have hz := dvd_imp_residue_zero 79 6 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 6, (2 ^ eResid 79 r.val + 3) % 79 ≠ 0 := by decide
  exact (hbad ⟨n % 6, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_83 (n : ℕ) : ¬ 83 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 10, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 10) ≡ 2 ^ cOf r.val [MOD 83 - 1] := by decide
  have hz := dvd_imp_residue_zero 83 10 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 10, (2 ^ eResid 83 r.val + 3) % 83 ≠ 0 := by decide
  exact (hbad ⟨n % 10, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_89 (n : ℕ) : ¬ 89 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 5, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 5) ≡ 2 ^ cOf r.val [MOD 89 - 1] := by decide
  have hz := dvd_imp_residue_zero 89 5 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 5, (2 ^ eResid 89 r.val + 3) % 89 ≠ 0 := by decide
  exact (hbad ⟨n % 5, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_97 (n : ℕ) : ¬ 97 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 1, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 1) ≡ 2 ^ cOf r.val [MOD 97 - 1] := by decide
  have hz := dvd_imp_residue_zero 97 1 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 1, (2 ^ eResid 97 r.val + 3) % 97 ≠ 0 := by decide
  exact (hbad ⟨n % 1, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_101 (n : ℕ) : ¬ 101 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 10, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 10) ≡ 2 ^ cOf r.val [MOD 101 - 1] := by decide
  have hz := dvd_imp_residue_zero 101 10 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 10, (2 ^ eResid 101 r.val + 3) % 101 ≠ 0 := by decide
  exact (hbad ⟨n % 10, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_103 (n : ℕ) : ¬ 103 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 4, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 4) ≡ 2 ^ cOf r.val [MOD 103 - 1] := by decide
  have hz := dvd_imp_residue_zero 103 4 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 4, (2 ^ eResid 103 r.val + 3) % 103 ≠ 0 := by decide
  exact (hbad ⟨n % 4, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_107 (n : ℕ) : ¬ 107 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 26, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 26) ≡ 2 ^ cOf r.val [MOD 107 - 1] := by decide
  have hz := dvd_imp_residue_zero 107 26 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 26, (2 ^ eResid 107 r.val + 3) % 107 ≠ 0 := by decide
  exact (hbad ⟨n % 26, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_109 (n : ℕ) : ¬ 109 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 9, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 9) ≡ 2 ^ cOf r.val [MOD 109 - 1] := by decide
  have hz := dvd_imp_residue_zero 109 9 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 9, (2 ^ eResid 109 r.val + 3) % 109 ≠ 0 := by decide
  exact (hbad ⟨n % 9, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_113 (n : ℕ) : ¬ 113 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 3, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 3) ≡ 2 ^ cOf r.val [MOD 113 - 1] := by decide
  have hz := dvd_imp_residue_zero 113 3 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 3, (2 ^ eResid 113 r.val + 3) % 113 ≠ 0 := by decide
  exact (hbad ⟨n % 3, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_127 (n : ℕ) : ¬ 127 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 3, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 3) ≡ 2 ^ cOf r.val [MOD 127 - 1] := by decide
  have hz := dvd_imp_residue_zero 127 3 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 3, (2 ^ eResid 127 r.val + 3) % 127 ≠ 0 := by decide
  exact (hbad ⟨n % 3, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_131 (n : ℕ) : ¬ 131 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 6, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 6) ≡ 2 ^ cOf r.val [MOD 131 - 1] := by decide
  have hz := dvd_imp_residue_zero 131 6 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 6, (2 ^ eResid 131 r.val + 3) % 131 ≠ 0 := by decide
  exact (hbad ⟨n % 6, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_137 (n : ℕ) : ¬ 137 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 4, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 4) ≡ 2 ^ cOf r.val [MOD 137 - 1] := by decide
  have hz := dvd_imp_residue_zero 137 4 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 4, (2 ^ eResid 137 r.val + 3) % 137 ≠ 0 := by decide
  exact (hbad ⟨n % 4, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_139 (n : ℕ) : ¬ 139 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 11, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 11) ≡ 2 ^ cOf r.val [MOD 139 - 1] := by decide
  have hz := dvd_imp_residue_zero 139 11 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 11, (2 ^ eResid 139 r.val + 3) % 139 ≠ 0 := by decide
  exact (hbad ⟨n % 11, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_149 (n : ℕ) : ¬ 149 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 18, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 18) ≡ 2 ^ cOf r.val [MOD 149 - 1] := by decide
  have hz := dvd_imp_residue_zero 149 18 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 18, (2 ^ eResid 149 r.val + 3) % 149 ≠ 0 := by decide
  exact (hbad ⟨n % 18, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_151 (n : ℕ) : ¬ 151 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 10, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 10) ≡ 2 ^ cOf r.val [MOD 151 - 1] := by decide
  have hz := dvd_imp_residue_zero 151 10 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 10, (2 ^ eResid 151 r.val + 3) % 151 ≠ 0 := by decide
  exact (hbad ⟨n % 10, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_157 (n : ℕ) : ¬ 157 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 6, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 6) ≡ 2 ^ cOf r.val [MOD 157 - 1] := by decide
  have hz := dvd_imp_residue_zero 157 6 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 6, (2 ^ eResid 157 r.val + 3) % 157 ≠ 0 := by decide
  exact (hbad ⟨n % 6, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_163 (n : ℕ) : ¬ 163 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 27, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 27) ≡ 2 ^ cOf r.val [MOD 163 - 1] := by decide
  have hz := dvd_imp_residue_zero 163 27 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 27, (2 ^ eResid 163 r.val + 3) % 163 ≠ 0 := by decide
  exact (hbad ⟨n % 27, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_167 (n : ℕ) : ¬ 167 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 41, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 41) ≡ 2 ^ cOf r.val [MOD 167 - 1] := by decide
  have hz := dvd_imp_residue_zero 167 41 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 41, (2 ^ eResid 167 r.val + 3) % 167 ≠ 0 := by decide
  exact (hbad ⟨n % 41, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_173 (n : ℕ) : ¬ 173 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 7, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 7) ≡ 2 ^ cOf r.val [MOD 173 - 1] := by decide
  have hz := dvd_imp_residue_zero 173 7 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 7, (2 ^ eResid 173 r.val + 3) % 173 ≠ 0 := by decide
  exact (hbad ⟨n % 7, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_179 (n : ℕ) : ¬ 179 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 11, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 11) ≡ 2 ^ cOf r.val [MOD 179 - 1] := by decide
  have hz := dvd_imp_residue_zero 179 11 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 11, (2 ^ eResid 179 r.val + 3) % 179 ≠ 0 := by decide
  exact (hbad ⟨n % 11, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_181 (n : ℕ) : ¬ 181 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 6, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 6) ≡ 2 ^ cOf r.val [MOD 181 - 1] := by decide
  have hz := dvd_imp_residue_zero 181 6 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 6, (2 ^ eResid 181 r.val + 3) % 181 ≠ 0 := by decide
  exact (hbad ⟨n % 6, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_191 (n : ℕ) : ¬ 191 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 18, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 18) ≡ 2 ^ cOf r.val [MOD 191 - 1] := by decide
  have hz := dvd_imp_residue_zero 191 18 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 18, (2 ^ eResid 191 r.val + 3) % 191 ≠ 0 := by decide
  exact (hbad ⟨n % 18, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_193 (n : ℕ) : ¬ 193 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 1, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 1) ≡ 2 ^ cOf r.val [MOD 193 - 1] := by decide
  have hz := dvd_imp_residue_zero 193 1 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 1, (2 ^ eResid 193 r.val + 3) % 193 ≠ 0 := by decide
  exact (hbad ⟨n % 1, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_197 (n : ℕ) : ¬ 197 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 21, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 21) ≡ 2 ^ cOf r.val [MOD 197 - 1] := by decide
  have hz := dvd_imp_residue_zero 197 21 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 21, (2 ^ eResid 197 r.val + 3) % 197 ≠ 0 := by decide
  exact (hbad ⟨n % 21, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_199 (n : ℕ) : ¬ 199 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 15, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 15) ≡ 2 ^ cOf r.val [MOD 199 - 1] := by decide
  have hz := dvd_imp_residue_zero 199 15 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 15, (2 ^ eResid 199 r.val + 3) % 199 ≠ 0 := by decide
  exact (hbad ⟨n % 15, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_211 (n : ℕ) : ¬ 211 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 6, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 6) ≡ 2 ^ cOf r.val [MOD 211 - 1] := by decide
  have hz := dvd_imp_residue_zero 211 6 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 6, (2 ^ eResid 211 r.val + 3) % 211 ≠ 0 := by decide
  exact (hbad ⟨n % 6, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_223 (n : ℕ) : ¬ 223 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 18, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 18) ≡ 2 ^ cOf r.val [MOD 223 - 1] := by decide
  have hz := dvd_imp_residue_zero 223 18 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 18, (2 ^ eResid 223 r.val + 3) % 223 ≠ 0 := by decide
  exact (hbad ⟨n % 18, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_227 (n : ℕ) : ¬ 227 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 14, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 14) ≡ 2 ^ cOf r.val [MOD 227 - 1] := by decide
  have hz := dvd_imp_residue_zero 227 14 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 14, (2 ^ eResid 227 r.val + 3) % 227 ≠ 0 := by decide
  exact (hbad ⟨n % 14, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_229 (n : ℕ) : ¬ 229 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 9, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 9) ≡ 2 ^ cOf r.val [MOD 229 - 1] := by decide
  have hz := dvd_imp_residue_zero 229 9 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 9, (2 ^ eResid 229 r.val + 3) % 229 ≠ 0 := by decide
  exact (hbad ⟨n % 9, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_233 (n : ℕ) : ¬ 233 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 14, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 14) ≡ 2 ^ cOf r.val [MOD 233 - 1] := by decide
  have hz := dvd_imp_residue_zero 233 14 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 14, (2 ^ eResid 233 r.val + 3) % 233 ≠ 0 := by decide
  exact (hbad ⟨n % 14, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_239 (n : ℕ) : ¬ 239 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 12, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 12) ≡ 2 ^ cOf r.val [MOD 239 - 1] := by decide
  have hz := dvd_imp_residue_zero 239 12 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 12, (2 ^ eResid 239 r.val + 3) % 239 ≠ 0 := by decide
  exact (hbad ⟨n % 12, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_241 (n : ℕ) : ¬ 241 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 2, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 2) ≡ 2 ^ cOf r.val [MOD 241 - 1] := by decide
  have hz := dvd_imp_residue_zero 241 2 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 2, (2 ^ eResid 241 r.val + 3) % 241 ≠ 0 := by decide
  exact (hbad ⟨n % 2, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_251 (n : ℕ) : ¬ 251 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 50, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 50) ≡ 2 ^ cOf r.val [MOD 251 - 1] := by decide
  have hz := dvd_imp_residue_zero 251 50 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 50, (2 ^ eResid 251 r.val + 3) % 251 ≠ 0 := by decide
  exact (hbad ⟨n % 50, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_257 (n : ℕ) : ¬ 257 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 1, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 1) ≡ 2 ^ cOf r.val [MOD 257 - 1] := by decide
  have hz := dvd_imp_residue_zero 257 1 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 1, (2 ^ eResid 257 r.val + 3) % 257 ≠ 0 := by decide
  exact (hbad ⟨n % 1, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_263 (n : ℕ) : ¬ 263 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 65, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 65) ≡ 2 ^ cOf r.val [MOD 263 - 1] := by decide
  have hz := dvd_imp_residue_zero 263 65 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 65, (2 ^ eResid 263 r.val + 3) % 263 ≠ 0 := by decide
  exact (hbad ⟨n % 65, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_269 (n : ℕ) : ¬ 269 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 33, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 33) ≡ 2 ^ cOf r.val [MOD 269 - 1] := by decide
  have hz := dvd_imp_residue_zero 269 33 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 33, (2 ^ eResid 269 r.val + 3) % 269 ≠ 0 := by decide
  exact (hbad ⟨n % 33, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_277 (n : ℕ) : ¬ 277 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 11, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 11) ≡ 2 ^ cOf r.val [MOD 277 - 1] := by decide
  have hz := dvd_imp_residue_zero 277 11 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 11, (2 ^ eResid 277 r.val + 3) % 277 ≠ 0 := by decide
  exact (hbad ⟨n % 11, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_281 (n : ℕ) : ¬ 281 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 6, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 6) ≡ 2 ^ cOf r.val [MOD 281 - 1] := by decide
  have hz := dvd_imp_residue_zero 281 6 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 6, (2 ^ eResid 281 r.val + 3) % 281 ≠ 0 := by decide
  exact (hbad ⟨n % 6, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_283 (n : ℕ) : ¬ 283 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 23, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 23) ≡ 2 ^ cOf r.val [MOD 283 - 1] := by decide
  have hz := dvd_imp_residue_zero 283 23 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 23, (2 ^ eResid 283 r.val + 3) % 283 ≠ 0 := by decide
  exact (hbad ⟨n % 23, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_293 (n : ℕ) : ¬ 293 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 9, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 9) ≡ 2 ^ cOf r.val [MOD 293 - 1] := by decide
  have hz := dvd_imp_residue_zero 293 9 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 9, (2 ^ eResid 293 r.val + 3) % 293 ≠ 0 := by decide
  exact (hbad ⟨n % 9, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_307 (n : ℕ) : ¬ 307 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 12, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 12) ≡ 2 ^ cOf r.val [MOD 307 - 1] := by decide
  have hz := dvd_imp_residue_zero 307 12 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 12, (2 ^ eResid 307 r.val + 3) % 307 ≠ 0 := by decide
  exact (hbad ⟨n % 12, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_311 (n : ℕ) : ¬ 311 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 10, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 10) ≡ 2 ^ cOf r.val [MOD 311 - 1] := by decide
  have hz := dvd_imp_residue_zero 311 10 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 10, (2 ^ eResid 311 r.val + 3) % 311 ≠ 0 := by decide
  exact (hbad ⟨n % 10, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_313 (n : ℕ) : ¬ 313 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 6, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 6) ≡ 2 ^ cOf r.val [MOD 313 - 1] := by decide
  have hz := dvd_imp_residue_zero 313 6 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 6, (2 ^ eResid 313 r.val + 3) % 313 ≠ 0 := by decide
  exact (hbad ⟨n % 6, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_317 (n : ℕ) : ¬ 317 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 39, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 39) ≡ 2 ^ cOf r.val [MOD 317 - 1] := by decide
  have hz := dvd_imp_residue_zero 317 39 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 39, (2 ^ eResid 317 r.val + 3) % 317 ≠ 0 := by decide
  exact (hbad ⟨n % 39, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_331 (n : ℕ) : ¬ 331 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 10, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 10) ≡ 2 ^ cOf r.val [MOD 331 - 1] := by decide
  have hz := dvd_imp_residue_zero 331 10 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 10, (2 ^ eResid 331 r.val + 3) % 331 ≠ 0 := by decide
  exact (hbad ⟨n % 10, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_337 (n : ℕ) : ¬ 337 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 3, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 3) ≡ 2 ^ cOf r.val [MOD 337 - 1] := by decide
  have hz := dvd_imp_residue_zero 337 3 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 3, (2 ^ eResid 337 r.val + 3) % 337 ≠ 0 := by decide
  exact (hbad ⟨n % 3, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_347 (n : ℕ) : ¬ 347 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 86, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 86) ≡ 2 ^ cOf r.val [MOD 347 - 1] := by decide
  have hz := dvd_imp_residue_zero 347 86 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 86, (2 ^ eResid 347 r.val + 3) % 347 ≠ 0 := by decide
  exact (hbad ⟨n % 86, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_349 (n : ℕ) : ¬ 349 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 14, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 14) ≡ 2 ^ cOf r.val [MOD 349 - 1] := by decide
  have hz := dvd_imp_residue_zero 349 14 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 14, (2 ^ eResid 349 r.val + 3) % 349 ≠ 0 := by decide
  exact (hbad ⟨n % 14, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_353 (n : ℕ) : ¬ 353 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 5, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 5) ≡ 2 ^ cOf r.val [MOD 353 - 1] := by decide
  have hz := dvd_imp_residue_zero 353 5 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 5, (2 ^ eResid 353 r.val + 3) % 353 ≠ 0 := by decide
  exact (hbad ⟨n % 5, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_359 (n : ℕ) : ¬ 359 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 89, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 89) ≡ 2 ^ cOf r.val [MOD 359 - 1] := by decide
  have hz := dvd_imp_residue_zero 359 89 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 89, (2 ^ eResid 359 r.val + 3) % 359 ≠ 0 := by decide
  exact (hbad ⟨n % 89, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_367 (n : ℕ) : ¬ 367 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 30, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 30) ≡ 2 ^ cOf r.val [MOD 367 - 1] := by decide
  have hz := dvd_imp_residue_zero 367 30 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 30, (2 ^ eResid 367 r.val + 3) % 367 ≠ 0 := by decide
  exact (hbad ⟨n % 30, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_373 (n : ℕ) : ¬ 373 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 5, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 5) ≡ 2 ^ cOf r.val [MOD 373 - 1] := by decide
  have hz := dvd_imp_residue_zero 373 5 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 5, (2 ^ eResid 373 r.val + 3) % 373 ≠ 0 := by decide
  exact (hbad ⟨n % 5, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_379 (n : ℕ) : ¬ 379 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 9, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 9) ≡ 2 ^ cOf r.val [MOD 379 - 1] := by decide
  have hz := dvd_imp_residue_zero 379 9 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 9, (2 ^ eResid 379 r.val + 3) % 379 ≠ 0 := by decide
  exact (hbad ⟨n % 9, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_383 (n : ℕ) : ¬ 383 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 95, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 95) ≡ 2 ^ cOf r.val [MOD 383 - 1] := by decide
  have hz := dvd_imp_residue_zero 383 95 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 95, (2 ^ eResid 383 r.val + 3) % 383 ≠ 0 := by decide
  exact (hbad ⟨n % 95, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_389 (n : ℕ) : ¬ 389 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 24, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 24) ≡ 2 ^ cOf r.val [MOD 389 - 1] := by decide
  have hz := dvd_imp_residue_zero 389 24 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 24, (2 ^ eResid 389 r.val + 3) % 389 ≠ 0 := by decide
  exact (hbad ⟨n % 24, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_397 (n : ℕ) : ¬ 397 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 15, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 15) ≡ 2 ^ cOf r.val [MOD 397 - 1] := by decide
  have hz := dvd_imp_residue_zero 397 15 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 15, (2 ^ eResid 397 r.val + 3) % 397 ≠ 0 := by decide
  exact (hbad ⟨n % 15, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_401 (n : ℕ) : ¬ 401 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 10, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 10) ≡ 2 ^ cOf r.val [MOD 401 - 1] := by decide
  have hz := dvd_imp_residue_zero 401 10 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 10, (2 ^ eResid 401 r.val + 3) % 401 ≠ 0 := by decide
  exact (hbad ⟨n % 10, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_409 (n : ℕ) : ¬ 409 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 4, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 4) ≡ 2 ^ cOf r.val [MOD 409 - 1] := by decide
  have hz := dvd_imp_residue_zero 409 4 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 4, (2 ^ eResid 409 r.val + 3) % 409 ≠ 0 := by decide
  exact (hbad ⟨n % 4, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_419 (n : ℕ) : ¬ 419 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 45, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 45) ≡ 2 ^ cOf r.val [MOD 419 - 1] := by decide
  have hz := dvd_imp_residue_zero 419 45 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 45, (2 ^ eResid 419 r.val + 3) % 419 ≠ 0 := by decide
  exact (hbad ⟨n % 45, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_421 (n : ℕ) : ¬ 421 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 6, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 6) ≡ 2 ^ cOf r.val [MOD 421 - 1] := by decide
  have hz := dvd_imp_residue_zero 421 6 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 6, (2 ^ eResid 421 r.val + 3) % 421 ≠ 0 := by decide
  exact (hbad ⟨n % 6, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_431 (n : ℕ) : ¬ 431 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 14, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 14) ≡ 2 ^ cOf r.val [MOD 431 - 1] := by decide
  have hz := dvd_imp_residue_zero 431 14 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 14, (2 ^ eResid 431 r.val + 3) % 431 ≠ 0 := by decide
  exact (hbad ⟨n % 14, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_433 (n : ℕ) : ¬ 433 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 9, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 9) ≡ 2 ^ cOf r.val [MOD 433 - 1] := by decide
  have hz := dvd_imp_residue_zero 433 9 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 9, (2 ^ eResid 433 r.val + 3) % 433 ≠ 0 := by decide
  exact (hbad ⟨n % 9, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_439 (n : ℕ) : ¬ 439 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 9, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 9) ≡ 2 ^ cOf r.val [MOD 439 - 1] := by decide
  have hz := dvd_imp_residue_zero 439 9 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 9, (2 ^ eResid 439 r.val + 3) % 439 ≠ 0 := by decide
  exact (hbad ⟨n % 9, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_443 (n : ℕ) : ¬ 443 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 12, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 12) ≡ 2 ^ cOf r.val [MOD 443 - 1] := by decide
  have hz := dvd_imp_residue_zero 443 12 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 12, (2 ^ eResid 443 r.val + 3) % 443 ≠ 0 := by decide
  exact (hbad ⟨n % 12, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_449 (n : ℕ) : ¬ 449 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 3, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 3) ≡ 2 ^ cOf r.val [MOD 449 - 1] := by decide
  have hz := dvd_imp_residue_zero 449 3 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 3, (2 ^ eResid 449 r.val + 3) % 449 ≠ 0 := by decide
  exact (hbad ⟨n % 3, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_457 (n : ℕ) : ¬ 457 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 9, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 9) ≡ 2 ^ cOf r.val [MOD 457 - 1] := by decide
  have hz := dvd_imp_residue_zero 457 9 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 9, (2 ^ eResid 457 r.val + 3) % 457 ≠ 0 := by decide
  exact (hbad ⟨n % 9, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_461 (n : ℕ) : ¬ 461 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 22, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 22) ≡ 2 ^ cOf r.val [MOD 461 - 1] := by decide
  have hz := dvd_imp_residue_zero 461 22 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 22, (2 ^ eResid 461 r.val + 3) % 461 ≠ 0 := by decide
  exact (hbad ⟨n % 22, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_463 (n : ℕ) : ¬ 463 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 15, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 15) ≡ 2 ^ cOf r.val [MOD 463 - 1] := by decide
  have hz := dvd_imp_residue_zero 463 15 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 15, (2 ^ eResid 463 r.val + 3) % 463 ≠ 0 := by decide
  exact (hbad ⟨n % 15, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_467 (n : ℕ) : ¬ 467 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 1, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 1) ≡ 2 ^ cOf r.val [MOD 467 - 1] := by decide
  have hz := dvd_imp_residue_zero 467 1 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 1, (2 ^ eResid 467 r.val + 3) % 467 ≠ 0 := by decide
  exact (hbad ⟨n % 1, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_479 (n : ℕ) : ¬ 479 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 119, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 119) ≡ 2 ^ cOf r.val [MOD 479 - 1] := by decide
  have hz := dvd_imp_residue_zero 479 119 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 119, (2 ^ eResid 479 r.val + 3) % 479 ≠ 0 := by decide
  exact (hbad ⟨n % 119, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_487 (n : ℕ) : ¬ 487 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 81, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 81) ≡ 2 ^ cOf r.val [MOD 487 - 1] := by decide
  have hz := dvd_imp_residue_zero 487 81 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 81, (2 ^ eResid 487 r.val + 3) % 487 ≠ 0 := by decide
  exact (hbad ⟨n % 81, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_491 (n : ℕ) : ¬ 491 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 42, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 42) ≡ 2 ^ cOf r.val [MOD 491 - 1] := by decide
  have hz := dvd_imp_residue_zero 491 42 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 42, (2 ^ eResid 491 r.val + 3) % 491 ≠ 0 := by decide
  exact (hbad ⟨n % 42, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_499 (n : ℕ) : ¬ 499 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 41, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 41) ≡ 2 ^ cOf r.val [MOD 499 - 1] := by decide
  have hz := dvd_imp_residue_zero 499 41 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 41, (2 ^ eResid 499 r.val + 3) % 499 ≠ 0 := by decide
  exact (hbad ⟨n % 41, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_503 (n : ℕ) : ¬ 503 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 25, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 25) ≡ 2 ^ cOf r.val [MOD 503 - 1] := by decide
  have hz := dvd_imp_residue_zero 503 25 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 25, (2 ^ eResid 503 r.val + 3) % 503 ≠ 0 := by decide
  exact (hbad ⟨n % 25, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_509 (n : ℕ) : ¬ 509 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 7, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 7) ≡ 2 ^ cOf r.val [MOD 509 - 1] := by decide
  have hz := dvd_imp_residue_zero 509 7 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 7, (2 ^ eResid 509 r.val + 3) % 509 ≠ 0 := by decide
  exact (hbad ⟨n % 7, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_521 (n : ℕ) : ¬ 521 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 6, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 6) ≡ 2 ^ cOf r.val [MOD 521 - 1] := by decide
  have hz := dvd_imp_residue_zero 521 6 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 6, (2 ^ eResid 521 r.val + 3) % 521 ≠ 0 := by decide
  exact (hbad ⟨n % 6, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_541 (n : ℕ) : ¬ 541 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 18, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 18) ≡ 2 ^ cOf r.val [MOD 541 - 1] := by decide
  have hz := dvd_imp_residue_zero 541 18 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 18, (2 ^ eResid 541 r.val + 3) % 541 ≠ 0 := by decide
  exact (hbad ⟨n % 18, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_547 (n : ℕ) : ¬ 547 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 6, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 6) ≡ 2 ^ cOf r.val [MOD 547 - 1] := by decide
  have hz := dvd_imp_residue_zero 547 6 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 6, (2 ^ eResid 547 r.val + 3) % 547 ≠ 0 := by decide
  exact (hbad ⟨n % 6, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_557 (n : ℕ) : ¬ 557 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 69, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 69) ≡ 2 ^ cOf r.val [MOD 557 - 1] := by decide
  have hz := dvd_imp_residue_zero 557 69 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 69, (2 ^ eResid 557 r.val + 3) % 557 ≠ 0 := by decide
  exact (hbad ⟨n % 69, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_563 (n : ℕ) : ¬ 563 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 35, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 35) ≡ 2 ^ cOf r.val [MOD 563 - 1] := by decide
  have hz := dvd_imp_residue_zero 563 35 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 35, (2 ^ eResid 563 r.val + 3) % 563 ≠ 0 := by decide
  exact (hbad ⟨n % 35, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_569 (n : ℕ) : ¬ 569 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 35, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 35) ≡ 2 ^ cOf r.val [MOD 569 - 1] := by decide
  have hz := dvd_imp_residue_zero 569 35 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 35, (2 ^ eResid 569 r.val + 3) % 569 ≠ 0 := by decide
  exact (hbad ⟨n % 35, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_571 (n : ℕ) : ¬ 571 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 18, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 18) ≡ 2 ^ cOf r.val [MOD 571 - 1] := by decide
  have hz := dvd_imp_residue_zero 571 18 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 18, (2 ^ eResid 571 r.val + 3) % 571 ≠ 0 := by decide
  exact (hbad ⟨n % 18, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_577 (n : ℕ) : ¬ 577 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 3, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 3) ≡ 2 ^ cOf r.val [MOD 577 - 1] := by decide
  have hz := dvd_imp_residue_zero 577 3 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 3, (2 ^ eResid 577 r.val + 3) % 577 ≠ 0 := by decide
  exact (hbad ⟨n % 3, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_587 (n : ℕ) : ¬ 587 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 146, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 146) ≡ 2 ^ cOf r.val [MOD 587 - 1] := by decide
  have hz := dvd_imp_residue_zero 587 146 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 146, (2 ^ eResid 587 r.val + 3) % 587 ≠ 0 := by decide
  exact (hbad ⟨n % 146, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_593 (n : ℕ) : ¬ 593 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 18, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 18) ≡ 2 ^ cOf r.val [MOD 593 - 1] := by decide
  have hz := dvd_imp_residue_zero 593 18 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 18, (2 ^ eResid 593 r.val + 3) % 593 ≠ 0 := by decide
  exact (hbad ⟨n % 18, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_599 (n : ℕ) : ¬ 599 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 66, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 66) ≡ 2 ^ cOf r.val [MOD 599 - 1] := by decide
  have hz := dvd_imp_residue_zero 599 66 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 66, (2 ^ eResid 599 r.val + 3) % 599 ≠ 0 := by decide
  exact (hbad ⟨n % 66, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_601 (n : ℕ) : ¬ 601 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 10, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 10) ≡ 2 ^ cOf r.val [MOD 601 - 1] := by decide
  have hz := dvd_imp_residue_zero 601 10 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 10, (2 ^ eResid 601 r.val + 3) % 601 ≠ 0 := by decide
  exact (hbad ⟨n % 10, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_607 (n : ℕ) : ¬ 607 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 50, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 50) ≡ 2 ^ cOf r.val [MOD 607 - 1] := by decide
  have hz := dvd_imp_residue_zero 607 50 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 50, (2 ^ eResid 607 r.val + 3) % 607 ≠ 0 := by decide
  exact (hbad ⟨n % 50, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_613 (n : ℕ) : ¬ 613 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 12, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 12) ≡ 2 ^ cOf r.val [MOD 613 - 1] := by decide
  have hz := dvd_imp_residue_zero 613 12 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 12, (2 ^ eResid 613 r.val + 3) % 613 ≠ 0 := by decide
  exact (hbad ⟨n % 12, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_617 (n : ℕ) : ¬ 617 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 15, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 15) ≡ 2 ^ cOf r.val [MOD 617 - 1] := by decide
  have hz := dvd_imp_residue_zero 617 15 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 15, (2 ^ eResid 617 r.val + 3) % 617 ≠ 0 := by decide
  exact (hbad ⟨n % 15, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_619 (n : ℕ) : ¬ 619 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 51, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 51) ≡ 2 ^ cOf r.val [MOD 619 - 1] := by decide
  have hz := dvd_imp_residue_zero 619 51 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 51, (2 ^ eResid 619 r.val + 3) % 619 ≠ 0 := by decide
  exact (hbad ⟨n % 51, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_631 (n : ℕ) : ¬ 631 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 6, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 6) ≡ 2 ^ cOf r.val [MOD 631 - 1] := by decide
  have hz := dvd_imp_residue_zero 631 6 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 6, (2 ^ eResid 631 r.val + 3) % 631 ≠ 0 := by decide
  exact (hbad ⟨n % 6, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_641 (n : ℕ) : ¬ 641 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 2, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 2) ≡ 2 ^ cOf r.val [MOD 641 - 1] := by decide
  have hz := dvd_imp_residue_zero 641 2 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 2, (2 ^ eResid 641 r.val + 3) % 641 ≠ 0 := by decide
  exact (hbad ⟨n % 2, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_643 (n : ℕ) : ¬ 643 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 53, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 53) ≡ 2 ^ cOf r.val [MOD 643 - 1] := by decide
  have hz := dvd_imp_residue_zero 643 53 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 53, (2 ^ eResid 643 r.val + 3) % 643 ≠ 0 := by decide
  exact (hbad ⟨n % 53, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_647 (n : ℕ) : ¬ 647 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 36, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 36) ≡ 2 ^ cOf r.val [MOD 647 - 1] := by decide
  have hz := dvd_imp_residue_zero 647 36 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 36, (2 ^ eResid 647 r.val + 3) % 647 ≠ 0 := by decide
  exact (hbad ⟨n % 36, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_653 (n : ℕ) : ¬ 653 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 81, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 81) ≡ 2 ^ cOf r.val [MOD 653 - 1] := by decide
  have hz := dvd_imp_residue_zero 653 81 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 81, (2 ^ eResid 653 r.val + 3) % 653 ≠ 0 := by decide
  exact (hbad ⟨n % 81, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_659 (n : ℕ) : ¬ 659 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 69, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 69) ≡ 2 ^ cOf r.val [MOD 659 - 1] := by decide
  have hz := dvd_imp_residue_zero 659 69 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 69, (2 ^ eResid 659 r.val + 3) % 659 ≠ 0 := by decide
  exact (hbad ⟨n % 69, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_661 (n : ℕ) : ¬ 661 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 10, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 10) ≡ 2 ^ cOf r.val [MOD 661 - 1] := by decide
  have hz := dvd_imp_residue_zero 661 10 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 10, (2 ^ eResid 661 r.val + 3) % 661 ≠ 0 := by decide
  exact (hbad ⟨n % 10, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_673 (n : ℕ) : ¬ 673 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 3, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 3) ≡ 2 ^ cOf r.val [MOD 673 - 1] := by decide
  have hz := dvd_imp_residue_zero 673 3 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 3, (2 ^ eResid 673 r.val + 3) % 673 ≠ 0 := by decide
  exact (hbad ⟨n % 3, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_677 (n : ℕ) : ¬ 677 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 78, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 78) ≡ 2 ^ cOf r.val [MOD 677 - 1] := by decide
  have hz := dvd_imp_residue_zero 677 78 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 78, (2 ^ eResid 677 r.val + 3) % 677 ≠ 0 := by decide
  exact (hbad ⟨n % 78, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_683 (n : ℕ) : ¬ 683 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 5, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 5) ≡ 2 ^ cOf r.val [MOD 683 - 1] := by decide
  have hz := dvd_imp_residue_zero 683 5 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 5, (2 ^ eResid 683 r.val + 3) % 683 ≠ 0 := by decide
  exact (hbad ⟨n % 5, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_691 (n : ℕ) : ¬ 691 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 22, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 22) ≡ 2 ^ cOf r.val [MOD 691 - 1] := by decide
  have hz := dvd_imp_residue_zero 691 22 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 22, (2 ^ eResid 691 r.val + 3) % 691 ≠ 0 := by decide
  exact (hbad ⟨n % 22, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_701 (n : ℕ) : ¬ 701 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 30, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 30) ≡ 2 ^ cOf r.val [MOD 701 - 1] := by decide
  have hz := dvd_imp_residue_zero 701 30 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 30, (2 ^ eResid 701 r.val + 3) % 701 ≠ 0 := by decide
  exact (hbad ⟨n % 30, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_709 (n : ℕ) : ¬ 709 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 1, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 1) ≡ 2 ^ cOf r.val [MOD 709 - 1] := by decide
  have hz := dvd_imp_residue_zero 709 1 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 1, (2 ^ eResid 709 r.val + 3) % 709 ≠ 0 := by decide
  exact (hbad ⟨n % 1, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_719 (n : ℕ) : ¬ 719 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 179, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 179) ≡ 2 ^ cOf r.val [MOD 719 - 1] := by decide
  have hz := dvd_imp_residue_zero 719 179 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 179, (2 ^ eResid 719 r.val + 3) % 719 ≠ 0 := by decide
  exact (hbad ⟨n % 179, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_727 (n : ℕ) : ¬ 727 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 55, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 55) ≡ 2 ^ cOf r.val [MOD 727 - 1] := by decide
  have hz := dvd_imp_residue_zero 727 55 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 55, (2 ^ eResid 727 r.val + 3) % 727 ≠ 0 := by decide
  exact (hbad ⟨n % 55, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_733 (n : ℕ) : ¬ 733 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 30, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 30) ≡ 2 ^ cOf r.val [MOD 733 - 1] := by decide
  have hz := dvd_imp_residue_zero 733 30 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 30, (2 ^ eResid 733 r.val + 3) % 733 ≠ 0 := by decide
  exact (hbad ⟨n % 30, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_739 (n : ℕ) : ¬ 739 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 30, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 30) ≡ 2 ^ cOf r.val [MOD 739 - 1] := by decide
  have hz := dvd_imp_residue_zero 739 30 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 30, (2 ^ eResid 739 r.val + 3) % 739 ≠ 0 := by decide
  exact (hbad ⟨n % 30, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_743 (n : ℕ) : ¬ 743 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 78, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 78) ≡ 2 ^ cOf r.val [MOD 743 - 1] := by decide
  have hz := dvd_imp_residue_zero 743 78 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 78, (2 ^ eResid 743 r.val + 3) % 743 ≠ 0 := by decide
  exact (hbad ⟨n % 78, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_751 (n : ℕ) : ¬ 751 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 50, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 50) ≡ 2 ^ cOf r.val [MOD 751 - 1] := by decide
  have hz := dvd_imp_residue_zero 751 50 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 50, (2 ^ eResid 751 r.val + 3) % 751 ≠ 0 := by decide
  exact (hbad ⟨n % 50, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_757 (n : ℕ) : ¬ 757 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 9, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 9) ≡ 2 ^ cOf r.val [MOD 757 - 1] := by decide
  have hz := dvd_imp_residue_zero 757 9 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 9, (2 ^ eResid 757 r.val + 3) % 757 ≠ 0 := by decide
  exact (hbad ⟨n % 9, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_761 (n : ℕ) : ¬ 761 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 18, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 18) ≡ 2 ^ cOf r.val [MOD 761 - 1] := by decide
  have hz := dvd_imp_residue_zero 761 18 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 18, (2 ^ eResid 761 r.val + 3) % 761 ≠ 0 := by decide
  exact (hbad ⟨n % 18, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_769 (n : ℕ) : ¬ 769 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 1, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 1) ≡ 2 ^ cOf r.val [MOD 769 - 1] := by decide
  have hz := dvd_imp_residue_zero 769 1 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 1, (2 ^ eResid 769 r.val + 3) % 769 ≠ 0 := by decide
  exact (hbad ⟨n % 1, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_773 (n : ℕ) : ¬ 773 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 48, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 48) ≡ 2 ^ cOf r.val [MOD 773 - 1] := by decide
  have hz := dvd_imp_residue_zero 773 48 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 48, (2 ^ eResid 773 r.val + 3) % 773 ≠ 0 := by decide
  exact (hbad ⟨n % 48, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_787 (n : ℕ) : ¬ 787 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 65, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 65) ≡ 2 ^ cOf r.val [MOD 787 - 1] := by decide
  have hz := dvd_imp_residue_zero 787 65 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 65, (2 ^ eResid 787 r.val + 3) % 787 ≠ 0 := by decide
  exact (hbad ⟨n % 65, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_797 (n : ℕ) : ¬ 797 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 99, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 99) ≡ 2 ^ cOf r.val [MOD 797 - 1] := by decide
  have hz := dvd_imp_residue_zero 797 99 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 99, (2 ^ eResid 797 r.val + 3) % 797 ≠ 0 := by decide
  exact (hbad ⟨n % 99, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_809 (n : ℕ) : ¬ 809 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 50, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 50) ≡ 2 ^ cOf r.val [MOD 809 - 1] := by decide
  have hz := dvd_imp_residue_zero 809 50 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 50, (2 ^ eResid 809 r.val + 3) % 809 ≠ 0 := by decide
  exact (hbad ⟨n % 50, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_811 (n : ℕ) : ¬ 811 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 54, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 54) ≡ 2 ^ cOf r.val [MOD 811 - 1] := by decide
  have hz := dvd_imp_residue_zero 811 54 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 54, (2 ^ eResid 811 r.val + 3) % 811 ≠ 0 := by decide
  exact (hbad ⟨n % 54, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_821 (n : ℕ) : ¬ 821 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 10, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 10) ≡ 2 ^ cOf r.val [MOD 821 - 1] := by decide
  have hz := dvd_imp_residue_zero 821 10 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 10, (2 ^ eResid 821 r.val + 3) % 821 ≠ 0 := by decide
  exact (hbad ⟨n % 10, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_823 (n : ℕ) : ¬ 823 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 34, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 34) ≡ 2 ^ cOf r.val [MOD 823 - 1] := by decide
  have hz := dvd_imp_residue_zero 823 34 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 34, (2 ^ eResid 823 r.val + 3) % 823 ≠ 0 := by decide
  exact (hbad ⟨n % 34, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_827 (n : ℕ) : ¬ 827 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 3, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 3) ≡ 2 ^ cOf r.val [MOD 827 - 1] := by decide
  have hz := dvd_imp_residue_zero 827 3 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 3, (2 ^ eResid 827 r.val + 3) % 827 ≠ 0 := by decide
  exact (hbad ⟨n % 3, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_829 (n : ℕ) : ¬ 829 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 33, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 33) ≡ 2 ^ cOf r.val [MOD 829 - 1] := by decide
  have hz := dvd_imp_residue_zero 829 33 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 33, (2 ^ eResid 829 r.val + 3) % 829 ≠ 0 := by decide
  exact (hbad ⟨n % 33, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_839 (n : ℕ) : ¬ 839 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 209, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 209) ≡ 2 ^ cOf r.val [MOD 839 - 1] := by decide
  have hz := dvd_imp_residue_zero 839 209 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 209, (2 ^ eResid 839 r.val + 3) % 839 ≠ 0 := by decide
  exact (hbad ⟨n % 209, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_853 (n : ℕ) : ¬ 853 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 35, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 35) ≡ 2 ^ cOf r.val [MOD 853 - 1] := by decide
  have hz := dvd_imp_residue_zero 853 35 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 35, (2 ^ eResid 853 r.val + 3) % 853 ≠ 0 := by decide
  exact (hbad ⟨n % 35, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_857 (n : ℕ) : ¬ 857 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 53, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 53) ≡ 2 ^ cOf r.val [MOD 857 - 1] := by decide
  have hz := dvd_imp_residue_zero 857 53 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 53, (2 ^ eResid 857 r.val + 3) % 857 ≠ 0 := by decide
  exact (hbad ⟨n % 53, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_859 (n : ℕ) : ¬ 859 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 30, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 30) ≡ 2 ^ cOf r.val [MOD 859 - 1] := by decide
  have hz := dvd_imp_residue_zero 859 30 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 30, (2 ^ eResid 859 r.val + 3) % 859 ≠ 0 := by decide
  exact (hbad ⟨n % 30, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_863 (n : ℕ) : ¬ 863 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 43, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 43) ≡ 2 ^ cOf r.val [MOD 863 - 1] := by decide
  have hz := dvd_imp_residue_zero 863 43 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 43, (2 ^ eResid 863 r.val + 3) % 863 ≠ 0 := by decide
  exact (hbad ⟨n % 43, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_877 (n : ℕ) : ¬ 877 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 9, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 9) ≡ 2 ^ cOf r.val [MOD 877 - 1] := by decide
  have hz := dvd_imp_residue_zero 877 9 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 9, (2 ^ eResid 877 r.val + 3) % 877 ≠ 0 := by decide
  exact (hbad ⟨n % 9, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_881 (n : ℕ) : ¬ 881 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 10, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 10) ≡ 2 ^ cOf r.val [MOD 881 - 1] := by decide
  have hz := dvd_imp_residue_zero 881 10 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 10, (2 ^ eResid 881 r.val + 3) % 881 ≠ 0 := by decide
  exact (hbad ⟨n % 10, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_883 (n : ℕ) : ¬ 883 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 21, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 21) ≡ 2 ^ cOf r.val [MOD 883 - 1] := by decide
  have hz := dvd_imp_residue_zero 883 21 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 21, (2 ^ eResid 883 r.val + 3) % 883 ≠ 0 := by decide
  exact (hbad ⟨n % 21, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_887 (n : ℕ) : ¬ 887 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 221, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 221) ≡ 2 ^ cOf r.val [MOD 887 - 1] := by decide
  have hz := dvd_imp_residue_zero 887 221 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 221, (2 ^ eResid 887 r.val + 3) % 887 ≠ 0 := by decide
  exact (hbad ⟨n % 221, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_907 (n : ℕ) : ¬ 907 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 15, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 15) ≡ 2 ^ cOf r.val [MOD 907 - 1] := by decide
  have hz := dvd_imp_residue_zero 907 15 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 15, (2 ^ eResid 907 r.val + 3) % 907 ≠ 0 := by decide
  exact (hbad ⟨n % 15, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_911 (n : ℕ) : ¬ 911 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 6, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 6) ≡ 2 ^ cOf r.val [MOD 911 - 1] := by decide
  have hz := dvd_imp_residue_zero 911 6 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 6, (2 ^ eResid 911 r.val + 3) % 911 ≠ 0 := by decide
  exact (hbad ⟨n % 6, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_919 (n : ℕ) : ¬ 919 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 36, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 36) ≡ 2 ^ cOf r.val [MOD 919 - 1] := by decide
  have hz := dvd_imp_residue_zero 919 36 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 36, (2 ^ eResid 919 r.val + 3) % 919 ≠ 0 := by decide
  exact (hbad ⟨n % 36, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_929 (n : ℕ) : ¬ 929 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 14, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 14) ≡ 2 ^ cOf r.val [MOD 929 - 1] := by decide
  have hz := dvd_imp_residue_zero 929 14 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 14, (2 ^ eResid 929 r.val + 3) % 929 ≠ 0 := by decide
  exact (hbad ⟨n % 14, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_937 (n : ℕ) : ¬ 937 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 6, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 6) ≡ 2 ^ cOf r.val [MOD 937 - 1] := by decide
  have hz := dvd_imp_residue_zero 937 6 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 6, (2 ^ eResid 937 r.val + 3) % 937 ≠ 0 := by decide
  exact (hbad ⟨n % 6, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_941 (n : ℕ) : ¬ 941 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 46, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 46) ≡ 2 ^ cOf r.val [MOD 941 - 1] := by decide
  have hz := dvd_imp_residue_zero 941 46 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 46, (2 ^ eResid 941 r.val + 3) % 941 ≠ 0 := by decide
  exact (hbad ⟨n % 46, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_947 (n : ℕ) : ¬ 947 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 35, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 35) ≡ 2 ^ cOf r.val [MOD 947 - 1] := by decide
  have hz := dvd_imp_residue_zero 947 35 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 35, (2 ^ eResid 947 r.val + 3) % 947 ≠ 0 := by decide
  exact (hbad ⟨n % 35, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_953 (n : ℕ) : ¬ 953 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 12, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 12) ≡ 2 ^ cOf r.val [MOD 953 - 1] := by decide
  have hz := dvd_imp_residue_zero 953 12 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 12, (2 ^ eResid 953 r.val + 3) % 953 ≠ 0 := by decide
  exact (hbad ⟨n % 12, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_967 (n : ℕ) : ¬ 967 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 33, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 33) ≡ 2 ^ cOf r.val [MOD 967 - 1] := by decide
  have hz := dvd_imp_residue_zero 967 33 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 33, (2 ^ eResid 967 r.val + 3) % 967 ≠ 0 := by decide
  exact (hbad ⟨n % 33, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_971 (n : ℕ) : ¬ 971 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 24, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 24) ≡ 2 ^ cOf r.val [MOD 971 - 1] := by decide
  have hz := dvd_imp_residue_zero 971 24 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 24, (2 ^ eResid 971 r.val + 3) % 971 ≠ 0 := by decide
  exact (hbad ⟨n % 24, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_977 (n : ℕ) : ¬ 977 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 30, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 30) ≡ 2 ^ cOf r.val [MOD 977 - 1] := by decide
  have hz := dvd_imp_residue_zero 977 30 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 30, (2 ^ eResid 977 r.val + 3) % 977 ≠ 0 := by decide
  exact (hbad ⟨n % 30, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_983 (n : ℕ) : ¬ 983 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 245, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 245) ≡ 2 ^ cOf r.val [MOD 983 - 1] := by decide
  have hz := dvd_imp_residue_zero 983 245 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 245, (2 ^ eResid 983 r.val + 3) % 983 ≠ 0 := by decide
  exact (hbad ⟨n % 245, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_991 (n : ℕ) : ¬ 991 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 30, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 30) ≡ 2 ^ cOf r.val [MOD 991 - 1] := by decide
  have hz := dvd_imp_residue_zero 991 30 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 30, (2 ^ eResid 991 r.val + 3) % 991 ≠ 0 := by decide
  exact (hbad ⟨n % 30, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_997 (n : ℕ) : ¬ 997 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 41, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 41) ≡ 2 ^ cOf r.val [MOD 997 - 1] := by decide
  have hz := dvd_imp_residue_zero 997 41 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 41, (2 ^ eResid 997 r.val + 3) % 997 ≠ 0 := by decide
  exact (hbad ⟨n % 41, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1009 (n : ℕ) : ¬ 1009 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 3, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 3) ≡ 2 ^ cOf r.val [MOD 1009 - 1] := by decide
  have hz := dvd_imp_residue_zero 1009 3 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 3, (2 ^ eResid 1009 r.val + 3) % 1009 ≠ 0 := by decide
  exact (hbad ⟨n % 3, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1013 (n : ℕ) : ¬ 1013 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 55, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 55) ≡ 2 ^ cOf r.val [MOD 1013 - 1] := by decide
  have hz := dvd_imp_residue_zero 1013 55 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 55, (2 ^ eResid 1013 r.val + 3) % 1013 ≠ 0 := by decide
  exact (hbad ⟨n % 55, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1019 (n : ℕ) : ¬ 1019 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 254, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 254) ≡ 2 ^ cOf r.val [MOD 1019 - 1] := by decide
  have hz := dvd_imp_residue_zero 1019 254 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 254, (2 ^ eResid 1019 r.val + 3) % 1019 ≠ 0 := by decide
  exact (hbad ⟨n % 254, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1021 (n : ℕ) : ¬ 1021 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 4, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 4) ≡ 2 ^ cOf r.val [MOD 1021 - 1] := by decide
  have hz := dvd_imp_residue_zero 1021 4 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 4, (2 ^ eResid 1021 r.val + 3) % 1021 ≠ 0 := by decide
  exact (hbad ⟨n % 4, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1031 (n : ℕ) : ¬ 1031 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 102, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 102) ≡ 2 ^ cOf r.val [MOD 1031 - 1] := by decide
  have hz := dvd_imp_residue_zero 1031 102 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 102, (2 ^ eResid 1031 r.val + 3) % 1031 ≠ 0 := by decide
  exact (hbad ⟨n % 102, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1033 (n : ℕ) : ¬ 1033 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 7, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 7) ≡ 2 ^ cOf r.val [MOD 1033 - 1] := by decide
  have hz := dvd_imp_residue_zero 1033 7 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 7, (2 ^ eResid 1033 r.val + 3) % 1033 ≠ 0 := by decide
  exact (hbad ⟨n % 7, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1039 (n : ℕ) : ¬ 1039 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 86, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 86) ≡ 2 ^ cOf r.val [MOD 1039 - 1] := by decide
  have hz := dvd_imp_residue_zero 1039 86 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 86, (2 ^ eResid 1039 r.val + 3) % 1039 ≠ 0 := by decide
  exact (hbad ⟨n % 86, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1049 (n : ℕ) : ¬ 1049 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 65, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 65) ≡ 2 ^ cOf r.val [MOD 1049 - 1] := by decide
  have hz := dvd_imp_residue_zero 1049 65 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 65, (2 ^ eResid 1049 r.val + 3) % 1049 ≠ 0 := by decide
  exact (hbad ⟨n % 65, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1051 (n : ℕ) : ¬ 1051 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 30, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 30) ≡ 2 ^ cOf r.val [MOD 1051 - 1] := by decide
  have hz := dvd_imp_residue_zero 1051 30 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 30, (2 ^ eResid 1051 r.val + 3) % 1051 ≠ 0 := by decide
  exact (hbad ⟨n % 30, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1061 (n : ℕ) : ¬ 1061 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 26, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 26) ≡ 2 ^ cOf r.val [MOD 1061 - 1] := by decide
  have hz := dvd_imp_residue_zero 1061 26 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 26, (2 ^ eResid 1061 r.val + 3) % 1061 ≠ 0 := by decide
  exact (hbad ⟨n % 26, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1063 (n : ℕ) : ¬ 1063 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 3, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 3) ≡ 2 ^ cOf r.val [MOD 1063 - 1] := by decide
  have hz := dvd_imp_residue_zero 1063 3 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 3, (2 ^ eResid 1063 r.val + 3) % 1063 ≠ 0 := by decide
  exact (hbad ⟨n % 3, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1069 (n : ℕ) : ¬ 1069 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 11, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 11) ≡ 2 ^ cOf r.val [MOD 1069 - 1] := by decide
  have hz := dvd_imp_residue_zero 1069 11 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 11, (2 ^ eResid 1069 r.val + 3) % 1069 ≠ 0 := by decide
  exact (hbad ⟨n % 11, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1087 (n : ℕ) : ¬ 1087 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 90, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 90) ≡ 2 ^ cOf r.val [MOD 1087 - 1] := by decide
  have hz := dvd_imp_residue_zero 1087 90 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 90, (2 ^ eResid 1087 r.val + 3) % 1087 ≠ 0 := by decide
  exact (hbad ⟨n % 90, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1091 (n : ℕ) : ¬ 1091 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 18, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 18) ≡ 2 ^ cOf r.val [MOD 1091 - 1] := by decide
  have hz := dvd_imp_residue_zero 1091 18 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 18, (2 ^ eResid 1091 r.val + 3) % 1091 ≠ 0 := by decide
  exact (hbad ⟨n % 18, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1093 (n : ℕ) : ¬ 1093 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 6, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 6) ≡ 2 ^ cOf r.val [MOD 1093 - 1] := by decide
  have hz := dvd_imp_residue_zero 1093 6 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 6, (2 ^ eResid 1093 r.val + 3) % 1093 ≠ 0 := by decide
  exact (hbad ⟨n % 6, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1097 (n : ℕ) : ¬ 1097 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 34, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 34) ≡ 2 ^ cOf r.val [MOD 1097 - 1] := by decide
  have hz := dvd_imp_residue_zero 1097 34 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 34, (2 ^ eResid 1097 r.val + 3) % 1097 ≠ 0 := by decide
  exact (hbad ⟨n % 34, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1103 (n : ℕ) : ¬ 1103 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 126, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 126) ≡ 2 ^ cOf r.val [MOD 1103 - 1] := by decide
  have hz := dvd_imp_residue_zero 1103 126 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 126, (2 ^ eResid 1103 r.val + 3) % 1103 ≠ 0 := by decide
  exact (hbad ⟨n % 126, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1109 (n : ℕ) : ¬ 1109 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 46, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 46) ≡ 2 ^ cOf r.val [MOD 1109 - 1] := by decide
  have hz := dvd_imp_residue_zero 1109 46 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 46, (2 ^ eResid 1109 r.val + 3) % 1109 ≠ 0 := by decide
  exact (hbad ⟨n % 46, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1117 (n : ℕ) : ¬ 1117 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 15, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 15) ≡ 2 ^ cOf r.val [MOD 1117 - 1] := by decide
  have hz := dvd_imp_residue_zero 1117 15 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 15, (2 ^ eResid 1117 r.val + 3) % 1117 ≠ 0 := by decide
  exact (hbad ⟨n % 15, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1123 (n : ℕ) : ¬ 1123 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 20, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 20) ≡ 2 ^ cOf r.val [MOD 1123 - 1] := by decide
  have hz := dvd_imp_residue_zero 1123 20 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 20, (2 ^ eResid 1123 r.val + 3) % 1123 ≠ 0 := by decide
  exact (hbad ⟨n % 20, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1129 (n : ℕ) : ¬ 1129 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 23, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 23) ≡ 2 ^ cOf r.val [MOD 1129 - 1] := by decide
  have hz := dvd_imp_residue_zero 1129 23 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 23, (2 ^ eResid 1129 r.val + 3) % 1129 ≠ 0 := by decide
  exact (hbad ⟨n % 23, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1151 (n : ℕ) : ¬ 1151 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 110, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 110) ≡ 2 ^ cOf r.val [MOD 1151 - 1] := by decide
  have hz := dvd_imp_residue_zero 1151 110 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 110, (2 ^ eResid 1151 r.val + 3) % 1151 ≠ 0 := by decide
  exact (hbad ⟨n % 110, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1153 (n : ℕ) : ¬ 1153 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 3, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 3) ≡ 2 ^ cOf r.val [MOD 1153 - 1] := by decide
  have hz := dvd_imp_residue_zero 1153 3 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 3, (2 ^ eResid 1153 r.val + 3) % 1153 ≠ 0 := by decide
  exact (hbad ⟨n % 3, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1163 (n : ℕ) : ¬ 1163 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 123, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 123) ≡ 2 ^ cOf r.val [MOD 1163 - 1] := by decide
  have hz := dvd_imp_residue_zero 1163 123 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 123, (2 ^ eResid 1163 r.val + 3) % 1163 ≠ 0 := by decide
  exact (hbad ⟨n % 123, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1171 (n : ℕ) : ¬ 1171 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 6, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 6) ≡ 2 ^ cOf r.val [MOD 1171 - 1] := by decide
  have hz := dvd_imp_residue_zero 1171 6 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 6, (2 ^ eResid 1171 r.val + 3) % 1171 ≠ 0 := by decide
  exact (hbad ⟨n % 6, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1181 (n : ℕ) : ¬ 1181 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 2, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 2) ≡ 2 ^ cOf r.val [MOD 1181 - 1] := by decide
  have hz := dvd_imp_residue_zero 1181 2 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 2, (2 ^ eResid 1181 r.val + 3) % 1181 ≠ 0 := by decide
  exact (hbad ⟨n % 2, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1187 (n : ℕ) : ¬ 1187 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 74, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 74) ≡ 2 ^ cOf r.val [MOD 1187 - 1] := by decide
  have hz := dvd_imp_residue_zero 1187 74 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 74, (2 ^ eResid 1187 r.val + 3) % 1187 ≠ 0 := by decide
  exact (hbad ⟨n % 74, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1193 (n : ℕ) : ¬ 1193 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 74, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 74) ≡ 2 ^ cOf r.val [MOD 1193 - 1] := by decide
  have hz := dvd_imp_residue_zero 1193 74 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 74, (2 ^ eResid 1193 r.val + 3) % 1193 ≠ 0 := by decide
  exact (hbad ⟨n % 74, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1201 (n : ℕ) : ¬ 1201 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 10, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 10) ≡ 2 ^ cOf r.val [MOD 1201 - 1] := by decide
  have hz := dvd_imp_residue_zero 1201 10 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 10, (2 ^ eResid 1201 r.val + 3) % 1201 ≠ 0 := by decide
  exact (hbad ⟨n % 10, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1213 (n : ℕ) : ¬ 1213 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 50, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 50) ≡ 2 ^ cOf r.val [MOD 1213 - 1] := by decide
  have hz := dvd_imp_residue_zero 1213 50 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 50, (2 ^ eResid 1213 r.val + 3) % 1213 ≠ 0 := by decide
  exact (hbad ⟨n % 50, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1217 (n : ℕ) : ¬ 1217 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 9, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 9) ≡ 2 ^ cOf r.val [MOD 1217 - 1] := by decide
  have hz := dvd_imp_residue_zero 1217 9 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 9, (2 ^ eResid 1217 r.val + 3) % 1217 ≠ 0 := by decide
  exact (hbad ⟨n % 9, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1223 (n : ℕ) : ¬ 1223 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 138, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 138) ≡ 2 ^ cOf r.val [MOD 1223 - 1] := by decide
  have hz := dvd_imp_residue_zero 1223 138 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 138, (2 ^ eResid 1223 r.val + 3) % 1223 ≠ 0 := by decide
  exact (hbad ⟨n % 138, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1229 (n : ℕ) : ¬ 1229 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 51, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 51) ≡ 2 ^ cOf r.val [MOD 1229 - 1] := by decide
  have hz := dvd_imp_residue_zero 1229 51 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 51, (2 ^ eResid 1229 r.val + 3) % 1229 ≠ 0 := by decide
  exact (hbad ⟨n % 51, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1231 (n : ℕ) : ¬ 1231 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 10, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 10) ≡ 2 ^ cOf r.val [MOD 1231 - 1] := by decide
  have hz := dvd_imp_residue_zero 1231 10 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 10, (2 ^ eResid 1231 r.val + 3) % 1231 ≠ 0 := by decide
  exact (hbad ⟨n % 10, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1237 (n : ℕ) : ¬ 1237 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 51, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 51) ≡ 2 ^ cOf r.val [MOD 1237 - 1] := by decide
  have hz := dvd_imp_residue_zero 1237 51 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 51, (2 ^ eResid 1237 r.val + 3) % 1237 ≠ 0 := by decide
  exact (hbad ⟨n % 51, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1249 (n : ℕ) : ¬ 1249 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 6, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 6) ≡ 2 ^ cOf r.val [MOD 1249 - 1] := by decide
  have hz := dvd_imp_residue_zero 1249 6 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 6, (2 ^ eResid 1249 r.val + 3) % 1249 ≠ 0 := by decide
  exact (hbad ⟨n % 6, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1259 (n : ℕ) : ¬ 1259 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 36, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 36) ≡ 2 ^ cOf r.val [MOD 1259 - 1] := by decide
  have hz := dvd_imp_residue_zero 1259 36 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 36, (2 ^ eResid 1259 r.val + 3) % 1259 ≠ 0 := by decide
  exact (hbad ⟨n % 36, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1277 (n : ℕ) : ¬ 1277 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 70, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 70) ≡ 2 ^ cOf r.val [MOD 1277 - 1] := by decide
  have hz := dvd_imp_residue_zero 1277 70 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 70, (2 ^ eResid 1277 r.val + 3) % 1277 ≠ 0 := by decide
  exact (hbad ⟨n % 70, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1279 (n : ℕ) : ¬ 1279 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 105, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 105) ≡ 2 ^ cOf r.val [MOD 1279 - 1] := by decide
  have hz := dvd_imp_residue_zero 1279 105 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 105, (2 ^ eResid 1279 r.val + 3) % 1279 ≠ 0 := by decide
  exact (hbad ⟨n % 105, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1283 (n : ℕ) : ¬ 1283 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 32, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 32) ≡ 2 ^ cOf r.val [MOD 1283 - 1] := by decide
  have hz := dvd_imp_residue_zero 1283 32 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 32, (2 ^ eResid 1283 r.val + 3) % 1283 ≠ 0 := by decide
  exact (hbad ⟨n % 32, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1289 (n : ℕ) : ¬ 1289 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 33, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 33) ≡ 2 ^ cOf r.val [MOD 1289 - 1] := by decide
  have hz := dvd_imp_residue_zero 1289 33 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 33, (2 ^ eResid 1289 r.val + 3) % 1289 ≠ 0 := by decide
  exact (hbad ⟨n % 33, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1291 (n : ℕ) : ¬ 1291 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 14, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 14) ≡ 2 ^ cOf r.val [MOD 1291 - 1] := by decide
  have hz := dvd_imp_residue_zero 1291 14 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 14, (2 ^ eResid 1291 r.val + 3) % 1291 ≠ 0 := by decide
  exact (hbad ⟨n % 14, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1297 (n : ℕ) : ¬ 1297 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 27, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 27) ≡ 2 ^ cOf r.val [MOD 1297 - 1] := by decide
  have hz := dvd_imp_residue_zero 1297 27 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 27, (2 ^ eResid 1297 r.val + 3) % 1297 ≠ 0 := by decide
  exact (hbad ⟨n % 27, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1301 (n : ℕ) : ¬ 1301 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 30, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 30) ≡ 2 ^ cOf r.val [MOD 1301 - 1] := by decide
  have hz := dvd_imp_residue_zero 1301 30 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 30, (2 ^ eResid 1301 r.val + 3) % 1301 ≠ 0 := by decide
  exact (hbad ⟨n % 30, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1303 (n : ℕ) : ¬ 1303 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 15, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 15) ≡ 2 ^ cOf r.val [MOD 1303 - 1] := by decide
  have hz := dvd_imp_residue_zero 1303 15 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 15, (2 ^ eResid 1303 r.val + 3) % 1303 ≠ 0 := by decide
  exact (hbad ⟨n % 15, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1307 (n : ℕ) : ¬ 1307 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 326, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 326) ≡ 2 ^ cOf r.val [MOD 1307 - 1] := by decide
  have hz := dvd_imp_residue_zero 1307 326 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 326, (2 ^ eResid 1307 r.val + 3) % 1307 ≠ 0 := by decide
  exact (hbad ⟨n % 326, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1319 (n : ℕ) : ¬ 1319 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 329, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 329) ≡ 2 ^ cOf r.val [MOD 1319 - 1] := by decide
  have hz := dvd_imp_residue_zero 1319 329 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 329, (2 ^ eResid 1319 r.val + 3) % 1319 ≠ 0 := by decide
  exact (hbad ⟨n % 329, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1321 (n : ℕ) : ¬ 1321 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 10, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 10) ≡ 2 ^ cOf r.val [MOD 1321 - 1] := by decide
  have hz := dvd_imp_residue_zero 1321 10 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 10, (2 ^ eResid 1321 r.val + 3) % 1321 ≠ 0 := by decide
  exact (hbad ⟨n % 10, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1327 (n : ℕ) : ¬ 1327 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 12, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 12) ≡ 2 ^ cOf r.val [MOD 1327 - 1] := by decide
  have hz := dvd_imp_residue_zero 1327 12 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 12, (2 ^ eResid 1327 r.val + 3) % 1327 ≠ 0 := by decide
  exact (hbad ⟨n % 12, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1361 (n : ℕ) : ¬ 1361 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 4, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 4) ≡ 2 ^ cOf r.val [MOD 1361 - 1] := by decide
  have hz := dvd_imp_residue_zero 1361 4 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 4, (2 ^ eResid 1361 r.val + 3) % 1361 ≠ 0 := by decide
  exact (hbad ⟨n % 4, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1367 (n : ℕ) : ¬ 1367 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 11, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 11) ≡ 2 ^ cOf r.val [MOD 1367 - 1] := by decide
  have hz := dvd_imp_residue_zero 1367 11 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 11, (2 ^ eResid 1367 r.val + 3) % 1367 ≠ 0 := by decide
  exact (hbad ⟨n % 11, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1373 (n : ℕ) : ¬ 1373 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 147, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 147) ≡ 2 ^ cOf r.val [MOD 1373 - 1] := by decide
  have hz := dvd_imp_residue_zero 1373 147 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 147, (2 ^ eResid 1373 r.val + 3) % 1373 ≠ 0 := by decide
  exact (hbad ⟨n % 147, Nat.mod_lt n (by norm_num)⟩) hz

lemma no_dvd_1381 (n : ℕ) : ¬ 1381 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
  intro h
  have hstep : ∀ r : Fin 22, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 22) ≡ 2 ^ cOf r.val [MOD 1381 - 1] := by decide
  have hz := dvd_imp_residue_zero 1381 22 n (by norm_num) (by decide) hstep h
  have hbad : ∀ r : Fin 22, (2 ^ eResid 1381 r.val + 3) % 1381 ≠ 0 := by decide
  exact (hbad ⟨n % 22, Nat.mod_lt n (by norm_num)⟩) hz


lemma c1_of_mod5 (n : ℕ) (hr : n % 5 = 2) : covered_by_C1 (58 * n + 26) := by
  have hn : n = 5 * (n / 5) + 2 := by
    have hd : 5 * (n / 5) + n % 5 = n := Nat.div_add_mod n 5
    omega
  use 29 * (n / 5) + 14
  omega

lemma c2_or_c1_of_mod18 (n : ℕ) (hr : n % 18 = 11) : covered_by_C1 (58 * n + 26) ∨ covered_by_C2 (58 * n + 26) := by
  have hn : n = 18 * (n / 18) + 11 := by
    have hd : 18 * (n / 18) + n % 18 = n := Nat.div_add_mod n 18
    omega
  by_cases hm : (29 * (n / 18) + 18) % 5 = 1
  · left
    apply c1_of_mod5
    omega
  · right
    unfold covered_by_C2
    use 29 * (n / 18) + 18
    constructor <;> omega

lemma c3_or_c1_of_mod42 (n : ℕ) (hr : n % 42 = 26) : covered_by_C1 (58 * n + 26) ∨ covered_by_C3 (58 * n + 26) := by
  have hn : n = 42 * (n / 42) + 26 := by
    have hd : 42 * (n / 42) + n % 42 = n := Nat.div_add_mod n 42
    omega
  by_cases hm : (29 * (n / 42) + 18) % 5 = 0
  · left
    apply c1_of_mod5
    omega
  · right
    unfold covered_by_C3
    use 29 * (n / 42) + 18
    constructor <;> omega

lemma dvd67_imp_c1 (n : ℕ) (h : 67 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3) :
    covered_by_C1 (58 * n + 26) := by
  have hstep : ∀ r : Fin 5, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 5) ≡ 2 ^ cOf r.val [MOD 67 - 1] := by decide
  have hz := dvd_imp_residue_zero 67 5 n (by norm_num) (by decide) hstep h
  have hres : ∀ r : Fin 5, (2 ^ eResid 67 r.val + 3) % 67 = 0 → r.val = 2 := by decide
  have hr : n % 5 = 2 := hres ⟨n % 5, Nat.mod_lt n (by norm_num)⟩ hz
  exact c1_of_mod5 n (by omega)

lemma dvd271_imp_c1_or_c2 (n : ℕ) (h : 271 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3) :
    covered_by_C1 (58 * n + 26) ∨ covered_by_C2 (58 * n + 26) := by
  have hstep : ∀ r : Fin 18, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 18) ≡ 2 ^ cOf r.val [MOD 271 - 1] := by decide
  have hz := dvd_imp_residue_zero 271 18 n (by norm_num) (by decide) hstep h
  have hres : ∀ r : Fin 18, (2 ^ eResid 271 r.val + 3) % 271 = 0 → r.val = 11 := by decide
  have hr : n % 18 = 11 := hres ⟨n % 18, Nat.mod_lt n (by norm_num)⟩ hz
  exact c2_or_c1_of_mod18 n hr

lemma dvd523_imp_c1_or_c3 (n : ℕ) (h : 523 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3) :
    covered_by_C1 (58 * n + 26) ∨ covered_by_C3 (58 * n + 26) := by
  have hstep : ∀ r : Fin 42, (2 : ℕ) ^ cOf r.val * 2 ^ (58 * 42) ≡ 2 ^ cOf r.val [MOD 523 - 1] := by decide
  have hz := dvd_imp_residue_zero 523 42 n (by norm_num) (by decide) hstep h
  have hres : ∀ r : Fin 42, (2 ^ eResid 523 r.val + 3) % 523 = 0 → r.val = 26 := by decide
  have hr : n % 42 = 26 := hres ⟨n % 42, Nat.mod_lt n (by norm_num)⟩ hz
  exact c3_or_c1_of_mod42 n hr

/--
A248802 Conjecture 4: a(58n+26) = 1399 for n >= 0 and when it is not covered by Conjectures 1-3.
-/
theorem oeis_248802_conjecture_4 (n : ℕ) :
  (¬ covered_by_C1 (58 * n + 26) ∧
   ¬ covered_by_C2 (58 * n + 26) ∧
   ¬ covered_by_C3 (58 * n + 26)) →
  a (58 * n + 26) = 1399 := by
  intro hcov
  unfold a
  let N := 2 ^ (2 ^ (58 * n + 26) + 2) + 3
  have hNgt : 1 < N := by
    dsimp [N]
    have : 0 < 2 ^ (2 ^ (58 * n + 26) + 2) := by positivity
    omega
  have hNne : N ≠ 1 := ne_of_gt hNgt
  have hle : N.minFac ≤ 1399 := Nat.minFac_le_of_dvd (by norm_num) (by simpa [N] using dvd1399_main n)
  have hge : 1399 ≤ N.minFac := by
    have hall : ∀ p, Nat.Prime p → p ∣ N → 1399 ≤ p := by
      intro p hp hpdvd
      by_contra hltNot
      have hlt : p < 1399 := by omega
      interval_cases p
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_2 n (by simpa [N] using hpdvd))
      · exact False.elim (no_dvd_3 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_5 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_7 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_11 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_13 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_17 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_19 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_23 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_29 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_31 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_37 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_41 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_43 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_47 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_53 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_59 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_61 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (hcov.1 (dvd67_imp_c1 n (by simpa [N] using hpdvd)))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_71 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_73 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_79 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_83 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_89 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_97 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_101 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_103 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_107 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_109 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_113 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_127 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_131 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_137 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_139 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_149 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_151 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_157 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_163 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_167 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_173 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_179 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_181 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_191 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_193 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_197 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_199 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_211 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_223 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_227 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_229 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_233 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_239 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_241 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_251 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_257 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_263 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_269 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · have hc := dvd271_imp_c1_or_c2 n (by simpa [N] using hpdvd)
        rcases hc with hc1 | hc2
        · exact False.elim (hcov.1 hc1)
        · exact False.elim (hcov.2.1 hc2)
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_277 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_281 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_283 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_293 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_307 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_311 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_313 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_317 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_331 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_337 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_347 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_349 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_353 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_359 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_367 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_373 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_379 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_383 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_389 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_397 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_401 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_409 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_419 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_421 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_431 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_433 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_439 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_443 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_449 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_457 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_461 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_463 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_467 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_479 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_487 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_491 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_499 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_503 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_509 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_521 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · have hc := dvd523_imp_c1_or_c3 n (by simpa [N] using hpdvd)
        rcases hc with hc1 | hc3
        · exact False.elim (hcov.1 hc1)
        · exact False.elim (hcov.2.2 hc3)
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_541 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_547 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_557 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_563 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_569 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_571 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_577 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_587 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_593 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_599 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_601 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_607 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_613 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_617 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_619 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_631 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_641 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_643 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_647 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_653 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_659 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_661 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_673 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_677 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_683 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_691 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_701 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_709 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_719 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_727 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_733 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_739 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_743 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_751 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_757 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_761 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_769 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_773 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_787 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_797 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_809 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_811 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_821 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_823 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_827 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_829 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_839 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_853 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_857 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_859 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_863 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_877 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_881 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_883 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_887 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_907 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_911 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_919 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_929 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_937 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_941 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_947 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_953 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_967 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_971 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_977 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_983 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_991 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_997 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1009 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1013 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1019 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_1021 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1031 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_1033 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1039 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1049 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_1051 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1061 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_1063 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1069 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1087 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1091 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_1093 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1097 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1103 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1109 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1117 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1123 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1129 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1151 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_1153 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1163 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1171 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1181 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1187 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1193 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1201 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1213 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1217 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1223 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1229 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_1231 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1237 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1249 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1259 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1277 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_1279 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1283 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1289 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_1291 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1297 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1301 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_1303 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1307 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1319 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · exact False.elim (no_dvd_1321 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1327 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1361 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1367 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1373 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · exact False.elim (no_dvd_1381 n (by simpa [N] using hpdvd))
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
      · norm_num at hp
    have h := (Nat.le_minFac (m := 1399) (n := N)).2 hall
    rcases h with hEq | hlemin
    · exact False.elim (hNne hEq)
    · exact hlemin
  exact le_antisymm hle hge
