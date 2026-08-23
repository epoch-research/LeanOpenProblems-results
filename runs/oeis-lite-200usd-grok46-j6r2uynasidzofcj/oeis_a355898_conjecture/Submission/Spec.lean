import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/--
A355898: $a(1) = a(2) = 1$; $a(n) = \gcd(a(n-1), a(n-2)) + \frac{a(n-1) + a(n-2)}{\gcd(a(n-1), a(n-2))}$.
-/
def A355898 : ℕ → ℕ
| 0 => 0 -- Sequence starts properly at A355898(1)
| 1 => 1
| 2 => 1
| n + 3 =>
  let an_minus_1 := A355898 (n + 2)
  let an_minus_2 := A355898 (n + 1)
  let g := Nat.gcd an_minus_1 an_minus_2
  g + (an_minus_1 + an_minus_2) / g

/- Iterative computation of A355898 -/

/-- `aPair n = (A355898 n, A355898 (n + 1))`, computed iteratively. -/
def aPair : ℕ → ℕ × ℕ
| 0 => (0, 1)
| 1 => (1, 1)
| n + 2 =>
  let pr := aPair (n + 1)
  let g := Nat.gcd pr.1 pr.2
  (pr.2, g + (pr.1 + pr.2) / g)

lemma A355898_add_three (n : ℕ) :
    A355898 (n + 3) =
      let g := Nat.gcd (A355898 (n + 2)) (A355898 (n + 1))
      g + (A355898 (n + 2) + A355898 (n + 1)) / g :=
  rfl

lemma aPair_eq : ∀ n, aPair n = (A355898 n, A355898 (n + 1))
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    change (let pr := aPair (n + 1)
            let g := Nat.gcd pr.1 pr.2
            (pr.2, g + (pr.1 + pr.2) / g)) =
      (A355898 (n + 2), A355898 (n + 3))
    rw [aPair_eq (n + 1)]
    simp only
    refine Prod.ext ?_ ?_
    · simp
    · rw [A355898_add_three]
      have : n + 1 + 1 = n + 2 := by omega
      simp [this, Nat.gcd_comm, Nat.add_comm]

lemma A355898_eq_aPair_fst (n : ℕ) : A355898 n = (aPair n).1 := by
  rw [aPair_eq]

lemma A355898_pos : ∀ n, 0 < n → 0 < A355898 n
  | 0, h => (lt_irrefl _ h).elim
  | 1, _ => by decide
  | 2, _ => by decide
  | n + 3, _ => by
    have h2 : 0 < A355898 (n + 2) := A355898_pos (n + 2) (succ_pos _)
    rw [A355898_add_three]
    have hg : 0 < Nat.gcd (A355898 (n + 2)) (A355898 (n + 1)) :=
      Nat.gcd_pos_of_pos_left _ h2
    exact Nat.add_pos_left hg _

/- Binary Fibonacci in `ZMod p` -/

def fibStep {p : ℕ} (b : Bool) (pair : ZMod p × ZMod p) : ZMod p × ZMod p :=
  if b then
    (pair.2 ^ 2 + pair.1 ^ 2, pair.2 * (2 * pair.1 + pair.2))
  else
    (pair.1 * (2 * pair.2 - pair.1), pair.2 ^ 2 + pair.1 ^ 2)

/-- LSB-first binary digits. -/
def bitsToNat : List Bool → ℕ
  | [] => 0
  | false :: bs => 2 * bitsToNat bs
  | true :: bs => 2 * bitsToNat bs + 1

/-- LSB-first fold computing `(↑(fib n), ↑(fib (n + 1)))`. -/
def fibRun (p : ℕ) : List Bool → ZMod p × ZMod p
  | [] => (0, 1)
  | b :: bs => fibStep b (fibRun p bs)

lemma fib_le_two_mul_fib_succ (n : ℕ) : fib n ≤ 2 * fib (n + 1) :=
  fib_le_fib_succ.trans <|
    (Nat.le_mul_of_pos_right (fib (n + 1)) (by decide : (0 : ℕ) < 2)).trans_eq (mul_comm _ _)

lemma fibRun_eq (p : ℕ) : ∀ bs,
    fibRun p bs = ((fib (bitsToNat bs) : ZMod p), (fib (bitsToNat bs + 1) : ZMod p))
  | [] => by simp [fibRun, bitsToNat]
  | false :: bs => by
    change fibStep false (fibRun p bs) = _
    rw [fibRun_eq p bs]
    dsimp [fibStep]
    simp only [bitsToNat]
    have hle := fib_le_two_mul_fib_succ (bitsToNat bs)
    rw [fib_two_mul, fib_two_mul_add_one]
    push_cast [hle]
    ring
  | true :: bs => by
    change fibStep true (fibRun p bs) = _
    rw [fibRun_eq p bs]
    dsimp [fibStep]
    simp only [bitsToNat]
    rw [show 2 * bitsToNat bs + 1 + 1 = 2 * bitsToNat bs + 2 by ring]
    rw [fib_two_mul_add_one, fib_two_mul_add_two]
    push_cast
    ring

/- Concrete modulus and index -/

def bitsK : List Bool :=
  [true, false, false, false, true, false, false, false, true, false, false, false,
   true, true, false, true, true, false, false, false, false, true, false, false,
   false, false, true, true, true, false, false, false, false, true, false, true,
   true, true]

def bitsKm1 : List Bool :=
  [false, false, false, false, true, false, false, false, true, false, false, false,
   true, true, false, true, true, false, false, false, false, true, false, false,
   false, false, true, true, true, false, false, false, false, true, false, true,
   true, true]

lemma bitsToNat_bitsK : bitsToNat bitsK = 249580073233 := by
  decide

lemma bitsToNat_bitsKm1 : bitsToNat bitsKm1 = 249580073232 := by
  decide

lemma fibRun_bitsK :
    fibRun 195318521017 bitsK = (21827756563, 139205883321) := by
  unfold bitsK
  decide

lemma fibRun_bitsKm1 :
    fibRun 195318521017 bitsKm1 = (117378126758, 21827756563) := by
  unfold bitsKm1
  decide

lemma aPair_3773_mod : (aPair 3773).1 % 195318521017 = 77940394258 := by
  decide

lemma aPair_3774_mod : (aPair 3774).1 % 195318521017 = 99768150821 := by
  decide

lemma A355898_3773_zmod :
    (A355898 3773 : ZMod 195318521017) = ↑(77940394258 : ℕ) := by
  rw [A355898_eq_aPair_fst, ZMod.natCast_eq_natCast_iff, Nat.ModEq, aPair_3773_mod]

lemma A355898_3774_zmod :
    (A355898 3774 : ZMod 195318521017) = ↑(99768150821 : ℕ) := by
  rw [A355898_eq_aPair_fst, ZMod.natCast_eq_natCast_iff, Nat.ModEq, aPair_3774_mod]

lemma fib_fst_of_run {p : ℕ} {bs : List Bool} {x y : ZMod p}
    (h : fibRun p bs = (x, y)) :
    (fib (bitsToNat bs) : ZMod p) = x := by
  have hr := fibRun_eq p bs
  rw [h] at hr
  cases hr
  rfl

lemma fib_snd_of_run {p : ℕ} {bs : List Bool} {x y : ZMod p}
    (h : fibRun p bs = (x, y)) :
    (fib (bitsToNat bs + 1) : ZMod p) = y := by
  have hr := fibRun_eq p bs
  rw [h] at hr
  cases hr
  rfl

lemma fib_Kidx_zmod :
    (fib 249580073233 : ZMod 195318521017) = ↑(21827756563 : ℕ) := by
  have h := fib_fst_of_run fibRun_bitsK
  rw [bitsToNat_bitsK] at h
  exact h

lemma fib_Km1_zmod :
    (fib 249580073232 : ZMod 195318521017) = ↑(117378126758 : ℕ) := by
  have h := fib_fst_of_run fibRun_bitsKm1
  rw [bitsToNat_bitsKm1] at h
  exact h

lemma fib_Kp1_zmod :
    (fib 249580073234 : ZMod 195318521017) = ↑(139205883321 : ℕ) := by
  have h := fib_snd_of_run fibRun_bitsK
  rw [bitsToNat_bitsK] at h
  rw [show (249580073233 : ℕ) + 1 = 249580073234 by omega] at h
  exact h

/- Closed form under the coprimality assumption -/

def c (k : ℕ) : ℕ := A355898 (3773 + k) + 1

lemma c_add_two (hf1 : ∀ n, 3775 ≤ n → A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
    (k : ℕ) : c (k + 2) = c (k + 1) + c k := by
  unfold c
  have hidx : 3773 + (k + 2) = 3775 + k := by omega
  have hidx1 : 3773 + (k + 1) = 3774 + k := by omega
  rw [hidx, hidx1]
  have hf := hf1 (3775 + k) (Nat.le_add_right _ _)
  have d1 : 3775 + k - 1 = 3774 + k := by omega
  have d2 : 3775 + k - 2 = 3773 + k := by omega
  rw [hf, d1, d2]
  ac_rfl

lemma c_formula (hf1 : ∀ n, 3775 ≤ n → A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
    (k : ℕ) : c (k + 1) = c 1 * fib (k + 1) + c 0 * fib k := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    match k with
    | 0 =>
      simp [fib_zero, fib_one]
    | 1 =>
      have h := c_add_two hf1 0
      simp [h, fib_one, fib_two]
    | k + 2 =>
      have ih1 := ih (k + 1) (by omega)
      have ih0 := ih k (by omega)
      have hsum := c_add_two hf1 (k + 1)
      -- hsum : c (k+3) = c (k+2) + c (k+1)
      have : c (k + 2 + 1) = c (k + 3) := by
        rw [show k + 2 + 1 = k + 3 by omega]
      rw [this, show k + 1 + 2 = k + 3 by omega] at hsum
      rw [this, hsum, ih1, ih0]
      have hk : k + 1 + 1 = k + 2 := by omega
      rw [hk]
      have f1 : fib (k + 3) = fib (k + 1) + fib (k + 2) := by
        rw [show k + 3 = k + 1 + 2 by omega, fib_add_two]
      have f0 : fib (k + 2) = fib k + fib (k + 1) := fib_add_two
      rw [f1, f0]
      ring

lemma c0_zmod : (c 0 : ZMod 195318521017) = ↑(77940394259 : ℕ) := by
  unfold c
  rw [Nat.cast_add, A355898_3773_zmod]
  norm_num

lemma c1_zmod : (c 1 : ZMod 195318521017) = ↑(99768150822 : ℕ) := by
  unfold c
  rw [show 3773 + 1 = 3774 by omega, Nat.cast_add, A355898_3774_zmod]
  norm_num

lemma nat_mod_eval_K :
    (99768150822 * 21827756563 + 77940394259 * 117378126758) % 195318521017 = 1 := by
  decide

lemma nat_mod_eval_Kp1 :
    (99768150822 * 139205883321 + 77940394259 * 21827756563) % 195318521017 = 1 := by
  decide

lemma c_Kidx_zmod
    (hf1 : ∀ n, 3775 ≤ n → A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2)) :
    (c 249580073233 : ZMod 195318521017) = 1 := by
  have hf := c_formula hf1 249580073232
  -- c 249580073233 = c 1 * fib 249580073233 + c 0 * fib 249580073232
  rw [show 249580073232 + 1 = 249580073233 by omega] at hf
  rw [hf, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, c0_zmod, c1_zmod,
      fib_Kidx_zmod, fib_Km1_zmod, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_add]
  have one_cast : (1 : ZMod 195318521017) = ((1 : ℕ) : ZMod 195318521017) :=
    Nat.cast_one.symm
  rw [one_cast, ZMod.natCast_eq_natCast_iff, Nat.ModEq, nat_mod_eval_K]

lemma c_succ_Kidx_zmod
    (hf1 : ∀ n, 3775 ≤ n → A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2)) :
    (c 249580073234 : ZMod 195318521017) = 1 := by
  have hf := c_formula hf1 249580073233
  rw [show 249580073233 + 1 = 249580073234 by omega] at hf
  rw [hf, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, c0_zmod, c1_zmod,
      fib_Kp1_zmod, fib_Kidx_zmod, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_add]
  have one_cast : (1 : ZMod 195318521017) = ((1 : ℕ) : ZMod 195318521017) :=
    Nat.cast_one.symm
  rw [one_cast, ZMod.natCast_eq_natCast_iff, Nat.ModEq, nat_mod_eval_Kp1]

lemma pMod_dvd_A355898_of_c
    (k : ℕ) (hk : (c k : ZMod 195318521017) = 1) :
    195318521017 ∣ A355898 (3773 + k) := by
  have hc : (c k : ZMod 195318521017) = (A355898 (3773 + k) : ZMod 195318521017) + 1 := by
    unfold c
    exact Nat.cast_add _ _
  have : (A355898 (3773 + k) : ZMod 195318521017) = 0 := by
    rw [hk] at hc
    exact add_right_cancel (b := (1 : ZMod 195318521017)) (by
      rw [zero_add]
      exact hc.symm)
  exact (ZMod.natCast_eq_zero_iff _ _).1 this

lemma A355898_of_ge_three {n : ℕ} (hn : 3 ≤ n) :
    A355898 n =
      let g := Nat.gcd (A355898 (n - 1)) (A355898 (n - 2))
      g + (A355898 (n - 1) + A355898 (n - 2)) / g := by
  have h : n = n - 3 + 3 := by omega
  nth_rw 1 [h]
  rw [A355898_add_three]
  have h1 : n - 3 + 2 = n - 1 := by omega
  have h2 : n - 3 + 1 = n - 2 := by omega
  simp [h1, h2]

lemma le_3775_N : 3775 ≤ 3773 + 249580073233 + 2 := by omega

lemma le_3_N : 3 ≤ 3773 + 249580073233 + 2 := by omega

lemma sub_N_one : 3773 + 249580073233 + 2 - 1 = 3773 + 249580073234 := by omega

lemma sub_N_two : 3773 + 249580073233 + 2 - 2 = 3773 + 249580073233 := by omega

lemma formula1_at_N
    (hf1 : ∀ n, 3775 ≤ n → A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2)) :
    A355898 (3773 + 249580073233 + 2) =
      1 + A355898 (3773 + 249580073234) + A355898 (3773 + 249580073233) := by
  have h := hf1 (3773 + 249580073233 + 2) le_3775_N
  rw [sub_N_one, sub_N_two] at h
  exact h

lemma A355898_N_rec :
    A355898 (3773 + 249580073233 + 2) =
      let g := Nat.gcd (A355898 (3773 + 249580073234)) (A355898 (3773 + 249580073233))
      g + (A355898 (3773 + 249580073234) + A355898 (3773 + 249580073233)) / g := by
  have h := A355898_of_ge_three (n := 3773 + 249580073233 + 2) le_3_N
  rw [sub_N_one, sub_N_two] at h
  exact h

lemma contradiction_of_g_q (g q s : ℕ) (hg : 1 < g) (hs : g + g ≤ s)
    (heq : g + q = 1 + s) (hsg : q * g = s) : False := by
  have hg0 : 0 < g := lt_trans (by decide : (0 : ℕ) < 1) hg
  have h2g : 2 * g ≤ s := by simpa [two_mul] using hs
  have hq2 : 2 ≤ q := by
    have : 2 * g ≤ q * g := by simpa [hsg] using h2g
    have := Nat.le_of_mul_le_mul_right this hg0
    simpa [Nat.mul_comm q, Nat.mul_comm 2] using this
  have heq' : g + q = 1 + q * g := by rw [heq, ← hsg]
  have hcancel : g - 1 = q * (g - 1) := by
    have hg1 : 1 ≤ g := le_of_lt hg
    zify [hg1] at heq' ⊢
    linarith
  have hne : 0 < g - 1 := Nat.sub_pos_of_lt hg
  have hq1 : q = 1 :=
    Nat.eq_of_mul_eq_mul_right hne (by rw [Nat.one_mul]; exact hcancel.symm)
  exact (hq2.trans_eq hq1).not_gt (by decide : (1 : ℕ) < 2)

/-- The three claimed identities do not all hold for every `n ≥ 3775`. -/
theorem oeis_a355898_conjecture.disproof :
    ¬ (∀ (n : ℕ), 3775 ≤ n →
        (A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
        ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
        ∧ (A355898 n =
            (A355898 3774 + 1) * Nat.fib (n - 3772) -
              (A355898 3772 + 1) * Nat.fib (n - 3774) - 1)) := by
  intro hconj
  have hf1 : ∀ n, 3775 ≤ n → A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2) :=
    fun n hn => (hconj n hn).1
  have hdiv1 : 195318521017 ∣ A355898 (3773 + 249580073234) :=
    pMod_dvd_A355898_of_c _ (c_succ_Kidx_zmod hf1)
  have hdiv2 : 195318521017 ∣ A355898 (3773 + 249580073233) :=
    pMod_dvd_A355898_of_c _ (c_Kidx_zmod hf1)
  have hpos1 : 0 < A355898 (3773 + 249580073234) :=
    A355898_pos _ (Nat.add_pos_left (by decide : (0 : ℕ) < 3773) _)
  have hpos2 : 0 < A355898 (3773 + 249580073233) :=
    A355898_pos _ (Nat.add_pos_left (by decide : (0 : ℕ) < 3773) _)
  set a1 := A355898 (3773 + 249580073234)
  set a2 := A355898 (3773 + 249580073233)
  set g := Nat.gcd a1 a2
  have hg : 195318521017 ∣ g := Nat.dvd_gcd hdiv1 hdiv2
  have gpos : 1 < g :=
    lt_of_lt_of_le (by decide : (1 : ℕ) < 195318521017)
      (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hpos1) hg)
  set s := a1 + a2
  set q := s / g
  have hdef : A355898 (3773 + 249580073233 + 2) = g + q := by
    simpa [a1, a2, g, s, q] using A355898_N_rec
  have hform := formula1_at_N hf1
  have heq : g + q = 1 + s := by
    rw [← hdef, hform]
    simp only [a1, a2, s, Nat.add_assoc]
  have hsg : q * g = s :=
    Nat.div_mul_cancel (Nat.dvd_add (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _))
  have hs2 : g + g ≤ s :=
    Nat.add_le_add (Nat.le_of_dvd hpos1 (Nat.gcd_dvd_left _ _))
      (Nat.le_of_dvd hpos2 (Nat.gcd_dvd_right _ _))
  exact contradiction_of_g_q g q s gpos hs2 heq hsg

