import FormalConjectures.Util.ProblemImports

open Nat

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

/--
Conjecture: For n >= 3775 a(n) can also be expressed in the following three ways:
1) a(n) = 1 + a(n-1) + a(n-2).
2) a(n) = 2*a(n-1) - a(n-3).
3) If A = a(3774), B = a(3772) and F = Fibonacci A000045(n),
   a(n) = (A+1)*F(n-3772) - (B+1)*F(n-3774) - 1.
These three formulas only work for n >= 3775.
-/
theorem oeis_a355898_conjecture (n : ℕ) (h : 3775 ≤ n) :
  (A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
  ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
  ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1) :=
by sorry

def p := 195318521017

def loop (n : ℕ) (prev curr : ℕ) : ℕ :=
  match n with
  | 0 => curr
  | k + 1 =>
      let g := Nat.gcd curr prev
      loop k curr (g + (curr + prev) / g)

theorem loop_eq (n : ℕ) : ∀ k, loop n (A355898 (k + 1)) (A355898 (k + 2)) = A355898 (n + k + 2) := by
  induction n with
  | zero =>
    intro k
    rw [Nat.zero_add]
    rfl
  | succ n ih =>
    intro k
    calc
      loop (n + 1) (A355898 (k + 1)) (A355898 (k + 2))
        = loop n (A355898 (k + 2)) (Nat.gcd (A355898 (k + 2)) (A355898 (k + 1)) + (A355898 (k + 2) + A355898 (k + 1)) / Nat.gcd (A355898 (k + 2)) (A355898 (k + 1))) := by rfl
      _ = loop n (A355898 (k + 2)) (A355898 (k + 3)) := by rfl
      _ = A355898 (n + (k + 1) + 2) := ih (k + 1)
      _ = A355898 (n + 1 + k + 2) := by congr 1; omega

theorem A355898_eq_loop (n : ℕ) : A355898 (n + 2) = loop n 1 1 := by
  have h := loop_eq n 0
  change loop n (A355898 1) (A355898 2) = A355898 (n + 0 + 2) at h
  rw [show A355898 1 = 1 from rfl, show A355898 2 = 1 from rfl] at h
  rw [Nat.add_zero] at h
  exact h.symm

set_option maxRecDepth 200000

lemma A3774_mod_loop : loop 3772 1 1 = 58247620166949433924152349110387952083697979943894432862563828976040095229520447551846447106151838744759854302693877131497631690251007647345990824945923089962629840263458365713419764969401061223771086474022889794898006618157003102858034604369810330403334719184536749507414607510201847709900422830948846697746280327160364518807058513260008283 := by decide
lemma A3772_mod_loop : loop 3770 1 1 = 50821856637385792267808398991468475721843483337998623640757098602636928393269892952934230874475945024513818501434870581449774982213886818298525314166884933137805368884278748201859762766881515372183084024083577995511024802455180968712692288879507888937250291063504680754992157949256964474278019411768646907989461240384266638096191096905619665 := by decide

lemma A3774_mod : (((A355898 3774 + 1 : ℕ) : ZMod p)) = 99768150822 := by
  have h : A355898 3774 = loop 3772 1 1 := A355898_eq_loop 3772
  rw [h, A3774_mod_loop]
  rfl

lemma A3772_mod : (((A355898 3772 + 1 : ℕ) : ZMod p)) = 21827756563 := by
  have h : A355898 3772 = loop 3770 1 1 := A355898_eq_loop 3770
  rw [h, A3772_mod_loop]
  rfl

lemma fib_le (n : ℕ) : Nat.fib n ≤ 2 * Nat.fib (n+1) := by
  have : Nat.fib n ≤ Nat.fib (n+1) := Nat.fib_le_fib_succ
  omega

lemma fib_mod_bit0 (n : ℕ) :
  (Nat.fib (2 * n) : ZMod p) = (Nat.fib n : ZMod p) * (2 * (Nat.fib (n+1) : ZMod p) - (Nat.fib n : ZMod p)) := by
  rw [Nat.fib_two_mul, Nat.cast_mul, Nat.cast_sub (fib_le n)]
  push_cast
  rfl

lemma fib_mod_bit1 (n : ℕ) :
  (Nat.fib (2 * n + 1) : ZMod p) = (Nat.fib (n+1) : ZMod p)^2 + (Nat.fib n : ZMod p)^2 := by
  rw [Nat.fib_two_mul_add_one]
  push_cast
  rfl

lemma fib_mod_bit2 (n : ℕ) :
  (Nat.fib (2 * n + 2) : ZMod p) = (Nat.fib (2 * n) : ZMod p) + (Nat.fib (2 * n + 1) : ZMod p) := by
  have : Nat.fib (2 * n + 2) = Nat.fib (2 * n) + Nat.fib (2 * n + 1) := by
    rw [Nat.fib_add_two]
  rw [this]
  push_cast
  ring

def fib_bits_ZMod (bits : List Bool) (val : ZMod p × ZMod p) : ZMod p × ZMod p :=
  match bits with
  | [] => val
  | b :: bs =>
      let (fk, fk1) := val
      let fk2 := fk * fk
      let fk12 := fk1 * fk1
      let f2k := fk * (2 * fk1 - fk)
      let f2k1 := fk2 + fk12
      let f2k2 := f2k + f2k1
      let next_val := if b then (f2k1, f2k2) else (f2k, f2k1)
      fib_bits_ZMod bs next_val

def bits_val (bits : List Bool) (init : ℕ) : ℕ :=
  match bits with
  | [] => init
  | b :: bs => bits_val bs (2 * init + if b then 1 else 0)

lemma fib_bits_ZMod_eq (bits : List Bool) (init : ℕ) (val : ZMod p × ZMod p)
    (h : val = ((Nat.fib init : ZMod p), (Nat.fib (init + 1) : ZMod p))) :
  fib_bits_ZMod bits val = ((Nat.fib (bits_val bits init) : ZMod p), (Nat.fib (bits_val bits init + 1) : ZMod p)) := by
  induction bits generalizing init val with
  | nil =>
    exact h
  | cons b bs ih =>
    apply ih
    subst h
    dsimp [fib_bits_ZMod, bits_val]
    ext
    · cases b
      · dsimp
        rw [fib_mod_bit0]
      · dsimp
        rw [fib_mod_bit1]
        ring
    · cases b
      · dsimp
        have h1 : 2 * init + 0 + 1 = 2 * init + 1 := by omega
        rw [h1]
        rw [fib_mod_bit1]
        ring
      · dsimp
        have h1 : 2 * init + 1 + 1 = 2 * init + 2 := by omega
        rw [h1]
        rw [fib_mod_bit2, fib_mod_bit0, fib_mod_bit1]
        ring

def bits_N_3774 : List Bool :=
  [true, true, true, false, true, false, false, false, false, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, false, false, true, false, false, false, true, false, false, false, false]
def bits_N_3772 : List Bool :=
  [true, true, true, false, true, false, false, false, false, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, false, false, true, false, false, false, true, false, false, true, false]

def bits_N1_3774 : List Bool :=
  [true, true, true, false, true, false, false, false, false, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, false, false, true, false, false, false, true, false, false, false, true]
def bits_N1_3772 : List Bool :=
  [true, true, true, false, true, false, false, false, false, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, false, false, true, false, false, false, true, false, false, true, true]

lemma bits_N_3774_val : bits_val bits_N_3774 0 = 249580073232 := by rfl
lemma bits_N_3772_val : bits_val bits_N_3772 0 = 249580073234 := by rfl
lemma bits_N1_3774_val : bits_val bits_N1_3774 0 = 249580073233 := by rfl
lemma bits_N1_3772_val : bits_val bits_N1_3772 0 = 249580073235 := by rfl

def N := 249580077006

lemma F_N_3774_val : (Nat.fib (N - 3774) : ZMod p) = (fib_bits_ZMod bits_N_3774 (0, 1)).1 := by
  have h := fib_bits_ZMod_eq bits_N_3774 0 (0, 1) rfl
  have h_val : bits_val bits_N_3774 0 = N - 3774 := bits_N_3774_val
  rw [h_val] at h
  exact h.symm ▸ rfl

lemma F_N_3772_val : (Nat.fib (N - 3772) : ZMod p) = (fib_bits_ZMod bits_N_3772 (0, 1)).1 := by
  have h := fib_bits_ZMod_eq bits_N_3772 0 (0, 1) rfl
  have h_val : bits_val bits_N_3772 0 = N - 3772 := bits_N_3772_val
  rw [h_val] at h
  exact h.symm ▸ rfl

lemma F_N1_3774_val : (Nat.fib (N + 1 - 3774) : ZMod p) = (fib_bits_ZMod bits_N1_3774 (0, 1)).1 := by
  have h := fib_bits_ZMod_eq bits_N1_3774 0 (0, 1) rfl
  have h_val : bits_val bits_N1_3774 0 = N + 1 - 3774 := bits_N1_3774_val
  rw [h_val] at h
  exact h.symm ▸ rfl

lemma F_N1_3772_val : (Nat.fib (N + 1 - 3772) : ZMod p) = (fib_bits_ZMod bits_N1_3772 (0, 1)).1 := by
  have h := fib_bits_ZMod_eq bits_N1_3772 0 (0, 1) rfl
  have h_val : bits_val bits_N1_3772 0 = N + 1 - 3772 := bits_N1_3772_val
  rw [h_val] at h
  exact h.symm ▸ rfl

lemma eval_N : (99768150822 : ZMod p) * (fib_bits_ZMod bits_N_3772 (0, 1)).1 - (21827756563 : ZMod p) * (fib_bits_ZMod bits_N_3774 (0, 1)).1 = 1 := by rfl
lemma eval_N1 : (99768150822 : ZMod p) * (fib_bits_ZMod bits_N1_3772 (0, 1)).1 - (21827756563 : ZMod p) * (fib_bits_ZMod bits_N1_3774 (0, 1)).1 = 1 := by rfl

lemma sub_eq (x y z : ℕ) (h : x = y - z - 1) (hx : x ≥ 1) : x + z + 1 = y := by omega

lemma zero_of_mod (aN B_F1 A_F2 : ℕ)
    (h1 : aN + B_F1 + 1 = A_F2)
    (h2 : (A_F2 : ZMod p) - (B_F1 : ZMod p) = 1) :
    p ∣ aN := by
  have h3 : (aN : ZMod p) + (B_F1 : ZMod p) + 1 = (A_F2 : ZMod p) := by
    have h1_cast := congrArg (fun x : ℕ => (x : ZMod p)) h1
    push_cast at h1_cast
    exact h1_cast
  have h4 : (aN : ZMod p) = 0 := by
    calc (aN : ZMod p) = (aN : ZMod p) + (B_F1 : ZMod p) + 1 - (B_F1 : ZMod p) - 1 := by ring
    _ = (A_F2 : ZMod p) - (B_F1 : ZMod p) - 1 := by rw [h3]
    _ = 1 - 1 := by rw [h2]
    _ = 0 := by ring
  exact (CharP.cast_eq_zero_iff (ZMod p) p aN).mp h4

lemma gcd_prop (g x a b : ℕ) (hg : g > 1) (hx : x = a + b) (h_g : g = Nat.gcd a b)
    (h_a : a > 0) (h_b : b > 0) (h2 : g + x / g = 1 + x) : False := by
  have h_dvd : g ∣ x := by
    rw [hx]
    exact dvd_add (h_g ▸ Nat.gcd_dvd_left a b) (h_g ▸ Nat.gcd_dvd_right a b)
  have h3 : (g + x / g) * g = (1 + x) * g := by rw [h2]
  rw [add_mul, Nat.div_mul_cancel h_dvd] at h3
  have h_xg : x = g := by
    zify at h3 hg
    nlinarith
  have h_gb : g ≤ b := by
    rw [h_g]
    exact Nat.le_of_dvd h_b (Nat.gcd_dvd_right a b)
  omega

lemma A355898_step (n : ℕ) :
  A355898 (n + 3) = Nat.gcd (A355898 (n+2)) (A355898 (n+1)) + (A355898 (n+2) + A355898 (n+1)) / Nat.gcd (A355898 (n+2)) (A355898 (n+1)) := rfl

lemma eq_proof (M : ℕ) (hM2_conj : A355898 (M + 2) = 1 + A355898 (M + 2 - 1) + A355898 (M + 2 - 2)) :
  A355898 (M + 2) = 1 + A355898 (M + 1) + A355898 M := by
  have h1 : M + 2 - 1 = M + 1 := by omega
  have h2 : M + 2 - 2 = M := by omega
  rw [h1, h2] at hM2_conj
  exact hM2_conj



lemma helper1 : (((A355898 3774 + 1) * Nat.fib (N - 3772) : ℕ) : ZMod p) = (((A355898 3774 + 1) : ℕ) : ZMod p) * (Nat.fib (N - 3772) : ZMod p) := Nat.cast_mul _ _
lemma helper2 : (((A355898 3772 + 1) * Nat.fib (N - 3774) : ℕ) : ZMod p) = (((A355898 3772 + 1) : ℕ) : ZMod p) * (Nat.fib (N - 3774) : ZMod p) := Nat.cast_mul _ _
lemma helper3 : (((A355898 3774 + 1) * Nat.fib (N + 1 - 3772) : ℕ) : ZMod p) = (((A355898 3774 + 1) : ℕ) : ZMod p) * (Nat.fib (N + 1 - 3772) : ZMod p) := Nat.cast_mul _ _
lemma helper4 : (((A355898 3772 + 1) * Nat.fib (N + 1 - 3774) : ℕ) : ZMod p) = (((A355898 3772 + 1) : ℕ) : ZMod p) * (Nat.fib (N + 1 - 3774) : ZMod p) := Nat.cast_mul _ _

lemma hN_mod_lemma (hN_eq1 : A355898 N + (A355898 3772 + 1) * Nat.fib (N - 3774) + 1 = (A355898 3774 + 1) * Nat.fib (N - 3772)) : p ∣ A355898 N := by
  have hN_mod : (((A355898 3774 + 1) * Nat.fib (N - 3772) : ℕ) : ZMod p) - (((A355898 3772 + 1) * Nat.fib (N - 3774) : ℕ) : ZMod p) = 1 := by
    rw [helper1, helper2, A3774_mod, A3772_mod, F_N_3772_val, F_N_3774_val]
    exact eval_N
  exact zero_of_mod (A355898 N) ((A355898 3772 + 1) * Nat.fib (N - 3774)) ((A355898 3774 + 1) * Nat.fib (N - 3772)) hN_eq1 hN_mod

lemma hN1_mod_lemma (hN1_eq1 : A355898 (N + 1) + (A355898 3772 + 1) * Nat.fib (N + 1 - 3774) + 1 = (A355898 3774 + 1) * Nat.fib (N + 1 - 3772)) : p ∣ A355898 (N + 1) := by
  have hN1_mod : (((A355898 3774 + 1) * Nat.fib (N + 1 - 3772) : ℕ) : ZMod p) - (((A355898 3772 + 1) * Nat.fib (N + 1 - 3774) : ℕ) : ZMod p) = 1 := by
    rw [helper3, helper4, A3774_mod, A3772_mod, F_N1_3772_val, F_N1_3774_val]
    exact eval_N1
  exact zero_of_mod (A355898 (N + 1)) ((A355898 3772 + 1) * Nat.fib (N + 1 - 3774)) ((A355898 3774 + 1) * Nat.fib (N + 1 - 3772)) hN1_eq1 hN1_mod

lemma H_lemma (H : ∀ (n : ℕ),
    3775 ≤ n →
      A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2) ∧
        A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3) ∧
          A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1) : False := by
  have hN := H N (by decide)
  have hN1 := H (N + 1) (by decide)
  have hN2 := H (N + 2) (by decide)

  have haN : A355898 N ≥ 1 := by omega
  have haN1 : A355898 (N + 1) ≥ 1 := by omega

  have hN_eq1 := sub_eq (A355898 N) ((A355898 3774 + 1) * Nat.fib (N - 3772)) ((A355898 3772 + 1) * Nat.fib (N - 3774)) hN.2.2 haN
  have hN1_eq1 := sub_eq (A355898 (N + 1)) ((A355898 3774 + 1) * Nat.fib (N + 1 - 3772)) ((A355898 3772 + 1) * Nat.fib (N + 1 - 3774)) hN1.2.2 haN1

  have h_div_N := hN_mod_lemma hN_eq1
  have h_div_N1 := hN1_mod_lemma hN1_eq1

  generalize hg : Nat.gcd (A355898 (N + 1)) (A355898 N) = g
  have h_g_div : p ∣ g := by
    rw [←hg]
    exact Nat.dvd_gcd h_div_N1 h_div_N
  have h_g_pos : g > 0 := by
    have h1 : A355898 N > 0 := by omega
    have h2 := Nat.gcd_pos_of_pos_right (A355898 (N + 1)) h1
    rw [hg] at h2
    exact h2
  have h_g_gt_1 : g > 1 := by
    calc g ≥ p := Nat.le_of_dvd h_g_pos h_g_div
         _ > 1 := by decide

  have hN2_def : A355898 (N + 2) = g + (A355898 (N + 1) + A355898 N) / g := by
    have h_step := A355898_step (N - 1)
    have h_sub1 : N - 1 + 2 = N + 1 := by rfl
    have h_sub2 : N - 1 + 1 = N := by rfl
    have h_sub3 : N - 1 + 3 = N + 2 := by rfl
    rw [h_sub1, h_sub2, h_sub3] at h_step
    rw [←hg]
    exact h_step

  have h_eq : g + (A355898 (N + 1) + A355898 N) / g = 1 + (A355898 (N + 1) + A355898 N) := by
    have hN2_conj_simp := eq_proof N hN2.1
    omega

  exact gcd_prop g (A355898 (N + 1) + A355898 N) (A355898 (N + 1)) (A355898 N) h_g_gt_1 rfl hg.symm (by omega) (by omega) h_eq

theorem oeis_a355898_conjecture.disproof : ¬ (type_of% @oeis_a355898_conjecture) := by
  intro H
  exact H_lemma H
