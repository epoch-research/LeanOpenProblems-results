import Submission.Lib
open Finset

lemma coprime_p3 (p : ℕ) (hp : Nat.Prime p) (a : ℤ) (h : ¬(p:ℤ)∣a) :
    IsCoprime ((p:ℤ)^3) a := by
  have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  exact (hpp.coprime_iff_not_dvd.mpr h).pow_left

lemma nonsingular_step (p n : ℕ) (hp : Nat.Prime p)
    (hP0 : ¬ (p:ℤ) ∣ Rec374605.P0 ↑n)
    (h1 : ((p:ℤ)^3) ∣ Rec374605.aSeq (n+1))
    (h2 : ((p:ℤ)^3) ∣ Rec374605.aSeq (n+2)) :
    ((p:ℤ)^3) ∣ Rec374605.aSeq n := by
  have hrec := Rec374605.aSeq_rec n
  have hdvd : ((p:ℤ)^3) ∣ Rec374605.P0 ↑n * Rec374605.aSeq n := by
    have : Rec374605.P0 ↑n * Rec374605.aSeq n
        = -(Rec374605.P1 ↑n * Rec374605.aSeq (n+1) + Rec374605.P2 ↑n * Rec374605.aSeq (n+2)) := by
      linear_combination hrec
    rw [this]
    exact (dvd_neg).mpr (dvd_add (Dvd.dvd.mul_left h1 _) (Dvd.dvd.mul_left h2 _))
  exact (coprime_p3 p hp _ hP0).dvd_of_dvd_mul_left hdvd

-- band helper: a*p < x < (a+1)*p ⟹ p ∤ x
lemma notdvd_band (p x a : ℕ) (hlo : a * p < x) (hhi : x < (a+1) * p) : ¬ p ∣ x := by
  rintro ⟨k, hk⟩
  have h1 : a < k := by
    apply Nat.lt_of_mul_lt_mul_left (a := p)
    calc p * a = a * p := Nat.mul_comm p a
      _ < x := hlo
      _ = p * k := hk
  have h2 : k < a + 1 := by
    apply Nat.lt_of_mul_lt_mul_left (a := p)
    calc p * k = x := hk.symm
      _ < (a+1) * p := hhi
      _ = p * (a+1) := Nat.mul_comm (a+1) p
  omega

lemma notdvd_bandZ (p x a : ℕ) (hlo : a * p < x) (hhi : x < (a+1) * p) : ¬ (p:ℤ) ∣ (x:ℤ) := by
  intro h
  exact notdvd_band p x a hlo hhi (by exact_mod_cast h)

lemma notdvd_P0 (p n : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hlo : 2*p ≤ 3*n) (hhi : n + 3 ≤ p)
    (hQ : ¬ (p:ℤ) ∣ Rec374605.Q0val ↑n) :
    ¬ (p:ℤ) ∣ Rec374605.P0 ↑n := by
  have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have nd_mul : ∀ a b : ℤ, ¬(p:ℤ)∣a → ¬(p:ℤ)∣b → ¬(p:ℤ)∣(a*b) :=
    fun a b ha hb h => (hpp.dvd_mul.mp h).elim ha hb
  have nd_pow : ∀ (a : ℤ) (m : ℕ), ¬(p:ℤ)∣a → ¬(p:ℤ)∣(a^m) :=
    fun a m ha h => ha (hpp.dvd_of_dvd_pow h)
  have e2 : ¬ (p:ℤ) ∣ ((n:ℤ)+2) := by
    intro h
    have : (p:ℤ) ∣ ((n+2:ℕ):ℤ) := by push_cast; convert h using 1
    exact notdvd_band p (n+2) 0 (by omega) (by omega) (by exact_mod_cast this)
  have e31 : ¬ (p:ℤ) ∣ (3*(n:ℤ)+1) := by
    intro h
    have : (p:ℤ) ∣ ((3*n+1:ℕ):ℤ) := by push_cast; convert h using 1
    exact notdvd_band p (3*n+1) 2 (by omega) (by omega) (by exact_mod_cast this)
  have e32 : ¬ (p:ℤ) ∣ (3*(n:ℤ)+2) := by
    intro h
    have : (p:ℤ) ∣ ((3*n+2:ℕ):ℤ) := by push_cast; convert h using 1
    exact notdvd_band p (3*n+2) 2 (by omega) (by omega) (by exact_mod_cast this)
  have e27 : ¬ (p:ℤ) ∣ (-27 : ℤ) := by
    intro h
    rw [Int.dvd_neg] at h
    have h3 : (p:ℤ) ∣ (3:ℤ) := hpp.dvd_of_dvd_pow (show (p:ℤ)∣(3:ℤ)^3 by rw [show ((3:ℤ)^3)=27 by norm_num]; exact h)
    have : p ∣ 3 := by exact_mod_cast h3
    have := Nat.le_of_dvd (by norm_num) this; omega
  have hQ' : ¬ (p:ℤ) ∣ (5616 * (n:ℤ) ^ 4 + 36504 * (n:ℤ) ^ 3 + 88731 * (n:ℤ) ^ 2 + 95597 * (n:ℤ) + 38524) := by
    rw [show (5616 * (n:ℤ) ^ 4 + 36504 * (n:ℤ) ^ 3 + 88731 * (n:ℤ) ^ 2 + 95597 * (n:ℤ) + 38524) = Rec374605.Q0val ↑n from by unfold Rec374605.Q0val; ring]
    exact hQ
  unfold Rec374605.P0
  exact nd_mul _ _ (nd_mul _ _ (nd_mul _ _ (nd_mul _ _ e27 e2) (nd_pow _ 3 e31)) (nd_pow _ 3 e32)) hQ'

lemma notdvd_Udes (p n : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hlo : 2*p ≤ 3*n) (hhi : n + 3 ≤ p) :
    ¬ (p:ℤ) ∣ Rec374605.Udes ↑n := by
  have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have nd_mul : ∀ a b : ℤ, ¬(p:ℤ)∣a → ¬(p:ℤ)∣b → ¬(p:ℤ)∣(a*b) :=
    fun a b ha hb h => (hpp.dvd_mul.mp h).elim ha hb
  have nd_pow : ∀ (a : ℤ) (m : ℕ), ¬(p:ℤ)∣a → ¬(p:ℤ)∣(a^m) :=
    fun a m ha h => ha (hpp.dvd_of_dvd_pow h)
  have e2 : ¬ (p:ℤ) ∣ ((n:ℤ)+2) := by
    intro h
    have : (p:ℤ) ∣ ((n+2:ℕ):ℤ) := by push_cast; convert h using 1
    exact notdvd_band p (n+2) 0 (by omega) (by omega) (by exact_mod_cast this)
  have e31 : ¬ (p:ℤ) ∣ (3*(n:ℤ)+1) := by
    intro h
    have : (p:ℤ) ∣ ((3*n+1:ℕ):ℤ) := by push_cast; convert h using 1
    exact notdvd_band p (3*n+1) 2 (by omega) (by omega) (by exact_mod_cast this)
  have e32 : ¬ (p:ℤ) ∣ (3*(n:ℤ)+2) := by
    intro h
    have : (p:ℤ) ∣ ((3*n+2:ℕ):ℤ) := by push_cast; convert h using 1
    exact notdvd_band p (3*n+2) 2 (by omega) (by omega) (by exact_mod_cast this)
  have e27 : ¬ (p:ℤ) ∣ (-27 : ℤ) := by
    intro h
    rw [Int.dvd_neg] at h
    have h3 : (p:ℤ) ∣ (3:ℤ) := hpp.dvd_of_dvd_pow (show (p:ℤ)∣(3:ℤ)^3 by rw [show ((3:ℤ)^3)=27 by norm_num]; exact h)
    have : p ∣ 3 := by exact_mod_cast h3
    have := Nat.le_of_dvd (by norm_num) this; omega
  unfold Rec374605.Udes
  exact nd_mul _ _ (nd_mul _ _ (nd_mul _ _ e27 e2) (nd_pow _ 3 e31)) (nd_pow _ 3 e32)

lemma singular_step (p n : ℕ) (hp : Nat.Prime p)
    (hC : ¬ (p:ℤ) ∣ (Rec374605.Udes ↑n * Rec374605.P0 (↑n+1)))
    (h2 : ((p:ℤ)^3) ∣ Rec374605.aSeq (n+2))
    (h3 : ((p:ℤ)^3) ∣ Rec374605.aSeq (n+3)) :
    ((p:ℤ)^3) ∣ Rec374605.aSeq n := by
  have hdes := Rec374605.aSeq_desing n
  have hdvd : ((p:ℤ)^3) ∣ (Rec374605.Udes ↑n * Rec374605.P0 (↑n+1)) * Rec374605.aSeq n := by
    have : (Rec374605.Udes ↑n * Rec374605.P0 (↑n+1)) * Rec374605.aSeq n
        = Rec374605.Cqdes ↑n * Rec374605.aSeq (n+3) - Rec374605.Bqdes ↑n * Rec374605.aSeq (n+2) := by
      linear_combination hdes
    rw [this]
    exact dvd_sub (Dvd.dvd.mul_left h3 _) (Dvd.dvd.mul_left h2 _)
  exact (coprime_p3 p hp _ hC).dvd_of_dvd_mul_left hdvd
