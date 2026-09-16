import Submission.Spec
import Mathlib

open Nat Finset ArithmeticFunction

def f : ArithmeticFunction ℕ := ArithmeticFunction.id.pmul (sigma 0)
def F : ArithmeticFunction ℕ := f * zeta

lemma f_mult : f.IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.pmul isMultiplicative_id (isMultiplicative_sigma (k := 0))

lemma F_mult : F.IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.mul f_mult isMultiplicative_zeta

lemma f_apply {n : ℕ} : f n = n * (Nat.divisors n).card := by
  rw [f, pmul_apply, id_apply]
  have : (sigma 0) n = (Nat.divisors n).card := by simp [sigma]
  rw [this]

lemma F_apply {n : ℕ} (hn : n ≠ 0) : F n = ∑ d ∈ n.divisors, d * (Nat.divisors d).card := by
  unfold F
  rw [mul_apply]
  have : (∑ x ∈ n.divisorsAntidiagonal, f x.1 * zeta x.2) =
    ∑ i ∈ n.divisors, f i * zeta (n / i) := by
    exact Nat.sum_divisorsAntidiagonal (fun a b => f a * zeta b)
  rw [this]
  apply Finset.sum_congr rfl
  intro d hd
  have h_nd : n / d ≠ 0 := by
    rw [Nat.mem_divisors] at hd
    intro h_zero
    have : d * (n / d) = n := Nat.mul_div_cancel' hd.1
    rw [h_zero, mul_zero] at this
    exact hn this.symm
  rw [zeta_apply, if_neg h_nd, mul_one, f_apply]


lemma a_eq_F (n : ℕ) (hn : 0 < n) : a n = F n - n * (Nat.divisors n).card := by
  unfold a
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
  rw [F_apply hn_ne]

lemma F_p (p : ℕ) (hp : p.Prime) : F p = 1 + 2 * p := by
  have hp_ne : p ≠ 0 := hp.ne_zero
  rw [F_apply hp_ne]
  have h_divs : p.divisors = {1, p} := Nat.Prime.divisors hp
  rw [h_divs]
  have h_ne : p ≠ 1 := hp.ne_one
  have h_not_mem : p ∉ ({1} : Finset ℕ) := by rw [mem_singleton]; exact h_ne
  have h_eq : ({1, p} : Finset ℕ) = {p, 1} := by ext x; simp only [mem_insert, mem_singleton]; tauto
  rw [h_eq, sum_insert h_not_mem, sum_singleton]
  have tau1 : (Nat.divisors 1).card = 1 := rfl
  have taup : (Nat.divisors p).card = 2 := by
    rw [h_divs, h_eq, card_insert_of_notMem h_not_mem, card_singleton]
  rw [tau1, taup]
  ring

lemma F_pm {p m : ℕ} (h_coprime : p.Coprime m) :
  F (p * m) = F p * F m := by
  exact F_mult.map_mul_of_coprime h_coprime

lemma F_ge_n_tau {n : ℕ} (hn : 0 < n) : F n ≥ n * (Nat.divisors n).card := by
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
  rw [F_apply hn_ne]
  have h_in : n ∈ n.divisors := by rw [Nat.mem_divisors]; exact ⟨dvd_refl n, hn_ne⟩
  have h_split := Finset.sum_erase_add n.divisors (fun d => d * (Nat.divisors d).card) h_in
  rw [add_comm] at h_split
  rw [← h_split]
  exact Nat.le_add_right _ _
