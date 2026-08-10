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

-- The formalization of the conjecture C A091669 from Jan 19 2020.
/--
Conjecture A091669: (for $n > 2$), if $n \mid a(n-1) + 2^{n-2}$, then $n$ is a prime
for which 2 is a primitive root modulo $n$ (A001122).
Note: We use `ZMod n` for the modulo ring and assume `totient` is available through `Mathlib`.
-/
theorem a091669_conjecture_primitive_root (n : ℕ) (hn : n > 2) :
  n ∣ (a (n - 1) + 2 ^ (n - 2)) →
  Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) := by
  intro hdvd
  have hp : Nat.Prime n := sorry
  constructor
  · exact hp
  · have h_totient : Nat.totient n = n - 1 := Nat.totient_prime hp
    rw [IsPrimitiveRoot.iff_orderOf, h_totient]
    haveI : Fact n.Prime := ⟨hp⟩
    have h2_ne_zero : (2 : ZMod n) ≠ 0 := by
      intro h_zero
      have h_zero' : ((2 : ℕ) : ZMod n) = 0 := h_zero
      rw [ZMod.natCast_eq_zero_iff] at h_zero'
      have : n ≤ 2 := Nat.le_of_dvd (by decide) h_zero'
      omega
    have h_order_dvd : orderOf (2 : ZMod n) ∣ n - 1 := ZMod.orderOf_dvd_card_sub_one h2_ne_zero
    by_contra h_ne
    have h_not_dvd : ¬ n ∣ 2 := by
      intro h_dvd
      have : n ≤ 2 := Nat.le_of_dvd (by decide) h_dvd
      omega
    have h_cop : Nat.Coprime 2 n := (hp.coprime_iff_not_dvd.mpr h_not_dvd).symm
    let u : (ZMod n)ˣ := ZMod.unitOfCoprime 2 h_cop
    have hd_pos_units : 0 < orderOf u := orderOf_pos u
    have h_coe_u : (u : ZMod n) = 2 := ZMod.coe_unitOfCoprime 2 h_cop
    have h_order_eq : orderOf (2 : ZMod n) = orderOf u := by
      rw [← h_coe_u, orderOf_units]
    have hd_pos : 0 < orderOf (2 : ZMod n) := by
      rw [h_order_eq]
      exact hd_pos_units
    have hd_lt : orderOf (2 : ZMod n) < n - 1 := lt_of_le_of_ne (Nat.le_of_dvd (by omega) h_order_dvd) h_ne
    have h_mem : orderOf (2 : ZMod n) ∈ Finset.Ico 1 (n - 1) := by
      rw [Finset.mem_Ico]
      exact ⟨hd_pos, hd_lt⟩
    let d := orderOf (2 : ZMod n)
    have h_pow_one : (2 : ZMod n) ^ d = 1 := pow_orderOf_eq_one (2 : ZMod n)
    have h_cast : ((2 ^ d : ℕ) : ZMod n) = (2 : ZMod n) ^ d := by push_cast; rfl
    have h_pow_one' : ((2 ^ d : ℕ) : ZMod n) = 1 := h_cast.trans h_pow_one
    have hd_ge_one : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by omega)
    have h_sub_zero : (((2 ^ d - 1 : ℕ) : ZMod n)) = 0 := by
      have h_eq : (2 ^ d : ℕ) = (2 ^ d - 1) + 1 := (Nat.sub_add_cancel hd_ge_one).symm
      have h_eq' : ((2 ^ d : ℕ) : ZMod n) = (((2 ^ d - 1 : ℕ) : ZMod n)) + 1 := by
        rw [h_eq]
        push_cast
        rfl
      rw [h_pow_one'] at h_eq'
      have h_eq'' : (((2 ^ d - 1 : ℕ) : ZMod n)) + 1 = 0 + 1 := by
        rw [zero_add]
        exact h_eq'.symm
      exact add_right_cancel h_eq''
    have h_div_sub : n ∣ 2 ^ d - 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      exact h_sub_zero
    have h_dvd_prod : (2 ^ d - 1) ∣ (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := Finset.dvd_prod_of_mem _ h_mem
    have h_n_dvd_prod : n ∣ (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := dvd_trans h_div_sub h_dvd_prod
    have h_n_dvd_num : n ∣ ((2 ^ (n - 2)) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := dvd_mul_of_dvd_right h_n_dvd_prod _
    have h_not_dvd_fact : ¬ n ∣ (n - 1).factorial := by
      intro h_dvd
      have h_le : n ≤ n - 1 := (hp.dvd_factorial).mp h_dvd
      omega
    have h_exact : (n - 1).factorial ∣ ((2 ^ (n - 2)) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := sorry
    have ha_eq : a (n - 1) = ((2 ^ (n - 1).pred) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) / (n - 1).factorial := by
      unfold a
      split_ifs with h0
      · omega
      · rfl
    have h_pred : (n - 1).pred = n - 2 := by
      have : n - 1 = (n - 2) + 1 := by omega
      rw [this]
      rfl
    have ha_eq' : a (n - 1) = ((2 ^ (n - 2)) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) / (n - 1).factorial := by
      rw [← h_pred]
      exact ha_eq
    have h_exact_eq : ((2 ^ (n - 2)) * (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) = a (n - 1) * (n - 1).factorial := by
      rw [ha_eq']
      exact (Nat.div_mul_cancel h_exact).symm
    have h_n_dvd_mul : n ∣ a (n - 1) * (n - 1).factorial := by
      rw [← h_exact_eq]
      exact h_n_dvd_num
    have h_dvd_a : n ∣ a (n - 1) := by
      rcases hp.dvd_mul.mp h_n_dvd_mul with h1 | h2
      · exact h1
      · contradiction
    have h_dvd_pow2 : n ∣ 2 ^ (n - 2) := (@Nat.dvd_add_iff_right n (a (n - 1)) (2 ^ (n - 2)) h_dvd_a).mpr hdvd
    have h_dvd_2 : n ∣ 2 := hp.dvd_of_dvd_pow h_dvd_pow2
    have : n ≤ 2 := Nat.le_of_dvd (by decide) h_dvd_2
    omega
