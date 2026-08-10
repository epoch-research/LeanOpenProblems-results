import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

/--
A352275: $a(0) = 1$ and
$$a(n) = \sum_{k = 0}^{2n} \frac{n}{n + 2k} \binom{n + 2k}{k} \text{ for } n \ge 1.$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    (range (2 * n + 1)).sum fun k : ℕ =>
      let term_q : ℚ := (n : ℚ) / (n + 2 * k : ℚ) * ((n + 2 * k).choose k : ℚ)
      (Rat.floor term_q).toNat

/--
More generally, for $m$ a positive integer, define a sequence $u_m$ by setting
$$u_m(n) = \sum_{k = 0}^{m n} \frac{n}{n + 2k} \binom{n + 2k}{k} \text{ for } n \ge 1.$$
We set $u_m(0) = 1$ to match the sequence $A352275 = u_2$.
-/
noncomputable def u (m n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    (range (m * n + 1)).sum fun k : ℕ =>
      let term_q : ℚ := (n : ℚ) / (n + 2 * k : ℚ) * ((n + 2 * k).choose k : ℚ)
      (Rat.floor term_q).toNat


lemma choose_relation (n k : ℕ) (hk : k > 0) :
    (n + 2 * k) * (n + 2 * k - 1).choose (k - 1) = (n + 2 * k).choose k * k := by
  have h1 : n + 2 * k - 1 + 1 = n + 2 * k := by
    omega
  have h2 : k - 1 + 1 = k := by
    omega
  have h3 := add_one_mul_choose_eq (n + 2 * k - 1) (k - 1)
  rw [h1, h2] at h3
  exact h3

lemma choose_relation_combined (n k : ℕ) (hk : k > 0) :
    n * (n + 2 * k).choose k + 2 * (n + 2 * k) * (n + 2 * k - 1).choose (k - 1) =
    (n + 2 * k) * (n + 2 * k).choose k := by
  have h := choose_relation n k hk
  calc n * (n + 2 * k).choose k + 2 * (n + 2 * k) * (n + 2 * k - 1).choose (k - 1)
    _ = n * (n + 2 * k).choose k + 2 * ((n + 2 * k) * (n + 2 * k - 1).choose (k - 1)) := by ring
    _ = n * (n + 2 * k).choose k + 2 * ((n + 2 * k).choose k * k) := by rw [h]
    _ = (n + 2 * k) * (n + 2 * k).choose k := by ring

lemma term_q_eq (n k : ℕ) (hn : n > 0) (hk : k > 0) :
    (n : ℚ) / (n + 2 * k : ℚ) * ((n + 2 * k).choose k : ℚ) =
    (((n + 2 * k).choose k : ℚ) - 2 * ((n + 2 * k - 1).choose (k - 1) : ℚ)) := by
  have h_combined := choose_relation_combined n k hk
  have h_cast : ((n * (n + 2 * k).choose k + 2 * (n + 2 * k) * (n + 2 * k - 1).choose (k - 1) : ℕ) : ℚ) =
                (((n + 2 * k) * (n + 2 * k).choose k : ℕ) : ℚ) := by rw [h_combined]
  push_cast at h_cast
  have h_nz : (n : ℚ) + 2 * (k : ℚ) ≠ 0 := by
    have : n + 2 * k > 0 := by omega
    exact_mod_cast Nat.ne_of_gt this
  have h_div : (n * (n + 2 * k).choose k : ℚ) / ((n : ℚ) + 2 * (k : ℚ)) =
               ((n + 2 * k).choose k : ℚ) - 2 * ((n + 2 * k - 1).choose (k - 1) : ℚ) := by
    have h_factor : (n : ℚ) * ((n + 2 * k).choose k : ℚ) =
                    ((n : ℚ) + 2 * (k : ℚ)) * (((n + 2 * k).choose k : ℚ) - 2 * ((n + 2 * k - 1).choose (k - 1) : ℚ)) := by
      linear_combination h_cast
    rw [h_factor]
    exact mul_div_cancel_left₀ _ h_nz
  calc (n : ℚ) / (n + 2 * k : ℚ) * ((n + 2 * k).choose k : ℚ)
    _ = (n * (n + 2 * k).choose k : ℚ) / ((n : ℚ) + 2 * (k : ℚ)) := by ring
    _ = ((n + 2 * k).choose k : ℚ) - 2 * ((n + 2 * k - 1).choose (k - 1) : ℚ) := h_div

lemma range_succ_split (M : ℕ) (f : ℕ → ℤ) :
    (range (M + 1)).sum f = f 0 + (Ioc 0 M).sum f := by
  have h : range (M + 1) = insert 0 (Ioc 0 M) := by
    ext x
    simp only [mem_range, mem_insert, mem_Ioc]
    omega
  rw [h]
  have h_not : 0 ∉ Ioc 0 M := by simp
  exact sum_insert h_not

lemma term_at_zero (n : ℕ) (hn : n > 0) :
    let term_q : ℚ := (n : ℚ) / (n + 2 * 0 : ℚ) * ((n + 2 * 0).choose 0 : ℚ)
    (Rat.floor term_q).toNat = 1 := by
  intro term_q
  have h_term : term_q = 1 := by
    dsimp [term_q]
    have hn_nz : (n : ℚ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hn
    simp [hn_nz]
  rw [h_term]
  rfl


lemma term_q_floor_eq (n k : ℕ) (hn : n > 0) (hk : k > 0) :
    Rat.floor ((n : ℚ) / (n + 2 * k : ℚ) * ((n + 2 * k).choose k : ℚ)) =
    ((n + 2 * k).choose k : ℤ) - 2 * ((n + 2 * k - 1).choose (k - 1) : ℤ) := by
  have h_floor_eq (q : ℚ) : Rat.floor q = ⌊q⌋ := rfl
  rw [h_floor_eq]
  rw [term_q_eq n k hn hk]
  have h_cast : (((n + 2 * k).choose k : ℚ) - 2 * ((n + 2 * k - 1).choose (k - 1) : ℚ)) =
                ((( (n + 2 * k).choose k : ℤ) - 2 * ((n + 2 * k - 1).choose (k - 1) : ℤ) : ℤ) : ℚ) := by
    push_cast
    rfl
  rw [h_cast]
  exact Int.floor_intCast _

lemma term_nonneg (n k : ℕ) (hn : n > 0) (hk : k > 0) :
    2 * ((n + 2 * k - 1).choose (k - 1) : ℤ) ≤ ((n + 2 * k).choose k : ℤ) := by
  have h_rel := choose_relation n k hk
  have h_cast : (((n + 2 * k) * (n + 2 * k - 1).choose (k - 1) : ℕ) : ℤ) = (((n + 2 * k).choose k * k : ℕ) : ℤ) := by rw [h_rel]
  push_cast at h_cast
  let Y := ((n + 2 * k - 1).choose (k - 1) : ℤ)
  let X := ((n + 2 * k).choose k : ℤ)
  have h_n : (n : ℤ) ≥ 1 := by omega
  have h_ineq : (2 * (k : ℤ)) * Y ≤ ((n : ℤ) + 2 * (k : ℤ)) * Y := by
    have h_coeff : 2 * (k : ℤ) ≤ (n : ℤ) + 2 * (k : ℤ) := by omega
    have h_Y_nonneg : Y ≥ 0 := by positivity
    exact mul_le_mul_of_nonneg_right h_coeff h_Y_nonneg
  have h_eq : ((n : ℤ) + 2 * (k : ℤ)) * Y = X * (k : ℤ) := by
    calc ((n : ℤ) + 2 * (k : ℤ)) * Y
      _ = (n + 2 * k) * Y := by ring
      _ = X * k := h_cast
      _ = X * (k : ℤ) := by ring
  rw [h_eq] at h_ineq
  have h_ineq' : (2 * Y) * (k : ℤ) ≤ X * (k : ℤ) := by
    calc (2 * Y) * (k : ℤ)
      _ = 2 * (k : ℤ) * Y := by ring
      _ ≤ X * (k : ℤ) := h_ineq
  have hk_pos : (0 : ℤ) < (k : ℤ) := by omega
  rwa [mul_le_mul_iff_of_pos_right hk_pos] at h_ineq'


lemma C_eq (n k : ℕ) (hk : k > 0) :
    ((n + 2 * k).choose k : ℤ) - 2 * ((n + 2 * k - 1).choose (k - 1) : ℤ) =
    ((n + 2 * k - 1).choose k : ℤ) - ((n + 2 * k - 1).choose (k - 1) : ℤ) := by
  have hk_nz : n + 2 * k ≠ 0 := by omega
  have h1 : (n + 2 * k - 1).succ = n + 2 * k := Nat.succ_pred hk_nz
  have hk_nz2 : k ≠ 0 := by omega
  have h2 : (k - 1).succ = k := Nat.succ_pred hk_nz2
  have h_choose := Nat.choose_succ_succ (n + 2 * k - 1) (k - 1)
  rw [h1, h2] at h_choose
  have h_cast : (( (n + 2 * k).choose k : ℕ) : ℤ) = ((( (n + 2 * k - 1).choose (k - 1) + (n + 2 * k - 1).choose k : ℕ) : ℤ)) := by rw [h_choose]
  push_cast at h_cast
  rw [h_cast]
  ring

lemma u_eq_sum (m n : ℕ) (hn : n > 0) :
    (u m n : ℤ) = 1 + ∑ k ∈ Ioc 0 (m * n), (((n + 2 * k).choose k : ℤ) - 2 * ((n + 2 * k - 1).choose (k - 1) : ℤ)) := by
  dsimp [u]
  split_ifs with h_cond
  · omega
  have h_cast : (( (range (m * n + 1)).sum fun k : ℕ => (Rat.floor ((n : ℚ) / (n + 2 * k : ℚ) * ((n + 2 * k).choose k : ℚ))).toNat : ℕ) : ℤ) =
                (range (m * n + 1)).sum fun k : ℕ => ((Rat.floor ((n : ℚ) / (n + 2 * k : ℚ) * ((n + 2 * k).choose k : ℚ))).toNat : ℤ) := by
    exact_mod_cast rfl
  rw [h_cast]
  have h0 : ((Rat.floor ((n : ℚ) / (n + 2 * 0 : ℚ) * ((n + 2 * 0).choose 0 : ℚ))).toNat : ℤ) = 1 := by
    have := term_at_zero n hn
    omega
  rw [range_succ_split (m * n)]
  simp only [Nat.cast_zero, mul_zero, add_zero] at *
  rw [h0]
  have h_congr : (Ioc 0 (m * n)).sum (fun k : ℕ => ((Rat.floor ((n : ℚ) / (n + 2 * k : ℚ) * ((n + 2 * k).choose k : ℚ))).toNat : ℤ)) =
                 (Ioc 0 (m * n)).sum (fun k : ℕ => (((n + 2 * k).choose k : ℤ) - 2 * ((n + 2 * k - 1).choose (k - 1) : ℤ))) := by
    apply sum_congr rfl
    intro k hk
    have hk_gt : k > 0 := by
      simp only [mem_Ioc] at hk
      exact hk.1
    rw [term_q_floor_eq n k hn hk_gt]
    have h_nonneg : 0 ≤ ((n + 2 * k).choose k : ℤ) - 2 * ((n + 2 * k - 1).choose (k - 1) : ℤ) := by
      have := term_nonneg n k hn hk_gt
      omega
    exact Int.toNat_of_nonneg h_nonneg
  rw [h_congr]

/--
oeis_352275_conjecture_2:
Then we conjecture that each sequence $u_m$ satisfies the above supercongruences.
Conjecture: the supercongruences $a(n p^r) \equiv a(n p^{r-1}) \pmod{p^{3r}}$ hold for primes $p \ge 5$ and positive integers $n$ and $r$.
This is equivalent to: $u_m(n p^r) \equiv u_m(n p^{r-1}) \pmod{p^{3r}}$ holds for primes $p \ge 5$ and positive integers $m, n, r$.
-/
theorem u_m_supercongruence_conjecture (m n r : ℕ) (hm : m > 0) (hn : n > 0) (hr : r > 0)
    (p : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) :
    (u m (n * p ^ r) : ℤ) ≡ (u m (n * p ^ (r - 1)) : ℤ) [ZMOD (p ^ (3 * r) : ℤ)] := by
  sorry
