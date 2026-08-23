import FormalConjectures.Util.ProblemImports
open Nat Finset BigOperators Int

def generalized_choose_int (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1 else
    (Finset.prod (Finset.range k) fun i => r - (i : ℤ)) / (k.factorial : ℤ)

lemma generalized_choose_int_eq_choose (r : ℤ) (k : ℕ) :
    generalized_choose_int r k = Ring.choose r k := by
  rw [generalized_choose_int]
  split_ifs with hk
  · subst k
    simp [Ring.choose_zero_right]
  · apply Int.ediv_eq_of_eq_mul_left (by exact_mod_cast Nat.factorial_ne_zero k)
    rw [mul_comm, ← nsmul_eq_mul, ← Ring.descPochhammer_eq_factorial_smul_choose]
    rw [← Polynomial.eval_eq_smeval]
    exact (descPochhammer_eval_eq_prod_range k r).symm


def generalized_catalan_coefficient (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1 else
    let num_choose := generalized_choose_int (r + 2 * (k : ℤ) - 1) k
    let denominator : ℤ := r + k
    (r * num_choose) / denominator

lemma choose_mul_index (q : ℤ) {k : ℕ} (hk : 0 < k) :
    (k : ℤ) * Ring.choose q k =
      Ring.choose q (k - 1) * (q - (k - 1 : ℕ)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have h := Ring.choose_smul_choose q (Nat.sub_le (j + 1) 1)
  rw [nsmul_eq_mul] at h
  simpa [Ring.choose_one_right] using h

lemma generalized_catalan_coefficient_eq_sub (r : ℤ) {k : ℕ} (hk : 0 < k)
    (hden : r + (k : ℤ) ≠ 0) :
    generalized_catalan_coefficient r k =
      Ring.choose (r + 2 * (k : ℤ) - 1) k -
        Ring.choose (r + 2 * (k : ℤ) - 1) (k - 1) := by
  rw [generalized_catalan_coefficient, if_neg (Nat.ne_of_gt hk),
    generalized_choose_int_eq_choose]
  apply Int.ediv_eq_of_eq_mul_left hden
  have hratio := choose_mul_index (r + 2 * (k : ℤ) - 1) hk
  norm_num [Nat.cast_sub (by omega : 1 ≤ k)] at hratio
  rw [show (r * Ring.choose (r + 2 * (k : ℤ) - 1) k) =
      (Ring.choose (r + 2 * (k : ℤ) - 1) k -
       Ring.choose (r + 2 * (k : ℤ) - 1) (k - 1)) * (r + k) by
    linear_combination -hratio]



def catalanPartial (r : ℤ) (N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (N + 1), generalized_catalan_coefficient r j

-- This is the central arithmetic statement still to prove.
theorem catalanPartial_scale_supercongruence
    (r : ℤ) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (N e : ℕ)
    (hN : p ^ e ∣ N) (hr : (p ^ e : ℤ) ∣ r) :
    catalanPartial ((p : ℤ) * r) (p * N) ≡ catalanPartial r N
      [ZMOD ((p : ℤ) ^ (3 * (e + 1)))] := by
  sorry


def a_gen (m : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 1 else
    let r : ℤ := m * (n : ℤ)
    Finset.sum (range (n + 1)) fun k => generalized_catalan_coefficient r k

lemma a_gen_eq_partial (m : ℤ) {N : ℕ} (hN : N ≠ 0) :
    a_gen m N = catalanPartial (m * (N : ℤ)) N := by
  simp [a_gen, hN, catalanPartial]

theorem final_from_scale (m : ℤ) (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5)
    (n k : ℕ) (hn : n > 0) (hk : k > 0) :
    a_gen m (n * p ^ k) ≡ a_gen m (n * p ^ (k - 1))
      [ZMOD (p ^ (3 * k) : ℤ)] := by
  let N := n * p ^ (k - 1)
  have hp0 : p ≠ 0 := hp.ne_zero
  have hN0 : N ≠ 0 := mul_ne_zero (Nat.ne_of_gt hn) (pow_ne_zero _ hp0)
  have hbig0 : n * p ^ k ≠ 0 := mul_ne_zero (Nat.ne_of_gt hn) (pow_ne_zero _ hp0)
  have hk_eq : k - 1 + 1 = k := by omega
  have hpow : n * p ^ k = p * N := by
    calc
      n * p ^ k = n * (p ^ (k - 1) * p) := by
        nth_rewrite 1 [show k = (k - 1) + 1 by omega]
        rw [pow_succ]
      _ = p * (n * p ^ (k - 1)) := by ac_rfl
      _ = p * N := rfl
  rw [a_gen_eq_partial m hbig0, a_gen_eq_partial m hN0, hpow]
  have hNdvd : p ^ (k - 1) ∣ N := by simp [N]
  have hrdvd : ((p ^ (k - 1) : ℕ) : ℤ) ∣ m * (N : ℤ) := by
    obtain ⟨c, hc⟩ := hNdvd
    use m * (c : ℤ)
    rw [hc]
    push_cast
    ring
  have h := catalanPartial_scale_supercongruence (m * (N : ℤ)) p hp hp5 N (k - 1)
    hNdvd hrdvd
  norm_num [hk_eq] at h ⊢
  convert h using 1 <;> ring


