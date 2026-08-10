import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A278070: $a(n) = \text{hypergeometric}([n, -n], [], -1)$.
This is equivalent to the combinatorial sum:
$$a(n) = \sum_{k=0}^n \binom{n}{k} \binom{n+k-1}{k} k!$$
The expression uses $\mathbb{N}$ arithmetic throughout, safely handling the subtraction via `Nat.pred`.
-/
def A278070 (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun k =>
    (n.choose k) * ((n + k).pred.choose k) * (k.factorial)

namespace Nat

lemma dvd_descFactorial_of_pos (k : ℕ) : ∀ {r : ℕ}, 0 < r → k ∣ k.descFactorial r
  | 0, h => by cases h
  | 1, _ => by simp [descFactorial]
  | r + 2, _ => by
      rw [descFactorial_succ]
      exact dvd_mul_of_dvd_right (dvd_descFactorial_of_pos k (r := r + 1) (Nat.succ_pos r)) _

lemma dvd_choose_mul_factorial_of_pos_le {k r j : ℕ} (hr0 : 0 < r) (hrj : r ≤ j) :
    k ∣ k.choose r * j.factorial := by
  obtain ⟨c, hc⟩ := factorial_dvd_factorial hrj
  have h₁ : k ∣ k.choose r * r.factorial := by
    rw [mul_comm, ← descFactorial_eq_factorial_mul_choose]
    exact dvd_descFactorial_of_pos k hr0
  simpa [hc, mul_assoc] using dvd_mul_of_dvd_left h₁ c

lemma choose_add_mul_factorial_modEq (x k j : ℕ) :
    (x + k).choose j * j.factorial ≡ x.choose j * j.factorial [MOD k] := by
  rw [add_choose_eq]
  rw [Finset.sum_mul]
  refine (Nat.sum_modEq_single (s := Finset.antidiagonal j) (a := (j, 0)) ?ha ?h).trans ?base
  · intro hnot
    exfalso
    exact hnot (by simp [Finset.mem_antidiagonal])
  · intro ij hij hne
    have hsum : ij.1 + ij.2 = j := by simpa [Finset.mem_antidiagonal] using hij
    have hpos : 0 < ij.2 := by
      by_contra hz
      have hz' : ij.2 = 0 := Nat.eq_zero_of_not_pos hz
      have hfst : ij.1 = j := by omega
      exact hne (Prod.ext hfst hz')
    have hle : ij.2 ≤ j := by omega
    have hdvd : k ∣ (x.choose ij.1 * k.choose ij.2) * j.factorial := by
      have hd : k ∣ k.choose ij.2 * j.factorial :=
        dvd_choose_mul_factorial_of_pos_le hpos hle
      simpa [mul_assoc, mul_left_comm, mul_comm] using dvd_mul_of_dvd_right hd (x.choose ij.1)
    exact (Nat.modEq_zero_iff_dvd).2 hdvd
  · simp [Nat.ModEq]


end Nat

lemma A278070_term_modEq (n k j : ℕ) :
    (n + k).choose j * (((n + k) + j).pred.choose j) * j.factorial ≡
      n.choose j * ((n + j).pred.choose j) * j.factorial [MOD k] := by
  by_cases hj : j = 0
  · subst j
    simpa using (Nat.ModEq.refl 1 : 1 ≡ 1 [MOD k])
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
    have hpred : ((n + k) + j).pred = (n + j).pred + k := by
      rw [Nat.pred_eq_sub_one, Nat.pred_eq_sub_one]
      omega
    have h₂ : (((n + k) + j).pred.choose j * j.factorial) ≡
        ((n + j).pred.choose j * j.factorial) [MOD k] := by
      have h₂0 := Nat.choose_add_mul_factorial_modEq ((n + j).pred) k j
      rw [← hpred] at h₂0
      simpa [Nat.add_assoc] using h₂0
    have h₁ : ((n + k).choose j * j.factorial) ≡
        (n.choose j * j.factorial) [MOD k] :=
      Nat.choose_add_mul_factorial_modEq n k j
    calc
      (n + k).choose j * (((n + k) + j).pred.choose j) * j.factorial
          = (n + k).choose j * ((((n + k) + j).pred.choose j) * j.factorial) := by
              rw [mul_assoc]
      _ ≡ (n + k).choose j * (((n + j).pred.choose j) * j.factorial) [MOD k] := by
              exact h₂.mul_left ((n + k).choose j)
      _ = ((n + k).choose j * j.factorial) * ((n + j).pred.choose j) := by ring


      _ ≡ (n.choose j * j.factorial) * ((n + j).pred.choose j) [MOD k] := by
              exact h₁.mul_right ((n + j).pred.choose j)
      _ = n.choose j * ((n + j).pred.choose j) * j.factorial := by ring


lemma A278070_sum_extend (n k : ℕ) :
    (Finset.range (n + k + 1)).sum (fun j =>
      n.choose j * ((n + j).pred.choose j) * j.factorial) = A278070 n := by
  unfold A278070
  exact (Finset.sum_subset (s₁ := Finset.range (n + 1)) (s₂ := Finset.range (n + k + 1))
    (by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega)
    (by
      intro x hxlarge hxsmall
      simp only [Finset.mem_range, not_lt] at hxlarge hxsmall
      have hnx : n < x := by omega
      simp [Nat.choose_eq_zero_of_lt hnx])).symm


/--
We conjecture that a(n+k) == a(n) (mod k) for all n and k.
If true, then for each k, the sequence a(n) taken modulo k is a periodic sequence and the period divides k.
For example, modulo 7 the sequence becomes [1, 2, 4, 1, 1, 4, 2, 1, 2, 4, 1, 1, 4, 2, ...], apparently a periodic sequence of period 7.
-/
theorem oeis_278070_conjecture_0 : ∀ (n k : ℕ), Nat.ModEq k (A278070 (n + k)) (A278070 n) := by
  intro n k
  unfold A278070
  calc
    (Finset.range (n + k + 1)).sum (fun j =>
        (n + k).choose j * (((n + k) + j).pred.choose j) * j.factorial)
        ≡ (Finset.range (n + k + 1)).sum (fun j =>
          n.choose j * ((n + j).pred.choose j) * j.factorial) [MOD k] := by
            exact Nat.ModEq.sum fun j _ => A278070_term_modEq n k j
    _ = A278070 n := A278070_sum_extend n k
