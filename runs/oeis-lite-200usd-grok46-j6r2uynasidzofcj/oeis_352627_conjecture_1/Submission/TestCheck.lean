import FormalConjectures.Util.ProblemImports

open Nat Finset

def aa (n : ℕ) : ℕ :=
  let R : Finset ℕ := Finset.range (sqrt n + 1)
  let S_quadruples := R.product (R.product (R.product R))
  (S_quadruples.filter (fun p =>
    let a := p.1;
    let b := p.2.1;
    let c := p.2.2.1;
    let d := p.2.2.2;
    a^2 + 2 * b^2 + c^4 + 4 * d^4 + c^2 * d^2 = n
  )).card

lemma le_sqrt_of_pow_two_le {k n : ℕ} (h : k ^ 2 ≤ n) : k ≤ sqrt n :=
  Nat.le_sqrt'.mpr h

lemma mem_range_sqrt {k n : ℕ} (h : k ≤ sqrt n) : k ∈ range (sqrt n + 1) := by
  simp [mem_range]
  omega

lemma exists_imp_aa_pos {n x y c d : ℕ}
    (h : x ^ 2 + 2 * y ^ 2 + c ^ 4 + 4 * d ^ 4 + c ^ 2 * d ^ 2 = n) :
    0 < aa n := by
  have hx : x ≤ sqrt n := le_sqrt_of_pow_two_le (by omega)
  have hy : y ≤ sqrt n := by
    have h1 : 2 * y ^ 2 ≤ n := by omega
    have h2 : y ^ 2 ≤ 2 * y ^ 2 := Nat.le_mul_of_pos_left _ (by decide)
    exact le_sqrt_of_pow_two_le (le_trans h2 h1)
  have hc2 : c ^ 2 ≤ n := by
    cases c with
    | zero => simp
    | succ c =>
      have : (c + 1) ^ 2 ≤ (c + 1) ^ 4 := by
        rw [show (c + 1) ^ 4 = (c + 1) ^ 2 * (c + 1) ^ 2 from by ring]
        exact Nat.le_mul_of_pos_right _ (by simp)
      omega
  have hc : c ≤ sqrt n := le_sqrt_of_pow_two_le hc2
  have hd2 : d ^ 2 ≤ n := by
    cases d with
    | zero => simp
    | succ d =>
      have hle : (d + 1) ^ 2 ≤ 4 * (d + 1) ^ 4 := by
        have : (d + 1) ^ 2 ≤ (d + 1) ^ 4 := by
          rw [show (d + 1) ^ 4 = (d + 1) ^ 2 * (d + 1) ^ 2 from by ring]
          exact Nat.le_mul_of_pos_right _ (by simp)
        have : (d + 1) ^ 4 ≤ 4 * (d + 1) ^ 4 := Nat.le_mul_of_pos_left _ (by decide)
        exact le_trans ‹(d + 1) ^ 2 ≤ (d + 1) ^ 4› this
      omega
  have hd : d ≤ sqrt n := le_sqrt_of_pow_two_le hd2
  set R := range (sqrt n + 1)
  set S := R.product (R.product (R.product R))
  have hp : (x, (y, (c, d))) ∈ S := by
    simp [S, R, mem_product, mem_range_sqrt hx, mem_range_sqrt hy,
      mem_range_sqrt hc, mem_range_sqrt hd]
  have hpred : (fun p : ℕ × ℕ × ℕ × ℕ =>
      p.1 ^ 2 + 2 * p.2.1 ^ 2 + p.2.2.1 ^ 4 + 4 * p.2.2.2 ^ 4 +
        p.2.2.1 ^ 2 * p.2.2.2 ^ 2 = n) (x, (y, (c, d))) := h
  have hmem : (x, (y, (c, d))) ∈ S.filter (fun p =>
      p.1 ^ 2 + 2 * p.2.1 ^ 2 + p.2.2.1 ^ 4 + 4 * p.2.2.2 ^ 4 +
        p.2.2.1 ^ 2 * p.2.2.2 ^ 2 = n) :=
    mem_filter.mpr ⟨hp, hpred⟩
  have hcard : 0 < (S.filter (fun p =>
      p.1 ^ 2 + 2 * p.2.1 ^ 2 + p.2.2.1 ^ 4 + 4 * p.2.2.2 ^ 4 +
        p.2.2.1 ^ 2 * p.2.2.2 ^ 2 = n)).card :=
    card_pos.mpr ⟨_, hmem⟩
  simpa [aa, R, S] using hcard

example : 0 < aa 14 :=
  exists_imp_aa_pos (x := 0) (y := 2) (c := 1) (d := 1) (by norm_num)
