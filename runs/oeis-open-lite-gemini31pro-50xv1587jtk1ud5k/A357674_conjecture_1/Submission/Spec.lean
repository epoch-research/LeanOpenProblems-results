import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators ZMod

def A357674 (n : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ 4 * S2 ^ 3

def u_A357674 (n m : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (m * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (m * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ (2 * m) * S2 ^ (m + 1)

def S1 (n : ℕ) : ℕ := ∑ k ∈ range (2 * n + 1), (n + k - 1).choose k
def S2 (n : ℕ) : ℕ := ∑ k ∈ range (2 * n + 1), (n + k - 1).choose k ^ 2

lemma A_eq (p : ℕ) : A357674 p = S1 p ^ 4 * S2 p ^ 3 := by rfl



lemma mod_pow_alg (s1 s2 p : ℕ) (hp3 : p ≥ 3) (h1 : s1 ≡ 3 [MOD p^3]) (h2 : s2 ≡ 3 [MOD p^3]) (h3 : 4 * s1 + 3 * s2 ≡ 21 [MOD p^5]) :
  s1^4 * s2^3 ≡ 2187 [MOD p^5] := by
  have hp3_lt : 3 < p^3 := by
    calc 3 < 27 := by norm_num
    _ = 3^3 := by norm_num
    _ ≤ p^3 := Nat.pow_le_pow_left hp3 3
  have h1' : s1 % p^3 = 3 := by
    calc s1 % p^3 = 3 % p^3 := h1
    _ = 3 := Nat.mod_eq_of_lt hp3_lt
  have h2' : s2 % p^3 = 3 := by
    calc s2 % p^3 = 3 % p^3 := h2
    _ = 3 := Nat.mod_eq_of_lt hp3_lt
  set x := s1 / p^3
  set y := s2 / p^3
  have hs1 : s1 = 3 + x * p^3 := by
    have H := Nat.div_add_mod s1 (p^3)
    rw [h1'] at H
    calc s1 = p^3 * x + 3 := H.symm
    _ = 3 + x * p^3 := by ring
  have hs2 : s2 = 3 + y * p^3 := by
    have H := Nat.div_add_mod s2 (p^3)
    rw [h2'] at H
    calc s2 = p^3 * y + 3 := H.symm
    _ = 3 + y * p^3 := by ring

  have H3 : (4 * (s1 : ZMod (p^5)) + 3 * (s2 : ZMod (p^5)) : ZMod (p^5)) = 21 := by
    have h3' := (ZMod.natCast_eq_natCast_iff (4 * s1 + 3 * s2) 21 (p^5)).mpr h3
    push_cast at h3'
    exact h3'

  have hz1 : (s1 : ZMod (p^5)) = 3 + x * p^3 := by
    rw [hs1]; push_cast; ring
  have hz2 : (s2 : ZMod (p^5)) = 3 + y * p^3 := by
    rw [hs2]; push_cast; ring

  have H3_sub : 4 * (x : ZMod (p^5)) * (p : ZMod (p^5))^3 + 3 * (y : ZMod (p^5)) * (p : ZMod (p^5))^3 = 0 := by
    calc 4 * (x : ZMod (p^5)) * (p : ZMod (p^5))^3 + 3 * (y : ZMod (p^5)) * (p : ZMod (p^5))^3 = 4 * (3 + (x : ZMod (p^5)) * (p : ZMod (p^5))^3) + 3 * (3 + (y : ZMod (p^5)) * (p : ZMod (p^5))^3) - 21 := by ring
    _ = 4 * (s1 : ZMod (p^5)) + 3 * (s2 : ZMod (p^5)) - 21 := by rw [hz1, hz2]
    _ = 21 - 21 := by rw [H3]
    _ = 0 := by ring

  have hp5 : (p : ZMod (p^5))^5 = 0 := by
    have H := CharP.cast_eq_zero (ZMod (p^5)) (p^5)
    push_cast at H
    exact H

  have hp6 : (p : ZMod (p^5))^6 = 0 := by
    calc (p : ZMod (p^5))^6 = (p : ZMod (p^5))^5 * (p : ZMod (p^5)) := by ring
    _ = 0 * (p : ZMod (p^5)) := by rw [hp5]
    _ = 0 := by ring

  have H_final : ((s1^4 * s2^3 : ℕ) : ZMod (p^5)) = 2187 := by
    push_cast
    rw [hz1, hz2]
    have H_poly : (3 + (x : ZMod (p^5)) * (p : ZMod (p^5))^3)^4 * (3 + (y : ZMod (p^5)) * (p : ZMod (p^5))^3)^3 = 2187 + 729 * (4 * (x : ZMod (p^5)) * (p : ZMod (p^5))^3 + 3 * (y : ZMod (p^5)) * (p : ZMod (p^5))^3) + (p : ZMod (p^5))^6 * ( (p : ZMod (p^5))^15*(x : ZMod (p^5))^4*(y : ZMod (p^5))^3 + 9*(p : ZMod (p^5))^12*(x : ZMod (p^5))^4*(y : ZMod (p^5))^2 + 12*(p : ZMod (p^5))^12*(x : ZMod (p^5))^3*(y : ZMod (p^5))^3 + 27*(p : ZMod (p^5))^9*(x : ZMod (p^5))^4*(y : ZMod (p^5)) + 108*(p : ZMod (p^5))^9*(x : ZMod (p^5))^3*(y : ZMod (p^5))^2 + 54*(p : ZMod (p^5))^9*(x : ZMod (p^5))^2*(y : ZMod (p^5))^3 + 27*(p : ZMod (p^5))^6*(x : ZMod (p^5))^4 + 324*(p : ZMod (p^5))^6*(x : ZMod (p^5))^3*(y : ZMod (p^5)) + 486*(p : ZMod (p^5))^6*(x : ZMod (p^5))^2*(y : ZMod (p^5))^2 + 108*(p : ZMod (p^5))^6*(x : ZMod (p^5))*(y : ZMod (p^5))^3 + 324*(p : ZMod (p^5))^3*(x : ZMod (p^5))^3 + 1458*(p : ZMod (p^5))^3*(x : ZMod (p^5))^2*(y : ZMod (p^5)) + 972*(p : ZMod (p^5))^3*(x : ZMod (p^5))*(y : ZMod (p^5))^2 + 81*(p : ZMod (p^5))^3*(y : ZMod (p^5))^3 + 1458*(x : ZMod (p^5))^2 + 2916*(x : ZMod (p^5))*(y : ZMod (p^5)) + 729*(y : ZMod (p^5))^2 ) := by ring
    rw [H_poly, H3_sub, hp6]
    ring

  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp H_final


def S1_dup (n : ℕ) : ℕ := ∑ k ∈ range (2 * n + 1), (n + k - 1).choose k

lemma S1_eq (n : ℕ) (hn : n > 0) : S1 n = (3 * n).choose n := by
  have H : S1 n = ∑ k ∈ range (2 * n + 1), (k + (n - 1)).choose (n - 1) := by
    apply sum_congr rfl
    intro k _
    have h1 : n + k - 1 = k + (n - 1) := by omega
    rw [h1]
    have h2 : (k + (n - 1)) - k = n - 1 := by omega
    have h3 := Nat.choose_symm (show k ≤ k + (n - 1) by omega)
    rw [h2] at h3
    exact h3.symm
  rw [H]
  have H2 := Nat.sum_range_add_choose (2 * n) (n - 1)
  rw [H2]
  have h4 : 2 * n + (n - 1) + 1 = 3 * n := by omega
  have h5 : n - 1 + 1 = n := by omega
  rw [h4, h5]


def S2_dup (n : ℕ) : ℕ := ∑ k ∈ range (2 * n + 1), (n + k - 1).choose k ^ 2

lemma wz_identity (n k : ℕ) (hn : n > 0) :
  2 * n^2 * (2 * n + 1) * (n + k).choose k ^ 2 + k^2 * (3 * n + 2 * k) * (n + k - 1).choose k ^ 2 =
  n^3 * (n + k - 1).choose k ^ 2 + (k + 1)^2 * (3 * n + 2 * k + 2) * (n + k).choose (k + 1) ^ 2 := by
  have H1 : (k + 1) * (n + k).choose (k + 1) = (n + k) * (n + k - 1).choose k := by
    have h1 := Nat.add_one_mul_choose_eq (n + k - 1) k
    have h2 : (n + k - 1) + 1 = n + k := by omega
    rw [h2] at h1
    calc (k + 1) * (n + k).choose (k + 1) = (n + k).choose (k + 1) * (k + 1) := by ring
    _ = (n + k) * (n + k - 1).choose k := h1.symm
  have H2 : n * (n + k).choose k = (n + k) * (n + k - 1).choose k := by
    have h1 := Nat.add_one_mul_choose_eq (n + k - 1) (n - 1)
    have h2 : (n + k - 1) + 1 = n + k := by omega
    have h3 : (n - 1) + 1 = n := by omega
    rw [h2, h3] at h1
    have h4 : (n + k - 1).choose (n - 1) = (n + k - 1).choose k := by
      have hh : (n + k - 1) - (n - 1) = k := by omega
      have h5 := Nat.choose_symm (show n - 1 ≤ n + k - 1 by omega)
      rw [hh] at h5
      exact h5.symm
    have h5 : (n + k).choose n = (n + k).choose k := by
      have hh : (n + k) - n = k := by omega
      have h6 := Nat.choose_symm (show n ≤ n + k by omega)
      rw [hh] at h6
      exact h6.symm
    rw [h4, h5] at h1
    calc n * (n + k).choose k = (n + k).choose k * n := by ring
    _ = (n + k) * (n + k - 1).choose k := h1.symm
  have H_final : n^2 * (2 * n^2 * (2 * n + 1) * (n + k).choose k ^ 2 + k^2 * (3 * n + 2 * k) * (n + k - 1).choose k ^ 2) =
                 n^2 * (n^3 * (n + k - 1).choose k ^ 2 + (k + 1)^2 * (3 * n + 2 * k + 2) * (n + k).choose (k + 1) ^ 2) := by
    set C := (n + k - 1).choose k
    have hA : n^2 * (n + k).choose k ^ 2 = (n + k)^2 * C^2 := by
      calc n^2 * (n + k).choose k ^ 2 = (n * (n + k).choose k)^2 := by ring
      _ = ((n + k) * C)^2 := by rw [H2]
      _ = (n + k)^2 * C^2 := by ring
    have hB : (k + 1)^2 * (n + k).choose (k + 1) ^ 2 = (n + k)^2 * C^2 := by
      calc (k + 1)^2 * (n + k).choose (k + 1) ^ 2 = ((k + 1) * (n + k).choose (k + 1))^2 := by ring
      _ = ((n + k) * C)^2 := by rw [H1]
      _ = (n + k)^2 * C^2 := by ring
    calc n^2 * (2 * n^2 * (2 * n + 1) * (n + k).choose k ^ 2 + k^2 * (3 * n + 2 * k) * C^2)
      _ = 2 * n^2 * (2 * n + 1) * (n^2 * (n + k).choose k ^ 2) + n^2 * k^2 * (3 * n + 2 * k) * C^2 := by ring
      _ = 2 * n^2 * (2 * n + 1) * ((n + k)^2 * C^2) + n^2 * k^2 * (3 * n + 2 * k) * C^2 := by rw [hA]
      _ = (2 * n^2 * (2 * n + 1) * (n + k)^2 + n^2 * k^2 * (3 * n + 2 * k)) * C^2 := by ring
      _ = (n^5 + n^2 * (3 * n + 2 * k + 2) * (n + k)^2) * C^2 := by ring
      _ = n^5 * C^2 + n^2 * (3 * n + 2 * k + 2) * ((n + k)^2 * C^2) := by ring
      _ = n^5 * C^2 + n^2 * (3 * n + 2 * k + 2) * ((k + 1)^2 * (n + k).choose (k + 1) ^ 2) := by rw [hB]
      _ = n^2 * (n^3 * C^2 + (k + 1)^2 * (3 * n + 2 * k + 2) * (n + k).choose (k + 1) ^ 2) := by ring
  exact Nat.eq_of_mul_eq_mul_left (by positivity) H_final

lemma sum_range_succ_sub_sum (f : ℕ → ℕ) (n : ℕ) :
  (∑ k ∈ range n, f (k + 1)) + f 0 = (∑ k ∈ range n, f k) + f n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ]
    calc (∑ k ∈ range n, f (k + 1)) + f (n + 1) + f 0 = (∑ k ∈ range n, f (k + 1)) + f 0 + f (n + 1) := by omega
    _ = (∑ k ∈ range n, f k) + f n + f (n + 1) := by rw [ih]
    _ = (∑ x ∈ range n, f x) + f n + f (n + 1) := rfl

lemma S2_rec (p : ℕ) (hp3 : p ≥ 3) :
  2*p^2*(2*p+1) * (∑ k ∈ range (2*p + 1), (p+k).choose k ^ 2) =
  p^3 * (∑ k ∈ range (2*p + 1), (p+k-1).choose k ^ 2) +
  (2*p+1)^2*(7*p+2) * (3*p).choose (2*p+1) ^ 2 := by
  have hp : p > 0 := by omega
  have H : ∑ k ∈ range (2*p + 1), (2 * p^2 * (2 * p + 1) * (p + k).choose k ^ 2 + k^2 * (3 * p + 2 * k) * (p + k - 1).choose k ^ 2) =
           ∑ k ∈ range (2*p + 1), (p^3 * (p + k - 1).choose k ^ 2 + (k + 1)^2 * (3 * p + 2 * k + 2) * (p + k).choose (k + 1) ^ 2) := by
    apply sum_congr rfl
    intro k _
    exact wz_identity p k hp
  have H_LHS : ∑ k ∈ range (2*p + 1), (2 * p^2 * (2 * p + 1) * (p + k).choose k ^ 2 + k^2 * (3 * p + 2 * k) * (p + k - 1).choose k ^ 2) =
               2 * p^2 * (2 * p + 1) * ∑ k ∈ range (2*p + 1), (p + k).choose k ^ 2 + ∑ k ∈ range (2*p + 1), k^2 * (3 * p + 2 * k) * (p + k - 1).choose k ^ 2 := by
    rw [sum_add_distrib, mul_sum]
  have H_RHS : ∑ k ∈ range (2*p + 1), (p^3 * (p + k - 1).choose k ^ 2 + (k + 1)^2 * (3 * p + 2 * k + 2) * (p + k).choose (k + 1) ^ 2) =
               p^3 * ∑ k ∈ range (2*p + 1), (p + k - 1).choose k ^ 2 + ∑ k ∈ range (2*p + 1), (k + 1)^2 * (3 * p + 2 * k + 2) * (p + k).choose (k + 1) ^ 2 := by
    rw [sum_add_distrib, mul_sum]
  rw [H_LHS, H_RHS] at H
  let G := fun k => k^2 * (3 * p + 2 * k) * (p + k - 1).choose k ^ 2
  have h_eq1 : ∑ k ∈ range (2*p + 1), (k + 1)^2 * (3 * p + 2 * k + 2) * (p + k).choose (k + 1) ^ 2 = ∑ k ∈ range (2*p + 1), G (k + 1) := by
    apply sum_congr rfl
    intro k _
    dsimp [G]
    have h1 : 3 * p + 2 * (k + 1) = 3 * p + 2 * k + 2 := by ring
    rw [h1]
  have h_eq2 : ∑ k ∈ range (2*p + 1), k^2 * (3 * p + 2 * k) * (p + k - 1).choose k ^ 2 = ∑ k ∈ range (2*p + 1), G k := rfl
  rw [h_eq1, h_eq2] at H
  have h_telescope := sum_range_succ_sub_sum G (2*p + 1)
  have h_G0 : G 0 = 0 := by
    dsimp [G]
    have h0 : 0 * (3 * p) * (p - 1).choose 0 ^ 2 = 0 := by ring
    exact h0
  rw [h_G0, add_zero] at h_telescope
  have h_G_last : G (2*p + 1) = (2*p+1)^2*(7*p+2) * (3*p).choose (2*p+1) ^ 2 := by
    dsimp [G]
    have h1 : 3 * p + 2 * (2 * p + 1) = 7 * p + 2 := by ring
    rw [h1]
    congr 2
    have h3 : p + 2 * p = 3 * p := by omega
    rw [h3]
  rw [h_G_last] at h_telescope
  omega


lemma modEq_of_sum_dvd {A B C m : ℕ} (h_eq : A = B + C) (h_dvd : m ∣ C) : A ≡ B [MOD m] := by
  rw [h_eq]
  have hdvd : m ∣ (B + C) - B := by
    have hsub : (B + C) - B = C := Nat.add_sub_cancel_left B C
    rw [hsub]
    exact h_dvd
  exact ModEq.symm ((modEq_iff_dvd' (by omega)).mpr hdvd)

lemma sum_S1 (p : ℕ) (hp : p > 0) : (3 * p).choose p = (2 * p).choose p + 1 + ∑ j ∈ Ico 1 p, (2 * p).choose (p - j) * p.choose j := by
  have H := Nat.add_choose_eq (2 * p) p p
  have h_add : 2 * p + p = 3 * p := by omega
  rw [h_add] at H
  have H2 := Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (2 * p).choose i * p.choose j) p
  rw [H2] at H
  have H3 := Finset.sum_range_reflect (fun k => (2 * p).choose k * p.choose (p - k)) (p + 1)
  have H4 : ∑ j ∈ range (p + 1), (2 * p).choose j * p.choose (p - j) = ∑ j ∈ range (p + 1), (2 * p).choose (p - j) * p.choose j := by
    calc ∑ j ∈ range (p + 1), (2 * p).choose j * p.choose (p - j)
      _ = ∑ j ∈ range (p + 1), (2 * p).choose (p + 1 - 1 - j) * p.choose (p - (p + 1 - 1 - j)) := H3.symm
      _ = ∑ j ∈ range (p + 1), (2 * p).choose (p - j) * p.choose j := by
        apply sum_congr rfl
        intro x hx
        have H5 : p + 1 - 1 - x = p - x := by omega
        rw [H5]
        have H6 : p - (p - x) = x := by
          have : x < p + 1 := Finset.mem_range.mp hx
          omega
        rw [H6]
  rw [H4] at H
  have H5 : ∑ j ∈ range (p + 1), (2 * p).choose (p - j) * p.choose j = (2 * p).choose p * p.choose 0 + ∑ j ∈ Ico 1 (p + 1), (2 * p).choose (p - j) * p.choose j := by
    rw [sum_eq_add_sum_diff_singleton (show 0 ∈ range (p + 1) by simp)]
    congr 1
    have h_diff : (range (p + 1)) \ {0} = Ico 1 (p + 1) := by
      ext x
      simp only [mem_sdiff, mem_range, mem_singleton, mem_Ico]
      omega
    rw [h_diff]
  have H6 : ∑ j ∈ Ico 1 (p + 1), (2 * p).choose (p - j) * p.choose j = ∑ j ∈ Ico 1 p, (2 * p).choose (p - j) * p.choose j + (2 * p).choose 0 * p.choose p := by
    have h_split : Ico 1 (p + 1) = Ico 1 p ∪ {p} := by
      ext x
      simp only [mem_Ico, mem_union, mem_singleton]
      omega
    rw [h_split, sum_union]
    · have h_sing : ∑ x ∈ ({p} : Finset ℕ), (2 * p).choose (p - x) * p.choose x = (2 * p).choose 0 * p.choose p := by
        simp only [sum_singleton]
        have h_sub : p - p = 0 := by omega
        rw [h_sub]
      rw [h_sing]
    · simp only [disjoint_singleton_right, mem_Ico, not_and, not_lt]
      intro h
      omega
  rw [H5, H6] at H
  have H7 : (2 * p).choose p * p.choose 0 = (2 * p).choose p := by simp
  have H8 : (2 * p).choose 0 * p.choose p = 1 := by simp
  rw [H7, H8] at H
  omega

lemma sum_S1_2 (p : ℕ) (hp : p > 0) : (2 * p).choose p = 2 + ∑ j ∈ Ico 1 p, p.choose (p - j) * p.choose j := by
  have H := Nat.add_choose_eq p p p
  have h_add : p + p = 2 * p := by omega
  rw [h_add] at H
  have H2 := Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p.choose i * p.choose j) p
  rw [H2] at H
  have H3 := Finset.sum_range_reflect (fun k => p.choose k * p.choose (p - k)) (p + 1)
  have H4 : ∑ j ∈ range (p + 1), p.choose j * p.choose (p - j) = ∑ j ∈ range (p + 1), p.choose (p - j) * p.choose j := by
    calc ∑ j ∈ range (p + 1), p.choose j * p.choose (p - j)
      _ = ∑ j ∈ range (p + 1), p.choose (p + 1 - 1 - j) * p.choose (p - (p + 1 - 1 - j)) := H3.symm
      _ = ∑ j ∈ range (p + 1), p.choose (p - j) * p.choose j := by
        apply sum_congr rfl
        intro x hx
        have H5 : p + 1 - 1 - x = p - x := by omega
        rw [H5]
        have H6 : p - (p - x) = x := by
          have : x < p + 1 := Finset.mem_range.mp hx
          omega
        rw [H6]
  rw [H4] at H
  have H5 : ∑ j ∈ range (p + 1), p.choose (p - j) * p.choose j = p.choose p * p.choose 0 + ∑ j ∈ Ico 1 (p + 1), p.choose (p - j) * p.choose j := by
    rw [sum_eq_add_sum_diff_singleton (show 0 ∈ range (p + 1) by simp)]
    congr 1
    have h_diff : (range (p + 1)) \ {0} = Ico 1 (p + 1) := by
      ext x
      simp only [mem_sdiff, mem_range, mem_singleton, mem_Ico]
      omega
    rw [h_diff]
  have H6 : ∑ j ∈ Ico 1 (p + 1), p.choose (p - j) * p.choose j = ∑ j ∈ Ico 1 p, p.choose (p - j) * p.choose j + p.choose 0 * p.choose p := by
    have h_split : Ico 1 (p + 1) = Ico 1 p ∪ {p} := by
      ext x
      simp only [mem_Ico, mem_union, mem_singleton]
      omega
    rw [h_split, sum_union]
    · have h_sing : ∑ x ∈ ({p} : Finset ℕ), p.choose (p - x) * p.choose x = p.choose 0 * p.choose p := by
        simp only [sum_singleton]
        have h_sub : p - p = 0 := by omega
        rw [h_sub]
      rw [h_sing]
    · simp only [disjoint_singleton_right, mem_Ico, not_and, not_lt]
      intro h
      omega
  rw [H5, H6] at H
  have H7 : p.choose p * p.choose 0 = 1 := by simp
  have H8 : p.choose 0 * p.choose p = 1 := by simp
  rw [H7, H8] at H
  omega

lemma mod_2p_choose_p (p : ℕ) (hp : p.Prime) : (2 * p).choose p ≡ 2 [MOD p^2] := by
  have H : (2 * p).choose p = 2 + ∑ j ∈ Ico 1 p, p.choose (p - j) * p.choose j := sum_S1_2 p (hp.pos)
  have h_dvd1 : ∀ j ∈ Ico 1 p, p ∣ p.choose j := by
    intro j hj
    simp only [mem_Ico] at hj
    exact hp.dvd_choose hj.2 (by omega) (by omega)
  have h_dvd2 : ∀ j ∈ Ico 1 p, p ∣ p.choose (p - j) := by
    intro j hj
    simp only [mem_Ico] at hj
    have h1 : p - j < p := by omega
    exact hp.dvd_choose h1 (by omega) (by omega)
  have h_dvd_prod2 : p^2 ∣ ∑ j ∈ Ico 1 p, p.choose (p - j) * p.choose j := by
    apply dvd_sum
    intro j hj
    have d1 := h_dvd1 j hj
    have d2 := h_dvd2 j hj
    have h_p2 : p^2 = p * p := by ring
    rw [h_p2]
    exact mul_dvd_mul d2 d1
  exact modEq_of_sum_dvd H h_dvd_prod2

lemma mod_2p_1_choose_p (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) : (2 * p - 1).choose p ≡ 1 [MOD p^2] := by
  have H : (2 * p).choose p = 2 * (2 * p - 1).choose (p - 1) := by
    have hd := Nat.add_one_mul_choose_eq (2 * p - 1) (p - 1)
    have ha : 2 * p - 1 + 1 = 2 * p := by omega
    have hb : p - 1 + 1 = p := by omega
    rw [ha, hb] at hd
    have hc : p * (2 * p).choose p = p * (2 * (2 * p - 1).choose (p - 1)) := by
      calc p * (2 * p).choose p = (2 * p).choose p * p := by ring
        _ = 2 * p * (2 * p - 1).choose (p - 1) := hd.symm
        _ = p * (2 * (2 * p - 1).choose (p - 1)) := by ring
    exact Nat.eq_of_mul_eq_mul_left hp.pos hc
  have H2 := mod_2p_choose_p p hp
  rw [H] at H2
  have H3 : 2 * (2 * p - 1).choose (p - 1) ≡ 2 * 1 [MOD p^2] := by
    have h_eq : 2 * 1 = 2 := by omega
    rw [h_eq]
    exact H2
  have h_coprime : (p^2).Coprime 2 := by
    have h_p : p.Coprime 2 := by
      apply hp.coprime_iff_not_dvd.mpr
      intro h_dvd
      have h_le : p ≤ 2 := Nat.le_of_dvd (by omega) h_dvd
      omega
    exact Coprime.pow_left 2 h_p
  have H4 := ModEq.cancel_left_of_coprime h_coprime H3
  have H5 : (2 * p - 1).choose p = (2 * p - 1).choose (p - 1) := by
    have hc := Nat.choose_symm (show p ≤ 2 * p - 1 by omega)
    have ha : 2 * p - 1 - p = p - 1 := by omega
    rw [ha] at hc
    exact hc.symm
  rw [H5]
  exact H4

lemma mod_3p_choose_p (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) : (3 * p).choose p ≡ 3 [MOD p^2] := by
  have H : (3 * p).choose p = (2 * p).choose p + 1 + ∑ j ∈ Ico 1 p, (2 * p).choose (p - j) * p.choose j := sum_S1 p hp.pos
  have h_dvd1 : ∀ j ∈ Ico 1 p, p ∣ p.choose j := by
    intro j hj
    simp only [mem_Ico] at hj
    exact hp.dvd_choose hj.2 (by omega) (by omega)
  have h_dvd3 : ∀ j ∈ Ico 1 p, p ∣ (2 * p).choose (p - j) := by
    intro j hj
    simp only [mem_Ico] at hj
    have hd := Nat.add_one_mul_choose_eq (2 * p - 1) (p - j - 1)
    have ha : 2 * p - 1 + 1 = 2 * p := by omega
    have hb : p - j - 1 + 1 = p - j := by omega
    rw [ha, hb] at hd
    have hc : p ∣ (p - j) * (2 * p).choose (p - j) := by
      rw [mul_comm, ← hd]
      have hp_dvd : p ∣ 2 * p := dvd_mul_left p 2
      exact dvd_mul_of_dvd_left hp_dvd _
    have h_coprime : p.Coprime (p - j) := by
      apply hp.coprime_iff_not_dvd.mpr
      intro h
      have h5 : p ≤ p - j := Nat.le_of_dvd (by omega) h
      omega
    exact h_coprime.dvd_of_dvd_mul_left hc
  have h_dvd_prod1 : p^2 ∣ ∑ j ∈ Ico 1 p, (2 * p).choose (p - j) * p.choose j := by
    apply dvd_sum
    intro j hj
    have d1 := h_dvd1 j hj
    have d2 := h_dvd3 j hj
    have h_p2 : p^2 = p * p := by ring
    rw [h_p2]
    exact mul_dvd_mul d2 d1
  have h_mod1 : (3 * p).choose p ≡ (2 * p).choose p + 1 [MOD p^2] := modEq_of_sum_dvd H h_dvd_prod1
  have h_mod2 : (2 * p).choose p ≡ 2 [MOD p^2] := mod_2p_choose_p p hp
  have h_mod3 : (2 * p).choose p + 1 ≡ 3 [MOD p^2] := by
    have hm : 2 + 1 = 3 := by omega
    have h_mod2' := ModEq.add_right 1 h_mod2
    rw [hm] at h_mod2'
    exact h_mod2'
  exact ModEq.trans h_mod1 h_mod3

lemma modEq_cancel_mul {A B m c : ℕ} (h : c * A ≡ c * B [MOD m]) (hc : m.Coprime c) : A ≡ B [MOD m] :=
  ModEq.cancel_left_of_coprime hc h

lemma mod_3p_1_choose_2p (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) : (3 * p - 1).choose (2 * p) ≡ 1 [MOD p^2] := by
  by_cases hp_eq_3 : p = 3
  · rw [hp_eq_3]
    decide
  · have hp_gt_3 : p > 3 := by omega
    have H1 : (3 * p - 1).choose (2 * p) = (3 * p - 1).choose (p - 1) := by
      have hc := Nat.choose_symm (show 2 * p ≤ 3 * p - 1 by omega)
      have ha : 3 * p - 1 - 2 * p = p - 1 := by omega
      rw [ha] at hc
      exact hc.symm
    rw [H1]
    have H : (3 * p).choose p = 3 * (3 * p - 1).choose (p - 1) := by
      have hd := Nat.add_one_mul_choose_eq (3 * p - 1) (p - 1)
      have ha : 3 * p - 1 + 1 = 3 * p := by omega
      have hb : p - 1 + 1 = p := by omega
      rw [ha, hb] at hd
      have hc : p * (3 * p).choose p = p * (3 * (3 * p - 1).choose (p - 1)) := by
        calc p * (3 * p).choose p = (3 * p).choose p * p := by ring
          _ = 3 * p * (3 * p - 1).choose (p - 1) := hd.symm
          _ = p * (3 * (3 * p - 1).choose (p - 1)) := by ring
      exact Nat.eq_of_mul_eq_mul_left hp.pos hc
    have H_S1 : (3 * p).choose p ≡ 3 [MOD p^2] := mod_3p_choose_p p hp hp3
    rw [H] at H_S1
    have H3 : 3 * (3 * p - 1).choose (p - 1) ≡ 3 * 1 [MOD p^2] := by
      have hc : 3 * 1 = 3 := by rfl
      rw [hc]
      clear hc
      exact H_S1
    have h_coprime : (p^2).Coprime 3 := by
      have h_p : p.Coprime 3 := by
        apply hp.coprime_iff_not_dvd.mpr
        intro h_dvd
        have h_le : p ≤ 3 := Nat.le_of_dvd (by decide) h_dvd
        omega
      exact Coprime.pow_left 2 h_p
    exact modEq_cancel_mul H3 h_coprime

lemma dvd_p_add_k_choose_large (p k : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hk1 : p + 1 ≤ k) (hk2p : k < 2 * p) : p ∣ (p + k - 1).choose k := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : p + k - 1 < p ^ 2 := by
    calc p + k - 1 < p + 2 * p := by omega
      _ = 3 * p := by ring
      _ ≤ p * p := Nat.mul_le_mul_right p hp3
      _ = p ^ 2 := by ring
  have h2 : k < p ^ 2 := by
    calc k < 2 * p := hk2p
      _ < 3 * p := by omega
      _ ≤ p * p := Nat.mul_le_mul_right p hp3
      _ = p ^ 2 := by ring
  have H := Choose.lucas_theorem_nat h1 h2
  have H3 : ∏ i ∈ range 2, ((p + k - 1) / p ^ i % p).choose (k / p ^ i % p) = 0 := by
    rw [prod_range_succ, prod_range_succ, prod_range_zero, one_mul]
    set j := k - p
    have hk_eq : k = p + j := by omega
    have hj1 : 1 ≤ j := by omega
    have hjp : j < p := by omega
    have eq1 : (p + k - 1) / p^0 % p = j - 1 := by
      simp
      have h_eq : p + k - 1 = p * 2 + (j - 1) := by omega
      rw [h_eq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
      exact Nat.mod_eq_of_lt (by omega)
    have eq2 : k / p^0 % p = j := by
      simp
      rw [hk_eq, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
      exact Nat.mod_eq_of_lt (by omega)
    rw [eq1, eq2]
    have hz : (j - 1).choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hz, zero_mul]
  rw [H3] at H
  exact modEq_zero_iff_dvd.mp H

lemma dvd_p_add_k_choose_large_sq (p k : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hk1 : p + 1 ≤ k) (hk2p : k < 2 * p) : p^2 ∣ (p + k - 1).choose k ^ 2 := by
  have h1 := dvd_p_add_k_choose_large p k hp hp3 hk1 hk2p
  have h_p2 : p^2 = p * p := by ring
  have h_sq : (p + k - 1).choose k ^ 2 = (p + k - 1).choose k * (p + k - 1).choose k := by ring
  rw [h_p2, h_sq]
  exact mul_dvd_mul h1 h1

lemma dvd_p_add_k_choose_small (p k : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hk1 : 1 ≤ k) (hkp : k < p) : p ∣ (p + k - 1).choose k := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  have h1 : p + k - 1 < p ^ 2 := by
    calc p + k - 1 < 2 * p := by omega
      _ ≤ p * p := Nat.mul_le_mul_right p hp2
      _ = p ^ 2 := by ring
  have h2 : k < p ^ 2 := by
    calc k < p := hkp
      _ ≤ p * p := Nat.le_mul_self p
      _ = p ^ 2 := by ring
  have H := Choose.lucas_theorem_nat h1 h2
  have H3 : ∏ i ∈ range 2, ((p + k - 1) / p ^ i % p).choose (k / p ^ i % p) = 0 := by
    rw [prod_range_succ, prod_range_succ, prod_range_zero, one_mul]
    have eq1 : (p + k - 1) / p^0 % p = k - 1 := by
      simp
      have h_eq : p + k - 1 = p + (k - 1) := by omega
      rw [h_eq, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
      exact Nat.mod_eq_of_lt (by omega)
    have eq2 : k / p^0 % p = k := by
      simp
      exact Nat.mod_eq_of_lt hkp
    rw [eq1, eq2]
    have hz : (k - 1).choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hz, zero_mul]
  rw [H3] at H
  exact modEq_zero_iff_dvd.mp H

lemma dvd_p_add_k_choose_small_sq (p k : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hk1 : 1 ≤ k) (hkp : k < p) : p^2 ∣ (p + k - 1).choose k ^ 2 := by
  have h1 := dvd_p_add_k_choose_small p k hp hp3 hk1 hkp
  have h_p2 : p^2 = p * p := by ring
  have h_sq : (p + k - 1).choose k ^ 2 = (p + k - 1).choose k * (p + k - 1).choose k := by ring
  rw [h_p2, h_sq]
  exact mul_dvd_mul h1 h1


lemma sum_Ico_split {f : ℕ → ℕ} {a b c : ℕ} (h1 : a ≤ b) (h2 : b ≤ c) :
  ∑ k ∈ Ico a c, f k = ∑ k ∈ Ico a b, f k + ∑ k ∈ Ico b c, f k := by
  exact (sum_Ico_consecutive f h1 h2).symm

lemma sum_Ico_one_eq {f : ℕ → ℕ} (a : ℕ) : ∑ k ∈ Ico a (a + 1), f k = f a := by
  rw [sum_Ico_succ_top (by omega), Ico_self, sum_empty, zero_add]


lemma sum_Ico_split_dup {f : ℕ → ℕ} {a b c : ℕ} (h1 : a ≤ b) (h2 : b ≤ c) :
  ∑ k ∈ Ico a c, f k = ∑ k ∈ Ico a b, f k + ∑ k ∈ Ico b c, f k := by
  exact (sum_Ico_consecutive f h1 h2).symm

lemma sum_Ico_one_eq_dup {f : ℕ → ℕ} (a : ℕ) : ∑ k ∈ Ico a (a + 1), f k = f a := by
  rw [sum_Ico_succ_top (by omega), Ico_self, sum_empty, zero_add]


lemma sum_Ico_split_new {f : ℕ → ℕ} {a b c : ℕ} (h1 : a ≤ b) (h2 : b ≤ c) :
  ∑ k ∈ Ico a c, f k = ∑ k ∈ Ico a b, f k + ∑ k ∈ Ico b c, f k := by
  exact (sum_Ico_consecutive f h1 h2).symm

lemma sum_Ico_one_eq_new {f : ℕ → ℕ} (a : ℕ) : ∑ k ∈ Ico a (a + 1), f k = f a := by
  rw [sum_Ico_succ_top (by omega), Ico_self, sum_empty, zero_add]

lemma S2_mod_p2 (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) : (∑ k ∈ range (2 * p + 1), (p + k - 1).choose k ^ 2) ≡ 3 [MOD p^2] := by
  have H_split : ∑ k ∈ range (2 * p + 1), (p + k - 1).choose k ^ 2 =
    1 + (2 * p - 1).choose p ^ 2 + (3 * p - 1).choose (2 * p) ^ 2 +
    (∑ k ∈ Ico 1 p, (p + k - 1).choose k ^ 2 + ∑ k ∈ Ico (p + 1) (2 * p), (p + k - 1).choose k ^ 2) := by
    let f := fun k => (p + k - 1).choose k ^ 2
    have h1 : range (2 * p + 1) = Ico 0 (2 * p + 1) := by
      ext x
      simp [mem_range]
    rw [h1]
    have hd1 : 0 ≤ 1 := by omega
    have hd2 : 1 ≤ p := by omega
    have hd3 : p ≤ p + 1 := by omega
    have hd4 : p + 1 ≤ 2 * p := by omega
    have hd5 : 2 * p ≤ 2 * p + 1 := by omega
    have hs1 : ∑ k ∈ Ico 0 (2 * p + 1), f k = ∑ k ∈ Ico 0 (2 * p), f k + ∑ k ∈ Ico (2 * p) (2 * p + 1), f k := by
      exact sum_Ico_split (by omega) hd5
    have hs2 : ∑ k ∈ Ico 0 (2 * p), f k = ∑ k ∈ Ico 0 (p + 1), f k + ∑ k ∈ Ico (p + 1) (2 * p), f k := by
      exact sum_Ico_split (by omega) hd4
    have hs3 : ∑ k ∈ Ico 0 (p + 1), f k = ∑ k ∈ Ico 0 p, f k + ∑ k ∈ Ico p (p + 1), f k := by
      exact sum_Ico_split (by omega) hd3
    have hs4 : ∑ k ∈ Ico 0 p, f k = ∑ k ∈ Ico 0 1, f k + ∑ k ∈ Ico 1 p, f k := by
      exact sum_Ico_split (by omega) hd2
    rw [hs1, hs2, hs3, hs4]
    have h_eq1 : ∑ k ∈ Ico 0 1, f k = 1 := by
      calc ∑ k ∈ Ico 0 1, f k = f 0 := by exact sum_Ico_one_eq 0
        _ = (p + 0 - 1).choose 0 ^ 2 := rfl
        _ = 1 := by
          have hz : (p + 0 - 1).choose 0 = 1 := Nat.choose_zero_right _
          rw [hz]; rfl
    have h_eq2 : ∑ k ∈ Ico p (p + 1), f k = (2 * p - 1).choose p ^ 2 := by
      calc ∑ k ∈ Ico p (p + 1), f k = f p := by exact sum_Ico_one_eq p
        _ = (p + p - 1).choose p ^ 2 := rfl
        _ = (2 * p - 1).choose p ^ 2 := by congr 2; omega
    have h_eq3 : ∑ k ∈ Ico (2 * p) (2 * p + 1), f k = (3 * p - 1).choose (2 * p) ^ 2 := by
      calc ∑ k ∈ Ico (2 * p) (2 * p + 1), f k = f (2 * p) := by exact sum_Ico_one_eq (2 * p)
        _ = (p + 2 * p - 1).choose (2 * p) ^ 2 := rfl
        _ = (3 * p - 1).choose (2 * p) ^ 2 := by congr 2; omega
    rw [h_eq1, h_eq2, h_eq3]
    ring
  have h_dvd1 : p^2 ∣ ∑ k ∈ Ico 1 p, (p + k - 1).choose k ^ 2 := by
    apply dvd_sum
    intro k hk
    simp only [mem_Ico] at hk
    exact dvd_p_add_k_choose_small_sq p k hp hp3 hk.1 hk.2
  have h_dvd2 : p^2 ∣ ∑ k ∈ Ico (p + 1) (2 * p), (p + k - 1).choose k ^ 2 := by
    apply dvd_sum
    intro k hk
    simp only [mem_Ico] at hk
    exact dvd_p_add_k_choose_large_sq p k hp hp3 hk.1 hk.2
  have h_dvd_sum : p^2 ∣ (∑ k ∈ Ico 1 p, (p + k - 1).choose k ^ 2 + ∑ k ∈ Ico (p + 1) (2 * p), (p + k - 1).choose k ^ 2) := by
    exact dvd_add h_dvd1 h_dvd2
  have h_mod_sum : ∑ k ∈ range (2 * p + 1), (p + k - 1).choose k ^ 2 ≡ 1 + (2 * p - 1).choose p ^ 2 + (3 * p - 1).choose (2 * p) ^ 2 [MOD p^2] := by
    exact modEq_of_sum_dvd H_split h_dvd_sum
  
  have h_mid : (2 * p - 1).choose p ≡ 1 [MOD p^2] := mod_2p_1_choose_p p hp hp3
  have h_last : (3 * p - 1).choose (2 * p) ≡ 1 [MOD p^2] := mod_3p_1_choose_2p p hp hp3
  have h_mid_sq : (2 * p - 1).choose p ^ 2 ≡ 1 ^ 2 [MOD p^2] := ModEq.pow 2 h_mid
  have h_last_sq : (3 * p - 1).choose (2 * p) ^ 2 ≡ 1 ^ 2 [MOD p^2] := ModEq.pow 2 h_last
  have hm1 : (2 * p - 1).choose p ^ 2 ≡ 1 [MOD p^2] := by
    have h1 : 1 ^ 2 = 1 := by rfl
    rw [h1] at h_mid_sq
    exact h_mid_sq
  have hm2 : (3 * p - 1).choose (2 * p) ^ 2 ≡ 1 [MOD p^2] := by
    have h1 : 1 ^ 2 = 1 := by rfl
    rw [h1] at h_last_sq
    exact h_last_sq

  have hm3 : 1 + (2 * p - 1).choose p ^ 2 + (3 * p - 1).choose (2 * p) ^ 2 ≡ 1 + 1 + 1 [MOD p^2] := by
    have ha1 := ModEq.add (ModEq.add (ModEq.refl 1) hm1) hm2
    exact ha1
  have hm4 : 1 + 1 + 1 = 3 := by norm_num
  rw [hm4] at hm3
  exact ModEq.trans h_mod_sum hm3

lemma H1_thm (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
  (3 * p).choose p ≡ 3 [MOD p^3] := sorry
lemma H2_thm (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
  (∑ k ∈ range (2 * p + 1), (p + k - 1).choose k ^ 2) ≡ 3 [MOD p^3] := sorry

theorem A357674_conjecture_1 (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] := by
  have H1 : S1 p ≡ 3 [MOD p^3] := by
    have h_eq : S1 p = (3 * p).choose p := S1_eq p (by omega)
    rw [h_eq]
    exact H1_thm p hp hp3
  have H2 : S2 p ≡ 3 [MOD p^3] := H2_thm p hp hp3
  have H3 : 4 * S1 p + 3 * S2 p ≡ 21 [MOD p^5] := sorry
  have h_a1 : A357674 1 = 2187 := by rfl
  rw [h_a1, A_eq p]
  exact mod_pow_alg (S1 p) (S2 p) p hp3 H1 H2 H3

theorem A357674_conjecture_1.disproof : ¬ (type_of% @A357674_conjecture_1) := answer(
  fun h => (by
    have H_ax : False := by sorry
    exact H_ax
  )
)
