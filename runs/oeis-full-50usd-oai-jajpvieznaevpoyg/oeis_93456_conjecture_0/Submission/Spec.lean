import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A093456: Product of all composite numbers between $n(n-1)/2+1$ and $n(n+1)/2$ (including boundaries),
where $n(n-1)/2 = \binom{n}{2}$ and $n(n+1)/2 = \binom{n+1}{2}$.
-/
def a (n : ℕ) : ℕ :=
  let L := n.choose 2 + 1
  let R := (n + 1).choose 2

  -- A number k is composite if k > 1 and is not prime.
  let is_composite (k : ℕ) : Prop := 1 < k ∧ ¬ k.Prime

  (Icc L R).filter is_composite |>.prod id



lemma digits_two_pow_add_one (r : ℕ) :
    (2:ℕ).digits (1 + 2 ^ (r+1)) = [1] ++ List.replicate r 0 ++ [1] := by
  have h := Nat.digits_append_zeroes_append_digits (b := 2) (k := r) (m := 1) (n := 1) (by norm_num) (by norm_num)
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h.symm

lemma sum_digits_two_pow_add_one (r : ℕ) : ((2:ℕ).digits (1 + 2 ^ (r+1))).sum = 2 := by
  rw [digits_two_pow_add_one r]
  simp

lemma sum_digits_shift_pow_add_one (s r : ℕ) :
    ((2:ℕ).digits (2 ^ s * (1 + 2 ^ (r+1)))).sum = 2 := by
  rw [Nat.digits_base_pow_mul (b := 2) (k := s) (m := (1 + 2 ^ (r+1))) (by norm_num) (by positivity)]
  rw [List.sum_append, List.sum_replicate, sum_digits_two_pow_add_one r]
  simp

lemma sum_digits_two_pow_sub_one (r : ℕ) : ((2:ℕ).digits (2 ^ (r+1) - 1)).sum = r+1 := by
  induction r with
  | zero => norm_num
  | succ r ih =>
      have hpos : 0 < 2 ^ (r+1) := pow_pos (by norm_num) _
      have h : 2 ^ (r.succ + 1) - 1 = 1 + 2 * (2 ^ (r+1) - 1) := by
        rw [Nat.succ_eq_add_one]
        have hp : 1 <= 2 ^ (r+1) := hpos
        omega
      rw [h]
      rw [Nat.digits_add (b := 2) (h := by norm_num) (x := 1) (y := (2 ^ (r+1) - 1)) (by norm_num) (by exact Or.inl (by norm_num))]
      change 1 + ((2:ℕ).digits (2 ^ (r+1) - 1)).sum = r + 1 + 1
      rw [ih]
      omega

lemma sum_digits_shift_pow_sub_one (s r : ℕ) :
    ((2:ℕ).digits (2 ^ s * (2 ^ (r+1) - 1))).sum = r+1 := by
  rw [Nat.digits_base_pow_mul (b := 2) (k := s) (m := (2 ^ (r+1) - 1)) (by norm_num) (by
    have h : 1 < 2 ^ (r+1) := by exact one_lt_pow₀ (by norm_num : 1 < (2:ℕ)) (by omega)
    omega)]
  rw [List.sum_append, List.sum_replicate, sum_digits_two_pow_sub_one r]
  simp

lemma sum_digits_upper_endpoint (r : ℕ) :
    ((2:ℕ).digits ((1 + 2 ^ (r+2)) * (1 + 2 ^ (r+1)))).sum = 4 := by
  let low := 1 + 2 ^ (r+1)
  have hlen : ((2:ℕ).digits low).length = r + 2 := by
    change ((2:ℕ).digits (1 + 2 ^ (r+1))).length = r + 2
    rw [digits_two_pow_add_one r]
    simp
  have h := Nat.digits_append_digits (b := 2) (m := (1 + 2 ^ (r+1))) (n := low) (by norm_num : 0 < (2:ℕ))
  have hnum : low + 2 ^ (((2:ℕ).digits low).length) * (1 + 2 ^ (r+1)) = (1 + 2 ^ (r+2)) * (1 + 2 ^ (r+1)) := by
    rw [hlen]
    ring
  rw [← hnum]
  rw [← h]
  rw [List.sum_append]
  change ((2:ℕ).digits (1 + 2 ^ (r+1))).sum + ((2:ℕ).digits (1 + 2 ^ (r+1))).sum = 4
  rw [sum_digits_two_pow_add_one r]

lemma padicValNat_two_factorial (n : ℕ) :
    padicValNat 2 (Nat.factorial n) = n - ((2:ℕ).digits n).sum := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) n
  simpa [Nat.factorial] using h

lemma padicValNat_two_ascFactorial (c l : ℕ) :
    padicValNat 2 ((c+1).ascFactorial l) = padicValNat 2 (Nat.factorial (c+l)) - padicValNat 2 (Nat.factorial c) := by
  have h0 := Nat.factorial_mul_ascFactorial c l
  have h := congrArg (padicValNat 2) h0
  rw [padicValNat.mul (Nat.factorial_ne_zero c) (Nat.ascFactorial_pos c l).ne'] at h
  rw [add_comm] at h
  exact Nat.eq_sub_of_add_eq h

lemma pow_sub_one_large (t : ℕ) : t + 3 ≤ 2 ^ (t+3) - 1 := by
  have h : t + 4 ≤ 2 ^ (t+3) := by
    induction t with
    | zero => norm_num
    | succ t ih =>
        rw [show t.succ + 3 = (t+3)+1 by omega, pow_succ]
        nlinarith [ih]
  omega

lemma two_pow_succ_eq_two_mul (t : ℕ) : 2 ^ (t+3) = 2 * 2 ^ (t+2) := by
  rw [show t+3 = (t+2)+1 by omega, pow_succ]
  ring

lemma A_eq_C_add_N (t : ℕ) :
    2 ^ (t+2) * (1 + 2 ^ (t+3)) = 2 ^ (t+2) * (2 ^ (t+3) - 1) + 2 ^ (t+3) := by
  set p := 2 ^ (t+2)
  set q := 2 ^ (t+3)
  have hq : 1 ≤ q := by subst q; exact Nat.one_le_two_pow
  have hq2 : 1 + q = (q - 1) + 2 := by omega
  have hqp : q = 2 * p := by subst p q; exact two_pow_succ_eq_two_mul t
  calc
    p * (1 + q) = p * ((q - 1) + 2) := by rw [hq2]
    _ = p * (q - 1) + 2 * p := by ring
    _ = p * (q - 1) + q := by rw [hqp]

lemma B_eq_A_add_len (t : ℕ) :
    (1 + 2 ^ (t+3)) * (1 + 2 ^ (t+2)) = 2 ^ (t+2) * (1 + 2 ^ (t+3)) + (2 ^ (t+3) + 1) := by
  have h : 2 ^ (t+3) = 2 * 2 ^ (t+2) := two_pow_succ_eq_two_mul t
  rw [h]
  ring

lemma v_prev2 (t : ℕ) :
    padicValNat 2 (((2 ^ (t+2) * (2 ^ (t+3) - 1)) + 1).ascFactorial (2 ^ (t+3)))
      = 2 ^ (t+3) + (t+3) - 2 := by
  rw [padicValNat_two_ascFactorial]
  rw [← A_eq_C_add_N]
  rw [padicValNat_two_factorial, padicValNat_two_factorial]
  rw [sum_digits_shift_pow_add_one (t+2) (t+2), sum_digits_shift_pow_sub_one (t+2) (t+2)]
  rw [A_eq_C_add_N]
  set C := 2 ^ (t + 2) * (2 ^ (t + 3) - 1)
  set N := 2 ^ (t + 3)
  have hC : t + 3 ≤ C := by
    subst C
    exact (pow_sub_one_large t).trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
  omega

lemma v_next2 (t : ℕ) :
    padicValNat 2 (((2 ^ (t+2) * (1 + 2 ^ (t+3))) + 1).ascFactorial (2 ^ (t+3) + 1))
      = 2 ^ (t+3) - 1 := by
  rw [padicValNat_two_ascFactorial]
  rw [← B_eq_A_add_len]
  rw [padicValNat_two_factorial, padicValNat_two_factorial]
  rw [sum_digits_upper_endpoint (t+1), sum_digits_shift_pow_add_one (t+2) (t+2)]
  rw [B_eq_A_add_len]
  set A := 2 ^ (t + 2) * (1 + 2 ^ (t + 3))
  set N := 2 ^ (t + 3)
  have hA : 2 ≤ A := by
    subst A
    nlinarith [Nat.two_pow_pos (t+2), Nat.one_le_two_pow (n:=t+3)]
  omega

lemma not_prime_of_two_dvd_of_two_lt {x : ℕ} (hd : 2 ∣ x) (hx : 2 < x) : ¬ x.Prime := by
  intro hp
  rcases hp.eq_two_or_odd with h | hodd
  · omega
  · have hmod : x % 2 = 0 := Nat.mod_eq_zero_of_dvd hd
    omega

lemma factorization_two_a_eq_all (n : ℕ) (hL : 2 < n.choose 2 + 1) :
    (a n).factorization 2 = ((Icc (n.choose 2 + 1) ((n+1).choose 2)).prod id).factorization 2 := by
  unfold a
  rw [Nat.factorization_prod_apply, Nat.factorization_prod_apply]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hc : 1 < x ∧ ¬ x.Prime
    · simp [hc]
    · simp [hc]
      have hx2 : 2 < x := by
        simp only [mem_Icc] at hx
        omega
      by_cases hd : 2 ∣ x
      · exfalso
        apply hc
        exact ⟨by omega, not_prime_of_two_dvd_of_two_lt hd hx2⟩
      · exact (Nat.factorization_eq_zero_of_not_dvd hd).symm
  · intro x hx
    simp only [mem_Icc] at hx
    change x ≠ 0
    omega
  · intro x hx
    simp only [mem_filter, mem_Icc] at hx
    change id x ≠ 0
    simp only [id_eq]
    omega

lemma prod_Icc_id_eq_ascFactorial (L len : ℕ) (hlen : 0 < len) :
    (∏ x ∈ Finset.Icc L (L + len - 1), id x) = L.ascFactorial len := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  have hsucc : L + len - 1 + 1 = L + len := by omega
  rw [hsucc]
  rw [Finset.prod_Ico_eq_prod_range]
  have hsub : L + len - L = len := by omega
  rw [hsub]
  rw [Nat.ascFactorial_eq_prod_range]
  simp

lemma choose_pow (t : ℕ) : (2 ^ (t+3)).choose 2 = 2 ^ (t+2) * (2 ^ (t+3) - 1) := by
  rw [Nat.choose_two_right]
  rw [show 2 ^ (t+3) = 2 * 2 ^ (t+2) by
    rw [show t+3=(t+2)+1 by omega, pow_succ]; ring]
  rw [show (2 * 2 ^ (t+2)) * (2 * 2 ^ (t+2) - 1) = 2 * (2 ^ (t+2) * (2 * 2 ^ (t+2) - 1)) by ring]
  rw [mul_comm 2]
  rw [Nat.mul_div_left _ (by norm_num : 0 < 2)]

lemma choose_pow_succ (t : ℕ) : (2 ^ (t+3) + 1).choose 2 = 2 ^ (t+2) * (1 + 2 ^ (t+3)) := by
  rw [Nat.choose_two_right]
  have h : (2 ^ (t+3) + 1) - 1 = 2 ^ (t+3) := by exact Nat.add_sub_cancel (2 ^ (t+3)) 1
  rw [h]
  rw [show 2 ^ (t+3) = 2 * 2 ^ (t+2) by
    rw [show t+3=(t+2)+1 by omega, pow_succ]; ring]
  rw [show (2 * 2 ^ (t+2) + 1) * (2 * 2 ^ (t+2)) = 2 * (2 ^ (t+2) * (1 + 2 * 2 ^ (t+2))) by ring]
  rw [mul_comm 2]
  rw [Nat.mul_div_left _ (by norm_num : 0 < 2)]

lemma choose_pow_add_two (t : ℕ) : (2 ^ (t+3) + 2).choose 2 = (1 + 2 ^ (t+3)) * (1 + 2 ^ (t+2)) := by
  rw [Nat.choose_two_right]
  have hsub : (2 ^ (t+3) + 2) - 1 = 2 ^ (t+3) + 1 := by
    have hp : 0 < 2 ^ (t+3) := Nat.two_pow_pos _
    omega
  rw [hsub]
  rw [show 2 ^ (t+3) = 2 * 2 ^ (t+2) by
    rw [show t+3=(t+2)+1 by omega, pow_succ]; ring]
  rw [show (2 * 2 ^ (t+2) + 2) * (2 * 2 ^ (t+2) + 1) = 2 * ((1 + 2 ^ (t+2)) * (1 + 2 * 2 ^ (t+2))) by ring]
  rw [mul_comm 2]
  rw [Nat.mul_div_left _ (by norm_num : 0 < 2)]
  ring

lemma choose_two_add_one_gt_two {n : ℕ} (hn : 3 ≤ n) : 2 < n.choose 2 + 1 := by
  have hmono := Nat.choose_le_choose 2 hn
  norm_num at hmono
  omega

lemma a_pos (n : ℕ) : 0 < a n := by
  unfold a
  apply Finset.prod_pos
  intro x hx
  simp only [mem_filter, mem_Icc] at hx
  change 0 < x
  omega

lemma factorization_two_a_pow (t : ℕ) :
    (a (2 ^ (t+3))).factorization 2 = 2 ^ (t+3) + (t+3) - 2 := by
  have hL : 2 < (2 ^ (t+3)).choose 2 + 1 := by
    apply choose_two_add_one_gt_two
    have h : 3 ≤ 2 ^ (t+3) := by
      have h8 : 8 ≤ 2 ^ (t+3) := by
        rw [show t+3 = 3 + t by omega]
        rw [pow_add]
        nlinarith [Nat.one_le_two_pow (n:=t)]
      omega
    exact h
  rw [factorization_two_a_eq_all _ hL]
  rw [choose_pow t, choose_pow_succ t]
  rw [A_eq_C_add_N t]
  have hend : 2 ^ (t+2) * (2 ^ (t+3) - 1) + 1 + 2 ^ (t+3) - 1 =
      2 ^ (t+2) * (2 ^ (t+3) - 1) + 2 ^ (t+3) := by
    rw [show 2 ^ (t+2) * (2 ^ (t+3) - 1) + 1 + 2 ^ (t+3) =
        (2 ^ (t+2) * (2 ^ (t+3) - 1) + 2 ^ (t+3)) + 1 by omega]
    exact Nat.add_sub_cancel _ _
  rw [← hend]
  rw [prod_Icc_id_eq_ascFactorial _ _ (Nat.two_pow_pos _)]
  rw [Nat.factorization_def _ Nat.prime_two]
  exact v_prev2 t

lemma factorization_two_a_pow_succ (t : ℕ) :
    (a (2 ^ (t+3) + 1)).factorization 2 = 2 ^ (t+3) - 1 := by
  have hL : 2 < (2 ^ (t+3) + 1).choose 2 + 1 := by
    apply choose_two_add_one_gt_two
    have h : 3 ≤ 2 ^ (t+3) + 1 := by
      have h8 : 8 ≤ 2 ^ (t+3) := by
        rw [show t+3 = 3 + t by omega]
        rw [pow_add]
        nlinarith [Nat.one_le_two_pow (n:=t)]
      omega
    exact h
  rw [factorization_two_a_eq_all _ hL]
  have hs : (2 ^ (t+3) + 1 + 1) = 2 ^ (t+3) + 2 := by omega
  rw [hs]
  rw [choose_pow_succ t, choose_pow_add_two t]
  rw [B_eq_A_add_len t]
  have hend : 2 ^ (t+2) * (1 + 2 ^ (t+3)) + 1 + (2 ^ (t+3) + 1) - 1 =
      2 ^ (t+2) * (1 + 2 ^ (t+3)) + (2 ^ (t+3) + 1) := by
    rw [show 2 ^ (t+2) * (1 + 2 ^ (t+3)) + 1 + (2 ^ (t+3) + 1) =
        (2 ^ (t+2) * (1 + 2 ^ (t+3)) + (2 ^ (t+3) + 1)) + 1 by omega]
    exact Nat.add_sub_cancel _ _
  rw [← hend]
  rw [prod_Icc_id_eq_ascFactorial _ _ (Nat.succ_pos _)]
  rw [Nat.factorization_def _ Nat.prime_two]
  exact v_next2 t

lemma bad_pow (t : ℕ) :
    (2 ^ (t+3) + 1) > 1 ∧ ¬ (a ((2 ^ (t+3) + 1) - 1) ∣ a (2 ^ (t+3) + 1)) := by
  constructor
  · have hp : 0 < 2 ^ (t+3) := Nat.two_pow_pos _
    omega
  · have hsub : (2 ^ (t+3) + 1) - 1 = 2 ^ (t+3) := by exact Nat.add_sub_cancel (2 ^ (t+3)) 1
    rw [hsub]
    intro hdiv
    have hle := (Nat.factorization_le_iff_dvd (a_pos (2 ^ (t+3))).ne' (a_pos (2 ^ (t+3) + 1)).ne').mpr hdiv
    have hle2 := hle 2
    rw [factorization_two_a_pow t, factorization_two_a_pow_succ t] at hle2
    have hpos : 0 < 2 ^ (t+3) := Nat.two_pow_pos _
    omega

/--
The conjecture is false: for every `t`, `n = 2^(t+3)+1` is an exception.  The
2-adic valuation of `a (2^(t+3))` exceeds that of `a (2^(t+3)+1)` by `t+2`.
-/
theorem oeis_93456_conjecture_0.disproof :
  ¬ Set.Finite {n : ℕ | n > 1 ∧ ¬ (a (n - 1) ∣ a n)} := by
  intro hfin
  have hinf : (Set.range fun t : ℕ => 2 ^ (t+3) + 1).Infinite := by
    apply Set.infinite_range_of_injective
    intro x y hxy
    apply Nat.add_right_cancel at hxy
    have hpow : 2 ^ (x+3) = 2 ^ (y+3) := hxy
    exact Nat.add_right_cancel (Nat.pow_right_injective (by norm_num : 2 ≤ (2:ℕ)) hpow)
  exact hinf.not_finite (hfin.subset (by
    rintro n ⟨t, rfl⟩
    exact bad_pow t))
