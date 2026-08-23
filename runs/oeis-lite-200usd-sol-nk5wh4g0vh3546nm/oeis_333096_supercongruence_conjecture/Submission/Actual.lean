import Submission.Bridge
open Nat Finset BigOperators Int

def generalized_choose_int (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1 else
    (Finset.prod (Finset.range k) fun i => r - (i : ℤ)) / (k.factorial : ℤ)

def generalized_catalan_coefficient (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1 else
    let num_choose := generalized_choose_int (r + 2 * (k : ℤ) - 1) k
    let denominator : ℤ := r + k
    (r * num_choose) / denominator

def a_gen (m : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 1 else
    let r : ℤ := m * (n : ℤ)
    Finset.sum (range (n + 1)) fun k => generalized_catalan_coefficient r k

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

lemma generalized_catalan_eq_formal (r : ℤ) (k : ℕ)
    (hden : k=0 ∨ r+(k:ℤ) ≠ 0) :
    generalized_catalan_coefficient r k = formalCatalanCoeff r k := by
  by_cases hk0 : k=0
  · subst k
    simp [generalized_catalan_coefficient, formalCatalanCoeff]
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    have hden' : r+(k:ℤ) ≠ 0 := hden.resolve_left hk0
    rw [generalized_catalan_coefficient_eq_sub r hk hden']
    simp [formalCatalanCoeff, hk0]

lemma a_gen_nat_eq_FNat (M N : ℕ) (hN : 0 < N) :
    a_gen (M : ℤ) N = FNat ((M+2)*N) N := by
  rw [a_gen, if_neg (Nat.ne_of_gt hN)]
  rw [← formalPartial_eq_FNat ((M+2)*N) N]
  have hr : (((M+2)*N : ℕ) : ℤ) - 2*(N : ℤ) = (M : ℤ)*(N : ℤ) := by
    push_cast
    ring
  rw [hr]
  unfold formalPartial
  apply Finset.sum_congr rfl
  intro k hk
  apply generalized_catalan_eq_formal
  by_cases hk0 : k=0
  · exact Or.inl hk0
  · right
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have : k ≤ N := by simp only [Finset.mem_range] at hk; omega
    positivity

lemma formalCoeff_neg_one_endpoint (N : ℕ) (hN : 0 < N) :
    formalCatalanCoeff (-(N : ℤ)) N = -1 := by
  rw [formalCatalanCoeff, if_neg (Nat.ne_of_gt hN)]
  have hu : -(N : ℤ) + 2*(N : ℤ)-1 = ((N-1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    ring
  rw [hu, Ring.choose_natCast, Ring.choose_natCast]
  rw [Nat.choose_eq_zero_of_lt (by omega : N-1 < N), Nat.choose_self]
  norm_num

lemma actualCoeff_neg_one (N k : ℕ) (hN : 0 < N) (hk : k ≤ N) :
    generalized_catalan_coefficient (-(N : ℤ)) k =
      formalCatalanCoeff (-(N : ℤ)) k + (if k=N then 1 else 0) := by
  by_cases hkN : k=N
  · subst k
    rw [formalCoeff_neg_one_endpoint N hN]
    simp [generalized_catalan_coefficient, hN.ne']
  · rw [if_neg hkN, add_zero]
    apply generalized_catalan_eq_formal
    by_cases hk0 : k=0
    · exact Or.inl hk0
    · right
      push_cast
      omega

lemma a_gen_neg_one_eq_FNat (N : ℕ) (hN : 0 < N) :
    a_gen (-1) N = FNat N N + 1 := by
  rw [a_gen, if_neg (Nat.ne_of_gt hN)]
  simp only [neg_one_mul]
  rw [← formalPartial_eq_FNat N N]
  have hr : ((N : ℤ)-2*(N : ℤ)) = -(N : ℤ) := by ring
  rw [hr]
  unfold formalPartial
  have hind : (∑ k ∈ Finset.range (N+1), (if k=N then (1:ℤ) else 0)) = 1 := by
    rw [Finset.sum_eq_single N]
    · simp
    · intro b hb hne; simp [hne]
    · simp
  calc
    (∑ k ∈ Finset.range (N+1), generalized_catalan_coefficient (-(N:ℤ)) k) =
        ∑ k ∈ Finset.range (N+1),
          (formalCatalanCoeff (-(N:ℤ)) k + (if k=N then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro k hk
            apply actualCoeff_neg_one N k hN
            simp only [Finset.mem_range] at hk
            omega
    _ = (∑ k ∈ Finset.range (N+1), formalCatalanCoeff (-(N:ℤ)) k) +
          ∑ k ∈ Finset.range (N+1), (if k=N then 1 else 0) :=
            Finset.sum_add_distrib
    _ = _ := by rw [hind]

lemma a_gen_neg_two_eq_FNat (N : ℕ) (hN : 0 < N) :
    a_gen (-2) N = FNat 0 N := by
  rw [a_gen, if_neg (Nat.ne_of_gt hN)]
  rw [← formalPartial_eq_FNat 0 N]
  change (∑ k ∈ Finset.range (N+1),
      generalized_catalan_coefficient ((-2)*(N:ℤ)) k) =
    formalPartial ((0:ℤ)-2*(N:ℤ)) N

  have hr : ((0 : ℤ)-2*(N : ℤ)) = (-2)*(N : ℤ) := by ring
  rw [hr]
  unfold formalPartial
  apply Finset.sum_congr rfl
  intro k hk
  apply generalized_catalan_eq_formal
  by_cases hk0 : k=0
  · exact Or.inl hk0
  · right
    have hkN : k ≤ N := by simp only [Finset.mem_range] at hk; omega
    push_cast
    omega

lemma FNat_zero (N : ℕ) : FNat 0 N = Core.qCoeff N := by
  unfold FNat
  simp only [pow_zero, Polynomial.coe_one, mul_one, Core.Qseries,
    PowerSeries.coeff_mk]

lemma a_gen_nat_scale {M p N lev : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) (hdiv : p^lev ∣ N) :
    a_gen (M:ℤ) (p*N) ≡ a_gen (M:ℤ) N
      [ZMOD ((p:ℤ)^(3*(lev+1)))] := by
  have hpN : 0 < p*N := mul_pos hp.pos hN
  rw [a_gen_nat_eq_FNat M (p*N) hpN, a_gen_nat_eq_FNat M N hN]
  have hY : p^lev ∣ (M+1)*N := dvd_mul_of_dvd_right hdiv (M+1)
  have h := FNat_scale_supercongruence hp hp5 hdiv hY
  convert h using 1 <;> ring

lemma a_gen_neg_one_scale {p N lev : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) (hdiv : p^lev ∣ N) :
    a_gen (-1) (p*N) ≡ a_gen (-1) N
      [ZMOD ((p:ℤ)^(3*(lev+1)))] := by
  rw [a_gen_neg_one_eq_FNat (p*N) (mul_pos hp.pos hN),
    a_gen_neg_one_eq_FNat N hN]
  exact (FNat_scale_supercongruence hp hp5 hdiv (dvd_zero _)).add rfl

lemma a_gen_neg_two_scale {p N lev : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) :
    a_gen (-2) (p*N) ≡ a_gen (-2) N
      [ZMOD ((p:ℤ)^(3*(lev+1)))] := by
  rw [a_gen_neg_two_eq_FNat (p*N) (mul_pos hp.pos hN),
    a_gen_neg_two_eq_FNat N hN, FNat_zero, FNat_zero]
  have hq := Core.qCoeff_mul_prime (hp := hp) (hp5 := hp5) (n := N)
  rw [hq]

