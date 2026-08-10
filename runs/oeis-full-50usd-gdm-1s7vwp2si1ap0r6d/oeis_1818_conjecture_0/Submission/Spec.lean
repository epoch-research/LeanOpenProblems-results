import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix Equiv

/--
A001818: Squares of double factorials: $(1 \cdot 3 \cdot 5 \cdot \dots \cdot (2n-1))^2 = ((2n-1)!!)^2$.
-/
def a (n : ℕ) : ℕ :=
  ((range n).prod (fun k => 2 * k + 1)) ^ 2

lemma eq_neg_one_of_isPrimitiveRoot_two (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 2) : ζ = -1 := by
  have h_pow : ζ ^ 2 = 1 := hζ.pow_eq_one
  have h_ne : ζ ≠ 1 := by
    intro h
    have h_dvd : 2 ∣ 1 := hζ.dvd_of_pow_eq_one 1 (by rw [h, pow_one])
    norm_num at h_dvd
  have h_sq : ζ ^ 2 - 1 = 0 := sub_eq_zero.mpr h_pow
  have h_factor : (ζ - 1) * (ζ + 1) = 0 := by
    calc (ζ - 1) * (ζ + 1) = ζ ^ 2 - 1 := by ring
    _ = 0 := h_sq
  cases mul_eq_zero.mp h_factor with
  | inl h1 =>
    have : ζ = 1 := by
      calc ζ = (ζ - 1) + 1 := by ring
      _ = 0 + 1 := by rw [h1]
      _ = 1 := by ring
    contradiction
  | inr h2 =>
    calc ζ = (ζ + 1) - 1 := by ring
    _ = 0 - 1 := by rw [h2]
    _ = -1 := by ring

lemma permanent_two (M : Matrix (Fin 2) (Fin 2) ℂ) :
    permanent M = M 0 0 * M 1 1 + M 1 0 * M 0 1 := by
  unfold permanent
  have h_univ : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [h_univ]
  simp_rw [Fin.prod_univ_two]
  have h_ne : (1 : Equiv.Perm (Fin 2)) ∉ ({Equiv.swap 0 1} : Finset (Equiv.Perm (Fin 2))) := by decide
  rw [Finset.sum_insert h_ne, Finset.sum_singleton]
  simp

theorem oeis_1818_conjecture_0_n1 (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 2) :
    permanent (fun (i j : Fin 2) =>
      if i = j then
        (1 : ℂ)
      else
        (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
    ) = (a 1 : ℂ) := by
  have h_zeta : ζ = -1 := eq_neg_one_of_isPrimitiveRoot_two ζ hζ
  rw [h_zeta, permanent_two]
  simp [a]


lemma sq_eq_neg_one_of_isPrimitiveRoot_four (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 4) : ζ ^ 2 = -1 := by
  have h4 : ζ ^ 4 = 1 := hζ.pow_eq_one
  have h2 : ζ ^ 2 ≠ 1 := by
    intro h
    have hdvd : 4 ∣ 2 := hζ.dvd_of_pow_eq_one 2 h
    norm_num at hdvd
  have h_factor : (ζ ^ 2 - 1) * (ζ ^ 2 + 1) = 0 := by
    calc (ζ ^ 2 - 1) * (ζ ^ 2 + 1) = ζ ^ 4 - 1 := by ring
    _ = 0 := by rw [h4, sub_self]
  cases mul_eq_zero.mp h_factor with
  | inl h_inl =>
    have : ζ ^ 2 = 1 := sub_eq_zero.mp h_inl
    contradiction
  | inr h_inr =>
    calc ζ ^ 2 = (ζ ^ 2 + 1) - 1 := by ring
    _ = 0 - 1 := by rw [h_inr]
    _ = -1 := by ring

lemma inv_eq_neg_of_isPrimitiveRoot_four (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 4) : ζ⁻¹ = -ζ := by
  have h_sq : ζ ^ 2 = -1 := sq_eq_neg_one_of_isPrimitiveRoot_four ζ hζ
  have h_ne_zero : ζ ≠ 0 := by
    intro h
    subst h
    have : (0 : ℂ) ^ 4 = 1 := hζ.pow_eq_one
    norm_num at this
  calc ζ⁻¹ = ζ⁻¹ * 1 := (mul_one _).symm
  _ = ζ⁻¹ * -(ζ ^ 2) := by rw [h_sq, neg_neg]
  _ = - (ζ⁻¹ * (ζ * ζ)) := by ring
  _ = - (ζ⁻¹ * ζ * ζ) := by ring_nf
  _ = - (1 * ζ) := by rw [inv_mul_cancel₀ h_ne_zero]
  _ = -ζ := by ring

lemma zpow_simpl (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 4) :
    (ζ ^ (0 : ℤ) = 1) ∧
    (ζ ^ (1 : ℤ) = ζ) ∧
    (ζ ^ (2 : ℤ) = -1) ∧
    (ζ ^ (3 : ℤ) = -ζ) ∧
    (ζ ^ (-1 : ℤ) = -ζ) ∧
    (ζ ^ (-2 : ℤ) = -1) ∧
    (ζ ^ (-3 : ℤ) = ζ) := by
  have h_sq : ζ ^ 2 = -1 := sq_eq_neg_one_of_isPrimitiveRoot_four ζ hζ
  have h_sq_z : ζ ^ (2 : ℤ) = -1 := by
    have : ζ ^ (2 : ℤ) = ζ ^ 2 := by norm_cast
    rw [this, h_sq]
  have h_ne_zero : ζ ≠ 0 := by
    intro h
    subst h
    have : (0 : ℂ) ^ 4 = 1 := hζ.pow_eq_one
    norm_num at this
  refine ⟨by simp, ⟨by simp, ⟨h_sq_z, ?_⟩⟩⟩
  have h3 : ζ ^ (3 : ℤ) = -ζ := by
    have : (3 : ℤ) = 2 + 1 := rfl
    rw [this, zpow_add₀ h_ne_zero, h_sq_z]
    simp
  refine ⟨h3, ?_⟩
  have h_neg1 : ζ ^ (-1 : ℤ) = -ζ := by
    have h4 : ζ ^ (4 : ℤ) = 1 := by
      have : ζ ^ (4 : ℤ) = ζ ^ 4 := by norm_cast
      rw [this, hζ.pow_eq_one]
    have h_neg4_eq : (-4 : ℤ) = 4 * -1 := by norm_num
    calc ζ ^ (-1 : ℤ) = ζ ^ (3 + -4 : ℤ) := by ring_nf
    _ = ζ ^ (3 : ℤ) * ζ ^ (-4 : ℤ) := zpow_add₀ h_ne_zero 3 (-4)
    _ = -ζ * ζ ^ (4 * -1 : ℤ) := by rw [h3, h_neg4_eq]
    _ = -ζ * (ζ ^ (4 : ℤ)) ^ (-1 : ℤ) := by rw [_root_.zpow_mul]
    _ = -ζ * 1 ^ (-1 : ℤ) := by rw [h4]
    _ = -ζ := by ring
  refine ⟨h_neg1, ?_⟩
  have h_neg2 : ζ ^ (-2 : ℤ) = -1 := by
    have h_neg2_eq : (-2 : ℤ) = 2 * -1 := by norm_num
    calc ζ ^ (-2 : ℤ) = ζ ^ (2 * -1 : ℤ) := by rw [h_neg2_eq]
    _ = (ζ ^ (2 : ℤ)) ^ (-1 : ℤ) := by rw [_root_.zpow_mul]
    _ = (-1) ^ (-1 : ℤ) := by rw [h_sq_z]
    _ = -1 := by norm_num
  refine ⟨h_neg2, ?_⟩
  have h_neg3 : ζ ^ (-3 : ℤ) = ζ := by
    calc ζ ^ (-3 : ℤ) = ζ ^ (-2 + -1 : ℤ) := by ring_nf
    _ = ζ ^ (-2 : ℤ) * ζ ^ (-1 : ℤ) := zpow_add₀ h_ne_zero (-2) (-1)
    _ = -1 * -ζ := by rw [h_neg2, h_neg1]
    _ = ζ := by ring
  exact h_neg3

lemma denom_ne_zero (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 4) :
    (1 - ζ ≠ 0) ∧ (1 + ζ ≠ 0) := by
  have h_sq : ζ ^ 2 = -1 := sq_eq_neg_one_of_isPrimitiveRoot_four ζ hζ
  have h1 : 1 - ζ = 0 → False := by
    intro h
    have : ζ = 1 := by
      calc ζ = -(1 - ζ) + 1 := by ring
      _ = -0 + 1 := by rw [h]
      _ = 1 := by ring
    have h_sq2 : ζ ^ 2 = 1 := by rw [this, one_pow]
    rw [h_sq] at h_sq2
    norm_num at h_sq2
  have h2 : 1 + ζ = 0 → False := by
    intro h
    have : ζ = -1 := by
      calc ζ = (1 + ζ) - 1 := by ring
      _ = 0 - 1 := by rw [h]
      _ = -1 := by ring
    have h_sq2 : ζ ^ 2 = 1 := by rw [this, neg_one_sq]
    rw [h_sq] at h_sq2
    norm_num at h_sq2
  exact ⟨h1, h2⟩

noncomputable def M_val (ζ : ℂ) (i j : Fin 4) : ℂ :=
  if i = j then (1 : ℂ) else (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))

lemma M_val_concrete (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 4) (i j : Fin 4) :
    M_val ζ i j =
    if i = 0 ∧ j = 0 then 1
    else if i = 1 ∧ j = 1 then 1
    else if i = 2 ∧ j = 2 then 1
    else if i = 3 ∧ j = 3 then 1
    else if i = 0 ∧ j = 1 then (1 - ζ) / (1 + ζ)
    else if i = 0 ∧ j = 2 then 0
    else if i = 0 ∧ j = 3 then (1 + ζ) / (1 - ζ)
    else if i = 1 ∧ j = 0 then (1 + ζ) / (1 - ζ)
    else if i = 1 ∧ j = 2 then (1 - ζ) / (1 + ζ)
    else if i = 1 ∧ j = 3 then 0
    else if i = 2 ∧ j = 0 then 0
    else if i = 2 ∧ j = 1 then (1 + ζ) / (1 - ζ)
    else if i = 2 ∧ j = 3 then (1 - ζ) / (1 + ζ)
    else if i = 3 ∧ j = 0 then (1 - ζ) / (1 + ζ)
    else if i = 3 ∧ j = 1 then 0
    else if i = 3 ∧ j = 2 then (1 + ζ) / (1 - ζ)
    else 0 := by
  have h_powers := zpow_simpl ζ hζ
  rcases h_powers with ⟨_, hp1, hp2, hp3, hp_neg1, hp_neg2, hp_neg3⟩
  unfold M_val
  fin_cases i <;> fin_cases j <;> (simp [hp1, hp2, hp3, hp_neg1, hp_neg2, hp_neg3]; try ring; try norm_num)

lemma univ_perm_four : (Finset.univ : Finset (Equiv.Perm (Fin 4))) =
  {1,
   c[2, 3],
   c[1, 2],
   c[1, 2, 3],
   c[1, 3],
   c[1, 3, 2],
   c[0, 1],
   c[0, 1] * c[2, 3],
   c[0, 1, 2],
   c[0, 1, 2, 3],
   c[0, 1, 3],
   c[0, 1, 3, 2],
   c[0, 2],
   c[0, 2, 3],
   c[0, 2, 1],
   c[0, 2, 3, 1],
   c[0, 2] * c[1, 3],
   c[0, 2, 1, 3],
   c[0, 3],
   c[0, 3, 2],
   c[0, 3] * c[1, 2],
   c[0, 3, 1, 2],
   c[0, 3, 1],
   c[0, 3, 2, 1]} := by decide

theorem oeis_1818_conjecture_0_n2 (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 4) :
    Matrix.permanent (fun (i j : Fin 4) =>
      if i = j then
        (1 : ℂ)
      else
        (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
    ) = 9 := by
  have h_M_val : (fun (i j : Fin 4) => if i = j then (1 : ℂ) else (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))) = M_val ζ := rfl
  rw [h_M_val]
  unfold Matrix.permanent
  rw [univ_perm_four]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp_rw [Fin.prod_univ_four]
  simp [Equiv.swap_apply_def]
  simp_rw [M_val_concrete ζ hζ]
  simp
  have h_denom := denom_ne_zero ζ hζ
  rcases h_denom with ⟨hd1, hd2⟩
  have h_two_ne : (2 : ℂ) ≠ 0 := by norm_num
  field_simp [hd1, hd2, h_two_ne]
  ring_nf
  have h_sq : ζ ^ 2 = -1 := sq_eq_neg_one_of_isPrimitiveRoot_four ζ hζ
  have h4 : ζ ^ 4 = 1 := by
    calc ζ ^ 4 = (ζ ^ 2) ^ 2 := by ring
    _ = (-1) ^ 2 := by rw [h_sq]
    _ = 1 := by norm_num
  have h6 : ζ ^ 6 = -1 := by
    calc ζ ^ 6 = ζ ^ 4 * ζ ^ 2 := by ring
    _ = 1 * -1 := by rw [h4, h_sq]
    _ = -1 := by norm_num
  have h8 : ζ ^ 8 = 1 := by
    calc ζ ^ 8 = ζ ^ 6 * ζ ^ 2 := by ring
    _ = -1 * -1 := by rw [h6, h_sq]
    _ = 1 := by norm_num
  rw [h_sq, h4, h6, h8]
  norm_num

lemma pow_n_eq_neg_one {n : ℕ} (hn : 1 ≤ n) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * n)) : ζ ^ n = -1 := by
  have h_pow2 : (ζ ^ n) ^ 2 = 1 := by
    calc (ζ ^ n) ^ 2 = ζ ^ (n * 2) := by rw [← pow_mul]
    _ = ζ ^ (2 * n) := by rw [mul_comm n 2]
    _ = 1 := hζ.pow_eq_one
  have h_ne : ζ ^ n ≠ 1 := by
    apply hζ.pow_ne_one_of_pos_of_lt
    · omega
    · omega
  have h_sq : (ζ ^ n) ^ 2 - 1 = 0 := sub_eq_zero.mpr h_pow2
  have h_factor : (ζ ^ n - 1) * (ζ ^ n + 1) = 0 := by
    calc (ζ ^ n - 1) * (ζ ^ n + 1) = (ζ ^ n) ^ 2 - 1 := by ring
    _ = 0 := h_sq
  cases mul_eq_zero.mp h_factor with
  | inl h1 =>
    have : ζ ^ n = 1 := by
      calc ζ ^ n = (ζ ^ n - 1) + 1 := by ring
      _ = 0 + 1 := by rw [h1]
      _ = 1 := by ring
    contradiction
  | inr h2 =>
    calc ζ ^ n = (ζ ^ n + 1) - 1 := by ring
    _ = 0 - 1 := by rw [h2]
    _ = -1 := by ring

/--
Conjecture 1: For any primitive 2n-th root zeta of unity, the permanent of the 2n X 2n matrix [m(j,k)]_{j,k=1..2n} coincides with a(n) = ((2n-1)!!)^2, where m(j,k) is (1+zeta^(j-k))/(1-zeta^(j-k)) if j is not equal to k, and 1 otherwise.
-/
theorem oeis_1818_conjecture_0 (n : ℕ) (h_n : 1 ≤ n) :
    ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ) := by
  intro ζ hζ
  rcases n with _ | n
  · omega
  · rcases n with _ | n
    · exact oeis_1818_conjecture_0_n1 ζ hζ
    · rcases n with _ | n
      · exact oeis_1818_conjecture_0_n2 ζ hζ
      · sorry




