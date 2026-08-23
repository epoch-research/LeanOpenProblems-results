import FormalConjectures.Util.ProblemImports

open Real

/--
A190363: $a(n) = n + \lfloor n \cdot r/t \rfloor + \lfloor n \cdot s/t \rfloor$; $r=1, s=\sqrt{5/4}, t=\sqrt{4/5}$.
The equivalent formula used in implementations is $a(n) = 2n + \lfloor n \cdot \sqrt{5/4} \rfloor + \lfloor n/4 \rfloor$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let n_R : ℝ := n
  let sqrt_expr : ℝ := sqrt (5 / 4)

  -- $\lfloor n \cdot \sqrt{5/4} \rfloor$
  let floor_term_sqrt : ℕ := (Int.floor (n_R * sqrt_expr)).toNat

  -- $\lfloor n/4 \rfloor$ (Natural number division is floor division)
  let floor_term_div : ℕ := n / 4

  2 * n + floor_term_sqrt + floor_term_div

open scoped BigOperators

/-- The set of coefficients $\tilde{c}_i$ for the linear recurrence relation of order 21.
The recurrence is $u(n+21) = \sum_{i=0}^{20} \tilde{c}_i u(n+i)$.
This corresponds to $a(n+21) = a(n+17) + a(n+4) - a(n)$.
The coefficients are $\tilde{c}_0 = -1, \tilde{c}_4 = 1, \tilde{c}_{17} = 1$, and 0 otherwise.
-/
noncomputable def A190363_coeffs : Fin 21 → ℤ :=
  fun i =>
    match i.val with
    | 0 => -1 -- coefficient for a(n)
    | 4 => 1  -- coefficient for a(n+4)
    | 17 => 1 -- coefficient for a(n+17)
    | _ => 0

/-- The linear recurrence structure for A190363 defined over $\mathbb{Z}$. -/
noncomputable def A190363_LR : LinearRecurrence ℤ :=
  LinearRecurrence.mk 21 A190363_coeffs

lemma A190363_coeffs_of_val (i : Fin 21) :
    A190363_coeffs i =
      if i.val = 0 then (-1 : ℤ)
      else if i.val = 4 then 1
      else if i.val = 17 then 1
      else 0 := by
  fin_cases i <;> decide

lemma A190363_coeffs_zero_of_notMem {i : Fin 21}
    (hi : i ∉ ({⟨0, by decide⟩, ⟨4, by decide⟩, ⟨17, by decide⟩} : Finset (Fin 21))) :
    A190363_coeffs i = 0 := by
  rw [A190363_coeffs_of_val]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  rcases hi with ⟨h0, h4, h17⟩
  have h0' : i.val ≠ 0 := fun h => h0 (Fin.ext h)
  have h4' : i.val ≠ 4 := fun h => h4 (Fin.ext h)
  have h17' : i.val ≠ 17 := fun h => h17 (Fin.ext h)
  simp [h0', h4', h17']

/-- The characteristic sum of `A190363_LR` reduces to three terms. -/
lemma A190363_sum_coeffs (u : ℕ → ℤ) (n : ℕ) :
    ∑ i : Fin 21, A190363_coeffs i * u (n + i) =
      u (n + 17) + u (n + 4) - u n := by
  set s : Finset (Fin 21) := {⟨0, by decide⟩, ⟨4, by decide⟩, ⟨17, by decide⟩}
  have hsum := Finset.sum_add_sum_compl (s := s)
    (f := fun i : Fin 21 => A190363_coeffs i * u (n + i))
  have hs : ∑ i ∈ s, A190363_coeffs i * u (n + i) =
      u (n + 17) + u (n + 4) - u n := by
    simp [s, Finset.sum_insert, A190363_coeffs_of_val, add_comm, sub_eq_add_neg]
  have hsc : ∑ i ∈ sᶜ, A190363_coeffs i * u (n + i) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    simp [A190363_coeffs_zero_of_notMem (Finset.mem_compl.mp hi)]
  linarith

lemma A190363_isSolution_iff (u : ℕ → ℤ) :
    A190363_LR.IsSolution u ↔ ∀ n, u (n + 21) = u (n + 17) + u (n + 4) - u n := by
  constructor
  · intro h n
    simpa [A190363_LR, A190363_sum_coeffs] using h n
  · intro h n
    simpa [A190363_LR, A190363_sum_coeffs] using h n

/-- `⌊n √(5/4)⌋ = k` follows from the integer comparisons `4k² ≤ 5n² < 4(k+1)²`. -/
lemma floor_mul_sqrt_five_div_four (n k : ℕ)
    (h₁ : 4 * k ^ 2 ≤ 5 * n ^ 2) (h₂ : 5 * n ^ 2 < 4 * (k + 1) ^ 2) :
    Int.floor ((n : ℝ) * sqrt (5 / 4)) = k := by
  have h54 : (0 : ℝ) ≤ 5 / 4 := by positivity
  rw [Int.floor_eq_iff]
  constructor
  · change (k : ℝ) ≤ (n : ℝ) * sqrt (5 / 4)
    refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
    rw [mul_pow, sq_sqrt h54]
    have : (4 * (k : ℝ) ^ 2) ≤ 5 * (n : ℝ) ^ 2 := by exact_mod_cast h₁
    nlinarith
  · change (n : ℝ) * sqrt (5 / 4) < (k : ℝ) + 1
    refine (sq_lt_sq₀ (by positivity) (by positivity)).mp ?_
    rw [mul_pow, sq_sqrt h54]
    have : (5 * (n : ℝ) ^ 2) < 4 * ((k : ℝ) + 1) ^ 2 := by
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; rfl
      have := (Nat.cast_lt (α := ℝ)).mpr h₂
      push_cast at this
      simpa [hcast] using this
    nlinarith

lemma a_eq (n k : ℕ) (hf : Int.floor ((n : ℝ) * sqrt (5 / 4)) = k) :
    a n = 2 * n + k + n / 4 := by
  dsimp [a]
  rw [hf]
  simp

lemma a_140 : a 140 = 471 :=
  a_eq 140 156 (floor_mul_sqrt_five_div_four 140 156 (by norm_num) (by norm_num))

lemma a_144 : a 144 = 484 :=
  a_eq 144 160 (floor_mul_sqrt_five_div_four 144 160 (by norm_num) (by norm_num))

lemma a_157 : a 157 = 528 :=
  a_eq 157 175 (floor_mul_sqrt_five_div_four 157 175 (by norm_num) (by norm_num))

lemma a_161 : a 161 = 542 :=
  a_eq 161 180 (floor_mul_sqrt_five_div_four 161 180 (by norm_num) (by norm_num))

/--
The claimed linear recurrence
`a(n+21) = a(n+17) + a(n+4) - a(n)` (equivalently, `A190363_LR.IsSolution`)
fails already at `n = 140`.
-/
theorem oeis_190363_conjecture_0.disproof :
    ¬ A190363_LR.IsSolution (fun n : ℕ => (a (n + 1) : ℤ)) := by
  rw [A190363_isSolution_iff]
  intro h
  have h139 := h 139
  -- `a 161 = a 157 + a 144 - a 140`, i.e. `542 = 541`.
  simp only [Nat.reduceAdd] at h139
  rw [a_161, a_157, a_144, a_140] at h139
  norm_num at h139
