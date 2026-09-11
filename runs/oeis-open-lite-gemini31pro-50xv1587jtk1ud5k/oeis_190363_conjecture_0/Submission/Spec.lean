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

/--
A190363 Conjecture: linear recurrence with constant coefficients 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1.
This list of coefficients $c_1, \dots, c_{21}$ defines the relation $a(n) = \sum_{i=1}^{21} c_i a(n-i)$,
which when shifted is $a(n+21) = a(n+17) + a(n+4) - a(n)$ for $n \ge 1$.
We formalize this by checking if the sequence indexed from $a(1)$ satisfies the `LinearRecurrence.IsSolution` property over $\mathbb{Z}$.
-/
theorem oeis_190363_conjecture_0 :
  A190363_LR.IsSolution (fun n : ℕ => (a (n + 1) : ℤ)) := by sorry


lemma floor_sqrt_val (n : ℕ) (k : ℤ) (h1 : (k : ℝ)^2 ≤ (n : ℝ)^2 * (5 / 4))
    (h2 : (n : ℝ)^2 * (5 / 4) < (k + 1 : ℝ)^2) (hn : 0 ≤ (n : ℝ)) (hk : 0 ≤ (k : ℝ)) :
  Int.floor ((n : ℝ) * sqrt (5 / 4)) = k := by
  apply Int.floor_eq_iff.mpr
  constructor
  · have h : (k : ℝ) = sqrt ((k : ℝ)^2) := (sqrt_sq hk).symm
    rw [h]
    have h_sqrt : sqrt ((n : ℝ)^2 * (5 / 4)) = (n : ℝ) * sqrt (5 / 4) := by
      rw [sqrt_mul (sq_nonneg _), sqrt_sq hn]
    rw [← h_sqrt]
    exact sqrt_le_sqrt h1
  · have h : (k + 1 : ℝ) = sqrt ((k + 1 : ℝ)^2) := (sqrt_sq (by linarith)).symm
    rw [h]
    have h_sqrt : sqrt ((n : ℝ)^2 * (5 / 4)) = (n : ℝ) * sqrt (5 / 4) := by
      rw [sqrt_mul (sq_nonneg _), sqrt_sq hn]
    rw [← h_sqrt]
    apply sqrt_lt_sqrt (by positivity) h2

lemma a_140 : a 140 = 471 := by
  change 2 * 140 + (Int.floor ((140 : ℝ) * sqrt (5 / 4))).toNat + 140 / 4 = 471
  have h_floor : Int.floor ((140 : ℝ) * sqrt (5 / 4)) = 156 :=
    floor_sqrt_val 140 156 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [h_floor]
  rfl

lemma a_144 : a 144 = 484 := by
  change 2 * 144 + (Int.floor ((144 : ℝ) * sqrt (5 / 4))).toNat + 144 / 4 = 484
  have h_floor : Int.floor ((144 : ℝ) * sqrt (5 / 4)) = 160 :=
    floor_sqrt_val 144 160 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [h_floor]
  rfl

lemma a_157 : a 157 = 528 := by
  change 2 * 157 + (Int.floor ((157 : ℝ) * sqrt (5 / 4))).toNat + 157 / 4 = 528
  have h_floor : Int.floor ((157 : ℝ) * sqrt (5 / 4)) = 175 :=
    floor_sqrt_val 157 175 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [h_floor]
  rfl

lemma a_161 : a 161 = 542 := by
  change 2 * 161 + (Int.floor ((161 : ℝ) * sqrt (5 / 4))).toNat + 161 / 4 = 542
  have h_floor : Int.floor ((161 : ℝ) * sqrt (5 / 4)) = 180 :=
    floor_sqrt_val 161 180 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [h_floor]
  rfl

def A190363_coeffs_nat (i : ℕ) : ℤ :=
    match i with
    | 0 => -1
    | 4 => 1
    | 17 => 1
    | _ => 0

lemma coeffs_eq (i : Fin 21) : A190363_coeffs i = A190363_coeffs_nat (i : ℕ) := by
  unfold A190363_coeffs A190363_coeffs_nat
  rfl

lemma sum_eval : (∑ i : Fin 21, A190363_coeffs i * (a (139 + 1 + (i : ℕ)) : ℤ)) =
  - (a 140 : ℤ) + (a 144 : ℤ) + (a 157 : ℤ) := by
  have : (∑ i : Fin 21, A190363_coeffs i * (a (139 + 1 + (i : ℕ)) : ℤ)) =
    ∑ i : Fin 21, A190363_coeffs_nat (i : ℕ) * (a (139 + 1 + (i : ℕ)) : ℤ) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [coeffs_eq]
  rw [this]
  have h_sum : (∑ i : Fin 21, A190363_coeffs_nat (i : ℕ) * (a (139 + 1 + (i : ℕ)) : ℤ)) =
    ∑ i ∈ Finset.range 21, A190363_coeffs_nat i * (a (139 + 1 + i) : ℤ) :=
    Fin.sum_univ_eq_sum_range (fun i => A190363_coeffs_nat i * (a (139 + 1 + i) : ℤ)) 21
  rw [h_sum]
  simp [Finset.sum_range_succ, add_assoc]
  unfold A190363_coeffs_nat
  simp

theorem oeis_190363_conjecture_0.disproof : ¬ (type_of% @oeis_190363_conjecture_0) := by
  intro h
  have h139 := h 139
  change (a 161 : ℤ) = ∑ i : Fin 21, A190363_coeffs i * (a (139 + 1 + ↑i) : ℤ) at h139
  rw [sum_eval] at h139
  rw [a_140, a_144, a_157, a_161] at h139
  norm_num at h139
