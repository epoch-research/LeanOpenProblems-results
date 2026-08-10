import FormalConjectures.Util.ProblemImports

open BigOperators LinearRecurrence

def A227582_base (n : ℕ) : ℤ :=
  let order := 7
  let coeffs : Fin order → ℤ := ![1, -2, 1, 0, 0, -1, 2]
  let init : Fin order → ℤ := ![2, 7, 14, 23, 35, 50, 67]
  let E : LinearRecurrence ℤ := { order := order, coeffs := coeffs }
  E.mkSol init n

noncomputable def E : LinearRecurrence ℤ := { order := 7, coeffs := ![1, -2, 1, 0, 0, -1, 2] }
noncomputable def init7 : Fin 7 → ℤ := ![2, 7, 14, 23, 35, 50, 67]

example (n : ℕ) : A227582_base n = E.mkSol init7 n := by
  rfl

lemma base_val (j : Fin 7) : A227582_base (j : ℕ) = init7 j := by
  have := E.mkSol_eq_init init7 j
  simpa [A227582_base, E] using this

-- recurrence
lemma base_rec (n : ℕ) : A227582_base (n + 7) =
    A227582_base n - 2 * A227582_base (n+1) + A227582_base (n+2)
      - A227582_base (n+5) + 2 * A227582_base (n+6) := by
  have h2 : E.mkSol init7 (n+7) = ∑ i : Fin 7, E.coeffs i * E.mkSol init7 (n + (i:ℕ)) :=
    E.is_sol_mkSol init7 n
  have e : ∀ k, A227582_base k = E.mkSol init7 k := fun k => rfl
  rw [e (n+7), e n, e (n+1), e (n+2), e (n+5), e (n+6)]
  rw [h2, Fin.sum_univ_seven]
  simp only [E, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Fin.isValue, Fin.val_zero, Fin.val_one, Nat.add_zero]
  norm_num
  ring

/-- The period-5 correction in the closed form `5 * base m = 6 m² + 18 m + cc (m % 5)`. -/
def cc (r : ℕ) : ℤ := if r = 0 then 10 else if r = 1 then 11 else if r = 2 then 10 else 7

lemma bv0 : A227582_base 0 = 2 := by have := base_val ⟨0, by decide⟩; simpa [init7] using this
lemma bv1 : A227582_base 1 = 7 := by have := base_val ⟨1, by decide⟩; simpa [init7] using this
lemma bv2 : A227582_base 2 = 14 := by have := base_val ⟨2, by decide⟩; simpa [init7] using this
lemma bv3 : A227582_base 3 = 23 := by have := base_val ⟨3, by decide⟩; simpa [init7] using this
lemma bv4 : A227582_base 4 = 35 := by have := base_val ⟨4, by decide⟩; simpa [init7] using this
lemma bv5 : A227582_base 5 = 50 := by have := base_val ⟨5, by decide⟩; simpa [init7] using this
lemma bv6 : A227582_base 6 = 67 := by have := base_val ⟨6, by decide⟩; simpa [init7] using this

lemma closed (m : ℕ) : 5 * A227582_base m = 6 * (m : ℤ)^2 + 18 * m + cc (m % 5) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases lt_or_ge m 7 with hm | hm
    · interval_cases m <;>
        simp only [bv0, bv1, bv2, bv3, bv4, bv5, bv6, cc] <;> norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 7 := ⟨m - 7, by omega⟩
      have h0 := ih k (by omega)
      have h1 := ih (k+1) (by omega)
      have h2 := ih (k+2) (by omega)
      have h5 := ih (k+5) (by omega)
      have h6 := ih (k+6) (by omega)
      have e5 : (k+5) % 5 = k % 5 := by omega
      have e6 : (k+6) % 5 = (k+1) % 5 := by omega
      have e7 : (k+7) % 5 = (k+2) % 5 := by omega
      rw [e5] at h5
      rw [e6] at h6
      rw [base_rec k, e7]
      push_cast at h0 h1 h2 h5 h6 ⊢
      linear_combination h0 - 2*h1 + h2 - h5 + 2*h6
