import FormalConjectures.Util.ProblemImports

open Matrix Nat Finset

noncomputable def poch (a : ℚ) : ℕ → ℚ
  | 0 => 1
  | n+1 => poch a n * (a + n)
lemma poch_succ (a : ℚ) (n : ℕ) : poch a (n+1) = poch a n * (a+n) := rfl
lemma poch_succ_left (a : ℚ) (n : ℕ) : poch a (n+1) = a * poch (a+1) n := by
  induction n with
  | zero => simp [poch]
  | succ n ih => rw [poch_succ, ih, poch_succ]; norm_num [Nat.cast_add, Nat.cast_one]; ring_nf
lemma poch_two_left (b : ℚ) (n : ℕ) : poch b (n+2) = b * (b+1) * poch (b+2) n := by
  rw [poch_succ_left b (n+1), poch_succ_left (b+1) n]; ring

lemma entry_id (a b : ℚ) (i j : ℕ)
    (hb0 : b ≠ 0) (hb1 : b + 1 ≠ 0) (hbj : b + j ≠ 0)
    (h1 : poch b (i+j+1) ≠ 0) (h2 : poch b (i+j+2) ≠ 0)
    (h3 : poch (b+2) (i+j) ≠ 0) :
    poch a (i+j+2) / poch b (i+j+2)
      - ((a + j) / (b + j)) * (poch a (i+j+1) / poch b (i+j+1))
    = (i+1 : ℚ) * (b-a) * a / (b*(b+1)*(b+j)) * (poch (a+1) (i+j) / poch (b+2) (i+j)) := by
  rw [poch_succ_left a (i+j+1), poch_succ_left a (i+j), poch_two_left b (i+j)]
  rw [poch_succ (a+1) (i+j)]
  field_simp [hb0,hb1,hbj,h1,h2,h3]
  have hs : poch b (i+j+1) = poch b (i+j) * (b + (i+j : ℕ)) := by rw [poch_succ]
  have hrel : poch (b+2) (i+j) = poch b (i+j) * (b + (i+j : ℕ)) * (b + (i+j : ℕ) + 1) / (b*(b+1)) := by
    have hb4 : poch b (i+j+2) = poch b (i+j) * (b + (i+j : ℕ)) * (b + (i+j : ℕ) + 1) := by
      rw [show i+j+2 = (i+j+1)+1 by omega, poch_succ, poch_succ]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring_nf
      all_goals simp
    have hb5 : poch b (i+j+2) = b*(b+1)*poch (b+2) (i+j) := poch_two_left b (i+j)
    rw [eq_div_iff (mul_ne_zero hb0 hb1)]
    rw [← hb4, hb5]
    ring
  rw [hs, hrel]
  field_simp [hb0,hb1]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring_nf

lemma poch_ne_zero_of_pos (a : ℚ) (ha : 0 < a) (n : ℕ) : poch a n ≠ 0 := by
  induction n with
  | zero => simp [poch]
  | succ n ih =>
      rw [poch_succ]
      exact mul_ne_zero ih (ne_of_gt (by positivity : 0 < a + (n:ℚ)))

noncomputable def H (n : ℕ) (a b : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => poch a (i.val + j.val) / poch b (i.val + j.val)

lemma det_H_succ_pos (n : ℕ) (a b : ℚ) (ha : 0 < a) (hb : 0 < b) :
    (H (n+1) a b).det =
      ((∏ i : Fin n, ((i.val+1 : ℕ) : ℚ) * (b-a) * a / (b*(b+1))) *
       (∏ j : Fin n, (b + (j.val:ℚ))⁻¹)) * (H n (a+1) (b+2)).det := by
  classical
  let A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ := H (n+1) a b
  let c : Fin n → ℚ := fun j => (a + (j.val:ℚ)) / (b + (j.val:ℚ))
  let B : Matrix (Fin (n+1)) (Fin (n+1)) ℚ := fun i j =>
    Fin.cases (A i 0) (fun j : Fin n => A i j.succ - c j * A i (Fin.castSucc j)) j
  have hdetAB : A.det = B.det := by
    exact Matrix.det_eq_of_forall_col_eq_smul_add_pred (A := A) (B := B) c
      (by intro i; simp [B])
      (by intro i j; simp [B, c, sub_eq_add_neg, add_comm, add_left_comm])
  have hrow0 : ∀ j : Fin n, B 0 j.succ = 0 := by
    intro j
    have hbjnz : b + (j.val:ℚ) ≠ 0 := ne_of_gt (by positivity : 0 < b + (j.val:ℚ))
    simp [B, A, H, c]
    rw [poch_succ a j.val, poch_succ b j.val]
    have hpb : poch b j.val ≠ 0 := poch_ne_zero_of_pos b hb j.val
    field_simp [hbjnz, hpb]
    ring
  have hdetB : B.det = (B.submatrix Fin.succ Fin.succ).det := by
    rw [Matrix.det_succ_row_zero]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.zero_succAbove]
    have hB00 : B 0 0 = 1 := by simp [B, A, H, poch]
    rw [hB00, one_mul]
    apply add_eq_left.mpr
    apply Finset.sum_eq_zero
    intro x hx
    rw [hrow0 x]
    simp
  have hblock : B.submatrix Fin.succ Fin.succ =
      Matrix.of (fun i j : Fin n => (((i.val+1 : ℕ):ℚ) * (b-a) * a / (b*(b+1))) *
        ((b + (j.val:ℚ))⁻¹) * (H n (a+1) (b+2) i j)) := by
    ext i j
    have hb0 : b ≠ 0 := ne_of_gt hb
    have hb1 : b + 1 ≠ 0 := ne_of_gt (by positivity : 0 < b + 1)
    have hbj : b + (j.val:ℚ) ≠ 0 := ne_of_gt (by positivity : 0 < b + (j.val:ℚ))
    have h1 : poch b (i.val+j.val+1) ≠ 0 := poch_ne_zero_of_pos b hb _
    have h2 : poch b (i.val+j.val+2) ≠ 0 := poch_ne_zero_of_pos b hb _
    have h3 : poch (b+2) (i.val+j.val) ≠ 0 := poch_ne_zero_of_pos (b+2) (by positivity) _
    simp [B, A, H, c, Fin.val_succ, Fin.val_castSucc]
    rw [show i.val + 1 + (j.val + 1) = i.val + j.val + 2 by omega]
    rw [show i.val + 1 + j.val = i.val + j.val + 1 by omega]
    rw [entry_id a b i.val j.val hb0 hb1 hbj h1 h2 h3]
    field_simp [hb0, hb1, hbj]
  rw [show (H (n+1) a b).det = A.det by rfl, hdetAB, hdetB, hblock]
  let ci : Fin n → ℚ := fun i => ((i.val+1 : ℕ):ℚ) * (b-a) * a / (b*(b+1))
  let dj : Fin n → ℚ := fun j => (b + (j.val:ℚ))⁻¹
  let M : Matrix (Fin n) (Fin n) ℚ := H n (a+1) (b+2)
  have hscale : (Matrix.of fun i j : Fin n => ci i * dj j * M i j).det =
      (∏ i, ci i) * (∏ j, dj j) * M.det := by
    calc
      (Matrix.of fun i j : Fin n => ci i * dj j * M i j).det
          = (Matrix.of fun i j : Fin n => ci i * (Matrix.of fun i j : Fin n => dj j * M i j) i j).det := by
            congr
            ext i j
            simp
            ring
      _ = (∏ i, ci i) * (Matrix.of fun i j : Fin n => dj j * M i j).det := by rw [Matrix.det_mul_column]
      _ = (∏ i, ci i) * ((∏ j, dj j) * M.det) := by rw [Matrix.det_mul_row]
      _ = (∏ i, ci i) * (∏ j, dj j) * M.det := by ring
  convert hscale using 1 <;> simp [ci, dj, M] <;> ring
