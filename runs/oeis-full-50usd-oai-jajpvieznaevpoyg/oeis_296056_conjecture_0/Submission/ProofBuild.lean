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
set_option maxHeartbeats 800000
lemma poch_eq_prod_range (a : ℚ) (n : ℕ) : poch a n = ∏ k ∈ range n, (a + (k:ℚ)) := by
  induction n with
  | zero => simp [poch]
  | succ n ih =>
      rw [poch_succ, ih]
      rw [prod_range_succ]

lemma factorial_cast_eq_prod_range (n : ℕ) : ((n ! : ℕ) : ℚ) = ∏ k ∈ range n, (((k+1:ℕ):ℚ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.factorial_succ, Nat.cast_mul, ih]
      rw [prod_range_succ]
      ring

lemma poch_neg_half_ne_zero (r n : ℕ) : poch ((r:ℚ) - 3/2) n ≠ 0 := by
  induction n with
  | zero => simp [poch]
  | succ n ih =>
      rw [poch_succ]
      apply mul_ne_zero ih
      have h : ((r:ℚ) - 3/2 + (n:ℚ)) = (((2*(r+n) : ℕ) : ℚ) - 3) / 2 := by
        norm_num [Nat.cast_add, Nat.cast_mul]
        ring
      rw [h]
      intro hz
      have hz' : (((2*(r+n) : ℕ) : ℚ) - 3 : ℚ) = 0 := by
        nlinarith
      have h2 : ((2*(r+n) : ℕ) : ℚ) = (3:ℚ) := by linarith
      have hnat : 2 * (r+n) = 3 := by exact_mod_cast h2
      omega

noncomputable def aa (r : ℕ) : ℚ := (2:ℚ) + r
noncomputable def bb (r : ℕ) : ℚ := (1:ℚ)/2 + 2*r
noncomputable def cc (r : ℕ) : ℚ := bb r - aa r

noncomputable def term (n r x : ℕ) : ℚ :=
  (((x ! : ℕ) : ℚ) * poch (aa r) x * poch (cc r) x /
    poch (bb r) (n+x-1))

noncomputable def ff (r x : ℕ) : ℚ :=
  (((x+1:ℕ):ℚ) * cc r * aa r / (bb r * (bb r + 1))) * ((bb r + (x:ℚ))⁻¹)

noncomputable def corr (n r x : ℕ) : ℚ :=
  (((x+1:ℕ):ℚ) * (aa r + x) * (cc r + x)) /
    ((bb r + x) * (bb r + (n:ℚ) + x))

noncomputable def HD (n r : ℕ) : ℚ := ∏ j ∈ range n, term n r j
noncomputable def Ffac (n r : ℕ) : ℚ := ∏ i ∈ range n, ff r i

lemma aa_succ (r : ℕ) : aa (r+1) = aa r + 1 := by simp [aa]; ring
lemma bb_succ (r : ℕ) : bb (r+1) = bb r + 2 := by simp [bb]; ring
lemma cc_succ (r : ℕ) : cc (r+1) = cc r + 1 := by simp [cc, aa, bb]; ring

lemma bb_pos (r : ℕ) : 0 < bb r := by simp [bb]; positivity
lemma aa_pos (r : ℕ) : 0 < aa r := by simp [aa]; positivity
lemma bb_ne_zero (r : ℕ) : bb r ≠ 0 := ne_of_gt (bb_pos r)
lemma bb_add_one_ne_zero (r : ℕ) : bb r + 1 ≠ 0 := ne_of_gt (by have := bb_pos r; positivity)
lemma bb_add_nat_ne_zero (r x : ℕ) : bb r + (x:ℚ) ≠ 0 := ne_of_gt (by have := bb_pos r; positivity)
lemma aa_add_nat_ne_zero (r x : ℕ) : aa r + (x:ℚ) ≠ 0 := ne_of_gt (by have := aa_pos r; positivity)
lemma cc_add_nat_ne_zero (r x : ℕ) : cc r + (x:ℚ) ≠ 0 := by
  simp [cc, aa, bb]
  intro h
  have hq : (2:ℚ) * (r + x) = 3 := by
    norm_num [Nat.cast_add, Nat.cast_mul] at h
    nlinarith
  have hnat : 2 * (r+x) = 3 := by exact_mod_cast hq
  omega

lemma poch_shift1_ratio (a : ℚ) (x : ℕ) (ha : a ≠ 0) (hp : poch a x ≠ 0) :
    poch (a+1) x / poch a x = (a + x) / a := by
  have hleft := poch_succ_left a x
  have hsucc : poch a (x+1) = poch a x * (a+x) := poch_succ a x
  rw [hsucc] at hleft
  field_simp [hp, ha]
  nlinarith [hleft]

lemma poch_shift2_ratio (b : ℚ) (m : ℕ) (hb : b ≠ 0) (hb1 : b+1 ≠ 0) (hpb : poch b (m+1) ≠ 0) :
    poch (b+2) m / poch b (m+1) = (b + (m:ℚ) + 1) / (b*(b+1)) := by
  have htwo := poch_two_left b m
  have hs : poch b (m+2) = poch b (m+1) * (b + (m+1:ℕ)) := poch_succ b (m+1)
  rw [hs] at htwo
  field_simp [hb, hb1, hpb]
  norm_num [Nat.cast_add, Nat.cast_one] at htwo ⊢
  nlinarith [htwo]

lemma term_factor (n r x : ℕ) (hx : x ∈ range n) :
    ff r x * term n (r+1) x = term (n+1) r x * corr n r x := by
  have hxn : x < n := mem_range.mp hx
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le x) hxn
  have hm : n + x - 1 + 1 = n + x := by omega
  have hidx : n + 1 + x - 1 = n + x := by omega
  have hb0 := bb_ne_zero r
  have hb1 := bb_add_one_ne_zero r
  have hpb : poch (bb r) ((n+x-1)+1) ≠ 0 := by
    rw [hm]
    exact poch_ne_zero_of_pos (bb r) (bb_pos r) (n+x)
  have hpb2 : poch (bb r) (n + x) ≠ 0 := poch_ne_zero_of_pos (bb r) (bb_pos r) _
  have hdenR : poch (bb (r+1)) (n+x-1) ≠ 0 := by
    exact poch_ne_zero_of_pos (bb (r+1)) (bb_pos (r+1)) _
  simp only [term, ff, corr, aa_succ, bb_succ, cc_succ]
  rw [hidx]
  rw [show bb r + 2 = bb r + 2 by rfl]
  have hs2 := poch_shift2_ratio (bb r) (n+x-1) hb0 hb1 hpb
  rw [hm] at hs2
  have haP : poch (aa r) x ≠ 0 := poch_ne_zero_of_pos (aa r) (aa_pos r) x
  have hcP : poch (cc r) x ≠ 0 := by
    have hcc : cc r = (r:ℚ) - 3/2 := by simp [cc, aa, bb]; ring
    rw [hcc]
    exact poch_neg_half_ne_zero r x
  have hc0 : cc r ≠ 0 := by simpa using cc_add_nat_ne_zero r 0
  have haR := poch_shift1_ratio (aa r) x (ne_of_gt (aa_pos r)) haP
  have hcR := poch_shift1_ratio (cc r) x hc0 hcP
  field_simp [hpb2, hdenR, bb_add_nat_ne_zero r x, aa_add_nat_ne_zero r x, cc_add_nat_ne_zero r x,
    bb_ne_zero r, bb_add_one_ne_zero r]
  have ha0 : aa r ≠ 0 := ne_of_gt (aa_pos r)
  have haEq : poch (aa r + 1) x = poch (aa r) x * (aa r + x) / aa r := by
    have t := haR
    field_simp [haP, ha0] at t
    rw [eq_div_iff ha0]
    nlinarith [t]
  have hcEq : poch (cc r + 1) x = poch (cc r) x * (cc r + x) / cc r := by
    have t := hcR
    field_simp [hcP, hc0] at t
    rw [eq_div_iff hc0]
    nlinarith [t]
  have hbnx : bb r + (n:ℚ) + x ≠ 0 := ne_of_gt (by have := bb_pos r; positivity)
  have hdenR' : poch (bb r + 2) (n + x - 1) ≠ 0 := by simpa [bb_succ] using hdenR
  have hdenR'' : poch (2 + bb r) (n + x - 1) ≠ 0 := by
    convert hdenR' using 2
    ring

  have hcastm : ((n+x-1:ℕ):ℚ) + 1 = (n:ℚ) + x := by exact_mod_cast hm
  have hcastm2 : bb r + ((n+x-1:ℕ):ℚ) + 1 = bb r + (n:ℚ) + x := by nlinarith [hcastm]
  have hbEq : poch (bb r) (n + x) / poch (bb r + 2) (n + x - 1)
      = (bb r * (bb r + 1)) / (bb r + (n:ℚ) + x) := by
    have t := hs2
    rw [hcastm2] at t
    field_simp [hpb2, hdenR, hdenR', hdenR'', hb0, hb1, hbnx, mul_ne_zero hb0 hb1] at t ⊢
    ring_nf at t ⊢
    nlinarith [t]
  have hbMul : poch (bb r) (n + x) * (bb r + (n:ℚ) + x)
      = (bb r * (bb r + 1)) * poch (bb r + 2) (n + x - 1) := by
    have t := hbEq
    field_simp [hdenR, hdenR', hdenR'', hbnx] at t
    ring_nf at t ⊢
    nlinarith [t]
  rw [haEq, hcEq]
  field_simp [hb0, hb1, hbnx, ha0, hc0, hdenR, hdenR', hdenR'']
  linear_combination ((aa r + (x:ℚ)) * (cc r + (x:ℚ))) * hbMul

lemma corr_prod_eq_final (n r : ℕ) :
    (∏ x ∈ range n, corr n r x) = term (n+1) r n := by
  unfold corr term
  rw [prod_div_distrib]
  rw [prod_mul_distrib, prod_mul_distrib, prod_mul_distrib]
  rw [← factorial_cast_eq_prod_range n]
  rw [← poch_eq_prod_range (aa r) n]
  rw [← poch_eq_prod_range (cc r) n]
  have htail : (∏ x ∈ range n, (bb r + (n:ℚ) + (x:ℚ))) = ∏ x ∈ range n, (bb r + ((n+x:ℕ):ℚ)) := by
    apply prod_congr rfl
    intro x hx
    norm_num [Nat.cast_add]
    ring
  rw [htail]

  rw [← Finset.prod_range_add (fun x => bb r + (x:ℚ)) n n]
  rw [← poch_eq_prod_range (bb r) (n+n)]
  have hidx : n + 1 + n - 1 = n + n := by omega
  rw [hidx]

lemma HD_step (n r : ℕ) : HD (n+1) r = Ffac n r * HD n (r+1) := by
  unfold HD Ffac
  rw [prod_range_succ]
  rw [← corr_prod_eq_final n r]
  rw [← prod_mul_distrib]
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro x hx
  exact (term_factor n r x hx).symm

lemma det_H_closed (n r : ℕ) : (H n (aa r) (bb r)).det = HD n r := by
  induction n generalizing r with
  | zero => simp [H, HD]
  | succ n ih =>
      rw [det_H_succ_pos n (aa r) (bb r) (aa_pos r) (bb_pos r)]
      rw [← aa_succ r, ← bb_succ r]
      rw [ih (r+1)]
      rw [show (∏ i : Fin n, ↑(i.val + 1) * (bb r - aa r) * aa r / (bb r * (bb r + 1))) =
          ∏ i ∈ range n, ↑(i + 1) * cc r * aa r / (bb r * (bb r + 1)) by
            simpa [cc] using (Fin.prod_univ_eq_prod_range (fun i => (↑(i + 1) : ℚ) * (bb r - aa r) * aa r / (bb r * (bb r + 1))) n)]
      rw [show (∏ j : Fin n, (bb r + ↑j.val)⁻¹) = ∏ j ∈ range n, (bb r + ↑j)⁻¹ by
            simpa using (Fin.prod_univ_eq_prod_range (fun j => (bb r + (j:ℚ))⁻¹) n)]
      rw [show ((∏ i ∈ range n, ↑(i + 1) * cc r * aa r / (bb r * (bb r + 1))) * ∏ j ∈ range n, (bb r + ↑j)⁻¹) = Ffac n r by
        unfold Ffac ff
        rw [← prod_mul_distrib]]
      rw [← HD_step n r]

#check det_H_closed

lemma poch_add (a : ℚ) (m k : ℕ) : poch a (m+k) = poch a m * poch (a + (m:ℚ)) k := by
  induction k with
  | zero => simp [poch]
  | succ k ih =>
      rw [Nat.add_succ, poch_succ, ih, poch_succ]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

lemma poch_two_nat (k : ℕ) : poch 2 k = (((k+1)! : ℕ) : ℚ) := by
  induction k with
  | zero => norm_num [poch]
  | succ k ih =>
      rw [poch_succ, ih]
      rw [show (k+1+1)! = (k+2) * (k+1)! by
        rw [show k+1+1 = (k+1)+1 by omega, Nat.factorial_succ]]
      norm_num [Nat.cast_add, Nat.cast_one, Nat.cast_mul]
      ring

lemma poch_half_formula (m : ℕ) :
    poch (1/2) m = ((Nat.factorial (2*m) : ℕ) : ℚ) / (((4:ℚ)^m) * ((Nat.factorial m : ℕ) : ℚ)) := by
  induction m with
  | zero => norm_num [poch]
  | succ m ih =>
      rw [poch_succ, ih]
      have h4 : (4:ℚ) ^ (m+1) = (4:ℚ)^m * 4 := by rw [pow_succ]
      rw [h4]
      rw [show 2*(m+1) = (2*m+2) by omega]
      rw [show Nat.factorial (2*m+2) = (2*m+2)*(2*m+1)*Nat.factorial (2*m) by
        rw [show 2*m+2 = (2*m+1)+1 by omega, Nat.factorial_succ]
        rw [show 2*m+1 = (2*m)+1 by omega, Nat.factorial_succ]
        ring]
      rw [Nat.factorial_succ]
      norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp
      ring

lemma poch_neg_three_half (n : ℕ) (hn : 3 ≤ n) :
    poch (-3/2) (n-1) = (3/4:ℚ) * poch (1/2) (n-3) := by
  have h : n - 1 = (n-3)+2 := by omega
  rw [h]
  rw [show (n-3)+2 = (n-3)+2 by rfl]
  rw [poch_two_left (-3/2) (n-3)]
  norm_num

lemma poch_start_half (n : ℕ) (hn : 3 ≤ n) :
    poch ((n:ℚ) - 3/2) (n-1) = poch (1/2) (2*n-3) / poch (1/2) (n-2) := by
  have hsum : (n-2) + (n-1) = 2*n-3 := by omega
  have hstart : (1/2:ℚ) + ((n-2:ℕ):ℚ) = (n:ℚ) - 3/2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    ring
  have hp : poch (1/2) (n-2) ≠ 0 := poch_ne_zero_of_pos (1/2) (by norm_num) _
  have h := poch_add (1/2) (n-2) (n-1)
  rw [hsum, hstart] at h
  rw [h]
  field_simp [hp]

lemma catalan_cast_formula (m : ℕ) : (catalan m : ℚ) = (Nat.choose (2*m) m : ℚ) / ((m+1:ℕ):ℚ) := by
  have h : ((m+1) * catalan m : ℕ) = Nat.centralBinom m := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using succ_mul_catalan_eq_centralBinom m
  have hc : Nat.centralBinom m = Nat.choose (2*m) m := by rfl
  rw [← hc]
  have hm : (((m+1:ℕ):ℚ) ≠ 0) := by positivity
  have hq : ((m+1:ℕ):ℚ) * (catalan m : ℚ) = (Nat.centralBinom m : ℚ) := by
    norm_num [Nat.cast_mul]
    exact_mod_cast h
  field_simp [hm]
  nlinarith


noncomputable def rawR (n : ℕ) : ℚ :=
  ((4:ℚ)^(2*n-2) * poch (1/2) (2*n-2) * poch ((n:ℚ)-3/2) (n-1)) /
    ((((n-1)! : ℕ) : ℚ) * poch 2 (n-1) * poch (-3/2) (n-1))

noncomputable def Jfac (n : ℕ) : ℚ :=
  (((2*(2*n-5)*Nat.choose (4*n-6) (2*n-4) : ℕ) : ℚ) / (n:ℚ)) *
    (((2*n-3)*(2*n-1) : ℕ) : ℚ) / 3

lemma rawR_eq_catalan_J (n : ℕ) (hn : 3 ≤ n) :
    rawR n = (catalan (2*n-2) : ℚ) * Jfac n := by
  unfold rawR Jfac
  rw [poch_start_half n hn]
  rw [poch_neg_three_half n hn]
  rw [poch_two_nat (n-1)]
  rw [poch_half_formula (2*n-2)]
  rw [poch_half_formula (2*n-3)]
  rw [poch_half_formula (n-2)]
  rw [poch_half_formula (n-3)]
  rw [catalan_cast_formula (2*n-2)]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  have hch1 : 2*n-2 ≤ 2*(2*n-2) := by omega
  have hch2 : 2*n-4 ≤ 4*n-6 := by omega
  rw [Nat.cast_choose (K:=ℚ) hch1]
  rw [Nat.cast_choose (K:=ℚ) hch2]
  field_simp
  ring_nf
  rw [show (n * 2 - 3) * 2 = n * 4 - 6 by omega]
  rw [show (n * 2 - 2) * 2 - (n * 2 - 2) = n * 2 - 2 by omega]
  rw [show n * 4 - 6 - (n * 2 - 4) = n * 2 - 2 by omega]
  rw [show 1 + (n * 2 - 2) = n * 2 - 1 by omega]
  rw [show 1 + (n - 1) = n by omega]
  rw [show (n - 2) * 2 = n * 2 - 4 by omega]
  rw [show (n - 3) * 2 = n * 2 - 6 by omega]
  have hfn2 : Nat.factorial (n-2) = (n-2) * Nat.factorial (n-3) := by
    rw [show n-2 = (n-3)+1 by omega, Nat.factorial_succ]
  have hfn1 : Nat.factorial (n-1) = (n-1) * (n-2) * Nat.factorial (n-3) := by
    rw [show n-1 = (n-2)+1 by omega, Nat.factorial_succ, hfn2]
    ring
  have hfn : Nat.factorial n = n * (n-1) * (n-2) * Nat.factorial (n-3) := by
    calc
      Nat.factorial n = n * Nat.factorial (n-1) := by
        rw [show n = (n-1)+1 by omega, Nat.factorial_succ]
        rw [show n - 1 + 1 - 1 = n - 1 by omega]
      _ = n * ((n-1) * (n-2) * Nat.factorial (n-3)) := by rw [hfn1]
      _ = n * (n-1) * (n-2) * Nat.factorial (n-3) := by ring
  have hf2a : Nat.factorial (n*2-4) = (n*2-4) * (n*2-5) * Nat.factorial (n*2-6) := by
    rw [show n*2-4 = (n*2-5)+1 by omega, Nat.factorial_succ]
    rw [show n*2-5 = (n*2-6)+1 by omega, Nat.factorial_succ]
    ring
  have hf2b : Nat.factorial (n*2-3) = (n*2-3) * (n*2-4) * (n*2-5) * Nat.factorial (n*2-6) := by
    rw [show n*2-3 = (n*2-4)+1 by omega, Nat.factorial_succ, hf2a]
    ring
  have hf2c : Nat.factorial (n*2-2) = (n*2-2) * (n*2-3) * (n*2-4) * (n*2-5) * Nat.factorial (n*2-6) := by
    rw [show n*2-2 = (n*2-3)+1 by omega, Nat.factorial_succ, hf2b]
    ring
  rw [hfn2, hfn1, hfn, hf2a, hf2b, hf2c]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  ring_nf

  have hpowL : (4:ℚ) ^ (n - 2) * 4 ^ (n - 3) * 4 = (4:ℚ) ^ (2*n - 4) := by
    rw [← pow_add]
    rw [← pow_succ]
    congr 1
    omega
  have hpowR : (4:ℚ) ^ (n * 2 - 3) * 2 = 8 * (4:ℚ) ^ (2*n - 4) := by
    rw [show n*2-3 = (2*n-4)+1 by omega, pow_succ]
    ring
  have hpowLr : (4:ℚ) ^ (n - 2) * (4 ^ (n - 3) * 4) = (4:ℚ) ^ (2*n - 4) := by
    rw [← mul_assoc, hpowL]
  repeat rw [mul_assoc]
  rw [hpowLr]
  rw [hpowR]
  have c2n2 : ((n*2-2 : ℕ) : ℚ) = 2*(n:ℚ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n*2), Nat.cast_mul]
    ring
  have c2n4 : ((n*2-4 : ℕ) : ℚ) = 2*(n:ℚ) - 4 := by
    rw [Nat.cast_sub (by omega : 4 ≤ n*2), Nat.cast_mul]
    ring
  have cn1 : ((n-1 : ℕ) : ℚ) = (n:ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have cn2 : ((n-2 : ℕ) : ℚ) = (n:ℚ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    norm_num
  rw [c2n2, c2n4, cn1, cn2]
  ring_nf


noncomputable def Bclosed (n : ℕ) : ℚ := (4:ℚ)^(n*(n-1)) * (HD n 0)⁻¹

lemma HD_successive_zero (n : ℕ) (hn : 3 ≤ n) :
    HD n 0 = HD (n-1) 0 *
      (((((n-1)! : ℕ) : ℚ) * poch 2 (n-1) * poch (-3/2) (n-1)) /
        (poch (1/2) (2*n-2) * poch ((n:ℚ)-3/2) (n-1))) := by
  unfold HD term aa bb cc
  rw [show n = (n-1)+1 by omega]
  rw [prod_range_succ]
  have hprod :
      (∏ x ∈ range (n-1),
        (((x ! : ℕ) : ℚ) * poch (2 + (0:ℚ)) x * poch ((1/2:ℚ) + 2*(0:ℚ) - (2 + (0:ℚ))) x /
          poch ((1/2:ℚ) + 2*(0:ℚ)) (n - 1 + 1 + x - 1)))
      = (∏ x ∈ range (n-1),
        (((x ! : ℕ) : ℚ) * poch (2 + (0:ℚ)) x * poch ((1/2:ℚ) + 2*(0:ℚ) - (2 + (0:ℚ))) x /
          poch ((1/2:ℚ) + 2*(0:ℚ)) (n - 1 + x - 1))) /
          poch ((n:ℚ)-3/2) (n-1) := by
    rw [← poch_eq_prod_range ((n:ℚ)-3/2) (n-1)]
    rw [div_eq_mul_inv, ← prod_inv_distrib, ← prod_mul_distrib]
    apply prod_congr rfl
    intro x hx
    have hxlt : x < n-1 := mem_range.mp hx
    have hidxOld : n - 1 + x - 1 + 1 = n + x - 1 := by omega
    have hidxNew : n - 1 + 1 + x - 1 = n + x - 1 := by omega
    have hcast : (1/2:ℚ) + (n - 1 + x - 1 : ℕ) = (n:ℚ) - 3/2 + (x:ℚ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ n - 1 + x)]
      norm_num [Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ n)]
      ring
    have hpold : poch (1/2) (n - 1 + x - 1) ≠ 0 := poch_ne_zero_of_pos (1/2) (by norm_num) _
    rw [show (1/2:ℚ) + 2 * (0:ℚ) = 1/2 by norm_num]
    rw [show (2:ℚ) + 0 = 2 by norm_num]
    rw [show (1/2:ℚ) - 2 = -3/2 by norm_num]
    rw [hidxNew]
    rw [← hidxOld, poch_succ]
    rw [hcast]
    field_simp [hpold]
    ring
  simp only [aa, bb, cc, Nat.cast_zero, mul_zero, add_zero] at hprod ⊢

  rw [hprod]
  rw [show n - 1 + 1 + (n - 1) - 1 = 2*n-2 by omega]
  norm_num
  ring

lemma HD_ratio_raw (n : ℕ) (hn : 3 ≤ n) : Bclosed n = Bclosed (n-1) * rawR n := by
  unfold Bclosed rawR
  rw [HD_successive_zero n hn]
  have hpow : (4:ℚ) ^ (n * (n - 1)) = (4:ℚ)^((n-1)*(n-2)) * (4:ℚ)^(2*n-2) := by
    rw [← pow_add]
    congr 1
    nlinarith [hn]
  rw [hpow]
  have hden1 : HD (n-1) 0 ≠ 0 := by
    -- follows from the product formula; all factors are nonzero
    unfold HD term aa bb cc
    apply prod_ne_zero_iff.mpr
    intro x hx
    have hxlt : x < n-1 := mem_range.mp hx
    have hf : (((x ! : ℕ) : ℚ) ≠ 0) := by positivity
    have hp2 : poch (2 + (0:ℚ)) x ≠ 0 := by apply poch_ne_zero_of_pos; norm_num
    have hpn : poch ((1/2:ℚ) + 2*(0:ℚ)) (n - 1 + x - 1) ≠ 0 := by apply poch_ne_zero_of_pos; norm_num
    have hneg : poch ((1/2:ℚ) + 2*(0:ℚ) - (2 + (0:ℚ))) x ≠ 0 := by
      have hcc : (1/2:ℚ) + 2*(0:ℚ) - (2 + (0:ℚ)) = (0:ℚ) - 3/2 := by norm_num
      rw [hcc]
      exact poch_neg_half_ne_zero 0 x
    simp only [aa, bb, cc, Nat.cast_zero, mul_zero, add_zero]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hf hp2) hneg) hpn
  have hpstart : poch ((n:ℚ)-3/2) (n-1) ≠ 0 := by
    have hcc : (n:ℚ)-3/2 = ((n:ℚ)-3/2) := rfl
    rw [← hcc]
    apply poch_ne_zero_of_pos
    have hnq : (3:ℚ) ≤ (n:ℚ) := by exact_mod_cast hn
    linarith
  have hphalf : poch (1/2) (2*n-2) ≠ 0 := poch_ne_zero_of_pos (1/2) (by norm_num) _
  have hfact : (((n-1)! : ℕ) : ℚ) * poch 2 (n-1) * poch (-3/2) (n-1) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · positivity
      · apply poch_ne_zero_of_pos; norm_num
    · exact by simpa using poch_neg_three_half n hn ▸ (mul_ne_zero (by norm_num) (poch_ne_zero_of_pos (1/2) (by norm_num) (n-3)))
  rw [show n - 1 - 1 = n - 2 by omega]

  field_simp [hden1, hpstart, hphalf, hfact]
  ring


