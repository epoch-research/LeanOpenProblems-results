import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 800000


open Nat Finset Matrix

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

lemma poch_ne_zero_of_pos (a : ℚ) (ha : 0 < a) (n : ℕ) : poch a n ≠ 0 := by
  induction n with
  | zero => simp [poch]
  | succ n ih =>
      rw [poch_succ]
      exact mul_ne_zero ih (ne_of_gt (by positivity : 0 < a + (n:ℚ)))

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
