import FormalConjectures.Util.ProblemImports

open BigOperators Matrix Nat

def A005259' (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (n.choose k)^2 * ((Nat.choose (n + k) k))^2

/-- subset-of-subset identity: for k ≤ n,
  C(n,k)*C(n+k,k) = C(n+k,2k)*C(2k,k). -/
lemma choose_prod_id (n k : ℕ) :
    n.choose k * (n + k).choose k = (n + k).choose (2 * k) * (2 * k).choose k := by
  rcases le_or_gt k n with hkn | hkn
  · -- use factorial identity
    have h2k : 2 * k ≤ n + k := by omega
    have hk2k : k ≤ 2 * k := by omega
    -- multiply both sides by k! * k! * (n-k)! and compare to (n+k)!
    -- We prove via the "choose_mul_choose" relation manually.
    have key : ∀ a b c : ℕ, c ≤ b → b ≤ a →
        a.choose b * b.choose c = a.choose c * (a - c).choose (b - c) := by
      intro a b c hcb hba
      have hca : c ≤ a := le_trans hcb hba
      -- compare after multiplying by c! (b-c)! (a-b)!
      have e1 : a.choose b * b.choose c
          * (c.factorial * (b - c).factorial * (a - b).factorial)
          = a.factorial := by
        have hb := Nat.choose_mul_factorial_mul_factorial hba
        have hc := Nat.choose_mul_factorial_mul_factorial hcb
        -- a.choose b * b! * (a-b)! = a! ; b.choose c * c! * (b-c)! = b!
        calc a.choose b * b.choose c * (c.factorial * (b - c).factorial * (a - b).factorial)
            = (a.choose b * (b.choose c * c.factorial * (b-c).factorial)) * (a-b).factorial := by ring
          _ = (a.choose b * b.factorial) * (a-b).factorial := by rw [hc]
          _ = a.choose b * b.factorial * (a-b).factorial := by ring
          _ = a.factorial := by rw [hb]
      have e2 : a.choose c * (a - c).choose (b - c)
          * (c.factorial * (b - c).factorial * (a - b).factorial)
          = a.factorial := by
        have hc := Nat.choose_mul_factorial_mul_factorial hca
        have hbc : b - c ≤ a - c := by omega
        have hd := Nat.choose_mul_factorial_mul_factorial hbc
        have hsub : a - c - (b - c) = a - b := by omega
        calc a.choose c * (a - c).choose (b - c) * (c.factorial * (b - c).factorial * (a - b).factorial)
            = (a.choose c) * ((a-c).choose (b-c) * (b-c).factorial * ((a-c)-(b-c)).factorial) * c.factorial := by
                rw [hsub]; ring
          _ = (a.choose c) * (a-c).factorial * c.factorial := by rw [hd]
          _ = a.choose c * c.factorial * (a-c).factorial := by ring
          _ = a.factorial := by rw [hc]
      have hcomb : a.choose b * b.choose c * (c.factorial * (b - c).factorial * (a - b).factorial)
          = a.choose c * (a - c).choose (b - c) * (c.factorial * (b - c).factorial * (a - b).factorial) := by
        rw [e1, e2]
      exact Nat.eq_of_mul_eq_mul_right (by positivity) hcomb
    have hkey := key (n + k) (2 * k) k (by omega) (by omega)
    rw [hkey]
    have hA : n + k - k = n := by omega
    have hB : 2 * k - k = k := by omega
    rw [hA, hB, mul_comm]
  · -- k > n : both sides are 0
    have h1 : n.choose k = 0 := Nat.choose_eq_zero_of_lt hkn
    have h2 : (n + k).choose (2 * k) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h1, h2]; ring

/-- The central binomial coefficient `(2k).choose k` is even for `k ≥ 1`. -/
lemma central_even {k : ℕ} (hk : 1 ≤ k) : 2 ∣ (2 * k).choose k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hk  -- k = 0 + m + 1
  -- k = m + 1
  have hk' : 0 + m + 1 = m + 1 := by ring
  rw [hk']
  have : (2 * (m + 1)).choose (m + 1) = (2 * m + 1).choose m + (2 * m + 1).choose (m + 1) := by
    have : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
    rw [this, Nat.choose_succ_succ']
  rw [this]
  have hsymm : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m := by
    have := Nat.choose_symm (n := 2 * m + 1) (k := m) (by omega)
    rw [show 2 * m + 1 - m = m + 1 by omega] at this
    exact this
  rw [hsymm]
  exact ⟨(2 * m + 1).choose m, by ring⟩

/-- Apéry numbers are `≡ 1 (mod 4)`. -/
lemma A005259'_mod_four (n : ℕ) : (A005259' n : ZMod 4) = 1 := by
  unfold A005259'
  rw [Nat.cast_sum, Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    -- term ≡ 0 mod 4 for k ≥ 1
    have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hprod := choose_prod_id n k
    have heven : 2 ∣ (2 * k).choose k := central_even hkpos
    -- (n.choose k)^2 * ((n+k).choose k)^2 = (n.choose k * (n+k).choose k)^2
    -- = ((n+k).choose (2k) * (2k).choose k)^2, divisible by 4
    have hdvd : (4 : ℕ) ∣ (n.choose k)^2 * ((n + k).choose k)^2 := by
      have : (n.choose k)^2 * ((n + k).choose k)^2
          = (n.choose k * (n + k).choose k)^2 := by ring
      rw [this, hprod]
      obtain ⟨t, ht⟩ := heven
      rw [ht]
      exact ⟨((n + k).choose (2 * k))^2 * t^2, by ring⟩
    exact (CharP.cast_eq_zero_iff (ZMod 4) 4 _).mpr hdvd
  · intro h; simp at h

/-- Single-step Lucas mod 3. -/
lemma lucas3 (n k : ℕ) :
    (n.choose k : ZMod 3)
      = (Nat.choose (n % 3) (k % 3) : ZMod 3) * (Nat.choose (n / 3) (k / 3) : ZMod 3) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := 3)
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  push_cast at this
  exact this

/-- Per-term 3-section identity (in `ZMod 3`). -/
lemma term_id (r s a b : ℕ) (hr : r < 3) (hs : s < 3) :
    (((3 * a + r).choose (3 * b + s)) ^ 2 * ((3 * a + r + (3 * b + s)).choose (3 * b + s)) ^ 2
        : ZMod 3)
      = ((r.choose s) ^ 2 * ((r + s).choose s) ^ 2 : ZMod 3)
        * ((a.choose b) ^ 2 * ((a + b).choose b) ^ 2 : ZMod 3) := by
  -- mod/div facts
  have m1 : (3 * a + r) % 3 = r := by omega
  have d1 : (3 * a + r) / 3 = a := by omega
  have m2 : (3 * b + s) % 3 = s := by omega
  have d2 : (3 * b + s) / 3 = b := by omega
  have m3 : (3 * a + r + (3 * b + s)) % 3 = (r + s) % 3 := by omega
  have d3 : (3 * a + r + (3 * b + s)) / 3 = (a + b) + (r + s) / 3 := by omega
  have L1 := lucas3 (3 * a + r) (3 * b + s)
  rw [m1, d1, m2, d2] at L1
  have L2 := lucas3 (3 * a + r + (3 * b + s)) (3 * b + s)
  rw [m3, d3, m2, d2] at L2
  push_cast
  rw [L1, L2]
  by_cases h : r + s < 3
  · have e1 : (r + s) % 3 = r + s := by omega
    have e2 : (r + s) / 3 = 0 := by omega
    rw [e1, e2, add_zero]
    ring
  · -- r + s ≥ 3 : both sides vanish
    have hz1 : ((r + s) % 3).choose s = 0 := by
      apply Nat.choose_eq_zero_of_lt; omega
    rw [hz1]
    have hz2 : ((r + s).choose s : ZMod 3) = 0 := by
      interval_cases r <;> interval_cases s <;> simp_all <;> decide
    rw [hz2]
    push_cast
    ring

/-- The 3-section recurrence for Apéry numbers mod 3. -/
lemma A_three_section (a r : ℕ) (hr : r < 3) :
    (A005259' (3 * a + r) : ZMod 3) = (-1) ^ r * (A005259' a : ZMod 3) := by
  -- abbreviations
  set n := 3 * a + r with hn
  -- Step 1: write the cast sum and extend the range to range (3*(a+1)).
  have hcast : (A005259' n : ZMod 3)
      = ∑ k ∈ Finset.range (n + 1),
          (((n.choose k) ^ 2 * ((n + k).choose k) ^ 2 : ℕ) : ZMod 3) := by
    unfold A005259'; push_cast [Nat.cast_sum]; rfl
  rw [hcast]
  have hextend : ∑ k ∈ Finset.range (n + 1),
          (((n.choose k) ^ 2 * ((n + k).choose k) ^ 2 : ℕ) : ZMod 3)
      = ∑ k ∈ Finset.range (3 * (a + 1)),
          (((n.choose k) ^ 2 * ((n + k).choose k) ^ 2 : ℕ) : ZMod 3) := by
    apply Finset.sum_subset
    · intro x hx; simp only [Finset.mem_range] at *; omega
    · intro x hx hx2; simp only [Finset.mem_range] at hx hx2
      have : n.choose x = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [this]; simp
  rw [hextend]
  -- Step 2: reindex k = 3*b + s
  rw [show 3 * (a + 1) = 3 * (a + 1) from rfl]
  have hreindex : ∑ k ∈ Finset.range (3 * (a + 1)),
        (((n.choose k) ^ 2 * ((n + k).choose k) ^ 2 : ℕ) : ZMod 3)
      = ∑ b ∈ Finset.range (a + 1), ∑ s ∈ Finset.range 3,
          (((n.choose (3 * b + s)) ^ 2 * ((n + (3 * b + s)).choose (3 * b + s)) ^ 2 : ℕ)
            : ZMod 3) := by
    rw [← Finset.sum_product']
    apply Finset.sum_nbij' (fun k => (k / 3, k % 3)) (fun p => 3 * p.1 + p.2)
    · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_product, Finset.mem_range]
      omega
    · intro p hp; simp only [Finset.mem_product, Finset.mem_range] at hp
      simp only [Finset.mem_range]; omega
    · intro k hk; simp only [Finset.mem_range] at hk; omega
    · intro p hp; simp only [Finset.mem_product, Finset.mem_range] at hp; ext <;> simp <;> omega
    · intro k hk; simp only [Finset.mem_range] at hk; dsimp only
      have h : 3 * (k / 3) + k % 3 = k := by omega
      rw [h]
  rw [hreindex]
  -- Step 3: apply term_id and factor
  have hterm : ∀ b ∈ Finset.range (a + 1), ∀ s ∈ Finset.range 3,
      (((n.choose (3 * b + s)) ^ 2 * ((n + (3 * b + s)).choose (3 * b + s)) ^ 2 : ℕ) : ZMod 3)
        = (((r.choose s) ^ 2 * ((r + s).choose s) ^ 2 : ℕ) : ZMod 3)
          * (((a.choose b) ^ 2 * ((a + b).choose b) ^ 2 : ℕ) : ZMod 3) := by
    intro b _ s hs; simp only [Finset.mem_range] at hs
    have ht := term_id r s a b hr hs
    rw [hn]
    push_cast at ht ⊢
    convert ht using 2
  rw [Finset.sum_congr rfl (fun b hb => Finset.sum_congr rfl (fun s hs => hterm b hb s hs))]
  -- now ∑_b ∑_s sp(s) * ap(b) = (∑_s sp(s)) * (∑_b ap(b))
  have hfac : ∑ b ∈ Finset.range (a + 1), ∑ s ∈ Finset.range 3,
        (((r.choose s) ^ 2 * ((r + s).choose s) ^ 2 : ℕ) : ZMod 3)
          * (((a.choose b) ^ 2 * ((a + b).choose b) ^ 2 : ℕ) : ZMod 3)
      = (∑ s ∈ Finset.range 3, (((r.choose s) ^ 2 * ((r + s).choose s) ^ 2 : ℕ) : ZMod 3))
        * (∑ b ∈ Finset.range (a + 1), (((a.choose b) ^ 2 * ((a + b).choose b) ^ 2 : ℕ) : ZMod 3)) := by
    symm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_mul]
  rw [hfac]
  -- s-sum = (-1)^r
  have hssum : (∑ s ∈ Finset.range 3, (((r.choose s) ^ 2 * ((r + s).choose s) ^ 2 : ℕ) : ZMod 3))
      = (-1) ^ r := by
    interval_cases r <;> decide
  -- b-sum = A005259' a
  have hbsum : (∑ b ∈ Finset.range (a + 1),
        (((a.choose b) ^ 2 * ((a + b).choose b) ^ 2 : ℕ) : ZMod 3))
      = (A005259' a : ZMod 3) := by
    unfold A005259'; push_cast [Nat.cast_sum]; rfl
  rw [hssum, hbsum]

/-- **Column-reduction determinant divisibility.**
If every column `j ≠ 0` of an integer matrix is, modulo `p`, a fixed multiple `ε j` of column `0`,
then `p^N` divides the determinant of the `(N+1)×(N+1)` matrix. -/
lemma pow_dvd_det_of_col_cong {N : ℕ} (p : ℤ) (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℤ)
    (ε : Fin (N + 1) → ℤ)
    (hdvd : ∀ i j, j ≠ 0 → p ∣ (M i j - ε j * M i 0)) :
    p ^ N ∣ M.det := by
  classical
  set E : Matrix (Fin (N + 1)) (Fin (N + 1)) ℤ := fun k j =>
    (if k = j then 1 else 0) + (if k = 0 ∧ j ≠ 0 then -ε j else 0) with hEdef
  set D : Matrix (Fin (N + 1)) (Fin (N + 1)) ℤ :=
    Matrix.diagonal (fun j => if j = 0 then 1 else p) with hDdef
  set M'' : Matrix (Fin (N + 1)) (Fin (N + 1)) ℤ := fun i j =>
    if j = 0 then M i 0 else (M i j - ε j * M i 0) / p with hM''def
  -- det E = 1
  have hE : E.det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · apply Finset.prod_eq_one
      intro i _
      simp [hEdef]
    · intro i j hji
      simp only [hEdef]
      have hij : i ≠ j := by
        intro h; rw [h] at hji; exact lt_irrefl _ hji
      have hi0 : ¬ (i = 0 ∧ j ≠ 0) := by
        rintro ⟨hi, _⟩
        rw [hi] at hji
        exact (Fin.not_lt_zero j) hji
      rw [if_neg hij, if_neg hi0]; ring
  -- M * E = M'' * D
  have hME : M * E = M'' * D := by
    ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    -- RHS: ∑ M'' i k * D k j = M'' i j * (if j=0 then 1 else p)
    have hRHS : ∑ k, M'' i k * D k j = M'' i j * (if j = 0 then 1 else p) := by
      rw [Finset.sum_eq_single j]
      · simp [hDdef, Matrix.diagonal]
      · intro k _ hkj
        simp [hDdef, Matrix.diagonal, hkj]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hRHS]
    -- LHS: ∑ M i k * E k j
    have hLHS : ∑ k, M i k * E k j
        = M i j + (if j = 0 then 0 else -(ε j) * M i 0) := by
      simp only [hEdef, mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      · -- ∑ M i k * (if k=j then 1 else 0) = M i j
        rw [Finset.sum_eq_single j] <;> simp_all
      · -- ∑ M i k * (if k=0∧j≠0 then -ε j else 0)
        by_cases hj : j = 0
        · simp [hj]
        · rw [Finset.sum_eq_single (0 : Fin (N + 1))]
          · simp [hj]; ring
          · intro k _ hk; simp [hk]
          · intro h; exact absurd (Finset.mem_univ _) h
    rw [hLHS]
    by_cases hj : j = 0
    · simp [hM''def, hj]
    · simp only [hM''def, hj, if_neg hj, if_false]
      rw [Int.ediv_mul_cancel (hdvd i j hj)]
      ring
  -- det D = p^N
  have hD : D.det = p ^ N := by
    rw [hDdef, Matrix.det_diagonal,
        ← Finset.prod_erase_mul Finset.univ (fun j => if j = 0 then (1:ℤ) else p)
          (Finset.mem_univ (0 : Fin (N + 1)))]
    have h0 : (if (0 : Fin (N+1)) = 0 then (1:ℤ) else p) = 1 := by simp
    rw [h0, mul_one, Finset.prod_congr rfl (g := fun _ => p)]
    · rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin]
      simp
    · intro i hi
      simp only [Finset.mem_erase] at hi
      rw [if_neg hi.1]
  -- combine
  have hkey : M.det = M''.det * p ^ N := by
    have : M.det * E.det = M''.det * D.det := by
      rw [← Matrix.det_mul, ← Matrix.det_mul, hME]
    rw [hE, mul_one, hD] at this
    exact this
  rw [hkey]
  exact Dvd.intro_left _ rfl

/-- The Hankel-type sequence A228143 (matching `Spec.a`). -/
noncomputable def a (n : ℕ) : ℕ :=
  (Matrix.of (fun i j : Fin (n + 1) => (A005259' (i.val + j.val) : ℤ))).det.natAbs

/-- Apéry numbers satisfy `A_n ≡ (-1)^n (mod 3)`. -/
lemma A005259'_mod_three (n : ℕ) : (A005259' n : ZMod 3) = (-1) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; decide
    · obtain ⟨a, r, hr, rfl⟩ : ∃ a r, r < 3 ∧ n = 3 * a + r :=
        ⟨n / 3, n % 3, by omega, by omega⟩
      rw [A_three_section a r hr]
      have ha : a < 3 * a + r := by omega
      rw [ih a ha, ← pow_add]
      conv_rhs => rw [show 3 * a + r = (r + a) + 2 * a by ring, pow_add, pow_mul]
      norm_num

/-- `3^n` divides `a n`. -/
lemma three_pow_dvd_a (n : ℕ) : (3 : ℕ) ^ n ∣ a n := by
  set M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
    Matrix.of (fun i j => (A005259' (i.val + j.val) : ℤ)) with hM
  have hdet : (3 : ℤ) ^ n ∣ M.det := by
    apply pow_dvd_det_of_col_cong 3 M (fun j => (-1) ^ (j.val))
    intro i j _
    have hz : ((M i j - (-1) ^ (j.val) * M i 0 : ℤ) : ZMod 3) = 0 := by
      push_cast [hM, Matrix.of_apply]
      rw [A005259'_mod_three, A005259'_mod_three]
      simp only [Fin.val_zero, add_zero]
      rw [show i.val + j.val = j.val + i.val by ring, pow_add]
      ring
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hz
    exact_mod_cast this
  have : ((3 : ℕ) ^ n : ℤ) ∣ M.det := by exact_mod_cast hdet
  rw [a, ← hM]
  rw [← Int.natAbs_dvd_natAbs] at this
  simpa using this

/-- `4^n` divides `a n`. -/
lemma four_pow_dvd_a (n : ℕ) : (4 : ℕ) ^ n ∣ a n := by
  set M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
    Matrix.of (fun i j => (A005259' (i.val + j.val) : ℤ)) with hM
  have hdet : (4 : ℤ) ^ n ∣ M.det := by
    apply pow_dvd_det_of_col_cong 4 M (fun _ => 1)
    intro i j _
    have hz : ((M i j - 1 * M i 0 : ℤ) : ZMod 4) = 0 := by
      push_cast [hM, Matrix.of_apply]
      have h1 : (A005259' (i.val + j.val) : ZMod 4) = 1 := A005259'_mod_four _
      have h2 : (A005259' (i.val + (0:Fin (n+1)).val) : ZMod 4) = 1 := A005259'_mod_four _
      simp only [Fin.val_zero, add_zero] at h2 ⊢
      rw [h1, h2]; ring
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp hz
    exact_mod_cast this
  have : ((4 : ℕ) ^ n : ℤ) ∣ M.det := by exact_mod_cast hdet
  rw [a, ← hM]
  rw [← Int.natAbs_dvd_natAbs] at this
  simpa using this

