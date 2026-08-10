import FormalConjectures.Util.ProblemImports

open BigOperators Matrix Nat Finset PowerSeries

/--
A005259: The auxiliary sequence used for the Hankel matrix, defined as
$$\sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k}^2$$
-/
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

/--
A228143: Determinant of the $(n+1) \times (n+1)$ Hankel-type matrix with $(i,j)$-entry equal to A005259$(i+j)$ for all $i,j = 0,\dots,n$.
The entry function A005259 is taken to be $\sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k}^2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let dim : Type := Fin (n + 1)
  -- Matrix entries are lifted to ℤ for determinant calculation
  let M : Matrix dim dim ℤ :=
    Matrix.of fun i j => (A005259' (i.val + j.val) : ℤ)
  -- The sequence is known to be non-negative integers (nonn).
  M.det.natAbs

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
  have hd2 : ((3 : ℕ) ^ n : ℤ) ∣ M.det := by exact_mod_cast hdet
  show (3 : ℕ) ^ n ∣ M.det.natAbs
  rw [← Int.natAbs_dvd_natAbs] at hd2
  simpa using hd2

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
  have hd2 : ((4 : ℕ) ^ n : ℤ) ∣ M.det := by exact_mod_cast hdet
  show (4 : ℕ) ^ n ∣ M.det.natAbs
  rw [← Int.natAbs_dvd_natAbs] at hd2
  simpa using hd2

lemma A005259'_zero : A005259' 0 = 1 := by decide
lemma A005259'_one : A005259' 1 = 5 := by decide
lemma A005259'_two : A005259' 2 = 73 := by decide

lemma a_zero : a 0 = 1 := by
  show (Matrix.of (fun i j : Fin 1 => (A005259' (i.val + j.val) : ℤ))).det.natAbs = 1
  rw [Matrix.det_fin_one]
  simp [A005259'_zero]

lemma a_one : a 1 = 48 := by
  show (Matrix.of (fun i j : Fin 2 => (A005259' (i.val + j.val) : ℤ))).det.natAbs = 48
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply]
  norm_num [A005259'_zero, A005259'_one, A005259'_two]

lemma sixteen_dvd_a (n : ℕ) (hn : 1 ≤ n) : (16 : ℕ) ∣ a n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · rw [a_one]; norm_num
  · have h4 := four_pow_dvd_a n
    have h16 : (16:ℕ) ∣ 4 ^ n := by
      have : (16:ℕ) = 4^2 := by norm_num
      rw [this]; exact pow_dvd_pow 4 h
    exact dvd_trans h16 h4

/-- The power series $A(x/3) = \sum_{n=0}^\infty \frac{a(n)}{3^n} x^n$ over ℚ. -/
noncomputable def OGF_A_scaled : PowerSeries ℚ :=
  PowerSeries.mk fun n => (a n : ℚ) / (3 ^ n : ℚ)

lemma pn_prod (p : ℕ) [Fact p.Prime] {α} [DecidableEq α] (s : Finset α) (f : α → ℚ) :
    padicNorm p (∏ i ∈ s, f i) = ∏ i ∈ s, padicNorm p (f i) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, padicNorm.mul, ih]

lemma pn18 (i : ℕ) : padicNorm 2 (1/8 - (i:ℚ)) = 8 := by
  have h2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hx : (8:ℚ) * (1/8 - (i:ℚ)) = ((1 - 8 * (i:ℤ) : ℤ) : ℚ) := by push_cast; ring
  have hodd : ¬ (2 ∣ (1 - 8 * (i:ℤ))) := by intro h; omega
  have hn1 : padicNorm 2 (((1 - 8 * (i:ℤ) : ℤ) : ℚ)) = 1 := by
    have hle := padicNorm.of_int (p := 2) (1 - 8 * (i:ℤ))
    have hlt : ¬ padicNorm 2 (((1 - 8 * (i:ℤ) : ℤ) : ℚ)) < 1 := by
      rw [padicNorm.int_lt_one_iff]; exact hodd
    rcases lt_or_eq_of_le hle with h | h
    · exact absurd h hlt
    · exact h
  have h2' : padicNorm 2 ((2:ℕ):ℚ) = (2:ℚ)⁻¹ := padicNorm.padicNorm_p_of_prime
  have h8 : padicNorm 2 (8:ℚ) = 1/8 := by
    rw [show (8:ℚ) = ((2:ℕ):ℚ)*((2:ℕ):ℚ)*((2:ℕ):ℚ) by norm_num, padicNorm.mul, padicNorm.mul, h2']
    norm_num
  have hc := congrArg (padicNorm 2) hx
  rw [padicNorm.mul, h8, hn1] at hc
  linarith

lemma choose_eighth_prod (d : ℕ) :
    (d.factorial : ℚ) * Ring.choose (1/8 : ℚ) d = ∏ i ∈ Finset.range d, (1/8 - (i:ℚ)) := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose (1/8 : ℚ) d
  rw [nsmul_eq_mul] at h
  rw [← h]
  clear h
  induction d with
  | zero => simp
  | succ n ih =>
    rw [descPochhammer_succ_right, Polynomial.smeval_mul, ih, Finset.prod_range_succ]
    congr 1
    simp [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast]

lemma pn_fact_lb (d : ℕ) : (1/2:ℚ)^d ≤ padicNorm 2 ((d.factorial : ℕ) : ℚ) := by
  have h2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hfne : ((d.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero d)
  rw [padicNorm.eq_zpow_of_nonzero hfne]
  have hv : padicValRat 2 ((d.factorial : ℕ):ℚ) = (padicValNat 2 d.factorial : ℤ) := by
    rw [← padicValRat.of_nat]
  rw [hv]
  have hle : padicValNat 2 d.factorial ≤ d := by
    have hh := Nat.factorization_factorial_le_div_pred (p := 2) (by norm_num) d
    rw [Nat.factorization_def _ (by norm_num)] at hh
    simpa using hh
  rw [show (1/2:ℚ) = (2:ℚ)^(-1:ℤ) by norm_num, ← zpow_natCast, ← _root_.zpow_mul]
  apply zpow_le_zpow_right₀ (by norm_num : (1:ℚ) ≤ 2)
  have hcast : (padicValNat 2 d.factorial : ℤ) ≤ (d : ℤ) := by exact_mod_cast hle
  push_cast
  linarith

lemma choose_pn_two_bound (d : ℕ) :
    padicNorm 2 (Ring.choose (1/8 : ℚ) d) ≤ (16:ℚ)^d := by
  have h2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hc := congrArg (padicNorm 2) (choose_eighth_prod d)
  rw [padicNorm.mul, pn_prod] at hc
  have hprodval : (∏ i ∈ Finset.range d, padicNorm 2 (1/8 - (i:ℚ))) = (8:ℚ)^d := by
    rw [Finset.prod_congr rfl (fun i _ => pn18 i), Finset.prod_const, Finset.card_range]
  rw [hprodval] at hc
  -- hc : padicNorm 2 d! * padicNorm 2 choose = 8^d
  set A2 := padicNorm 2 ((d.factorial : ℕ):ℚ) with hA2
  have hApos : 0 < A2 := by
    rw [hA2]
    refine lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm ?_)
    apply padicNorm.nonzero
    exact_mod_cast Nat.factorial_ne_zero d
  have hAlb : (1/2:ℚ)^d ≤ A2 := pn_fact_lb d
  -- from hc: A2 * choose = 8^d, push_cast d! 
  have hc2 : A2 * padicNorm 2 (Ring.choose (1/8:ℚ) d) = (8:ℚ)^d := by
    rw [hA2]; convert hc using 3 <;> push_cast <;> ring
  have hchoose : padicNorm 2 (Ring.choose (1/8:ℚ) d) = (8:ℚ)^d / A2 := by
    field_simp at hc2 ⊢; linarith [hc2]
  rw [hchoose]
  rw [div_le_iff₀ hApos]
  calc (8:ℚ)^d = (16:ℚ)^d * (1/2:ℚ)^d := by rw [← mul_pow]; norm_num
    _ ≤ (16:ℚ)^d * A2 := by apply mul_le_mul_of_nonneg_left hAlb (by positivity)

lemma choose_pn_odd (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (d : ℕ) :
    padicNorm p (Ring.choose (1/8 : ℚ) d) ≤ 1 := by
  have hden : ¬ (p ∣ (1/8 : ℚ).den) := by
    have h8 : (1/8 : ℚ).den = 8 := by norm_num
    rw [h8]; intro h
    have h2 := Nat.Prime.dvd_of_dvd_pow hp.out (show p ∣ 2^3 by simpa using h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).mp h2)
  have hle : ‖(1/8 : ℚ_[p])‖ ≤ 1 := by
    simpa using Padic.norm_rat_le_one (p := p) hden
  set y : ℤ_[p] := ⟨(1/8 : ℚ_[p]), hle⟩ with hy
  have key : ‖((Ring.choose (1/8 : ℚ) d : ℚ) : ℚ_[p])‖ ≤ 1 := by
    have hmap : ((Ring.choose (1/8 : ℚ) d : ℚ) : ℚ_[p]) = Ring.choose ((1/8 : ℚ_[p])) d := by
      simpa using Ring.map_choose (Rat.castHom ℚ_[p]) (1/8 : ℚ) d
    rw [hmap]
    have hcoe : ((y : ℚ_[p])) = (1/8 : ℚ_[p]) := rfl
    have hmap2 : Ring.choose (1/8 : ℚ_[p]) d = ((Ring.choose y d : ℤ_[p]) : ℚ_[p]) := by
      rw [← hcoe]
      exact (Ring.map_choose (PadicInt.Coe.ringHom (p := p)) y d).symm
    rw [hmap2]
    exact PadicInt.norm_le_one _
  rw [Padic.eq_padicNorm] at key
  exact_mod_cast key

noncomputable def Bq : PowerSeries ℚ := PowerSeries.binomialSeries ℚ (1/8 : ℚ)

theorem Bq8 : Bq ^ 8 = 1 + (X : PowerSeries ℚ) := by
  have helper : ∀ k : ℕ, Bq ^ k = PowerSeries.binomialSeries ℚ ((k : ℚ) * (1/8)) := by
    intro k
    induction k with
    | zero => simp [Bq]
    | succ n ih =>
      rw [pow_succ, ih, Bq, ← PowerSeries.binomialSeries_add]; congr 1; push_cast; ring
  rw [helper]
  have h8 : ((8:ℕ) : ℚ) * (1/8) = ((1:ℕ) : ℚ) := by norm_num
  rw [h8, PowerSeries.binomialSeries_nat]; simp

lemma subst8 (u : PowerSeries ℚ) (hu : PowerSeries.constantCoeff (R := ℚ) u = 0) :
    (subst u Bq) ^ 8 = 1 + u := by
  have hsub : HasSubst u := HasSubst.of_constantCoeff_zero' hu
  have h1 : subst u (1 : PowerSeries ℚ) = 1 := by
    rw [← coe_substAlgHom hsub]; exact map_one _
  rw [← subst_pow hsub, Bq8, subst_add hsub, subst_X hsub, h1]

lemma Bq_coeff (d : ℕ) : (PowerSeries.coeff d) Bq = Ring.choose (1/8 : ℚ) d := by
  rw [Bq, PowerSeries.binomialSeries_coeff]; simp

noncomputable section

def w : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ))
def w3 : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ) / (3:ℤ)^n)
def w16 : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ) / 16)
def uq : PowerSeries ℚ := OGF_A_scaled - 1

lemma w_coeff (n : ℕ) : (PowerSeries.coeff n) w = if n = 0 then 0 else (a n : ℤ) := by
  simp [w, coeff_mk]

lemma const_w : (PowerSeries.constantCoeff (R := ℤ)) w = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, w_coeff]; simp

lemma hw3 : w = (rescale (3:ℤ)) w3 := by
  ext n
  rw [w_coeff, coeff_rescale, w3, coeff_mk]
  by_cases h : n = 0
  · simp [h]
  · simp only [if_neg h]
    rw [Int.mul_ediv_cancel']
    exact_mod_cast three_pow_dvd_a n

lemma hw16 : w = PowerSeries.C (16:ℤ) * w16 := by
  ext n
  rw [w_coeff, coeff_C_mul, w16, coeff_mk]
  by_cases h : n = 0
  · simp [h]
  · simp only [if_neg h]
    rw [Int.mul_ediv_cancel']
    exact_mod_cast sixteen_dvd_a n (Nat.one_le_iff_ne_zero.mpr h)

-- u = rescale(1/3)(map cast w)
lemma hu_eq : uq = (rescale (1/3:ℚ)) (map (Int.castRingHom ℚ) w) := by
  ext n
  simp only [uq, map_sub, coeff_rescale, coeff_map, w_coeff, OGF_A_scaled, coeff_mk,
    Int.coe_castRingHom, PowerSeries.coeff_one]
  by_cases h : n = 0
  · subst h; simp [a_zero]
  · simp only [if_neg h]
    push_cast
    rw [div_pow, one_pow]
    ring

lemma const_u : (PowerSeries.constantCoeff (R := ℚ)) uq = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, uq, map_sub]
  simp only [OGF_A_scaled, coeff_mk, PowerSeries.coeff_one]
  simp [a_zero]

-- coeff m (u^d) = (1/3)^m * (coeff m (w^d) : ℚ)
lemma coeff_u_pow (m d : ℕ) :
    (PowerSeries.coeff m) (uq ^ d) = (1/3:ℚ)^m * (((PowerSeries.coeff m) (w ^ d) : ℤ) : ℚ) := by
  rw [hu_eq, ← map_pow, ← map_pow, coeff_rescale, coeff_map]
  simp

-- divisibility
lemma dvd3 (m d : ℕ) : (3:ℤ)^m ∣ (PowerSeries.coeff m) (w ^ d) := by
  rw [hw3, ← map_pow, coeff_rescale]
  exact Dvd.intro _ rfl

lemma dvd16 (m d : ℕ) : (16:ℤ)^d ∣ (PowerSeries.coeff m) (w ^ d) := by
  rw [hw16, mul_pow, ← map_pow, coeff_C_mul]
  exact Dvd.intro _ rfl

-- vanishing for d > m
lemma coeff_w_pow_eq_zero (m d : ℕ) (h : m < d) : (PowerSeries.coeff m) (w ^ d) = 0 := by
  have hX : (X : PowerSeries ℤ) ^ d ∣ w ^ d := by
    apply pow_dvd_pow_of_dvd
    rw [X_dvd_iff]; exact const_w
  rw [X_pow_dvd_iff] at hX
  exact hX m h


-- helper: padicNorm of power
lemma pn_pow (p : ℕ) [Fact p.Prime] (q : ℚ) (m : ℕ) :
    padicNorm p (q ^ m) = (padicNorm p q) ^ m := by
  induction m with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, padicNorm.mul, ih]

lemma pn_third_ne3 (p : ℕ) [Fact p.Prime] (h : p ≠ 3) :
    padicNorm p (1/3 : ℚ) = 1 := by
  have h3 : padicNorm p (3:ℚ) = 1 := by
    have he : (3:ℚ) = ((3:ℤ):ℚ) := by norm_num
    rw [he, padicNorm.int_eq_one_iff]
    intro hd
    rw [show (3:ℤ) = ((3:ℕ):ℤ) by norm_num, Int.natCast_dvd_natCast] at hd
    exact h ((Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp hd)
  rw [padicNorm.div, padicNorm.one, h3]; norm_num

lemma pn_third_3 : padicNorm 3 (1/3:ℚ) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [padicNorm.div, padicNorm.one]
  have h3 : padicNorm 3 (3:ℚ) = (3:ℚ)⁻¹ := by
    have he : (3:ℚ) = ((3:ℕ):ℚ) := by norm_num
    rw [he]; exact padicNorm.padicNorm_p_of_prime
  rw [h3]; norm_num

lemma term_pn (m d : ℕ) (p : ℕ) [hp : Fact p.Prime] :
    padicNorm p (Ring.choose (1/8:ℚ) d * (PowerSeries.coeff m) (uq ^ d)) ≤ 1 := by
  set cm : ℤ := (PowerSeries.coeff m) (w ^ d) with hcm
  rw [coeff_u_pow, ← mul_assoc]
  -- padicNorm p (ch * (1/3)^m * cm)
  rw [padicNorm.mul, padicNorm.mul, pn_pow]
  by_cases hp3 : p = 3
  · subst hp3
    rw [pn_third_3]
    -- ≤ 1 * 3^m * pn(cm) ; with pn(ch)≤1, pn(cm)≤3^{-m}
    have hch : padicNorm 3 (Ring.choose (1/8:ℚ) d) ≤ 1 := choose_pn_odd 3 (by norm_num) d
    have hcmn : padicNorm 3 ((cm:ℚ)) ≤ (3:ℚ)^(-(m:ℤ)) := by
      have hd : ((3^m : ℕ):ℤ) ∣ cm := by rw [hcm]; exact_mod_cast dvd3 m d
      have key := (padicNorm.dvd_iff_norm_le (p:=3)).mp hd
      simpa using key
    calc padicNorm 3 (Ring.choose (1/8:ℚ) d) * (3:ℚ)^m * padicNorm 3 ((cm:ℚ))
        ≤ 1 * (3:ℚ)^m * (3:ℚ)^(-(m:ℤ)) := by
          apply mul_le_mul (mul_le_mul hch (le_refl _) (by positivity) (by norm_num))
            hcmn (padicNorm.nonneg _) (by positivity)
      _ = 1 := by
          rw [one_mul, ← zpow_natCast (3:ℚ) m, ← zpow_add₀ (by norm_num : (3:ℚ) ≠ 0)]
          simp
  · by_cases hp2 : p = 2
    · subst hp2
      rw [pn_third_ne3 2 (by norm_num), one_pow, mul_one]
      have hch : padicNorm 2 (Ring.choose (1/8:ℚ) d) ≤ (16:ℚ)^d := choose_pn_two_bound d
      have hcmn : padicNorm 2 ((cm:ℚ)) ≤ (16:ℚ)^(-(d:ℤ)) := by
        have hdvd : ((2^(4*d) : ℕ) : ℤ) ∣ cm := by
          have hh := dvd16 m d
          rw [← hcm] at hh
          rw [show (2^(4*d):ℕ) = (16:ℕ)^d by rw [pow_mul]; norm_num]
          exact_mod_cast hh
        have key := (padicNorm.dvd_iff_norm_le (p:=2) (n := 4*d) (z := cm)).mp hdvd
        have heq : ((2:ℕ):ℚ)^(-(((4*d):ℕ):ℤ)) = (16:ℚ)^(-(d:ℤ)) := by
          rw [show (16:ℚ) = ((2:ℕ):ℚ)^(4:ℕ) by norm_num, ← zpow_natCast ((2:ℕ):ℚ) 4,
            ← _root_.zpow_mul]
          congr 1; push_cast; ring
        exact le_trans key (le_of_eq heq)
      calc padicNorm 2 (Ring.choose (1/8:ℚ) d) * padicNorm 2 ((cm:ℚ))
          ≤ (16:ℚ)^d * (16:ℚ)^(-(d:ℤ)) := by
            apply mul_le_mul hch hcmn (padicNorm.nonneg _) (by positivity)
        _ = 1 := by
            rw [← zpow_natCast (16:ℚ) d, ← zpow_add₀ (by norm_num : (16:ℚ) ≠ 0)]
            simp
    · -- p ≥ 5
      rw [pn_third_ne3 p hp3, one_pow, mul_one]
      have hch : padicNorm p (Ring.choose (1/8:ℚ) d) ≤ 1 := choose_pn_odd p hp2 d
      have hcmn : padicNorm p ((cm:ℚ)) ≤ 1 := padicNorm.of_int _
      calc padicNorm p (Ring.choose (1/8:ℚ) d) * padicNorm p ((cm:ℚ))
          ≤ 1 * 1 := mul_le_mul hch hcmn (padicNorm.nonneg _) (by norm_num)
        _ = 1 := by norm_num

def Cq : PowerSeries ℚ := subst uq Bq

lemma coeff_C_eq (m : ℕ) :
    (PowerSeries.coeff m) Cq
      = ∑ d ∈ Finset.range (m+1), Ring.choose (1/8:ℚ) d * (PowerSeries.coeff m) (uq^d) := by
  have hsub : HasSubst uq := HasSubst.of_constantCoeff_zero' const_u
  rw [Cq, coeff_subst' hsub]
  rw [finsum_eq_sum_of_support_subset
      (fun d => (PowerSeries.coeff d) Bq • (PowerSeries.coeff m) (uq^d))
      (s := Finset.range (m+1)) ?_]
  · apply Finset.sum_congr rfl
    intro d _
    rw [Bq_coeff, smul_eq_mul]
  · intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    push_neg at hcon
    apply hd
    rw [Bq_coeff, smul_eq_mul, coeff_u_pow, coeff_w_pow_eq_zero m d (by omega)]
    simp

lemma coeff_C_padic (m : ℕ) (p : ℕ) [Fact p.Prime] :
    padicNorm p ((PowerSeries.coeff m) Cq) ≤ 1 := by
  rw [coeff_C_eq]
  apply padicNorm.sum_le'
  · intro d _; exact term_pn m d p
  · norm_num

lemma den_eq_one_of (q : ℚ) (h : ∀ p : ℕ, p.Prime → padicNorm p q ≤ 1) : q.den = 1 := by
  by_contra hd
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
  haveI : Fact p.Prime := ⟨hp⟩
  have hq0 : q ≠ 0 := by rintro rfl; exact hd (by norm_num)
  have hpn : ¬ p ∣ q.num.natAbs := by
    intro hn
    have hdg : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd hn hpd
    rw [q.reduced] at hdg
    exact hp.ne_one (Nat.dvd_one.mp hdg)
  have hval : padicValRat p q < 0 := by
    rw [padicValRat_def]
    have h1 : padicValInt p q.num = 0 := by
      apply padicValInt.eq_zero_of_not_dvd
      intro hdvd
      apply hpn
      have := Int.natAbs_dvd_natAbs.mpr hdvd
      simpa using this
    have h2 : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd q.den_nz hpd
    omega
  have hgt : 1 < padicNorm p q := by
    rw [padicNorm.eq_zpow_of_nonzero hq0]
    rw [one_lt_zpow_iff_right₀ (by exact_mod_cast hp.one_lt)]
    omega
  linarith [h p hp]

lemma coeff_C_den (m : ℕ) : ((PowerSeries.coeff m) Cq).den = 1 := by
  apply den_eq_one_of
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  exact coeff_C_padic m p

-- the integer power series
def Cz : PowerSeries ℤ := mk (fun m => ((PowerSeries.coeff m) Cq).num)

lemma map_Cz : map (Int.castRingHom ℚ) Cz = Cq := by
  ext m
  rw [coeff_map, Cz, coeff_mk]
  simp only [Int.coe_castRingHom]
  exact (Rat.den_eq_one_iff _).mp (coeff_C_den m)

/--
A228143 Conjecture: if $A(x) = 1 + 48*x + 161856*x^2 + \dots$ denotes the o.g.f. then
$A(x/3)^{1/8}$ has integer coefficients (checked up to $x^{30}$).
-/
theorem oeis_228143_conjecture_1 :
    ∃ C : PowerSeries ℤ,
      (PowerSeries.map (Int.castRingHom ℚ)) (C ^ 8) = OGF_A_scaled := by
  refine ⟨Cz, ?_⟩
  rw [map_pow, map_Cz, Cq, subst8 uq const_u, uq]
  ring

end
