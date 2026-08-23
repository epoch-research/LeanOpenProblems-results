import FormalConjectures.Util.ProblemImports

open Nat Finset Int

/--
A301376: Number of ways to write $n^2$ as $x^2 + y^2 + z^2 + w^2$ with $x,y,z,w$ nonnegative integers and $z \le w$ such that $x^2-(3y)^2 = 4^k$ for some $k = 0,1,2,\ldots$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  -- Search space for (x, y, z, w) as nested products ((x, y), (z, w)).
  let domain : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := (R.product R).product (R.product R)

  Finset.card $ domain.filter (λ p : (ℕ × ℕ) × (ℕ × ℕ) =>
    let x := p.fst.fst; let y := p.fst.snd;
    let z := p.snd.fst; let w := p.snd.snd;

    x^2 + y^2 + z^2 + w^2 = n^2 ∧
    z ≤ w ∧
    -- The condition: x^2 - (3*y)^2 = 4^k. Casted to ℤ for subtraction, then compared to 4^k (which is in ℕ and implicitly cast to ℤ).
    -- Bounded existence: 4^k <= n^2 implies k is bounded by log_4(n^2). range (n + 1) is a safe upper bound for k.
    (∃ k ∈ Finset.range (n + 1), (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ))
  )

/-- A convenient existence statement equivalent to `a n > 0`. -/
def HasARep (n : ℕ) : Prop :=
  ∃ (x y z w k : ℕ),
    x ≤ n ∧ y ≤ n ∧ z ≤ n ∧ w ≤ n ∧ k ≤ n ∧
    z ≤ w ∧
    x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ^ 2 ∧
    (x ^ 2 : ℤ) - (3 * y : ℤ) ^ 2 = (4 ^ k : ℤ)

lemma hasARep_of_a_pos {n : ℕ} (h : 0 < a n) : HasARep n := by
  unfold a at h
  obtain ⟨p, hp⟩ := Finset.card_pos.mp h
  have hp' := Finset.mem_filter.mp hp
  obtain ⟨hpdom, hsum, hzw, ⟨k, hk, hcond⟩⟩ := hp'
  have hprod := Finset.mem_product.mp hpdom
  obtain ⟨hxy, hzw'⟩ := hprod
  have hx := Finset.mem_range.mp (Finset.mem_product.mp hxy).1
  have hy := Finset.mem_range.mp (Finset.mem_product.mp hxy).2
  have hz := Finset.mem_range.mp (Finset.mem_product.mp hzw').1
  have hw := Finset.mem_range.mp (Finset.mem_product.mp hzw').2
  exact ⟨p.1.1, p.1.2, p.2.1, p.2.2, k,
    Nat.lt_succ_iff.mp hx, Nat.lt_succ_iff.mp hy,
    Nat.lt_succ_iff.mp hz, Nat.lt_succ_iff.mp hw,
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), hzw, hsum, hcond⟩

lemma a_pos_of_hasARep {n : ℕ} (h : HasARep n) : 0 < a n := by
  obtain ⟨x, y, z, w, k, hx, hy, hz, hw, hk, hzw, hsum, hcond⟩ := h
  unfold a
  refine Finset.card_pos.mpr ?_
  refine Finset.filter_nonempty_iff.mpr ?_
  refine ⟨((x, y), (z, w)), ?_, ?_⟩
  · simp [Finset.mem_product, Finset.mem_range]
    exact ⟨⟨hx, hy⟩, hz, hw⟩
  · exact ⟨hsum, hzw, ⟨k, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk), hcond⟩⟩

lemma hasARep_iff_a_pos (n : ℕ) : HasARep n ↔ 0 < a n :=
  ⟨a_pos_of_hasARep, hasARep_of_a_pos⟩

/-- Package a four-tuple satisfying the numerical conditions into `HasARep`. -/
lemma hasARep_of_data {n x y z w k : ℕ}
    (hx : x ≤ n) (hy : y ≤ n) (hz : z ≤ n) (hw : w ≤ n) (hk : k ≤ n)
    (hzw : z ≤ w)
    (hsum : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ^ 2)
    (hcond : (x ^ 2 : ℤ) - (3 * y : ℤ) ^ 2 = (4 ^ k : ℤ)) :
    HasARep n :=
  ⟨x, y, z, w, k, hx, hy, hz, hw, hk, hzw, hsum, hcond⟩

lemma sq_le_of_sq_add_le {a b c : ℕ} (h : a ^ 2 + b ^ 2 ≤ c ^ 2) : a ≤ c := by
  have : a ^ 2 ≤ c ^ 2 := le_trans (Nat.le_add_right _ _) h
  exact (Nat.pow_le_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).1 this

lemma sq_le_of_add_sq_le {a b c : ℕ} (h : a ^ 2 + b ^ 2 ≤ c ^ 2) : b ≤ c := by
  have : b ^ 2 ≤ c ^ 2 := le_trans (Nat.le_add_left _ _) h
  exact (Nat.pow_le_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).1 this

lemma k_le_of_cond {n x y k : ℕ} (hx : x ≤ n)
    (hcond : (x ^ 2 : ℤ) - (3 * y : ℤ) ^ 2 = (4 ^ k : ℤ)) : k ≤ n := by
  have hx2 : (x ^ 2 : ℤ) - (3 * y : ℤ) ^ 2 ≤ (x ^ 2 : ℤ) :=
    sub_le_self _ (sq_nonneg _)
  have : (4 ^ k : ℤ) ≤ (x ^ 2 : ℤ) := by
    rw [← hcond]; exact hx2
  have h4 : (4 ^ k : ℕ) ≤ x ^ 2 := by exact_mod_cast this
  have hx2n : x ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hx 2
  have hle : 4 ^ k ≤ n ^ 2 := le_trans h4 hx2n
  have hpow : (2 ^ k) ^ 2 ≤ n ^ 2 := by
    have : 4 ^ k = (2 ^ k) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rwa [this] at hle
  have : 2 ^ k ≤ n := (Nat.pow_le_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).1 hpow
  exact le_trans (Nat.lt_pow_self (by decide : 1 < 2) |>.le) this

lemma hasARep_of_remainder {n x y k : ℕ}
    (hx : x ≤ n) (hy : y ≤ n)
    (hcond : (x ^ 2 : ℤ) - (3 * y : ℤ) ^ 2 = (4 ^ k : ℤ))
    (hxy : x ^ 2 + y ^ 2 ≤ n ^ 2)
    (hrem : ∃ z w : ℕ, z ^ 2 + w ^ 2 = n ^ 2 - x ^ 2 - y ^ 2) :
    HasARep n := by
  obtain ⟨z0, w0, hzw0⟩ := hrem
  wlog hle : z0 ≤ w0 generalizing z0 w0
  · exact this w0 z0 (by rw [add_comm]; exact hzw0) (le_of_not_ge hle)
  have hsum : x ^ 2 + y ^ 2 + z0 ^ 2 + w0 ^ 2 = n ^ 2 := by
    have : n ^ 2 - x ^ 2 - y ^ 2 = n ^ 2 - (x ^ 2 + y ^ 2) := by
      simp [Nat.sub_sub]
    omega
  have hremle : z0 ^ 2 + w0 ^ 2 ≤ n ^ 2 := by
    have : n ^ 2 - x ^ 2 - y ^ 2 = n ^ 2 - (x ^ 2 + y ^ 2) := by
      simp [Nat.sub_sub]
    rw [this] at hzw0
    rw [hzw0]
    exact Nat.sub_le _ _
  exact hasARep_of_data hx hy (sq_le_of_sq_add_le hremle) (sq_le_of_add_sq_le hremle)
    (k_le_of_cond hx hcond) hle hsum hcond

/-- The pair `(2^k, 0)` satisfies the difference-of-squares condition. -/
lemma pow2_sq (k : ℕ) : (2 ^ k) ^ 2 = 4 ^ k := by
  calc
    (2 ^ k) ^ 2 = 2 ^ (k * 2) := by rw [← pow_mul]
    _ = 2 ^ (2 * k) := by rw [mul_comm]
    _ = (2 ^ 2) ^ k := by rw [pow_mul]
    _ = 4 ^ k := by norm_num

lemma cond_of_nat_sq {x y k : ℕ} (h : x ^ 2 = 9 * y ^ 2 + 4 ^ k) :
    (x ^ 2 : ℤ) - (3 * y : ℤ) ^ 2 = (4 ^ k : ℤ) := by
  have hle : 9 * y ^ 2 ≤ x ^ 2 := by rw [h]; exact Nat.le_add_right _ _
  have hnat : x ^ 2 - 9 * y ^ 2 = 4 ^ k := by
    rw [Nat.sub_eq_iff_eq_add hle, h, add_comm]
  have hx2 : ((x ^ 2 : ℕ) : ℤ) = (x : ℤ) ^ 2 := by push_cast; rfl
  have h9 : ((9 * y ^ 2 : ℕ) : ℤ) = (3 * y : ℤ) ^ 2 := by push_cast; ring
  have : ((x ^ 2 - 9 * y ^ 2 : ℕ) : ℤ) = (x : ℤ) ^ 2 - (3 * y : ℤ) ^ 2 := by
    rw [Nat.cast_sub hle, hx2, h9]
  rw [← this, hnat]
  norm_cast

lemma cond_pow2 (k : ℕ) :
    ((2 ^ k) ^ 2 : ℤ) - (3 * (0 : ℕ) : ℤ) ^ 2 = (4 ^ k : ℤ) :=
  cond_of_nat_sq (by simp [pow2_sq])

lemma cond_one :
    ((1 : ℕ) ^ 2 : ℤ) - (3 * (0 : ℕ) : ℤ) ^ 2 = (4 ^ 0 : ℤ) := by
  norm_num

lemma three_dvd_four_pow_sub_one (t : ℕ) : 3 ∣ 4 ^ t - 1 := by
  have h : 4 ≡ 1 [MOD 3] := by decide
  have : 4 ^ t ≡ 1 [MOD 3] := by simpa using h.pow t
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow t 4 (by decide))).mp this.symm

lemma four_pow_pos (t : ℕ) : 1 ≤ 4 ^ t :=
  Nat.one_le_pow t 4 (by decide)

lemma four_pow_sq_id (t : ℕ) :
    (4 ^ t + 1) ^ 2 = (4 ^ t - 1) ^ 2 + 4 ^ (t + 1) := by
  have ha := four_pow_pos t
  have hsub : (4 ^ t + 1) ^ 2 - (4 ^ t - 1) ^ 2 = 4 * 4 ^ t := by
    rw [Nat.sq_sub_sq]
    have hsum : 4 ^ t + 1 + (4 ^ t - 1) = 2 * 4 ^ t := by omega
    have hdif : 4 ^ t + 1 - (4 ^ t - 1) = 2 := by omega
    rw [hsum, hdif]
    ring
  have hle : (4 ^ t - 1) ^ 2 ≤ (4 ^ t + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  rw [Nat.sub_eq_iff_eq_add hle] at hsub
  rw [hsub, pow_succ]
  ring

/-- Natural-number form of the family identity: `x² = 9y² + 4^{r+t+1}`. -/
lemma family_sq_add (t r : ℕ) :
    ((4 ^ t + 1) * 2 ^ r) ^ 2
      = 9 * ((((4 ^ t - 1) / 3) * 2 ^ r) ^ 2) + 4 ^ (r + t + 1) := by
  have hy : 3 * ((4 ^ t - 1) / 3) = 4 ^ t - 1 :=
    Nat.mul_div_cancel' (three_dvd_four_pow_sub_one t)
  have h9 : 9 * (((4 ^ t - 1) / 3) ^ 2) = (4 ^ t - 1) ^ 2 := by
    calc
      9 * (((4 ^ t - 1) / 3) ^ 2) = (3 * ((4 ^ t - 1) / 3)) ^ 2 := by ring
      _ = (4 ^ t - 1) ^ 2 := by rw [hy]
  have hpow : (2 ^ r) ^ 2 = 4 ^ r := pow2_sq r
  calc
    ((4 ^ t + 1) * 2 ^ r) ^ 2
        = (4 ^ t + 1) ^ 2 * (2 ^ r) ^ 2 := by ring
    _ = ((4 ^ t - 1) ^ 2 + 4 ^ (t + 1)) * (2 ^ r) ^ 2 := by rw [four_pow_sq_id]
    _ = (4 ^ t - 1) ^ 2 * (2 ^ r) ^ 2 + 4 ^ (t + 1) * (2 ^ r) ^ 2 := by ring
    _ = 9 * (((4 ^ t - 1) / 3) ^ 2) * (2 ^ r) ^ 2 + 4 ^ (t + 1) * 4 ^ r := by
        rw [h9, hpow]
    _ = 9 * ((((4 ^ t - 1) / 3) * 2 ^ r) ^ 2) + 4 ^ (r + t + 1) := by
        have : 4 ^ (t + 1) * 4 ^ r = 4 ^ (r + t + 1) := by
          rw [← pow_add]; ac_rfl
        rw [this]
        ring

lemma cond_family (t r : ℕ) :
    (((4 ^ t + 1) * 2 ^ r) ^ 2 : ℤ)
      - (3 * ((((4 ^ t - 1) / 3) * 2 ^ r : ℕ)) : ℤ) ^ 2
      = (4 ^ (r + t + 1) : ℤ) :=
  cond_of_nat_sq (family_sq_add t r)

lemma t1_sq_sum (r : ℕ) :
    (5 * 2 ^ r) ^ 2 + (2 ^ r) ^ 2 = 26 * 4 ^ r := by
  calc
    (5 * 2 ^ r) ^ 2 + (2 ^ r) ^ 2 = 25 * (2 ^ r) ^ 2 + (2 ^ r) ^ 2 := by ring
    _ = 26 * (2 ^ r) ^ 2 := by ring
    _ = 26 * 4 ^ r := by rw [pow2_sq]

lemma cond_t1 (r : ℕ) :
    ((5 * 2 ^ r) ^ 2 : ℤ) - (3 * (2 ^ r) : ℤ) ^ 2 = (4 ^ (r + 2) : ℤ) := by
  apply cond_of_nat_sq
  have h16 : 16 * 4 ^ r = 4 ^ (r + 2) := by
    rw [show 16 = 4 ^ 2 by norm_num, ← pow_add]; ac_rfl
  calc
    (5 * 2 ^ r) ^ 2 = 5 ^ 2 * (2 ^ r) ^ 2 := by rw [mul_pow]
    _ = 25 * 4 ^ r := by rw [pow2_sq]; norm_num
    _ = 9 * 4 ^ r + 16 * 4 ^ r := by ring
    _ = 9 * (2 ^ r) ^ 2 + 4 ^ (r + 2) := by rw [pow2_sq, h16]

lemma t2_sq_sum (r : ℕ) :
    (17 * 2 ^ r) ^ 2 + (5 * 2 ^ r) ^ 2 = 314 * 4 ^ r := by
  calc
    (17 * 2 ^ r) ^ 2 + (5 * 2 ^ r) ^ 2
        = 289 * (2 ^ r) ^ 2 + 25 * (2 ^ r) ^ 2 := by ring
    _ = 314 * (2 ^ r) ^ 2 := by ring
    _ = 314 * 4 ^ r := by rw [pow2_sq]

lemma cond_t2 (r : ℕ) :
    ((17 * 2 ^ r) ^ 2 : ℤ) - (3 * (5 * 2 ^ r) : ℤ) ^ 2 = (4 ^ (r + 3) : ℤ) := by
  apply cond_of_nat_sq
  have h64 : 64 * 4 ^ r = 4 ^ (r + 3) := by
    rw [show 64 = 4 ^ 3 by norm_num, ← pow_add]; ac_rfl
  calc
    (17 * 2 ^ r) ^ 2 = 17 ^ 2 * (2 ^ r) ^ 2 := by rw [mul_pow]
    _ = 289 * 4 ^ r := by rw [pow2_sq]; norm_num
    _ = 9 * (5 * 2 ^ r) ^ 2 + 64 * 4 ^ r := by
        have : 9 * (5 * 2 ^ r) ^ 2 = 225 * 4 ^ r := by
          rw [mul_pow, pow2_sq]; ring
        omega
    _ = 9 * (5 * 2 ^ r) ^ 2 + 4 ^ (r + 3) := by rw [h64]

/-- If `n` is a power of two then `(n,0,0,0)` is a representation. -/
lemma hasARep_pow2 (t : ℕ) : HasARep (2 ^ t) := by
  refine ⟨2 ^ t, 0, 0, 0, t, le_rfl, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, ?_,
    Nat.zero_le _, ?_, cond_pow2 t⟩
  · exact Nat.le_of_lt t.lt_two_pow_self
  · simp

/-- Scaling a representation of `m` by `2` yields a representation of `2m`. -/
lemma hasARep_double {m : ℕ} (hm : 0 < m) (h : HasARep m) : HasARep (2 * m) := by
  obtain ⟨x, y, z, w, k, hx, hy, hz, hw, hk, hzw, hsum, hcond⟩ := h
  refine ⟨2 * x, 2 * y, 2 * z, 2 * w, k + 1, ?x, ?y, ?z, ?w, ?k, ?zw, ?sum, ?cond⟩
  · exact Nat.mul_le_mul_left 2 hx
  · exact Nat.mul_le_mul_left 2 hy
  · exact Nat.mul_le_mul_left 2 hz
  · exact Nat.mul_le_mul_left 2 hw
  · have : k + 1 ≤ m + m := by omega
    simpa [two_mul] using this
  · exact Nat.mul_le_mul_left 2 hzw
  · calc
      (2 * x) ^ 2 + (2 * y) ^ 2 + (2 * z) ^ 2 + (2 * w) ^ 2
        = 4 * x ^ 2 + 4 * y ^ 2 + 4 * z ^ 2 + 4 * w ^ 2 := by ring
      _ = 4 * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by ring
      _ = 4 * m ^ 2 := by rw [hsum]
      _ = (2 * m) ^ 2 := by ring
  · have : ((2 * x : ℕ) ^ 2 : ℤ) - (3 * (2 * y : ℕ) : ℤ) ^ 2 =
        4 * ((x ^ 2 : ℤ) - (3 * y : ℤ) ^ 2) := by
      push_cast
      ring
    rw [this, hcond]
    ring

lemma hasARep_of_lt_of_even (n : ℕ) (hn : 0 < n)
    (ih : ∀ m < n, 0 < m → HasARep m) (he : Even n) : HasARep n := by
  obtain ⟨m, rfl⟩ := he
  have hmpos : 0 < m := by omega
  have : HasARep m := ih m (by omega) hmpos
  simpa [two_mul] using hasARep_double hmpos this

lemma hasARep_of_k0 {n : ℕ} (hn : 1 ≤ n)
    (hrem : ∃ z w : ℕ, z ^ 2 + w ^ 2 = n ^ 2 - 1) :
    HasARep n := by
  have hxy : (1 : ℕ) ^ 2 + 0 ^ 2 ≤ n ^ 2 := by
    have : 1 ≤ n ^ 2 := one_le_pow 2 n (by omega)
    simpa using this
  exact hasARep_of_remainder hn (Nat.zero_le _) cond_one hxy (by simpa using hrem)

lemma hasARep_of_pow2_remainder {n k : ℕ}
    (hx : 2 ^ k ≤ n)
    (hrem : ∃ z w : ℕ, z ^ 2 + w ^ 2 = n ^ 2 - 4 ^ k) :
    HasARep n := by
  have hxy : (2 ^ k) ^ 2 + (0 : ℕ) ^ 2 ≤ n ^ 2 := by
    have : (2 ^ k) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hx 2
    simpa using this
  refine hasARep_of_remainder hx (Nat.zero_le _) (cond_pow2 k) hxy ?_
  simpa [pow2_sq] using hrem

lemma hasARep_of_t1 {n r : ℕ}
    (hx : 5 * 2 ^ r ≤ n)
    (hremle : 26 * 4 ^ r ≤ n ^ 2)
    (hrem : ∃ z w : ℕ, z ^ 2 + w ^ 2 = n ^ 2 - 26 * 4 ^ r) :
    HasARep n := by
  have hy : 2 ^ r ≤ n :=
    le_trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 5)) hx
  have hxy : (5 * 2 ^ r) ^ 2 + (2 ^ r) ^ 2 ≤ n ^ 2 := by
    rwa [t1_sq_sum]
  refine hasARep_of_remainder hx hy (cond_t1 r) hxy ?_
  rwa [Nat.sub_sub, t1_sq_sum]

lemma hasARep_of_t2 {n r : ℕ}
    (hx : 17 * 2 ^ r ≤ n)
    (hremle : 314 * 4 ^ r ≤ n ^ 2)
    (hrem : ∃ z w : ℕ, z ^ 2 + w ^ 2 = n ^ 2 - 314 * 4 ^ r) :
    HasARep n := by
  have hy : 5 * 2 ^ r ≤ n := by
    have : 5 * 2 ^ r ≤ 17 * 2 ^ r := Nat.mul_le_mul_right _ (by decide)
    exact le_trans this hx
  have hxy : (17 * 2 ^ r) ^ 2 + (5 * 2 ^ r) ^ 2 ≤ n ^ 2 := by
    rwa [t2_sq_sum]
  refine hasARep_of_remainder hx hy (cond_t2 r) hxy ?_
  rwa [Nat.sub_sub, t2_sq_sum]

lemma hasARep_of_family {n t r : ℕ}
    (hx : (4 ^ t + 1) * 2 ^ r ≤ n)
    (hxy : ((4 ^ t + 1) * 2 ^ r) ^ 2 + (((4 ^ t - 1) / 3) * 2 ^ r) ^ 2 ≤ n ^ 2)
    (hrem : ∃ z w : ℕ,
        z ^ 2 + w ^ 2
          = n ^ 2 - ((4 ^ t + 1) * 2 ^ r) ^ 2
              - (((4 ^ t - 1) / 3) * 2 ^ r) ^ 2) :
    HasARep n := by
  have hy : ((4 ^ t - 1) / 3) * 2 ^ r ≤ n := by
    have hdiv : (4 ^ t - 1) / 3 ≤ 4 ^ t - 1 := Nat.div_le_self _ _
    have hle : 4 ^ t - 1 ≤ 4 ^ t + 1 :=
      le_trans (Nat.sub_le _ _) (Nat.le_add_right _ _)
    exact le_trans (Nat.mul_le_mul_right _ (le_trans hdiv hle)) hx
  exact hasARep_of_remainder hx hy (cond_family t r) hxy hrem

/-- `m` is a sum of two squares. -/
def IsSumTwoSq (m : ℕ) : Prop := ∃ z w : ℕ, z ^ 2 + w ^ 2 = m

lemma isSumTwoSq_zero : IsSumTwoSq 0 := ⟨0, 0, by simp⟩

lemma isSumTwoSq_one : IsSumTwoSq 1 := ⟨0, 1, by simp⟩

lemma isSumTwoSq_mul {a b : ℕ} (ha : IsSumTwoSq a) (hb : IsSumTwoSq b) :
    IsSumTwoSq (a * b) := by
  obtain ⟨x, y, hx⟩ := ha
  obtain ⟨u, v, hu⟩ := hb
  obtain ⟨r, s, hrs⟩ := Nat.sq_add_sq_mul hx.symm hu.symm
  exact ⟨r, s, hrs.symm⟩

lemma isSumTwoSq_iff (m : ℕ) :
    IsSumTwoSq m ↔ ∀ q ∈ m.primeFactors, q % 4 = 3 → Even (padicValNat q m) := by
  constructor
  · intro h
    rw [← Nat.eq_sq_add_sq_iff]
    obtain ⟨z, w, hzw⟩ := h
    exact ⟨z, w, hzw.symm⟩
  · intro h
    obtain ⟨z, w, hzw⟩ := Nat.eq_sq_add_sq_iff.mpr h
    exact ⟨z, w, hzw.symm⟩

instance instDecidableIsSumTwoSq (m : ℕ) : Decidable (IsSumTwoSq m) :=
  decidable_of_iff' _ (isSumTwoSq_iff m)

lemma hasARep_of_isSumTwoSq_k0 {n : ℕ} (hn : 1 ≤ n) (h : IsSumTwoSq (n ^ 2 - 1)) :
    HasARep n :=
  hasARep_of_k0 hn h

lemma hasARep_of_isSumTwoSq_pow2 {n k : ℕ} (hx : 2 ^ k ≤ n)
    (h : IsSumTwoSq (n ^ 2 - 4 ^ k)) : HasARep n :=
  hasARep_of_pow2_remainder hx h

lemma hasARep_of_isSumTwoSq_t1 {n r : ℕ} (hx : 5 * 2 ^ r ≤ n)
    (hle : 26 * 4 ^ r ≤ n ^ 2) (h : IsSumTwoSq (n ^ 2 - 26 * 4 ^ r)) :
    HasARep n :=
  hasARep_of_t1 hx hle h

lemma hasARep_of_isSumTwoSq_t2 {n r : ℕ} (hx : 17 * 2 ^ r ≤ n)
    (hle : 314 * 4 ^ r ≤ n ^ 2) (h : IsSumTwoSq (n ^ 2 - 314 * 4 ^ r)) :
    HasARep n :=
  hasARep_of_t2 hx hle h

lemma hasARep_one : HasARep 1 :=
  hasARep_of_data (x := 1) (y := 0) (z := 0) (w := 0) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_three : HasARep 3 :=
  hasARep_of_k0 (by decide) ⟨2, 2, by norm_num⟩

lemma hasARep_five : HasARep 5 :=
  hasARep_of_pow2_remainder (k := 2) (by decide) ⟨0, 3, by norm_num⟩

lemma hasARep_seven : HasARep 7 :=
  hasARep_of_pow2_remainder (k := 1) (by decide) ⟨3, 6, by norm_num⟩

lemma hasARep_nine : HasARep 9 :=
  hasARep_of_k0 (by decide) ⟨4, 8, by norm_num⟩

/-- A number congruent to `3` modulo `4` is never a sum of two squares. -/
lemma not_isSumTwoSq_of_mod4 {m : ℕ} (h : m % 4 = 3) : ¬ IsSumTwoSq m := by
  rintro ⟨x, y, hxy⟩
  have hx2 : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
    have : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
    rcases this with hx | hx | hx | hx <;> simp [Nat.pow_mod, hx]
  have hy2 : y ^ 2 % 4 = 0 ∨ y ^ 2 % 4 = 1 := by
    have : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by omega
    rcases this with hy | hy | hy | hy <;> simp [Nat.pow_mod, hy]
  have : (x ^ 2 + y ^ 2) % 4 ≠ 3 := by
    rcases hx2 with hx2 | hx2 <;> rcases hy2 with hy2 | hy2 <;>
      simp [Nat.add_mod, hx2, hy2]
  rw [hxy] at this
  exact this h

/-- Squares modulo 8 are `0,1,4`. -/
lemma sq_mod8 (x : ℕ) : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  have : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨
      x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by omega
  rcases this with h | h | h | h | h | h | h | h <;> simp [Nat.pow_mod, h]

lemma not_isSumTwoSq_of_mod8 {m : ℕ} (h : m % 8 = 7) : ¬ IsSumTwoSq m := by
  rintro ⟨x, y, hxy⟩
  have hx := sq_mod8 x
  have hy := sq_mod8 y
  have : (x ^ 2 + y ^ 2) % 8 ≠ 7 := by
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;>
      simp [Nat.add_mod, hx, hy]
  rw [hxy] at this
  exact this h

lemma odd_sq_mod8 {n : ℕ} (h : Odd n) : n ^ 2 % 8 = 1 := by
  have : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    have : n % 2 = 1 := Nat.odd_iff.mp h
    omega
  rcases this with h | h | h | h <;> simp [Nat.pow_mod, h]

/-- `n = m² + 4^k + 1` works with remainder `4^{k+1}`:
`n² - 4^{k+1} = (m² + 4^k - 1)² + (2m)²`. -/
lemma hasARep_sq_add_four_pow (m k : ℕ) : HasARep (m ^ 2 + 4 ^ k + 1) := by
  set n := m ^ 2 + 4 ^ k + 1
  have hx : 2 ^ (k + 1) ≤ n := by
    have h2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h4 : 2 ^ (k + 1) ≤ 4 ^ k + 1 := by
      have hpow : (2 ^ k) ^ 2 = 4 ^ k := pow2_sq k
      have hid : 2 ^ (k + 1) ≤ (2 ^ k) ^ 2 + 1 := by
        calc
          2 ^ (k + 1) ≤ (2 ^ k - 1) ^ 2 + 2 ^ (k + 1) := Nat.le_add_left _ _
          _ = (2 ^ k) ^ 2 + 1 := by
            zify [h2]
            ring
      rwa [hpow] at hid
    omega
  have hle : 4 ^ (k + 1) ≤ n ^ 2 := by
    have : (2 ^ (k + 1)) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hx 2
    rwa [pow2_sq] at this
  have hrem : IsSumTwoSq (n ^ 2 - 4 ^ (k + 1)) := by
    have h4pos : 1 ≤ 4 ^ k := four_pow_pos k
    have hsub : 1 ≤ m ^ 2 + 4 ^ k := by omega
    have hcalc : n ^ 2 - 4 ^ (k + 1) = (m ^ 2 + 4 ^ k - 1) ^ 2 + (2 * m) ^ 2 := by
      rw [Nat.sub_eq_iff_eq_add hle]
      have rhs :
          (m ^ 2 + 4 ^ k - 1) ^ 2 + (2 * m) ^ 2 + 4 ^ (k + 1)
            = (m ^ 2 + 4 ^ k + 1) ^ 2 := by
        zify [hsub]
        ring
      simpa [n] using rhs.symm
    exact ⟨m ^ 2 + 4 ^ k - 1, 2 * m, hcalc.symm⟩
  exact hasARep_of_isSumTwoSq_pow2 hx hrem

lemma hasARep_11 : HasARep 11 :=
  hasARep_of_data (x := 2) (y := 0) (z := 6) (w := 9) (k := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_13 : HasARep 13 :=
  hasARep_of_data (x := 4) (y := 0) (z := 3) (w := 12) (k := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_15 : HasARep 15 :=
  hasARep_of_data (x := 2) (y := 0) (z := 5) (w := 14) (k := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_17 : HasARep 17 :=
  hasARep_of_data (x := 1) (y := 0) (z := 12) (w := 12) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_19 : HasARep 19 :=
  hasARep_of_data (x := 1) (y := 0) (z := 6) (w := 18) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_21 : HasARep 21 :=
  hasARep_of_data (x := 4) (y := 0) (z := 5) (w := 20) (k := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_23 : HasARep 23 :=
  hasARep_of_data (x := 10) (y := 2) (z := 5) (w := 20) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_25 : HasARep 25 :=
  hasARep_of_data (x := 16) (y := 0) (z := 12) (w := 15) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_27 : HasARep 27 :=
  hasARep_of_data (x := 2) (y := 0) (z := 7) (w := 26) (k := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_29 : HasARep 29 :=
  hasARep_of_data (x := 16) (y := 0) (z := 3) (w := 24) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_31 : HasARep 31 :=
  hasARep_of_data (x := 10) (y := 2) (z := 4) (w := 29) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_33 : HasARep 33 :=
  hasARep_of_data (x := 1) (y := 0) (z := 8) (w := 32) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_35 : HasARep 35 :=
  hasARep_of_data (x := 1) (y := 0) (z := 18) (w := 30) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_37 : HasARep 37 :=
  hasARep_of_data (x := 8) (y := 0) (z := 3) (w := 36) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_39 : HasARep 39 :=
  hasARep_of_data (x := 2) (y := 0) (z := 19) (w := 34) (k := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_41 : HasARep 41 :=
  hasARep_of_data (x := 4) (y := 0) (z := 12) (w := 39) (k := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_43 : HasARep 43 :=
  hasARep_of_data (x := 2) (y := 0) (z := 9) (w := 42) (k := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_45 : HasARep 45 :=
  hasARep_of_data (x := 4) (y := 0) (z := 28) (w := 35) (k := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_47 : HasARep 47 :=
  hasARep_of_data (x := 2) (y := 0) (z := 21) (w := 42) (k := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_49 : HasARep 49 :=
  hasARep_of_data (x := 4) (y := 0) (z := 9) (w := 48) (k := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_51 : HasARep 51 :=
  hasARep_of_data (x := 1) (y := 0) (z := 10) (w := 50) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_53 : HasARep 53 :=
  hasARep_of_data (x := 8) (y := 0) (z := 12) (w := 51) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_55 : HasARep 55 :=
  hasARep_of_data (x := 20) (y := 4) (z := 20) (w := 47) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_57 : HasARep 57 :=
  hasARep_of_data (x := 4) (y := 0) (z := 23) (w := 52) (k := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_59 : HasARep 59 :=
  hasARep_of_data (x := 20) (y := 4) (z := 16) (w := 53) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_61 : HasARep 61 :=
  hasARep_of_data (x := 10) (y := 2) (z := 41) (w := 44) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_63 : HasARep 63 :=
  hasARep_of_data (x := 2) (y := 0) (z := 11) (w := 62) (k := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_65 : HasARep 65 :=
  hasARep_of_data (x := 16) (y := 0) (z := 0) (w := 63) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_67 : HasARep 67 :=
  hasARep_of_data (x := 10) (y := 2) (z := 17) (w := 64) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_69 : HasARep 69 :=
  hasARep_of_data (x := 4) (y := 0) (z := 11) (w := 68) (k := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_71 : HasARep 71 :=
  hasARep_of_data (x := 10) (y := 2) (z := 29) (w := 64) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_73 : HasARep 73 :=
  hasARep_of_data (x := 1) (y := 0) (z := 12) (w := 72) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_75 : HasARep 75 :=
  hasARep_of_data (x := 10) (y := 2) (z := 36) (w := 65) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_77 : HasARep 77 :=
  hasARep_of_data (x := 4) (y := 0) (z := 27) (w := 72) (k := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_79 : HasARep 79 :=
  hasARep_of_data (x := 10) (y := 2) (z := 19) (w := 76) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)


lemma hasARep_of_lt_10 {n : ℕ} (hodd : Odd n) (hn : 0 < n) (h : n < 10) :
    HasARep n := by
  have hmod : n % 2 = 1 := Nat.odd_iff.mp hodd
  revert hodd hn hmod
  interval_cases n <;> intro hodd hn hmod
  · exact (lt_irrefl 0 hn).elim
  · exact hasARep_one
  · cases hmod
  · exact hasARep_three
  · cases hmod
  · exact hasARep_five
  · cases hmod
  · exact hasARep_seven
  · cases hmod
  · exact hasARep_nine

lemma hasARep_of_lt_80 {n : ℕ} (hodd : Odd n) (hn : 0 < n) (h : n < 80) :
    HasARep n := by
  have hmod : n % 2 = 1 := Nat.odd_iff.mp hodd
  revert hodd hn hmod
  interval_cases n <;> intro hodd hn hmod
  · exact (lt_irrefl 0 hn).elim
  · exact hasARep_one
  · cases hmod
  · exact hasARep_three
  · cases hmod
  · exact hasARep_five
  · cases hmod
  · exact hasARep_seven
  · cases hmod
  · exact hasARep_nine
  · cases hmod
  · exact hasARep_11
  · cases hmod
  · exact hasARep_13
  · cases hmod
  · exact hasARep_15
  · cases hmod
  · exact hasARep_17
  · cases hmod
  · exact hasARep_19
  · cases hmod
  · exact hasARep_21
  · cases hmod
  · exact hasARep_23
  · cases hmod
  · exact hasARep_25
  · cases hmod
  · exact hasARep_27
  · cases hmod
  · exact hasARep_29
  · cases hmod
  · exact hasARep_31
  · cases hmod
  · exact hasARep_33
  · cases hmod
  · exact hasARep_35
  · cases hmod
  · exact hasARep_37
  · cases hmod
  · exact hasARep_39
  · cases hmod
  · exact hasARep_41
  · cases hmod
  · exact hasARep_43
  · cases hmod
  · exact hasARep_45
  · cases hmod
  · exact hasARep_47
  · cases hmod
  · exact hasARep_49
  · cases hmod
  · exact hasARep_51
  · cases hmod
  · exact hasARep_53
  · cases hmod
  · exact hasARep_55
  · cases hmod
  · exact hasARep_57
  · cases hmod
  · exact hasARep_59
  · cases hmod
  · exact hasARep_61
  · cases hmod
  · exact hasARep_63
  · cases hmod
  · exact hasARep_65
  · cases hmod
  · exact hasARep_67
  · cases hmod
  · exact hasARep_69
  · cases hmod
  · exact hasARep_71
  · cases hmod
  · exact hasARep_73
  · cases hmod
  · exact hasARep_75
  · cases hmod
  · exact hasARep_77
  · cases hmod
  · exact hasARep_79


lemma hasARep_81 : HasARep 81 :=
  hasARep_of_data (x := 1) (y := 0) (z := 28) (w := 76) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_83 : HasARep 83 :=
  hasARep_of_data (x := 2) (y := 0) (z := 18) (w := 81) (k := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_85 : HasARep 85 :=
  hasARep_of_data (x := 4) (y := 0) (z := 45) (w := 72) (k := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_87 : HasARep 87 :=
  hasARep_of_data (x := 2) (y := 0) (z := 13) (w := 86) (k := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_89 : HasARep 89 :=
  hasARep_of_data (x := 8) (y := 0) (z := 36) (w := 81) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_91 : HasARep 91 :=
  hasARep_of_data (x := 10) (y := 2) (z := 16) (w := 89) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_93 : HasARep 93 :=
  hasARep_of_data (x := 4) (y := 0) (z := 13) (w := 92) (k := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_95 : HasARep 95 :=
  hasARep_of_data (x := 20) (y := 4) (z := 47) (w := 80) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_97 : HasARep 97 :=
  hasARep_of_data (x := 16) (y := 0) (z := 63) (w := 72) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_99 : HasARep 99 :=
  hasARep_of_data (x := 1) (y := 0) (z := 14) (w := 98) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_101 : HasARep 101 :=
  hasARep_of_data (x := 16) (y := 0) (z := 12) (w := 99) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_103 : HasARep 103 :=
  hasARep_of_data (x := 20) (y := 4) (z := 28) (w := 97) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_105 : HasARep 105 :=
  hasARep_of_data (x := 1) (y := 0) (z := 32) (w := 100) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_107 : HasARep 107 :=
  hasARep_of_data (x := 10) (y := 2) (z := 23) (w := 104) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_109 : HasARep 109 :=
  hasARep_of_data (x := 8) (y := 0) (z := 51) (w := 96) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_111 : HasARep 111 :=
  hasARep_of_data (x := 2) (y := 0) (z := 46) (w := 101) (k := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_113 : HasARep 113 :=
  hasARep_of_data (x := 4) (y := 0) (z := 33) (w := 108) (k := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_115 : HasARep 115 :=
  hasARep_of_data (x := 2) (y := 0) (z := 15) (w := 114) (k := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_117 : HasARep 117 :=
  hasARep_of_data (x := 4) (y := 0) (z := 77) (w := 88) (k := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_119 : HasARep 119 :=
  hasARep_of_data (x := 2) (y := 0) (z := 66) (w := 99) (k := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_121 : HasARep 121 :=
  hasARep_of_data (x := 4) (y := 0) (z := 15) (w := 120) (k := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_123 : HasARep 123 :=
  hasARep_of_data (x := 2) (y := 0) (z := 22) (w := 121) (k := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_125 : HasARep 125 :=
  hasARep_of_data (x := 80) (y := 16) (z := 35) (w := 88) (k := 6)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_127 : HasARep 127 :=
  hasARep_of_data (x := 10) (y := 2) (z := 20) (w := 125) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_129 : HasARep 129 :=
  hasARep_of_data (x := 1) (y := 0) (z := 16) (w := 128) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_131 : HasARep 131 :=
  hasARep_of_data (x := 10) (y := 2) (z := 41) (w := 124) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_133 : HasARep 133 :=
  hasARep_of_data (x := 16) (y := 0) (z := 3) (w := 132) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_135 : HasARep 135 :=
  hasARep_of_data (x := 10) (y := 2) (z := 61) (w := 120) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_137 : HasARep 137 :=
  hasARep_of_data (x := 16) (y := 0) (z := 33) (w := 132) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_139 : HasARep 139 :=
  hasARep_of_data (x := 40) (y := 8) (z := 76) (w := 109) (k := 5)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_141 : HasARep 141 :=
  hasARep_of_data (x := 4) (y := 0) (z := 37) (w := 136) (k := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_143 : HasARep 143 :=
  hasARep_of_data (x := 10) (y := 2) (z := 32) (w := 139) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_145 : HasARep 145 :=
  hasARep_of_data (x := 1) (y := 0) (z := 60) (w := 132) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_147 : HasARep 147 :=
  hasARep_of_data (x := 1) (y := 0) (z := 38) (w := 142) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_149 : HasARep 149 :=
  hasARep_of_data (x := 4) (y := 0) (z := 24) (w := 147) (k := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_151 : HasARep 151 :=
  hasARep_of_data (x := 2) (y := 0) (z := 54) (w := 141) (k := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_153 : HasARep 153 :=
  hasARep_of_data (x := 4) (y := 0) (z := 17) (w := 152) (k := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_155 : HasARep 155 :=
  hasARep_of_data (x := 2) (y := 0) (z := 39) (w := 150) (k := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_157 : HasARep 157 :=
  hasARep_of_data (x := 10) (y := 2) (z := 64) (w := 143) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_159 : HasARep 159 :=
  hasARep_of_data (x := 10) (y := 2) (z := 29) (w := 156) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_161 : HasARep 161 :=
  hasARep_of_data (x := 1) (y := 0) (z := 72) (w := 144) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_163 : HasARep 163 :=
  hasARep_of_data (x := 1) (y := 0) (z := 18) (w := 162) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_165 : HasARep 165 :=
  hasARep_of_data (x := 8) (y := 0) (z := 56) (w := 155) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_167 : HasARep 167 :=
  hasARep_of_data (x := 10) (y := 2) (z := 56) (w := 157) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_169 : HasARep 169 :=
  hasARep_of_data (x := 16) (y := 0) (z := 9) (w := 168) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_171 : HasARep 171 :=
  hasARep_of_data (x := 2) (y := 0) (z := 26) (w := 169) (k := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_173 : HasARep 173 :=
  hasARep_of_data (x := 10) (y := 2) (z := 44) (w := 167) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_175 : HasARep 175 :=
  hasARep_of_data (x := 20) (y := 4) (z := 25) (w := 172) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_177 : HasARep 177 :=
  hasARep_of_data (x := 4) (y := 0) (z := 97) (w := 148) (k := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_179 : HasARep 179 :=
  hasARep_of_data (x := 1) (y := 0) (z := 42) (w := 174) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_181 : HasARep 181 :=
  hasARep_of_data (x := 64) (y := 0) (z := 21) (w := 168) (k := 6)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_183 : HasARep 183 :=
  hasARep_of_data (x := 2) (y := 0) (z := 19) (w := 182) (k := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_185 : HasARep 185 :=
  hasARep_of_data (x := 10) (y := 2) (z := 85) (w := 164) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_187 : HasARep 187 :=
  hasARep_of_data (x := 20) (y := 4) (z := 68) (w := 173) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_189 : HasARep 189 :=
  hasARep_of_data (x := 4) (y := 0) (z := 19) (w := 188) (k := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_191 : HasARep 191 :=
  hasARep_of_data (x := 20) (y := 4) (z := 47) (w := 184) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_193 : HasARep 193 :=
  hasARep_of_data (x := 20) (y := 4) (z := 128) (w := 143) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_195 : HasARep 195 :=
  hasARep_of_data (x := 1) (y := 0) (z := 70) (w := 182) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_197 : HasARep 197 :=
  hasARep_of_data (x := 10) (y := 2) (z := 17) (w := 196) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_199 : HasARep 199 :=
  hasARep_of_data (x := 20) (y := 4) (z := 44) (w := 193) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)


lemma hasARep_of_lt_200 {n : ℕ} (hodd : Odd n) (hn : 0 < n) (h : n < 200) :
    HasARep n := by
  have hmod : n % 2 = 1 := Nat.odd_iff.mp hodd
  revert hodd hn hmod
  interval_cases n <;> intro hodd hn hmod
  · exact (lt_irrefl 0 hn).elim
  · exact hasARep_one
  · cases hmod
  · exact hasARep_three
  · cases hmod
  · exact hasARep_five
  · cases hmod
  · exact hasARep_seven
  · cases hmod
  · exact hasARep_nine
  · cases hmod
  · exact hasARep_11
  · cases hmod
  · exact hasARep_13
  · cases hmod
  · exact hasARep_15
  · cases hmod
  · exact hasARep_17
  · cases hmod
  · exact hasARep_19
  · cases hmod
  · exact hasARep_21
  · cases hmod
  · exact hasARep_23
  · cases hmod
  · exact hasARep_25
  · cases hmod
  · exact hasARep_27
  · cases hmod
  · exact hasARep_29
  · cases hmod
  · exact hasARep_31
  · cases hmod
  · exact hasARep_33
  · cases hmod
  · exact hasARep_35
  · cases hmod
  · exact hasARep_37
  · cases hmod
  · exact hasARep_39
  · cases hmod
  · exact hasARep_41
  · cases hmod
  · exact hasARep_43
  · cases hmod
  · exact hasARep_45
  · cases hmod
  · exact hasARep_47
  · cases hmod
  · exact hasARep_49
  · cases hmod
  · exact hasARep_51
  · cases hmod
  · exact hasARep_53
  · cases hmod
  · exact hasARep_55
  · cases hmod
  · exact hasARep_57
  · cases hmod
  · exact hasARep_59
  · cases hmod
  · exact hasARep_61
  · cases hmod
  · exact hasARep_63
  · cases hmod
  · exact hasARep_65
  · cases hmod
  · exact hasARep_67
  · cases hmod
  · exact hasARep_69
  · cases hmod
  · exact hasARep_71
  · cases hmod
  · exact hasARep_73
  · cases hmod
  · exact hasARep_75
  · cases hmod
  · exact hasARep_77
  · cases hmod
  · exact hasARep_79
  · cases hmod
  · exact hasARep_81
  · cases hmod
  · exact hasARep_83
  · cases hmod
  · exact hasARep_85
  · cases hmod
  · exact hasARep_87
  · cases hmod
  · exact hasARep_89
  · cases hmod
  · exact hasARep_91
  · cases hmod
  · exact hasARep_93
  · cases hmod
  · exact hasARep_95
  · cases hmod
  · exact hasARep_97
  · cases hmod
  · exact hasARep_99
  · cases hmod
  · exact hasARep_101
  · cases hmod
  · exact hasARep_103
  · cases hmod
  · exact hasARep_105
  · cases hmod
  · exact hasARep_107
  · cases hmod
  · exact hasARep_109
  · cases hmod
  · exact hasARep_111
  · cases hmod
  · exact hasARep_113
  · cases hmod
  · exact hasARep_115
  · cases hmod
  · exact hasARep_117
  · cases hmod
  · exact hasARep_119
  · cases hmod
  · exact hasARep_121
  · cases hmod
  · exact hasARep_123
  · cases hmod
  · exact hasARep_125
  · cases hmod
  · exact hasARep_127
  · cases hmod
  · exact hasARep_129
  · cases hmod
  · exact hasARep_131
  · cases hmod
  · exact hasARep_133
  · cases hmod
  · exact hasARep_135
  · cases hmod
  · exact hasARep_137
  · cases hmod
  · exact hasARep_139
  · cases hmod
  · exact hasARep_141
  · cases hmod
  · exact hasARep_143
  · cases hmod
  · exact hasARep_145
  · cases hmod
  · exact hasARep_147
  · cases hmod
  · exact hasARep_149
  · cases hmod
  · exact hasARep_151
  · cases hmod
  · exact hasARep_153
  · cases hmod
  · exact hasARep_155
  · cases hmod
  · exact hasARep_157
  · cases hmod
  · exact hasARep_159
  · cases hmod
  · exact hasARep_161
  · cases hmod
  · exact hasARep_163
  · cases hmod
  · exact hasARep_165
  · cases hmod
  · exact hasARep_167
  · cases hmod
  · exact hasARep_169
  · cases hmod
  · exact hasARep_171
  · cases hmod
  · exact hasARep_173
  · cases hmod
  · exact hasARep_175
  · cases hmod
  · exact hasARep_177
  · cases hmod
  · exact hasARep_179
  · cases hmod
  · exact hasARep_181
  · cases hmod
  · exact hasARep_183
  · cases hmod
  · exact hasARep_185
  · cases hmod
  · exact hasARep_187
  · cases hmod
  · exact hasARep_189
  · cases hmod
  · exact hasARep_191
  · cases hmod
  · exact hasARep_193
  · cases hmod
  · exact hasARep_195
  · cases hmod
  · exact hasARep_197
  · cases hmod
  · exact hasARep_199


/- The family `Q(t)` and the key criterion for sums of two squares -/

/-- `Q(t) = (4^t + 1)² + ((4^t - 1)/3)²`. -/
def QT (t : ℕ) : ℕ :=
  (4 ^ t + 1) ^ 2 + ((4 ^ t - 1) / 3) ^ 2

lemma QT_zero : QT 0 = 4 := by
  simp [QT]

lemma QT_one : QT 1 = 26 := by
  simp [QT]

lemma QT_two : QT 2 = 314 := by
  simp [QT]

lemma QT_pos (t : ℕ) : 0 < QT t := by
  unfold QT
  have : 0 < (4 ^ t + 1) ^ 2 := by
    exact Nat.pow_pos (Nat.succ_pos _)
  exact lt_of_lt_of_le this (Nat.le_add_right _ _)

lemma family_sq_sum (t r : ℕ) :
    ((4 ^ t + 1) * 2 ^ r) ^ 2 + (((4 ^ t - 1) / 3) * 2 ^ r) ^ 2 = QT t * 4 ^ r := by
  unfold QT
  have hpow : (2 ^ r) ^ 2 = 4 ^ r := pow2_sq r
  calc
    ((4 ^ t + 1) * 2 ^ r) ^ 2 + (((4 ^ t - 1) / 3) * 2 ^ r) ^ 2
        = (4 ^ t + 1) ^ 2 * (2 ^ r) ^ 2 + ((4 ^ t - 1) / 3) ^ 2 * (2 ^ r) ^ 2 := by ring
    _ = ((4 ^ t + 1) ^ 2 + ((4 ^ t - 1) / 3) ^ 2) * (2 ^ r) ^ 2 := by ring
    _ = QT t * 4 ^ r := by rw [hpow]; rfl

lemma hasARep_of_isSumTwoSq_family {n t r : ℕ}
    (hx : (4 ^ t + 1) * 2 ^ r ≤ n)
    (hle : QT t * 4 ^ r ≤ n ^ 2)
    (h : IsSumTwoSq (n ^ 2 - QT t * 4 ^ r)) :
    HasARep n := by
  have hxy : ((4 ^ t + 1) * 2 ^ r) ^ 2 + (((4 ^ t - 1) / 3) * 2 ^ r) ^ 2 ≤ n ^ 2 := by
    rwa [family_sq_sum]
  refine hasARep_of_family hx hxy ?_
  rwa [Nat.sub_sub, family_sq_sum]

lemma not_isSumTwoSq_of_mod4_eq_three {m : ℕ} (h : m % 4 = 3) : ¬ IsSumTwoSq m :=
  not_isSumTwoSq_of_mod4 h

lemma even_padicValNat_of_isSumTwoSq {m q : ℕ}
    (h : IsSumTwoSq m) (hq : q ∈ m.primeFactors) (hq4 : q % 4 = 3) :
    Even (padicValNat q m) :=
  (isSumTwoSq_iff m).mp h q hq hq4

lemma padicValNat_eq_one_of_lt_sq {m q n : ℕ} [Fact q.Prime]
    (hdiv : q ∣ m) (hmpos : 0 < m) (hmlt : m < n ^ 2) (hqn : n ≤ q) :
    padicValNat q m = 1 := by
  have hm0 : m ≠ 0 := hmpos.ne'
  have h1 : 1 ≤ padicValNat q m := one_le_padicValNat_of_dvd hm0 hdiv
  have hn2 : n ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hqn 2
  have not2 : ¬ q ^ 2 ∣ m := by
    intro hd
    exact not_le_of_gt hmlt (le_trans hn2 (Nat.le_of_dvd hmpos hd))
  have hlt2 : padicValNat q m < 2 := by
    rw [← not_le]
    intro hge
    exact not2 ((padicValNat_dvd_iff_le hm0).mpr hge)
  omega

lemma mul_mod4_three_of_one {q s : ℕ} (hq : q % 4 = 3) (hqs : (q * s) % 4 = 1) :
    s % 4 = 3 := by
  have : ((q % 4) * (s % 4)) % 4 = 1 := by
    rwa [← Nat.mul_mod]
  rw [hq] at this
  have hs4 : s % 4 = 0 ∨ s % 4 = 1 ∨ s % 4 = 2 ∨ s % 4 = 3 := by omega
  rcases hs4 with h | h | h | h <;> simp [h] at this
  exact h

/-- An odd number `≡ 3 (mod 4)` has some prime factor `≡ 3 (mod 4)` of odd valuation. -/
lemma exists_odd_val_of_mod4_eq_three {s : ℕ} (_hspos : 0 < s) (hs4 : s % 4 = 3) :
    ∃ p, p.Prime ∧ p % 4 = 3 ∧ p ∣ s ∧ Odd (padicValNat p s) := by
  by_contra hnone
  push_neg at hnone
  have hS : IsSumTwoSq s := by
    apply (isSumTwoSq_iff s).mpr
    intro p hpmem hp4
    have hp : p.Prime := (Nat.mem_primeFactors.mp hpmem).1
    have hpd : p ∣ s := (Nat.mem_primeFactors.mp hpmem).2.1
    exact Nat.not_odd_iff_even.mp (hnone p hp hp4 hpd)
  exact not_isSumTwoSq_of_mod4 hs4 hS

/--
If `m < n²` is odd and `m ≡ 1 (mod 4)`, then `m` is a sum of two squares if and only if
every prime `p ≡ 3 (mod 4)` with `p < n` has even `p`-adic valuation on `m`.
-/
lemma isSumTwoSq_iff_small_primes {m n : ℕ}
    (hmodd : Odd m) (hm4 : m % 4 = 1) (hmlt : m < n ^ 2) :
    IsSumTwoSq m ↔
      ∀ q : ℕ, q.Prime → q % 4 = 3 → q < n → Even (padicValNat q m) := by
  constructor
  · intro h q hq hq4 _hqn
    by_cases hdiv : q ∣ m
    · have hm0 : m ≠ 0 := (Odd.pos hmodd).ne'
      exact even_padicValNat_of_isSumTwoSq h
        (Nat.mem_primeFactors.mpr ⟨hq, hdiv, hm0⟩) hq4
    · rw [padicValNat.eq_zero_of_not_dvd hdiv]
      exact Even.zero
  · intro H
    apply (isSumTwoSq_iff m).mpr
    intro q hqmem hq4
    have hq : q.Prime := (Nat.mem_primeFactors.mp hqmem).1
    have hdiv : q ∣ m := (Nat.mem_primeFactors.mp hqmem).2.1
    by_cases hqn : q < n
    · exact H q hq hq4 hqn
    · have hq_ge : n ≤ q := le_of_not_gt hqn
      have : Fact q.Prime := ⟨hq⟩
      have hmpos : 0 < m := Odd.pos hmodd
      have hval : padicValNat q m = 1 :=
        padicValNat_eq_one_of_lt_sq hdiv hmpos hmlt hq_ge
      obtain ⟨s, hs⟩ : ∃ s, m = q * s := hdiv
      have hqpos : 0 < q := hq.pos
      have hs_lt : s < n := by
        have h1 : q * s < n * n := by
          calc q * s = m := hs.symm
            _ < n ^ 2 := hmlt
            _ = n * n := pow_two n
        have h2 : n * n ≤ q * n := by
          rw [mul_comm q]; exact Nat.mul_le_mul_left n hq_ge
        have : q * s < q * n := lt_of_lt_of_le h1 h2
        exact (Nat.mul_lt_mul_left hqpos).mp this
      have hs_mod : s % 4 = 3 :=
        mul_mod4_three_of_one hq4 (by rw [← hs]; exact hm4)
      have hspos : 0 < s := by
        have : 0 < q * s := hs ▸ hmpos
        exact (Nat.pos_of_mul_pos_left this)
      obtain ⟨p, hp, hp4, hpd, hpodd⟩ := exists_odd_val_of_mod4_eq_three hspos hs_mod
      have hp_lt : p < n := lt_of_le_of_lt (Nat.le_of_dvd hspos hpd) hs_lt
      have hpq : p ≠ q := by
        intro heq
        have hqq : q ^ 2 ∣ m := by
          rw [hs, pow_two]
          have : q ∣ s := by rwa [← heq]
          exact mul_dvd_mul_left q this
        have : Fact q.Prime := ⟨hq⟩
        have : 2 ≤ padicValNat q m := (padicValNat_dvd_iff_le hmpos.ne').mp hqq
        omega
      have : Fact p.Prime := ⟨hp⟩
      have : Fact q.Prime := ⟨hq⟩
      have hvalp : padicValNat p m = padicValNat p s := by
        rw [hs, padicValNat.mul hqpos.ne' hspos.ne', padicValNat_primes hpq, zero_add]
      have hOdd : Odd (padicValNat p m) := by rwa [hvalp]
      have hEven : Even (padicValNat p m) := H p hp hp4 hp_lt
      exact absurd hOdd (Nat.not_odd_iff_even.mpr hEven)


/- Infinite families -/

/-- `n = 2 a² + 1` always works with `k = 0`, since `n² - 1 = 4 a² (a² + 1)`
and both `a²` and `a² + 1 = a² + 1²` are sums of two squares. -/
lemma hasARep_two_sq_add_one (a : ℕ) : HasARep (2 * a ^ 2 + 1) := by
  set n := 2 * a ^ 2 + 1
  have hn : 1 ≤ n := Nat.succ_le_succ (Nat.zero_le _)
  have hrem : IsSumTwoSq (n ^ 2 - 1) := by
    have hcalc : n ^ 2 - 1 = 4 * a ^ 2 * (a ^ 2 + 1) := by
      have hle : 1 ≤ n ^ 2 := one_le_pow 2 n (Nat.succ_pos _)
      rw [Nat.sub_eq_iff_eq_add hle]
      ring
    rw [hcalc]
    refine isSumTwoSq_mul (isSumTwoSq_mul ⟨2, 0, by norm_num⟩ ⟨a, 0, by ring⟩)
      ⟨a, 1, by ring⟩
  exact hasARep_of_isSumTwoSq_k0 hn hrem

lemma rem_lt_sq {n c : ℕ} (hc : 0 < c) (hle : c ≤ n ^ 2) : n ^ 2 - c < n ^ 2 :=
  Nat.sub_lt (lt_of_lt_of_le hc hle) hc

lemma isSumTwoSq_two : IsSumTwoSq 2 := ⟨1, 1, by norm_num⟩

lemma isSumTwoSq_pow2 (k : ℕ) : IsSumTwoSq (2 ^ k) := by
  induction k with
  | zero => exact isSumTwoSq_one
  | succ k ih =>
    rw [pow_succ]
    exact isSumTwoSq_mul ih isSumTwoSq_two

lemma hasARep_pos_of_lt {N : ℕ}
    (hsmall : ∀ m, Odd m → 0 < m → m < N → HasARep m)
    (hlarge : ∀ m, Odd m → N ≤ m → HasARep m) :
    ∀ n, 0 < n → HasARep n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases he : Even n
    · exact hasARep_of_lt_of_even n hn (fun m hm hm0 => ih m hm hm0) he
    · have hodd : Odd n := Nat.not_even_iff_odd.mp he
      by_cases hN : n < N
      · exact hsmall n hodd hn hN
      · exact hlarge n hodd (le_of_not_gt hN)

lemma hasARep_of_lt_of_odd_small {n : ℕ} (hodd : Odd n) (hn : 0 < n) (h : n < 200) :
    HasARep n :=
  hasARep_of_lt_200 hodd hn h


/- More infinite families from polynomial identities -/

/-- `n = m² + 2` works with `k = 1`, since `n² - 4 = m²(m² + 4) = m²(m² + 2²)`. -/
lemma hasARep_sq_add_two (m : ℕ) : HasARep (m ^ 2 + 2) := by
  set n := m ^ 2 + 2
  have hx : 2 ≤ n := by
    have : 2 ≤ m ^ 2 + 2 := Nat.le_add_left _ _
    exact this
  have hrem : IsSumTwoSq (n ^ 2 - 4) := by
    have hle : 4 ≤ n ^ 2 := by
      have : 2 ≤ n := hx
      exact Nat.pow_le_pow_left this 2
    have hcalc : n ^ 2 - 4 = m ^ 2 * (m ^ 2 + 4) := by
      rw [Nat.sub_eq_iff_eq_add hle]
      ring
    rw [hcalc]
    exact isSumTwoSq_mul ⟨m, 0, by ring⟩ ⟨m, 2, by ring⟩
  exact hasARep_of_isSumTwoSq_pow2 (k := 1) (by omega) hrem

/-- `n = m² + 5` works with `k = 2`, since `n² - 16 = (m² + 1)(m² + 9)`. -/
lemma hasARep_sq_add_five (m : ℕ) : HasARep (m ^ 2 + 5) := by
  set n := m ^ 2 + 5
  have hx : 4 ≤ n := by
    have : 4 ≤ m ^ 2 + 5 := by omega
    exact this
  have hrem : IsSumTwoSq (n ^ 2 - 16) := by
    have hle : 16 ≤ n ^ 2 := by
      have : 4 ≤ n := hx
      exact Nat.pow_le_pow_left this 2
    have hcalc : n ^ 2 - 16 = (m ^ 2 + 1) * (m ^ 2 + 9) := by
      rw [Nat.sub_eq_iff_eq_add hle]
      ring
    rw [hcalc]
    exact isSumTwoSq_mul ⟨m, 1, by ring⟩ ⟨m, 3, by ring⟩
  exact hasARep_of_isSumTwoSq_pow2 (k := 2) (by omega) hrem

/-- If `k` is odd then `n = m² + 2^k` works with this same `k`,
because `n² - 4^k = m² (m² + 2^{k+1})` and `k+1` even so `m² + 2^{k+1}` is a sum of two squares. -/
lemma hasARep_sq_add_pow2_odd (m k : ℕ) (hodd : Odd k) : HasARep (m ^ 2 + 2 ^ k) := by
  set n := m ^ 2 + 2 ^ k
  have hkpos : 0 < k := Odd.pos hodd
  have hx : 2 ^ k ≤ n := Nat.le_add_left _ _
  have hrem : IsSumTwoSq (n ^ 2 - 4 ^ k) := by
    have h4 : 4 ^ k = (2 ^ k) ^ 2 := pow2_sq k |>.symm
    have hle : 4 ^ k ≤ n ^ 2 := by
      rw [h4]
      exact Nat.pow_le_pow_left hx 2
    have hcalc : n ^ 2 - 4 ^ k = m ^ 2 * (m ^ 2 + 2 ^ (k + 1)) := by
      rw [Nat.sub_eq_iff_eq_add hle, h4]
      ring
    rw [hcalc]
    refine isSumTwoSq_mul ⟨m, 0, by ring⟩ ?_
    -- `k` odd ⇒ `k+1` even, write `k+1 = 2 ℓ`
    obtain ⟨ℓ, hℓ⟩ := hodd
    have : k + 1 = (ℓ + 1) * 2 := by omega
    have hpow : 2 ^ (k + 1) = (2 ^ (ℓ + 1)) ^ 2 := by
      rw [this, pow_mul]
    refine ⟨m, 2 ^ (ℓ + 1), ?_⟩
    rw [hpow]
  exact hasARep_of_isSumTwoSq_pow2 hx hrem

/-- `n = 2 m² + 15` works with `t = 1`, `r = 1`: remainder is `(2m² + 11)² + (4m)²`. -/
lemma hasARep_two_sq_add_fifteen (m : ℕ) : HasARep (2 * m ^ 2 + 15) := by
  set n := 2 * m ^ 2 + 15
  have hx : 5 * 2 ^ 1 ≤ n := by
    have : 10 ≤ 2 * m ^ 2 + 15 := by omega
    exact this
  have hle : 26 * 4 ^ 1 ≤ n ^ 2 := by
    have : 104 ≤ n ^ 2 := by
      have hn : 15 ≤ n := by omega
      have : 15 ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
      exact le_trans (by norm_num) this
    exact this
  have hrem : IsSumTwoSq (n ^ 2 - 26 * 4 ^ 1) := by
    have hle' : 104 ≤ n ^ 2 := hle
    have hcalc : n ^ 2 - 104 = (2 * m ^ 2 + 11) ^ 2 + (4 * m) ^ 2 := by
      rw [Nat.sub_eq_iff_eq_add hle']
      ring
    refine ⟨2 * m ^ 2 + 11, 4 * m, ?_⟩
    simpa using hcalc.symm
  exact hasARep_of_isSumTwoSq_t1 (r := 1) hx hle hrem

/-- If `n ≥ 6 · 2^r` and the `t = 1` remainder is a sum of two squares, we are done. -/
lemma hasARep_of_t1_ge (n r : ℕ) (hge : 6 * 2 ^ r ≤ n)
    (h : IsSumTwoSq (n ^ 2 - 26 * 4 ^ r)) : HasARep n := by
  have hx : 5 * 2 ^ r ≤ n :=
    le_trans (Nat.mul_le_mul_right _ (by decide : 5 ≤ 6)) hge
  have hle : 26 * 4 ^ r ≤ n ^ 2 := by
    have h36 : 26 * 4 ^ r ≤ 36 * 4 ^ r := Nat.mul_le_mul_right _ (by decide)
    have hsq : 36 * 4 ^ r = (6 * 2 ^ r) ^ 2 := by
      have : (6 * 2 ^ r) ^ 2 = 36 * (2 ^ r) ^ 2 := by ring
      rw [this, pow2_sq]
    have : (6 * 2 ^ r) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hge 2
    exact le_trans h36 (hsq ▸ this)
  exact hasARep_of_isSumTwoSq_t1 hx hle h

/-- If `QT t ≤ B ^ 2` and `B * 2 ^ r ≤ n`, a good remainder gives `HasARep n`. -/
lemma hasARep_of_family_bound (n t r B : ℕ)
    (hB : QT t ≤ B ^ 2) (hge : B * 2 ^ r ≤ n)
    (h : IsSumTwoSq (n ^ 2 - QT t * 4 ^ r)) : HasARep n := by
  have hx : (4 ^ t + 1) * 2 ^ r ≤ n := by
    have hx0 : 4 ^ t + 1 ≤ B := by
      have : (4 ^ t + 1) ^ 2 ≤ QT t := by
        unfold QT
        exact Nat.le_add_right _ _
      have : (4 ^ t + 1) ^ 2 ≤ B ^ 2 := le_trans this hB
      exact (Nat.pow_le_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).1 this
    exact le_trans (Nat.mul_le_mul_right _ hx0) hge
  have hle : QT t * 4 ^ r ≤ n ^ 2 := by
    have h1 : QT t * 4 ^ r ≤ B ^ 2 * 4 ^ r := Nat.mul_le_mul_right _ hB
    have h2 : B ^ 2 * 4 ^ r = (B * 2 ^ r) ^ 2 := by
      have : (B * 2 ^ r) ^ 2 = B ^ 2 * (2 ^ r) ^ 2 := by ring
      rw [this, pow2_sq]
    have h3 : (B * 2 ^ r) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hge 2
    exact le_trans h1 (h2 ▸ h3)
  exact hasARep_of_isSumTwoSq_family hx hle h

/-- If `n ≥ 18 · 2^r` and the `t = 2` remainder is a sum of two squares, we are done. -/
lemma hasARep_of_t2_ge (n r : ℕ) (hge : 18 * 2 ^ r ≤ n)
    (h : IsSumTwoSq (n ^ 2 - 314 * 4 ^ r)) : HasARep n := by
  have hx : 17 * 2 ^ r ≤ n :=
    le_trans (Nat.mul_le_mul_right _ (by decide : 17 ≤ 18)) hge
  have hle : 314 * 4 ^ r ≤ n ^ 2 := by
    have h324 : 314 * 4 ^ r ≤ 324 * 4 ^ r := Nat.mul_le_mul_right _ (by decide)
    have hsq : 324 * 4 ^ r = (18 * 2 ^ r) ^ 2 := by
      have : (18 * 2 ^ r) ^ 2 = 324 * (2 ^ r) ^ 2 := by ring
      rw [this, pow2_sq]
    have : (18 * 2 ^ r) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hge 2
    exact le_trans h324 (hsq ▸ this)
  exact hasARep_of_isSumTwoSq_t2 hx hle h

lemma hasARep_1537 : HasARep 1537 :=
  hasARep_of_data (x := 16) (y := 0) (z := 348) (w := 1497) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1539 : HasARep 1539 :=
  hasARep_of_data (x := 10) (y := 2) (z := 776) (w := 1329) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1541 : HasARep 1541 :=
  hasARep_of_data (x := 16) (y := 0) (z := 123) (w := 1536) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1543 : HasARep 1543 :=
  hasARep_of_data (x := 10) (y := 2) (z := 472) (w := 1469) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1545 : HasARep 1545 :=
  hasARep_of_data (x := 1) (y := 0) (z := 200) (w := 1532) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1547 : HasARep 1547 :=
  hasARep_of_data (x := 40) (y := 8) (z := 211) (w := 1532) (k := 5)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1549 : HasARep 1549 :=
  hasARep_of_data (x := 512) (y := 0) (z := 456) (w := 1389) (k := 9)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1551 : HasARep 1551 :=
  hasARep_of_data (x := 2) (y := 0) (z := 229) (w := 1534) (k := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1553 : HasARep 1553 :=
  hasARep_of_data (x := 4) (y := 0) (z := 492) (w := 1473) (k := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1555 : HasARep 1555 :=
  hasARep_of_data (x := 2) (y := 0) (z := 705) (w := 1386) (k := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1557 : HasARep 1557 :=
  hasARep_of_data (x := 8) (y := 0) (z := 176) (w := 1547) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1559 : HasARep 1559 :=
  hasARep_of_data (x := 10) (y := 2) (z := 176) (w := 1549) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1561 : HasARep 1561 :=
  hasARep_of_data (x := 4) (y := 0) (z := 201) (w := 1548) (k := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1563 : HasARep 1563 :=
  hasARep_of_data (x := 10) (y := 2) (z := 624) (w := 1433) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1565 : HasARep 1565 :=
  hasARep_of_data (x := 8) (y := 0) (z := 660) (w := 1419) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1567 : HasARep 1567 :=
  hasARep_of_data (x := 20) (y := 4) (z := 208) (w := 1553) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1569 : HasARep 1569 :=
  hasARep_of_data (x := 1) (y := 0) (z := 56) (w := 1568) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1571 : HasARep 1571 :=
  hasARep_of_data (x := 10) (y := 2) (z := 524) (w := 1481) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1573 : HasARep 1573 :=
  hasARep_of_data (x := 1024) (y := 0) (z := 483) (w := 1092) (k := 10)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1575 : HasARep 1575 :=
  hasARep_of_data (x := 20) (y := 4) (z := 95) (w := 1572) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1577 : HasARep 1577 :=
  hasARep_of_data (x := 20) (y := 4) (z := 167) (w := 1568) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1579 : HasARep 1579 :=
  hasARep_of_data (x := 20) (y := 4) (z := 136) (w := 1573) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1581 : HasARep 1581 :=
  hasARep_of_data (x := 16) (y := 0) (z := 301) (w := 1552) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1583 : HasARep 1583 :=
  hasARep_of_data (x := 10) (y := 2) (z := 112) (w := 1579) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1585 : HasARep 1585 :=
  hasARep_of_data (x := 64) (y := 0) (z := 273) (w := 1560) (k := 6)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1587 : HasARep 1587 :=
  hasARep_of_data (x := 1) (y := 0) (z := 302) (w := 1558) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1589 : HasARep 1589 :=
  hasARep_of_data (x := 32) (y := 0) (z := 156) (w := 1581) (k := 5)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1591 : HasARep 1591 :=
  hasARep_of_data (x := 20) (y := 4) (z := 217) (w := 1576) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1593 : HasARep 1593 :=
  hasARep_of_data (x := 8) (y := 0) (z := 281) (w := 1568) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1595 : HasARep 1595 :=
  hasARep_of_data (x := 10) (y := 2) (z := 736) (w := 1415) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1597 : HasARep 1597 :=
  hasARep_of_data (x := 32) (y := 0) (z := 579) (w := 1488) (k := 5)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1599 : HasARep 1599 :=
  hasARep_of_data (x := 2) (y := 0) (z := 806) (w := 1381) (k := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1601 : HasARep 1601 :=
  hasARep_of_data (x := 1) (y := 0) (z := 360) (w := 1560) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1603 : HasARep 1603 :=
  hasARep_of_data (x := 1) (y := 0) (z := 282) (w := 1578) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1605 : HasARep 1605 :=
  hasARep_of_data (x := 4) (y := 0) (z := 80) (w := 1603) (k := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1607 : HasARep 1607 :=
  hasARep_of_data (x := 10) (y := 2) (z := 533) (w := 1516) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1609 : HasARep 1609 :=
  hasARep_of_data (x := 128) (y := 0) (z := 159) (w := 1596) (k := 7)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1611 : HasARep 1611 :=
  hasARep_of_data (x := 2) (y := 0) (z := 406) (w := 1559) (k := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1613 : HasARep 1613 :=
  hasARep_of_data (x := 16) (y := 0) (z := 288) (w := 1587) (k := 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1615 : HasARep 1615 :=
  hasARep_of_data (x := 10) (y := 2) (z := 436) (w := 1555) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1617 : HasARep 1617 :=
  hasARep_of_data (x := 1) (y := 0) (z := 788) (w := 1412) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1619 : HasARep 1619 :=
  hasARep_of_data (x := 1) (y := 0) (z := 234) (w := 1602) (k := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1621 : HasARep 1621 :=
  hasARep_of_data (x := 8) (y := 0) (z := 636) (w := 1491) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1623 : HasARep 1623 :=
  hasARep_of_data (x := 2) (y := 0) (z := 205) (w := 1610) (k := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1625 : HasARep 1625 :=
  hasARep_of_data (x := 4) (y := 0) (z := 753) (w := 1440) (k := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1627 : HasARep 1627 :=
  hasARep_of_data (x := 2) (y := 0) (z := 57) (w := 1626) (k := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1629 : HasARep 1629 :=
  hasARep_of_data (x := 8) (y := 0) (z := 704) (w := 1469) (k := 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1631 : HasARep 1631 :=
  hasARep_of_data (x := 40) (y := 8) (z := 1121) (w := 1184) (k := 5)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1633 : HasARep 1633 :=
  hasARep_of_data (x := 4) (y := 0) (z := 57) (w := 1632) (k := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_1635 : HasARep 1635 :=
  hasARep_of_data (x := 40) (y := 8) (z := 1131) (w := 1180) (k := 5)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)

lemma hasARep_of_1536_1636 {n : ℕ} (hodd : Odd n) (hlo : 1536 ≤ n) (hhi : n < 1636) :
    HasARep n := by
  have hmod : n % 2 = 1 := Nat.odd_iff.mp hodd
  have hdiff : n - 1536 < 100 := by omega
  interval_cases h : n - 1536
  · have hn : n = 1536 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1537 := by omega
    rw [hn]; exact hasARep_1537
  · have hn : n = 1538 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1539 := by omega
    rw [hn]; exact hasARep_1539
  · have hn : n = 1540 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1541 := by omega
    rw [hn]; exact hasARep_1541
  · have hn : n = 1542 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1543 := by omega
    rw [hn]; exact hasARep_1543
  · have hn : n = 1544 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1545 := by omega
    rw [hn]; exact hasARep_1545
  · have hn : n = 1546 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1547 := by omega
    rw [hn]; exact hasARep_1547
  · have hn : n = 1548 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1549 := by omega
    rw [hn]; exact hasARep_1549
  · have hn : n = 1550 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1551 := by omega
    rw [hn]; exact hasARep_1551
  · have hn : n = 1552 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1553 := by omega
    rw [hn]; exact hasARep_1553
  · have hn : n = 1554 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1555 := by omega
    rw [hn]; exact hasARep_1555
  · have hn : n = 1556 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1557 := by omega
    rw [hn]; exact hasARep_1557
  · have hn : n = 1558 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1559 := by omega
    rw [hn]; exact hasARep_1559
  · have hn : n = 1560 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1561 := by omega
    rw [hn]; exact hasARep_1561
  · have hn : n = 1562 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1563 := by omega
    rw [hn]; exact hasARep_1563
  · have hn : n = 1564 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1565 := by omega
    rw [hn]; exact hasARep_1565
  · have hn : n = 1566 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1567 := by omega
    rw [hn]; exact hasARep_1567
  · have hn : n = 1568 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1569 := by omega
    rw [hn]; exact hasARep_1569
  · have hn : n = 1570 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1571 := by omega
    rw [hn]; exact hasARep_1571
  · have hn : n = 1572 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1573 := by omega
    rw [hn]; exact hasARep_1573
  · have hn : n = 1574 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1575 := by omega
    rw [hn]; exact hasARep_1575
  · have hn : n = 1576 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1577 := by omega
    rw [hn]; exact hasARep_1577
  · have hn : n = 1578 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1579 := by omega
    rw [hn]; exact hasARep_1579
  · have hn : n = 1580 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1581 := by omega
    rw [hn]; exact hasARep_1581
  · have hn : n = 1582 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1583 := by omega
    rw [hn]; exact hasARep_1583
  · have hn : n = 1584 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1585 := by omega
    rw [hn]; exact hasARep_1585
  · have hn : n = 1586 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1587 := by omega
    rw [hn]; exact hasARep_1587
  · have hn : n = 1588 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1589 := by omega
    rw [hn]; exact hasARep_1589
  · have hn : n = 1590 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1591 := by omega
    rw [hn]; exact hasARep_1591
  · have hn : n = 1592 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1593 := by omega
    rw [hn]; exact hasARep_1593
  · have hn : n = 1594 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1595 := by omega
    rw [hn]; exact hasARep_1595
  · have hn : n = 1596 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1597 := by omega
    rw [hn]; exact hasARep_1597
  · have hn : n = 1598 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1599 := by omega
    rw [hn]; exact hasARep_1599
  · have hn : n = 1600 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1601 := by omega
    rw [hn]; exact hasARep_1601
  · have hn : n = 1602 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1603 := by omega
    rw [hn]; exact hasARep_1603
  · have hn : n = 1604 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1605 := by omega
    rw [hn]; exact hasARep_1605
  · have hn : n = 1606 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1607 := by omega
    rw [hn]; exact hasARep_1607
  · have hn : n = 1608 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1609 := by omega
    rw [hn]; exact hasARep_1609
  · have hn : n = 1610 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1611 := by omega
    rw [hn]; exact hasARep_1611
  · have hn : n = 1612 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1613 := by omega
    rw [hn]; exact hasARep_1613
  · have hn : n = 1614 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1615 := by omega
    rw [hn]; exact hasARep_1615
  · have hn : n = 1616 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1617 := by omega
    rw [hn]; exact hasARep_1617
  · have hn : n = 1618 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1619 := by omega
    rw [hn]; exact hasARep_1619
  · have hn : n = 1620 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1621 := by omega
    rw [hn]; exact hasARep_1621
  · have hn : n = 1622 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1623 := by omega
    rw [hn]; exact hasARep_1623
  · have hn : n = 1624 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1625 := by omega
    rw [hn]; exact hasARep_1625
  · have hn : n = 1626 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1627 := by omega
    rw [hn]; exact hasARep_1627
  · have hn : n = 1628 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1629 := by omega
    rw [hn]; exact hasARep_1629
  · have hn : n = 1630 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1631 := by omega
    rw [hn]; exact hasARep_1631
  · have hn : n = 1632 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1633 := by omega
    rw [hn]; exact hasARep_1633
  · have hn : n = 1634 := by omega
    rw [hn] at hmod; cases hmod
  · have hn : n = 1635 := by omega
    rw [hn]; exact hasARep_1635
