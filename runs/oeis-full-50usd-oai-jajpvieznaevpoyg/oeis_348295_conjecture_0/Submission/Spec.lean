import FormalConjectures.Util.ProblemImports

/--
A348295: The sequence a(n) is the sum of (-1) to floor(k*(sqrt 2 - 1)).
-/
noncomputable def a (n : ℕ) : ℤ :=
  Finset.sum (Finset.Ioc 0 n) fun k : ℕ =>
    let k_real : ℝ := k
    let exponent_real : ℝ := k_real * (Real.sqrt 2 - 1)
    let exponent_int : ℤ := Int.floor exponent_real
    -- The exponent is non-negative for k >= 1.
    (-1 : ℤ) ^ exponent_int.toNat

open Finset

def ratSum (p q : ℕ) : ℤ :=
  ∑ k ∈ Finset.Ioc 0 q, (-1 : ℤ) ^ ((k * p - 1) / q)

def ratCountSum (p q : ℕ) : ℤ :=
  ∑ j ∈ Finset.range p, ((-1 : ℤ) ^ j) * (((((j + 1) * q) / p) - ((j * q) / p) : ℕ) : ℤ)

lemma ratSum_eq_count (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    ratSum p q = ratCountSum p q := by
  classical
  unfold ratSum ratCountSum
  let e : ℕ → ℕ := fun k => (k * p - 1) / q
  have hmap : ∀ k ∈ Finset.Ioc 0 q, e k ∈ Finset.range p := by
    intro k hk
    rw [Finset.mem_range]
    dsimp [e]
    apply (Nat.div_lt_iff_lt_mul hq).2
    have hkq : k ≤ q := (Finset.mem_Ioc.mp hk).2
    have hkpos : 0 < k := (Finset.mem_Ioc.mp hk).1
    have hkp_le : k * p ≤ q * p := Nat.mul_le_mul_right p hkq
    have hlt : k * p - 1 < q * p := Nat.sub_one_lt_of_le (Nat.mul_pos hkpos hp) hkp_le
    simpa [Nat.mul_comm] using hlt
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.Ioc 0 q) (t := Finset.range p) (g := e) hmap (fun k => (-1 : ℤ) ^ e k)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < p := Finset.mem_range.mp hj
  have hconst : (∑ k ∈ Finset.Ioc 0 q with e k = j, (-1 : ℤ) ^ e k) =
      ((#{k ∈ Finset.Ioc 0 q | e k = j} : ℕ) : ℤ) * ((-1 : ℤ) ^ j) := by
    calc
      (∑ k ∈ Finset.Ioc 0 q with e k = j, (-1 : ℤ) ^ e k)
          = ∑ k ∈ Finset.Ioc 0 q with e k = j, (-1 : ℤ) ^ j := by
            apply Finset.sum_congr rfl
            intro k hk
            simp at hk
            simp [hk.2]
      _ = ((#{k ∈ Finset.Ioc 0 q | e k = j} : ℕ) : ℤ) * ((-1 : ℤ) ^ j) := by
            rw [Finset.sum_const, nsmul_eq_mul]
  rw [hconst]
  rw [mul_comm]
  congr 1
  norm_cast
  have hset : {k ∈ Finset.Ioc 0 q | e k = j} =
      Finset.Ioc ((j * q) / p) (((j + 1) * q) / p) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hk, hek⟩
      have hkpos : 0 < k := hk.1
      have hleq : k ≤ q := hk.2
      have heq : (k * p - 1) / q = j := by simpa [e] using hek
      have hlow0 : j * q ≤ k * p - 1 := by
        rw [← heq]
        exact Nat.div_mul_le_self _ _
      have hkp_pos : 0 < k * p := Nat.mul_pos hkpos hp
      have hsub_lt : k * p - 1 < k * p := Nat.sub_one_lt hkp_pos.ne'
      have hlow : j * q < k * p := lt_of_le_of_lt hlow0 hsub_lt
      have hhigh0 : k * p - 1 < (j + 1) * q := by
        rw [← heq]
        exact (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self _)
      have hhigh : k * p ≤ (j + 1) * q := by omega
      constructor
      · exact (Nat.div_lt_iff_lt_mul hp).2 (by simpa [Nat.mul_comm] using hlow)
      · exact (Nat.le_div_iff_mul_le hp).2 (by simpa [Nat.mul_comm] using hhigh)
    · intro hk
      have hlow : j * q < k * p := by
        exact (Nat.div_lt_iff_lt_mul hp).mp hk.1
      have hhigh : k * p ≤ (j + 1) * q := by
        exact (Nat.le_div_iff_mul_le hp).mp hk.2
      have hkpos : 0 < k := by
        by_contra h0
        have : k = 0 := Nat.eq_zero_of_not_pos h0
        subst k
        simp at hlow
      have hleq : k ≤ q := by
        have hj1 : j + 1 ≤ p := Nat.succ_le_iff.mpr hjlt
        have hdivle : ((j + 1) * q) / p ≤ q := by
          apply Nat.div_le_of_le_mul
          have : (j + 1) * q ≤ p * q := Nat.mul_le_mul_right q hj1
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
        exact le_trans hk.2 hdivle
      constructor
      · exact ⟨hkpos, hleq⟩
      · dsimp [e]
        apply Nat.le_antisymm
        · have hlt : (k * p - 1) / q < j + 1 := by
            apply (Nat.div_lt_iff_lt_mul hq).2
            omega
          exact Nat.lt_succ_iff.mp hlt
        · apply (Nat.le_div_iff_mul_le hq).2
          omega
  rw [hset, Nat.card_Ioc]

lemma div_mul_two_add (p r j : ℕ) (hp : 0 < p) :
    ((j + 1) * (2 * p + r)) / p = 2 * (j + 1) + ((j + 1) * r) / p := by
  have hrewrite : (j + 1) * (2 * p + r) = p * (2 * (j + 1)) + (j + 1) * r := by ring
  rw [hrewrite, Nat.mul_add_div hp]

lemma ratCountSum_decomp (p r : ℕ) (hp : 0 < p) :
    ratCountSum p (2 * p + r) =
      (∑ j ∈ Finset.range p, ((-1 : ℤ) ^ j) * (2 : ℤ)) + ratCountSum p r := by
  unfold ratCountSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have h1 := div_mul_two_add p r j hp
  have h0 : (j * (2 * p + r)) / p = 2 * j + (j * r) / p := by
    have hrewrite : j * (2 * p + r) = p * (2 * j) + j * r := by ring
    rw [hrewrite, Nat.mul_add_div hp]
  have hdiff : (((j + 1) * (2 * p + r)) / p - (j * (2 * p + r)) / p : ℕ)
      = 2 + (((j + 1) * r) / p - (j * r) / p) := by
    have hlediv : (j * r) / p ≤ ((j + 1) * r) / p := by
      exact Nat.div_le_div_right (Nat.mul_le_mul_right r (Nat.le_succ j))
    rw [h1, h0]
    omega
  rw [hdiff]
  norm_num [Int.natCast_add, mul_add]

lemma ratSum_reduce_num (s r : ℕ) (hs : 0 < s) (hr : 0 < r) :
    ratSum (2 * r + s) r = ratSum s r := by
  unfold ratSum
  apply Finset.sum_congr rfl
  intro k hk
  have hkpos : 0 < k := (Finset.mem_Ioc.mp hk).1
  have hdiv : (k * (2 * r + s) - 1) / r = 2 * k + (k * s - 1) / r := by
    have hkspos : 0 < k * s := Nat.mul_pos hkpos hs
    have hrewrite : k * (2 * r + s) - 1 = r * (2 * k) + (k * s - 1) := by
      have hbase : k * (2 * r + s) = r * (2 * k) + k * s := by ring
      rw [hbase]
      exact Nat.add_sub_assoc (Nat.succ_le_of_lt hkspos) (r * (2 * k))
    rw [hrewrite, Nat.mul_add_div hr]
  rw [hdiv]
  -- (-1)^(2*k + m) = (-1)^m over integers
  rw [pow_add]
  have htwo : ((-1 : ℤ) ^ (2 * k) = 1) := by
    rw [pow_mul]
    norm_num
  rw [htwo, one_mul]

lemma alt_sum_range_odd {p : ℕ} (hpodd : Odd p) :
    (∑ j ∈ Finset.range p, ((-1 : ℤ) ^ j)) = 1 := by
  rw [neg_one_geom_sum]
  have hne : ¬ Even p := (Nat.not_even_iff_odd.mpr hpodd)
  simp [hne]

lemma ratSum_recurrence (s r p q : ℕ) (hs : 0 < s) (hr : 0 < r) (hpodd : Odd p)
    (hp_eq : p = 2 * r + s) (hq_eq : q = 2 * p + r) :
    ratSum p q = 2 + ratSum s r := by
  have hp : 0 < p := by omega
  have hq : 0 < q := by omega
  calc
    ratSum p q = ratCountSum p q := ratSum_eq_count p q hp hq
    _ = ratCountSum p (2 * p + r) := by rw [hq_eq]
    _ = (∑ j ∈ Finset.range p, ((-1 : ℤ) ^ j) * (2 : ℤ)) + ratCountSum p r := ratCountSum_decomp p r hp
    _ = 2 + ratCountSum p r := by
      have hsum : (∑ j ∈ Finset.range p, ((-1 : ℤ) ^ j) * (2 : ℤ)) = 2 := by
        rw [← Finset.sum_mul]
        rw [alt_sum_range_odd hpodd]
        norm_num
      rw [hsum]
    _ = 2 + ratSum p r := by rw [ratSum_eq_count p r hp hr]
    _ = 2 + ratSum (2 * r + s) r := by rw [hp_eq]
    _ = 2 + ratSum s r := by rw [ratSum_reduce_num s r hs hr]


def pellPair : ℕ → ℕ × ℕ
  | 0 => (1, 2)
  | n + 1 =>
      let p := (pellPair n).1
      let q := (pellPair n).2
      let p' := 2 * q + p
      (p', 2 * p' + q)

def pp (n : ℕ) : ℕ := (pellPair n).1
def qq (n : ℕ) : ℕ := (pellPair n).2

@[simp] lemma pp_zero : pp 0 = 1 := rfl
@[simp] lemma qq_zero : qq 0 = 2 := rfl
@[simp] lemma pp_succ (n : ℕ) : pp (n+1) = 2 * qq n + pp n := by
  simp [pp, qq, pellPair]
@[simp] lemma qq_succ (n : ℕ) : qq (n+1) = 2 * pp (n+1) + qq n := by
  simp [pp, qq, pellPair]

lemma pp_pos (n : ℕ) : 0 < pp n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pp_succ]
      exact Nat.add_pos_right _ ih

lemma qq_pos (n : ℕ) : 0 < qq n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [qq_succ]
      exact Nat.add_pos_right _ ih

lemma pp_odd (n : ℕ) : Odd (pp n) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pp_succ]
      exact Even.add_odd (even_two_mul (qq n)) ih

lemma ratSum_pellPair (n : ℕ) : ratSum (pp n) (qq n) = (2 * (n + 1) : ℤ) := by
  induction n with
  | zero =>
      unfold ratSum pp qq pellPair
      rw [Finset.sum_Ioc_succ_top (by norm_num : 0 ≤ 1)]
      rw [Finset.sum_Ioc_succ_top (by norm_num : 0 ≤ 0)]
      simp
  | succ n ih =>
      calc
        ratSum (pp (n+1)) (qq (n+1)) = 2 + ratSum (pp n) (qq n) := by
          apply ratSum_recurrence (s := pp n) (r := qq n) (p := pp (n+1)) (q := qq (n+1))
          · exact pp_pos n
          · exact qq_pos n
          · exact pp_odd (n+1)
          · simp
          · simp
        _ = (2 * ((n+1) + 1) : ℤ) := by
          rw [ih]
          ring


lemma pellPair_eq_int (n : ℕ) :
    ((pp n : ℤ)^2 + 2 * (pp n : ℤ) * (qq n : ℤ) - (qq n : ℤ)^2 = 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pp_succ, qq_succ]
      norm_num
      ring_nf at ih ⊢
      nlinarith


lemma sqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
lemma alpha_pos : (0 : ℝ) < Real.sqrt 2 - 1 := by
  have hsq : (1 : ℝ) < Real.sqrt 2 := by
    rw [← sq_lt_sq₀ zero_le_one (Real.sqrt_nonneg 2)]
    simp [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  linarith

lemma pell_approx_bound (n : ℕ) :
    0 < ((pp n : ℝ) / (qq n : ℝ) - (Real.sqrt 2 - 1)) ∧
    ((pp n : ℝ) / (qq n : ℝ) - (Real.sqrt 2 - 1)) < 1 / (qq n : ℝ)^2 := by
  let p : ℝ := pp n
  let q : ℝ := qq n
  have hqpos_nat : 0 < qq n := qq_pos n
  have hqpos : 0 < q := by
    dsimp [q]
    exact_mod_cast hqpos_nat
  have hdenpos : 0 < (p / q + Real.sqrt 2 + 1) := by
    have hpnonneg : 0 ≤ p / q := div_nonneg (by positivity) hqpos.le
    positivity
  have hden_gt_one : 1 < (p / q + Real.sqrt 2 + 1) := by
    have hpnonneg : 0 ≤ p / q := div_nonneg (by positivity) hqpos.le
    have hspos := sqrt2_pos
    linarith
  have hquad_int := pellPair_eq_int n
  have hquad : (p / q)^2 + 2 * (p / q) - 1 = 1 / q^2 := by
    dsimp [p,q]
    field_simp [show (qq n : ℝ) ≠ 0 by positivity]
    norm_cast at hquad_int ⊢
    ring_nf at hquad_int ⊢
    nlinarith
  have hfactor : (p / q - (Real.sqrt 2 - 1)) * (p / q + Real.sqrt 2 + 1) =
      (p / q)^2 + 2 * (p / q) - 1 := by
    have hs : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
    ring_nf
    rw [hs]
    ring
  have hdiff_eq : p / q - (Real.sqrt 2 - 1) = (1 / q^2) / (p / q + Real.sqrt 2 + 1) := by
    apply (eq_div_iff (show p / q + Real.sqrt 2 + 1 ≠ 0 by positivity)).2
    rw [hfactor, hquad]
  constructor
  · rw [hdiff_eq]
    positivity
  · rw [hdiff_eq]
    have hnumpos : 0 < 1 / q^2 := by positivity
    exact div_lt_self hnumpos hden_gt_one


lemma floor_alpha_eq_rat (n k : ℕ) (hkpos : 0 < k) (hkq : k ≤ qq n) :
    (Int.floor ((k : ℝ) * (Real.sqrt 2 - 1))).toNat = (k * pp n - 1) / qq n := by
  let p : ℝ := pp n
  let q : ℝ := qq n
  let e : ℕ := (k * pp n - 1) / qq n
  have hqpos_nat : 0 < qq n := qq_pos n
  have hqpos : 0 < q := by dsimp [q]; exact_mod_cast hqpos_nat
  have hkposR : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have hdiff := pell_approx_bound n
  have hdpos : 0 < p / q - (Real.sqrt 2 - 1) := by simpa [p,q] using hdiff.1
  have hdlt : p / q - (Real.sqrt 2 - 1) < 1 / q^2 := by simpa [p,q] using hdiff.2
  have halpha_lt : (Real.sqrt 2 - 1) < p / q := sub_pos.mp hdpos
  have hkp_pos_nat : 0 < k * pp n := Nat.mul_pos hkpos (pp_pos n)
  have he_mul_le_nat : e * qq n ≤ k * pp n - 1 := by
    dsimp [e]
    exact Nat.div_mul_le_self _ _
  have he_le_sub : (e : ℝ) ≤ ((k : ℝ) * p - 1) / q := by
    have hcast : ((e * qq n : ℕ) : ℝ) ≤ ((k * pp n - 1 : ℕ) : ℝ) := by exact_mod_cast he_mul_le_nat
    have hcast' : (e : ℝ) * q ≤ (k : ℝ) * p - 1 := by
      dsimp [p,q] at hcast ⊢
      norm_num at hcast ⊢
      -- cast of subtraction
      have hkpp : (1 : ℕ) ≤ k * pp n := Nat.succ_le_of_lt hkp_pos_nat
      rw [Nat.cast_sub hkpp] at hcast
      simpa [Nat.cast_mul] using hcast
    exact (le_div_iff₀ hqpos).2 hcast'
  have hkd_lt : (k : ℝ) * (p / q - (Real.sqrt 2 - 1)) < 1 / q := by
    have hk_le_q : (k : ℝ) ≤ q := by dsimp [q]; exact_mod_cast hkq
    calc
      (k : ℝ) * (p / q - (Real.sqrt 2 - 1)) ≤ q * (p / q - (Real.sqrt 2 - 1)) := by
        gcongr
      _ < q * (1 / q^2) := by gcongr
      _ = 1 / q := by field_simp [show q ≠ 0 by positivity]
  have he_lt_alpha : (e : ℝ) < (k : ℝ) * (Real.sqrt 2 - 1) := by
    have hsub_le : ((k : ℝ) * p - 1) / q ≤ (k : ℝ) * (p / q) - 1 / q := by
      field_simp [show q ≠ 0 by positivity]
      linarith
    have he_le : (e : ℝ) ≤ (k : ℝ) * (p / q) - 1 / q := le_trans he_le_sub hsub_le
    have hrewrite : (k : ℝ) * (Real.sqrt 2 - 1) = (k : ℝ) * (p / q) - (k : ℝ) * (p / q - (Real.sqrt 2 - 1)) := by ring
    rw [hrewrite]
    linarith
  have hupper_nat : k * pp n ≤ (e + 1) * qq n := by
    have hlt : k * pp n - 1 < (e + 1) * qq n := by
      dsimp [e]
      exact (Nat.div_lt_iff_lt_mul hqpos_nat).mp (Nat.lt_succ_self _)
    omega
  have hupper : (k : ℝ) * (Real.sqrt 2 - 1) < (e : ℝ) + 1 := by
    have hkp_div_le : (k : ℝ) * p / q ≤ (e : ℝ) + 1 := by
      have hcast : ((k * pp n : ℕ) : ℝ) ≤ (((e + 1) * qq n : ℕ) : ℝ) := by exact_mod_cast hupper_nat
      have hcast' : (k : ℝ) * p ≤ ((e : ℝ) + 1) * q := by
        dsimp [p,q] at hcast ⊢
        norm_num at hcast ⊢
        simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hcast
      exact (div_le_iff₀ hqpos).2 hcast'
    have hltkp : (k : ℝ) * (Real.sqrt 2 - 1) < (k : ℝ) * (p / q) := by gcongr
    have : (k : ℝ) * (p / q) = (k : ℝ) * p / q := by ring
    rw [this] at hltkp
    exact lt_of_lt_of_le hltkp hkp_div_le
  have hfloor : Int.floor ((k : ℝ) * (Real.sqrt 2 - 1)) = (e : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · exact_mod_cast he_lt_alpha.le
    · simpa [Int.cast_natCast] using hupper
  have heq : (Int.floor ((k : ℝ) * (Real.sqrt 2 - 1))).toNat = e := by
    rw [hfloor]
    simp
  simpa [e]


lemma a_qq_eq_ratSum (n : ℕ) : a (qq n) = ratSum (pp n) (qq n) := by
  unfold a ratSum
  apply Finset.sum_congr rfl
  intro k hk
  simp only
  congr 1
  exact floor_alpha_eq_rat n k (Finset.mem_Ioc.mp hk).1 (Finset.mem_Ioc.mp hk).2

/--
Conjecture (1) for A348295: The sequence is unbounded from above.
Moreover, it seems that the earliest occurrence of m is A000129(m) for even m
and A001333(m) for odd m (this has been confirmed for m <= 32 by Chai Wah Wu,
Oct 21 2021). See A084068 for the conjectured indices of records.
-/
theorem oeis_348295_conjecture_0 : ∀ (M : ℤ), ∃ (n : ℕ), a n > M := by
  intro M
  let t : ℕ := M.toNat
  refine ⟨qq t, ?_⟩
  rw [a_qq_eq_ratSum, ratSum_pellPair]
  have ht : (M : ℤ) ≤ (t : ℤ) := by
    dsimp [t]
    by_cases hM : 0 ≤ M
    · rw [Int.toNat_of_nonneg hM]
    · have hMle : M ≤ 0 := le_of_not_ge hM
      exact hMle.trans (by norm_num)
  have : M < (2 * (t + 1) : ℤ) := by
    have htlt : (t : ℤ) < (2 * (t + 1) : ℤ) := by
      omega
    exact lt_of_le_of_lt ht htlt
  simpa using this
