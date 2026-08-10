import FormalConjectures.Util.ProblemImports

open BigOperators Int

/-- The generalized coefficient $c_{m} (k) = \frac{(m k)!}{(k!)^m}$ in $\mathbb{N}$. -/
def coeff_of_log_gf_gen (m k : ℕ) : ℕ :=
  (m * k).factorial / (k.factorial ^ m)

private noncomputable def generalized_exp_coeff (d : ℕ → ℕ) : ℕ → ℕ
| 0 => 1
| k' + 1 =>
  let k := k' + 1
  (Finset.sum (Finset.range k) fun j =>
    (d (j + 1)) * (generalized_exp_coeff d (k - (j + 1)))) / k

noncomputable def b_m_int (m n : ℕ) : ℤ :=
  if n = 0 then 0
  else
    let d (k : ℕ) : ℕ := n * coeff_of_log_gf_gen m k
    (generalized_exp_coeff d n : ℤ)

open scoped BigOperators
open Finset PowerSeries ArithmeticFunction
noncomputable section


variable {R : Type*} [CommRing R]

-- (a) d ∣ ∏(1+x) - 1
theorem prodexp_a (d : R) (x : ι → R) (s : Finset ι) (hx : ∀ j ∈ s, d ∣ x j) :
    d ∣ (∏ j ∈ s, (1 + x j)) - 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have hP : (1 + x i) * ∏ j ∈ s, (1 + x j) - 1
        = ((∏ j ∈ s, (1 + x j)) - 1) + x i * ∏ j ∈ s, (1 + x j) := by ring
    rw [hP]
    apply dvd_add
    · exact ih (fun j hj => hx j (Finset.mem_insert_of_mem hj))
    · exact Dvd.dvd.mul_right (hx i (Finset.mem_insert_self i s)) _

-- (b) d² ∣ ∏(1+x) - 1 - ∑x
theorem prodexp_b (d : R) (x : ι → R) (s : Finset ι) (hx : ∀ j ∈ s, d ∣ x j) :
    d^2 ∣ (∏ j ∈ s, (1 + x j)) - 1 - ∑ j ∈ s, x j := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    have hP : (1 + x i) * ∏ j ∈ s, (1 + x j) - 1 - (x i + ∑ j ∈ s, x j)
        = ((∏ j ∈ s, (1 + x j)) - 1 - ∑ j ∈ s, x j)
          + x i * ((∏ j ∈ s, (1 + x j)) - 1) := by ring
    rw [hP]
    apply dvd_add
    · exact ih (fun j hj => hx j (Finset.mem_insert_of_mem hj))
    · rw [pow_two]
      exact mul_dvd_mul (hx i (Finset.mem_insert_self i s))
        (prodexp_a d x s (fun j hj => hx j (Finset.mem_insert_of_mem hj)))

-- (c) d³ ∣ 2∏ - 2 - 2∑x - ((∑x)² - ∑x²)
theorem prodexp_c (d : R) (x : ι → R) (s : Finset ι) (hx : ∀ j ∈ s, d ∣ x j) :
    d^3 ∣ 2 * (∏ j ∈ s, (1 + x j)) - 2 - 2 * (∑ j ∈ s, x j)
          - ((∑ j ∈ s, x j)^2 - ∑ j ∈ s, (x j)^2) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.sum_insert hi]
    have hP : 2 * ((1 + x i) * ∏ j ∈ s, (1 + x j)) - 2 - 2 * (x i + ∑ j ∈ s, x j)
          - ((x i + ∑ j ∈ s, x j)^2 - ((x i)^2 + ∑ j ∈ s, (x j)^2))
        = (2 * (∏ j ∈ s, (1 + x j)) - 2 - 2 * (∑ j ∈ s, x j)
            - ((∑ j ∈ s, x j)^2 - ∑ j ∈ s, (x j)^2))
          + 2 * x i * ((∏ j ∈ s, (1 + x j)) - 1 - ∑ j ∈ s, x j) := by ring
    rw [hP]
    apply dvd_add
    · exact ih (fun j hj => hx j (Finset.mem_insert_of_mem hj))
    · rw [pow_succ, pow_two]
      have h1 : d ∣ x i := hx i (Finset.mem_insert_self i s)
      have h2 : d^2 ∣ (∏ j ∈ s, (1 + x j)) - 1 - ∑ j ∈ s, x j :=
        prodexp_b d x s (fun j hj => hx j (Finset.mem_insert_of_mem hj))
      have : d * d * d ∣ (2 * x i) * ((∏ j ∈ s, (1 + x j)) - 1 - ∑ j ∈ s, x j) := by
        have hxi : d ∣ 2 * x i := Dvd.dvd.mul_left h1 2
        calc d * d * d = d * (d * d) := by ring
          _ ∣ (2 * x i) * ((∏ j ∈ s, (1 + x j)) - 1 - ∑ j ∈ s, x j) := by
              rw [← pow_two]; exact mul_dvd_mul hxi h2
      exact this

-- main: in ZMod (p^c), product ≡ 1 mod p^{3a}
theorem prod_expansion_main {p a c : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hac : 3 * a ≤ c)
    (x : ι → ZMod (p^c)) (s : Finset ι)
    (hx : ∀ j ∈ s, ((p^a : ℕ) : ZMod (p^c)) ∣ x j)
    (hs1 : ((p^(3*a) : ℕ) : ZMod (p^c)) ∣ ∑ j ∈ s, x j)
    (hs2 : ((p^(3*a) : ℕ) : ZMod (p^c)) ∣ ∑ j ∈ s, (x j)^2) :
    ((p^(3*a) : ℕ) : ZMod (p^c)) ∣ (∏ j ∈ s, (1 + x j)) - 1 := by
  haveI : NeZero (p^c) := ⟨pow_ne_zero _ (Fact.out : p.Prime).pos.ne'⟩
  set d : ZMod (p^c) := ((p^a : ℕ) : ZMod (p^c)) with hd
  have hcast : ((p^(3*a) : ℕ) : ZMod (p^c)) = d^3 := by
    rw [hd, ← Nat.cast_pow, ← pow_mul]; congr 1; ring
  rw [hcast] at hs1 hs2 ⊢
  have hc := prodexp_c d x s hx
  -- d^3 ∣ 2*(∏-1)
  have hsx2 : d^3 ∣ (∑ j ∈ s, x j)^2 := by
    rw [pow_two]; exact Dvd.dvd.mul_right hs1 _
  have key : d^3 ∣ 2 * ((∏ j ∈ s, (1 + x j)) - 1) := by
    have e : 2 * ((∏ j ∈ s, (1 + x j)) - 1)
        = (2 * (∏ j ∈ s, (1 + x j)) - 2 - 2 * (∑ j ∈ s, x j)
            - ((∑ j ∈ s, x j)^2 - ∑ j ∈ s, (x j)^2))
          + 2 * (∑ j ∈ s, x j) + ((∑ j ∈ s, x j)^2 - ∑ j ∈ s, (x j)^2) := by ring
    rw [e]
    apply dvd_add
    apply dvd_add hc (Dvd.dvd.mul_left hs1 2)
    exact dvd_sub hsx2 hs2
  -- 2 is a unit
  have h2u : IsUnit (2 : ZMod (p^c)) := by
    have : IsUnit (((2:ℕ) : ZMod (p^c))) := by
      rw [ZMod.isUnit_iff_coprime]
      apply Nat.Coprime.pow_right; rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr
        (by intro hd2; have := Nat.le_of_dvd (by norm_num) hd2; omega)
    simpa using this
  obtain ⟨w, hw⟩ := key
  obtain ⟨v, hv⟩ := h2u.exists_left_inv
  refine ⟨v * w, ?_⟩
  rw [show (∏ j ∈ s, (1 + x j)) - 1 = v * (2 * ((∏ j ∈ s, (1 + x j)) - 1)) by
        rw [← mul_assoc, hv, one_mul], hw]
  ring

-- reindex products over multiples of p
theorem mult_reindex {M : Type*} [CommMonoid M] (p B : ℕ) (hp : 1 ≤ p) (f : ℕ → M) :
    ∏ j ∈ (Finset.Icc 1 (p*B)).filter (fun j => p ∣ j), f j
      = ∏ i ∈ Finset.Icc 1 B, f (p*i) := by
  refine Finset.prod_nbij' (fun j => j / p) (fun i => p*i) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha ⊢
    obtain ⟨⟨h1, h2⟩, hd⟩ := ha
    obtain ⟨q, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left _ hp]
    refine ⟨?_, Nat.le_of_mul_le_mul_left h2 hp⟩
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp at h1
    · exact hq
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_Icc] at hb ⊢
    obtain ⟨h1, h2⟩ := hb
    refine ⟨⟨?_, ?_⟩, ⟨b, rfl⟩⟩
    · calc 1 ≤ p := hp
        _ = p*1 := by ring
        _ ≤ p*b := by apply Nat.mul_le_mul_left; exact h1
    · exact Nat.mul_le_mul_left p h2
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    obtain ⟨_, hd⟩ := ha
    obtain ⟨q, rfl⟩ := hd
    simp only [Nat.mul_div_cancel_left _ hp]
  · intro b _
    simp only [Nat.mul_div_cancel_left _ hp]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    obtain ⟨_, hd⟩ := ha
    obtain ⟨q, rfl⟩ := hd
    simp only [Nat.mul_div_cancel_left _ hp]

-- shifted product = descFactorial
theorem shift_prod (A B : ℕ) (hBA : B ≤ A) :
    ∏ i ∈ Finset.Icc 1 B, ((A - B) + i) = A.descFactorial B := by
  rw [Nat.descFactorial_eq_prod_range]
  refine Finset.prod_nbij' (fun i => B - i) (fun k => B - k) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢; omega
  · intro i hi; simp only [Finset.mem_Icc] at hi; simp only []; omega
  · intro k hk; simp only [Finset.mem_range] at hk; simp only []; omega
  · intro i hi; simp only [Finset.mem_Icc] at hi; simp only []; omega

theorem prod_Icc_id (n : ℕ) : ∏ i ∈ Finset.Icc 1 n, i = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ]; ring

theorem kaz_int_id (p A B : ℕ) (hp : 1 ≤ p) (hBA : B ≤ A) :
    Nat.choose (p*A) (p*B) * (∏ j ∈ (Finset.Icc 1 (p*B)).filter (fun j => ¬ p ∣ j), j)
      = Nat.choose A B * (∏ j ∈ (Finset.Icc 1 (p*B)).filter (fun j => ¬ p ∣ j), (p*(A-B) + j)) := by
  set U := ∏ j ∈ (Finset.Icc 1 (p*B)).filter (fun j => ¬ p ∣ j), j with hU
  set V := ∏ j ∈ (Finset.Icc 1 (p*B)).filter (fun j => ¬ p ∣ j), (p*(A-B) + j) with hV
  have hcard : (Finset.Icc 1 B).card = B := by rw [Nat.card_Icc]; omega
  -- hF : (p*B)! = p^B * B! * U
  have hF : (p*B).factorial = p^B * B.factorial * U := by
    rw [← prod_Icc_id, ← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (p*B)) (fun j => p ∣ j) (fun j => j)]
    rw [mult_reindex p B hp (fun j => j)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard, prod_Icc_id]
  -- G
  set G := ∏ j ∈ Finset.Icc 1 (p*B), (p*(A-B) + j) with hG
  -- hG2 : G = p^B * B! * C(A,B) * V
  have hG2 : G = p^B * B.factorial * Nat.choose A B * V := by
    rw [hG, ← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (p*B)) (fun j => p ∣ j) (fun j => p*(A-B)+j)]
    rw [mult_reindex p B hp (fun j => p*(A-B)+j)]
    have hterm : ∀ i ∈ Finset.Icc 1 B, p*(A-B) + p*i = p*((A-B)+i) := by intro i _; ring
    rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_const, hcard,
        shift_prod A B hBA, Nat.descFactorial_eq_factorial_mul_choose]
    ring
  -- hG3 : G = (p*B)! * C(p*A, p*B)
  have hpsub : p*(A-B) = p*A - p*B := by
    rw [Nat.mul_comm p (A-B), Nat.sub_mul, Nat.mul_comm A p, Nat.mul_comm B p]
  have hG3 : G = (p*B).factorial * Nat.choose (p*A) (p*B) := by
    rw [hG]
    have hterm : ∀ j ∈ Finset.Icc 1 (p*B), p*(A-B) + j = (p*A - p*B) + j := by
      intro j _; rw [hpsub]
    rw [Finset.prod_congr rfl hterm, shift_prod (p*A) (p*B) (Nat.mul_le_mul_left p hBA),
        Nat.descFactorial_eq_factorial_mul_choose]
  -- combine
  have hkey : (p*B).factorial * Nat.choose (p*A) (p*B) = p^B * B.factorial * Nat.choose A B * V := by
    rw [← hG3, hG2]
  rw [hF] at hkey
  -- p^B*B!*U*C(pA,pB) = p^B*B!*C(A,B)*V
  have hpos : 0 < p^B * B.factorial := by positivity
  have hkey' : (p^B*B.factorial) * (Nat.choose (p*A) (p*B) * U)
      = (p^B*B.factorial) * (Nat.choose A B * V) := by
    rw [show (p^B*B.factorial)*(Nat.choose (p*A) (p*B)*U)
          = p^B*B.factorial*U*Nat.choose (p*A) (p*B) by ring,
        show (p^B*B.factorial)*(Nat.choose A B*V)
          = p^B*B.factorial*Nat.choose A B*V by ring]
    exact hkey
  exact Nat.eq_of_mul_eq_mul_left hpos hkey'

-- core: sum of v^k over units of ZMod m is killed by (1 - c^k) for any unit c
theorem unit_pow_sum_mul (m : ℕ) [NeZero m] (k : ℕ) (c : (ZMod m)ˣ) :
    (1 - (c:ZMod m)^k) * (∑ v : (ZMod m)ˣ, (v:ZMod m)^k) = 0 := by
  have hperm : (∑ v : (ZMod m)ˣ, (v:ZMod m)^k) = ∑ v : (ZMod m)ˣ, (c:ZMod m)^k * (v:ZMod m)^k := by
    rw [← Equiv.sum_comp (Equiv.mulLeft c) (fun v => (v:ZMod m)^k)]
    apply Finset.sum_congr rfl
    intro v _
    simp only [Equiv.coe_mulLeft, Units.val_mul, mul_pow]
  rw [sub_mul, one_mul, Finset.mul_sum]
  rw [hperm]
  ring

-- helper: from (1-2^k) unit and 2 unit, sum of (↑v)^k over units = 0
theorem unit_pow_sum_zero (m : ℕ) [NeZero m] (k : ℕ)
    (h2 : IsUnit (2 : ZMod m)) (hk : IsUnit (1 - (2:ZMod m)^k)) :
    (∑ v : (ZMod m)ˣ, (v:ZMod m)^k) = 0 := by
  obtain ⟨c, hc⟩ := h2
  have := unit_pow_sum_mul m k c
  rw [hc] at this
  exact (hk.mul_right_eq_zero).mp this

theorem isunit_small (p a n : ℕ) [Fact p.Prime] (hn : ¬ p ∣ n) :
    IsUnit ((n : ℕ) : ZMod (p^a)) := by
  haveI : NeZero (p^a) := ⟨pow_ne_zero _ (Fact.out : p.Prime).pos.ne'⟩
  rw [ZMod.isUnit_iff_coprime]; apply Nat.Coprime.pow_right; rw [Nat.coprime_comm]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hn

theorem units_sum_one_zero (p a : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (ha : 1 ≤ a) :
    (∑ v : (ZMod (p^a))ˣ, (v:ZMod (p^a))^1) = 0 := by
  haveI : NeZero (p^a) := ⟨pow_ne_zero _ (Fact.out : p.Prime).pos.ne'⟩
  apply unit_pow_sum_zero
  · have h := isunit_small p a 2 (by intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega)
    simpa using h
  · rw [pow_one]
    have : (1 : ZMod (p^a)) - 2 = -1 := by ring
    rw [this]; exact (isUnit_one).neg

theorem units_sum_sq_zero (p a : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (ha : 1 ≤ a) :
    (∑ v : (ZMod (p^a))ˣ, (v:ZMod (p^a))^2) = 0 := by
  haveI : NeZero (p^a) := ⟨pow_ne_zero _ (Fact.out : p.Prime).pos.ne'⟩
  apply unit_pow_sum_zero
  · have h := isunit_small p a 2 (by intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega)
    simpa using h
  · have : (1 : ZMod (p^a)) - 2^2 = -((3:ℕ):ZMod (p^a)) := by push_cast; ring
    rw [this, IsUnit.neg_iff]
    exact isunit_small p a 3 (by intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega)

theorem units_sum_inv_sq_zero (p a : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (ha : 1 ≤ a) :
    (∑ v : (ZMod (p^a))ˣ, ((v:ZMod (p^a))⁻¹)^2) = 0 := by
  haveI : NeZero (p^a) := ⟨pow_ne_zero _ (Fact.out : p.Prime).pos.ne'⟩
  rw [← Equiv.sum_comp (Equiv.inv (ZMod (p^a))ˣ) (fun v => ((v:ZMod (p^a))⁻¹)^2)]
  have : ∀ v : (ZMod (p^a))ˣ, (((Equiv.inv (ZMod (p^a))ˣ) v : ZMod (p^a))⁻¹)^2 = ((v:ZMod (p^a)))^2 := by
    intro v
    simp only [Equiv.inv_apply, ZMod.inv_coe_unit, inv_inv]
  rw [Finset.sum_congr rfl (fun v _ => this v)]
  exact units_sum_sq_zero p a hp5 ha

theorem units_sum_inv_one_zero (p a : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (ha : 1 ≤ a) :
    (∑ v : (ZMod (p^a))ˣ, ((v:ZMod (p^a))⁻¹)^1) = 0 := by
  haveI : NeZero (p^a) := ⟨pow_ne_zero _ (Fact.out : p.Prime).pos.ne'⟩
  rw [← Equiv.sum_comp (Equiv.inv (ZMod (p^a))ˣ) (fun v => ((v:ZMod (p^a))⁻¹)^1)]
  have : ∀ v : (ZMod (p^a))ˣ, (((Equiv.inv (ZMod (p^a))ˣ) v : ZMod (p^a))⁻¹)^1 = ((v:ZMod (p^a)))^1 := by
    intro v
    simp only [Equiv.inv_apply, ZMod.inv_coe_unit, inv_inv]
  rw [Finset.sum_congr rfl (fun v _ => this v)]
  exact units_sum_one_zero p a hp5 ha

-- counting/periodicity
variable {p a : ℕ}

theorem sum_range_units {R : Type*} [AddCommMonoid R] [Fact p.Prime] (ha : 1 ≤ a)
    (g : ZMod (p^a) → R) :
    ∑ v : (ZMod (p^a))ˣ, g (v : ZMod (p^a))
      = ∑ j ∈ (Finset.range (p^a)).filter (fun j => ¬ p ∣ j), g (j : ZMod (p^a)) := by
  haveI : NeZero (p^a) := ⟨pow_ne_zero _ (Fact.out : p.Prime).pos.ne'⟩
  have hppa : p ∣ p^a := dvd_pow_self p (by omega : a ≠ 0)
  refine Finset.sum_bij (fun v _ => (v : ZMod (p^a)).val) ?_ ?_ ?_ ?_
  · intro v _
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt _, ?_⟩
    intro hdvd
    have hcop : Nat.Coprime (v:ZMod (p^a)).val (p^a) := by
      rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_val, ZMod.cast_id]; exact v.isUnit
    have hd1 : p ∣ Nat.gcd (v:ZMod (p^a)).val (p^a) := Nat.dvd_gcd hdvd hppa
    rw [hcop] at hd1
    have hp1 := Nat.le_of_dvd one_pos hd1
    have := (Fact.out : p.Prime).two_le; omega
  · intro v1 _ v2 _ h
    exact Units.ext (ZMod.val_injective (p^a) h)
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    have hcop : Nat.Coprime j (p^a) := by
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hj.2
    refine ⟨ZMod.unitOfCoprime j hcop, Finset.mem_univ _, ?_⟩
    show ((ZMod.unitOfCoprime j hcop : ZMod (p^a)).val) = j
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt hj.1]
  · intro v _
    rw [ZMod.natCast_val, ZMod.cast_id]

theorem sum_periodic {R : Type*} [AddCommMonoid R] [Fact p.Prime] (ha : 1 ≤ a)
    (g : ZMod (p^a) → R) (u : ℕ) :
    ∑ j ∈ (Finset.range (p^a*u)).filter (fun j => ¬ p ∣ j), g (j : ZMod (p^a))
      = u • (∑ j ∈ (Finset.range (p^a)).filter (fun j => ¬ p ∣ j), g (j : ZMod (p^a))) := by
  classical
  simp only [Finset.sum_filter]
  have hpa : p ∣ p^a := dvd_pow_self p (by omega : a ≠ 0)
  induction u with
  | zero => simp
  | succ u ih =>
    rw [show p^a*(u+1) = p^a*u+p^a by ring, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hcong : ((p^a*u+i : ℕ):ZMod (p^a)) = (i:ZMod (p^a)) := by
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add]
    have hdvd : (p ∣ p^a*u+i) ↔ (p ∣ i) := by
      constructor
      · intro h; exact (Nat.dvd_add_right (Dvd.dvd.mul_right hpa u)).mp h
      · intro h; exact Dvd.dvd.add (Dvd.dvd.mul_right hpa u) h
    by_cases hc : p ∣ i
    · rw [if_neg (not_not.mpr (hdvd.mpr hc)), if_neg (not_not.mpr hc)]
    · rw [if_pos (by rw [hdvd]; exact hc), if_pos hc, hcong]

-- bridges

-- bridge: castHom to ZMod p^a is zero ⟹ p^a divides x in ZMod p^c
theorem castHom_zero_dvd {p c a : ℕ} [Fact p.Prime] (hac : a ≤ c) (x : ZMod (p^c))
    (hx : (ZMod.castHom (pow_dvd_pow p hac) (ZMod (p^a))) x = 0) :
    ((p^a : ℕ) : ZMod (p^c)) ∣ x := by
  haveI : NeZero (p^c) := ⟨pow_ne_zero _ (Fact.out : p.Prime).pos.ne'⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hx
  obtain ⟨m, hm⟩ := hx
  refine ⟨(m : ZMod (p^c)), ?_⟩
  have hxv : (x.val : ZMod (p^c)) = x := ZMod.natCast_zmod_val x
  rw [← hxv, hm, Nat.cast_mul]

-- castHom commutes with inverse of a unit
theorem castHom_inv {p c a : ℕ} [Fact p.Prime] (hac : a ≤ c) (u : ZMod (p^c)) (hu : IsUnit u) :
    (ZMod.castHom (pow_dvd_pow p hac) (ZMod (p^a))) u⁻¹
      = ((ZMod.castHom (pow_dvd_pow p hac) (ZMod (p^a))) u)⁻¹ := by
  have h1 : (ZMod.castHom (pow_dvd_pow p hac) (ZMod (p^a))) u
      * (ZMod.castHom (pow_dvd_pow p hac) (ZMod (p^a))) u⁻¹ = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit u hu, map_one]
  have hcu : IsUnit ((ZMod.castHom (pow_dvd_pow p hac) (ZMod (p^a))) u) :=
    RingHom.isUnit_map _ hu
  calc (ZMod.castHom (pow_dvd_pow p hac) (ZMod (p^a))) u⁻¹
      = (1 : ZMod (p^a)) * (ZMod.castHom (pow_dvd_pow p hac) (ZMod (p^a))) u⁻¹ := (one_mul _).symm
    _ = (((ZMod.castHom (pow_dvd_pow p hac) (ZMod (p^a))) u)⁻¹
          * (ZMod.castHom (pow_dvd_pow p hac) (ZMod (p^a))) u)
          * (ZMod.castHom (pow_dvd_pow p hac) (ZMod (p^a))) u⁻¹ := by
        rw [ZMod.inv_mul_of_unit _ hcu]
    _ = ((ZMod.castHom (pow_dvd_pow p hac) (ZMod (p^a))) u)⁻¹
          * ((ZMod.castHom (pow_dvd_pow p hac) (ZMod (p^a))) u
            * (ZMod.castHom (pow_dvd_pow p hac) (ZMod (p^a))) u⁻¹) := by ring
    _ = ((ZMod.castHom (pow_dvd_pow p hac) (ZMod (p^a))) u)⁻¹ := by rw [h1, mul_one]

-- generalized isunit
theorem isunit_natCast {p c n : ℕ} [Fact p.Prime] (hn : ¬ p ∣ n) :
    IsUnit ((n : ℕ) : ZMod (p^c)) := by
  haveI : NeZero (p^c) := ⟨pow_ne_zero _ (Fact.out : p.Prime).pos.ne'⟩
  rw [ZMod.isUnit_iff_coprime]; apply Nat.Coprime.pow_right; rw [Nat.coprime_comm]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hn

-- S2 divisibility: p^a divides the inverse-square harmonic sum (working mod p^c)
theorem harm_sq_dvd {p a c u : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (ha : 1 ≤ a) (hac : a ≤ c) :
    ((p^a : ℕ) : ZMod (p^c)) ∣
      ∑ j ∈ (Finset.range (p^a*u)).filter (fun j => ¬ p ∣ j), ((j : ZMod (p^c))⁻¹)^2 := by
  apply castHom_zero_dvd hac
  rw [map_sum]
  have hcong : ∀ j ∈ (Finset.range (p^a*u)).filter (fun j => ¬ p ∣ j),
      (ZMod.castHom (pow_dvd_pow p hac) (ZMod (p^a))) (((j : ZMod (p^c))⁻¹)^2)
        = (((j : ZMod (p^a))⁻¹)^2) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [map_pow, castHom_inv hac _ (isunit_natCast hj.2), ZMod.castHom_apply, ZMod.cast_natCast (pow_dvd_pow p hac)]
  rw [Finset.sum_congr rfl hcong, sum_periodic ha (fun y => (y⁻¹)^2) u, ← sum_range_units ha (fun x => (x⁻¹)^2),
      units_sum_inv_sq_zero p a hp5 ha, smul_zero]

-- involution on the filter set
theorem invol_filt {R : Type*} [AddCommMonoid R] {p a u : ℕ} (hpd : p ∣ p^a*u) (f : ℕ → R) :
    ∑ j ∈ (Finset.range (p^a*u)).filter (fun j => ¬ p ∣ j), f j
      = ∑ j ∈ (Finset.range (p^a*u)).filter (fun j => ¬ p ∣ j), f (p^a*u - j) := by
  refine Finset.sum_nbij' (fun j => p^a*u - j) (fun j => p^a*u - j) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    have hj0 : j ≠ 0 := by rintro rfl; exact hj.2 (dvd_zero p)
    refine ⟨by omega, ?_⟩
    intro hc
    exact hj.2 (by have := Nat.dvd_sub hpd hc; rwa [Nat.sub_sub_self (by omega)] at this)
  · intro j hj; simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    have hj0 : j ≠ 0 := by rintro rfl; exact hj.2 (dvd_zero p)
    refine ⟨by omega, ?_⟩
    intro hc
    exact hj.2 (by have := Nat.dvd_sub hpd hc; rwa [Nat.sub_sub_self (by omega)] at this)
  · intro j hj; simp only [Finset.mem_filter, Finset.mem_range] at hj; show p^a*u - (p^a*u - j) = j; omega
  · intro j hj; simp only [Finset.mem_filter, Finset.mem_range] at hj; show p^a*u - (p^a*u - j) = j; omega
  · intro j hj; simp only [Finset.mem_filter, Finset.mem_range] at hj; show f j = f (p^a*u - (p^a*u-j)); congr 1; omega

theorem zmod_inv_eq_of_mul {m : ℕ} {x y : ZMod m} (hx : IsUnit x) (h : x * y = 1) : x⁻¹ = y := by
  calc x⁻¹ = x⁻¹ * 1 := (mul_one _).symm
    _ = x⁻¹ * (x * y) := by rw [h]
    _ = (x⁻¹ * x) * y := by ring
    _ = 1 * y := by rw [ZMod.inv_mul_of_unit _ hx]
    _ = y := one_mul _

theorem pair_inv {n : ℕ} (a b : ZMod n) (ha : IsUnit a) (hb : IsUnit b) :
    a⁻¹ + b⁻¹ = (a + b) * (a * b)⁻¹ := by
  have hab : IsUnit (a * b) := ha.mul hb
  have key : (a⁻¹ + b⁻¹) * (a * b) = a + b := by
    have h1 := ZMod.inv_mul_of_unit a ha
    have h2 := ZMod.inv_mul_of_unit b hb
    linear_combination b * h1 + a * h2
  have := congrArg (· * (a * b)⁻¹) key
  simp only [mul_assoc, ZMod.mul_inv_of_unit _ hab, mul_one] at this
  exact this

-- S1 divisibility: p^(2a) divides the inverse harmonic sum (working mod p^c), c ≥ 2a
theorem harm_one_dvd {p a c u : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (ha : 1 ≤ a) (hac : 2*a ≤ c) :
    ((p^(2*a) : ℕ) : ZMod (p^c)) ∣
      ∑ j ∈ (Finset.range (p^a*u)).filter (fun j => ¬ p ∣ j), (j : ZMod (p^c))⁻¹ := by
  have hac1 : a ≤ c := by omega
  have hpd : p ∣ p^a*u := Dvd.dvd.mul_right (dvd_pow_self p (by omega : a ≠ 0)) u
  set S := ∑ j ∈ (Finset.range (p^a*u)).filter (fun j => ¬ p ∣ j), (j : ZMod (p^c))⁻¹ with hS
  set U := ∑ j ∈ (Finset.range (p^a*u)).filter (fun j => ¬ p ∣ j),
      ((j:ZMod (p^c)) * ((p^a*u - j : ℕ):ZMod (p^c)))⁻¹ with hU
  -- pairing
  have hpair : (2 : ZMod (p^c)) * S = ((p^a*u : ℕ) : ZMod (p^c)) * U := by
    rw [two_mul]
    nth_rewrite 2 [hS]
    rw [invol_filt hpd (fun j => (j:ZMod (p^c))⁻¹)]
    rw [hS, ← Finset.sum_add_distrib, hU, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    have hj0 : j ≠ 0 := by rintro rfl; exact hj.2 (dvd_zero p)
    have hju : IsUnit (j:ZMod (p^c)) := isunit_natCast hj.2
    have hpju : IsUnit ((p^a*u - j : ℕ):ZMod (p^c)) := isunit_natCast (by
      intro hc; exact hj.2 (by have := Nat.dvd_sub hpd hc; rwa [Nat.sub_sub_self (by omega)] at this))
    rw [pair_inv _ _ hju hpju]
    congr 1
    rw [← Nat.cast_add]; congr 1; omega
  -- p^a | U
  have hUdvd : ((p^a : ℕ) : ZMod (p^c)) ∣ U := by
    apply castHom_zero_dvd hac1
    rw [hU, map_sum]
    have hcong : ∀ j ∈ (Finset.range (p^a*u)).filter (fun j => ¬ p ∣ j),
        (ZMod.castHom (pow_dvd_pow p hac1) (ZMod (p^a)))
          ((j:ZMod (p^c)) * ((p^a*u - j : ℕ):ZMod (p^c)))⁻¹
          = -(((j : ZMod (p^a))⁻¹)^2) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_range] at hj
      have hju : IsUnit (j:ZMod (p^c)) := isunit_natCast hj.2
      have hpju : IsUnit ((p^a*u - j : ℕ):ZMod (p^c)) := isunit_natCast (by
        intro hc; exact hj.2 (by have := Nat.dvd_sub hpd hc; rwa [Nat.sub_sub_self (by omega)] at this))
      rw [castHom_inv hac1 _ (hju.mul hpju), map_mul, ZMod.castHom_apply, ZMod.castHom_apply,
          ZMod.cast_natCast (pow_dvd_pow p hac1), ZMod.cast_natCast (pow_dvd_pow p hac1)]
      -- (↑j * ↑(p^a u - j))⁻¹ = -((↑j)⁻¹)^2 in ZMod p^a
      have hcast : ((p^a*u - j : ℕ) : ZMod (p^a)) = -(j : ZMod (p^a)) := by
        rw [Nat.cast_sub (by omega), Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_sub]
      rw [hcast]
      have hju' : IsUnit (j:ZMod (p^a)) := isunit_natCast hj.2
      apply zmod_inv_eq_of_mul (hju'.mul hju'.neg)
      rw [show ((j:ZMod (p^a)) * -(j:ZMod (p^a))) * (-(((j:ZMod (p^a))⁻¹)^2))
            = ((j:ZMod (p^a)) * (j:ZMod (p^a))⁻¹)^2 by ring,
          ZMod.mul_inv_of_unit _ hju', one_pow]
    rw [Finset.sum_congr rfl hcong, Finset.sum_neg_distrib]
    rw [sum_periodic ha (fun y => (y⁻¹)^2) u, ← sum_range_units ha (fun x => (x⁻¹)^2),
        units_sum_inv_sq_zero p a hp5 ha, smul_zero, neg_zero]
  -- conclude
  obtain ⟨W, hW⟩ := hUdvd
  have hp2u : ((p^a*u : ℕ) : ZMod (p^c)) = ((p^a : ℕ):ZMod (p^c)) * (u:ZMod (p^c)) := by
    rw [Nat.cast_mul]
  have key : (2 : ZMod (p^c)) * S = ((p^(2*a) : ℕ) : ZMod (p^c)) * ((u:ZMod (p^c)) * W) := by
    rw [hpair, hp2u, hW]
    rw [show p^(2*a) = p^a * p^a by rw [← pow_add]; congr 1; omega, Nat.cast_mul]
    ring
  -- 2 unit
  have h2u : IsUnit (2 : ZMod (p^c)) := by
    have h := isunit_natCast (c := c) (p := p) (n := 2)
      (by intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega)
    simpa using h
  refine ⟨(2:ZMod (p^c))⁻¹ * ((u:ZMod (p^c)) * W), ?_⟩
  rw [show ((p^(2*a):ℕ):ZMod (p^c)) * ((2:ZMod (p^c))⁻¹ * ((u:ZMod (p^c))*W))
        = (2:ZMod (p^c))⁻¹ * (((p^(2*a):ℕ):ZMod (p^c)) * ((u:ZMod (p^c))*W)) by ring,
      ← key, ← mul_assoc, ZMod.inv_mul_of_unit _ h2u, one_mul]

-- product form: (∏_{i<m} C((i+1)k,k)) * (k!)^m = (m*k)!
theorem prod_choose_mul (m k : ℕ) :
    (∏ i ∈ Finset.range m, Nat.choose ((i+1)*k) k) * (k.factorial)^m = (m*k).factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, pow_succ]
    -- (∏ * C((m+1)k,k)) * ((k!)^m * k!) = ((m+1)k)!
    have key : Nat.choose ((m+1)*k) k * k.factorial * (m*k).factorial = ((m+1)*k).factorial := by
      have h := Nat.choose_mul_factorial_mul_factorial (n := (m+1)*k) (k := k) (by nlinarith)
      have hsub : (m+1)*k - k = m*k := by ring_nf; omega
      rw [hsub] at h
      exact h
    calc (∏ i ∈ Finset.range m, Nat.choose ((i+1)*k) k) * Nat.choose ((m+1)*k) k
            * (k.factorial^m * k.factorial)
        = ((∏ i ∈ Finset.range m, Nat.choose ((i+1)*k) k) * k.factorial^m)
            * (Nat.choose ((m+1)*k) k * k.factorial) := by ring
      _ = (m*k).factorial * (Nat.choose ((m+1)*k) k * k.factorial) := by rw [ih]
      _ = Nat.choose ((m+1)*k) k * k.factorial * (m*k).factorial := by ring
      _ = ((m+1)*k).factorial := key

def cm (m k : ℕ) : ℕ := (m * k).factorial / (k.factorial ^ m)

theorem cm_prod (m k : ℕ) :
    cm m k = ∏ i ∈ Finset.range m, Nat.choose ((i+1)*k) k := by
  unfold cm
  rw [Nat.div_eq_of_eq_mul_left (by positivity) (prod_choose_mul m k).symm]

theorem cm_mul (m k : ℕ) : cm m k * (k.factorial)^m = (m*k).factorial := by
  rw [cm_prod]; exact prod_choose_mul m k

-- ZMod factorization of Kazandzidis
theorem kaz_zmod {p A B c : ℕ} [Fact p.Prime] (hBA : B ≤ A) :
    ((Nat.choose (p*A) (p*B) : ZMod (p^c)))
      = (Nat.choose A B : ZMod (p^c)) *
        ∏ j ∈ (Finset.Icc 1 (p*B)).filter (fun j => ¬ p ∣ j),
          (1 + ((p*(A-B) : ℕ) : ZMod (p^c)) * ((j : ℕ) : ZMod (p^c))⁻¹) := by
  haveI : NeZero (p^c) := ⟨pow_ne_zero _ (Fact.out : p.Prime).pos.ne'⟩
  classical
  set s := (Finset.Icc 1 (p*B)).filter (fun j => ¬ p ∣ j) with hs
  -- each j in s is a unit
  have hju : ∀ j ∈ s, IsUnit ((j : ℕ) : ZMod (p^c)) := by
    intro j hj
    rw [hs, Finset.mem_filter] at hj
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right; rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hj.2
  -- cast the integer identity
  have hid := kaz_int_id p A B (Fact.out : p.Prime).pos hBA
  have hcast : ((Nat.choose (p*A) (p*B) : ZMod (p^c))) * (∏ j ∈ s, ((j:ℕ) : ZMod (p^c)))
      = (Nat.choose A B : ZMod (p^c)) * (∏ j ∈ s, (((p*(A-B)+j : ℕ)) : ZMod (p^c))) := by
    have := congrArg (Nat.cast : ℕ → ZMod (p^c)) hid
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_prod, Nat.cast_prod] at this
    rw [hs]; exact this
  -- V̂ = Û * ∏(1+x)
  have hV : (∏ j ∈ s, (((p*(A-B)+j : ℕ)) : ZMod (p^c)))
      = (∏ j ∈ s, ((j:ℕ) : ZMod (p^c)))
        * ∏ j ∈ s, (1 + ((p*(A-B) : ℕ) : ZMod (p^c)) * ((j : ℕ) : ZMod (p^c))⁻¹) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    have hu := hju j hj
    rw [Nat.cast_add, mul_add, mul_one, mul_comm ((j:ℕ):ZMod (p^c)) _, mul_assoc,
        ZMod.inv_mul_of_unit _ hu, mul_one, add_comm]
  rw [hV, ← mul_assoc] at hcast
  set Q := ∏ j ∈ s, ((j:ℕ) : ZMod (p^c)) with hQ
  set P := ∏ j ∈ s, (1 + ((p*(A-B) : ℕ) : ZMod (p^c)) * ((j : ℕ) : ZMod (p^c))⁻¹) with hP
  -- cancel Û (unit)
  have hUu : IsUnit Q := by
    rw [hQ]
    apply Finset.prod_induction _ IsUnit
    · intro a b; exact IsUnit.mul
    · exact isUnit_one
    · exact hju
  obtain ⟨w, hw⟩ := hUu.exists_right_inv
  have hcast2 : (Nat.choose (p*A) (p*B) : ZMod (p^c)) * Q
      = ((Nat.choose A B : ZMod (p^c)) * P) * Q := by rw [hcast]; ring
  calc (Nat.choose (p*A) (p*B) : ZMod (p^c))
      = (Nat.choose (p*A) (p*B) : ZMod (p^c)) * (Q*w) := by rw [hw, mul_one]
    _ = ((Nat.choose (p*A) (p*B) : ZMod (p^c)) * Q) * w := by ring
    _ = (((Nat.choose A B : ZMod (p^c)) * P) * Q) * w := by rw [hcast2]
    _ = ((Nat.choose A B : ZMod (p^c)) * P) * (Q*w) := by ring
    _ = (Nat.choose A B : ZMod (p^c)) * P := by rw [hw, mul_one]
-- set bridge: Icc 1 N filter ¬p∣ = range N filter ¬p∣ when p∣N
theorem filter_Icc_eq_filter_range {p N : ℕ} (hpN : p ∣ N) :
    (Finset.Icc 1 N).filter (fun j => ¬ p ∣ j) = (Finset.range N).filter (fun j => ¬ p ∣ j) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, hnp⟩
    refine ⟨?_, hnp⟩
    rcases lt_or_eq_of_le h2 with h | h
    · exact h
    · exact absurd (h ▸ hpN) hnp
  · rintro ⟨h1, hnp⟩
    refine ⟨⟨?_, by omega⟩, hnp⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact absurd (dvd_zero p) hnp
    · exact hj

theorem kaz_strong {p a u A : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (ha : 1 ≤ a)
    (hAB : p^(a-1)*u ≤ A) (hdiff : p^(a-1) ∣ (A - p^(a-1)*u)) :
    (Nat.choose (p*A) (p*(p^(a-1)*u)) : ZMod (p^(3*a)))
      = (Nat.choose A (p^(a-1)*u) : ZMod (p^(3*a))) := by
  haveI : NeZero (p^(3*a)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).pos.ne'⟩
  set B := p^(a-1)*u with hB
  have hpB : p*B = p^a*u := by
    rw [hB, ← mul_assoc]; congr 1; rw [← pow_succ']; congr 1; omega
  set s := (Finset.Icc 1 (p*B)).filter (fun j => ¬ p ∣ j) with hs
  set x : ℕ → ZMod (p^(3*a)) :=
    fun j => ((p*(A-B) : ℕ) : ZMod (p^(3*a))) * ((j : ℕ) : ZMod (p^(3*a)))⁻¹ with hx_def
  -- p^a ∣ p*(A-B) in ℕ
  have hpadvd : p^a ∣ p*(A-B) := by
    obtain ⟨t, ht⟩ := hdiff
    rw [ht, ← mul_assoc, ← pow_succ']
    rw [show a-1+1 = a by omega]
    exact Dvd.intro t rfl
  have hpacast : ((p^a : ℕ) : ZMod (p^(3*a))) ∣ ((p*(A-B) : ℕ) : ZMod (p^(3*a))) := by
    obtain ⟨t, ht⟩ := hpadvd
    exact ⟨(t : ZMod (p^(3*a))), by rw [ht, Nat.cast_mul]⟩
  -- hx
  have hx : ∀ j ∈ s, ((p^a : ℕ) : ZMod (p^(3*a))) ∣ x j := by
    intro j _; rw [hx_def]; exact Dvd.dvd.mul_right hpacast _
  -- harmonic sums over s
  have hsetbridge : s = (Finset.range (p^a*u)).filter (fun j => ¬ p ∣ j) := by
    rw [hs, hpB]; exact filter_Icc_eq_filter_range (dvd_mul_of_dvd_left (dvd_pow_self p (by omega : a ≠ 0)) u)
  have harm1 : ((p^(2*a) : ℕ) : ZMod (p^(3*a))) ∣ ∑ j ∈ s, ((j : ℕ) : ZMod (p^(3*a)))⁻¹ := by
    rw [hsetbridge]; exact harm_one_dvd hp5 ha (by omega)
  have harm2 : ((p^a : ℕ) : ZMod (p^(3*a))) ∣ ∑ j ∈ s, (((j : ℕ) : ZMod (p^(3*a)))⁻¹)^2 := by
    rw [hsetbridge]; exact harm_sq_dvd hp5 ha (by omega)
  -- cast power identities
  have hc3 : ((p^a : ℕ) : ZMod (p^(3*a))) * ((p^(2*a) : ℕ) : ZMod (p^(3*a)))
      = ((p^(3*a) : ℕ) : ZMod (p^(3*a))) := by
    rw [← Nat.cast_mul, ← pow_add]; congr 2; omega
  have hc3' : ((p^(2*a) : ℕ) : ZMod (p^(3*a))) * ((p^a : ℕ) : ZMod (p^(3*a)))
      = ((p^(3*a) : ℕ) : ZMod (p^(3*a))) := by
    rw [← Nat.cast_mul, ← pow_add]; congr 2; omega
  -- hs1
  have hs1 : ((p^(3*a) : ℕ) : ZMod (p^(3*a))) ∣ ∑ j ∈ s, x j := by
    have he : ∑ j ∈ s, x j
        = ((p*(A-B) : ℕ) : ZMod (p^(3*a))) * ∑ j ∈ s, ((j : ℕ) : ZMod (p^(3*a)))⁻¹ := by
      rw [hx_def, Finset.mul_sum]
    rw [he, ← hc3]; exact mul_dvd_mul hpacast harm1
  -- hs2
  have hs2 : ((p^(3*a) : ℕ) : ZMod (p^(3*a))) ∣ ∑ j ∈ s, (x j)^2 := by
    have he : ∑ j ∈ s, (x j)^2
        = ((p*(A-B) : ℕ) : ZMod (p^(3*a)))^2 * ∑ j ∈ s, (((j : ℕ) : ZMod (p^(3*a)))⁻¹)^2 := by
      rw [hx_def, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [mul_pow]
    rw [he, ← hc3']
    refine mul_dvd_mul ?_ harm2
    have h2a : ((p^a : ℕ) : ZMod (p^(3*a))) * ((p^a : ℕ) : ZMod (p^(3*a)))
        = ((p^(2*a) : ℕ) : ZMod (p^(3*a))) := by
      rw [← Nat.cast_mul, ← pow_add]; congr 2; omega
    rw [pow_two, ← h2a]; exact mul_dvd_mul hpacast hpacast
  -- product = 1
  have hpe := prod_expansion_main (p:=p) (a:=a) (c:=3*a) hp5 (le_refl _) x s hx hs1 hs2
  rw [ZMod.natCast_self, zero_dvd_iff, sub_eq_zero] at hpe
  rw [kaz_zmod (c := 3*a) (show B ≤ A from hAB)]
  rw [show (∏ j ∈ (Finset.Icc 1 (p*B)).filter (fun j => ¬ p ∣ j),
        (1 + ((p*(A-B) : ℕ) : ZMod (p^(3*a))) * ((j : ℕ) : ZMod (p^(3*a)))⁻¹))
        = ∏ j ∈ s, (1 + x j) from rfl, hpe, mul_one]

theorem cm_tower {p a u m : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (ha : 1 ≤ a) :
    (cm m (p*(p^(a-1)*u)) : ZMod (p^(3*a))) = (cm m (p^(a-1)*u) : ZMod (p^(3*a))) := by
  rw [cm_prod, cm_prod, Nat.cast_prod, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  have e1 : (i+1)*(p*(p^(a-1)*u)) = p*((i+1)*(p^(a-1)*u)) := by ring
  rw [e1]
  have hAB : p^(a-1)*u ≤ (i+1)*(p^(a-1)*u) := Nat.le_mul_of_pos_left _ (by omega)
  have hdiff : p^(a-1) ∣ ((i+1)*(p^(a-1)*u) - p^(a-1)*u) := by
    have hsub : (i+1)*(p^(a-1)*u) - p^(a-1)*u = i*(p^(a-1)*u) := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel]
    rw [hsub]; exact (dvd_mul_right (p^(a-1)) u).mul_left i
  exact kaz_strong hp5 ha hAB hdiff
-- Weak Gauss congruence for cm, all primes p, mod p^{1+v} where p^v ∣ k
theorem cm_gauss {p k v m : ℕ} [Fact p.Prime] (hv : p^v ∣ k) :
    (cm m (p*k) : ZMod (p^(1+v))) = (cm m k : ZMod (p^(1+v))) := by
  haveI : NeZero (p^(1+v)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).pos.ne'⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rw [cm_prod, cm_prod, Nat.cast_prod, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  have e1 : (i+1)*(p*k) = p*((i+1)*k) := by ring
  rw [e1, kaz_zmod (c:=1+v) (show k ≤ (i+1)*k from Nat.le_mul_of_pos_left _ (by omega))]
  have hzero : ((p*((i+1)*k - k) : ℕ) : ZMod (p^(1+v))) = 0 := by
    have hsub : (i+1)*k - k = i*k := by rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel]
    rw [hsub]
    rw [ZMod.natCast_eq_zero_iff]
    obtain ⟨t, ht⟩ := hv
    refine ⟨i*t, ?_⟩
    rw [ht, pow_add, pow_one]; ring
  have hprod1 : (∏ j ∈ (Finset.Icc 1 (p*k)).filter (fun j => ¬ p ∣ j),
      (1 + ((p*((i+1)*k - k) : ℕ) : ZMod (p^(1+v))) * ((j:ℕ):ZMod (p^(1+v)))⁻¹)) = 1 := by
    apply Finset.prod_eq_one
    intro j _; rw [hzero, zero_mul, add_zero]
  rw [hprod1, mul_one]

-- For coprime m,n, sum over divisors of m*n splits as double sum
theorem coprime_sum_divisors {M : Type*} [AddCommMonoid M] {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (hmn : Nat.Coprime m n) (f : ℕ → M) :
    ∑ d ∈ (m*n).divisors, f d = ∑ d1 ∈ m.divisors, ∑ d2 ∈ n.divisors, f (d1*d2) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun d => (Nat.gcd d m, Nat.gcd d n))
    (fun p => p.1 * p.2) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [Nat.mem_divisors] at hd
    simp only [Finset.mem_product, Nat.mem_divisors]
    exact ⟨⟨Nat.gcd_dvd_right d m, hm⟩, ⟨Nat.gcd_dvd_right d n, hn⟩⟩
  · intro p hp
    simp only [Finset.mem_product, Nat.mem_divisors] at hp
    rw [Nat.mem_divisors]
    exact ⟨mul_dvd_mul hp.1.1 hp.2.1, Nat.mul_ne_zero hm hn⟩
  · intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨hdvd, _⟩ := hd
    -- d = gcd d m * gcd d n  for d | m*n with coprime m n
    have h1 : Nat.gcd d m * Nat.gcd d n = d := by
      have := Nat.Coprime.gcd_mul d hmn
      -- gcd d (m*n) = gcd d m * gcd d n
      rw [Nat.gcd_eq_left hdvd] at this
      exact this.symm
    simp only []; exact h1
  · intro p hp
    obtain ⟨a, b⟩ := p
    simp only [Finset.mem_product, Nat.mem_divisors] at hp
    obtain ⟨⟨hd1, _⟩, ⟨hd2, _⟩⟩ := hp
    have hc2m : Nat.Coprime b m := Nat.Coprime.coprime_dvd_left hd2 hmn.symm
    have hc1n : Nat.Coprime a n := Nat.Coprime.coprime_dvd_left hd1 hmn
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [Nat.gcd_mul_left_left_of_gcd_eq_one hc2m, Nat.gcd_eq_left hd1]
    · rw [Nat.gcd_mul_right_left_of_gcd_eq_one hc1n, Nat.gcd_eq_left hd2]
  · intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨hdvd, _⟩ := hd
    have h1 : Nat.gcd d m * Nat.gcd d n = d := by
      have := Nat.Coprime.gcd_mul d hmn
      rw [Nat.gcd_eq_left hdvd] at this
      exact this.symm
    simp only []; rw [h1]

-- per-prime divisibility of the Mobius transform, given Gauss congruences for t
theorem perprime {p e n' : ℕ} (hp : p.Prime) (hn' : 0 < n') (hpn' : ¬ p ∣ n') (he : 1 ≤ e)
    (t : ℕ → ℤ)
    (hgauss : ∀ k v, p^v ∣ k → (p:ℤ)^(1+v) ∣ (t (p*k) - t k)) :
    (p:ℤ)^e ∣ ∑ d ∈ (p^e * n').divisors, (ArithmeticFunction.moebius ((p^e*n')/d)) * t d := by
  have hcop : Nat.Coprime (p^e) n' := Nat.Coprime.pow_left e ((hp.coprime_iff_not_dvd).mpr hpn')
  have hpe0 : p^e ≠ 0 := pow_ne_zero _ hp.pos.ne'
  rw [coprime_sum_divisors hpe0 hn'.ne' hcop, Finset.sum_comm]
  apply Finset.dvd_sum
  intro d2 hd2
  rw [Nat.mem_divisors] at hd2
  obtain ⟨hd2dvd, _⟩ := hd2
  have hpd2 : ¬ p ∣ d2 := fun h => hpn' (h.trans hd2dvd)
  have hpnd : ¬ p ∣ (n'/d2) := fun h => hpn' (h.trans (Nat.div_dvd_of_dvd hd2dvd))
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  have hsummand : ∀ j ∈ Finset.range (e+1),
      (ArithmeticFunction.moebius ((p^e*n')/((⟨(p ^ ·), Nat.pow_right_injective hp.two_le⟩ : ℕ ↪ ℕ) j * d2)))
        * t ((⟨(p ^ ·), Nat.pow_right_injective hp.two_le⟩ : ℕ ↪ ℕ) j * d2)
        = (ArithmeticFunction.moebius (p^(e-j)))
          * (ArithmeticFunction.moebius (n'/d2)) * t (p^j*d2) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hje : j ≤ e := by omega
    show (ArithmeticFunction.moebius ((p^e*n')/(p^j * d2))) * t (p^j * d2)
        = (ArithmeticFunction.moebius (p^(e-j))) * (ArithmeticFunction.moebius (n'/d2)) * t (p^j*d2)
    have hd2pos : 0 < d2 := Nat.pos_of_dvd_of_pos hd2dvd hn'
    have hdiv : (p^e*n')/(p^j*d2) = p^(e-j)*(n'/d2) := by
      apply Nat.div_eq_of_eq_mul_left (Nat.mul_pos (pow_pos hp.pos _) hd2pos)
      rw [show p^(e-j)*(n'/d2)*(p^j*d2) = (p^j*p^(e-j))*(d2*(n'/d2)) by ring,
          ← pow_add, show j+(e-j)=e by omega, Nat.mul_div_cancel' hd2dvd]
    rw [hdiv, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        (Nat.Coprime.pow_left _ ((hp.coprime_iff_not_dvd).mpr hpnd))]
  rw [Finset.sum_congr rfl hsummand]
  rw [show (∑ j ∈ Finset.range (e+1), ArithmeticFunction.moebius (p^(e-j))
        * ArithmeticFunction.moebius (n'/d2) * t (p^j*d2))
       = ArithmeticFunction.moebius (n'/d2)
         * ∑ j ∈ Finset.range (e+1), ArithmeticFunction.moebius (p^(e-j)) * t (p^j*d2) by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring]
  have hcollapse : ∑ j ∈ Finset.range (e+1), ArithmeticFunction.moebius (p^(e-j)) * t (p^j*d2)
      = t (p^e*d2) - t (p^(e-1)*d2) := by
    rw [← Finset.sum_subset (s₁ := ({e-1, e} : Finset ℕ))]
    · rw [Finset.sum_pair (by omega : e-1 ≠ e),
          show e-(e-1)=1 by omega, show e-e=0 by omega, pow_zero,
          ArithmeticFunction.moebius_apply_one,
          ArithmeticFunction.moebius_apply_prime_pow hp (by norm_num : (1:ℕ)≠0)]
      norm_num; ring
    · intro x hx; rw [Finset.mem_insert, Finset.mem_singleton] at hx; rw [Finset.mem_range]; omega
    · intro x hx hxnot
      rw [Finset.mem_range] at hx; rw [Finset.mem_insert, Finset.mem_singleton] at hxnot
      rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega : e-x≠0), if_neg (by omega : ¬(e-x=1))]
      ring
  rw [hcollapse]
  apply Dvd.dvd.mul_left
  have hg := hgauss (p^(e-1)*d2) (e-1) (dvd_mul_right _ _)
  rw [show p*(p^(e-1)*d2) = p^e*d2 by
        rw [← mul_assoc, ← _root_.pow_succ', Nat.sub_add_cancel he],
      show 1+(e-1)=e by omega] at hg
  exact hg

theorem dvd_of_prime_pow_dvd {S : ℤ} {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p, p.Prime → (p^(n.factorization p) : ℤ) ∣ S) : (n : ℤ) ∣ S := by
  have hsplit : ((n.primeFactors).prod (fun p => p^(n.factorization p)) : ℕ) = n := by
    conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rw [Nat.factorization]
    rfl
  have key : (∏ p ∈ n.primeFactors, ((p:ℤ)^(n.factorization p))) ∣ S := by
    apply Finset.prod_dvd_of_coprime
    · intro p hp q hq hpq
      simp only [Function.onFun]
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
      apply IsCoprime.pow
      rw [Int.isCoprime_iff_gcd_eq_one]
      have : Nat.Coprime p q := (Nat.coprime_primes hpp hqp).mpr hpq
      simpa [Int.gcd] using this
    · intro p hp
      exact h p (Nat.prime_of_mem_primeFactors hp)
  have hcast : (∏ p ∈ n.primeFactors, ((p:ℤ)^(n.factorization p))) = (n:ℤ) := by
    have hc := congrArg (Nat.cast : ℕ → ℤ) hsplit
    push_cast at hc
    exact hc
  rwa [hcast] at key
theorem gauss_dvd {n : ℕ} (hn : 1 ≤ n) (t : ℕ → ℤ)
    (hgauss : ∀ (p : ℕ), p.Prime → ∀ (k v : ℕ), p^v ∣ k → (p:ℤ)^(1+v) ∣ (t (p*k) - t k)) :
    (n : ℤ) ∣ ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n/d)) * t d := by
  apply dvd_of_prime_pow_dvd (by omega : n ≠ 0)
  intro p hpp
  rcases Nat.eq_zero_or_pos (n.factorization p) with he0 | hepos
  · rw [he0]; simp
  · haveI : Fact p.Prime := ⟨hpp⟩
    set e := n.factorization p with he
    set n' := n / p^e with hn'def
    have hsplit : p^e * n' = n := Nat.ordProj_mul_ordCompl_eq_self n p
    have hpn' : ¬ p ∣ n' := Nat.not_dvd_ordCompl hpp (by omega : n ≠ 0)
    have hn'pos : 0 < n' := Nat.ordCompl_pos p (by omega : n ≠ 0)
    have := perprime (p:=p) (e:=e) (n':=n') hpp hn'pos hpn' hepos t
      (fun k v hkv => hgauss p hpp k v hkv)
    rw [hsplit] at this
    exact this

theorem cm_gauss_dvd {p k v : ℕ} (m : ℕ) (hpp : p.Prime) (hv : p^v ∣ k) :
    (p:ℤ)^(1+v) ∣ ((cm m (p*k):ℤ) - (cm m k:ℤ)) := by
  haveI : Fact p.Prime := ⟨hpp⟩
  have hpe : (p:ℤ)^(1+v) = ((p^(1+v):ℕ):ℤ) := by push_cast; ring
  rw [hpe, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [sub_eq_zero]
  exact_mod_cast cm_gauss (p:=p) (k:=k) (v:=v) (m:=m) hv


def gfun (t : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℤ) * t x.2

theorem necklace_sum (t : ℕ → ℤ) (n : ℕ) (hn : 0 < n) :
    ∑ i ∈ n.divisors, gfun t i = t n := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (f := gfun t) (g := t)).mpr
    (fun n _ => rfl)
  exact h n hn

theorem gfun_eq_div (t : ℕ → ℤ) (n : ℕ) :
    gfun t n = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n/d) : ℤ) * t d := by
  rw [gfun, Nat.sum_divisorsAntidiagonal' (f := fun a b => (ArithmeticFunction.moebius a : ℤ) * t b)]

theorem gfun_dvd (t : ℕ → ℤ) (n : ℕ) (hn : 1 ≤ n)
    (hw : ∀ m : ℕ, 1 ≤ m → (m:ℤ) ∣ ∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m/d):ℤ) * t d) :
    (n:ℤ) ∣ gfun t n := by
  rw [gfun_eq_div]; exact hw n hn

def wInt (t : ℕ → ℤ) (n : ℕ) : ℤ := gfun t n / n

theorem w_mul (t : ℕ → ℤ) (n : ℕ) (hn : 1 ≤ n)
    (hw : ∀ m : ℕ, 1 ≤ m → (m:ℤ) ∣ ∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m/d):ℤ) * t d) :
    (n:ℤ) * wInt t n = gfun t n := by
  rw [wInt, Int.mul_ediv_cancel' (gfun_dvd t n hn hw)]

theorem necklace_w (t : ℕ → ℤ) (n : ℕ) (hn : 1 ≤ n)
    (hw : ∀ m : ℕ, 1 ≤ m → (m:ℤ) ∣ ∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m/d):ℤ) * t d) :
    ∑ i ∈ n.divisors, (i:ℤ) * wInt t i = t n := by
  rw [← necklace_sum t n hn]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.mem_divisors] at hi
  have hipos : 1 ≤ i := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr hi)
  exact w_mul t i hipos hw

namespace Dev



def Aq (d : ℕ → ℚ) : ℕ → ℚ
  | 0 => 1
  | (k+1) => (∑ j ∈ Finset.range (k+1), d (j+1) * Aq d (k - j)) / (k+1)

@[simp] theorem Aq_zero (d : ℕ → ℚ) : Aq d 0 = 1 := by rw [Aq]

theorem Aq_succ (d : ℕ → ℚ) (k : ℕ) :
    ((k : ℚ) + 1) * Aq d (k+1) = ∑ j ∈ Finset.range (k+1), d (j+1) * Aq d (k - j) := by
  rw [Aq]; field_simp

def fps (d : ℕ → ℚ) : ℚ⟦X⟧ := mk (Aq d)

def driver (d : ℕ → ℚ) : ℚ⟦X⟧ := mk (fun k => d (k+1))

@[simp] theorem constantCoeff_fps (d : ℕ → ℚ) : constantCoeff (fps d) = 1 := by
  rw [fps, ← coeff_zero_eq_constantCoeff, coeff_mk, Aq_zero]

theorem derivative_fps (d : ℕ → ℚ) :
    derivativeFun (fps d) = driver d * fps d := by
  ext n
  simp only [fps, driver, coeff_derivativeFun, coeff_mk, coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => d (i+1) * Aq d j)]
  have hrec := Aq_succ d n
  rw [mul_comm]
  exact hrec


theorem ode_unique (h g1 g2 : ℚ⟦X⟧) (hg1 : derivativeFun g1 = h * g1)
    (hg2 : derivativeFun g2 = h * g2)
    (he : constantCoeff g1 = constantCoeff g2) : g1 = g2 := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simpa using he
    | (m+1) =>
      have e1 : coeff (m+1) g1 * ((m:ℚ)+1) = coeff (m+1) g2 * ((m:ℚ)+1) := by
        have d1 := congrArg (coeff m) hg1
        have d2 := congrArg (coeff m) hg2
        rw [coeff_derivativeFun] at d1 d2
        rw [coeff_mul] at d1 d2
        rw [d1, d2]
        apply Finset.sum_congr rfl
        intro p hp
        have hj : p.2 < m + 1 := by
          have := Finset.mem_antidiagonal.mp hp
          omega
        rw [ih p.2 hj]
      have : ((m:ℚ)+1) ≠ 0 := by positivity
      exact mul_right_cancel₀ this e1


theorem driver_smul (N : ℕ) (d : ℕ → ℚ) :
    driver (fun k => (N:ℚ) * d k) = (N : ℚ) • driver d := by
  ext k
  simp [driver, coeff_mk]

theorem derivativeFun_pow (f : ℚ⟦X⟧) (N : ℕ) :
    derivativeFun (f^N) = (N:ℚ⟦X⟧) * f^(N-1) * derivativeFun f := by
  have h := (PowerSeries.derivative (R:=ℚ)).leibniz_pow f N
  have e : (PowerSeries.derivative (R:=ℚ)) f = derivativeFun f := rfl
  have e2 : (PowerSeries.derivative (R:=ℚ)) (f^N) = derivativeFun (f^N) := rfl
  rw [e] at h; rw [e2] at h; rw [h, nsmul_eq_mul, smul_eq_mul]; ring

theorem fps_smul_eq_pow (N : ℕ) (hN : 1 ≤ N) (d : ℕ → ℚ) :
    fps (fun k => (N:ℚ) * d k) = (fps d)^N := by
  set h := (N:ℚ) • driver d with hh
  apply ode_unique h
  · rw [derivative_fps, driver_smul]
  · -- derivativeFun ((fps d)^N) = h * (fps d)^N
    rw [derivativeFun_pow, derivative_fps]
    have : (fps d)^(N-1) * (driver d * fps d) = driver d * (fps d)^N := by
      have : (fps d)^(N-1) * fps d = (fps d)^N := by
        rw [← pow_succ]; congr 1; omega
      rw [← mul_assoc, mul_comm ((fps d)^(N-1)) (driver d), mul_assoc, this]
    rw [mul_assoc, this, hh]
    simp only [Algebra.smul_def, map_natCast]
    ring
  · simp [map_pow]


section Reduction

/-- The Frobenius quotient `G = f^p / f(x^p)`. -/
def Gfrob {p : ℕ} (hp : p ≠ 0) (f : ℚ⟦X⟧) : ℚ⟦X⟧ := f^p * (expand p hp f)⁻¹

theorem frob_factor {p : ℕ} (hp : p ≠ 0) (f : ℚ⟦X⟧) (hf : constantCoeff f = 1) :
    f^p = expand p hp f * Gfrob hp f := by
  rw [Gfrob]
  rw [show expand p hp f * (f^p * (expand p hp f)⁻¹)
        = f^p * (expand p hp f * (expand p hp f)⁻¹) by ring]
  rw [PowerSeries.mul_inv_cancel _ (by simp [hf]), mul_one]

theorem reduction {p : ℕ} (hp : p ≠ 0) (f : ℚ⟦X⟧) (hf : constantCoeff f = 1) (N : ℕ) :
    coeff (p*N) (f^(p*N)) =
      ∑ a' ∈ Finset.range (N+1), coeff a' (f^N) * coeff (p*(N-a')) ((Gfrob hp f)^N) := by
  have hpow : f^(p*N) = expand p hp (f^N) * (Gfrob hp f)^N := by
    rw [pow_mul, frob_factor hp f hf, mul_pow, map_pow]
  rw [hpow, coeff_mul]
  rw [← Finset.sum_filter_of_ne (p := fun x : ℕ × ℕ => p ∣ x.1)]
  · refine Finset.sum_bij' (fun x _ => x.1 / p) (fun a' _ => (p*a', p*(N-a'))) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨a, b⟩ := x
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hx
      obtain ⟨hab, q, rfl⟩ := hx
      rw [Finset.mem_range]
      simp only [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp)]
      have hle : p*q ≤ p*N := by omega
      have : q ≤ N := Nat.le_of_mul_le_mul_left hle (Nat.pos_of_ne_zero hp)
      omega
    · intro a' ha'
      rw [Finset.mem_range] at ha'
      simp only [Finset.mem_filter, Finset.mem_antidiagonal]
      refine ⟨?_, ⟨a', rfl⟩⟩
      rw [← Nat.mul_add]
      congr 1
      omega
    · intro x hx
      obtain ⟨a, b⟩ := x
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hx
      obtain ⟨hab, q, rfl⟩ := hx
      simp only [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp)]
      have hle : p*q ≤ p*N := by omega
      have hqN : q ≤ N := Nat.le_of_mul_le_mul_left hle (Nat.pos_of_ne_zero hp)
      have hd : p * (N - q) = p * N - p * q := by rw [Nat.mul_sub]
      apply Prod.ext
      · rfl
      · simp only
        omega
    · intro a' ha'
      rw [Finset.mem_range] at ha'
      dsimp only
      rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp)]
    · intro x hx
      obtain ⟨a, b⟩ := x
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hx
      obtain ⟨hab, q, rfl⟩ := hx
      simp only [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp), coeff_expand_mul]
      have hle : p*q ≤ p*N := by omega
      have hqN : q ≤ N := Nat.le_of_mul_le_mul_left hle (Nat.pos_of_ne_zero hp)
      have hd : p * (N - q) = p * N - p * q := by rw [Nat.mul_sub]
      have hb : b = p * (N - q) := by omega
      rw [hb]
  · intro x hx hne
    by_contra h
    exact hne (by rw [coeff_expand_of_not_dvd p hp _ h, zero_mul])

end Reduction

/-- Truncated ODE uniqueness: if the drivers agree below `M`, the solutions agree up to `M`. -/
theorem ode_unique_trunc (h1 h2 g1 g2 : ℚ⟦X⟧) (hg1 : derivativeFun g1 = h1 * g1)
    (hg2 : derivativeFun g2 = h2 * g2)
    (he : constantCoeff g1 = constantCoeff g2)
    (M : ℕ) (hh : ∀ k < M, coeff k h1 = coeff k h2) :
    ∀ k ≤ M, coeff k g1 = coeff k g2 := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, hk with
    | 0, _ => simpa using he
    | (m+1), hk =>
      have e1 : coeff (m+1) g1 * ((m:ℚ)+1) = coeff (m+1) g2 * ((m:ℚ)+1) := by
        have d1 := congrArg (coeff m) hg1
        have d2 := congrArg (coeff m) hg2
        rw [coeff_derivativeFun] at d1 d2
        rw [coeff_mul] at d1 d2
        rw [d1, d2]
        apply Finset.sum_congr rfl
        intro pr hpr
        have hsum : pr.1 + pr.2 = m := Finset.mem_antidiagonal.mp hpr
        have hk1 : pr.1 < M := by omega
        have hk2 : pr.2 ≤ M := by omega
        have hk2' : pr.2 < m + 1 := by omega
        rw [hh pr.1 hk1, ih pr.2 hk2' hk2]
      have : ((m:ℚ)+1) ≠ 0 := by positivity
      exact mul_right_cancel₀ this e1


/-- Logarithmic derivative of a unit power series. -/
def LD (u : ℚ⟦X⟧ˣ) : ℚ⟦X⟧ := derivativeFun (u : ℚ⟦X⟧) * ((u⁻¹ : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)

theorem LD_mul (u v : ℚ⟦X⟧ˣ) : LD (u*v) = LD u + LD v := by
  unfold LD
  set a := (u:ℚ⟦X⟧); set b := (v:ℚ⟦X⟧)
  set ai := ((u⁻¹:ℚ⟦X⟧ˣ):ℚ⟦X⟧); set bi := ((v⁻¹:ℚ⟦X⟧ˣ):ℚ⟦X⟧)
  have hd : derivativeFun (a * b) = a * derivativeFun b + b * derivativeFun a := by
    have h := (PowerSeries.derivative (R:=ℚ)).leibniz a b
    rw [smul_eq_mul, smul_eq_mul] at h
    exact h
  have huv : (((u*v : ℚ⟦X⟧ˣ)):ℚ⟦X⟧) = a * b := by rw [Units.val_mul]
  have hinv : ((((u*v)⁻¹ : ℚ⟦X⟧ˣ)):ℚ⟦X⟧) = bi * ai := by rw [mul_inv_rev, Units.val_mul]
  rw [huv, hinv, hd]
  have e1 : a * ai = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e2 : b * bi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  linear_combination (derivativeFun b * bi) * e1 + (derivativeFun a * ai) * e2

theorem LD_one : LD (1 : ℚ⟦X⟧ˣ) = 0 := by
  simp only [LD, Units.val_one, inv_one, derivativeFun_one, zero_mul]

theorem LD_inv (u : ℚ⟦X⟧ˣ) : LD u⁻¹ = - LD u := by
  have h := LD_mul u u⁻¹
  rw [mul_inv_cancel, LD_one] at h
  linear_combination -h

theorem LD_zpow (u : ℚ⟦X⟧ˣ) (c : ℤ) : LD (u^c) = c • LD u := by
  refine Int.induction_on c ?_ ?_ ?_
  · simp [LD_one]
  · intro n ih; rw [zpow_add_one, LD_mul, ih]; push_cast; ring
  · intro n ih; rw [zpow_sub_one, LD_mul, LD_inv, ih]; push_cast; ring




/-- `expS S = exp(S)`. -/
def expS (S : ℚ⟦X⟧) : ℚ⟦X⟧ := (exp ℚ).subst S

theorem coeff_pow_eq_zero_of_lt {S : ℚ⟦X⟧} (h : constantCoeff S = 0) {n d : ℕ}
    (hd : n < d) : coeff n (S^d) = 0 := by
  apply coeff_of_lt_order
  calc (↑n : ℕ∞) < ↑d := by exact_mod_cast hd
    _ ≤ (S^d).order := le_order_pow_of_constantCoeff_eq_zero d h

theorem coeff_expS (S : ℚ⟦X⟧) (h : constantCoeff S = 0) (n : ℕ) :
    coeff n (expS S) = ∑ d ∈ Finset.range (n+1), coeff n (S^d) / (d.factorial : ℚ) := by
  have hs : HasSubst S := HasSubst.of_constantCoeff_zero' h
  rw [expS, coeff_subst' hs]
  rw [finsum_eq_finset_sum_of_support_subset _ (s := Finset.range (n+1))]
  · apply Finset.sum_congr rfl
    intro d _
    rw [coeff_exp, smul_eq_mul]
    rw [map_div₀, map_one, map_natCast]
    ring
  · intro d hd
    simp only [Function.mem_support] at hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    push_neg at hcon
    apply hd
    rw [coeff_pow_eq_zero_of_lt h (by omega : n < d), smul_zero]


variable {p : ℕ} [hp : Fact p.Prime]

theorem le_padicValRat_sum {ι : Type*} (s : Finset ι) (F : ι → ℚ) (b : ℤ)
    (hb : ∀ i ∈ s, F i ≠ 0 → b ≤ padicValRat p (F i)) :
    (∑ i ∈ s, F i) = 0 ∨ b ≤ padicValRat p (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction with
  | empty => left; simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    rcases ih (fun i hi _ => hb i (Finset.mem_insert_of_mem hi) ‹_›) with h0 | hpos
    · rw [h0, add_zero]
      by_cases hFa : F a = 0
      · left; rw [hFa]
      · right; exact hb a (Finset.mem_insert_self a s) hFa
    · by_cases hFa : F a = 0
      · rw [hFa, zero_add]; right; exact hpos
      · by_cases hsum0 : F a + ∑ i ∈ s, F i = 0
        · left; exact hsum0
        · right
          calc b ≤ min (padicValRat p (F a)) (padicValRat p (∑ i ∈ s, F i)) :=
                  le_min (hb a (Finset.mem_insert_self a s) hFa) hpos
            _ ≤ padicValRat p (F a + ∑ i ∈ s, F i) := padicValRat.min_le_padicValRat_add hsum0


theorem le_padicValRat_coeff_mul (A B : ℚ⟦X⟧) (n : ℕ) (b : ℤ)
    (hb : ∀ ij ∈ Finset.antidiagonal n, coeff ij.1 A ≠ 0 → coeff ij.2 B ≠ 0 →
      b ≤ padicValRat p (coeff ij.1 A) + padicValRat p (coeff ij.2 B)) :
    coeff n (A * B) = 0 ∨ b ≤ padicValRat p (coeff n (A * B)) := by
  rw [coeff_mul]
  apply le_padicValRat_sum
  intro ij hij hne
  have h1 : coeff ij.1 A ≠ 0 := by rintro h; rw [h, zero_mul] at hne; exact hne rfl
  have h2 : coeff ij.2 B ≠ 0 := by rintro h; rw [h, mul_zero] at hne; exact hne rfl
  rw [padicValRat.mul h1 h2]
  exact hb ij hij h1 h2


-- product valuation bound
theorem padicValRat_prod_ge {ι : Type*} (s : Finset ι) (f : ι → ℚ) (b : ι → ℤ)
    (hf : ∀ i ∈ s, f i ≠ 0) (hb : ∀ i ∈ s, b i ≤ padicValRat p (f i)) :
    (∑ i ∈ s, b i) ≤ padicValRat p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hfa : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
    have hprod : (∏ i ∈ s, f i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rw [padicValRat.mul hfa hprod]
    have := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
                (fun i hi => hb i (Finset.mem_insert_of_mem hi))
    have hba := hb a (Finset.mem_insert_self a s)
    omega

-- composition-sum valuation bound for coeff of S^d (linear growth)
theorem le_padicValRat_coeff_pow (S : ℚ⟦X⟧) (c : ℤ) (n d : ℕ)
    (hS : ∀ k, coeff k S ≠ 0 → (k:ℤ) * c ≤ padicValRat p (coeff k S)) :
    coeff n (S^d) = 0 ∨ (n:ℤ) * c ≤ padicValRat p (coeff n (S^d)) := by
  rw [coeff_pow]
  apply le_padicValRat_sum
  intro l hl hne
  rw [Finset.mem_finsuppAntidiag] at hl
  have hsum : ∑ i ∈ Finset.range d, l i = n := hl.1
  have hfac : ∀ i ∈ Finset.range d, coeff (l i) S ≠ 0 := by
    intro i hi
    exact Finset.prod_ne_zero_iff.mp hne i hi
  have hb : (∑ i ∈ Finset.range d, (l i : ℤ) * c) ≤ padicValRat p (∏ i ∈ Finset.range d, coeff (l i) S) := by
    apply padicValRat_prod_ge _ _ _ hfac
    intro i hi
    exact hS (l i) (hfac i hi)
  rw [← Finset.sum_mul] at hb
  rw [show (∑ i ∈ Finset.range d, (l i:ℤ)) = (n:ℤ) by rw [← Nat.cast_sum, hsum]] at hb
  exact hb




def geomN (n : ℕ) : ℚ⟦X⟧ := mk (fun j => if n ∣ j then (1:ℚ) else 0)

theorem oneSubXpow_mul_geom (n : ℕ) (hn : 1 ≤ n) :
    ((1 : ℚ⟦X⟧) - X^n) * geomN n = 1 := by
  have hexp : ((1 : ℚ⟦X⟧) - X^n) * geomN n = geomN n - X^n * geomN n := by ring
  ext m
  rw [hexp, map_sub, coeff_X_pow_mul', geomN, coeff_mk, coeff_one]
  by_cases hm0 : m = 0
  · subst hm0
    simp only [dvd_zero, if_true]
    rw [if_neg (by omega : ¬ n ≤ 0)]
    simp
  · rw [if_neg hm0]
    by_cases hdvd : n ∣ m
    · have hle : n ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdvd
      rw [if_pos hdvd, if_pos hle, coeff_mk, if_pos (Nat.dvd_sub hdvd dvd_rfl)]
      ring
    · rw [if_neg hdvd]
      by_cases hle : n ≤ m
      · have hns : ¬ n ∣ (m - n) := by
          intro hc
          exact hdvd (by have := Nat.dvd_add hc (dvd_refl n); rwa [Nat.sub_add_cancel hle] at this)
        rw [if_pos hle, coeff_mk, if_neg hns]
        ring
      · rw [if_neg hle]; ring

theorem deriv_oneSubXpow (n : ℕ) (hn : 1 ≤ n) :
    derivativeFun ((1:ℚ⟦X⟧) - X^n) = (monomial (n-1)) (-(n:ℚ)) := by
  ext a
  rw [coeff_derivativeFun, map_sub, coeff_monomial, coeff_X_pow, coeff_one]
  by_cases ha : a = n - 1
  · subst ha
    rw [if_pos rfl, if_neg (by omega : ¬ n-1+1 = 0), if_pos (by omega : n-1+1=n)]
    have hc : ((n-1:ℕ):ℚ)+1 = (n:ℚ) := by rw [Nat.cast_sub hn]; push_cast; ring
    rw [hc]; ring
  · rw [if_neg ha]
    by_cases ha1 : a + 1 = n
    · exact absurd (show a = n-1 by omega) ha
    · rw [if_neg ha1, if_neg (by omega : ¬ a + 1 = 0)]; ring

def unitN (n : ℕ) (hn : 1 ≤ n) : ℚ⟦X⟧ˣ :=
  Units.mkOfMulEqOne (1 - X^n) (geomN n) (oneSubXpow_mul_geom n hn)

theorem coeff_LD_unitN (n : ℕ) (hn : 1 ≤ n) (j : ℕ) :
    coeff j (LD (unitN n hn)) = if n ∣ (j+1) then -(n:ℚ) else 0 := by
  have hval : ((unitN n hn : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) = 1 - X^n := rfl
  have hinv : (((unitN n hn)⁻¹ : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) = geomN n := rfl
  rw [LD, hval, hinv, deriv_oneSubXpow n hn]
  have hmon : (monomial (n-1)) (-(n:ℚ)) = C (-(n:ℚ)) * X^(n-1) := by
    ext m; rw [coeff_C_mul, coeff_X_pow, coeff_monomial]; split <;> simp
  rw [hmon, mul_assoc, coeff_C_mul, coeff_X_pow_mul', geomN]
  by_cases hdvd : n ∣ (j+1)
  · have hle : n - 1 ≤ j := by
      have : n ≤ j + 1 := Nat.le_of_dvd (by omega) hdvd
      omega
    have hdvd' : n ∣ j - (n-1) := by
      have he : j - (n-1) = (j+1) - n := by omega
      rw [he]; exact Nat.dvd_sub hdvd dvd_rfl
    rw [if_pos hle, coeff_mk, if_pos hdvd, if_pos hdvd']; ring
  · rw [if_neg hdvd]
    by_cases hle : n - 1 ≤ j
    · have hnd : ¬ n ∣ j - (n-1) := by
        intro hc
        apply hdvd
        have he : j - (n-1) = (j+1) - n := by omega
        rw [he] at hc
        have : n ∣ ((j+1-n) + n) := Nat.dvd_add hc dvd_rfl
        rwa [Nat.sub_add_cancel (by omega : n ≤ j+1)] at this
      rw [if_pos hle, coeff_mk, if_neg hnd]; ring
    · rw [if_neg hle]; ring

-- LD of finite product
theorem LD_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ⟦X⟧ˣ) :
    LD (∏ i ∈ s, f i) = ∑ i ∈ s, LD (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [LD_one]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, LD_mul, ih]



def SubInt : Subring ℚ := (Int.castRingHom ℚ).range

def IsInt (f : ℚ⟦X⟧) : Prop := ∀ n, coeff n f ∈ SubInt

theorem intCast_mem (z : ℤ) : (z : ℚ) ∈ SubInt := ⟨z, rfl⟩

theorem ite_mem (c : Prop) [Decidable c] (a b : ℚ) (ha : a ∈ SubInt) (hb : b ∈ SubInt) :
    (if c then a else b) ∈ SubInt := by split; exacts [ha, hb]

theorem IsInt_one : IsInt 1 := by
  intro n; rw [coeff_one]; exact ite_mem _ _ _ SubInt.one_mem SubInt.zero_mem

theorem IsInt_mul {f g : ℚ⟦X⟧} (hf : IsInt f) (hg : IsInt g) : IsInt (f*g) := by
  intro n
  rw [coeff_mul]
  apply Subring.sum_mem
  intro p _
  exact SubInt.mul_mem (hf p.1) (hg p.2)

theorem IsInt_pow {f : ℚ⟦X⟧} (hf : IsInt f) (k : ℕ) : IsInt (f^k) := by
  induction k with
  | zero => simpa using IsInt_one
  | succ k ih => rw [pow_succ]; exact IsInt_mul ih hf

theorem IsInt_geomN (n : ℕ) : IsInt (geomN n) := by
  intro m; rw [geomN, coeff_mk]; exact ite_mem _ _ _ SubInt.one_mem SubInt.zero_mem

theorem IsInt_oneSubXpow (k : ℕ) : IsInt ((1:ℚ⟦X⟧) - X^k) := by
  intro n; rw [map_sub, coeff_X_pow, coeff_one]
  exact Subring.sub_mem _ (ite_mem _ _ _ SubInt.one_mem SubInt.zero_mem)
    (ite_mem _ _ _ SubInt.one_mem SubInt.zero_mem)

-- the units: U i = 1 - X^(i+1)
def Uunit (i : ℕ) : ℚ⟦X⟧ˣ := unitN (i+1) (by omega)

theorem coeff_LD_Uunit (i j : ℕ) :
    coeff j (LD (Uunit i)) = if (i+1) ∣ (j+1) then -((i+1:ℕ):ℚ) else 0 :=
  coeff_LD_unitN (i+1) (by omega) j

theorem Uunit_val (i : ℕ) : ((Uunit i : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) = 1 - X^(i+1) := rfl
theorem Uunit_inv_val (i : ℕ) : (((Uunit i)⁻¹ : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) = geomN (i+1) := rfl

theorem IsInt_zpow (i : ℕ) (z : ℤ) : IsInt ((((Uunit i)^z : ℚ⟦X⟧ˣ)) : ℚ⟦X⟧) := by
  refine Int.induction_on z ?_ ?_ ?_
  · rw [zpow_zero, Units.val_one]; exact IsInt_one
  · intro n ih
    rw [zpow_add_one, Units.val_mul, Uunit_val]
    exact IsInt_mul ih (IsInt_oneSubXpow _)
  · intro n ih
    rw [zpow_sub_one, Units.val_mul, Uunit_inv_val]
    exact IsInt_mul ih (IsInt_geomN _)


theorem IsInt_finprod {ι : Type*} (s : Finset ι) (h : ι → ℚ⟦X⟧)
    (hh : ∀ i ∈ s, IsInt (h i)) : IsInt (∏ i ∈ s, h i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using IsInt_one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact IsInt_mul (hh i (Finset.mem_insert_self i s))
      (ih (fun j hj => hh j (Finset.mem_insert_of_mem hj)))

def Pk (t : ℕ → ℤ) (k : ℕ) : ℚ⟦X⟧ˣ :=
  ∏ i ∈ Finset.range k, (Uunit i) ^ (- wInt t (i+1))

theorem val_Pk (t : ℕ → ℤ) (k : ℕ) :
    ((Pk t k : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) = ∏ i ∈ Finset.range k, (((Uunit i) ^ (- wInt t (i+1)) : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) := by
  rw [Pk, ← Units.coeHom_apply, map_prod]; rfl

theorem IsInt_Pk (t : ℕ → ℤ) (k : ℕ) : IsInt ((Pk t k : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) := by
  rw [val_Pk]
  exact IsInt_finprod _ _ (fun i _ => IsInt_zpow i _)

theorem constCoeff_Uunit_zpow (i : ℕ) (z : ℤ) :
    constantCoeff (((Uunit i) ^ z : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) = 1 := by
  refine Int.induction_on z ?_ ?_ ?_
  · rw [zpow_zero, Units.val_one, map_one]
  · intro n ih
    rw [zpow_add_one, Units.val_mul, map_mul, ih, Uunit_val, map_sub, map_one, one_mul]
    have : constantCoeff ((X:ℚ⟦X⟧)^(i+1)) = 0 := by
      rw [map_pow, constantCoeff_X]; simp
    rw [this, sub_zero]
  · intro n ih
    rw [zpow_sub_one, Units.val_mul, map_mul, ih, Uunit_inv_val, one_mul, geomN,
      ← coeff_zero_eq_constantCoeff, coeff_mk, if_pos (dvd_zero _)]

theorem constCoeff_Pk (t : ℕ → ℤ) (k : ℕ) :
    constantCoeff ((Pk t k : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) = 1 := by
  rw [val_Pk, map_prod]
  apply Finset.prod_eq_one
  intro i _
  exact constCoeff_Uunit_zpow i _

theorem LD_spec (u : ℚ⟦X⟧ˣ) : derivativeFun (u : ℚ⟦X⟧) = LD u * (u : ℚ⟦X⟧) := by
  rw [LD, mul_assoc]
  have : (((u⁻¹ : ℚ⟦X⟧ˣ) : ℚ⟦X⟧)) * (u : ℚ⟦X⟧) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [this, mul_one]

theorem coeff_LD_Pk (t : ℕ → ℤ) (k j : ℕ) (hjk : j < k)
    (hw : ∀ m : ℕ, 1 ≤ m → (m:ℤ) ∣ ∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m/d):ℤ) * t d) :
    coeff j (LD (Pk t k)) = (t (j+1) : ℚ) := by
  have hLD : LD (Pk t k) = ∑ i ∈ Finset.range k, (- wInt t (i+1)) • LD (Uunit i) := by
    rw [Pk, LD_prod]
    apply Finset.sum_congr rfl
    intro i _; rw [LD_zpow]
  rw [hLD, map_sum]
  -- coeff j of each smul term
  have hterm : ∀ i ∈ Finset.range k,
      coeff j ((- wInt t (i+1)) • LD (Uunit i))
        = (if (i+1) ∣ (j+1) then ((i+1:ℕ):ℚ) * (wInt t (i+1)) else 0) := by
    intro i _
    rw [map_zsmul, coeff_LD_Uunit]
    by_cases hd : (i+1) ∣ (j+1)
    · rw [if_pos hd, if_pos hd, zsmul_eq_mul]; push_cast; ring
    · rw [if_neg hd, if_neg hd, smul_zero]
  rw [Finset.sum_congr rfl hterm]
  -- now reindex to divisors of j+1
  have hbij : ∑ i ∈ Finset.range k, (if (i+1) ∣ (j+1) then ((i+1:ℕ):ℚ) * (wInt t (i+1)) else 0)
      = ∑ n ∈ (j+1).divisors, ((n:ℚ) * (wInt t n)) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_nbij' (fun i => i + 1) (fun n => n - 1)
    · intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      rw [Nat.mem_divisors]; exact ⟨hi.2, by omega⟩
    · intro n hn
      rw [Nat.mem_divisors] at hn
      have hn1 : 1 ≤ n := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr hn)
      have hnle : n ≤ j + 1 := Nat.le_of_dvd (by omega) hn.1
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [Nat.sub_add_cancel hn1]; exact hn.1
    · intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi; omega
    · intro n hn
      rw [Nat.mem_divisors] at hn
      have hn1 : 1 ≤ n := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr hn)
      omega
    · intro i hi
      rfl
  rw [hbij]
  have hneck := necklace_w t (j+1) (by omega) hw
  rw [← hneck]
  push_cast
  apply Finset.sum_congr rfl
  intro n _; push_cast; ring

theorem aq_integral (t : ℕ → ℤ)
    (hw : ∀ m : ℕ, 1 ≤ m → (m:ℤ) ∣ ∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m/d):ℤ) * t d)
    (k : ℕ) :
    ∃ z : ℤ, Aq (fun i => (t i : ℚ)) k = (z : ℚ) := by
  set d : ℕ → ℚ := fun i => (t i : ℚ) with hd
  have hmatch : coeff k (fps d) = coeff k ((Pk t k : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) := by
    have key := ode_unique_trunc (LD (Pk t k)) (driver d)
      ((Pk t k : ℚ⟦X⟧ˣ) : ℚ⟦X⟧) (fps d)
      (LD_spec (Pk t k)) (derivative_fps d)
      (by rw [constCoeff_Pk, constantCoeff_fps]) k
      (by
        intro j hj
        rw [coeff_LD_Pk t k j hj hw, driver, coeff_mk])
      k (le_refl k)
    exact key.symm
  have hAq : Aq d k = coeff k (fps d) := by rw [fps, coeff_mk]
  rw [hAq, hmatch]
  obtain ⟨z, hz⟩ := IsInt_Pk t k k
  exact ⟨z, hz.symm⟩


noncomputable def gecD (d : ℕ → ℕ) : ℕ → ℕ
| 0 => 1
| k' + 1 =>
  let k := k' + 1
  (Finset.sum (Finset.range k) fun j => (d (j + 1)) * (gecD d (k - (j + 1)))) / k

theorem Aq_nonneg (d : ℕ → ℚ) (hd : ∀ i, 0 ≤ d i) (k : ℕ) : 0 ≤ Aq d k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => rw [Aq_zero]; norm_num
    | (m+1) =>
      rw [Aq]
      apply div_nonneg
      · apply Finset.sum_nonneg
        intro j hj
        rw [Finset.mem_range] at hj
        exact mul_nonneg (hd _) (ih (m - j) (by omega))
      · positivity

theorem gecD_eq_Aq (d : ℕ → ℕ)
    (hint : ∀ j, ∃ z : ℕ, Aq (fun i => (d i : ℚ)) j = (z : ℚ)) (k : ℕ) :
    (gecD d k : ℚ) = Aq (fun i => (d i : ℚ)) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => rw [gecD, Aq_zero]; norm_num
    | (m+1) =>
      set d' : ℕ → ℚ := fun i => (d i : ℚ) with hd'
      -- numerator as a nat
      set SN : ℕ := ∑ j ∈ Finset.range (m+1), d (j+1) * gecD d (m+1 - (j+1)) with hSN
      have hgec : gecD d (m+1) = SN / (m+1) := by rw [gecD]
      -- Aq numerator equals SN cast
      have haq : Aq d' (m+1) = (SN : ℚ) / ((m:ℚ)+1) := by
        rw [Aq]
        congr 1
        rw [hSN]
        push_cast
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        rw [← ih (m-j) (by omega)]
      obtain ⟨z, hz⟩ := hint (m+1)
      rw [hd'] at hz
      rw [haq] at hz
      -- (SN:ℚ)/(m+1) = z  ⟹ SN = (m+1)*z
      have hm1 : ((m:ℚ)+1) ≠ 0 := by positivity
      have hSNz : (SN : ℚ) = ((m+1)*z : ℕ) := by
        field_simp at hz
        push_cast
        push_cast at hz
        linarith [hz]
      have hSNnat : SN = (m+1)*z := by exact_mod_cast hSNz
      have hdiv : SN / (m+1) = z := by
        rw [hSNnat]; exact Nat.mul_div_cancel_left z (by omega)
      rw [hgec, hdiv]
      rw [haq]
      rw [hSNnat]
      push_cast
      field_simp



theorem cm_bridge (m N : ℕ) (hN : 1 ≤ N) :
    ((gecD (fun k => N * cm m k) N : ℕ) : ℚ)
      = coeff N ((fps (fun i => (cm m i : ℚ)))^N) := by
  set t : ℕ → ℤ := fun i => ((N * cm m i : ℕ) : ℤ) with ht
  have hw : ∀ mm : ℕ, 1 ≤ mm →
      (mm:ℤ) ∣ ∑ d ∈ mm.divisors, (ArithmeticFunction.moebius (mm/d):ℤ) * t d := by
    intro mm hmm
    apply gauss_dvd hmm t
    intro p hpp k v hkv
    have h := cm_gauss_dvd (p:=p) (k:=k) (v:=v) m hpp hkv
    have he : t (p*k) - t k = (N:ℤ) * ((cm m (p*k):ℤ) - (cm m k:ℤ)) := by
      simp only [ht]; push_cast; ring
    rw [he]; exact h.mul_left _
  have hint : ∀ j, ∃ z : ℕ, Aq (fun i => ((N*cm m i:ℕ):ℚ)) j = (z:ℚ) := by
    intro j
    obtain ⟨z, hz⟩ := aq_integral t hw j
    have hnn : 0 ≤ Aq (fun i => ((N*cm m i:ℕ):ℚ)) j :=
      Aq_nonneg _ (fun i => by positivity) j
    have hfun : (fun i => (t i : ℚ)) = (fun i => ((N*cm m i:ℕ):ℚ)) := by
      funext i; simp only [ht, Int.cast_natCast]
    rw [hfun] at hz
    have hz0 : 0 ≤ z := by rw [hz] at hnn; exact_mod_cast hnn
    exact ⟨z.toNat, by rw [hz]; exact_mod_cast (Int.toNat_of_nonneg hz0).symm⟩
  have hge := gecD_eq_Aq (fun k => N * cm m k) hint N
  rw [hge]
  have hcast : (fun i => ((N*cm m i:ℕ):ℚ)) = (fun i => (N:ℚ)*(cm m i:ℚ)) := by
    funext i; push_cast; ring
  rw [hcast,
    show Aq (fun i => (N:ℚ)*(cm m i:ℚ)) N
        = coeff N (fps (fun i => (N:ℚ)*(cm m i:ℚ))) by rw [fps, coeff_mk],
    fps_smul_eq_pow N hN (fun i => (cm m i:ℚ))]


theorem dvd_of_padicValRat {p : ℕ} [Fact p.Prime] (D : ℤ) (k : ℕ)
    (h : (k:ℤ) ≤ padicValRat p (D:ℚ)) : (p:ℤ)^k ∣ D := by
  rw [padicValRat.of_int] at h
  have hk : k ≤ padicValInt p D := by exact_mod_cast h
  exact (padicValInt_dvd_iff k D).mpr (Or.inr hk)

theorem cc_Gfrob {p : ℕ} (hp : p ≠ 0) (f : ℚ⟦X⟧) (hf : constantCoeff f = 1) :
    constantCoeff (Gfrob hp f) = 1 := by
  rw [Gfrob, map_mul, map_pow, hf, one_pow, one_mul, constantCoeff_inv,
    constantCoeff_expand, hf, inv_one]

theorem fA_cc (m : ℕ) : constantCoeff (fps (fun i => (cm m i:ℚ))) = 1 := constantCoeff_fps _

-- the key analytic bound (to be proved)
theorem key_bound {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (m N a' : ℕ) (hN : 1 ≤ N)
    (ha' : a' < N)
    (h1 : coeff a' ((fps (fun i => (cm m i:ℚ)))^N) ≠ 0)
    (h2 : coeff (p*(N-a')) ((Gfrob (show p ≠ 0 by omega) (fps (fun i => (cm m i:ℚ))))^N) ≠ 0) :
    (3*(padicValNat p N + 1):ℤ)
      ≤ padicValRat p (coeff a' ((fps (fun i => (cm m i:ℚ)))^N))
        + padicValRat p (coeff (p*(N-a')) ((Gfrob (show p ≠ 0 by omega) (fps (fun i => (cm m i:ℚ))))^N)) := by
  sorry

theorem super_dvd (m n r p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    (p:ℤ)^(3*r) ∣
      ((gecD (fun k => (n*p^r) * cm m k) (n*p^r) : ℤ)
        - (gecD (fun k => (n*p^(r-1)) * cm m k) (n*p^(r-1)) : ℤ)) := by
  have hp0 : p ≠ 0 := by omega
  set N := n*p^(r-1) with hNdef
  have hN1 : 1 ≤ N := by
    rw [hNdef]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hpr : p^r = p * p^(r-1) := by rw [← pow_succ', Nat.sub_add_cancel hr]
  have hM : n*p^r = p*N := by rw [hNdef, hpr]; ring
  set f := fps (fun i => (cm m i:ℚ)) with hf
  have hfcc : constantCoeff f = 1 := fA_cc m
  -- bridge
  have hbM : ((gecD (fun k => (n*p^r) * cm m k) (n*p^r) : ℕ):ℚ) = coeff (p*N) (f^(p*N)) := by
    rw [hM]; exact cm_bridge m (p*N) (Nat.mul_pos (by omega) hN1)
  have hbN : ((gecD (fun k => N * cm m k) N : ℕ):ℚ) = coeff N (f^N) := cm_bridge m N hN1
  -- difference as ℚ
  set D : ℤ := (gecD (fun k => (n*p^r) * cm m k) (n*p^r) : ℤ)
        - (gecD (fun k => N * cm m k) N : ℤ) with hD
  have hDQ : (D:ℚ) = coeff (p*N) (f^(p*N)) - coeff N (f^N) := by
    rw [hD]; push_cast; rw [hbM, hbN]
  -- reduction
  have hred := reduction hp0 f hfcc N
  have hsucc : ∑ a' ∈ Finset.range (N+1),
      coeff a' (f^N) * coeff (p*(N-a')) ((Gfrob hp0 f)^N)
      = (∑ a' ∈ Finset.range N, coeff a' (f^N) * coeff (p*(N-a')) ((Gfrob hp0 f)^N))
        + coeff N (f^N) := by
    rw [Finset.sum_range_succ]
    congr 1
    have hc0 : coeff 0 ((Gfrob hp0 f)^N) = 1 := by
      rw [coeff_zero_eq_constantCoeff, map_pow, cc_Gfrob hp0 f hfcc, one_pow]
    rw [Nat.sub_self, Nat.mul_zero, hc0, mul_one]
  rw [hsucc] at hred
  have hDsum : (D:ℚ) = ∑ a' ∈ Finset.range N, coeff a' (f^N) * coeff (p*(N-a')) ((Gfrob hp0 f)^N) := by
    rw [hDQ, hred]; ring
  -- now bound
  by_cases hD0 : D = 0
  · rw [hD0]; exact dvd_zero _
  apply dvd_of_padicValRat
  rw [hDsum]
  have hge : (3*r:ℤ) ≤ 3*(padicValNat p N + 1) := by
    have : (r:ℤ) ≤ padicValNat p N + 1 := by
      have hvN : r - 1 ≤ padicValNat p N := by
        rw [hNdef, padicValNat.mul (by positivity) (by positivity), padicValNat.prime_pow]
        omega
      omega
    omega
  refine le_trans hge ?_
  -- sum bound
  have hDne : (D:ℚ) ≠ 0 := by exact_mod_cast hD0
  have hb : ∀ a' ∈ Finset.range N,
      coeff a' (f^N) * coeff (p*(N-a')) ((Gfrob hp0 f)^N) ≠ 0 →
      (3*(padicValNat p N + 1):ℤ)
        ≤ padicValRat p (coeff a' (f^N) * coeff (p*(N-a')) ((Gfrob hp0 f)^N)) := by
    intro a' ha' hne
    rw [Finset.mem_range] at ha'
    have hf1 : coeff a' (f^N) ≠ 0 := by rintro h; rw [h, zero_mul] at hne; exact hne rfl
    have hf2 : coeff (p*(N-a')) ((Gfrob hp0 f)^N) ≠ 0 := by rintro h; rw [h, mul_zero] at hne; exact hne rfl
    rw [padicValRat.mul hf1 hf2]
    exact key_bound hp5 m N a' hN1 ha' hf1 hf2
  rcases le_padicValRat_sum (p:=p) (Finset.range N)
      (fun a' => coeff a' (f^N) * coeff (p*(N-a')) ((Gfrob hp0 f)^N))
      (3*(padicValNat p N + 1)) hb with h0 | hpos
  · exact absurd (by rw [hDsum]; exact h0) hDne
  · exact hpos


end Dev

end

-- Glue: gecD equals the private generalized_exp_coeff (identical recursion)
theorem gecD_eq_gen (d : ℕ → ℕ) : ∀ k, Dev.gecD d k = generalized_exp_coeff d k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero => rw [Dev.gecD, generalized_exp_coeff]
    | succ k' =>
      rw [Dev.gecD, generalized_exp_coeff]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [ih (k'+1 - (j+1)) (by omega)]

theorem general_supercongruence_conjecture (m n r p : ℕ) (hp : Nat.Prime p)
    (hp5 : p ≥ 5) (hm : m ≥ 1) (hn : n ≥ 1) (hr : r ≥ 1) :
    b_m_int m (n * p ^ r) ≡ b_m_int m (n * p ^ (r - 1)) [ZMOD (p ^ (3 * r) : ℤ)] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp5' : 5 ≤ p := hp5
  -- unfold b_m_int for positive arguments
  have key : ∀ M : ℕ, 1 ≤ M →
      b_m_int m M = (Dev.gecD (fun k => M * cm m k) M : ℤ) := by
    intro M hM
    rw [b_m_int]
    simp only [Nat.one_le_iff_ne_zero.mp hM, if_false]
    rw [gecD_eq_gen]
    norm_cast
  have hM1 : 1 ≤ n * p ^ r := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hM2 : 1 ≤ n * p ^ (r-1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [key _ hM1, key _ hM2]
  rw [Int.modEq_iff_dvd]
  have hd := Dev.super_dvd m n r p hp5' hn hr
  -- hd : p^(3r) ∣ (gecD M1 - gecD M2)
  -- goal : p^(3r) ∣ (gecD M2 - gecD M1)
  rcases hd with ⟨c, hc⟩
  exact ⟨-c, by rw [← neg_sub]; rw [hc]; ring⟩
