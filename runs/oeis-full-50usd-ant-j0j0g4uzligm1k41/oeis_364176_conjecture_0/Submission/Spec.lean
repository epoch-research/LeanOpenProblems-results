import FormalConjectures.Util.ProblemImports

open Real Nat Finset

/--
A364176 term:
$$a(n) = \frac{(15n)! (5n/2)! (2n)!}{(15n/2)! (6n)! (5n)! n!}$$
where integer factorials are evaluated using `Nat.factorial`, and fractional factorials $x!$ are defined as $\Gamma(x+1)$.
-/
noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n.cast
  let num_int_15 : ℝ := (15 * n).factorial.cast
  let num_int_2 : ℝ := (2 * n).factorial.cast
  let num_frac_5_halves : ℝ := Real.Gamma (5 * n_r / 2 + 1)

  let den_frac_15_halves : ℝ := Real.Gamma (15 * n_r / 2 + 1)
  let den_int_6 : ℝ := (6 * n).factorial.cast
  let den_int_5 : ℝ := (5 * n).factorial.cast
  let den_int_1 : ℝ := n.factorial.cast

  (num_int_15 * num_frac_5_halves * num_int_2) /
  (den_frac_15_halves * den_int_6 * den_int_5 * den_int_1)

/-! ## Foundational lemmas -/

theorem sum_units_sq_eq_zero (n : ℕ) [NeZero n] (h2 : IsUnit (2 : ZMod n)) (h3 : IsUnit (3 : ZMod n)) :
    ∑ u : (ZMod n)ˣ, ((u : ZMod n))^2 = 0 := by
  set u2 := h2.unit with hu2
  have hspec : (u2 : ZMod n) = 2 := h2.unit_spec
  set S := ∑ u : (ZMod n)ˣ, ((u : ZMod n))^2 with hS
  have reindex : ∑ u : (ZMod n)ˣ, (((u2 * u : (ZMod n)ˣ) : ZMod n))^2 = S := by
    rw [hS]; exact Equiv.sum_comp (Equiv.mulLeft u2) (fun v => ((v : ZMod n))^2)
  have expand : ∑ u : (ZMod n)ˣ, (((u2 * u : (ZMod n)ˣ) : ZMod n))^2 = 4 * S := by
    rw [hS, Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _
    push_cast; rw [hspec]; ring
  have hEq : S = 4 * S := reindex.symm.trans expand
  have h3S : (3 : ZMod n) * S = 0 := by linear_combination -hEq
  exact h3.mul_right_eq_zero.mp h3S

theorem prod_add_delta {ι : Type*} [DecidableEq ι] (s : Finset ι) (b : ι → ℤ) (δ : ℤ) :
    (∏ i ∈ s, (b i + δ)) ≡ (∏ i ∈ s, b i) + δ * (∑ i ∈ s, ∏ j ∈ s.erase i, b j) [ZMOD δ^2] := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hcong : (b a + δ) * (∏ i ∈ s, (b i + δ)) ≡
        (b a + δ) * ((∏ i ∈ s, b i) + δ * (∑ i ∈ s, ∏ j ∈ s.erase i, b j)) [ZMOD δ^2] :=
      Int.ModEq.mul_left _ ih
    refine hcong.trans ?_
    have e1 : ∏ j ∈ (insert a s).erase a, b j = ∏ j ∈ s, b j := by rw [Finset.erase_insert ha]
    have e2 : ∀ i ∈ s, ∏ j ∈ (insert a s).erase i, b j = b a * ∏ j ∈ s.erase i, b j := by
      intro i hi
      rw [Finset.erase_insert_of_ne (by rintro rfl; exact ha hi)]
      rw [Finset.prod_insert (by simp [Finset.mem_erase]; tauto)]
    rw [e1]
    calc (b a + δ) * ((∏ i ∈ s, b i) + δ * (∑ i ∈ s, ∏ j ∈ s.erase i, b j))
        = (b a * (∏ i ∈ s, b i)) + δ * ((∏ i ∈ s, b i) + b a * (∑ i ∈ s, ∏ j ∈ s.erase i, b j)) + δ^2 * (∑ i ∈ s, ∏ j ∈ s.erase i, b j) := by ring
      _ ≡ (b a * (∏ i ∈ s, b i)) + δ * ((∏ i ∈ s, b i) + b a * (∑ i ∈ s, ∏ j ∈ s.erase i, b j)) + 0 [ZMOD δ^2] := by
            apply Int.ModEq.add_left
            exact (Int.modEq_zero_iff_dvd.mpr (dvd_mul_right (δ^2) _))
      _ = (b a * ∏ i ∈ s, b i) + δ * ((∏ i ∈ s, b i) + ∑ i ∈ s, b a * ∏ j ∈ s.erase i, b j) := by
            rw [Finset.mul_sum]; ring
      _ = (b a * ∏ i ∈ s, b i) + δ * ((∏ j ∈ s, b j) + ∑ i ∈ s, ∏ j ∈ (insert a s).erase i, b j) := by
            rw [Finset.sum_congr rfl e2]

theorem prod_pair {M : Type*} [CommMonoid M] (q : ℕ) (hq : Odd q) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ e, 1 ≤ e → e ≤ q - 1 → (P e ↔ P (q - e))) (f : ℕ → M) :
    ∏ e ∈ (Finset.Icc 1 (q-1)).filter P, f e
      = ∏ e ∈ (Finset.Icc 1 ((q-1)/2)).filter P, (f e * f (q - e)) := by
  obtain ⟨k, hk⟩ := hq
  have hqpos : 1 ≤ q := by omega
  set L := (Finset.Icc 1 ((q-1)/2)).filter P with hL
  set Up := (Finset.Icc ((q-1)/2 + 1) (q-1)).filter P with hUp
  have hsplit : (Finset.Icc 1 (q-1)).filter P = L ∪ Up := by
    rw [hL, hUp, ← Finset.filter_union]; congr 1
    ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint L Up := by
    rw [hL, hUp]; apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_Icc] at ha hb; omega
  have hinj : Set.InjOn (fun e => q - e) L := by
    intro a ha b hb hab
    simp only [hL, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha hb
    simp only at hab; omega
  have himg : Up = L.image (fun e => q - e) := by
    ext x
    simp only [hUp, hL, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hx1, hx2⟩, hPx⟩
      refine ⟨q - x, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      have := (hP (q - x) (by omega) (by omega))
      rw [show q - (q - x) = x by omega] at this
      exact this.mpr hPx
    · rintro ⟨e, ⟨⟨he1, he2⟩, hPe⟩, rfl⟩
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      exact (hP e (by omega) (by omega)).mp hPe
  rw [hsplit, Finset.prod_union hdisj, himg, Finset.prod_image hinj, ← Finset.prod_mul_distrib]

theorem sum_pair {M : Type*} [AddCommMonoid M] (q : ℕ) (hq : Odd q) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ e, 1 ≤ e → e ≤ q - 1 → (P e ↔ P (q - e))) (f : ℕ → M) :
    ∑ e ∈ (Finset.Icc 1 (q-1)).filter P, f e
      = ∑ e ∈ (Finset.Icc 1 ((q-1)/2)).filter P, (f e + f (q - e)) := by
  obtain ⟨k, hk⟩ := hq
  have hqpos : 1 ≤ q := by omega
  set L := (Finset.Icc 1 ((q-1)/2)).filter P with hL
  set Up := (Finset.Icc ((q-1)/2 + 1) (q-1)).filter P with hUp
  have hsplit : (Finset.Icc 1 (q-1)).filter P = L ∪ Up := by
    rw [hL, hUp, ← Finset.filter_union]; congr 1
    ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint L Up := by
    rw [hL, hUp]; apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_Icc] at ha hb; omega
  have hinj : Set.InjOn (fun e => q - e) L := by
    intro a ha b hb hab
    simp only [hL, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha hb
    simp only at hab; omega
  have himg : Up = L.image (fun e => q - e) := by
    ext x
    simp only [hUp, hL, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hx1, hx2⟩, hPx⟩
      refine ⟨q - x, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      have := (hP (q - x) (by omega) (by omega))
      rw [show q - (q - x) = x by omega] at this
      exact this.mpr hPx
    · rintro ⟨e, ⟨⟨he1, he2⟩, hPe⟩, rfl⟩
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      exact (hP e (by omega) (by omega)).mp hPe
  rw [hsplit, Finset.sum_union hdisj, himg, Finset.sum_image hinj, ← Finset.sum_add_distrib]

theorem sum_Ucop_eq_units {M : Type*} [AddCommMonoid M] (q : ℕ) [NeZero q] (hq : 1 < q) (g : ZMod q → M) :
    ∑ e ∈ (Finset.Icc 1 (q-1)).filter (fun e => Nat.Coprime e q), g (e : ZMod q)
      = ∑ u : (ZMod q)ˣ, g (u : ZMod q) := by
  haveI : Fact (1 < q) := ⟨hq⟩
  refine Finset.sum_bij'
    (i := fun e he => ZMod.unitOfCoprime e ((Finset.mem_filter.mp he).2))
    (j := fun u _ => (u : ZMod q).val)
    (fun a ha => Finset.mem_univ _) ?_ ?_ ?_ ?_
  · intro u _
    dsimp only
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ZMod.val_coe_unit_coprime u⟩
    · have h0 : (u : ZMod q) ≠ 0 := u.isUnit.ne_zero
      have hv0 : (u : ZMod q).val ≠ 0 := fun h => h0 ((ZMod.val_eq_zero _).mp h)
      omega
    · have := ZMod.val_lt (u : ZMod q); omega
  · intro a ha
    dsimp only
    have ha' := Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  · intro u _
    dsimp only
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime, ZMod.natCast_val, ZMod.cast_id]
  · intro a ha
    dsimp only
    rw [ZMod.coe_unitOfCoprime]

/- Generalized Wolstenholme (W2) for q = p^r -/

theorem neg_inv_sq {n:ℕ} (a : ZMod n) (h : IsUnit a) : ((-a)⁻¹)^2 = (a⁻¹)^2 := by
  obtain ⟨u, rfl⟩ := h
  have h1 : (-(↑u:ZMod n)) = ↑((-1) * u) := by push_cast; ring
  rw [h1, ZMod.inv_coe_unit, ZMod.inv_coe_unit, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
  congr 1
  rw [mul_inv_rev, mul_pow]
  simp


theorem zmod_inv_sq {n:ℕ}(a:ZMod n)(h:IsUnit a): (a⁻¹)^2 = (a^2)⁻¹ := by
  obtain ⟨u,rfl⟩ := h
  rw [ZMod.inv_coe_unit, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ZMod.inv_coe_unit, inv_pow]

theorem zmod_neg_inv {n:ℕ}(a:ZMod n)(h:IsUnit a): (-a)⁻¹ = -(a⁻¹) := by
  obtain ⟨u,rfl⟩ := h
  rw [← Units.val_neg, ZMod.inv_coe_unit, ZMod.inv_coe_unit, ← Units.val_neg]
  congr 1

theorem zmod_mul_inv {n:ℕ}(a b:ZMod n)(ha:IsUnit a)(hb:IsUnit b): (a*b)⁻¹ = a⁻¹*b⁻¹ := by
  obtain ⟨u,rfl⟩ := ha; obtain ⟨v,rfl⟩ := hb
  rw [← Units.val_mul, ZMod.inv_coe_unit, ZMod.inv_coe_unit, ZMod.inv_coe_unit,
      ← Units.val_mul, mul_inv_rev, mul_comm]


theorem zmod_leave_one {n:ℕ}{ι:Type*}[DecidableEq ι](s:Finset ι)(f:ι→ZMod n)(e:ι)(he:e∈s)
    (hu:IsUnit (f e)) : (∏ e' ∈ s, f e') * (f e)⁻¹ = ∏ e' ∈ s.erase e, f e' := by
  have h1 : f e * ∏ e' ∈ s.erase e, f e' = ∏ e' ∈ s, f e' := Finset.mul_prod_erase s f he
  have h2 : (f e)⁻¹ * f e = 1 := ZMod.inv_mul_of_unit _ hu
  calc (∏ e' ∈ s, f e') * (f e)⁻¹ = ((f e)⁻¹ * f e) * ∏ e' ∈ s.erase e, f e' := by rw [← h1]; ring
    _ = ∏ e' ∈ s.erase e, f e' := by rw [h2, one_mul]

section Wolstenholme
variable (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r)
include hp hp5 hr

theorem coprime_iff_not_dvd (e : ℕ) : Nat.Coprime e (p^r) ↔ ¬ p ∣ e := by
  rw [Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm, hp.coprime_iff_not_dvd]

theorem two_unit : IsUnit (2 : ZMod (p^r)) := by
  rw [show (2:ZMod (p^r)) = ((2:ℕ):ZMod (p^r)) by push_cast; ring, ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.pow_right r ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega))

theorem three_unit : IsUnit (3 : ZMod (p^r)) := by
  rw [show (3:ZMod (p^r)) = ((3:ℕ):ZMod (p^r)) by push_cast; ring, ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.pow_right r ((Nat.coprime_primes (by norm_num) hp).mpr (by omega))

theorem full_W2 :
    ∑ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((e:ZMod (p^r))⁻¹)^2 = 0 := by
  have hq : 1 < p^r := by
    have : p^1 ≤ p^r := Nat.pow_le_pow_right (by omega) hr
    simp at this; omega
  haveI : NeZero (p^r) := ⟨by omega⟩
  have hfe : (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e)
           = (Finset.Icc 1 (p^r-1)).filter (fun e => Nat.Coprime e (p^r)) := by
    apply Finset.filter_congr; intro e _; rw [coprime_iff_not_dvd p r hp hp5 hr]
  rw [hfe]
  rw [sum_Ucop_eq_units (p^r) hq (fun x => (x⁻¹)^2)]
  have : ∀ u : (ZMod (p^r))ˣ, ((u:ZMod (p^r))⁻¹)^2 = ((u⁻¹ : (ZMod (p^r))ˣ):ZMod (p^r))^2 := by
    intro u; rw [ZMod.inv_coe_unit]
  simp_rw [this]
  refine (Fintype.sum_bijective (fun x : (ZMod (p^r))ˣ => x⁻¹) (Equiv.inv _).bijective
    (fun x => ((x⁻¹:(ZMod (p^r))ˣ):ZMod (p^r))^2) (fun x => ((x:ZMod (p^r)))^2) (fun x => rfl)).trans ?_
  exact sum_units_sq_eq_zero _ (two_unit p r hp hp5 hr) (three_unit p r hp hp5 hr)

theorem half_W2 :
    ∑ e ∈ (Finset.Icc 1 ((p^r-1)/2)).filter (fun e => ¬ p ∣ e), ((e:ZMod (p^r))⁻¹)^2 = 0 := by
  have hq : 1 < p^r := by
    have : p^1 ≤ p^r := Nat.pow_le_pow_right (by omega) hr
    simp at this; omega
  haveI : NeZero (p^r) := ⟨by omega⟩
  have hodd : Odd (p^r) := (hp.odd_of_ne_two (by omega)).pow
  set L := (Finset.Icc 1 ((p^r-1)/2)).filter (fun e => ¬ p ∣ e) with hLdef
  set F : ℕ → ZMod (p^r) := fun e => ((e:ZMod (p^r))⁻¹)^2 with hFdef
  have hP : ∀ e, 1 ≤ e → e ≤ (p^r) - 1 → ((¬ p ∣ e) ↔ (¬ p ∣ (p^r - e))) := by
    intro e he1 he2
    have hpq : p ∣ p^r := dvd_pow_self p (by omega)
    constructor
    · intro h hd; exact h (by have := Nat.dvd_sub hpq hd; rwa [Nat.sub_sub_self (by omega)] at this)
    · intro h hd; exact h (Nat.dvd_sub hpq hd)
  have hpair := sum_pair (p^r) hodd (fun e => ¬ p ∣ e) hP F
  have hterm : ∀ e ∈ L, F e + F (p^r - e) = 2 * F e := by
    intro e he
    simp only [hLdef, Finset.mem_filter, Finset.mem_Icc] at he
    have hele : e ≤ p^r := by omega
    have hcast : ((p^r - e : ℕ) : ZMod (p^r)) = -(e : ZMod (p^r)) := by
      rw [Nat.cast_sub hele, ZMod.natCast_self]; ring
    have hunit : IsUnit ((e:ZMod (p^r))) := by
      rw [ZMod.isUnit_iff_coprime]; exact (coprime_iff_not_dvd p r hp hp5 hr e).mpr he.2
    show F e + F (p^r - e) = 2 * F e
    rw [hFdef]; simp only; rw [hcast, neg_inv_sq _ hunit]; ring
  rw [full_W2 p r hp hp5 hr] at hpair  -- hpair: 0 = ∑_L (F e + F(q-e))
  rw [Finset.sum_congr rfl hterm] at hpair
  rw [← Finset.mul_sum] at hpair
  have h2 := two_unit p r hp hp5 hr
  have := h2.mul_right_eq_zero.mp hpair.symm
  exact this

theorem block_cong (c : ℕ) :
    (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((c*p^r + e : ℕ) : ℤ))
      ≡ (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((e:ℕ) : ℤ)) [ZMOD ((p^r : ℕ) : ℤ)^3] := by
  have hq1 : 1 < p^r := by
    have : p^1 ≤ p^r := Nat.pow_le_pow_right (by omega) hr
    simp at this; omega
  haveI : NeZero (p^r) := ⟨by omega⟩
  have hodd : Odd (p^r) := (hp.odd_of_ne_two (by omega)).pow
  have hP : ∀ e, 1 ≤ e → e ≤ (p^r) - 1 → ((¬ p ∣ e) ↔ (¬ p ∣ (p^r - e))) := by
    intro e he1 he2
    have hpq : p ∣ p^r := dvd_pow_self p (by omega)
    constructor
    · intro h hd; exact h (by have := Nat.dvd_sub hpq hd; rwa [Nat.sub_sub_self (by omega)] at this)
    · intro h hd; exact h (Nat.dvd_sub hpq hd)
  set Lf := (Finset.Icc 1 ((p^r-1)/2)).filter (fun e => ¬ p ∣ e) with hLf
  set b : ℕ → ℤ := fun e => (e:ℤ) * ((p^r:ℤ) - (e:ℤ)) with hbdef
  set δ : ℤ := (c:ℤ) * ((c:ℤ)+1) * (p^r:ℤ)^2 with hδdef
  have hLHS := prod_pair (p^r) hodd (fun e => ¬ p ∣ e) hP (fun e => ((c*p^r+e:ℕ):ℤ))
  have hRHS := prod_pair (p^r) hodd (fun e => ¬ p ∣ e) hP (fun e => ((e:ℕ):ℤ))
  rw [hLHS, hRHS]
  have hbe : ∀ e ∈ Lf, ((c*p^r+e:ℕ):ℤ) * ((c*p^r+(p^r-e):ℕ):ℤ) = b e + δ := by
    intro e he
    simp only [hLf, Finset.mem_filter, Finset.mem_Icc] at he
    have hle : e ≤ p^r := by omega
    rw [hbdef, hδdef]; push_cast [Nat.cast_sub hle]; ring
  have hbe2 : ∀ e ∈ Lf, ((e:ℕ):ℤ) * ((p^r-e:ℕ):ℤ) = b e := by
    intro e he
    simp only [hLf, Finset.mem_filter, Finset.mem_Icc] at he
    have hle : e ≤ p^r := by omega
    rw [hbdef]; push_cast [Nat.cast_sub hle]; ring
  rw [Finset.prod_congr rfl hbe, Finset.prod_congr rfl hbe2]
  -- Now: ∏_{Lf}(b e + δ) ≡ ∏_{Lf} b e  [ZMOD (p^r)^3]
  have hpad := prod_add_delta Lf b δ
  have hq3δ2 : ((p^r:ℤ))^3 ∣ δ^2 := ⟨(c:ℤ)^2*((c:ℤ)+1)^2*(p^r:ℤ), by rw [hδdef]; ring⟩
  have h1 := hpad.of_dvd hq3δ2
  -- q ∣ D
  have hunit : ∀ e' ∈ Lf, IsUnit ((e':ZMod (p^r))) := by
    intro e' he'
    simp only [hLf, Finset.mem_filter] at he'
    rw [ZMod.isUnit_iff_coprime]; exact (coprime_iff_not_dvd p r hp hp5 hr e').mpr he'.2
  have hbcast : ∀ e', ((b e' : ℤ) : ZMod (p^r)) = -(((e':ℕ):ZMod (p^r)))^2 := by
    intro e'; rw [hbdef]; push_cast
    rw [show ((p:ZMod (p^r)))^r = 0 by rw [← Nat.cast_pow, ZMod.natCast_self]]; ring
  have hDcast : ((∑ e ∈ Lf, ∏ e' ∈ Lf.erase e, b e' : ℤ) : ZMod (p^r)) = 0 := by
    push_cast
    simp_rw [hbcast]
    have key : ∀ e ∈ Lf, ∏ e' ∈ Lf.erase e, (-(((e':ℕ):ZMod (p^r)))^2)
        = (∏ e' ∈ Lf, (-(((e':ℕ):ZMod (p^r)))^2)) * (-(((e:ℕ):ZMod (p^r)))^2)⁻¹ := by
      intro e he
      rw [zmod_leave_one Lf (fun e' => -(((e':ℕ):ZMod (p^r)))^2) e he
          (((hunit e he).pow 2).neg)]
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
    have hz : ∑ e ∈ Lf, (-(((e:ℕ):ZMod (p^r)))^2)⁻¹ = 0 := by
      have heq : ∀ e ∈ Lf, (-(((e:ℕ):ZMod (p^r)))^2)⁻¹ = -((((e:ℕ):ZMod (p^r)))⁻¹)^2 := by
        intro e he
        rw [zmod_neg_inv _ ((hunit e he).pow 2), zmod_inv_sq _ (hunit e he)]
      rw [Finset.sum_congr rfl heq]
      rw [Finset.sum_neg_distrib, half_W2 p r hp hp5 hr, neg_zero]
    rw [hz, mul_zero]
  have hD : (p^r:ℤ) ∣ (∑ e ∈ Lf, ∏ e' ∈ Lf.erase e, b e') := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p^r)).mp hDcast
    exact_mod_cast this
  have hδD : ((p^r:ℤ))^3 ∣ δ * (∑ e ∈ Lf, ∏ e' ∈ Lf.erase e, b e') := by
    obtain ⟨D', hD'⟩ := hD
    exact ⟨(c:ℤ)*((c:ℤ)+1)*D', by rw [hδdef, hD']; ring⟩
  calc (∏ e ∈ Lf, (b e + δ)) ≡ (∏ e ∈ Lf, b e) + δ * (∑ e ∈ Lf, ∏ e' ∈ Lf.erase e, b e') [ZMOD ((p^r:ℤ))^3] := h1
    _ ≡ (∏ e ∈ Lf, b e) + 0 [ZMOD ((p^r:ℤ))^3] := by
        apply Int.ModEq.add_left; exact (Int.modEq_zero_iff_dvd.mpr hδD)
    _ = ∏ e ∈ Lf, b e := by ring

end Wolstenholme

/- Gauss factorial product and its block structure -/

def Gcop (p N : ℕ) : ℕ := ∏ e ∈ (Finset.Icc 1 N).filter (fun e => ¬ p ∣ e), e

theorem gcop_succ (p q K : ℕ) (hpq : p ∣ q) :
    Gcop p ((K+1)*q) = Gcop p (K*q) * ∏ e ∈ (Finset.Icc 1 q).filter (fun e => ¬ p ∣ e), (K*q + e) := by
  unfold Gcop
  have hexp : (K+1)*q = K*q + q := by ring
  have hsplit : (Finset.Icc 1 ((K+1)*q)).filter (fun e => ¬ p ∣ e)
      = ((Finset.Icc 1 (K*q)).filter (fun e => ¬ p ∣ e))
        ∪ ((Finset.Icc (K*q+1) ((K+1)*q)).filter (fun e => ¬ p ∣ e)) := by
    rw [← Finset.filter_union]; congr 1
    ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint ((Finset.Icc 1 (K*q)).filter (fun e => ¬ p ∣ e))
        ((Finset.Icc (K*q+1) ((K+1)*q)).filter (fun e => ¬ p ∣ e)) := by
    apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_Icc] at ha hb; omega
  rw [hsplit, Finset.prod_union hdisj]
  congr 1
  rw [show (Finset.Icc (K*q+1) ((K+1)*q)).filter (fun e => ¬ p ∣ e)
        = ((Finset.Icc 1 q).filter (fun e => ¬ p ∣ e)).image (fun e => K*q + e) from ?_]
  · rw [Finset.prod_image (by intro a _ b _ h; exact Nat.add_left_cancel h)]
  · ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hx1, hx2⟩, hpx⟩
      refine ⟨x - K*q, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      intro hd; apply hpx
      have h2 : p ∣ K*q := Dvd.dvd.mul_left hpq K
      have := Nat.dvd_add h2 hd
      rwa [Nat.add_sub_cancel' (by omega : K*q ≤ x)] at this
    · rintro ⟨e, ⟨⟨he1, he2⟩, hpe⟩, rfl⟩
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      intro hd; apply hpe
      have h2 : p ∣ K*q := Dvd.dvd.mul_left hpq K
      have := Nat.dvd_sub hd h2
      rwa [Nat.add_sub_cancel_left] at this

theorem core_G (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) (K : ℕ) :
    (Gcop p (K*p^r) : ℤ) ≡ (Gcop p (p^r) : ℤ)^K [ZMOD ((p^r : ℕ) : ℤ)^3] := by
  have hpq : p ∣ p^r := dvd_pow_self p (by omega)
  have hpr1 : 1 ≤ p^r := Nat.one_le_pow _ _ hp.pos
  have hqf : (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e)
           = (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1,h2⟩, hpx⟩
      refine ⟨⟨h1, ?_⟩, hpx⟩
      rcases Nat.lt_or_ge x (p^r) with h|h
      · omega
      · exfalso; have hx : x = p^r := by omega
        rw [hx] at hpx; exact hpx hpq
    · rintro ⟨⟨h1,h2⟩, hpx⟩
      exact ⟨⟨h1, by omega⟩, hpx⟩
  induction K with
  | zero =>
      simp only [Nat.zero_mul, pow_zero]
      unfold Gcop
      norm_num
  | succ K IH =>
      rw [gcop_succ p (p^r) K hpq]
      have hcast : ((Gcop p (K*p^r) * ∏ e ∈ (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e), (K*p^r + e) : ℕ) : ℤ)
          = (Gcop p (K*p^r):ℤ) * ∏ e ∈ (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e), ((K*p^r + e : ℕ):ℤ) := by
        push_cast; ring
      rw [hcast]
      have hGcop : (Gcop p (p^r):ℤ) = ∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((e:ℕ):ℤ) := by
        unfold Gcop; rw [hqf]; push_cast; rfl
      have hblock : (∏ e ∈ (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e), ((K*p^r + e : ℕ):ℤ))
          ≡ (Gcop p (p^r):ℤ) [ZMOD ((p^r:ℕ):ℤ)^3] := by
        rw [hqf, hGcop]
        exact block_cong p r hp hp5 hr K
      calc (Gcop p (K*p^r):ℤ) * ∏ e ∈ (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e), ((K*p^r + e : ℕ):ℤ)
          ≡ (Gcop p (p^r):ℤ)^K * (Gcop p (p^r):ℤ) [ZMOD ((p^r:ℕ):ℤ)^3] := Int.ModEq.mul IH hblock
        _ = (Gcop p (p^r):ℤ)^(K+1) := by rw [pow_succ]


theorem block_cong2 (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) (c : ℕ) :
    (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((c*p^r + 2*e : ℕ) : ℤ))
      ≡ (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((2*e:ℕ) : ℤ)) [ZMOD ((p^r : ℕ) : ℤ)^3] := by
  have hq1 : 1 < p^r := by
    have : p^1 ≤ p^r := Nat.pow_le_pow_right (by omega) hr
    simp at this; omega
  haveI : NeZero (p^r) := ⟨by omega⟩
  have hodd : Odd (p^r) := (hp.odd_of_ne_two (by omega)).pow
  have hP : ∀ e, 1 ≤ e → e ≤ (p^r) - 1 → ((¬ p ∣ e) ↔ (¬ p ∣ (p^r - e))) := by
    intro e he1 he2
    have hpq : p ∣ p^r := dvd_pow_self p (by omega)
    constructor
    · intro h hd; exact h (by have := Nat.dvd_sub hpq hd; rwa [Nat.sub_sub_self (by omega)] at this)
    · intro h hd; exact h (Nat.dvd_sub hpq hd)
  set Lf := (Finset.Icc 1 ((p^r-1)/2)).filter (fun e => ¬ p ∣ e) with hLf
  set b : ℕ → ℤ := fun e => (4:ℤ) * ((e:ℤ) * ((p^r:ℤ) - (e:ℤ))) with hbdef
  set δ : ℤ := (c:ℤ) * ((c:ℤ)+2) * (p^r:ℤ)^2 with hδdef
  have hLHS := prod_pair (p^r) hodd (fun e => ¬ p ∣ e) hP (fun e => ((c*p^r+2*e:ℕ):ℤ))
  have hRHS := prod_pair (p^r) hodd (fun e => ¬ p ∣ e) hP (fun e => ((2*e:ℕ):ℤ))
  rw [hLHS, hRHS]
  have hbe : ∀ e ∈ Lf, ((c*p^r+2*e:ℕ):ℤ) * ((c*p^r+2*(p^r-e):ℕ):ℤ) = b e + δ := by
    intro e he
    simp only [hLf, Finset.mem_filter, Finset.mem_Icc] at he
    have hle : e ≤ p^r := by omega
    rw [hbdef, hδdef]; push_cast [Nat.cast_sub hle]; ring
  have hbe2 : ∀ e ∈ Lf, ((2*e:ℕ):ℤ) * ((2*(p^r-e):ℕ):ℤ) = b e := by
    intro e he
    simp only [hLf, Finset.mem_filter, Finset.mem_Icc] at he
    have hle : e ≤ p^r := by omega
    rw [hbdef]; push_cast [Nat.cast_sub hle]; ring
  rw [Finset.prod_congr rfl hbe, Finset.prod_congr rfl hbe2]
  have hpad := prod_add_delta Lf b δ
  have hq3δ2 : ((p^r:ℤ))^3 ∣ δ^2 := ⟨(c:ℤ)^2*((c:ℤ)+2)^2*(p^r:ℤ), by rw [hδdef]; ring⟩
  have h1 := hpad.of_dvd hq3δ2
  have hunit : ∀ e' ∈ Lf, IsUnit ((e':ZMod (p^r))) := by
    intro e' he'
    simp only [hLf, Finset.mem_filter] at he'
    rw [ZMod.isUnit_iff_coprime]; exact (coprime_iff_not_dvd p r hp hp5 hr e').mpr he'.2
  have h4unit : IsUnit (4 : ZMod (p^r)) := by
    have := (two_unit p r hp hp5 hr).pow 2
    rwa [show (2:ZMod (p^r))^2 = 4 by ring] at this
  have hbcast : ∀ e', ((b e' : ℤ) : ZMod (p^r)) = -((4:ZMod (p^r)) * (((e':ℕ):ZMod (p^r)))^2) := by
    intro e'; rw [hbdef]; push_cast
    rw [show ((p:ZMod (p^r)))^r = 0 by rw [← Nat.cast_pow, ZMod.natCast_self]]; ring
  have hDcast : ((∑ e ∈ Lf, ∏ e' ∈ Lf.erase e, b e' : ℤ) : ZMod (p^r)) = 0 := by
    push_cast
    simp_rw [hbcast]
    have key : ∀ e ∈ Lf, ∏ e' ∈ Lf.erase e, (-((4:ZMod (p^r)) * (((e':ℕ):ZMod (p^r)))^2))
        = (∏ e' ∈ Lf, (-((4:ZMod (p^r)) * (((e':ℕ):ZMod (p^r)))^2)))
          * (-((4:ZMod (p^r)) * (((e:ℕ):ZMod (p^r)))^2))⁻¹ := by
      intro e he
      rw [zmod_leave_one Lf (fun e' => -((4:ZMod (p^r)) * (((e':ℕ):ZMod (p^r)))^2)) e he
          ((h4unit.mul ((hunit e he).pow 2)).neg)]
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
    have hz : ∑ e ∈ Lf, (-((4:ZMod (p^r)) * (((e:ℕ):ZMod (p^r)))^2))⁻¹ = 0 := by
      have heq : ∀ e ∈ Lf, (-((4:ZMod (p^r)) * (((e:ℕ):ZMod (p^r)))^2))⁻¹
          = (-((4:ZMod (p^r))⁻¹)) * ((((e:ℕ):ZMod (p^r)))⁻¹)^2 := by
        intro e he
        rw [zmod_neg_inv _ (h4unit.mul ((hunit e he).pow 2)),
            zmod_mul_inv _ _ h4unit ((hunit e he).pow 2), ← zmod_inv_sq _ (hunit e he)]
        ring
      rw [Finset.sum_congr rfl heq, ← Finset.mul_sum, half_W2 p r hp hp5 hr, mul_zero]
    rw [hz, mul_zero]
  have hD : (p^r:ℤ) ∣ (∑ e ∈ Lf, ∏ e' ∈ Lf.erase e, b e') := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p^r)).mp hDcast
    exact_mod_cast this
  have hδD : ((p^r:ℤ))^3 ∣ δ * (∑ e ∈ Lf, ∏ e' ∈ Lf.erase e, b e') := by
    obtain ⟨D', hD'⟩ := hD
    exact ⟨(c:ℤ)*((c:ℤ)+2)*D', by rw [hδdef, hD']; ring⟩
  calc (∏ e ∈ Lf, (b e + δ)) ≡ (∏ e ∈ Lf, b e) + δ * (∑ e ∈ Lf, ∏ e' ∈ Lf.erase e, b e') [ZMOD ((p^r:ℤ))^3] := h1
    _ ≡ (∏ e ∈ Lf, b e) + 0 [ZMOD ((p^r:ℤ))^3] := by
        apply Int.ModEq.add_left; exact (Int.modEq_zero_iff_dvd.mpr hδD)
    _ = ∏ e ∈ Lf, b e := by ring


def Pp (n : ℕ) : ℕ := ∏ j ∈ Finset.Icc 1 (5*n), (5*n + 2*j)

theorem gamma_pochhammer (x : ℝ) (hx : 0 < x) (k : ℕ) :
    Real.Gamma (x + k) = Real.Gamma x * ∏ i ∈ Finset.range k, (x + i) := by
  induction k with
  | zero => simp
  | succ k IH =>
    rw [Finset.prod_range_succ, Nat.cast_succ, show x + ((k:ℝ)+1) = (x+(k:ℝ))+1 from by ring,
        Real.Gamma_add_one (ne_of_gt (by positivity)), IH]
    ring

theorem fact_split (p Y : ℕ) (hp : 0 < p) :
    (Y*p)! = p^Y * Y ! * Gcop p (Y*p) := by
  have hfac : ∏ x ∈ Finset.Icc 1 (Y*p), x = (Y*p)! := by
    rw [← Finset.Ico_add_one_right_eq_Icc]; exact Finset.prod_Ico_id_eq_factorial (Y*p)
  have hmul : (∏ k ∈ (Finset.Icc 1 (Y*p)).filter (fun k => p ∣ k), k) = p^Y * Y ! := by
    have hset : (Finset.Icc 1 (Y*p)).filter (fun k => p ∣ k) = (Finset.Icc 1 Y).image (fun m => p * m) := by
      ext k
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hk1, hk2⟩, c, rfl⟩
        have hc0 : c ≠ 0 := by rintro rfl; simp at hk1
        have hcY : c ≤ Y := Nat.le_of_mul_le_mul_left (by rw [mul_comm Y p] at hk2; exact hk2) hp
        exact ⟨c, ⟨Nat.one_le_iff_ne_zero.mpr hc0, hcY⟩, rfl⟩
      · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
        exact ⟨⟨Nat.mul_pos hp hm1, by rw [mul_comm p m]; exact mul_le_mul_right' hm2 p⟩, dvd_mul_right p m⟩
    have hfacY : ∏ x ∈ Finset.Icc 1 Y, x = Y ! := by
      rw [← Finset.Ico_add_one_right_eq_Icc]; exact Finset.prod_Ico_id_eq_factorial Y
    rw [hset, Finset.prod_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hp h),
        Finset.prod_mul_distrib, Finset.prod_const, hfacY, Nat.card_Icc, Nat.add_sub_cancel]
  unfold Gcop
  rw [← hfac, ← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (Y*p)) (fun k => p ∣ k), hmul]

theorem a_reduce (n : ℕ) :
    a n * ((Pp n * (6*n)! * (5*n)! * n ! : ℕ) : ℝ)
      = (((15*n)! * (2*n)! * 2^(5*n) : ℕ) : ℝ) := by
  have hΓ : Real.Gamma (15 * (n:ℝ) / 2 + 1)
      = Real.Gamma (5 * (n:ℝ)/2 + 1) * ((Pp n : ℝ) / 2^(5*n)) := by
    have hx : (0:ℝ) < 5*(n:ℝ)/2 + 1 := by positivity
    have hpoch := gamma_pochhammer (5*(n:ℝ)/2+1) hx (5*n)
    have harg : (5*(n:ℝ)/2+1) + ((5*n:ℕ):ℝ) = 15*(n:ℝ)/2 + 1 := by push_cast; ring
    rw [harg] at hpoch
    rw [hpoch]
    congr 1
    -- ∏_{i∈range(5n)}((5n/2+1)+i) = Pp n / 2^(5n)
    rw [eq_div_iff (by positivity : (2:ℝ)^(5*n) ≠ 0)]
    rw [show (2:ℝ)^(5*n) = ∏ _i ∈ Finset.range (5*n), (2:ℝ) from by rw [Finset.prod_const, Finset.card_range]]
    rw [← Finset.prod_mul_distrib]
    have hPpr : ((Pp n:ℕ):ℝ) = ∏ j ∈ Finset.Icc 1 (5*n), ((5*n:ℝ)+2*(j:ℝ)) := by
      unfold Pp; rw [Nat.cast_prod]; apply Finset.prod_congr rfl; intro j _; push_cast; ring
    rw [hPpr, ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
    apply Finset.prod_congr (by rw [Nat.add_sub_cancel])
    intro i _; push_cast; ring
  rw [a]
  rw [hΓ]
  have hΓpos : Real.Gamma (5*(n:ℝ)/2+1) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have h6 : ((6*n)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h5 : ((5*n)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h1 : ((n)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hPp : ((Pp n : ℕ):ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; unfold Pp
    exact Finset.prod_ne_zero_iff.mpr (fun j hj => by simp only [Finset.mem_Icc] at hj; omega)
  have h2n : (2:ℝ)^(5*n) ≠ 0 := by positivity
  push_cast
  field_simp

/-! ## Shifted Gauss product (the P-part) -/

def BG2 (p r C K : ℕ) : ℕ := ∏ j ∈ (Finset.Icc 1 (K*p^r)).filter (fun j => ¬ p ∣ j), (C*p^r + 2*j)

theorem bg2_succ (p r C K : ℕ) (hp : 0 < p) (hr : 1 ≤ r) :
    BG2 p r C (K+1)
      = BG2 p r C K * ∏ e ∈ (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e), ((C+2*K)*p^r + 2*e) := by
  unfold BG2
  set q := p^r with hq
  have hexp : (K+1)*q = K*q + q := by ring
  have hqdvd : p ∣ K*q := by rw [hq]; exact (dvd_pow_self p (by omega : r ≠ 0)).mul_left K
  have hsplit : (Finset.Icc 1 ((K+1)*q)).filter (fun j => ¬ p ∣ j)
      = ((Finset.Icc 1 (K*q)).filter (fun j => ¬ p ∣ j))
        ∪ ((Finset.Icc (K*q+1) ((K+1)*q)).filter (fun j => ¬ p ∣ j)) := by
    rw [← Finset.filter_union]; congr 1
    ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint ((Finset.Icc 1 (K*q)).filter (fun j => ¬ p ∣ j))
        ((Finset.Icc (K*q+1) ((K+1)*q)).filter (fun j => ¬ p ∣ j)) := by
    apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_Icc] at ha hb; omega
  rw [hsplit, Finset.prod_union hdisj]
  congr 1
  rw [show (Finset.Icc (K*q+1) ((K+1)*q)).filter (fun j => ¬ p ∣ j)
        = ((Finset.Icc 1 q).filter (fun e => ¬ p ∣ e)).image (fun e => K*q + e) from ?_]
  · rw [Finset.prod_image (by intro a _ b _ h; exact Nat.add_left_cancel h)]
    apply Finset.prod_congr rfl
    intro e _; ring
  · ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hx1, hx2⟩, hpx⟩
      refine ⟨x - K*q, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      intro hd; apply hpx
      have := Nat.dvd_add hqdvd hd
      rwa [Nat.add_sub_cancel' (by omega : K*q ≤ x)] at this
    · rintro ⟨e, ⟨⟨he1, he2⟩, hpe⟩, rfl⟩
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      intro hd; apply hpe
      have := Nat.dvd_sub hd hqdvd
      rwa [Nat.add_sub_cancel_left] at this

theorem BG2_cong (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) (C K : ℕ) :
    (BG2 p r C K : ℤ)
      ≡ (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((2*e:ℕ):ℤ))^K
        [ZMOD ((p^r:ℕ):ℤ)^3] := by
  have hpr1 : 1 ≤ p^r := Nat.one_le_pow _ _ hp.pos
  have hpq : p ∣ p^r := dvd_pow_self p (by omega)
  have hqf : (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e)
           = (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1,h2⟩, hpx⟩
      refine ⟨⟨h1, ?_⟩, hpx⟩
      rcases Nat.lt_or_ge x (p^r) with h|h
      · omega
      · exfalso; have hx : x = p^r := by omega
        rw [hx] at hpx; exact hpx hpq
    · rintro ⟨⟨h1,h2⟩, hpx⟩
      exact ⟨⟨h1, by omega⟩, hpx⟩
  induction K with
  | zero => simp [BG2]
  | succ K IH =>
      rw [bg2_succ p r C K hp.pos hr]
      have hcast : ((BG2 p r C K * ∏ e ∈ (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e), ((C+2*K)*p^r + 2*e) : ℕ) : ℤ)
          = (BG2 p r C K:ℤ) * ∏ e ∈ (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e), (((C+2*K)*p^r + 2*e : ℕ):ℤ) := by
        push_cast; ring
      rw [hcast]
      have hblock : (∏ e ∈ (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e), (((C+2*K)*p^r + 2*e : ℕ):ℤ))
          ≡ (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((2*e:ℕ):ℤ)) [ZMOD ((p^r:ℕ):ℤ)^3] := by
        rw [hqf]
        exact block_cong2 p r hp hp5 hr (C+2*K)
      calc (BG2 p r C K:ℤ) * ∏ e ∈ (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e), (((C+2*K)*p^r + 2*e : ℕ):ℤ)
          ≡ (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((2*e:ℕ):ℤ))^K
            * (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((2*e:ℕ):ℤ)) [ZMOD ((p^r:ℕ):ℤ)^3] :=
              Int.ModEq.mul IH hblock
        _ = (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((2*e:ℕ):ℤ))^(K+1) := by rw [pow_succ]

theorem card_U (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) :
    ((Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e)).card = p^r - p^(r-1) := by
  have hpr : p^r = p * p^(r-1) := by
    conv_lhs => rw [show r = (r-1)+1 from by omega]
    rw [pow_succ]; ring
  have hpr1 : 1 ≤ p^(r-1) := Nat.one_le_pow _ _ hp.pos
  have hp2 : 2 ≤ p := hp.two_le
  have hcompl : (Finset.Icc 1 (p^r-1)).filter (fun e => p ∣ e)
      = (Finset.Icc 1 (p^(r-1)-1)).image (fun k => p*k) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hj1, hj2⟩, k, rfl⟩
      have hk0 : k ≠ 0 := by rintro rfl; simp at hj1
      refine ⟨k, ⟨Nat.one_le_iff_ne_zero.mpr hk0, ?_⟩, rfl⟩
      have hlt : p*k < p*p^(r-1) := by omega
      have := Nat.lt_of_mul_lt_mul_left hlt
      omega
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      refine ⟨⟨Nat.mul_pos hp.pos hk1, ?_⟩, dvd_mul_right p k⟩
      have hkle : p * k ≤ p * (p^(r-1)-1) := Nat.mul_le_mul_left p hk2
      have hprod : p * (p^(r-1)-1) + p = p^r := by
        rw [hpr]
        generalize p^(r-1) = s at hpr1 ⊢
        cases s with
        | zero => omega
        | succ t => simp [Nat.mul_succ]
      omega
  have hcardcompl : ((Finset.Icc 1 (p^r-1)).filter (fun e => p ∣ e)).card = p^(r-1) - 1 := by
    rw [hcompl, Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hp.pos h),
        Nat.card_Icc, Nat.add_sub_cancel]
  have htot := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.Icc 1 (p^r-1)) (p := fun e => p ∣ e)
  rw [hcardcompl, Nat.card_Icc, Nat.add_sub_cancel] at htot
  omega

def PGp (p M : ℕ) : ℕ := ∏ j ∈ (Finset.Icc 1 (5*M*p)).filter (fun j => ¬ p ∣ j), (5*M*p + 2*j)

theorem P_split (p M : ℕ) (hp : 0 < p) :
    Pp (M*p) = p^(5*M) * Pp M * PGp p M := by
  unfold Pp PGp
  rw [show 5*(M*p) = 5*M*p from by ring]
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (5*M*p)) (fun j => p ∣ j)]
  have hA : (∏ j ∈ (Finset.Icc 1 (5*M*p)).filter (fun j => p ∣ j), (5*M*p+2*j))
      = p^(5*M) * ∏ k ∈ Finset.Icc 1 (5*M), (5*M+2*k) := by
    have hset : (Finset.Icc 1 (5*M*p)).filter (fun j => p ∣ j) = (Finset.Icc 1 (5*M)).image (fun k => p*k) := by
      ext j
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hj1, hj2⟩, k, rfl⟩
        have hk0 : k ≠ 0 := by rintro rfl; simp at hj1
        have hkM : k ≤ 5*M := Nat.le_of_mul_le_mul_left (by rw [mul_comm (5*M) p] at hj2; exact hj2) hp
        exact ⟨k, ⟨Nat.one_le_iff_ne_zero.mpr hk0, hkM⟩, rfl⟩
      · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
        exact ⟨⟨Nat.mul_pos hp hk1, by rw [mul_comm p k]; exact mul_le_mul_right' hk2 p⟩, dvd_mul_right p k⟩
    rw [hset, Finset.prod_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hp h)]
    rw [Finset.prod_congr rfl (fun k _ => show 5*M*p + 2*(p*k) = p*(5*M+2*k) from by ring)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  rw [hA]


/-! ## Coprimality helpers and assembly -/

theorem Pp_ne_zero (n : ℕ) : Pp n ≠ 0 := by
  unfold Pp
  exact Finset.prod_ne_zero_iff.mpr (fun j hj => by simp only [Finset.mem_Icc] at hj; omega)

theorem gcop_coprime (p X : ℕ) (hp : p.Prime) : Nat.Coprime (Gcop p X) p := by
  unfold Gcop
  apply Nat.Coprime.prod_left
  intro e he
  simp only [Finset.mem_filter] at he
  exact (hp.coprime_iff_not_dvd.mpr he.2).symm

theorem pgp_coprime (p M : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : Nat.Coprime (PGp p M) p := by
  unfold PGp
  apply Nat.Coprime.prod_left
  intro j hj
  simp only [Finset.mem_filter] at hj
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro hd
  apply hj.2
  have h5 : p ∣ 5*M*p := ⟨5*M, by ring⟩
  have h2j : p ∣ 2*j := by
    have := Nat.dvd_sub hd h5; rwa [Nat.add_sub_cancel_left] at this
  rcases hp.dvd_mul.mp h2j with h|h
  · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  · exact h

theorem core (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (n r : ℕ) (hn : 0 < n) (hr : 0 < r)
    (A B : ℤ) (hA : (A : ℝ) = a (n * p ^ r)) (hB : (B : ℝ) = a (n * p ^ (r - 1))) :
    (p : ℤ) ^ (3 * r) ∣ (A - B) := by
  have hp0 : 0 < p := hp.pos
  set M := n * p ^ (r - 1) with hM
  have hNM : n * p ^ r = M * p := by
    rw [hM, mul_assoc, ← pow_succ, show (r - 1) + 1 = r from by omega]
  have hcoef : ∀ c : ℕ, c * M * p = (c * n) * p ^ r := by
    intro c; rw [mul_assoc, ← hNM]; ring
  -- integer identities from a_reduce
  have hAi : (A:ℤ) * ((Pp (M*p) * (6*(M*p))! * (5*(M*p))! * (M*p)! : ℕ):ℤ)
      = (((15*(M*p))! * (2*(M*p))! * 2^(5*(M*p)) : ℕ):ℤ) := by
    have hR := a_reduce (n*p^r)
    rw [← hA, hNM] at hR
    exact_mod_cast hR
  have hBi : (B:ℤ) * ((Pp M * (6*M)! * (5*M)! * M ! : ℕ):ℤ)
      = (((15*M)! * (2*M)! * 2^(5*M) : ℕ):ℤ) := by
    have hR := a_reduce M
    rw [← hB] at hR
    exact_mod_cast hR
  -- the nat identity K'
  set SL := PGp p M * Gcop p (6*M*p) * Gcop p (5*M*p) * Gcop p (M*p) with hSL
  set SR := 2^(5*M*(p-1)) * Gcop p (15*M*p) * Gcop p (2*M*p) with hSR
  have e15 : (15*(M*p))! = p^(15*M) * (15*M)! * Gcop p (15*M*p) := by
    rw [show 15*(M*p) = (15*M)*p from by ring]; exact fact_split p (15*M) hp0
  have e2 : (2*(M*p))! = p^(2*M) * (2*M)! * Gcop p (2*M*p) := by
    rw [show 2*(M*p) = (2*M)*p from by ring]; exact fact_split p (2*M) hp0
  have e6 : (6*(M*p))! = p^(6*M) * (6*M)! * Gcop p (6*M*p) := by
    rw [show 6*(M*p) = (6*M)*p from by ring]; exact fact_split p (6*M) hp0
  have e5 : (5*(M*p))! = p^(5*M) * (5*M)! * Gcop p (5*M*p) := by
    rw [show 5*(M*p) = (5*M)*p from by ring]; exact fact_split p (5*M) hp0
  have e1 : (M*p)! = p^M * M ! * Gcop p (M*p) := fact_split p M hp0
  have eP : Pp (M*p) = p^(5*M) * Pp M * PGp p M := P_split p M hp0
  have e2pow : (2:ℕ)^(5*(M*p)) = 2^(5*M) * 2^(5*M*(p-1)) := by
    rw [← pow_add]; congr 1
    have h : 5*(M*p) = 5*M*p := by ring
    rw [h]; conv_lhs => rw [show (p:ℕ) = (p-1)+1 from by omega]
    ring
  have hK : ((15*(M*p))! * (2*(M*p))! * 2^(5*(M*p))) * SL * (Pp M * (6*M)! * (5*M)! * M !)
      = ((15*M)! * (2*M)! * 2^(5*M)) * SR * (Pp (M*p) * (6*(M*p))! * (5*(M*p))! * (M*p)!) := by
    rw [e15, e2, e6, e5, e1, eP, e2pow, hSL, hSR]
    ring
  -- derive A * SL = B * SR
  have hKz : (((15*(M*p))! * (2*(M*p))! * 2^(5*(M*p)) : ℕ):ℤ) * (SL:ℤ) * ((Pp M * (6*M)! * (5*M)! * M ! : ℕ):ℤ)
      = (((15*M)! * (2*M)! * 2^(5*M) : ℕ):ℤ) * (SR:ℤ) * ((Pp (M*p) * (6*(M*p))! * (5*(M*p))! * (M*p)! : ℕ):ℤ) := by
    exact_mod_cast hK
  rw [← hAi, ← hBi] at hKz
  have hDN0 : ((Pp (M*p) * (6*(M*p))! * (5*(M*p))! * (M*p)! : ℕ):ℤ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Pp_ne_zero _) (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _)
  have hDM0 : ((Pp M * (6*M)! * (5*M)! * M ! : ℕ):ℤ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Pp_ne_zero _) (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _)
  have hABSL : (A:ℤ) * (SL:ℤ) = (B:ℤ) * (SR:ℤ) := by
    have hprod : ((A:ℤ) * (SL:ℤ)) * (((Pp (M*p) * (6*(M*p))! * (5*(M*p))! * (M*p)! : ℕ):ℤ) * ((Pp M * (6*M)! * (5*M)! * M ! : ℕ):ℤ))
        = ((B:ℤ) * (SR:ℤ)) * (((Pp (M*p) * (6*(M*p))! * (5*(M*p))! * (M*p)! : ℕ):ℤ) * ((Pp M * (6*M)! * (5*M)! * M ! : ℕ):ℤ)) := by
      linear_combination hKz
    exact mul_right_cancel₀ (mul_ne_zero hDN0 hDM0) hprod
  -- congruence SL ≡ SR mod (p^r)^3
  have hgcong : ∀ c : ℕ, (Gcop p (c*M*p):ℤ) ≡ (Gcop p (p^r):ℤ)^(c*n) [ZMOD ((p^r:ℕ):ℤ)^3] := by
    intro c; rw [hcoef c]; exact core_G p r hp hp5 hr (c*n)
  have hg1 : (Gcop p (M*p):ℤ) ≡ (Gcop p (p^r):ℤ)^n [ZMOD ((p^r:ℕ):ℤ)^3] := by
    rw [← hNM]; exact core_G p r hp hp5 hr n
  have h5MN : 5*M*p = (5*n)*p^r := hcoef 5
  have hPGeq : PGp p M = BG2 p r (5*n) (5*n) := by
    unfold PGp BG2; rw [h5MN]
  have hPG : (PGp p M:ℤ)
      ≡ (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((2*e:ℕ):ℤ))^(5*n) [ZMOD ((p^r:ℕ):ℤ)^3] := by
    rw [hPGeq]; exact BG2_cong p r hp hp5 hr (5*n) (5*n)
  have hSLcong : (SL:ℤ) ≡ (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((2*e:ℕ):ℤ))^(5*n)
      * (Gcop p (p^r):ℤ)^(6*n) * (Gcop p (p^r):ℤ)^(5*n) * (Gcop p (p^r):ℤ)^n [ZMOD ((p^r:ℕ):ℤ)^3] := by
    rw [hSL]; push_cast
    exact ((hPG.mul (hgcong 6)).mul (hgcong 5)).mul hg1
  have hSRcong : (SR:ℤ) ≡ (2:ℤ)^(5*M*(p-1)) * (Gcop p (p^r):ℤ)^(15*n) * (Gcop p (p^r):ℤ)^(2*n) [ZMOD ((p^r:ℕ):ℤ)^3] := by
    rw [hSR]; push_cast
    exact ((Int.ModEq.refl _).mul (hgcong 15)).mul (hgcong 2)
  -- ∏_U (2e) = 2^card * Gcop, and card = p^r - p^(r-1)
  have hpr1 : 1 ≤ p^r := Nat.one_le_pow _ _ hp.pos
  have hpq : p ∣ p^r := dvd_pow_self p (by omega)
  have hqf : (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e)
           = (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1,h2⟩, hpx⟩
      refine ⟨⟨h1, ?_⟩, hpx⟩
      rcases Nat.lt_or_ge x (p^r) with h|h
      · omega
      · exfalso; have hx : x = p^r := by omega
        rw [hx] at hpx; exact hpx hpq
    · rintro ⟨⟨h1,h2⟩, hpx⟩
      exact ⟨⟨h1, by omega⟩, hpx⟩
  have hGU : (Gcop p (p^r):ℤ) = ∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((e:ℕ):ℤ) := by
    unfold Gcop; rw [hqf]; push_cast; rfl
  have h2eU : (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((2*e:ℕ):ℤ))
      = 2^(((Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e)).card) * (Gcop p (p^r):ℤ) := by
    rw [hGU, Finset.prod_congr rfl (fun e _ => by push_cast; ring :
        ∀ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((2*e:ℕ):ℤ) = 2 * (e:ℤ)),
        Finset.prod_mul_distrib, Finset.prod_const]
  have hcardcard := card_U p r hp hr
  have hcardeq : 5*n*(p^r - p^(r-1)) = 5*M*(p-1) := by
    rw [hM]
    have hpr : p^r = p^(r-1)*p := by rw [← pow_succ]; congr 1; omega
    rw [hpr]
    generalize p^(r-1) = s
    have hss : s * p - s = s * (p-1) := by
      cases p with
      | zero => simp
      | succ t => rw [Nat.mul_succ, Nat.add_sub_cancel, Nat.succ_sub_one]
    rw [hss]; ring
  have hEQ : (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((2*e:ℕ):ℤ))^(5*n)
        * (Gcop p (p^r):ℤ)^(6*n) * (Gcop p (p^r):ℤ)^(5*n) * (Gcop p (p^r):ℤ)^n
      = (2:ℤ)^(5*M*(p-1)) * (Gcop p (p^r):ℤ)^(15*n) * (Gcop p (p^r):ℤ)^(2*n) := by
    rw [h2eU, mul_pow, ← pow_mul, hcardcard,
        show (p^r - p^(r-1))*(5*n) = 5*M*(p-1) from by rw [mul_comm]; exact hcardeq]
    ring
  have hSLfinal : (SL:ℤ) ≡ (SR:ℤ) [ZMOD ((p^r:ℕ):ℤ)^3] :=
    (hSLcong.trans (hEQ ▸ Int.ModEq.refl _)).trans hSRcong.symm
  -- convert modulus
  have hmod : ((p^r:ℕ):ℤ)^3 = (p:ℤ)^(3*r) := by push_cast; rw [← pow_mul, Nat.mul_comm]
  have hdvd1 : (p:ℤ)^(3*r) ∣ ((SR:ℤ) - (SL:ℤ)) := by
    have := Int.ModEq.dvd hSLfinal
    rwa [hmod] at this
  have hmul : (A - B) * (SL:ℤ) = (B:ℤ) * ((SR:ℤ) - (SL:ℤ)) := by
    have := hABSL
    linear_combination (SL:ℤ) * (0:ℤ) + this
  have hdvd2 : (p:ℤ)^(3*r) ∣ (A - B) * (SL:ℤ) := by
    rw [hmul]; exact Dvd.dvd.mul_left hdvd1 _
  have hcopSL : Nat.Coprime SL p := by
    rw [hSL]
    exact (((pgp_coprime p M hp hp5).mul (gcop_coprime p (6*M*p) hp)).mul (gcop_coprime p (5*M*p) hp)).mul (gcop_coprime p (M*p) hp)
  have hcop : IsCoprime ((p:ℤ)^(3*r)) (SL:ℤ) :=
    (Nat.isCoprime_iff_coprime.mpr hcopSL).symm.pow_left
  exact hcop.dvd_of_dvd_mul_right hdvd2

/--
Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and all positive integers n and r.
Note: The sequence a(n) is only conjecturally integer-valued. We formalize the congruence as divisibility of real numbers, requiring that the sequence terms are indeed integers.
-/
theorem oeis_364176_conjecture_0
  (p : ℕ) (hp : Nat.Prime p) (hp_ge_five : 5 ≤ p)
  (n r : ℕ) (hn_pos : 0 < n) (hr_pos : 0 < r) :
  -- Define the arguments for a, ensuring r-1 is safe (guaranteed by hr_pos)
  let k_r := n * p ^ r
  let k_r_minus_1 := n * p ^ (r - 1)
  -- Define the modulus as a real number
  let modulus : ℝ := (p ^ (3 * r)).cast
  -- The premise is the conjectural integrality of the two relevant terms, i.e., they are in the image of Int.cast
  (a k_r ∈ Set.range (Int.cast : ℤ → ℝ)) ∧ (a k_r_minus_1 ∈ Set.range (Int.cast : ℤ → ℝ)) →
  -- The conclusion is the divisibility condition: modulus divides the difference.
  -- This is formalized as the quotient being an integer.
  (a k_r - a k_r_minus_1) / modulus ∈ Set.range (Int.cast : ℤ → ℝ)
:= by
  intro k_r k_r_minus_1 modulus h
  obtain ⟨A, hA⟩ := h.1
  obtain ⟨B, hB⟩ := h.2
  obtain ⟨c, hc⟩ := core p hp hp_ge_five n r hn_pos hr_pos A B hA hB
  refine ⟨c, ?_⟩
  have hmod : modulus = ((p : ℝ) ^ (3 * r)) := by simp [modulus]
  rw [hmod, ← hA, ← hB]
  have hp0 : (p : ℝ) ^ (3 * r) ≠ 0 := by
    have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.pos.ne'
    positivity
  field_simp
  have hcast : (↑A - ↑B : ℝ) = ↑p ^ (3 * r) * ↑c := by exact_mod_cast hc
  rw [hcast]; ring
