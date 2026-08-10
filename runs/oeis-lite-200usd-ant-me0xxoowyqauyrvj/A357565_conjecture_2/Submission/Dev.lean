import FormalConjectures.Util.ProblemImports

open Finset Nat

-- Classical Wolstenholme harmonic congruence mod p^2 (feasibility gate).
-- Strategy: in ZMod (p^2), 2*S = p*T with T ≡ 0 mod p (sum of inverse squares vanishes mod p).

variable {p : ℕ}

-- Step 1: sum of squares over nonzero elements of ZMod p is 0 for p ≥ 5.
theorem sum_sq_units_zero [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ x : ZMod p, x ^ 2 = 0 := by
  have hc : Fintype.card (ZMod p) = p := ZMod.card p
  apply FiniteField.sum_pow_lt_card_sub_one
  rw [hc]; omega

-- helper: p * x = 0 when reduction of x mod p is 0.
theorem p_mul_eq_zero_of_castHom [hp : Fact p.Prime]
    (x : ZMod (p^2)) (hx : (ZMod.castHom (by exact Dvd.intro p (by ring)) (ZMod p)) x = 0) :
    (p : ZMod (p^2)) * x = 0 := by
  have hp0 : p ≠ 0 := hp.out.pos.ne'
  have hpne : NeZero (p^2) := ⟨pow_ne_zero 2 hp0⟩
  -- x.val is divisible by p
  have h2 : (x.val : ZMod p) = 0 := by
    rw [ZMod.castHom_apply] at hx
    simpa [ZMod.castHom_apply, ZMod.natCast_val] using hx
  rw [ZMod.natCast_eq_zero_iff] at h2
  obtain ⟨t, ht⟩ := h2
  have hxv : ((x.val : ℕ) : ZMod (p^2)) = x := ZMod.natCast_rightInverse x
  calc (p : ZMod (p^2)) * x = (p : ZMod (p^2)) * ((x.val : ℕ) : ZMod (p^2)) := by rw [hxv]
    _ = ((p * x.val : ℕ) : ZMod (p^2)) := by push_cast; ring
    _ = ((p^2 * t : ℕ) : ZMod (p^2)) := by rw [ht]; ring_nf
    _ = 0 := by rw [ZMod.natCast_eq_zero_iff]; exact Dvd.intro t rfl

-- reflection on Icc 1 (p-1): k ↦ p - k
theorem sum_Icc_reflect {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ k ∈ Finset.Icc 1 (p-1), f k = ∑ k ∈ Finset.Icc 1 (p-1), f (p - k) := by
  apply Finset.sum_nbij' (fun k => p - k) (fun k => p - k)
  · intro a ha; simp only [Finset.mem_Icc] at *; omega
  · intro a ha; simp only [Finset.mem_Icc] at *; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha; congr 1; omega

theorem isUnit_of_lt [hp : Fact p.Prime] {M : ℕ} {k : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k ≤ p - 1) : IsUnit (k : ZMod (p^M)) := by
  rw [ZMod.isUnit_iff_coprime]
  have hkp : k < p := by have := hp.out.two_le; omega
  have hnd : ¬ p ∣ k := fun h => by have := Nat.le_of_dvd hk1 h; omega
  exact (((hp.out.coprime_iff_not_dvd).mpr hnd).symm).pow_right M

-- Reindex a sum over Icc 1 (p-1) (cast into ZMod p) to a sum over nonzero elements.
theorem reindex_Icc_to_units [hp : Fact p.Prime] {M : Type*} [AddCommMonoid M]
    (F : ZMod p → M) :
    ∑ k ∈ Finset.Icc 1 (p-1), F (k : ZMod p) = ∑ x ∈ (Finset.univ.erase (0 : ZMod p)), F x := by
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  apply Finset.sum_nbij' (fun k => ((k : ℕ) : ZMod p)) (fun x => x.val)
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    have hiff : ((a : ℕ) : ZMod p) = 0 ↔ p ∣ a := by
      rw [ZMod.natCast_eq_zero_iff]
    intro h; rw [hiff] at h; have := Nat.le_of_dvd (by omega) h; omega
  · intro x hx
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx
    simp only [Finset.mem_Icc]
    constructor
    · have : x.val ≠ 0 := by
        intro h; apply hx; have := ZMod.natCast_zmod_val x; rw [h] at this; simpa using this.symm
      omega
    · have := ZMod.val_lt x; omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    have hlt : a < p := by omega
    rw [ZMod.val_natCast_of_lt hlt]
  · intro x hx
    simp only [Finset.mem_erase] at hx
    exact ZMod.natCast_zmod_val x
  · intro a ha; rfl

-- sum of squares of inverses over nonzero = 0
theorem sum_inv_sq_units_zero [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ k ∈ Finset.Icc 1 (p-1), ((k : ZMod p)⁻¹) ^ 2 = 0 := by
  rw [reindex_Icc_to_units (fun x => (x⁻¹)^2)]
  -- ∑ over nonzero of (x⁻¹)^2 = ∑ over nonzero of x^2 (x↦x⁻¹ bijects nonzero) = ∑ all x^2 - 0
  have h2 : ∑ x ∈ (Finset.univ.erase (0 : ZMod p)), (x⁻¹)^2 = ∑ x ∈ (Finset.univ.erase (0:ZMod p)), x^2 := by
    apply Finset.sum_nbij' (fun x => x⁻¹) (fun x => x⁻¹)
    · intro a ha; simp only [Finset.mem_erase, Finset.mem_univ, and_true] at *; exact inv_ne_zero ha
    · intro a ha; simp only [Finset.mem_erase, Finset.mem_univ, and_true] at *; exact inv_ne_zero ha
    · intro a ha; simp only [Finset.mem_erase, Finset.mem_univ, and_true] at ha; exact inv_inv a
    · intro a ha; simp only [Finset.mem_erase, Finset.mem_univ, and_true] at ha; exact inv_inv a
    · intro a ha; rfl
  rw [h2]
  have h3 : ∑ x ∈ (Finset.univ.erase (0:ZMod p)), x^2 = ∑ x : ZMod p, x^2 := by
    rw [Finset.sum_erase]; exact by norm_num
  rw [h3]; exact sum_sq_units_zero hp5

-- castHom commutes with inverse of a unit (target is a field).
theorem castHom_inv_unit [Fact p.Prime] (hd : p ∣ p^2) (a : ZMod (p^2)) (ha : IsUnit a) :
    (ZMod.castHom hd (ZMod p)) (a⁻¹) = ((ZMod.castHom hd (ZMod p)) a)⁻¹ := by
  have h1 : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit a ha
  have h2 : (ZMod.castHom hd (ZMod p)) a * (ZMod.castHom hd (ZMod p)) (a⁻¹) = 1 := by
    rw [← map_mul, h1, map_one]
  exact (inv_eq_of_mul_eq_one_right h2).symm

theorem wolstenholme_p2 [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ k ∈ Finset.Icc 1 (p-1), (k : ZMod (p^2))⁻¹ = 0 := by
  have hd : p ∣ p^2 := dvd_pow_self p (two_ne_zero)
  set cst := ZMod.castHom hd (ZMod p) with hcst
  -- p ≤ p^2 lemmas
  have hp0 : p ≠ 0 := hp.out.pos.ne'
  -- reflection: S = ∑ (↑(p-k))⁻¹
  set S := ∑ k ∈ Finset.Icc 1 (p-1), (k : ZMod (p^2))⁻¹ with hS
  have hrefl : S = ∑ k ∈ Finset.Icc 1 (p-1), ((p - k : ℕ) : ZMod (p^2))⁻¹ :=
    sum_Icc_reflect (fun k => (k : ZMod (p^2))⁻¹)
  -- units
  have hunit : ∀ k ∈ Finset.Icc 1 (p-1), IsUnit (k : ZMod (p^2)) := by
    intro k hk; simp only [Finset.mem_Icc] at hk
    exact isUnit_of_lt hk.1 hk.2
  have hunit' : ∀ k ∈ Finset.Icc 1 (p-1), IsUnit ((p - k : ℕ) : ZMod (p^2)) := by
    intro k hk; simp only [Finset.mem_Icc] at hk
    exact isUnit_of_lt (by omega) (by omega)
  -- 2 • S = p * T
  set T := ∑ k ∈ Finset.Icc 1 (p-1), ((k : ZMod (p^2))⁻¹ * ((p - k : ℕ) : ZMod (p^2))⁻¹) with hT
  have hcast : ∀ k ∈ Finset.Icc 1 (p-1), ((p - k : ℕ) : ZMod (p^2)) = (p : ZMod (p^2)) - (k : ZMod (p^2)) := by
    intro k hk; simp only [Finset.mem_Icc] at hk
    rw [Nat.cast_sub (by omega)]
  have hkey : (2 : ZMod (p^2)) * S = (p : ZMod (p^2)) * T := by
    rw [two_mul]
    nth_rewrite 2 [hrefl]
    rw [hT, Finset.mul_sum, hS, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hu := hunit k hk; have hw := hunit' k hk
    have hck := hcast k hk
    -- u⁻¹ + w⁻¹ = p * (u⁻¹ * w⁻¹), using u + w = p
    have hsum : (k : ZMod (p^2)) + ((p - k : ℕ) : ZMod (p^2)) = (p : ZMod (p^2)) := by
      rw [hck]; ring
    have e1 : (k : ZMod (p^2)) * ((k : ZMod (p^2))⁻¹) = 1 := ZMod.mul_inv_of_unit _ hu
    have e2 : ((p - k : ℕ) : ZMod (p^2)) * (((p - k : ℕ) : ZMod (p^2))⁻¹) = 1 := ZMod.mul_inv_of_unit _ hw
    -- show (↑k)⁻¹ + (↑(p-k))⁻¹ = ↑p * ((↑k)⁻¹ * (↑(p-k))⁻¹)
    have : (k : ZMod (p^2))⁻¹ + ((p - k : ℕ) : ZMod (p^2))⁻¹
         = ((k : ZMod (p^2)) + ((p - k : ℕ) : ZMod (p^2))) * ((k : ZMod (p^2))⁻¹ * ((p - k : ℕ) : ZMod (p^2))⁻¹) := by
      rw [add_mul]
      rw [show ((k : ZMod (p^2)) * ((k : ZMod (p^2))⁻¹ * ((p - k : ℕ) : ZMod (p^2))⁻¹))
            = ((k : ZMod (p^2)) * (k : ZMod (p^2))⁻¹) * ((p - k : ℕ) : ZMod (p^2))⁻¹ by ring,
          e1, one_mul]
      rw [show (((p - k : ℕ) : ZMod (p^2)) * ((k : ZMod (p^2))⁻¹ * ((p - k : ℕ) : ZMod (p^2))⁻¹))
            = ((p - k : ℕ) : ZMod (p^2)) * ((p - k : ℕ) : ZMod (p^2))⁻¹ * (k : ZMod (p^2))⁻¹ by ring,
          e2, one_mul]
      rw [add_comm]
    rw [this, hsum]
  -- p * T = 0 since castHom T = 0
  have hcastT : cst T = 0 := by
    rw [hT, map_sum]
    have hterm : ∀ k ∈ Finset.Icc 1 (p-1),
        cst ((k : ZMod (p^2))⁻¹ * ((p - k : ℕ) : ZMod (p^2))⁻¹) = -(((k : ZMod p)⁻¹)^2) := by
      intro k hk
      simp only [Finset.mem_Icc] at hk
      rw [map_mul, castHom_inv_unit hd _ (hunit k (by simp [Finset.mem_Icc]; omega)),
          castHom_inv_unit hd _ (hunit' k (by simp [Finset.mem_Icc]; omega))]
      have c1 : cst ((k : ℕ) : ZMod (p^2)) = ((k : ℕ) : ZMod p) := by rw [hcst]; exact map_natCast _ k
      have c2 : cst ((p - k : ℕ) : ZMod (p^2)) = ((p - k : ℕ) : ZMod p) := by rw [hcst]; exact map_natCast _ _
      rw [c1, c2]
      have c3 : ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring
      rw [c3, inv_neg]; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, sum_inv_sq_units_zero hp5, neg_zero]
  have hpT : (p : ZMod (p^2)) * T = 0 := p_mul_eq_zero_of_castHom T (by rw [← hcst]; exact hcastT)
  have h2S : (2 : ZMod (p^2)) * S = 0 := by rw [hkey, hpT]
  -- 2 is a unit, so S = 0
  have h2unit : IsUnit (2 : ZMod (p^2)) := by
    have h := isUnit_of_lt (p := p) (M := 2) (k := 2) (by norm_num) (by omega)
    simpa using h
  calc S = (2 : ZMod (p^2))⁻¹ * ((2 : ZMod (p^2)) * S) := by
              rw [← mul_assoc, ZMod.inv_mul_of_unit _ h2unit, one_mul]
    _ = 0 := by rw [h2S, mul_zero]

/-! ## Decomposition machinery -/

-- Splitting a sum over range(N+1), N = p*M, by divisibility by p, reindexing multiples.
theorem sum_range_split_by_p {M0 : Type*} [AddCommMonoid M0] (p M : ℕ) (hp : 1 ≤ p)
    (g : ℕ → M0) :
    ∑ k ∈ Finset.range (p * M + 1), g k
      = (∑ l ∈ Finset.range (M + 1), g (p * l))
        + ∑ k ∈ (Finset.range (p * M + 1)).filter (fun k => ¬ p ∣ k), g k := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (p * M + 1)) (fun k => p ∣ k) g]
  congr 1
  have himg : (Finset.range (p * M + 1)).filter (fun k => p ∣ k)
      = (Finset.range (M + 1)).image (fun l => p * l) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, t, rfl⟩
      refine ⟨t, ?_, rfl⟩
      have : p * t ≤ p * M := by omega
      exact lt_of_le_of_lt (Nat.le_of_mul_le_mul_left this hp) (by omega)
    · rintro ⟨t, ht, rfl⟩
      exact ⟨by nlinarith, Dvd.intro t rfl⟩
  rw [himg, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left hp hab

-- Box decomposition: units in [1, p^r) are exactly a + p*b for a∈[1,p-1], b∈[0,p^{r-1}).
theorem units_box_sum {M0 : Type*} [AddCommMonoid M0] {p r : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ r)
    (g : ℕ → M0) :
    ∑ k ∈ (Finset.range (p ^ r + 1)).filter (fun k => ¬ p ∣ k), g k
      = ∑ a ∈ Finset.Icc 1 (p - 1), ∑ b ∈ Finset.range (p ^ (r - 1)), g (a + p * b) := by
  have hpr : p ^ r = p * p ^ (r - 1) := by
    conv_lhs => rw [show r = (r - 1) + 1 by omega]
    ring
  have himg : (Finset.range (p ^ r + 1)).filter (fun k => ¬ p ∣ k)
      = (Finset.Icc 1 (p - 1) ×ˢ Finset.range (p ^ (r - 1))).image (fun ab => ab.1 + p * ab.2) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_product,
      Finset.mem_Icc, Prod.exists]
    constructor
    · rintro ⟨hk, hndvd⟩
      refine ⟨k % p, k / p, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · exact Nat.one_le_iff_ne_zero.mpr (fun h => hndvd (Nat.dvd_of_mod_eq_zero h))
      · have := Nat.mod_lt k (show 0 < p by omega); omega
      · -- k / p < p^(r-1)
        rw [hpr] at hk
        have hkp : k < p * p ^ (r - 1) := by
          rcases Nat.lt_or_ge k (p * p^(r-1)) with h | h
          · exact h
          · exfalso
            have hke : k = p * p^(r-1) := le_antisymm (by omega) h
            exact hndvd ⟨p^(r-1), hke⟩
        rw [Nat.div_lt_iff_lt_mul (by omega), Nat.mul_comm]; exact hkp
      · rw [Nat.mod_add_div k p]
    · rintro ⟨a, b, ⟨⟨ha1, ha2⟩, hb0⟩, rfl⟩
      constructor
      · rw [hpr]
        have hpos : 1 ≤ p^(r-1) := Nat.one_le_pow _ _ (by omega)
        have hexp : p * (p^(r-1) - 1) + p = p * p^(r-1) := by
          have h1 : p^(r-1) - 1 + 1 = p^(r-1) := Nat.sub_add_cancel hpos
          calc p * (p^(r-1)-1) + p = p * (p^(r-1)-1+1) := by rw [Nat.mul_add, Nat.mul_one]
            _ = p * p^(r-1) := by rw [h1]
        have hpb : p * b ≤ p * (p^(r-1) - 1) := by
          have hb : b ≤ p^(r-1) - 1 := by omega
          gcongr
        omega
      · rintro ⟨t, ht⟩
        have hmod : (a + p * b) % p = (p * t) % p := by rw [ht]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega), Nat.mul_mod_right] at hmod
        omega
  rw [himg, Finset.sum_image, Finset.sum_product]
  rintro ⟨a1, b1⟩ hm1 ⟨a2, b2⟩ hm2 h
  have ha1 : a1 ≤ p - 1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hm1).1).2
  have ha2 : a2 ≤ p - 1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hm2).1).2
  have hlt1 : a1 < p := by omega
  have hlt2 : a2 < p := by omega
  have h' : a1 + p * b1 = a2 + p * b2 := h
  have hmod : a1 = a2 := by
    have hh : (a1 + p * b1) % p = (a2 + p * b2) % p := by rw [h']
    rwa [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hh
  have hb : b1 = b2 := by
    have hpb : p * b1 = p * b2 := by rw [hmod] at h'; omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) hpb
  rw [Prod.mk.injEq]; exact ⟨hmod, hb⟩

/-! ## W-sums and pairing relations -/

-- The set of units (mod p) in [0, p^r), i.e. {k : 1 ≤ k < p^r, p ∤ k}.
def unitSet (p r : ℕ) : Finset ℕ := (Finset.range (p ^ r)).filter (fun k => ¬ p ∣ k)

-- membership
theorem mem_unitSet {p r k : ℕ} : k ∈ unitSet p r ↔ k < p ^ r ∧ ¬ p ∣ k := by
  simp [unitSet, Finset.mem_filter, Finset.mem_range]

-- The W-sum: ∑_{k ∈ unitSet} 1/k^s  (rational)
def Wsum (p r s : ℕ) : ℚ := ∑ k ∈ unitSet p r, (1 / (k : ℚ) ^ s)

-- reflection k ↦ p^r - k on unitSet
theorem unitSet_reflect {M0 : Type*} [AddCommMonoid M0] {p r : ℕ} (hp : 1 ≤ p) (hr : 1 ≤ r)
    (g : ℕ → M0) :
    ∑ k ∈ unitSet p r, g k = ∑ k ∈ unitSet p r, g (p ^ r - k) := by
  have hclosed : ∀ a, a ∈ unitSet p r → (p ^ r - a) ∈ unitSet p r := by
    intro a ha; rw [mem_unitSet] at ha ⊢
    have ha0 : a ≠ 0 := fun h => ha.2 (h ▸ dvd_zero p)
    refine ⟨by omega, ?_⟩
    intro hd2
    have hd1 : p ∣ p ^ r := dvd_pow_self p (by omega)
    have hd3 : p ∣ (p ^ r - (p ^ r - a)) := Nat.dvd_sub hd1 hd2
    have he : p ^ r - (p ^ r - a) = a := by omega
    rw [he] at hd3; exact ha.2 hd3
  apply Finset.sum_nbij' (fun k => p ^ r - k) (fun k => p ^ r - k)
  · exact hclosed
  · exact hclosed
  · intro a ha; rw [mem_unitSet] at ha; omega
  · intro a ha; rw [mem_unitSet] at ha; omega
  · intro a ha; rw [mem_unitSet] at ha; congr 1; omega

-- key pairing identity: 2 W1 + p^r W2 + p^{2r} W3 = p^{3r} * R3
theorem pairing3 {p r : ℕ} (hp : 1 ≤ p) (hr : 1 ≤ r) :
    2 * Wsum p r 1 + (↑(p ^ r) : ℚ) * Wsum p r 2 + (↑(p ^ r) : ℚ) ^ 2 * Wsum p r 3
      = (↑(p ^ r) : ℚ) ^ 3 * ∑ k ∈ unitSet p r, 1 / ((k : ℚ) ^ 3 * ((↑(p ^ r) : ℚ) - k)) := by
  -- reflected sum equals W1
  have hrefl : ∑ k ∈ unitSet p r, (1 / ((↑(p ^ r - k) : ℚ)) ^ 1) = Wsum p r 1 := by
    rw [Wsum]; exact (unitSet_reflect hp hr (fun k => 1 / ((k : ℚ)) ^ 1)).symm
  -- per-term identity
  have key : ∀ k ∈ unitSet p r,
      (1 / ((↑(p ^ r - k) : ℚ)) ^ 1) + (1 / (k : ℚ) ^ 1) + (↑(p ^ r) : ℚ) * (1 / (k : ℚ) ^ 2)
          + (↑(p ^ r) : ℚ) ^ 2 * (1 / (k : ℚ) ^ 3)
        = (↑(p ^ r) : ℚ) ^ 3 * (1 / ((k : ℚ) ^ 3 * ((↑(p ^ r) : ℚ) - k))) := by
    intro k hk
    rw [mem_unitSet] at hk
    have hk0 : (k : ℚ) ≠ 0 := by
      have : k ≠ 0 := fun h => hk.2 (h ▸ dvd_zero p)
      exact_mod_cast this
    have hpk : ((↑(p ^ r - k) : ℚ)) = (↑(p ^ r) : ℚ) - (k : ℚ) := by
      rw [Nat.cast_sub (le_of_lt hk.1)]
    have hpk0 : (↑(p ^ r) : ℚ) - (k : ℚ) ≠ 0 := by
      rw [← hpk]
      have : p ^ r - k ≠ 0 := by omega
      exact_mod_cast this
    rw [hpk]
    field_simp
    ring
  calc 2 * Wsum p r 1 + (↑(p ^ r) : ℚ) * Wsum p r 2 + (↑(p ^ r) : ℚ) ^ 2 * Wsum p r 3
      = (∑ k ∈ unitSet p r, (1 / ((↑(p ^ r - k) : ℚ)) ^ 1))
          + (∑ k ∈ unitSet p r, (1 / (k : ℚ) ^ 1))
          + (↑(p ^ r) : ℚ) * (∑ k ∈ unitSet p r, (1 / (k : ℚ) ^ 2))
          + (↑(p ^ r) : ℚ) ^ 2 * (∑ k ∈ unitSet p r, (1 / (k : ℚ) ^ 3)) := by
        rw [hrefl]; simp only [Wsum]; ring
    _ = ∑ k ∈ unitSet p r, ((1 / ((↑(p ^ r - k) : ℚ)) ^ 1) + (1 / (k : ℚ) ^ 1)
          + (↑(p ^ r) : ℚ) * (1 / (k : ℚ) ^ 2) + (↑(p ^ r) : ℚ) ^ 2 * (1 / (k : ℚ) ^ 3)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
          ← Finset.sum_add_distrib]
    _ = ∑ k ∈ unitSet p r, ((↑(p ^ r) : ℚ) ^ 3 * (1 / ((k : ℚ) ^ 3 * ((↑(p ^ r) : ℚ) - k)))) :=
        Finset.sum_congr rfl key
    _ = (↑(p ^ r) : ℚ) ^ 3 * ∑ k ∈ unitSet p r, 1 / ((k : ℚ) ^ 3 * ((↑(p ^ r) : ℚ) - k)) := by
        rw [Finset.mul_sum]

/-! ## Product formula for binomial coefficients (rational form) -/

-- k! * C(N+k-1, k) = ∏_{i<k} (N+i)  (as naturals)
theorem factorial_mul_choose_eq_prod (N k : ℕ) :
    (k.factorial) * (Nat.choose (N + k - 1) k) = ∏ i ∈ Finset.range k, (N + i) := by
  rw [← Nat.ascFactorial_eq_factorial_mul_choose', Nat.ascFactorial_eq_prod_range]

-- rational version: C(N+k-1,k) = (∏_{i<k}(N+i)) / k!
theorem choose_eq_prod_div (N k : ℕ) :
    ((Nat.choose (N + k - 1) k : ℚ)) = (∏ i ∈ Finset.range k, ((N + i : ℕ) : ℚ)) / (k.factorial : ℚ) := by
  have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  rw [eq_div_iff hk]
  have := factorial_mul_choose_eq_prod N k
  have h2 : ((k.factorial * Nat.choose (N + k - 1) k : ℕ) : ℚ) = ((∏ i ∈ Finset.range k, (N + i) : ℕ) : ℚ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) this
  push_cast at h2 ⊢
  linarith [h2]

-- b_k = (N/k) * ∏_{i=1}^{k-1} (1 + N/i)   (rational, for k ≥ 1)
theorem choose_eq_Nk_prod (N k : ℕ) (hk : 1 ≤ k) :
    ((Nat.choose (N + k - 1) k : ℚ))
      = ((N : ℚ) / (k : ℚ)) * ∏ i ∈ Finset.Icc 1 (k - 1), (1 + (N : ℚ) / (i : ℚ)) := by
  have hkpos : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  -- range k = insert 0 (Icc 1 (k-1))
  have hrange : Finset.range k = insert 0 (Finset.Icc 1 (k - 1)) := by
    ext i; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have h0notin : (0 : ℕ) ∉ Finset.Icc 1 (k - 1) := by simp
  -- numerator product
  have hnum : (∏ i ∈ Finset.range k, ((N + i : ℕ) : ℚ))
      = (N : ℚ) * ∏ i ∈ Finset.Icc 1 (k - 1), ((N : ℚ) + (i : ℚ)) := by
    rw [hrange, Finset.prod_insert h0notin]
    push_cast
    ring_nf
  -- factorial: k! = k * (k-1)!  and (k-1)! = ∏_{Icc 1 (k-1)} i
  have hII : Finset.Icc 1 (k - 1) = Finset.Ico 1 k := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have h1 : ∏ i ∈ Finset.Icc 1 (k - 1), (i : ℕ) = (k - 1).factorial := by
    rw [hII]
    have := Finset.prod_Ico_id_eq_factorial (k - 1)
    rwa [show k - 1 + 1 = k from by omega] at this
  have hfact : (k.factorial : ℚ) = (k : ℚ) * ∏ i ∈ Finset.Icc 1 (k - 1), (i : ℚ) := by
    have h2 : k.factorial = k * (k - 1).factorial := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      rw [Nat.factorial_succ]
      congr 1 <;> omega
    have h1q : (∏ i ∈ Finset.Icc 1 (k - 1), (i : ℚ)) = ((k - 1).factorial : ℚ) := by
      rw [← Nat.cast_prod]; exact_mod_cast h1
    rw [h1q, h2]; push_cast; ring
  -- the product 1 + N/i = (N+i)/i
  have hprod : ∏ i ∈ Finset.Icc 1 (k - 1), (1 + (N : ℚ) / (i : ℚ))
      = (∏ i ∈ Finset.Icc 1 (k - 1), ((N : ℚ) + i)) / (∏ i ∈ Finset.Icc 1 (k - 1), (i : ℚ)) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [Finset.mem_Icc] at hi
    have hi0 : (i : ℚ) ≠ 0 := by exact_mod_cast (by omega : i ≠ 0)
    field_simp
    ring
  have hprodi_ne : (∏ i ∈ Finset.Icc 1 (k - 1), (i : ℚ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi; simp only [Finset.mem_Icc] at hi
    exact_mod_cast (by omega : i ≠ 0)
  rw [choose_eq_prod_div, hnum, hprod, hfact]
  field_simp
