import FormalConjectures.Util.ProblemImports

open Finset

variable {p : ℕ}

theorem p_mul_of_castHom_zero (hp : Nat.Prime p) (x : ZMod (p^2))
    (h : (ZMod.castHom (⟨p, by ring⟩ : p ∣ p^2) (ZMod p)) x = 0) :
    (p : ZMod (p^2)) * x = 0 := by
  haveI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  have hxval : ((x.val : ℕ) : ZMod (p^2)) = x := ZMod.natCast_zmod_val x
  have h2 : ((x.val : ℕ) : ZMod p) = 0 := by
    have := h; rw [← hxval, map_natCast] at this; exact this
  rw [ZMod.natCast_eq_zero_iff] at h2
  obtain ⟨m, hm⟩ := h2
  rw [← hxval, hm]; push_cast
  rw [show (p:ZMod (p^2)) * ((p:ZMod (p^2)) * (m:ZMod (p^2))) = ((p^2 : ℕ) : ZMod (p^2)) * (m:ZMod (p^2)) by push_cast; ring, ZMod.natCast_self, zero_mul]

-- general: if x : ZMod (p^3) reduces to 0 mod p^k (k ≤ 3) then p^k ∣ x
theorem pow_dvd_of_castHom_zero (hp : Nat.Prime p) {k : ℕ} (hk : k ≤ 3) (x : ZMod (p^3))
    (h : (ZMod.castHom (pow_dvd_pow p hk) (ZMod (p^k))) x = 0) :
    (p^k : ZMod (p^3)) ∣ x := by
  haveI : NeZero (p^3) := ⟨pow_ne_zero 3 hp.pos.ne'⟩
  have hxval : ((x.val : ℕ) : ZMod (p^3)) = x := ZMod.natCast_zmod_val x
  have h2 : ((x.val : ℕ) : ZMod (p^k)) = 0 := by
    have := h; rw [← hxval, map_natCast] at this; exact this
  rw [ZMod.natCast_eq_zero_iff] at h2
  obtain ⟨m, hm⟩ := h2
  refine ⟨(m : ZMod (p^3)), ?_⟩
  rw [← hxval, hm]; push_cast; ring

-- ring hom preserves inverse of coprime element
theorem castHom_inv {a b : ℕ} (hp : Nat.Prime p) (hab : p^b ∣ p^a) (hba : b ≤ a) (i : ℕ)
    (hcop : ¬ p ∣ i) :
    (ZMod.castHom hab (ZMod (p^b))) ((i:ZMod (p^a))⁻¹) = ((i:ZMod (p^b)))⁻¹ := by
  have hca : Nat.Coprime i (p^a) := Nat.Coprime.pow_right a ((hp.coprime_iff_not_dvd.mpr hcop).symm)
  have hcb : Nat.Coprime i (p^b) := Nat.Coprime.pow_right b ((hp.coprime_iff_not_dvd.mpr hcop).symm)
  have hua : IsUnit ((i:ℕ):ZMod (p^a)) := (ZMod.isUnit_iff_coprime i (p^a)).mpr hca
  have hub : IsUnit ((i:ℕ):ZMod (p^b)) := (ZMod.isUnit_iff_coprime i (p^b)).mpr hcb
  set φ := ZMod.castHom hab (ZMod (p^b))
  have h1 : φ ((i:ZMod (p^a))⁻¹) * ((i:ℕ):ZMod (p^b)) = 1 := by
    have : φ ((i:ZMod (p^a))⁻¹) * φ ((i:ℕ):ZMod (p^a)) = 1 := by
      rw [← map_mul, ZMod.inv_mul_of_unit _ hua, map_one]
    rwa [map_natCast] at this
  have h2 : ((i:ℕ):ZMod (p^b)) * ((i:ℕ):ZMod (p^b))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hub
  calc φ ((i:ZMod (p^a))⁻¹) = φ ((i:ZMod (p^a))⁻¹) * (((i:ℕ):ZMod (p^b)) * ((i:ℕ):ZMod (p^b))⁻¹) := by rw [h2, mul_one]
    _ = (φ ((i:ZMod (p^a))⁻¹) * ((i:ℕ):ZMod (p^b))) * ((i:ℕ):ZMod (p^b))⁻¹ := by ring
    _ = ((i:ℕ):ZMod (p^b))⁻¹ := by rw [h1, one_mul]

theorem sum_range_eq_univ [NeZero p] (f : ZMod p → ZMod p) :
    ∑ i ∈ Finset.range p, f (i : ZMod p) = ∑ x : ZMod p, f x := by
  refine Finset.sum_bij' (fun a _ => (a : ZMod p)) (fun x _ => x.val)
    (fun a _ => Finset.mem_univ _) (fun x _ => ?_) (fun a ha => ?_)
    (fun x _ => ZMod.natCast_zmod_val x) (fun a _ => rfl)
  · rw [Finset.mem_range]; exact ZMod.val_lt x
  · rw [Finset.mem_range] at ha; exact ZMod.val_natCast_of_lt ha

theorem sum_inv_sq_field [Fact (Nat.Prime p)] (hp3 : 3 < p) :
    ∑ x : ZMod p, (x⁻¹)^2 = 0 := by
  let e : ZMod p ≃ ZMod p := ⟨Inv.inv, Inv.inv, inv_inv, inv_inv⟩
  have h1 : ∑ x : ZMod p, (e x)^2 = ∑ x : ZMod p, x^2 := Equiv.sum_comp e (·^2)
  have h2 : ∑ x : ZMod p, x ^ 2 = 0 :=
    FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) 2 (by rw [ZMod.card]; omega)
  have h3 : ∑ x : ZMod p, (e x)^2 = ∑ x : ZMod p, (x⁻¹)^2 := rfl
  rw [← h3, h1, h2]

theorem sum_inv_sq_range [Fact (Nat.Prime p)] (hp3 : 3 < p) :
    ∑ i ∈ Finset.range p, ((i : ZMod p)⁻¹)^2 = 0 := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  rw [sum_range_eq_univ (fun x => (x⁻¹)^2)]
  exact sum_inv_sq_field hp3

theorem sum_inv_sq_Icc [Fact (Nat.Prime p)] (hp3 : 3 < p) :
    ∑ i ∈ Finset.Icc 1 (p-1), ((i : ZMod p)⁻¹)^2 = 0 := by
  have hp := Fact.out (p := Nat.Prime p)
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  rw [← sum_inv_sq_range hp3]
  have hset : Finset.Icc 1 (p-1) = (Finset.range p).erase 0 := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]; omega
  rw [hset, Finset.sum_erase _ (by simp)]

-- coprimality helper
theorem coprime_of_mem_Icc (hp : Nat.Prime p) {i : ℕ} (hi : i ∈ Finset.Icc 1 (p-1)) :
    Nat.Coprime i (p^2) := by
  rw [Finset.mem_Icc] at hi
  have hip : i < p := by omega
  have : ¬ p ∣ i := by
    intro hd; have := Nat.le_of_dvd (by omega) hd; omega
  exact (Nat.Coprime.pow_right 2 ((hp.coprime_iff_not_dvd.mpr this).symm))

theorem isUnit_p2 (hp : Nat.Prime p) {i : ℕ} (hi : i ∈ Finset.Icc 1 (p-1)) :
    IsUnit ((i : ℕ) : ZMod (p^2)) :=
  (ZMod.isUnit_iff_coprime i (p^2)).mpr (coprime_of_mem_Icc hp hi)

-- reindex by i ↦ p - i on Icc 1 (p-1)
theorem sum_reflect {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ i ∈ Finset.Icc 1 (p-1), g (p - i) = ∑ i ∈ Finset.Icc 1 (p-1), g i := by
  refine Finset.sum_nbij' (fun i => p - i) (fun i => p - i) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; rfl

-- Wolstenholme's theorem mod p^2
theorem wolstenholme (hp : Nat.Prime p) (hp3 : 3 < p) :
    ∑ i ∈ Finset.Icc 1 (p-1), ((i : ℕ) : ZMod (p^2))⁻¹ = 0 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  set R := ZMod (p^2)
  set H := ∑ i ∈ Finset.Icc 1 (p-1), ((i : ℕ) : R)⁻¹ with hH
  -- pairing identity
  have hpair : ∀ i ∈ Finset.Icc 1 (p-1),
      ((i : ℕ) : R)⁻¹ + ((p - i : ℕ) : R)⁻¹ = (p : R) * (((i:ℕ):R)⁻¹ * ((p-i:ℕ):R)⁻¹) := by
    intro i hi
    have hmem := hi
    rw [Finset.mem_Icc] at hi
    have hu : ((i:ℕ):R) * ((i:ℕ):R)⁻¹ = 1 := ZMod.mul_inv_of_unit _ (isUnit_p2 hp hmem)
    have hvmem : (p - i) ∈ Finset.Icc 1 (p-1) := by rw [Finset.mem_Icc]; omega
    have hv : ((p-i:ℕ):R) * ((p-i:ℕ):R)⁻¹ = 1 := ZMod.mul_inv_of_unit _ (isUnit_p2 hp hvmem)
    have hsum : ((i:ℕ):R) + ((p-i:ℕ):R) = (p : R) := by
      rw [← Nat.cast_add]; congr 1; omega
    set a := ((i:ℕ):R); set b := ((p-i:ℕ):R)
    have key : a⁻¹ + b⁻¹ = (a + b) * (a⁻¹ * b⁻¹) := by
      calc a⁻¹ + b⁻¹ = (b * b⁻¹) * a⁻¹ + (a * a⁻¹) * b⁻¹ := by rw [hu, hv]; ring
        _ = (a + b) * (a⁻¹ * b⁻¹) := by ring
    rw [key, hsum]
  -- T and the 2H = p T identity
  set T := ∑ i ∈ Finset.Icc 1 (p-1), (((i:ℕ):R)⁻¹ * ((p-i:ℕ):R)⁻¹) with hT
  have hrefl : ∑ i ∈ Finset.Icc 1 (p-1), ((p - i : ℕ) : R)⁻¹ = H :=
    sum_reflect (fun j => ((j:ℕ):R)⁻¹)
  have h2H : H + H = (p : R) * T := by
    have e1 : ∑ i ∈ Finset.Icc 1 (p-1), (((i:ℕ):R)⁻¹ + ((p-i:ℕ):R)⁻¹)
        = (p : R) * T := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hpair
    rw [Finset.sum_add_distrib, hrefl, ← hH] at e1
    exact e1
  -- castHom T = 0
  set φ := ZMod.castHom (⟨p, by ring⟩ : p ∣ p^2) (ZMod p) with hφ
  have hφT : φ T = 0 := by
    rw [hT, map_sum]
    rw [show (0 : ZMod p) = ∑ i ∈ Finset.Icc 1 (p-1), -(((i:ℕ):ZMod p)⁻¹)^2 by
      rw [Finset.sum_neg_distrib, sum_inv_sq_Icc hp3, neg_zero]]
    apply Finset.sum_congr rfl
    intro i hi
    have hmem := hi
    rw [Finset.mem_Icc] at hi
    have hu : ((i:ℕ):R) * ((i:ℕ):R)⁻¹ = 1 := ZMod.mul_inv_of_unit _ (isUnit_p2 hp hmem)
    have hvmem : (p - i) ∈ Finset.Icc 1 (p-1) := by rw [Finset.mem_Icc]; omega
    have hv : ((p-i:ℕ):R) * ((p-i:ℕ):R)⁻¹ = 1 := ZMod.mul_inv_of_unit _ (isUnit_p2 hp hvmem)
    have hφa : φ (((i:ℕ):R)⁻¹) = ((i:ℕ):ZMod p)⁻¹ := by
      have : φ ((i:ℕ):R) * φ (((i:ℕ):R)⁻¹) = 1 := by rw [← map_mul, hu, map_one]
      rw [map_natCast] at this
      exact eq_inv_of_mul_eq_one_right this
    have hφb : φ (((p-i:ℕ):R)⁻¹) = ((p-i:ℕ):ZMod p)⁻¹ := by
      have : φ ((p-i:ℕ):R) * φ (((p-i:ℕ):R)⁻¹) = 1 := by rw [← map_mul, hv, map_one]
      rw [map_natCast] at this
      exact eq_inv_of_mul_eq_one_right this
    have hcast : ((p-i:ℕ):ZMod p) = -((i:ℕ):ZMod p) := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
    rw [map_mul, hφa, hφb, hcast, inv_neg]
    ring
  have hpT : (p : R) * T = 0 := p_mul_of_castHom_zero hp T hφT
  have h2H0 : H + H = 0 := by rw [h2H, hpT]
  -- 2 is a unit in R
  have h2unit : IsUnit (2 : R) := by
    have : ((2:ℕ):R) = (2:R) := by norm_num
    rw [← this]
    refine (ZMod.isUnit_iff_coprime 2 (p^2)).mpr ?_
    have : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
    exact Nat.Coprime.pow_right 2 this
  have : (2 : R) * H = 0 := by rw [two_mul]; exact h2H0
  exact (h2unit.mul_right_eq_zero).mp this

-- Truncated product expansion: if all uᵢ divisible by b and b³=0, the product of (1+uᵢ)
-- equals 1 + ∑u + e₂, with e₂ = ((∑u)²-∑u²)/2.
theorem prod_one_add_truncate (b : ZMod (p^3)) (hb3 : b^3 = 0)
    (u : ℕ → ZMod (p^3)) (inv2 : ZMod (p^3)) (hinv2 : (2:ZMod (p^3)) * inv2 = 1)
    (s : Finset ℕ) (hu : ∀ i ∈ s, b ∣ u i) :
    ∏ i ∈ s, (1 + u i)
      = 1 + (∑ i ∈ s, u i) + ((∑ i ∈ s, u i)^2 - ∑ i ∈ s, (u i)^2) * inv2 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert x t hx ih =>
    have hut : ∀ i ∈ t, b ∣ u i := fun i hi => hu i (Finset.mem_insert_of_mem hi)
    have hbx : b ∣ u x := hu x (Finset.mem_insert_self x t)
    rw [Finset.prod_insert hx, Finset.sum_insert hx, Finset.sum_insert hx, ih hut]
    -- b² ∣ E2(t)
    have hbSum : b ∣ ∑ i ∈ t, u i := Finset.dvd_sum hut
    have hbQ : b^2 ∣ ∑ i ∈ t, (u i)^2 := by
      apply Finset.dvd_sum; intro i hi; obtain ⟨v, hv⟩ := hut i hi; exact ⟨v^2, by rw [hv]; ring⟩
    have hbSum2 : b^2 ∣ (∑ i ∈ t, u i)^2 := by obtain ⟨w, hw⟩ := hbSum; exact ⟨w^2, by rw [hw]; ring⟩
    have hbE2 : b^2 ∣ ((∑ i ∈ t, u i)^2 - ∑ i ∈ t, (u i)^2) * inv2 := by
      exact Dvd.dvd.mul_right (dvd_sub hbSum2 hbQ) inv2
    have hkill : u x * (((∑ i ∈ t, u i)^2 - ∑ i ∈ t, (u i)^2) * inv2) = 0 := by
      obtain ⟨vx, hvx⟩ := hbx; obtain ⟨w2, hw2⟩ := hbE2
      rw [hvx, hw2]; rw [show b * vx * (b^2 * w2) = b^3 * (vx * w2) by ring, hb3, zero_mul]
    linear_combination (-(u x * ∑ i ∈ t, u i)) * hinv2 + hkill

theorem H1div (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (p^2 : ZMod (p^3)) ∣ ∑ i ∈ Finset.Icc 1 (p-1), ((i:ℕ):ZMod (p^3))⁻¹ := by
  have hp3 : 3 < p := by omega
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  apply pow_dvd_of_castHom_zero hp (show (2:ℕ) ≤ 3 by norm_num)
  rw [map_sum, show (0:ZMod (p^2)) = ∑ i ∈ Finset.Icc 1 (p-1), ((i:ℕ):ZMod (p^2))⁻¹ from
    (wolstenholme hp hp3).symm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  exact castHom_inv hp (pow_dvd_pow p (show (2:ℕ)≤3 by norm_num)) (show (2:ℕ)≤3 by norm_num) i
    (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)

theorem H2div (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (p : ZMod (p^3)) ∣ ∑ i ∈ Finset.Icc 1 (p-1), (((i:ℕ):ZMod (p^3))⁻¹)^2 := by
  have hp3 : 3 < p := by omega
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have : (p:ZMod (p^3)) = (p^1 : ZMod (p^3)) := by ring
  rw [this]
  apply pow_dvd_of_castHom_zero hp (show (1:ℕ) ≤ 3 by norm_num)
  rw [map_sum, show (0:ZMod (p^1)) = ∑ i ∈ Finset.Icc 1 (p-1), (((i:ℕ):ZMod (p^1))⁻¹)^2 from by
    rw [pow_one]; exact (sum_inv_sq_Icc hp3).symm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  rw [map_pow]
  congr 1
  exact castHom_inv hp (pow_dvd_pow p (show (1:ℕ)≤3 by norm_num)) (show (1:ℕ)≤3 by norm_num) i
    (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)

theorem prod_Icc_cast (n : ℕ) :
    ∏ i ∈ Finset.Icc 1 n, ((i:ℕ):ZMod (p^3)) = ((Nat.factorial n : ℕ) : ZMod (p^3)) := by
  have h : Finset.Icc 1 n = Finset.Ico 1 (n+1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [← Nat.cast_prod, h, Finset.prod_Ico_id_eq_factorial]

theorem full_block (hp : Nat.Prime p) (hp5 : 5 ≤ p) (j : ℕ) :
    ∏ i ∈ Finset.Icc 1 (p-1), ((j*p+i : ℕ) : ZMod (p^3)) = ((Nat.factorial (p-1) : ℕ) : ZMod (p^3)) := by
  have hp3 : 3 < p := by omega
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero (p^3) := ⟨pow_ne_zero 3 hp.pos.ne'⟩
  set b : ZMod (p^3) := ((j*p : ℕ) : ZMod (p^3)) with hb
  have hb3 : b^3 = 0 := by
    rw [hb, ← Nat.cast_pow, show (j*p)^3 = (j^3) * p^3 by ring, Nat.cast_mul, Nat.cast_pow,
      ZMod.natCast_self, mul_zero]
  -- 2 is a unit
  have h2u : IsUnit ((2:ℕ):ZMod (p^3)) :=
    (ZMod.isUnit_iff_coprime 2 (p^3)).mpr (Nat.Coprime.pow_right 3 ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)))
  set inv2 : ZMod (p^3) := ((2:ℕ):ZMod (p^3))⁻¹ with hinv2def
  have hinv2 : (2:ZMod (p^3)) * inv2 = 1 := by
    rw [show (2:ZMod (p^3)) = ((2:ℕ):ZMod (p^3)) by norm_num]
    exact ZMod.mul_inv_of_unit _ h2u
  -- u i and divisibility
  set u : ℕ → ZMod (p^3) := fun i => b * ((i:ℕ):ZMod (p^3))⁻¹ with hu
  have hudvd : ∀ i ∈ Finset.Icc 1 (p-1), b ∣ u i := fun i _ => ⟨((i:ℕ):ZMod (p^3))⁻¹, rfl⟩
  -- each factor (j*p+i) = c_i * (1 + u i)
  have hfac : ∀ i ∈ Finset.Icc 1 (p-1),
      ((j*p+i : ℕ) : ZMod (p^3)) = ((i:ℕ):ZMod (p^3)) * (1 + u i) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hci : IsUnit ((i:ℕ):ZMod (p^3)) :=
      (ZMod.isUnit_iff_coprime i (p^3)).mpr (Nat.Coprime.pow_right 3 ((hp.coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)).symm))
    have key : ((i:ℕ):ZMod (p^3)) * (1 + u i) = ((i:ℕ):ZMod (p^3)) + b := by
      show ((i:ℕ):ZMod (p^3)) * (1 + b * ((i:ℕ):ZMod (p^3))⁻¹) = ((i:ℕ):ZMod (p^3)) + b
      rw [mul_add, mul_one, show ((i:ℕ):ZMod (p^3)) * (b * ((i:ℕ):ZMod (p^3))⁻¹)
        = b * (((i:ℕ):ZMod (p^3)) * ((i:ℕ):ZMod (p^3))⁻¹) by ring, ZMod.mul_inv_of_unit _ hci, mul_one]
    rw [key, hb, ← Nat.cast_add]; congr 1; omega
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, prod_Icc_cast]
  -- ∏(1+u) = 1
  rw [prod_one_add_truncate b hb3 u inv2 hinv2 _ hudvd]
  have hp30 : ((p:ZMod (p^3)))^3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hsumu : (∑ i ∈ Finset.Icc 1 (p-1), u i) = 0 := by
    simp only [hu, ← Finset.mul_sum]
    obtain ⟨y, hy⟩ := H1div hp hp5
    rw [hy, hb, show ((j*p:ℕ):ZMod (p^3)) * ((p:ZMod (p^3))^2 * y)
      = (j:ZMod (p^3)) * ((p:ZMod (p^3))^3) * y by push_cast; ring, hp30]; ring
  have hsumu2 : (∑ i ∈ Finset.Icc 1 (p-1), (u i)^2) = 0 := by
    simp only [hu, mul_pow, ← Finset.mul_sum]
    obtain ⟨z, hz⟩ := H2div hp hp5
    rw [hz, hb, show ((j*p:ℕ):ZMod (p^3))^2 * ((p:ZMod (p^3)) * z)
      = (j:ZMod (p^3))^2 * ((p:ZMod (p^3))^3) * z by push_cast; ring, hp30]; ring
  rw [hsumu, hsumu2]; ring

-- Partial block: ∏_{i=1}^r (q*p+i) ≡ r! · (1 + qp·H1 + (qp)²·(H1²-Q)·inv2) mod p³
-- where H1 = ∑ i⁻¹, Q = ∑ i⁻², inv2 = 1/2.
theorem partial_block (hp : Nat.Prime p) (hp5 : 5 ≤ p) (q r : ℕ) (hr : r ≤ p-1)
    (inv2 : ZMod (p^3)) (hinv2 : (2:ZMod (p^3)) * inv2 = 1) :
    ∏ i ∈ Finset.Icc 1 r, ((q*p+i : ℕ) : ZMod (p^3))
      = ((Nat.factorial r : ℕ) : ZMod (p^3)) *
        (1 + ((q*p:ℕ):ZMod (p^3)) * (∑ i ∈ Finset.Icc 1 r, ((i:ℕ):ZMod (p^3))⁻¹)
          + (((q*p:ℕ):ZMod (p^3))^2)
            * (((∑ i ∈ Finset.Icc 1 r, ((i:ℕ):ZMod (p^3))⁻¹)^2
                - ∑ i ∈ Finset.Icc 1 r, (((i:ℕ):ZMod (p^3))⁻¹)^2)) * inv2) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero (p^3) := ⟨pow_ne_zero 3 hp.pos.ne'⟩
  set b : ZMod (p^3) := ((q*p : ℕ) : ZMod (p^3)) with hb
  have hb3 : b^3 = 0 := by
    rw [hb, ← Nat.cast_pow, show (q*p)^3 = (q^3) * p^3 by ring, Nat.cast_mul, Nat.cast_pow,
      ZMod.natCast_self, mul_zero]
  set u : ℕ → ZMod (p^3) := fun i => b * ((i:ℕ):ZMod (p^3))⁻¹ with hu
  have hudvd : ∀ i ∈ Finset.Icc 1 r, b ∣ u i := fun i _ => ⟨((i:ℕ):ZMod (p^3))⁻¹, rfl⟩
  have hfac : ∀ i ∈ Finset.Icc 1 r,
      ((q*p+i : ℕ) : ZMod (p^3)) = ((i:ℕ):ZMod (p^3)) * (1 + u i) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hci : IsUnit ((i:ℕ):ZMod (p^3)) :=
      (ZMod.isUnit_iff_coprime i (p^3)).mpr (Nat.Coprime.pow_right 3 ((hp.coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)).symm))
    have key : ((i:ℕ):ZMod (p^3)) * (1 + u i) = ((i:ℕ):ZMod (p^3)) + b := by
      show ((i:ℕ):ZMod (p^3)) * (1 + b * ((i:ℕ):ZMod (p^3))⁻¹) = ((i:ℕ):ZMod (p^3)) + b
      rw [mul_add, mul_one, show ((i:ℕ):ZMod (p^3)) * (b * ((i:ℕ):ZMod (p^3))⁻¹)
        = b * (((i:ℕ):ZMod (p^3)) * ((i:ℕ):ZMod (p^3))⁻¹) by ring, ZMod.mul_inv_of_unit _ hci, mul_one]
    rw [key, hb, ← Nat.cast_add]; congr 1; omega
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, prod_Icc_cast,
    prod_one_add_truncate b hb3 u inv2 hinv2 _ hudvd]
  congr 1
  simp only [hu, ← Finset.mul_sum, mul_pow]
  ring

-- product of multiples of p up to m = p^q * q! where q = m/p
theorem prod_multiples (hp : Nat.Prime p) (m : ℕ) :
    ∏ t ∈ (Finset.Icc 1 m).filter (fun t => p ∣ t), (t : ZMod (p^3))
      = (p : ZMod (p^3))^(m/p) * ((Nat.factorial (m/p) : ℕ) : ZMod (p^3)) := by
  haveI : NeZero (p^3) := ⟨pow_ne_zero 3 hp.pos.ne'⟩
  have hbij : (Finset.Icc 1 m).filter (fun t => p ∣ t) = (Finset.Icc 1 (m/p)).image (fun j => p * j) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨j, rfl⟩⟩
      have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at h1)
      exact ⟨j, ⟨hj1, (Nat.le_div_iff_mul_le hp.pos).mpr (by rw [mul_comm]; exact h2)⟩, rfl⟩
    · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ⟨j, rfl⟩⟩
      · have := hp.two_le; nlinarith
      · calc p * j ≤ p * (m/p) := Nat.mul_le_mul_left p hj2
          _ = (m/p) * p := by ring
          _ ≤ m := Nat.div_mul_le_self m p
  rw [hbij, Finset.prod_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hp.pos h)]
  push_cast
  rw [Finset.prod_mul_distrib, Finset.prod_const, prod_Icc_cast, Nat.card_Icc, Nat.add_sub_cancel]
