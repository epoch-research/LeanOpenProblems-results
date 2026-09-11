import FormalConjectures.Util.ProblemImports

open scoped Real

/--
A364173: The sequence defined by the factorial ratio
$$a(n) = \frac{(9n)! (2n)! (3n/2)!}{(9n/2)! (4n)! (3n)! n!}$$
where fractional factorials $x!$ are defined as $\Gamma(x+1)$.
-/
noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))


open scoped BigOperators
namespace Super

lemma prod_expand {R ι : Type*} [CommRing R] (s : Finset ι) (f : ι → R)
    (t : R) (ht : t ^ 3 = 0) :
    2 * ∏ i ∈ s, (1 + t * f i) =
      2 + 2 * t * (∑ i ∈ s, f i) +
        t ^ 2 * ((∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, (f i) ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    linear_combination (1 + t * f a) * ih +
      (f a * (∑ i ∈ s, f i) ^ 2 - f a * ∑ i ∈ s, f i ^ 2) * ht

lemma prod_eq_one {R ι : Type*} [CommRing R] (s : Finset ι) (f : ι → R)
    (t : R) (ht : t ^ 3 = 0) (h2 : IsUnit (2 : R))
    (h1 : t * ∑ i ∈ s, f i = 0) (hs : t ^ 2 * ∑ i ∈ s, f i ^ 2 = 0) :
    ∏ i ∈ s, (1 + t * f i) = 1 := by
  apply h2.mul_left_cancel
  have h := prod_expand s f t ht
  have h11 : t ^ 2 * (∑ i ∈ s, f i) ^ 2 = 0 := by
    calc
      _ = (t * ∑ i ∈ s, f i) ^ 2 := by ring
      _ = 0 := by rw [h1]; simp
  linear_combination h - hs + h11 + 2 * h1

lemma prod_double {R ι : Type*} [CommRing R] (s : Finset ι) (f : ι → R)
    (t : R) (ht : t ^ 3 = 0) (h2 : IsUnit (2 : R))
    (hs : t ^ 2 * ∑ i ∈ s, f i ^ 2 = 0) :
    ∏ i ∈ s, (1 + (2 * t) * f i) = (∏ i ∈ s, (1 + t * f i)) ^ 2 := by
  have h := prod_expand s f t ht
  have ht' : (2 * t) ^ 3 = 0 := by rw [mul_pow, ht, mul_zero]
  have h' := prod_expand s f (2 * t) ht'
  have hts : t ^ 3 * (∑ i ∈ s, f i) = 0 := by rw [ht, zero_mul]
  have ht4 : t ^ 4 = 0 := by rw [show (4:ℕ) = 3+1 from rfl, pow_add, ht, zero_mul]
  apply (h2.mul h2).mul_left_cancel
  change (2 * 2) * _ = (2 * 2) * _
  linear_combination 2 * h' -
    (2 * (∏ i ∈ s, (1 + t * f i)) +
      (2 + 2 * t * (∑ i ∈ s, f i) +
        t ^ 2 * ((∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, f i ^ 2))) * h +
    (-4) * hs -
    4 * ((∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, f i ^ 2) * hts -
    ((∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, f i ^ 2) ^ 2 * ht4


lemma unit_nat {p : ℕ} (hp : p.Prime) (r n : ℕ) (hn : ¬ p ∣ n) :
    IsUnit (n : ZMod (p ^ r)) := by
  apply (ZMod.isUnit_iff_coprime _ _).mpr
  exact ((hp.coprime_iff_not_dvd.mpr hn).symm).pow_right r

lemma unit_small {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (r n : ℕ)
    (hpos : 0 < n) (hlt : n < 5) : IsUnit (n : ZMod (p ^ r)) := by
  apply unit_nat hp
  exact Nat.not_dvd_of_pos_of_lt hpos (lt_of_lt_of_le hlt h5)

lemma map_inv {m n : ℕ} (φ : ZMod m →+* ZMod n) (x : ZMod m) (hx : IsUnit x) :
    φ (x⁻¹) = (φ x)⁻¹ := by
  symm
  apply ZMod.inv_eq_of_mul_eq_one
  rw [← map_mul, ZMod.mul_inv_of_unit x hx, map_one]

lemma sum_units_sq (m : ℕ) [NeZero m] (h2 : IsUnit (2 : ZMod m))
    (h3 : IsUnit (3 : ZMod m)) :
    ∑ u : (ZMod m)ˣ, (u : ZMod m) ^ 2 = 0 := by
  classical
  obtain ⟨u, hu⟩ := h2
  have h := Equiv.sum_comp (Equiv.mulLeft u) (fun v : (ZMod m)ˣ => (v : ZMod m) ^ 2)
  change (∑ v : (ZMod m)ˣ, ((u * v : (ZMod m)ˣ) : ZMod m) ^ 2) = _ at h
  simp only [Units.val_mul, hu, mul_pow, ← Finset.mul_sum] at h
  apply h3.mul_left_cancel
  linear_combination h

lemma sum_units_inv_sq (m : ℕ) [NeZero m] (h2 : IsUnit (2 : ZMod m))
    (h3 : IsUnit (3 : ZMod m)) :
    ∑ u : (ZMod m)ˣ, (u : ZMod m)⁻¹ ^ 2 = 0 := by
  classical
  simp_rw [ZMod.inv_coe_unit]
  exact (Equiv.sum_comp (Equiv.inv ((ZMod m)ˣ)) (fun v : (ZMod m)ˣ => (v : ZMod m) ^ 2)).trans (sum_units_sq m h2 h3)

def inds (p N : ℕ) : Finset ℕ := (Finset.range N).filter (fun k => ¬ p ∣ k)
def block (p N : ℕ) : ℕ := ∏ k ∈ inds p N, k

@[simp] lemma mem_inds {p N k : ℕ} : k ∈ inds p N ↔ k < N ∧ ¬ p ∣ k := by
  simp [inds]

lemma inds_pos {p N k : ℕ} (hk : k ∈ inds p N) : 0 < k := by
  have := (mem_inds.mp hk).2
  by_contra h
  have : k = 0 := by omega
  simp [this] at *

lemma sum_inds_eq_units {p r : ℕ} [NeZero (p ^ r)] (hp : p.Prime) (hr : 0 < r)
    {A : Type*} [AddCommMonoid A] (f : ZMod (p ^ r) → A) :
    ∑ k ∈ inds p (p ^ r), f k = ∑ u : (ZMod (p ^ r))ˣ, f u := by
  classical
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  apply Finset.sum_bij (fun k hk => (unit_nat hp r k (mem_inds.mp hk).2).unit)
  · simp
  · intro a ha b hb hab
    have hab' := congrArg (fun u : (ZMod (p ^ r))ˣ => (u : ZMod (p ^ r)).val) hab
    simpa only [IsUnit.unit_spec, ZMod.val_natCast_of_lt (mem_inds.mp ha).1,
      ZMod.val_natCast_of_lt (mem_inds.mp hb).1] using hab'
  · intro u hu
    have hk : (u : ZMod (p ^ r)).val ∈ inds p (p ^ r) := by
      refine mem_inds.mpr ⟨ZMod.val_lt _, ?_⟩
      have hc := ZMod.val_coe_unit_coprime u
      intro hd
      have hpr : p ∣ p ^ r := dvd_pow_self _ (Nat.ne_of_gt hr)
      exact hp.not_dvd_one (dvd_trans (Nat.dvd_gcd hd hpr) (by rw [hc.gcd_eq_one]))
    refine ⟨(u : ZMod (p ^ r)).val, hk, ?_⟩
    apply Units.ext
    simp [ZMod.natCast_zmod_val]
  · intro a ha
    simp

lemma kill_of_cast_zero (A B : ℕ) [NeZero (A * B)]
    (x : ZMod (A * B))
    (hx : ZMod.castHom (dvd_mul_right A B) (ZMod A) x = 0) :
    (B : ZMod (A * B)) * x = 0 := by
  rw [← ZMod.natCast_zmod_val x] at hx ⊢
  rw [map_natCast, ZMod.natCast_eq_zero_iff] at hx
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  simpa [Nat.mul_comm] using Nat.mul_dvd_mul_left B hx


@[to_additive sum_inds_add]
lemma prod_inds_add {M : Type*} [CommMonoid M] (p A B : ℕ) (hpA : p ∣ A) (f : ℕ → M) :
    (∏ k ∈ inds p (A + B), f k) =
      (∏ k ∈ inds p A, f k) * ∏ k ∈ inds p B, f (A + k) := by
  classical
  simp only [inds, Finset.prod_filter]
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  simp only [Nat.dvd_add_right hpA]

@[to_additive sum_inds_multiple]
lemma prod_inds_multiple {M : Type*} [CommMonoid M] (p P : ℕ) (hpP : p ∣ P)
    (f : ℕ → M) (hf : ∀ k, f (P + k) = f k) (c : ℕ) :
    (∏ k ∈ inds p (c * P), f k) = (∏ k ∈ inds p P, f k) ^ c := by
  induction c with
  | zero => simp [inds]
  | succ c ih =>
    rw [Nat.succ_mul, Nat.add_comm, prod_inds_add p P (c * P) hpP]
    simp_rw [hf]
    rw [ih, pow_succ']

@[to_additive sum_inds_reflect]
lemma prod_inds_reflect {M : Type*} [CommMonoid M] (p N : ℕ) (hpN : p ∣ N)
    (f : ℕ → M) : (∏ k ∈ inds p N, f (N - k)) = ∏ k ∈ inds p N, f k := by
  classical
  apply Finset.prod_bij (fun k _ => N - k)
  · intro k hk
    obtain ⟨hkn, hkp⟩ := mem_inds.mp hk
    have hpos := inds_pos hk
    apply mem_inds.mpr
    refine ⟨by omega, ?_⟩
    intro hd
    apply hkp
    simpa [Nat.sub_sub_self hkn.le] using Nat.dvd_sub hpN hd
  · intro a ha b hb hab
    have := (mem_inds.mp ha).1
    have := (mem_inds.mp hb).1
    omega
  · intro b hb
    have hbn := (mem_inds.mp hb).1
    have hbpos := inds_pos hb
    have hnb : N - b ∈ inds p N := by
      refine mem_inds.mpr ⟨by omega, ?_⟩
      intro hd
      apply (mem_inds.mp hb).2
      have := Nat.dvd_sub hpN hd
      simpa [Nat.sub_sub_self hbn.le] using this
    exact ⟨N - b, hnb, by omega⟩
  · intros; rfl

lemma unit_cube {p : ℕ} (hp : p.Prime) (r n : ℕ) (hn : ¬ p ∣ n) :
    IsUnit (n : ZMod ((p ^ r) ^ 3)) := by
  rw [← pow_mul]
  exact unit_nat hp (r * 3) n hn

lemma cube_zero (P : ℕ) : (P : ZMod (P ^ 3)) ^ 3 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

lemma kill_sq_of_cast_zero (P : ℕ) [NeZero P] (x : ZMod (P ^ 3))
    (hx : ZMod.castHom (dvd_pow_self P (by decide : 3 ≠ 0)) (ZMod P) x = 0) :
    (P : ZMod (P ^ 3)) ^ 2 * x = 0 := by
  rw [← ZMod.natCast_zmod_val x] at hx ⊢
  rw [map_natCast, ZMod.natCast_eq_zero_iff] at hx
  rw [← Nat.cast_pow, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  obtain ⟨c, hc⟩ := hx
  refine ⟨c, ?_⟩
  rw [hc]
  ring

lemma harmonic_sq {p r : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hr : 0 < r) :
    (∑ k ∈ inds p (p ^ r), ((k : ZMod (p ^ r))⁻¹) ^ 2) = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [sum_inds_eq_units hp hr (fun x : ZMod (p ^ r) => x⁻¹ ^ 2)]
  exact sum_units_inv_sq _ (unit_small hp h5 r 2 (by decide) (by decide))
    (unit_small hp h5 r 3 (by decide) (by decide))

lemma harmonic_sq_multiple {p r : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hr : 0 < r)
    (c : ℕ) : (∑ k ∈ inds p (c * p ^ r), ((k : ZMod (p ^ r))⁻¹) ^ 2) = 0 := by
  rw [sum_inds_multiple p (p ^ r) (dvd_pow_self _ (Nat.ne_of_gt hr))]
  · rw [harmonic_sq hp h5 hr, nsmul_zero]
  · intro k
    simp

lemma harmonic_sq_cube {p r : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hr : 0 < r)
    (c : ℕ) :
    (p ^ r : ZMod ((p ^ r) ^ 3)) ^ 2 *
      (∑ k ∈ inds p (c * p ^ r), ((k : ZMod ((p ^ r) ^ 3))⁻¹) ^ 2) = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [← Nat.cast_pow]
  apply kill_sq_of_cast_zero
  rw [map_sum]
  convert harmonic_sq_multiple hp h5 hr c using 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_pow, map_inv _ _ (unit_cube hp r k (mem_inds.mp hk).2), map_natCast]

lemma pair_inverse {R : Type*} [CommRing R] (t x y ix iy : R)
    (ht : t ^ 3 = 0) (hxy : x + y = t) (hx : x * ix = 1) (hy : y * iy = 1) :
    t * (ix + iy) + t ^ 2 * ix ^ 2 = 0 := by
  have h : ix + iy = t * ix * iy := by
    rw [← hxy]
    linear_combination -iy * hx - ix * hy
  calc
    t * (ix + iy) + t ^ 2 * ix ^ 2 = t ^ 2 * ix * (ix + iy) := by
      conv_lhs => rw [h]
      ring
    _ = t ^ 3 * ix ^ 2 * iy := by rw [h]; ring
    _ = 0 := by rw [ht]; ring

lemma harmonic_one_cube {p r : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hr : 0 < r) :
    (p ^ r : ZMod ((p ^ r) ^ 3)) *
      (∑ k ∈ inds p (p ^ r), (k : ZMod ((p ^ r) ^ 3))⁻¹) = 0 := by
  let R := ZMod ((p ^ r) ^ 3)
  have h2 : IsUnit (2 : R) := by
    change IsUnit (2 : ZMod ((p ^ r) ^ 3))
    rw [← pow_mul]
    exact unit_small hp h5 (r*3) 2 (by decide) (by decide)
  have hsq := harmonic_sq_cube hp h5 hr 1
  simp only [one_mul] at hsq
  have hsum : ∑ k ∈ inds p (p ^ r),
      ((p ^ r : R) * ((k : R)⁻¹ + ((p ^ r - k : ℕ) : R)⁻¹) +
        (p ^ r : R) ^ 2 * (k : R)⁻¹ ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkn := (mem_inds.mp hk).1
    have hkp := (mem_inds.mp hk).2
    have hpn : p ∣ p ^ r := dvd_pow_self _ (Nat.ne_of_gt hr)
    have hsub : ¬p ∣ p ^ r - k := by
      intro hd
      apply hkp
      simpa [Nat.sub_sub_self hkn.le] using Nat.dvd_sub hpn hd
    apply pair_inverse _ (k : R) ((p ^ r - k : ℕ) : R)
    · simpa only [Nat.cast_pow] using cube_zero (p ^ r)
    · rw [Nat.cast_sub hkn.le, Nat.cast_pow]; ring
    · exact ZMod.mul_inv_of_unit _ (unit_cube hp r k hkp)
    · exact ZMod.mul_inv_of_unit _ (unit_cube hp r _ hsub)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [sum_inds_reflect p (p ^ r)
    (dvd_pow_self _ (Nat.ne_of_gt hr)) (fun k => (k : R)⁻¹)] at hsum
  apply h2.mul_left_cancel
  change (2 : R) * _ = 2 * 0
  linear_combination hsum - hsq


@[simp] lemma block_cast {R : Type*} [CommSemiring R] (p N : ℕ) :
    (block p N : R) = ∏ k ∈ inds p N, (k : R) := by
  simp [block]

lemma block_unit {p : ℕ} (hp : p.Prime) (r N : ℕ) : IsUnit (block p N : ZMod (p ^ r)) := by
  rw [block_cast]
  exact IsUnit.prod_iff.mpr (fun k hk => unit_nat hp r k (mem_inds.mp hk).2)

lemma block_unit_cube {p : ℕ} (hp : p.Prime) (r N : ℕ) :
    IsUnit (block p N : ZMod ((p ^ r) ^ 3)) := by
  rw [← pow_mul]
  exact block_unit hp _ _

lemma shifted_block_cube {p r : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hr : 0 < r) (c : ℕ) :
    (∏ k ∈ inds p (p ^ r), ((c * p ^ r + k : ℕ) : ZMod ((p ^ r) ^ 3))) =
      (block p (p ^ r) : ZMod ((p ^ r) ^ 3)) := by
  let R := ZMod ((p ^ r) ^ 3)
  have h2 : IsUnit (2 : R) := by
    change IsUnit (2 : ZMod ((p ^ r) ^ 3))
    rw [← pow_mul]
    exact unit_small hp h5 (r*3) 2 (by decide) (by decide)
  have ht : ((c : R) * (p : R) ^ r) ^ 3 = 0 := by
    rw [mul_pow]
    have hz : ((p : R) ^ r) ^ 3 = 0 := by simpa using cube_zero (p ^ r)
    rw [hz, mul_zero]
  have h1 : ((c : R) * (p : R) ^ r) * ∑ k ∈ inds p (p ^ r), (k : R)⁻¹ = 0 := by
    rw [mul_assoc, harmonic_one_cube hp h5 hr, mul_zero]
  have hs : ((c : R) * (p : R) ^ r) ^ 2 *
      ∑ k ∈ inds p (p ^ r), (k : R)⁻¹ ^ 2 = 0 := by
    rw [mul_pow, mul_assoc]
    have h := harmonic_sq_cube hp h5 hr 1
    simp only [one_mul] at h
    rw [h, mul_zero]
  calc
    _ = ∏ k ∈ inds p (p ^ r),
        (k : R) * (1 + ((c : R) * (p : R) ^ r) * (k : R)⁻¹) := by
      apply Finset.prod_congr rfl
      intro k hk
      push_cast
      have h := ZMod.mul_inv_of_unit (k : R) (unit_cube hp r k (mem_inds.mp hk).2)
      linear_combination -((c : R) * (p : R) ^ r) * h
    _ = _ := by
      rw [Finset.prod_mul_distrib, prod_eq_one _ _ _ ht h2 h1 hs, mul_one, block_cast]

lemma block_multiple_cube {p r : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hr : 0 < r) (c : ℕ) :
    (block p (c * p ^ r) : ZMod ((p ^ r) ^ 3)) =
      (block p (p ^ r) : ZMod ((p ^ r) ^ 3)) ^ c := by
  induction c with
  | zero => simp [block, inds]
  | succ c ih =>
    rw [Nat.succ_mul, block_cast, prod_inds_add p (c * p ^ r) (p ^ r)
      (dvd_mul_of_dvd_right (dvd_pow_self p (Nat.ne_of_gt hr)) c)]
    rw [← block_cast, ih, shifted_block_cube hp h5 hr]
    simp only [pow_succ]

lemma block_multiple_base {p : ℕ} (hp : p.Prime) (c : ℕ) :
    (block p (c * p) : ZMod p) = (block p p : ZMod p) ^ c := by
  simp only [block_cast]
  exact prod_inds_multiple p p (dvd_refl p) (fun k => (k : ZMod p))
    (fun k => by simp) c


lemma reflect_mem {p N k : ℕ} (hpN : p ∣ N) (hk : k ∈ inds p N) :
    N - k ∈ inds p N := by
  have hkn := (mem_inds.mp hk).1
  have hkpos := inds_pos hk
  refine mem_inds.mpr ⟨by omega, ?_⟩
  intro hd
  apply (mem_inds.mp hk).2
  simpa [Nat.sub_sub_self hkn.le] using Nat.dvd_sub hpN hd

@[to_additive]
lemma prod_inds_halves {M : Type*} [CommMonoid M] (p N : ℕ) (hpN : p ∣ N)
    (hN : N % 2 = 1) (f : ℕ → M) :
    (∏ k ∈ inds p N, f k) = (∏ k ∈ inds p (N / 2 + 1), f k) *
      ∏ k ∈ inds p (N / 2 + 1), f (N - k) := by
  classical
  have hlow : (inds p N).filter (fun k => k ≤ N/2) = inds p (N/2+1) := by
    ext k
    simp only [Finset.mem_filter, mem_inds]
    omega
  have hhi : (∏ k ∈ inds p (N/2+1), f (N-k)) =
      ∏ k ∈ (inds p N).filter (fun k => ¬ k ≤ N/2), f k := by
    apply Finset.prod_bij (fun k _ => N-k)
    · intro k hk
      have hkn := (mem_inds.mp hk).1
      have hkp := (mem_inds.mp hk).2
      have hkpos := inds_pos hk
      have hk' : k ∈ inds p N := mem_inds.mpr ⟨by omega, hkp⟩
      exact Finset.mem_filter.mpr ⟨reflect_mem hpN hk', by omega⟩
    · intro a ha b hb hab
      have := (mem_inds.mp ha).1
      have := (mem_inds.mp hb).1
      omega
    · intro b hb
      obtain ⟨hb, hbh⟩ := Finset.mem_filter.mp hb
      have hbN := (mem_inds.mp hb).1
      have hnb := reflect_mem hpN hb
      have hk : N-b ∈ inds p (N/2+1) :=
        mem_inds.mpr ⟨by omega, (mem_inds.mp hnb).2⟩
      exact ⟨N-b, hk, by omega⟩
    · intros; rfl
  rw [← Finset.prod_filter_mul_prod_filter_not (inds p N) (fun k => k ≤ N/2),
    hlow, ← hhi]

lemma inv_neg_unit {m : ℕ} (x : ZMod m) (hx : IsUnit x) : (-x)⁻¹ = -x⁻¹ := by
  apply ZMod.inv_eq_of_mul_eq_one
  simpa using ZMod.mul_inv_of_unit x hx

lemma harmonic_sq_half {p r : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hr : 0 < r)
    (c : ℕ) (hN : (c * p ^ r) % 2 = 1) :
    (∑ k ∈ inds p ((c * p ^ r) / 2 + 1), ((k : ZMod (p ^ r))⁻¹) ^ 2) = 0 := by
  let N := c * p ^ r
  let R := ZMod (p ^ r)
  have h2 : IsUnit (2 : R) := unit_small hp h5 r 2 (by decide) (by decide)
  have hpN : p ∣ N := dvd_mul_of_dvd_right (dvd_pow_self p (Nat.ne_of_gt hr)) c
  have h := harmonic_sq_multiple hp h5 hr c
  rw [sum_inds_halves p N hpN hN] at h
  have heq : (∑ k ∈ inds p (N/2+1), ((N-k : ℕ) : R)⁻¹ ^ 2) =
      ∑ k ∈ inds p (N/2+1), (k : R)⁻¹ ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkN : k ≤ N := by have := (mem_inds.mp hk).1; omega
    have hzero : (N : R) = 0 := by simp [N, R]
    rw [Nat.cast_sub hkN, hzero, zero_sub,
      inv_neg_unit _ (unit_nat hp r k (mem_inds.mp hk).2), neg_sq]
  rw [heq] at h
  apply h2.mul_left_cancel
  linear_combination h

lemma harmonic_sq_half_cube {p r : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hr : 0 < r)
    (c : ℕ) (hN : (c * p ^ r) % 2 = 1) :
    (p ^ r : ZMod ((p ^ r) ^ 3)) ^ 2 *
      (∑ k ∈ inds p ((c * p ^ r) / 2 + 1), ((k : ZMod ((p ^ r) ^ 3))⁻¹) ^ 2) = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [← Nat.cast_pow]
  apply kill_sq_of_cast_zero
  rw [map_sum]
  convert harmonic_sq_half hp h5 hr c hN using 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_pow, map_inv _ _ (unit_cube hp r k (mem_inds.mp hk).2), map_natCast]

@[to_additive]
lemma prod_inds_double_halves {M : Type*} [CommMonoid M] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (N : ℕ) (hpN : p ∣ N) (hN : N % 2 = 1) (f : ℕ → M) :
    (∏ k ∈ inds p N, f k) = (∏ k ∈ inds p (N / 2 + 1), f (2*k)) *
      ∏ k ∈ inds p (N / 2 + 1), f (N - 2*k) := by
  classical
  have hp_two : ¬p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have hmul : ∀ k, p ∣ 2*k ↔ p ∣ k := fun k => by
    rw [hp.dvd_mul]; simp [hp_two]
  have heven : (∏ k ∈ inds p (N/2+1), f (2*k)) =
      ∏ k ∈ (inds p N).filter (fun k => k % 2 = 0), f k := by
    apply Finset.prod_bij (fun k _ => 2*k)
    · intro k hk
      obtain ⟨hkn, hkp⟩ := mem_inds.mp hk
      exact Finset.mem_filter.mpr ⟨mem_inds.mpr ⟨by omega, by simpa [hmul] using hkp⟩,
        by omega⟩
    · intros; omega
    · intro b hb
      obtain ⟨hb, hbe⟩ := Finset.mem_filter.mp hb
      obtain ⟨hbN, hbp⟩ := mem_inds.mp hb
      have hb : 2 * (b/2) = b := by omega
      refine ⟨b/2, mem_inds.mpr ⟨by omega, ?_⟩, hb⟩
      intro hd
      apply hbp
      rw [← hb, hmul]
      exact hd
    · intros; rfl
  have hodd : (∏ k ∈ inds p (N/2+1), f (N-2*k)) =
      ∏ k ∈ (inds p N).filter (fun k => ¬ k % 2 = 0), f k := by
    apply Finset.prod_bij (fun k _ => N-2*k)
    · intro k hk
      obtain ⟨hkn, hkp⟩ := mem_inds.mp hk
      have hkpos := inds_pos hk
      have hk' : 2*k ∈ inds p N := mem_inds.mpr ⟨by omega, by simpa [hmul] using hkp⟩
      exact Finset.mem_filter.mpr ⟨reflect_mem hpN hk', by omega⟩
    · intro a ha b hb hab
      have := (mem_inds.mp ha).1
      have := (mem_inds.mp hb).1
      omega
    · intro b hb
      obtain ⟨hb, hbo⟩ := Finset.mem_filter.mp hb
      have hbN := (mem_inds.mp hb).1
      have hbpos := inds_pos hb
      have hnb := reflect_mem hpN hb
      have heq : 2 * ((N-b)/2) = N-b := by omega
      have hk : (N-b)/2 ∈ inds p (N/2+1) := by
        refine mem_inds.mpr ⟨by omega, ?_⟩
        intro hd
        apply (mem_inds.mp hnb).2
        rw [← heq, hmul]
        exact hd
      exact ⟨(N-b)/2, hk, by omega⟩
    · intros; rfl
  rw [← Finset.prod_filter_mul_prod_filter_not (inds p N) (fun k => k % 2 = 0),
    ← heven, ← hodd]


lemma prod_affine {q : ℕ} (s : Finset ℕ) (d v : ZMod q)
    (hu : ∀ k ∈ s, IsUnit (k : ZMod q)) :
    (∏ k ∈ s, d * ((k : ZMod q) + v)) =
      d ^ s.card * (∏ k ∈ s, (k : ZMod q)) * ∏ k ∈ s, (1 + v * (k : ZMod q)⁻¹) := by
  classical
  calc
    _ = ∏ k ∈ s, d * (k : ZMod q) * (1 + v * (k : ZMod q)⁻¹) := by
      apply Finset.prod_congr rfl
      intro k hk
      have h := ZMod.mul_inv_of_unit (k : ZMod q) (hu k hk)
      linear_combination -(d * v) * h
    _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_const]

lemma square_eliminate {R : Type*} [CommRing R] (a b d s v : R)
    (hs : s ^ 2 = 1) (hb : IsUnit b)
    (h1 : b = s * a ^ 2 * v ^ 2) (h2 : b = s * d * a ^ 2 * v) :
    a ^ 2 * d ^ 2 = s * b := by
  apply hb.mul_left_cancel
  linear_combination (a ^ 2 * d ^ 2) * h1 -
    s * (b + s * d * a ^ 2 * v) * h2 - s * d ^ 2 * a ^ 4 * v ^ 2 * hs

lemma half_block_cube {p r : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hr : 0 < r)
    (c : ℕ) (hN : (c * p ^ r) % 2 = 1) :
    (block p ((c * p ^ r) / 2 + 1) : ZMod ((p ^ r) ^ 3)) ^ 2 *
        16 ^ (inds p ((c * p ^ r) / 2 + 1)).card =
      (-1) ^ (inds p ((c * p ^ r) / 2 + 1)).card * (block p (c * p ^ r) : ZMod ((p ^ r) ^ 3)) := by
  let R := ZMod ((p ^ r) ^ 3)
  let N := c * p ^ r
  let S := inds p (N/2+1)
  let M := S.card
  let A : R := block p (N/2+1)
  let B : R := block p N
  let t : R := -(N : R) * (2 : R)⁻¹
  let V : R := ∏ k ∈ S, (1 + t * (k : R)⁻¹)
  have hu : ∀ k ∈ S, IsUnit (k : R) := fun k hk => unit_cube hp r k (mem_inds.mp hk).2
  have htwo : IsUnit (2 : R) := by
    change IsUnit (2 : ZMod ((p ^ r) ^ 3))
    rw [← pow_mul]
    exact unit_small hp h5 (r*3) 2 (by decide) (by decide)
  have hinv : (2 : R) * (2 : R)⁻¹ = 1 := ZMod.mul_inv_of_unit _ htwo
  have hpN : p ∣ N := dvd_mul_of_dvd_right (dvd_pow_self p (Nat.ne_of_gt hr)) c
  have hNt : (2 : R) * t = -(N : R) := by
    dsimp [t]
    linear_combination -(N : R) * hinv
  have ht : t ^ 3 = 0 := by
    have hz : ((p : R) ^ r) ^ 3 = 0 := by simpa using cube_zero (p ^ r)
    dsimp [t, N]
    push_cast
    rw [mul_pow, neg_pow, mul_pow, hz]
    ring
  have hs : t ^ 2 * ∑ k ∈ S, (k : R)⁻¹ ^ 2 = 0 := by
    have h := harmonic_sq_half_cube hp h5 hr c hN
    dsimp [t, N, S]
    push_cast
    linear_combination (c : R) ^ 2 * (2 : R)⁻¹ ^ 2 * h
  have hv : (∏ k ∈ S, (1 + (-(N : R)) * (k : R)⁻¹)) = V ^ 2 := by
    rw [← hNt]
    exact prod_double S (fun k => (k : R)⁻¹) t ht htwo hs
  have h1 : B = (-1 : R) ^ M * A ^ 2 * V ^ 2 := by
    change (block p N : R) = _
    rw [block_cast, prod_inds_halves p N hpN hN]
    have heq : (∏ k ∈ S, ((N-k : ℕ) : R)) = (-1 : R)^M * A *
        ∏ k ∈ S, (1 + (-(N : R)) * (k : R)⁻¹) := by
      have h := prod_affine S (-1 : R) (-(N : R)) hu
      convert h using 1
      · apply Finset.prod_congr rfl
        intro k hk
        have hkN : k ≤ N := by have := (mem_inds.mp hk).1; omega
        rw [Nat.cast_sub hkN]
        ring
      · simp only [A, block_cast, S, M]
    change (∏ k ∈ S, (k : R)) * (∏ k ∈ S, ((N-k : ℕ) : R)) = _
    rw [heq, hv]
    have hA : (∏ k ∈ S, (k : R)) = A := (block_cast p (N/2+1)).symm
    rw [hA]
    ring
  have h2 : B = (-1 : R) ^ M * (4 : R)^M * A ^ 2 * V := by
    change (block p N : R) = _
    rw [block_cast, prod_inds_double_halves hp (by omega) N hpN hN]
    have heq : (∏ k ∈ S, ((N-2*k : ℕ) : R)) = (-2 : R)^M * A * V := by
      have h := prod_affine S (-2 : R) t hu
      convert h using 1
      · apply Finset.prod_congr rfl
        intro k hk
        have hkN : 2*k ≤ N := by have := (mem_inds.mp hk).1; omega
        rw [Nat.cast_sub hkN]
        have hNt' := hNt
        push_cast at hNt' ⊢
        linear_combination hNt'
      · simp only [A, block_cast, S, M, V]
    change (∏ k ∈ S, ((2*k : ℕ) : R)) * (∏ k ∈ S, ((N-2*k : ℕ) : R)) = _
    rw [heq]
    have hd : (∏ k ∈ S, ((2*k : ℕ) : R)) = (2 : R)^M * A := by
      simp only [Nat.cast_mul, Nat.cast_two, Finset.prod_mul_distrib, Finset.prod_const]
      simp only [M, A, block_cast, S]
    rw [hd]
    have hpow : (2 : R)^M * (-2 : R)^M = (-1 : R)^M * (4 : R)^M := by
      rw [← mul_pow, ← mul_pow]
      congr 1
      ring
    calc
      _ = ((2 : R)^M * (-2 : R)^M) * A^2 * V := by ring
      _ = _ := by rw [hpow]
  have hsign : ((-1 : R)^M)^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm M 2, pow_mul]
    norm_num
  have hfour : ((4 : R)^M)^2 = (16 : R)^M := by
    rw [← pow_mul, Nat.mul_comm M 2, pow_mul]
    norm_num
  have h := square_eliminate A B ((4 : R)^M) ((-1 : R)^M) V hsign
    (block_unit_cube hp r N) h1 h2
  rw [hfour] at h
  exact h


lemma card_inds_succ (p n : ℕ) : (inds p (n+1)).card = n - n/p := by
  have heq : inds p (n+1) = (Finset.Ioc 0 n).filter (fun k => ¬p ∣ k) := by
    ext k
    simp only [mem_inds, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hk, hd⟩
      exact ⟨⟨Nat.pos_of_ne_zero (by rintro rfl; exact hd (dvd_zero p)), by omega⟩, hd⟩
    · omega
  rw [heq]
  have h := Finset.card_filter_add_card_filter_not (s := Finset.Ioc 0 n) (fun k => p ∣ k)
  rw [Nat.Ioc_filter_dvd_card_eq_div] at h
  simp only [Nat.card_Ioc, Nat.sub_zero] at h
  omega

lemma half_mul_odd (m p : ℕ) (hp : p % 2 = 1) :
    m*p/2 = m*(p/2) + m/2 := by
  have heq : m*p = (m*(p/2))*2 + m := by
    have h : p = p/2*2 + 1 := by omega
    conv_lhs => rw [h]
    ring
  omega

lemma card_half_block {p : ℕ} (hp : 0 < p) (hpodd : p % 2 = 1) (m : ℕ) :
    (inds p (m*p/2+1)).card = m*(p/2) := by
  rw [card_inds_succ]
  have hd : m*p/2/p = m/2 := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm 2 p, ← Nat.div_div_eq_div_mul,
      Nat.mul_div_cancel _ hp]
  rw [hd, half_mul_odd m p hpodd]
  omega

lemma half_block_base {p : ℕ} (hp : p.Prime) (m : ℕ) (hm : m % 2 = 1) :
    (block p (m*p/2+1) : ZMod p) =
      (block p p : ZMod p)^(m/2) * (block p (p/2+1) : ZMod p) := by
  have heq : m*p/2+1 = (m/2)*p + (p/2+1) := by
    have h := half_mul_odd p m hm
    rw [Nat.mul_comm p m, Nat.mul_comm p (m/2)] at h
    omega
  rw [heq, block_cast, prod_inds_add p ((m/2)*p) (p/2+1) (dvd_mul_left p (m/2))]
  have htail : (∏ k ∈ inds p (p/2+1), (((m/2)*p+k : ℕ) : ZMod p)) =
      (block p (p/2+1) : ZMod p) := by
    simp
  rw [htail, ← block_cast, block_multiple_base hp]

lemma unit_of_base {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (x : ZMod (p ^ k))
    (hx : IsUnit (ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hk)) (ZMod p) x)) :
    IsUnit x := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x] at hx ⊢
  rw [map_natCast, ZMod.isUnit_iff_coprime] at hx
  apply unit_nat hp
  exact hp.coprime_iff_not_dvd.mp hx.symm

lemma eq_of_sq_eq_base {p k : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hk : 0 < k)
    (x y : ZMod (p ^ k)) (hy : IsUnit y) (hxy : x ^ 2 = y ^ 2)
    (hbase : ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hk)) (ZMod p) x =
      ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hk)) (ZMod p) y) : x = y := by
  let φ := ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hk)) (ZMod p)
  have hu : IsUnit (x+y) := by
    apply unit_of_base hp hk
    change IsUnit (φ (x+y))
    rw [map_add, hbase, ← two_mul]
    have h2 : IsUnit (2 : ZMod p) := by
      have h := unit_small hp h5 1 2 (by decide) (by decide)
      rw [pow_one] at h
      exact h
    exact h2.mul (hy.map φ)
  apply hu.mul_left_cancel
  linear_combination hxy

lemma sixteen_half_pow {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (16 : ZMod p) ^ (p/2) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : p % 2 = 1 := by
    have := hp.eq_two_or_odd
    rcases this with h | h
    · omega
    · exact h
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega) hd
  have hpow : (2 : ZMod p)^(p-1) = 1 := ZMod.pow_card_sub_one_eq_one h2
  calc
    (16 : ZMod p)^(p/2) = ((2 : ZMod p)^(p-1))^2 := by
      rw [show (16 : ZMod p) = 2^4 by norm_num, ← pow_mul, ← pow_mul]
      congr 1
      omega
    _ = 1 := by rw [hpow]; norm_num


lemma odd_blocks_base {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (m : ℕ) (hm : m % 2 = 1) :
    (16 : ZMod p)^(3*m*(p/2)) * (block p (9*m*p/2+1) : ZMod p) * (block p (2*m*p) : ZMod p) =
      (block p (3*m*p/2+1) : ZMod p) * (block p (4*m*p) : ZMod p) * (block p (m*p) : ZMod p) := by
  have h9 : (9*m) % 2 = 1 := by omega
  have h3 : (3*m) % 2 = 1 := by omega
  have h16 : (16 : ZMod p)^(3*m*(p/2)) = 1 := by
    rw [Nat.mul_comm (3*m) (p/2), pow_mul, sixteen_half_pow hp h5, one_pow]
  rw [h16, one_mul, half_block_base hp (9*m) h9, half_block_base hp (3*m) h3,
    block_multiple_base hp (2*m), block_multiple_base hp (4*m), block_multiple_base hp m]
  let b : ZMod p := block p p
  let h : ZMod p := block p (p/2+1)
  change b^(9*m/2) * h * b^(2*m) = b^(3*m/2) * h * b^(4*m) * b^m
  calc
    _ = b^(9*m/2+2*m) * h := by rw [pow_add]; ring
    _ = b^(3*m/2+4*m+m) * h := by
      have he : 9*m/2+2*m = 3*m/2+4*m+m := by omega
      rw [he]
    _ = _ := by simp only [pow_add]; ring

lemma eq_of_sq_eq_base_cube {p r : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hr : 0 < r)
    (x y : ZMod ((p ^ r) ^ 3)) (hy : IsUnit y) (hxy : x ^ 2 = y ^ 2)
    (hbase : ZMod.castHom (dvd_trans (dvd_pow_self p (Nat.ne_of_gt hr))
        (dvd_pow_self (p ^ r) (by decide : 3 ≠ 0))) (ZMod p) x =
      ZMod.castHom (dvd_trans (dvd_pow_self p (Nat.ne_of_gt hr))
        (dvd_pow_self (p ^ r) (by decide : 3 ≠ 0))) (ZMod p) y) : x = y := by
  haveI : NeZero ((p^r)^3) := ⟨pow_ne_zero _ (pow_ne_zero _ hp.ne_zero)⟩
  let φ := ZMod.castHom (dvd_trans (dvd_pow_self p (Nat.ne_of_gt hr))
    (dvd_pow_self (p^r) (by decide : 3 ≠ 0))) (ZMod p)
  have liftunit (a : ZMod ((p^r)^3)) (ha : IsUnit (φ a)) : IsUnit a := by
    rw [← ZMod.natCast_zmod_val a] at ha ⊢
    rw [map_natCast, ZMod.isUnit_iff_coprime] at ha
    apply unit_cube hp
    exact hp.coprime_iff_not_dvd.mp ha.symm
  have hu : IsUnit (x+y) := by
    apply liftunit
    rw [map_add, hbase, ← two_mul]
    have h2 : IsUnit (2 : ZMod p) := by
      have h := unit_small hp h5 1 2 (by decide) (by decide)
      rw [pow_one] at h
      exact h
    exact h2.mul (hy.map φ)
  apply hu.mul_left_cancel
  linear_combination hxy

lemma odd_square {R : Type*} [CommRing R] (L A B s z : R) (hL : IsUnit L)
    (hA : A^2*L^3 = s*z^9) (hB : B^2*L = s*z^3) :
    (L*A*z^2)^2 = (B*z^4*z)^2 := by
  apply hL.mul_left_cancel
  linear_combination z^4*hA - z^10*hB

lemma odd_blocks_cube {p r : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hr : 0 < r)
    (m c : ℕ) (hm : m % 2 = 1) (hmc : m*p = c*p^r) :
    (16 : ZMod ((p^r)^3))^(3*m*(p/2)) *
        (block p (9*m*p/2+1) : ZMod ((p^r)^3)) * (block p (2*m*p) : ZMod ((p^r)^3)) =
      (block p (3*m*p/2+1) : ZMod ((p^r)^3)) * (block p (4*m*p) : ZMod ((p^r)^3)) *
        (block p (m*p) : ZMod ((p^r)^3)) := by
  let R := ZMod ((p^r)^3)
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  let D := 3*m*(p/2)
  let L : R := 16^D
  let A : R := block p (9*m*p/2+1)
  let B : R := block p (3*m*p/2+1)
  let s : R := (-1)^D
  let z : R := (block p (p^r) : R)^c
  have full (k : ℕ) : (block p (k*m*p) : R) = z^k := by
    have heq : k*m*p = (c*k)*p^r := by
      calc
        _ = k*(m*p) := by ring
        _ = k*(c*p^r) := by rw [hmc]
        _ = _ := by ring
    rw [heq, block_multiple_cube hp h5 hr, pow_mul]
  have hL : IsUnit L := by
    have h2 : IsUnit (2 : R) := by
      change IsUnit (2 : ZMod ((p^r)^3))
      rw [← pow_mul]
      exact unit_small hp h5 (r*3) 2 (by decide) (by decide)
    have h16 : IsUnit (16 : R) := by convert h2.pow 4 using 1 <;> norm_num
    exact h16.pow D
  have hs3 : s^3 = s := by
    change ((-1 : R)^D)^3 = (-1 : R)^D
    rw [← pow_mul (-1 : R) D 3, Nat.mul_comm D 3, pow_mul (-1 : R) 3 D]
    rw [show (-1 : R)^3 = (-1 : R) by ring]
  have hn (k : ℕ) : (k*c)*p^r = k*m*p := by
    calc
      _ = k*(c*p^r) := by ring
      _ = k*(m*p) := by rw [hmc]
      _ = _ := by ring
  have hA : A^2*L^3 = s*z^9 := by
    have hnodd : ((9*c)*p^r) % 2 = 1 := by
      rw [hn 9]
      simp [Nat.mul_mod, hm, hpodd]
    have h := half_block_cube hp h5 hr (9*c) hnodd
    rw [hn 9, card_half_block hp.pos hpodd (9*m), full 9] at h
    have he : 9*m*(p/2) = D*3 := by dsimp [D]; ring
    rw [he, pow_mul (16 : R) D 3, pow_mul (-1 : R) D 3] at h
    change A^2*L^3 = s^3*z^9 at h
    rwa [hs3] at h
  have hB : B^2*L = s*z^3 := by
    have hnodd : ((3*c)*p^r) % 2 = 1 := by
      rw [hn 3]
      simp [Nat.mul_mod, hm, hpodd]
    have h := half_block_cube hp h5 hr (3*c) hnodd
    rw [hn 3, card_half_block hp.pos hpodd (3*m), full 3] at h
    exact h
  apply eq_of_sq_eq_base_cube hp h5 hr
  · exact ((block_unit_cube hp r _).mul (block_unit_cube hp r _)).mul (block_unit_cube hp r _)
  · rw [full 2, full 4]
    have hfull1 : (block p (m*p) : R) = z := by simpa using full 1
    rw [hfull1]
    exact odd_square L A B s z hL hA hB
  · simp only [map_mul, map_pow, map_natCast, map_ofNat]
    exact odd_blocks_base hp h5 m hm


lemma block_succ (p n : ℕ) : block p (n+1) =
    if p ∣ n then block p n else block p n * n := by
  classical
  unfold block inds
  rw [Finset.range_succ, Finset.filter_insert]
  by_cases hn : p ∣ n
  · simp [hn]
  · simp [hn, Finset.mem_filter, Finset.mem_range, mul_comm]

lemma factorial_strip {p : ℕ} (hp : 0 < p) (n : ℕ) :
    n.factorial = p^(n/p) * (n/p).factorial * block p (n+1) := by
  induction n with
  | zero =>
    simp only [Nat.zero_div, Nat.factorial_zero, pow_zero, one_mul]
    rw [block_succ]
    simp [block, inds]
  | succ n ih =>
    rw [Nat.factorial_succ, ih, block_succ p (n+1)]
    by_cases hd : p ∣ n+1
    · rw [if_pos hd, Nat.succ_div_of_dvd hd, Nat.factorial_succ, pow_succ]
      have heq : n+1 = p*(n/p+1) := by
        have h := Nat.div_mul_cancel hd
        rw [Nat.succ_div_of_dvd hd] at h
        simpa [Nat.mul_comm] using h.symm
      rw [heq]
      ring
    · rw [if_neg hd, Nat.succ_div_of_not_dvd hd]
      ring

lemma factorial_mul_strip {p : ℕ} (hp : 0 < p) (m : ℕ) :
    (m*p).factorial = p^m * m.factorial * block p (m*p) := by
  rw [factorial_strip hp, Nat.mul_div_cancel _ hp, block_succ,
    if_pos (dvd_mul_left p m)]

lemma factorial_half_strip {p : ℕ} (hp : 0 < p) (m : ℕ) :
    (m*p/2).factorial = p^(m/2) * (m/2).factorial * block p (m*p/2+1) := by
  rw [factorial_strip hp]
  have hd : m*p/2/p = m/2 := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm 2 p, ← Nat.div_div_eq_div_mul,
      Nat.mul_div_cancel _ hp]
  rw [hd]

noncomputable def aa (n : ℕ) : ℝ :=
  (Real.Gamma (9 * (n:ℝ) + 1) * Real.Gamma (2 * (n:ℝ) + 1) * Real.Gamma (3 / 2 * (n:ℝ) + 1)) /
  (Real.Gamma (9 / 2 * (n:ℝ) + 1) * Real.Gamma (4 * (n:ℝ) + 1) * Real.Gamma (3 * (n:ℝ) + 1) * Real.Gamma ((n:ℝ) + 1))

lemma gamma_double_nat (k : ℕ) :
    Real.Gamma (((k:ℝ)+1)/2) * Real.Gamma ((k:ℝ)/2+1) * (2:ℝ)^k =
      (k.factorial : ℝ) * Real.sqrt Real.pi := by
  have h := Real.Gamma_mul_Gamma_add_half (((k:ℝ)+1)/2)
  have h1 : ((k:ℝ)+1)/2+1/2 = (k:ℝ)/2+1 := by ring
  have h2 : 2*(((k:ℝ)+1)/2) = (k:ℝ)+1 := by ring
  rw [h1, h2, show 1-((k:ℝ)+1) = -(k:ℝ) by ring,
    Real.Gamma_nat_eq_factorial, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
    Real.rpow_natCast] at h
  rw [h]
  have hne : (2:ℝ)^k ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

lemma aa_even (m : ℕ) :
    aa (2*m) =
      ((18*m).factorial : ℝ) * (4*m).factorial * (3*m).factorial /
        ((9*m).factorial * (8*m).factorial * (6*m).factorial * (2*m).factorial) := by
  unfold aa
  have h9 : 9*(↑(2*m):ℝ)+1 = (↑(18*m):ℝ)+1 := by push_cast; ring
  have h2 : 2*(↑(2*m):ℝ)+1 = (↑(4*m):ℝ)+1 := by push_cast; ring
  have h3 : 3/2*(↑(2*m):ℝ)+1 = (↑(3*m):ℝ)+1 := by push_cast; ring
  have h92 : 9/2*(↑(2*m):ℝ)+1 = (↑(9*m):ℝ)+1 := by push_cast; ring
  have h4 : 4*(↑(2*m):ℝ)+1 = (↑(8*m):ℝ)+1 := by push_cast; ring
  have h6 : 3*(↑(2*m):ℝ)+1 = (↑(6*m):ℝ)+1 := by push_cast; ring
  rw [h9,h2,h3,h92,h4,h6]
  simp only [Real.Gamma_nat_eq_factorial]

lemma half_nat_real (k : ℕ) (hk : k % 2 = 1) : ((k:ℝ)+1)/2 = (k/2:ℕ)+1 := by
  have h : k = 2*(k/2)+1 := by omega
  have hc : (k:ℝ) = 2*(k/2:ℕ)+1 := by exact_mod_cast h
  linarith

lemma aa_odd (n : ℕ) (hn : n % 2 = 1) :
    aa n = (2:ℝ)^(6*n) * (9*n/2).factorial * (2*n).factorial /
      ((3*n/2).factorial * (4*n).factorial * n.factorial) := by
  have h9 := gamma_double_nat (9*n)
  have h3 := gamma_double_nat (3*n)
  have hn9 : (9*n)%2 = 1 := by omega
  have hn3 : (3*n)%2 = 1 := by omega
  rw [half_nat_real _ hn9, Real.Gamma_nat_eq_factorial] at h9
  rw [half_nat_real _ hn3, Real.Gamma_nat_eq_factorial] at h3
  have hs : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
  have hgn9 : Real.Gamma ((9*(n:ℝ))/2+1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hgn3 : Real.Gamma ((3*(n:ℝ))/2+1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hf (k : ℕ) : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hp2 (k : ℕ) : (2:ℝ)^k ≠ 0 := pow_ne_zero _ (by norm_num)
  unfold aa
  have hgam (k : ℕ) : Real.Gamma ((k:ℝ)*(n:ℝ)+1) = (k*n).factorial := by
    rw [← Nat.cast_mul, Real.Gamma_nat_eq_factorial]
  have g9 := hgam 9
  have g2 := hgam 2
  have g4 := hgam 4
  have g3 := hgam 3
  norm_num only [Nat.cast_ofNat] at g9 g2 g4 g3
  rw [g9, g2, g4, g3, Real.Gamma_nat_eq_factorial]
  push_cast at h9 h3
  have he : (2:ℝ)^(9*n) = (2:ℝ)^(6*n) * (2:ℝ)^(3*n) := by
    rw [← pow_add]
    congr 1
    omega
  rw [he] at h9
  have hg9 : Real.Gamma (9/2*(n:ℝ)+1) = Real.Gamma ((9*(n:ℝ))/2+1) := by congr 1; ring
  have hg3 : Real.Gamma (3/2*(n:ℝ)+1) = Real.Gamma ((3*(n:ℝ))/2+1) := by congr 1; ring
  rw [hg9,hg3]
  apply (div_eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero hgn9 (hf (4*n))) (hf (3*n))) (hf n))
    (mul_ne_zero (mul_ne_zero (hf (3*n/2)) (hf (4*n))) (hf n))).mpr
  apply mul_right_cancel₀ hs
  linear_combination
    -(Real.Gamma ((3*(n:ℝ))/2+1) * ((2*n).factorial:ℝ) * (4*n).factorial * n.factorial * (3*n/2).factorial) * h9 +
    ((9*n/2).factorial:ℝ) * ((2*n).factorial:ℝ) * (4*n).factorial * n.factorial *
      Real.Gamma ((9*(n:ℝ))/2+1) * (2:ℝ)^(6*n) * h3


lemma block_pos (p N : ℕ) : 0 < block p N := by
  apply Finset.prod_pos
  exact fun k hk => inds_pos hk

lemma fac_cast_ne (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by
  exact_mod_cast n.factorial_ne_zero

lemma block_cast_ne (p N : ℕ) : (block p N : ℝ) ≠ 0 := by
  exact_mod_cast (block_pos p N).ne'

lemma factorial_scaled_strip {p : ℕ} (hp : 0 < p) (m k : ℕ) :
    ((k*m*p).factorial : ℝ) = ((p:ℝ)^m)^k * (k*m).factorial * block p (k*m*p) := by
  rw [factorial_mul_strip hp (k*m)]
  push_cast
  rw [Nat.mul_comm k m, pow_mul]

lemma aa_even_transfer {p : ℕ} (hp : 0 < p) (m : ℕ) :
    aa (2*m*p) *
      ((block p (9*m*p) : ℝ) * block p (8*m*p) * block p (6*m*p) * block p (2*m*p)) =
    aa (2*m) * ((block p (18*m*p) : ℝ) * block p (4*m*p) * block p (3*m*p)) := by
  rw [Nat.mul_assoc 2 m p, aa_even (m*p), aa_even m]
  simp only [← Nat.mul_assoc]
  rw [factorial_scaled_strip hp m 18, factorial_scaled_strip hp m 4,
    factorial_scaled_strip hp m 3, factorial_scaled_strip hp m 9,
    factorial_scaled_strip hp m 8, factorial_scaled_strip hp m 6, factorial_scaled_strip hp m 2]
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq : (p:ℝ)^m ≠ 0 := pow_ne_zero _ hp0
  field_simp [-block_cast, fac_cast_ne, block_cast_ne, hq]
  <;> ring_nf
  all_goals field_simp [block_cast_ne]
  apply (div_eq_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero (block_cast_ne _ _) (block_cast_ne _ _))
    (block_cast_ne _ _)) (block_cast_ne _ _))).mpr
  ring

lemma two_power_step {p : ℕ} (hp : p % 2 = 1) (m : ℕ) :
    (2:ℝ)^(6*m*p) = (2:ℝ)^(6*m) * (16:ℝ)^(3*m*(p/2)) := by
  rw [show (16:ℝ) = 2^4 by norm_num, ← pow_mul, ← pow_add]
  congr 1
  have hp' : p = 2*(p/2)+1 := by omega
  conv_lhs => rw [hp']
  ring

lemma aa_odd_transfer {p : ℕ} (hp : 0 < p) (hpodd : p % 2 = 1) (m : ℕ) (hm : m % 2 = 1) :
    aa (m*p) * ((block p (3*m*p/2+1) : ℝ) * block p (4*m*p) * block p (m*p)) =
      aa m * ((16:ℝ)^(3*m*(p/2)) * block p (9*m*p/2+1) * block p (2*m*p)) := by
  have hmp : (m*p)%2 = 1 := by simp [Nat.mul_mod, hm, hpodd]
  rw [aa_odd (m*p) hmp, aa_odd m hm]
  simp only [← Nat.mul_assoc]
  rw [factorial_half_strip hp (9*m), factorial_half_strip hp (3*m),
    factorial_scaled_strip hp m 2, factorial_scaled_strip hp m 4,
    factorial_mul_strip hp m]
  push_cast
  have hd : 9*m/2 = 3*m/2 + 3*m := by omega
  have hpow : (p:ℝ)^(9*m/2) = (p:ℝ)^(3*m/2) * ((p:ℝ)^m)^3 := by
    rw [hd, pow_add, Nat.mul_comm 3 m, pow_mul]
  rw [hpow, two_power_step hpodd m]
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq : (p:ℝ)^m ≠ 0 := pow_ne_zero _ hp0
  have hu : (p:ℝ)^(3*m/2) ≠ 0 := pow_ne_zero _ hp0
  field_simp [-block_cast, fac_cast_ne, block_cast_ne, hq, hu]
  <;> ring_nf
  all_goals field_simp [block_cast_ne]
  apply (div_eq_iff (mul_ne_zero (mul_ne_zero (block_cast_ne _ _) (block_cast_ne _ _))
    (block_cast_ne _ _))).mpr
  ring


lemma even_blocks_cube {p r : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hr : 0 < r)
    (m c : ℕ) (hmc : m*p = c*p^r) :
    ((block p (18*m*p) : ZMod ((p^r)^3)) * block p (4*m*p) * block p (3*m*p)) =
      (block p (9*m*p) : ZMod ((p^r)^3)) * block p (8*m*p) * block p (6*m*p) * block p (2*m*p) := by
  let R := ZMod ((p^r)^3)
  let z : R := (block p (p^r) : R)^c
  have full (k : ℕ) : (block p (k*m*p) : R) = z^k := by
    have heq : k*m*p = (c*k)*p^r := by
      calc
        _ = k*(m*p) := by ring
        _ = k*(c*p^r) := by rw [hmc]
        _ = _ := by ring
    rw [heq, block_multiple_cube hp h5 hr, pow_mul]
  rw [full 18, full 4, full 3, full 9, full 8, full 6, full 2]
  ring

lemma even_int_step {p r : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hr : 0 < r)
    (m c : ℕ) (hmc : m*p = c*p^r) (A B : ℤ)
    (hA : (A:ℝ) = aa (2*m*p)) (hB : (B:ℝ) = aa (2*m)) :
    (A : ZMod ((p^r)^3)) = (B : ZMod ((p^r)^3)) := by
  have ht := aa_even_transfer hp.pos m
  rw [← hA, ← hB] at ht
  have hi : A * ((block p (9*m*p) : ℤ) * block p (8*m*p) * block p (6*m*p) * block p (2*m*p)) =
      B * ((block p (18*m*p) : ℤ) * block p (4*m*p) * block p (3*m*p)) := by
    exact_mod_cast ht
  have hz : (A : ZMod ((p^r)^3)) *
      ((block p (9*m*p) : ZMod ((p^r)^3)) * block p (8*m*p) * block p (6*m*p) * block p (2*m*p)) =
      (B : ZMod ((p^r)^3)) * ((block p (18*m*p) : ZMod ((p^r)^3)) * block p (4*m*p) * block p (3*m*p)) := by
    have hh := congrArg (fun z : ℤ => (z : ZMod ((p^r)^3))) hi
    push_cast at hh
    exact hh
  rw [even_blocks_cube hp h5 hr m c hmc] at hz
  exact (((block_unit_cube hp r _).mul (block_unit_cube hp r _)).mul
    (block_unit_cube hp r _)).mul (block_unit_cube hp r _) |>.mul_right_cancel hz

lemma odd_int_step {p r : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hr : 0 < r)
    (m c : ℕ) (hm : m%2 = 1) (hmc : m*p = c*p^r) (A B : ℤ)
    (hA : (A:ℝ) = aa (m*p)) (hB : (B:ℝ) = aa m) :
    (A : ZMod ((p^r)^3)) = (B : ZMod ((p^r)^3)) := by
  have hpodd : p%2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have ht := aa_odd_transfer hp.pos hpodd m hm
  rw [← hA, ← hB] at ht
  have hi : A * ((block p (3*m*p/2+1) : ℤ) * block p (4*m*p) * block p (m*p)) =
      B * ((16:ℤ)^(3*m*(p/2)) * block p (9*m*p/2+1) * block p (2*m*p)) := by
    exact_mod_cast ht
  have hz : (A : ZMod ((p^r)^3)) *
      ((block p (3*m*p/2+1) : ZMod ((p^r)^3)) * block p (4*m*p) * block p (m*p)) =
      (B : ZMod ((p^r)^3)) * ((16:ZMod ((p^r)^3))^(3*m*(p/2)) * block p (9*m*p/2+1) * block p (2*m*p)) := by
    have hh := congrArg (fun z : ℤ => (z : ZMod ((p^r)^3))) hi
    push_cast at hh
    exact hh
  rw [odd_blocks_cube hp h5 hr m c hm hmc] at hz
  exact ((block_unit_cube hp r _).mul (block_unit_cube hp r _)).mul
    (block_unit_cube hp r _) |>.mul_right_cancel hz

lemma aa_supercongruence
    (h_int : ∀ m : ℕ, aa m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (_hp : Nat.Prime p) (_h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (_hn : n > 0) (_hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] := by
  intro p hp h5 n r hn hr
  let A : ℤ := Classical.choose (h_int (n*p^r))
  let B : ℤ := Classical.choose (h_int (n*p^(r-1)))
  have hA : (A:ℝ) = aa (n*p^r) := Classical.choose_spec (h_int (n*p^r))
  have hB : (B:ℝ) = aa (n*p^(r-1)) := Classical.choose_spec (h_int (n*p^(r-1)))
  have hpow : p^(r-1)*p = p^r := by
    rw [← pow_succ]
    congr 1
    omega
  have hz : (A : ZMod ((p^r)^3)) = (B : ZMod ((p^r)^3)) := by
    by_cases hn2 : n%2 = 0
    · have he : n = 2*(n/2) := by omega
      let m := (n/2)*p^(r-1)
      have hmc : m*p = (n/2)*p^r := by
        dsimp [m]
        rw [Nat.mul_assoc, hpow]
      have hma : 2*m*p = n*p^r := by
        rw [Nat.mul_assoc 2 m p, hmc, ← Nat.mul_assoc, ← he]
      have hmb : 2*m = n*p^(r-1) := by
        dsimp [m]
        rw [← Nat.mul_assoc, ← he]
      apply even_int_step hp h5 hr m (n/2) hmc A B
      · rwa [hma]
      · rwa [hmb]
    · have hnodd : n%2 = 1 := by omega
      have hpodd : p%2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
      let m := n*p^(r-1)
      have hm : m%2 = 1 := by simp [m, Nat.mul_mod, Nat.pow_mod, hnodd, hpodd]
      have hmc : m*p = n*p^r := by
        dsimp [m]
        rw [Nat.mul_assoc, hpow]
      apply odd_int_step hp h5 hr m n hm hmc A B
      · rwa [hmc]
      · exact hB
  have hc := (ZMod.intCast_eq_intCast_iff A B ((p^r)^3)).mp hz
  have he : (((p^r)^3 : ℕ) : ℤ) = (p:ℤ)^(3*r) := by
    push_cast
    rw [← pow_mul]
    congr 1
    omega
  rwa [he] at hc

end Super

/--
Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and all positive integers n and r.
Note: This conjecture requires that a(n) is an integer for all n, which is only conjectural.
We assume integrality for the purpose of stating the congruence.
-/
theorem oeis_364173_conjecture_0
    (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] :=
by
  exact Super.aa_supercongruence h_int

theorem oeis_364173_conjecture_0.disproof : ¬ (type_of% @oeis_364173_conjecture_0) := sorry
