import Submission.Jacob

open Finset

namespace JacobRef

/-- Product of integers in `[1, p*n]` that are NOT divisible by `p`. -/
def P (p n : ℕ) : ℕ := ∏ k ∈ (Finset.Icc 1 (p * n)).filter (fun k => ¬ p ∣ k), k

/-- `∏ k ∈ Icc 1 m, k = m!`. -/
lemma prod_Icc_id (m : ℕ) : (∏ k ∈ Finset.Icc 1 m, k) = Nat.factorial m := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ]
    ring

/-- The multiples of `p` in `[1, p*n]` are exactly `p*1, …, p*n`. -/
lemma filter_dvd_eq_image (p n : ℕ) (hp : 0 < p) :
    (Finset.Icc 1 (p * n)).filter (fun k => p ∣ k)
      = (Finset.Icc 1 n).image (fun j => p * j) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hk1, hk2⟩, j, rfl⟩
    refine ⟨j, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos j with h | h
      · simp [h] at hk1
      · exact h
    · exact Nat.le_of_mul_le_mul_left hk2 hp
  · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
    exact ⟨⟨by have := Nat.mul_pos hp (show 0 < j by omega); omega, Nat.mul_le_mul_left p hj2⟩, ⟨j, rfl⟩⟩

/-- Factorization: `(p*n)! = p^n * n! * P p n`. -/
lemma factorial_eq (p n : ℕ) (hp : 0 < p) :
    Nat.factorial (p * n) = p ^ n * Nat.factorial n * P p n := by
  have hsplit := Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (p * n))
      (fun k => p ∣ k) (fun k => k)
  rw [prod_Icc_id] at hsplit
  -- the multiples part
  have hmul : (∏ k ∈ (Finset.Icc 1 (p * n)).filter (fun k => p ∣ k), k) = p ^ n * Nat.factorial n := by
    rw [filter_dvd_eq_image p n hp,
        Finset.prod_image (by
          intro x _ y _ h; exact Nat.eq_of_mul_eq_mul_left hp h)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, prod_Icc_id]
    congr 1
    · rw [Nat.card_Icc]; congr 1
  -- combine
  rw [hmul] at hsplit
  rw [← hsplit]
  simp only [P]

/-- The exact block-product identity (★):
`C(pa,pb) * P(b) * P(a-b) = C(a,b) * P(a)` in ℕ. -/
lemma choose_prod_identity (p a b : ℕ) (hp : 0 < p) (hba : b ≤ a) :
    Nat.choose (p * a) (p * b) * P p b * P p (a - b) = Nat.choose a b * P p a := by
  have hpba : p * b ≤ p * a := Nat.mul_le_mul_left p hba
  have hsub : p * a - p * b = p * (a - b) := by rw [Nat.mul_sub]
  have hI := Nat.choose_mul_factorial_mul_factorial hpba
  rw [hsub, factorial_eq p a hp, factorial_eq p b hp, factorial_eq p (a - b) hp] at hI
  have hII := Nat.choose_mul_factorial_mul_factorial hba
  have hpow : p ^ b * p ^ (a - b) = p ^ a := by
    rw [← pow_add]; congr 1; omega
  rw [← hII, ← hpow] at hI
  have hcancel : 0 < p ^ b * p ^ (a - b) * (Nat.factorial b * Nat.factorial (a - b)) := by
    positivity
  apply Nat.eq_of_mul_eq_mul_right hcancel
  rw [show (Nat.choose (p * a) (p * b) * P p b * P p (a - b))
          * (p ^ b * p ^ (a - b) * (Nat.factorial b * Nat.factorial (a - b)))
        = Nat.choose (p * a) (p * b) * (p ^ b * Nat.factorial b * P p b)
          * (p ^ (a - b) * Nat.factorial (a - b) * P p (a - b)) from by ring,
      show (Nat.choose a b * P p a)
          * (p ^ b * p ^ (a - b) * (Nat.factorial b * Nat.factorial (a - b)))
        = p ^ b * p ^ (a - b) * (Nat.choose a b * Nat.factorial b * Nat.factorial (a - b))
          * P p a from by ring]
  exact hI

/-! ### General ring helpers for the block expansion -/

/-- Truncated product expansion when `X^3 = 0`:
`∏(1 + X u i) = 1 + X (∑ u) + X² (∑_{j<i} u i u j)`. -/
lemma prod_one_add_nilp {R : Type*} [CommRing R] (X : R) (hX : X ^ 3 = 0)
    (s : Finset ℕ) (u : ℕ → R) :
    ∏ i ∈ s, (1 + X * u i)
      = 1 + X * (∑ i ∈ s, u i)
        + X ^ 2 * (∑ i ∈ s, ∑ j ∈ s with j < i, u i * u j) := by
  induction s using Finset.induction_on_max with
  | h0 => simp
  | step a s ha ih =>
    have has : a ∉ s := fun h => (lt_irrefl a (ha a h))
    have hfilt_a : s.filter (fun j => j < a) = s := by
      apply Finset.filter_true_of_mem; intro x hx; exact ha x hx
    have htri : (∑ i ∈ insert a s, ∑ j ∈ (insert a s) with j < i, u i * u j)
        = (∑ i ∈ s, ∑ j ∈ s with j < i, u i * u j) + u a * (∑ j ∈ s, u j) := by
      rw [Finset.sum_insert has]
      have e1 : (∑ j ∈ (insert a s) with j < a, u a * u j) = u a * (∑ j ∈ s, u j) := by
        rw [Finset.filter_insert, if_neg (lt_irrefl a), hfilt_a, ← Finset.mul_sum]
      have e2 : (∑ i ∈ s, ∑ j ∈ (insert a s) with j < i, u i * u j)
          = (∑ i ∈ s, ∑ j ∈ s with j < i, u i * u j) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [Finset.filter_insert, if_neg (not_lt.mpr (le_of_lt (ha i hi)))]
      rw [e1, e2, add_comm]
    rw [Finset.prod_insert has, Finset.sum_insert has, ih, htri]
    linear_combination (u a * (∑ i ∈ s, ∑ j ∈ s with j < i, u i * u j)) * hX

/-- Newton-type identity: `2·∑_{j<i} u i u j = (∑ u)² - ∑ u²`. -/
lemma two_mul_tri {R : Type*} [CommRing R] (s : Finset ℕ) (u : ℕ → R) :
    2 * (∑ i ∈ s, ∑ j ∈ s with j < i, u i * u j)
      = (∑ i ∈ s, u i) ^ 2 - ∑ i ∈ s, (u i) ^ 2 := by
  induction s using Finset.induction_on_max with
  | h0 => simp
  | step a s ha ih =>
    have has : a ∉ s := fun h => (lt_irrefl a (ha a h))
    have hfilt_a : s.filter (fun j => j < a) = s := by
      apply Finset.filter_true_of_mem; intro x hx; exact ha x hx
    have htri : (∑ i ∈ insert a s, ∑ j ∈ (insert a s) with j < i, u i * u j)
        = (∑ i ∈ s, ∑ j ∈ s with j < i, u i * u j) + u a * (∑ j ∈ s, u j) := by
      rw [Finset.sum_insert has]
      have e1 : (∑ j ∈ (insert a s) with j < a, u a * u j) = u a * (∑ j ∈ s, u j) := by
        rw [Finset.filter_insert, if_neg (lt_irrefl a), hfilt_a, ← Finset.mul_sum]
      have e2 : (∑ i ∈ s, ∑ j ∈ (insert a s) with j < i, u i * u j)
          = (∑ i ∈ s, ∑ j ∈ s with j < i, u i * u j) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [Finset.filter_insert, if_neg (not_lt.mpr (le_of_lt (ha i hi)))]
      rw [e1, e2, add_comm]
    rw [htri, Finset.sum_insert has, Finset.sum_insert has]
    linear_combination ih

/-- A ring hom `ZMod n → ZMod m` sends the inverse of a unit to the inverse of its image. -/
lemma castHom_inv {m n : ℕ} [NeZero m] (h : m ∣ n) (a : ZMod n) (ha : IsUnit a) :
    ZMod.castHom h (ZMod m) a⁻¹ = (ZMod.castHom h (ZMod m) a)⁻¹ := by
  have hb : IsUnit (ZMod.castHom h (ZMod m) a) := ha.map _
  have h1 : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit a ha
  have h2 : (ZMod.castHom h (ZMod m) a) * (ZMod.castHom h (ZMod m) a⁻¹) = 1 := by
    rw [← map_mul, h1, map_one]
  have h3 := ZMod.mul_inv_of_unit _ hb
  exact hb.mul_right_inj.mp (h2.trans h3.symm)

/-! ### Kernel lemmas relating `ZMod (p^3)` to `ZMod (p^2)` and `ZMod p` -/

lemma kerA (p : ℕ) [Fact p.Prime] (x : ZMod (p ^ 3))
    (h : ZMod.castHom (show (p ^ 2 : ℕ) ∣ p ^ 3 from ⟨p, by ring⟩) (ZMod (p ^ 2)) x = 0) :
    (p : ZMod (p ^ 3)) * x = 0 := by
  haveI : NeZero (p ^ 3) := ⟨pow_ne_zero 3 (Fact.out (p := p.Prime)).pos.ne'⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (Fact.out (p := p.Prime)).pos.ne'⟩
  have hp3 : (p : ZMod (p ^ 3)) ^ 3 = 0 := by rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff] at h
  obtain ⟨t, ht⟩ := h
  have hx : x = ((p ^ 2 * t : ℕ) : ZMod (p ^ 3)) := by
    rw [← ZMod.natCast_zmod_val x, ht]
  rw [hx]
  push_cast
  linear_combination (t : ZMod (p ^ 3)) * hp3

lemma kerB (p : ℕ) [Fact p.Prime] (x : ZMod (p ^ 3))
    (h : ZMod.castHom (show (p : ℕ) ∣ p ^ 3 from ⟨p ^ 2, by ring⟩) (ZMod p) x = 0) :
    (p : ZMod (p ^ 3)) ^ 2 * x = 0 := by
  haveI : NeZero (p ^ 3) := ⟨pow_ne_zero 3 (Fact.out (p := p.Prime)).pos.ne'⟩
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  have hp3 : (p : ZMod (p ^ 3)) ^ 3 = 0 := by rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff] at h
  obtain ⟨t, ht⟩ := h
  have hx : x = ((p * t : ℕ) : ZMod (p ^ 3)) := by
    rw [← ZMod.natCast_zmod_val x, ht]
  rw [hx]
  push_cast
  linear_combination (t : ZMod (p ^ 3)) * hp3

/-- Recursion for `P`: the `(n+1)`-th product picks up one more block. -/
lemma P_succ (p n : ℕ) (hp : 0 < p) :
    P p (n + 1) = P p n * ∏ r ∈ Finset.Icc 1 (p - 1), (p * n + r) := by
  have hpm : p * (n + 1) = p * n + p := Nat.mul_succ p n
  have hIccIoc : ∀ m, Finset.Icc 1 m = Finset.Ioc 0 m := by
    intro m; ext x; rw [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have key : Finset.Ioc 0 (p * (n + 1))
      = Finset.Ioc 0 (p * n) ∪ Finset.Ioc (p * n) (p * (n + 1)) :=
    (Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (by omega)).symm
  have hdisj : Disjoint ((Finset.Ioc 0 (p * n)).filter (fun k => ¬ p ∣ k))
      ((Finset.Ioc (p * n) (p * (n + 1))).filter (fun k => ¬ p ∣ k)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    rw [Finset.mem_filter, Finset.mem_Ioc] at hx hy
    omega
  have e1 : P p (n + 1)
      = ∏ k ∈ ((Finset.Ioc 0 (p * n)).filter (fun k => ¬ p ∣ k))
          ∪ ((Finset.Ioc (p * n) (p * (n + 1))).filter (fun k => ¬ p ∣ k)), k := by
    rw [P, hIccIoc, key, Finset.filter_union]
  rw [e1, Finset.prod_union hdisj]
  have hf1 : (∏ k ∈ (Finset.Ioc 0 (p * n)).filter (fun k => ¬ p ∣ k), k) = P p n := by
    simp only [P, hIccIoc]
  have hf2 : (∏ k ∈ (Finset.Ioc (p * n) (p * (n + 1))).filter (fun k => ¬ p ∣ k), k)
      = ∏ r ∈ Finset.Icc 1 (p - 1), (p * n + r) := by
    rw [show (Finset.Ioc (p * n) (p * (n + 1))).filter (fun k => ¬ p ∣ k)
          = (Finset.Icc 1 (p - 1)).image (fun r => p * n + r) from ?_]
    · rw [Finset.prod_image (by intro x _ y _ h; dsimp only at h; omega)]
    · ext k
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hk1, hk2⟩, hnd⟩
        have hkne : k ≠ p * n + p := fun h => hnd (h ▸ ⟨n + 1, by ring⟩)
        exact ⟨k - p * n, ⟨by omega, by omega⟩, by omega⟩
      · rintro ⟨r, ⟨hr1, hr2⟩, rfl⟩
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        intro h
        have hr : p ∣ r := (Nat.dvd_add_right ⟨n, rfl⟩).mp h
        have := Nat.le_of_dvd (by omega) hr
        omega
  rw [hf1, hf2]

/-! ### The block congruence `B_j ≡ (p-1)! (mod p^3)` -/

open Wolst in
/-- Block congruence: `∏_{r=1}^{p-1}(p*n + r) ≡ (p-1)! (mod p^3)`. -/
lemma block_congr (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (n : ℕ) :
    ((∏ r ∈ Finset.Icc 1 (p - 1), (p * n + r) : ℕ) : ZMod (p ^ 3))
      = ((Nat.factorial (p - 1) : ℕ) : ZMod (p ^ 3)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.pos.ne'⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  set s := Finset.Icc 1 (p - 1) with hs
  -- coprimality / units
  have hcop : ∀ r ∈ s, Nat.Coprime r p := by
    intro r hr; rw [hs, Finset.mem_Icc] at hr
    have hnd : ¬ p ∣ r := fun h => by have := Nat.le_of_dvd (by omega) h; omega
    exact (hp.coprime_iff_not_dvd.mpr hnd).symm
  have hunit : ∀ r ∈ s, IsUnit ((r : ℕ) : ZMod (p ^ 3)) := fun r hr => by
    rw [ZMod.isUnit_iff_coprime]; exact Nat.Coprime.pow_right 3 (hcop r hr)
  have hunit2 : ∀ r ∈ s, IsUnit ((r : ℕ) : ZMod (p ^ 2)) := fun r hr => by
    rw [ZMod.isUnit_iff_coprime]; exact Nat.Coprime.pow_right 2 (hcop r hr)
  set X : ZMod (p ^ 3) := ((p * n : ℕ) : ZMod (p ^ 3)) with hX
  set u : ℕ → ZMod (p ^ 3) := fun r => ((r : ℕ) : ZMod (p ^ 3))⁻¹ with hu
  -- X^3 = 0
  have hX3 : X ^ 3 = 0 := by
    rw [hX, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]; exact ⟨n ^ 3, by ring⟩
  -- the factorization of each factor
  have hstep : ∀ r ∈ s, ((p * n + r : ℕ) : ZMod (p ^ 3)) = ((r : ℕ) : ZMod (p ^ 3)) * (1 + X * u r) := by
    intro r hr
    have hru : ((r : ℕ) : ZMod (p ^ 3)) * ((r : ℕ) : ZMod (p ^ 3))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ (hunit r hr)
    have hexp : ((r : ℕ) : ZMod (p ^ 3)) * (1 + X * u r)
        = ((r : ℕ) : ZMod (p ^ 3)) + X * (((r : ℕ) : ZMod (p ^ 3)) * ((r : ℕ) : ZMod (p ^ 3))⁻¹) := by
      simp only [hu]; ring
    rw [hexp, hru, mul_one, Nat.cast_add, ← hX]; ring
  -- product = (p-1)! * ∏ (1 + X u r)
  have hprodcast : ((∏ r ∈ s, (p * n + r) : ℕ) : ZMod (p ^ 3))
      = ((Nat.factorial (p - 1) : ℕ) : ZMod (p ^ 3)) * ∏ r ∈ s, (1 + X * u r) := by
    rw [Nat.cast_prod, Finset.prod_congr rfl hstep, Finset.prod_mul_distrib]
    congr 1
    rw [← Nat.cast_prod, prod_Icc_id]
  -- expand ∏ (1 + X u r)
  rw [hprodcast, prod_one_add_nilp X hX3 s u]
  -- X * ∑ u = 0
  have hXsum : X * (∑ i ∈ s, u i) = 0 := by
    have hψ : (ZMod.castHom (show (p ^ 2 : ℕ) ∣ p ^ 3 from ⟨p, by ring⟩) (ZMod (p ^ 2)))
        (∑ i ∈ s, u i) = 0 := by
      rw [map_sum]
      have hcong : ∀ r ∈ s, (ZMod.castHom (show (p ^ 2 : ℕ) ∣ p ^ 3 from ⟨p, by ring⟩)
          (ZMod (p ^ 2))) (u r) = ((r : ℕ) : ZMod (p ^ 2))⁻¹ := by
        intro r hr; rw [hu]; simp only
        rw [castHom_inv _ _ (hunit r hr), map_natCast]
      rw [Finset.sum_congr rfl hcong]
      exact Wolst.sum_inv p hp5
    have hp_sum : (p : ZMod (p ^ 3)) * (∑ i ∈ s, u i) = 0 := kerA p _ hψ
    rw [hX]
    have hpn : ((p * n : ℕ) : ZMod (p ^ 3)) = (n : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) := by
      push_cast; ring
    rw [hpn, mul_assoc, hp_sum, mul_zero]
  -- X^2 * tri = 0
  have hXtri : X ^ 2 * (∑ i ∈ s, ∑ j ∈ s with j < i, u i * u j) = 0 := by
    -- reduce inverse sum mod p
    have hsum_inv_p : (∑ r ∈ s, ((r : ℕ) : ZMod p)⁻¹) = 0 := by
      have hw := Wolst.sum_inv p hp5
      have hc := congrArg (ZMod.castHom (show (p : ℕ) ∣ p ^ 2 from ⟨p, by ring⟩) (ZMod p)) hw
      rw [map_sum, map_zero] at hc
      rw [← hc]
      refine Finset.sum_congr rfl (fun r hr => ?_)
      rw [castHom_inv _ _ (hunit2 r hr), map_natCast]
    have htri_p : (∑ i ∈ s, ∑ j ∈ s with j < i, ((i : ℕ) : ZMod p)⁻¹ * ((j : ℕ) : ZMod p)⁻¹) = 0 := by
      have h2 := two_mul_tri s (fun r => ((r : ℕ) : ZMod p)⁻¹)
      simp only at h2
      rw [hsum_inv_p] at h2
      have hsq := Wolst.sum_inv_sq p hp5
      rw [hsq] at h2
      -- h2 : 2 * tri_p = 0^2 - 0
      have h2unit : IsUnit (2 : ZMod p) := by
        have hcast : ((2 : ℕ) : ZMod p) = (2 : ZMod p) := by norm_num
        rw [← hcast, ZMod.isUnit_iff_coprime]
        have hnd : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
        exact (hp.coprime_iff_not_dvd.mpr hnd).symm
      have : (2 : ZMod p) * (∑ i ∈ s, ∑ j ∈ s with j < i, ((i : ℕ) : ZMod p)⁻¹ * ((j : ℕ) : ZMod p)⁻¹) = 0 := by
        rw [h2]; ring
      exact (h2unit.mul_right_eq_zero).mp this
    have hφ : (ZMod.castHom (show (p : ℕ) ∣ p ^ 3 from ⟨p ^ 2, by ring⟩) (ZMod p))
        (∑ i ∈ s, ∑ j ∈ s with j < i, u i * u j) = 0 := by
      rw [map_sum]
      have hcong : ∀ i ∈ s, (ZMod.castHom (show (p : ℕ) ∣ p ^ 3 from ⟨p ^ 2, by ring⟩) (ZMod p))
          (∑ j ∈ s with j < i, u i * u j)
          = ∑ j ∈ s with j < i, ((i : ℕ) : ZMod p)⁻¹ * ((j : ℕ) : ZMod p)⁻¹ := by
        intro i hi
        rw [map_sum]
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have hj' : j ∈ s := Finset.mem_of_mem_filter j hj
        rw [hu]; simp only
        rw [map_mul, castHom_inv _ _ (hunit i hi), castHom_inv _ _ (hunit j hj'),
          map_natCast, map_natCast]
      rw [Finset.sum_congr rfl hcong]
      exact htri_p
    have hp2_tri : (p : ZMod (p ^ 3)) ^ 2 * (∑ i ∈ s, ∑ j ∈ s with j < i, u i * u j) = 0 :=
      kerB p _ hφ
    rw [hX]
    have : ((p * n : ℕ) : ZMod (p ^ 3)) ^ 2 = (n : ZMod (p ^ 3)) ^ 2 * (p : ZMod (p ^ 3)) ^ 2 := by
      push_cast; ring
    rw [this, mul_assoc, hp2_tri, mul_zero]
  rw [hXsum, hXtri]
  ring

/-- `P p n ≡ ((p-1)!)^n (mod p^3)`. -/
lemma P_cast (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (n : ℕ) :
    ((P p n : ℕ) : ZMod (p ^ 3)) = ((Nat.factorial (p - 1) : ℕ) : ZMod (p ^ 3)) ^ n := by
  induction n with
  | zero => simp [P]
  | succ m ih =>
    rw [P_succ p m hp.pos, Nat.cast_mul, ih, block_congr p hp hp5 m]; ring

/-! ### Combining the pieces -/

/-- `P p n` is coprime to `p`. -/
lemma P_coprime (p : ℕ) (hp : p.Prime) (n : ℕ) : Nat.Coprime (P p n) p := by
  rw [P]
  apply Nat.Coprime.prod_left
  intro k hk
  rw [Finset.mem_filter] at hk
  exact (hp.coprime_iff_not_dvd.mpr hk.2).symm

/-- `p^3 ∣ P a - P b · P (a-b)` (the base block congruence, integer form). -/
lemma P_diff_dvd (p a b : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hba : b ≤ a) :
    (p : ℤ) ^ 3 ∣ ((P p a : ℤ) - (P p b : ℤ) * (P p (a - b) : ℤ)) := by
  set D : ℤ := (P p a : ℤ) - (P p b : ℤ) * (P p (a - b) : ℤ) with hD
  have hz : ((D : ℤ) : ZMod (p ^ 3)) = 0 := by
    rw [hD]; push_cast
    rw [P_cast p hp hp5 a, P_cast p hp hp5 b, P_cast p hp hp5 (a - b),
      ← pow_add, show b + (a - b) = a from by omega, sub_self]
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd D (p ^ 3)).mp hz
  rwa [show ((p ^ 3 : ℕ) : ℤ) = (p : ℤ) ^ 3 from by push_cast; ring] at hd

/-- **Refined Jacobsthal congruence (choose-refinement).**
`p^(3 + v_p(C(a,b))) ∣ C(pa,pb) - C(a,b)`. -/
theorem jacobsthal_choose_refined (p a b : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hba : b < a) :
    (p : ℤ) ^ (3 + padicValNat p (Nat.choose a b))
      ∣ ((Nat.choose (p * a) (p * b) : ℤ) - Nat.choose a b) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set w := padicValNat p (Nat.choose a b) with hw_def
  have hident : (Nat.choose (p * a) (p * b) : ℤ) * (P p b : ℤ) * (P p (a - b) : ℤ)
      = (Nat.choose a b : ℤ) * (P p a : ℤ) := by
    exact_mod_cast choose_prod_identity p a b hp.pos (le_of_lt hba)
  have hdiamond : ((Nat.choose (p * a) (p * b) : ℤ) - Nat.choose a b)
        * ((P p b : ℤ) * (P p (a - b) : ℤ))
      = (Nat.choose a b : ℤ) * ((P p a : ℤ) - (P p b : ℤ) * (P p (a - b) : ℤ)) := by
    linear_combination hident
  have hw : (p : ℤ) ^ w ∣ (Nat.choose a b : ℤ) := by
    have h := pow_padicValNat_dvd (p := p) (n := Nat.choose a b)
    exact_mod_cast h
  have h3 : (p : ℤ) ^ 3 ∣ ((P p a : ℤ) - (P p b : ℤ) * (P p (a - b) : ℤ)) :=
    P_diff_dvd p a b hp hp5 (le_of_lt hba)
  have hRHS : (p : ℤ) ^ (3 + w)
      ∣ (Nat.choose a b : ℤ) * ((P p a : ℤ) - (P p b : ℤ) * (P p (a - b) : ℤ)) := by
    have h := mul_dvd_mul hw h3
    rw [← pow_add] at h
    rwa [show 3 + w = w + 3 from by omega]
  have hLHS : (p : ℤ) ^ (3 + w)
      ∣ ((Nat.choose (p * a) (p * b) : ℤ) - Nat.choose a b)
          * ((P p b : ℤ) * (P p (a - b) : ℤ)) := by
    rw [hdiamond]; exact hRHS
  have hcop : IsCoprime ((p : ℤ) ^ (3 + w)) ((P p b : ℤ) * (P p (a - b) : ℤ)) := by
    apply IsCoprime.pow_left
    rw [show ((P p b : ℤ) * (P p (a - b) : ℤ)) = (((P p b * P p (a - b) : ℕ)) : ℤ) from by
      push_cast; ring]
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.mul_right (P_coprime p hp b).symm (P_coprime p hp (a - b)).symm
  exact hcop.dvd_of_dvd_mul_right hLHS

end JacobRef

#print axioms JacobRef.jacobsthal_choose_refined
#print axioms JacobRef.block_congr
#print axioms JacobRef.choose_prod_identity
#print axioms JacobRef.factorial_eq
