import FormalConjectures.Util.ProblemImports

open Nat Int Finset BigOperators

namespace Harmonic

variable (p : ℕ) [Fact p.Prime]

lemma zmod_sum_pow {j : ℕ} (hj : 1 ≤ j) (hjp : ¬ (p - 1) ∣ j) :
    ∑ x : ZMod p, x ^ j = 0 := by
  classical
  have hp : p.Prime := Fact.out
  set m := j % (p - 1) with hm
  have hp2 : 2 ≤ p := hp.two_le
  have hmlt : m < p - 1 := Nat.mod_lt _ (by omega)
  have hm0 : m ≠ 0 := fun h => hjp (Nat.dvd_of_mod_eq_zero h)
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hpow : ∀ x : ZMod p, x ^ j = x ^ m := by
    intro x
    by_cases hx : x = 0
    · subst hx; rw [zero_pow (by omega), zero_pow hm0]
    · have hfer : x ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx
      conv_lhs => rw [← Nat.div_add_mod j (p - 1)]
      rw [pow_add, pow_mul, hfer, one_pow, one_mul, ← hm]
  simp_rw [hpow]
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) m (by rw [hcard]; exact hmlt)

/-- Sum over `ZMod p` equals sum over `range p` via the cast bijection. -/
lemma sum_zmod_eq_sum_range (f : ZMod p → ZMod p) :
    ∑ x : ZMod p, f x = ∑ i ∈ Finset.range p, f (i : ZMod p) := by
  classical
  refine Finset.sum_nbij' (fun x => x.val) (fun i => (i : ZMod p)) ?_ ?_ ?_ ?_ ?_
  · intro x _; simp only [Finset.mem_range]; exact ZMod.val_lt x
  · intro i _; exact Finset.mem_univ _
  · intro x _; simp only [ZMod.natCast_val, ZMod.cast_id]
  · intro i hi; simp only [Finset.mem_range] at hi; simp only [ZMod.val_natCast_of_lt hi]
  · intro x _; simp only [ZMod.natCast_val, ZMod.cast_id]

lemma sum_pow_Ico {j : ℕ} (hj : 1 ≤ j) (hjp : ¬ (p - 1) ∣ j) :
    ∑ i ∈ Finset.Ico 1 p, ((i : ZMod p)) ^ j = 0 := by
  have hp : p.Prime := Fact.out
  have h1p : 1 ≤ p := by have := hp.two_le; omega
  have hj0 : j ≠ 0 := Nat.one_le_iff_ne_zero.mp hj
  have key := zmod_sum_pow p hj hjp
  rw [sum_zmod_eq_sum_range p (fun x => x ^ j), Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive (fun i => ((i : ZMod p)) ^ j) (Nat.zero_le 1) h1p] at key
  rw [show Finset.Ico 0 1 = {0} from by decide] at key
  simp only [Finset.sum_singleton, Nat.cast_zero, zero_pow hj0, zero_add] at key
  exact key

/-- If reduction mod p of `Y : ZMod (p^2)` is zero, then `p * Y = 0`. -/
lemma p_mul_eq_zero_of_castHom {p : ℕ} [Fact p.Prime] (Y : ZMod (p^2))
    (hY : (ZMod.castHom (⟨p, sq p⟩ : p ∣ p^2) (ZMod p)) Y = 0) :
    (p : ZMod (p^2)) * Y = 0 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  have hval : (Y.val : ZMod p) = 0 := by
    rw [ZMod.natCast_val, ← ZMod.castHom_apply (R := ZMod p) Y]; exact hY
  have hdvd : p ∣ Y.val := (ZMod.natCast_eq_zero_iff _ _).mp hval
  obtain ⟨m, hm⟩ := hdvd
  have hY2 : Y = (p : ZMod (p^2)) * (m : ZMod (p^2)) := by
    have h0 : ((Y.val : ℕ) : ZMod (p^2)) = Y := by rw [ZMod.natCast_val, ZMod.cast_id]
    rw [← h0, hm]; push_cast; ring
  rw [hY2, ← mul_assoc, ← Nat.cast_mul, ← pow_two, ZMod.natCast_self, zero_mul]

/-- Inverse as a power in `ZMod p`. -/
lemma inv_eq_pow {x : ZMod p} (hx : x ≠ 0) : x⁻¹ = x ^ (p - 2) := by
  have hp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp.two_le
  have h1 : x ^ (p - 2) * x = 1 := by
    rw [← pow_succ, show p - 2 + 1 = p - 1 by omega, ZMod.pow_card_sub_one_eq_one hx]
  exact inv_eq_of_mul_eq_one_left h1

/-- The mod-p sum of squared inverses vanishes (`p ≥ 5`). -/
lemma sum_inv_sq_eq_zero (hp5 : 5 ≤ p) :
    ∑ i ∈ Finset.Ico 1 p, ((i : ZMod p)⁻¹) ^ 2 = 0 := by
  have hp : p.Prime := Fact.out
  have hndvd : ¬ (p - 1) ∣ (2 * p - 4) := by
    have e : 2 * p - 4 = (p - 1) + (p - 3) := by omega
    rw [e, Nat.dvd_add_right (dvd_refl _)]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have key := sum_pow_Ico p (j := 2 * p - 4) (by omega) hndvd
  rw [← key]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_Ico] at hi
  have hi0 : (i : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => by have := Nat.le_of_dvd (by omega) h; omega
  rw [inv_eq_pow p hi0, ← pow_mul]
  congr 1
  omega

/-- **Wolstenholme**: `∑_{i=1}^{p-1} i⁻¹ = 0` in `ZMod (p^2)` for `p ≥ 5`. -/
lemma wolstenholme (hp5 : 5 ≤ p) :
    ∑ i ∈ Finset.Ico 1 p, ((i : ZMod (p^2)))⁻¹ = 0 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  set S := ∑ i ∈ Finset.Ico 1 p, ((i : ZMod (p^2)))⁻¹ with hS
  -- reindex i ↦ p - i
  have hre : S = ∑ i ∈ Finset.Ico 1 p, (((p - i : ℕ) : ZMod (p^2)))⁻¹ := by
    rw [hS]
    refine Finset.sum_nbij' (fun i => p - i) (fun i => p - i) ?_ ?_ ?_ ?_ ?_ <;>
      intro i hi <;> simp only [Finset.mem_Ico] at * <;> try omega
    congr 2; omega
  -- units
  have hunit : ∀ i ∈ Finset.Ico 1 p, IsUnit (i : ZMod (p^2)) ∧ IsUnit ((p - i : ℕ) : ZMod (p^2)) := by
    intro i hi; simp only [Finset.mem_Ico] at hi
    constructor <;>
      · rw [ZMod.isUnit_iff_coprime]
        apply Nat.Coprime.pow_right
        rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
        intro h; have := Nat.le_of_dvd (by omega) h; omega
  -- pair up
  have h2S : (2 : ZMod (p^2)) * S
      = (p : ZMod (p^2)) * ∑ i ∈ Finset.Ico 1 p, ((i : ZMod (p^2)) * ((p - i : ℕ) : ZMod (p^2)))⁻¹ := by
    rw [two_mul]
    nth_rewrite 2 [hre]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨ha, hb⟩ := hunit i hi
    have hab : IsUnit ((i : ZMod (p^2)) * ((p - i : ℕ) : ZMod (p^2))) := ha.mul hb
    simp only [Finset.mem_Ico] at hi
    have hpsum : (i : ZMod (p^2)) + ((p - i : ℕ) : ZMod (p^2)) = (p : ZMod (p^2)) := by
      rw [← Nat.cast_add, show i + (p - i) = p by omega]
    rw [← hpsum]
    -- prove a⁻¹+b⁻¹ = (a+b)(ab)⁻¹ by cancelling the unit ab
    apply hab.mul_right_injective
    show (i : ZMod (p^2)) * ((p - i : ℕ) : ZMod (p^2)) * ((i : ZMod (p^2))⁻¹ + ((p - i : ℕ) : ZMod (p^2))⁻¹)
        = (i : ZMod (p^2)) * ((p - i : ℕ) : ZMod (p^2)) *
          (((i : ZMod (p^2)) + ((p - i : ℕ) : ZMod (p^2))) * ((i : ZMod (p^2)) * ((p - i : ℕ) : ZMod (p^2)))⁻¹)
    rw [mul_add]
    rw [show (i : ZMod (p^2)) * ((p - i : ℕ) : ZMod (p^2)) * (i : ZMod (p^2))⁻¹
          = ((p - i : ℕ) : ZMod (p^2)) * ((i : ZMod (p^2)) * (i : ZMod (p^2))⁻¹) by ring,
        show (i : ZMod (p^2)) * ((p - i : ℕ) : ZMod (p^2)) * ((p - i : ℕ) : ZMod (p^2))⁻¹
          = (i : ZMod (p^2)) * (((p - i : ℕ) : ZMod (p^2)) * ((p - i : ℕ) : ZMod (p^2))⁻¹) by ring,
        ZMod.mul_inv_of_unit _ ha, ZMod.mul_inv_of_unit _ hb, mul_one, mul_one,
        show (i : ZMod (p^2)) * ((p - i : ℕ) : ZMod (p^2)) *
            (((i : ZMod (p^2)) + ((p - i : ℕ) : ZMod (p^2))) *
              ((i : ZMod (p^2)) * ((p - i : ℕ) : ZMod (p^2)))⁻¹)
          = ((i : ZMod (p^2)) + ((p - i : ℕ) : ZMod (p^2))) *
              ((i : ZMod (p^2)) * ((p - i : ℕ) : ZMod (p^2)) *
                ((i : ZMod (p^2)) * ((p - i : ℕ) : ZMod (p^2)))⁻¹) by ring,
        ZMod.mul_inv_of_unit _ hab, mul_one, add_comm]
  -- the inner sum reduces to 0 mod p
  have hcast : (ZMod.castHom (⟨p, sq p⟩ : p ∣ p^2) (ZMod p))
      (∑ i ∈ Finset.Ico 1 p, ((i : ZMod (p^2)) * ((p - i : ℕ) : ZMod (p^2)))⁻¹) = 0 := by
    rw [map_sum]
    rw [show (0 : ZMod p) = - ∑ i ∈ Finset.Ico 1 p, ((i : ZMod p)⁻¹) ^ 2 by
      rw [sum_inv_sq_eq_zero p hp5, neg_zero]]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨ha, hb⟩ := hunit i hi
    have hab : IsUnit ((i : ZMod (p^2)) * ((p - i : ℕ) : ZMod (p^2))) := ha.mul hb
    simp only [Finset.mem_Ico] at hi
    have hi0 : (i : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; intro h
      have := Nat.le_of_dvd (by omega) h; omega
    have hpi : ((p - i : ℕ) : ZMod p) = -(i : ZMod p) := by
      rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add, show p - i + i = p by omega,
        ZMod.natCast_self]
    -- castHom preserves inverse of the unit
    set F := ZMod.castHom (⟨p, sq p⟩ : p ∣ p^2) (ZMod p)
    have hmap : F ((i : ZMod (p^2)) * ((p - i : ℕ) : ZMod (p^2)))⁻¹
        = (F ((i : ZMod (p^2)) * ((p - i : ℕ) : ZMod (p^2))))⁻¹ := by
      have h1 : F ((i : ZMod (p^2)) * ((p - i : ℕ) : ZMod (p^2)))
          * F ((i : ZMod (p^2)) * ((p - i : ℕ) : ZMod (p^2)))⁻¹ = 1 := by
        rw [← map_mul, ZMod.mul_inv_of_unit _ hab, map_one]
      exact (inv_eq_of_mul_eq_one_right h1).symm
    rw [hmap, map_mul, map_natCast, map_natCast, hpi, mul_neg, inv_neg, mul_inv, ← pow_two]
  have hpY := p_mul_eq_zero_of_castHom _ hcast
  rw [← h2S] at hpY
  -- 2 is a unit
  have h2u : IsUnit (2 : ZMod (p^2)) := by
    rw [show (2 : ZMod (p^2)) = ((2 : ℕ) : ZMod (p^2)) by norm_num, ZMod.isUnit_iff_coprime]
    have : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
    exact (this.pow_right 2)
  exact (h2u.mul_right_eq_zero).mp hpY

namespace GenWol

variable (p : ℕ) [Fact p.Prime]

/-- castHom of sum of inverse-squares over [1,p) in ZMod (p^2) is zero. -/
lemma castHom_inv_sq (hp5 : 5 ≤ p) :
    (ZMod.castHom (⟨p, sq p⟩ : p ∣ p^2) (ZMod p))
      (∑ s ∈ Finset.Ico 1 p, ((s : ZMod (p^2)))⁻¹ ^ 2) = 0 := by
  have hp : p.Prime := Fact.out
  rw [map_sum, ← sum_inv_sq_eq_zero p hp5]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [Finset.mem_Ico] at hs
  have hsu : IsUnit ((s : ZMod (p^2))) := by
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro h; have := Nat.le_of_dvd (by omega) h; omega
  set F := ZMod.castHom (⟨p, sq p⟩ : p ∣ p^2) (ZMod p)
  have hmap : F ((s : ZMod (p^2)))⁻¹ = (F (s : ZMod (p^2)))⁻¹ := by
    have h1 : F (s : ZMod (p^2)) * F ((s : ZMod (p^2)))⁻¹ = 1 := by
      rw [← map_mul, ZMod.mul_inv_of_unit _ hsu, map_one]
    exact (inv_eq_of_mul_eq_one_right h1).symm
  rw [map_pow, hmap, map_natCast]

end GenWol

namespace GenWol2

variable (p : ℕ) [Fact p.Prime]

/-- For a unit `a` in `ZMod n`, `a * y = 1` determines `a⁻¹ = y`. -/
lemma inv_eq_of_unit_mul {n : ℕ} {a y : ZMod n} (ha : IsUnit a) (h : a * y = 1) :
    a⁻¹ = y := by
  have := ZMod.inv_mul_of_unit a ha
  calc a⁻¹ = a⁻¹ * (a * y) := by rw [h, mul_one]
    _ = (a⁻¹ * a) * y := by ring
    _ = y := by rw [this, one_mul]

/-- `p * ∑ s⁻² = 0` in `ZMod (p^2)`. -/
lemma p_mul_sum_inv_sq (hp5 : 5 ≤ p) :
    (p : ZMod (p^2)) * (∑ s ∈ Finset.Ico 1 p, ((s : ZMod (p^2)))⁻¹ ^ 2) = 0 :=
  p_mul_eq_zero_of_castHom _ (GenWol.castHom_inv_sq p hp5)

/-- Per-block inverse expansion: `(bp+s)⁻¹ = s⁻¹ - bp·s⁻²` in `ZMod (p^2)`, for `p∤s`. -/
lemma inv_block (hp5 : 5 ≤ p) (b s : ℕ) (hs1 : 1 ≤ s) (hs2 : s < p) :
    ((b * p + s : ℕ) : ZMod (p^2))⁻¹
      = ((s : ZMod (p^2)))⁻¹
        - (b : ZMod (p^2)) * (p : ZMod (p^2)) * ((s : ZMod (p^2)))⁻¹ ^ 2 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  have hsu : IsUnit ((s : ZMod (p^2))) := by
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro h; have := Nat.le_of_dvd (by omega) h; omega
  have hau : IsUnit (((b * p + s : ℕ) : ZMod (p^2))) := by
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro h
    have : p ∣ s := (Nat.dvd_add_right (Dvd.intro_left b rfl)).mp h
    have := Nat.le_of_dvd (by omega) this; omega
  refine inv_eq_of_unit_mul hau ?_
  have hp2 : (p : ZMod (p^2)) * (p : ZMod (p^2)) = 0 := by
    rw [← Nat.cast_mul, ← pow_two, ZMod.natCast_self]
  have hss : (s : ZMod (p^2)) * ((s : ZMod (p^2)))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hsu
  have hss2 : (s : ZMod (p^2)) * ((s : ZMod (p^2)))⁻¹ ^ 2 = ((s : ZMod (p^2)))⁻¹ := by
    calc (s : ZMod (p^2)) * ((s : ZMod (p^2)))⁻¹ ^ 2
        = ((s : ZMod (p^2)) * ((s : ZMod (p^2)))⁻¹) * ((s : ZMod (p^2)))⁻¹ := by
          rw [pow_two]; ring
      _ = ((s : ZMod (p^2)))⁻¹ := by rw [hss, one_mul]
  push_cast
  set B := (b : ZMod (p^2))
  set P := (p : ZMod (p^2))
  set I := ((s : ZMod (p^2)))⁻¹
  have expand : (B * P + (s : ZMod (p^2))) * (I - B * P * I ^ 2)
      = B * P * I - B * P * (B * P) * I ^ 2 + (s : ZMod (p^2)) * I
        - B * P * ((s : ZMod (p^2)) * I ^ 2) := by ring
  rw [expand, hss2, hss,
    show B * P * (B * P) * I ^ 2 = (P * P) * (B * B * I ^ 2) by ring, hp2, zero_mul]
  ring

end GenWol2

namespace GenWol3

variable (p : ℕ) [Fact p.Prime]

/-- Each block sums to zero: `∑_{s=1}^{p-1} (bp+s)⁻¹ = 0` in `ZMod (p^2)`. -/
lemma block_sum_zero (hp5 : 5 ≤ p) (b : ℕ) :
    ∑ s ∈ Finset.Ico 1 p, ((b * p + s : ℕ) : ZMod (p^2))⁻¹ = 0 := by
  have hexp : ∀ s ∈ Finset.Ico 1 p,
      ((b * p + s : ℕ) : ZMod (p^2))⁻¹
        = ((s : ZMod (p^2)))⁻¹
          - (b : ZMod (p^2)) * (p : ZMod (p^2)) * ((s : ZMod (p^2)))⁻¹ ^ 2 := by
    intro s hs; simp only [Finset.mem_Ico] at hs
    exact GenWol2.inv_block p hp5 b s hs.1 hs.2
  rw [Finset.sum_congr rfl hexp, Finset.sum_sub_distrib, wolstenholme p hp5]
  rw [← Finset.mul_sum, mul_assoc, GenWol2.p_mul_sum_inv_sq p hp5, mul_zero, sub_zero]

/-- The reindexing: filtered range as a double sum over blocks. -/
lemma filter_eq_blocks (M : ℕ) (f : ℕ → ZMod (p^2)) :
    ∑ t ∈ (Finset.Ico 1 (p * M)).filter (fun t => ¬ p ∣ t), f t
      = ∑ b ∈ Finset.range M, ∑ s ∈ Finset.Ico 1 p, f (b * p + s) := by
  have hp : p.Prime := Fact.out
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun t => (⟨t / p, t % p⟩ : Σ _ : ℕ, ℕ))
    (fun x => x.1 * p + x.2) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_Ico] at ht
    obtain ⟨⟨ht1, ht2⟩, ht3⟩ := ht
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico]
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul hp.pos]
      have hm : p * M = M * p := Nat.mul_comm p M
      omega
    · rw [Nat.one_le_iff_ne_zero]; intro h; exact ht3 (Nat.dvd_of_mod_eq_zero h)
    · exact Nat.mod_lt _ hp.pos
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico] at hx
    obtain ⟨hb, hs1, hs2⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · omega
    · have hlt : x.1 * p + x.2 < M * p := by
        calc x.1 * p + x.2 < x.1 * p + p := by omega
          _ = (x.1 + 1) * p := by ring
          _ ≤ M * p := Nat.mul_le_mul_right p (by omega)
      have hm : M * p = p * M := Nat.mul_comm M p
      omega
    · intro h
      have : p ∣ x.2 := (Nat.dvd_add_right (dvd_mul_left p x.1)).mp h
      have := Nat.le_of_dvd (by omega) this; omega
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_Ico] at ht
    show (t / p) * p + t % p = t
    rw [Nat.mul_comm]
    exact Nat.div_add_mod t p
  · intro x hx
    obtain ⟨a, c⟩ := x
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico] at hx
    obtain ⟨hb, hs1, hs2⟩ := hx
    have h1 : (a * p + c) / p = a := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp.pos, Nat.div_eq_of_lt hs2, Nat.zero_add]
    have h2 : (a * p + c) % p = c := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hs2
    simp only [h1, h2]
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_Ico] at ht
    show f t = f ((t / p) * p + (t % p))
    congr 1
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod t p).symm

/-- **Generalized Wolstenholme**: `∑_{p∤t, 1≤t<pM} t⁻¹ = 0` in `ZMod (p^2)` for `p ≥ 5`. -/
theorem gen_wolstenholme (hp5 : 5 ≤ p) (M : ℕ) :
    ∑ t ∈ (Finset.Ico 1 (p * M)).filter (fun t => ¬ p ∣ t), ((t : ZMod (p^2)))⁻¹ = 0 := by
  rw [filter_eq_blocks p M (fun t => ((t : ZMod (p^2)))⁻¹)]
  apply Finset.sum_eq_zero
  intro b _
  exact block_sum_zero p hp5 b

end GenWol3
