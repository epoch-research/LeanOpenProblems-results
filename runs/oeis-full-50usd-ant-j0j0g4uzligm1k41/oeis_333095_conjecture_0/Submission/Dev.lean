import FormalConjectures.Util.ProblemImports
open Nat Finset

-- Development file for the A333095 supercongruence proof.

-- sum of x^2 over all of ZMod p is 0
theorem sum_sq_univ_zero (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ x : ZMod p, x ^ 2 = 0 := by
  have hq : Fintype.card (ZMod p) = p := ZMod.card p
  apply FiniteField.sum_pow_lt_card_sub_one
  rw [hq]; omega

-- sum of x^2 over nonzero elements is 0
theorem sum_sq_nonzero_zero (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ x ∈ (Finset.univ : Finset (ZMod p)) \ {0}, x ^ 2 = 0 := by
  have h := sum_sq_univ_zero p hp5
  rw [Finset.sum_sdiff_eq_sub (by simp : ({0} : Finset (ZMod p)) ⊆ univ)]
  simp [h]

-- sum of x⁻¹^2 over nonzero elements is 0 (inverse is a bijection on nonzero)
theorem sum_inv_sq_nonzero_zero (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ x ∈ (Finset.univ : Finset (ZMod p)) \ {0}, (x⁻¹) ^ 2 = 0 := by
  have key : ∑ x ∈ (Finset.univ : Finset (ZMod p)) \ {0}, (x⁻¹) ^ 2
      = ∑ x ∈ (Finset.univ : Finset (ZMod p)) \ {0}, x ^ 2 := by
    apply Finset.sum_nbij' (fun x => x⁻¹) (fun x => x⁻¹)
    · intro a ha; simp only [mem_sdiff, mem_univ, true_and, mem_singleton] at *
      exact inv_ne_zero ha
    · intro a ha; simp only [mem_sdiff, mem_univ, true_and, mem_singleton] at *
      exact inv_ne_zero ha
    · intro a ha; simp only [mem_sdiff, mem_univ, true_and, mem_singleton] at ha
      exact inv_inv a
    · intro a ha; simp only [mem_sdiff, mem_univ, true_and, mem_singleton] at ha
      exact inv_inv a
    · intro a ha; rfl
  rw [key, sum_sq_nonzero_zero p hp5]

/-- For `k` in `1..p-1`, `k` is a unit in `ZMod (p^2)`. -/
theorem isUnit_cast_p2 (p : ℕ) [Fact p.Prime] (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < p) :
    IsUnit (k : ZMod (p ^ 2)) := by
  rw [ZMod.isUnit_iff_coprime]
  have hp : p.Prime := Fact.out
  have hkp : Nat.Coprime k p := by
    rw [Nat.coprime_comm]
    rw [hp.coprime_iff_not_dvd]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  exact hkp.pow_right 2

/-- In `ZMod (p^2)`, if `x` reduces to `0 mod p` then `p * x = 0`. -/
theorem p_mul_eq_zero_of_castHom_zero (p : ℕ) (hp0 : 0 < p) (x : ZMod (p ^ 2))
    (hx : (ZMod.castHom (by exact ⟨p, by ring⟩ : p ∣ p ^ 2) (ZMod p)) x = 0) :
    (p : ZMod (p ^ 2)) * x = 0 := by
  haveI : NeZero (p ^ 2) := ⟨by positivity⟩
  -- reduce to divisibility of x.val by p
  have hxval : ((x.val : ℕ) : ZMod p) = 0 := by
    have h2 : (ZMod.castHom (by exact ⟨p, by ring⟩ : p ∣ p ^ 2) (ZMod p)) x
        = ((x.val : ℕ) : ZMod p) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val x]
      rw [map_natCast]
    rw [h2] at hx
    exact hx
  have hdvd : p ∣ x.val := by
    rwa [ZMod.natCast_eq_zero_iff] at hxval
  obtain ⟨m, hm⟩ := hdvd
  have h3 : (p : ZMod (p ^ 2)) * x = ((p * x.val : ℕ) : ZMod (p ^ 2)) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [h3, hm]
  have h4 : p * (p * m) = p ^ 2 * m := by ring
  rw [h4, Nat.cast_mul, ZMod.natCast_self]
  ring

/-- The pairing identity: `1/k + 1/(p-k) = p * (k(p-k))⁻¹` in `ZMod (p^2)`. -/
theorem pair_inv (p : ℕ) [Fact p.Prime] (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < p) :
    (k : ZMod (p ^ 2))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 2))⁻¹
      = (p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2)) * ((p - k : ℕ) : ZMod (p ^ 2)))⁻¹ := by
  set a : ZMod (p ^ 2) := (k : ZMod (p ^ 2)) with ha_def
  set b : ZMod (p ^ 2) := ((p - k : ℕ) : ZMod (p ^ 2)) with hb_def
  have ha : IsUnit a := isUnit_cast_p2 p k hk1 hk2
  have hb : IsUnit b := isUnit_cast_p2 p (p - k) (by omega) (by omega)
  have hab : IsUnit (a * b) := ha.mul hb
  have hsum : a + b = (p : ZMod (p ^ 2)) := by
    rw [ha_def, hb_def, ← Nat.cast_add]
    congr 1
    omega
  have hainv : a⁻¹ = b * (a * b)⁻¹ := by
    have h1 : a * (b * (a * b)⁻¹) = 1 := by
      rw [← mul_assoc]; exact ZMod.mul_inv_of_unit _ hab
    calc a⁻¹ = a⁻¹ * (a * (b * (a * b)⁻¹)) := by rw [h1, mul_one]
      _ = (a⁻¹ * a) * (b * (a * b)⁻¹) := by ring
      _ = b * (a * b)⁻¹ := by rw [ZMod.inv_mul_of_unit _ ha, one_mul]
  have hbinv : b⁻¹ = a * (a * b)⁻¹ := by
    have h1 : b * (a * (a * b)⁻¹) = 1 := by
      rw [show b * (a * (a * b)⁻¹) = (a * b) * (a * b)⁻¹ by ring]
      exact ZMod.mul_inv_of_unit _ hab
    calc b⁻¹ = b⁻¹ * (b * (a * (a * b)⁻¹)) := by rw [h1, mul_one]
      _ = (b⁻¹ * b) * (a * (a * b)⁻¹) := by ring
      _ = a * (a * b)⁻¹ := by rw [ZMod.inv_mul_of_unit _ hb, one_mul]
  rw [hainv, hbinv, ← hsum]
  ring

/-- A ring hom to a field sends the ZMod-inverse of a unit to the field inverse. -/
theorem castHom_inv (p : ℕ) [Fact p.Prime] (hdvd : p ∣ p ^ 2) (u : ZMod (p ^ 2))
    (hu : IsUnit u) :
    (ZMod.castHom hdvd (ZMod p)) u⁻¹ = ((ZMod.castHom hdvd (ZMod p)) u)⁻¹ := by
  have h1 : (ZMod.castHom hdvd (ZMod p)) u * (ZMod.castHom hdvd (ZMod p)) u⁻¹ = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit u hu, map_one]
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h1)

/-- Sum over `Ico 1 p` of inverse-squares is 0 mod p. -/
theorem sum_inv_sq_Ico (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ k ∈ Finset.Ico 1 p, ((k : ZMod p)⁻¹) ^ 2 = 0 := by
  rw [← sum_inv_sq_nonzero_zero p hp5]
  refine Finset.sum_nbij' (fun k => (k : ZMod p)) ZMod.val ?_ ?_ ?_ ?_ ?_
  · intro a ha; rw [Finset.mem_Ico] at ha
    simp only [mem_sdiff, mem_univ, true_and, mem_singleton,
      ZMod.natCast_eq_zero_iff]
    intro h; have := Nat.le_of_dvd (by omega) h; omega
  · intro x hx; simp only [mem_sdiff, mem_univ, true_and, mem_singleton] at hx
    rw [Finset.mem_Ico]
    refine ⟨?_, ZMod.val_lt x⟩
    rw [Nat.one_le_iff_ne_zero]
    intro h; exact hx (by rw [← ZMod.natCast_zmod_val x, h]; simp)
  · intro a ha; rw [Finset.mem_Ico] at ha; exact ZMod.val_natCast_of_lt ha.2
  · intro x hx; exact ZMod.natCast_zmod_val x
  · intro a ha; rfl

/-- Wolstenholme's theorem: for prime `p ≥ 5`, `∑_{k=1}^{p-1} 1/k ≡ 0 mod p²`. -/
theorem wolstenholme (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ k ∈ Finset.Ico 1 p, ((k : ZMod (p ^ 2))⁻¹) = 0 := by
  have hp : p.Prime := Fact.out
  set S := ∑ k ∈ Finset.Ico 1 p, ((k : ZMod (p ^ 2))⁻¹) with hS
  -- Reindex by k ↦ p - k.
  have hreindex : S = ∑ k ∈ Finset.Ico 1 p, (((p - k : ℕ) : ZMod (p ^ 2))⁻¹) := by
    rw [hS]
    apply Finset.sum_nbij' (fun k => p - k) (fun k => p - k)
    · intro a ha; rw [Finset.mem_Ico] at *; omega
    · intro a ha; rw [Finset.mem_Ico] at *; omega
    · intro a ha; rw [Finset.mem_Ico] at ha; omega
    · intro a ha; rw [Finset.mem_Ico] at ha; omega
    · intro a ha; rw [Finset.mem_Ico] at ha
      have : p - (p - a) = a := by omega
      rw [this]
  -- 2 S = p * T
  set T := ∑ k ∈ Finset.Ico 1 p, ((k : ZMod (p ^ 2)) * ((p - k : ℕ) : ZMod (p ^ 2)))⁻¹ with hT
  have h2S : (2 : ZMod (p ^ 2)) * S = (p : ZMod (p ^ 2)) * T := by
    have e1 : (2 : ZMod (p ^ 2)) * S = S + S := by ring
    rw [e1]
    nth_rewrite 2 [hreindex]
    rw [hT, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Ico] at hk
    exact pair_inv p k hk.1 hk.2
  -- castHom T = 0
  have hdvd : p ∣ p ^ 2 := ⟨p, by ring⟩
  have hcast : (ZMod.castHom hdvd (ZMod p)) T = 0 := by
    rw [hT, map_sum]
    have hstep : ∑ k ∈ Finset.Ico 1 p,
        (ZMod.castHom hdvd (ZMod p)) ((k : ZMod (p ^ 2)) * ((p - k : ℕ) : ZMod (p ^ 2)))⁻¹
        = ∑ k ∈ Finset.Ico 1 p, -(((k : ZMod p)⁻¹) ^ 2) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hku : IsUnit ((k : ZMod (p ^ 2)) * ((p - k : ℕ) : ZMod (p ^ 2))) :=
        (isUnit_cast_p2 p k hk.1 hk.2).mul (isUnit_cast_p2 p (p - k) (by omega) (by omega))
      rw [castHom_inv p hdvd _ hku]
      rw [map_mul, map_natCast, map_natCast]
      have hpk : ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
        have h5 : ((p - k : ℕ) : ZMod p) = ((p : ℕ) : ZMod p) - (k : ZMod p) := by
          rw [← Nat.cast_sub (by omega)]
        rw [h5, ZMod.natCast_self, zero_sub]
      rw [hpk, mul_neg, ← sq, inv_neg, ← inv_pow]
    rw [hstep, Finset.sum_neg_distrib, sum_inv_sq_Ico p hp5, neg_zero]
  have hpT : (p : ZMod (p ^ 2)) * T = 0 := p_mul_eq_zero_of_castHom_zero p (by omega) T hcast
  have h2S0 : (2 : ZMod (p ^ 2)) * S = 0 := by rw [h2S, hpT]
  -- 2 is a unit, so S = 0
  have h2u : IsUnit (2 : ZMod (p ^ 2)) := by
    have h6 : ((2 : ℕ) : ZMod (p ^ 2)) = (2 : ZMod (p ^ 2)) := by norm_num
    rw [← h6, ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  exact (h2u.mul_right_eq_zero).mp h2S0
