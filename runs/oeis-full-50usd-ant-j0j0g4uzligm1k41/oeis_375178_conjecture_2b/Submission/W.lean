import FormalConjectures.Util.ProblemImports
open Finset

-- mod p power-sum over units, from FiniteField.sum_pow_lt_card_sub_one
example (p : ℕ) [Fact p.Prime] (i : ℕ) (h : i < p - 1) :
    ∑ x : ZMod p, x ^ i = 0 := by
  simpa using FiniteField.sum_pow_lt_card_sub_one (ZMod p) i (by simpa [ZMod.card] using h)

-- KEY TOOL: sum over the unit group of any power that is "nontrivial" (v^s ≠ 1 as a unit) vanishes.
lemma sum_units_pow_eq_zero {R : Type*} [CommRing R] [Fintype Rˣ] (s : ℕ)
    (v : Rˣ) (hv : IsUnit ((v : R)^s - 1)) :
    ∑ u : Rˣ, ((u : R))^s = 0 := by
  have hreindex : ∑ u : Rˣ, ((u : R))^s = (v : R)^s * ∑ u : Rˣ, ((u : R))^s := by
    conv_lhs => rw [← Equiv.sum_comp (Equiv.mulLeft v) (fun u => ((u : R))^s)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    simp only [Equiv.coe_mulLeft, Units.val_mul, mul_pow]
  have key : ((v : R)^s - 1) * (∑ u : Rˣ, ((u : R))^s) = 0 := by
    rw [sub_mul, one_mul, ← hreindex, sub_self]
  exact hv.mul_right_eq_zero.mp key

-- helper: p*x=0 lemma as a named lemma
lemma pmul_eq_zero (p : ℕ) (hp : 0 < p) (x : ZMod (p^2))
    (hx : (ZMod.castHom (dvd_pow_self p (by omega : 2 ≠ 0)) (ZMod p)) x = 0) :
    (p : ZMod (p^2)) * x = 0 := by
  haveI : NeZero (p^2) := ⟨by positivity⟩
  have hx2 : x = ((x.val : ℕ) : ZMod (p^2)) := (ZMod.natCast_rightInverse x).symm
  have hval : ((x.val : ℕ) : ZMod p) = 0 := by
    have h := congrArg (ZMod.castHom (dvd_pow_self p (by omega : 2 ≠ 0)) (ZMod p)) hx2
    rw [map_natCast] at h
    rw [← h]; exact hx
  rw [ZMod.natCast_eq_zero_iff] at hval
  obtain ⟨m, hm⟩ := hval
  have hp2 : ((p:ZMod (p^2)))^2 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  calc (p:ZMod (p^2)) * x = (p:ZMod (p^2)) * ((p:ZMod (p^2)) * (m:ZMod (p^2))) := by
              rw [hx2, hm]; push_cast; ring
    _ = (p:ZMod (p^2))^2 * (m:ZMod (p^2)) := by ring
    _ = 0 := by rw [hp2]; ring

-- ∑ (k⁻¹)^2 = 0 over units of ZMod p (reusable)
lemma sum_inv_sq_units (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ k ∈ Icc 1 (p-1), (((k : ZMod p))⁻¹)^2 = 0 := by
  haveI : NeZero p := ⟨by omega⟩
  have hfull : ∑ x : ZMod p, ((x : ZMod p)⁻¹)^2 = 0 := by
    rw [show (∑ x : ZMod p, ((x)⁻¹)^2) = ∑ x : ZMod p, (x)^2 from
      Fintype.sum_bijective (·⁻¹) (inv_involutive.bijective) _ _ (fun x => rfl)]
    simpa using FiniteField.sum_pow_lt_card_sub_one (ZMod p) 2
      (by simpa [ZMod.card] using (by omega : 2 < p - 1))
  have e1 : ∑ x ∈ (univ : Finset (ZMod p)).erase 0, (x⁻¹)^2
      = ∑ k ∈ Icc 1 (p-1), (((k : ZMod p))⁻¹)^2 := by
    refine Finset.sum_nbij' (fun x => ZMod.val x) (fun k => (k : ZMod p)) ?_ ?_ ?_ ?_ ?_
    · intro x hx; rw [Finset.mem_erase] at hx; rw [mem_Icc]
      have hv : x.val < p := ZMod.val_lt x
      have hne : x.val ≠ 0 := fun h => hx.1 (by rw [← ZMod.natCast_rightInverse x, h]; simp)
      exact ⟨Nat.one_le_iff_ne_zero.mpr hne, Nat.le_sub_one_of_lt hv⟩
    · intro k hk; rw [mem_Icc] at hk; rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
    · intro x hx; exact ZMod.natCast_rightInverse x
    · intro k hk; rw [mem_Icc] at hk; exact ZMod.val_natCast_of_lt (by omega)
    · intro x hx; rw [ZMod.natCast_rightInverse x]
  have hcond : ∀ x ∈ (univ : Finset (ZMod p)), x ∉ (univ : Finset (ZMod p)).erase 0
      → (x⁻¹)^2 = 0 := by
    intro x _ hx
    have hx0 : x = 0 := by simpa [Finset.mem_erase] using hx
    subst hx0; simp
  rw [← e1, Finset.sum_subset (Finset.subset_univ _) hcond, hfull]

-- Shifted Wolstenholme block: ∑_{i=1}^{p-1} (p*b+i)⁻¹ = 0 in ZMod (p^2)
lemma block_wolstenholme (p b : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ i ∈ Icc 1 (p-1), ((p*b+i : ℕ) : ZMod (p^2))⁻¹ = 0 := by
  haveI : NeZero (p^2) := ⟨by positivity⟩
  haveI : NeZero p := ⟨by omega⟩
  set S := ∑ i ∈ Icc 1 (p-1), ((p*b+i : ℕ) : ZMod (p^2))⁻¹ with hS
  have hunit : ∀ i ∈ Icc 1 (p-1), IsUnit ((p*b+i : ℕ) : ZMod (p^2)) := by
    intro i hi
    rw [mem_Icc] at hi
    have hnd : ¬ p ∣ (p*b+i) := by
      rw [Nat.dvd_add_right (Dvd.intro b rfl)]
      exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
    rw [ZMod.isUnit_iff_coprime]
    exact ((hp.out.coprime_iff_not_dvd.mpr hnd).symm).pow_right 2
  have hmapmem : ∀ i ∈ Icc 1 (p-1), p - i ∈ Icc 1 (p-1) := by
    intro i hi; rw [mem_Icc] at *; omega
  have hreindex : ∑ i ∈ Icc 1 (p-1), ((p*b+(p - i) : ℕ) : ZMod (p^2))⁻¹ = S := by
    rw [hS]
    apply Finset.sum_nbij' (fun i => p - i) (fun i => p - i) hmapmem hmapmem
    · intro i hi; rw [mem_Icc] at hi; omega
    · intro i hi; rw [mem_Icc] at hi; omega
    · intro a _; rfl
  have hterm : ∀ i ∈ Icc 1 (p-1),
      ((p*b+i : ℕ) : ZMod (p^2))⁻¹ + ((p*b+(p - i) : ℕ) : ZMod (p^2))⁻¹
        = (p*(2*b+1) : ℕ) * (((p*b+i : ℕ) : ZMod (p^2))⁻¹ * ((p*b+(p - i) : ℕ) : ZMod (p^2))⁻¹) := by
    intro i hi
    rw [mem_Icc] at hi
    have ha : ((p*b+i : ℕ) : ZMod (p^2)) * ((p*b+i : ℕ) : ZMod (p^2))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ (hunit i (by rw [mem_Icc]; omega))
    have hbb : ((p*b+(p-i) : ℕ) : ZMod (p^2)) * ((p*b+(p-i) : ℕ) : ZMod (p^2))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ (hunit (p-i) (hmapmem i (by rw [mem_Icc]; omega)))
    have hsum : ((p*b+i : ℕ) : ZMod (p^2)) + ((p*b+(p-i) : ℕ) : ZMod (p^2))
        = ((p*(2*b+1) : ℕ) : ZMod (p^2)) := by
      rw [← Nat.cast_add]
      congr 1
      have hip : i ≤ p := by omega
      have hio : i + (p - i) = p := Nat.add_sub_cancel' hip
      calc p*b+i + (p*b+(p-i)) = p*b + p*b + (i + (p-i)) := by ring
        _ = p*b + p*b + p := by rw [hio]
        _ = p*(2*b+1) := by ring
    rw [← hsum]
    calc ((p*b+i : ℕ) : ZMod (p^2))⁻¹ + ((p*b+(p - i) : ℕ) : ZMod (p^2))⁻¹
        = (((p*b+i : ℕ) : ZMod (p^2)) * ((p*b+i : ℕ) : ZMod (p^2))⁻¹) * ((p*b+(p - i) : ℕ) : ZMod (p^2))⁻¹
          + (((p*b+(p-i) : ℕ) : ZMod (p^2)) * ((p*b+(p-i) : ℕ) : ZMod (p^2))⁻¹) * ((p*b+i : ℕ) : ZMod (p^2))⁻¹ := by
            rw [ha, hbb]; ring
      _ = (((p*b+i : ℕ) : ZMod (p^2)) + ((p*b+(p-i) : ℕ) : ZMod (p^2)))
            * (((p*b+i : ℕ) : ZMod (p^2))⁻¹ * ((p*b+(p - i) : ℕ) : ZMod (p^2))⁻¹) := by ring
  set T := ∑ i ∈ Icc 1 (p-1), (((p*b+i : ℕ) : ZMod (p^2))⁻¹ * ((p*b+(p - i) : ℕ) : ZMod (p^2))⁻¹) with hT
  have h2S : 2 * S = ((p*(2*b+1) : ℕ) : ZMod (p^2)) * T := by
    have : S + S = ∑ i ∈ Icc 1 (p-1),
        (((p*b+i : ℕ) : ZMod (p^2))⁻¹ + ((p*b+(p - i) : ℕ) : ZMod (p^2))⁻¹) := by
      rw [Finset.sum_add_distrib, hreindex, hS]
    rw [two_mul, this, Finset.sum_congr rfl hterm, ← Finset.mul_sum, hT]
  have hcast : (ZMod.castHom (dvd_pow_self p (by omega : 2 ≠ 0)) (ZMod p)) T = 0 := by
    rw [hT, map_sum]
    have hkey : ∀ i ∈ Icc 1 (p-1),
        (ZMod.castHom (dvd_pow_self p (by omega : 2 ≠ 0)) (ZMod p))
          (((p*b+i : ℕ) : ZMod (p^2))⁻¹ * ((p*b+(p - i) : ℕ) : ZMod (p^2))⁻¹)
          = -(((i : ZMod p))⁻¹)^2 := by
      intro i hi
      rw [mem_Icc] at hi
      have hik : (ZMod.castHom (dvd_pow_self p (by omega : 2 ≠ 0)) (ZMod p)) (((p*b+i : ℕ) : ZMod (p^2))⁻¹)
          = ((i : ZMod p))⁻¹ := by
        have ha : ((p*b+i : ℕ) : ZMod (p^2)) * ((p*b+i : ℕ) : ZMod (p^2))⁻¹ = 1 :=
          ZMod.mul_inv_of_unit _ (hunit i (by rw [mem_Icc]; omega))
        have hc := congrArg (ZMod.castHom (dvd_pow_self p (by omega : 2 ≠ 0)) (ZMod p)) ha
        rw [map_mul, map_one, map_natCast] at hc
        have hpbi : ((p*b+i : ℕ) : ZMod p) = (i : ZMod p) := by
          push_cast; rw [ZMod.natCast_self]; ring
        rw [hpbi] at hc
        exact eq_inv_of_mul_eq_one_right hc
      have hib : (ZMod.castHom (dvd_pow_self p (by omega : 2 ≠ 0)) (ZMod p)) (((p*b+(p-i):ℕ) : ZMod (p^2))⁻¹)
          = ((p - i : ℕ) : ZMod p)⁻¹ := by
        have hb : ((p*b+(p-i):ℕ) : ZMod (p^2)) * ((p*b+(p-i):ℕ) : ZMod (p^2))⁻¹ = 1 :=
          ZMod.mul_inv_of_unit _ (hunit (p-i) (hmapmem i (by rw [mem_Icc]; omega)))
        have hc := congrArg (ZMod.castHom (dvd_pow_self p (by omega : 2 ≠ 0)) (ZMod p)) hb
        rw [map_mul, map_one, map_natCast] at hc
        have hpbi : ((p*b+(p-i) : ℕ) : ZMod p) = ((p-i:ℕ) : ZMod p) := by
          push_cast; rw [ZMod.natCast_self]; ring
        rw [hpbi] at hc
        exact eq_inv_of_mul_eq_one_right hc
      rw [map_mul, hik, hib]
      have hpk : ((p - i : ℕ) : ZMod p) = -(i : ZMod p) := by
        have : ((p - i : ℕ) : ZMod p) = (p : ZMod p) - (i : ZMod p) := by
          rw [Nat.cast_sub (by omega)]
        rw [this, ZMod.natCast_self, zero_sub]
      rw [hpk, inv_neg]; ring
    rw [Finset.sum_congr rfl hkey, Finset.sum_neg_distrib, sum_inv_sq_units p hp5, neg_zero]
  have hpT : ((p*(2*b+1) : ℕ) : ZMod (p^2)) * T = 0 := by
    have : ((p*(2*b+1) : ℕ) : ZMod (p^2)) = (p : ZMod (p^2)) * ((2*b+1 : ℕ) : ZMod (p^2)) := by
      push_cast; ring
    rw [this, show (p:ZMod (p^2)) * ((2*b+1:ℕ):ZMod (p^2)) * T
        = ((2*b+1:ℕ):ZMod (p^2)) * ((p:ZMod (p^2)) * T) by ring,
      pmul_eq_zero p (by omega) T hcast, mul_zero]
  have h2S0 : (2 : ZMod (p^2)) * S = 0 := by rw [h2S, hpT]
  have h2unit : IsUnit (2 : ZMod (p^2)) := by
    rw [show (2 : ZMod (p^2)) = ((2:ℕ) : ZMod (p^2)) by push_cast; ring, ZMod.isUnit_iff_coprime]
    exact ((Nat.coprime_primes Nat.prime_two hp.out).mpr (by omega)).pow_right 2
  exact h2unit.mul_right_eq_zero.mp h2S0

-- units of ZMod n ↔ {k<n : coprime k n}
lemma sum_units_as_filter (n : ℕ) [NeZero n] (g : ZMod n → ZMod n) :
    ∑ u : (ZMod n)ˣ, g (u:ZMod n) = ∑ k ∈ (range n).filter (fun k => Nat.Coprime k n), g (k:ZMod n) := by
  refine Finset.sum_nbij' (fun u => (u:ZMod n).val)
    (fun k => if h : Nat.Coprime k n then (ZMod.unitOfCoprime k h) else 1) ?_ ?_ ?_ ?_ ?_
  · intro u _; rw [mem_filter, mem_range]
    exact ⟨ZMod.val_lt _, ZMod.val_coe_unit_coprime u⟩
  · intro k _; exact mem_univ _
  · intro u _
    have hc : Nat.Coprime (u:ZMod n).val n := ZMod.val_coe_unit_coprime u
    dsimp only; rw [dif_pos hc]; apply Units.ext
    rw [ZMod.coe_unitOfCoprime]; exact ZMod.natCast_rightInverse (u:ZMod n)
  · intro k hk; rw [mem_filter, mem_range] at hk
    dsimp only; rw [dif_pos hk.2, ZMod.coe_unitOfCoprime]
    exact ZMod.val_natCast_of_lt hk.1
  · intro u _; dsimp only; congr 1; exact (ZMod.natCast_rightInverse (u:ZMod n)).symm

-- power sum over p∤k, k<p^M, vanishes in ZMod (p^M), given a nontrivial witness
lemma sum_pow_filter_zero (p M t : ℕ) [hp : Fact p.Prime] (hM : 0 < M)
    (v : (ZMod (p^M))ˣ) (hv : IsUnit (((v : ZMod (p^M)))^t - 1)) :
    ∑ k ∈ (range (p^M)).filter (fun k => ¬ p ∣ k), ((k : ZMod (p^M)))^t = 0 := by
  haveI : NeZero (p^M) := ⟨(pow_pos hp.out.pos M).ne'⟩
  have hfilter : (range (p^M)).filter (fun k => ¬ p ∣ k)
      = (range (p^M)).filter (fun k => Nat.Coprime k (p^M)) := by
    apply Finset.filter_congr
    intro k _
    rw [Nat.coprime_pow_right_iff hM, Nat.coprime_comm]
    exact (hp.out.coprime_iff_not_dvd).symm
  rw [hfilter, ← sum_units_as_filter (p^M) (fun x => x^t)]
  exact sum_units_pow_eq_zero t v hv

-- periodicity version: power sum over p∤k, k<p^N, vanishes in ZMod (p^M) for M ≤ N
lemma sum_pow_filter_zero_range (p N M t : ℕ) [hp : Fact p.Prime] (hM : 0 < M) (hNM : M ≤ N)
    (v : (ZMod (p^M))ˣ) (hv : IsUnit (((v : ZMod (p^M)))^t - 1)) :
    ∑ k ∈ (range (p^N)).filter (fun k => ¬ p ∣ k), ((k : ZMod (p^M)))^t = 0 := by
  haveI : NeZero (p^M) := ⟨(pow_pos hp.out.pos M).ne'⟩
  have hp0 : 0 < p := hp.out.pos
  set inner := (range (p^M)).filter (fun s => ¬ p ∣ s) with hinner
  set S := (range (p^(N-M))) ×ˢ inner with hSdef
  set f : ℕ × ℕ → ℕ := fun qs => qs.1 * p^M + qs.2 with hf
  have hsplit : p^N = p^(N-M) * p^M := by rw [← pow_add]; congr 1; omega
  have hset : (range (p^N)).filter (fun k => ¬ p ∣ k) = S.image f := by
    ext k
    simp only [mem_filter, mem_range, mem_image, hSdef, mem_product, hinner, hf, Prod.exists]
    constructor
    · rintro ⟨hlt, hnd⟩
      refine ⟨k / p^M, k % p^M, ⟨?_, ⟨?_, ?_⟩⟩, ?_⟩
      · rw [hsplit] at hlt; exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hlt)
      · exact Nat.mod_lt k (pow_pos hp0 M)
      · intro hdvd
        apply hnd
        rw [← Nat.div_add_mod k (p^M)]
        exact Nat.dvd_add (Dvd.dvd.mul_right (dvd_pow_self p (by omega : M ≠ 0)) _) hdvd
      · exact Nat.div_add_mod' k (p^M)
    · rintro ⟨q, s, ⟨hq, hs, hnd⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hsplit]; calc q*p^M+s < q*p^M + p^M := by omega
          _ = (q+1)*p^M := by ring
          _ ≤ p^(N-M)*p^M := Nat.mul_le_mul_right _ (by omega)
      · rw [Nat.dvd_add_right (Dvd.dvd.mul_left (dvd_pow_self p (by omega : M ≠ 0)) q)]; exact hnd
  have hinj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y := by
    rintro ⟨q1, s1⟩ hx ⟨q2, s2⟩ hy hfe
    simp only [hSdef, mem_product, mem_range, hinner, mem_filter] at hx hy
    simp only [hf] at hfe
    have hs1 : s1 < p^M := hx.2.1
    have hs2 : s2 < p^M := hy.2.1
    have hi : s1 = s2 := by
      have e1 : (q1*p^M+s1) % p^M = s1 := by rw [Nat.mul_add_mod']; exact Nat.mod_eq_of_lt hs1
      have e2 : (q2*p^M+s2) % p^M = s2 := by rw [Nat.mul_add_mod']; exact Nat.mod_eq_of_lt hs2
      rw [← e1, ← e2, hfe]
    subst hi
    have hq : q1 = q2 := Nat.eq_of_mul_eq_mul_right (pow_pos hp0 M) (by omega)
    subst hq; rfl
  rw [hset, Finset.sum_image hinj, hSdef, Finset.sum_product]
  apply Finset.sum_eq_zero
  intro q _
  have hstep : ∀ s ∈ inner, ((f (q,s) : ℕ) : ZMod (p^M))^t = ((s : ℕ) : ZMod (p^M))^t := by
    intro s _
    congr 1
    simp only [hf]
    push_cast
    rw [show ((p:ZMod (p^M))^M) = 0 from by rw [← Nat.cast_pow, ZMod.natCast_self]]
    ring
  rw [Finset.sum_congr rfl hstep]
  exact sum_pow_filter_zero p M t hM v hv

lemma gen_wolstenholme (p N : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ s ∈ (range (p*N)).filter (fun s => ¬ p ∣ s), ((s : ℕ) : ZMod (p^2))⁻¹ = 0 := by
  have hp0 : 0 < p := by omega
  set S := (range N) ×ˢ (Icc 1 (p-1)) with hSdef
  set f : ℕ × ℕ → ℕ := fun bi => p * bi.1 + bi.2 with hf
  have hset : (range (p*N)).filter (fun s => ¬ p ∣ s) = S.image f := by
    ext s
    simp only [mem_filter, mem_range, mem_image, hSdef, mem_product, mem_Icc, hf,
      Prod.exists]
    constructor
    · rintro ⟨hlt, hnd⟩
      refine ⟨s / p, s % p, ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
      · exact Nat.div_lt_of_lt_mul (by omega)
      · rcases Nat.eq_zero_or_pos (s % p) with h|h
        · exact absurd (Nat.dvd_of_mod_eq_zero h) hnd
        · exact h
      · have := Nat.mod_lt s hp0; omega
      · exact Nat.div_add_mod s p
    · rintro ⟨b, i, ⟨hb, hi1, hi2⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · have : p * b + i < p * b + p := by omega
        calc p*b+i < p*b+p := this
          _ = p*(b+1) := by ring
          _ ≤ p*N := Nat.mul_le_mul_left p (by omega)
      · rw [Nat.dvd_add_right (Dvd.intro b rfl)]
        exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have hinj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y := by
    rintro ⟨b1, i1⟩ hx ⟨b2, i2⟩ hy hfe
    simp only [hSdef, mem_product, mem_range, mem_Icc] at hx hy
    simp only [hf] at hfe
    have hi : i1 = i2 := by
      have e1 : (p*b1+i1) % p = i1 := by rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
      have e2 : (p*b2+i2) % p = i2 := by rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
      rw [← e1, ← e2, hfe]
    subst hi
    have hb : b1 = b2 := Nat.eq_of_mul_eq_mul_left hp0 (by omega)
    subst hb; rfl
  rw [hset, Finset.sum_image hinj]
  rw [hSdef, Finset.sum_product]
  apply Finset.sum_eq_zero
  intro b _
  simp only [hf]
  exact block_wolstenholme p b hp5

-- Wolstenholme mod p^2 : ∑_{k=1}^{p-1} k⁻¹ = 0 in ZMod (p^2)
lemma wolstenholme (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ k ∈ Icc 1 (p-1), (k : ZMod (p^2))⁻¹ = 0 := by
  haveI : NeZero (p^2) := ⟨by positivity⟩
  haveI : NeZero p := ⟨by omega⟩
  set S := ∑ k ∈ Icc 1 (p-1), (k : ZMod (p^2))⁻¹ with hS
  -- each k in [1,p-1] is a unit in ZMod (p^2)
  have hunit : ∀ k ∈ Icc 1 (p-1), IsUnit (k : ZMod (p^2)) := by
    intro k hk
    rw [mem_Icc] at hk
    have hnd : ¬ p ∣ k := fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
    rw [ZMod.isUnit_iff_coprime]
    exact ((hp.out.coprime_iff_not_dvd.mpr hnd).symm).pow_right 2
  -- reindex k ↦ p - k
  have hmapmem : ∀ k ∈ Icc 1 (p-1), p - k ∈ Icc 1 (p-1) := by
    intro k hk; rw [mem_Icc] at *; omega
  have hreindex : ∑ k ∈ Icc 1 (p-1), ((p - k : ℕ) : ZMod (p^2))⁻¹ = S := by
    rw [hS]
    apply Finset.sum_nbij' (fun k => p - k) (fun k => p - k) hmapmem hmapmem
    · intro k hk; rw [mem_Icc] at hk; omega
    · intro k hk; rw [mem_Icc] at hk; omega
    · intro k hk; rfl
  -- 2S = p * T
  have hterm : ∀ k ∈ Icc 1 (p-1),
      (k : ZMod (p^2))⁻¹ + ((p - k : ℕ) : ZMod (p^2))⁻¹
        = (p : ZMod (p^2)) * ((k : ZMod (p^2))⁻¹ * ((p - k : ℕ) : ZMod (p^2))⁻¹) := by
    intro k hk
    rw [mem_Icc] at hk
    have ha : (k : ZMod (p^2)) * (k : ZMod (p^2))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ (hunit k (by rw [mem_Icc]; omega))
    have hb : ((p-k:ℕ) : ZMod (p^2)) * ((p-k:ℕ) : ZMod (p^2))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ (hunit (p-k) (hmapmem k (by rw [mem_Icc]; omega)))
    have hsum : (k : ZMod (p^2)) + ((p-k:ℕ) : ZMod (p^2)) = (p : ZMod (p^2)) := by
      rw [← Nat.cast_add]; congr 1; omega
    rw [← hsum]
    calc (k : ZMod (p^2))⁻¹ + ((p - k : ℕ) : ZMod (p^2))⁻¹
        = ((k : ZMod (p^2)) * (k : ZMod (p^2))⁻¹) * ((p - k : ℕ) : ZMod (p^2))⁻¹
          + (((p-k:ℕ) : ZMod (p^2)) * ((p-k:ℕ) : ZMod (p^2))⁻¹) * (k : ZMod (p^2))⁻¹ := by
            rw [ha, hb]; ring
      _ = ((k : ZMod (p^2)) + ((p-k:ℕ) : ZMod (p^2)))
            * ((k : ZMod (p^2))⁻¹ * ((p - k : ℕ) : ZMod (p^2))⁻¹) := by ring
  -- Now: 2 S = p * T where T = ∑ k⁻¹ * (p-k)⁻¹
  set T := ∑ k ∈ Icc 1 (p-1), ((k : ZMod (p^2))⁻¹ * ((p - k : ℕ) : ZMod (p^2))⁻¹) with hT
  have h2S : 2 * S = (p : ZMod (p^2)) * T := by
    have : S + S = ∑ k ∈ Icc 1 (p-1),
        ((k : ZMod (p^2))⁻¹ + ((p - k : ℕ) : ZMod (p^2))⁻¹) := by
      rw [Finset.sum_add_distrib, hreindex, hS]
    rw [two_mul, this, Finset.sum_congr rfl hterm, ← Finset.mul_sum, hT]
  -- castHom T = 0
  have hcast : (ZMod.castHom (dvd_pow_self p (by omega : 2 ≠ 0)) (ZMod p)) T = 0 := by
    rw [hT, map_sum]
    have hkey : ∀ k ∈ Icc 1 (p-1),
        (ZMod.castHom (dvd_pow_self p (by omega : 2 ≠ 0)) (ZMod p))
          ((k : ZMod (p^2))⁻¹ * ((p - k : ℕ) : ZMod (p^2))⁻¹)
          = -(((k : ZMod p))⁻¹)^2 := by
      intro k hk
      rw [mem_Icc] at hk
      have hnd : ¬ p ∣ k := fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
      -- castHom preserves the inverses of these units
      have hik : (ZMod.castHom (dvd_pow_self p (by omega : 2 ≠ 0)) (ZMod p)) ((k : ZMod (p^2))⁻¹)
          = ((k : ZMod p))⁻¹ := by
        have ha : (k : ZMod (p^2)) * (k : ZMod (p^2))⁻¹ = 1 :=
          ZMod.mul_inv_of_unit _ (hunit k (by rw [mem_Icc]; omega))
        have := congrArg (ZMod.castHom (dvd_pow_self p (by omega : 2 ≠ 0)) (ZMod p)) ha
        rw [map_mul, map_one, map_natCast] at this
        exact eq_inv_of_mul_eq_one_right this
      have hib : (ZMod.castHom (dvd_pow_self p (by omega : 2 ≠ 0)) (ZMod p)) (((p-k:ℕ) : ZMod (p^2))⁻¹)
          = ((p - k : ℕ) : ZMod p)⁻¹ := by
        have hb : ((p-k:ℕ) : ZMod (p^2)) * ((p-k:ℕ) : ZMod (p^2))⁻¹ = 1 :=
          ZMod.mul_inv_of_unit _ (hunit (p-k) (hmapmem k (by rw [mem_Icc]; omega)))
        have := congrArg (ZMod.castHom (dvd_pow_self p (by omega : 2 ≠ 0)) (ZMod p)) hb
        rw [map_mul, map_one, map_natCast] at this
        exact eq_inv_of_mul_eq_one_right this
      rw [map_mul, hik, hib]
      have hpk : ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
        have : ((p - k : ℕ) : ZMod p) = (p : ZMod p) - (k : ZMod p) := by
          rw [Nat.cast_sub (by omega)]
        rw [this, ZMod.natCast_self, zero_sub]
      rw [hpk, inv_neg]; ring
    rw [Finset.sum_congr rfl hkey, Finset.sum_neg_distrib]
    -- ∑ (k⁻¹)^2 = 0 in ZMod p
    have hsq : ∑ k ∈ Icc 1 (p-1), (((k : ZMod p))⁻¹)^2 = 0 := by
      -- relate to full sum over ZMod p
      have hfull : ∑ x : ZMod p, ((x : ZMod p)⁻¹)^2 = 0 := by
        rw [show (∑ x : ZMod p, ((x)⁻¹)^2) = ∑ x : ZMod p, (x)^2 from
          Fintype.sum_bijective (·⁻¹) (inv_involutive.bijective) _ _ (fun x => rfl)]
        simpa using FiniteField.sum_pow_lt_card_sub_one (ZMod p) 2
          (by simpa [ZMod.card] using (by omega : 2 < p - 1))
      have e1 : ∑ x ∈ (univ : Finset (ZMod p)).erase 0, (x⁻¹)^2
          = ∑ k ∈ Icc 1 (p-1), (((k : ZMod p))⁻¹)^2 := by
        refine Finset.sum_nbij' (fun x => ZMod.val x) (fun k => (k : ZMod p)) ?_ ?_ ?_ ?_ ?_
        · intro x hx; rw [Finset.mem_erase] at hx; rw [mem_Icc]
          have hv : x.val < p := ZMod.val_lt x
          have hne : x.val ≠ 0 := fun h => hx.1 (by rw [← ZMod.natCast_rightInverse x, h]; simp)
          exact ⟨Nat.one_le_iff_ne_zero.mpr hne, Nat.le_sub_one_of_lt hv⟩
        · intro k hk; rw [mem_Icc] at hk; rw [Finset.mem_erase]
          refine ⟨?_, Finset.mem_univ _⟩
          rw [Ne, ZMod.natCast_eq_zero_iff]
          exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
        · intro x hx; exact ZMod.natCast_rightInverse x
        · intro k hk; rw [mem_Icc] at hk; exact ZMod.val_natCast_of_lt (by omega)
        · intro x hx; rw [ZMod.natCast_rightInverse x]
      have hcond : ∀ x ∈ (univ : Finset (ZMod p)), x ∉ (univ : Finset (ZMod p)).erase 0
          → (x⁻¹)^2 = 0 := by
        intro x _ hx
        have hx0 : x = 0 := by simpa [Finset.mem_erase] using hx
        subst hx0; simp
      rw [← e1, Finset.sum_subset (Finset.subset_univ _) hcond, hfull]
    rw [hsq, neg_zero]
  have hpT : (p : ZMod (p^2)) * T = 0 := pmul_eq_zero p (by omega) T hcast
  have h2S0 : (2 : ZMod (p^2)) * S = 0 := by rw [h2S, hpT]
  have h2unit : IsUnit (2 : ZMod (p^2)) := by
    rw [show (2 : ZMod (p^2)) = ((2:ℕ) : ZMod (p^2)) by push_cast; ring, ZMod.isUnit_iff_coprime]
    exact ((Nat.coprime_primes Nat.prime_two hp.out).mpr (by omega)).pow_right 2
  exact h2unit.mul_right_eq_zero.mp h2S0
