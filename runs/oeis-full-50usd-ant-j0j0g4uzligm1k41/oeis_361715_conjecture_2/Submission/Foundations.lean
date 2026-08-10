import Mathlib
open Nat Finset BigOperators

namespace A361715

/-! ## Sum of powers of units -/
theorem sum_units_pow_eq_zero (n : ℕ) [NeZero n] (c : (ZMod n)ˣ) (s : ℕ)
    (hc : IsUnit ((c:ZMod n)^s - 1)) :
    ∑ x : (ZMod n)ˣ, (x : ZMod n)^s = 0 := by
  set S := ∑ x : (ZMod n)ˣ, (x : ZMod n)^s with hS
  have key : (c:ZMod n)^s * S = S := by
    rw [hS, Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft c) (fun x => ((x:ZMod n))^s)]
    exact Finset.sum_congr rfl (fun x _ => by simp [Equiv.mulLeft, mul_pow])
  exact (hc.mul_right_eq_zero).mp (by linear_combination key)

theorem sum_units_inv_pow_eq_zero (n : ℕ) [NeZero n] (c : (ZMod n)ˣ) (s : ℕ)
    (hc : IsUnit ((c:ZMod n)^s - 1)) :
    ∑ x : (ZMod n)ˣ, ((x : ZMod n)⁻¹)^s = 0 := by
  have h : ∑ x : (ZMod n)ˣ, ((x : ZMod n)⁻¹)^s = ∑ x : (ZMod n)ˣ, ((x : ZMod n))^s := by
    rw [← Equiv.sum_comp (Equiv.inv (ZMod n)ˣ) (fun x => ((x:ZMod n))^s)]
    exact Finset.sum_congr rfl (fun x _ => by simp [Equiv.inv])
  rw [h]; exact sum_units_pow_eq_zero n c s hc

theorem sum_filter_isUnit_eq_sum_units (n : ℕ) [NeZero n] (f : ZMod n → ZMod n) :
    ∑ x ∈ (univ.filter (fun x : ZMod n => IsUnit x)), f x = ∑ u : (ZMod n)ˣ, f (u : ZMod n) := by
  have : (univ.filter (fun x : ZMod n => IsUnit x))
       = univ.map ⟨(fun u : (ZMod n)ˣ => (u : ZMod n)), Units.val_injective⟩ := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro hx; exact ⟨hx.unit, by simp⟩
    · rintro ⟨u, _, rfl⟩; exact u.isUnit
  rw [this, Finset.sum_map]; rfl

theorem sum_range_eq_sum_zmod (n : ℕ) [NeZero n] (g : ZMod n → ZMod n) :
    ∑ k ∈ Finset.range n, g (k : ZMod n) = ∑ x : ZMod n, g x := by
  apply Finset.sum_nbij' (i := fun k : ℕ => (k : ZMod n)) (j := fun x : ZMod n => x.val)
  · intro a _; exact mem_univ _
  · intro a _; simp [ZMod.val_lt]
  · intro a ha; simp only [mem_range] at ha; exact ZMod.val_natCast_of_lt ha
  · intro a _; exact ZMod.natCast_zmod_val a
  · intro a _; rfl

theorem castHom_eq_zero_of_not_isUnit (p m : ℕ) [hpp : Fact p.Prime] (hm : 1 ≤ m)
    (z : ZMod (p^m)) (hz : ¬ IsUnit z) :
    (ZMod.castHom (dvd_pow_self p (by omega : m ≠ 0)) (ZMod p)) z = 0 := by
  have hval : ((z.val : ZMod (p^m))) = z := ZMod.natCast_zmod_val z
  rw [← hval, map_natCast, ZMod.natCast_eq_zero_iff]
  by_contra hnd
  apply hz
  rw [← hval, ZMod.isUnit_iff_coprime]
  exact ((Nat.Prime.coprime_iff_not_dvd hpp.out).mpr hnd |>.symm).pow_right m

theorem exists_unit_pow_sub_one_isUnit (p m : ℕ) [hpp : Fact p.Prime] (hm : 1 ≤ m) (s : ℕ)
    (hs : ¬ (p - 1 ∣ s)) :
    ∃ c : (ZMod (p^m))ˣ, IsUnit ((c : ZMod (p^m))^s - 1) := by
  haveI : NeZero (p^m) := ⟨pow_ne_zero m hpp.out.ne_zero⟩
  by_contra h
  push_neg at h
  set f : ZMod (p^m) →+* ZMod p := ZMod.castHom (dvd_pow_self p (by omega : m ≠ 0)) (ZMod p) with hf
  have key : ∀ a : (ZMod p)ˣ, a^s = 1 := by
    intro a
    obtain ⟨c, hc⟩ := ZMod.unitsMap_surjective (dvd_pow_self p (by omega : m ≠ 0)) a
    have h2 : f ((c : ZMod (p^m))^s - 1) = 0 := castHom_eq_zero_of_not_isUnit p m hm _ (h c)
    rw [map_sub, map_pow, map_one] at h2
    have hfc : f (c : ZMod (p^m)) = (a : ZMod p) := by
      have := congrArg (fun u => ((u : (ZMod p)ˣ) : ZMod p)) hc
      simpa [ZMod.unitsMap, hf] using this
    rw [hfc] at h2
    ext; push_cast; simpa using (by linear_combination h2 : ((a:ZMod p))^s = 1)
  have hcard : Fintype.card (ZMod p)ˣ ∣ s := by
    have := Monoid.exponent_dvd_of_forall_pow_eq_one key
    rwa [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card] at this
  rw [ZMod.card_units p] at hcard
  exact hs hcard

/-! ## Generalized Wolstenholme (ZMod p^r) -/
theorem genWolstenholme_inv (p r s : ℕ) [hpp : Fact p.Prime] (hr : 1 ≤ r)
    (hs : ¬ (p - 1 ∣ s)) :
    ∑ k ∈ (Finset.range (p^r)).filter (fun k => ¬ p ∣ k), ((k : ZMod (p^r))⁻¹)^s = 0 := by
  haveI : NeZero (p^r) := ⟨pow_ne_zero r hpp.out.ne_zero⟩
  classical
  have hiff : ∀ k : ℕ, IsUnit ((k:ZMod (p^r))) ↔ ¬ p ∣ k := fun k => by
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff hr, Nat.coprime_comm,
      hpp.out.coprime_iff_not_dvd]
  have step : ∑ k ∈ (Finset.range (p^r)).filter (fun k => ¬ p ∣ k), ((k : ZMod (p^r))⁻¹)^s
      = ∑ x ∈ (univ.filter (fun x : ZMod (p^r) => IsUnit x)), (x⁻¹)^s := by
    rw [Finset.sum_filter, Finset.sum_filter,
        ← sum_range_eq_sum_zmod (p^r) (fun x => if IsUnit x then (x⁻¹)^s else 0)]
    exact Finset.sum_congr rfl (fun k _ => by simp only [hiff k])
  rw [step, sum_filter_isUnit_eq_sum_units (p^r) (fun x => (x⁻¹)^s)]
  obtain ⟨c, hc⟩ := exists_unit_pow_sub_one_isUnit p r hr s hs
  exact sum_units_inv_pow_eq_zero (p^r) c s hc

/-! ## Padic inverse -/
theorem padicInt_natCast_isUnit (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : ¬ p ∣ k) :
    IsUnit (k : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hk

noncomputable def pinv (p : ℕ) [Fact p.Prime] (k : ℕ) : ℤ_[p] :=
  if h : ¬ p ∣ k then ((padicInt_natCast_isUnit p h).unit⁻¹ : ℤ_[p]ˣ) else 0

theorem pinv_mul (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : ¬ p ∣ k) :
    (k : ℤ_[p]) * pinv p k = 1 := by
  unfold pinv; rw [dif_pos hk]; exact (padicInt_natCast_isUnit p hk).unit.mul_inv

theorem toZModPow_pinv (p : ℕ) [Fact p.Prime] (n : ℕ) {k : ℕ} (hk : ¬ p ∣ k) :
    PadicInt.toZModPow n (pinv p k) = ((k : ZMod (p^n)))⁻¹ := by
  have h1 := pinv_mul p hk
  have hthis := congrArg (PadicInt.toZModPow n) h1
  rw [map_mul, map_one, map_natCast] at hthis
  have hku : IsUnit ((k:ZMod (p^n))) := by
    have h := (padicInt_natCast_isUnit p hk).map (PadicInt.toZModPow n)
    rwa [map_natCast] at h
  rw [← one_mul (PadicInt.toZModPow n (pinv p k)), ← ZMod.inv_mul_of_unit _ hku, mul_assoc,
    hthis, mul_one]

/-! ## Power-sum valuation: p^r ∣ ∑ pinv^s -/
theorem dvd_sum_pinv_pow (p r s : ℕ) [hpp : Fact p.Prime] (hr : 1 ≤ r)
    (hs : ¬ (p - 1 ∣ s)) :
    (p^r : ℤ_[p]) ∣ ∑ k ∈ (Finset.range (p^r)).filter (fun k => ¬ p ∣ k), (pinv p k)^s := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sum]
  have hcongr : ∑ k ∈ (Finset.range (p^r)).filter (fun k => ¬ p ∣ k),
        PadicInt.toZModPow r ((pinv p k)^s)
      = ∑ k ∈ (Finset.range (p^r)).filter (fun k => ¬ p ∣ k), ((k : ZMod (p^r))⁻¹)^s := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [map_pow, toZModPow_pinv]
    simp only [Finset.mem_filter] at hk; exact hk.2
  rw [hcongr]; exact genWolstenholme_inv p r s hr hs


noncomputable def R (p r s : ℕ) [Fact p.Prime] : ℤ_[p] :=
  ∑ k ∈ (Finset.range (p^r)).filter (fun k => ¬ p ∣ k), (pinv p k)^s

theorem reindex_gen {M : Type*} [AddCommMonoid M] (p r : ℕ) (hp : 0 < p) (g : ℕ → M) :
    ∑ k ∈ range (p^(r+1)), g (k % p) = ∑ b ∈ range p, ∑ _a ∈ range (p^r), g b := by
  rw [pow_succ]
  rw [show (∑ b ∈ range p, ∑ _a ∈ range (p^r), g b)
      = ∑ x ∈ range p ×ˢ range (p^r), g x.1 from (Finset.sum_product' _ _ _).symm]
  apply Finset.sum_bij' (i := fun k _ => (k % p, k / p)) (j := fun ab _ => ab.2 * p + ab.1)
  · rintro k hk; simp only [mem_product, mem_range] at *
    exact ⟨Nat.mod_lt _ hp, Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hk)⟩
  · rintro ⟨b,a⟩ hab; simp only [mem_product, mem_range] at hab ⊢
    calc a*p+b < a*p+p := by omega
      _ = (a+1)*p := by ring
      _ ≤ p^r*p := Nat.mul_le_mul_right _ hab.2
  · rintro k hk; simp only; rw [mul_comm (k/p) p]; exact Nat.div_add_mod k p
  · rintro ⟨b,a⟩ hab; simp only [mem_product, mem_range] at hab
    have h1 : (a*p+b)/p = a := by
      rw [add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hab.1, zero_add]
    have h2 : (a*p+b)%p = b := by
      rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hab.1]
    simp only [h1, h2]
  · rintro k hk; rfl

theorem R_pos (p r s : ℕ) [hpp : Fact p.Prime] (hr : 2 ≤ r) : (p:ℤ_[p]) ∣ R p r s := by
  haveI : NeZero (p^r) := ⟨pow_ne_zero r hpp.out.ne_zero⟩
  have hp0 : 0 < p := hpp.out.pos
  have h0 : PadicInt.toZModPow 1 (R p r s) = 0 := by
    unfold R
    rw [map_sum]
    have hterm : ∀ k ∈ (Finset.range (p^r)).filter (fun k => ¬ p ∣ k),
        PadicInt.toZModPow 1 ((pinv p k)^s) = (((k % p : ℕ) : ZMod (p^1))⁻¹)^s := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      rw [map_pow, toZModPow_pinv p 1 hk.2]
      congr 2
      rw [pow_one, ZMod.natCast_mod]
    rw [Finset.sum_congr rfl hterm]
    rw [Finset.sum_filter]
    have hfun : ∀ k, (if ¬ p ∣ k then (((k % p:ℕ):ZMod (p^1))⁻¹)^s else 0)
        = (fun b => if b = 0 then 0 else (((b:ℕ):ZMod (p^1))⁻¹)^s) (k % p) := by
      intro k; by_cases h : p ∣ k
      · simp [h, Nat.mod_eq_zero_of_dvd h]
      · have : k % p ≠ 0 := by rwa [Ne, ← Nat.dvd_iff_mod_eq_zero]
        simp [h, this]
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [Finset.sum_congr rfl (fun k _ => hfun k),
      reindex_gen p r' hp0 (fun b => if b = 0 then 0 else (((b:ℕ):ZMod (p^1))⁻¹)^s)]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    apply Finset.sum_eq_zero
    intro b _
    have hz : ((p^r' : ℕ) : ZMod (p^1)) = 0 := by
      rw [pow_one]; push_cast; rw [ZMod.natCast_self, zero_pow (by omega : r' ≠ 0)]
    rw [hz, zero_mul]
  rw [← Ideal.mem_span_singleton]
  have hker := PadicInt.ker_toZModPow (p := p) 1
  have hmem : R p r s ∈ Ideal.span {(p:ℤ_[p])^1} := by
    rw [← hker, RingHom.mem_ker]; exact h0
  rwa [pow_one] at hmem

theorem sum_reflect (p r : ℕ) (hr : 1 ≤ r) (hp : Nat.Prime p) {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) :
    ∑ k ∈ (range (p^r)).filter (fun k => ¬ p ∣ k), f k
      = ∑ k ∈ (range (p^r)).filter (fun k => ¬ p ∣ k), f (p^r - k) := by
  apply Finset.sum_nbij' (i := fun k => p^r - k) (j := fun k => p^r - k)
  · intro k hk; simp only [mem_filter, mem_range] at hk ⊢
    obtain ⟨hlt, hnd⟩ := hk
    have hk0 : k ≠ 0 := by rintro rfl; exact hnd (dvd_zero p)
    refine ⟨by omega, ?_⟩
    intro hd; apply hnd
    have : p ∣ p^r := dvd_pow_self p (by omega)
    have h2 : k = p^r - (p^r - k) := by omega
    rw [h2]; exact Nat.dvd_sub this hd
  · intro k hk; simp only [mem_filter, mem_range] at hk ⊢
    obtain ⟨hlt, hnd⟩ := hk
    have hk0 : k ≠ 0 := by rintro rfl; exact hnd (dvd_zero p)
    refine ⟨by omega, ?_⟩
    intro hd; apply hnd
    have : p ∣ p^r := dvd_pow_self p (by omega)
    have h2 : k = p^r - (p^r - k) := by omega
    rw [h2]; exact Nat.dvd_sub this hd
  · intro k hk; simp only [mem_filter, mem_range] at hk; omega
  · intro k hk; simp only [mem_filter, mem_range] at hk; omega
  · intro k hk; simp only [mem_filter, mem_range] at hk; congr 1; omega

theorem refl_term (p r : ℕ) [Fact p.Prime] {k : ℕ} (hk : ¬ p ∣ k) (hkN : k < p^r) :
    (pinv p k)^3 + (pinv p (p^r - k))^3 + 3*(p^r:ℤ_[p])*(pinv p k)^4
      = (p^r:ℤ_[p])^2 * (3*(p^r:ℤ_[p])^2 - 8*(p^r:ℤ_[p])*(k:ℤ_[p]) + 6*(k:ℤ_[p])^2)
          * (pinv p k)^4 * (pinv p (p^r - k))^3 := by
  set N : ℤ_[p] := (p:ℤ_[p])^r with hN
  set kk := pinv p k with hkk
  set L := pinv p (p^r - k) with hL
  have h1 : (k:ℤ_[p]) * kk = 1 := pinv_mul p hk
  have hnd : ¬ p ∣ (p^r - k) := by
    intro hd; apply hk
    have hpd : p ∣ p^r := dvd_pow_self p (by rintro rfl; rw [pow_zero, Nat.lt_one_iff] at hkN; subst hkN; exact hk (dvd_zero p))
    have : k = p^r - (p^r - k) := by omega
    rw [this]; exact Nat.dvd_sub hpd hd
  have h2' : ((p^r - k : ℕ):ℤ_[p]) * L = 1 := pinv_mul p hnd
  have hcast : ((p^r - k : ℕ):ℤ_[p]) = N - (k:ℤ_[p]) := by
    rw [Nat.cast_sub (le_of_lt hkN)]; push_cast; ring
  rw [hcast] at h2'
  have PI : (k:ℤ_[p])*(N - k)^3 + (k:ℤ_[p])^4 + 3*N*(N - k)^3
      = N^2*(3*N^2 - 8*N*(k:ℤ_[p]) + 6*(k:ℤ_[p])^2) := by ring
  have key := congrArg (fun t => t * (kk^4 * L^3)) PI
  simp only at key
  have e1 : (k:ℤ_[p])*(N-k)^3 * (kk^4 * L^3) = kk^3 := by
    have : ((N - (k:ℤ_[p]))*L)^3 = 1 := by rw [h2']; ring
    calc (k:ℤ_[p])*(N-k)^3 * (kk^4 * L^3)
        = ((k:ℤ_[p])*kk) * ((N-k)*L)^3 * kk^3 := by ring
      _ = kk^3 := by rw [h1, this]; ring
  have e2 : (k:ℤ_[p])^4 * (kk^4 * L^3) = L^3 := by
    calc (k:ℤ_[p])^4 * (kk^4 * L^3) = ((k:ℤ_[p])*kk)^4 * L^3 := by ring
      _ = L^3 := by rw [h1]; ring
  have e3 : 3*N*(N-k)^3 * (kk^4 * L^3) = 3*N*kk^4 := by
    have : ((N - (k:ℤ_[p]))*L)^3 = 1 := by rw [h2']; ring
    calc 3*N*(N-k)^3 * (kk^4 * L^3) = 3*N* ((N-k)*L)^3 * kk^4 := by ring
      _ = 3*N*kk^4 := by rw [this]; ring
  have lhs_eq : ((k:ℤ_[p])*(N-k)^3 + (k:ℤ_[p])^4 + 3*N*(N-k)^3) * (kk^4*L^3)
      = kk^3 + L^3 + 3*N*kk^4 := by rw [add_mul, add_mul, e1, e2, e3]
  rw [lhs_eq] at key
  rw [key]; ring

theorem R3_reflect (p r : ℕ) [hpp : Fact p.Prime] (hr : 1 ≤ r) :
    (p^r:ℤ_[p])^2 ∣ (2 * R p r 3 + 3 * (p^r:ℤ_[p]) * R p r 4) := by
  have hp := hpp.out
  have hreflR3 : R p r 3 = ∑ k ∈ (range (p^r)).filter (fun k => ¬ p ∣ k), (pinv p (p^r - k))^3 := by
    unfold R
    exact sum_reflect p r hr hp (fun k => (pinv p k)^3)
  have hsplit : 2 * R p r 3 + 3 * (p^r:ℤ_[p]) * R p r 4
      = ∑ k ∈ (range (p^r)).filter (fun k => ¬ p ∣ k),
          ((pinv p k)^3 + (pinv p (p^r - k))^3 + 3*(p^r:ℤ_[p])*(pinv p k)^4) := by
    have : (2:ℤ_[p]) * R p r 3 = R p r 3 + R p r 3 := by ring
    rw [this]
    nth_rewrite 2 [hreflR3]
    unfold R
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [hsplit]
  have hterm : ∀ k ∈ (range (p^r)).filter (fun k => ¬ p ∣ k),
      ((pinv p k)^3 + (pinv p (p^r - k))^3 + 3*(p^r:ℤ_[p])*(pinv p k)^4)
      = (p^r:ℤ_[p])^2 * ((3*(p^r:ℤ_[p])^2 - 8*(p^r:ℤ_[p])*(k:ℤ_[p]) + 6*(k:ℤ_[p])^2)
          * (pinv p k)^4 * (pinv p (p^r - k))^3) := by
    intro k hk; simp only [mem_filter, mem_range] at hk
    rw [refl_term p r hk.2 hk.1]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  exact dvd_mul_right _ _

/-- Capstone: `R3 = ∑ (pinv k)^3` has `p`-adic valuation `≥ 3` for `p ≥ 5`, `r ≥ 2`. -/
theorem R3_val3 (p r : ℕ) [hpp : Fact p.Prime] (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
    (p:ℤ_[p])^3 ∣ R p r 3 := by
  have hrefl := R3_reflect p r (by omega)
  -- (p^r:ℤ_[p])^2 = (p:ℤ_[p])^(2*r)
  have hpow : ((p:ℤ_[p])^r)^2 = (p:ℤ_[p])^(2*r) := by
    rw [← pow_mul, Nat.mul_comm]
  rw [hpow] at hrefl
  have hR4 : (p:ℤ_[p]) ∣ R p r 4 := R_pos p r 4 (by omega)
  -- assembly logic
  set R3 := R p r 3
  set R4 := R p r 4
  obtain ⟨w, hw⟩ := hR4
  have hA : (p:ℤ_[p])^(r+1) ∣ (2*R3 + 3*(p:ℤ_[p])^r*R4) :=
    dvd_trans (pow_dvd_pow _ (by omega)) hrefl
  have hB : (p:ℤ_[p])^(r+1) ∣ 3*(p:ℤ_[p])^r*R4 := by
    rw [hw]; exact ⟨3*w, by ring⟩
  have hC : (p:ℤ_[p])^(r+1) ∣ 2*R3 := by
    have := dvd_sub hA hB
    rwa [show (2*R3 + 3*(p:ℤ_[p])^r*R4) - 3*(p:ℤ_[p])^r*R4 = 2*R3 from by ring] at this
  have h2unit : IsUnit (2:ℤ_[p]) := by
    have : ((2:ℕ):ℤ_[p]) = (2:ℤ_[p]) := by norm_num
    rw [← this]; exact padicInt_natCast_isUnit p (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
  have hR3 : (p:ℤ_[p])^(r+1) ∣ R3 := (IsUnit.dvd_mul_left h2unit).mp hC
  exact dvd_trans (pow_dvd_pow _ (by omega)) hR3


theorem choose_prod (p : ℕ) [Fact p.Prime] (M : ℕ) : ∀ m : ℕ, m ≤ M →
    (Nat.choose M m : ℚ_[p]) = ∏ i ∈ Finset.range m, ((M:ℚ_[p]) - i) / (i+1) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [Finset.prod_range_succ, ← ih (by omega)]
    have hkey : (Nat.choose M (n+1) : ℚ_[p]) * ((n:ℚ_[p])+1) = (Nat.choose M n : ℚ_[p]) * ((M:ℚ_[p]) - n) := by
      have h := Nat.choose_succ_right_eq M n
      have : ((Nat.choose M (n+1) * (n+1) : ℕ) : ℚ_[p]) = ((Nat.choose M n * (M - n) : ℕ):ℚ_[p]) := by
        rw [h]
      push_cast [Nat.cast_sub (by omega : n ≤ M)] at this
      linear_combination this
    have hn1 : ((n:ℚ_[p])+1) ≠ 0 := by
      have : ((n+1:ℕ):ℚ_[p]) ≠ 0 := by rw [Ne, Nat.cast_eq_zero]; omega
      push_cast at this; convert this using 2
    field_simp
    linear_combination hkey

theorem bk_prod (p : ℕ) [Fact p.Prime] (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) :
    ((Nat.choose (N-1) (k-1))^2 * Nat.choose (N+k-1) (k-1) : ℚ_[p])
      = ∏ i ∈ Finset.range (k-1), ((1 - (N:ℚ_[p])/(i+1))^2 * (1 + (N:ℚ_[p])/(i+1))) := by
  have hNpos : 1 ≤ N := le_trans hk hkN
  have hC1 : (Nat.choose (N-1) (k-1) : ℚ_[p]) = ∏ i ∈ Finset.range (k-1), (((N-1:ℕ):ℚ_[p]) - i)/(i+1) :=
    choose_prod p (N-1) (k-1) (by omega)
  have hC2 : (Nat.choose (N+k-1) (k-1) : ℚ_[p]) = ∏ i ∈ Finset.range (k-1), (((N+k-1:ℕ):ℚ_[p]) - i)/(i+1) :=
    choose_prod p (N+k-1) (k-1) (by omega)
  rw [hC1, hC2]
  have e1 : (((N-1:ℕ):ℚ_[p])) = (N:ℚ_[p]) - 1 := by
    rw [Nat.cast_sub hNpos]; push_cast; ring
  have e2 : (((N+k-1:ℕ):ℚ_[p])) = (N:ℚ_[p]) + (k:ℚ_[p]) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [e1, e2]
  have hrefl : (∏ i ∈ Finset.range (k-1), (((N:ℚ_[p]) + (k:ℚ_[p]) - 1) - i)/((i:ℚ_[p])+1))
             = ∏ i ∈ Finset.range (k-1), (((N:ℚ_[p]) + (i:ℚ_[p]) + 1)/((i:ℚ_[p])+1)) := by
    rw [Finset.prod_div_distrib, Finset.prod_div_distrib]
    congr 1
    rw [← Finset.prod_range_reflect (fun i => (N:ℚ_[p]) + (i:ℚ_[p]) + 1) (k-1)]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    have : ((k - 1 - 1 - i : ℕ):ℚ_[p]) = (k:ℚ_[p]) - 1 - 1 - (i:ℚ_[p]) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast; ring
    rw [this]; ring
  rw [hrefl, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hden : ((i:ℚ_[p]) + 1) ≠ 0 := by
    have : ((i+1:ℕ):ℚ_[p]) ≠ 0 := by rw [Ne, Nat.cast_eq_zero]; omega
    push_cast at this; exact this
  field_simp
  ring


theorem norm_xdiv_le' (p r i : ℕ) [hpp : Fact p.Prime] (hi : i + 1 < p^r) :
    ‖((p:ℚ_[p])^r/((i:ℚ_[p])+1))‖ ≤ 1 := by
  rw [Padic.norm_le_one_iff_val_nonneg, div_eq_mul_inv]
  have hi1 : ((i:ℚ_[p])+1) = ((i+1:ℕ):ℚ_[p]) := by push_cast; ring
  have hpne : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hpp.out.ne_zero
  have hnum_ne : (p:ℚ_[p])^r ≠ 0 := pow_ne_zero _ hpne
  have hden_ne : ((i:ℚ_[p])+1) ≠ 0 := by rw [hi1]; exact_mod_cast (by omega : (i+1:ℕ) ≠ 0)
  rw [Padic.valuation_mul hnum_ne (inv_ne_zero hden_ne), Padic.valuation_pow, Padic.valuation_p,
      Padic.valuation_inv, hi1, Padic.valuation_natCast]
  have hv : padicValNat p (i+1) ≤ r := by
    have hle : p^(padicValNat p (i+1)) ≤ i+1 := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    by_contra h; push_neg at h
    have : p^r < p^(padicValNat p (i+1)) := Nat.pow_lt_pow_right hpp.out.one_lt h
    omega
  omega

noncomputable def xdiv (p r i : ℕ) [Fact p.Prime] : ℤ_[p] :=
  if h : i+1 < p^r then ⟨(p:ℚ_[p])^r/((i:ℚ_[p])+1), norm_xdiv_le' p r i h⟩ else 0

theorem coe_xdiv (p r i : ℕ) [Fact p.Prime] (hi : i+1 < p^r) :
    ((xdiv p r i : ℤ_[p]) : ℚ_[p]) = (p:ℚ_[p])^r/((i:ℚ_[p])+1) := by
  unfold xdiv; rw [dif_pos hi]

theorem dvd_xdiv (p r i : ℕ) [hpp : Fact p.Prime] (hi : i+1 < p^r) (hr : 1 ≤ r) :
    (p:ℤ_[p]) ∣ xdiv p r i := by
  rw [← PadicInt.norm_lt_one_iff_dvd, PadicInt.norm_def, coe_xdiv p r i hi]
  set x := (p:ℚ_[p])^r/((i:ℚ_[p])+1) with hx
  have hi1 : ((i:ℚ_[p])+1) = ((i+1:ℕ):ℚ_[p]) := by push_cast; ring
  have hpne : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hpp.out.ne_zero
  have hnum_ne : (p:ℚ_[p])^r ≠ 0 := pow_ne_zero _ hpne
  have hden_ne : ((i:ℚ_[p])+1) ≠ 0 := by rw [hi1]; exact_mod_cast (by omega : (i+1:ℕ) ≠ 0)
  have hxne : x ≠ 0 := div_ne_zero hnum_ne hden_ne
  have hv : padicValNat p (i+1) < r := by
    have hle : p^(padicValNat p (i+1)) ≤ i+1 := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    have hlt : p^(padicValNat p (i+1)) < p^r := lt_of_le_of_lt hle hi
    exact (Nat.pow_lt_pow_iff_right hpp.out.one_lt).mp hlt
  have hval : x.valuation = (r:ℤ) - (padicValNat p (i+1) : ℤ) := by
    rw [hx, div_eq_mul_inv, Padic.valuation_mul hnum_ne (inv_ne_zero hden_ne),
      Padic.valuation_pow, Padic.valuation_p, Padic.valuation_inv, hi1, Padic.valuation_natCast]
    ring
  have hneg : -x.valuation < 0 := by rw [hval]; omega
  rw [Padic.norm_eq_zpow_neg_valuation hxne]
  have hp1 : (1:ℝ) < p := by exact_mod_cast hpp.out.one_lt
  calc (p:ℝ)^(-x.valuation) < (p:ℝ)^(0:ℤ) := zpow_lt_zpow_right₀ hp1 hneg
    _ = 1 := by simp



noncomputable def wdiv (p r i : ℕ) [Fact p.Prime] : ℤ_[p] :=
  -(xdiv p r i) - (xdiv p r i)^2 + (xdiv p r i)^3

theorem bk_prod_int (p r k : ℕ) [hpp : Fact p.Prime] (hk : 1 ≤ k) (hkN : k ≤ p^r) :
    ((Nat.choose (p^r-1) (k-1))^2 * Nat.choose (p^r+k-1) (k-1) : ℤ_[p])
      = ∏ i ∈ Finset.range (k-1), (1 + wdiv p r i) := by
  apply Subtype.coe_injective
  push_cast
  rw [bk_prod p (p^r) k hk hkN, ← PadicInt.Coe.ringHom_apply, map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  have hi' : i + 1 < p^r := by omega
  rw [PadicInt.Coe.ringHom_apply, PadicInt.coe_add, PadicInt.coe_one]
  unfold wdiv
  rw [PadicInt.coe_add, PadicInt.coe_sub, PadicInt.coe_neg, PadicInt.coe_pow, PadicInt.coe_pow,
      coe_xdiv p r i hi']
  have hden : ((i:ℚ_[p]) + 1) ≠ 0 := by
    have : ((i+1:ℕ):ℚ_[p]) ≠ 0 := by rw [Ne, Nat.cast_eq_zero]; omega
    push_cast at this; exact this
  simp only [Nat.cast_pow]
  field_simp
  ring

theorem dvd_wdiv (p r i : ℕ) [hpp : Fact p.Prime] (hi : i+1 < p^r) (hr : 1 ≤ r) :
    (p:ℤ_[p]) ∣ wdiv p r i := by
  unfold wdiv
  obtain ⟨w, hw⟩ := dvd_xdiv p r i hi hr
  exact ⟨-w - p*w^2 + p^2*w^3, by rw [hw]; ring⟩


theorem prod_expand_mod' {ι : Type*} [DecidableEq ι] (p : ℕ) [Fact p.Prime] (s : Finset ι) (w : ι → ℤ_[p])
    (hw : ∀ i ∈ s, (p:ℤ_[p]) ∣ w i) :
    (p:ℤ_[p])^3 ∣ (∏ i ∈ s, (1 + w i)
        - ∑ t ∈ s.powerset.filter (fun t => t.card ≤ 2), ∏ i ∈ t, w i) := by
  rw [Finset.prod_one_add]
  rw [← Finset.sum_filter_add_sum_filter_not s.powerset (fun t => t.card ≤ 2)]
  rw [add_sub_cancel_left]
  apply Finset.dvd_sum
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_powerset, not_le] at ht
  obtain ⟨hts, htc⟩ := ht
  have hpc : (∏ _i ∈ t, (p:ℤ_[p])) ∣ ∏ i ∈ t, w i :=
    Finset.prod_dvd_prod_of_dvd _ _ (fun i hi => hw i (hts hi))
  rw [Finset.prod_const] at hpc
  exact dvd_trans (pow_dvd_pow _ (by omega)) hpc

/-- Mod-`p^3` expansion of the central binomial product `B_k`. -/
theorem bk_expand (p r k : ℕ) [Fact p.Prime] (hk : 1 ≤ k) (hkN : k ≤ p^r) (hr : 1 ≤ r) :
    (p:ℤ_[p])^3 ∣ (((Nat.choose (p^r-1) (k-1))^2 * Nat.choose (p^r+k-1) (k-1) : ℤ_[p])
      - ∑ t ∈ (Finset.range (k-1)).powerset.filter (fun t => t.card ≤ 2), ∏ i ∈ t, wdiv p r i) := by
  have hpe := prod_expand_mod' p (Finset.range (k-1)) (fun i => wdiv p r i)
    (fun i hi => by
      simp only [Finset.mem_range] at hi
      exact dvd_wdiv p r i (by omega) hr)
  have hB := bk_prod_int p r k hk hkN
  rw [hB]; exact hpe

/-- Decomposition of the `card ≤ 2` power-set sum into cardinalities 0, 1, 2. -/
theorem sum_powerset_card_le_two (p : ℕ) [Fact p.Prime] {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℤ_[p]) :
    ∑ t ∈ s.powerset.filter (fun t => t.card ≤ 2), ∏ i ∈ t, w i
    = ∑ t ∈ s.powersetCard 0, ∏ i ∈ t, w i
      + ∑ t ∈ s.powersetCard 1, ∏ i ∈ t, w i
      + ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, w i := by
  have hd1 : Disjoint (s.powersetCard 0) (s.powersetCard 1) := by
    rw [Finset.disjoint_left]; intro a ha ha1
    rw [Finset.mem_powersetCard] at ha ha1; omega
  have hd2 : Disjoint (s.powersetCard 0 ∪ s.powersetCard 1) (s.powersetCard 2) := by
    rw [Finset.disjoint_left]; intro a ha ha2
    rw [Finset.mem_union, Finset.mem_powersetCard, Finset.mem_powersetCard] at ha
    rw [Finset.mem_powersetCard] at ha2; omega
  rw [← Finset.sum_union hd1, ← Finset.sum_union hd2]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext t
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union, Finset.mem_powersetCard]
  constructor
  · rintro ⟨hs, hc⟩
    rcases (by omega : t.card = 0 ∨ t.card = 1 ∨ t.card = 2) with h|h|h
    · exact Or.inl (Or.inl ⟨hs,h⟩)
    · exact Or.inl (Or.inr ⟨hs,h⟩)
    · exact Or.inr ⟨hs,h⟩
  · rintro ((⟨hs,h⟩|⟨hs,h⟩)|⟨hs,h⟩) <;> exact ⟨hs, by omega⟩

theorem sum_powersetCard_zero (p : ℕ) [Fact p.Prime] {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℤ_[p]) :
    ∑ t ∈ s.powersetCard 0, ∏ i ∈ t, w i = 1 := by
  rw [Finset.powersetCard_zero]; simp

theorem sum_powersetCard_one (p : ℕ) [Fact p.Prime] {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℤ_[p]) :
    ∑ t ∈ s.powersetCard 1, ∏ i ∈ t, w i = ∑ a ∈ s, w a := by
  rw [Finset.powersetCard_one, Finset.sum_map]; simp

/-- Concrete mod-`p^3` expansion: `B_k ≡ 1 + Σ w_i + Σ_{pairs} w_i w_j`. -/
theorem bk_expand_concrete (p r k : ℕ) [Fact p.Prime] (hk : 1 ≤ k) (hkN : k ≤ p^r) (hr : 1 ≤ r) :
    (p:ℤ_[p])^3 ∣ ((Nat.choose (p^r-1) (k-1))^2 * Nat.choose (p^r+k-1) (k-1)
      - (1 + (∑ a ∈ Finset.range (k-1), wdiv p r a)
          + ∑ t ∈ (Finset.range (k-1)).powersetCard 2, ∏ i ∈ t, wdiv p r i)) := by
  have h := bk_expand p r k hk hkN hr
  rw [sum_powerset_card_le_two p (Finset.range (k-1)) (fun i => wdiv p r i),
      sum_powersetCard_zero p (Finset.range (k-1)) (fun i => wdiv p r i),
      sum_powersetCard_one p (Finset.range (k-1)) (fun i => wdiv p r i)] at h
  exact h
