import FormalConjectures.Util.ProblemImports

open scoped BigOperators
open Finset

/-- Feasibility probe: Wolstenholme's harmonic sum in `ZMod (p^2)`.
`∑_{k=1}^{p-1} k⁻¹ ≡ 0 (mod p^2)` for primes `p ≥ 5`. -/

-- W2 first: ∑_{k=1}^{p-1} 1/k^2 ≡ 0 mod p, via ∑ x^2 = 0 over the field ZMod p.
example (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    ∑ x : ZMod p, x ^ 2 = 0 := by
  apply FiniteField.sum_pow_lt_card_sub_one
  have : Fintype.card (ZMod p) = p := ZMod.card p
  rw [this]
  omega

-- STEP 1: sum of squares of all units of ZMod N is 0, when 3 and 2 are units (p ≥ 5).
lemma sum_units_sq_eq_zero (N : ℕ) [Fact (1 < N)] (h2 : IsUnit (2 : ZMod N))
    (h3 : IsUnit (3 : ZMod N)) :
    ∑ u : (ZMod N)ˣ, ((u : ZMod N)) ^ 2 = 0 := by
  set S := ∑ u : (ZMod N)ˣ, ((u : ZMod N)) ^ 2 with hS
  -- reindex by multiplication by the unit `t` with value 2
  obtain ⟨t, ht⟩ := h2
  have hperm : S = ∑ u : (ZMod N)ˣ, (((t * u : (ZMod N)ˣ) : ZMod N)) ^ 2 := by
    rw [hS]
    exact (Equiv.sum_comp (Equiv.mulLeft t) (fun u => ((u : ZMod N)) ^ 2)).symm
  have hval : ∀ u : (ZMod N)ˣ, (((t * u : (ZMod N)ˣ) : ZMod N)) ^ 2
      = 4 * ((u : ZMod N)) ^ 2 := by
    intro u
    rw [Units.val_mul, ht, mul_pow]
    ring
  simp_rw [hval] at hperm
  rw [← Finset.mul_sum] at hperm
  -- hperm : S = 4 * S
  have h3S : (3 : ZMod N) * S = 0 := by
    have : (4 : ZMod N) * S - S = 0 := by rw [← hperm]; ring
    linear_combination this
  obtain ⟨w, hw⟩ := h3
  have hwS : (w : ZMod N) * S = 0 := by rw [hw]; exact h3S
  have hS0 : S = 0 := by
    have := congrArg (fun z => ((w⁻¹ : (ZMod N)ˣ) : ZMod N) * z) hwS
    simpa [← mul_assoc, ← Units.val_mul] using this
  rw [hS] at hS0 ⊢; exact hS0

-- STEP 2: base bijection: sum over p-coprime residues in [0,p^r) = sum over units.
open Finset in
lemma sum_block_eq_units (p r : ℕ) [Fact p.Prime] (hr : 0 < r) {M : Type*} [AddCommMonoid M]
    (g : ZMod (p^r) → M) :
    ∑ k ∈ (range (p^r)).filter (fun k => ¬ p ∣ k), g (k : ZMod (p^r))
      = ∑ u : (ZMod (p^r))ˣ, g (u : ZMod (p^r)) := by
  have hp : (p:ℕ).Prime := (Fact.out : p.Prime)
  have hNe : NeZero (p^r) := ⟨pow_ne_zero r hp.ne_zero⟩
  symm
  apply Finset.sum_bij (i := fun (u : (ZMod (p^r))ˣ) _ => ((u : ZMod (p^r)).val))
  · -- maps into the filter
    intro u _
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt _, ?_⟩
    intro hdvd
    have hcop : Nat.Coprime ((u : ZMod (p^r)).val) (p^r) := ZMod.val_coe_unit_coprime u
    have hpr : p ∣ p^r := dvd_pow_self p hr.ne'
    exact hp.ne_one (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hdvd hpr))
  · -- injective
    intro u₁ _ u₂ _ heq
    exact Units.ext (ZMod.val_injective (p^r) heq)
  · -- surjective
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hklt, hkdvd⟩ := hk
    have hcop : Nat.Coprime k (p^r) := (((hp.coprime_iff_not_dvd).2 hkdvd).symm).pow_right r
    refine ⟨ZMod.unitOfCoprime k hcop, Finset.mem_univ _, ?_⟩
    rw [ZMod.coe_unitOfCoprime]
    exact ZMod.val_natCast_of_lt hklt
  · -- summand agrees
    intro u _
    congr 1
    rw [ZMod.natCast_val, ZMod.cast_id]

-- STEP 3: sum over p-coprime k in [0, b*p^r) = b • (sum over units).
open Finset in
lemma sum_range_bp_eq_units (p r : ℕ) [Fact p.Prime] (hr : 0 < r) {M : Type*} [AddCommMonoid M]
    (g : ZMod (p^r) → M) (b : ℕ) :
    ∑ k ∈ (range (b * p^r)).filter (fun k => ¬ p ∣ k), g (k : ZMod (p^r))
      = b • ∑ u : (ZMod (p^r))ˣ, g (u : ZMod (p^r)) := by
  have hp : (p:ℕ).Prime := (Fact.out : p.Prime)
  induction b with
  | zero => simp
  | succ b ih =>
    have hpbpr : p ∣ b * p^r := Dvd.dvd.mul_left (dvd_pow_self p hr.ne') b
    rw [show (b+1) * p^r = b*p^r + p^r by ring, Finset.range_add, Finset.filter_union,
        Finset.sum_union (Finset.disjoint_filter_filter
          (Finset.disjoint_range_addLeftEmbedding (b*p^r) (range (p^r)))), ih]
    have h2 : ∑ k ∈ ((range (p^r)).map (addLeftEmbedding (b*p^r))).filter (fun k => ¬ p ∣ k),
          g (k : ZMod (p^r)) = ∑ u : (ZMod (p^r))ˣ, g (u : ZMod (p^r)) := by
      rw [Finset.filter_map, Finset.sum_map, ← sum_block_eq_units p r hr g]
      apply Finset.sum_congr
      · apply Finset.filter_congr
        intro i _
        simp only [Function.comp, addLeftEmbedding_apply]
        have : p ∣ (b*p^r + i) ↔ p ∣ i := Nat.dvd_add_right hpbpr
        tauto
      · intro i hi
        simp only [addLeftEmbedding_apply]
        congr 1
        have : ((b*p^r + i : ℕ) : ZMod (p^r)) = (i : ZMod (p^r)) := by
          push_cast
          rw [show ((b:ZMod (p^r)) * (p:ZMod (p^r))^r) = 0 by
            rw [show ((p:ZMod (p^r))^r) = ((p^r : ℕ) : ZMod (p^r)) by push_cast; ring,
                ZMod.natCast_self]; ring]
          ring
        exact this
    rw [h2, succ_nsmul]

-- STEP 4: sum of inverse-squares of units is 0 (reindex by inversion).
lemma sum_units_inv_sq_eq_zero (N : ℕ) [Fact (1 < N)] (h2 : IsUnit (2 : ZMod N))
    (h3 : IsUnit (3 : ZMod N)) :
    ∑ u : (ZMod N)ˣ, ((u : ZMod N))⁻¹ ^ 2 = 0 := by
  rw [← Equiv.sum_comp (Equiv.inv (ZMod N)ˣ) (fun u => ((u : ZMod N))⁻¹ ^ 2)]
  have h : ∀ u : (ZMod N)ˣ,
      (((Equiv.inv (ZMod N)ˣ) u : (ZMod N)ˣ) : ZMod N)⁻¹ ^ 2 = ((u : ZMod N)) ^ 2 := by
    intro u
    simp only [Equiv.inv_apply]
    rw [ZMod.inv_coe_unit, inv_inv]
  simp_rw [h]
  exact sum_units_sq_eq_zero N h2 h3

-- STEP 5: 2 and 3 are units in ZMod (p^m), for primes p ≥ 5.
lemma two_three_units (p m : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    IsUnit (2 : ZMod (p^m)) ∧ IsUnit (3 : ZMod (p^m)) := by
  have hp : p.Prime := Fact.out
  have hNe : NeZero (p^m) := ⟨pow_ne_zero m hp.ne_zero⟩
  constructor
  · rw [show (2 : ZMod (p^m)) = ((2:ℕ) : ZMod (p^m)) by norm_cast, ZMod.isUnit_iff_coprime]
    exact (((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)).pow_right m)
  · rw [show (3 : ZMod (p^m)) = ((3:ℕ) : ZMod (p^m)) by norm_cast, ZMod.isUnit_iff_coprime]
    exact (((Nat.coprime_primes Nat.prime_three hp).mpr (by omega)).pow_right m)

-- STEP 6: (W-a) sum of inverse-squares over p-coprime k in [0,b p^r) is 0 in ZMod (p^r).
lemma sum_range_inv_sq_zero (p r b : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) :
    ∑ k ∈ (Finset.range (b * p^r)).filter (fun k => ¬ p ∣ k),
      ((k : ZMod (p^r)))⁻¹ ^ 2 = 0 := by
  haveI : Fact (1 < p^r) := ⟨by
    have := (Fact.out : p.Prime).two_le
    calc 1 < p := by omega
      _ ≤ p^r := Nat.le_self_pow hr.ne' p⟩
  obtain ⟨h2, h3⟩ := two_three_units p r hp5
  rw [sum_range_bp_eq_units p r hr (fun x => x⁻¹ ^ 2) b,
    sum_units_inv_sq_eq_zero (p^r) h2 h3, smul_zero]

-- STEP 7: p^r * x = 0 in ZMod (p^(2r)) when x reduces to 0 in ZMod (p^r).
lemma pr_mul_of_reduces_zero (p r : ℕ) [Fact p.Prime] (x : ZMod (p^(2*r)))
    (h : (ZMod.castHom (pow_dvd_pow p (by omega : r ≤ 2*r)) (ZMod (p^r))) x = 0) :
    (p^r : ZMod (p^(2*r))) * x = 0 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p^(2*r)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hpv : p^r ∣ x.val := by
    have h2 : (ZMod.cast x : ZMod (p^r)) = 0 := by rw [← ZMod.castHom_apply]; exact h
    have : ((x.val : ℕ) : ZMod (p^r)) = 0 := by rw [ZMod.natCast_val]; exact h2
    exact (ZMod.natCast_eq_zero_iff _ _).1 this
  obtain ⟨m, hm⟩ := hpv
  have hx : x = (p^r : ZMod (p^(2*r))) * (m : ZMod (p^(2*r))) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x, hm]
    push_cast; ring
  rw [hx, ← mul_assoc]
  have hz : ((p : ZMod (p^(2*r))))^r * ((p : ZMod (p^(2*r))))^r = 0 := by
    rw [← pow_add, show r + r = 2*r by ring, ← Nat.cast_pow, ZMod.natCast_self]
  rw [hz, zero_mul]

-- STEP 8: the reduction map ZMod(p^(2r)) → ZMod(p^r) sends (k)⁻¹ to (k)⁻¹ for p∤k.
lemma cast_inv_reduce (p r k : ℕ) [Fact p.Prime] (hk : ¬ p ∣ k) :
    (ZMod.castHom (pow_dvd_pow p (by omega : r ≤ 2*r)) (ZMod (p^r))) ((k : ZMod (p^(2*r)))⁻¹)
      = ((k : ZMod (p^r)))⁻¹ := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p^(2*r)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (p^r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  set φ := ZMod.castHom (pow_dvd_pow p (by omega : r ≤ 2*r)) (ZMod (p^r)) with hφ
  have hunit : IsUnit ((k : ZMod (p^(2*r)))) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (((hp.coprime_iff_not_dvd).2 hk).symm).pow_right (2*r)
  have h1 : (k : ZMod (p^(2*r))) * (k : ZMod (p^(2*r)))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hunit
  have h2 := congrArg φ h1
  rw [map_mul, map_one, map_natCast] at h2
  exact (ZMod.inv_eq_of_mul_eq_one _ _ _ h2).symm

-- STEP 9: generalized Wolstenholme: ∑ 1/k ≡ 0 mod p^(2r) over p-coprime k in [0, b p^r).
open Finset in
lemma wolstenholme (p r b : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) :
    ∑ k ∈ (range (b * p^r)).filter (fun k => ¬ p ∣ k), ((k : ZMod (p^(2*r))))⁻¹ = 0 := by
  have hp : p.Prime := Fact.out
  haveI hNe : NeZero (p^(2*r)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI hF1 : Fact (1 < p^(2*r)) := ⟨by
    have := hp.two_le
    calc 1 < p := by omega
      _ ≤ p^(2*r) := Nat.le_self_pow (by omega) p⟩
  set n := b * p^r with hn
  have hpn : p ∣ n := Dvd.dvd.mul_left (dvd_pow_self p hr.ne') b
  set F := (range n).filter (fun k => ¬ p ∣ k) with hF
  set S := ∑ k ∈ F, ((k : ZMod (p^(2*r))))⁻¹ with hS
  -- ¬p∣(n-k) for k∈F
  have hnk_dvd : ∀ k, k < n → ¬ p ∣ k → ¬ p ∣ (n - k) := by
    intro k hlt hd hdd
    exact hd ((Nat.dvd_sub_iff_right (le_of_lt hlt) hpn).mp hdd)
  -- reindex k ↦ n - k
  have reindex : ∑ k ∈ F, ((n - k : ℕ) : ZMod (p^(2*r)))⁻¹ = S := by
    rw [hS]
    refine Finset.sum_nbij' (fun k => n - k) (fun k => n - k) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [hF, mem_filter, mem_range] at hk ⊢
      obtain ⟨hlt, hd⟩ := hk
      have hk0 : k ≠ 0 := fun h => hd (h ▸ dvd_zero p)
      exact ⟨by omega, hnk_dvd k hlt hd⟩
    · intro k hk
      simp only [hF, mem_filter, mem_range] at hk ⊢
      obtain ⟨hlt, hd⟩ := hk
      have hk0 : k ≠ 0 := fun h => hd (h ▸ dvd_zero p)
      exact ⟨by omega, hnk_dvd k hlt hd⟩
    · intro k hk
      rw [hF, mem_filter, mem_range] at hk
      exact Nat.sub_sub_self (le_of_lt hk.1)
    · intro k hk
      rw [hF, mem_filter, mem_range] at hk
      exact Nat.sub_sub_self (le_of_lt hk.1)
    · intro k _; rfl
  -- pairing
  set T := ∑ k ∈ F, ((k : ZMod (p^(2*r))))⁻¹ * ((n - k : ℕ) : ZMod (p^(2*r)))⁻¹ with hT
  have hpair : (2 : ZMod (p^(2*r))) * S = (n : ZMod (p^(2*r))) * T := by
    have hSS : (∑ k ∈ F, (((k : ZMod (p^(2*r))))⁻¹ + (((n - k : ℕ)) : ZMod (p^(2*r)))⁻¹)) = S + S := by
      rw [Finset.sum_add_distrib, reindex]
    have h2S : (2 : ZMod (p^(2*r))) * S = S + S := by ring
    rw [h2S, ← hSS, hT, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hF, mem_filter, mem_range] at hk
    obtain ⟨hlt, hd⟩ := hk
    have hunit_k : IsUnit ((k : ZMod (p^(2*r)))) := by
      rw [ZMod.isUnit_iff_coprime]; exact (((hp.coprime_iff_not_dvd).2 hd).symm).pow_right (2*r)
    have hunit_nk : IsUnit (((n - k : ℕ)) : ZMod (p^(2*r))) := by
      rw [ZMod.isUnit_iff_coprime]
      exact (((hp.coprime_iff_not_dvd).2 (hnk_dvd k hlt hd)).symm).pow_right (2*r)
    set a := (k : ZMod (p^(2*r)))
    set b' := ((n - k : ℕ) : ZMod (p^(2*r)))
    have ha : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit _ hunit_k
    have hb : b' * b'⁻¹ = 1 := ZMod.mul_inv_of_unit _ hunit_nk
    have hab : a + b' = (n : ZMod (p^(2*r))) := by
      rw [show a = ((k:ℕ):ZMod (p^(2*r))) from rfl, show b' = ((n-k:ℕ):ZMod (p^(2*r))) from rfl,
        ← Nat.cast_add, Nat.add_sub_cancel' (le_of_lt hlt)]
    calc a⁻¹ + b'⁻¹ = (a * a⁻¹) * b'⁻¹ + a⁻¹ * (b' * b'⁻¹) := by rw [ha, hb]; ring
      _ = (a + b') * (a⁻¹ * b'⁻¹) := by ring
      _ = (n : ZMod (p^(2*r))) * (a⁻¹ * b'⁻¹) := by rw [hab]
  -- n * T = p^r * (b * T), and show that is 0
  have hnT : (n : ZMod (p^(2*r))) * T = ((p : ZMod (p^(2*r)))^r) * ((b : ZMod (p^(2*r))) * T) := by
    rw [hn]; push_cast; ring
  -- image of (b * T) in ZMod(p^r) is 0
  set φ := ZMod.castHom (pow_dvd_pow p (by omega : r ≤ 2*r)) (ZMod (p^r)) with hφ
  have himg : φ ((b : ZMod (p^(2*r))) * T) = 0 := by
    rw [map_mul, hT, map_sum]
    have : ∀ k ∈ F, φ (((k : ZMod (p^(2*r))))⁻¹ * ((n - k : ℕ) : ZMod (p^(2*r)))⁻¹)
        = - (((k : ZMod (p^r)))⁻¹ ^ 2) := by
      intro k hk
      rw [hF, mem_filter, mem_range] at hk
      obtain ⟨hlt, hd⟩ := hk
      rw [map_mul, hφ, cast_inv_reduce p r k hd, cast_inv_reduce p r (n-k) (hnk_dvd k hlt hd)]
      have hcast : ((n - k : ℕ) : ZMod (p^r)) = - ((k : ZMod (p^r))) := by
        rw [Nat.cast_sub (le_of_lt hlt)]
        have : ((n : ℕ) : ZMod (p^r)) = 0 := by
          rw [hn]; push_cast
          rw [show ((p:ZMod (p^r))^r) = ((p^r:ℕ):ZMod (p^r)) by push_cast; ring, ZMod.natCast_self]
          ring
        rw [this]; ring
      rw [hcast]
      haveI : NeZero (p^r) := ⟨pow_ne_zero _ hp.ne_zero⟩
      have hunit_kr : IsUnit ((k : ZMod (p^r))) := by
        rw [ZMod.isUnit_iff_coprime]; exact (((hp.coprime_iff_not_dvd).2 hd).symm).pow_right r
      have ha' : (k : ZMod (p^r)) * (k : ZMod (p^r))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hunit_kr
      have hneg : (- ((k : ZMod (p^r))))⁻¹ = - (((k : ZMod (p^r)))⁻¹) := by
        apply ZMod.inv_eq_of_mul_eq_one
        rw [neg_mul_neg]; exact ha'
      rw [hneg]; ring
    have hsq := sum_range_inv_sq_zero p r b hp5 hr
    rw [← hn, ← hF] at hsq
    rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib, hsq, neg_zero, mul_zero]
  have hkey : (2 : ZMod (p^(2*r))) * S = 0 := by
    rw [hpair, hnT]; exact pr_mul_of_reduces_zero p r _ himg
  obtain ⟨h2u, _⟩ := two_three_units p (2*r) hp5
  obtain ⟨w, hw⟩ := h2u
  have hwS : (w : ZMod (p^(2*r))) * S = 0 := by rw [hw]; exact hkey
  have hfin := congrArg (fun z => ((w⁻¹ : (ZMod (p^(2*r)))ˣ) : ZMod (p^(2*r))) * z) hwS
  simpa [← mul_assoc, ← Units.val_mul] using hfin

-- STEP 10: product expansion when all triple products vanish.
open Finset in
lemma two_mul_prod_one_add {ι R : Type*} [CommRing R] (s : Finset ι) (x : ι → R)
    (htriple : ∀ i j k, x i * x j * x k = 0) :
    2 * ∏ k ∈ s, (1 + x k)
      = 2 + 2 * (∑ k ∈ s, x k) + (∑ k ∈ s, x k)^2 - ∑ k ∈ s, (x k)^2 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 : x a * (∑ k ∈ s, x k)^2 = 0 := by
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      apply Finset.sum_eq_zero; intro i _
      rw [Finset.mul_sum]; apply Finset.sum_eq_zero; intro j _
      rw [← mul_assoc]; exact htriple a i j
    have h2 : x a * (∑ k ∈ s, (x k)^2) = 0 := by
      rw [Finset.mul_sum]; apply Finset.sum_eq_zero; intro k _
      rw [sq, ← mul_assoc]; exact htriple a k k
    have hkey : x a * ((∑ k ∈ s, x k)^2 - ∑ k ∈ s, (x k)^2) = 0 := by
      rw [mul_sub, h1, h2, sub_zero]
    linear_combination (1 + x a) * ih + hkey

-- Generalized cast of inverse.
lemma cast_inv_reduce_gen (p l m k : ℕ) [Fact p.Prime] (hlm : l ≤ m) (hk : ¬ p ∣ k) :
    (ZMod.castHom (pow_dvd_pow p hlm) (ZMod (p^l))) ((k : ZMod (p^m))⁻¹)
      = ((k : ZMod (p^l)))⁻¹ := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p^m) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (p^l) := ⟨pow_ne_zero _ hp.ne_zero⟩
  set φ := ZMod.castHom (pow_dvd_pow p hlm) (ZMod (p^l)) with hφ
  have hunit : IsUnit ((k : ZMod (p^m))) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (((hp.coprime_iff_not_dvd).2 hk).symm).pow_right m
  have h1 : (k : ZMod (p^m)) * (k : ZMod (p^m))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hunit
  have h2 := congrArg φ h1
  rw [map_mul, map_one, map_natCast] at h2
  exact (ZMod.inv_eq_of_mul_eq_one _ _ _ h2).symm

-- STEP 11: general p-adic reduction: if x reduces to 0 in ZMod(p^a), then p^c * x = 0 in ZMod(p^(a+c)).
lemma pk_mul_reduce_zero (p a c : ℕ) [Fact p.Prime] (x : ZMod (p^(a+c)))
    (h : (ZMod.castHom (pow_dvd_pow p (Nat.le_add_right a c)) (ZMod (p^a))) x = 0) :
    ((p : ZMod (p^(a+c)))^c) * x = 0 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p^(a+c)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hpv : p^a ∣ x.val := by
    have h2 : (ZMod.cast x : ZMod (p^a)) = 0 := by rw [← ZMod.castHom_apply]; exact h
    have : ((x.val : ℕ) : ZMod (p^a)) = 0 := by rw [ZMod.natCast_val]; exact h2
    exact (ZMod.natCast_eq_zero_iff _ _).1 this
  obtain ⟨m, hm⟩ := hpv
  have hx : x = ((p : ZMod (p^(a+c)))^a) * (m : ZMod (p^(a+c))) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x, hm]
    push_cast; ring
  rw [hx, ← mul_assoc]
  have hz : ((p : ZMod (p^(a+c)))^c) * ((p : ZMod (p^(a+c)))^a) = 0 := by
    rw [← pow_add, add_comm, ← Nat.cast_pow, ZMod.natCast_self]
  rw [hz, zero_mul]

-- STEP 11': cleaner p-adic reduction avoiding a+c defeq issues.
lemma pk_reduce_zero' (p tot a : ℕ) [Fact p.Prime] (hle : a ≤ tot) (x : ZMod (p^tot))
    (h : (ZMod.castHom (pow_dvd_pow p hle) (ZMod (p^a))) x = 0) :
    ((p : ZMod (p^tot))^(tot - a)) * x = 0 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p^tot) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hpv : p^a ∣ x.val := by
    have h2 : (ZMod.cast x : ZMod (p^a)) = 0 := by rw [← ZMod.castHom_apply]; exact h
    have : ((x.val : ℕ) : ZMod (p^a)) = 0 := by rw [ZMod.natCast_val]; exact h2
    exact (ZMod.natCast_eq_zero_iff _ _).1 this
  obtain ⟨m, hm⟩ := hpv
  have hx : x = ((p : ZMod (p^tot))^a) * (m : ZMod (p^tot)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x, hm]
    push_cast; ring
  rw [hx, ← mul_assoc]
  have hz : ((p : ZMod (p^tot))^(tot - a)) * ((p : ZMod (p^tot))^a) = 0 := by
    rw [← pow_add, Nat.sub_add_cancel hle, ← Nat.cast_pow, ZMod.natCast_self]
  rw [hz, zero_mul]

open Finset in
-- reduction of the inverse-sum (Wolstenholme) over one block to ZMod (p^(2*r))
lemma sum_inv_reduces_2r (p r : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) :
    (ZMod.castHom (pow_dvd_pow p (by omega : 2*r ≤ 3*r)) (ZMod (p^(2*r))))
      (∑ ℓ ∈ (range (p^r)).filter (fun k => ¬ p ∣ k), ((ℓ : ZMod (p^(3*r))))⁻¹) = 0 := by
  rw [map_sum]
  have heq : ∀ ℓ ∈ (range (p^r)).filter (fun k => ¬ p ∣ k),
      (ZMod.castHom (pow_dvd_pow p (by omega : 2*r ≤ 3*r)) (ZMod (p^(2*r)))) ((ℓ : ZMod (p^(3*r))))⁻¹
        = ((ℓ : ZMod (p^(2*r))))⁻¹ := by
    intro ℓ hℓ
    rw [Finset.mem_filter] at hℓ
    exact cast_inv_reduce_gen p (2*r) (3*r) ℓ (by omega) hℓ.2
  rw [Finset.sum_congr rfl heq]
  have hw := wolstenholme p r 1 hp5 hr
  rw [one_mul] at hw
  exact hw

open Finset in
-- reduction of the inverse-square-sum over one block to ZMod (p^r)
lemma sum_invsq_reduces_r (p r : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) :
    (ZMod.castHom (pow_dvd_pow p (by omega : r ≤ 3*r)) (ZMod (p^r)))
      (∑ ℓ ∈ (range (p^r)).filter (fun k => ¬ p ∣ k), (((ℓ : ZMod (p^(3*r))))⁻¹)^2) = 0 := by
  rw [map_sum]
  have heq : ∀ ℓ ∈ (range (p^r)).filter (fun k => ¬ p ∣ k),
      (ZMod.castHom (pow_dvd_pow p (by omega : r ≤ 3*r)) (ZMod (p^r))) ((((ℓ : ZMod (p^(3*r))))⁻¹)^2)
        = (((ℓ : ZMod (p^r)))⁻¹)^2 := by
    intro ℓ hℓ
    rw [Finset.mem_filter] at hℓ
    rw [map_pow]
    congr 1
    exact cast_inv_reduce_gen p r (3*r) ℓ (by omega) hℓ.2
  rw [Finset.sum_congr rfl heq]
  have hs := sum_range_inv_sq_zero p r 1 hp5 hr
  rw [one_mul] at hs
  exact hs

open Finset in
-- BLOCK LEMMA: the i-th block product equals the 0-th block product G0 in ZMod (p^(3*r)).
lemma block_eq_G0 (p r : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) (i : ℕ) :
    ∏ ℓ ∈ (range (p^r)).filter (fun k => ¬ p ∣ k), ((i * p^r + ℓ : ℕ) : ZMod (p^(3*r)))
      = ∏ ℓ ∈ (range (p^r)).filter (fun k => ¬ p ∣ k), ((ℓ : ℕ) : ZMod (p^(3*r))) := by
  have hp : p.Prime := Fact.out
  set N := p^(3*r) with hN
  haveI : NeZero N := ⟨pow_ne_zero _ hp.ne_zero⟩
  set F := (range (p^r)).filter (fun k => ¬ p ∣ k) with hF
  set x : ℕ → ZMod N := fun ℓ => (i : ZMod N) * (p : ZMod N)^r * ((ℓ : ZMod N))⁻¹ with hx
  -- each factor factorises as ℓ * (1 + x ℓ)
  have hterm : ∀ ℓ ∈ F, ((i * p^r + ℓ : ℕ) : ZMod N) = (ℓ : ZMod N) * (1 + x ℓ) := by
    intro ℓ hℓ
    rw [hF, Finset.mem_filter, Finset.mem_range] at hℓ
    obtain ⟨_, hℓd⟩ := hℓ
    have hunit : IsUnit ((ℓ : ZMod N)) := by
      rw [ZMod.isUnit_iff_coprime]
      exact (((hp.coprime_iff_not_dvd).2 hℓd).symm).pow_right (3*r)
    have hll : (ℓ : ZMod N) * ((ℓ : ZMod N))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hunit
    rw [hx]
    push_cast
    rw [mul_add, mul_one, ← mul_assoc, ← mul_assoc]
    rw [show (ℓ : ZMod N) * (i : ZMod N) * (p:ZMod N)^r * ((ℓ:ZMod N))⁻¹
          = ((ℓ:ZMod N) * ((ℓ:ZMod N))⁻¹) * ((i:ZMod N)*(p:ZMod N)^r) by ring, hll, one_mul]
    ring
  rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib]
  -- reduce to ∏ (1 + x ℓ) = 1
  have hprod1 : ∏ ℓ ∈ F, (1 + x ℓ) = 1 := by
    have htriple : ∀ a b c, x a * x b * x c = 0 := by
      intro a b c
      have h0 : (p:ZMod N)^r * (p:ZMod N)^r * (p:ZMod N)^r = 0 := by
        rw [← pow_add, ← pow_add, show r+r+r = 3*r by ring, ← Nat.cast_pow, ← hN, ZMod.natCast_self]
      calc x a * x b * x c
          = ((p:ZMod N)^r*(p:ZMod N)^r*(p:ZMod N)^r) * ((i:ZMod N)^3 *
              ((a:ZMod N)⁻¹*(b:ZMod N)⁻¹*(c:ZMod N)⁻¹)) := by rw [hx]; ring
        _ = 0 := by rw [h0]; ring
    have hmain := two_mul_prod_one_add F x htriple
    -- show the RHS collapses to 2
    set S := ∑ ℓ ∈ F, ((ℓ : ZMod N))⁻¹ with hS
    have hsumx : ∑ ℓ ∈ F, x ℓ = (i:ZMod N) * ((p:ZMod N)^r * S) := by
      simp only [hx, hS, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro ℓ _; ring
    -- p^r * S = 0 in ZMod N
    have hpS : (p:ZMod N)^r * S = 0 := by
      have := pk_reduce_zero' p (3*r) (2*r) (by omega) S (sum_inv_reduces_2r p r hp5 hr)
      rwa [show 3*r - 2*r = r by omega] at this
    have hsumx0 : ∑ ℓ ∈ F, x ℓ = 0 := by rw [hsumx, hpS, mul_zero]
    -- ∑ x^2 = 0
    set T := ∑ ℓ ∈ F, (((ℓ : ZMod N))⁻¹)^2 with hT
    have hsumxsq : ∑ ℓ ∈ F, (x ℓ)^2 = (i:ZMod N)^2 * ((p:ZMod N)^(2*r) * T) := by
      have hpp : ((p:ZMod N)^r)^2 = (p:ZMod N)^(2*r) := by rw [← pow_mul, Nat.mul_comm]
      simp only [hx, hT, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro ℓ _
      rw [← hpp]; ring
    have hpT : (p:ZMod N)^(2*r) * T = 0 := by
      have := pk_reduce_zero' p (3*r) r (by omega) T (sum_invsq_reduces_r p r hp5 hr)
      rwa [show 3*r - r = 2*r by omega] at this
    have hsumxsq0 : ∑ ℓ ∈ F, (x ℓ)^2 = 0 := by rw [hsumxsq, hpT, mul_zero]
    rw [hsumx0, hsumxsq0] at hmain
    -- hmain : 2 * ∏ (1 + x) = 2 + 2*0 + 0^2 - 0
    have h2 : (2 : ZMod N) * ∏ ℓ ∈ F, (1 + x ℓ) = (2:ZMod N) * 1 := by
      rw [hmain]; ring
    haveI : Nontrivial (ZMod N) := by
      haveI : Fact (1 < N) := ⟨by
        have := hp.two_le
        calc 1 < p := by omega
          _ ≤ p^(3*r) := Nat.le_self_pow (by omega) p⟩
      exact ZMod.nontrivial N
    obtain ⟨w, hw⟩ := (two_three_units p (3*r) hp5).1
    have key : (↑w : ZMod N) * ∏ ℓ ∈ F, (1 + x ℓ) = (↑w : ZMod N) * 1 := by rw [hw]; exact h2
    have hu : (↑(w⁻¹) : ZMod N) * (↑w : ZMod N) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc ∏ ℓ ∈ F, (1 + x ℓ) = ↑(w⁻¹) * ((↑w : ZMod N) * ∏ ℓ ∈ F, (1 + x ℓ)) := by
            rw [← mul_assoc, hu, one_mul]
      _ = ↑(w⁻¹) * ((↑w : ZMod N) * 1) := by rw [key]
      _ = 1 := by rw [mul_one, hu]
  rw [hprod1, mul_one]

open Finset in
-- split a product over p-coprime residues in [0, b*p^r) into b blocks of length p^r.
lemma prod_range_block {M : Type*} [CommMonoid M] (p r : ℕ) (hr : 0 < r) (f : ℕ → M) (b : ℕ) :
    ∏ k ∈ (range (b * p^r)).filter (fun k => ¬ p ∣ k), f k
      = ∏ i ∈ range b, ∏ ℓ ∈ (range (p^r)).filter (fun k => ¬ p ∣ k), f (i * p^r + ℓ) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hpbpr : p ∣ b * p^r := Dvd.dvd.mul_left (dvd_pow_self p hr.ne') b
    rw [show (b+1) * p^r = b*p^r + p^r by ring, Finset.range_add, Finset.filter_union,
        Finset.prod_union (Finset.disjoint_filter_filter
          (Finset.disjoint_range_addLeftEmbedding (b*p^r) (range (p^r)))), ih, Finset.prod_range_succ]
    congr 1
    rw [Finset.filter_map, Finset.prod_map]
    apply Finset.prod_congr
    · apply Finset.filter_congr
      intro i _
      simp only [Function.comp, addLeftEmbedding_apply]
      have : p ∣ (b*p^r + i) ↔ p ∣ i := Nat.dvd_add_right hpbpr
      tauto
    · intro i _
      simp only [addLeftEmbedding_apply]

open Finset in
-- g-product equals G0^b in ZMod (p^(3*r)), where G0 is the length-p^r block product.
lemma g_prod_eq (p r : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) (b : ℕ) :
    ∏ k ∈ (range (b * p^r)).filter (fun k => ¬ p ∣ k), ((k : ℕ) : ZMod (p^(3*r)))
      = (∏ ℓ ∈ (range (p^r)).filter (fun k => ¬ p ∣ k), ((ℓ : ℕ) : ZMod (p^(3*r))))^b := by
  rw [prod_range_block p r hr (fun k => ((k : ℕ) : ZMod (p^(3*r)))) b]
  rw [Finset.prod_congr rfl (fun i _ => block_eq_G0 p r hp5 hr i)]
  rw [Finset.prod_const, Finset.card_range]

open scoped Real

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

-- even closed form (all-integer factorials)
lemma a_even (M : ℕ) :
    a (2*M) * (((9*M).factorial : ℝ) * (8*M).factorial * (6*M).factorial * (2*M).factorial)
      = ((18*M).factorial : ℝ) * (4*M).factorial * (3*M).factorial := by
  have g1 : Real.Gamma (9 * ((2*M : ℕ) : ℝ) + 1) = ((18*M).factorial : ℝ) := by
    rw [show (9 : ℝ) * ((2*M : ℕ) : ℝ) + 1 = ((18*M : ℕ) : ℝ) + 1 by push_cast; ring,
        Real.Gamma_nat_eq_factorial]
  have g2 : Real.Gamma (2 * ((2*M : ℕ) : ℝ) + 1) = ((4*M).factorial : ℝ) := by
    rw [show (2 : ℝ) * ((2*M : ℕ) : ℝ) + 1 = ((4*M : ℕ) : ℝ) + 1 by push_cast; ring,
        Real.Gamma_nat_eq_factorial]
  have g3 : Real.Gamma (3 / 2 * ((2*M : ℕ) : ℝ) + 1) = ((3*M).factorial : ℝ) := by
    rw [show (3 / 2 : ℝ) * ((2*M : ℕ) : ℝ) + 1 = ((3*M : ℕ) : ℝ) + 1 by push_cast; ring,
        Real.Gamma_nat_eq_factorial]
  have g4 : Real.Gamma (9 / 2 * ((2*M : ℕ) : ℝ) + 1) = ((9*M).factorial : ℝ) := by
    rw [show (9 / 2 : ℝ) * ((2*M : ℕ) : ℝ) + 1 = ((9*M : ℕ) : ℝ) + 1 by push_cast; ring,
        Real.Gamma_nat_eq_factorial]
  have g5 : Real.Gamma (4 * ((2*M : ℕ) : ℝ) + 1) = ((8*M).factorial : ℝ) := by
    rw [show (4 : ℝ) * ((2*M : ℕ) : ℝ) + 1 = ((8*M : ℕ) : ℝ) + 1 by push_cast; ring,
        Real.Gamma_nat_eq_factorial]
  have g6 : Real.Gamma (3 * ((2*M : ℕ) : ℝ) + 1) = ((6*M).factorial : ℝ) := by
    rw [show (3 : ℝ) * ((2*M : ℕ) : ℝ) + 1 = ((6*M : ℕ) : ℝ) + 1 by push_cast; ring,
        Real.Gamma_nat_eq_factorial]
  have g7 : Real.Gamma (((2*M : ℕ) : ℝ) + 1) = ((2*M).factorial : ℝ) := by
    rw [Real.Gamma_nat_eq_factorial]
  have hpos : (0:ℝ) < ((9*M).factorial : ℝ) * (8*M).factorial * (6*M).factorial * (2*M).factorial := by
    positivity
  unfold a
  simp only [g1, g2, g3, g4, g5, g6, g7]
  field_simp

open Finset in
lemma prod_Icc_one_eq_factorial (n : ℕ) : ∏ k ∈ Finset.Icc 1 n, k = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)), ih,
        Nat.factorial_succ]
    ring

open Finset in
lemma multiples_image (p n : ℕ) (hp : 1 < p) :
    (Finset.Icc 1 n).filter (fun k => p ∣ k) = (Finset.Icc 1 (n/p)).image (fun j => p*j) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hk1, hkn⟩, hdvd⟩
    obtain ⟨j, rfl⟩ := hdvd
    refine ⟨j, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos j with hj|hj
      · simp [hj] at hk1
      · exact hj
    · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.mul_comm]; exact hkn)
  · rintro ⟨j, ⟨hj1, hjn⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ⟨j, rfl⟩⟩
    · calc 1 ≤ p*1 := by omega
        _ ≤ p*j := Nat.mul_le_mul_left p hj1
    · calc p*j ≤ p*(n/p) := Nat.mul_le_mul_left p hjn
        _ ≤ n := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self n p

open Finset in
lemma factorial_split (p n : ℕ) (hp : 1 < p) :
    n.factorial = (∏ k ∈ (Finset.Icc 1 n).filter (fun k => ¬ p ∣ k), k)
                  * (p^(n/p) * (n/p).factorial) := by
  conv_lhs => rw [← prod_Icc_one_eq_factorial n,
    ← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 n) (fun k => p ∣ k) (fun k => k)]
  rw [mul_comm]
  congr 1
  rw [multiples_image p n hp,
      Finset.prod_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left (by omega) h),
      Finset.prod_mul_distrib, Finset.prod_const, prod_Icc_one_eq_factorial, Nat.card_Icc,
      Nat.add_sub_cancel]

open Finset in
lemma Icc_filter_eq_range_filter (p n : ℕ) (hpn : p ∣ n) :
    (Finset.Icc 1 n).filter (fun k => ¬ p ∣ k) = (Finset.range n).filter (fun k => ¬ p ∣ k) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨hk1, hkn⟩, hd⟩
    refine ⟨?_, hd⟩
    rcases Nat.lt_or_ge k n with h|h
    · exact h
    · exact absurd ((show k = n by omega) ▸ hpn) hd
  · rintro ⟨hkn, hd⟩
    refine ⟨⟨?_, by omega⟩, hd⟩
    rcases Nat.eq_zero_or_pos k with h|h
    · exact absurd (h ▸ dvd_zero p) hd
    · exact h

open Finset in
-- ℤ-version of the single-level factorial split.
lemma single_split (p b r : ℕ) (hp : p.Prime) (hr : 0 < r) :
    ((b*p^r).factorial : ℤ)
      = (∏ k ∈ (Finset.range (b*p^r)).filter (fun k => ¬ p ∣ k), (k:ℤ))
        * (p:ℤ)^(b*p^(r-1)) * ((b*p^(r-1)).factorial : ℤ) := by
  have hpr : p^r = p^(r-1)*p := by rw [← pow_succ]; congr 1; omega
  have hpn : p ∣ b*p^r := ⟨b*p^(r-1), by rw [hpr]; ring⟩
  have hdiv : (b*p^r)/p = b*p^(r-1) := by
    rw [hpr, ← mul_assoc, Nat.mul_div_cancel _ hp.pos]
  have hs := factorial_split p (b*p^r) hp.one_lt
  rw [hdiv, Icc_filter_eq_range_filter p (b*p^r) hpn] at hs
  have hcast := congrArg (Nat.cast : ℕ → ℤ) hs
  push_cast at hcast
  rw [hcast]; ring

open Finset in
-- cast of the ℤ g-product to ZMod (p^(3*r)) is G0^b.
lemma g_prod_int_cast (p r : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) (b : ℕ) :
    ((∏ k ∈ (Finset.range (b*p^r)).filter (fun k => ¬ p ∣ k), (k:ℤ)) : ZMod (p^(3*r)))
      = (∏ ℓ ∈ (Finset.range (p^r)).filter (fun k => ¬ p ∣ k), ((ℓ:ℕ) : ZMod (p^(3*r))))^b := by
  push_cast
  exact g_prod_eq p r hp5 hr b

open Finset in
-- the ℤ g-product casts to a unit in ZMod (p^(3*r)).
lemma g_prod_int_isUnit (p r m : ℕ) [Fact p.Prime] :
    IsUnit ((∏ k ∈ (Finset.range m).filter (fun k => ¬ p ∣ k), (k:ℤ)) : ZMod (p^(3*r))) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p^(3*r)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  push_cast
  apply Finset.prod_induction _ IsUnit (fun a b => IsUnit.mul) isUnit_one
  intro k hk
  rw [Finset.mem_filter] at hk
  rw [ZMod.isUnit_iff_coprime]
  exact (((hp.coprime_iff_not_dvd).2 hk.2).symm).pow_right (3*r)

open Finset in
lemma g_prod_zmod_isUnit (p r m : ℕ) [Fact p.Prime] :
    IsUnit (∏ k ∈ (range m).filter (fun k => ¬ p ∣ k), ((k:ℕ) : ZMod (p^(3*r)))) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p^(3*r)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  apply Finset.prod_induction _ IsUnit (fun a b => IsUnit.mul) isUnit_one
  intro k hk; rw [Finset.mem_filter] at hk
  rw [ZMod.isUnit_iff_coprime]
  exact (((hp.coprime_iff_not_dvd).2 hk.2).symm).pow_right (3*r)

open Finset in
lemma even_case (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (r : ℕ) (hr : 0 < r) (μ : ℕ)
    (x y : ℤ)
    (hx : x * (((9*μ*p^r).factorial : ℤ) * (8*μ*p^r).factorial * (6*μ*p^r).factorial * (2*μ*p^r).factorial)
          = ((18*μ*p^r).factorial : ℤ) * (4*μ*p^r).factorial * (3*μ*p^r).factorial)
    (hy : y * (((9*μ*p^(r-1)).factorial : ℤ) * (8*μ*p^(r-1)).factorial * (6*μ*p^(r-1)).factorial * (2*μ*p^(r-1)).factorial)
          = ((18*μ*p^(r-1)).factorial : ℤ) * (4*μ*p^(r-1)).factorial * (3*μ*p^(r-1)).factorial) :
    x ≡ y [ZMOD ((p:ℤ)^(3*r))] := by
  haveI : Fact p.Prime := ⟨hp⟩
  set G0 := ∏ ℓ ∈ (range (p^r)).filter (fun k => ¬ p ∣ k), ((ℓ:ℕ) : ZMod (p^(3*r))) with hG0
  -- abbreviations for the seven g-products (over ℤ)
  set G18 := ∏ k ∈ (range (18*μ*p^r)).filter (fun k => ¬ p ∣ k), (k:ℤ) with hG18
  set G4  := ∏ k ∈ (range (4*μ*p^r)).filter (fun k => ¬ p ∣ k), (k:ℤ) with hG4
  set G3  := ∏ k ∈ (range (3*μ*p^r)).filter (fun k => ¬ p ∣ k), (k:ℤ) with hG3
  set G9  := ∏ k ∈ (range (9*μ*p^r)).filter (fun k => ¬ p ∣ k), (k:ℤ) with hG9
  set G8  := ∏ k ∈ (range (8*μ*p^r)).filter (fun k => ¬ p ∣ k), (k:ℤ) with hG8
  set G6  := ∏ k ∈ (range (6*μ*p^r)).filter (fun k => ¬ p ∣ k), (k:ℤ) with hG6
  set G2  := ∏ k ∈ (range (2*μ*p^r)).filter (fun k => ¬ p ∣ k), (k:ℤ) with hG2
  set E := 25 * μ * p^(r-1) with hE
  -- factorial splits
  have s18 := single_split p (18*μ) r hp hr
  have s4  := single_split p (4*μ) r hp hr
  have s3  := single_split p (3*μ) r hp hr
  have s9  := single_split p (9*μ) r hp hr
  have s8  := single_split p (8*μ) r hp hr
  have s6  := single_split p (6*μ) r hp hr
  have s2  := single_split p (2*μ) r hp hr
  rw [← hG18] at s18; rw [← hG4] at s4; rw [← hG3] at s3
  rw [← hG9] at s9; rw [← hG8] at s8; rw [← hG6] at s6; rw [← hG2] at s2
  -- power-collection identities
  have hpowN : (p:ℤ)^(18*μ*p^(r-1))*(p:ℤ)^(4*μ*p^(r-1))*(p:ℤ)^(3*μ*p^(r-1)) = (p:ℤ)^E := by
    rw [← pow_add, ← pow_add]; congr 1; rw [hE]; ring
  have hpowD : (p:ℤ)^(9*μ*p^(r-1))*(p:ℤ)^(8*μ*p^(r-1))*(p:ℤ)^(6*μ*p^(r-1))*(p:ℤ)^(2*μ*p^(r-1)) = (p:ℤ)^E := by
    rw [← pow_add, ← pow_add, ← pow_add]; congr 1; rw [hE]; ring
  set Nm := ((18*μ*p^(r-1)).factorial : ℤ) * (4*μ*p^(r-1)).factorial * (3*μ*p^(r-1)).factorial with hNm
  set Dm := ((9*μ*p^(r-1)).factorial : ℤ) * (8*μ*p^(r-1)).factorial * (6*μ*p^(r-1)).factorial * (2*μ*p^(r-1)).factorial with hDm
  have hDM : ((9*μ*p^r).factorial : ℤ) * (8*μ*p^r).factorial * (6*μ*p^r).factorial * (2*μ*p^r).factorial
      = (G9*G8*G6*G2) * (p:ℤ)^E * Dm := by
    rw [s9, s8, s6, s2, ← hpowD, hDm]; ring
  have hNM : ((18*μ*p^r).factorial : ℤ) * (4*μ*p^r).factorial * (3*μ*p^r).factorial
      = (G18*G4*G3) * (p:ℤ)^E * Nm := by
    rw [s18, s4, s3, ← hpowN, hNm]; ring
  -- cancel to get x * V = U * y
  have hcancel : x * (G9*G8*G6*G2) = (G18*G4*G3) * y := by
    have e1 : (x * (G9*G8*G6*G2)) * ((p:ℤ)^E * Dm) = ((G18*G4*G3) * y) * ((p:ℤ)^E * Dm) := by
      have h := hx
      rw [hDM, hNM] at h
      rw [← hy] at h
      linear_combination h
    have hne : ((p:ℤ)^E * Dm) ≠ 0 := by
      apply ne_of_gt; rw [hDm]; positivity
    exact mul_right_cancel₀ hne e1
  -- reduce mod p^(3*r)
  have hVU : ((G9*G8*G6*G2 : ℤ) : ZMod (p^(3*r))) = ((G18*G4*G3 : ℤ) : ZMod (p^(3*r))) := by
    rw [hG9, hG8, hG6, hG2, hG18, hG4, hG3]
    push_cast
    rw [g_prod_eq p r hp5 hr (9*μ), g_prod_eq p r hp5 hr (8*μ),
        g_prod_eq p r hp5 hr (6*μ), g_prod_eq p r hp5 hr (2*μ),
        g_prod_eq p r hp5 hr (18*μ), g_prod_eq p r hp5 hr (4*μ),
        g_prod_eq p r hp5 hr (3*μ), ← hG0,
        ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    congr 1; ring
  have hVunit : IsUnit ((G9*G8*G6*G2 : ℤ) : ZMod (p^(3*r))) := by
    rw [hG9, hG8, hG6, hG2]
    push_cast
    exact (((g_prod_zmod_isUnit p r (9*μ*p^r)).mul (g_prod_zmod_isUnit p r (8*μ*p^r))).mul
      (g_prod_zmod_isUnit p r (6*μ*p^r))).mul (g_prod_zmod_isUnit p r (2*μ*p^r))
  -- cast hcancel
  have hcast : (x : ZMod (p^(3*r))) * ↑(G9*G8*G6*G2) = ↑(G18*G4*G3) * (y : ZMod (p^(3*r))) := by
    rw [← Int.cast_mul, ← Int.cast_mul]; exact congrArg _ hcancel
  rw [← hVU] at hcast
  -- hcast : ↑x * ↑(G9*G8*G6*G2) = ↑(G9*G8*G6*G2) * ↑y
  have hxy : (x : ZMod (p^(3*r))) = (y : ZMod (p^(3*r))) := by
    rw [mul_comm (↑(G9*G8*G6*G2) : ZMod (p^(3*r))) (↑y)] at hcast
    obtain ⟨u, hu⟩ := hVunit
    rw [← hu] at hcast
    calc (x : ZMod (p^(3*r))) = ((x : ZMod (p^(3*r))) * ↑u) * ↑(u⁻¹) := by
            rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
      _ = ((y : ZMod (p^(3*r))) * ↑u) * ↑(u⁻¹) := by rw [hcast]
      _ = (y : ZMod (p^(3*r))) := by
            rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  rw [show ((p:ℤ)^(3*r)) = ((p^(3*r) : ℕ) : ℤ) by push_cast; ring, ← ZMod.intCast_eq_intCast_iff]
  exact hxy

open Finset in
lemma key_even (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (μ r : ℕ) (hr : 0 < r)
    (x y : ℤ) (hx : (x:ℝ) = a (2*μ*p^r)) (hy : (y:ℝ) = a (2*μ*p^(r-1))) :
    x ≡ y [ZMOD ((p:ℤ)^(3*r))] := by
  apply even_case p hp hp5 r hr μ x y
  · have key : (x:ℝ) * (((9*μ*p^r).factorial:ℝ)*(8*μ*p^r).factorial*(6*μ*p^r).factorial*(2*μ*p^r).factorial)
        = ((18*μ*p^r).factorial:ℝ)*(4*μ*p^r).factorial*(3*μ*p^r).factorial := by
      rw [hx, show (2*μ*p^r) = 2*(μ*p^r) by ring, show (9*μ*p^r) = 9*(μ*p^r) by ring,
          show (8*μ*p^r) = 8*(μ*p^r) by ring, show (6*μ*p^r) = 6*(μ*p^r) by ring,
          show (18*μ*p^r) = 18*(μ*p^r) by ring,
          show (4*μ*p^r) = 4*(μ*p^r) by ring, show (3*μ*p^r) = 3*(μ*p^r) by ring]
      exact a_even (μ*p^r)
    exact_mod_cast key
  · have key : (y:ℝ) * (((9*μ*p^(r-1)).factorial:ℝ)*(8*μ*p^(r-1)).factorial*(6*μ*p^(r-1)).factorial*(2*μ*p^(r-1)).factorial)
        = ((18*μ*p^(r-1)).factorial:ℝ)*(4*μ*p^(r-1)).factorial*(3*μ*p^(r-1)).factorial := by
      rw [hy, show (2*μ*p^(r-1)) = 2*(μ*p^(r-1)) by ring, show (9*μ*p^(r-1)) = 9*(μ*p^(r-1)) by ring,
          show (8*μ*p^(r-1)) = 8*(μ*p^(r-1)) by ring, show (6*μ*p^(r-1)) = 6*(μ*p^(r-1)) by ring,
          show (18*μ*p^(r-1)) = 18*(μ*p^(r-1)) by ring,
          show (4*μ*p^(r-1)) = 4*(μ*p^(r-1)) by ring, show (3*μ*p^(r-1)) = 3*(μ*p^(r-1)) by ring]
      exact a_even (μ*p^(r-1))
    exact_mod_cast key

/-! ### Odd case: reflection/doubling partition infrastructure -/

private def Uset (p r : ℕ) : Finset ℕ := (Finset.range (p^r)).filter (fun k => ¬ p ∣ k)
private def Lset (p r : ℕ) : Finset ℕ := (Uset p r).filter (fun k => 2*k ≤ p^r)

lemma mem_Uset {p r k : ℕ} : k ∈ Uset p r ↔ k < p^r ∧ ¬ p ∣ k := by
  simp [Uset, Finset.mem_filter, Finset.mem_range]
lemma mem_Lset {p r k : ℕ} : k ∈ Lset p r ↔ (k < p^r ∧ ¬ p ∣ k) ∧ 2*k ≤ p^r := by
  simp [Lset, mem_Uset, Finset.mem_filter, and_assoc]
lemma pr_odd (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ 2 ∣ p^r := by
  intro h
  have h2 : (2:ℕ) ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
  have : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm
  omega
lemma not_dvd_sub {p r k : ℕ} (hr : 0 < r) (hk : ¬ p ∣ k) (hle : k ≤ p^r) : ¬ p ∣ (p^r - k) := by
  intro hd; apply hk
  have := Nat.dvd_sub (dvd_pow_self p hr.ne') hd
  rwa [Nat.sub_sub_self hle] at this
lemma not_dvd_two_mul {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : ¬ p ∣ k) : ¬ p ∣ (2*k) := by
  intro hd
  rcases (hp.dvd_mul.1 hd) with h2 | h2
  · have : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2; omega
  · exact hk h2
lemma not_dvd_half {p a : ℕ} (h2 : 2 ∣ a) (hk : ¬ p ∣ a) : ¬ p ∣ (a/2) := by
  intro hd; apply hk
  have ha : a = 2*(a/2) := by omega
  rw [ha]; exact Dvd.dvd.mul_left hd 2

lemma prod_split_refl {M : Type*} [CommMonoid M] (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 0 < r)
    (f : ℕ → M) :
    ∏ k ∈ Uset p r, f k = (∏ ℓ ∈ Lset p r, f ℓ) * (∏ ℓ ∈ Lset p r, f (p^r - ℓ)) := by
  have hodd := pr_odd p r hp hp5
  set Uh := (Uset p r).filter (fun k => ¬ (2*k ≤ p^r)) with hUh
  have hsplit : (∏ ℓ ∈ Lset p r, f ℓ) * (∏ k ∈ Uh, f k) = ∏ k ∈ Uset p r, f k :=
    Finset.prod_filter_mul_prod_filter_not (Uset p r) (fun k => 2*k ≤ p^r) f
  rw [← hsplit]; congr 1
  refine Finset.prod_nbij' (fun k => p^r - k) (fun ℓ => p^r - ℓ) ?_ ?_ ?_ ?_ ?_
  · intro a ha; beta_reduce
    rw [hUh, Finset.mem_filter, mem_Uset] at ha
    obtain ⟨⟨halt, hand⟩, hnot⟩ := ha
    have ha0 : a ≠ 0 := by rintro rfl; exact hand (dvd_zero p)
    have hne : 2*a ≠ p^r := fun h => hodd ⟨a, by omega⟩
    rw [mem_Lset]
    exact ⟨⟨by omega, not_dvd_sub hr hand (le_of_lt halt)⟩, by omega⟩
  · intro a ha; beta_reduce
    rw [mem_Lset] at ha
    obtain ⟨⟨halt, hand⟩, hle⟩ := ha
    have ha0 : a ≠ 0 := by rintro rfl; exact hand (dvd_zero p)
    have hne : 2*a ≠ p^r := fun h => hodd ⟨a, by omega⟩
    rw [hUh, Finset.mem_filter, mem_Uset]
    exact ⟨⟨by omega, not_dvd_sub hr hand (le_of_lt halt)⟩, by omega⟩
  · intro a ha; beta_reduce
    rw [hUh, Finset.mem_filter, mem_Uset] at ha; omega
  · intro a ha; beta_reduce
    rw [mem_Lset] at ha; omega
  · intro a ha; beta_reduce; congr 1
    rw [hUh, Finset.mem_filter, mem_Uset] at ha; omega

lemma prod_split_double {M : Type*} [CommMonoid M] (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 0 < r)
    (f : ℕ → M) :
    ∏ k ∈ Uset p r, f k = (∏ ℓ ∈ Lset p r, f (2*ℓ)) * (∏ ℓ ∈ Lset p r, f (p^r - 2*ℓ)) := by
  have hodd := pr_odd p r hp hp5
  set O := (Uset p r).filter (fun k => ¬ (2 ∣ k)) with hO
  have hsplit : (∏ e ∈ (Uset p r).filter (fun k => 2 ∣ k), f e) * (∏ k ∈ O, f k) = ∏ k ∈ Uset p r, f k :=
    Finset.prod_filter_mul_prod_filter_not (Uset p r) (fun k => 2 ∣ k) f
  rw [← hsplit]; congr 1
  · refine Finset.prod_nbij' (fun e => e/2) (fun ℓ => 2*ℓ) ?_ ?_ ?_ ?_ ?_
    · intro a ha; beta_reduce
      rw [Finset.mem_filter, mem_Uset] at ha; obtain ⟨⟨halt, hand⟩, h2⟩ := ha
      obtain ⟨c, hc⟩ := h2
      rw [mem_Lset]
      exact ⟨⟨by omega, not_dvd_half ⟨c,hc⟩ hand⟩, by omega⟩
    · intro a ha; beta_reduce
      rw [mem_Lset] at ha; obtain ⟨⟨halt, hand⟩, hle⟩ := ha
      have hne : 2*a ≠ p^r := fun h => hodd ⟨a, by omega⟩
      rw [Finset.mem_filter, mem_Uset]
      exact ⟨⟨by omega, not_dvd_two_mul hp hp5 hand⟩, ⟨a, rfl⟩⟩
    · intro a ha; beta_reduce
      rw [Finset.mem_filter] at ha; obtain ⟨_, c, hc⟩ := ha; omega
    · intro a ha; beta_reduce; omega
    · intro a ha; beta_reduce; congr 1
      rw [Finset.mem_filter] at ha; obtain ⟨_, c, hc⟩ := ha; omega
  · refine Finset.prod_nbij' (fun o => (p^r - o)/2) (fun ℓ => p^r - 2*ℓ) ?_ ?_ ?_ ?_ ?_
    · intro a ha; beta_reduce
      rw [hO, Finset.mem_filter, mem_Uset] at ha; obtain ⟨⟨halt, hand⟩, hodd_a⟩ := ha
      obtain ⟨c, hc⟩ : 2 ∣ (p^r - a) := by omega
      rw [mem_Lset]
      exact ⟨⟨by omega, not_dvd_half ⟨c,hc⟩ (not_dvd_sub hr hand (le_of_lt halt))⟩, by omega⟩
    · intro a ha; beta_reduce
      rw [mem_Lset] at ha; obtain ⟨⟨halt, hand⟩, hle⟩ := ha
      have ha0 : a ≠ 0 := by rintro rfl; exact hand (dvd_zero p)
      rw [hO, Finset.mem_filter, mem_Uset]
      refine ⟨⟨by omega, not_dvd_sub hr (not_dvd_two_mul hp hp5 hand) hle⟩, ?_⟩
      intro hd; apply hodd; obtain ⟨c,hc⟩ := hd; exact ⟨c + a, by omega⟩
    · intro a ha; beta_reduce
      rw [hO, Finset.mem_filter, mem_Uset] at ha; obtain ⟨⟨halt, hand⟩, hodd_a⟩ := ha
      obtain ⟨c, hc⟩ : 2 ∣ (p^r - a) := by omega
      omega
    · intro a ha; beta_reduce
      rw [mem_Lset] at ha; obtain ⟨⟨halt,_⟩,hle⟩ := ha; omega
    · intro a ha; beta_reduce; congr 1
      rw [hO, Finset.mem_filter, mem_Uset] at ha; obtain ⟨⟨halt, hand⟩, hodd_a⟩ := ha
      obtain ⟨c, hc⟩ : 2 ∣ (p^r - a) := by omega
      omega

lemma sum_split_refl {M : Type*} [AddCommMonoid M] (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 0 < r)
    (f : ℕ → M) :
    ∑ k ∈ Uset p r, f k = (∑ ℓ ∈ Lset p r, f ℓ) + (∑ ℓ ∈ Lset p r, f (p^r - ℓ)) := by
  have hodd := pr_odd p r hp hp5
  set Uh := (Uset p r).filter (fun k => ¬ (2*k ≤ p^r)) with hUh
  have hsplit : (∑ ℓ ∈ Lset p r, f ℓ) + (∑ k ∈ Uh, f k) = ∑ k ∈ Uset p r, f k :=
    Finset.sum_filter_add_sum_filter_not (Uset p r) (fun k => 2*k ≤ p^r) f
  rw [← hsplit]; congr 1
  refine Finset.sum_nbij' (fun k => p^r - k) (fun ℓ => p^r - ℓ) ?_ ?_ ?_ ?_ ?_
  · intro a ha; beta_reduce
    rw [hUh, Finset.mem_filter, mem_Uset] at ha
    obtain ⟨⟨halt, hand⟩, hnot⟩ := ha
    have ha0 : a ≠ 0 := by rintro rfl; exact hand (dvd_zero p)
    have hne : 2*a ≠ p^r := fun h => hodd ⟨a, by omega⟩
    rw [mem_Lset]
    exact ⟨⟨by omega, not_dvd_sub hr hand (le_of_lt halt)⟩, by omega⟩
  · intro a ha; beta_reduce
    rw [mem_Lset] at ha
    obtain ⟨⟨halt, hand⟩, hle⟩ := ha
    have ha0 : a ≠ 0 := by rintro rfl; exact hand (dvd_zero p)
    have hne : 2*a ≠ p^r := fun h => hodd ⟨a, by omega⟩
    rw [hUh, Finset.mem_filter, mem_Uset]
    exact ⟨⟨by omega, not_dvd_sub hr hand (le_of_lt halt)⟩, by omega⟩
  · intro a ha; beta_reduce
    rw [hUh, Finset.mem_filter, mem_Uset] at ha; omega
  · intro a ha; beta_reduce
    rw [mem_Lset] at ha; omega
  · intro a ha; beta_reduce; congr 1
    rw [hUh, Finset.mem_filter, mem_Uset] at ha; omega

lemma Uset_eq_range_filter (p r : ℕ) : Uset p r = (Finset.range (p^r)).filter (fun k => ¬ p ∣ k) := rfl

lemma sum_L_invsq_zero (p r : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) :
    ∑ ℓ ∈ Lset p r, (((ℓ:ℕ) : ZMod (p^r)))⁻¹^2 = 0 := by
  have hp : p.Prime := Fact.out
  haveI : Fact (1 < p^r) := ⟨by
    have := hp.two_le; calc 1 < p := by omega
      _ ≤ p^r := Nat.le_self_pow hr.ne' p⟩
  have hrefl := sum_split_refl p r hp hp5 hr (fun k => (((k:ℕ) : ZMod (p^r)))⁻¹^2)
  have hU : ∑ k ∈ Uset p r, (((k:ℕ) : ZMod (p^r)))⁻¹^2 = 0 := by
    have := sum_range_inv_sq_zero p r 1 hp5 hr
    rw [one_mul] at this; rw [Uset_eq_range_filter]; exact this
  have heq : ∑ ℓ ∈ Lset p r, (((p^r - ℓ:ℕ) : ZMod (p^r)))⁻¹^2
        = ∑ ℓ ∈ Lset p r, (((ℓ:ℕ) : ZMod (p^r)))⁻¹^2 := by
    apply Finset.sum_congr rfl; intro ℓ hℓ
    rw [mem_Lset] at hℓ
    have hle : ℓ ≤ p^r := le_of_lt hℓ.1.1
    have hunit : IsUnit ((ℓ:ℕ) : ZMod (p^r)) := by
      rw [ZMod.isUnit_iff_coprime]; exact (((hp.coprime_iff_not_dvd).2 hℓ.1.2).symm).pow_right r
    have hcast : ((p^r - ℓ : ℕ) : ZMod (p^r)) = -((ℓ:ℕ) : ZMod (p^r)) := by
      have h0 : ((p^r : ℕ) : ZMod (p^r)) = 0 := ZMod.natCast_self _
      rw [Nat.cast_sub hle, h0]; ring
    rw [hcast]
    have hne : (-((ℓ:ℕ):ZMod (p^r))) * (-(((ℓ:ℕ):ZMod (p^r))⁻¹)) = 1 := by
      rw [show (-((ℓ:ℕ):ZMod (p^r)))*(-(((ℓ:ℕ):ZMod (p^r))⁻¹)) = ((ℓ:ℕ):ZMod (p^r)) * ((ℓ:ℕ):ZMod (p^r))⁻¹ from by ring]
      exact ZMod.mul_inv_of_unit _ hunit
    rw [ZMod.inv_eq_of_mul_eq_one _ _ _ hne, neg_sq]
  rw [heq, hU] at hrefl
  have h2u : IsUnit (2 : ZMod (p^r)) := (two_three_units p r hp5).1
  have h2S : (2 : ZMod (p^r)) * (∑ ℓ ∈ Lset p r, (((ℓ:ℕ) : ZMod (p^r)))⁻¹^2) = 0 := by
    rw [two_mul]; exact hrefl.symm
  exact (h2u.mul_right_eq_zero).mp h2S

-- Lemma A: p^(2r) * H2 = 0 in ZMod (p^(3r)),  H2 = ∑_L (ℓ⁻¹)²
lemma h2_reduce (p r : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) :
    ((p : ZMod (p^(3*r)))^(2*r)) * (∑ ℓ ∈ Lset p r, (((ℓ:ℕ) : ZMod (p^(3*r))))⁻¹^2) = 0 := by
  have hp : p.Prime := Fact.out
  set S3 := ∑ ℓ ∈ Lset p r, (((ℓ:ℕ) : ZMod (p^(3*r))))⁻¹^2 with hS3
  have hcast : (ZMod.castHom (pow_dvd_pow p (by omega : r ≤ 3*r)) (ZMod (p^r))) S3 = 0 := by
    rw [hS3, map_sum]
    have : ∀ ℓ ∈ Lset p r,
        (ZMod.castHom (pow_dvd_pow p (by omega : r ≤ 3*r)) (ZMod (p^r))) ((((ℓ:ℕ) : ZMod (p^(3*r))))⁻¹^2)
          = (((ℓ:ℕ) : ZMod (p^r)))⁻¹^2 := by
      intro ℓ hℓ
      rw [mem_Lset] at hℓ
      rw [map_pow]; congr 1
      exact cast_inv_reduce_gen p r (3*r) ℓ (by omega) hℓ.1.2
    rw [Finset.sum_congr rfl this]
    exact sum_L_invsq_zero p r hp5 hr
  have := pk_reduce_zero' p (3*r) r (by omega) S3 hcast
  rwa [show 3*r - r = 2*r by omega] at this

lemma card_mult_range (p r : ℕ) (hp : p.Prime) (hr : 0 < r) :
    ((Finset.range (p^r)).filter (fun k => p ∣ k)).card = p^(r-1) := by
  have hpr : p^r = p^(r-1) * p := by rw [← pow_succ]; congr 1; omega
  have himg : (Finset.range (p^r)).filter (fun k => p ∣ k) = (Finset.range (p^(r-1))).image (fun j => p*j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, j, rfl⟩
      refine ⟨j, ?_, rfl⟩
      rw [hpr, mul_comm p j] at hk
      by_contra h; push_neg at h
      have : p^(r-1)*p ≤ j*p := Nat.mul_le_mul_right p h
      omega
    · rintro ⟨j, hj, rfl⟩
      refine ⟨?_, j, rfl⟩
      rw [hpr, mul_comm (p^(r-1)) p]
      exact (Nat.mul_lt_mul_left hp.pos).mpr hj
  rw [himg, Finset.card_image_of_injective _ (by intro a b h; exact Nat.eq_of_mul_eq_mul_left hp.pos h),
      Finset.card_range]

lemma card_U (p r : ℕ) (hp : p.Prime) (hr : 0 < r) : (Uset p r).card = p^r - p^(r-1) := by
  have hkey := Finset.filter_card_add_filter_neg_card_eq_card (s := Finset.range (p^r)) (p := fun k => p ∣ k)
  rw [card_mult_range p r hp hr, Finset.card_range] at hkey
  rw [Uset_eq_range_filter]; omega

lemma card_L (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 0 < r) :
    2 * (Lset p r).card = p^r - p^(r-1) := by
  have h := sum_split_refl p r hp hp5 hr (fun _ => (1:ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  rw [card_U p r hp hr] at h; omega

-- unit facts
lemma L_cast_unit {p r ℓ : ℕ} [Fact p.Prime] (hℓ : ℓ ∈ Lset p r) :
    IsUnit ((ℓ:ℕ) : ZMod (p^(3*r))) := by
  have hp : p.Prime := Fact.out
  rw [mem_Lset] at hℓ
  rw [ZMod.isUnit_iff_coprime]; exact (((hp.coprime_iff_not_dvd).2 hℓ.1.2).symm).pow_right (3*r)

lemma AR1 (p r : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) :
    (∏ ℓ ∈ Lset p r, ((ℓ:ℕ):ZMod (p^(3*r))))
      * (∏ ℓ ∈ Lset p r, (1 - (p:ZMod (p^(3*r)))^r * ((ℓ:ℕ):ZMod (p^(3*r)))⁻¹))
      = ((-1:ZMod (p^(3*r))))^(Lset p r).card * (∏ ℓ ∈ Lset p r, ((p^r - ℓ:ℕ):ZMod (p^(3*r)))) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_neg]
  apply Finset.prod_congr rfl
  intro ℓ hℓ
  have hle : ℓ ≤ p^r := le_of_lt (mem_Lset.1 hℓ).1.1
  have hll := ZMod.mul_inv_of_unit _ (L_cast_unit hℓ)
  have hcast : ((p^r - ℓ:ℕ):ZMod (p^(3*r))) = (p:ZMod (p^(3*r)))^r - ((ℓ:ℕ):ZMod (p^(3*r))) := by
    rw [Nat.cast_sub hle, Nat.cast_pow]
  rw [hcast, mul_sub, mul_one, mul_comm ((p:ZMod (p^(3*r)))^r) _, ← mul_assoc, hll, one_mul]
  ring

lemma ARh (p r : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) :
    (∏ ℓ ∈ Lset p r, ((2*ℓ:ℕ):ZMod (p^(3*r))))
      * (∏ ℓ ∈ Lset p r, (1 - (p:ZMod (p^(3*r)))^r * ((2*ℓ:ℕ):ZMod (p^(3*r)))⁻¹))
      = ((-1:ZMod (p^(3*r))))^(Lset p r).card * (∏ ℓ ∈ Lset p r, ((p^r - 2*ℓ:ℕ):ZMod (p^(3*r)))) := by
  have hp : p.Prime := Fact.out
  rw [← Finset.prod_mul_distrib, ← Finset.prod_neg]
  apply Finset.prod_congr rfl
  intro ℓ hℓ
  have hℓ' := mem_Lset.1 hℓ
  have hle : 2*ℓ ≤ p^r := hℓ'.2
  have hunit : IsUnit ((2*ℓ:ℕ):ZMod (p^(3*r))) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (((hp.coprime_iff_not_dvd).2 (not_dvd_two_mul hp hp5 hℓ'.1.2)).symm).pow_right (3*r)
  have hll := ZMod.mul_inv_of_unit _ hunit
  have hcast : ((p^r - 2*ℓ:ℕ):ZMod (p^(3*r))) = (p:ZMod (p^(3*r)))^r - ((2*ℓ:ℕ):ZMod (p^(3*r))) := by
    rw [Nat.cast_sub hle, Nat.cast_pow]
  rw [hcast, mul_sub, mul_one, mul_comm ((p:ZMod (p^(3*r)))^r) _, ← mul_assoc, hll, one_mul]
  ring

lemma split1 (p r : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) :
    (∏ k ∈ Uset p r, ((k:ℕ):ZMod (p^(3*r))))
      = (∏ ℓ ∈ Lset p r, ((ℓ:ℕ):ZMod (p^(3*r)))) * (∏ ℓ ∈ Lset p r, ((p^r - ℓ:ℕ):ZMod (p^(3*r)))) := by
  exact prod_split_refl p r Fact.out hp5 hr (fun k => ((k:ℕ):ZMod (p^(3*r))))

lemma split2 (p r : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) :
    (∏ k ∈ Uset p r, ((k:ℕ):ZMod (p^(3*r))))
      = (∏ ℓ ∈ Lset p r, ((2*ℓ:ℕ):ZMod (p^(3*r)))) * (∏ ℓ ∈ Lset p r, ((p^r - 2*ℓ:ℕ):ZMod (p^(3*r)))) := by
  exact prod_split_double p r Fact.out hp5 hr (fun k => ((k:ℕ):ZMod (p^(3*r))))

lemma P2_eq (p r : ℕ) [Fact p.Prime] :
    (∏ ℓ ∈ Lset p r, ((2*ℓ:ℕ):ZMod (p^(3*r))))
      = (2:ZMod (p^(3*r)))^(Lset p r).card * (∏ ℓ ∈ Lset p r, ((ℓ:ℕ):ZMod (p^(3*r)))) := by
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro ℓ _; push_cast; ring

lemma inv_two_mul (p r ℓ : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hℓ : ℓ ∈ Lset p r) :
    ((2*ℓ:ℕ):ZMod (p^(3*r)))⁻¹ = (2:ZMod (p^(3*r)))⁻¹ * ((ℓ:ℕ):ZMod (p^(3*r)))⁻¹ := by
  have h2u : IsUnit (2:ZMod (p^(3*r))) := (two_three_units p (3*r) hp5).1
  have hlu := L_cast_unit hℓ
  have hmul : ((2*ℓ:ℕ):ZMod (p^(3*r))) * ((2:ZMod (p^(3*r)))⁻¹ * ((ℓ:ℕ):ZMod (p^(3*r)))⁻¹) = 1 := by
    push_cast
    rw [show (2:ZMod (p^(3*r))) * (ℓ:ZMod (p^(3*r))) * ((2:ZMod (p^(3*r)))⁻¹ * ((ℓ:ℕ):ZMod (p^(3*r)))⁻¹)
      = ((2:ZMod (p^(3*r))) * (2:ZMod (p^(3*r)))⁻¹) * (((ℓ:ℕ):ZMod (p^(3*r))) * ((ℓ:ℕ):ZMod (p^(3*r)))⁻¹) by ring,
      ZMod.mul_inv_of_unit _ h2u, ZMod.mul_inv_of_unit _ hlu, mul_one]
  exact ZMod.inv_eq_of_mul_eq_one _ _ _ hmul

lemma Rh_sq (p r : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) :
    (∏ ℓ ∈ Lset p r, (1 - (p:ZMod (p^(3*r)))^r * ((2*ℓ:ℕ):ZMod (p^(3*r)))⁻¹))^2
      = ∏ ℓ ∈ Lset p r, (1 - (p:ZMod (p^(3*r)))^r * ((ℓ:ℕ):ZMod (p^(3*r)))⁻¹) := by
  set N := p^(3*r) with hN
  set c := (p:ZMod N)^r with hc
  set x : ℕ → ZMod N := fun ℓ => -(c * ((ℓ:ℕ):ZMod N)⁻¹) with hx
  set y : ℕ → ZMod N := fun ℓ => (2:ZMod N)⁻¹ * x ℓ with hy
  have h2u : IsUnit (2:ZMod N) := (two_three_units p (3*r) hp5).1
  have hc3 : c^3 = 0 := by
    rw [hc, ← pow_mul, hN, show r*3 = 3*r by ring, ← Nat.cast_pow, ZMod.natCast_self]
  -- rewrite both products as ∏(1+·)
  have hR1 : (∏ ℓ ∈ Lset p r, (1 - c * ((ℓ:ℕ):ZMod N)⁻¹)) = ∏ ℓ ∈ Lset p r, (1 + x ℓ) := by
    apply Finset.prod_congr rfl; intro ℓ _; rw [hx]; ring
  have hRh : (∏ ℓ ∈ Lset p r, (1 - c * ((2*ℓ:ℕ):ZMod N)⁻¹)) = ∏ ℓ ∈ Lset p r, (1 + y ℓ) := by
    apply Finset.prod_congr rfl; intro ℓ hℓ
    rw [inv_two_mul p r ℓ hp5 hℓ, hy, hx]; ring
  -- triple products vanish
  have htx : ∀ i j k, x i * x j * x k = 0 := by
    intro i j k; rw [hx]
    rw [show (-(c * ((i:ℕ):ZMod N)⁻¹)) * (-(c * ((j:ℕ):ZMod N)⁻¹)) * (-(c * ((k:ℕ):ZMod N)⁻¹))
      = -(c^3 * (((i:ℕ):ZMod N)⁻¹ * ((j:ℕ):ZMod N)⁻¹ * ((k:ℕ):ZMod N)⁻¹)) by ring, hc3, zero_mul, neg_zero]
  have hty : ∀ i j k, y i * y j * y k = 0 := by
    intro i j k; rw [hy]
    rw [show ((2:ZMod N)⁻¹ * x i) * ((2:ZMod N)⁻¹ * x j) * ((2:ZMod N)⁻¹ * x k)
      = ((2:ZMod N)⁻¹)^3 * (x i * x j * x k) by ring, htx, mul_zero]
  set Sx := ∑ ℓ ∈ Lset p r, x ℓ with hSx
  set Sy := ∑ ℓ ∈ Lset p r, y ℓ with hSy
  -- Sx2 = 0
  have hSx2 : ∑ ℓ ∈ Lset p r, (x ℓ)^2 = 0 := by
    have hc2 : ∀ ℓ ∈ Lset p r, (x ℓ)^2 = (p:ZMod N)^(2*r) * (((ℓ:ℕ):ZMod N)⁻¹)^2 := by
      intro ℓ _; rw [hx, show (2*r) = r*2 by ring, pow_mul, ← hc]; ring
    rw [Finset.sum_congr rfl hc2, ← Finset.mul_sum]
    exact h2_reduce p r hp5 hr
  have hSy2 : ∑ ℓ ∈ Lset p r, (y ℓ)^2 = 0 := by
    have : ∀ ℓ ∈ Lset p r, (y ℓ)^2 = ((2:ZMod N)⁻¹)^2 * (x ℓ)^2 := by intro ℓ _; rw [hy]; ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hSx2, mul_zero]
  -- Sx = 2 * Sy
  have hSxSy : Sx = 2 * Sy := by
    rw [hSx, hSy, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro ℓ _
    show x ℓ = 2 * ((2:ZMod N)⁻¹ * x ℓ)
    rw [← mul_assoc, ZMod.mul_inv_of_unit _ h2u, one_mul]
  -- Sy^3 = 0
  have hSxc : Sx = c * (∑ ℓ ∈ Lset p r, (-(((ℓ:ℕ):ZMod N)⁻¹))) := by
    rw [hSx, Finset.mul_sum]; apply Finset.sum_congr rfl; intro ℓ _
    show x ℓ = c * (-(((ℓ:ℕ):ZMod N)⁻¹)); rw [hx]; ring
  have hSx3 : Sx^3 = 0 := by rw [hSxc, mul_pow, hc3, zero_mul]
  have hSyeq : Sy = (2:ZMod N)⁻¹ * Sx := by
    rw [hSxSy, ← mul_assoc,
      show (2:ZMod N)⁻¹ * 2 = 1 from by rw [mul_comm]; exact ZMod.mul_inv_of_unit _ h2u, one_mul]
  have hSy3 : Sy^3 = 0 := by rw [hSyeq, mul_pow, hSx3, mul_zero]
  -- expansions
  have e2R1 : 2 * (∏ ℓ ∈ Lset p r, (1 + x ℓ)) = 2 + 2*Sx + Sx^2 := by
    rw [two_mul_prod_one_add _ x htx, hSx2, ← hSx]; ring
  have e2Rh : 2 * (∏ ℓ ∈ Lset p r, (1 + y ℓ)) = 2 + 2*Sy + Sy^2 := by
    rw [two_mul_prod_one_add _ y hty, hSy2, ← hSy]; ring
  -- combine
  rw [hRh, hR1]
  set R1 := ∏ ℓ ∈ Lset p r, (1 + x ℓ) with hR1def
  set Rh := ∏ ℓ ∈ Lset p r, (1 + y ℓ) with hRhdef
  have key : (2*Rh)^2 = 4 * R1 := by
    have lhs : (2*Rh)^2 = (2 + 2*Sy + Sy^2)^2 := by rw [e2Rh]
    have rhs : (4:ZMod N) * R1 = 2*(2 + 2*Sx + Sx^2) := by rw [← e2R1]; ring
    rw [lhs, rhs, hSxSy]
    linear_combination (4 + Sy) * hSy3
  have h4u : IsUnit (4:ZMod N) := by
    have : (4:ZMod N) = 2*2 := by norm_num
    rw [this]; exact h2u.mul h2u
  have hz : (4:ZMod N) * (Rh^2 - R1) = 0 := by
    have : (2*Rh)^2 = 4 * Rh^2 := by ring
    rw [this] at key; linear_combination key
  have := (h4u.mul_right_eq_zero).mp hz
  linear_combination this

lemma G0_eq (p r : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) :
    (∏ k ∈ Uset p r, ((k:ℕ):ZMod (p^(3*r))))
      = ((-1:ZMod (p^(3*r))))^(Lset p r).card * (4:ZMod (p^(3*r)))^(p^r - p^(r-1))
        * (∏ ℓ ∈ Lset p r, ((ℓ:ℕ):ZMod (p^(3*r))))^2 := by
  set N := p^(3*r) with hN
  set c := (p:ZMod N)^r with hc
  set h := (Lset p r).card with hh
  set A := ∏ ℓ ∈ Lset p r, ((ℓ:ℕ):ZMod N) with hA
  set Bp := ∏ ℓ ∈ Lset p r, ((p^r - ℓ:ℕ):ZMod N) with hBp
  set Cp := ∏ ℓ ∈ Lset p r, ((p^r - 2*ℓ:ℕ):ZMod N) with hCp
  set P2 := ∏ ℓ ∈ Lset p r, ((2*ℓ:ℕ):ZMod N) with hP2
  set R1 := ∏ ℓ ∈ Lset p r, (1 - c * ((ℓ:ℕ):ZMod N)⁻¹) with hR1
  set Rh := ∏ ℓ ∈ Lset p r, (1 - c * ((2*ℓ:ℕ):ZMod N)⁻¹) with hRh
  set G0 := ∏ k ∈ Uset p r, ((k:ℕ):ZMod N) with hG0
  have hc3 : c^3 = 0 := by
    rw [hc, ← pow_mul, hN, show r*3 = 3*r by ring, ← Nat.cast_pow, ZMod.natCast_self]
  have hs1 : G0 = A * Bp := split1 p r hp5 hr
  have hs2 : G0 = P2 * Cp := split2 p r hp5 hr
  have har1 : A * R1 = (-1:ZMod N)^h * Bp := AR1 p r hp5 hr
  have harh : P2 * Rh = (-1:ZMod N)^h * Cp := ARh p r hp5 hr
  have hP2A : P2 = (2:ZMod N)^h * A := P2_eq p r
  have hrhsq : Rh^2 = R1 := Rh_sq p r hp5 hr
  -- units
  have hAunit : IsUnit A := by
    rw [hA]
    exact Finset.prod_induction _ IsUnit (fun a b => IsUnit.mul) isUnit_one (fun ℓ hℓ => L_cast_unit hℓ)
  have hR1unit : IsUnit R1 := by
    rw [hR1]
    refine Finset.prod_induction _ IsUnit (fun a b => IsUnit.mul) isUnit_one ?_
    intro ℓ _
    refine IsUnit.of_mul_eq_one (1 + c*((ℓ:ℕ):ZMod N)⁻¹ + (c*((ℓ:ℕ):ZMod N)⁻¹)^2) ?_
    have : (c*((ℓ:ℕ):ZMod N)⁻¹)^3 = 0 := by rw [mul_pow, hc3, zero_mul]
    linear_combination -this
  have hRhunit : IsUnit Rh := by
    have : IsUnit (Rh * Rh) := by rw [← sq, hrhsq]; exact hR1unit
    exact isUnit_of_mul_isUnit_left this
  -- A^2*R1 = (-1)^h G0 ; P2^2*Rh = (-1)^h G0
  have e1 : A^2 * R1 = (-1:ZMod N)^h * G0 := by
    rw [hs1, show A^2 * R1 = A * (A * R1) by ring, har1]; ring
  have e2 : P2^2 * Rh = (-1:ZMod N)^h * G0 := by
    rw [hs2, show P2^2 * Rh = P2 * (P2 * Rh) by ring, harh]; ring
  have hP2sq : P2^2 = (2:ZMod N)^(2*h) * A^2 := by
    rw [hP2A, mul_pow, ← pow_mul, show h*2 = 2*h by ring]
  -- R1 = 2^{2h} Rh
  have hR1Rh : R1 = (2:ZMod N)^(2*h) * Rh := by
    have hAR : A^2 * R1 = P2^2 * Rh := by rw [e1, e2]
    have : A^2 * R1 = A^2 * ((2:ZMod N)^(2*h) * Rh) := by rw [hAR, hP2sq]; ring
    exact (hAunit.pow 2).mul_left_cancel this
  -- Rh = 2^{2h}
  have hRhval : Rh = (2:ZMod N)^(2*h) := by
    have : Rh * Rh = Rh * (2:ZMod N)^(2*h) := by rw [← sq, hrhsq, hR1Rh]; ring
    exact hRhunit.mul_left_cancel this
  have hR1val : R1 = (2:ZMod N)^(4*h) := by
    rw [hR1Rh, hRhval, ← pow_add]; congr 1; ring
  -- G0 = (-1)^h A^2 R1
  have hG0val : G0 = (-1:ZMod N)^h * (A^2 * R1) := by
    have h11 : ((-1:ZMod N)^h)*((-1:ZMod N)^h) = 1 := by
      rw [← pow_add, show h + h = 2*h by ring, pow_mul, neg_one_sq, one_pow]
    calc G0 = (((-1:ZMod N)^h)*((-1:ZMod N)^h)) * G0 := by rw [h11]; ring
      _ = (-1:ZMod N)^h * ((-1:ZMod N)^h * G0) := by ring
      _ = (-1:ZMod N)^h * (A^2 * R1) := by rw [e1]
  rw [hG0val, hR1val]
  have h4 : (2:ZMod N)^(4*h) = (4:ZMod N)^(p^r - p^(r-1)) := by
    have hcard := card_L p r Fact.out hp5 hr
    rw [show (4:ZMod N) = 2^2 by norm_num, ← pow_mul]
    congr 1
    rw [← hcard]; ring
  rw [h4]; ring

lemma blockU (p r q : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) :
    ∏ k ∈ Uset p r, ((q*p^r + k:ℕ):ZMod (p^(3*r))) = ∏ k ∈ Uset p r, ((k:ℕ):ZMod (p^(3*r))) := by
  rw [Uset_eq_range_filter]; exact block_eq_G0 p r hp5 hr q

lemma prod_one_add_pw {ι N : Type*} [CommRing N] (s : Finset ι) (w : ι → N)
    (hpw : ∀ i j, w i * w j = 0) : ∏ i ∈ s, (1 + w i) = 1 + ∑ i ∈ s, w i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
    have h1 : w a * (∑ i ∈ s, w i) = 0 := by
      rw [Finset.mul_sum]; apply Finset.sum_eq_zero; intro i _; exact hpw a i
    linear_combination h1

lemma PB_step (p r q : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) :
    (∏ ℓ ∈ Lset p r, ((q*p^r+ℓ:ℕ):ZMod (p^(3*r))))
      = (4:ZMod (p^(3*r)))^(p^r - p^(r-1)) * (∏ ℓ ∈ Lset p r, (((q+1)*p^r+ℓ:ℕ):ZMod (p^(3*r)))) := by
  set N := p^(3*r) with hN
  set c := (p:ZMod N)^r with hc
  set qq := ((q:ℕ):ZMod N) with hqq
  set h := (Lset p r).card with hh
  set A := ∏ ℓ ∈ Lset p r, ((ℓ:ℕ):ZMod N) with hA
  set Aq := ∏ ℓ ∈ Lset p r, (((q+1)*p^r - ℓ:ℕ):ZMod N) with hAq
  set G0 := ∏ k ∈ Uset p r, ((k:ℕ):ZMod N) with hG0
  set PBq := ∏ ℓ ∈ Lset p r, ((q*p^r+ℓ:ℕ):ZMod N) with hPBq
  set PBq1 := ∏ ℓ ∈ Lset p r, (((q+1)*p^r+ℓ:ℕ):ZMod N) with hPBq1
  set w : ℕ → ZMod N := fun ℓ => -(((qq+1)^2 * c^2) * (((ℓ:ℕ):ZMod N)⁻¹)^2) with hw
  have hc3 : c^3 = 0 := by
    rw [hc, ← pow_mul, hN, show r*3 = 3*r by ring, ← Nat.cast_pow, ZMod.natCast_self]
  have hc4 : c^4 = 0 := by rw [show (4:ℕ) = 3+1 from rfl, pow_add, hc3, zero_mul]
  have hc2H : c^2 * (∑ ℓ ∈ Lset p r, (((ℓ:ℕ):ZMod N)⁻¹)^2) = 0 := by
    rw [show c^2 = (p:ZMod N)^(2*r) from by rw [hc, ← pow_mul]; congr 1; ring]
    exact h2_reduce p r hp5 hr
  -- (b)
  have hb : PBq * Aq = G0 := by
    have hsplit := prod_split_refl p r Fact.out hp5 hr (fun k => ((q*p^r + k:ℕ):ZMod N))
    have hblk := blockU p r q hp5 hr
    have hAq2 : Aq = ∏ ℓ ∈ Lset p r, ((q*p^r + (p^r - ℓ):ℕ):ZMod N) := by
      rw [hAq]; apply Finset.prod_congr rfl; intro ℓ hℓ
      congr 1; rw [mem_Lset] at hℓ
      have h1 : (q+1)*p^r = q*p^r + p^r := by ring
      have h2 : ℓ < p^r := hℓ.1.1
      omega
    rw [hPBq, hAq2, hG0, ← hblk]
    exact hsplit.symm
  -- (d)
  have hpw : ∀ i j, w i * w j = 0 := by
    intro i j; rw [hw]
    rw [show (-(((qq+1)^2 * c^2) * (((i:ℕ):ZMod N)⁻¹)^2)) * (-(((qq+1)^2 * c^2) * (((j:ℕ):ZMod N)⁻¹)^2))
      = ((qq+1)^4 * (((i:ℕ):ZMod N)⁻¹)^2 * (((j:ℕ):ZMod N)⁻¹)^2) * c^4 by ring, hc4, mul_zero]
  have hsumw : ∑ ℓ ∈ Lset p r, w ℓ = 0 := by
    have key : ∀ ℓ, w ℓ = (-((qq+1)^2 * c^2)) * (((ℓ:ℕ):ZMod N)⁻¹)^2 := fun ℓ => by rw [hw]; ring
    rw [Finset.sum_congr rfl (fun ℓ _ => key ℓ), ← Finset.mul_sum,
      show (-((qq+1)^2 * c^2)) * (∑ ℓ ∈ Lset p r, (((ℓ:ℕ):ZMod N)⁻¹)^2)
        = -((qq+1)^2 * (c^2 * ∑ ℓ ∈ Lset p r, (((ℓ:ℕ):ZMod N)⁻¹)^2)) by ring, hc2H, mul_zero, neg_zero]
  have hd : PBq1 * Aq = (-1:ZMod N)^h * A^2 := by
    rw [hPBq1, hAq, ← Finset.prod_mul_distrib]
    have htermeq : ∀ ℓ ∈ Lset p r,
        ((((q+1)*p^r+ℓ:ℕ)):ZMod N) * ((((q+1)*p^r - ℓ:ℕ)):ZMod N)
          = (-(((ℓ:ℕ):ZMod N))^2) * (1 + w ℓ) := by
      intro ℓ hℓ
      have hlt : ℓ < p^r := (mem_Lset.1 hℓ).1.1
      have hple : p^r ≤ (q+1)*p^r := le_mul_of_one_le_left (Nat.zero_le _) (by omega)
      have hle : ℓ ≤ (q+1)*p^r := by omega
      have hcast1 : ((((q+1)*p^r+ℓ:ℕ)):ZMod N) = (qq+1)*c + ((ℓ:ℕ):ZMod N) := by
        rw [hqq, hc]; push_cast; ring
      have hcast2 : ((((q+1)*p^r-ℓ:ℕ)):ZMod N) = (qq+1)*c - ((ℓ:ℕ):ZMod N) := by
        rw [Nat.cast_sub hle, hqq, hc]; push_cast; ring
      have hll : ((ℓ:ℕ):ZMod N)^2 * (((ℓ:ℕ):ZMod N)⁻¹)^2 = 1 := by
        rw [← mul_pow, ZMod.mul_inv_of_unit _ (L_cast_unit hℓ), one_pow]
      rw [hcast1, hcast2, hw]
      linear_combination (-(qq+1)^2 * c^2) * hll
    rw [Finset.prod_congr rfl htermeq, Finset.prod_mul_distrib, Finset.prod_neg,
      prod_one_add_pw _ w hpw, hsumw, add_zero, mul_one, Finset.prod_pow, ← hA, ← hh]
  -- assemble
  have hG0eq : G0 = (-1:ZMod N)^h * (4:ZMod N)^(p^r - p^(r-1)) * A^2 := G0_eq p r hp5 hr
  have hAqunit : IsUnit Aq := by
    rw [hAq]
    refine Finset.prod_induction _ IsUnit (fun a b => IsUnit.mul) isUnit_one ?_
    intro ℓ hℓ
    rw [mem_Lset] at hℓ
    rw [ZMod.isUnit_iff_coprime]
    refine (((Fact.out : p.Prime).coprime_iff_not_dvd).2 ?_).symm.pow_right (3*r)
    intro hd2
    apply hℓ.1.2
    have hpr : p ∣ (q+1)*p^r := Dvd.dvd.mul_left (dvd_pow_self p hr.ne') (q+1)
    have hle : ℓ ≤ (q+1)*p^r := le_trans (le_of_lt hℓ.1.1) (le_mul_of_one_le_left (Nat.zero_le _) (by omega))
    have := Nat.dvd_sub hpr hd2
    rwa [Nat.sub_sub_self hle] at this
  have hfin : Aq * PBq = Aq * ((4:ZMod N)^(p^r-p^(r-1)) * PBq1) := by
    rw [mul_comm Aq PBq, hb, hG0eq, mul_comm Aq ((4:ZMod N)^(p^r-p^(r-1)) * PBq1),
      show ((4:ZMod N)^(p^r-p^(r-1)) * PBq1) * Aq = (4:ZMod N)^(p^r-p^(r-1)) * (PBq1 * Aq) by ring, hd]
    ring
  exact hAqunit.mul_left_cancel hfin

lemma PB_telescope (p r a k : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) :
    (∏ ℓ ∈ Lset p r, ((a*p^r+ℓ:ℕ):ZMod (p^(3*r))))
      = (4:ZMod (p^(3*r)))^(k*(p^r - p^(r-1)))
        * (∏ ℓ ∈ Lset p r, (((a+k)*p^r+ℓ:ℕ):ZMod (p^(3*r)))) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih, PB_step p r (a+k) hp5 hr, ← mul_assoc, ← pow_add,
        show k*(p^r-p^(r-1)) + (p^r-p^(r-1)) = (k+1)*(p^r-p^(r-1)) by ring,
        show a+k+1 = a+(k+1) by ring]

lemma Gamma_half (k : ℕ) :
    Real.Gamma ((k:ℝ) + 1/2)
      = ((2*k).factorial : ℝ) / (4^k * (k.factorial : ℝ)) * Real.sqrt Real.pi := by
  induction k with
  | zero => norm_num [Real.Gamma_one_half_eq]
  | succ k ih =>
    have hk : ((k:ℝ) + 1/2) ≠ 0 := by positivity
    have e1 : ((k+1:ℕ):ℝ) + 1/2 = ((k:ℝ)+1/2) + 1 := by push_cast; ring
    rw [e1, Real.Gamma_add_one hk, ih]
    have f1 : (2*(k+1)).factorial = (2*k+2)*((2*k+1)*(2*k).factorial) := by
      rw [show 2*(k+1) = (2*k+1)+1 by ring, Nat.factorial_succ,
          show 2*k+1 = (2*k)+1 by ring, Nat.factorial_succ]
    have f2 : (k+1).factorial = (k+1)*k.factorial := Nat.factorial_succ k
    have hkf : (0:ℝ) < (k.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos k
    rw [f1, f2, pow_succ]
    push_cast
    field_simp
    ring

lemma a_odd (μ : ℕ) :
    a (2*μ+1) * (((8*μ+4).factorial:ℝ) * ((2*μ+1).factorial:ℝ) * ((3*μ+1).factorial:ℝ))
      = (4:ℝ)^(6*μ+3) * ((4*μ+2).factorial:ℝ) * ((9*μ+4).factorial:ℝ) := by
  have g1 : Real.Gamma (9 * ((2*μ+1 : ℕ) : ℝ) + 1) = ((18*μ+9).factorial : ℝ) := by
    rw [show (9 : ℝ) * ((2*μ+1 : ℕ) : ℝ) + 1 = ((18*μ+9 : ℕ) : ℝ) + 1 by push_cast; ring,
        Real.Gamma_nat_eq_factorial]
  have g2 : Real.Gamma (2 * ((2*μ+1 : ℕ) : ℝ) + 1) = ((4*μ+2).factorial : ℝ) := by
    rw [show (2 : ℝ) * ((2*μ+1 : ℕ) : ℝ) + 1 = ((4*μ+2 : ℕ) : ℝ) + 1 by push_cast; ring,
        Real.Gamma_nat_eq_factorial]
  have g3 : Real.Gamma (3/2 * ((2*μ+1 : ℕ) : ℝ) + 1)
      = ((6*μ+4).factorial : ℝ) / (4^(3*μ+2) * ((3*μ+2).factorial:ℝ)) * Real.sqrt Real.pi := by
    rw [show (3/2 : ℝ) * ((2*μ+1 : ℕ) : ℝ) + 1 = ((3*μ+2 : ℕ) : ℝ) + 1/2 by push_cast; ring,
        Gamma_half (3*μ+2), show 2*(3*μ+2) = 6*μ+4 by ring]
  have g4 : Real.Gamma (9/2 * ((2*μ+1 : ℕ) : ℝ) + 1)
      = ((18*μ+10).factorial : ℝ) / (4^(9*μ+5) * ((9*μ+5).factorial:ℝ)) * Real.sqrt Real.pi := by
    rw [show (9/2 : ℝ) * ((2*μ+1 : ℕ) : ℝ) + 1 = ((9*μ+5 : ℕ) : ℝ) + 1/2 by push_cast; ring,
        Gamma_half (9*μ+5), show 2*(9*μ+5) = 18*μ+10 by ring]
  have g5 : Real.Gamma (4 * ((2*μ+1 : ℕ) : ℝ) + 1) = ((8*μ+4).factorial : ℝ) := by
    rw [show (4 : ℝ) * ((2*μ+1 : ℕ) : ℝ) + 1 = ((8*μ+4 : ℕ) : ℝ) + 1 by push_cast; ring,
        Real.Gamma_nat_eq_factorial]
  have g6 : Real.Gamma (3 * ((2*μ+1 : ℕ) : ℝ) + 1) = ((6*μ+3).factorial : ℝ) := by
    rw [show (3 : ℝ) * ((2*μ+1 : ℕ) : ℝ) + 1 = ((6*μ+3 : ℕ) : ℝ) + 1 by push_cast; ring,
        Real.Gamma_nat_eq_factorial]
  have g7 : Real.Gamma (((2*μ+1 : ℕ) : ℝ) + 1) = ((2*μ+1).factorial : ℝ) := by
    rw [Real.Gamma_nat_eq_factorial]
  -- factorial recurrences
  have R1 : ((18*μ+10).factorial:ℝ) = (18*μ+10 : ℝ)*((18*μ+9).factorial:ℝ) := by
    have : (18*μ+10).factorial = (18*μ+10)*(18*μ+9).factorial := by
      rw [show 18*μ+10 = (18*μ+9)+1 by ring, Nat.factorial_succ]
    rw [this]; push_cast; ring
  have R2 : ((6*μ+4).factorial:ℝ) = (6*μ+4 : ℝ)*((6*μ+3).factorial:ℝ) := by
    have : (6*μ+4).factorial = (6*μ+4)*(6*μ+3).factorial := by
      rw [show 6*μ+4 = (6*μ+3)+1 by ring, Nat.factorial_succ]
    rw [this]; push_cast; ring
  have R3 : ((9*μ+5).factorial:ℝ) = (9*μ+5 : ℝ)*((9*μ+4).factorial:ℝ) := by
    have : (9*μ+5).factorial = (9*μ+5)*(9*μ+4).factorial := by
      rw [show 9*μ+5 = (9*μ+4)+1 by ring, Nat.factorial_succ]
    rw [this]; push_cast; ring
  have R4 : ((3*μ+2).factorial:ℝ) = (3*μ+2 : ℝ)*((3*μ+1).factorial:ℝ) := by
    have : (3*μ+2).factorial = (3*μ+2)*(3*μ+1).factorial := by
      rw [show 3*μ+2 = (3*μ+1)+1 by ring, Nat.factorial_succ]
    rw [this]; push_cast; ring
  have R5 : (4:ℝ)^(9*μ+5) = 4^(6*μ+3) * 4^(3*μ+2) := by
    rw [← pow_add]; congr 1; ring
  have hsp : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h4 : (0:ℝ) < (4:ℝ)^(3*μ+2) := by positivity
  have hf1 : (0:ℝ) < ((3*μ+2).factorial:ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hf2 : (0:ℝ) < ((9*μ+5).factorial:ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hf3 : (0:ℝ) < ((8*μ+4).factorial:ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hf4 : (0:ℝ) < ((6*μ+3).factorial:ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hf5 : (0:ℝ) < ((2*μ+1).factorial:ℝ) := by exact_mod_cast Nat.factorial_pos _
  unfold a
  simp only [g1, g2, g3, g4, g5, g6, g7]
  rw [R1, R2, R3, R4, R5]
  field_simp
  ring

open Finset in
lemma Lset_eq (p r q : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 0 < r) :
    (range ((p^r-1)/2 + 1)).filter (fun i => ¬ p ∣ (q*p^r+i)) = Lset p r := by
  have hpqpr : p ∣ q * p^r := Dvd.dvd.mul_left (dvd_pow_self p hr.ne') q
  have hodd : ¬ 2 ∣ p^r := pr_odd p r hp hp5
  ext i
  rw [Finset.mem_filter, Finset.mem_range, mem_Lset]
  have hd : p ∣ (q*p^r+i) ↔ p ∣ i := Nat.dvd_add_right hpqpr
  rw [hd]
  constructor
  · rintro ⟨hi, hnd⟩
    exact ⟨⟨by omega, hnd⟩, by omega⟩
  · rintro ⟨⟨hi, hnd⟩, h2⟩
    exact ⟨by omega, hnd⟩

open Finset in
lemma g_half_split (p r q : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) :
    (∏ k ∈ (range (q*p^r + ((p^r-1)/2 + 1))).filter (fun k => ¬ p ∣ k), ((k:ℕ):ZMod (p^(3*r))))
      = (∏ ℓ ∈ (range (p^r)).filter (fun k => ¬ p ∣ k), ((ℓ:ℕ):ZMod (p^(3*r))))^q
        * (∏ ℓ ∈ Lset p r, ((q*p^r+ℓ:ℕ):ZMod (p^(3*r)))) := by
  have hp : p.Prime := Fact.out
  have hpqpr : p ∣ q * p^r := Dvd.dvd.mul_left (dvd_pow_self p hr.ne') q
  rw [Finset.range_add, Finset.filter_union,
      Finset.prod_union (Finset.disjoint_filter_filter
        (Finset.disjoint_range_addLeftEmbedding (q*p^r) (range ((p^r-1)/2+1)))),
      g_prod_eq p r hp5 hr q]
  congr 1
  rw [Finset.filter_map, Finset.prod_map]
  have hset : (range ((p^r-1)/2+1)).filter ((fun k => ¬ p ∣ k) ∘ ⇑(addLeftEmbedding (q*p^r)))
      = Lset p r := by
    rw [← Lset_eq p r q hp hp5 hr]
    apply Finset.filter_congr
    intro i _
    simp [addLeftEmbedding_apply]
  rw [hset]
  apply Finset.prod_congr rfl
  intro ℓ _
  simp only [addLeftEmbedding_apply]

lemma a_odd' (m : ℕ) (hm : Odd m) :
    a m * (((4*m).factorial:ℝ) * (m.factorial:ℝ) * (((3*m-1)/2).factorial:ℝ))
      = (4:ℝ)^(3*m) * ((2*m).factorial:ℝ) * (((9*m-1)/2).factorial:ℝ) := by
  obtain ⟨μ, hμ⟩ := hm
  subst hμ
  rw [show (3*(2*μ+1)-1)/2 = 3*μ+1 by omega,
      show (9*(2*μ+1)-1)/2 = 9*μ+4 by omega,
      show 4*(2*μ+1) = 8*μ+4 by ring, show 2*(2*μ+1) = 4*μ+2 by ring,
      show 3*(2*μ+1) = 6*μ+3 by ring]
  linarith [a_odd μ]

open Finset in
lemma Icc1_filter_range (p n : ℕ) :
    (Finset.Icc 1 n).filter (fun k => ¬ p ∣ k) = (Finset.range (n+1)).filter (fun k => ¬ p ∣ k) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1,h2⟩,hd⟩; exact ⟨by omega, hd⟩
  · rintro ⟨h,hd⟩
    refine ⟨⟨?_, by omega⟩, hd⟩
    rcases Nat.eq_zero_or_pos k with h0|h0
    · exact absurd (h0 ▸ dvd_zero p) hd
    · exact h0

open Finset in
lemma half_div (p q r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 0 < r) :
    (q*p^r + (p^r-1)/2)/p = q*p^(r-1)+(p^(r-1)-1)/2 := by
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hPodd : Odd (p^(r-1)) := Odd.pow hpodd
  obtain ⟨c, hc⟩ := hpodd
  obtain ⟨b, hb⟩ := hPodd
  have hmul : p^r = p * p^(r-1) := by rw [← pow_succ']; congr 1; omega
  have hpr_val : p^r = (2*c+1)*(2*b+1) := by rw [hmul, hb, hc]
  have hprod : (2*c+1)*(2*b+1) = 2*(2*(b*c)+b+c)+1 := by ring
  have ha : (p^r-1)/2 = 2*(b*c)+b+c := by omega
  have hbdiv : (p^(r-1)-1)/2 = b := by omega
  have hcdiv : (p-1)/2 = c := by omega
  have hn : q*p^r + (p^r-1)/2 = (q*p^(r-1)+(p^(r-1)-1)/2)*p + (p-1)/2 := by
    rw [ha, hbdiv, hcdiv, hpr_val, hb, hc]; ring
  rw [hn, add_comm, Nat.add_mul_div_right _ _ hp.pos,
      Nat.div_eq_of_lt (by omega : (p-1)/2 < p), zero_add]

open Finset in
lemma single_split_half (p q r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 0 < r) :
    ((q*p^r + (p^r-1)/2).factorial : ℤ)
      = (∏ k ∈ (range (q*p^r + ((p^r-1)/2+1))).filter (fun k => ¬ p ∣ k), (k:ℤ))
        * (p:ℤ)^(q*p^(r-1)+(p^(r-1)-1)/2) * ((q*p^(r-1)+(p^(r-1)-1)/2).factorial : ℤ) := by
  have hdiv := half_div p q r hp hp5 hr
  have hs := factorial_split p (q*p^r + (p^r-1)/2) hp.one_lt
  rw [hdiv, Icc1_filter_range p (q*p^r + (p^r-1)/2),
      show (q*p^r + (p^r-1)/2) + 1 = q*p^r + ((p^r-1)/2+1) by ring] at hs
  have hcast := congrArg (Nat.cast : ℕ → ℤ) hs
  push_cast at hcast
  rw [hcast]; ring

lemma half_arg (p a e : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hodd : Odd a) :
    (a*p^e-1)/2 = ((a-1)/2)*p^e + (p^e-1)/2 := by
  obtain ⟨q, hq⟩ := hodd
  obtain ⟨b, hb⟩ : Odd (p^e) := (hp.odd_of_ne_two (by omega)).pow
  have hap : a*p^e = 2*(2*(q*b)+q+b)+1 := by rw [hq, hb]; ring
  have hL : (a*p^e-1)/2 = 2*(q*b)+q+b := by omega
  have hq2 : (a-1)/2 = q := by omega
  have hb2 : (p^e-1)/2 = b := by omega
  rw [hL, hq2, hb2, hb]; ring

open Finset in
lemma half_split_full (p a r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 0 < r) (hodd : Odd a) :
    (((a*p^r-1)/2).factorial : ℤ)
      = (∏ k ∈ (range (((a-1)/2)*p^r + ((p^r-1)/2+1))).filter (fun k => ¬ p ∣ k), (k:ℤ))
        * (p:ℤ)^(((a-1)/2)*p^(r-1)+(p^(r-1)-1)/2)
        * (((a*p^(r-1)-1)/2).factorial : ℤ) := by
  have ha_r := half_arg p a r hp hp5 hodd
  have ha_r1 := half_arg p a (r-1) hp hp5 hodd
  have hss := single_split_half p ((a-1)/2) r hp hp5 hr
  rw [ha_r, ha_r1]
  exact hss

open Finset in
lemma g_half_int_cast (p r q : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) :
    ((∏ k ∈ (range (q*p^r + ((p^r-1)/2+1))).filter (fun k => ¬ p ∣ k), (k:ℤ)) : ZMod (p^(3*r)))
      = (∏ ℓ ∈ (range (p^r)).filter (fun k => ¬ p ∣ k), ((ℓ:ℕ):ZMod (p^(3*r))))^q
        * (∏ ℓ ∈ Lset p r, ((q*p^r+ℓ:ℕ):ZMod (p^(3*r)))) := by
  simp only [Int.cast_natCast]
  exact g_half_split p r q hp5 hr

open Finset in
lemma odd_case (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (r : ℕ) (hr : 0 < r)
    (n : ℕ) (hn : 0 < n) (hnodd : Odd n)
    (x y : ℤ)
    (hx : x * (((4*n*p^r).factorial:ℤ) * (n*p^r).factorial * ((3*n*p^r-1)/2).factorial)
          = (4:ℤ)^(3*n*p^r) * (2*n*p^r).factorial * ((9*n*p^r-1)/2).factorial)
    (hy : y * (((4*n*p^(r-1)).factorial:ℤ) * (n*p^(r-1)).factorial * ((3*n*p^(r-1)-1)/2).factorial)
          = (4:ℤ)^(3*n*p^(r-1)) * (2*n*p^(r-1)).factorial * ((9*n*p^(r-1)-1)/2).factorial) :
    x ≡ y [ZMOD ((p:ℤ)^(3*r))] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd3 : Odd (3*n) := by obtain ⟨k, hk⟩ := hnodd; exact ⟨3*k+1, by omega⟩
  have hodd9 : Odd (9*n) := by obtain ⟨k, hk⟩ := hnodd; exact ⟨9*k+4, by omega⟩
  -- ℤ g-products
  set GA4 := ∏ k ∈ (range (4*n*p^r)).filter (fun k => ¬ p ∣ k), (k:ℤ) with hGA4
  set GA1 := ∏ k ∈ (range (n*p^r)).filter (fun k => ¬ p ∣ k), (k:ℤ) with hGA1
  set GA2 := ∏ k ∈ (range (2*n*p^r)).filter (fun k => ¬ p ∣ k), (k:ℤ) with hGA2
  set GH3 := ∏ k ∈ (range (((3*n-1)/2)*p^r + ((p^r-1)/2+1))).filter (fun k => ¬ p ∣ k), (k:ℤ) with hGH3
  set GH9 := ∏ k ∈ (range (((9*n-1)/2)*p^r + ((p^r-1)/2+1))).filter (fun k => ¬ p ∣ k), (k:ℤ) with hGH9
  set E := (5*n + (3*n-1)/2) * p^(r-1) + (p^(r-1)-1)/2 with hE
  set Dm := ((4*n*p^(r-1)).factorial:ℤ) * (n*p^(r-1)).factorial * ((3*n*p^(r-1)-1)/2).factorial with hDm
  set Rm := ((2*n*p^(r-1)).factorial:ℤ) * ((9*n*p^(r-1)-1)/2).factorial with hRm
  -- splits
  have e4 := single_split p (4*n) r hp hr
  have e1 := single_split p n r hp hr
  have e2 := single_split p (2*n) r hp hr
  have e3h := half_split_full p (3*n) r hp hp5 hr hodd3
  have e9h := half_split_full p (9*n) r hp hp5 hr hodd9
  rw [← hGA4] at e4
  rw [← hGA1] at e1
  rw [← hGA2] at e2
  rw [← hGH3] at e3h
  rw [← hGH9] at e9h
  -- p-power collections
  have hpowL : (p:ℤ)^((4*n)*p^(r-1)) * (p:ℤ)^(n*p^(r-1))
        * (p:ℤ)^(((3*n-1)/2)*p^(r-1) + (p^(r-1)-1)/2) = (p:ℤ)^E := by
    rw [← pow_add, ← pow_add]; congr 1; rw [hE]; ring
  have hnum : 2*n + (9*n-1)/2 = 5*n + (3*n-1)/2 := by omega
  have hpowR : (p:ℤ)^((2*n)*p^(r-1)) * (p:ℤ)^(((9*n-1)/2)*p^(r-1) + (p^(r-1)-1)/2) = (p:ℤ)^E := by
    rw [← pow_add]; congr 1
    rw [hE, show (2*n)*p^(r-1) + (((9*n-1)/2)*p^(r-1) + (p^(r-1)-1)/2)
          = (2*n+(9*n-1)/2)*p^(r-1) + (p^(r-1)-1)/2 by ring, hnum]
  -- lump factorials
  have hLHSfac : (((4*n*p^r).factorial:ℤ) * (n*p^r).factorial * ((3*n*p^r-1)/2).factorial)
      = (GA4*GA1*GH3) * (p:ℤ)^E * Dm := by
    have expand : (GA4*GA1*GH3) * (p:ℤ)^E * Dm
        = (GA4 * (p:ℤ)^((4*n)*p^(r-1)) * ((4*n*p^(r-1)).factorial:ℤ))
          * (GA1 * (p:ℤ)^(n*p^(r-1)) * ((n*p^(r-1)).factorial:ℤ))
          * (GH3 * (p:ℤ)^(((3*n-1)/2)*p^(r-1) + (p^(r-1)-1)/2) * (((3*n*p^(r-1)-1)/2).factorial:ℤ)) := by
      rw [hDm, ← hpowL]; ring
    rw [expand, ← e4, ← e1, ← e3h]
  have hRHSfac : (((2*n*p^r).factorial:ℤ) * ((9*n*p^r-1)/2).factorial)
      = (GA2*GH9) * (p:ℤ)^E * Rm := by
    have expand : (GA2*GH9) * (p:ℤ)^E * Rm
        = (GA2 * (p:ℤ)^((2*n)*p^(r-1)) * ((2*n*p^(r-1)).factorial:ℤ))
          * (GH9 * (p:ℤ)^(((9*n-1)/2)*p^(r-1) + (p^(r-1)-1)/2) * (((9*n*p^(r-1)-1)/2).factorial:ℤ)) := by
      rw [hRm, ← hpowR]; ring
    rw [expand, ← e2, ← e9h]
  -- 4-power split
  set W := (4:ℤ)^(3*n*p^(r-1)) with hW
  set V := (4:ℤ)^(3*n*(p^r - p^(r-1))) with hV
  have hpow4 : (4:ℤ)^(3*n*p^r) = W * V := by
    rw [hW, hV, ← pow_add]; congr 1
    have hle : p^(r-1) ≤ p^r := Nat.pow_le_pow_right hp.pos (by omega)
    rw [← Nat.mul_add]; congr 1; omega
  -- substituted hx
  have hx_sub : x * ((GA4*GA1*GH3)*(p:ℤ)^E*Dm) = W * V * ((GA2*GH9)*(p:ℤ)^E*Rm) := by
    rw [← hLHSfac, ← hRHSfac, ← hpow4]
    linear_combination hx
  -- big cancellation equation
  have hbig : (x*(GA4*GA1*GH3)) * ((p:ℤ)^E * Dm)
      = (V*(GA2*GH9)*y) * ((p:ℤ)^E * Dm) := by
    linear_combination hx_sub - (V*(GA2*GH9)*(p:ℤ)^E) * hy
  have hne : (p:ℤ)^E * Dm ≠ 0 := by
    apply ne_of_gt
    have hpp : (0:ℤ) < (p:ℤ)^E := pow_pos (by exact_mod_cast hp.pos) E
    have hdm : (0:ℤ) < Dm := by rw [hDm]; positivity
    positivity
  have hcancel : x*(GA4*GA1*GH3) = V*(GA2*GH9)*y := mul_right_cancel₀ hne hbig
  -- reduce mod p^(3*r)
  set G0 := ∏ ℓ ∈ (range (p^r)).filter (fun k => ¬ p ∣ k), ((ℓ:ℕ):ZMod (p^(3*r))) with hG0
  set PB3 := ∏ ℓ ∈ Lset p r, ((((3*n-1)/2)*p^r+ℓ:ℕ):ZMod (p^(3*r))) with hPB3
  set PB9 := ∏ ℓ ∈ Lset p r, ((((9*n-1)/2)*p^r+ℓ:ℕ):ZMod (p^(3*r))) with hPB9
  -- casts
  have cGA4 : ((GA4:ℤ):ZMod (p^(3*r))) = G0^(4*n) := by
    rw [hGA4]; push_cast; rw [g_prod_eq p r hp5 hr (4*n), ← hG0]
  have cGA1 : ((GA1:ℤ):ZMod (p^(3*r))) = G0^n := by
    rw [hGA1]; push_cast; rw [g_prod_eq p r hp5 hr n, ← hG0]
  have cGA2 : ((GA2:ℤ):ZMod (p^(3*r))) = G0^(2*n) := by
    rw [hGA2]; push_cast; rw [g_prod_eq p r hp5 hr (2*n), ← hG0]
  have cGH3 : ((GH3:ℤ):ZMod (p^(3*r))) = G0^((3*n-1)/2) * PB3 := by
    rw [hGH3]; push_cast; rw [g_half_split p r ((3*n-1)/2) hp5 hr, ← hG0, ← hPB3]
  have cGH9 : ((GH9:ℤ):ZMod (p^(3*r))) = G0^((9*n-1)/2) * PB9 := by
    rw [hGH9]; push_cast; rw [g_half_split p r ((9*n-1)/2) hp5 hr, ← hG0, ← hPB9]
  have cV : ((V:ℤ):ZMod (p^(3*r))) = (4:ZMod (p^(3*r)))^(3*n*(p^r-p^(r-1))) := by
    rw [hV]; push_cast; ring
  -- cast hcancel
  have hcast : (x:ZMod (p^(3*r))) * (↑GA4 * ↑GA1 * ↑GH3)
      = (↑V * (↑GA2 * ↑GH9)) * (y:ZMod (p^(3*r))) := by
    have h := congrArg (fun z : ℤ => (z : ZMod (p^(3*r)))) hcancel
    push_cast at h
    linear_combination h
  rw [cGA4, cGA1, cGA2, cGH3, cGH9, cV] at hcast
  -- combine G0 powers
  have hg0L : G0^(4*n) * G0^n * G0^((3*n-1)/2) = G0^(5*n+(3*n-1)/2) := by
    rw [← pow_add, ← pow_add, show 4*n+n+(3*n-1)/2 = 5*n+(3*n-1)/2 by omega]
  have hg0R : G0^(2*n) * G0^((9*n-1)/2) = G0^(5*n+(3*n-1)/2) := by
    rw [← pow_add, show 2*n+(9*n-1)/2 = 5*n+(3*n-1)/2 by omega]
  rw [show G0^(4*n) * G0^n * (G0^((3*n-1)/2)*PB3) = (G0^(4*n) * G0^n * G0^((3*n-1)/2))*PB3 by ring, hg0L,
      show (4:ZMod (p^(3*r)))^(3*n*(p^r-p^(r-1))) * (G0^(2*n)*(G0^((9*n-1)/2)*PB9))
        = (4:ZMod (p^(3*r)))^(3*n*(p^r-p^(r-1))) * ((G0^(2*n)*G0^((9*n-1)/2))*PB9) by ring, hg0R] at hcast
  -- telescope
  have htel : PB3 = (4:ZMod (p^(3*r)))^(3*n*(p^r-p^(r-1))) * PB9 := by
    have h := PB_telescope p r ((3*n-1)/2) (3*n) hp5 hr
    rw [show (3*n-1)/2 + 3*n = (9*n-1)/2 by omega] at h
    rw [hPB3, hPB9]; exact h
  rw [htel] at hcast
  -- units
  have hG0u : IsUnit G0 := by rw [hG0]; exact g_prod_zmod_isUnit p r (p^r)
  have h4u : IsUnit (4:ZMod (p^(3*r))) := by
    have h2 := (two_three_units p (3*r) hp5).1
    rw [show (4:ZMod (p^(3*r))) = 2*2 by norm_num]; exact h2.mul h2
  have hPB9u : IsUnit PB9 := by
    rw [hPB9]
    refine Finset.prod_induction _ IsUnit (fun a b => IsUnit.mul) isUnit_one ?_
    intro ℓ hℓ
    rw [mem_Lset] at hℓ
    rw [ZMod.isUnit_iff_coprime]
    refine (((hp.coprime_iff_not_dvd).2 ?_).symm).pow_right (3*r)
    intro hd
    have hpr : p ∣ ((9*n-1)/2)*p^r := Dvd.dvd.mul_left (dvd_pow_self p hr.ne') _
    exact hℓ.1.2 ((Nat.dvd_add_right hpr).1 hd)
  set U := G0^(5*n+(3*n-1)/2) * ((4:ZMod (p^(3*r)))^(3*n*(p^r-p^(r-1))) * PB9) with hU
  have hUu : IsUnit U := by
    rw [hU]
    exact (hG0u.pow (5*n+(3*n-1)/2)).mul ((h4u.pow (3*n*(p^r-p^(r-1)))).mul hPB9u)
  have hfinal : U * (x:ZMod (p^(3*r))) = U * (y:ZMod (p^(3*r))) := by
    rw [hU]; linear_combination hcast
  have hxy : (x:ZMod (p^(3*r))) = (y:ZMod (p^(3*r))) := hUu.mul_left_cancel hfinal
  rw [show ((p:ℤ)^(3*r)) = ((p^(3*r) : ℕ) : ℤ) by push_cast; ring, ← ZMod.intCast_eq_intCast_iff]
  exact hxy

lemma key_odd (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (n r : ℕ) (hn : 0 < n) (hnodd : Odd n)
    (hr : 0 < r) (x y : ℤ) (hx : (x:ℝ) = a (n*p^r)) (hy : (y:ℝ) = a (n*p^(r-1))) :
    x ≡ y [ZMOD ((p:ℤ)^(3*r))] := by
  have hodd_pr : Odd (n*p^r) := hnodd.mul (Odd.pow (hp.odd_of_ne_two (by omega)))
  have hodd_pr1 : Odd (n*p^(r-1)) := hnodd.mul (Odd.pow (hp.odd_of_ne_two (by omega)))
  apply odd_case p hp hp5 r hr n hn hnodd x y
  · have key : (x:ℝ) * (((4*(n*p^r)).factorial:ℝ)*((n*p^r).factorial:ℝ)*(((3*(n*p^r)-1)/2).factorial:ℝ))
         = (4:ℝ)^(3*(n*p^r))*((2*(n*p^r)).factorial:ℝ)*(((9*(n*p^r)-1)/2).factorial:ℝ) := by
      rw [hx]; exact a_odd' (n*p^r) hodd_pr
    rw [show 4*n*p^r = 4*(n*p^r) by ring, show 2*n*p^r = 2*(n*p^r) by ring,
        show 9*n*p^r = 9*(n*p^r) by ring, show 3*n*p^r = 3*(n*p^r) by ring]
    exact_mod_cast key
  · have key : (y:ℝ) * (((4*(n*p^(r-1))).factorial:ℝ)*((n*p^(r-1)).factorial:ℝ)*(((3*(n*p^(r-1))-1)/2).factorial:ℝ))
         = (4:ℝ)^(3*(n*p^(r-1)))*((2*(n*p^(r-1))).factorial:ℝ)*(((9*(n*p^(r-1))-1)/2).factorial:ℝ) := by
      rw [hy]; exact a_odd' (n*p^(r-1)) hodd_pr1
    rw [show 4*n*p^(r-1) = 4*(n*p^(r-1)) by ring, show 2*n*p^(r-1) = 2*(n*p^(r-1)) by ring,
        show 9*n*p^(r-1) = 9*(n*p^(r-1)) by ring, show 3*n*p^(r-1) = 3*(n*p^(r-1)) by ring]
    exact_mod_cast key

open scoped Real in
/--
Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and all positive integers n and r.
Note: This conjecture requires that a(n) is an integer for all n, which is only conjectural.
We assume integrality for the purpose of stating the congruence.
-/
-- The key number-theoretic content, stated independently of `h_int`:
-- for the integers `x, y` representing `a (n*p^r)` and `a (n*p^(r-1))`, we have
-- `x ≡ y [ZMOD p^(3r)]`. This is the Jacobsthal–Kazandzidis-type supercongruence
-- for the (generalized) factorial-ratio sequence `a`.
theorem oeis_364173_key
    (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0)
    (x y : ℤ) (hx : (x : ℝ) = a (n * p ^ r)) (hy : (y : ℝ) = a (n * p ^ (r - 1))) :
    x ≡ y [ZMOD ((p : ℤ) ^ (3 * r))] := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨μ, rfl⟩ := he
    apply key_even p hp h_p_ge_5 μ r hr x y
    · rw [hx]; congr 1; ring
    · rw [hy]; congr 1; ring
  · exact key_odd p hp h_p_ge_5 n r hn ho hr x y hx hy

theorem oeis_364173_conjecture_0
    (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] :=
by
  intro p hp h_p_ge_5 n r hn hr
  exact oeis_364173_key p hp h_p_ge_5 n r hn hr _ _
    (Classical.choose_spec (h_int (n * p ^ r)))
    (Classical.choose_spec (h_int (n * p ^ (r - 1))))
