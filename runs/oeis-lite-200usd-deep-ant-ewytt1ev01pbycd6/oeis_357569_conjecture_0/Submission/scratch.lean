import FormalConjectures.Util.ProblemImports
open Nat Finset
open scoped BigOperators

theorem sum_sq_range (N : ℕ) :
    6 * (∑ i ∈ Finset.range N, (i : ℤ)^2) = ((N : ℤ) - 1) * N * (2 * N - 1) := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, mul_add, ih]; push_cast; ring

theorem map_ring_inverse {R S F : Type*} [CommRing R] [CommRing S]
    [FunLike F R S] [RingHomClass F R S] (f : F) {u : R} (hu : IsUnit u) :
    f (Ring.inverse u) = Ring.inverse (f u) := by
  have hfu : IsUnit (f u) := hu.map f
  have h1 : f (Ring.inverse u) * f u = 1 := by
    rw [← map_mul, Ring.inverse_mul_cancel _ hu, map_one]
  have h2 : Ring.inverse (f u) * f u = 1 := Ring.inverse_mul_cancel _ hfu
  exact hfu.mul_right_cancel (by rw [h1, h2])

theorem ring_inv_inv {R : Type*} [CommRing R] {u : R} (hu : IsUnit u) :
    Ring.inverse (Ring.inverse u) = u := by
  obtain ⟨v, rfl⟩ := hu
  rw [Ring.inverse_unit, Ring.inverse_unit, inv_inv]

variable (p : ℕ)
def Tset (m : ℕ) : Finset ℕ := (Finset.range (p^m)).filter (fun t => ¬ p ∣ t)
def wv : ℕ := if p = 3 then 1 else 0

theorem mem_Tset {m t : ℕ} : t ∈ Tset p m ↔ t < p^m ∧ ¬ p ∣ t := by
  simp [Tset, Finset.mem_filter, Finset.mem_range]

variable [Fact p.Prime]

theorem zmod_inv_sq_sum (m : ℕ) (hm : 1 ≤ m) :
    (∑ t ∈ Tset p m, (Ring.inverse ((t : ZMod (p^m))))^2)
      = (∑ t ∈ Tset p m, ((t : ZMod (p^m)))^2) := by
  haveI hne : NeZero (p^m) := ⟨(pow_pos (Fact.out : p.Prime).pos m).ne'⟩
  have hp := (Fact.out : p.Prime)
  set σ : ℕ → ℕ := fun t => (Ring.inverse ((t : ZMod (p^m)))).val with hσ
  -- (a): ↑(σ t) = Ring.inverse ↑t
  have ha : ∀ t, ((σ t : ℕ) : ZMod (p^m)) = Ring.inverse ((t : ZMod (p^m))) := by
    intro t; rw [hσ]; exact ZMod.natCast_zmod_val _
  -- unit facts
  have hunit_t : ∀ t ∈ Tset p m, IsUnit ((t : ZMod (p^m))) := by
    intro t ht
    rw [ZMod.isUnit_iff_coprime]
    exact (((hp.coprime_iff_not_dvd).mpr ((mem_Tset p).mp ht).2).symm).pow_right m
  -- σ maps Tset to Tset
  have hmaps : ∀ t ∈ Tset p m, σ t ∈ Tset p m := by
    intro t ht
    rw [mem_Tset]
    refine ⟨by rw [hσ]; exact ZMod.val_lt _, ?_⟩
    -- ↑(σ t) is a unit ⟹ coprime ⟹ ¬p∣σt
    have huσ : IsUnit ((σ t : ZMod (p^m))) := by
      rw [ha t]; obtain ⟨u, hu⟩ := hunit_t t ht
      rw [← hu, Ring.inverse_unit]; exact (u⁻¹).isUnit
    rw [ZMod.isUnit_iff_coprime] at huσ
    have hcp : Nat.Coprime (σ t) p := huσ.coprime_dvd_right (dvd_pow_self p (by omega))
    exact (hp.coprime_iff_not_dvd).mp hcp.symm
  -- σ is an involution on Tset
  have hinv : ∀ t ∈ Tset p m, σ (σ t) = t := by
    intro t ht
    have h1 : ((σ (σ t) : ℕ) : ZMod (p^m)) = ((t : ℕ) : ZMod (p^m)) := by
      rw [ha (σ t), ha t, ring_inv_inv (hunit_t t ht)]
    -- cast injective on values < p^m
    have hlt1 : σ (σ t) < p^m := by rw [hσ]; exact ZMod.val_lt _
    have hlt2 : t < p^m := ((mem_Tset p).mp ht).1
    -- use ZMod.val injective
    have := congrArg ZMod.val h1
    rwa [ZMod.val_natCast_of_lt hlt1, ZMod.val_natCast_of_lt hlt2] at this
  -- rewrite LHS via ha, then reindex by σ
  rw [show (∑ t ∈ Tset p m, (Ring.inverse ((t : ZMod (p^m))))^2)
      = (∑ t ∈ Tset p m, (((σ t : ℕ) : ZMod (p^m)))^2) from
        Finset.sum_congr rfl (fun t _ => by rw [ha t])]
  exact Finset.sum_nbij' σ σ hmaps hmaps hinv hinv (fun a _ => rfl)

-- Step: the p∣· part reindexes.
theorem pdvd_reindex (m : ℕ) (hm : 1 ≤ m) (hp : 0 < p) :
    ((Finset.range (p^m)).filter (fun t => p ∣ t))
      = (Finset.range (p^(m-1))).image (fun s => p * s) := by
  have hpm : p^m = p * p^(m-1) := by rw [← pow_succ']; congr 1; omega
  ext t
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨htlt, s, rfl⟩
    refine ⟨s, ?_, rfl⟩
    rw [hpm] at htlt
    exact lt_of_mul_lt_mul_left htlt (Nat.zero_le p)
  · rintro ⟨s, hs, rfl⟩
    refine ⟨?_, ⟨s, rfl⟩⟩
    rw [hpm]
    exact Nat.mul_lt_mul_of_pos_left hs hp

theorem sq_split (m : ℕ) (hm : 1 ≤ m) (hp : 0 < p) :
    (∑ t ∈ Tset p m, (t:ℤ)^2)
      = (∑ t ∈ Finset.range (p^m), (t:ℤ)^2)
        - (p:ℤ)^2 * (∑ s ∈ Finset.range (p^(m-1)), (s:ℤ)^2) := by
  have hpart := Finset.sum_filter_add_sum_filter_not (Finset.range (p^m))
    (fun t => p ∣ t) (fun t => (t:ℤ)^2)
  have himg : (∑ t ∈ (Finset.range (p^m)).filter (fun t => p ∣ t), (t:ℤ)^2)
      = (p:ℤ)^2 * (∑ s ∈ Finset.range (p^(m-1)), (s:ℤ)^2) := by
    rw [pdvd_reindex p m hm hp, Finset.sum_image (by
      intro a _ b _ hab; exact Nat.eq_of_mul_eq_mul_left hp hab)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s _; push_cast; ring
  rw [himg] at hpart
  unfold Tset
  linarith [hpart]

theorem faulhaber (m : ℕ) (hm : 1 ≤ m) (hp : p.Prime) (hp3 : 3 ≤ p) :
    (p:ℤ)^(m - wv p) ∣ (∑ t ∈ Tset p m, (t:ℤ)^2) := by
  have hp0 : 0 < p := by omega
  set Ssq := ∑ t ∈ Tset p m, (t:ℤ)^2 with hSsq
  have hx : (p:ℤ)^m = (p:ℤ) * (p:ℤ)^(m-1) := by
    nth_rewrite 1 [show m = 1 + (m-1) by omega]
    rw [pow_add, pow_one]
  -- 6 * Ssq = p^m * K
  have h6 : 6 * Ssq = (p:ℤ)^m * ((((p:ℤ)^m - 1) * (2*(p:ℤ)^m - 1))
      - p * (((p:ℤ)^(m-1) - 1) * (2*(p:ℤ)^(m-1) - 1))) := by
    rw [hSsq, sq_split p m hm hp0, mul_sub]
    rw [show (6:ℤ) * (∑ t ∈ Finset.range (p^m), (t:ℤ)^2) = _ from sum_sq_range (p^m)]
    rw [show (6:ℤ) * ((p:ℤ)^2 * (∑ s ∈ Finset.range (p^(m-1)), (s:ℤ)^2))
        = (p:ℤ)^2 * (6 * (∑ s ∈ Finset.range (p^(m-1)), (s:ℤ)^2)) by ring]
    rw [show (6:ℤ) * (∑ s ∈ Finset.range (p^(m-1)), (s:ℤ)^2) = _ from sum_sq_range (p^(m-1))]
    push_cast
    rw [hx]; ring
  have hdvd6 : (p:ℤ)^m ∣ 6 * Ssq := ⟨_, h6⟩
  have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  by_cases hp3eq : p = 3
  · -- w = 1, need 3^(m-1) ∣ Ssq
    have hwv : wv p = 1 := by unfold wv; rw [if_pos hp3eq]
    rw [hwv]
    have hp3z : (p:ℤ) = 3 := by rw [hp3eq]; norm_num
    have h1 : (p:ℤ)^m ∣ 3 * (2 * Ssq) := by
      have : (6:ℤ) * Ssq = 3 * (2 * Ssq) := by ring
      rwa [this] at hdvd6
    have hxm : (p:ℤ)^m = (3:ℤ) * (p:ℤ)^(m-1) := by rw [hx, hp3z]
    have h2 : (3:ℤ) * (p:ℤ)^(m-1) ∣ 3 * (2 * Ssq) := by rw [← hxm]; exact h1
    have h3 : (p:ℤ)^(m-1) ∣ 2 * Ssq :=
      (mul_dvd_mul_iff_left (by norm_num : (3:ℤ) ≠ 0)).mp h2
    have hcop : IsCoprime ((p:ℤ)^(m-1)) 2 := by
      apply IsCoprime.pow_left
      rw [hp3z, Int.isCoprime_iff_gcd_eq_one]; decide
    exact hcop.dvd_of_dvd_mul_left h3
  · -- w = 0, need p^m ∣ Ssq
    have hwv : wv p = 0 := by unfold wv; simp [hp3eq]
    rw [hwv, Nat.sub_zero]
    have hcop : IsCoprime ((p:ℤ)^m) 6 := by
      apply IsCoprime.pow_left
      have hp5 : 5 ≤ p := by
        rcases Nat.lt_or_ge p 5 with h | h
        · interval_cases p <;> first | (exact absurd rfl hp3eq) | (exact absurd hp (by decide)) | omega
        · exact h
      have hnd2 : ¬ (p:ℤ) ∣ 2 := by
        intro h; have := Int.le_of_dvd (by norm_num) h; omega
      have hnd3 : ¬ (p:ℤ) ∣ 3 := by
        intro h; have := Int.le_of_dvd (by norm_num) h; omega
      have hnd6 : ¬ (p:ℤ) ∣ 6 := by
        intro h
        rcases hpp.dvd_mul.mp (show (p:ℤ) ∣ 2 * 3 by rwa [show (2:ℤ)*3 = 6 by norm_num]) with h2 | h3
        · exact hnd2 h2
        · exact hnd3 h3
      exact (hpp.coprime_iff_not_dvd).mpr hnd6
    exact hcop.dvd_of_dvd_mul_left hdvd6

theorem Tset_one_le {m t : ℕ} (ht : t ∈ Tset p m) : 1 ≤ t := by
  rw [mem_Tset] at ht
  exact Nat.one_le_iff_ne_zero.mpr (fun h => ht.2 (h ▸ dvd_zero p))

theorem Tset_symm {m t : ℕ} (ht : t ∈ Tset p m) : (p^m - t) ∈ Tset p m := by
  have h1 := Tset_one_le p ht
  rw [mem_Tset] at ht ⊢
  refine ⟨by omega, ?_⟩
  intro hd
  exact ht.2 (by
    have : p ∣ p^m - (p^m - t) := Nat.dvd_sub (dvd_pow_self p (by
      rintro rfl; simp only [pow_zero] at ht; omega)) hd
    rwa [Nat.sub_sub_self (le_of_lt ht.1)] at this)

/-- Fiber counting mod p: for m ≥ 2, any `F`-sum over Tset vanishes mod p. -/
theorem sum_Tset_mod_p (m : ℕ) (hm : 2 ≤ m) (F : ZMod p → ZMod p) :
    (∑ t ∈ Tset p m, F ((t : ZMod p))) = 0 := by
  have hp := (Fact.out : p.Prime)
  have hp0 : 0 < p := hp.pos
  have hbij : (∑ t ∈ Tset p m, F ((t:ZMod p)))
      = ∑ q ∈ (Tset p 1) ×ˢ (Finset.range (p^(m-1))), F ((q.1 : ZMod p)) := by
    have hpp : p * p^(m-1) = p^m := by
      conv_rhs => rw [show m = 1 + (m-1) by omega]
      rw [pow_add, pow_one]
    apply Finset.sum_nbij' (fun t => (t % p, t / p)) (fun q => q.1 + p * q.2)
    · intro t ht
      rw [mem_Tset] at ht
      rw [Finset.mem_product, mem_Tset, Finset.mem_range]
      refine ⟨⟨by rw [pow_one]; exact Nat.mod_lt _ hp0, ?_⟩, ?_⟩
      · intro hd
        exact ht.2 (Nat.dvd_of_mod_eq_zero
          (Nat.eq_zero_of_dvd_of_lt hd (Nat.mod_lt _ hp0)))
      · rw [Nat.div_lt_iff_lt_mul hp0, mul_comm, hpp]; exact ht.1
    · intro q hq
      rw [Finset.mem_product, mem_Tset, Finset.mem_range] at hq
      rw [mem_Tset]
      obtain ⟨⟨hr1, hr2⟩, hs⟩ := hq
      rw [pow_one] at hr1
      refine ⟨?_, ?_⟩
      · have h1 : q.1 + p * q.2 < p * q.2 + p := by omega
        have h2 : p * (q.2 + 1) ≤ p^m := by
          rw [← hpp]; exact mul_le_mul_left' (by omega) p
        have h3 : p * q.2 + p = p * (q.2 + 1) := by ring
        omega
      · intro hd
        exact hr2 ((Nat.dvd_add_right (Dvd.intro q.2 rfl)).mp (by rwa [add_comm] at hd))
    · intro t ht; simp [Nat.mod_add_div]
    · intro q hq
      rw [Finset.mem_product, mem_Tset, Finset.mem_range] at hq
      obtain ⟨⟨hr1, hr2⟩, hs⟩ := hq
      rw [pow_one] at hr1
      ext
      · simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr1]
      · rw [Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hr1, zero_add]
    · intro t ht
      show F ((t:ZMod p)) = F (((t % p : ℕ):ZMod p))
      rw [ZMod.natCast_mod]
  rw [hbij, Finset.sum_product]
  apply Finset.sum_eq_zero
  intro r hr
  dsimp only
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hz : ((p^(m-1) : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.natCast_self, zero_pow (by omega : m - 1 ≠ 0)]
  rw [hz, zero_mul]

theorem isUnit_cast {t : ℕ} (ht : ¬ p ∣ t) : IsUnit ((t : ℤ_[p])) := by
  rw [show ((t:ℤ_[p])) = ((t:ℤ):ℤ_[p]) by push_cast; ring, PadicInt.isUnit_iff,
      PadicInt.norm_intCast_eq_one_iff]
  have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hnd : ¬ (p:ℤ) ∣ (t:ℤ) := fun h => ht (by exact_mod_cast h)
  exact ((hpp.coprime_iff_not_dvd).mpr hnd).symm

noncomputable def Sig2 (m : ℕ) : ℤ_[p] := ∑ t ∈ Tset p m, (Ring.inverse (t:ℤ_[p]))^2

theorem Sig2_dvd (m : ℕ) (hm : 1 ≤ m) (hp3 : 3 ≤ p) :
    (p:ℤ_[p])^(m - wv p) ∣ Sig2 p m := by
  have hp := (Fact.out : p.Prime)
  set Ssum : ℤ_[p] := ∑ t ∈ Tset p m, ((t:ℤ_[p]))^2 with hSsum
  -- bridge via toZModPow m
  have hSig2map : PadicInt.toZModPow m (Sig2 p m)
      = ∑ t ∈ Tset p m, (Ring.inverse ((t:ZMod (p^m))))^2 := by
    unfold Sig2
    rw [map_sum]
    apply Finset.sum_congr rfl; intro t ht
    rw [map_pow, map_ring_inverse _ (isUnit_cast p ((mem_Tset p).mp ht).2), map_natCast]
  have hSsummap : PadicInt.toZModPow m Ssum
      = ∑ t ∈ Tset p m, ((t:ZMod (p^m)))^2 := by
    rw [hSsum, map_sum]
    apply Finset.sum_congr rfl; intro t _; rw [map_pow, map_natCast]
  have hbridge : (p:ℤ_[p])^m ∣ (Sig2 p m - Ssum) := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
        hSig2map, hSsummap, zmod_inv_sq_sum p m hm, sub_self]
  -- Faulhaber transported to ℤ_[p]
  obtain ⟨k, hk⟩ := faulhaber p m hm hp hp3
  have hSs_cast : Ssum = (((∑ t ∈ Tset p m, (t:ℤ)^2 : ℤ)):ℤ_[p]) := by
    rw [hSsum, Int.cast_sum]; apply Finset.sum_congr rfl; intro t _; push_cast; ring
  have hfaul_padic : (p:ℤ_[p])^(m - wv p) ∣ Ssum := by
    refine ⟨(k:ℤ_[p]), ?_⟩
    rw [hSs_cast, hk]; push_cast; ring
  have hsplit : Sig2 p m = (Sig2 p m - Ssum) + Ssum := by ring
  rw [hsplit]
  exact dvd_add (dvd_trans (pow_dvd_pow _ (Nat.sub_le m (wv p))) hbridge) hfaul_padic

noncomputable def Dd (m : ℕ) : ℤ_[p] :=
  ∑ t ∈ Tset p m, (Ring.inverse ((t:ℤ_[p]) * ((p^m - t : ℕ):ℤ_[p])))^2

theorem Dd_dvd (m : ℕ) (hm : 2 ≤ m) (hp3 : 3 ≤ p) : (p:ℤ_[p]) ∣ Dd p m := by
  have hp := (Fact.out : p.Prime)
  have h0 : PadicInt.toZMod (Dd p m) = 0 := by
    unfold Dd
    rw [map_sum]
    have hterm : ∀ t ∈ Tset p m,
        PadicInt.toZMod ((Ring.inverse ((t:ℤ_[p]) * ((p^m - t : ℕ):ℤ_[p])))^2)
          = (fun a => (Ring.inverse (a * (-a)))^2) ((t:ZMod p)) := by
      intro t ht
      have hu : IsUnit ((t:ℤ_[p]) * ((p^m - t : ℕ):ℤ_[p])) :=
        (isUnit_cast p ((mem_Tset p).mp ht).2).mul
          (isUnit_cast p ((mem_Tset p).mp (Tset_symm p ht)).2)
      have hpm0 : ((p^m : ℕ) : ZMod p) = 0 := by
        push_cast; rw [ZMod.natCast_self]; exact zero_pow (by omega)
      have hcast : ((p^m - t : ℕ) : ZMod p) = -(t : ZMod p) := by
        have hle : t ≤ p^m := le_of_lt ((mem_Tset p).mp ht).1
        rw [Nat.cast_sub hle, hpm0]; ring
      simp only
      rw [map_pow, map_ring_inverse _ hu, map_mul, map_natCast, map_natCast, hcast]
    rw [Finset.sum_congr rfl hterm]
    exact sum_Tset_mod_p p m hm (fun a => (Ring.inverse (a * (-a)))^2)
  rw [← PadicInt.norm_lt_one_iff_dvd]
  have hnu : ¬ IsUnit (Dd p m) := by
    rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker]
    exact h0
  rw [PadicInt.isUnit_iff] at hnu
  exact lt_of_le_of_ne (PadicInt.norm_le_one _) hnu
