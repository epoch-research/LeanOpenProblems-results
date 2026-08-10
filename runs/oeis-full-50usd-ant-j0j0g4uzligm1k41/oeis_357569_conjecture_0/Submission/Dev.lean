import FormalConjectures.Util.ProblemImports
open Nat
open scoped BigOperators

namespace OEIS357569

/-- The non-multiples-of-p in `[1,N]`. -/
def II (p N : ℕ) : Finset ℕ := (Finset.Icc 1 N).filter (fun i => ¬ p ∣ i)

lemma mem_II {p N i : ℕ} : i ∈ II p N ↔ (1 ≤ i ∧ i ≤ N) ∧ ¬ p ∣ i := by
  simp [II, Finset.mem_filter, Finset.mem_Icc, and_assoc]

variable {p r : ℕ}

/-- For `i` coprime to `p` (prime), `(i : ZMod (p^r))` is a unit. -/
lemma isUnit_cast {i : ℕ} (hp : p.Prime) (hi : ¬ p ∣ i) :
    IsUnit ((i : ZMod (p ^ r))) := by
  rw [ZMod.isUnit_iff_coprime]
  have h1 : Nat.Coprime i p := (Nat.Prime.coprime_iff_not_dvd hp).mpr hi |>.symm
  exact h1.pow_right r

/-- The involution `g i = ((i:ZMod(p^r))⁻¹).val` reindexes inverse-power sums to power sums. -/
lemma reindex (hp : p.Prime) (hr : 1 ≤ r) (k : ℕ) :
    ∑ i ∈ II p (p ^ r), ((i : ZMod (p ^ r))⁻¹) ^ k
      = ∑ i ∈ II p (p ^ r), ((i : ZMod (p ^ r))) ^ k := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.pos.ne'⟩
  haveI : Fact (1 < p ^ r) := ⟨Nat.one_lt_pow (by omega) hp.one_lt⟩
  set N := p ^ r with hN
  have hpN : p ∣ N := hN ▸ dvd_pow_self p (by omega : r ≠ 0)
  set g : ℕ → ℕ := fun i => ((i : ZMod N)⁻¹).val with hg
  have hcast : ∀ i, ¬ p ∣ i → ((g i : ZMod N)) = ((i : ZMod N)⁻¹) := by
    intro i hi
    simp only [hg]
    exact ZMod.natCast_zmod_val _
  have hmem : ∀ i ∈ II p N, g i ∈ II p N := by
    intro i hi
    rw [mem_II] at hi
    have hunit : IsUnit ((i : ZMod N)) := isUnit_cast hp hi.2
    set u : (ZMod N)ˣ := hunit.unit with hu
    have huval : (↑u : ZMod N) = (i : ZMod N) := IsUnit.unit_spec hunit
    have hgi_lt : g i < N := ZMod.val_lt _
    have hguinv : (↑(u⁻¹) : ZMod N) = (i : ZMod N)⁻¹ := by
      rw [← ZMod.inv_coe_unit, huval]
    have hcop : Nat.Coprime (g i) N := by
      have hco := ZMod.val_coe_unit_coprime (u⁻¹)
      rw [hguinv] at hco; exact hco
    have hndvd : ¬ p ∣ g i := by
      intro hdvd
      have hgcd : p ∣ Nat.gcd (g i) N := Nat.dvd_gcd hdvd hpN
      rw [Nat.Coprime] at hcop
      rw [hcop] at hgcd
      exact hp.ne_one (Nat.dvd_one.mp hgcd)
    rw [mem_II]
    refine ⟨⟨?_, ?_⟩, hndvd⟩
    · rcases Nat.eq_zero_or_pos (g i) with h0 | h0
      · exfalso
        have hz : ((i : ZMod N)⁻¹) = 0 := by
          have hh := hcast i hi.2
          rw [h0] at hh; simpa using hh.symm
        have hiu : IsUnit ((i : ZMod N)⁻¹) := hguinv ▸ (u⁻¹).isUnit
        exact hiu.ne_zero hz
      · exact h0
    · omega
  have hinv : ∀ i ∈ II p N, g (g i) = i := by
    intro i hi
    rw [mem_II] at hi
    have hunit : IsUnit ((i : ZMod N)) := isUnit_cast hp hi.2
    have hndvd_gi : ¬ p ∣ g i := (mem_II.mp (hmem i (mem_II.mpr hi))).2
    have e1 : ((g (g i) : ZMod N)) = ((g i : ZMod N)⁻¹) := hcast _ hndvd_gi
    have e2 : ((g i : ZMod N)) = ((i : ZMod N)⁻¹) := hcast _ hi.2
    have e3 : ((i : ZMod N)⁻¹)⁻¹ = (i : ZMod N) :=
      ZMod.inv_eq_of_mul_eq_one N _ _ (ZMod.inv_mul_of_unit _ hunit)
    have e4 : ((g (g i) : ZMod N)) = (i : ZMod N) := by rw [e1, e2, e3]
    have hlt1 : g (g i) < N := ZMod.val_lt _
    have hlt2 : i < N := by
      rcases lt_or_eq_of_le hi.1.2 with h | h
      · exact h
      · exact absurd (h ▸ hpN) hi.2
    have hc := congrArg ZMod.val e4
    rwa [ZMod.val_natCast_of_lt hlt1, ZMod.val_natCast_of_lt hlt2] at hc
  refine Finset.sum_nbij' g g hmem hmem hinv hinv ?_
  intro a ha
  rw [mem_II] at ha
  rw [hcast a ha.2]


-- Power-sum closed forms over ℤ (Faulhaber), proved by induction.
lemma faul1 (n : ℕ) : 2 * (∑ i ∈ Finset.range (n+1), (i:ℤ)) = n*(n+1) := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ]; push_cast; ring_nf; ring_nf at ih; linarith
lemma faul2 (n : ℕ) : 6 * (∑ i ∈ Finset.range (n+1), (i:ℤ)^2) = n*(n+1)*(2*n+1) := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ]; push_cast; ring_nf; ring_nf at ih; linarith
lemma faul3 (n : ℕ) : 4 * (∑ i ∈ Finset.range (n+1), (i:ℤ)^3) = (n*(n+1))^2 := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ]; push_cast; ring_nf; ring_nf at ih; linarith
lemma faul4 (n : ℕ) : 30 * (∑ i ∈ Finset.range (n+1), (i:ℤ)^4) = n*(n+1)*(2*n+1)*(3*n^2+3*n-1) := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ]; push_cast; ring_nf; ring_nf at ih; linarith

lemma sum_Icc_eq_range (N e : ℕ) (he : 1 ≤ e) :
    (∑ i ∈ Finset.Icc 1 N, (i:ℤ)^e) = ∑ i ∈ Finset.range (N+1), (i:ℤ)^e := by
  apply Finset.sum_subset
  · intro x hx; rw [Finset.mem_Icc] at hx; rw [Finset.mem_range]; omega
  · intro x _ hx
    rw [Finset.mem_Icc] at hx
    have : x = 0 := by rw [Finset.mem_range] at *; omega
    subst this; simp [pow_eq_zero_iff (by omega : e ≠ 0)]

lemma mult_filter_eq (p r : ℕ) (hp : 1 ≤ p) (hr : 1 ≤ r) :
    (Finset.Icc 1 (p^r)).filter (fun i => p ∣ i) = (Finset.Icc 1 (p^(r-1))).image (fun j => p*j) := by
  have hpr : p^r = p * p^(r-1) := by
    conv_lhs => rw [show r = (r-1)+1 by omega]
    rw [pow_succ, mul_comm]
  ext i
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, j, rfl⟩
    refine ⟨j, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos j with h | h
      · subst h; simp at h1
      · exact h
    · rw [hpr] at h2; exact Nat.le_of_mul_le_mul_left h2 (by omega)
  · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, j, rfl⟩
    · have : 0 < p*j := Nat.mul_pos (by omega) (by omega); omega
    · rw [hpr]; exact Nat.mul_le_mul_left p hj2

lemma II_sum_reduce (p r e : ℕ) (hp : 1 ≤ p) (hr : 1 ≤ r) (he : 1 ≤ e) :
    (∑ i ∈ II p (p^r), (i:ℤ)^e)
      = (∑ i ∈ Finset.range (p^r+1), (i:ℤ)^e)
        - (p:ℤ)^e * (∑ j ∈ Finset.range (p^(r-1)+1), (j:ℤ)^e) := by
  have hsplit : (∑ i ∈ Finset.Icc 1 (p^r), (i:ℤ)^e)
      = (∑ i ∈ II p (p^r), (i:ℤ)^e)
        + ∑ i ∈ (Finset.Icc 1 (p^r)).filter (fun i => p ∣ i), (i:ℤ)^e := by
    rw [II]
    rw [add_comm]
    exact (Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (p^r)) (fun i => p ∣ i) _).symm
  have hmult : (∑ i ∈ (Finset.Icc 1 (p^r)).filter (fun i => p ∣ i), (i:ℤ)^e)
      = (p:ℤ)^e * ∑ j ∈ Finset.Icc 1 (p^(r-1)), (j:ℤ)^e := by
    rw [mult_filter_eq p r hp hr, Finset.sum_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left (by omega) h)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _; push_cast; ring
  rw [sum_Icc_eq_range (p^r) e he] at hsplit
  rw [hmult, sum_Icc_eq_range (p^(r-1)) e he] at hsplit
  linarith

end OEIS357569

namespace OEIS357569

lemma dvd_six_J2 (p r : ℕ) (hp : 1 ≤ p) (hr : 1 ≤ r) :
    (p:ℤ)^r ∣ 6 * (∑ i ∈ II p (p^r), (i:ℤ)^2) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m+1 := ⟨r-1, by omega⟩
  rw [II_sum_reduce p (m+1) 2 hp hr (by norm_num)]
  simp only [Nat.add_sub_cancel]
  have h1 := faul2 (p^(m+1))
  have h2 := faul2 (p^m)
  push_cast at h1 h2 ⊢
  refine ⟨((p:ℤ)^(m+1)+1)*(2*(p:ℤ)^(m+1)+1) - p*(((p:ℤ)^m+1)*(2*(p:ℤ)^m+1)), ?_⟩
  linear_combination h1 - (p:ℤ)^2 * h2

lemma dvd_thirty_J4 (p r : ℕ) (hp : 1 ≤ p) (hr : 1 ≤ r) :
    (p:ℤ)^r ∣ 30 * (∑ i ∈ II p (p^r), (i:ℤ)^4) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m+1 := ⟨r-1, by omega⟩
  rw [II_sum_reduce p (m+1) 4 hp hr (by norm_num)]
  simp only [Nat.add_sub_cancel]
  have h1 := faul4 (p^(m+1))
  have h2 := faul4 (p^m)
  push_cast at h1 h2 ⊢
  refine ⟨((p:ℤ)^(m+1)+1)*(2*(p:ℤ)^(m+1)+1)*(3*((p:ℤ)^(m+1))^2+3*(p:ℤ)^(m+1)-1)
        - p^3*(((p:ℤ)^m+1)*(2*(p:ℤ)^m+1)*(3*((p:ℤ)^m)^2+3*(p:ℤ)^m-1)), ?_⟩
  linear_combination h1 - (p:ℤ)^4 * h2

end OEIS357569

namespace OEIS357569

lemma prod_Icc_fact (n : ℕ) : ∏ i ∈ Finset.Icc 1 n, i = n ! := by
  rw [show Finset.Icc 1 n = Finset.Ico 1 (n+1) from (Finset.Ico_succ_right_eq_Icc 1 n).symm,
    Finset.prod_Ico_id_eq_factorial]

-- product over multiples of p in Icc 1 N equals p^M * M!
lemma prod_mult_Icc (p r : ℕ) (hp : 1 ≤ p) (hr : 1 ≤ r) :
    ∏ i ∈ (Finset.Icc 1 (p^r)).filter (fun i => p ∣ i), i
      = p^(p^(r-1)) * (p^(r-1))! := by
  rw [mult_filter_eq p r hp hr, Finset.prod_image
    (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left (by omega) h)]
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  congr 1
  · congr 1
    rw [Nat.card_Icc]; omega
  · rw [prod_Icc_fact]

lemma prodD (p r : ℕ) (hp : 1 ≤ p) (hr : 1 ≤ r) :
    (∏ i ∈ II p (p^r), i) * (p^(p^(r-1)) * (p^(r-1))!) = (p^r)! := by
  rw [← prod_mult_Icc p r hp hr]
  rw [II, mul_comm]
  rw [Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (p^r)) (fun i => p ∣ i)]
  rw [prod_Icc_fact]

end OEIS357569

namespace OEIS357569
open Finset

lemma dvd_of_val_dvd {p m k : ℕ} [NeZero (p^m)] (x : ZMod (p^m)) (h : p^k ∣ x.val) :
    ((p : ZMod (p^m)))^k ∣ x := by
  obtain ⟨t, ht⟩ := h
  have hx : ((x.val : ℕ) : ZMod (p^m)) = x := ZMod.natCast_zmod_val x
  refine ⟨(t : ZMod (p^m)), ?_⟩
  rw [← hx, ht]; push_cast; ring

lemma dvd_of_cast_eq_zero {p m k : ℕ} [NeZero (p^m)] (x : ZMod (p^m))
    (h : ((x.val : ℕ) : ZMod (p^k)) = 0) :
    ((p : ZMod (p^m)))^k ∣ x := by
  apply dvd_of_val_dvd
  rwa [ZMod.natCast_eq_zero_iff] at h

lemma dvd_cast_of_int {p m k : ℕ} {c : ℤ} (h : (p:ℤ)^k ∣ c) :
    ((p : ZMod (p^m)))^k ∣ (c : ZMod (p^m)) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨(t : ZMod (p^m)), ?_⟩
  rw [ht]; push_cast; ring

lemma prod_one_add_eq {ι R : Type*} [CommRing R] (s : Finset ι) (a : ι → R) :
    ∏ i ∈ s, (1 + a i) = ∑ j ∈ range (#s + 1), ∑ t ∈ s.powersetCard j, ∏ i ∈ t, a i := by
  classical
  have h1 : ∏ i ∈ s, (1 + a i) = ∑ t ∈ s.powerset, ∏ i ∈ t, a i := by
    rw [show (∏ i ∈ s, (1 + a i)) = ∏ i ∈ s, (a i + 1) from by simp [add_comm]]
    rw [Finset.prod_add]; simp
  rw [h1, Finset.sum_powerset]

lemma sum_powersetCard_one {ι R : Type*} [CommRing R] (s : Finset ι) (a : ι → R) :
    ∑ t ∈ s.powersetCard 1, ∏ i ∈ t, a i = ∑ i ∈ s, a i := by
  classical
  rw [Finset.powersetCard_one, Finset.sum_map]
  apply Finset.sum_congr rfl; intro i _; simp

lemma prod_one_add_dvd_tail {ι R : Type*} [CommRing R] (s : Finset ι) (a : ι → R)
    (q : R) (e : ℕ) (ha : ∀ i ∈ s, q^e ∣ a i) (hs : 2 ≤ #s) :
    q^(3*e) ∣ (∏ i ∈ s, (1 + a i) - 1
      - (∑ i ∈ s, a i) - (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, a i)) := by
  classical
  have hexp : ∏ i ∈ s, (1 + a i)
      = 1 + (∑ i ∈ s, a i) + (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, a i)
        + (∑ j ∈ Finset.Ico 3 (#s+1), ∑ t ∈ s.powersetCard j, ∏ i ∈ t, a i) := by
    rw [prod_one_add_eq, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (show 0 ≤ 3 by omega) (show 3 ≤ #s + 1 by omega),
      show Finset.Ico 0 3 = {0,1,2} from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      Finset.powersetCard_zero, Finset.sum_singleton, Finset.prod_empty, sum_powersetCard_one]
    ring
  set A := ∑ i ∈ s, a i
  set B := ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, a i
  set C := ∑ j ∈ Finset.Ico 3 (#s+1), ∑ t ∈ s.powersetCard j, ∏ i ∈ t, a i with hC
  rw [hexp, show 1 + A + B + C - 1 - A - B = C from by ring, hC]
  apply Finset.dvd_sum
  intro j hj
  rw [Finset.mem_Ico] at hj
  apply Finset.dvd_sum
  intro t ht
  rw [Finset.mem_powersetCard] at ht
  obtain ⟨hts, htc⟩ := ht
  calc q^(3*e) ∣ q^(e * #t) := by
        apply pow_dvd_pow; rw [htc]; nlinarith [hj.1]
    _ = ∏ i ∈ t, q^e := by rw [Finset.prod_const, ← pow_mul]
    _ ∣ ∏ i ∈ t, a i := Finset.prod_dvd_prod_of_dvd _ _ (fun i hi => ha i (hts hi))

lemma pdvd_of_pow_dvd_mul {p : ℕ} (hp : p.Prime) {c J : ℤ} {r : ℕ}
    (hc : ¬ (p:ℤ)^2 ∣ c) (hr : 2 ≤ r) (h : (p:ℤ)^r ∣ c * J) : (p:ℤ) ∣ J := by
  have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : (p:ℤ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  have key : (p:ℤ)^(r-1) ∣ J := by
    by_cases hpc : (p:ℤ) ∣ c
    · obtain ⟨c', rfl⟩ := hpc
      have hpc' : ¬ (p:ℤ) ∣ c' := by
        intro ⟨d, hd⟩; exact hc ⟨d, by rw [hd]; ring⟩
      have h2 : (p:ℤ)^(r-1) ∣ c' * J := by
        have he : (p:ℤ)^r = (p:ℤ) * (p:ℤ)^(r-1) := by
          conv_lhs => rw [show r = (r-1)+1 by omega]
          rw [pow_succ, mul_comm]
        rw [he, show (p:ℤ) * c' * J = (p:ℤ) * (c' * J) by ring] at h
        exact (mul_dvd_mul_iff_left hp0).mp h
      have hco : IsCoprime ((p:ℤ)^(r-1)) c' :=
        IsCoprime.pow_left (hpp.coprime_iff_not_dvd.mpr hpc')
      exact hco.dvd_of_dvd_mul_left h2
    · have hco : IsCoprime ((p:ℤ)^r) c := IsCoprime.pow_left (hpp.coprime_iff_not_dvd.mpr hpc)
      exact dvd_trans (pow_dvd_pow _ (by omega)) (hco.dvd_of_dvd_mul_left h)
  exact dvd_trans (by simpa using pow_dvd_pow (p:ℤ) (show 1 ≤ r-1 by omega)) key

end OEIS357569

namespace OEIS357569
open Finset

lemma castval_eq {p m k : ℕ} [NeZero (p^m)] (hkm : p^k ∣ p^m) (x : ZMod (p^m)) :
    ((x.val : ℕ) : ZMod (p^k)) = ZMod.castHom hkm (ZMod (p^k)) x := by
  rw [ZMod.castHom_apply, ZMod.natCast_val]

lemma map_cast_inv {p m k n : ℕ} [NeZero (p^m)] (hp : p.Prime) (hn : ¬ p ∣ n)
    (f : ZMod (p^m) →+* ZMod (p^k)) :
    f ((n : ZMod (p^m))⁻¹) = ((n : ZMod (p^k)))⁻¹ := by
  have hu : IsUnit ((n : ZMod (p^m))) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn).symm.pow_right m
  have h1 : (n : ZMod (p^m))⁻¹ * (n : ZMod (p^m)) = 1 := ZMod.inv_mul_of_unit _ hu
  have h2 := congrArg f h1
  rw [map_mul, map_one, map_natCast] at h2
  have h3 : ((n : ZMod (p^k))) * f ((n : ZMod (p^m))⁻¹) = 1 := by rw [mul_comm]; exact h2
  exact (ZMod.inv_eq_of_mul_eq_one _ _ _ h3).symm

lemma inv_neg_unit {n : ℕ} {a : ZMod n} (h : IsUnit a) : (-a)⁻¹ = -a⁻¹ := by
  have : (-a) * (-a⁻¹) = 1 := by rw [neg_mul_neg]; exact ZMod.mul_inv_of_unit _ h
  exact (ZMod.inv_eq_of_mul_eq_one _ _ _ this)

lemma inv_sq_unit {n : ℕ} {a : ZMod n} (h : IsUnit a) : (a^2)⁻¹ = (a⁻¹)^2 := by
  have : (a^2) * (a⁻¹)^2 = 1 := by rw [← mul_pow, ZMod.mul_inv_of_unit _ h]; ring
  exact (ZMod.inv_eq_of_mul_eq_one _ _ _ this)

/-- The reduced form of a single `1/(i(N-i))` term modulo `p^s` (with `s ≤ r`). -/
lemma red_term {p r s m : ℕ} (hp : p.Prime) (hr : 1 ≤ r) (hsr : s ≤ r)
    [NeZero (p^m)] [NeZero (p^s)]
    (f : ZMod (p^m) →+* ZMod (p^s)) {i : ℕ} (hi : i ∈ II p (p^r)) :
    f ((((i*(p^r-i):ℕ)) : ZMod (p^m))⁻¹) = -(((i : ZMod (p^s)))⁻¹)^2 := by
  rw [mem_II] at hi
  obtain ⟨⟨hi1, hi2⟩, hip⟩ := hi
  have hpN : p ∣ p^r := dvd_pow_self p (by omega : r ≠ 0)
  have hni : ¬ p ∣ (p^r - i) := by
    intro hd; apply hip
    have he : i = p^r - (p^r - i) := by omega
    rw [he]; exact Nat.dvd_sub hpN hd
  have hnprod : ¬ p ∣ (i*(p^r-i)) := by rw [hp.dvd_mul]; push_neg; exact ⟨hip, hni⟩
  rw [map_cast_inv hp hnprod f]
  have hu : IsUnit ((i : ZMod (p^s))) := isUnit_cast hp hip
  have hcast : ((i*(p^r-i) : ℕ) : ZMod (p^s)) = -((i : ZMod (p^s))^2) := by
    push_cast
    rw [Nat.cast_sub hi2]
    have : ((p^r : ℕ) : ZMod (p^s)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]; exact pow_dvd_pow p hsr
    rw [this]; ring
  rw [hcast, inv_neg_unit (h := hu.pow 2), inv_sq_unit hu]

end OEIS357569

namespace OEIS357569
open Finset

lemma sum_pow_cast_eq {p r s k : ℕ} [NeZero (p^s)] :
    ∑ i ∈ II p (p^r), ((i:ZMod (p^s)))^k
      = ((∑ i ∈ II p (p^r), (i:ℤ)^k : ℤ) : ZMod (p^s)) := by
  push_cast; rfl

lemma not_pp_six {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) : ¬ (p:ℤ)^2 ∣ (6:ℤ) := by
  intro h
  have := Int.le_of_dvd (by norm_num) h
  have : (p:ℤ)^2 ≤ 6 := this
  nlinarith [hp3, (by exact_mod_cast hp3 : (3:ℤ) ≤ p)]

lemma not_pp_thirty {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) : ¬ (p:ℤ)^2 ∣ (30:ℤ) := by
  intro h
  have hle := Int.le_of_dvd (by norm_num) h
  have hpc : (3:ℤ) ≤ p := by exact_mod_cast hp3
  have : (p:ℤ) ≤ 5 := by nlinarith [hle, hpc]
  have hub : p ≤ 5 := by exact_mod_cast this
  interval_cases p <;> norm_num at h

end OEIS357569

namespace OEIS357569
open Finset

lemma pdvd_J2 {p r : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 2 ≤ r) :
    (p:ℤ) ∣ ∑ i ∈ II p (p^r), (i:ℤ)^2 :=
  pdvd_of_pow_dvd_mul hp (not_pp_six hp hp3) hr (dvd_six_J2 p r (by omega) (by omega))

lemma pdvd_J4 {p r : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 2 ≤ r) :
    (p:ℤ) ∣ ∑ i ∈ II p (p^r), (i:ℤ)^4 :=
  pdvd_of_pow_dvd_mul hp (not_pp_thirty hp hp3) hr (dvd_thirty_J4 p r (by omega) (by omega))

lemma castpr {p r : ℕ} : ((p^r : ℕ) : ℤ) = (p:ℤ)^r := by push_cast; ring

lemma dvd_six_S {p r m : ℕ} (hp : p.Prime) (hr : 2 ≤ r) (hrm : r ≤ m) [NeZero (p^m)] :
    ((p : ZMod (p^m)))^r ∣ 6 * ∑ i ∈ II p (p^r), (((i*(p^r-i):ℕ)) : ZMod (p^m))⁻¹ := by
  haveI : NeZero (p^r) := ⟨pow_ne_zero r hp.pos.ne'⟩
  apply dvd_of_cast_eq_zero
  rw [castval_eq (pow_dvd_pow p hrm)]
  set f := ZMod.castHom (pow_dvd_pow p hrm) (ZMod (p^r)) with hf
  rw [map_mul, map_sum]
  rw [Finset.sum_congr rfl (fun i hi => red_term hp (by omega) (le_refl r) f hi)]
  rw [Finset.sum_neg_distrib, reindex hp (by omega) 2, map_ofNat, sum_pow_cast_eq]
  have hd : (6:ZMod (p^r)) * ((∑ i ∈ II p (p^r), (i:ℤ)^2 : ℤ) : ZMod (p^r)) = 0 := by
    have h0 : ((6 * ∑ i ∈ II p (p^r), (i:ℤ)^2 : ℤ) : ZMod (p^r)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, castpr]
      exact dvd_six_J2 p r hp.pos (by omega)
    rwa [Int.cast_mul, Int.cast_ofNat] at h0
  rw [mul_neg, hd, neg_zero]

lemma S_def_bridge {p r m : ℕ} (hp : p.Prime) (hr : 2 ≤ r) (hrm : r ≤ m) [NeZero (p^m)] :
    ((p : ZMod (p^m)))^r ∣
      (∑ i ∈ II p (p^r), (((i*(p^r-i):ℕ)) : ZMod (p^m))⁻¹
        + ((∑ i ∈ II p (p^r), (i:ℤ)^2 : ℤ) : ZMod (p^m))) := by
  haveI : NeZero (p^r) := ⟨pow_ne_zero r hp.pos.ne'⟩
  apply dvd_of_cast_eq_zero
  rw [castval_eq (pow_dvd_pow p hrm)]
  set f := ZMod.castHom (pow_dvd_pow p hrm) (ZMod (p^r)) with hf
  rw [map_add, map_sum,
    Finset.sum_congr rfl (fun i hi => red_term hp (by omega) (le_refl r) f hi),
    Finset.sum_neg_distrib, reindex hp (by omega) 2, map_intCast,
    ← sum_pow_cast_eq, neg_add_cancel]

lemma V_def_bridge {p r m : ℕ} (hp : p.Prime) (hr : 2 ≤ r) (hrm : r ≤ m) [NeZero (p^m)] :
    ((p : ZMod (p^m)))^r ∣
      (∑ i ∈ II p (p^r), ((((i*(p^r-i):ℕ)) : ZMod (p^m))⁻¹)^2
        - ((∑ i ∈ II p (p^r), (i:ℤ)^4 : ℤ) : ZMod (p^m))) := by
  haveI : NeZero (p^r) := ⟨pow_ne_zero r hp.pos.ne'⟩
  apply dvd_of_cast_eq_zero
  rw [castval_eq (pow_dvd_pow p hrm)]
  set f := ZMod.castHom (pow_dvd_pow p hrm) (ZMod (p^r)) with hf
  have hterm : ∀ i ∈ II p (p^r),
      f (((((i*(p^r-i):ℕ)) : ZMod (p^m))⁻¹)^2) = (((i : ZMod (p^r)))⁻¹)^4 := by
    intro i hi; rw [map_pow, red_term hp (by omega) (le_refl r) f hi]; ring
  rw [map_sub, map_sum, Finset.sum_congr rfl hterm, reindex hp (by omega) 4, map_intCast,
    ← sum_pow_cast_eq, sub_self]

lemma dvd_S {p r m : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 2 ≤ r) (hrm : r ≤ m) [NeZero (p^m)] :
    ((p : ZMod (p^m)))^1 ∣ ∑ i ∈ II p (p^r), (((i*(p^r-i):ℕ)) : ZMod (p^m))⁻¹ := by
  have hb := S_def_bridge hp hr hrm
  have hJ : ((p : ZMod (p^m)))^1 ∣ ((∑ i ∈ II p (p^r), (i:ℤ)^2 : ℤ) : ZMod (p^m)) :=
    dvd_cast_of_int (by simpa using pdvd_J2 hp hp3 hr)
  have h1 : ((p : ZMod (p^m)))^1 ∣
      (∑ i ∈ II p (p^r), (((i*(p^r-i):ℕ)) : ZMod (p^m))⁻¹
        + ((∑ i ∈ II p (p^r), (i:ℤ)^2 : ℤ) : ZMod (p^m))) :=
    dvd_trans (pow_dvd_pow _ (by omega)) hb
  have := dvd_sub h1 hJ
  simpa using this

lemma dvd_V {p r m : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 2 ≤ r) (hrm : r ≤ m) [NeZero (p^m)] :
    ((p : ZMod (p^m)))^1 ∣ ∑ i ∈ II p (p^r), ((((i*(p^r-i):ℕ)) : ZMod (p^m))⁻¹)^2 := by
  have hb := V_def_bridge hp hr hrm
  have hJ : ((p : ZMod (p^m)))^1 ∣ ((∑ i ∈ II p (p^r), (i:ℤ)^4 : ℤ) : ZMod (p^m)) :=
    dvd_cast_of_int (by simpa using pdvd_J4 hp hp3 hr)
  have h1 : ((p : ZMod (p^m)))^1 ∣
      (∑ i ∈ II p (p^r), ((((i*(p^r-i):ℕ)) : ZMod (p^m))⁻¹)^2
        - ((∑ i ∈ II p (p^r), (i:ℤ)^4 : ℤ) : ZMod (p^m))) :=
    dvd_trans (pow_dvd_pow _ (by omega)) hb
  have := dvd_add h1 hJ
  simpa using this
end OEIS357569

namespace OEIS357569
open Finset

lemma factratio (a b : ℕ) (h : a ≤ b) : a ! * ∏ j ∈ Finset.Icc (a+1) b, j = b ! := by
  rw [show Finset.Icc (a+1) b = Finset.Ico (a+1) (b+1) from
        (Finset.Ico_succ_right_eq_Icc (a+1) b).symm,
    show a ! = ∏ x ∈ Finset.Ico 1 (a+1), x from (Finset.prod_Ico_id_eq_factorial a).symm,
    show b ! = ∏ x ∈ Finset.Ico 1 (b+1), x from (Finset.prod_Ico_id_eq_factorial b).symm]
  exact Finset.prod_Ico_consecutive _ (by omega) (by omega)

lemma mult_filter_gen (p M : ℕ) (hp : 1 ≤ p) :
    (Finset.Icc 1 (p*M)).filter (fun i => p ∣ i) = (Finset.Icc 1 M).image (fun j => p*j) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, j, rfl⟩
    have hj0 : 0 < j := by
      rcases Nat.eq_zero_or_pos j with h|h
      · simp [h] at h1
      · exact h
    exact ⟨j, ⟨hj0, Nat.le_of_mul_le_mul_left h2 (by omega)⟩, rfl⟩
  · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
    exact ⟨⟨by have : 0 < p*j := Nat.mul_pos (by omega) (by omega); omega,
      Nat.mul_le_mul_left p hj2⟩, j, rfl⟩

lemma mult_filter_Ioc (p M c : ℕ) (hp : 1 ≤ p) :
    (Finset.Icc (c*(p*M)+1) ((c+1)*(p*M))).filter (fun i => p ∣ i)
      = (Finset.Icc (c*M+1) ((c+1)*M)).image (fun j => p*j) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, j, rfl⟩
    refine ⟨j, ⟨?_, ?_⟩, rfl⟩
    · have : c*(p*M) < p*j := by omega
      have hcm : c*(p*M) = p*(c*M) := by ring
      rw [hcm] at this
      have := Nat.lt_of_mul_lt_mul_left this
      omega
    · have hcm : (c+1)*(p*M) = p*((c+1)*M) := by ring
      rw [hcm] at h2
      exact Nat.le_of_mul_le_mul_left h2 (by omega)
  · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, j, rfl⟩
    · have hcm : c*(p*M) = p*(c*M) := by ring
      rw [hcm]
      have : p*(c*M) < p*j := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      omega
    · have hcm : (c+1)*(p*M) = p*((c+1)*M) := by ring
      rw [hcm]; exact Nat.mul_le_mul_left p hj2

end OEIS357569

namespace OEIS357569
open Finset

lemma prod_mult_gen (p M : ℕ) (hp : 1 ≤ p) :
    ∏ i ∈ (Finset.Icc 1 (p*M)).filter (fun i => p ∣ i), i = p^M * M ! := by
  rw [mult_filter_gen p M hp,
    Finset.prod_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left (by omega) h),
    Finset.prod_mul_distrib, Finset.prod_const]
  congr 1
  · congr 1; rw [Nat.card_Icc]; omega
  · rw [prod_Icc_fact]

lemma prodD_gen (p M : ℕ) (hp : 1 ≤ p) :
    (∏ i ∈ II p (p*M), i) * (p^M * M !) = (p*M)! := by
  rw [← prod_mult_gen p M hp, II, mul_comm,
    Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (p*M)) (fun i => p ∣ i), prod_Icc_fact]

lemma prod_mult_Ioc (p M c : ℕ) (hp : 1 ≤ p) :
    ∏ i ∈ (Finset.Icc (c*(p*M)+1) ((c+1)*(p*M))).filter (fun i => p ∣ i), i
      = p^M * ∏ l ∈ Finset.Icc (c*M+1) ((c+1)*M), l := by
  rw [mult_filter_Ioc p M c hp,
    Finset.prod_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left (by omega) h),
    Finset.prod_mul_distrib, Finset.prod_const]
  congr 1
  congr 1; rw [Nat.card_Icc]
  have : (c+1)*M = c*M+M := by ring
  omega

lemma prodII_shift (p M c : ℕ) (hp : 1 ≤ p) :
    ∏ i ∈ II p (p*M), (c*(p*M)+i)
      = ∏ j ∈ (Finset.Icc (c*(p*M)+1) ((c+1)*(p*M))).filter (fun j => ¬ p ∣ j), j := by
  have hpd : p ∣ c*(p*M) := ⟨c*M, by ring⟩
  have hexp : (c+1)*(p*M) = c*(p*M) + p*M := by ring
  have hset : (II p (p*M)).image (fun i => c*(p*M)+i)
      = (Finset.Icc (c*(p*M)+1) ((c+1)*(p*M))).filter (fun j => ¬ p ∣ j) := by
    ext j
    simp only [Finset.mem_image, mem_II, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨i, ⟨⟨hi1, hi2⟩, hip⟩, rfl⟩
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      intro hd; apply hip
      have : i = (c*(p*M)+i) - c*(p*M) := by omega
      rw [this]; exact Nat.dvd_sub hd hpd
    · rintro ⟨⟨hj1, hj2⟩, hjp⟩
      refine ⟨j - c*(p*M), ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      intro hd; apply hjp
      have : j = (j - c*(p*M)) + c*(p*M) := by omega
      rw [this]; exact Nat.dvd_add hd hpd
  symm
  rw [← hset]
  exact Finset.prod_image (g := fun i => c*(p*M)+i) (fun a _ b _ h => by simpa using h)

end OEIS357569

namespace OEIS357569
open Finset

lemma Cmul_R (p M : ℕ) (hp : 1 ≤ p) (hM : 1 ≤ M) :
    (3*(p*M)).choose (p*M) * (∏ i ∈ II p (p*M), i)
      = (3*M).choose M * (∏ i ∈ II p (p*M), (2*(p*M)+i)) := by
  have hRmult : (∏ i ∈ II p (p*M), (2*(p*M)+i)) * (p^M * (∏ l ∈ Finset.Icc (2*M+1) (3*M), l))
      = ∏ j ∈ Finset.Icc (2*(p*M)+1) (3*(p*M)), j := by
    have h2 := prod_mult_Ioc p M 2 hp
    have h1 := prodII_shift p M 2 hp
    rw [show (2+1)*(p*M) = 3*(p*M) from by ring] at h2 h1
    rw [h1, ← h2, Finset.prod_filter_not_mul_prod_filter]
  have hfN : (2*(p*M))! * (∏ j ∈ Finset.Icc (2*(p*M)+1) (3*(p*M)), j) = (3*(p*M))! :=
    factratio (2*(p*M)) (3*(p*M)) (by omega)
  have hfM : (2*M)! * (∏ l ∈ Finset.Icc (2*M+1) (3*M), l) = (3*M)! :=
    factratio (2*M) (3*M) (by omega)
  have hD : (∏ i ∈ II p (p*M), i) * (p^M * M !) = (p*M)! := prodD_gen p M hp
  have hcN : (3*(p*M)).choose (p*M) * ((p*M)! * (2*(p*M))!) = (3*(p*M))! := by
    have h := Nat.add_choose_mul_factorial_mul_factorial (2*(p*M)) (p*M)
    rw [show 2*(p*M)+(p*M) = 3*(p*M) from by ring] at h
    rw [← h]; ring
  have hcM : (3*M).choose M * (M ! * (2*M)!) = (3*M)! := by
    have h := Nat.add_choose_mul_factorial_mul_factorial (2*M) M
    rw [show 2*M+M = 3*M from by ring] at h
    rw [← h]; ring
  set PN := ∏ j ∈ Finset.Icc (2*(p*M)+1) (3*(p*M)), j with hPN
  set PM := ∏ l ∈ Finset.Icc (2*M+1) (3*M), l with hPM
  set Dpr := ∏ i ∈ II p (p*M), i with hDpr
  set Rpr := ∏ i ∈ II p (p*M), (2*(p*M)+i) with hRpr
  set Z := (2*(p*M))! * (2*M)! * p^M * M ! with hZ
  have hZpos : 0 < Z := by positivity
  apply Nat.eq_of_mul_eq_mul_right hZpos
  have e1 : (3*(p*M)).choose (p*M) * Dpr * Z = (3*(p*M))! * (2*M)! := by
    have h : (3*(p*M)).choose (p*M) * Dpr * Z
        = (3*(p*M)).choose (p*M) * (Dpr * (p^M * M !)) * ((2*(p*M))! * (2*M)!) := by
      rw [hZ]; ring
    rw [h, hD, show (3*(p*M)).choose (p*M) * (p*M)! * ((2*(p*M))! * (2*M)!)
        = ((3*(p*M)).choose (p*M) * ((p*M)! * (2*(p*M))!)) * (2*M)! from by ring, hcN]
  have e2 : (3*M).choose M * Rpr * Z = (3*(p*M))! * (2*M)! := by
    have s1 : (3*M).choose M * Rpr * Z
        = ((3*M).choose M * (M ! * (2*M)!)) * ((2*(p*M))! * Rpr * p^M) := by rw [hZ]; ring
    rw [s1, hcM, ← hfM,
      show (2*M)! * PM * ((2*(p*M))! * Rpr * p^M) = (2*(p*M))! * (Rpr * (p^M * PM)) * (2*M)! from by ring,
      hRmult, hfN]
  rw [e1, e2]


lemma Cmul_Q (p M : ℕ) (hp : 1 ≤ p) (hM : 1 ≤ M) :
    (2*(p*M)).choose (p*M) * (∏ i ∈ II p (p*M), i)
      = (2*M).choose M * (∏ i ∈ II p (p*M), ((p*M)+i)) := by
  have hQmult : (∏ i ∈ II p (p*M), ((p*M)+i)) * (p^M * (∏ l ∈ Finset.Icc (M+1) (2*M), l))
      = ∏ j ∈ Finset.Icc ((p*M)+1) (2*(p*M)), j := by
    have h2 := prod_mult_Ioc p M 1 hp
    have h1 := prodII_shift p M 1 hp
    simp only [one_mul, show (1+1)*(p*M) = 2*(p*M) from by ring,
      show (1+1)*M = 2*M from by ring] at h2 h1
    rw [h1, ← h2, Finset.prod_filter_not_mul_prod_filter]
  have hfN : (p*M)! * (∏ j ∈ Finset.Icc ((p*M)+1) (2*(p*M)), j) = (2*(p*M))! :=
    factratio (p*M) (2*(p*M)) (by omega)
  have hfM : M ! * (∏ l ∈ Finset.Icc (M+1) (2*M), l) = (2*M)! :=
    factratio M (2*M) (by omega)
  have hD : (∏ i ∈ II p (p*M), i) * (p^M * M !) = (p*M)! := prodD_gen p M hp
  have hcN : (2*(p*M)).choose (p*M) * ((p*M)! * (p*M)!) = (2*(p*M))! := by
    have h := Nat.add_choose_mul_factorial_mul_factorial (p*M) (p*M)
    rw [show (p*M)+(p*M) = 2*(p*M) from by ring] at h
    rw [← h]; ring
  have hcM : (2*M).choose M * (M ! * M !) = (2*M)! := by
    have h := Nat.add_choose_mul_factorial_mul_factorial M M
    rw [show M+M = 2*M from by ring] at h
    rw [← h]; ring
  set PN := ∏ j ∈ Finset.Icc ((p*M)+1) (2*(p*M)), j with hPN
  set PM := ∏ l ∈ Finset.Icc (M+1) (2*M), l with hPM
  set Dpr := ∏ i ∈ II p (p*M), i with hDpr
  set Qpr := ∏ i ∈ II p (p*M), ((p*M)+i) with hQpr
  set Z := (p*M)! * M ! * M ! * p^M with hZ
  have hZpos : 0 < Z := by positivity
  apply Nat.eq_of_mul_eq_mul_right hZpos
  have e1 : (2*(p*M)).choose (p*M) * Dpr * Z = (2*(p*M))! * M ! := by
    have h : (2*(p*M)).choose (p*M) * Dpr * Z
        = (2*(p*M)).choose (p*M) * (Dpr * (p^M * M !)) * ((p*M)! * M !) := by rw [hZ]; ring
    rw [h, hD, show (2*(p*M)).choose (p*M) * (p*M)! * ((p*M)! * M !)
        = ((2*(p*M)).choose (p*M) * ((p*M)! * (p*M)!)) * M ! from by ring, hcN]
  have e2 : (2*M).choose M * Qpr * Z = (2*(p*M))! * M ! := by
    have s1 : (2*M).choose M * Qpr * Z
        = ((2*M).choose M * (M ! * M !)) * ((p*M)! * (Qpr * p^M)) := by rw [hZ]; ring
    rw [s1, hcM, ← hfM,
      show (M ! * PM) * ((p*M)! * (Qpr * p^M)) = (p*M)! * (Qpr * (p^M * PM)) * M ! from by ring,
      hQmult, ← hfN, mul_comm]
  rw [e1, e2]

end OEIS357569

namespace OEIS357569
open Finset

lemma uinv_mul {n a b : ℕ} (ha : IsUnit ((a:ZMod n))) (hb : IsUnit ((b:ZMod n))) :
    ((a:ZMod n))⁻¹ * ((b:ZMod n))⁻¹ = ((a*b : ℕ):ZMod n)⁻¹ := by
  have h : ((a*b:ℕ):ZMod n) * (((a:ZMod n))⁻¹ * ((b:ZMod n))⁻¹) = 1 := by
    push_cast
    rw [show (a:ZMod n)*(b:ZMod n)*((a:ZMod n)⁻¹*(b:ZMod n)⁻¹)
        = ((a:ZMod n)*(a:ZMod n)⁻¹)*((b:ZMod n)*(b:ZMod n)⁻¹) from by ring,
      ZMod.mul_inv_of_unit _ ha, ZMod.mul_inv_of_unit _ hb, mul_one]
  exact (ZMod.inv_eq_of_mul_eq_one _ _ _ h).symm

/-- The pairing factorization of `(1 + c·xᵢ)(1 + c·x_{N-i})`. -/
lemma pair_eq {p E N i : ℕ} [NeZero (p^E)] (hp : p.Prime) (hpN : p ∣ N) (hi : i ∈ II p N)
    (c : ZMod (p^E)) :
    (1 + c * ((i:ZMod (p^E)))⁻¹) * (1 + c * (((N-i:ℕ)):ZMod (p^E))⁻¹)
      = 1 + (c * ((N:ℕ):ZMod (p^E)) + c*c) * (((i*(N-i):ℕ)):ZMod (p^E))⁻¹ := by
  rw [mem_II] at hi
  obtain ⟨⟨hi1, hi2⟩, hip⟩ := hi
  have hni : ¬ p ∣ (N - i) := by
    intro hd; apply hip
    have : i = N - (N - i) := by omega
    rw [this]; exact Nat.dvd_sub hpN hd
  have hu : IsUnit ((i:ZMod (p^E))) := isUnit_cast hp hip
  have hv : IsUnit (((N-i:ℕ)):ZMod (p^E)) := isUnit_cast hp hni
  set u := (i:ZMod (p^E))
  set v := (((N-i:ℕ)):ZMod (p^E))
  have hAprod : u⁻¹ * v⁻¹ = (((i*(N-i):ℕ)):ZMod (p^E))⁻¹ := by
    have := uinv_mul (n := p^E) hu hv; simpa [u, v] using this
  have hsum : u + v = ((N:ℕ):ZMod (p^E)) := by
    rw [show u + v = ((i:ℕ):ZMod (p^E)) + (((N-i:ℕ)):ZMod (p^E)) from rfl]
    rw [← Nat.cast_add, show i + (N-i) = N from by omega]
  have hBgen : u⁻¹ + v⁻¹ = (u + v) * (u⁻¹ * v⁻¹) := by
    rw [add_mul,
      show (u⁻¹ * v⁻¹) = (u⁻¹ * v⁻¹) from rfl]
    rw [show u * (u⁻¹ * v⁻¹) = (u * u⁻¹) * v⁻¹ from by ring,
      show v * (u⁻¹ * v⁻¹) = (v * v⁻¹) * u⁻¹ from by ring,
      ZMod.mul_inv_of_unit _ hu, ZMod.mul_inv_of_unit _ hv, one_mul, one_mul, add_comm]
  have hB : u⁻¹ + v⁻¹ = ((N:ℕ):ZMod (p^E)) * (((i*(N-i):ℕ)):ZMod (p^E))⁻¹ := by
    rw [hBgen, hsum, hAprod]
  have key : (1 + c*u⁻¹)*(1 + c*v⁻¹)
      = 1 + c*(u⁻¹+v⁻¹) + c*c*(u⁻¹*v⁻¹) := by ring
  rw [show (1 + c*((i:ZMod (p^E)))⁻¹)*(1 + c*(((N-i:ℕ)):ZMod (p^E))⁻¹)
        = (1 + c*u⁻¹)*(1 + c*v⁻¹) from rfl, key, hB, hAprod]
  ring
end OEIS357569

namespace OEIS357569
open Finset

lemma reflect_mem {p N i : ℕ} (hp : p.Prime) (hpN : p ∣ N) (hi : i ∈ II p N) : N - i ∈ II p N := by
  rw [mem_II] at hi ⊢
  obtain ⟨⟨hi1, hi2⟩, hip⟩ := hi
  have hiN : i < N := by
    rcases lt_or_eq_of_le hi2 with h | h
    · exact h
    · exact absurd (h ▸ hpN) hip
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro hd; apply hip
  have : i = N - (N - i) := by omega
  rw [this]; exact Nat.dvd_sub hpN hd

lemma prod_reflect {R : Type*} [CommMonoid R] {p N : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (g : ℕ → R) : ∏ i ∈ II p N, g (N-i) = ∏ i ∈ II p N, g i := by
  apply Finset.prod_nbij' (fun i => N-i) (fun i => N-i)
    (fun a ha => reflect_mem hp hpN ha) (fun a ha => reflect_mem hp hpN ha)
  · intro a ha; rw [mem_II] at ha; omega
  · intro a ha; rw [mem_II] at ha; omega
  · intro a _; rfl

lemma sqProd {p E N : ℕ} [NeZero (p^E)] (hp : p.Prime) (hpN : p ∣ N) (c : ZMod (p^E)) :
    (∏ i ∈ II p N, (1 + c * ((i:ZMod (p^E)))⁻¹))^2
      = ∏ i ∈ II p N, (1 + (c * ((N:ℕ):ZMod (p^E)) + c*c) * (((i*(N-i):ℕ)):ZMod (p^E))⁻¹) := by
  have hrefl : (∏ i ∈ II p N, (1 + c * ((i:ZMod (p^E)))⁻¹))
      = ∏ i ∈ II p N, (1 + c * (((N-i:ℕ)):ZMod (p^E))⁻¹) :=
    (prod_reflect hp hpN (fun j => 1 + c * ((j:ZMod (p^E)))⁻¹)).symm
  rw [sq]
  nth_rewrite 2 [hrefl]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact pair_eq hp hpN hi c

end OEIS357569

namespace OEIS357569
open Finset

lemma prodII_unit {p E N : ℕ} (hp : p.Prime) :
    IsUnit (∏ i ∈ II p N, ((i:ZMod (p^E)))) := by
  rw [← Nat.cast_prod]
  apply isUnit_cast hp
  intro hd
  rw [Nat.Prime.prime hp |>.dvd_finset_prod_iff] at hd
  obtain ⟨i, hi, hdi⟩ := hd
  rw [mem_II] at hi
  exact hi.2 hdi

lemma cast_factor2 {p E N i : ℕ} [NeZero (p^E)] (hp : p.Prime) (hi : i ∈ II p N) :
    (2*((N:ℕ):ZMod (p^E)) + (i:ZMod (p^E)))
      = (1 + 2*((N:ℕ):ZMod (p^E))*((i:ZMod (p^E)))⁻¹) * ((i:ZMod (p^E))) := by
  rw [mem_II] at hi
  have hu : IsUnit ((i:ZMod (p^E))) := isUnit_cast hp hi.2
  rw [add_mul, one_mul,
    show 2*((N:ℕ):ZMod (p^E))*((i:ZMod (p^E)))⁻¹ * (i:ZMod (p^E))
      = 2*((N:ℕ):ZMod (p^E)) * ((i:ZMod (p^E))⁻¹ * (i:ZMod (p^E))) from by ring,
    ZMod.inv_mul_of_unit _ hu, mul_one]
  ring

lemma cast_factor1 {p E N i : ℕ} [NeZero (p^E)] (hp : p.Prime) (hi : i ∈ II p N) :
    (((N:ℕ):ZMod (p^E)) + (i:ZMod (p^E)))
      = (1 + ((N:ℕ):ZMod (p^E))*((i:ZMod (p^E)))⁻¹) * ((i:ZMod (p^E))) := by
  rw [mem_II] at hi
  have hu : IsUnit ((i:ZMod (p^E))) := isUnit_cast hp hi.2
  rw [add_mul, one_mul,
    show ((N:ℕ):ZMod (p^E))*((i:ZMod (p^E)))⁻¹ * (i:ZMod (p^E))
      = ((N:ℕ):ZMod (p^E)) * ((i:ZMod (p^E))⁻¹ * (i:ZMod (p^E))) from by ring,
    ZMod.inv_mul_of_unit _ hu, mul_one]
  ring

lemma CF2 {p E N M : ℕ} [NeZero (p^E)] (hp : p.Prime) (hE : 1 < p^E) (hM : 1 ≤ M) (hNM : N = p*M) :
    ((3*N).choose N : ZMod (p^E))
      = ((3*M).choose M : ZMod (p^E))
        * ∏ i ∈ II p N, (1 + 2*((N:ℕ):ZMod (p^E))*((i:ZMod (p^E)))⁻¹) := by
  haveI : Fact (1 < p^E) := ⟨hE⟩
  have hC := Cmul_R p M hp.pos hM
  rw [← hNM] at hC
  have hcast := congrArg (Nat.cast : ℕ → ZMod (p^E)) hC
  push_cast at hcast
  rw [Finset.prod_congr rfl (fun i hi => cast_factor2 hp hi), Finset.prod_mul_distrib] at hcast
  have hDu := prodII_unit (p:=p) (E:=E) (N:=N) hp
  rw [← mul_assoc] at hcast
  exact (IsUnit.mul_left_inj hDu).mp hcast

lemma two_sigma2 {ι R : Type*} [CommRing R] (s : Finset ι) (a : ι → R) :
    2 * (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, a i)
      = (∑ i ∈ s, a i)^2 - ∑ i ∈ s, (a i)^2 := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.powersetCard_eq_empty.mpr (by simp)]; simp
  | @insert x s hx ih =>
    rw [Finset.powersetCard_succ_insert hx 1]
    have hdisj : Disjoint (s.powersetCard 2) ((s.powersetCard 1).image (insert x)) := by
      rw [Finset.disjoint_left]
      intro t ht ht2
      rw [Finset.mem_powersetCard] at ht
      simp only [Finset.mem_image, Finset.mem_powersetCard] at ht2
      obtain ⟨u, _, hu⟩ := ht2
      have : x ∈ t := by rw [← hu]; exact Finset.mem_insert_self x u
      exact hx (ht.1 this)
    rw [Finset.sum_union hdisj]
    have hinj : ∀ u ∈ s.powersetCard 1, ∀ v ∈ s.powersetCard 1,
        insert x u = insert x v → u = v := by
      intro u hu v hv h
      rw [Finset.mem_powersetCard] at hu hv
      have hxu : x ∉ u := fun hc => hx (hu.1 hc)
      have hxv : x ∉ v := fun hc => hx (hv.1 hc)
      rw [← Finset.erase_insert hxu, ← Finset.erase_insert hxv, h]
    rw [Finset.sum_image hinj]
    have hsec : ∀ u ∈ s.powersetCard 1, ∏ i ∈ insert x u, a i = a x * ∏ i ∈ u, a i := by
      intro u hu
      rw [Finset.mem_powersetCard] at hu
      have hxu : x ∉ u := fun hc => hx (hu.1 hc)
      rw [Finset.prod_insert hxu]
    rw [Finset.sum_congr rfl hsec, ← Finset.mul_sum, sum_powersetCard_one]
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    have hexp : (a x + ∑ i ∈ s, a i)^2 - (a x ^2 + ∑ i ∈ s, (a i)^2)
        = (2 * a x * ∑ i ∈ s, a i) + ((∑ i ∈ s, a i)^2 - ∑ i ∈ s, (a i)^2) := by ring
    rw [hexp, ← ih]; ring

lemma prod_one_add_sub_one_dvd {ι R : Type*} [CommRing R] (s : Finset ι) (a : ι → R)
    (q : R) (e : ℕ) (ha : ∀ i ∈ s, q^e ∣ a i) :
    q^e ∣ (∏ i ∈ s, (1 + a i) - 1) := by
  classical
  rw [prod_one_add_eq]
  have h0 : ∑ j ∈ Finset.range (#s+1), ∑ t ∈ s.powersetCard j, ∏ i ∈ t, a i
      = 1 + ∑ j ∈ Finset.Ico 1 (#s+1), ∑ t ∈ s.powersetCard j, ∏ i ∈ t, a i := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (by omega),
       show Finset.Ico 0 1 = {0} from rfl, Finset.sum_singleton, Finset.powersetCard_zero,
       Finset.sum_singleton, Finset.prod_empty]
  rw [h0, add_sub_cancel_left]
  apply Finset.dvd_sum; intro j hj; rw [Finset.mem_Ico] at hj
  apply Finset.dvd_sum; intro t ht; rw [Finset.mem_powersetCard] at ht
  obtain ⟨hts, htc⟩ := ht
  have hne : t.Nonempty := by rw [← Finset.card_pos, htc]; omega
  obtain ⟨i0, hi0⟩ := hne
  calc q^e ∣ a i0 := ha i0 (hts hi0)
    _ ∣ ∏ i ∈ t, a i := Finset.dvd_prod_of_mem a hi0

lemma tail2_dvd {ι R : Type*} [CommRing R] (s : Finset ι) (a : ι → R)
    (q : R) (e : ℕ) (ha : ∀ i ∈ s, q^e ∣ a i) (hs : 2 ≤ #s) :
    q^(2*e) ∣ (∏ i ∈ s, (1 + a i) - 1 - ∑ i ∈ s, a i) := by
  classical
  have hexp : ∏ i ∈ s, (1 + a i)
      = 1 + (∑ i ∈ s, a i)
        + (∑ j ∈ Finset.Ico 2 (#s+1), ∑ t ∈ s.powersetCard j, ∏ i ∈ t, a i) := by
    rw [prod_one_add_eq, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (show 0 ≤ 2 by omega) (show 2 ≤ #s + 1 by omega),
      show Finset.Ico 0 2 = {0,1} from by decide,
      Finset.sum_insert (by decide), Finset.sum_singleton,
      Finset.powersetCard_zero, Finset.sum_singleton, Finset.prod_empty, sum_powersetCard_one]
  rw [hexp, show 1 + (∑ i ∈ s, a i)
        + (∑ j ∈ Finset.Ico 2 (#s+1), ∑ t ∈ s.powersetCard j, ∏ i ∈ t, a i) - 1
        - (∑ i ∈ s, a i)
      = (∑ j ∈ Finset.Ico 2 (#s+1), ∑ t ∈ s.powersetCard j, ∏ i ∈ t, a i) from by ring]
  apply Finset.dvd_sum; intro j hj; rw [Finset.mem_Ico] at hj
  apply Finset.dvd_sum; intro t ht; rw [Finset.mem_powersetCard] at ht
  obtain ⟨hts, htc⟩ := ht
  calc q^(2*e) ∣ q^(e * #t) := by
        apply pow_dvd_pow; rw [htc]; nlinarith [hj.1]
    _ = ∏ i ∈ t, q^e := by rw [Finset.prod_const, ← pow_mul]
    _ ∣ ∏ i ∈ t, a i := Finset.prod_dvd_prod_of_dvd _ _ (fun i hi => ha i (hts hi))

lemma pair_inv_sum {p E N i : ℕ} [NeZero (p^E)] (hp : p.Prime) (hpN : p ∣ N) (hi : i ∈ II p N) :
    ((i:ZMod (p^E)))⁻¹ + (((N-i:ℕ)):ZMod (p^E))⁻¹
      = ((N:ℕ):ZMod (p^E)) * (((i*(N-i):ℕ)):ZMod (p^E))⁻¹ := by
  rw [mem_II] at hi
  obtain ⟨⟨hi1, hi2⟩, hip⟩ := hi
  have hni : ¬ p ∣ (N - i) := by
    intro hd; apply hip
    have : i = N - (N - i) := by omega
    rw [this]; exact Nat.dvd_sub hpN hd
  have hu : IsUnit ((i:ZMod (p^E))) := isUnit_cast hp hip
  have hv : IsUnit (((N-i:ℕ)):ZMod (p^E)) := isUnit_cast hp hni
  set u := (i:ZMod (p^E))
  set v := (((N-i:ℕ)):ZMod (p^E))
  have hAprod : u⁻¹ * v⁻¹ = (((i*(N-i):ℕ)):ZMod (p^E))⁻¹ := by
    have := uinv_mul (n := p^E) hu hv; simpa [u, v] using this
  have hsum : u + v = ((N:ℕ):ZMod (p^E)) := by
    rw [show u + v = ((i:ℕ):ZMod (p^E)) + (((N-i:ℕ)):ZMod (p^E)) from rfl]
    rw [← Nat.cast_add, show i + (N-i) = N from by omega]
  have hBgen : u⁻¹ + v⁻¹ = (u + v) * (u⁻¹ * v⁻¹) := by
    rw [add_mul,
      show u * (u⁻¹ * v⁻¹) = (u * u⁻¹) * v⁻¹ from by ring,
      show v * (u⁻¹ * v⁻¹) = (v * v⁻¹) * u⁻¹ from by ring,
      ZMod.mul_inv_of_unit _ hu, ZMod.mul_inv_of_unit _ hv, one_mul, one_mul, add_comm]
  rw [hBgen, hsum, hAprod]

lemma sum_reflect {R : Type*} [AddCommMonoid R] {p N : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (g : ℕ → R) : ∑ i ∈ II p N, g (N-i) = ∑ i ∈ II p N, g i := by
  apply Finset.sum_nbij' (fun i => N-i) (fun i => N-i)
    (fun a ha => reflect_mem hp hpN ha) (fun a ha => reflect_mem hp hpN ha)
  · intro a ha; rw [mem_II] at ha; omega
  · intro a ha; rw [mem_II] at ha; omega
  · intro a _; rfl

lemma two_sum_x {p E N : ℕ} [NeZero (p^E)] (hp : p.Prime) (hpN : p ∣ N) :
    2 * (∑ i ∈ II p N, ((i:ZMod (p^E)))⁻¹)
      = ((N:ℕ):ZMod (p^E)) * (∑ i ∈ II p N, (((i*(N-i):ℕ)):ZMod (p^E))⁻¹) := by
  have hrefl : (∑ i ∈ II p N, ((i:ZMod (p^E)))⁻¹)
      = ∑ i ∈ II p N, (((N-i:ℕ)):ZMod (p^E))⁻¹ :=
    (sum_reflect hp hpN (fun j => ((j:ZMod (p^E)))⁻¹)).symm
  rw [two_mul]
  nth_rewrite 2 [hrefl]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact pair_inv_sum hp hpN hi

lemma two_le_card_II {p k : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hk : 1 ≤ k) :
    2 ≤ #(II p (p^k)) := by
  have hpk : p ≤ p^k := Nat.le_self_pow (by omega) p
  have hsub : ({1,2} : Finset ℕ) ⊆ II p (p^k) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_II]
    rcases hx with h | h <;> subst h
    · exact ⟨⟨by omega, by omega⟩, Nat.Prime.not_dvd_one hp⟩
    · refine ⟨⟨by omega, by omega⟩, ?_⟩
      intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
  calc (2:ℕ) = #({1,2} : Finset ℕ) := by decide
    _ ≤ _ := Finset.card_le_card hsub

lemma sigma2_const_mul {ι R : Type*} [CommRing R] (s : Finset ι) (c : R) (y : ι → R) :
    ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, (c * y i)
      = c^2 * ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i := by
  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t ht
  rw [Finset.mem_powersetCard] at ht
  rw [Finset.prod_mul_distrib, Finset.prod_const, ht.2]

lemma Pexpand {ι R : Type*} [CommRing R] (s : Finset ι) (y : ι → R) (q d : R) (e : ℕ)
    (hd : q^e ∣ d) (hs : 2 ≤ #s) :
    q^(3*e) ∣ (∏ i ∈ s, (1 + d * y i) - 1 - d * (∑ i ∈ s, y i)
      - d^2 * (∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i)) := by
  have hadvd : ∀ i ∈ s, q^e ∣ d * y i := fun i _ => hd.mul_right _
  have key := prod_one_add_dvd_tail s (fun i => d * y i) q e hadvd hs
  rw [← Finset.mul_sum, sigma2_const_mul] at key
  exact key

lemma two_unit {p m : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) : IsUnit ((2:ZMod (p^m))) := by
  have hnd : ¬ p ∣ 2 := by intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  have := isUnit_cast (i:=2) (r:=m) hp hnd
  simpa using this

lemma dvd_sigma2y {p r m : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 2 ≤ r) (hrm : r ≤ m)
    [NeZero (p^m)] :
    ((p : ZMod (p^m)))^1 ∣
      ∑ t ∈ (II p (p^r)).powersetCard 2, ∏ i ∈ t, (((i*(p^r-i):ℕ)):ZMod (p^m))⁻¹ := by
  set y : ℕ → ZMod (p^m) := fun i => (((i*(p^r-i):ℕ)):ZMod (p^m))⁻¹ with hy
  have h2 := two_sigma2 (II p (p^r)) y
  have hSy : ((p : ZMod (p^m)))^1 ∣ ∑ i ∈ II p (p^r), y i := dvd_S hp hp3 hr hrm
  have hVy : ((p : ZMod (p^m)))^1 ∣ ∑ i ∈ II p (p^r), (y i)^2 := dvd_V hp hp3 hr hrm
  have hd : ((p : ZMod (p^m)))^1 ∣
      ((∑ i ∈ II p (p^r), y i)^2 - ∑ i ∈ II p (p^r), (y i)^2) := by
    apply dvd_sub _ hVy
    rw [pow_two]; exact hSy.mul_right _
  rw [← h2] at hd
  exact (IsUnit.dvd_mul_left (two_unit hp hp3)).mp hd

lemma dvd_180_Sy_one {p m : ℕ} [NeZero (p^m)] (hp : p.Prime) (hp3 : 3 ≤ p) (hm : 1 ≤ m) :
    ((p:ZMod (p^m)))^1 ∣ 180 * ∑ i ∈ II p (p^1), (((i*(p^1-i):ℕ)):ZMod (p^m))⁻¹ := by
  haveI : NeZero (p^1) := ⟨pow_ne_zero 1 hp.pos.ne'⟩
  apply dvd_of_cast_eq_zero
  rw [castval_eq (pow_dvd_pow p hm)]
  set f := ZMod.castHom (pow_dvd_pow p hm) (ZMod (p^1)) with hf
  rw [map_mul, map_sum]
  rw [Finset.sum_congr rfl (fun i hi => red_term hp (le_refl 1) (le_refl 1) f hi)]
  rw [Finset.sum_neg_distrib, reindex hp (le_refl 1) 2, sum_pow_cast_eq]
  have hd : ((180 * ∑ i ∈ II p (p^1), (i:ℤ)^2 : ℤ):ZMod (p^1)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, castpr]
    obtain ⟨t, ht⟩ := dvd_six_J2 p 1 hp.pos (le_refl 1)
    refine ⟨30*t, ?_⟩
    rw [show (180:ℤ) * ∑ i ∈ II p (p^1), (i:ℤ)^2
          = 30 * (6 * ∑ i ∈ II p (p^1), (i:ℤ)^2) from by ring, ht]; ring
  rw [map_ofNat, mul_neg, neg_eq_zero,
    show (180:ZMod (p^1)) * (((∑ i ∈ II p (p^1), (i:ℤ)^2:ℤ)):ZMod (p^1))
        = (((180 * ∑ i ∈ II p (p^1), (i:ℤ)^2 : ℤ)):ZMod (p^1)) from by push_cast; ring]
  exact hd

lemma F1m1_dvd {p m k : ℕ} [NeZero (p^m)] (hp : p.Prime) (hp3 : 3 ≤ p) (hk : 1 ≤ k) :
    ((p:ZMod (p^m)))^(2*k) ∣
      (∏ i ∈ II p (p^k), (1 + ((p^k:ℕ):ZMod (p^m))*((i:ZMod (p^m)))⁻¹) - 1) := by
  set q := (p:ZMod (p^m)) with hq
  have hpN : p ∣ p^k := dvd_pow_self p (by omega)
  have hcast : ((p^k:ℕ):ZMod (p^m)) = q^k := by rw [hq]; push_cast; ring
  set a : ℕ → ZMod (p^m) := fun i => ((p^k:ℕ):ZMod (p^m))*((i:ZMod (p^m)))⁻¹ with ha
  have hadvd : ∀ i ∈ II p (p^k), q^k ∣ a i := by
    intro i _; rw [ha]; simp only []; rw [hcast]; exact Dvd.intro _ rfl
  have hcard := two_le_card_II hp hp3 hk
  have htail := tail2_dvd (II p (p^k)) a q k hadvd hcard
  have hsum : q^(2*k) ∣ ∑ i ∈ II p (p^k), a i := by
    have heq : ∑ i ∈ II p (p^k), a i
        = ((p^k:ℕ):ZMod (p^m)) * ∑ i ∈ II p (p^k), ((i:ZMod (p^m)))⁻¹ := by
      rw [Finset.mul_sum]
    have h2 := two_sum_x (p := p) (E := m) (N := p ^ k) hp hpN
    have hkey : 2 * (∑ i ∈ II p (p^k), a i)
        = q^(2*k) * ∑ i ∈ II p (p^k), (((i*(p^k-i):ℕ)):ZMod (p^m))⁻¹ := by
      rw [heq, show 2 * (((p^k:ℕ):ZMod (p^m)) * ∑ i ∈ II p (p^k), ((i:ZMod (p^m)))⁻¹)
            = ((p^k:ℕ):ZMod (p^m)) * (2 * ∑ i ∈ II p (p^k), ((i:ZMod (p^m)))⁻¹) from by ring,
        h2, hcast]
      ring
    have hdvd2 : q^(2*k) ∣ 2 * (∑ i ∈ II p (p^k), a i) := ⟨_, hkey⟩
    exact (IsUnit.dvd_mul_left (two_unit hp hp3)).mp hdvd2
  have hsplit : (∏ i ∈ II p (p^k), (1 + a i) - 1)
      = (∏ i ∈ II p (p^k), (1 + a i) - 1 - ∑ i ∈ II p (p^k), a i)
        + ∑ i ∈ II p (p^k), a i := by ring
  rw [show (∏ i ∈ II p (p^k), (1 + ((p^k:ℕ):ZMod (p^m))*((i:ZMod (p^m)))⁻¹) - 1)
       = (∏ i ∈ II p (p^k), (1 + a i) - 1) from rfl, hsplit]
  exact dvd_add htail hsum

/-- `G2 = F2² - 1` is divisible by `q^{2k}` (weak bound). -/
lemma G2_low {p m k : ℕ} [NeZero (p^m)] (hp : p.Prime) (hk : 1 ≤ k) :
    ((p:ZMod (p^m)))^(2*k) ∣
      ((∏ i ∈ II p (p^k), (1 + 2*((p^k:ℕ):ZMod (p^m))*((i:ZMod (p^m)))⁻¹))^2 - 1) := by
  set q := (p:ZMod (p^m)) with hq
  have hpN : p ∣ p^k := dvd_pow_self p (by omega)
  have hNr : ((p^k:ℕ):ZMod (p^m)) = q^k := by rw [hq]; push_cast; ring
  rw [sqProd hp hpN (2*((p^k:ℕ):ZMod (p^m)))]
  set d := (2*((p^k:ℕ):ZMod (p^m)))*((p^k:ℕ):ZMod (p^m))
      + (2*((p^k:ℕ):ZMod (p^m)))*(2*((p^k:ℕ):ZMod (p^m))) with hdd
  have hdvd_d : q^(2*k) ∣ d := by rw [hdd, hNr]; exact ⟨6, by ring⟩
  exact prod_one_add_sub_one_dvd _ _ q (2*k) (fun i _ => hdvd_d.mul_right _)

/-- `G2 = F2² - 1` is divisible by `q^{3k}` (sharp bound, needs `2 ≤ k ≤ m`). -/
lemma G2_high {p m k : ℕ} [NeZero (p^m)] (hp : p.Prime) (hp3 : 3 ≤ p) (hk2 : 2 ≤ k) (hkm : k ≤ m) :
    ((p:ZMod (p^m)))^(3*k) ∣
      ((∏ i ∈ II p (p^k), (1 + 2*((p^k:ℕ):ZMod (p^m))*((i:ZMod (p^m)))⁻¹))^2 - 1) := by
  set q := (p:ZMod (p^m)) with hq
  have hpN : p ∣ p^k := dvd_pow_self p (by omega)
  have hNr : ((p^k:ℕ):ZMod (p^m)) = q^k := by rw [hq]; push_cast; ring
  rw [sqProd hp hpN (2*((p^k:ℕ):ZMod (p^m)))]
  set y : ℕ → ZMod (p^m) := fun i => (((i*(p^k-i):ℕ)):ZMod (p^m))⁻¹ with hy
  set d := (2*((p^k:ℕ):ZMod (p^m)))*((p^k:ℕ):ZMod (p^m))
      + (2*((p^k:ℕ):ZMod (p^m)))*(2*((p^k:ℕ):ZMod (p^m))) with hdd
  have hd_eq : d = 6*((p^k:ℕ):ZMod (p^m))^2 := by rw [hdd]; ring
  have hdvd_d : q^(2*k) ∣ d := by rw [hd_eq, hNr]; exact ⟨6, by rw [← pow_mul]; ring⟩
  have hcard := two_le_card_II hp hp3 (by omega : 1 ≤ k)
  -- Pexpand tail
  have hPex := Pexpand (II p (p^k)) y q d (2*k) hdvd_d hcard
  -- d * Sy
  have hsix := dvd_six_S (p:=p) (r:=k) (m:=m) hp hk2 hkm
  have hNr2 : q^(2*k) ∣ ((p^k:ℕ):ZMod (p^m))^2 := by rw [hNr, ← pow_mul]; exact pow_dvd_pow q (by omega)
  have hdSy : q^(3*k) ∣ d * (∑ i ∈ II p (p^k), y i) := by
    rw [show d * (∑ i ∈ II p (p^k), y i)
        = ((p^k:ℕ):ZMod (p^m))^2 * (6 * ∑ i ∈ II p (p^k), y i) from by rw [hd_eq]; ring]
    have := mul_dvd_mul hNr2 hsix
    rwa [← pow_add, show 2*k+k = 3*k from by ring] at this
  -- d^2 * S2y
  have hNr4 : q^(3*k) ∣ ((p^k:ℕ):ZMod (p^m))^4 := by
    rw [hNr, ← pow_mul]; exact pow_dvd_pow q (by omega)
  have hd2 : q^(3*k) ∣ d^2 * (∑ t ∈ (II p (p^k)).powersetCard 2, ∏ i ∈ t, y i) := by
    rw [show d^2 = 36*((p^k:ℕ):ZMod (p^m))^4 from by rw [hd_eq]; ring]
    exact ((hNr4.mul_left 36).mul_right _)
  -- combine
  have hsplit : ((∏ i ∈ II p (p^k), (1 + d * y i)) - 1)
      = ((∏ i ∈ II p (p^k), (1 + d * y i)) - 1 - d * (∑ i ∈ II p (p^k), y i)
          - d^2 * (∑ t ∈ (II p (p^k)).powersetCard 2, ∏ i ∈ t, y i))
        + d * (∑ i ∈ II p (p^k), y i)
        + d^2 * (∑ t ∈ (II p (p^k)).powersetCard 2, ∏ i ∈ t, y i) := by ring
  rw [hsplit]
  exact dvd_add (dvd_add (dvd_trans (pow_dvd_pow q (by omega)) hPex) hdSy) hd2

lemma M2_dvd {p r m : ℕ} [NeZero (p^m)] (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 2 ≤ r) (hrm : r ≤ m)
    (A B : ZMod (p^m)) (hD4 : ((p:ZMod (p^m)))^3 ∣ (2*A^2 - 9*B)) :
    ((p:ZMod (p^m)))^(3*r+3) ∣
      (2*A^2*((∏ i ∈ II p (p^r), (1 + 2*((p^r:ℕ):ZMod (p^m))*((i:ZMod (p^m)))⁻¹))^2 - 1)
       - 27*B*((∏ i ∈ II p (p^r), (1 + ((p^r:ℕ):ZMod (p^m))*((i:ZMod (p^m)))⁻¹))^2 - 1)) := by
  set q := (p:ZMod (p^m)) with hq
  have hpN : p ∣ p^r := dvd_pow_self p (by omega)
  rw [sqProd hp hpN (2*((p^r:ℕ):ZMod (p^m))), sqProd hp hpN (((p^r:ℕ):ZMod (p^m)))]
  set Nr := ((p^r:ℕ):ZMod (p^m)) with hNrdef
  have hNr : Nr = q^r := by rw [hNrdef, hq]; push_cast; ring
  set y : ℕ → ZMod (p^m) := fun i => (((i*(p^r-i):ℕ)):ZMod (p^m))⁻¹ with hy
  set Sy := ∑ i ∈ II p (p^r), y i with hSydef
  set S2y := ∑ t ∈ (II p (p^r)).powersetCard 2, ∏ i ∈ t, y i with hS2ydef
  set d2 := (2*Nr)*Nr + (2*Nr)*(2*Nr) with hd2def
  set d1 := Nr*Nr + Nr*Nr with hd1def
  have hd2_eq : d2 = 6*Nr^2 := by rw [hd2def]; ring
  have hd1_eq : d1 = 2*Nr^2 := by rw [hd1def]; ring
  have hd2dvd : q^(2*r) ∣ d2 := by rw [hd2_eq, hNr]; exact ⟨6, by rw [← pow_mul]; ring⟩
  have hd1dvd : q^(2*r) ∣ d1 := by rw [hd1_eq, hNr]; exact ⟨2, by rw [← pow_mul]; ring⟩
  have hcard := two_le_card_II hp hp3 (by omega : 1 ≤ r)
  have hPex2 := Pexpand (II p (p^r)) y q d2 (2*r) hd2dvd hcard
  have hPex1 := Pexpand (II p (p^r)) y q d1 (2*r) hd1dvd hcard
  have hNr2 : q^(2*r) ∣ Nr^2 := by rw [hNr, ← pow_mul]; exact pow_dvd_pow q (by omega)
  have hNr4 : q^(4*r) ∣ Nr^4 := by rw [hNr, ← pow_mul]; exact pow_dvd_pow q (by omega)
  have hsix := dvd_six_S (p:=p) (r:=r) (m:=m) hp hr hrm
  have hsig := dvd_sigma2y (p:=p) (r:=r) (m:=m) hp hp3 hr hrm
  rw [show (2*A^2*((∏ i ∈ II p (p^r), (1 + d2 * y i)) - 1)
        - 27*B*((∏ i ∈ II p (p^r), (1 + d1 * y i)) - 1))
      = (2*A^2*((∏ i ∈ II p (p^r), (1 + d2 * y i)) - 1 - d2*Sy - d2^2*S2y)
          - 27*B*((∏ i ∈ II p (p^r), (1 + d1 * y i)) - 1 - d1*Sy - d1^2*S2y))
        + (2*A^2*d2 - 27*B*d1)*Sy
        + (2*A^2*d2^2 - 27*B*d1^2)*S2y from by
        simp only [hSydef, hS2ydef]; ring]
  refine dvd_add (dvd_add ?_ ?_) ?_
  · -- part1 : q^{6r} divides
    refine dvd_trans (pow_dvd_pow q (show 3*r+3 ≤ 3*(2*r) by omega)) ?_
    exact dvd_sub (hPex2.mul_left _) (hPex1.mul_left _)
  · -- part2 : (2A²d2-27Bd1)*Sy
    rw [show (2*A^2*d2 - 27*B*d1)*Sy = (2*A^2-9*B)*Nr^2*(6*Sy) from by rw [hd2_eq, hd1_eq]; ring]
    have hsix' : q^r ∣ 6*Sy := by rw [hSydef]; exact hsix
    have := mul_dvd_mul (mul_dvd_mul hD4 hNr2) hsix'
    rwa [← pow_add, ← pow_add, show 3+2*r+r = 3*r+3 by omega] at this
  · -- part3 : (2A²d2²-27Bd1²)*S2y
    rw [show (2*A^2*d2^2 - 27*B*d1^2)*S2y = 36*(2*A^2-3*B)*(Nr^4*S2y) from by rw [hd2_eq, hd1_eq]; ring]
    refine dvd_trans (pow_dvd_pow q (show 3*r+3 ≤ 4*r+1 by omega)) ?_
    have hsig' : q^1 ∣ S2y := by rw [hS2ydef]; exact hsig
    have hh := (mul_dvd_mul hNr4 hsig').mul_left (36*(2*A^2-3*B))
    rwa [← pow_add] at hh

lemma M36_18_dvd {p m : ℕ} [NeZero (p^m)] (hp : p.Prime) (hp3 : 3 ≤ p) (hm : 1 ≤ m) :
    ((p:ZMod (p^m)))^3 ∣
      (36*((∏ i ∈ II p (p^1), (1 + 2*((p^1:ℕ):ZMod (p^m))*((i:ZMod (p^m)))⁻¹))^2 - 1)
       - 18*((∏ i ∈ II p (p^1), (1 + ((p^1:ℕ):ZMod (p^m))*((i:ZMod (p^m)))⁻¹))^2 - 1)) := by
  set q := (p:ZMod (p^m)) with hq
  have hpN : p ∣ p^1 := dvd_pow_self p (by omega)
  rw [sqProd hp hpN (2*((p^1:ℕ):ZMod (p^m))), sqProd hp hpN (((p^1:ℕ):ZMod (p^m)))]
  set Nr := ((p^1:ℕ):ZMod (p^m)) with hNrdef
  have hNr : Nr = q := by rw [hNrdef, hq]; push_cast; ring
  set y : ℕ → ZMod (p^m) := fun i => (((i*(p^1-i):ℕ)):ZMod (p^m))⁻¹ with hy
  set Sy := ∑ i ∈ II p (p^1), y i with hSydef
  set S2y := ∑ t ∈ (II p (p^1)).powersetCard 2, ∏ i ∈ t, y i with hS2ydef
  set d2 := (2*Nr)*Nr + (2*Nr)*(2*Nr) with hd2def
  set d1 := Nr*Nr + Nr*Nr with hd1def
  have hd2_eq : d2 = 6*Nr^2 := by rw [hd2def]; ring
  have hd1_eq : d1 = 2*Nr^2 := by rw [hd1def]; ring
  have hd2dvd : q^(2*1) ∣ d2 := by rw [hd2_eq, hNr]; exact ⟨6, by ring⟩
  have hd1dvd : q^(2*1) ∣ d1 := by rw [hd1_eq, hNr]; exact ⟨2, by ring⟩
  have hcard := two_le_card_II hp hp3 (le_refl 1)
  have hPex2 := Pexpand (II p (p^1)) y q d2 (2*1) hd2dvd hcard
  have hPex1 := Pexpand (II p (p^1)) y q d1 (2*1) hd1dvd hcard
  rw [show (36*((∏ i ∈ II p (p^1), (1 + d2 * y i)) - 1)
        - 18*((∏ i ∈ II p (p^1), (1 + d1 * y i)) - 1))
      = (36*((∏ i ∈ II p (p^1), (1 + d2 * y i)) - 1 - d2*Sy - d2^2*S2y)
          - 18*((∏ i ∈ II p (p^1), (1 + d1 * y i)) - 1 - d1*Sy - d1^2*S2y))
        + (36*d2 - 18*d1)*Sy
        + (36*d2^2 - 18*d1^2)*S2y from by
        simp only [hSydef, hS2ydef]; ring]
  refine dvd_add (dvd_add ?_ ?_) ?_
  · refine dvd_trans (pow_dvd_pow q (show 3 ≤ 3*(2*1) by omega)) ?_
    exact dvd_sub (hPex2.mul_left _) (hPex1.mul_left _)
  · rw [show (36*d2 - 18*d1)*Sy = q^2*(180*Sy) from by rw [hd2_eq, hd1_eq, hNr]; ring]
    have h180 : q^1 ∣ 180*Sy := by rw [hSydef]; exact dvd_180_Sy_one (p:=p) (m:=m) hp hp3 hm
    have hmul := mul_dvd_mul_left (q^2) h180
    rw [← pow_add] at hmul; exact hmul
  · rw [show (36*d2^2 - 18*d1^2)*S2y = 1224*(Nr^4*S2y) from by rw [hd2_eq, hd1_eq]; ring]
    have hNr4 : q^3 ∣ Nr^4 := by rw [hNr]; exact pow_dvd_pow q (by omega)
    exact (hNr4.mul_right _).mul_left 1224

lemma CF1 {p E N M : ℕ} [NeZero (p^E)] (hp : p.Prime) (hE : 1 < p^E) (hM : 1 ≤ M) (hNM : N = p*M) :
    ((2*N).choose N : ZMod (p^E))
      = ((2*M).choose M : ZMod (p^E))
        * ∏ i ∈ II p N, (1 + ((N:ℕ):ZMod (p^E))*((i:ZMod (p^E)))⁻¹) := by
  haveI : Fact (1 < p^E) := ⟨hE⟩
  have hC := Cmul_Q p M hp.pos hM
  rw [← hNM] at hC
  have hcast := congrArg (Nat.cast : ℕ → ZMod (p^E)) hC
  push_cast at hcast
  rw [Finset.prod_congr rfl (fun i hi => cast_factor1 hp hi), Finset.prod_mul_distrib] at hcast
  have hDu := prodII_unit (p:=p) (E:=E) (N:=N) hp
  rw [← mul_assoc] at hcast
  exact (IsUnit.mul_left_inj hDu).mp hcast

lemma d4_zmod {p k : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hk : 1 ≤ k) :
    (2*(((3*p^k).choose (p^k):ℕ):ZMod (p^3))^2 - 9*(((2*p^k).choose (p^k):ℕ):ZMod (p^3)))
    = (2*(((3*p^(k-1)).choose (p^(k-1)):ℕ):ZMod (p^3))^2
        - 9*(((2*p^(k-1)).choose (p^(k-1)):ℕ):ZMod (p^3))) := by
  haveI : NeZero (p^3) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  have hpos1 : 1 < p^3 := by
    calc 1 < p := by omega
      _ ≤ p^3 := Nat.le_self_pow (by omega) p
  have hM : 1 ≤ p^(k-1) := Nat.one_le_pow _ _ hp.pos
  have hNM : p^k = p*p^(k-1) := by
    conv_lhs => rw [show k = (k-1)+1 by omega]
    rw [pow_succ, mul_comm]
  rw [CF2 hp hpos1 hM hNM, CF1 hp hpos1 hM hNM]
  set q := (p:ZMod (p^3)) with hq
  set A := (((3*p^(k-1)).choose (p^(k-1)):ℕ):ZMod (p^3)) with hAdef
  set B := (((2*p^(k-1)).choose (p^(k-1)):ℕ):ZMod (p^3)) with hBdef
  set F2 := ∏ i ∈ II p (p^k), (1 + 2*((p^k:ℕ):ZMod (p^3))*((i:ZMod (p^3)))⁻¹) with hF2def
  set F1 := ∏ i ∈ II p (p^k), (1 + ((p^k:ℕ):ZMod (p^3))*((i:ZMod (p^3)))⁻¹) with hF1def
  have hq30 : q^3 = 0 := by
    rw [hq, show (p:ZMod (p^3))^3 = ((p^3:ℕ):ZMod (p^3)) from by push_cast; ring, ZMod.natCast_self]
  have hkeyzero : 2*A^2*(F2^2-1) - 9*B*(F1-1) = 0 := by
    rcases Nat.lt_or_ge k 2 with hk1 | hk2
    · have hk1' : k = 1 := by omega
      have hA : A = 3 := by rw [hAdef, hk1']; simp [Nat.choose_one_right]
      have hB : B = 2 := by rw [hBdef, hk1']; simp [Nat.choose_one_right]
      have hF2eq : F2 = ∏ i ∈ II p (p^1), (1 + 2*((p^1:ℕ):ZMod (p^3))*((i:ZMod (p^3)))⁻¹) := by
        rw [hF2def, hk1']
      have hF1eq : F1 = ∏ i ∈ II p (p^1), (1 + ((p^1:ℕ):ZMod (p^3))*((i:ZMod (p^3)))⁻¹) := by
        rw [hF1def, hk1']
      have hg2 : q^2 ∣ (F2^2 - 1) := by rw [hF2eq]; exact G2_low (m:=3) (k:=1) hp (le_refl 1)
      have hf1 : q^2 ∣ (F1 - 1) := by rw [hF1eq]; exact F1m1_dvd (m:=3) (k:=1) hp hp3 (le_refl 1)
      have hM36 : q^3 ∣ (36*(F2^2-1) - 18*(F1^2-1)) := by
        rw [hF2eq, hF1eq]; exact M36_18_dvd (m:=3) hp hp3 (by omega)
      -- K*(F1+1) = 18(F2²-1)(F1-1) + (36(F2²-1)-18(F1²-1))
      have hmid : q^3 ∣ (18*((F2^2-1)*(F1-1))) := by
        have := mul_dvd_mul hg2 hf1
        rw [← pow_add] at this
        exact ((dvd_trans (pow_dvd_pow q (by omega : 3 ≤ 2+2)) this).mul_left 18)
      have hKF : q^3 ∣ (2*A^2*(F2^2-1) - 9*B*(F1-1)) * (F1+1) := by
        rw [hA, hB,
          show (2*3^2*(F2^2-1) - 9*2*(F1-1)) * (F1+1)
              = (18*((F2^2-1)*(F1-1))) + (36*(F2^2-1) - 18*(F1^2-1)) from by ring]
        exact dvd_add hmid hM36
      have hnil : IsNilpotent (F1 - 1) := by
        obtain ⟨w, hw⟩ := F1m1_dvd (p:=p) (m:=3) (k:=1) hp hp3 (le_refl 1)
        refine ⟨2, ?_⟩
        rw [hF1eq, hw, mul_pow, ← pow_mul, show 2*1*2 = 3+1 from rfl, pow_add, hq30,
          zero_mul, zero_mul]
      have hF1u : IsUnit (F1+1) := by
        have hu := hnil.isUnit_add_left_of_commute (two_unit (p:=p) (m:=3) hp hp3) (Commute.all _ _)
        rwa [show 2 + (F1-1) = F1+1 from by ring] at hu
      obtain ⟨t, ht⟩ := hKF
      have : (2*A^2*(F2^2-1) - 9*B*(F1-1)) * (F1+1) = 0 * (F1+1) := by
        rw [ht, hq30, zero_mul, zero_mul]
      exact (IsUnit.mul_left_inj hF1u).mp this
    · have hF2 : q^3 ∣ (F2^2 - 1) := by
        rw [hF2def]
        exact dvd_trans (pow_dvd_pow q (by omega)) (G2_low (m:=3) (k:=k) hp (by omega))
      have hF1 : q^3 ∣ (F1 - 1) := by
        rw [hF1def]
        exact dvd_trans (pow_dvd_pow q (by omega)) (F1m1_dvd (m:=3) (k:=k) hp hp3 (by omega))
      have hkd : q^3 ∣ (2*A^2*(F2^2-1) - 9*B*(F1-1)) := dvd_sub (hF2.mul_left _) (hF1.mul_left _)
      obtain ⟨t, ht⟩ := hkd; rw [ht, hq30, zero_mul]
  rw [← sub_eq_zero,
    show 2*(A*F2)^2 - 9*(B*F1) - (2*A^2 - 9*B) = 2*A^2*(F2^2-1) - 9*B*(F1-1) from by ring]
  exact hkeyzero

lemma D4_int {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (j : ℕ) :
    (p:ℤ)^3 ∣ (2*((3*p^j).choose (p^j):ℤ)^2 - 9*((2*p^j).choose (p^j):ℤ)) := by
  induction j with
  | zero =>
    have h0 : (2*((3*p^0).choose (p^0):ℤ)^2 - 9*((2*p^0).choose (p^0):ℤ)) = 0 := by
      simp [Nat.choose_one_right]
    rw [h0]; exact dvd_zero _
  | succ j ih =>
    have hstep : (p:ℤ)^3 ∣
        ((2*((3*p^(j+1)).choose (p^(j+1)):ℤ)^2 - 9*((2*p^(j+1)).choose (p^(j+1)):ℤ))
          - (2*((3*p^j).choose (p^j):ℤ)^2 - 9*((2*p^j).choose (p^j):ℤ))) := by
      have hz := d4_zmod (k:=j+1) hp hp3 (by omega)
      rw [show j+1-1 = j from rfl] at hz
      have hzero : (((2*((3*p^(j+1)).choose (p^(j+1)):ℤ)^2 - 9*((2*p^(j+1)).choose (p^(j+1)):ℤ))
          - (2*((3*p^j).choose (p^j):ℤ)^2 - 9*((2*p^j).choose (p^j):ℤ)) : ℤ) : ZMod (p^3)) = 0 := by
        push_cast
        rw [sub_eq_zero]
        exact hz
      rw [← castpr (p:=p) (r:=3)]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p^3)).mp hzero
    have hcomb := dvd_add hstep ih
    simpa using hcomb

def a (n : ℕ) : ℤ :=
  (Int.ofNat ((3 * n).choose n)) ^ 2 - (27 : ℤ) * Int.ofNat ((2 * n).choose n)

theorem oeis_357569_conjecture_0 (p r : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (hr : r ≥ 2) :
    a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] := by
  set E := 3*r+3 with hE
  haveI : NeZero (p^E) := ⟨pow_ne_zero E hp.pos.ne'⟩
  have hpos1 : 1 < p^E := by
    calc 1 < p := by omega
      _ ≤ p^E := Nat.le_self_pow (by omega) p
  have hM : 1 ≤ p^(r-1) := Nat.one_le_pow _ _ hp.pos
  have hNM : p^r = p*p^(r-1) := by
    conv_lhs => rw [show r = (r-1)+1 by omega]
    rw [pow_succ, mul_comm]
  rw [show ((p:ℤ)^E) = ((p^E:ℕ):ℤ) from by push_cast; ring]
  refine (ZMod.intCast_eq_intCast_iff _ _ _).mp ?_
  have hcast : ((a (p^r) : ℤ) : ZMod (p^E)) = ((a (p^(r-1)) : ℤ) : ZMod (p^E)) := by
    simp only [a, Int.ofNat_eq_coe]
    push_cast
    rw [CF2 hp hpos1 hM hNM, CF1 hp hpos1 hM hNM]
    set q := (p:ZMod (p^E)) with hq
    set A := (((3*p^(r-1)).choose (p^(r-1)):ℕ):ZMod (p^E)) with hAdef
    set B := (((2*p^(r-1)).choose (p^(r-1)):ℕ):ZMod (p^E)) with hBdef
    set F2 := ∏ i ∈ II p (p^r), (1 + 2*((p^r:ℕ):ZMod (p^E))*((i:ZMod (p^E)))⁻¹) with hF2def
    set F1 := ∏ i ∈ II p (p^r), (1 + ((p^r:ℕ):ZMod (p^E))*((i:ZMod (p^E)))⁻¹) with hF1def
    have hqE0 : q^E = 0 := by
      rw [hq, show (p:ZMod (p^E))^E = ((p^E:ℕ):ZMod (p^E)) from by push_cast; ring,
        ZMod.natCast_self]
    have hD4 : q^3 ∣ (2*A^2 - 9*B) := by
      have hc := dvd_cast_of_int (m:=E) (k:=3) (D4_int hp hp3 (r-1))
      have hth : ((2*((3*p^(r-1)).choose (p^(r-1)):ℤ)^2
            - 9*((2*p^(r-1)).choose (p^(r-1)):ℤ) : ℤ):ZMod (p^E)) = 2*A^2 - 9*B := by
        rw [hAdef, hBdef]; push_cast; ring
      rwa [hth] at hc
    have hM2 := M2_dvd (p:=p) (r:=r) (m:=E) hp hp3 hr (by rw [hE]; omega) A B hD4
    have hM1 : q^E ∣ A^2*((F2^2-1)*(F1-1)) := by
      have hg : q^(3*r) ∣ (F2^2-1) := by
        rw [hF2def]; exact G2_high (m:=E) (k:=r) hp hp3 hr (by rw [hE]; omega)
      have hf : q^(2*r) ∣ (F1-1) := by
        rw [hF1def]; exact F1m1_dvd (m:=E) (k:=r) hp hp3 (by omega)
      have hmul := mul_dvd_mul hg hf
      rw [← pow_add] at hmul
      exact (dvd_trans (pow_dvd_pow q (by rw [hE]; omega : E ≤ 3*r+2*r)) hmul).mul_left _
    have hKF : q^E ∣ (A^2*(F2^2-1) - 27*B*(F1-1)) * (F1+1) := by
      rw [show (A^2*(F2^2-1) - 27*B*(F1-1)) * (F1+1)
          = A^2*((F2^2-1)*(F1-1)) + (2*A^2*(F2^2-1) - 27*B*(F1^2-1)) from by ring]
      exact dvd_add hM1 hM2
    have hnil : IsNilpotent (F1 - 1) := by
      obtain ⟨w, hw⟩ := F1m1_dvd (p:=p) (m:=E) (k:=r) hp hp3 (by omega)
      refine ⟨E, ?_⟩
      rw [hF1def, hw, mul_pow, ← pow_mul, show 2*r*E = E*(2*r) from by ring, pow_mul, hqE0,
        zero_pow (by omega), zero_mul]
    have hF1u : IsUnit (F1+1) := by
      have hu := hnil.isUnit_add_left_of_commute (two_unit (p:=p) (m:=E) hp hp3) (Commute.all _ _)
      rwa [show 2 + (F1-1) = F1+1 from by ring] at hu
    obtain ⟨t, ht⟩ := hKF
    have hK0 : A^2*(F2^2-1) - 27*B*(F1-1) = 0 := by
      have heq : (A^2*(F2^2-1) - 27*B*(F1-1)) * (F1+1) = 0 * (F1+1) := by
        rw [ht, hqE0, zero_mul, zero_mul]
      exact (IsUnit.mul_left_inj hF1u).mp heq
    rw [← sub_eq_zero,
      show (A*F2)^2 - 27*(B*F1) - (A^2 - 27*B) = A^2*(F2^2-1) - 27*B*(F1-1) from by ring]
    exact hK0
  exact hcast

end OEIS357569
