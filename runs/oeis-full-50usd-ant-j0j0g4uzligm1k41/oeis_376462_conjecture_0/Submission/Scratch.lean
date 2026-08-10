import FormalConjectures.Util.ProblemImports
open Nat Finset

-- Sum of squares closed form in ℤ
theorem sum_sq_int (n : ℕ) :
    6 * ∑ k ∈ range n, (k : ℤ)^2 = (n : ℤ) * (n - 1) * (2 * n - 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    push_cast
    ring_nf
    ring_nf at ih
    linarith [ih]

-- Sum over p∤k of k^2 mod p^r
-- multiples of p below p^r, reindexed
theorem sum_mult_sq (p r : ℕ) (hp : 0 < p) (hr : 1 ≤ r) :
    ∑ k ∈ (range (p^r)).filter (fun k => p ∣ k), (k : ℤ)^2
      = (p : ℤ)^2 * ∑ j ∈ range (p^(r-1)), (j : ℤ)^2 := by
  have hset : (range (p^r)).filter (fun k => p ∣ k)
      = (range (p^(r-1))).image (fun j => j * p) := by
    ext k
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hk, m, rfl⟩
      refine ⟨m, ?_, by ring⟩
      have : p ^ r = p ^ (r-1) * p := by
        rw [← pow_succ]; congr 1; omega
      rw [this] at hk
      exact lt_of_mul_lt_mul_right (by rwa [mul_comm] at hk) (le_of_lt hp)
    · rintro ⟨j, hj, rfl⟩
      refine ⟨?_, ⟨j, by ring⟩⟩
      have : p ^ r = p ^ (r-1) * p := by
        rw [← pow_succ]; congr 1; omega
      rw [this]
      exact Nat.mul_lt_mul_of_pos_right hj hp
  rw [hset, Finset.sum_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_right hp h)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

theorem sum_units_sq_dvd (p r : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hr : 1 ≤ r) :
    ((p:ℤ) ^ r) ∣ ∑ k ∈ (range (p^r)).filter (fun k => ¬ p ∣ k), (k : ℤ)^2 := by
  have hp0 : 0 < p := by omega
  have hsplit : ∑ k ∈ (range (p^r)).filter (fun k => ¬ p ∣ k), (k : ℤ)^2
      = (∑ k ∈ range (p^r), (k:ℤ)^2) - ∑ k ∈ (range (p^r)).filter (fun k => p ∣ k), (k : ℤ)^2 := by
    rw [eq_sub_iff_add_eq, add_comm, Finset.sum_filter_add_sum_filter_not]
  have hM : ((p^r:ℕ):ℤ) = (p:ℤ)^r := by push_cast; ring
  have hm : ((p^(r-1):ℕ):ℤ) = (p:ℤ)^(r-1) := by push_cast; ring
  have e1 : (6:ℤ) * ∑ k ∈ range (p^r), (k:ℤ)^2
      = (p:ℤ)^r * ((p:ℤ)^r - 1) * (2 * (p:ℤ)^r - 1) := by rw [sum_sq_int, hM]
  have e2 : (6:ℤ) * ∑ j ∈ range (p^(r-1)), (j:ℤ)^2
      = (p:ℤ)^(r-1) * ((p:ℤ)^(r-1) - 1) * (2 * (p:ℤ)^(r-1) - 1) := by rw [sum_sq_int, hm]
  have key6 : (6 : ℤ) * ∑ k ∈ (range (p^r)).filter (fun k => ¬ p ∣ k), (k : ℤ)^2
      = (p:ℤ)^r * ((p:ℤ)^r - 1) * (2 * (p:ℤ)^r - 1)
        - (p:ℤ)^2 * ((p:ℤ)^(r-1) * ((p:ℤ)^(r-1) - 1) * (2 * (p:ℤ)^(r-1) - 1)) := by
    rw [hsplit, mul_sub, sum_mult_sq p r hp0 hr, e1,
        show (6:ℤ) * ((p:ℤ)^2 * ∑ j ∈ range (p^(r-1)), (j:ℤ)^2)
          = (p:ℤ)^2 * (6 * ∑ j ∈ range (p^(r-1)), (j:ℤ)^2) by ring, e2]
  have hdvd6 : ((p:ℤ)^r) ∣ 6 * ∑ k ∈ (range (p^r)).filter (fun k => ¬ p ∣ k), (k : ℤ)^2 := by
    rw [key6]
    apply _root_.dvd_sub
    · exact ⟨((p:ℤ)^r - 1) * (2 * (p:ℤ)^r - 1), by ring⟩
    · refine ⟨(p:ℤ) * ((p:ℤ)^(r-1) - 1) * (2 * (p:ℤ)^(r-1) - 1), ?_⟩
      have hpow : (p:ℤ)^2 * (p:ℤ)^(r-1) = (p:ℤ)^r * (p:ℤ) := by
        rw [← pow_add, show (p:ℤ)^r * (p:ℤ) = (p:ℤ)^(r+1) from (pow_succ _ _).symm]
        congr 1; omega
      calc (p:ℤ)^2 * ((p:ℤ)^(r-1) * ((p:ℤ)^(r-1) - 1) * (2 * (p:ℤ)^(r-1) - 1))
          = ((p:ℤ)^2 * (p:ℤ)^(r-1)) * (((p:ℤ)^(r-1) - 1) * (2 * (p:ℤ)^(r-1) - 1)) := by ring
        _ = (p:ℤ)^r * ((p:ℤ) * ((p:ℤ)^(r-1) - 1) * (2 * (p:ℤ)^(r-1) - 1)) := by rw [hpow]; ring
  -- coprimality of p^r and 6
  have hcop : IsCoprime ((p:ℤ)^r) 6 := by
    have h2 : ¬ (2 ∣ p) := by intro h; have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h; omega
    have h3 : ¬ (3 ∣ p) := by intro h; have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h; omega
    have hcp6 : Nat.Coprime p 6 := by
      have : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 (by omega)
      have h3' : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
      have : Nat.Coprime p (2*3) := Nat.Coprime.mul_right this h3'
      simpa using this
    have : IsCoprime (p:ℤ) 6 := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      simpa [Int.gcd] using hcp6
    exact this.pow_left
  exact hcop.dvd_of_dvd_mul_left hdvd6
-- ZMod corollary: sum of squares over the "units window" vanishes in ZMod (p^r)
theorem sum_units_sq_zmod (p r : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hr : 1 ≤ r) :
    (∑ k ∈ (range (p^r)).filter (fun k => ¬ p ∣ k), (k : ZMod (p^r))^2) = 0 := by
  have hd := sum_units_sq_dvd p r hp h5 hr
  have : ((∑ k ∈ (range (p^r)).filter (fun k => ¬ p ∣ k), (k : ℤ)^2 : ℤ) : ZMod (p^r)) = 0 := by
    obtain ⟨c, hc⟩ := hd
    rw [hc, Int.cast_mul, Int.cast_pow, Int.cast_natCast, ← Nat.cast_pow, ZMod.natCast_self,
        zero_mul]
  rw [← this]
  push_cast
  rfl

-- Units window in ZMod(p^r): each k in [1,p^r) with p∤k is a unit
theorem isUnit_of_ndvd (p r k : ℕ) (hp : p.Prime) (hr : 1 ≤ r)
    (hk : k < p^r) (hk0 : 0 < k) (hnd : ¬ p ∣ k) : IsUnit (k : ZMod (p^r)) := by
  have hc : Nat.Coprime k (p^r) := ((hp.coprime_iff_not_dvd.mpr hnd).symm).pow_right r
  exact (ZMod.isUnit_iff_coprime k (p^r)).mpr hc

-- Atom: k * C(m,k) = m * C(m-1,k-1)
theorem choose_atom (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    k * m.choose k = m * (m - 1).choose (k - 1) := by
  have h := Nat.succ_mul_choose_eq (m - 1) (k - 1)
  simp only [Nat.succ_eq_add_one, Nat.sub_add_cancel hm, Nat.sub_add_cancel hk] at h
  rw [mul_comm]; exact h.symm

-- Valuation: p^r ∣ C(n*p^r, k) for p∤k
theorem choose_np_dvd (p n r k : ℕ) (hp : p.Prime) (hr : 1 ≤ r) (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hnd : ¬ p ∣ k) : p^r ∣ (n * p^r).choose k := by
  have hm : 1 ≤ n * p^r := by
    have : 0 < n * p ^ r := Nat.mul_pos (by omega) (pow_pos hp.pos r)
    omega
  have atom := choose_atom (n * p^r) k hm hk
  have hdvd : p^r ∣ k * ((n * p^r).choose k) := by
    rw [atom]
    exact Dvd.dvd.mul_right (Dvd.intro_left n rfl) _
  have hcop : Nat.Coprime (p^r) k := (Nat.Coprime.pow_left r ((hp.coprime_iff_not_dvd).mpr hnd))
  exact (Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd)

-- The summand of A376462
noncomputable def auxT (N k : ℕ) : ℕ :=
  (range (k + 1)).sum fun i => (N.choose i) ^ 2 * ((N + k - i).choose (k - i))
noncomputable def TT (N k : ℕ) : ℕ :=
  (N.choose k) ^ 2 * (N + k).choose k * auxT N (N - k)

-- p^{2r} ∣ TT (n*p^r) k for p∤k
theorem pow_dvd_TT (p n r k : ℕ) (hp : p.Prime) (hr : 1 ≤ r) (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hnd : ¬ p ∣ k) : p^(2*r) ∣ TT (n*p^r) k := by
  have h1 : p^r ∣ (n*p^r).choose k := choose_np_dvd p n r k hp hr hk hn hnd
  have h2 : p^(2*r) ∣ ((n*p^r).choose k)^2 := by
    rw [two_mul, pow_add, sq]; exact mul_dvd_mul h1 h1
  exact (h2.mul_right _).mul_right _

-- Sum of inverse squares over the units window vanishes in ZMod (p^r)
theorem sum_units_invsq_zmod (p r : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hr : 1 ≤ r) :
    (∑ k ∈ (range (p^r)).filter (fun k => ¬ p ∣ k), ((k : ZMod (p^r))⁻¹)^2) = 0 := by
  have hpr : 0 < p^r := pow_pos (by omega) r
  haveI : NeZero (p^r) := ⟨by omega⟩
  set W := (range (p^r)).filter (fun k => ¬ p ∣ k) with hW
  have hmemW : ∀ k, k ∈ W ↔ (k < p^r ∧ ¬ p ∣ k) := by
    intro k; rw [hW]; simp [mem_filter, mem_range]
  have hunit : ∀ k ∈ W, IsUnit (k : ZMod (p^r)) := by
    intro k hk
    rw [hmemW] at hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso; exact hk.2 (h0 ▸ dvd_zero p)
    · exact isUnit_of_ndvd p r k hp hr hk.1 h0 hk.2
  -- σ k = val of the inverse of k
  set σ : ℕ → ℕ := fun k => ((k : ZMod (p^r))⁻¹).val with hσ
  have hcast : ∀ k ∈ W, ((σ k : ℕ) : ZMod (p^r)) = ((k : ZMod (p^r))⁻¹) := by
    intro k hk; rw [hσ]; simp [ZMod.natCast_val, ZMod.cast_id]
  have hσunit : ∀ k ∈ W, IsUnit ((σ k : ℕ) : ZMod (p^r)) := by
    intro k hk; rw [hcast k hk]
    exact IsUnit.of_mul_eq_one _ (ZMod.inv_mul_of_unit _ (hunit k hk))
  have hσmem : ∀ k ∈ W, σ k ∈ W := by
    intro k hk
    rw [hmemW]
    constructor
    · rw [hσ]; exact ZMod.val_lt _
    · intro hdvd
      -- p ∣ σ k contradicts σ k being a unit
      have hcop : Nat.Coprime (σ k) (p^r) := (ZMod.isUnit_iff_coprime _ _).mp (hσunit k hk)
      have hpd : p ∣ p^r := dvd_pow_self p (by omega : r ≠ 0)
      have hg : Nat.gcd (σ k) (p^r) = 1 := hcop
      have hd1 : p ∣ 1 := hg ▸ Nat.dvd_gcd hdvd hpd
      have hle := Nat.le_of_dvd one_pos hd1
      have := hp.two_le
      omega
  -- σ is an involution on W
  have hinv : ∀ k ∈ W, σ (σ k) = k := by
    intro k hk
    have h1 : ((σ (σ k) : ℕ) : ZMod (p^r)) = ((k : ℕ) : ZMod (p^r)) := by
      rw [hcast (σ k) (hσmem k hk)]
      apply ZMod.inv_eq_of_mul_eq_one
      rw [hcast k hk]
      exact ZMod.inv_mul_of_unit _ (hunit k hk)
    -- both σ(σ k) and k are < p^r, so equal
    have hlt1 : σ (σ k) < p^r := by rw [hσ]; exact ZMod.val_lt _
    have hlt2 : k < p^r := ((hmemW k).mp hk).1
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1
    rwa [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at this
  have hsum : (∑ k ∈ W, ((k : ZMod (p^r))⁻¹)^2) = ∑ k ∈ W, (k : ZMod (p^r))^2 := by
    apply Finset.sum_bij' (fun k _ => σ k) (fun k _ => σ k) hσmem hσmem hinv hinv
    intro k hk
    rw [← hcast k hk]
  rw [hsum]
  exact sum_units_sq_zmod p r hp h5 hr

-- If the mod-a reduction of S vanishes, then a ∣ S in ZMod b
theorem dvd_of_castHom_zero (a b : ℕ) (h : a ∣ b) [NeZero b] (S : ZMod b)
    (hS : (ZMod.castHom h (ZMod a)) S = 0) : (↑a : ZMod b) ∣ S := by
  have hval : S = ((S.val : ℕ) : ZMod b) := (ZMod.natCast_zmod_val S).symm
  have hφ : ((S.val : ℕ) : ZMod a) = 0 := by
    have e : (ZMod.castHom h (ZMod a)) S = ((S.val : ℕ) : ZMod a) := by
      conv_lhs => rw [hval]
      rw [map_natCast]
    rw [← e]; exact hS
  obtain ⟨t, ht⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hφ
  exact ⟨(t : ZMod b), by rw [hval, ht]; push_cast; ring⟩

-- ring homs preserve the inverse of a unit in ZMod
theorem castHom_inv {a b : ℕ} (h : a ∣ b) [NeZero a] (x : ZMod b) (hx : IsUnit x) :
    (ZMod.castHom h (ZMod a)) x⁻¹ = ((ZMod.castHom h (ZMod a)) x)⁻¹ := by
  symm
  apply ZMod.inv_eq_of_mul_eq_one
  rw [← map_mul, ZMod.mul_inv_of_unit x hx, map_one]

-- The inverse-square sum over one block (fiber) is divisible by p^r in ZMod(p^{3r})
theorem fiber_invsq_dvd (p n r b : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hr : 1 ≤ r) (hb : b < n) :
    (↑(p^r) : ZMod (p^(3*r))) ∣
      ∑ k ∈ (range (n*p^r+1)).filter (fun k => ¬ p ∣ k ∧ k / p^r = b),
        ((k : ZMod (p^(3*r)))⁻¹)^2 := by
  have hp0 : p ≠ 0 := by omega
  have hdvd : p^r ∣ p^(3*r) := pow_dvd_pow p (by omega)
  haveI : NeZero (p^(3*r)) := ⟨pow_ne_zero _ hp0⟩
  haveI : NeZero (p^r) := ⟨pow_ne_zero _ hp0⟩
  apply dvd_of_castHom_zero (p^r) (p^(3*r)) hdvd
  rw [map_sum]
  -- rewrite each term to ((k : ZMod (p^r))⁻¹)^2
  have hterm : ∀ k ∈ (range (n*p^r+1)).filter (fun k => ¬ p ∣ k ∧ k / p^r = b),
      (ZMod.castHom hdvd (ZMod (p^r))) (((k : ZMod (p^(3*r)))⁻¹)^2)
        = ((k : ZMod (p^r))⁻¹)^2 := by
    intro k hk
    rw [mem_filter] at hk
    have hku : IsUnit ((k : ℕ) : ZMod (p^(3*r))) := by
      rw [ZMod.isUnit_iff_coprime]
      exact (((hp.coprime_iff_not_dvd).mpr hk.2.1).symm).pow_right (3*r)
    rw [map_pow, castHom_inv hdvd _ hku, map_natCast]
  rw [Finset.sum_congr rfl hterm]
  have hprpos : 0 < p^r := Nat.pos_of_ne_zero (pow_ne_zero r hp0)
  rw [← sum_units_invsq_zmod p r hp h5 hr]
  -- reindex fiber ↔ window by k ↦ k % p^r
  apply Finset.sum_bij' (fun k _ => k % p^r) (fun u _ => b * p^r + u)
  · -- hi : fiber → window
    intro k hk
    rw [mem_filter] at hk
    rw [mem_filter, mem_range]
    refine ⟨Nat.mod_lt _ hprpos, ?_⟩
    intro hdd
    apply hk.2.1
    have hkeq : k = p^r * b + k % p^r := by
      conv_lhs => rw [← Nat.div_add_mod k (p^r), hk.2.2]
    rw [hkeq]
    exact Nat.dvd_add (Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _) hdd
  · -- hj : window → fiber
    intro u hu
    rw [mem_filter, mem_range] at hu
    rw [mem_filter, mem_range]
    have hupr : u < p^r := hu.1
    have hpb : p ∣ b * p^r := Dvd.dvd.mul_left (dvd_pow_self p (by omega)) _
    have hbound : b * p^r + u < n * p^r + 1 := by
      have hmul : (b + 1) * p^r ≤ n * p^r := mul_le_mul_right' (by omega) (p^r)
      nlinarith [hmul, hupr]
    refine ⟨hbound, ?_, ?_⟩
    · intro hdd
      exact hu.2 ((Nat.dvd_add_right hpb).mp hdd)
    · rw [mul_comm b (p^r), Nat.mul_add_div hprpos, Nat.div_eq_of_lt hupr, Nat.add_zero]
  · -- left inverse
    intro k hk
    rw [mem_filter] at hk
    conv_rhs => rw [← Nat.div_add_mod k (p^r), hk.2.2]
    ring
  · -- right inverse
    intro u hu
    rw [mem_filter, mem_range] at hu
    rw [add_comm (b * p^r) u, mul_comm b (p^r), Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hu.1
  · -- values agree
    intro k hk
    rw [mem_filter] at hk
    have hthis : (k : ZMod (p^r)) = ((k % p^r : ℕ) : ZMod (p^r)) := by
      conv_lhs => rw [← Nat.div_add_mod k (p^r), hk.2.2]
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add]
    rw [hthis]

-- Main P3 reduction: given block-constancy (A), Σ_{p∤k} TT ≡ 0 mod p^{3r}
theorem p3_vanish (p n r : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hr : 1 ≤ r) (hn : 1 ≤ n)
    (hA : ∀ k, 1 ≤ k → k < n * p^r → ¬ p ∣ k → ∀ k', 1 ≤ k' → k' < n * p^r → ¬ p ∣ k' →
          k / p^r = k' / p^r →
          (((k^2 * TT (n * p^r) k : ℕ)) : ZMod (p^(3*r)))
            = (((k'^2 * TT (n * p^r) k' : ℕ)) : ZMod (p^(3*r)))) :
    (∑ k ∈ (range (n * p^r + 1)).filter (fun k => ¬ p ∣ k),
        (TT (n * p^r) k : ZMod (p^(3*r)))) = 0 := by
  have hp0 : p ≠ 0 := by omega
  have hprpos : 0 < p^r := Nat.pos_of_ne_zero (pow_ne_zero r hp0)
  haveI : NeZero (p^(3*r)) := ⟨pow_ne_zero _ hp0⟩
  have hpN : p ∣ n * p^r := Dvd.dvd.mul_left (dvd_pow_self p (by omega)) n
  have hmaps : ∀ k ∈ (range (n * p^r + 1)).filter (fun k => ¬ p ∣ k), k / p^r ∈ range n := by
    intro k hk
    rw [mem_filter, mem_range] at hk
    rw [mem_range]
    have hkN : k < n * p^r := by
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hk.1) with h | h
      · exact h
      · exact absurd (h ▸ hpN) hk.2
    exact (Nat.div_lt_iff_lt_mul hprpos).mpr hkN
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun k => (TT (n * p^r) k : ZMod (p^(3*r))))]
  apply Finset.sum_eq_zero
  intro b hb
  rw [mem_range] at hb
  rw [Finset.filter_filter]
  -- Fb = (range (N+1)).filter (¬p∣k ∧ k/p^r=b)
  set Fb := (range (n * p^r + 1)).filter (fun k => ¬ p ∣ k ∧ k / p^r = b) with hFbdef
  -- extract member properties
  have hFb : ∀ j ∈ Fb, 1 ≤ j ∧ j < n * p^r ∧ ¬ p ∣ j ∧ j / p^r = b := by
    intro j hj
    rw [hFbdef, mem_filter, mem_range] at hj
    obtain ⟨hjr, hjnd, hjb⟩ := hj
    refine ⟨?_, ?_, hjnd, hjb⟩
    · rcases Nat.eq_zero_or_pos j with h | h
      · exact absurd (h ▸ dvd_zero p) hjnd
      · exact h
    · rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hjr) with h | h
      · exact h
      · exact absurd (h ▸ hpN) hjnd
  rcases Finset.eq_empty_or_nonempty Fb with he | ⟨k₀, hk₀⟩
  · rw [he]; simp
  · obtain ⟨hk₀1, hk₀N, hk₀nd, hk₀b⟩ := hFb k₀ hk₀
    -- rewrite each term as (k⁻¹)^2 * C with C = ((k₀^2 * TT k₀ : ℕ):R)
    have hrw : ∀ k ∈ Fb, (TT (n * p^r) k : ZMod (p^(3*r)))
        = ((k : ZMod (p^(3*r)))⁻¹)^2 * ((k₀^2 * TT (n * p^r) k₀ : ℕ) : ZMod (p^(3*r))) := by
      intro k hk
      obtain ⟨hk1, hkN, hknd, hkb⟩ := hFb k hk
      have hkunit : IsUnit ((k : ℕ) : ZMod (p^(3*r))) :=
        (ZMod.isUnit_iff_coprime _ _).mpr (((hp.coprime_iff_not_dvd).mpr hknd).symm.pow_right (3*r))
      have hone : ((k : ZMod (p^(3*r)))⁻¹)^2 * (k : ZMod (p^(3*r)))^2 = 1 := by
        rw [← mul_pow, ZMod.inv_mul_of_unit _ hkunit, one_pow]
      calc (TT (n * p^r) k : ZMod (p^(3*r)))
          = ((k : ZMod (p^(3*r)))⁻¹)^2 * ((k : ZMod (p^(3*r)))^2 * (TT (n * p^r) k : ZMod (p^(3*r)))) := by
            rw [← mul_assoc, hone, one_mul]
        _ = ((k : ZMod (p^(3*r)))⁻¹)^2 * ((k^2 * TT (n * p^r) k : ℕ) : ZMod (p^(3*r))) := by
            push_cast; ring
        _ = ((k : ZMod (p^(3*r)))⁻¹)^2 * ((k₀^2 * TT (n * p^r) k₀ : ℕ) : ZMod (p^(3*r))) := by
            rw [hA k hk1 hkN hknd k₀ hk₀1 hk₀N hk₀nd (by rw [hkb, hk₀b])]
    rw [Finset.sum_congr rfl hrw, ← Finset.sum_mul]
    -- Tb * C = 0
    obtain ⟨t, ht⟩ := fiber_invsq_dvd p n r b hp h5 hr hb
    have hCdvd : p^(2*r) ∣ k₀^2 * TT (n * p^r) k₀ :=
      Dvd.dvd.mul_left (pow_dvd_TT p n r k₀ hp hr hk₀1 hn hk₀nd) _
    obtain ⟨M, hM⟩ := hCdvd
    rw [← hFbdef] at ht
    rw [ht]
    have hCeq : ((k₀^2 * TT (n * p^r) k₀ : ℕ) : ZMod (p^(3*r)))
        = (↑(p^(2*r)) : ZMod (p^(3*r))) * (M : ZMod (p^(3*r))) := by
      rw [hM, Nat.cast_mul]
    rw [hCeq]
    have hpp : (↑(p^r) : ZMod (p^(3*r))) * ↑(p^(2*r)) = ↑(p^(3*r)) := by
      rw [← Nat.cast_mul, ← pow_add, show r + 2*r = 3*r from by ring]
    rw [show (↑(p^r) : ZMod (p^(3*r))) * t * (↑(p^(2*r)) * (M : ZMod (p^(3*r))))
          = (↑(p^r) * ↑(p^(2*r))) * (t * (M : ZMod (p^(3*r)))) by ring, hpp,
        ZMod.natCast_self, zero_mul]




-- Wolstenholme's theorem: sum of inverses of units mod p^2 vanishes (p ≥ 5)
theorem wolstenholme (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    (∑ k ∈ (range p).filter (fun k => ¬ p ∣ k), (k : ZMod (p^2))⁻¹) = 0 := by
  haveI : NeZero (p^2) := ⟨pow_ne_zero 2 (by omega)⟩
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact p.Prime := ⟨hp⟩
  set W := (range p).filter (fun k => ¬ p ∣ k) with hW
  have hmemW : ∀ k, k ∈ W ↔ (k < p ∧ ¬ p ∣ k) := by
    intro k; rw [hW]; simp [mem_filter, mem_range]
  have hltp2 : ∀ k, k < p → k < p^2 := by
    intro k hk; nlinarith [hp.pos]
  have hpos : ∀ k ∈ W, 0 < k := by
    intro k hk; rw [hmemW] at hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact absurd (h0 ▸ dvd_zero p) hk.2
    · exact h0
  have hunit : ∀ k ∈ W, IsUnit (k : ZMod (p^2)) := by
    intro k hk
    have hk' := (hmemW k).mp hk
    exact isUnit_of_ndvd p 2 k hp (by omega) (hltp2 k hk'.1) (hpos k hk) hk'.2
  -- reindex k ↦ p - k
  have hrefl : ∀ k ∈ W, (p - k) ∈ W := by
    intro k hk
    have hk' := (hmemW k).mp hk
    have hk0 := hpos k hk
    rw [hmemW]
    refine ⟨by omega, ?_⟩
    intro hd
    have hlt : p - k < p := by omega
    have h0 := Nat.eq_zero_of_dvd_of_lt hd hlt
    omega
  have hrefl2 : ∀ k ∈ W, p - (p - k) = k := by
    intro k hk; have hk' := (hmemW k).mp hk; omega
  -- 2 * S = p * T
  set S := ∑ k ∈ W, (k : ZMod (p^2))⁻¹ with hS
  have hSsym : S = ∑ k ∈ W, ((p - k : ℕ) : ZMod (p^2))⁻¹ := by
    rw [hS]
    exact (Finset.sum_bij' (fun k _ => p - k) (fun k _ => p - k) hrefl hrefl hrefl2 hrefl2
      (by intro k hk; rfl)).symm
  have h2S : (2 : ZMod (p^2)) * S = (p : ZMod (p^2)) *
      ∑ k ∈ W, ((k * (p - k) : ℕ) : ZMod (p^2))⁻¹ := by
    have e1 : (2 : ZMod (p^2)) * S
        = ∑ k ∈ W, (k : ZMod (p^2))⁻¹ + ∑ k ∈ W, ((p - k : ℕ) : ZMod (p^2))⁻¹ := by
      rw [two_mul]; nth_rewrite 2 [hSsym]; rw [hS]
    rw [e1, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := (hmemW k).mp hk
    have huk : IsUnit (k : ZMod (p^2)) := hunit k hk
    have hvk : IsUnit ((p - k : ℕ) : ZMod (p^2)) := hunit (p-k) (hrefl k hk)
    have hsum : (k : ZMod (p^2)) + ((p - k : ℕ) : ZMod (p^2)) = (p : ZMod (p^2)) := by
      rw [← Nat.cast_add]; congr 1; omega
    have hmulcast : ((k * (p - k) : ℕ) : ZMod (p^2)) = (k : ZMod (p^2)) * ((p - k : ℕ) : ZMod (p^2)) := by
      push_cast; ring
    have ha : (k : ZMod (p^2)) * (k : ZMod (p^2))⁻¹ = 1 := ZMod.mul_inv_of_unit _ huk
    have hb : ((p - k : ℕ) : ZMod (p^2)) * ((p - k : ℕ) : ZMod (p^2))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ hvk
    have hab : ((k * (p - k) : ℕ) : ZMod (p^2))⁻¹
        = (k : ZMod (p^2))⁻¹ * ((p - k : ℕ) : ZMod (p^2))⁻¹ := by
      rw [hmulcast]
      apply ZMod.inv_eq_of_mul_eq_one
      linear_combination (((p - k : ℕ) : ZMod (p^2)) * ((p - k : ℕ) : ZMod (p^2))⁻¹) * ha + hb
    rw [hab, ← hsum]
    linear_combination (-((p - k : ℕ) : ZMod (p^2))⁻¹) * ha + (-((k : ℕ) : ZMod (p^2))⁻¹) * hb
  -- Now show p * T = 0
  set T := ∑ k ∈ W, ((k * (p - k) : ℕ) : ZMod (p^2))⁻¹ with hT
  have hdvd2 : p ∣ p^2 := dvd_pow_self p two_ne_zero
  have hcastT : (ZMod.castHom hdvd2 (ZMod p)) T = 0 := by
    have hinvsq := sum_units_invsq_zmod p 1 hp h5 (le_refl 1)
    rw [pow_one] at hinvsq
    rw [hT, map_sum]
    have step : ∀ k ∈ W, (ZMod.castHom hdvd2 (ZMod p)) (((k * (p - k) : ℕ) : ZMod (p^2))⁻¹)
        = -(((k : ZMod p))⁻¹)^2 := by
      intro k hk
      have hk' := (hmemW k).mp hk
      have huk : IsUnit (k : ZMod (p^2)) := hunit k hk
      have hvk : IsUnit ((p - k : ℕ) : ZMod (p^2)) := hunit (p-k) (hrefl k hk)
      have hprod : IsUnit ((k * (p - k) : ℕ) : ZMod (p^2)) := by
        rw [Nat.cast_mul]; exact huk.mul hvk
      rw [castHom_inv hdvd2 _ hprod, map_natCast]
      have hpk : ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
        rw [Nat.cast_sub (by omega : k ≤ p), ZMod.natCast_self]; ring
      have hkp : ((k * (p - k) : ℕ) : ZMod p) = -(k : ZMod p)^2 := by
        rw [Nat.cast_mul, hpk]; ring
      rw [hkp, inv_neg, inv_pow]
    rw [Finset.sum_congr rfl step, Finset.sum_neg_distrib, neg_eq_zero]
    exact hinvsq
  have hpTdvd : (p : ZMod (p^2)) ∣ T := dvd_of_castHom_zero p (p^2) hdvd2 T hcastT
  obtain ⟨y, hy⟩ := hpTdvd
  have hpT0 : (p : ZMod (p^2)) * T = 0 := by
    rw [hy, ← mul_assoc, ← Nat.cast_mul, ← pow_two, ZMod.natCast_self, zero_mul]
  have h2S0 : (2 : ZMod (p^2)) * S = 0 := by rw [h2S]; exact hpT0
  have h2unit : IsUnit (2 : ZMod (p^2)) := by
    rw [show (2 : ZMod (p^2)) = ((2 : ℕ) : ZMod (p^2)) by push_cast; ring]
    exact isUnit_of_ndvd p 2 2 hp (by omega) (by nlinarith [hp.pos]) (by omega)
      (by intro h; have := Nat.le_of_dvd (by omega) h; omega)
  have := h2unit.mul_right_eq_zero.mp h2S0
  rw [hS] at this ⊢
  exact this
