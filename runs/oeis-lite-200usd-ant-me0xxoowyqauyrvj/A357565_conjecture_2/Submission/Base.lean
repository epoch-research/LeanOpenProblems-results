import FormalConjectures.Util.ProblemImports
import Submission.Dev

open Finset Nat

variable {p : ℕ}

-- The clean integer identity underlying the box product formula.
-- For N, k with the product split by divisibility by p.
-- ∏_{i=0}^{k-1} (N+i) = N * (∏_{p∤i, 1≤i<k} (N+i)) * (∏_{i'=1}^{b} (N + p*i'))   when k-1 multiples of p below k are p,2p,...,b*p.
-- We work with the factorial identity k! * C(N+k-1,k) = ∏_{i=0}^{k-1}(N+i).

-- Generic product split by a predicate.
theorem prod_split_filter {M0 : Type*} [CommMonoid M0] (s : Finset ℕ) (P : ℕ → Prop)
    [DecidablePred P] (g : ℕ → M0) :
    ∏ i ∈ s, g i = (∏ i ∈ s.filter (fun i => ¬ P i), g i) * (∏ i ∈ s.filter P, g i) := by
  rw [mul_comm, Finset.prod_filter_mul_prod_filter_not]

-- The multiples of p in range k reindex to range ((k-1)/p + 1) via l ↦ p*l.
theorem prod_pdvd_reindex {M0 : Type*} [CommMonoid M0] (p k : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k)
    (g : ℕ → M0) :
    ∏ i ∈ (Finset.range k).filter (fun i => p ∣ i), g i
      = ∏ l ∈ Finset.range ((k - 1) / p + 1), g (p * l) := by
  apply Finset.prod_nbij' (fun i => i / p) (fun l => p * l)
  · intro i hi; simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_range]
    obtain ⟨t, rfl⟩ := hi.2
    rw [Nat.mul_div_cancel_left _ hp]
    have : p * t ≤ k - 1 := by omega
    calc t = (p * t) / p := by rw [Nat.mul_div_cancel_left _ hp]
      _ ≤ (k - 1) / p := Nat.div_le_div_right this
      _ < (k-1)/p + 1 := by omega
  · intro l hl; simp only [Finset.mem_range] at hl
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, Dvd.intro l rfl⟩
    have : p * l ≤ p * ((k-1)/p) := by
      apply Nat.mul_le_mul_left; omega
    have h2 : p * ((k-1)/p) ≤ k - 1 := Nat.mul_div_le (k-1) p
    omega
  · intro i hi; simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨t, rfl⟩ := hi.2
    rw [Nat.mul_div_cancel_left _ hp]
  · intro l hl; rw [Nat.mul_div_cancel_left _ hp]
  · intro i hi; simp only [Finset.mem_filter] at hi
    obtain ⟨t, rfl⟩ := hi.2
    rw [Nat.mul_div_cancel_left _ hp]

-- (k-1)! split:  ∏_{i∈range k} i  has the i=0 factor; we use ∏_{i∈Ico 1 k}.
-- Core integer identity (N = p^r, r ≥ 1).  b := (k-1)/p.
-- choose(p^r+k-1,k) * (k * P1 * Pb) = p^r * (Q1 * Qb)
-- where P1 = ∏_{p∤i, i<k} i,  Pb = ∏_{l=1}^b l,  Q1 = ∏_{p∤i,i<k}(p^r+i),  Qb=∏_{l=1}^b (p^{r-1}+l).
theorem box_int_identity (p r k : ℕ) (hp : 1 ≤ p) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    (Nat.choose (p^r + k - 1) k)
        * (k * (∏ i ∈ (Finset.range k).filter (fun i => ¬ p ∣ i), i)
              * (∏ l ∈ Finset.Icc 1 ((k-1)/p), l))
      = p^r * ((∏ i ∈ (Finset.range k).filter (fun i => ¬ p ∣ i), (p^r + i))
              * (∏ l ∈ Finset.Icc 1 ((k-1)/p), (p^(r-1) + l))) := by
  set b := (k-1)/p with hb
  -- factorial identity
  have hfac : (k.factorial) * (Nat.choose (p^r + k - 1) k) = ∏ i ∈ Finset.range k, (p^r + i) :=
    factorial_mul_choose_eq_prod (p^r) k
  -- split ∏ (p^r + i) by p∣i
  have hsplitQ : (∏ i ∈ Finset.range k, (p^r + i))
      = (∏ i ∈ (Finset.range k).filter (fun i => ¬ p ∣ i), (p^r + i))
        * (∏ l ∈ Finset.range (b + 1), (p^r + p * l)) := by
    rw [prod_split_filter (Finset.range k) (fun i => p ∣ i) (fun i => p^r + i)]
    congr 1
    exact prod_pdvd_reindex p k hp hk (fun i => p^r + i)
  -- the p∣i product: p^r + p*l = p*(p^{r-1}+l); l=0 gives p^r
  have hprm1 : p^r = p * p^(r-1) := by
    conv_lhs => rw [show r = (r-1)+1 by omega]; rw [pow_succ, mul_comm]
  have hQp : (∏ l ∈ Finset.range (b + 1), (p^r + p * l))
      = p^(b+1) * (p^(r-1)) * (∏ l ∈ Finset.Icc 1 b, (p^(r-1) + l)) := by
    have : ∀ l, p^r + p * l = p * (p^(r-1) + l) := by intro l; rw [hprm1]; ring
    simp_rw [this]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    -- ∏_{l∈range(b+1)}(p^{r-1}+l) = (p^{r-1}+0)*∏_{l∈Icc 1 b}(...)
    have hr0 : ∀ m : ℕ, Finset.range (m+1) = insert 0 (Finset.Icc 1 m) := by
      intro m; ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hr0 b, Finset.prod_insert (by simp)]
    ring
  -- split k! = k * (k-1)!, and (k-1)! = P1 * p^b * Pb
  have hkfac : k.factorial = k * ((∏ i ∈ (Finset.range k).filter (fun i => ¬ p ∣ i), i)
        * (p^b * (∏ l ∈ Finset.Icc 1 b, l))) := by
    have hkf : k.factorial = k * (k-1).factorial := by
      conv_lhs => rw [show k = (k-1)+1 by omega]
      rw [Nat.factorial_succ]; congr 1 <;> omega
    have hkm1 : (k-1).factorial = ∏ i ∈ Finset.Ico 1 k, i := by
      have := Finset.prod_Ico_id_eq_factorial (k-1)
      rw [show k-1+1 = k by omega] at this
      exact this.symm
    -- range k product of id, but filter excludes 0; ∏_{range k} i has 0 factor = 0, so use Ico 1 k
    have hIco : (∏ i ∈ Finset.Ico 1 k, i)
        = (∏ i ∈ (Finset.range k).filter (fun i => ¬ p ∣ i), i) * (p^b * (∏ l ∈ Finset.Icc 1 b, l)) := by
      have hsplit : (∏ i ∈ Finset.Ico 1 k, i)
          = (∏ i ∈ (Finset.Ico 1 k).filter (fun i => ¬ p ∣ i), i)
            * (∏ i ∈ (Finset.Ico 1 k).filter (fun i => p ∣ i), i) := by
        rw [prod_split_filter (Finset.Ico 1 k) (fun i => p ∣ i) (fun i => i)]
      rw [hsplit]
      congr 1
      · -- filters over Ico 1 k vs range k agree (i=0 is p∣0, excluded by ¬p∣)
        apply Finset.prod_congr
        · ext x; simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range]
          constructor
          · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h2, h3⟩
          · rintro ⟨h1, h3⟩; refine ⟨⟨?_, h1⟩, h3⟩; rcases Nat.eq_zero_or_pos x with h|h
            · subst h; exact absurd (dvd_zero p) h3
            · omega
        · intros; rfl
      · -- p∣i part over Ico 1 k reindexes to p^b * Pb
        have hpd : (∏ i ∈ (Finset.Ico 1 k).filter (fun i => p ∣ i), i)
            = ∏ l ∈ Finset.Icc 1 b, (p * l) := by
          apply Finset.prod_nbij' (fun i => i / p) (fun l => p * l)
          · intro i hi; simp only [Finset.mem_filter, Finset.mem_Ico] at hi
            simp only [Finset.mem_Icc]
            obtain ⟨t, rfl⟩ := hi.2
            rw [Nat.mul_div_cancel_left _ hp]
            constructor
            · rcases Nat.eq_zero_or_pos t with h|h
              · subst h; simp at hi
              · exact h
            · have : p * t ≤ k - 1 := by omega
              calc t = (p*t)/p := by rw [Nat.mul_div_cancel_left _ hp]
                _ ≤ (k-1)/p := Nat.div_le_div_right this
          · intro l hl; simp only [Finset.mem_Icc] at hl
            simp only [Finset.mem_filter, Finset.mem_Ico]
            refine ⟨⟨?_, ?_⟩, Dvd.intro l rfl⟩
            · nlinarith [hl.1]
            · have h1 : p * l ≤ p * b := Nat.mul_le_mul_left _ hl.2
              have h2 : p * b ≤ k - 1 := Nat.mul_div_le (k-1) p
              omega
          · intro i hi; simp only [Finset.mem_filter, Finset.mem_Ico] at hi
            obtain ⟨t, rfl⟩ := hi.2; rw [Nat.mul_div_cancel_left _ hp]
          · intro l hl; rw [Nat.mul_div_cancel_left _ hp]
          · intro i hi; simp only [Finset.mem_filter] at hi
            obtain ⟨t, rfl⟩ := hi.2; rw [Nat.mul_div_cancel_left _ hp]
        rw [hpd, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
    rw [hkf, hkm1, hIco]
  -- combine: from hfac, hkfac, hsplitQ, hQp, cancel p^b
  rw [hkfac, hsplitQ, hQp] at hfac
  -- hfac : k * (P1 * (p^b * Pb)) * C = (Q1) * (p^(b+1)*p^(r-1)*Qb_prod)
  -- goal:  C * (k * P1 * Pb) = p^r * (Q1 * Qb)
  -- rearrange and cancel p^b
  have hpbpos : 0 < p^b := pow_pos (by omega) b
  set C := Nat.choose (p^r+k-1) k with hC
  set P1 := ∏ i ∈ (Finset.range k).filter (fun i => ¬ p ∣ i), i with hP1
  set Pb := ∏ l ∈ Finset.Icc 1 b, l with hPb
  set Q1 := ∏ i ∈ (Finset.range k).filter (fun i => ¬ p ∣ i), (p^r + i) with hQ1
  set Qb := ∏ l ∈ Finset.Icc 1 b, (p^(r-1) + l) with hQb
  have e1 : p^(b+1) * p^(r-1) = p^b * p^r := by rw [pow_succ, hprm1]; ring
  have key : C * (k * P1 * Pb) * p^b = p^r * (Q1 * Qb) * p^b := by
    have h2 : Q1 * (p^(b+1) * p^(r-1) * Qb) = p^r * (Q1 * Qb) * p^b := by rw [e1]; ring
    calc C * (k * P1 * Pb) * p^b = k * (P1 * (p^b * Pb)) * C := by ring
      _ = Q1 * (p^(b+1) * p^(r-1) * Qb) := hfac
      _ = p^r * (Q1 * Qb) * p^b := h2
  exact Nat.eq_of_mul_eq_mul_right hpbpos key

-- A natural number not divisible by p casts to a unit in ZMod (p^M).
theorem isUnit_cast_of_not_dvd [hp : Fact p.Prime] {M a : ℕ} (ha : ¬ p ∣ a) :
    IsUnit (a : ZMod (p^M)) := by
  haveI : NeZero (p^M) := ⟨pow_ne_zero M hp.out.pos.ne'⟩
  rw [ZMod.isUnit_iff_coprime]
  exact (((hp.out.coprime_iff_not_dvd).mpr ha).symm).pow_right M

-- Cast of box_int_identity to ZMod (p^M).
theorem zmod_box_cast [hp : Fact p.Prime] {r k : ℕ} (M : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    (Nat.choose (p^r+k-1) k : ZMod (p^M))
        * ((k : ZMod (p^M)) * (∏ i ∈ (Finset.range k).filter (fun i => ¬ p ∣ i), (i:ZMod (p^M)))
              * (∏ l ∈ Finset.Icc 1 ((k-1)/p), (l:ZMod (p^M))))
      = (p:ZMod (p^M))^r * ((∏ i ∈ (Finset.range k).filter (fun i => ¬ p ∣ i), ((p^r:ZMod (p^M)) + i))
              * (∏ l ∈ Finset.Icc 1 ((k-1)/p), ((p:ZMod (p^M))^(r-1) + l))) := by
  have h := box_int_identity p r k hp.out.pos hr hk
  have h2 := congrArg (fun n : ℕ => (n : ZMod (p^M))) h
  push_cast at h2
  convert h2 using 2

-- A product over residues coprime to p is a unit.
theorem prod_filter_isUnit [hp : Fact p.Prime] {M : ℕ} (s : Finset ℕ) (g : ℕ → ℕ)
    (hg : ∀ i ∈ s, ¬ p ∣ g i) : IsUnit (∏ i ∈ s, (g i : ZMod (p^M))) := by
  rw [← Nat.cast_prod]
  apply isUnit_cast_of_not_dvd
  intro hdvd
  rw [hp.out.prime.dvd_finset_prod_iff] at hdvd
  obtain ⟨i, hi, hdi⟩ := hdvd
  exact hg i hi hdi

-- Units mod p^M, for r = 2: the off-diagonal box product formula.
-- For p ∤ k and k < p^2 (so b = (k-1)/p < p): all of k, P1, Pb are units, hence
--   b_k = p^2 · k⁻¹ · (Q1 · P1⁻¹) · (Qb · Pb⁻¹).
theorem bk_offdiag_formula [hp : Fact p.Prime] {M k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < p^2)
    (hkp : ¬ p ∣ k) :
    (Nat.choose (p^2+k-1) k : ZMod (p^M))
      = (p:ZMod (p^M))^2 * (k : ZMod (p^M))⁻¹
          * ((∏ i ∈ (Finset.range k).filter (fun i => ¬ p ∣ i), ((p^2:ZMod (p^M)) + i))
                * (∏ i ∈ (Finset.range k).filter (fun i => ¬ p ∣ i), (i:ZMod (p^M)))⁻¹)
          * ((∏ l ∈ Finset.Icc 1 ((k-1)/p), ((p:ZMod (p^M)) + l))
                * (∏ l ∈ Finset.Icc 1 ((k-1)/p), (l:ZMod (p^M)))⁻¹) := by
  have hb : (k-1)/p < p := by
    have : k - 1 < p^2 := by omega
    calc (k-1)/p ≤ (p^2-1)/p := Nat.div_le_div_right (by omega)
      _ < p := by
          rw [Nat.div_lt_iff_lt_mul hp.out.pos]
          have h2 : p^2 = p * p := by ring
          omega
  -- unit facts
  have huk : IsUnit (k : ZMod (p^M)) := isUnit_cast_of_not_dvd hkp
  have huP1 : IsUnit (∏ i ∈ (Finset.range k).filter (fun i => ¬ p ∣ i), (i:ZMod (p^M))) := by
    apply prod_filter_isUnit
    intro i hi; exact (Finset.mem_filter.mp hi).2
  have huPb : IsUnit (∏ l ∈ Finset.Icc 1 ((k-1)/p), (l:ZMod (p^M))) := by
    apply prod_filter_isUnit (g := fun l => l)
    intro l hl
    rw [Finset.mem_Icc] at hl
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hcast := zmod_box_cast (p := p) (r := 2) M (by norm_num) hk1
  simp only [show (2:ℕ)-1 = 1 from rfl, pow_one] at hcast
  -- divide both sides by the unit (k * P1 * Pb)
  set C := (Nat.choose (p^2+k-1) k : ZMod (p^M))
  set P1 := ∏ i ∈ (Finset.range k).filter (fun i => ¬ p ∣ i), (i:ZMod (p^M)) with hP1
  set Pb := ∏ l ∈ Finset.Icc 1 ((k-1)/p), (l:ZMod (p^M)) with hPb
  set Q1 := ∏ i ∈ (Finset.range k).filter (fun i => ¬ p ∣ i), ((p^2:ZMod (p^M)) + i) with hQ1
  set Qb := ∏ l ∈ Finset.Icc 1 ((k-1)/p), ((p:ZMod (p^M)) + l) with hQb
  -- hcast : C * (k * P1 * Pb) = p^2 * (Q1 * Qb)
  have huprod : IsUnit ((k : ZMod (p^M)) * P1 * Pb) := (huk.mul huP1).mul huPb
  -- solve for C
  have hC : C = (p:ZMod (p^M))^2 * (Q1 * Qb) * ((k : ZMod (p^M)) * P1 * Pb)⁻¹ := by
    rw [← hcast, mul_assoc, ZMod.mul_inv_of_unit _ huprod, mul_one]
  rw [hC]
  apply huprod.mul_left_injective
  beta_reduce
  rw [mul_assoc ((p:ZMod (p^M))^2 * (Q1*Qb)), ZMod.inv_mul_of_unit _ huprod, mul_one]
  have hkk : (k:ZMod (p^M))⁻¹ * (k:ZMod (p^M)) = 1 := ZMod.inv_mul_of_unit _ huk
  have hPP : P1⁻¹ * P1 = 1 := ZMod.inv_mul_of_unit _ huP1
  have hPbPb : Pb⁻¹ * Pb = 1 := ZMod.inv_mul_of_unit _ huPb
  calc (p:ZMod (p^M))^2 * (Q1*Qb)
      = (p:ZMod (p^M))^2 * (Q1*Qb)
          * (((k:ZMod (p^M))⁻¹*(k:ZMod (p^M)))*(P1⁻¹*P1)*(Pb⁻¹*Pb)) := by
        rw [hkk, hPP, hPbPb]; ring
    _ = ((p:ZMod (p^M))^2 * (k:ZMod (p^M))⁻¹ * (Q1*P1⁻¹) * (Qb*Pb⁻¹))
          * ((k:ZMod (p^M))*P1*Pb) := by ring

-- Truncated product expansion: ∏(1+c x_i) ≡ ∑_{|t|≤n} c^|t| ∏_{t} x  (mod c^{n+1}).
theorem prod_one_add_trunc {R : Type*} [CommRing R] (c : R) (s : Finset ℕ) (x : ℕ → R) (n : ℕ) :
    c^(n+1) ∣ (∏ i ∈ s, (1 + c * x i)
        - ∑ t ∈ s.powerset.filter (fun t => t.card ≤ n), c^(t.card) * ∏ i ∈ t, x i) := by
  have hexp : ∏ i ∈ s, (1 + c * x i) = ∑ t ∈ s.powerset, c^(t.card) * ∏ i ∈ t, x i := by
    rw [Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [hexp]
  have hsplit : ∑ t ∈ s.powerset, c^(t.card) * ∏ i ∈ t, x i
      = ∑ t ∈ s.powerset.filter (fun t => t.card ≤ n), c^(t.card) * ∏ i ∈ t, x i
        + ∑ t ∈ s.powerset.filter (fun t => ¬ t.card ≤ n), c^(t.card) * ∏ i ∈ t, x i :=
    (Finset.sum_filter_add_sum_filter_not s.powerset (fun t => t.card ≤ n) _).symm
  rw [hsplit, add_sub_cancel_left]
  apply Finset.dvd_sum
  intro t ht
  rw [Finset.mem_filter] at ht
  have hcard : n + 1 ≤ t.card := by omega
  exact Dvd.dvd.mul_right (pow_dvd_pow c hcard) _

-- If the image of x under ZMod (p^t) → ZMod p is zero, then p ∣ x.
theorem dvd_of_castHom_eq_zero {t : ℕ} [Fact p.Prime] (ht : 1 ≤ t)
    (x : ZMod (p^t)) (h : (ZMod.castHom (dvd_pow_self p (by omega : t ≠ 0)) (ZMod p)) x = 0) :
    (p : ZMod (p^t)) ∣ x := by
  haveI : NeZero (p^t) := ⟨pow_ne_zero t (Fact.out (p := p.Prime)).pos.ne'⟩
  have hval : ((x.val : ZMod p)) = 0 := by
    have e : (ZMod.castHom (dvd_pow_self p (by omega : t ≠ 0)) (ZMod p)) x = (x.val : ZMod p) := by
      conv_lhs => rw [← ZMod.natCast_rightInverse (n := p^t) x]
      exact map_natCast _ x.val
    rw [e] at h; exact h
  rw [CharP.cast_eq_zero_iff (ZMod p) p] at hval
  obtain ⟨m, hm⟩ := hval
  refine ⟨(m : ZMod (p^t)), ?_⟩
  conv_lhs => rw [← ZMod.natCast_rightInverse (n := p^t) x, hm]
  push_cast; ring

-- castHom commutes with inverse of a unit (target ZMod p, a field), general modulus.
theorem castHom_inv_gen {t : ℕ} [Fact p.Prime] (ht : 1 ≤ t) (a : ZMod (p^t)) (ha : IsUnit a) :
    (ZMod.castHom (dvd_pow_self p (by omega : t ≠ 0)) (ZMod p)) (a⁻¹)
      = ((ZMod.castHom (dvd_pow_self p (by omega : t ≠ 0)) (ZMod p)) a)⁻¹ := by
  have h1 : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit a ha
  have h2 : (ZMod.castHom (dvd_pow_self p (by omega : t ≠ 0)) (ZMod p)) a
        * (ZMod.castHom (dvd_pow_self p (by omega : t ≠ 0)) (ZMod p)) (a⁻¹) = 1 := by
    rw [← map_mul, h1, map_one]
  exact (inv_eq_of_mul_eq_one_right h2).symm

-- Power sums over a finite field vanish below degree card - 1.
theorem sum_pow_field_zero [Fact p.Prime] {s : ℕ} (hs : s < p - 1) :
    ∑ x : ZMod p, x ^ s = 0 := by
  have hc : Fintype.card (ZMod p) = p := ZMod.card p
  apply FiniteField.sum_pow_lt_card_sub_one
  rw [hc]; omega

-- ∑_{k=1}^{p-1} (k⁻¹)^s = 0 in ZMod p, for 1 ≤ s < p-1.
theorem sum_inv_pow_units_zero [Fact p.Prime] {s : ℕ} (hs1 : 1 ≤ s) (hs : s < p - 1) :
    ∑ k ∈ Finset.Icc 1 (p-1), ((k : ZMod p)⁻¹) ^ s = 0 := by
  rw [reindex_Icc_to_units (fun x => (x⁻¹)^s)]
  have h2 : ∑ x ∈ (Finset.univ.erase (0 : ZMod p)), (x⁻¹)^s
      = ∑ x ∈ (Finset.univ.erase (0:ZMod p)), x^s := by
    apply Finset.sum_nbij' (fun x => x⁻¹) (fun x => x⁻¹)
    · intro a ha; simp only [Finset.mem_erase, Finset.mem_univ, and_true] at *; exact inv_ne_zero ha
    · intro a ha; simp only [Finset.mem_erase, Finset.mem_univ, and_true] at *; exact inv_ne_zero ha
    · intro a ha; simp only [Finset.mem_erase, Finset.mem_univ, and_true] at ha; exact inv_inv a
    · intro a ha; simp only [Finset.mem_erase, Finset.mem_univ, and_true] at ha; exact inv_inv a
    · intro a ha; rfl
  rw [h2]
  have h3 : ∑ x ∈ (Finset.univ.erase (0:ZMod p)), x^s = ∑ x : ZMod p, x^s := by
    rw [Finset.sum_erase]; rw [zero_pow (by omega : s ≠ 0)]
  rw [h3]; exact sum_pow_field_zero hs

-- w_s := ∑_{k=1}^{p-1} (k⁻¹)^s is divisible by p in ZMod (p^t), for 1 ≤ s < p-1.
theorem sum_inv_pow_dvd_p [Fact p.Prime] {t s : ℕ} (ht : 1 ≤ t) (hs1 : 1 ≤ s) (hs : s < p - 1) :
    (p : ZMod (p^t)) ∣ ∑ k ∈ Finset.Icc 1 (p-1), ((k : ZMod (p^t))⁻¹) ^ s := by
  apply dvd_of_castHom_eq_zero ht
  rw [map_sum]
  have hcong : ∀ k ∈ Finset.Icc 1 (p-1),
      (ZMod.castHom (dvd_pow_self p (by omega : t≠0)) (ZMod p)) (((k:ZMod (p^t))⁻¹)^s)
        = ((k:ZMod p)⁻¹)^s := by
    intro k hk; rw [Finset.mem_Icc] at hk
    rw [map_pow, castHom_inv_gen ht _ (isUnit_of_lt hk.1 hk.2), map_natCast]
  rw [Finset.sum_congr rfl hcong]
  exact sum_inv_pow_units_zero hs1 hs

-- per-term geometric expansion of (c + p*d)⁻¹ to second order, error divisible by p^3.
theorem inv_geom_term {t : ℕ} [Fact p.Prime] (c : ZMod (p^t)) (d : ℕ)
    (hc : IsUnit c) (hcd : IsUnit (c + p * d)) :
    (p:ZMod (p^t))^3 ∣ ((c + p * d)⁻¹
        - (c⁻¹ - (p:ZMod (p^t)) * d * (c⁻¹)^2 + (p:ZMod (p^t))^2 * d^2 * (c⁻¹)^3)) := by
  set ci := c⁻¹ with hci
  have hcci : c * ci = 1 := ZMod.mul_inv_of_unit c hc
  set q := (c + (p:ZMod (p^t)) * d) with hq
  have hqinv : q * q⁻¹ = 1 := ZMod.mul_inv_of_unit q hcd
  have hkey : q * (ci - (p:ZMod (p^t)) * d * ci^2 + (p:ZMod (p^t))^2 * d^2 * ci^3)
      = 1 + (p:ZMod (p^t))^3 * d^3 * ci^3 := by
    rw [hq]
    linear_combination (1 - (p:ZMod (p^t))*d*ci + (p:ZMod (p^t))^2*d^2*ci^2) * hcci
  have hfin : q⁻¹ - (ci - (p:ZMod (p^t)) * d * ci^2 + (p:ZMod (p^t))^2 * d^2 * ci^3)
      = q⁻¹ * (-(((p:ZMod (p^t))^3 * d^3 * ci^3))) := by
    have h0 : (ci - (p:ZMod (p^t)) * d * ci^2 + (p:ZMod (p^t))^2 * d^2 * ci^3)
        = q⁻¹ * (q * (ci - (p:ZMod (p^t)) * d * ci^2 + (p:ZMod (p^t))^2 * d^2 * ci^3)) := by
      rw [← mul_assoc, mul_comm q⁻¹ q, hqinv, one_mul]
    rw [h0, hkey]; ring
  rw [hfin]
  exact ⟨-(q⁻¹ * (d:ZMod (p^t))^3 * ci^3), by ring⟩

-- Reindex {i < p*b : p ∤ i} as a double sum over full residue blocks.
theorem fullblocks_reindex {M0 : Type*} [AddCommMonoid M0] (p b : ℕ) (hp : 1 ≤ p) (f : ℕ → M0) :
    ∑ i ∈ (Finset.range (p*b)).filter (fun i => ¬ p ∣ i), f i
      = ∑ d ∈ Finset.range b, ∑ c ∈ Finset.Icc 1 (p-1), f (c + p * d) := by
  rw [← Finset.sum_product']
  apply Finset.sum_nbij' (fun i => (i / p, i % p)) (fun x => x.2 + p * x.1)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_Icc]
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul hp, Nat.mul_comm]; exact hi.1
    · have : i % p ≠ 0 := fun h => hi.2 (Nat.dvd_of_mod_eq_zero h); omega
    · have := Nat.mod_lt i (show 0 < p by omega); omega
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at hx
    simp only [Finset.mem_filter, Finset.mem_range]
    obtain ⟨hd, hc1, hc2⟩ := hx
    refine ⟨?_, ?_⟩
    · have hb1 : x.1 + 1 ≤ b := by omega
      have h3 : p * x.1 + p ≤ p * b := by nlinarith
      omega
    · intro hdvd
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)] at hdvd
      omega
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only
    rw [Nat.add_comm]; exact Nat.div_add_mod i p
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at hx
    obtain ⟨hd, hc1, hc2⟩ := hx
    have hlt : x.2 < p := by omega
    apply Prod.ext
    · simp only; rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hlt, zero_add]
    · simp only; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only
    congr 1
    rw [Nat.add_comm]; exact (Nat.div_add_mod i p).symm

-- Split the partial-harmonic-type sum over {i < a + p*b : p∤i} into full blocks + last partial block.
theorem box_split {M0 : Type*} [AddCommMonoid M0] (p a b : ℕ) (hp : 1 ≤ p) (ha : 1 ≤ a)
    (ha2 : a ≤ p) (f : ℕ → M0) :
    ∑ i ∈ (Finset.range (a+p*b)).filter (fun i => ¬ p ∣ i), f i
      = (∑ d ∈ Finset.range b, ∑ c ∈ Finset.Icc 1 (p-1), f (c + p * d))
        + ∑ c ∈ Finset.Icc 1 (a-1), f (c + p * b) := by
  have hsplit : (Finset.range (a+p*b)).filter (fun i => ¬ p ∣ i)
      = (Finset.range (p*b)).filter (fun i => ¬ p ∣ i)
        ∪ (Finset.Ico (p*b) (a+p*b)).filter (fun i => ¬ p ∣ i) := by
    rw [← Finset.filter_union]
    congr 1
    simp only [Finset.range_eq_Ico]
    exact (Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (by omega)).symm
  rw [hsplit, Finset.sum_union]
  · rw [fullblocks_reindex p b hp f]
    congr 1
    apply Finset.sum_nbij' (fun i => i - p*b) (fun c => c + p*b)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_Ico] at hi
      simp only [Finset.mem_Icc]
      obtain ⟨⟨h1, h2⟩, h3⟩ := hi
      refine ⟨?_, by omega⟩
      have : i - p*b ≠ 0 := by
        intro h
        have hi2 : i = p*b := by omega
        exact h3 (hi2 ▸ Dvd.intro b (by ring))
      omega
    · intro c hc
      simp only [Finset.mem_Icc] at hc
      simp only [Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      intro hdvd
      have hd2 : p ∣ c := by
        have hh : p ∣ p*b + c := by rwa [Nat.add_comm] at hdvd
        exact (Nat.dvd_add_right (dvd_mul_right p b)).mp hh
      have := Nat.le_of_dvd (by omega) hd2
      omega
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_Ico] at hi
      omega
    · intro c hc
      simp only [Finset.mem_Icc] at hc
      omega
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_Ico] at hi
      congr 1; omega
  · apply Finset.disjoint_filter_filter
    rw [Finset.range_eq_Ico]
    exact Finset.Ico_disjoint_Ico_consecutive 0 (p*b) (a+p*b)

-- Reduction of an inner block sum ∑_{c≤m} (c+p*d)⁻¹ to its second-order approximation.
theorem inner_reduction {t : ℕ} [Fact p.Prime] (m d : ℕ) (hm : m ≤ p - 1) :
    (p:ZMod (p^t))^3 ∣ ((∑ c ∈ Finset.Icc 1 m, ((c:ZMod (p^t)) + p*d)⁻¹)
        - ((∑ c ∈ Finset.Icc 1 m, (c:ZMod (p^t))⁻¹)
           - (p:ZMod (p^t))*d*(∑ c ∈ Finset.Icc 1 m, ((c:ZMod (p^t))⁻¹)^2)
           + (p:ZMod (p^t))^2*d^2*(∑ c ∈ Finset.Icc 1 m, ((c:ZMod (p^t))⁻¹)^3))) := by
  have happrox : (∑ c ∈ Finset.Icc 1 m, (c:ZMod (p^t))⁻¹)
        - (p:ZMod (p^t))*d*(∑ c ∈ Finset.Icc 1 m, ((c:ZMod (p^t))⁻¹)^2)
        + (p:ZMod (p^t))^2*d^2*(∑ c ∈ Finset.Icc 1 m, ((c:ZMod (p^t))⁻¹)^3)
      = ∑ c ∈ Finset.Icc 1 m, ((c:ZMod (p^t))⁻¹ - (p:ZMod (p^t))*d*((c:ZMod (p^t))⁻¹)^2
            + (p:ZMod (p^t))^2*d^2*((c:ZMod (p^t))⁻¹)^3) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  rw [happrox, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro c hc
  rw [Finset.mem_Icc] at hc
  have huc : IsUnit (c:ZMod (p^t)) := isUnit_of_lt hc.1 (le_trans hc.2 hm)
  have hucd : IsUnit ((c:ZMod (p^t)) + p*d) := by
    have heq : (c:ZMod (p^t)) + (p:ZMod (p^t))*(d:ZMod (p^t)) = ((c + p*d : ℕ):ZMod (p^t)) := by
      push_cast; ring
    rw [heq]; apply isUnit_cast_of_not_dvd
    intro hdvd
    have hh : p ∣ p*d + c := by rwa [Nat.add_comm] at hdvd
    have hc' : p ∣ c := (Nat.dvd_add_right (dvd_mul_right p d)).mp hh
    have := Nat.le_of_dvd hc.1 hc'; omega
  exact inv_geom_term (c:ZMod (p^t)) d huc hucd

-- approximation for an inner block (m, d)
noncomputable def iapprox (t m d : ℕ) : ZMod (p^t) :=
  (∑ c ∈ Finset.Icc 1 m, (c:ZMod (p^t))⁻¹)
    - (p:ZMod (p^t))*d*(∑ c ∈ Finset.Icc 1 m, ((c:ZMod (p^t))⁻¹)^2)
    + (p:ZMod (p^t))^2*d^2*(∑ c ∈ Finset.Icc 1 m, ((c:ZMod (p^t))⁻¹)^3)

-- α-reduction: the partial-harmonic inverse sum over the box equals the block approximations mod p^3.
theorem alpha_reduction {t : ℕ} [Fact p.Prime] (a b : ℕ) (ha : 1 ≤ a) (ha2 : a ≤ p) :
    (p:ZMod (p^t))^3 ∣ ((∑ i ∈ (Finset.range (a+p*b)).filter (fun i => ¬p∣i), (i:ZMod (p^t))⁻¹)
        - ((∑ d ∈ Finset.range b, iapprox (p:=p) t (p-1) d) + iapprox (p:=p) t (a-1) b)) := by
  have hp : 1 ≤ p := (Fact.out (p := p.Prime)).pos
  rw [box_split p a b hp ha ha2 (fun i => (i:ZMod (p^t))⁻¹)]
  have hconv : ∀ (c d : ℕ), ((c + p*d : ℕ):ZMod (p^t))⁻¹ = ((c:ZMod (p^t))+p*d)⁻¹ := by
    intro c d; congr 1; push_cast; ring
  simp only [hconv]
  have hrw : ((∑ d ∈ Finset.range b, ∑ c ∈ Finset.Icc 1 (p-1), ((c:ZMod (p^t))+p*d)⁻¹)
        + ∑ c ∈ Finset.Icc 1 (a-1), ((c:ZMod (p^t))+p*b)⁻¹)
        - ((∑ d ∈ Finset.range b, iapprox (p:=p) t (p-1) d) + iapprox (p:=p) t (a-1) b)
      = (∑ d ∈ Finset.range b, ((∑ c ∈ Finset.Icc 1 (p-1), ((c:ZMod (p^t))+p*d)⁻¹)
            - iapprox (p:=p) t (p-1) d))
        + ((∑ c ∈ Finset.Icc 1 (a-1), ((c:ZMod (p^t))+p*b)⁻¹) - iapprox (p:=p) t (a-1) b) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hrw]
  apply dvd_add
  · apply Finset.dvd_sum
    intro d _
    rw [iapprox]
    exact inner_reduction (p-1) d (le_refl _)
  · rw [iapprox]
    exact inner_reduction (a-1) b (by omega)

-- Second-order product expansion (for A = ∏(1 + p²·i⁻¹)).
theorem A_expansion {t : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) (s : Finset ℕ)
    (x : ℕ → ZMod (p^t)) (c : ZMod (p^t)) :
    c^3 ∣ (∏ i ∈ s, (1 + c * x i)
        - (1 + c * (∑ i ∈ s, x i)
            + c^2 * ((2:ZMod (p^t))⁻¹ * ((∑ i ∈ s, x i)^2 - ∑ i ∈ s, (x i)^2)))) := by
  have h2u : IsUnit (2:ZMod (p^t)) := by
    have he : ((2:ℕ):ZMod (p^t)) = 2 := by push_cast; ring
    rw [← he]
    exact isUnit_cast_of_not_dvd (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
  have h2 : (2:ZMod (p^t)) * (2:ZMod (p^t))⁻¹ = 1 := ZMod.mul_inv_of_unit _ h2u
  induction s using Finset.induction with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, Finset.sum_insert hj]
    set Pr := ∏ i ∈ s, (1 + c * x i) with hPr
    set P1 := ∑ i ∈ s, x i with hP1
    set P2 := ∑ i ∈ s, (x i)^2 with hP2
    set iv := (2:ZMod (p^t))⁻¹ with hiv
    have key : (1 + c * x j) * Pr
        - (1 + c * (x j + P1) + c^2 * (iv * ((x j + P1)^2 - ((x j)^2 + P2))))
        = (1 + c * x j) * (Pr - (1 + c * P1 + c^2 * (iv * (P1^2 - P2))))
          + c^3 * (iv * (P1^2 - P2) * x j) := by
      linear_combination (-(c^2 * P1 * x j)) * h2
    rw [key]
    exact dvd_add (Dvd.dvd.mul_left ih _) (Dvd.intro _ rfl)

-- Fourth-order product expansion via elementary symmetric polynomials.
-- ∏(1 + c·x i) ≡ ∑_{j<5} c^j · e_j  (mod c^5), where e_j = ∑_{T∈powersetCard j} ∏ x.
theorem B_expansion {t : ℕ} (s : Finset ℕ) (x : ℕ → ZMod (p^t)) (c : ZMod (p^t)) :
    c^5 ∣ (∏ i ∈ s, (1 + c * x i)
      - ∑ j ∈ Finset.range 5, c^j * (∑ T ∈ s.powersetCard j, ∏ i ∈ T, x i)) := by
  have hterm : ∀ T : Finset ℕ, ∏ i ∈ T, (c * x i) = c^(T.card) * ∏ i ∈ T, x i := by
    intro T; rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hprod : ∏ i ∈ s, (1 + c * x i)
      = ∑ j ∈ Finset.range (s.card + 1), c^j * (∑ T ∈ s.powersetCard j, ∏ i ∈ T, x i) := by
    rw [Finset.prod_one_add s]
    simp only [hterm]
    rw [Finset.powerset_card_biUnion, Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      rw [Finset.mem_powersetCard] at hT
      rw [hT.2]
    · intro a _ b _ hab
      simp only [Function.onFun, Finset.disjoint_left]
      intro T hTa hTb
      rw [Finset.mem_powersetCard] at hTa hTb
      exact hab (hTa.2 ▸ hTb.2)
  rw [hprod]
  set F := fun j => c^j * (∑ T ∈ s.powersetCard j, ∏ i ∈ T, x i) with hF
  set N := s.card + 1 with hN
  set M := max N 5 with hM
  have hext : ∑ j ∈ Finset.range N, F j = ∑ j ∈ Finset.range M, F j := by
    apply Finset.sum_subset
    · intro a ha; simp only [Finset.mem_range] at ha ⊢; omega
    · intro j _ hjn
      simp only [Finset.mem_range, not_lt] at hjn
      simp only [hF]
      have : s.powersetCard j = ∅ := Finset.powersetCard_eq_empty.2 (by omega)
      rw [this]; simp
  rw [hext]
  have h5M : Finset.range 5 ⊆ Finset.range M := by
    intro a ha; simp only [Finset.mem_range] at ha ⊢; omega
  rw [← Finset.sum_sdiff h5M]
  rw [add_sub_cancel_right]
  apply Finset.dvd_sum
  intro j hj
  rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range, not_lt] at hj
  simp only [hF]
  have : c^j = c^5 * c^(j-5) := by rw [← pow_add]; congr 1; omega
  rw [this, mul_assoc]
  exact Dvd.intro _ rfl

-- ===== Newton identities (elementary symmetric -> power sums) =====
variable {R : Type*} [CommRing R]

-- E_j recursion under insert.
theorem esym_insert (f : ℕ → R) {x : ℕ} {s : Finset ℕ} (hx : x ∉ s) (j : ℕ) :
    ∑ T ∈ (insert x s).powersetCard (j+1), ∏ i ∈ T, f i
      = (∑ T ∈ s.powersetCard (j+1), ∏ i ∈ T, f i)
        + f x * ∑ T ∈ s.powersetCard j, ∏ i ∈ T, f i := by
  rw [Finset.powersetCard_succ_insert hx, Finset.sum_union]
  · congr 1
    rw [Finset.sum_image]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      rw [Finset.mem_powersetCard] at hT
      rw [Finset.prod_insert (fun h => hx (hT.1 h))]
    · intro T1 h1 T2 h2 he
      rw [Finset.mem_coe, Finset.mem_powersetCard] at h1 h2
      have e1 : x ∉ T1 := fun h => hx (h1.1 h)
      have e2 : x ∉ T2 := fun h => hx (h2.1 h)
      have := congrArg (fun u => Finset.erase u x) he
      simp only [Finset.erase_insert e1, Finset.erase_insert e2] at this
      exact this
  · rw [Finset.disjoint_left]
    intro T hT1 hT2
    rw [Finset.mem_powersetCard] at hT1
    rw [Finset.mem_image] at hT2
    obtain ⟨T', hT', rfl⟩ := hT2
    exact (fun h => hx (h)) (hT1.1 (Finset.mem_insert_self x T'))

-- E1 = S1
theorem esym_one_eq (f : ℕ → R) (s : Finset ℕ) :
    ∑ T ∈ s.powersetCard 1, ∏ i ∈ T, f i = ∑ i ∈ s, f i := by
  rw [Finset.powersetCard_one, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro i _
  simp

-- Newton identity 2: 2 * E2 = S1^2 - S2
theorem newton2 (f : ℕ → R) (s : Finset ℕ) :
    2 * (∑ T ∈ s.powersetCard 2, ∏ i ∈ T, f i)
      = (∑ i ∈ s, f i)^2 - ∑ i ∈ s, (f i)^2 := by
  induction s using Finset.induction with
  | empty =>
    have : (∅ : Finset ℕ).powersetCard 2 = ∅ := by rw [Finset.powersetCard_eq_empty]; simp
    rw [this]; simp
  | @insert x s hx ih =>
    have e2 : (insert x s).powersetCard 2 = (insert x s).powersetCard (1+1) := by norm_num
    rw [e2, esym_insert f hx 1, esym_one_eq f s, Finset.sum_insert hx, Finset.sum_insert hx]
    have h : 2 * ((∑ T ∈ s.powersetCard 2, ∏ i ∈ T, f i) + f x * ∑ i ∈ s, f i)
        = 2 * (∑ T ∈ s.powersetCard 2, ∏ i ∈ T, f i) + 2 * (f x * ∑ i ∈ s, f i) := by ring
    rw [h, ih]; ring

-- Newton identity 3: 6 * E3 = S1^3 - 3 S1 S2 + 2 S3
theorem newton3 (f : ℕ → R) (s : Finset ℕ) :
    6 * (∑ T ∈ s.powersetCard 3, ∏ i ∈ T, f i)
      = (∑ i ∈ s, f i)^3 - 3 * (∑ i ∈ s, f i) * (∑ i ∈ s, (f i)^2)
        + 2 * (∑ i ∈ s, (f i)^3) := by
  induction s using Finset.induction with
  | empty =>
    have : (∅ : Finset ℕ).powersetCard 3 = ∅ := by rw [Finset.powersetCard_eq_empty]; simp
    rw [this]; simp
  | @insert x s hx ih =>
    have e3 : (insert x s).powersetCard 3 = (insert x s).powersetCard (2+1) := by norm_num
    rw [e3, esym_insert f hx 2, Finset.sum_insert hx, Finset.sum_insert hx, Finset.sum_insert hx]
    linear_combination ih + 3 * (f x) * newton2 f s

-- Newton identity 4: 24 * E4 = S1^4 - 6 S1^2 S2 + 3 S2^2 + 8 S1 S3 - 6 S4
theorem newton4 (f : ℕ → R) (s : Finset ℕ) :
    24 * (∑ T ∈ s.powersetCard 4, ∏ i ∈ T, f i)
      = (∑ i ∈ s, f i)^4 - 6 * (∑ i ∈ s, f i)^2 * (∑ i ∈ s, (f i)^2)
        + 3 * (∑ i ∈ s, (f i)^2)^2 + 8 * (∑ i ∈ s, f i) * (∑ i ∈ s, (f i)^3)
        - 6 * (∑ i ∈ s, (f i)^4) := by
  induction s using Finset.induction with
  | empty =>
    have : (∅ : Finset ℕ).powersetCard 4 = ∅ := by rw [Finset.powersetCard_eq_empty]; simp
    rw [this]; simp
  | @insert x s hx ih =>
    have e4 : (insert x s).powersetCard 4 = (insert x s).powersetCard (3+1) := by norm_num
    rw [e4, esym_insert f hx 3, Finset.sum_insert hx, Finset.sum_insert hx, Finset.sum_insert hx,
       Finset.sum_insert hx]
    linear_combination ih + 4 * (f x) * newton3 f s

-- ===== Product/inverse ratio helpers =====
theorem prod_units_inv {t : ℕ} [Fact p.Prime] (s : Finset ℕ) (h : ℕ → ZMod (p^t))
    (hu : ∀ i ∈ s, IsUnit (h i)) :
    (∏ i ∈ s, h i)⁻¹ = ∏ i ∈ s, (h i)⁻¹ := by
  have key : (∏ i ∈ s, h i) * (∏ i ∈ s, (h i)⁻¹) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i hi
    exact ZMod.mul_inv_of_unit _ (hu i hi)
  have hu' : IsUnit (∏ i ∈ s, h i) := IsUnit.of_mul_eq_one _ key
  apply hu'.mul_right_injective
  beta_reduce
  rw [ZMod.mul_inv_of_unit _ hu', key]

theorem prod_one_add_ratio {t : ℕ} [Fact p.Prime] (s : Finset ℕ) (C : ZMod (p^t))
    (h : ℕ → ZMod (p^t)) (hu : ∀ i ∈ s, IsUnit (h i)) :
    (∏ i ∈ s, (C + h i)) * (∏ i ∈ s, h i)⁻¹ = ∏ i ∈ s, (1 + C * (h i)⁻¹) := by
  rw [prod_units_inv s h hu, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hh : (h i) * (h i)⁻¹ = 1 := ZMod.mul_inv_of_unit _ (hu i hi)
  linear_combination hh

-- ===== b_k product form: C(p^2+k-1,k) = p^2 k⁻¹ · A · B =====
theorem bk_AB [Fact p.Prime] {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < p^2) (hkp : ¬ p ∣ k) :
    (Nat.choose (p^2+k-1) k : ZMod (p^9))
      = (p:ZMod (p^9))^2 * (k:ZMod (p^9))⁻¹
          * (∏ i ∈ (Finset.range k).filter (fun i => ¬ p ∣ i),
                (1 + (p:ZMod (p^9))^2 * (i:ZMod (p^9))⁻¹))
          * (∏ l ∈ Finset.Icc 1 ((k-1)/p),
                (1 + (p:ZMod (p^9)) * (l:ZMod (p^9))⁻¹)) := by
  have hb : (k-1)/p < p := by
    have : k - 1 < p^2 := by omega
    calc (k-1)/p ≤ (p^2-1)/p := Nat.div_le_div_right (by omega)
      _ < p := by
          rw [Nat.div_lt_iff_lt_mul (Fact.out (p := p.Prime)).pos]
          have h2 : p^2 = p * p := by ring
          omega
  rw [bk_offdiag_formula hk1 hk2 hkp]
  have hr1 : (∏ i ∈ (Finset.range k).filter (fun i => ¬ p ∣ i), ((p^2:ZMod (p^9)) + i))
        * (∏ i ∈ (Finset.range k).filter (fun i => ¬ p ∣ i), (i:ZMod (p^9)))⁻¹
      = ∏ i ∈ (Finset.range k).filter (fun i => ¬ p ∣ i),
            (1 + (p:ZMod (p^9))^2 * (i:ZMod (p^9))⁻¹) := by
    have := prod_one_add_ratio (Finset.range k |>.filter (fun i => ¬ p ∣ i)) ((p:ZMod (p^9))^2)
        (fun i => (i:ZMod (p^9))) (by
          intro i hi; rw [Finset.mem_filter] at hi
          exact isUnit_cast_of_not_dvd hi.2)
    simp only at this
    rw [show ((p^2:ZMod (p^9))) = (p:ZMod (p^9))^2 by push_cast; ring]
    convert this using 2
  have hr2 : (∏ l ∈ Finset.Icc 1 ((k-1)/p), ((p:ZMod (p^9)) + l))
        * (∏ l ∈ Finset.Icc 1 ((k-1)/p), (l:ZMod (p^9)))⁻¹
      = ∏ l ∈ Finset.Icc 1 ((k-1)/p), (1 + (p:ZMod (p^9)) * (l:ZMod (p^9))⁻¹) := by
    have := prod_one_add_ratio (Finset.Icc 1 ((k-1)/p)) (p:ZMod (p^9))
        (fun l => (l:ZMod (p^9))) (by
          intro l hl; rw [Finset.mem_Icc] at hl
          apply isUnit_cast_of_not_dvd
          intro hd; have := Nat.le_of_dvd (by omega) hd; omega)
    exact this
  rw [hr1, hr2]

-- ===== g-value reduction: g(b_k) = g(beta_k) mod p^9 =====
theorem dvd_mul_sub {R : Type*} [CommRing R] (e X X0 Y Y0 : R)
    (hX : e ∣ (X - X0)) (hY : e ∣ (Y - Y0)) : e ∣ (X*Y - X0*Y0) := by
  have : X*Y - X0*Y0 = (X - X0)*Y + X0*(Y - Y0) := by ring
  rw [this]; exact dvd_add (hX.mul_right _) (hY.mul_left _)

theorem g_reduce {A B A0 B0 K : ZMod (p^9)}
    (hA : (p:ZMod (p^9))^6 ∣ (A - A0)) (hB : (p:ZMod (p^9))^5 ∣ (B - B0)) :
    3 * ((p:ZMod (p^9))^2 * K * A * B)^2 + 2 * ((p:ZMod (p^9))^2 * K * A * B)^3
      = 3 * ((p:ZMod (p^9))^2 * K * A0 * B0)^2 + 2 * ((p:ZMod (p^9))^2 * K * A0 * B0)^3 := by
  have hAn : ∀ n, (p:ZMod (p^9))^6 ∣ (A^n - A0^n) := fun n =>
    dvd_trans hA (sub_dvd_pow_sub_pow A A0 n)
  have hBn : ∀ n, (p:ZMod (p^9))^5 ∣ (B^n - B0^n) := fun n =>
    dvd_trans hB (sub_dvd_pow_sub_pow B B0 n)
  have hABn : ∀ n, (p:ZMod (p^9))^5 ∣ (A^n*B^n - A0^n*B0^n) := by
    intro n
    apply dvd_mul_sub
    · exact dvd_trans (pow_dvd_pow _ (by norm_num)) (hAn n)
    · exact hBn n
  have key : (p:ZMod (p^9))^9 ∣
      ((3 * ((p:ZMod (p^9))^2 * K * A * B)^2 + 2 * ((p:ZMod (p^9))^2 * K * A * B)^3)
       - (3 * ((p:ZMod (p^9))^2 * K * A0 * B0)^2 + 2 * ((p:ZMod (p^9))^2 * K * A0 * B0)^3)) := by
    obtain ⟨w2, hw2⟩ := hABn 2
    obtain ⟨w3, hw3⟩ := hABn 3
    have e2 : (3 * ((p:ZMod (p^9))^2 * K * A * B)^2 + 2 * ((p:ZMod (p^9))^2 * K * A * B)^3)
       - (3 * ((p:ZMod (p^9))^2 * K * A0 * B0)^2 + 2 * ((p:ZMod (p^9))^2 * K * A0 * B0)^3)
        = (p:ZMod (p^9))^4 * (3 * K^2 * (A^2*B^2 - A0^2*B0^2))
          + (p:ZMod (p^9))^6 * (2 * K^3 * (A^3*B^3 - A0^3*B0^3)) := by ring
    rw [e2, hw2, hw3]
    refine dvd_add ⟨3*K^2*w2, by ring⟩ ⟨(p:ZMod (p^9))^2*(2*K^3*w3), by ring⟩
  have hz : (p:ZMod (p^9))^9 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [hz, zero_dvd_iff] at key
  exact sub_eq_zero.mp key

-- ===== Truncated factors and per-term g-reduction =====
noncomputable def SA1 (k : ℕ) : ZMod (p^9) :=
  ∑ i ∈ (Finset.range k).filter (fun i => ¬ p ∣ i), (i:ZMod (p^9))⁻¹
noncomputable def SA2 (k : ℕ) : ZMod (p^9) :=
  ∑ i ∈ (Finset.range k).filter (fun i => ¬ p ∣ i), ((i:ZMod (p^9))⁻¹)^2
noncomputable def Atr (k : ℕ) : ZMod (p^9) :=
  1 + (p:ZMod (p^9))^2 * SA1 k
    + ((p:ZMod (p^9))^2)^2 * ((2:ZMod (p^9))⁻¹ * ((SA1 k)^2 - SA2 k))
noncomputable def Eb (j k : ℕ) : ZMod (p^9) :=
  ∑ T ∈ (Finset.Icc 1 ((k-1)/p)).powersetCard j, ∏ l ∈ T, (l:ZMod (p^9))⁻¹
noncomputable def Btr (k : ℕ) : ZMod (p^9) :=
  ∑ j ∈ Finset.range 5, (p:ZMod (p^9))^j * Eb j k

theorem term_eq [Fact p.Prime] (hp5 : 5 ≤ p) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < p^2)
    (hkp : ¬ p ∣ k) :
    3 * (Nat.choose (p^2+k-1) k : ZMod (p^9))^2 + 2 * (Nat.choose (p^2+k-1) k : ZMod (p^9))^3
      = 3 * ((p:ZMod (p^9))^2 * (k:ZMod (p^9))⁻¹ * Atr k * Btr k)^2
        + 2 * ((p:ZMod (p^9))^2 * (k:ZMod (p^9))⁻¹ * Atr k * Btr k)^3 := by
  rw [bk_AB hk1 hk2 hkp]
  apply g_reduce
  · have h := A_expansion (p:=p) (t:=9) (by omega)
      ((Finset.range k).filter (fun i => ¬ p ∣ i)) (fun i => (i:ZMod (p^9))⁻¹) ((p:ZMod (p^9))^2)
    rw [show ((p:ZMod (p^9))^2)^3 = (p:ZMod (p^9))^6 from by ring] at h
    simp only [Atr, SA1, SA2]
    convert h using 2
  · have h := B_expansion (p:=p) (t:=9)
      (Finset.Icc 1 ((k-1)/p)) (fun l => (l:ZMod (p^9))⁻¹) (p:ZMod (p^9))
    simp only [Btr, Eb]
    convert h using 2

-- ===== Diagonal identity: C(p^r+pj-1,pj)·P1 = C(p^(r-1)+j-1,j)·Q1 =====
theorem diag_int_identity (p r j : ℕ) (hp : 1 ≤ p) (hr : 1 ≤ r) (hj : 1 ≤ j) :
    (Nat.choose (p^r + p*j - 1) (p*j))
        * (∏ i ∈ (Finset.range (p*j)).filter (fun i => ¬ p ∣ i), i)
      = (Nat.choose (p^(r-1) + j - 1) j)
        * (∏ i ∈ (Finset.range (p*j)).filter (fun i => ¬ p ∣ i), (p^r + i)) := by
  have hle : p ≤ p*j := Nat.le_mul_of_pos_right p hj
  have hbeq : (p*j - 1)/p = j - 1 := by
    have hmul : p*(j-1) + p = p*j := by rw [← Nat.mul_succ]; congr 1; omega
    have h1 : p*j - 1 = (p-1) + p*(j-1) := by omega
    rw [h1, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (by omega : p-1<p)]; omega
  have hbox := box_int_identity p r (p*j) hp hr (Nat.mul_pos hp hj)
  rw [hbeq] at hbox
  have hIcc : Finset.Icc 1 (j-1) = Finset.Ico 1 ((j-1)+1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff]
  have hPbf : (∏ l ∈ Finset.Icc 1 (j-1), l) = (j-1).factorial := by
    rw [hIcc]; exact Finset.prod_Ico_id_eq_factorial (j-1)
  rw [hPbf] at hbox
  have hfc : j.factorial * Nat.choose (p^(r-1)+j-1) j = ∏ i ∈ Finset.range j, (p^(r-1)+i) :=
    factorial_mul_choose_eq_prod (p^(r-1)) j
  have hsplit0 : (∏ i ∈ Finset.range j, (p^(r-1)+i))
      = p^(r-1) * ∏ l ∈ Finset.Icc 1 (j-1), (p^(r-1)+l) := by
    have hr0 : Finset.range j = insert 0 (Finset.Icc 1 (j-1)) := by
      ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hr0, Finset.prod_insert (by simp), Nat.add_zero]
  set C2 := Nat.choose (p^r+p*j-1) (p*j)
  set P1 := ∏ i ∈ (Finset.range (p*j)).filter (fun i => ¬ p ∣ i), i with hP1
  set Q1 := ∏ i ∈ (Finset.range (p*j)).filter (fun i => ¬ p ∣ i), (p^r + i) with hQ1
  set Qb := ∏ l ∈ Finset.Icc 1 (j-1), (p^(r-1)+l) with hQbdef
  set Cj := Nat.choose (p^(r-1)+j-1) j with hCj
  have hQbrel : p^(r-1) * Qb = j.factorial * Cj := by rw [← hsplit0]; exact hfc.symm
  have hpr : p^r = p * p^(r-1) := by conv_lhs => rw [show r = (r-1)+1 by omega]; rw [pow_succ, mul_comm]
  have hjf : j.factorial = j * (j-1).factorial := (Nat.mul_factorial_pred (by omega : j ≠ 0)).symm
  have e : C2 * (p*j*P1*(j-1).factorial) * p^(r-1) = p^r * (Q1 * Qb) * p^(r-1) := by
    rw [hbox]
  have key : C2 * P1 * (p^r * j.factorial) = Cj * Q1 * (p^r * j.factorial) := by
    calc C2 * P1 * (p^r * j.factorial)
        = C2 * (p*j*P1*(j-1).factorial) * p^(r-1) := by rw [hpr, hjf]; ring
      _ = p^r * (Q1 * Qb) * p^(r-1) := e
      _ = Q1 * (p^(r-1) * Qb) * p^r := by ring
      _ = Q1 * (j.factorial * Cj) * p^r := by rw [hQbrel]
      _ = Cj * Q1 * (p^r * j.factorial) := by ring
  exact Nat.eq_of_mul_eq_mul_right (by positivity) key

-- ===== ZMod diagonal correction: b_{pj}(p^2) = b_j(p)·Gj =====
theorem diag_zmod [Fact p.Prime] {j : ℕ} (hj : 1 ≤ j) :
    (Nat.choose (p^2+p*j-1) (p*j) : ZMod (p^9))
      = (Nat.choose (p+j-1) j : ZMod (p^9))
        * ∏ i ∈ (Finset.range (p*j)).filter (fun i => ¬ p ∣ i),
            (1 + (p:ZMod (p^9))^2 * (i:ZMod (p^9))⁻¹) := by
  have hp1 : 1 ≤ p := (Fact.out (p := p.Prime)).one_le
  have hint := diag_int_identity p 2 j hp1 (by norm_num) hj
  rw [show (2:ℕ)-1 = 1 from rfl, pow_one] at hint
  -- cast to ZMod
  have hcast : (Nat.choose (p^2+p*j-1) (p*j) : ZMod (p^9))
        * (∏ i ∈ (Finset.range (p*j)).filter (fun i => ¬ p ∣ i), (i:ZMod (p^9)))
      = (Nat.choose (p+j-1) j : ZMod (p^9))
        * (∏ i ∈ (Finset.range (p*j)).filter (fun i => ¬ p ∣ i), ((p:ZMod (p^9))^2 + (i:ZMod (p^9)))) := by
    have := congrArg (fun n : ℕ => (n : ZMod (p^9))) hint
    push_cast at this
    convert this using 3
  have huP1 : IsUnit (∏ i ∈ (Finset.range (p*j)).filter (fun i => ¬ p ∣ i), (i:ZMod (p^9))) := by
    apply prod_filter_isUnit
    intro i hi; exact (Finset.mem_filter.mp hi).2
  -- ratio
  have hratio : (∏ i ∈ (Finset.range (p*j)).filter (fun i => ¬ p ∣ i), ((p:ZMod (p^9))^2 + (i:ZMod (p^9))))
        * (∏ i ∈ (Finset.range (p*j)).filter (fun i => ¬ p ∣ i), (i:ZMod (p^9)))⁻¹
      = ∏ i ∈ (Finset.range (p*j)).filter (fun i => ¬ p ∣ i),
          (1 + (p:ZMod (p^9))^2 * (i:ZMod (p^9))⁻¹) :=
    prod_one_add_ratio _ _ _ (by intro i hi; rw [Finset.mem_filter] at hi; exact isUnit_cast_of_not_dvd hi.2)
  -- solve for choose
  conv_lhs => rw [← mul_one (Nat.choose (p^2+p*j-1) (p*j) : ZMod (p^9)),
                  ← ZMod.mul_inv_of_unit _ huP1]
  rw [← mul_assoc, hcast, mul_assoc, hratio]

-- ===== Wolstenholme: p^2 | sum of inverses =====
theorem wol_div_p2 [hp : Fact p.Prime] (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
    (p : ZMod (p^t))^2 ∣ ∑ k ∈ Finset.Icc 1 (p-1), (k : ZMod (p^t))⁻¹ := by
  set S := ∑ k ∈ Finset.Icc 1 (p-1), (k : ZMod (p^t))⁻¹ with hS
  have hrefl : S = ∑ k ∈ Finset.Icc 1 (p-1), ((p - k : ℕ) : ZMod (p^t))⁻¹ :=
    sum_Icc_reflect (fun k => (k : ZMod (p^t))⁻¹)
  have hunit : ∀ k ∈ Finset.Icc 1 (p-1), IsUnit (k : ZMod (p^t)) := by
    intro k hk; simp only [Finset.mem_Icc] at hk; exact isUnit_of_lt hk.1 hk.2
  have hunit' : ∀ k ∈ Finset.Icc 1 (p-1), IsUnit ((p - k : ℕ) : ZMod (p^t)) := by
    intro k hk; simp only [Finset.mem_Icc] at hk; exact isUnit_of_lt (by omega) (by omega)
  set T := ∑ k ∈ Finset.Icc 1 (p-1), ((k : ZMod (p^t))⁻¹ * ((p - k : ℕ) : ZMod (p^t))⁻¹) with hT
  have hcast : ∀ k ∈ Finset.Icc 1 (p-1), ((p - k : ℕ) : ZMod (p^t)) = (p : ZMod (p^t)) - (k : ZMod (p^t)) := by
    intro k hk; simp only [Finset.mem_Icc] at hk; rw [Nat.cast_sub (by omega)]
  have hkey : (2 : ZMod (p^t)) * S = (p : ZMod (p^t)) * T := by
    rw [two_mul]; nth_rewrite 2 [hrefl]
    rw [hT, Finset.mul_sum, hS, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hu := hunit k hk; have hw := hunit' k hk; have hck := hcast k hk
    have hsum : (k : ZMod (p^t)) + ((p - k : ℕ) : ZMod (p^t)) = (p : ZMod (p^t)) := by rw [hck]; ring
    have e1 : (k : ZMod (p^t)) * ((k : ZMod (p^t))⁻¹) = 1 := ZMod.mul_inv_of_unit _ hu
    have e2 : ((p - k : ℕ) : ZMod (p^t)) * (((p - k : ℕ) : ZMod (p^t))⁻¹) = 1 := ZMod.mul_inv_of_unit _ hw
    have hexp : (k : ZMod (p^t))⁻¹ + ((p - k : ℕ) : ZMod (p^t))⁻¹
         = ((k : ZMod (p^t)) + ((p - k : ℕ) : ZMod (p^t))) * ((k : ZMod (p^t))⁻¹ * ((p - k : ℕ) : ZMod (p^t))⁻¹) := by
      rw [add_mul]
      rw [show ((k : ZMod (p^t)) * ((k : ZMod (p^t))⁻¹ * ((p - k : ℕ) : ZMod (p^t))⁻¹))
            = ((k : ZMod (p^t)) * (k : ZMod (p^t))⁻¹) * ((p - k : ℕ) : ZMod (p^t))⁻¹ by ring, e1, one_mul]
      rw [show (((p - k : ℕ) : ZMod (p^t)) * ((k : ZMod (p^t))⁻¹ * ((p - k : ℕ) : ZMod (p^t))⁻¹))
            = ((p - k : ℕ) : ZMod (p^t)) * ((p - k : ℕ) : ZMod (p^t))⁻¹ * (k : ZMod (p^t))⁻¹ by ring, e2, one_mul]
      rw [add_comm]
    rw [hexp, hsum]
  -- p | T
  have hpT : (p : ZMod (p^t)) ∣ T := by
    apply dvd_of_castHom_eq_zero ht
    rw [hT, map_sum]
    have hterm : ∀ k ∈ Finset.Icc 1 (p-1),
        (ZMod.castHom (dvd_pow_self p (by omega : t≠0)) (ZMod p))
          ((k : ZMod (p^t))⁻¹ * ((p - k : ℕ) : ZMod (p^t))⁻¹) = -(((k : ZMod p)⁻¹)^2) := by
      intro k hk; simp only [Finset.mem_Icc] at hk
      rw [map_mul, castHom_inv_gen ht _ (hunit k (by simp [Finset.mem_Icc]; omega)),
          castHom_inv_gen ht _ (hunit' k (by simp [Finset.mem_Icc]; omega)), map_natCast, map_natCast]
      have c3 : ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring
      rw [c3, inv_neg]; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, sum_inv_pow_units_zero (by norm_num) (by omega), neg_zero]
  obtain ⟨T', hT'⟩ := hpT
  have h2S : (2 : ZMod (p^t)) * S = (p : ZMod (p^t))^2 * T' := by rw [hkey, hT']; ring
  have h2unit : IsUnit (2 : ZMod (p^t)) := by
    have he : ((2:ℕ):ZMod (p^t)) = 2 := by push_cast; ring
    rw [← he]; exact isUnit_cast_of_not_dvd (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
  refine ⟨(2:ZMod (p^t))⁻¹ * T', ?_⟩
  have : S = (2:ZMod (p^t))⁻¹ * ((2:ZMod (p^t)) * S) := by
    rw [← mul_assoc, ZMod.inv_mul_of_unit _ h2unit, one_mul]
  rw [this, h2S]; ring

-- ===== A357565 definition and base case split =====
def A357565 (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k =>
    let b := choose (n + k - 1) k
    3 * b ^ 2 + 2 * b ^ 3

theorem A357565_zmod_eq (N M : ℕ) :
    (A357565 N : ZMod M)
      = ∑ k ∈ Finset.range (N+1),
          (3 * (Nat.choose (N+k-1) k : ZMod M)^2 + 2 * (Nat.choose (N+k-1) k : ZMod M)^3) := by
  unfold A357565; push_cast; rfl

noncomputable def Uoff [Fact p.Prime] : ZMod (p^9) :=
  ∑ a ∈ Finset.Icc 1 (p-1), ∑ b ∈ Finset.range p,
    (3 * ((p:ZMod (p^9))^2 * ((a+p*b:ℕ):ZMod (p^9))⁻¹ * Atr (a+p*b) * Btr (a+p*b))^2
     + 2 * ((p:ZMod (p^9))^2 * ((a+p*b:ℕ):ZMod (p^9))⁻¹ * Atr (a+p*b) * Btr (a+p*b))^3)

noncomputable def Ddiag [Fact p.Prime] : ZMod (p^9) :=
  ∑ l ∈ Finset.Icc 1 p,
    let bl := (Nat.choose (p+l-1) l : ZMod (p^9))
    let Gl := ∏ i ∈ (Finset.range (p*l)).filter (fun i => ¬ p ∣ i), (1 + (p:ZMod (p^9))^2 * (i:ZMod (p^9))⁻¹)
    3 * bl^2 * (Gl^2 - 1) + 2 * bl^3 * (Gl^3 - 1)

theorem base_split [Fact p.Prime] (hp5 : 5 ≤ p) :
    (A357565 (p^2) : ZMod (p^9)) - (A357565 p : ZMod (p^9)) = Uoff + Ddiag := by
  have hp1 : 1 ≤ p := (Fact.out (p := p.Prime)).one_le
  rw [A357565_zmod_eq, A357565_zmod_eq]
  have hN : p^2 = p * p := sq p
  set f : ℕ → ZMod (p^9) := fun k => 3 * (Nat.choose (p^2+k-1) k : ZMod (p^9))^2 + 2 * (Nat.choose (p^2+k-1) k : ZMod (p^9))^3 with hf
  rw [show (∑ k ∈ Finset.range (p^2+1), (3 * (Nat.choose (p^2+k-1) k : ZMod (p^9))^2 + 2 * (Nat.choose (p^2+k-1) k : ZMod (p^9))^3)) = ∑ k ∈ Finset.range (p^2+1), f k from rfl]
  rw [show p^2 + 1 = p*p + 1 from by rw [hN]]
  rw [sum_range_split_by_p p p hp1 f]
  rw [show p*p+1 = p^2+1 from by rw [hN]]
  -- off-diagonal sum = Uoff
  have hoff : (∑ k ∈ (Finset.range (p^2+1)).filter (fun k => ¬ p ∣ k), f k) = Uoff := by
    rw [units_box_sum (by omega) (by norm_num) f]
    simp only [show (2:ℕ)-1 = 1 from rfl, pow_one]
    rw [Uoff]
    apply Finset.sum_congr rfl; intro a ha
    apply Finset.sum_congr rfl; intro b hb
    simp only [Finset.mem_Icc] at ha
    simp only [Finset.mem_range] at hb
    have hk1 : 1 ≤ a + p*b := by omega
    have h1 : a < p := by omega
    have hb1 : b + 1 ≤ p := by omega
    have hk2 : a + p*b < p^2 := by
      have hmul : p * (b+1) ≤ p * p := Nat.mul_le_mul le_rfl hb1
      rw [hN]; nlinarith [hmul, h1]
    have hkp : ¬ p ∣ (a + p*b) := by
      intro hd
      have hda : p ∣ a := by
        have h2 : p ∣ p * b := Dvd.intro b rfl
        exact (Nat.dvd_add_right h2).mp (by rwa [Nat.add_comm] at hd)
      have := Nat.le_of_dvd (by omega) hda
      omega
    rw [hf]
    exact term_eq hp5 hk1 hk2 hkp
  -- diagonal sum
  have hdiag : (∑ l ∈ Finset.range (p+1), f (p*l)) - (∑ k ∈ Finset.range (p+1), (3 * (Nat.choose (p+k-1) k : ZMod (p^9))^2 + 2 * (Nat.choose (p+k-1) k : ZMod (p^9))^3)) = Ddiag := by
    have hr : Finset.range (p+1) = insert 0 (Finset.Icc 1 p) := by
      ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hr, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
    have hf0 : f (p*0) = 5 := by simp [hf]; norm_num
    have hg00 : (3 * (Nat.choose (p+0-1) 0 : ZMod (p^9))^2 + 2 * (Nat.choose (p+0-1) 0 : ZMod (p^9))^3) = 5 := by simp; norm_num
    rw [hf0, hg00, Ddiag]
    rw [show (5 + ∑ l ∈ Finset.Icc 1 p, f (p*l)) - (5 + ∑ k ∈ Finset.Icc 1 p, (3 * (Nat.choose (p+k-1) k : ZMod (p^9))^2 + 2 * (Nat.choose (p+k-1) k : ZMod (p^9))^3))
              = (∑ l ∈ Finset.Icc 1 p, f (p*l)) - (∑ k ∈ Finset.Icc 1 p, (3 * (Nat.choose (p+k-1) k : ZMod (p^9))^2 + 2 * (Nat.choose (p+k-1) k : ZMod (p^9))^3)) from by ring]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro l hl
    simp only [Finset.mem_Icc] at hl
    simp only [hf]
    rw [diag_zmod (by omega : 1 ≤ l)]
    ring
  rw [hoff]
  rw [show (∑ l ∈ Finset.range (p+1), f (p*l)) + Uoff - (∑ k ∈ Finset.range (p+1), (3 * (Nat.choose (p+k-1) k : ZMod (p^9))^2 + 2 * (Nat.choose (p+k-1) k : ZMod (p^9))^3))
        = ((∑ l ∈ Finset.range (p+1), f (p*l)) - (∑ k ∈ Finset.range (p+1), (3 * (Nat.choose (p+k-1) k : ZMod (p^9))^2 + 2 * (Nat.choose (p+k-1) k : ZMod (p^9))^3))) + Uoff from by ring]
  rw [hdiag]; ring

-- ===== order swap and b-sums =====
theorem sum_range_Icc_swap (p : ℕ) (f : ℕ → R) :
    ∑ b ∈ Finset.range p, ∑ i ∈ Finset.Icc 1 b, f i
      = ∑ i ∈ Finset.Icc 1 (p-1), (f i) * ((p : R) - (i : R)) := by
  have hinner : ∀ b ∈ Finset.range p, ∑ i ∈ Finset.Icc 1 b, f i
      = ∑ i ∈ Finset.range p, (if 1 ≤ i ∧ i ≤ b then f i else 0) := by
    intro b hb
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    simp only [Finset.mem_range] at hb
    ext i; simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]; omega
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
  have houter : ∀ i ∈ Finset.range p,
      ∑ b ∈ Finset.range p, (if 1 ≤ i ∧ i ≤ b then f i else 0)
        = (if 1 ≤ i then (f i) * ((p : R) - (i : R)) else 0) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    by_cases h1 : 1 ≤ i
    · simp only [h1, true_and, if_true]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
      have hcard : ((Finset.range p).filter (fun b => i ≤ b)).card = p - i := by
        rw [show (Finset.range p).filter (fun b => i ≤ b) = Finset.Ico i p from by
              ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega]
        rw [Nat.card_Ico]
      rw [hcard, nsmul_eq_mul, Nat.cast_sub (by omega), mul_comm]
    · simp only [h1, false_and, if_false, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl houter, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega

-- weighted order swap
theorem sum_range_Icc_wswap (p : ℕ) (f g : ℕ → R) :
    ∑ b ∈ Finset.range p, (∑ i ∈ Finset.Icc 1 b, f i) * g b
      = ∑ i ∈ Finset.Icc 1 (p-1), (f i) * (∑ b ∈ Finset.Icc i (p-1), g b) := by
  have hinner : ∀ b ∈ Finset.range p, (∑ i ∈ Finset.Icc 1 b, f i) * g b
      = ∑ i ∈ Finset.range p, (if 1 ≤ i ∧ i ≤ b then f i * g b else 0) := by
    intro b hb
    rw [Finset.sum_mul, ← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    simp only [Finset.mem_range] at hb
    ext i; simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]; omega
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
  have houter : ∀ i ∈ Finset.range p,
      ∑ b ∈ Finset.range p, (if 1 ≤ i ∧ i ≤ b then f i * g b else 0)
        = (if 1 ≤ i then (f i) * (∑ b ∈ Finset.Icc i (p-1), g b) else 0) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    by_cases h1 : 1 ≤ i
    · simp only [h1, true_and, if_true]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.mul_sum]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext b; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
    · simp only [h1, false_and, if_false, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl houter, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega

-- b-sum infrastructure
noncomputable def Hsum (b : ℕ) : ZMod (p^9) := ∑ i ∈ Finset.Icc 1 b, (i : ZMod (p^9))⁻¹
noncomputable def wsum (s : ℕ) : ZMod (p^9) := ∑ i ∈ Finset.Icc 1 (p-1), ((i : ZMod (p^9))⁻¹)^s

theorem unit_inv_mul [Fact p.Prime] {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ p-1) :
    (i : ZMod (p^9))⁻¹ * (i : ZMod (p^9)) = 1 :=
  ZMod.inv_mul_of_unit _ (isUnit_of_lt h1 (by omega))

theorem sum_Hsum [Fact p.Prime] :
    ∑ b ∈ Finset.range p, Hsum b
      = (p:ZMod (p^9)) * wsum 1 - ((p-1 : ℕ) : ZMod (p^9)) := by
  simp only [Hsum]
  rw [sum_range_Icc_swap p (fun i => (i:ZMod (p^9))⁻¹)]
  have key : ∀ i ∈ Finset.Icc 1 (p-1), (i:ZMod (p^9))⁻¹ * ((p:ZMod (p^9)) - (i:ZMod (p^9)))
      = (p:ZMod (p^9)) * ((i:ZMod (p^9))⁻¹)^1 - 1 := by
    intro i hi; simp only [Finset.mem_Icc] at hi
    rw [pow_one, mul_sub, unit_inv_mul hi.1 hi.2]; ring
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [wsum, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  rw [show (p-1)+1-1 = p-1 from by omega]

-- 5-term inverse geometric expansion
theorem inv_geom5 {t : ℕ} [Fact p.Prime] (c : ZMod (p^t)) (d : ℕ)
    (hc : IsUnit c) (hcd : IsUnit (c + p * d)) :
    (p:ZMod (p^t))^5 ∣ ((c + p * d)⁻¹
        - c⁻¹ * (∑ m ∈ Finset.range 5, (-(p:ZMod (p^t)) * d * c⁻¹)^m)) := by
  set ci := c⁻¹ with hci
  have hcci : c * ci = 1 := ZMod.mul_inv_of_unit c hc
  set q := (c + (p:ZMod (p^t)) * d) with hq
  have hqinv : q * q⁻¹ = 1 := ZMod.mul_inv_of_unit q hcd
  set x := -(p:ZMod (p^t)) * d * ci with hx
  set S := ∑ m ∈ Finset.range 5, x^m with hS
  have hqci : q * ci = 1 - x := by rw [hq, hx]; linear_combination hcci
  have hkey : q * (ci * S) = 1 - x^5 := by
    rw [← mul_assoc, hqci, mul_comm (1 - x) S, geom_sum_mul_neg]
  have hfin : q⁻¹ - ci * S = q⁻¹ * x^5 := by
    have h0 : ci * S = q⁻¹ * (q * (ci * S)) := by
      rw [← mul_assoc, mul_comm q⁻¹ q, hqinv, one_mul]
    rw [h0, hkey]; ring
  rw [hfin]
  have hx5 : x^5 = -((p:ZMod (p^t))^5 * d^5 * ci^5) := by rw [hx]; ring
  rw [hx5]
  exact ⟨-(q⁻¹ * (d^5 * ci^5)), by ring⟩

-- product reduction to precision p^5
theorem g_reduce' {X X0 : ZMod (p^9)} (hX : (p:ZMod (p^9))^5 ∣ (X - X0)) :
    3 * ((p:ZMod (p^9))^2 * X)^2 + 2 * ((p:ZMod (p^9))^2 * X)^3
      = 3 * ((p:ZMod (p^9))^2 * X0)^2 + 2 * ((p:ZMod (p^9))^2 * X0)^3 := by
  have hX2 : (p:ZMod (p^9))^5 ∣ (X^2 - X0^2) := dvd_trans hX (sub_dvd_pow_sub_pow X X0 2)
  have hX3 : (p:ZMod (p^9))^5 ∣ (X^3 - X0^3) := dvd_trans hX (sub_dvd_pow_sub_pow X X0 3)
  obtain ⟨u2, hu2⟩ := hX2
  obtain ⟨u3, hu3⟩ := hX3
  have key : (p:ZMod (p^9))^9 ∣
      ((3 * ((p:ZMod (p^9))^2 * X)^2 + 2 * ((p:ZMod (p^9))^2 * X)^3)
       - (3 * ((p:ZMod (p^9))^2 * X0)^2 + 2 * ((p:ZMod (p^9))^2 * X0)^3)) := by
    have e : (3 * ((p:ZMod (p^9))^2 * X)^2 + 2 * ((p:ZMod (p^9))^2 * X)^3)
       - (3 * ((p:ZMod (p^9))^2 * X0)^2 + 2 * ((p:ZMod (p^9))^2 * X0)^3)
        = (p:ZMod (p^9))^4 * (3 * (X^2 - X0^2)) + (p:ZMod (p^9))^6 * (2 * (X^3 - X0^3)) := by ring
    rw [e, hu2, hu3]
    refine dvd_add ⟨3*u2, by ring⟩ ⟨(p:ZMod (p^9))^2*(2*u3), by ring⟩
  have hz : (p:ZMod (p^9))^9 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [hz, zero_dvd_iff] at key
  exact sub_eq_zero.mp key

-- Atr reduction
noncomputable def APP (a b : ℕ) : ZMod (p^9) :=
  (∑ d ∈ Finset.range b, iapprox (p:=p) 9 (p-1) d) + iapprox (p:=p) 9 (a-1) b

noncomputable def Atr0 (a b : ℕ) : ZMod (p^9) :=
  1 + (p:ZMod (p^9))^2 * APP a b
    + (p:ZMod (p^9))^4 * ((2:ZMod (p^9))⁻¹ * ((APP a b)^2 - SA2 (a+p*b)))

theorem Atr_reduce [Fact p.Prime] (a b : ℕ) (ha : 1 ≤ a) (ha2 : a ≤ p) :
    (p:ZMod (p^9))^5 ∣ (Atr (a+p*b) - Atr0 a b) := by
  obtain ⟨w, hw⟩ := alpha_reduction (t:=9) a b ha ha2
  have hsa1 : SA1 (a+p*b) - APP a b = (p:ZMod (p^9))^3 * w := by
    rw [SA1, APP]; exact hw
  refine ⟨w + (p:ZMod (p^9))^2 * (2:ZMod (p^9))⁻¹ * w * (SA1 (a+p*b) + APP a b), ?_⟩
  rw [Atr, Atr0]
  linear_combination ((p:ZMod (p^9))^2
      + (p:ZMod (p^9))^4 * (2:ZMod (p^9))⁻¹ * (SA1 (a+p*b) + APP a b)) * hsa1

-- off-diagonal per-term reduction
noncomputable def K0 (a b : ℕ) : ZMod (p^9) :=
  (a:ZMod (p^9))⁻¹ * (∑ m ∈ Finset.range 5, (-(p:ZMod (p^9)) * b * (a:ZMod (p^9))⁻¹)^m)

theorem uoff_term_reduce [Fact p.Prime] (a b : ℕ) (ha1 : 1 ≤ a) (ha2 : a ≤ p-1) :
    3 * ((p:ZMod (p^9))^2 * ((a+p*b:ℕ):ZMod (p^9))⁻¹ * Atr (a+p*b) * Btr (a+p*b))^2
     + 2 * ((p:ZMod (p^9))^2 * ((a+p*b:ℕ):ZMod (p^9))⁻¹ * Atr (a+p*b) * Btr (a+p*b))^3
      = 3 * ((p:ZMod (p^9))^2 * (K0 a b * Atr0 a b * Btr (a+p*b)))^2
       + 2 * ((p:ZMod (p^9))^2 * (K0 a b * Atr0 a b * Btr (a+p*b)))^3 := by
  have hp1 : 1 ≤ p := (Fact.out (p := p.Prime)).one_le
  set Ki := ((a+p*b:ℕ):ZMod (p^9))⁻¹ with hKi
  set Ak := Atr (a+p*b) with hAk
  set Bk := Btr (a+p*b) with hBk
  have hca : IsUnit (a:ZMod (p^9)) := isUnit_of_lt ha1 (by omega)
  have hknd : ¬ p ∣ (a+p*b) := by
    intro hd
    have h2 : p ∣ p * b := Dvd.intro b rfl
    have := (Nat.dvd_add_right h2).mp (by rwa [Nat.add_comm] at hd)
    have := Nat.le_of_dvd (by omega) this; omega
  have hck : IsUnit ((a:ZMod (p^9)) + p*b) := by
    have he : (a:ZMod (p^9)) + p*b = ((a+p*b:ℕ):ZMod (p^9)) := by push_cast; ring
    rw [he]; exact isUnit_cast_of_not_dvd hknd
  have hk : (p:ZMod (p^9))^5 ∣ (Ki - K0 a b) := by
    have hcast : Ki = ((a:ZMod (p^9)) + p*b)⁻¹ := by rw [hKi]; congr 1; push_cast; ring
    rw [hcast, K0]; exact inv_geom5 (a:ZMod (p^9)) b hca hck
  have hA : (p:ZMod (p^9))^5 ∣ (Ak - Atr0 a b) := Atr_reduce a b ha1 (by omega)
  have hX : (p:ZMod (p^9))^5 ∣ (Ki * Ak * Bk - K0 a b * Atr0 a b * Bk) :=
    dvd_mul_sub _ _ _ Bk Bk (dvd_mul_sub _ _ _ Ak (Atr0 a b) hk hA) (by simp)
  have step := g_reduce' (X := Ki * Ak * Bk) (X0 := K0 a b * Atr0 a b * Bk) hX
  calc 3 * ((p:ZMod (p^9))^2 * Ki * Ak * Bk)^2 + 2 * ((p:ZMod (p^9))^2 * Ki * Ak * Bk)^3
      = 3 * ((p:ZMod (p^9))^2 * (Ki * Ak * Bk))^2 + 2 * ((p:ZMod (p^9))^2 * (Ki * Ak * Bk))^3 := by ring
    _ = 3 * ((p:ZMod (p^9))^2 * (K0 a b * Atr0 a b * Bk))^2 + 2 * ((p:ZMod (p^9))^2 * (K0 a b * Atr0 a b * Bk))^3 := step
    _ = 3 * ((p:ZMod (p^9))^2 * (K0 a b * Atr0 a b * Btr (a+p*b)))^2 + 2 * ((p:ZMod (p^9))^2 * (K0 a b * Atr0 a b * Btr (a+p*b)))^3 := by rw [hBk]

-- mixed-precision reduction
theorem g_reduce2 {X X1 X2 : ZMod (p^9)}
    (h1 : (p:ZMod (p^9))^5 ∣ (X - X1)) (h2 : (p:ZMod (p^9))^3 ∣ (X - X2)) :
    3 * ((p:ZMod (p^9))^2 * X)^2 + 2 * ((p:ZMod (p^9))^2 * X)^3
      = 3 * ((p:ZMod (p^9))^2 * X1)^2 + 2 * ((p:ZMod (p^9))^2 * X2)^3 := by
  have hX2sq : (p:ZMod (p^9))^5 ∣ (X^2 - X1^2) := dvd_trans h1 (sub_dvd_pow_sub_pow X X1 2)
  have hX3cu : (p:ZMod (p^9))^3 ∣ (X^3 - X2^3) := dvd_trans h2 (sub_dvd_pow_sub_pow X X2 3)
  obtain ⟨u2, hu2⟩ := hX2sq
  obtain ⟨u3, hu3⟩ := hX3cu
  have key : (p:ZMod (p^9))^9 ∣
      ((3 * ((p:ZMod (p^9))^2 * X)^2 + 2 * ((p:ZMod (p^9))^2 * X)^3)
       - (3 * ((p:ZMod (p^9))^2 * X1)^2 + 2 * ((p:ZMod (p^9))^2 * X2)^3)) := by
    have e : (3 * ((p:ZMod (p^9))^2 * X)^2 + 2 * ((p:ZMod (p^9))^2 * X)^3)
       - (3 * ((p:ZMod (p^9))^2 * X1)^2 + 2 * ((p:ZMod (p^9))^2 * X2)^3)
        = (p:ZMod (p^9))^4 * (3 * (X^2 - X1^2)) + (p:ZMod (p^9))^6 * (2 * (X^3 - X2^3)) := by ring
    rw [e, hu2, hu3]
    refine dvd_add ⟨3*u2, by ring⟩ ⟨2*u3, by ring⟩
  have hz : (p:ZMod (p^9))^9 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [hz, zero_dvd_iff] at key
  exact sub_eq_zero.mp key

-- per-term final reduction to LOW form
theorem Eb_zero (k : ℕ) : Eb (p:=p) 0 k = 1 := by
  rw [Eb, Finset.powersetCard_zero, Finset.sum_singleton, Finset.prod_empty]

noncomputable def LOWdef (a b : ℕ) : ZMod (p^9) := (APP a b)^2*((a:ZMod (p^9))⁻¹)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4 + (APP a b)*((a:ZMod (p^9))⁻¹)^3*(p:ZMod (p^9))^4*(b:ZMod (p^9))^2 - (APP a b)*((a:ZMod (p^9))⁻¹)^2*(Eb 1 (a+p*b))*(p:ZMod (p^9))^4*(b:ZMod (p^9)) - (APP a b)*((a:ZMod (p^9))⁻¹)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9)) + (APP a b)*((a:ZMod (p^9))⁻¹)*(Eb 1 (a+p*b))*(p:ZMod (p^9))^3 + (APP a b)*((a:ZMod (p^9))⁻¹)*(Eb 2 (a+p*b))*(p:ZMod (p^9))^4 + (APP a b)*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2 + ((a:ZMod (p^9))⁻¹)^5*(p:ZMod (p^9))^4*(b:ZMod (p^9))^4 - ((a:ZMod (p^9))⁻¹)^4*(Eb 1 (a+p*b))*(p:ZMod (p^9))^4*(b:ZMod (p^9))^3 - ((a:ZMod (p^9))⁻¹)^4*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3 + ((a:ZMod (p^9))⁻¹)^3*(Eb 1 (a+p*b))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2 + ((a:ZMod (p^9))⁻¹)^3*(Eb 2 (a+p*b))*(p:ZMod (p^9))^4*(b:ZMod (p^9))^2 + ((a:ZMod (p^9))⁻¹)^3*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2 - ((a:ZMod (p^9))⁻¹)^2*(Eb 1 (a+p*b))*(p:ZMod (p^9))^2*(b:ZMod (p^9)) - ((a:ZMod (p^9))⁻¹)^2*(Eb 2 (a+p*b))*(p:ZMod (p^9))^3*(b:ZMod (p^9)) - ((a:ZMod (p^9))⁻¹)^2*(Eb 3 (a+p*b))*(p:ZMod (p^9))^4*(b:ZMod (p^9)) - ((a:ZMod (p^9))⁻¹)^2*(p:ZMod (p^9))*(b:ZMod (p^9)) + ((a:ZMod (p^9))⁻¹)*(Eb 1 (a+p*b))*(p:ZMod (p^9)) + ((a:ZMod (p^9))⁻¹)*(Eb 2 (a+p*b))*(p:ZMod (p^9))^2 + ((a:ZMod (p^9))⁻¹)*(Eb 3 (a+p*b))*(p:ZMod (p^9))^3 + ((a:ZMod (p^9))⁻¹)*(Eb 4 (a+p*b))*(p:ZMod (p^9))^4 - ((a:ZMod (p^9))⁻¹)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*(SA2 (a+p*b)) + ((a:ZMod (p^9))⁻¹)

noncomputable def LOWlodef (a b : ℕ) : ZMod (p^9) := (APP a b)*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2 + ((a:ZMod (p^9))⁻¹)^3*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2 - ((a:ZMod (p^9))⁻¹)^2*(Eb 1 (a+p*b))*(p:ZMod (p^9))^2*(b:ZMod (p^9)) - ((a:ZMod (p^9))⁻¹)^2*(p:ZMod (p^9))*(b:ZMod (p^9)) + ((a:ZMod (p^9))⁻¹)*(Eb 1 (a+p*b))*(p:ZMod (p^9)) + ((a:ZMod (p^9))⁻¹)*(Eb 2 (a+p*b))*(p:ZMod (p^9))^2 + ((a:ZMod (p^9))⁻¹)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem uoff_term_final [Fact p.Prime] (a b : ℕ) (ha1 : 1 ≤ a) (ha2 : a ≤ p-1) :
    3 * ((p:ZMod (p^9))^2 * ((a+p*b:ℕ):ZMod (p^9))⁻¹ * Atr (a+p*b) * Btr (a+p*b))^2
     + 2 * ((p:ZMod (p^9))^2 * ((a+p*b:ℕ):ZMod (p^9))⁻¹ * Atr (a+p*b) * Btr (a+p*b))^3
      = 3 * ((p:ZMod (p^9))^2 * LOWdef a b)^2 + 2 * ((p:ZMod (p^9))^2 * LOWlodef a b)^3 := by
  rw [uoff_term_reduce a b ha1 ha2]
  have hbtr : Btr (a+p*b) = 1 + (p:ZMod (p^9))*Eb 1 (a+p*b) + (p:ZMod (p^9))^2*Eb 2 (a+p*b)
      + (p:ZMod (p^9))^3*Eb 3 (a+p*b) + (p:ZMod (p^9))^4*Eb 4 (a+p*b) := by
    simp only [Btr]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_one, Eb_zero]; ring
  have hk0 : K0 a b = (a:ZMod (p^9))⁻¹ * (1 + (-(p:ZMod (p^9))*(b:ZMod (p^9))*(a:ZMod (p^9))⁻¹)
      + (-(p:ZMod (p^9))*(b:ZMod (p^9))*(a:ZMod (p^9))⁻¹)^2 + (-(p:ZMod (p^9))*(b:ZMod (p^9))*(a:ZMod (p^9))⁻¹)^3
      + (-(p:ZMod (p^9))*(b:ZMod (p^9))*(a:ZMod (p^9))⁻¹)^4) := by
    simp only [K0]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_one]; ring
  apply g_reduce2 (X := K0 a b * Atr0 a b * Btr (a+p*b)) (X1 := LOWdef a b) (X2 := LOWlodef a b)
  · rw [hk0, hbtr]; simp only [Atr0, LOWdef]
    exact ⟨(APP a b)^2*((a:ZMod (p^9))⁻¹)^5*(Eb 1 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*(b:ZMod (p^9))^4 + (APP a b)^2*((a:ZMod (p^9))⁻¹)^5*(Eb 2 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^5*(b:ZMod (p^9))^4 + (APP a b)^2*((a:ZMod (p^9))⁻¹)^5*(Eb 3 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^6*(b:ZMod (p^9))^4 + (APP a b)^2*((a:ZMod (p^9))⁻¹)^5*(Eb 4 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^7*(b:ZMod (p^9))^4 + (APP a b)^2*((a:ZMod (p^9))⁻¹)^5*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4 - (APP a b)^2*((a:ZMod (p^9))⁻¹)^4*(Eb 1 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3 - (APP a b)^2*((a:ZMod (p^9))⁻¹)^4*(Eb 2 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*(b:ZMod (p^9))^3 - (APP a b)^2*((a:ZMod (p^9))⁻¹)^4*(Eb 3 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^5*(b:ZMod (p^9))^3 - (APP a b)^2*((a:ZMod (p^9))⁻¹)^4*(Eb 4 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^6*(b:ZMod (p^9))^3 - (APP a b)^2*((a:ZMod (p^9))⁻¹)^4*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3 + (APP a b)^2*((a:ZMod (p^9))⁻¹)^3*(Eb 1 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2 + (APP a b)^2*((a:ZMod (p^9))⁻¹)^3*(Eb 2 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2 + (APP a b)^2*((a:ZMod (p^9))⁻¹)^3*(Eb 3 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*(b:ZMod (p^9))^2 + (APP a b)^2*((a:ZMod (p^9))⁻¹)^3*(Eb 4 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^5*(b:ZMod (p^9))^2 + (APP a b)^2*((a:ZMod (p^9))⁻¹)^3*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(b:ZMod (p^9))^2 - (APP a b)^2*((a:ZMod (p^9))⁻¹)^2*(Eb 1 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(b:ZMod (p^9)) - (APP a b)^2*((a:ZMod (p^9))⁻¹)^2*(Eb 2 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2*(b:ZMod (p^9)) - (APP a b)^2*((a:ZMod (p^9))⁻¹)^2*(Eb 3 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(b:ZMod (p^9)) - (APP a b)^2*((a:ZMod (p^9))⁻¹)^2*(Eb 4 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*(b:ZMod (p^9)) - (APP a b)^2*((a:ZMod (p^9))⁻¹)^2*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9)) + (APP a b)^2*((a:ZMod (p^9))⁻¹)*(Eb 1 (a+p*b))*((2:ZMod (p^9))⁻¹) + (APP a b)^2*((a:ZMod (p^9))⁻¹)*(Eb 2 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9)) + (APP a b)^2*((a:ZMod (p^9))⁻¹)*(Eb 3 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2 + (APP a b)^2*((a:ZMod (p^9))⁻¹)*(Eb 4 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3 + (APP a b)*((a:ZMod (p^9))⁻¹)^5*(Eb 1 (a+p*b))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^4 + (APP a b)*((a:ZMod (p^9))⁻¹)^5*(Eb 2 (a+p*b))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4 + (APP a b)*((a:ZMod (p^9))⁻¹)^5*(Eb 3 (a+p*b))*(p:ZMod (p^9))^4*(b:ZMod (p^9))^4 + (APP a b)*((a:ZMod (p^9))⁻¹)^5*(Eb 4 (a+p*b))*(p:ZMod (p^9))^5*(b:ZMod (p^9))^4 + (APP a b)*((a:ZMod (p^9))⁻¹)^5*(p:ZMod (p^9))*(b:ZMod (p^9))^4 - (APP a b)*((a:ZMod (p^9))⁻¹)^4*(Eb 1 (a+p*b))*(p:ZMod (p^9))*(b:ZMod (p^9))^3 - (APP a b)*((a:ZMod (p^9))⁻¹)^4*(Eb 2 (a+p*b))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3 - (APP a b)*((a:ZMod (p^9))⁻¹)^4*(Eb 3 (a+p*b))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3 - (APP a b)*((a:ZMod (p^9))⁻¹)^4*(Eb 4 (a+p*b))*(p:ZMod (p^9))^4*(b:ZMod (p^9))^3 - (APP a b)*((a:ZMod (p^9))⁻¹)^4*(b:ZMod (p^9))^3 + (APP a b)*((a:ZMod (p^9))⁻¹)^3*(Eb 1 (a+p*b))*(b:ZMod (p^9))^2 + (APP a b)*((a:ZMod (p^9))⁻¹)^3*(Eb 2 (a+p*b))*(p:ZMod (p^9))*(b:ZMod (p^9))^2 + (APP a b)*((a:ZMod (p^9))⁻¹)^3*(Eb 3 (a+p*b))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2 + (APP a b)*((a:ZMod (p^9))⁻¹)^3*(Eb 4 (a+p*b))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2 - (APP a b)*((a:ZMod (p^9))⁻¹)^2*(Eb 2 (a+p*b))*(b:ZMod (p^9)) - (APP a b)*((a:ZMod (p^9))⁻¹)^2*(Eb 3 (a+p*b))*(p:ZMod (p^9))*(b:ZMod (p^9)) - (APP a b)*((a:ZMod (p^9))⁻¹)^2*(Eb 4 (a+p*b))*(p:ZMod (p^9))^2*(b:ZMod (p^9)) + (APP a b)*((a:ZMod (p^9))⁻¹)*(Eb 3 (a+p*b)) + (APP a b)*((a:ZMod (p^9))⁻¹)*(Eb 4 (a+p*b))*(p:ZMod (p^9)) - ((a:ZMod (p^9))⁻¹)^5*(Eb 1 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*(SA2 (a+p*b))*(b:ZMod (p^9))^4 + ((a:ZMod (p^9))⁻¹)^5*(Eb 1 (a+p*b))*(b:ZMod (p^9))^4 - ((a:ZMod (p^9))⁻¹)^5*(Eb 2 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^5*(SA2 (a+p*b))*(b:ZMod (p^9))^4 + ((a:ZMod (p^9))⁻¹)^5*(Eb 2 (a+p*b))*(p:ZMod (p^9))*(b:ZMod (p^9))^4 - ((a:ZMod (p^9))⁻¹)^5*(Eb 3 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^6*(SA2 (a+p*b))*(b:ZMod (p^9))^4 + ((a:ZMod (p^9))⁻¹)^5*(Eb 3 (a+p*b))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^4 - ((a:ZMod (p^9))⁻¹)^5*(Eb 4 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^7*(SA2 (a+p*b))*(b:ZMod (p^9))^4 + ((a:ZMod (p^9))⁻¹)^5*(Eb 4 (a+p*b))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4 - ((a:ZMod (p^9))⁻¹)^5*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(SA2 (a+p*b))*(b:ZMod (p^9))^4 + ((a:ZMod (p^9))⁻¹)^4*(Eb 1 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(SA2 (a+p*b))*(b:ZMod (p^9))^3 + ((a:ZMod (p^9))⁻¹)^4*(Eb 2 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*(SA2 (a+p*b))*(b:ZMod (p^9))^3 - ((a:ZMod (p^9))⁻¹)^4*(Eb 2 (a+p*b))*(b:ZMod (p^9))^3 + ((a:ZMod (p^9))⁻¹)^4*(Eb 3 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^5*(SA2 (a+p*b))*(b:ZMod (p^9))^3 - ((a:ZMod (p^9))⁻¹)^4*(Eb 3 (a+p*b))*(p:ZMod (p^9))*(b:ZMod (p^9))^3 + ((a:ZMod (p^9))⁻¹)^4*(Eb 4 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^6*(SA2 (a+p*b))*(b:ZMod (p^9))^3 - ((a:ZMod (p^9))⁻¹)^4*(Eb 4 (a+p*b))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3 + ((a:ZMod (p^9))⁻¹)^4*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2*(SA2 (a+p*b))*(b:ZMod (p^9))^3 - ((a:ZMod (p^9))⁻¹)^3*(Eb 1 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2*(SA2 (a+p*b))*(b:ZMod (p^9))^2 - ((a:ZMod (p^9))⁻¹)^3*(Eb 2 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(SA2 (a+p*b))*(b:ZMod (p^9))^2 - ((a:ZMod (p^9))⁻¹)^3*(Eb 3 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*(SA2 (a+p*b))*(b:ZMod (p^9))^2 + ((a:ZMod (p^9))⁻¹)^3*(Eb 3 (a+p*b))*(b:ZMod (p^9))^2 - ((a:ZMod (p^9))⁻¹)^3*(Eb 4 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^5*(SA2 (a+p*b))*(b:ZMod (p^9))^2 + ((a:ZMod (p^9))⁻¹)^3*(Eb 4 (a+p*b))*(p:ZMod (p^9))*(b:ZMod (p^9))^2 - ((a:ZMod (p^9))⁻¹)^3*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(SA2 (a+p*b))*(b:ZMod (p^9))^2 + ((a:ZMod (p^9))⁻¹)^2*(Eb 1 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(SA2 (a+p*b))*(b:ZMod (p^9)) + ((a:ZMod (p^9))⁻¹)^2*(Eb 2 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2*(SA2 (a+p*b))*(b:ZMod (p^9)) + ((a:ZMod (p^9))⁻¹)^2*(Eb 3 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(SA2 (a+p*b))*(b:ZMod (p^9)) + ((a:ZMod (p^9))⁻¹)^2*(Eb 4 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*(SA2 (a+p*b))*(b:ZMod (p^9)) - ((a:ZMod (p^9))⁻¹)^2*(Eb 4 (a+p*b))*(b:ZMod (p^9)) + ((a:ZMod (p^9))⁻¹)^2*((2:ZMod (p^9))⁻¹)*(SA2 (a+p*b))*(b:ZMod (p^9)) - ((a:ZMod (p^9))⁻¹)*(Eb 1 (a+p*b))*((2:ZMod (p^9))⁻¹)*(SA2 (a+p*b)) - ((a:ZMod (p^9))⁻¹)*(Eb 2 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(SA2 (a+p*b)) - ((a:ZMod (p^9))⁻¹)*(Eb 3 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2*(SA2 (a+p*b)) - ((a:ZMod (p^9))⁻¹)*(Eb 4 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(SA2 (a+p*b)), by ring⟩
  · rw [hk0, hbtr]; simp only [Atr0, LOWlodef]
    exact ⟨(APP a b)^2*((a:ZMod (p^9))⁻¹)^5*(Eb 1 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^6*(b:ZMod (p^9))^4 + (APP a b)^2*((a:ZMod (p^9))⁻¹)^5*(Eb 2 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^7*(b:ZMod (p^9))^4 + (APP a b)^2*((a:ZMod (p^9))⁻¹)^5*(Eb 3 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^8*(b:ZMod (p^9))^4 + (APP a b)^2*((a:ZMod (p^9))⁻¹)^5*(Eb 4 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^9*(b:ZMod (p^9))^4 + (APP a b)^2*((a:ZMod (p^9))⁻¹)^5*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^5*(b:ZMod (p^9))^4 - (APP a b)^2*((a:ZMod (p^9))⁻¹)^4*(Eb 1 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^5*(b:ZMod (p^9))^3 - (APP a b)^2*((a:ZMod (p^9))⁻¹)^4*(Eb 2 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^6*(b:ZMod (p^9))^3 - (APP a b)^2*((a:ZMod (p^9))⁻¹)^4*(Eb 3 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^7*(b:ZMod (p^9))^3 - (APP a b)^2*((a:ZMod (p^9))⁻¹)^4*(Eb 4 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^8*(b:ZMod (p^9))^3 - (APP a b)^2*((a:ZMod (p^9))⁻¹)^4*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*(b:ZMod (p^9))^3 + (APP a b)^2*((a:ZMod (p^9))⁻¹)^3*(Eb 1 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*(b:ZMod (p^9))^2 + (APP a b)^2*((a:ZMod (p^9))⁻¹)^3*(Eb 2 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^5*(b:ZMod (p^9))^2 + (APP a b)^2*((a:ZMod (p^9))⁻¹)^3*(Eb 3 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^6*(b:ZMod (p^9))^2 + (APP a b)^2*((a:ZMod (p^9))⁻¹)^3*(Eb 4 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^7*(b:ZMod (p^9))^2 + (APP a b)^2*((a:ZMod (p^9))⁻¹)^3*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2 - (APP a b)^2*((a:ZMod (p^9))⁻¹)^2*(Eb 1 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(b:ZMod (p^9)) - (APP a b)^2*((a:ZMod (p^9))⁻¹)^2*(Eb 2 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*(b:ZMod (p^9)) - (APP a b)^2*((a:ZMod (p^9))⁻¹)^2*(Eb 3 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^5*(b:ZMod (p^9)) - (APP a b)^2*((a:ZMod (p^9))⁻¹)^2*(Eb 4 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^6*(b:ZMod (p^9)) - (APP a b)^2*((a:ZMod (p^9))⁻¹)^2*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2*(b:ZMod (p^9)) + (APP a b)^2*((a:ZMod (p^9))⁻¹)*(Eb 1 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2 + (APP a b)^2*((a:ZMod (p^9))⁻¹)*(Eb 2 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3 + (APP a b)^2*((a:ZMod (p^9))⁻¹)*(Eb 3 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4 + (APP a b)^2*((a:ZMod (p^9))⁻¹)*(Eb 4 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^5 + (APP a b)^2*((a:ZMod (p^9))⁻¹)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9)) + (APP a b)*((a:ZMod (p^9))⁻¹)^5*(Eb 1 (a+p*b))*(p:ZMod (p^9))^4*(b:ZMod (p^9))^4 + (APP a b)*((a:ZMod (p^9))⁻¹)^5*(Eb 2 (a+p*b))*(p:ZMod (p^9))^5*(b:ZMod (p^9))^4 + (APP a b)*((a:ZMod (p^9))⁻¹)^5*(Eb 3 (a+p*b))*(p:ZMod (p^9))^6*(b:ZMod (p^9))^4 + (APP a b)*((a:ZMod (p^9))⁻¹)^5*(Eb 4 (a+p*b))*(p:ZMod (p^9))^7*(b:ZMod (p^9))^4 + (APP a b)*((a:ZMod (p^9))⁻¹)^5*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4 - (APP a b)*((a:ZMod (p^9))⁻¹)^4*(Eb 1 (a+p*b))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3 - (APP a b)*((a:ZMod (p^9))⁻¹)^4*(Eb 2 (a+p*b))*(p:ZMod (p^9))^4*(b:ZMod (p^9))^3 - (APP a b)*((a:ZMod (p^9))⁻¹)^4*(Eb 3 (a+p*b))*(p:ZMod (p^9))^5*(b:ZMod (p^9))^3 - (APP a b)*((a:ZMod (p^9))⁻¹)^4*(Eb 4 (a+p*b))*(p:ZMod (p^9))^6*(b:ZMod (p^9))^3 - (APP a b)*((a:ZMod (p^9))⁻¹)^4*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3 + (APP a b)*((a:ZMod (p^9))⁻¹)^3*(Eb 1 (a+p*b))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2 + (APP a b)*((a:ZMod (p^9))⁻¹)^3*(Eb 2 (a+p*b))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2 + (APP a b)*((a:ZMod (p^9))⁻¹)^3*(Eb 3 (a+p*b))*(p:ZMod (p^9))^4*(b:ZMod (p^9))^2 + (APP a b)*((a:ZMod (p^9))⁻¹)^3*(Eb 4 (a+p*b))*(p:ZMod (p^9))^5*(b:ZMod (p^9))^2 + (APP a b)*((a:ZMod (p^9))⁻¹)^3*(p:ZMod (p^9))*(b:ZMod (p^9))^2 - (APP a b)*((a:ZMod (p^9))⁻¹)^2*(Eb 1 (a+p*b))*(p:ZMod (p^9))*(b:ZMod (p^9)) - (APP a b)*((a:ZMod (p^9))⁻¹)^2*(Eb 2 (a+p*b))*(p:ZMod (p^9))^2*(b:ZMod (p^9)) - (APP a b)*((a:ZMod (p^9))⁻¹)^2*(Eb 3 (a+p*b))*(p:ZMod (p^9))^3*(b:ZMod (p^9)) - (APP a b)*((a:ZMod (p^9))⁻¹)^2*(Eb 4 (a+p*b))*(p:ZMod (p^9))^4*(b:ZMod (p^9)) - (APP a b)*((a:ZMod (p^9))⁻¹)^2*(b:ZMod (p^9)) + (APP a b)*((a:ZMod (p^9))⁻¹)*(Eb 1 (a+p*b)) + (APP a b)*((a:ZMod (p^9))⁻¹)*(Eb 2 (a+p*b))*(p:ZMod (p^9)) + (APP a b)*((a:ZMod (p^9))⁻¹)*(Eb 3 (a+p*b))*(p:ZMod (p^9))^2 + (APP a b)*((a:ZMod (p^9))⁻¹)*(Eb 4 (a+p*b))*(p:ZMod (p^9))^3 - ((a:ZMod (p^9))⁻¹)^5*(Eb 1 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^6*(SA2 (a+p*b))*(b:ZMod (p^9))^4 + ((a:ZMod (p^9))⁻¹)^5*(Eb 1 (a+p*b))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^4 - ((a:ZMod (p^9))⁻¹)^5*(Eb 2 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^7*(SA2 (a+p*b))*(b:ZMod (p^9))^4 + ((a:ZMod (p^9))⁻¹)^5*(Eb 2 (a+p*b))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4 - ((a:ZMod (p^9))⁻¹)^5*(Eb 3 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^8*(SA2 (a+p*b))*(b:ZMod (p^9))^4 + ((a:ZMod (p^9))⁻¹)^5*(Eb 3 (a+p*b))*(p:ZMod (p^9))^4*(b:ZMod (p^9))^4 - ((a:ZMod (p^9))⁻¹)^5*(Eb 4 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^9*(SA2 (a+p*b))*(b:ZMod (p^9))^4 + ((a:ZMod (p^9))⁻¹)^5*(Eb 4 (a+p*b))*(p:ZMod (p^9))^5*(b:ZMod (p^9))^4 - ((a:ZMod (p^9))⁻¹)^5*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^5*(SA2 (a+p*b))*(b:ZMod (p^9))^4 + ((a:ZMod (p^9))⁻¹)^5*(p:ZMod (p^9))*(b:ZMod (p^9))^4 + ((a:ZMod (p^9))⁻¹)^4*(Eb 1 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^5*(SA2 (a+p*b))*(b:ZMod (p^9))^3 - ((a:ZMod (p^9))⁻¹)^4*(Eb 1 (a+p*b))*(p:ZMod (p^9))*(b:ZMod (p^9))^3 + ((a:ZMod (p^9))⁻¹)^4*(Eb 2 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^6*(SA2 (a+p*b))*(b:ZMod (p^9))^3 - ((a:ZMod (p^9))⁻¹)^4*(Eb 2 (a+p*b))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3 + ((a:ZMod (p^9))⁻¹)^4*(Eb 3 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^7*(SA2 (a+p*b))*(b:ZMod (p^9))^3 - ((a:ZMod (p^9))⁻¹)^4*(Eb 3 (a+p*b))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3 + ((a:ZMod (p^9))⁻¹)^4*(Eb 4 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^8*(SA2 (a+p*b))*(b:ZMod (p^9))^3 - ((a:ZMod (p^9))⁻¹)^4*(Eb 4 (a+p*b))*(p:ZMod (p^9))^4*(b:ZMod (p^9))^3 + ((a:ZMod (p^9))⁻¹)^4*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*(SA2 (a+p*b))*(b:ZMod (p^9))^3 - ((a:ZMod (p^9))⁻¹)^4*(b:ZMod (p^9))^3 - ((a:ZMod (p^9))⁻¹)^3*(Eb 1 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*(SA2 (a+p*b))*(b:ZMod (p^9))^2 + ((a:ZMod (p^9))⁻¹)^3*(Eb 1 (a+p*b))*(b:ZMod (p^9))^2 - ((a:ZMod (p^9))⁻¹)^3*(Eb 2 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^5*(SA2 (a+p*b))*(b:ZMod (p^9))^2 + ((a:ZMod (p^9))⁻¹)^3*(Eb 2 (a+p*b))*(p:ZMod (p^9))*(b:ZMod (p^9))^2 - ((a:ZMod (p^9))⁻¹)^3*(Eb 3 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^6*(SA2 (a+p*b))*(b:ZMod (p^9))^2 + ((a:ZMod (p^9))⁻¹)^3*(Eb 3 (a+p*b))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2 - ((a:ZMod (p^9))⁻¹)^3*(Eb 4 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^7*(SA2 (a+p*b))*(b:ZMod (p^9))^2 + ((a:ZMod (p^9))⁻¹)^3*(Eb 4 (a+p*b))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2 - ((a:ZMod (p^9))⁻¹)^3*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(SA2 (a+p*b))*(b:ZMod (p^9))^2 + ((a:ZMod (p^9))⁻¹)^2*(Eb 1 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(SA2 (a+p*b))*(b:ZMod (p^9)) + ((a:ZMod (p^9))⁻¹)^2*(Eb 2 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*(SA2 (a+p*b))*(b:ZMod (p^9)) - ((a:ZMod (p^9))⁻¹)^2*(Eb 2 (a+p*b))*(b:ZMod (p^9)) + ((a:ZMod (p^9))⁻¹)^2*(Eb 3 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^5*(SA2 (a+p*b))*(b:ZMod (p^9)) - ((a:ZMod (p^9))⁻¹)^2*(Eb 3 (a+p*b))*(p:ZMod (p^9))*(b:ZMod (p^9)) + ((a:ZMod (p^9))⁻¹)^2*(Eb 4 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^6*(SA2 (a+p*b))*(b:ZMod (p^9)) - ((a:ZMod (p^9))⁻¹)^2*(Eb 4 (a+p*b))*(p:ZMod (p^9))^2*(b:ZMod (p^9)) + ((a:ZMod (p^9))⁻¹)^2*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2*(SA2 (a+p*b))*(b:ZMod (p^9)) - ((a:ZMod (p^9))⁻¹)*(Eb 1 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2*(SA2 (a+p*b)) - ((a:ZMod (p^9))⁻¹)*(Eb 2 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(SA2 (a+p*b)) - ((a:ZMod (p^9))⁻¹)*(Eb 3 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*(SA2 (a+p*b)) + ((a:ZMod (p^9))⁻¹)*(Eb 3 (a+p*b)) - ((a:ZMod (p^9))⁻¹)*(Eb 4 (a+p*b))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^5*(SA2 (a+p*b)) + ((a:ZMod (p^9))⁻¹)*(Eb 4 (a+p*b))*(p:ZMod (p^9)) - ((a:ZMod (p^9))⁻¹)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(SA2 (a+p*b)), by ring⟩

-- HAsum and APP reduction
noncomputable def HAsum (s m : ℕ) : ZMod (p^9) := ∑ c ∈ Finset.Icc 1 m, ((c:ZMod (p^9))⁻¹)^s

theorem iapprox_eq (m d : ℕ) :
    iapprox (p:=p) 9 m d
      = HAsum 1 m - (p:ZMod (p^9))*(d:ZMod (p^9))*HAsum 2 m
        + (p:ZMod (p^9))^2*(d:ZMod (p^9))^2*HAsum 3 m := by
  simp only [iapprox, HAsum, pow_one]

theorem APP_reduce (a b : ℕ) :
    APP a b = (b:ZMod (p^9)) * HAsum 1 (p-1)
        - (p:ZMod (p^9)) * (∑ d ∈ Finset.range b, (d:ZMod (p^9))) * HAsum 2 (p-1)
        + (p:ZMod (p^9))^2 * (∑ d ∈ Finset.range b, (d:ZMod (p^9))^2) * HAsum 3 (p-1)
        + HAsum 1 (a-1) - (p:ZMod (p^9))*(b:ZMod (p^9))*HAsum 2 (a-1)
        + (p:ZMod (p^9))^2*(b:ZMod (p^9))^2*HAsum 3 (a-1) := by
  have e1 : ∀ d:ℕ, (p:ZMod (p^9))*(d:ZMod (p^9))*HAsum 2 (p-1)
      = ((p:ZMod (p^9))*HAsum 2 (p-1))*(d:ZMod (p^9)) := fun d => by ring
  have e2 : ∀ d:ℕ, (p:ZMod (p^9))^2*(d:ZMod (p^9))^2*HAsum 3 (p-1)
      = ((p:ZMod (p^9))^2*HAsum 3 (p-1))*((d:ZMod (p^9))^2) := fun d => by ring
  simp only [APP, iapprox_eq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, e1, e2]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

-- SA2 mod-p reduction
theorem inv_dvd_p_sub [Fact p.Prime] (c : ZMod (p^9)) (d : ℕ) (hc : IsUnit c)
    (hcd : IsUnit (c + (p:ZMod (p^9))*(d:ZMod (p^9)))) :
    (p:ZMod (p^9)) ∣ ((c + (p:ZMod (p^9))*(d:ZMod (p^9)))⁻¹ - c⁻¹) := by
  obtain ⟨w, hw⟩ := inv_geom_term (t:=9) c d hc hcd
  refine ⟨-(d:ZMod (p^9))*(c⁻¹)^2 + (p:ZMod (p^9))*(d:ZMod (p^9))^2*(c⁻¹)^3 + (p:ZMod (p^9))^2*w, ?_⟩
  linear_combination hw

theorem inv_sq_dvd_p_sub [Fact p.Prime] (c : ZMod (p^9)) (d : ℕ) (hc : IsUnit c)
    (hcd : IsUnit (c + (p:ZMod (p^9))*(d:ZMod (p^9)))) :
    (p:ZMod (p^9)) ∣ (((c + (p:ZMod (p^9))*(d:ZMod (p^9)))⁻¹)^2 - (c⁻¹)^2) := by
  have h := inv_dvd_p_sub c d hc hcd
  have e : ((c + (p:ZMod (p^9))*(d:ZMod (p^9)))⁻¹)^2 - (c⁻¹)^2
      = ((c + (p:ZMod (p^9))*(d:ZMod (p^9)))⁻¹ - c⁻¹) * ((c + (p:ZMod (p^9))*(d:ZMod (p^9)))⁻¹ + c⁻¹) := by ring
  rw [e]; exact h.mul_right _

theorem SA2_reduce [Fact p.Prime] (hp5 : 5 ≤ p) (a b : ℕ) (ha : 1 ≤ a) (ha2 : a ≤ p - 1) :
    (p:ZMod (p^9)) ∣ (SA2 (a+p*b) - HAsum 2 (a-1)) := by
  have hp1 : 1 ≤ p := by omega
  -- unit helper for c + p*d with 1 ≤ c ≤ p-1
  have hunit : ∀ (c d : ℕ), 1 ≤ c → c ≤ p-1 →
      IsUnit ((c:ZMod (p^9)) + (p:ZMod (p^9))*(d:ZMod (p^9))) := by
    intro c d hc1 hc2
    have he : (c:ZMod (p^9)) + (p:ZMod (p^9))*(d:ZMod (p^9)) = ((c+p*d:ℕ):ZMod (p^9)) := by
      push_cast; ring
    rw [he]
    apply isUnit_cast_of_not_dvd
    intro hdvd
    rw [Nat.add_comm] at hdvd
    have hc : p ∣ c := (Nat.dvd_add_right (dvd_mul_right p d)).mp hdvd
    have := Nat.le_of_dvd hc1 hc; omega
  have hconv2 : ∀ (c d : ℕ), (((c+p*d:ℕ):ZMod (p^9))⁻¹)^2
      = (((c:ZMod (p^9)) + (p:ZMod (p^9))*(d:ZMod (p^9)))⁻¹)^2 := by
    intro c d; congr 2; push_cast; ring
  simp only [SA2]
  rw [box_split p a b hp1 ha (by omega) (fun i => ((i:ZMod (p^9))⁻¹)^2)]
  simp only [hconv2]
  -- HAsum 2 (a-1) unfold
  have hHA : HAsum 2 (a-1) = ∑ c ∈ Finset.Icc 1 (a-1), ((c:ZMod (p^9))⁻¹)^2 := by
    simp only [HAsum]
  rw [hHA]
  have hrw : (∑ d ∈ Finset.range b, ∑ c ∈ Finset.Icc 1 (p-1),
        (((c:ZMod (p^9)) + (p:ZMod (p^9))*(d:ZMod (p^9)))⁻¹)^2)
      + (∑ c ∈ Finset.Icc 1 (a-1), (((c:ZMod (p^9)) + (p:ZMod (p^9))*(b:ZMod (p^9)))⁻¹)^2)
      - (∑ c ∈ Finset.Icc 1 (a-1), ((c:ZMod (p^9))⁻¹)^2)
    = (∑ d ∈ Finset.range b, ∑ c ∈ Finset.Icc 1 (p-1),
        (((c:ZMod (p^9)) + (p:ZMod (p^9))*(d:ZMod (p^9)))⁻¹)^2)
      + (∑ c ∈ Finset.Icc 1 (a-1),
          ((((c:ZMod (p^9)) + (p:ZMod (p^9))*(b:ZMod (p^9)))⁻¹)^2 - ((c:ZMod (p^9))⁻¹)^2)) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hrw]
  apply dvd_add
  · apply Finset.dvd_sum
    intro d _
    -- inner: p ∣ ∑_c (((c)+pd)⁻¹)^2
    have hsplit : ∑ c ∈ Finset.Icc 1 (p-1), (((c:ZMod (p^9)) + (p:ZMod (p^9))*(d:ZMod (p^9)))⁻¹)^2
        = (∑ c ∈ Finset.Icc 1 (p-1),
            ((((c:ZMod (p^9)) + (p:ZMod (p^9))*(d:ZMod (p^9)))⁻¹)^2 - ((c:ZMod (p^9))⁻¹)^2))
          + (∑ c ∈ Finset.Icc 1 (p-1), ((c:ZMod (p^9))⁻¹)^2) := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro c _; ring
    rw [hsplit]
    apply dvd_add
    · apply Finset.dvd_sum
      intro c hc
      rw [Finset.mem_Icc] at hc
      exact inv_sq_dvd_p_sub (c:ZMod (p^9)) d (isUnit_of_lt hc.1 hc.2) (hunit c d hc.1 hc.2)
    · exact sum_inv_pow_dvd_p (by norm_num) (by norm_num) (by omega)
  · apply Finset.dvd_sum
    intro c hc
    rw [Finset.mem_Icc] at hc
    exact inv_sq_dvd_p_sub (c:ZMod (p^9)) b (isUnit_of_lt hc.1 (by omega)) (hunit c b hc.1 (by omega))

-- Eb depends only on b
noncomputable def EBb (j b : ℕ) : ZMod (p^9) :=
  ∑ T ∈ (Finset.Icc 1 b).powersetCard j, ∏ l ∈ T, (l:ZMod (p^9))⁻¹

theorem Eb_idx (a b : ℕ) (ha : 1 ≤ a) (ha2 : a ≤ p) : (a + p*b - 1)/p = b := by
  have hp1 : 1 ≤ p := by omega
  have he : a + p*b - 1 = (a-1) + b*p := by
    rw [Nat.mul_comm]; omega
  rw [he, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add]

theorem Eb_eq_EBb (j a b : ℕ) (ha : 1 ≤ a) (ha2 : a ≤ p) :
    Eb (p:=p) j (a + p*b) = EBb j b := by
  simp only [Eb, EBb, Eb_idx a b ha ha2]

-- Bpow, EBb Newton relations, sq_reduce5
noncomputable def Bpow (s b : ℕ) : ZMod (p^9) := ∑ l ∈ Finset.Icc 1 b, ((l:ZMod (p^9))⁻¹)^s

theorem EBb1 (b : ℕ) : EBb (p:=p) 1 b = Bpow 1 b := by
  simp only [EBb, Bpow, pow_one]
  exact esym_one_eq (fun l => (l:ZMod (p^9))⁻¹) (Finset.Icc 1 b)

theorem EBb2 (b : ℕ) : 2 * EBb (p:=p) 2 b = (Bpow 1 b)^2 - Bpow 2 b := by
  simp only [EBb, Bpow, pow_one]
  exact newton2 (fun l => (l:ZMod (p^9))⁻¹) (Finset.Icc 1 b)

theorem EBb3 (b : ℕ) :
    6 * EBb (p:=p) 3 b = (Bpow 1 b)^3 - 3*(Bpow 1 b)*(Bpow 2 b) + 2*(Bpow 3 b) := by
  simp only [EBb, Bpow, pow_one]
  exact newton3 (fun l => (l:ZMod (p^9))⁻¹) (Finset.Icc 1 b)

theorem EBb4 (b : ℕ) :
    24 * EBb (p:=p) 4 b = (Bpow 1 b)^4 - 6*(Bpow 1 b)^2*(Bpow 2 b) + 3*(Bpow 2 b)^2
      + 8*(Bpow 1 b)*(Bpow 3 b) - 6*(Bpow 4 b) := by
  simp only [EBb, Bpow, pow_one]
  exact newton4 (fun l => (l:ZMod (p^9))⁻¹) (Finset.Icc 1 b)

theorem sq_reduce5 {A B : ZMod (p^9)} (h : (p:ZMod (p^9))^5 ∣ (A - B)) :
    3 * ((p:ZMod (p^9))^2 * A)^2 = 3 * ((p:ZMod (p^9))^2 * B)^2 := by
  obtain ⟨w, hw⟩ := h
  have hp9 : (p:ZMod (p^9))^9 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have : A = B + (p:ZMod (p^9))^5 * w := by linear_combination hw
  rw [this]
  linear_combination (3*w*(2*B+(p:ZMod (p^9))^5*w)) * hp9

-- ===== Off-diagonal separation =====
theorem cube_reduce3 {A B : ZMod (p^9)} (h : (p:ZMod (p^9))^3 ∣ (A - B)) :
    2 * ((p:ZMod (p^9))^2 * A)^3 = 2 * ((p:ZMod (p^9))^2 * B)^3 := by
  obtain ⟨w, hw⟩ := h
  have hp9 : (p:ZMod (p^9))^9 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hAB : A = B + (p:ZMod (p^9))^3 * w := by linear_combination hw
  rw [hAB]
  linear_combination (2*w*(3*B^2+3*B*(p:ZMod (p^9))^3*w+(p:ZMod (p^9))^6*w^2)) * hp9

set_option maxHeartbeats 4000000 in
noncomputable def LOWdefS (a b : ℕ) : ZMod (p^9) :=
  (-1:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(b:ZMod (p^9))*(HAsum 3 (p-1))*(p:ZMod (p^9))^6*((a:ZMod (p^9))⁻¹)^2 + (-1:ZMod (p^9))*(EBb 1 b)*(HAsum 3 (a-1))*(p:ZMod (p^9))^6*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (1:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 2 (p-1))*(p:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^2 + (1:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*((a:ZMod (p^9))⁻¹)*(HAsum 3 (p-1))*(p:ZMod (p^9))^5 + (1:ZMod (p^9))*(EBb 1 b)*(HAsum 2 (a-1))*(p:ZMod (p^9))^5*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (1:ZMod (p^9))*(EBb 1 b)*(HAsum 3 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^5*(b:ZMod (p^9))^2 + (-1:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*((a:ZMod (p^9))⁻¹)*(HAsum 2 (p-1))*(p:ZMod (p^9))^4 + (-1:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))^4*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (-1:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (p-1))*(p:ZMod (p^9))^4*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-1:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(p:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^2 + (-1:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4 + (1:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (1:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))*((a:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))*(p:ZMod (p^9))^3 + (1:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3 + (-1:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (1:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))*((a:ZMod (p^9))⁻¹) + (1:ZMod (p^9))*(EBb 2 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*((a:ZMod (p^9))⁻¹)*(HAsum 3 (p-1))*(p:ZMod (p^9))^6 + (1:ZMod (p^9))*(EBb 2 b)*(HAsum 3 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^6*(b:ZMod (p^9))^2 + (-1:ZMod (p^9))*(EBb 2 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*((a:ZMod (p^9))⁻¹)*(HAsum 2 (p-1))*(p:ZMod (p^9))^5 + (-1:ZMod (p^9))*(EBb 2 b)*(b:ZMod (p^9))*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^5 + (1:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))^4*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (1:ZMod (p^9))*(EBb 2 b)*(b:ZMod (p^9))*((a:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))*(p:ZMod (p^9))^4 + (1:ZMod (p^9))*(EBb 2 b)*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4 + (-1:ZMod (p^9))*(EBb 2 b)*(b:ZMod (p^9))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (1:ZMod (p^9))*(EBb 2 b)*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2 + (-1:ZMod (p^9))*(EBb 3 b)*(b:ZMod (p^9))*(p:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^2 + (1:ZMod (p^9))*(EBb 3 b)*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3 + (1:ZMod (p^9))*(EBb 4 b)*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4 + (1:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^8*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)^2*(HAsum 3 (p-1))^2 + (2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 3 (a-1))*((a:ZMod (p^9))⁻¹)*(HAsum 3 (p-1))*(p:ZMod (p^9))^8*(b:ZMod (p^9))^2 + (1:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^8*(b:ZMod (p^9))^4*(HAsum 3 (a-1))^2 + (-2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*((a:ZMod (p^9))⁻¹)*(HAsum 2 (p-1))*(HAsum 3 (p-1))*(p:ZMod (p^9))^7 + (-2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 3 (a-1))*((a:ZMod (p^9))⁻¹)*(HAsum 2 (p-1))*(p:ZMod (p^9))^7*(b:ZMod (p^9))^2 + (-2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(b:ZMod (p^9))*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)*(HAsum 3 (p-1))*(p:ZMod (p^9))^7 + (-2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 2 (a-1))*(HAsum 3 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^7*(b:ZMod (p^9))^3 + (1:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^6*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))^2*(HAsum 2 (p-1))^2 + (2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)*(HAsum 2 (p-1))*(p:ZMod (p^9))^6 + (2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(b:ZMod (p^9))*((a:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))*(HAsum 3 (p-1))*(p:ZMod (p^9))^6 + (2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)*(HAsum 3 (p-1))*(p:ZMod (p^9))^6 + (2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 3 (a-1))*((a:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))*(p:ZMod (p^9))^6*(b:ZMod (p^9))^3 + (2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 1 (a-1))*(HAsum 3 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^6*(b:ZMod (p^9))^2 + (1:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^6*(b:ZMod (p^9))^2*(HAsum 2 (a-1))^2 + (-2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*((a:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^5 + (-2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)*(HAsum 2 (p-1))*(p:ZMod (p^9))^5 + (-2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))*(p:ZMod (p^9))^5*(b:ZMod (p^9))^2 + (-2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^5 + (-1:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(SA2 (a+p*b))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4 + (1:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*(b:ZMod (p^9))^2*(HAsum 1 (p-1))^2 + (2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))*(p:ZMod (p^9))^4 + (1:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*(HAsum 1 (a-1))^2 + (1:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 3 (p-1))*(p:ZMod (p^9))^6*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (1:ZMod (p^9))*(HAsum 3 (a-1))*(p:ZMod (p^9))^6*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^3 + (-1:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(p:ZMod (p^9))^5*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-1:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(b:ZMod (p^9))*(HAsum 3 (p-1))*(p:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^2 + (-1:ZMod (p^9))*(HAsum 2 (a-1))*(p:ZMod (p^9))^5*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (-1:ZMod (p^9))*(HAsum 3 (a-1))*(p:ZMod (p^9))^5*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (1:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 2 (p-1))*(p:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^2 + (1:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*((a:ZMod (p^9))⁻¹)*(HAsum 3 (p-1))*(p:ZMod (p^9))^4 + (1:ZMod (p^9))*(p:ZMod (p^9))^4*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^5 + (1:ZMod (p^9))*(HAsum 1 (p-1))*(p:ZMod (p^9))^4*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (1:ZMod (p^9))*(HAsum 1 (a-1))*(p:ZMod (p^9))^4*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (1:ZMod (p^9))*(HAsum 2 (a-1))*(p:ZMod (p^9))^4*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (1:ZMod (p^9))*(HAsum 3 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*(b:ZMod (p^9))^2 + (-1:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*((a:ZMod (p^9))⁻¹)*(HAsum 2 (p-1))*(p:ZMod (p^9))^3 + (-1:ZMod (p^9))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (-1:ZMod (p^9))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-1:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (a-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (-1:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3 + (1:ZMod (p^9))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (1:ZMod (p^9))*(b:ZMod (p^9))*((a:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))*(p:ZMod (p^9))^2 + (1:ZMod (p^9))*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2 + (-1:ZMod (p^9))*(p:ZMod (p^9))*(b:ZMod (p^9))*((a:ZMod (p^9))⁻¹)^2 + (1:ZMod (p^9))*((a:ZMod (p^9))⁻¹)

set_option maxHeartbeats 4000000 in
noncomputable def LOWlodefS (a b : ℕ) : ZMod (p^9) :=
  (-1:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (1:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))*((a:ZMod (p^9))⁻¹) + (1:ZMod (p^9))*(EBb 2 b)*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2 + (1:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*((a:ZMod (p^9))⁻¹)*(HAsum 3 (p-1))*(p:ZMod (p^9))^4 + (1:ZMod (p^9))*(HAsum 3 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*(b:ZMod (p^9))^2 + (-1:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*((a:ZMod (p^9))⁻¹)*(HAsum 2 (p-1))*(p:ZMod (p^9))^3 + (-1:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3 + (1:ZMod (p^9))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (1:ZMod (p^9))*(b:ZMod (p^9))*((a:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))*(p:ZMod (p^9))^2 + (1:ZMod (p^9))*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2 + (-1:ZMod (p^9))*(p:ZMod (p^9))*(b:ZMod (p^9))*((a:ZMod (p^9))⁻¹)^2 + (1:ZMod (p^9))*((a:ZMod (p^9))⁻¹)

set_option maxHeartbeats 4000000 in
noncomputable def FINALsqT (a b : ℕ) : ZMod (p^9) :=
  (-1:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*((a:ZMod (p^9))⁻¹)*(HAsum 2 (p-1))*(p:ZMod (p^9))^4 + (-1:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))^4*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (-1:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (p-1))*(p:ZMod (p^9))^4*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-1:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(p:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^2 + (-1:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4 + (1:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (1:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))*((a:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))*(p:ZMod (p^9))^3 + (1:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3 + (-1:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (1:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))*((a:ZMod (p^9))⁻¹) + (1:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))^4*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (1:ZMod (p^9))*(EBb 2 b)*(b:ZMod (p^9))*((a:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))*(p:ZMod (p^9))^4 + (1:ZMod (p^9))*(EBb 2 b)*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4 + (-1:ZMod (p^9))*(EBb 2 b)*(b:ZMod (p^9))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (1:ZMod (p^9))*(EBb 2 b)*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2 + (-1:ZMod (p^9))*(EBb 3 b)*(b:ZMod (p^9))*(p:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^2 + (1:ZMod (p^9))*(EBb 3 b)*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3 + (1:ZMod (p^9))*(EBb 4 b)*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4 + (1:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*(b:ZMod (p^9))^2*(HAsum 1 (p-1))^2 + (2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))*(p:ZMod (p^9))^4 + (1:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*(HAsum 1 (a-1))^2 + (-1:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4 + (1:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 2 (p-1))*(p:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^2 + (1:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*((a:ZMod (p^9))⁻¹)*(HAsum 3 (p-1))*(p:ZMod (p^9))^4 + (1:ZMod (p^9))*(p:ZMod (p^9))^4*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^5 + (1:ZMod (p^9))*(HAsum 1 (p-1))*(p:ZMod (p^9))^4*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (1:ZMod (p^9))*(HAsum 1 (a-1))*(p:ZMod (p^9))^4*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (1:ZMod (p^9))*(HAsum 2 (a-1))*(p:ZMod (p^9))^4*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (1:ZMod (p^9))*(HAsum 3 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*(b:ZMod (p^9))^2 + (-1:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*((a:ZMod (p^9))⁻¹)*(HAsum 2 (p-1))*(p:ZMod (p^9))^3 + (-1:ZMod (p^9))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (-1:ZMod (p^9))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-1:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (a-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (-1:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3 + (1:ZMod (p^9))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (1:ZMod (p^9))*(b:ZMod (p^9))*((a:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))*(p:ZMod (p^9))^2 + (1:ZMod (p^9))*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2 + (-1:ZMod (p^9))*(p:ZMod (p^9))*(b:ZMod (p^9))*((a:ZMod (p^9))⁻¹)^2 + (1:ZMod (p^9))*((a:ZMod (p^9))⁻¹)

set_option maxHeartbeats 4000000 in
noncomputable def LOWlodefST (a b : ℕ) : ZMod (p^9) :=
  (-1:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (1:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))*((a:ZMod (p^9))⁻¹) + (1:ZMod (p^9))*(EBb 2 b)*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2 + (1:ZMod (p^9))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (1:ZMod (p^9))*(b:ZMod (p^9))*((a:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))*(p:ZMod (p^9))^2 + (1:ZMod (p^9))*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2 + (-1:ZMod (p^9))*(p:ZMod (p^9))*(b:ZMod (p^9))*((a:ZMod (p^9))⁻¹)^2 + (1:ZMod (p^9))*((a:ZMod (p^9))⁻¹)

set_option maxHeartbeats 4000000 in
noncomputable def FINAL_sep (a b : ℕ) : ZMod (p^9) :=
  (9:ZMod (p^9))*(EBb 1 b)^2*(p:ZMod (p^9))^8*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (p-1))*(EBb 1 b)^2*(p:ZMod (p^9))^8*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(HAsum 1 (a-1))*(EBb 1 b)^2*(p:ZMod (p^9))^8*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 1 b)^2*(p:ZMod (p^9))^8*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(b:ZMod (p^9))*(EBb 1 b)^2*(p:ZMod (p^9))^7*((a:ZMod (p^9))⁻¹)^3 + (3:ZMod (p^9))*(EBb 1 b)^2*(p:ZMod (p^9))^6*((a:ZMod (p^9))⁻¹)^2 + (-12:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(b:ZMod (p^9))*(p:ZMod (p^9))^8*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(p:ZMod (p^9))^7*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 1 b)*(EBb 3 b)*(p:ZMod (p^9))^8*((a:ZMod (p^9))⁻¹)^2 + (-12:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(p:ZMod (p^9))^8*((a:ZMod (p^9))⁻¹)^2 + (-24:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))^8*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (-24:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (p-1))*(p:ZMod (p^9))^8*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-24:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(p:ZMod (p^9))^8*((a:ZMod (p^9))⁻¹)^3 + (-12:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))*(HAsum 2 (a-1))*(p:ZMod (p^9))^8*((a:ZMod (p^9))⁻¹)^2 + (-18:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))*(p:ZMod (p^9))^8*((a:ZMod (p^9))⁻¹)^4 + (18:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))^7*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (12:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))*(HAsum 1 (p-1))*(p:ZMod (p^9))^7*((a:ZMod (p^9))⁻¹)^2 + (12:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (a-1))*(p:ZMod (p^9))^7*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))^7*((a:ZMod (p^9))⁻¹)^3 + (-12:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))*(p:ZMod (p^9))^6*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^2 + (3:ZMod (p^9))*(EBb 2 b)^2*(p:ZMod (p^9))^8*((a:ZMod (p^9))⁻¹)^2 + (18:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))^8*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (12:ZMod (p^9))*(EBb 2 b)*(b:ZMod (p^9))*(HAsum 1 (p-1))*(p:ZMod (p^9))^8*((a:ZMod (p^9))⁻¹)^2 + (12:ZMod (p^9))*(EBb 2 b)*(HAsum 1 (a-1))*(p:ZMod (p^9))^8*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))^8*((a:ZMod (p^9))⁻¹)^3 + (-12:ZMod (p^9))*(EBb 2 b)*(b:ZMod (p^9))*(p:ZMod (p^9))^7*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))^6*((a:ZMod (p^9))⁻¹)^2 + (-12:ZMod (p^9))*(EBb 3 b)*(b:ZMod (p^9))*(p:ZMod (p^9))^8*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 3 b)*(p:ZMod (p^9))^7*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 4 b)*(p:ZMod (p^9))^8*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^8*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^2 + (12:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^8*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^8*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 2 (a-1))*(p:ZMod (p^9))^8*((a:ZMod (p^9))⁻¹)^2 + (12:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 2 (p-1))*(p:ZMod (p^9))^8*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 3 (p-1))*(p:ZMod (p^9))^8*((a:ZMod (p^9))⁻¹)^2 + (15:ZMod (p^9))*(p:ZMod (p^9))^8*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^6 + (18:ZMod (p^9))*(HAsum 1 (p-1))*(p:ZMod (p^9))^8*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (18:ZMod (p^9))*(HAsum 1 (a-1))*(p:ZMod (p^9))^8*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (12:ZMod (p^9))*(HAsum 2 (a-1))*(p:ZMod (p^9))^8*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(HAsum 3 (a-1))*(p:ZMod (p^9))^8*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (12:ZMod (p^9))*(p:ZMod (p^9))^8*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^5 + (3:ZMod (p^9))*(p:ZMod (p^9))^8*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^2 + (6:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^8*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (p-1))*(p:ZMod (p^9))^8*((a:ZMod (p^9))⁻¹)^3 + (3:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(HAsum 1 (a-1))*(p:ZMod (p^9))^8*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(p:ZMod (p^9))^7*((a:ZMod (p^9))⁻¹)^2 + (-12:ZMod (p^9))*(p:ZMod (p^9))^7*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (-12:ZMod (p^9))*(HAsum 1 (p-1))*(p:ZMod (p^9))^7*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-12:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (a-1))*(p:ZMod (p^9))^7*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 2 (a-1))*(p:ZMod (p^9))^7*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(b:ZMod (p^9))*(p:ZMod (p^9))^7*((a:ZMod (p^9))⁻¹)^4 + (9:ZMod (p^9))*(p:ZMod (p^9))^6*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (p-1))*(p:ZMod (p^9))^6*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(HAsum 1 (a-1))*(p:ZMod (p^9))^6*((a:ZMod (p^9))⁻¹)^2 + (2:ZMod (p^9))*(p:ZMod (p^9))^6*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(b:ZMod (p^9))*(p:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^3 + (3:ZMod (p^9))*(p:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^2

theorem LOWdef_eq_S [Fact p.Prime] (a b : ℕ) (ha : 1 ≤ a) (ha2 : a ≤ p) :
    LOWdef (p:=p) a b = LOWdefS (p:=p) a b := by
  simp only [LOWdef, LOWdefS]
  rw [APP_reduce a b, Eb_eq_EBb 1 a b ha ha2, Eb_eq_EBb 2 a b ha ha2,
      Eb_eq_EBb 3 a b ha ha2, Eb_eq_EBb 4 a b ha ha2]
  ring

theorem LOWlodef_eq_S [Fact p.Prime] (a b : ℕ) (ha : 1 ≤ a) (ha2 : a ≤ p) :
    LOWlodef (p:=p) a b = LOWlodefS (p:=p) a b := by
  simp only [LOWlodef, LOWlodefS]
  rw [APP_reduce a b, Eb_eq_EBb 1 a b ha ha2, Eb_eq_EBb 2 a b ha ha2]
  ring

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem uoff_sep [Fact p.Prime] (hp5 : 5 ≤ p) (a b : ℕ) (ha : 1 ≤ a) (ha2 : a ≤ p - 1) :
    3 * ((p:ZMod (p^9))^2 * ((a+p*b:ℕ):ZMod (p^9))⁻¹ * Atr (a+p*b) * Btr (a+p*b))^2
     + 2 * ((p:ZMod (p^9))^2 * ((a+p*b:ℕ):ZMod (p^9))⁻¹ * Atr (a+p*b) * Btr (a+p*b))^3
      = FINAL_sep a b := by
  have hap : a ≤ p := by omega
  rw [uoff_term_final a b ha ha2, LOWdef_eq_S a b ha hap, LOWlodef_eq_S a b ha hap]
  obtain ⟨wv, hw⟩ := SA2_reduce hp5 a b ha ha2
  have hp9 : (p:ZMod (p^9))^9 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hsq : (p:ZMod (p^9))^5 ∣ (LOWdefS a b - FINALsqT a b) := by
    refine ⟨((-1:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*((a:ZMod (p^9))⁻¹)) * wv + ((-1:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(b:ZMod (p^9))*(HAsum 3 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (-1:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))*(HAsum 3 (a-1))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (1:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 2 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (1:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*((a:ZMod (p^9))⁻¹)*(HAsum 3 (p-1)) + (1:ZMod (p^9))*(EBb 1 b)*(HAsum 2 (a-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (1:ZMod (p^9))*(EBb 1 b)*(HAsum 3 (a-1))*((a:ZMod (p^9))⁻¹)*(b:ZMod (p^9))^2 + (1:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*((a:ZMod (p^9))⁻¹)*(HAsum 3 (p-1)) + (1:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))*(HAsum 3 (a-1))*((a:ZMod (p^9))⁻¹)*(b:ZMod (p^9))^2 + (-1:ZMod (p^9))*(EBb 2 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*((a:ZMod (p^9))⁻¹)*(HAsum 2 (p-1)) + (-1:ZMod (p^9))*(EBb 2 b)*(b:ZMod (p^9))*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹) + (1:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)^2*(HAsum 3 (p-1))^2 + (2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 3 (a-1))*((a:ZMod (p^9))⁻¹)*(HAsum 3 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2 + (1:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*(HAsum 3 (a-1))^2 + (-2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*((a:ZMod (p^9))⁻¹)*(HAsum 2 (p-1))*(HAsum 3 (p-1))*(p:ZMod (p^9))^2 + (-2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 3 (a-1))*((a:ZMod (p^9))⁻¹)*(HAsum 2 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2 + (-2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(b:ZMod (p^9))*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)*(HAsum 3 (p-1))*(p:ZMod (p^9))^2 + (-2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 2 (a-1))*(HAsum 3 (a-1))*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3 + (1:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*((a:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))^2*(HAsum 2 (p-1))^2 + (2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)*(HAsum 2 (p-1)) + (2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(b:ZMod (p^9))*((a:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))*(HAsum 3 (p-1)) + (2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)*(HAsum 3 (p-1)) + (2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(HAsum 3 (a-1))*((a:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))*(b:ZMod (p^9))^3 + (2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 3 (a-1))*((a:ZMod (p^9))⁻¹)*(b:ZMod (p^9))^2 + (1:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*((a:ZMod (p^9))⁻¹)*(b:ZMod (p^9))^2*(HAsum 2 (a-1))^2 + (-2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*((a:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))*(HAsum 2 (p-1)) + (-2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)*(HAsum 2 (p-1)) + (-2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))*(b:ZMod (p^9))^2 + (-2:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹) + (1:ZMod (p^9))*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 3 (p-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (1:ZMod (p^9))*(p:ZMod (p^9))*(HAsum 3 (a-1))*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^3 + (-1:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-1:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(b:ZMod (p^9))*(HAsum 3 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (-1:ZMod (p^9))*(HAsum 2 (a-1))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (-1:ZMod (p^9))*(HAsum 3 (a-1))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2), ?_⟩
    simp only [LOWdefS, FINALsqT]
    linear_combination ((-1:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*((a:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4) * hw
  have hcb : (p:ZMod (p^9))^3 ∣ (LOWlodefS a b - LOWlodefST a b) := by
    refine ⟨(1:ZMod (p^9))*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*((a:ZMod (p^9))⁻¹)*(HAsum 3 (p-1)) + (1:ZMod (p^9))*(p:ZMod (p^9))*(HAsum 3 (a-1))*((a:ZMod (p^9))⁻¹)*(b:ZMod (p^9))^2 + (-1:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*((a:ZMod (p^9))⁻¹)*(HAsum 2 (p-1)) + (-1:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹), ?_⟩
    simp only [LOWlodefS, LOWlodefST]
    ring
  rw [sq_reduce5 hsq, cube_reduce3 hcb]
  simp only [FINALsqT, LOWlodefST, FINAL_sep]
  linear_combination ((-2:ZMod (p^9))*(EBb 1 b)^3*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^6 + (6:ZMod (p^9))*(EBb 1 b)^3*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^5 + (-6:ZMod (p^9))*(p:ZMod (p^9))*(b:ZMod (p^9))*(EBb 1 b)^3*((a:ZMod (p^9))⁻¹)^4 + (2:ZMod (p^9))*(EBb 1 b)^3*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 2 b)*(EBb 1 b)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^5 + (-12:ZMod (p^9))*(EBb 2 b)*(b:ZMod (p^9))*(EBb 1 b)^2*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))*(EBb 1 b)^2*((a:ZMod (p^9))⁻¹)^3 + (3:ZMod (p^9))*(EBb 1 b)^2*(p:ZMod (p^9))^3*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))^2*((a:ZMod (p^9))⁻¹)^2*(HAsum 2 (p-1))^2 + (6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(EBb 1 b)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 1 (p-1))*(HAsum 2 (p-1))*(EBb 1 b)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 2 (p-1))*(EBb 1 b)^2*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 2 (a-1))*(HAsum 2 (p-1))*(EBb 1 b)^2*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (3:ZMod (p^9))*(EBb 1 b)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^6*((a:ZMod (p^9))⁻¹)^8 + (6:ZMod (p^9))*(HAsum 1 (p-1))*(EBb 1 b)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^6 + (6:ZMod (p^9))*(HAsum 1 (a-1))*(EBb 1 b)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^6 + (6:ZMod (p^9))*(HAsum 2 (a-1))*(EBb 1 b)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^5 + (6:ZMod (p^9))*(EBb 1 b)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^7 + (3:ZMod (p^9))*(EBb 1 b)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^4*(HAsum 1 (p-1))^2 + (6:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(EBb 1 b)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(HAsum 2 (a-1))*(HAsum 1 (p-1))*(EBb 1 b)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(HAsum 1 (p-1))*(EBb 1 b)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (3:ZMod (p^9))*(EBb 1 b)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 2 (a-1))*(EBb 1 b)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(HAsum 1 (a-1))*(EBb 1 b)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^5 + (3:ZMod (p^9))*(EBb 1 b)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*(HAsum 2 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(EBb 1 b)^2*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (-6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 1 (p-1))*(HAsum 2 (p-1))*(EBb 1 b)^2*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 1 (a-1))*(HAsum 2 (p-1))*(EBb 1 b)^2*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 1 b)^2*(p:ZMod (p^9))^2*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^7 + (-12:ZMod (p^9))*(HAsum 1 (p-1))*(EBb 1 b)^2*(p:ZMod (p^9))^2*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^5 + (-12:ZMod (p^9))*(HAsum 1 (a-1))*(EBb 1 b)^2*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (-6:ZMod (p^9))*(HAsum 2 (a-1))*(EBb 1 b)^2*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (-18:ZMod (p^9))*(EBb 1 b)^2*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^6 + (-6:ZMod (p^9))*(EBb 1 b)^2*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3*(HAsum 1 (p-1))^2 + (-12:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(EBb 1 b)^2*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(HAsum 2 (a-1))*(HAsum 1 (p-1))*(EBb 1 b)^2*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-12:ZMod (p^9))*(HAsum 1 (p-1))*(EBb 1 b)^2*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (-6:ZMod (p^9))*(b:ZMod (p^9))*(EBb 1 b)^2*(p:ZMod (p^9))^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 2 (a-1))*(EBb 1 b)^2*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-12:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (a-1))*(EBb 1 b)^2*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 2 (p-1))*(EBb 1 b)^2*((a:ZMod (p^9))⁻¹)^3 + (9:ZMod (p^9))*(p:ZMod (p^9))*(EBb 1 b)^2*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^6 + (12:ZMod (p^9))*(p:ZMod (p^9))*(HAsum 1 (p-1))*(EBb 1 b)^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (12:ZMod (p^9))*(p:ZMod (p^9))*(HAsum 1 (a-1))*(EBb 1 b)^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(p:ZMod (p^9))*(HAsum 2 (a-1))*(EBb 1 b)^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (24:ZMod (p^9))*(p:ZMod (p^9))*(EBb 1 b)^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^5 + (3:ZMod (p^9))*(p:ZMod (p^9))*(EBb 1 b)^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^2 + (6:ZMod (p^9))*(p:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(EBb 1 b)^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(p:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (p-1))*(EBb 1 b)^2*((a:ZMod (p^9))⁻¹)^3 + (3:ZMod (p^9))*(p:ZMod (p^9))*(EBb 1 b)^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(p:ZMod (p^9))*(HAsum 1 (a-1))*(EBb 1 b)^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(EBb 1 b)^2*((a:ZMod (p^9))⁻¹)^2 + (-12:ZMod (p^9))*(EBb 1 b)^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (-12:ZMod (p^9))*(HAsum 1 (p-1))*(EBb 1 b)^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-12:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (a-1))*(EBb 1 b)^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 2 (a-1))*(EBb 1 b)^2*((a:ZMod (p^9))⁻¹)^2 + (-18:ZMod (p^9))*(b:ZMod (p^9))*(EBb 1 b)^2*((a:ZMod (p^9))⁻¹)^4 + (-6:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))*(EBb 2 b)^2*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)^2*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (-6:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 1 (p-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 1 (a-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^7 + (-12:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^5 + (-12:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(HAsum 1 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (-6:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (-12:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^6 + (-6:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3*(HAsum 1 (p-1))^2 + (-12:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(HAsum 2 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-12:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (-6:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(b:ZMod (p^9))*(p:ZMod (p^9))^3*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (-12:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 2 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (12:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^6 + (18:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (18:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(HAsum 1 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(HAsum 2 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (24:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^5 + (6:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^2 + (12:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (12:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(b:ZMod (p^9))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(p:ZMod (p^9))^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (12:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(HAsum 1 (a-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (-18:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(p:ZMod (p^9))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (-18:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(p:ZMod (p^9))*(HAsum 1 (p-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-18:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(p:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(p:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)^2 + (-24:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(p:ZMod (p^9))*(b:ZMod (p^9))*((a:ZMod (p^9))⁻¹)^4 + (18:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (12:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(b:ZMod (p^9))*(HAsum 1 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (12:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2 + (12:ZMod (p^9))*(EBb 1 b)*(EBb 2 b)*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 1 b)*(EBb 3 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 1 b)*(EBb 3 b)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^6 + (6:ZMod (p^9))*(EBb 1 b)*(EBb 3 b)*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(EBb 1 b)*(EBb 3 b)*(HAsum 1 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(EBb 1 b)*(EBb 3 b)*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 1 b)*(EBb 3 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-12:ZMod (p^9))*(EBb 1 b)*(EBb 3 b)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (-12:ZMod (p^9))*(EBb 1 b)*(EBb 3 b)*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-12:ZMod (p^9))*(EBb 1 b)*(EBb 3 b)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 1 b)*(EBb 3 b)*(b:ZMod (p^9))*(HAsum 2 (a-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (12:ZMod (p^9))*(EBb 1 b)*(EBb 3 b)*(p:ZMod (p^9))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(EBb 1 b)*(EBb 3 b)*(p:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 1 b)*(EBb 3 b)*(p:ZMod (p^9))*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2 + (-12:ZMod (p^9))*(EBb 1 b)*(EBb 3 b)*(b:ZMod (p^9))*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 1 b)*(EBb 4 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 1 b)*(EBb 4 b)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (-6:ZMod (p^9))*(EBb 1 b)*(EBb 4 b)*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 1 b)*(EBb 4 b)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 1 b)*(EBb 4 b)*(b:ZMod (p^9))*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 1 b)*(EBb 4 b)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(EBb 1 b)*(EBb 4 b)*(b:ZMod (p^9))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 1 b)*(EBb 4 b)*(HAsum 1 (a-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 1 b)*(EBb 4 b)*(p:ZMod (p^9))*(b:ZMod (p^9))*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 1 b)*(EBb 4 b)*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^2 + (-12:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (a-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^5*(HAsum 1 (p-1))^2 + (-12:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^5 + (-6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^3*(HAsum 1 (p-1))^3 + (-6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^5 + (-18:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(HAsum 1 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3*(HAsum 1 (p-1))^2 + (6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (-6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^2 + (-18:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^3 + (-12:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(HAsum 1 (a-1))*(HAsum 2 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(HAsum 2 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(p:ZMod (p^9))^3*(HAsum 1 (a-1))^3*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(p:ZMod (p^9))^3*(HAsum 2 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^4*(HAsum 1 (p-1))^2 + (12:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^3 + (6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^4 + (18:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(HAsum 1 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^2 + (-6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(HAsum 2 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (18:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(HAsum 2 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2*(HAsum 1 (a-1))^3*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(HAsum 1 (a-1))*(HAsum 2 (a-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3*(HAsum 1 (p-1))^2 + (-12:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^2 + (12:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 1 b)*((2:ZMod (p^9))⁻¹)*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))*(p:ZMod (p^9))^3*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))^2*((a:ZMod (p^9))⁻¹)^3*(HAsum 2 (p-1))^2 + (-6:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 2 (p-1))*(HAsum 3 (p-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (-12:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^6 + (-12:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 1 (p-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (-12:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 1 (a-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (-12:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (a-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 3 (a-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 3 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (-6:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 1 (p-1))*(HAsum 3 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 3 (p-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(b:ZMod (p^9))*(HAsum 2 (a-1))*(HAsum 3 (p-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^7*((a:ZMod (p^9))⁻¹)^9 + (-12:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^6*((a:ZMod (p^9))⁻¹)^7 + (-12:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^7 + (-12:ZMod (p^9))*(EBb 1 b)*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^6 + (-6:ZMod (p^9))*(EBb 1 b)*(HAsum 3 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^5 + (-6:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^8 + (-6:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^5*(HAsum 1 (p-1))^2 + (-12:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^5 + (-12:ZMod (p^9))*(EBb 1 b)*(HAsum 2 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^4 + (-6:ZMod (p^9))*(EBb 1 b)*(HAsum 3 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^3 + (-12:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^6 + (-6:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^5 + (-12:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (a-1))*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (-6:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (a-1))*(HAsum 3 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (-12:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^6 + (-6:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*(HAsum 2 (a-1))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 1 b)*(HAsum 2 (a-1))*(HAsum 3 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4*(HAsum 1 (p-1))^2 + (-12:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (-6:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))*(p:ZMod (p^9))^3*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))^2*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))^2*((a:ZMod (p^9))⁻¹)^2*(HAsum 2 (p-1))^2 + (18:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (18:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 1 (p-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (18:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (12:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 2 (a-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 3 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(b:ZMod (p^9))*(HAsum 1 (p-1))*(HAsum 3 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 1 (a-1))*(HAsum 3 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (12:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^6*((a:ZMod (p^9))⁻¹)^8 + (24:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^6 + (24:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^6 + (18:ZMod (p^9))*(EBb 1 b)*(HAsum 2 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^5 + (6:ZMod (p^9))*(EBb 1 b)*(HAsum 3 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^4 + (18:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^7 + (12:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^4*(HAsum 1 (p-1))^2 + (24:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (18:ZMod (p^9))*(EBb 1 b)*(HAsum 2 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 1 b)*(HAsum 3 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (24:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (12:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^4 + (18:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (a-1))*(HAsum 2 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (a-1))*(HAsum 3 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (24:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^5 + (6:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*(HAsum 2 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3*(HAsum 1 (p-1))^2 + (12:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^3 + (-18:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (-12:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 1 (p-1))*(HAsum 2 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (-12:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 1 (a-1))*(HAsum 2 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(b:ZMod (p^9))*(HAsum 3 (p-1))*((a:ZMod (p^9))⁻¹)^3 + (-18:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^7 + (-30:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))*(HAsum 1 (p-1))*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^5 + (-30:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))*(HAsum 1 (a-1))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (-18:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))*(HAsum 2 (a-1))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (-6:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))*(HAsum 3 (a-1))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (-30:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^6 + (-12:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3*(HAsum 1 (p-1))^2 + (-24:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-12:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))*(HAsum 2 (a-1))*(HAsum 1 (p-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-24:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))*(HAsum 1 (p-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (-12:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^3 + (-12:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)^2 + (-24:ZMod (p^9))*(EBb 1 b)*(p:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^4 + (18:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 2 (p-1))*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 3 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (24:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^6 + (30:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (p-1))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (30:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (a-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (18:ZMod (p^9))*(EBb 1 b)*(HAsum 2 (a-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 1 b)*(HAsum 3 (a-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (30:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^5 + (6:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^2 + (12:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (12:ZMod (p^9))*(EBb 1 b)*(b:ZMod (p^9))*(HAsum 1 (p-1))*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (12:ZMod (p^9))*(EBb 1 b)*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^3 + (2:ZMod (p^9))*(EBb 2 b)^3*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (3:ZMod (p^9))*(EBb 2 b)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^6 + (6:ZMod (p^9))*(HAsum 1 (p-1))*(EBb 2 b)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(HAsum 1 (a-1))*(EBb 2 b)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(EBb 2 b)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^5 + (3:ZMod (p^9))*(EBb 2 b)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^2 + (6:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(EBb 2 b)^2*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (p-1))*(EBb 2 b)^2*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (3:ZMod (p^9))*(EBb 2 b)^2*(p:ZMod (p^9))^3*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(HAsum 1 (a-1))*(EBb 2 b)^2*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 2 b)^2*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (-6:ZMod (p^9))*(HAsum 1 (p-1))*(EBb 2 b)^2*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (a-1))*(EBb 2 b)^2*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(b:ZMod (p^9))*(EBb 2 b)^2*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (9:ZMod (p^9))*(p:ZMod (p^9))*(EBb 2 b)^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(p:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (p-1))*(EBb 2 b)^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(p:ZMod (p^9))*(HAsum 1 (a-1))*(EBb 2 b)^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(p:ZMod (p^9))*(EBb 2 b)^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(b:ZMod (p^9))*(EBb 2 b)^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 2 b)*(EBb 3 b)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (-6:ZMod (p^9))*(EBb 2 b)*(EBb 3 b)*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 2 b)*(EBb 3 b)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (12:ZMod (p^9))*(EBb 2 b)*(EBb 3 b)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(EBb 2 b)*(EBb 3 b)*(b:ZMod (p^9))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 2 b)*(EBb 3 b)*(HAsum 1 (a-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-12:ZMod (p^9))*(EBb 2 b)*(EBb 3 b)*(p:ZMod (p^9))*(b:ZMod (p^9))*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 2 b)*(EBb 3 b)*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 2 b)*(EBb 4 b)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(EBb 2 b)*(EBb 4 b)*(b:ZMod (p^9))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 2 b)*(EBb 4 b)*(HAsum 1 (a-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 2 b)*(EBb 4 b)*(b:ZMod (p^9))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 2 b)*(EBb 4 b)*(p:ZMod (p^9))*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 2 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^4*(HAsum 1 (p-1))^2 + (12:ZMod (p^9))*(EBb 2 b)*((2:ZMod (p^9))⁻¹)*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(EBb 2 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^3 + (6:ZMod (p^9))*(EBb 2 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^4 + (18:ZMod (p^9))*(EBb 2 b)*((2:ZMod (p^9))⁻¹)*(HAsum 1 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^2 + (-6:ZMod (p^9))*(EBb 2 b)*((2:ZMod (p^9))⁻¹)*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (18:ZMod (p^9))*(EBb 2 b)*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 2 b)*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(HAsum 2 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 2 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(HAsum 1 (a-1))^3*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 2 b)*((2:ZMod (p^9))⁻¹)*(HAsum 1 (a-1))*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 2 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3*(HAsum 1 (p-1))^2 + (-12:ZMod (p^9))*(EBb 2 b)*((2:ZMod (p^9))⁻¹)*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 2 b)*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(p:ZMod (p^9))^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 2 b)*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(HAsum 2 (a-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 2 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^2 + (12:ZMod (p^9))*(EBb 2 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 2 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 2 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 2 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (6:ZMod (p^9))*(EBb 2 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 1 (p-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 2 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 2 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 3 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(EBb 2 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(b:ZMod (p^9))*(HAsum 1 (p-1))*(HAsum 3 (p-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 2 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 1 (a-1))*(HAsum 3 (p-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^6*((a:ZMod (p^9))⁻¹)^8 + (12:ZMod (p^9))*(EBb 2 b)*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^6 + (12:ZMod (p^9))*(EBb 2 b)*(HAsum 1 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^6 + (6:ZMod (p^9))*(EBb 2 b)*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^5 + (6:ZMod (p^9))*(EBb 2 b)*(HAsum 3 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^7 + (6:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^4*(HAsum 1 (p-1))^2 + (12:ZMod (p^9))*(EBb 2 b)*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(EBb 2 b)*(HAsum 2 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 2 b)*(HAsum 3 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (12:ZMod (p^9))*(EBb 2 b)*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (6:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(EBb 2 b)*(HAsum 1 (a-1))*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 2 b)*(HAsum 1 (a-1))*(HAsum 3 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (12:ZMod (p^9))*(EBb 2 b)*(HAsum 1 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^5 + (6:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3*(HAsum 1 (p-1))^2 + (12:ZMod (p^9))*(EBb 2 b)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))^3*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^3 + (-12:ZMod (p^9))*(EBb 2 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (-6:ZMod (p^9))*(EBb 2 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 1 (p-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 2 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 1 (a-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 2 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(b:ZMod (p^9))*(HAsum 3 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-12:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^7 + (-18:ZMod (p^9))*(EBb 2 b)*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^5 + (-18:ZMod (p^9))*(EBb 2 b)*(HAsum 1 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (-12:ZMod (p^9))*(EBb 2 b)*(HAsum 2 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (-6:ZMod (p^9))*(EBb 2 b)*(HAsum 3 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (-12:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^6 + (-6:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3*(HAsum 1 (p-1))^2 + (-12:ZMod (p^9))*(EBb 2 b)*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 2 b)*(HAsum 2 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-12:ZMod (p^9))*(EBb 2 b)*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (-6:ZMod (p^9))*(EBb 2 b)*(b:ZMod (p^9))*(p:ZMod (p^9))^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 2 b)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 2 (a-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-12:ZMod (p^9))*(EBb 2 b)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (12:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 2 (p-1))*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 3 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (18:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^6 + (24:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))*(HAsum 1 (p-1))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (24:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))*(HAsum 1 (a-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (12:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))*(HAsum 2 (a-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))*(HAsum 3 (a-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (18:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^5 + (6:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^2 + (12:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (12:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (p-1))*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (12:ZMod (p^9))*(EBb 2 b)*(p:ZMod (p^9))*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 2 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (-18:ZMod (p^9))*(EBb 2 b)*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (-18:ZMod (p^9))*(EBb 2 b)*(HAsum 1 (p-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-18:ZMod (p^9))*(EBb 2 b)*(b:ZMod (p^9))*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 2 b)*(b:ZMod (p^9))*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)^2 + (-12:ZMod (p^9))*(EBb 2 b)*(b:ZMod (p^9))*((a:ZMod (p^9))⁻¹)^4 + (3:ZMod (p^9))*(EBb 3 b)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (-6:ZMod (p^9))*(b:ZMod (p^9))*(EBb 3 b)^2*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (3:ZMod (p^9))*(p:ZMod (p^9))*(EBb 3 b)^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 3 b)*(EBb 4 b)*(b:ZMod (p^9))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 3 b)*(EBb 4 b)*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 3 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3*(HAsum 1 (p-1))^2 + (-12:ZMod (p^9))*(EBb 3 b)*((2:ZMod (p^9))⁻¹)*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 3 b)*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(p:ZMod (p^9))^3*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 3 b)*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 3 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^2 + (12:ZMod (p^9))*(EBb 3 b)*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 3 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 3 b)*((2:ZMod (p^9))⁻¹)*(HAsum 2 (a-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 3 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (-6:ZMod (p^9))*(EBb 3 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(b:ZMod (p^9))*(HAsum 3 (p-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 3 b)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^7 + (-6:ZMod (p^9))*(EBb 3 b)*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^5 + (-6:ZMod (p^9))*(EBb 3 b)*(HAsum 1 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (-6:ZMod (p^9))*(EBb 3 b)*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (-6:ZMod (p^9))*(EBb 3 b)*(HAsum 3 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (12:ZMod (p^9))*(EBb 3 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 2 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 3 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 3 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (12:ZMod (p^9))*(EBb 3 b)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^6 + (12:ZMod (p^9))*(EBb 3 b)*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (12:ZMod (p^9))*(EBb 3 b)*(HAsum 1 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (12:ZMod (p^9))*(EBb 3 b)*(HAsum 2 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 3 b)*(HAsum 3 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 3 b)*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (-12:ZMod (p^9))*(EBb 3 b)*(p:ZMod (p^9))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (-12:ZMod (p^9))*(EBb 3 b)*(p:ZMod (p^9))*(HAsum 1 (p-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-12:ZMod (p^9))*(EBb 3 b)*(p:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 3 b)*(p:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)^2 + (12:ZMod (p^9))*(EBb 3 b)*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(EBb 3 b)*(b:ZMod (p^9))*(HAsum 1 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 3 b)*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2 + (3:ZMod (p^9))*(EBb 4 b)^2*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 4 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^2 + (12:ZMod (p^9))*(EBb 4 b)*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 4 b)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 4 b)*((2:ZMod (p^9))⁻¹)*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 4 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 4 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 3 (p-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 4 b)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^6 + (6:ZMod (p^9))*(EBb 4 b)*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(EBb 4 b)*(HAsum 1 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(EBb 4 b)*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(EBb 4 b)*(HAsum 3 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 4 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 4 b)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (-6:ZMod (p^9))*(EBb 4 b)*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 4 b)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(EBb 4 b)*(b:ZMod (p^9))*(HAsum 2 (a-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 4 b)*(p:ZMod (p^9))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(EBb 4 b)*(p:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(EBb 4 b)*(p:ZMod (p^9))*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(EBb 4 b)*(b:ZMod (p^9))*((a:ZMod (p^9))⁻¹)^3 + (3:ZMod (p^9))*((2:ZMod (p^9))⁻¹)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^4 + (12:ZMod (p^9))*(HAsum 1 (a-1))*((2:ZMod (p^9))⁻¹)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^3 + (18:ZMod (p^9))*((2:ZMod (p^9))⁻¹)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^2 + (-6:ZMod (p^9))*(HAsum 2 (a-1))*((2:ZMod (p^9))⁻¹)^2*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^2 + (12:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (p-1))*((2:ZMod (p^9))⁻¹)^2*(p:ZMod (p^9))^3*(HAsum 1 (a-1))^3*((a:ZMod (p^9))⁻¹)^2 + (-12:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 2 (a-1))*(HAsum 1 (p-1))*((2:ZMod (p^9))⁻¹)^2*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (3:ZMod (p^9))*((2:ZMod (p^9))⁻¹)^2*(p:ZMod (p^9))^3*(HAsum 1 (a-1))^4*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(HAsum 2 (a-1))*((2:ZMod (p^9))⁻¹)^2*(p:ZMod (p^9))^3*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (3:ZMod (p^9))*((2:ZMod (p^9))⁻¹)^2*(p:ZMod (p^9))^3*(HAsum 2 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3*(HAsum 1 (p-1))^2 + (12:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 2 (a-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 3 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^2 + (12:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(HAsum 3 (p-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 3 (p-1))*(p:ZMod (p^9))^3*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 2 (a-1))*(HAsum 3 (p-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^6*((a:ZMod (p^9))⁻¹)^6*(HAsum 1 (p-1))^2 + (12:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^6 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^4*(HAsum 1 (p-1))^3 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^6 + (18:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 1 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^4*(HAsum 1 (p-1))^2 + (-6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^6 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^3*(HAsum 1 (p-1))^2 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 3 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^2 + (18:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^4 + (12:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 1 (a-1))*(HAsum 2 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (12:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 1 (a-1))*(HAsum 3 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 2 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*(HAsum 1 (a-1))^3*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 3 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 1 (a-1))*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (-6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*(HAsum 2 (a-1))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 2 (a-1))*(HAsum 3 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^2 + (-12:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(p:ZMod (p^9))^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (a-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^5*(HAsum 1 (p-1))^2 + (-12:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^5 + (-6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^3*(HAsum 1 (p-1))^3 + (-6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^5 + (-18:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 1 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3*(HAsum 1 (p-1))^2 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 2 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (-6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 2 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^2 + (-18:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^3 + (-12:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 1 (a-1))*(HAsum 2 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 2 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(p:ZMod (p^9))^2*(HAsum 1 (a-1))^3*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(HAsum 2 (a-1))*(p:ZMod (p^9))^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 2 (a-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(p:ZMod (p^9))^2*(HAsum 2 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^4*(HAsum 1 (p-1))^2 + (12:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^3 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(b:ZMod (p^9))^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^4 + (18:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(HAsum 1 (a-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2*(HAsum 1 (p-1))^2 + (-6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(HAsum 2 (a-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (18:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (p-1))*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 2 (a-1))*(HAsum 1 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(HAsum 1 (a-1))^3*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3*(HAsum 1 (p-1))^2 + (-12:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*((2:ZMod (p^9))⁻¹)*(b:ZMod (p^9))*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)^3 + (3:ZMod (p^9))*(p:ZMod (p^9))^3*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4*(HAsum 2 (p-1))^2 + (6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(b:ZMod (p^9))*(HAsum 2 (p-1))*(HAsum 3 (p-1))*(p:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^7 + (6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 1 (p-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^5 + (6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 1 (a-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (a-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 3 (a-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (3:ZMod (p^9))*(p:ZMod (p^9))^3*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)^2*((a:ZMod (p^9))⁻¹)^2*(HAsum 3 (p-1))^2 + (6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 3 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^6 + (6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 1 (p-1))*(HAsum 3 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 1 (a-1))*(HAsum 3 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 2 (a-1))*(HAsum 3 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 3 (a-1))*(HAsum 3 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (3:ZMod (p^9))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^8*((a:ZMod (p^9))⁻¹)^10 + (6:ZMod (p^9))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^7*((a:ZMod (p^9))⁻¹)^8 + (6:ZMod (p^9))*(HAsum 1 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^6*((a:ZMod (p^9))⁻¹)^8 + (6:ZMod (p^9))*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^6*((a:ZMod (p^9))⁻¹)^7 + (6:ZMod (p^9))*(HAsum 3 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^6*((a:ZMod (p^9))⁻¹)^6 + (2:ZMod (p^9))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^6*((a:ZMod (p^9))⁻¹)^9 + (3:ZMod (p^9))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^6*((a:ZMod (p^9))⁻¹)^6*(HAsum 1 (p-1))^2 + (6:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^6 + (6:ZMod (p^9))*(HAsum 2 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^5 + (6:ZMod (p^9))*(HAsum 3 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^7 + (3:ZMod (p^9))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^6 + (6:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 2 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^5 + (6:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 3 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(HAsum 1 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^7 + (3:ZMod (p^9))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*(HAsum 2 (a-1))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(HAsum 2 (a-1))*(HAsum 3 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^3 + (3:ZMod (p^9))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*(HAsum 3 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^5*(HAsum 1 (p-1))^2 + (12:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (2:ZMod (p^9))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3*(HAsum 1 (p-1))^3 + (6:ZMod (p^9))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^5 + (6:ZMod (p^9))*(HAsum 1 (a-1))*(p:ZMod (p^9))^3*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3*(HAsum 1 (p-1))^2 + (6:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (p-1))*(p:ZMod (p^9))^3*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^3 + (2:ZMod (p^9))*(p:ZMod (p^9))^3*(HAsum 1 (a-1))^3*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(b:ZMod (p^9))*(p:ZMod (p^9))^2*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))^2*((a:ZMod (p^9))⁻¹)^3*(HAsum 2 (p-1))^2 + (-6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 2 (p-1))*(HAsum 3 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-12:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^6 + (-12:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 1 (p-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (-12:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 1 (a-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (-12:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (a-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 3 (a-1))*(HAsum 2 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 3 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (-6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 1 (p-1))*(HAsum 3 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 3 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(b:ZMod (p^9))*(HAsum 2 (a-1))*(HAsum 3 (p-1))*(p:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^7*((a:ZMod (p^9))⁻¹)^9 + (-12:ZMod (p^9))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^6*((a:ZMod (p^9))⁻¹)^7 + (-12:ZMod (p^9))*(HAsum 1 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^7 + (-12:ZMod (p^9))*(HAsum 2 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^6 + (-6:ZMod (p^9))*(HAsum 3 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^5 + (-6:ZMod (p^9))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^8 + (-6:ZMod (p^9))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^5*(HAsum 1 (p-1))^2 + (-12:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^5 + (-12:ZMod (p^9))*(HAsum 2 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^4 + (-6:ZMod (p^9))*(HAsum 3 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^3 + (-12:ZMod (p^9))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^6 + (-6:ZMod (p^9))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^5 + (-12:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 2 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (-6:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 3 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (-12:ZMod (p^9))*(HAsum 1 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^6 + (-6:ZMod (p^9))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*(HAsum 2 (a-1))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(HAsum 2 (a-1))*(HAsum 3 (a-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4*(HAsum 1 (p-1))^2 + (-12:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(p:ZMod (p^9))^2*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (-6:ZMod (p^9))*(b:ZMod (p^9))*(p:ZMod (p^9))^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^4 + (3:ZMod (p^9))*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))^2*((a:ZMod (p^9))⁻¹)^2*(HAsum 2 (p-1))^2 + (12:ZMod (p^9))*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (12:ZMod (p^9))*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 1 (p-1))*(HAsum 2 (p-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (12:ZMod (p^9))*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 2 (p-1))*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 2 (a-1))*(HAsum 2 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 3 (p-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (6:ZMod (p^9))*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(b:ZMod (p^9))*(HAsum 1 (p-1))*(HAsum 3 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(p:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(HAsum 1 (a-1))*(HAsum 3 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (9:ZMod (p^9))*(p:ZMod (p^9))*(b:ZMod (p^9))^6*((a:ZMod (p^9))⁻¹)^8 + (18:ZMod (p^9))*(p:ZMod (p^9))*(HAsum 1 (p-1))*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^6 + (18:ZMod (p^9))*(p:ZMod (p^9))*(HAsum 1 (a-1))*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^6 + (12:ZMod (p^9))*(p:ZMod (p^9))*(HAsum 2 (a-1))*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^5 + (6:ZMod (p^9))*(p:ZMod (p^9))*(HAsum 3 (a-1))*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^4 + (12:ZMod (p^9))*(p:ZMod (p^9))*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^7 + (9:ZMod (p^9))*(p:ZMod (p^9))*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^4*(HAsum 1 (p-1))^2 + (18:ZMod (p^9))*(p:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (12:ZMod (p^9))*(p:ZMod (p^9))*(HAsum 2 (a-1))*(HAsum 1 (p-1))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(p:ZMod (p^9))*(HAsum 3 (a-1))*(HAsum 1 (p-1))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^2 + (18:ZMod (p^9))*(p:ZMod (p^9))*(HAsum 1 (p-1))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (9:ZMod (p^9))*(p:ZMod (p^9))*(b:ZMod (p^9))^2*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^4 + (12:ZMod (p^9))*(p:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 2 (a-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(p:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 3 (a-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (18:ZMod (p^9))*(p:ZMod (p^9))*(HAsum 1 (a-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^5 + (3:ZMod (p^9))*(p:ZMod (p^9))*(b:ZMod (p^9))^2*(HAsum 2 (a-1))^2*((a:ZMod (p^9))⁻¹)^2 + (6:ZMod (p^9))*(p:ZMod (p^9))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3*(HAsum 1 (p-1))^2 + (12:ZMod (p^9))*(p:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*((a:ZMod (p^9))⁻¹)^3 + (6:ZMod (p^9))*(p:ZMod (p^9))*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^3 + (-12:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 2 (p-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (-6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))*(HAsum 1 (p-1))*(HAsum 2 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(HAsum 1 (a-1))*(HAsum 2 (p-1))*((a:ZMod (p^9))⁻¹)^2 + (-6:ZMod (p^9))*(∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)*(b:ZMod (p^9))*(HAsum 3 (p-1))*((a:ZMod (p^9))⁻¹)^3 + (-12:ZMod (p^9))*(b:ZMod (p^9))^5*((a:ZMod (p^9))⁻¹)^7 + (-18:ZMod (p^9))*(HAsum 1 (p-1))*(b:ZMod (p^9))^4*((a:ZMod (p^9))⁻¹)^5 + (-18:ZMod (p^9))*(HAsum 1 (a-1))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^5 + (-12:ZMod (p^9))*(HAsum 2 (a-1))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^4 + (-6:ZMod (p^9))*(HAsum 3 (a-1))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3 + (-14:ZMod (p^9))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^6 + (-6:ZMod (p^9))*(b:ZMod (p^9))^3*((a:ZMod (p^9))⁻¹)^3*(HAsum 1 (p-1))^2 + (-12:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 1 (p-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(HAsum 2 (a-1))*(HAsum 1 (p-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^2 + (-12:ZMod (p^9))*(HAsum 1 (p-1))*(b:ZMod (p^9))^2*((a:ZMod (p^9))⁻¹)^4 + (-6:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^3 + (-6:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (a-1))*(HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)^2 + (-12:ZMod (p^9))*(b:ZMod (p^9))*(HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^4) * hp9

-- Uoff as sum of FINAL_sep
theorem Uoff_eq [Fact p.Prime] (hp5 : 5 ≤ p) :
    Uoff (p:=p) = ∑ a ∈ Finset.Icc 1 (p-1), ∑ b ∈ Finset.range p, FINAL_sep a b := by
  simp only [Uoff]
  apply Finset.sum_congr rfl; intro a ha
  rw [Finset.mem_Icc] at ha
  apply Finset.sum_congr rfl; intro b _
  exact uoff_sep hp5 a b ha.1 ha.2

-- b-summation lemmas
theorem sum_Bpow2 [Fact p.Prime] :
    ∑ b ∈ Finset.range p, Bpow 2 b = (p:ZMod (p^9)) * wsum 2 - wsum 1 := by
  simp only [Bpow]
  rw [sum_range_Icc_swap p (fun i => ((i:ZMod (p^9))⁻¹)^2)]
  have key : ∀ i ∈ Finset.Icc 1 (p-1), ((i:ZMod (p^9))⁻¹)^2 * ((p:ZMod (p^9)) - (i:ZMod (p^9)))
      = (p:ZMod (p^9)) * ((i:ZMod (p^9))⁻¹)^2 - ((i:ZMod (p^9))⁻¹)^1 := by
    intro i hi; simp only [Finset.mem_Icc] at hi
    have hu : (i:ZMod (p^9))⁻¹ * (i:ZMod (p^9)) = 1 := unit_inv_mul hi.1 hi.2
    rw [mul_sub]; linear_combination (-(i:ZMod (p^9))⁻¹) * hu
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [wsum]

theorem sum_Bpow3 [Fact p.Prime] :
    ∑ b ∈ Finset.range p, Bpow 3 b = (p:ZMod (p^9)) * wsum 3 - wsum 2 := by
  simp only [Bpow]
  rw [sum_range_Icc_swap p (fun i => ((i:ZMod (p^9))⁻¹)^3)]
  have key : ∀ i ∈ Finset.Icc 1 (p-1), ((i:ZMod (p^9))⁻¹)^3 * ((p:ZMod (p^9)) - (i:ZMod (p^9)))
      = (p:ZMod (p^9)) * ((i:ZMod (p^9))⁻¹)^3 - ((i:ZMod (p^9))⁻¹)^2 := by
    intro i hi; simp only [Finset.mem_Icc] at hi
    have hu : (i:ZMod (p^9))⁻¹ * (i:ZMod (p^9)) = 1 := unit_inv_mul hi.1 hi.2
    rw [mul_sub]; linear_combination (-((i:ZMod (p^9))⁻¹)^2) * hu
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [wsum]

-- nested order-swap
theorem nested_swap (p : ℕ) (f g : ℕ → R) :
    ∑ i ∈ Finset.Icc 1 (p-1), (f i) * (∑ j ∈ Finset.Icc 1 (i-1), g j)
      = ∑ j ∈ Finset.Icc 1 (p-1), (g j) * (∑ i ∈ Finset.Icc (j+1) (p-1), f i) := by
  have L : ∀ i ∈ Finset.Icc 1 (p-1), (f i) * (∑ j ∈ Finset.Icc 1 (i-1), g j)
      = ∑ j ∈ Finset.Icc 1 (p-1), (if j + 1 ≤ i then f i * g j else 0) := by
    intro i hi; rw [Finset.mem_Icc] at hi
    rw [Finset.mul_sum, ← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext j; simp only [Finset.mem_Icc, Finset.mem_filter]; omega
  rw [Finset.sum_congr rfl L, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j hj; rw [Finset.mem_Icc] at hj
  rw [Finset.mul_sum, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => by ring)
  ext i; simp only [Finset.mem_Icc, Finset.mem_filter]; omega

-- partial sums & nested
theorem psum_Hsum [Fact p.Prime] (m : ℕ) (hm : m ≤ p) :
    ∑ b ∈ Finset.range m, Hsum b
      = (m:ZMod (p^9)) * HAsum 1 (m-1) - ((m-1 : ℕ) : ZMod (p^9)) := by
  simp only [Hsum]
  rw [sum_range_Icc_swap m (fun i => (i:ZMod (p^9))⁻¹)]
  have key : ∀ i ∈ Finset.Icc 1 (m-1), (i:ZMod (p^9))⁻¹ * ((m:ZMod (p^9)) - (i:ZMod (p^9)))
      = (m:ZMod (p^9)) * ((i:ZMod (p^9))⁻¹)^1 - 1 := by
    intro i hi; simp only [Finset.mem_Icc] at hi
    rw [pow_one, mul_sub, unit_inv_mul hi.1 (by omega)]; ring
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [HAsum, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one, pow_one]
  rw [show (m-1)+1-1 = m-1 from by omega]


theorem sum_nest_H1 [Fact p.Prime] :
    ∑ i ∈ Finset.Icc 1 (p-1), HAsum 1 (i-1)
      = ((p-1:ℕ):ZMod (p^9)) * wsum 1 - ((p-1:ℕ):ZMod (p^9)) := by
  have e : ∀ i ∈ Finset.Icc 1 (p-1), HAsum 1 (i-1)
      = (1:ZMod (p^9)) * (∑ j ∈ Finset.Icc 1 (i-1), (j:ZMod (p^9))⁻¹) := by
    intro i _; simp only [HAsum, one_mul, pow_one]
  rw [Finset.sum_congr rfl e, nested_swap p (fun _ => (1:ZMod (p^9))) (fun j => (j:ZMod (p^9))⁻¹)]
  have e2 : ∀ j ∈ Finset.Icc 1 (p-1),
      (j:ZMod (p^9))⁻¹ * (∑ i ∈ Finset.Icc (j+1) (p-1), (1:ZMod (p^9)))
      = ((p-1:ℕ):ZMod (p^9)) * (j:ZMod (p^9))⁻¹ - 1 := by
    intro j hj; simp only [Finset.mem_Icc] at hj
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one,
        show (p-1)+1-(j+1) = (p-1) - j from by omega, Nat.cast_sub (by omega)]
    have hu : (j:ZMod (p^9))⁻¹ * (j:ZMod (p^9)) = 1 := unit_inv_mul hj.1 hj.2
    linear_combination (-(1:ZMod (p^9))) * hu
  rw [Finset.sum_congr rfl e2, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [wsum, pow_one, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  rw [show (p-1)+1-1 = p-1 from by omega]

-- product b-sum
theorem sum_Hsq [Fact p.Prime] (hp : 2 ≤ p) :
    ∑ b ∈ Finset.range p, (Hsum b)^2
      = (p:ZMod (p^9)) * (wsum 1)^2 - (2*(p:ZMod (p^9))-1) * wsum 1 + 2*((p-1:ℕ):ZMod (p^9)) := by
  have hsq : ∑ b ∈ Finset.range p, (Hsum b)^2
      = ∑ b ∈ Finset.range p, (∑ i ∈ Finset.Icc 1 b, (i:ZMod (p^9))⁻¹) * (Hsum b) := by
    apply Finset.sum_congr rfl; intro b _; rw [sq]; simp only [Hsum]
  rw [hsq, sum_range_Icc_wswap p (fun i => (i:ZMod (p^9))⁻¹) (fun b => Hsum b)]
  have key : ∀ i ∈ Finset.Icc 1 (p-1),
      (i:ZMod (p^9))⁻¹ * (∑ b ∈ Finset.Icc i (p-1), Hsum b)
      = ((p:ZMod (p^9)) * wsum 1 - ((p-1:ℕ):ZMod (p^9))) * (i:ZMod (p^9))⁻¹
        - HAsum 1 (i-1) + (1 - (i:ZMod (p^9))⁻¹) := by
    intro i hi; rw [Finset.mem_Icc] at hi
    have hu : (i:ZMod (p^9))⁻¹ * (i:ZMod (p^9)) = 1 := unit_inv_mul hi.1 hi.2
    have hinner : ∑ b ∈ Finset.Icc i (p-1), Hsum b
        = ((p:ZMod (p^9)) * wsum 1 - ((p-1:ℕ):ZMod (p^9)))
          - ((i:ZMod (p^9)) * HAsum 1 (i-1) - ((i-1:ℕ):ZMod (p^9))) := by
      rw [show Finset.Icc i (p-1) = Finset.range p \ Finset.range i from by
            ext x; simp only [Finset.mem_Icc, Finset.mem_sdiff, Finset.mem_range]; omega]
      rw [Finset.sum_sdiff_eq_sub (by intro x hx; simp only [Finset.mem_range] at *; omega)]
      rw [psum_Hsum p (le_refl p), psum_Hsum i (by omega), show HAsum 1 (p-1) = wsum 1 from rfl]
    rw [hinner, Nat.cast_sub hi.1, Nat.cast_one]
    linear_combination (1 - HAsum 1 (i-1)) * hu
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, sum_nest_H1, Finset.sum_sub_distrib]
  have hws : ∑ i ∈ Finset.Icc 1 (p-1), (i:ZMod (p^9))⁻¹ = wsum 1 := by simp only [wsum, pow_one]
  rw [hws]
  simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one,
    show (p-1)+1-1 = p-1 from by omega]
  rw [Nat.cast_sub (show (1:ℕ) ≤ p from by omega), Nat.cast_one]
  ring

-- b-power sums
theorem psum_b1 (m : ℕ) :
    ∑ b ∈ Finset.range m, (b:ZMod (p^9)) = ((∑ b ∈ Finset.range m, b : ℕ) : ZMod (p^9)) := by
  rw [Nat.cast_sum]

theorem sum_b1 [Fact p.Prime] (hp : 3 ≤ p) :
    ∑ b ∈ Finset.range p, (b:ZMod (p^9)) = (p:ZMod (p^9))*((p:ZMod (p^9))-1)*(2:ZMod (p^9))⁻¹ := by
  have h2u : (2:ZMod (p^9)) * (2:ZMod (p^9))⁻¹ = 1 := by
    have he : ((2:ℕ):ZMod (p^9)) = 2 := by push_cast; ring
    rw [← he]; exact ZMod.mul_inv_of_unit _ (isUnit_cast_of_not_dvd (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega))
  have hgauss : (∑ b ∈ Finset.range p, b) * 2 = p * (p-1) := Finset.sum_range_id_mul_two p
  rw [psum_b1]
  have : ((∑ b ∈ Finset.range p, b : ℕ):ZMod (p^9)) * 2 = (p:ZMod (p^9))*((p:ZMod (p^9))-1) := by
    rw [← Nat.cast_ofNat (n:=2), ← Nat.cast_mul, hgauss]
    push_cast [Nat.cast_sub (show 1 ≤ p from by omega)]; ring
  linear_combination (2:ZMod (p^9))⁻¹ * this - ((∑ b ∈ Finset.range p, b : ℕ):ZMod (p^9))*h2u

-- nat_sum_sq, sum_b2 (b^2 power sum)
theorem nat_sum_sq (m : ℕ) : 6 * (∑ b ∈ Finset.range m, b^2) = m*(m-1)*(2*m-1) := by
  induction m with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    obtain rfl | hn := Nat.eq_zero_or_pos n
    · rfl
    · zify [show 1 ≤ n from hn, show 1 ≤ 2*n from by omega,
        show 1 ≤ n+1 from by omega, show 1 ≤ 2*(n+1) from by omega]; ring

theorem sum_b2 [Fact p.Prime] (hp : 7 ≤ p) :
    ∑ b ∈ Finset.range p, (b:ZMod (p^9))^2
      = (p:ZMod (p^9))*((p:ZMod (p^9))-1)*(2*(p:ZMod (p^9))-1)*(6:ZMod (p^9))⁻¹ := by
  have h6u : (6:ZMod (p^9)) * (6:ZMod (p^9))⁻¹ = 1 := by
    have he : ((6:ℕ):ZMod (p^9)) = 6 := by push_cast; ring
    rw [← he]; exact ZMod.mul_inv_of_unit _ (isUnit_cast_of_not_dvd (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega))
  have hcast : ∑ b ∈ Finset.range p, (b:ZMod (p^9))^2 = ((∑ b ∈ Finset.range p, b^2 : ℕ):ZMod (p^9)) := by
    push_cast; rfl
  rw [hcast]
  have key : ((∑ b ∈ Finset.range p, b^2 : ℕ):ZMod (p^9)) * 6
      = (p:ZMod (p^9))*((p:ZMod (p^9))-1)*(2*(p:ZMod (p^9))-1) := by
    rw [← Nat.cast_ofNat (n:=6), ← Nat.cast_mul, mul_comm, nat_sum_sq]
    push_cast [Nat.cast_sub (show 1 ≤ p from by omega), Nat.cast_sub (show 1 ≤ 2*p from by omega)]; ring
  linear_combination (6:ZMod (p^9))⁻¹ * key - ((∑ b ∈ Finset.range p, b^2 : ℕ):ZMod (p^9))*h6u

-- sum_B1b : ∑ Hsum b · b
set_option maxHeartbeats 1000000 in
theorem sum_B1b [Fact p.Prime] (hp : 3 ≤ p) :
    ∑ b ∈ Finset.range p, Hsum b * (b:ZMod (p^9))
      = (p:ZMod (p^9))*((p-1:ℕ):ZMod (p^9))*(2:ZMod (p^9))⁻¹ * wsum 1
        - ((p-1:ℕ):ZMod (p^9))*((p-2:ℕ):ZMod (p^9))*(2:ZMod (p^9))⁻¹*(2:ZMod (p^9))⁻¹ := by
  have h2u : (2:ZMod (p^9)) * (2:ZMod (p^9))⁻¹ = 1 := by
    have he : ((2:ℕ):ZMod (p^9)) = 2 := by push_cast; ring
    rw [← he]; exact ZMod.mul_inv_of_unit _ (isUnit_cast_of_not_dvd (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega))
  simp only [Hsum]
  rw [sum_range_Icc_wswap p (fun i => (i:ZMod (p^9))⁻¹) (fun b => (b:ZMod (p^9)))]
  have key : ∀ i ∈ Finset.Icc 1 (p-1),
      (i:ZMod (p^9))⁻¹ * (∑ b ∈ Finset.Icc i (p-1), (b:ZMod (p^9)))
      = (p:ZMod (p^9))*((p-1:ℕ):ZMod (p^9))*(2:ZMod (p^9))⁻¹ * (i:ZMod (p^9))⁻¹
        - ((i-1:ℕ):ZMod (p^9))*(2:ZMod (p^9))⁻¹ := by
    intro i hi; rw [Finset.mem_Icc] at hi
    have hu : (i:ZMod (p^9))⁻¹ * (i:ZMod (p^9)) = 1 := unit_inv_mul hi.1 hi.2
    have hsplit : ∑ b ∈ Finset.Icc i (p-1), (b:ZMod (p^9))
        = ((∑ b ∈ Finset.range p, b : ℕ):ZMod (p^9)) - ((∑ b ∈ Finset.range i, b : ℕ):ZMod (p^9)) := by
      rw [show Finset.Icc i (p-1) = Finset.range p \ Finset.range i from by
            ext x; simp only [Finset.mem_Icc, Finset.mem_sdiff, Finset.mem_range]; omega]
      rw [Finset.sum_sdiff_eq_sub (by intro x hx; simp only [Finset.mem_range] at *; omega),
          Nat.cast_sum, Nat.cast_sum]
    have hp2 : ((∑ b ∈ Finset.range p, b : ℕ):ZMod (p^9)) * 2 = (p:ZMod (p^9))*((p-1:ℕ):ZMod (p^9)) := by
      rw [← Nat.cast_ofNat (n:=2), ← Nat.cast_mul, Finset.sum_range_id_mul_two p]; push_cast; ring
    have hi2 : ((∑ b ∈ Finset.range i, b : ℕ):ZMod (p^9)) * 2 = (i:ZMod (p^9))*((i-1:ℕ):ZMod (p^9)) := by
      rw [← Nat.cast_ofNat (n:=2), ← Nat.cast_mul, Finset.sum_range_id_mul_two i]; push_cast; ring
    have hcrp : ((∑ b ∈ Finset.range p, b : ℕ):ZMod (p^9)) = (p:ZMod (p^9))*((p-1:ℕ):ZMod (p^9))*(2:ZMod (p^9))⁻¹ := by
      linear_combination (2:ZMod (p^9))⁻¹*hp2 - ((∑ b ∈ Finset.range p, b : ℕ):ZMod (p^9))*h2u
    have hcri : ((∑ b ∈ Finset.range i, b : ℕ):ZMod (p^9)) = (i:ZMod (p^9))*((i-1:ℕ):ZMod (p^9))*(2:ZMod (p^9))⁻¹ := by
      linear_combination (2:ZMod (p^9))⁻¹*hi2 - ((∑ b ∈ Finset.range i, b : ℕ):ZMod (p^9))*h2u
    rw [hsplit, hcrp, hcri]
    linear_combination (-(((i-1:ℕ):ZMod (p^9)))*(2:ZMod (p^9))⁻¹)*hu
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have hws : ∑ i ∈ Finset.Icc 1 (p-1), (i:ZMod (p^9))⁻¹ = wsum 1 := by simp only [wsum, pow_one]
  rw [hws]
  have hsumi : ∑ x ∈ Finset.Icc 1 (p-1), ((x-1:ℕ):ZMod (p^9))
      = ((p-1:ℕ):ZMod (p^9))*((p-2:ℕ):ZMod (p^9))*(2:ZMod (p^9))⁻¹ := by
    have hre : ∑ i ∈ Finset.Icc 1 (p-1), ((i-1:ℕ):ZMod (p^9))
        = ((∑ i ∈ Finset.range (p-1), i : ℕ):ZMod (p^9)) := by
      rw [Nat.cast_sum, show Finset.Icc 1 (p-1) = Finset.Ico 1 p from by
            ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
          Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr (by rw [show p-1 = p-1 from rfl])
      intro x hx; simp only [Nat.add_sub_cancel_left]
    rw [hre]
    have h0 : ((∑ i ∈ Finset.range (p-1), i : ℕ):ZMod (p^9)) * 2 = ((p-1:ℕ):ZMod (p^9))*((p-2:ℕ):ZMod (p^9)) := by
      rw [← Nat.cast_ofNat (n:=2), ← Nat.cast_mul, Finset.sum_range_id_mul_two (p-1)]
      push_cast [show p-1-1 = p-2 from by omega]; ring
    linear_combination (2:ZMod (p^9))⁻¹*h0 - ((∑ i ∈ Finset.range (p-1), i : ℕ):ZMod (p^9))*h2u
  rw [hsumi]

-- sum_B1b2 : ∑ Hsum b · b^2
set_option maxHeartbeats 1000000 in
theorem sum_B1b2 [Fact p.Prime] (hp : 7 ≤ p) :
    ∑ b ∈ Finset.range p, Hsum b * (b:ZMod (p^9))^2
      = (p:ZMod (p^9))*((p-1:ℕ):ZMod (p^9))*((2*p-1:ℕ):ZMod (p^9))*(6:ZMod (p^9))⁻¹ * wsum 1
        - ((p-1:ℕ):ZMod (p^9))*((p-2:ℕ):ZMod (p^9))*((4*p-3:ℕ):ZMod (p^9))*(6:ZMod (p^9))⁻¹*(6:ZMod (p^9))⁻¹ := by
  have h6u : (6:ZMod (p^9)) * (6:ZMod (p^9))⁻¹ = 1 := by
    have he : ((6:ℕ):ZMod (p^9)) = 6 := by push_cast; ring
    rw [← he]; exact ZMod.mul_inv_of_unit _ (isUnit_cast_of_not_dvd (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega))
  have hcast : ∀ b, Hsum b * (b:ZMod (p^9))^2 = (∑ i ∈ Finset.Icc 1 b, (i:ZMod (p^9))⁻¹) * ((b:ZMod (p^9))^2) := by
    intro b; rw [Hsum]
  simp only [hcast]
  rw [sum_range_Icc_wswap p (fun i => (i:ZMod (p^9))⁻¹) (fun b => (b:ZMod (p^9))^2)]
  have key : ∀ i ∈ Finset.Icc 1 (p-1),
      (i:ZMod (p^9))⁻¹ * (∑ b ∈ Finset.Icc i (p-1), (b:ZMod (p^9))^2)
      = (p:ZMod (p^9))*((p-1:ℕ):ZMod (p^9))*((2*p-1:ℕ):ZMod (p^9))*(6:ZMod (p^9))⁻¹ * (i:ZMod (p^9))⁻¹
        - ((i-1:ℕ):ZMod (p^9))*((2*i-1:ℕ):ZMod (p^9))*(6:ZMod (p^9))⁻¹ := by
    intro i hi; rw [Finset.mem_Icc] at hi
    have hu : (i:ZMod (p^9))⁻¹ * (i:ZMod (p^9)) = 1 := unit_inv_mul hi.1 hi.2
    have hsplit : ∑ b ∈ Finset.Icc i (p-1), (b:ZMod (p^9))^2
        = ((∑ b ∈ Finset.range p, b^2 : ℕ):ZMod (p^9)) - ((∑ b ∈ Finset.range i, b^2 : ℕ):ZMod (p^9)) := by
      rw [show Finset.Icc i (p-1) = Finset.range p \ Finset.range i from by
            ext x; simp only [Finset.mem_Icc, Finset.mem_sdiff, Finset.mem_range]; omega]
      rw [Finset.sum_sdiff_eq_sub (by intro x hx; simp only [Finset.mem_range] at *; omega)]
      push_cast [Nat.cast_sum]; rfl
    have hp2 : ((∑ b ∈ Finset.range p, b^2 : ℕ):ZMod (p^9)) * 6 = (p:ZMod (p^9))*((p-1:ℕ):ZMod (p^9))*((2*p-1:ℕ):ZMod (p^9)) := by
      rw [← Nat.cast_ofNat (n:=6), mul_comm, ← Nat.cast_mul, nat_sum_sq p]; push_cast; ring
    have hi2 : ((∑ b ∈ Finset.range i, b^2 : ℕ):ZMod (p^9)) * 6 = (i:ZMod (p^9))*((i-1:ℕ):ZMod (p^9))*((2*i-1:ℕ):ZMod (p^9)) := by
      rw [← Nat.cast_ofNat (n:=6), mul_comm, ← Nat.cast_mul, nat_sum_sq i]; push_cast; ring
    have hcrp : ((∑ b ∈ Finset.range p, b^2 : ℕ):ZMod (p^9)) = (p:ZMod (p^9))*((p-1:ℕ):ZMod (p^9))*((2*p-1:ℕ):ZMod (p^9))*(6:ZMod (p^9))⁻¹ := by
      linear_combination (6:ZMod (p^9))⁻¹*hp2 - ((∑ b ∈ Finset.range p, b^2 : ℕ):ZMod (p^9))*h6u
    have hcri : ((∑ b ∈ Finset.range i, b^2 : ℕ):ZMod (p^9)) = (i:ZMod (p^9))*((i-1:ℕ):ZMod (p^9))*((2*i-1:ℕ):ZMod (p^9))*(6:ZMod (p^9))⁻¹ := by
      linear_combination (6:ZMod (p^9))⁻¹*hi2 - ((∑ b ∈ Finset.range i, b^2 : ℕ):ZMod (p^9))*h6u
    rw [hsplit, hcrp, hcri]
    linear_combination (-(((i-1:ℕ):ZMod (p^9)))*(((2*i-1:ℕ):ZMod (p^9)))*(6:ZMod (p^9))⁻¹)*hu
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have hws : ∑ i ∈ Finset.Icc 1 (p-1), (i:ZMod (p^9))⁻¹ = wsum 1 := by simp only [wsum, pow_one]
  rw [hws]
  -- ∑_{i∈Icc1(p-1)} (i-1)(2i-1) closed form via reindex
  have hsumi : ∑ x ∈ Finset.Icc 1 (p-1), (((x-1:ℕ):ZMod (p^9))*((2*x-1:ℕ):ZMod (p^9)))
      = ((p-1:ℕ):ZMod (p^9))*((p-2:ℕ):ZMod (p^9))*((4*p-3:ℕ):ZMod (p^9))*(6:ZMod (p^9))⁻¹ := by
    have hre : ∑ x ∈ Finset.Icc 1 (p-1), (((x-1:ℕ):ZMod (p^9))*((2*x-1:ℕ):ZMod (p^9)))
        = ((∑ j ∈ Finset.range (p-1), j*(2*j+1) : ℕ):ZMod (p^9)) := by
      rw [Nat.cast_sum, show Finset.Icc 1 (p-1) = Finset.Ico 1 p from by
            ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
          Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro x hx; simp only [Finset.mem_range] at hx
      push_cast [show 1+x-1 = x from by omega, show 2*(1+x)-1 = 2*x+1 from by omega]; ring
    rw [hre]
    have hnat : 6 * (∑ j ∈ Finset.range (p-1), j*(2*j+1)) = (p-1)*(p-2)*(4*p-3) := by
      have e1 : ∑ j ∈ Finset.range (p-1), j*(2*j+1)
          = 2*(∑ j ∈ Finset.range (p-1), j^2) + (∑ j ∈ Finset.range (p-1), j) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j hj; ring
      have hsq := nat_sum_sq (p-1)
      have hid := Finset.sum_range_id_mul_two (p-1)
      rw [e1]
      zify [show 1 ≤ p from by omega, show 2 ≤ p from by omega, show 3 ≤ 2*p from by omega,
        show 3 ≤ 4*p from by omega, show 1 ≤ p-1 from by omega, show 1 ≤ 2*(p-1) from by omega] at hsq hid ⊢
      linear_combination 2*hsq + 3*hid
    have h0 : ((∑ j ∈ Finset.range (p-1), j*(2*j+1) : ℕ):ZMod (p^9)) * 6
        = ((p-1:ℕ):ZMod (p^9))*((p-2:ℕ):ZMod (p^9))*((4*p-3:ℕ):ZMod (p^9)) := by
      rw [← Nat.cast_ofNat (n:=6), mul_comm, ← Nat.cast_mul, hnat]; push_cast; ring
    linear_combination (6:ZMod (p^9))⁻¹*h0 - ((∑ j ∈ Finset.range (p-1), j*(2*j+1) : ℕ):ZMod (p^9))*h6u
  rw [hsumi]

-- nested helpers: psum_B2, sum_nest_H2, sum_nest_invH1
theorem psum_B2 [Fact p.Prime] (m : ℕ) (hm : m ≤ p) :
    ∑ b ∈ Finset.range m, Bpow 2 b
      = (m:ZMod (p^9)) * HAsum 2 (m-1) - HAsum 1 (m-1) := by
  simp only [Bpow]
  rw [sum_range_Icc_swap m (fun i => ((i:ZMod (p^9))⁻¹)^2)]
  have key : ∀ i ∈ Finset.Icc 1 (m-1), ((i:ZMod (p^9))⁻¹)^2 * ((m:ZMod (p^9)) - (i:ZMod (p^9)))
      = (m:ZMod (p^9)) * ((i:ZMod (p^9))⁻¹)^2 - ((i:ZMod (p^9))⁻¹)^1 := by
    intro i hi; simp only [Finset.mem_Icc] at hi
    have hu : (i:ZMod (p^9))⁻¹ * (i:ZMod (p^9)) = 1 := unit_inv_mul hi.1 (by omega)
    linear_combination (-(i:ZMod (p^9))⁻¹) * hu
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [HAsum, pow_one]

theorem sum_nest_H2 [Fact p.Prime] :
    ∑ i ∈ Finset.Icc 1 (p-1), HAsum 2 (i-1)
      = ((p-1:ℕ):ZMod (p^9)) * wsum 2 - wsum 1 := by
  have e : ∀ i ∈ Finset.Icc 1 (p-1), HAsum 2 (i-1)
      = (1:ZMod (p^9)) * (∑ j ∈ Finset.Icc 1 (i-1), ((j:ZMod (p^9))⁻¹)^2) := by
    intro i _; simp only [HAsum, one_mul]
  rw [Finset.sum_congr rfl e, nested_swap p (fun _ => (1:ZMod (p^9))) (fun j => ((j:ZMod (p^9))⁻¹)^2)]
  have e2 : ∀ j ∈ Finset.Icc 1 (p-1),
      ((j:ZMod (p^9))⁻¹)^2 * (∑ i ∈ Finset.Icc (j+1) (p-1), (1:ZMod (p^9)))
      = ((p-1:ℕ):ZMod (p^9)) * ((j:ZMod (p^9))⁻¹)^2 - ((j:ZMod (p^9))⁻¹)^1 := by
    intro j hj; simp only [Finset.mem_Icc] at hj
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one,
        show (p-1)+1-(j+1) = (p-1) - j from by omega, Nat.cast_sub (by omega)]
    have hu : (j:ZMod (p^9))⁻¹ * (j:ZMod (p^9)) = 1 := unit_inv_mul hj.1 hj.2
    linear_combination (-(j:ZMod (p^9))⁻¹) * hu
  rw [Finset.sum_congr rfl e2, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [wsum, pow_one]

set_option maxHeartbeats 800000 in
theorem sum_nest_invH1 [Fact p.Prime] :
    2 * (∑ i ∈ Finset.Icc 1 (p-1), (i:ZMod (p^9))⁻¹ * HAsum 1 (i-1))
      = (wsum 1)^2 - wsum 2 := by
  set S := ∑ i ∈ Finset.Icc 1 (p-1), (i:ZMod (p^9))⁻¹ * HAsum 1 (i-1) with hS
  -- S' := ∑_j j⁻¹·tail_j, equal to S via nested_swap
  have hnest : (∑ i ∈ Finset.Icc 1 (p-1), (i:ZMod (p^9))⁻¹ * (∑ j ∈ Finset.Icc 1 (i-1), (j:ZMod (p^9))⁻¹))
      = ∑ j ∈ Finset.Icc 1 (p-1), (j:ZMod (p^9))⁻¹ * (∑ i ∈ Finset.Icc (j+1) (p-1), (i:ZMod (p^9))⁻¹) :=
    nested_swap p (fun i => (i:ZMod (p^9))⁻¹) (fun j => (j:ZMod (p^9))⁻¹)
  have hSeq : S = ∑ i ∈ Finset.Icc 1 (p-1), (i:ZMod (p^9))⁻¹ * (∑ j ∈ Finset.Icc 1 (i-1), (j:ZMod (p^9))⁻¹) := by
    rw [hS]; apply Finset.sum_congr rfl; intro i _; simp only [HAsum, pow_one]
  -- wsum1^2 = ∑_i i⁻¹·wsum1
  have hsq : (wsum 1)^2 = ∑ i ∈ Finset.Icc 1 (p-1), (i:ZMod (p^9))⁻¹ * wsum 1 := by
    rw [sq, ← Finset.sum_mul]; congr 1; simp only [wsum, pow_one]
  -- for each i, wsum1 = HAsum1(i-1) + i⁻¹ + tail_i
  have hsplit : ∀ i ∈ Finset.Icc 1 (p-1), wsum 1
      = (∑ j ∈ Finset.Icc 1 (i-1), (j:ZMod (p^9))⁻¹) + (i:ZMod (p^9))⁻¹
        + (∑ j ∈ Finset.Icc (i+1) (p-1), (j:ZMod (p^9))⁻¹) := by
    intro i hi; simp only [Finset.mem_Icc] at hi
    simp only [wsum, pow_one]
    rw [show Finset.Icc 1 (p-1) = Finset.Icc 1 (i-1) ∪ {i} ∪ Finset.Icc (i+1) (p-1) from by
          ext x; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]; omega]
    rw [Finset.sum_union (by rw [Finset.disjoint_union_left]; constructor <;>
          (rw [Finset.disjoint_left]; intro a ha hb; simp only [Finset.mem_Icc, Finset.mem_singleton] at *; omega)),
        Finset.sum_union (by rw [Finset.disjoint_left]; intro a ha hb; simp only [Finset.mem_Icc, Finset.mem_singleton] at *; omega),
        Finset.sum_singleton]
  calc 2 * S = S + ∑ i ∈ Finset.Icc 1 (p-1), (i:ZMod (p^9))⁻¹ * (∑ j ∈ Finset.Icc (i+1) (p-1), (j:ZMod (p^9))⁻¹) := by
              rw [hSeq, hnest]; ring
    _ = (wsum 1)^2 - wsum 2 := by
              have hw2 : ∑ i ∈ Finset.Icc 1 (p-1), (i:ZMod (p^9))⁻¹ * (i:ZMod (p^9))⁻¹ = wsum 2 := by
                simp only [wsum]; apply Finset.sum_congr rfl; intro i _; rw [sq]
              rw [hsq]
              have hrw : ∑ i ∈ Finset.Icc 1 (p-1), (i:ZMod (p^9))⁻¹ * wsum 1
                  = ∑ i ∈ Finset.Icc 1 (p-1), ((i:ZMod (p^9))⁻¹ * (∑ j ∈ Finset.Icc 1 (i-1), (j:ZMod (p^9))⁻¹)
                      + (i:ZMod (p^9))⁻¹ * (i:ZMod (p^9))⁻¹
                      + (i:ZMod (p^9))⁻¹ * (∑ j ∈ Finset.Icc (i+1) (p-1), (j:ZMod (p^9))⁻¹)) := by
                apply Finset.sum_congr rfl; intro i hi; rw [hsplit i hi]; ring
              rw [hrw, Finset.sum_add_distrib, Finset.sum_add_distrib, ← hSeq, hw2]
              ring

-- sum_B1B2
set_option maxHeartbeats 1000000 in
theorem sum_B1B2 [Fact p.Prime] (hp : 3 ≤ p) :
    ∑ b ∈ Finset.range p, Bpow 1 b * Bpow 2 b
      = (p:ZMod (p^9)) * wsum 1 * wsum 2 - (wsum 1)^2*(2:ZMod (p^9))⁻¹
        - ((p-1:ℕ):ZMod (p^9))*wsum 2 - wsum 2*(2:ZMod (p^9))⁻¹ + wsum 1 := by
  have h2u : (2:ZMod (p^9)) * (2:ZMod (p^9))⁻¹ = 1 := by
    have he : ((2:ℕ):ZMod (p^9)) = 2 := by push_cast; ring
    rw [← he]; exact ZMod.mul_inv_of_unit _ (isUnit_cast_of_not_dvd (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega))
  have hcast : ∀ b, Bpow 1 b * Bpow 2 b = (∑ i ∈ Finset.Icc 1 b, (i:ZMod (p^9))⁻¹) * (Bpow 2 b) := by
    intro b; rw [Bpow]; simp only [pow_one]
  simp only [hcast]
  rw [sum_range_Icc_wswap p (fun i => (i:ZMod (p^9))⁻¹) (fun b => Bpow 2 b)]
  have key : ∀ i ∈ Finset.Icc 1 (p-1),
      (i:ZMod (p^9))⁻¹ * (∑ b ∈ Finset.Icc i (p-1), Bpow 2 b)
      = ((p:ZMod (p^9)) * wsum 2 - wsum 1) * (i:ZMod (p^9))⁻¹
        - HAsum 2 (i-1) + (i:ZMod (p^9))⁻¹ * HAsum 1 (i-1) := by
    intro i hi; rw [Finset.mem_Icc] at hi
    have hu : (i:ZMod (p^9))⁻¹ * (i:ZMod (p^9)) = 1 := unit_inv_mul hi.1 hi.2
    have hinner : ∑ b ∈ Finset.Icc i (p-1), Bpow 2 b
        = ((p:ZMod (p^9)) * wsum 2 - wsum 1)
          - ((i:ZMod (p^9)) * HAsum 2 (i-1) - HAsum 1 (i-1)) := by
      rw [show Finset.Icc i (p-1) = Finset.range p \ Finset.range i from by
            ext x; simp only [Finset.mem_Icc, Finset.mem_sdiff, Finset.mem_range]; omega]
      rw [Finset.sum_sdiff_eq_sub (by intro x hx; simp only [Finset.mem_range] at *; omega)]
      rw [psum_B2 p (le_refl p), psum_B2 i (by omega),
          show HAsum 2 (p-1) = wsum 2 from rfl, show HAsum 1 (p-1) = wsum 1 from rfl]
    rw [hinner]
    linear_combination (-(HAsum 2 (i-1))) * hu
  rw [Finset.sum_congr rfl key]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hws2 : ∑ i ∈ Finset.Icc 1 (p-1), (i:ZMod (p^9))⁻¹ = wsum 1 := by simp only [wsum, pow_one]
  rw [hws2, sum_nest_H2]
  rw [show ∑ i ∈ Finset.Icc 1 (p-1), (i:ZMod (p^9))⁻¹ * HAsum 1 (i-1)
        = (wsum 1^2 - wsum 2) * (2:ZMod (p^9))⁻¹ from by
      have := sum_nest_invH1 (p:=p)
      linear_combination (2:ZMod (p^9))⁻¹ * this
        - (∑ i ∈ Finset.Icc 1 (p-1), (i:ZMod (p^9))⁻¹ * HAsum 1 (i-1)) * h2u]
  linear_combination (wsum 1^2) * h2u

-- gen_nestH1, gen_psum_Hsq (general m)
theorem gen_nestH1 [Fact p.Prime] (m : ℕ) (hm : m ≤ p) :
    ∑ i ∈ Finset.Icc 1 (m-1), HAsum 1 (i-1)
      = ((m-1:ℕ):ZMod (p^9)) * HAsum 1 (m-1) - ((m-1:ℕ):ZMod (p^9)) := by
  have e : ∀ i ∈ Finset.Icc 1 (m-1), HAsum 1 (i-1)
      = (1:ZMod (p^9)) * (∑ j ∈ Finset.Icc 1 (i-1), (j:ZMod (p^9))⁻¹) := by
    intro i _; simp only [HAsum, one_mul, pow_one]
  rw [Finset.sum_congr rfl e, nested_swap m (fun _ => (1:ZMod (p^9))) (fun j => (j:ZMod (p^9))⁻¹)]
  have e2 : ∀ j ∈ Finset.Icc 1 (m-1),
      (j:ZMod (p^9))⁻¹ * (∑ i ∈ Finset.Icc (j+1) (m-1), (1:ZMod (p^9)))
      = ((m-1:ℕ):ZMod (p^9)) * (j:ZMod (p^9))⁻¹ - 1 := by
    intro j hj; simp only [Finset.mem_Icc] at hj
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one,
        show (m-1)+1-(j+1) = (m-1) - j from by omega, Nat.cast_sub (by omega)]
    have hu : (j:ZMod (p^9))⁻¹ * (j:ZMod (p^9)) = 1 := unit_inv_mul hj.1 (by omega)
    linear_combination (-(1:ZMod (p^9))) * hu
  rw [Finset.sum_congr rfl e2, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [HAsum, pow_one, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  rw [show (m-1)+1-1 = m-1 from by omega]

set_option maxHeartbeats 800000 in
theorem gen_psum_Hsq [Fact p.Prime] (m : ℕ) (hm : m ≤ p) :
    ∑ b ∈ Finset.range m, (Hsum b)^2
      = (m:ZMod (p^9)) * (HAsum 1 (m-1))^2 - (2*(m:ZMod (p^9))-1) * HAsum 1 (m-1)
        + 2*((m-1:ℕ):ZMod (p^9)) := by
  obtain rfl | hm1 := Nat.eq_zero_or_pos m
  · simp [HAsum]
  have hsq : ∑ b ∈ Finset.range m, (Hsum b)^2
      = ∑ b ∈ Finset.range m, (∑ i ∈ Finset.Icc 1 b, (i:ZMod (p^9))⁻¹) * (Hsum b) := by
    apply Finset.sum_congr rfl; intro b _; rw [sq]; simp only [Hsum]
  rw [hsq, sum_range_Icc_wswap m (fun i => (i:ZMod (p^9))⁻¹) (fun b => Hsum b)]
  have key : ∀ i ∈ Finset.Icc 1 (m-1),
      (i:ZMod (p^9))⁻¹ * (∑ b ∈ Finset.Icc i (m-1), Hsum b)
      = ((m:ZMod (p^9)) * HAsum 1 (m-1) - ((m-1:ℕ):ZMod (p^9))) * (i:ZMod (p^9))⁻¹
        - HAsum 1 (i-1) + (1 - (i:ZMod (p^9))⁻¹) := by
    intro i hi; rw [Finset.mem_Icc] at hi
    have hu : (i:ZMod (p^9))⁻¹ * (i:ZMod (p^9)) = 1 := unit_inv_mul hi.1 (by omega)
    have hinner : ∑ b ∈ Finset.Icc i (m-1), Hsum b
        = ((m:ZMod (p^9)) * HAsum 1 (m-1) - ((m-1:ℕ):ZMod (p^9)))
          - ((i:ZMod (p^9)) * HAsum 1 (i-1) - ((i-1:ℕ):ZMod (p^9))) := by
      rw [show Finset.Icc i (m-1) = Finset.range m \ Finset.range i from by
            ext x; simp only [Finset.mem_Icc, Finset.mem_sdiff, Finset.mem_range]; omega]
      rw [Finset.sum_sdiff_eq_sub (by intro x hx; simp only [Finset.mem_range] at *; omega)]
      rw [psum_Hsum m hm, psum_Hsum i (by omega)]
    rw [hinner, Nat.cast_sub hi.1, Nat.cast_one]
    linear_combination (1 - HAsum 1 (i-1)) * hu
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, gen_nestH1 m hm, Finset.sum_sub_distrib]
  have hws : ∑ i ∈ Finset.Icc 1 (m-1), (i:ZMod (p^9))⁻¹ = HAsum 1 (m-1) := by
    simp only [HAsum, pow_one]
  rw [hws]
  simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one,
    show (m-1)+1-1 = m-1 from by omega]
  rw [Nat.cast_sub (show (1:ℕ) ≤ m from hm1), Nat.cast_one]
  ring

-- gen_nest_invH1 (general n Euler sum)
set_option maxHeartbeats 800000 in
theorem gen_nest_invH1 [Fact p.Prime] (n : ℕ) (hn : n ≤ p-1) :
    2 * (∑ i ∈ Finset.Icc 1 n, (i:ZMod (p^9))⁻¹ * HAsum 1 (i-1))
      = (HAsum 1 n)^2 - HAsum 2 n := by
  set S := ∑ i ∈ Finset.Icc 1 n, (i:ZMod (p^9))⁻¹ * HAsum 1 (i-1) with hS
  have hnest : (∑ i ∈ Finset.Icc 1 n, (i:ZMod (p^9))⁻¹ * (∑ j ∈ Finset.Icc 1 (i-1), (j:ZMod (p^9))⁻¹))
      = ∑ j ∈ Finset.Icc 1 n, (j:ZMod (p^9))⁻¹ * (∑ i ∈ Finset.Icc (j+1) n, (i:ZMod (p^9))⁻¹) :=
    nested_swap (n+1) (fun i => (i:ZMod (p^9))⁻¹) (fun j => (j:ZMod (p^9))⁻¹)
  have hSeq : S = ∑ i ∈ Finset.Icc 1 n, (i:ZMod (p^9))⁻¹ * (∑ j ∈ Finset.Icc 1 (i-1), (j:ZMod (p^9))⁻¹) := by
    rw [hS]; apply Finset.sum_congr rfl; intro i _; simp only [HAsum, pow_one]
  have hsq : (HAsum 1 n)^2 = ∑ i ∈ Finset.Icc 1 n, (i:ZMod (p^9))⁻¹ * HAsum 1 n := by
    rw [sq, ← Finset.sum_mul]; congr 1; simp only [HAsum, pow_one]
  have hsplit : ∀ i ∈ Finset.Icc 1 n, HAsum 1 n
      = (∑ j ∈ Finset.Icc 1 (i-1), (j:ZMod (p^9))⁻¹) + (i:ZMod (p^9))⁻¹
        + (∑ j ∈ Finset.Icc (i+1) n, (j:ZMod (p^9))⁻¹) := by
    intro i hi; simp only [Finset.mem_Icc] at hi
    simp only [HAsum, pow_one]
    rw [show Finset.Icc 1 n = Finset.Icc 1 (i-1) ∪ {i} ∪ Finset.Icc (i+1) n from by
          ext x; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]; omega]
    rw [Finset.sum_union (by rw [Finset.disjoint_union_left]; constructor <;>
          (rw [Finset.disjoint_left]; intro a ha hb; simp only [Finset.mem_Icc, Finset.mem_singleton] at *; omega)),
        Finset.sum_union (by rw [Finset.disjoint_left]; intro a ha hb; simp only [Finset.mem_Icc, Finset.mem_singleton] at *; omega),
        Finset.sum_singleton]
  calc 2 * S = S + ∑ i ∈ Finset.Icc 1 n, (i:ZMod (p^9))⁻¹ * (∑ j ∈ Finset.Icc (i+1) n, (j:ZMod (p^9))⁻¹) := by
              rw [hSeq, hnest]; ring
    _ = (HAsum 1 n)^2 - HAsum 2 n := by
              have hw2 : ∑ i ∈ Finset.Icc 1 n, (i:ZMod (p^9))⁻¹ * (i:ZMod (p^9))⁻¹ = HAsum 2 n := by
                simp only [HAsum]; apply Finset.sum_congr rfl; intro i _; rw [sq]
              rw [hsq]
              have hrw : ∑ i ∈ Finset.Icc 1 n, (i:ZMod (p^9))⁻¹ * HAsum 1 n
                  = ∑ i ∈ Finset.Icc 1 n, ((i:ZMod (p^9))⁻¹ * (∑ j ∈ Finset.Icc 1 (i-1), (j:ZMod (p^9))⁻¹)
                      + (i:ZMod (p^9))⁻¹ * (i:ZMod (p^9))⁻¹
                      + (i:ZMod (p^9))⁻¹ * (∑ j ∈ Finset.Icc (i+1) n, (j:ZMod (p^9))⁻¹)) := by
                apply Finset.sum_congr rfl; intro i hi; rw [hsplit i hi]; ring
              rw [hrw, Finset.sum_add_distrib, Finset.sum_add_distrib, ← hSeq, hw2]
              ring

-- sum_nest_Hsq
set_option maxHeartbeats 800000 in
theorem sum_nest_Hsq [Fact p.Prime] (hp : 3 ≤ p) :
    ∑ l ∈ Finset.Icc 1 (p-1), (HAsum 1 (l-1))^2
      = ((p-1:ℕ):ZMod (p^9))*wsum 2 - wsum 1
        + 2*(((p-1:ℕ):ZMod (p^9))*((wsum 1^2 - wsum 2)*(2:ZMod (p^9))⁻¹)
            - (((p-1:ℕ):ZMod (p^9))*wsum 1 - ((p-1:ℕ):ZMod (p^9)))) := by
  have h2u : (2:ZMod (p^9)) * (2:ZMod (p^9))⁻¹ = 1 := by
    have he : ((2:ℕ):ZMod (p^9)) = 2 := by push_cast; ring
    rw [← he]; exact ZMod.mul_inv_of_unit _ (isUnit_cast_of_not_dvd (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega))
  -- per-l square identity
  have hper : ∀ l ∈ Finset.Icc 1 (p-1), (HAsum 1 (l-1))^2
      = HAsum 2 (l-1) + 2 * (∑ k ∈ Finset.Icc 1 (l-1), (k:ZMod (p^9))⁻¹ * HAsum 1 (k-1)) := by
    intro l hl; rw [Finset.mem_Icc] at hl
    have := gen_nest_invH1 (p:=p) (l-1) (by omega)
    linear_combination -this
  rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib, sum_nest_H2, ← Finset.mul_sum]
  -- double sum: ∑_l ∑_{k<l} G k  with G k = k⁻¹ HAsum1(k-1)
  have hdbl : ∑ l ∈ Finset.Icc 1 (p-1), (∑ k ∈ Finset.Icc 1 (l-1), (k:ZMod (p^9))⁻¹ * HAsum 1 (k-1))
      = ∑ k ∈ Finset.Icc 1 (p-1), ((k:ZMod (p^9))⁻¹ * HAsum 1 (k-1)) * (∑ i ∈ Finset.Icc (k+1) (p-1), (1:ZMod (p^9))) := by
    have h1 : ∑ l ∈ Finset.Icc 1 (p-1), (∑ k ∈ Finset.Icc 1 (l-1), (k:ZMod (p^9))⁻¹ * HAsum 1 (k-1))
        = ∑ l ∈ Finset.Icc 1 (p-1), (1:ZMod (p^9)) * (∑ k ∈ Finset.Icc 1 (l-1), (k:ZMod (p^9))⁻¹ * HAsum 1 (k-1)) := by
      apply Finset.sum_congr rfl; intro l _; rw [one_mul]
    rw [h1, nested_swap p (fun _ => (1:ZMod (p^9))) (fun k => (k:ZMod (p^9))⁻¹ * HAsum 1 (k-1))]
  rw [hdbl]
  have hcount : ∀ k ∈ Finset.Icc 1 (p-1),
      ((k:ZMod (p^9))⁻¹ * HAsum 1 (k-1)) * (∑ i ∈ Finset.Icc (k+1) (p-1), (1:ZMod (p^9)))
      = ((p-1:ℕ):ZMod (p^9)) * ((k:ZMod (p^9))⁻¹ * HAsum 1 (k-1)) - HAsum 1 (k-1) := by
    intro k hk; simp only [Finset.mem_Icc] at hk
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one,
        show (p-1)+1-(k+1) = (p-1)-k from by omega, Nat.cast_sub (by omega)]
    have hu : (k:ZMod (p^9))⁻¹ * (k:ZMod (p^9)) = 1 := unit_inv_mul hk.1 hk.2
    linear_combination (- HAsum 1 (k-1)) * hu
  rw [Finset.sum_congr rfl hcount, Finset.sum_sub_distrib, ← Finset.mul_sum]
  -- ∑_k k⁻¹ HAsum1(k-1) via sum_nest_invH1, ∑_k HAsum1(k-1) via sum_nest_H1
  have heuler : ∑ k ∈ Finset.Icc 1 (p-1), (k:ZMod (p^9))⁻¹ * HAsum 1 (k-1)
      = (wsum 1^2 - wsum 2)*(2:ZMod (p^9))⁻¹ := by
    have := sum_nest_invH1 (p:=p)
    linear_combination (2:ZMod (p^9))⁻¹ * this
      - (∑ k ∈ Finset.Icc 1 (p-1), (k:ZMod (p^9))⁻¹ * HAsum 1 (k-1)) * h2u
  rw [heuler, sum_nest_H1]

-- sum_B1cube
set_option maxHeartbeats 2000000 in
theorem sum_B1cube [Fact p.Prime] (hp : 3 ≤ p) :
    ∑ b ∈ Finset.range p, (Bpow 1 b)^3
      = (p:ZMod (p^9))*wsum 1^3 - 3*(p:ZMod (p^9))*wsum 1^2 + 3*wsum 1^2*(2:ZMod (p^9))⁻¹
        + 6*(p:ZMod (p^9))*wsum 1 - 3*wsum 1 + wsum 2*(2:ZMod (p^9))⁻¹
        - 6*(p:ZMod (p^9)) + 6 := by
  have h2u : (2:ZMod (p^9)) * (2:ZMod (p^9))⁻¹ = 1 := by
    have he : ((2:ℕ):ZMod (p^9)) = 2 := by push_cast; ring
    rw [← he]; exact ZMod.mul_inv_of_unit _ (isUnit_cast_of_not_dvd (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega))
  have hcast : ∀ b, (Bpow 1 b)^3 = (∑ l ∈ Finset.Icc 1 b, (l:ZMod (p^9))⁻¹) * (Hsum b)^2 := by
    intro b; rw [Bpow]; simp only [pow_one, Hsum]; ring
  simp only [hcast]
  rw [sum_range_Icc_wswap p (fun l => (l:ZMod (p^9))⁻¹) (fun b => (Hsum b)^2)]
  set C := (p:ZMod (p^9))*(wsum 1)^2 - (2*(p:ZMod (p^9))-1)*wsum 1 + 2*((p-1:ℕ):ZMod (p^9)) with hC
  have key : ∀ l ∈ Finset.Icc 1 (p-1),
      (l:ZMod (p^9))⁻¹ * (∑ b ∈ Finset.Icc l (p-1), (Hsum b)^2)
      = C * (l:ZMod (p^9))⁻¹ - (HAsum 1 (l-1))^2 + (2 - (l:ZMod (p^9))⁻¹)*HAsum 1 (l-1)
        - (2 - 2*(l:ZMod (p^9))⁻¹) := by
    intro l hl; rw [Finset.mem_Icc] at hl
    have hu : (l:ZMod (p^9))⁻¹ * (l:ZMod (p^9)) = 1 := unit_inv_mul hl.1 hl.2
    have hinner : ∑ b ∈ Finset.Icc l (p-1), (Hsum b)^2
        = C - ((l:ZMod (p^9))*(HAsum 1 (l-1))^2 - (2*(l:ZMod (p^9))-1)*HAsum 1 (l-1) + 2*((l-1:ℕ):ZMod (p^9))) := by
      rw [show Finset.Icc l (p-1) = Finset.range p \ Finset.range l from by
            ext x; simp only [Finset.mem_Icc, Finset.mem_sdiff, Finset.mem_range]; omega]
      rw [Finset.sum_sdiff_eq_sub (by intro x hx; simp only [Finset.mem_range] at *; omega)]
      rw [gen_psum_Hsq p (le_refl p), gen_psum_Hsq l (by omega), hC,
          show HAsum 1 (p-1) = wsum 1 from rfl]
    rw [hinner]
    have hl1 : ((l-1:ℕ):ZMod (p^9)) = (l:ZMod (p^9)) - 1 := by
      rw [Nat.cast_sub hl.1, Nat.cast_one]
    rw [hl1]
    linear_combination (-(HAsum 1 (l-1))^2 + 2*HAsum 1 (l-1) - 2) * hu
  rw [Finset.sum_congr rfl key]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hws : ∑ l ∈ Finset.Icc 1 (p-1), (l:ZMod (p^9))⁻¹ = wsum 1 := by simp only [wsum, pow_one]
  rw [hws]
  -- ∑ (2-l⁻¹)·H(l-1) = 2·nestH1 - euler
  have hA : ∑ l ∈ Finset.Icc 1 (p-1), (2 - (l:ZMod (p^9))⁻¹)*HAsum 1 (l-1)
      = 2*(((p-1:ℕ):ZMod (p^9))*wsum 1 - ((p-1:ℕ):ZMod (p^9)))
        - (wsum 1^2 - wsum 2)*(2:ZMod (p^9))⁻¹ := by
    have hexp : ∀ l ∈ Finset.Icc 1 (p-1), (2 - (l:ZMod (p^9))⁻¹)*HAsum 1 (l-1)
        = 2*HAsum 1 (l-1) - (l:ZMod (p^9))⁻¹*HAsum 1 (l-1) := by intro l _; ring
    rw [Finset.sum_congr rfl hexp, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_nest_H1]
    have heuler : ∑ l ∈ Finset.Icc 1 (p-1), (l:ZMod (p^9))⁻¹ * HAsum 1 (l-1)
        = (wsum 1^2 - wsum 2)*(2:ZMod (p^9))⁻¹ := by
      have := sum_nest_invH1 (p:=p)
      linear_combination (2:ZMod (p^9))⁻¹ * this
        - (∑ l ∈ Finset.Icc 1 (p-1), (l:ZMod (p^9))⁻¹ * HAsum 1 (l-1)) * h2u
    rw [heuler]
  -- ∑ (2-2l⁻¹) = 2(p-1) - 2 wsum1
  have hB : ∑ l ∈ Finset.Icc 1 (p-1), (2 - 2*(l:ZMod (p^9))⁻¹)
      = 2*((p-1:ℕ):ZMod (p^9)) - 2*wsum 1 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hws, Finset.sum_const, Nat.card_Icc,
        show (p-1)+1-1 = p-1 from by omega, nsmul_eq_mul]
    ring
  rw [sum_nest_Hsq hp, hA, hB, hC]
  have hpc : ((p-1:ℕ):ZMod (p^9)) = (p:ZMod (p^9)) - 1 := by
    rw [Nat.cast_sub (show (1:ℕ) ≤ p from by omega), Nat.cast_one]
  rw [hpc]
  linear_combination (-(p:ZMod (p^9))*wsum 1^2 + (p:ZMod (p^9))*wsum 2 - wsum 1^2 - wsum 2) * h2u

-- wsum3_dvd_p2 (odd power vp>=2)
theorem wsum3_dvd_p2 [hp : Fact p.Prime] (hp7 : 7 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
    (p : ZMod (p^t))^2 ∣ ∑ k ∈ Finset.Icc 1 (p-1), ((k : ZMod (p^t))⁻¹)^3 := by
  set S := ∑ k ∈ Finset.Icc 1 (p-1), ((k : ZMod (p^t))⁻¹)^3 with hS
  have hrefl : S = ∑ k ∈ Finset.Icc 1 (p-1), (((p - k : ℕ) : ZMod (p^t))⁻¹)^3 :=
    sum_Icc_reflect (fun k => ((k : ZMod (p^t))⁻¹)^3)
  have hunit : ∀ k ∈ Finset.Icc 1 (p-1), IsUnit (k : ZMod (p^t)) := by
    intro k hk; simp only [Finset.mem_Icc] at hk; exact isUnit_of_lt hk.1 hk.2
  have hunit' : ∀ k ∈ Finset.Icc 1 (p-1), IsUnit ((p - k : ℕ) : ZMod (p^t)) := by
    intro k hk; simp only [Finset.mem_Icc] at hk; exact isUnit_of_lt (by omega) (by omega)
  set T := ∑ k ∈ Finset.Icc 1 (p-1),
      ((k : ZMod (p^t))⁻¹ * ((p - k : ℕ) : ZMod (p^t))⁻¹)
      * (((k : ZMod (p^t))⁻¹)^2 - (k : ZMod (p^t))⁻¹ * ((p - k : ℕ) : ZMod (p^t))⁻¹
          + (((p - k : ℕ) : ZMod (p^t))⁻¹)^2) with hT
  have hkey : (2 : ZMod (p^t)) * S = (p : ZMod (p^t)) * T := by
    rw [two_mul]; nth_rewrite 2 [hrefl]
    rw [hT, Finset.mul_sum, hS, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hu := hunit k hk; have hw := hunit' k hk
    have hck : ((p - k : ℕ) : ZMod (p^t)) = (p : ZMod (p^t)) - (k : ZMod (p^t)) := by
      simp only [Finset.mem_Icc] at hk; rw [Nat.cast_sub (by omega)]
    have e1 : (k : ZMod (p^t)) * ((k : ZMod (p^t))⁻¹) = 1 := ZMod.mul_inv_of_unit _ hu
    have e2 : ((p - k : ℕ) : ZMod (p^t)) * (((p - k : ℕ) : ZMod (p^t))⁻¹) = 1 := ZMod.mul_inv_of_unit _ hw
    have hsum : (k : ZMod (p^t))⁻¹ + ((p - k : ℕ) : ZMod (p^t))⁻¹
        = (p : ZMod (p^t)) * ((k : ZMod (p^t))⁻¹ * ((p - k : ℕ) : ZMod (p^t))⁻¹) := by
      have : (p : ZMod (p^t)) = (k : ZMod (p^t)) + ((p - k : ℕ) : ZMod (p^t)) := by rw [hck]; ring
      rw [this]
      linear_combination -(((p - k : ℕ) : ZMod (p^t))⁻¹ * e1) - (k : ZMod (p^t))⁻¹ * e2
    -- u^3+v^3 = (u+v)(u^2-uv+v^2)
    have hfac : ((k : ZMod (p^t))⁻¹)^3 + (((p - k : ℕ) : ZMod (p^t))⁻¹)^3
        = ((k : ZMod (p^t))⁻¹ + ((p - k : ℕ) : ZMod (p^t))⁻¹)
          * (((k : ZMod (p^t))⁻¹)^2 - (k : ZMod (p^t))⁻¹ * ((p - k : ℕ) : ZMod (p^t))⁻¹
              + (((p - k : ℕ) : ZMod (p^t))⁻¹)^2) := by ring
    rw [hfac, hsum]; ring
  have hpT : (p : ZMod (p^t)) ∣ T := by
    apply dvd_of_castHom_eq_zero ht
    rw [hT, map_sum]
    have hterm : ∀ k ∈ Finset.Icc 1 (p-1),
        (ZMod.castHom (dvd_pow_self p (by omega : t≠0)) (ZMod p))
          (((k : ZMod (p^t))⁻¹ * ((p - k : ℕ) : ZMod (p^t))⁻¹)
            * (((k : ZMod (p^t))⁻¹)^2 - (k : ZMod (p^t))⁻¹ * ((p - k : ℕ) : ZMod (p^t))⁻¹
                + (((p - k : ℕ) : ZMod (p^t))⁻¹)^2))
          = -(3 * ((k : ZMod p)⁻¹)^4) := by
      intro k hk; simp only [Finset.mem_Icc] at hk
      simp only [map_mul, map_add, map_sub, map_pow,
          castHom_inv_gen ht (k:ZMod (p^t)) (hunit k (by simp [Finset.mem_Icc]; omega)),
          castHom_inv_gen ht ((p - k : ℕ):ZMod (p^t)) (hunit' k (by simp [Finset.mem_Icc]; omega)),
          map_natCast]
      have c3 : ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring
      rw [c3, inv_neg]; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, ← Finset.mul_sum,
        sum_inv_pow_units_zero (by norm_num) (by omega), mul_zero, neg_zero]
  obtain ⟨T', hT'⟩ := hpT
  have h2S : (2 : ZMod (p^t)) * S = (p : ZMod (p^t))^2 * T' := by rw [hkey, hT']; ring
  have h2unit : IsUnit (2 : ZMod (p^t)) := by
    have he : ((2:ℕ):ZMod (p^t)) = 2 := by push_cast; ring
    rw [← he]; exact isUnit_cast_of_not_dvd (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
  refine ⟨(2:ZMod (p^t))⁻¹ * T', ?_⟩
  have : S = (2:ZMod (p^t))⁻¹ * ((2:ZMod (p^t)) * S) := by
    rw [← mul_assoc, ZMod.inv_mul_of_unit _ h2unit, one_mul]
  rw [this, h2S]; ring

-- wsum5_dvd_p2 (odd power vp>=2)
theorem wsum5_dvd_p2 [hp : Fact p.Prime] (hp11 : 11 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
    (p : ZMod (p^t))^2 ∣ ∑ k ∈ Finset.Icc 1 (p-1), ((k : ZMod (p^t))⁻¹)^5 := by
  set S := ∑ k ∈ Finset.Icc 1 (p-1), ((k : ZMod (p^t))⁻¹)^5 with hS
  have hrefl : S = ∑ k ∈ Finset.Icc 1 (p-1), (((p - k : ℕ) : ZMod (p^t))⁻¹)^5 :=
    sum_Icc_reflect (fun k => ((k : ZMod (p^t))⁻¹)^5)
  have hunit : ∀ k ∈ Finset.Icc 1 (p-1), IsUnit (k : ZMod (p^t)) := by
    intro k hk; simp only [Finset.mem_Icc] at hk; exact isUnit_of_lt hk.1 hk.2
  have hunit' : ∀ k ∈ Finset.Icc 1 (p-1), IsUnit ((p - k : ℕ) : ZMod (p^t)) := by
    intro k hk; simp only [Finset.mem_Icc] at hk; exact isUnit_of_lt (by omega) (by omega)
  set T := ∑ k ∈ Finset.Icc 1 (p-1),
      ((k : ZMod (p^t))⁻¹ * ((p - k : ℕ) : ZMod (p^t))⁻¹)
      * (((k : ZMod (p^t))⁻¹)^4 - ((k : ZMod (p^t))⁻¹)^3 * ((p - k : ℕ) : ZMod (p^t))⁻¹
          + ((k : ZMod (p^t))⁻¹)^2 * (((p - k : ℕ) : ZMod (p^t))⁻¹)^2
          - (k : ZMod (p^t))⁻¹ * (((p - k : ℕ) : ZMod (p^t))⁻¹)^3
          + (((p - k : ℕ) : ZMod (p^t))⁻¹)^4) with hT
  have hkey : (2 : ZMod (p^t)) * S = (p : ZMod (p^t)) * T := by
    rw [two_mul]; nth_rewrite 2 [hrefl]
    rw [hT, Finset.mul_sum, hS, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hu := hunit k hk; have hw := hunit' k hk
    have hck : ((p - k : ℕ) : ZMod (p^t)) = (p : ZMod (p^t)) - (k : ZMod (p^t)) := by
      simp only [Finset.mem_Icc] at hk; rw [Nat.cast_sub (by omega)]
    have e1 : (k : ZMod (p^t)) * ((k : ZMod (p^t))⁻¹) = 1 := ZMod.mul_inv_of_unit _ hu
    have e2 : ((p - k : ℕ) : ZMod (p^t)) * (((p - k : ℕ) : ZMod (p^t))⁻¹) = 1 := ZMod.mul_inv_of_unit _ hw
    have hsum : (k : ZMod (p^t))⁻¹ + ((p - k : ℕ) : ZMod (p^t))⁻¹
        = (p : ZMod (p^t)) * ((k : ZMod (p^t))⁻¹ * ((p - k : ℕ) : ZMod (p^t))⁻¹) := by
      have : (p : ZMod (p^t)) = (k : ZMod (p^t)) + ((p - k : ℕ) : ZMod (p^t)) := by rw [hck]; ring
      rw [this]
      linear_combination -(((p - k : ℕ) : ZMod (p^t))⁻¹ * e1) - (k : ZMod (p^t))⁻¹ * e2
    -- u^3+v^3 = (u+v)(u^2-uv+v^2)
    have hfac : ((k : ZMod (p^t))⁻¹)^5 + (((p - k : ℕ) : ZMod (p^t))⁻¹)^5
        = ((k : ZMod (p^t))⁻¹ + ((p - k : ℕ) : ZMod (p^t))⁻¹)
          * (((k : ZMod (p^t))⁻¹)^4 - ((k : ZMod (p^t))⁻¹)^3 * ((p - k : ℕ) : ZMod (p^t))⁻¹
              + ((k : ZMod (p^t))⁻¹)^2 * (((p - k : ℕ) : ZMod (p^t))⁻¹)^2
              - (k : ZMod (p^t))⁻¹ * (((p - k : ℕ) : ZMod (p^t))⁻¹)^3
              + (((p - k : ℕ) : ZMod (p^t))⁻¹)^4) := by ring
    rw [hfac, hsum]; ring
  have hpT : (p : ZMod (p^t)) ∣ T := by
    apply dvd_of_castHom_eq_zero ht
    rw [hT, map_sum]
    have hterm : ∀ k ∈ Finset.Icc 1 (p-1),
        (ZMod.castHom (dvd_pow_self p (by omega : t≠0)) (ZMod p))
          (((k : ZMod (p^t))⁻¹ * ((p - k : ℕ) : ZMod (p^t))⁻¹)
            * (((k : ZMod (p^t))⁻¹)^4 - ((k : ZMod (p^t))⁻¹)^3 * ((p - k : ℕ) : ZMod (p^t))⁻¹
                + ((k : ZMod (p^t))⁻¹)^2 * (((p - k : ℕ) : ZMod (p^t))⁻¹)^2
                - (k : ZMod (p^t))⁻¹ * (((p - k : ℕ) : ZMod (p^t))⁻¹)^3
                + (((p - k : ℕ) : ZMod (p^t))⁻¹)^4))
          = -(5 * ((k : ZMod p)⁻¹)^6) := by
      intro k hk; simp only [Finset.mem_Icc] at hk
      simp only [map_mul, map_add, map_sub, map_pow,
          castHom_inv_gen ht (k:ZMod (p^t)) (hunit k (by simp [Finset.mem_Icc]; omega)),
          castHom_inv_gen ht ((p - k : ℕ):ZMod (p^t)) (hunit' k (by simp [Finset.mem_Icc]; omega)),
          map_natCast]
      have c3 : ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring
      rw [c3, inv_neg]; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, ← Finset.mul_sum,
        sum_inv_pow_units_zero (by norm_num) (by omega), mul_zero, neg_zero]
  obtain ⟨T', hT'⟩ := hpT
  have h2S : (2 : ZMod (p^t)) * S = (p : ZMod (p^t))^2 * T' := by rw [hkey, hT']; ring
  have h2unit : IsUnit (2 : ZMod (p^t)) := by
    have he : ((2:ℕ):ZMod (p^t)) = 2 := by push_cast; ring
    rw [← he]; exact isUnit_cast_of_not_dvd (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
  refine ⟨(2:ZMod (p^t))⁻¹ * T', ?_⟩
  have : S = (2:ZMod (p^t))⁻¹ * ((2:ZMod (p^t)) * S) := by
    rw [← mul_assoc, ZMod.inv_mul_of_unit _ h2unit, one_mul]
  rw [this, h2S]; ring

-- ZMod p reflection identity for partial harmonic sums
theorem HAp_refl [Fact p.Prime] {s : ℕ} (hs1 : 1 ≤ s) (hs : s < p-1) {a : ℕ} (ha : 1 ≤ a) (ha2 : a ≤ p-1) :
    ∑ j ∈ Finset.Icc 1 (p-a-1), ((j : ZMod p)⁻¹)^s
      = (-1)^(s+1) * ∑ j ∈ Finset.Icc 1 a, ((j : ZMod p)⁻¹)^s := by
  have hsplit : ∑ j ∈ Finset.Icc 1 (p-1), ((j : ZMod p)⁻¹)^s
      = ∑ j ∈ Finset.Icc 1 (p-a-1), ((j : ZMod p)⁻¹)^s
        + ∑ j ∈ Finset.Icc (p-a) (p-1), ((j : ZMod p)⁻¹)^s := by
    rw [← Finset.sum_union]
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    · rw [Finset.disjoint_left]; intro x hx hy
      simp only [Finset.mem_Icc] at hx hy; omega
  have hw : ∑ j ∈ Finset.Icc 1 (p-1), ((j : ZMod p)⁻¹)^s = 0 := sum_inv_pow_units_zero hs1 hs
  have hreindex : ∑ j ∈ Finset.Icc (p-a) (p-1), ((j : ZMod p)⁻¹)^s
      = (-1)^s * ∑ i ∈ Finset.Icc 1 a, ((i : ZMod p)⁻¹)^s := by
    rw [Finset.mul_sum]
    apply Finset.sum_nbij' (fun j => p - j) (fun i => p - i)
    · intro j hj; simp only [Finset.mem_Icc] at *; omega
    · intro i hi; simp only [Finset.mem_Icc] at *; omega
    · intro j hj; simp only [Finset.mem_Icc] at hj; omega
    · intro i hi; simp only [Finset.mem_Icc] at hi; omega
    · intro j hj; simp only [Finset.mem_Icc] at hj
      have hc : ((p - j : ℕ) : ZMod p)⁻¹ = -((j : ZMod p)⁻¹) := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub, inv_neg]
      rw [hc, show (-(↑j:ZMod p)⁻¹)^s = (-1)^s * ((↑j:ZMod p)⁻¹)^s from neg_pow _ _, ← mul_assoc]
      rw [show ((-1:ZMod p))^s * ((-1:ZMod p))^s = 1 from by
        rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]]
      rw [one_mul]
  rw [hw, hreindex] at hsplit
  -- hsplit : 0 = H(p-a-1) + (-1)^s H(a)
  have hpow : ((-1:ZMod p))^(s+1) = -((-1:ZMod p))^s := by rw [pow_succ]; ring
  rw [hpow]
  linear_combination -hsplit

-- nested partial-harmonic sum divisible by p (s+m even)
theorem nested_HA_dvd_p [Fact p.Prime] (hp3 : 3 ≤ p) {s m : ℕ}
    (hs1 : 1 ≤ s) (hs : s < p-1) (hsm1 : 1 ≤ s+m) (hsm : s+m < p-1)
    (heven : (s+m) % 2 = 0) :
    (p : ZMod (p^9)) ∣ ∑ a ∈ Finset.Icc 1 (p-1), HAsum s (a-1) * ((a:ZMod (p^9))⁻¹)^m := by
  apply dvd_of_castHom_eq_zero (by norm_num)
  rw [map_sum]
  -- map of HAsum
  have hmapH : ∀ a ∈ Finset.Icc 1 (p-1),
      (ZMod.castHom (dvd_pow_self p (by norm_num : (9:ℕ)≠0)) (ZMod p)) (HAsum s (a-1))
        = ∑ c ∈ Finset.Icc 1 (a-1), ((c:ZMod p)⁻¹)^s := by
    intro a ha; rw [Finset.mem_Icc] at ha
    unfold HAsum
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro c hc; rw [Finset.mem_Icc] at hc
    rw [map_pow, castHom_inv_gen (by norm_num) _ (isUnit_of_lt hc.1 (by omega)), map_natCast]
  have hterm : ∀ a ∈ Finset.Icc 1 (p-1),
      (ZMod.castHom (dvd_pow_self p (by norm_num : (9:ℕ)≠0)) (ZMod p))
        (HAsum s (a-1) * ((a:ZMod (p^9))⁻¹)^m)
        = (∑ c ∈ Finset.Icc 1 (a-1), ((c:ZMod p)⁻¹)^s) * ((a:ZMod p)⁻¹)^m := by
    intro a ha
    rw [map_mul, hmapH a ha, map_pow,
        castHom_inv_gen (by norm_num) _ (isUnit_of_lt (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp ha).2),
        map_natCast]
  rw [Finset.sum_congr rfl hterm]
  -- now ZMod p goal: SU = 0
  have hrefl_term : ∀ a ∈ Finset.Icc 1 (p-1),
      (∑ c ∈ Finset.Icc 1 ((p-a)-1), ((c:ZMod p)⁻¹)^s) * (((p-a:ℕ):ZMod p)⁻¹)^m
        = (-1)^(s+m+1) * ((∑ c ∈ Finset.Icc 1 (a-1), ((c:ZMod p)⁻¹)^s) * ((a:ZMod p)⁻¹)^m
            + ((a:ZMod p)⁻¹)^(s+m)) := by
    intro a ha; rw [Finset.mem_Icc] at ha
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a-1, by omega⟩
    rw [HAp_refl hs1 hs ha.1 ha.2, Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ a'+1)]
    have hc : ((p-(a'+1):ℕ):ZMod p)⁻¹ = -(((a'+1:ℕ)):ZMod p)⁻¹ := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub, inv_neg]
    rw [hc]
    simp only [Nat.add_sub_cancel]
    ring
  have key : (∑ a ∈ Finset.Icc 1 (p-1), (∑ c ∈ Finset.Icc 1 (a-1), ((c:ZMod p)⁻¹)^s) * ((a:ZMod p)⁻¹)^m)
      = (-1)^(s+m+1) * (∑ a ∈ Finset.Icc 1 (p-1), (∑ c ∈ Finset.Icc 1 (a-1), ((c:ZMod p)⁻¹)^s) * ((a:ZMod p)⁻¹)^m) := by
    conv_lhs => rw [sum_Icc_reflect (fun a => (∑ c ∈ Finset.Icc 1 (a-1), ((c:ZMod p)⁻¹)^s) * ((a:ZMod p)⁻¹)^m)]
    rw [Finset.sum_congr rfl hrefl_term, ← Finset.mul_sum, Finset.sum_add_distrib,
        sum_inv_pow_units_zero hsm1 hsm, add_zero]
  have hev : Even (s+m) := Nat.even_iff.mpr heven
  have hpar : ((-1:ZMod p))^(s+m+1) = -1 := by
    rw [pow_succ, hev.neg_one_pow, one_mul]
  rw [hpar] at key
  have h2 : (2:ZMod p) * (∑ a ∈ Finset.Icc 1 (p-1), (∑ c ∈ Finset.Icc 1 (a-1), ((c:ZMod p)⁻¹)^s) * ((a:ZMod p)⁻¹)^m) = 0 := by
    linear_combination key
  have hne : (2:ZMod p) ≠ 0 := by
    have h2 : ((2:ℕ):ZMod p) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
      intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    simpa using h2
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h hne
  · exact h

-- separation of a double sum into product of single sums (constant C)
theorem sep_sum (C : ZMod (p^9)) (ga gb : ℕ → ZMod (p^9)) :
    (∑ a ∈ Finset.Icc 1 (p-1), ∑ b ∈ Finset.range p, C * ga a * gb b)
      = C * (∑ a ∈ Finset.Icc 1 (p-1), ga a) * (∑ b ∈ Finset.range p, gb b) := by
  have h1 : ∀ a, (∑ b ∈ Finset.range p, C * ga a * gb b) = (C * ga a) * (∑ b ∈ Finset.range p, gb b) := by
    intro a; rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun a _ => h1 a), ← Finset.sum_mul, ← Finset.mul_sum, mul_assoc]

-- Uoff separated into product-of-single-sums form
set_option maxHeartbeats 4000000 in
theorem Uoff_sep [Fact p.Prime] (hp5 : 5 ≤ p) :
    Uoff (p:=p) = ((9:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^4)*(∑ b ∈ Finset.range p, (EBb 1 b)^2*(b:ZMod (p^9))^2) + ((6:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 1 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 1 b)^2*(b:ZMod (p^9))) + ((6:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 1 b)^2) + ((6:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (EBb 1 b)^2) + ((-6:ZMod (p^9))*(p:ZMod (p^9))^7)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (EBb 1 b)^2*(b:ZMod (p^9))) + ((3:ZMod (p^9))*(p:ZMod (p^9))^6)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 1 b)^2) + ((-12:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (EBb 1 b)*(EBb 2 b)*(b:ZMod (p^9))) + ((6:ZMod (p^9))*(p:ZMod (p^9))^7)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 1 b)*(EBb 2 b)) + ((6:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 1 b)*(EBb 3 b)) + ((-12:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 2 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))) + ((-24:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^5)*(∑ b ∈ Finset.range p, (EBb 1 b)*(b:ZMod (p^9))^3) + ((-24:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 1 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (EBb 1 b)*(b:ZMod (p^9))^2) + ((-24:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (EBb 1 b)*(b:ZMod (p^9))) + ((-12:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 1 b)*(b:ZMod (p^9))) + ((-18:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^4)*(∑ b ∈ Finset.range p, (EBb 1 b)*(b:ZMod (p^9))) + ((18:ZMod (p^9))*(p:ZMod (p^9))^7)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^4)*(∑ b ∈ Finset.range p, (EBb 1 b)*(b:ZMod (p^9))^2) + ((12:ZMod (p^9))*(p:ZMod (p^9))^7*(HAsum 1 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 1 b)*(b:ZMod (p^9))) + ((12:ZMod (p^9))*(p:ZMod (p^9))^7)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 1 b)) + ((6:ZMod (p^9))*(p:ZMod (p^9))^7)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (EBb 1 b)) + ((-12:ZMod (p^9))*(p:ZMod (p^9))^6)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (EBb 1 b)*(b:ZMod (p^9))) + ((6:ZMod (p^9))*(p:ZMod (p^9))^5)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 1 b)) + ((3:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 2 b)^2) + ((18:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^4)*(∑ b ∈ Finset.range p, (EBb 2 b)*(b:ZMod (p^9))^2) + ((12:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 1 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 2 b)*(b:ZMod (p^9))) + ((12:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 2 b)) + ((6:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (EBb 2 b)) + ((-12:ZMod (p^9))*(p:ZMod (p^9))^7)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (EBb 2 b)*(b:ZMod (p^9))) + ((6:ZMod (p^9))*(p:ZMod (p^9))^6)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 2 b)) + ((-12:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (EBb 3 b)*(b:ZMod (p^9))) + ((6:ZMod (p^9))*(p:ZMod (p^9))^7)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 3 b)) + ((6:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 4 b)) + ((6:ZMod (p^9))*(p:ZMod (p^9))^8*((2:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))^2)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^2) + ((12:ZMod (p^9))*(p:ZMod (p^9))^8*((2:ZMod (p^9))⁻¹)*(HAsum 1 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))) + ((6:ZMod (p^9))*(p:ZMod (p^9))^8*((2:ZMod (p^9))⁻¹))*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (1:ZMod (p^9))) + ((-6:ZMod (p^9))*(p:ZMod (p^9))^8*((2:ZMod (p^9))⁻¹))*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (1:ZMod (p^9))) + ((12:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 2 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))) + ((6:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 3 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)) + ((15:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^6)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^4) + ((18:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 1 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^4)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^3) + ((18:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^4)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^2) + ((12:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^2) + ((6:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 3 (a-1))*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^2) + ((12:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^5)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^2) + ((3:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 1 (p-1))^2)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^2) + ((6:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 1 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))) + ((6:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 1 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))) + ((3:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (1:ZMod (p^9))) + ((6:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (1:ZMod (p^9))) + ((-6:ZMod (p^9))*(p:ZMod (p^9))^7*(HAsum 2 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (∑ d ∈ Finset.range b, (d:ZMod (p^9)))) + ((-12:ZMod (p^9))*(p:ZMod (p^9))^7)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^5)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^3) + ((-12:ZMod (p^9))*(p:ZMod (p^9))^7*(HAsum 1 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^2) + ((-12:ZMod (p^9))*(p:ZMod (p^9))^7)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))) + ((-6:ZMod (p^9))*(p:ZMod (p^9))^7)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))) + ((-6:ZMod (p^9))*(p:ZMod (p^9))^7)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^4)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))) + ((9:ZMod (p^9))*(p:ZMod (p^9))^6)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^4)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^2) + ((6:ZMod (p^9))*(p:ZMod (p^9))^6*(HAsum 1 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))) + ((6:ZMod (p^9))*(p:ZMod (p^9))^6)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (1:ZMod (p^9))) + ((2:ZMod (p^9))*(p:ZMod (p^9))^6)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (1:ZMod (p^9))) + ((-6:ZMod (p^9))*(p:ZMod (p^9))^5)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))) + ((3:ZMod (p^9))*(p:ZMod (p^9))^4)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (1:ZMod (p^9))) := by
  rw [Uoff_eq hp5, ← sep_sum ((9:ZMod (p^9))*(p:ZMod (p^9))^8) (fun a => ((a:ZMod (p^9))⁻¹)^4) (fun b => (EBb 1 b)^2*(b:ZMod (p^9))^2), ← sep_sum ((6:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 1 (p-1))) (fun a => ((a:ZMod (p^9))⁻¹)^2) (fun b => (EBb 1 b)^2*(b:ZMod (p^9))), ← sep_sum ((6:ZMod (p^9))*(p:ZMod (p^9))^8) (fun a => (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2) (fun b => (EBb 1 b)^2), ← sep_sum ((6:ZMod (p^9))*(p:ZMod (p^9))^8) (fun a => ((a:ZMod (p^9))⁻¹)^3) (fun b => (EBb 1 b)^2), ← sep_sum ((-6:ZMod (p^9))*(p:ZMod (p^9))^7) (fun a => ((a:ZMod (p^9))⁻¹)^3) (fun b => (EBb 1 b)^2*(b:ZMod (p^9))), ← sep_sum ((3:ZMod (p^9))*(p:ZMod (p^9))^6) (fun a => ((a:ZMod (p^9))⁻¹)^2) (fun b => (EBb 1 b)^2), ← sep_sum ((-12:ZMod (p^9))*(p:ZMod (p^9))^8) (fun a => ((a:ZMod (p^9))⁻¹)^3) (fun b => (EBb 1 b)*(EBb 2 b)*(b:ZMod (p^9))), ← sep_sum ((6:ZMod (p^9))*(p:ZMod (p^9))^7) (fun a => ((a:ZMod (p^9))⁻¹)^2) (fun b => (EBb 1 b)*(EBb 2 b)), ← sep_sum ((6:ZMod (p^9))*(p:ZMod (p^9))^8) (fun a => ((a:ZMod (p^9))⁻¹)^2) (fun b => (EBb 1 b)*(EBb 3 b)), ← sep_sum ((-12:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 2 (p-1))) (fun a => ((a:ZMod (p^9))⁻¹)^2) (fun b => (EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))), ← sep_sum ((-24:ZMod (p^9))*(p:ZMod (p^9))^8) (fun a => ((a:ZMod (p^9))⁻¹)^5) (fun b => (EBb 1 b)*(b:ZMod (p^9))^3), ← sep_sum ((-24:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 1 (p-1))) (fun a => ((a:ZMod (p^9))⁻¹)^3) (fun b => (EBb 1 b)*(b:ZMod (p^9))^2), ← sep_sum ((-24:ZMod (p^9))*(p:ZMod (p^9))^8) (fun a => (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^3) (fun b => (EBb 1 b)*(b:ZMod (p^9))), ← sep_sum ((-12:ZMod (p^9))*(p:ZMod (p^9))^8) (fun a => (HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)^2) (fun b => (EBb 1 b)*(b:ZMod (p^9))), ← sep_sum ((-18:ZMod (p^9))*(p:ZMod (p^9))^8) (fun a => ((a:ZMod (p^9))⁻¹)^4) (fun b => (EBb 1 b)*(b:ZMod (p^9))), ← sep_sum ((18:ZMod (p^9))*(p:ZMod (p^9))^7) (fun a => ((a:ZMod (p^9))⁻¹)^4) (fun b => (EBb 1 b)*(b:ZMod (p^9))^2), ← sep_sum ((12:ZMod (p^9))*(p:ZMod (p^9))^7*(HAsum 1 (p-1))) (fun a => ((a:ZMod (p^9))⁻¹)^2) (fun b => (EBb 1 b)*(b:ZMod (p^9))), ← sep_sum ((12:ZMod (p^9))*(p:ZMod (p^9))^7) (fun a => (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2) (fun b => (EBb 1 b)), ← sep_sum ((6:ZMod (p^9))*(p:ZMod (p^9))^7) (fun a => ((a:ZMod (p^9))⁻¹)^3) (fun b => (EBb 1 b)), ← sep_sum ((-12:ZMod (p^9))*(p:ZMod (p^9))^6) (fun a => ((a:ZMod (p^9))⁻¹)^3) (fun b => (EBb 1 b)*(b:ZMod (p^9))), ← sep_sum ((6:ZMod (p^9))*(p:ZMod (p^9))^5) (fun a => ((a:ZMod (p^9))⁻¹)^2) (fun b => (EBb 1 b)), ← sep_sum ((3:ZMod (p^9))*(p:ZMod (p^9))^8) (fun a => ((a:ZMod (p^9))⁻¹)^2) (fun b => (EBb 2 b)^2), ← sep_sum ((18:ZMod (p^9))*(p:ZMod (p^9))^8) (fun a => ((a:ZMod (p^9))⁻¹)^4) (fun b => (EBb 2 b)*(b:ZMod (p^9))^2), ← sep_sum ((12:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 1 (p-1))) (fun a => ((a:ZMod (p^9))⁻¹)^2) (fun b => (EBb 2 b)*(b:ZMod (p^9))), ← sep_sum ((12:ZMod (p^9))*(p:ZMod (p^9))^8) (fun a => (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2) (fun b => (EBb 2 b)), ← sep_sum ((6:ZMod (p^9))*(p:ZMod (p^9))^8) (fun a => ((a:ZMod (p^9))⁻¹)^3) (fun b => (EBb 2 b)), ← sep_sum ((-12:ZMod (p^9))*(p:ZMod (p^9))^7) (fun a => ((a:ZMod (p^9))⁻¹)^3) (fun b => (EBb 2 b)*(b:ZMod (p^9))), ← sep_sum ((6:ZMod (p^9))*(p:ZMod (p^9))^6) (fun a => ((a:ZMod (p^9))⁻¹)^2) (fun b => (EBb 2 b)), ← sep_sum ((-12:ZMod (p^9))*(p:ZMod (p^9))^8) (fun a => ((a:ZMod (p^9))⁻¹)^3) (fun b => (EBb 3 b)*(b:ZMod (p^9))), ← sep_sum ((6:ZMod (p^9))*(p:ZMod (p^9))^7) (fun a => ((a:ZMod (p^9))⁻¹)^2) (fun b => (EBb 3 b)), ← sep_sum ((6:ZMod (p^9))*(p:ZMod (p^9))^8) (fun a => ((a:ZMod (p^9))⁻¹)^2) (fun b => (EBb 4 b)), ← sep_sum ((6:ZMod (p^9))*(p:ZMod (p^9))^8*((2:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))^2) (fun a => ((a:ZMod (p^9))⁻¹)^2) (fun b => (b:ZMod (p^9))^2), ← sep_sum ((12:ZMod (p^9))*(p:ZMod (p^9))^8*((2:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))) (fun a => (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2) (fun b => (b:ZMod (p^9))), ← sep_sum ((6:ZMod (p^9))*(p:ZMod (p^9))^8*((2:ZMod (p^9))⁻¹)) (fun a => (HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2) (fun b => (1:ZMod (p^9))), ← sep_sum ((-6:ZMod (p^9))*(p:ZMod (p^9))^8*((2:ZMod (p^9))⁻¹)) (fun a => (HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)^2) (fun b => (1:ZMod (p^9))), ← sep_sum ((12:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 2 (p-1))) (fun a => ((a:ZMod (p^9))⁻¹)^3) (fun b => (∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))), ← sep_sum ((6:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 3 (p-1))) (fun a => ((a:ZMod (p^9))⁻¹)^2) (fun b => (∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)), ← sep_sum ((15:ZMod (p^9))*(p:ZMod (p^9))^8) (fun a => ((a:ZMod (p^9))⁻¹)^6) (fun b => (b:ZMod (p^9))^4), ← sep_sum ((18:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 1 (p-1))) (fun a => ((a:ZMod (p^9))⁻¹)^4) (fun b => (b:ZMod (p^9))^3), ← sep_sum ((18:ZMod (p^9))*(p:ZMod (p^9))^8) (fun a => (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^4) (fun b => (b:ZMod (p^9))^2), ← sep_sum ((12:ZMod (p^9))*(p:ZMod (p^9))^8) (fun a => (HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)^3) (fun b => (b:ZMod (p^9))^2), ← sep_sum ((6:ZMod (p^9))*(p:ZMod (p^9))^8) (fun a => (HAsum 3 (a-1))*((a:ZMod (p^9))⁻¹)^2) (fun b => (b:ZMod (p^9))^2), ← sep_sum ((12:ZMod (p^9))*(p:ZMod (p^9))^8) (fun a => ((a:ZMod (p^9))⁻¹)^5) (fun b => (b:ZMod (p^9))^2), ← sep_sum ((3:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 1 (p-1))^2) (fun a => ((a:ZMod (p^9))⁻¹)^2) (fun b => (b:ZMod (p^9))^2), ← sep_sum ((6:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 1 (p-1))) (fun a => (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2) (fun b => (b:ZMod (p^9))), ← sep_sum ((6:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 1 (p-1))) (fun a => ((a:ZMod (p^9))⁻¹)^3) (fun b => (b:ZMod (p^9))), ← sep_sum ((3:ZMod (p^9))*(p:ZMod (p^9))^8) (fun a => (HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2) (fun b => (1:ZMod (p^9))), ← sep_sum ((6:ZMod (p^9))*(p:ZMod (p^9))^8) (fun a => (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^3) (fun b => (1:ZMod (p^9))), ← sep_sum ((-6:ZMod (p^9))*(p:ZMod (p^9))^7*(HAsum 2 (p-1))) (fun a => ((a:ZMod (p^9))⁻¹)^2) (fun b => (∑ d ∈ Finset.range b, (d:ZMod (p^9)))), ← sep_sum ((-12:ZMod (p^9))*(p:ZMod (p^9))^7) (fun a => ((a:ZMod (p^9))⁻¹)^5) (fun b => (b:ZMod (p^9))^3), ← sep_sum ((-12:ZMod (p^9))*(p:ZMod (p^9))^7*(HAsum 1 (p-1))) (fun a => ((a:ZMod (p^9))⁻¹)^3) (fun b => (b:ZMod (p^9))^2), ← sep_sum ((-12:ZMod (p^9))*(p:ZMod (p^9))^7) (fun a => (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^3) (fun b => (b:ZMod (p^9))), ← sep_sum ((-6:ZMod (p^9))*(p:ZMod (p^9))^7) (fun a => (HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)^2) (fun b => (b:ZMod (p^9))), ← sep_sum ((-6:ZMod (p^9))*(p:ZMod (p^9))^7) (fun a => ((a:ZMod (p^9))⁻¹)^4) (fun b => (b:ZMod (p^9))), ← sep_sum ((9:ZMod (p^9))*(p:ZMod (p^9))^6) (fun a => ((a:ZMod (p^9))⁻¹)^4) (fun b => (b:ZMod (p^9))^2), ← sep_sum ((6:ZMod (p^9))*(p:ZMod (p^9))^6*(HAsum 1 (p-1))) (fun a => ((a:ZMod (p^9))⁻¹)^2) (fun b => (b:ZMod (p^9))), ← sep_sum ((6:ZMod (p^9))*(p:ZMod (p^9))^6) (fun a => (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2) (fun b => (1:ZMod (p^9))), ← sep_sum ((2:ZMod (p^9))*(p:ZMod (p^9))^6) (fun a => ((a:ZMod (p^9))⁻¹)^3) (fun b => (1:ZMod (p^9))), ← sep_sum ((-6:ZMod (p^9))*(p:ZMod (p^9))^5) (fun a => ((a:ZMod (p^9))⁻¹)^3) (fun b => (b:ZMod (p^9))), ← sep_sum ((3:ZMod (p^9))*(p:ZMod (p^9))^4) (fun a => ((a:ZMod (p^9))⁻¹)^2) (fun b => (1:ZMod (p^9)))]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  simp only [FINAL_sep]; ring

-- divisibility helpers for vanisher kills
theorem hp9z [Fact p.Prime] : (p:ZMod (p^9))^9 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

theorem eq0_of_p9 [Fact p.Prime] {x : ZMod (p^9)} (h : (p:ZMod (p^9))^9 ∣ x) : x = 0 := by
  obtain ⟨w, hw⟩ := h; rw [hw, hp9z, zero_mul]

-- a-power sums = HAsum, with divisibilities
theorem asum_eq [Fact p.Prime] (k : ℕ) :
    (∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^k) = HAsum k (p-1) := rfl

theorem wsum_dvd_p [Fact p.Prime] {s : ℕ} (hs1 : 1 ≤ s) (hs : s < p-1) :
    (p:ZMod (p^9)) ∣ HAsum s (p-1) := by
  have := sum_inv_pow_dvd_p (t:=9) (s:=s) (by norm_num) hs1 hs
  simpa [HAsum] using this

theorem sumone_eq [Fact p.Prime] : (∑ _b ∈ Finset.range p, (1:ZMod (p^9))) = (p:ZMod (p^9)) := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

theorem hasum1_dvd [Fact p.Prime] (hp5 : 5 ≤ p) : (p:ZMod (p^9))^2 ∣ HAsum 1 (p-1) := by
  have := wol_div_p2 (p:=p) hp5 (t:=9) (by norm_num)
  simpa [HAsum, pow_one] using this

theorem hasum3_dvd2 [Fact p.Prime] (hp7 : 7 ≤ p) : (p:ZMod (p^9))^2 ∣ HAsum 3 (p-1) := by
  have := wsum3_dvd_p2 (p:=p) hp7 (t:=9) (by norm_num)
  simpa [HAsum] using this

theorem hasum5_dvd2 [Fact p.Prime] (hp11 : 11 ≤ p) : (p:ZMod (p^9))^2 ∣ HAsum 5 (p-1) := by
  have := wsum5_dvd_p2 (p:=p) hp11 (t:=9) (by norm_num)
  simpa [HAsum] using this

theorem sumb1_dvd [Fact p.Prime] (hp : 3 ≤ p) : (p:ZMod (p^9)) ∣ ∑ b ∈ Finset.range p, (b:ZMod (p^9)) :=
  ⟨((p:ZMod (p^9))-1)*(2:ZMod (p^9))⁻¹, by rw [sum_b1 hp]; ring⟩

theorem sumb2_dvd [Fact p.Prime] (hp : 7 ≤ p) : (p:ZMod (p^9)) ∣ ∑ b ∈ Finset.range p, (b:ZMod (p^9))^2 :=
  ⟨((p:ZMod (p^9))-1)*(2*(p:ZMod (p^9))-1)*(6:ZMod (p^9))⁻¹, by rw [sum_b2 hp]; ring⟩

-- Uoff closed form (vanishers killed)
noncomputable def CU [Fact p.Prime] : ZMod (p^9) := (((6:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 1 b)^2)) + (((3:ZMod (p^9))*(p:ZMod (p^9))^6)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 1 b)^2)) + (((6:ZMod (p^9))*(p:ZMod (p^9))^7)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 1 b)*(EBb 2 b))) + (((18:ZMod (p^9))*(p:ZMod (p^9))^7)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^4)*(∑ b ∈ Finset.range p, (EBb 1 b)*(b:ZMod (p^9))^2)) + (((12:ZMod (p^9))*(p:ZMod (p^9))^7)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 1 b))) + (((-12:ZMod (p^9))*(p:ZMod (p^9))^6)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (EBb 1 b)*(b:ZMod (p^9)))) + (((6:ZMod (p^9))*(p:ZMod (p^9))^5)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 1 b))) + (((12:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 2 b))) + (((6:ZMod (p^9))*(p:ZMod (p^9))^6)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 2 b))) + (((6:ZMod (p^9))*(p:ZMod (p^9))^7)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 3 b))) + (((9:ZMod (p^9))*(p:ZMod (p^9))^6)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^4)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^2)) + (((6:ZMod (p^9))*(p:ZMod (p^9))^6)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (1:ZMod (p^9)))) + (((-6:ZMod (p^9))*(p:ZMod (p^9))^5)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (b:ZMod (p^9)))) + (((3:ZMod (p^9))*(p:ZMod (p^9))^4)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (1:ZMod (p^9))))

set_option maxHeartbeats 4000000 in
theorem Uoff_closed [Fact p.Prime] (hp : 11 ≤ p) : Uoff (p:=p) = CU := by
  have hp5 : 5 ≤ p := by omega
  rw [Uoff_sep hp5, CU]
  have hk0 : ((9:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^4)*(∑ b ∈ Finset.range p, (EBb 1 b)^2*(b:ZMod (p^9))^2) = 0 := by
    obtain ⟨AW, hAW⟩ := sum_inv_pow_dvd_p (t:=9) (by norm_num : (1:ℕ) ≤ 9) (by norm_num : (1:ℕ) ≤ 4) (by omega : (4:ℕ) < p - 1)
    rw [hAW]
    linear_combination (9*AW*(∑ b ∈ Finset.range p, (EBb 1 b)^2*(b:ZMod (p^9))^2)) * (hp9z (p:=p))
  have hk1 : ((6:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 1 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 1 b)^2*(b:ZMod (p^9))) = 0 := by
    obtain ⟨W_w1, hW_w1⟩ := hasum1_dvd (by omega : (5:ℕ) ≤ p)
    obtain ⟨AW, hAW⟩ := sum_inv_pow_dvd_p (t:=9) (by norm_num : (1:ℕ) ≤ 9) (by norm_num : (1:ℕ) ≤ 2) (by omega : (2:ℕ) < p - 1)
    rw [hW_w1, hAW]
    linear_combination (6*AW*(∑ b ∈ Finset.range p, (EBb 1 b)^2*(b:ZMod (p^9)))*(p:ZMod (p^9))^2*W_w1) * (hp9z (p:=p))
  have hk2 : ((6:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (EBb 1 b)^2) = 0 := by
    obtain ⟨AW, hAW⟩ := wsum3_dvd_p2 (by omega : (7:ℕ) ≤ p) (t:=9) (by norm_num)
    rw [hAW]
    linear_combination (6*AW*(∑ b ∈ Finset.range p, (EBb 1 b)^2)*(p:ZMod (p^9))) * (hp9z (p:=p))
  have hk3 : ((-6:ZMod (p^9))*(p:ZMod (p^9))^7)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (EBb 1 b)^2*(b:ZMod (p^9))) = 0 := by
    obtain ⟨AW, hAW⟩ := wsum3_dvd_p2 (by omega : (7:ℕ) ≤ p) (t:=9) (by norm_num)
    rw [hAW]
    linear_combination (-6*AW*(∑ b ∈ Finset.range p, (EBb 1 b)^2*(b:ZMod (p^9)))) * (hp9z (p:=p))
  have hk4 : ((-12:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (EBb 1 b)*(EBb 2 b)*(b:ZMod (p^9))) = 0 := by
    obtain ⟨AW, hAW⟩ := wsum3_dvd_p2 (by omega : (7:ℕ) ≤ p) (t:=9) (by norm_num)
    rw [hAW]
    linear_combination (-12*AW*(∑ b ∈ Finset.range p, (EBb 1 b)*(EBb 2 b)*(b:ZMod (p^9)))*(p:ZMod (p^9))) * (hp9z (p:=p))
  have hk5 : ((6:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 1 b)*(EBb 3 b)) = 0 := by
    obtain ⟨AW, hAW⟩ := sum_inv_pow_dvd_p (t:=9) (by norm_num : (1:ℕ) ≤ 9) (by norm_num : (1:ℕ) ≤ 2) (by omega : (2:ℕ) < p - 1)
    rw [hAW]
    linear_combination (6*AW*(∑ b ∈ Finset.range p, (EBb 1 b)*(EBb 3 b))) * (hp9z (p:=p))
  have hk6 : ((-12:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 2 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9)))) = 0 := by
    obtain ⟨W_w2, hW_w2⟩ := wsum_dvd_p (by norm_num : (1:ℕ) ≤ 2) (by omega : (2:ℕ) < p - 1)
    obtain ⟨AW, hAW⟩ := sum_inv_pow_dvd_p (t:=9) (by norm_num : (1:ℕ) ≤ 9) (by norm_num : (1:ℕ) ≤ 2) (by omega : (2:ℕ) < p - 1)
    rw [hW_w2, hAW]
    linear_combination (-12*AW*(∑ b ∈ Finset.range p, (EBb 1 b)*(∑ d ∈ Finset.range b, (d:ZMod (p^9))))*(p:ZMod (p^9))*W_w2) * (hp9z (p:=p))
  have hk7 : ((-24:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^5)*(∑ b ∈ Finset.range p, (EBb 1 b)*(b:ZMod (p^9))^3) = 0 := by
    obtain ⟨AW, hAW⟩ := wsum5_dvd_p2 (by omega : (11:ℕ) ≤ p) (t:=9) (by norm_num)
    rw [hAW]
    linear_combination (-24*AW*(∑ b ∈ Finset.range p, (EBb 1 b)*(b:ZMod (p^9))^3)*(p:ZMod (p^9))) * (hp9z (p:=p))
  have hk8 : ((-24:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 1 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (EBb 1 b)*(b:ZMod (p^9))^2) = 0 := by
    obtain ⟨W_w1, hW_w1⟩ := hasum1_dvd (by omega : (5:ℕ) ≤ p)
    obtain ⟨AW, hAW⟩ := wsum3_dvd_p2 (by omega : (7:ℕ) ≤ p) (t:=9) (by norm_num)
    rw [hW_w1, hAW]
    linear_combination (-24*AW*(∑ b ∈ Finset.range p, (EBb 1 b)*(b:ZMod (p^9))^2)*(p:ZMod (p^9))^3*W_w1) * (hp9z (p:=p))
  have hk9 : ((-24:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (EBb 1 b)*(b:ZMod (p^9))) = 0 := by
    obtain ⟨AW, hAW⟩ := nested_HA_dvd_p (s:=1) (m:=3) (by omega : (3:ℕ) ≤ p) (by norm_num) (by omega) (by norm_num) (by omega) (by norm_num)
    rw [hAW]
    linear_combination (-24*AW*(∑ b ∈ Finset.range p, (EBb 1 b)*(b:ZMod (p^9)))) * (hp9z (p:=p))
  have hk10 : ((-12:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 1 b)*(b:ZMod (p^9))) = 0 := by
    obtain ⟨AW, hAW⟩ := nested_HA_dvd_p (s:=2) (m:=2) (by omega : (3:ℕ) ≤ p) (by norm_num) (by omega) (by norm_num) (by omega) (by norm_num)
    rw [hAW]
    linear_combination (-12*AW*(∑ b ∈ Finset.range p, (EBb 1 b)*(b:ZMod (p^9)))) * (hp9z (p:=p))
  have hk11 : ((-18:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^4)*(∑ b ∈ Finset.range p, (EBb 1 b)*(b:ZMod (p^9))) = 0 := by
    obtain ⟨AW, hAW⟩ := sum_inv_pow_dvd_p (t:=9) (by norm_num : (1:ℕ) ≤ 9) (by norm_num : (1:ℕ) ≤ 4) (by omega : (4:ℕ) < p - 1)
    rw [hAW]
    linear_combination (-18*AW*(∑ b ∈ Finset.range p, (EBb 1 b)*(b:ZMod (p^9)))) * (hp9z (p:=p))
  have hk12 : ((12:ZMod (p^9))*(p:ZMod (p^9))^7*(HAsum 1 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 1 b)*(b:ZMod (p^9))) = 0 := by
    obtain ⟨W_w1, hW_w1⟩ := hasum1_dvd (by omega : (5:ℕ) ≤ p)
    obtain ⟨AW, hAW⟩ := sum_inv_pow_dvd_p (t:=9) (by norm_num : (1:ℕ) ≤ 9) (by norm_num : (1:ℕ) ≤ 2) (by omega : (2:ℕ) < p - 1)
    rw [hW_w1, hAW]
    linear_combination (12*AW*(∑ b ∈ Finset.range p, (EBb 1 b)*(b:ZMod (p^9)))*(p:ZMod (p^9))*W_w1) * (hp9z (p:=p))
  have hk13 : ((6:ZMod (p^9))*(p:ZMod (p^9))^7)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (EBb 1 b)) = 0 := by
    obtain ⟨AW, hAW⟩ := wsum3_dvd_p2 (by omega : (7:ℕ) ≤ p) (t:=9) (by norm_num)
    rw [hAW]
    linear_combination (6*AW*(∑ b ∈ Finset.range p, (EBb 1 b))) * (hp9z (p:=p))
  have hk14 : ((3:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 2 b)^2) = 0 := by
    obtain ⟨AW, hAW⟩ := sum_inv_pow_dvd_p (t:=9) (by norm_num : (1:ℕ) ≤ 9) (by norm_num : (1:ℕ) ≤ 2) (by omega : (2:ℕ) < p - 1)
    rw [hAW]
    linear_combination (3*AW*(∑ b ∈ Finset.range p, (EBb 2 b)^2)) * (hp9z (p:=p))
  have hk15 : ((18:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^4)*(∑ b ∈ Finset.range p, (EBb 2 b)*(b:ZMod (p^9))^2) = 0 := by
    obtain ⟨AW, hAW⟩ := sum_inv_pow_dvd_p (t:=9) (by norm_num : (1:ℕ) ≤ 9) (by norm_num : (1:ℕ) ≤ 4) (by omega : (4:ℕ) < p - 1)
    rw [hAW]
    linear_combination (18*AW*(∑ b ∈ Finset.range p, (EBb 2 b)*(b:ZMod (p^9))^2)) * (hp9z (p:=p))
  have hk16 : ((12:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 1 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 2 b)*(b:ZMod (p^9))) = 0 := by
    obtain ⟨W_w1, hW_w1⟩ := hasum1_dvd (by omega : (5:ℕ) ≤ p)
    obtain ⟨AW, hAW⟩ := sum_inv_pow_dvd_p (t:=9) (by norm_num : (1:ℕ) ≤ 9) (by norm_num : (1:ℕ) ≤ 2) (by omega : (2:ℕ) < p - 1)
    rw [hW_w1, hAW]
    linear_combination (12*AW*(∑ b ∈ Finset.range p, (EBb 2 b)*(b:ZMod (p^9)))*(p:ZMod (p^9))^2*W_w1) * (hp9z (p:=p))
  have hk17 : ((6:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (EBb 2 b)) = 0 := by
    obtain ⟨AW, hAW⟩ := wsum3_dvd_p2 (by omega : (7:ℕ) ≤ p) (t:=9) (by norm_num)
    rw [hAW]
    linear_combination (6*AW*(∑ b ∈ Finset.range p, (EBb 2 b))*(p:ZMod (p^9))) * (hp9z (p:=p))
  have hk18 : ((-12:ZMod (p^9))*(p:ZMod (p^9))^7)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (EBb 2 b)*(b:ZMod (p^9))) = 0 := by
    obtain ⟨AW, hAW⟩ := wsum3_dvd_p2 (by omega : (7:ℕ) ≤ p) (t:=9) (by norm_num)
    rw [hAW]
    linear_combination (-12*AW*(∑ b ∈ Finset.range p, (EBb 2 b)*(b:ZMod (p^9)))) * (hp9z (p:=p))
  have hk19 : ((-12:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (EBb 3 b)*(b:ZMod (p^9))) = 0 := by
    obtain ⟨AW, hAW⟩ := wsum3_dvd_p2 (by omega : (7:ℕ) ≤ p) (t:=9) (by norm_num)
    rw [hAW]
    linear_combination (-12*AW*(∑ b ∈ Finset.range p, (EBb 3 b)*(b:ZMod (p^9)))*(p:ZMod (p^9))) * (hp9z (p:=p))
  have hk20 : ((6:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (EBb 4 b)) = 0 := by
    obtain ⟨AW, hAW⟩ := sum_inv_pow_dvd_p (t:=9) (by norm_num : (1:ℕ) ≤ 9) (by norm_num : (1:ℕ) ≤ 2) (by omega : (2:ℕ) < p - 1)
    rw [hAW]
    linear_combination (6*AW*(∑ b ∈ Finset.range p, (EBb 4 b))) * (hp9z (p:=p))
  have hk21 : ((6:ZMod (p^9))*(p:ZMod (p^9))^8*((2:ZMod (p^9))⁻¹)*(HAsum 1 (p-1))^2)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^2) = 0 := by
    obtain ⟨W_w1, hW_w1⟩ := hasum1_dvd (by omega : (5:ℕ) ≤ p)
    obtain ⟨AW, hAW⟩ := sum_inv_pow_dvd_p (t:=9) (by norm_num : (1:ℕ) ≤ 9) (by norm_num : (1:ℕ) ≤ 2) (by omega : (2:ℕ) < p - 1)
    rw [hW_w1, hAW]
    linear_combination (6*AW*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^2)*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))^4*W_w1^2) * (hp9z (p:=p))
  have hk22 : ((12:ZMod (p^9))*(p:ZMod (p^9))^8*((2:ZMod (p^9))⁻¹)*(HAsum 1 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))) = 0 := by
    obtain ⟨W_w1, hW_w1⟩ := hasum1_dvd (by omega : (5:ℕ) ≤ p)
    rw [hW_w1]
    linear_combination (12*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (b:ZMod (p^9)))*((2:ZMod (p^9))⁻¹)*(p:ZMod (p^9))*W_w1) * (hp9z (p:=p))
  have hk23 : ((6:ZMod (p^9))*(p:ZMod (p^9))^8*((2:ZMod (p^9))⁻¹))*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (1:ZMod (p^9))) = 0 := by
    rw [sumone_eq]
    linear_combination (6*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2)*((2:ZMod (p^9))⁻¹)) * (hp9z (p:=p))
  have hk24 : ((-6:ZMod (p^9))*(p:ZMod (p^9))^8*((2:ZMod (p^9))⁻¹))*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (1:ZMod (p^9))) = 0 := by
    obtain ⟨AW, hAW⟩ := nested_HA_dvd_p (s:=2) (m:=2) (by omega : (3:ℕ) ≤ p) (by norm_num) (by omega) (by norm_num) (by omega) (by norm_num)
    rw [hAW]
    linear_combination (-6*AW*(∑ b ∈ Finset.range p, (1:ZMod (p^9)))*((2:ZMod (p^9))⁻¹)) * (hp9z (p:=p))
  have hk25 : ((12:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 2 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9))) = 0 := by
    obtain ⟨W_w2, hW_w2⟩ := wsum_dvd_p (by norm_num : (1:ℕ) ≤ 2) (by omega : (2:ℕ) < p - 1)
    obtain ⟨AW, hAW⟩ := wsum3_dvd_p2 (by omega : (7:ℕ) ≤ p) (t:=9) (by norm_num)
    rw [hW_w2, hAW]
    linear_combination (12*AW*(∑ b ∈ Finset.range p, (∑ d ∈ Finset.range b, (d:ZMod (p^9)))*(b:ZMod (p^9)))*(p:ZMod (p^9))^2*W_w2) * (hp9z (p:=p))
  have hk26 : ((6:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 3 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (∑ d ∈ Finset.range b, (d:ZMod (p^9))^2)) = 0 := by
    obtain ⟨W_w3, hW_w3⟩ := wsum_dvd_p (by norm_num : (1:ℕ) ≤ 3) (by omega : (3:ℕ) < p - 1)
    obtain ⟨AW, hAW⟩ := sum_inv_pow_dvd_p (t:=9) (by norm_num : (1:ℕ) ≤ 9) (by norm_num : (1:ℕ) ≤ 2) (by omega : (2:ℕ) < p - 1)
    rw [hW_w3, hAW]
    linear_combination (6*AW*(∑ b ∈ Finset.range p, (∑ d ∈ Finset.range b, (d:ZMod (p^9))^2))*(p:ZMod (p^9))*W_w3) * (hp9z (p:=p))
  have hk27 : ((15:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^6)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^4) = 0 := by
    obtain ⟨AW, hAW⟩ := sum_inv_pow_dvd_p (t:=9) (by norm_num : (1:ℕ) ≤ 9) (by norm_num : (1:ℕ) ≤ 6) (by omega : (6:ℕ) < p - 1)
    rw [hAW]
    linear_combination (15*AW*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^4)) * (hp9z (p:=p))
  have hk28 : ((18:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 1 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^4)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^3) = 0 := by
    obtain ⟨W_w1, hW_w1⟩ := hasum1_dvd (by omega : (5:ℕ) ≤ p)
    obtain ⟨AW, hAW⟩ := sum_inv_pow_dvd_p (t:=9) (by norm_num : (1:ℕ) ≤ 9) (by norm_num : (1:ℕ) ≤ 4) (by omega : (4:ℕ) < p - 1)
    rw [hW_w1, hAW]
    linear_combination (18*AW*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^3)*(p:ZMod (p^9))^2*W_w1) * (hp9z (p:=p))
  have hk29 : ((18:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^4)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^2) = 0 := by
    obtain ⟨BW, hBW⟩ := sumb2_dvd (by omega : (7:ℕ) ≤ p)
    rw [hBW]
    linear_combination (18*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^4)*BW) * (hp9z (p:=p))
  have hk30 : ((12:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^2) = 0 := by
    obtain ⟨BW, hBW⟩ := sumb2_dvd (by omega : (7:ℕ) ≤ p)
    rw [hBW]
    linear_combination (12*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)^3)*BW) * (hp9z (p:=p))
  have hk31 : ((6:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 3 (a-1))*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^2) = 0 := by
    obtain ⟨BW, hBW⟩ := sumb2_dvd (by omega : (7:ℕ) ≤ p)
    rw [hBW]
    linear_combination (6*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 3 (a-1))*((a:ZMod (p^9))⁻¹)^2)*BW) * (hp9z (p:=p))
  have hk32 : ((12:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^5)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^2) = 0 := by
    obtain ⟨AW, hAW⟩ := wsum5_dvd_p2 (by omega : (11:ℕ) ≤ p) (t:=9) (by norm_num)
    rw [hAW]
    linear_combination (12*AW*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^2)*(p:ZMod (p^9))) * (hp9z (p:=p))
  have hk33 : ((3:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 1 (p-1))^2)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^2) = 0 := by
    obtain ⟨W_w1, hW_w1⟩ := hasum1_dvd (by omega : (5:ℕ) ≤ p)
    obtain ⟨AW, hAW⟩ := sum_inv_pow_dvd_p (t:=9) (by norm_num : (1:ℕ) ≤ 9) (by norm_num : (1:ℕ) ≤ 2) (by omega : (2:ℕ) < p - 1)
    rw [hW_w1, hAW]
    linear_combination (3*AW*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^2)*(p:ZMod (p^9))^4*W_w1^2) * (hp9z (p:=p))
  have hk34 : ((6:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 1 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))) = 0 := by
    obtain ⟨W_w1, hW_w1⟩ := hasum1_dvd (by omega : (5:ℕ) ≤ p)
    rw [hW_w1]
    linear_combination (6*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (b:ZMod (p^9)))*(p:ZMod (p^9))*W_w1) * (hp9z (p:=p))
  have hk35 : ((6:ZMod (p^9))*(p:ZMod (p^9))^8*(HAsum 1 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))) = 0 := by
    obtain ⟨W_w1, hW_w1⟩ := hasum1_dvd (by omega : (5:ℕ) ≤ p)
    obtain ⟨AW, hAW⟩ := wsum3_dvd_p2 (by omega : (7:ℕ) ≤ p) (t:=9) (by norm_num)
    rw [hW_w1, hAW]
    linear_combination (6*AW*(∑ b ∈ Finset.range p, (b:ZMod (p^9)))*(p:ZMod (p^9))^3*W_w1) * (hp9z (p:=p))
  have hk36 : ((3:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (1:ZMod (p^9))) = 0 := by
    rw [sumone_eq]
    linear_combination (3*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))^2*((a:ZMod (p^9))⁻¹)^2)) * (hp9z (p:=p))
  have hk37 : ((6:ZMod (p^9))*(p:ZMod (p^9))^8)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (1:ZMod (p^9))) = 0 := by
    obtain ⟨AW, hAW⟩ := nested_HA_dvd_p (s:=1) (m:=3) (by omega : (3:ℕ) ≤ p) (by norm_num) (by omega) (by norm_num) (by omega) (by norm_num)
    rw [hAW]
    linear_combination (6*AW*(∑ b ∈ Finset.range p, (1:ZMod (p^9)))) * (hp9z (p:=p))
  have hk38 : ((-6:ZMod (p^9))*(p:ZMod (p^9))^7*(HAsum 2 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (∑ d ∈ Finset.range b, (d:ZMod (p^9)))) = 0 := by
    obtain ⟨W_w2, hW_w2⟩ := wsum_dvd_p (by norm_num : (1:ℕ) ≤ 2) (by omega : (2:ℕ) < p - 1)
    obtain ⟨AW, hAW⟩ := sum_inv_pow_dvd_p (t:=9) (by norm_num : (1:ℕ) ≤ 9) (by norm_num : (1:ℕ) ≤ 2) (by omega : (2:ℕ) < p - 1)
    rw [hW_w2, hAW]
    linear_combination (-6*AW*(∑ b ∈ Finset.range p, (∑ d ∈ Finset.range b, (d:ZMod (p^9))))*W_w2) * (hp9z (p:=p))
  have hk39 : ((-12:ZMod (p^9))*(p:ZMod (p^9))^7)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^5)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^3) = 0 := by
    obtain ⟨AW, hAW⟩ := wsum5_dvd_p2 (by omega : (11:ℕ) ≤ p) (t:=9) (by norm_num)
    rw [hAW]
    linear_combination (-12*AW*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^3)) * (hp9z (p:=p))
  have hk40 : ((-12:ZMod (p^9))*(p:ZMod (p^9))^7*(HAsum 1 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^2) = 0 := by
    obtain ⟨W_w1, hW_w1⟩ := hasum1_dvd (by omega : (5:ℕ) ≤ p)
    obtain ⟨AW, hAW⟩ := wsum3_dvd_p2 (by omega : (7:ℕ) ≤ p) (t:=9) (by norm_num)
    rw [hW_w1, hAW]
    linear_combination (-12*AW*(∑ b ∈ Finset.range p, (b:ZMod (p^9))^2)*(p:ZMod (p^9))^2*W_w1) * (hp9z (p:=p))
  have hk41 : ((-12:ZMod (p^9))*(p:ZMod (p^9))^7)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 1 (a-1))*((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))) = 0 := by
    obtain ⟨AW, hAW⟩ := nested_HA_dvd_p (s:=1) (m:=3) (by omega : (3:ℕ) ≤ p) (by norm_num) (by omega) (by norm_num) (by omega) (by norm_num)
    obtain ⟨BW, hBW⟩ := sumb1_dvd (by omega : (3:ℕ) ≤ p)
    rw [hAW, hBW]
    linear_combination (-12*AW*BW) * (hp9z (p:=p))
  have hk42 : ((-6:ZMod (p^9))*(p:ZMod (p^9))^7)*(∑ a ∈ Finset.Icc 1 (p-1), (HAsum 2 (a-1))*((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))) = 0 := by
    obtain ⟨AW, hAW⟩ := nested_HA_dvd_p (s:=2) (m:=2) (by omega : (3:ℕ) ≤ p) (by norm_num) (by omega) (by norm_num) (by omega) (by norm_num)
    obtain ⟨BW, hBW⟩ := sumb1_dvd (by omega : (3:ℕ) ≤ p)
    rw [hAW, hBW]
    linear_combination (-6*AW*BW) * (hp9z (p:=p))
  have hk43 : ((-6:ZMod (p^9))*(p:ZMod (p^9))^7)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^4)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))) = 0 := by
    obtain ⟨AW, hAW⟩ := sum_inv_pow_dvd_p (t:=9) (by norm_num : (1:ℕ) ≤ 9) (by norm_num : (1:ℕ) ≤ 4) (by omega : (4:ℕ) < p - 1)
    obtain ⟨BW, hBW⟩ := sumb1_dvd (by omega : (3:ℕ) ≤ p)
    rw [hAW, hBW]
    linear_combination (-6*AW*BW) * (hp9z (p:=p))
  have hk44 : ((6:ZMod (p^9))*(p:ZMod (p^9))^6*(HAsum 1 (p-1)))*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^2)*(∑ b ∈ Finset.range p, (b:ZMod (p^9))) = 0 := by
    obtain ⟨W_w1, hW_w1⟩ := hasum1_dvd (by omega : (5:ℕ) ≤ p)
    obtain ⟨AW, hAW⟩ := sum_inv_pow_dvd_p (t:=9) (by norm_num : (1:ℕ) ≤ 9) (by norm_num : (1:ℕ) ≤ 2) (by omega : (2:ℕ) < p - 1)
    rw [hW_w1, hAW]
    linear_combination (6*AW*(∑ b ∈ Finset.range p, (b:ZMod (p^9)))*W_w1) * (hp9z (p:=p))
  have hk45 : ((2:ZMod (p^9))*(p:ZMod (p^9))^6)*(∑ a ∈ Finset.Icc 1 (p-1), ((a:ZMod (p^9))⁻¹)^3)*(∑ b ∈ Finset.range p, (1:ZMod (p^9))) = 0 := by
    obtain ⟨AW, hAW⟩ := wsum3_dvd_p2 (by omega : (7:ℕ) ≤ p) (t:=9) (by norm_num)
    rw [hAW, sumone_eq]
    linear_combination (2*AW) * (hp9z (p:=p))
  rw [hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8, hk9, hk10, hk11, hk12, hk13, hk14, hk15, hk16, hk17, hk18, hk19, hk20, hk21, hk22, hk23, hk24, hk25, hk26, hk27, hk28, hk29, hk30, hk31, hk32, hk33, hk34, hk35, hk36, hk37, hk38, hk39, hk40, hk41, hk42, hk43, hk44, hk45]
  ring

-- Gl product expansion (gamma elem symmetric)
noncomputable def Sset (l : ℕ) : Finset ℕ := (Finset.range (p*l)).filter (fun i => ¬ p ∣ i)
noncomputable def gam (s l : ℕ) : ZMod (p^9) := ∑ i ∈ Sset (p:=p) l, ((i:ZMod (p^9))⁻¹)^s
noncomputable def esg (j l : ℕ) : ZMod (p^9) := ∑ T ∈ (Sset (p:=p) l).powersetCard j, ∏ i ∈ T, (i:ZMod (p^9))⁻¹

theorem Gl_eq [Fact p.Prime] (l : ℕ) :
    (∏ i ∈ Sset (p:=p) l, (1 + (p:ZMod (p^9))^2 * (i:ZMod (p^9))⁻¹))
      = ∑ j ∈ Finset.range 5, ((p:ZMod (p^9))^2)^j * esg (p:=p) j l := by
  have hd := B_expansion (p:=p) (t:=9) (Sset (p:=p) l) (fun i => (i:ZMod (p^9))⁻¹) ((p:ZMod (p^9))^2)
  have hz : ((p:ZMod (p^9))^2)^5 = 0 := by
    have he : ((p:ZMod (p^9))^2)^5 = (p:ZMod (p^9))^9 * p := by ring
    rw [he, hp9z, zero_mul]
  rw [hz] at hd
  have := (zero_dvd_iff.mp hd)
  simp only [esg]
  linear_combination this

-- survivor b-sum evaluations
theorem EBb1_Hsum (b : ℕ) : EBb (p:=p) 1 b = Hsum b := by
  rw [EBb1]; simp only [Bpow, Hsum, pow_one]

theorem bsv_E1 [Fact p.Prime] :
    ∑ b ∈ Finset.range p, EBb (p:=p) 1 b = (p:ZMod (p^9)) * wsum 1 - ((p-1:ℕ):ZMod (p^9)) := by
  simp only [EBb1_Hsum]; exact sum_Hsum

theorem bsv_E1sq [Fact p.Prime] (hp : 2 ≤ p) :
    ∑ b ∈ Finset.range p, (EBb (p:=p) 1 b)^2
      = (p:ZMod (p^9)) * (wsum 1)^2 - (2*(p:ZMod (p^9))-1) * wsum 1 + 2*((p-1:ℕ):ZMod (p^9)) := by
  simp only [EBb1_Hsum]; exact sum_Hsq hp

theorem bsv_E1b [Fact p.Prime] (hp : 3 ≤ p) :
    ∑ b ∈ Finset.range p, EBb (p:=p) 1 b * (b:ZMod (p^9))
      = (p:ZMod (p^9))*((p-1:ℕ):ZMod (p^9))*(2:ZMod (p^9))⁻¹ * wsum 1
        - ((p-1:ℕ):ZMod (p^9))*((p-2:ℕ):ZMod (p^9))*(2:ZMod (p^9))⁻¹*(2:ZMod (p^9))⁻¹ := by
  simp only [EBb1_Hsum]; exact sum_B1b hp

theorem bsv_E1b2 [Fact p.Prime] (hp : 7 ≤ p) :
    ∑ b ∈ Finset.range p, EBb (p:=p) 1 b * (b:ZMod (p^9))^2
      = (p:ZMod (p^9))*((p-1:ℕ):ZMod (p^9))*((2*p-1:ℕ):ZMod (p^9))*(6:ZMod (p^9))⁻¹ * wsum 1
        - ((p-1:ℕ):ZMod (p^9))*((p-2:ℕ):ZMod (p^9))*((4*p-3:ℕ):ZMod (p^9))*(6:ZMod (p^9))⁻¹*(6:ZMod (p^9))⁻¹ := by
  simp only [EBb1_Hsum]; exact sum_B1b2 hp

theorem bsv_E2 [Fact p.Prime] (hp : 2 ≤ p) :
    (2:ZMod (p^9)) * (∑ b ∈ Finset.range p, EBb (p:=p) 2 b)
      = ((p:ZMod (p^9)) * (wsum 1)^2 - (2*(p:ZMod (p^9))-1) * wsum 1 + 2*((p-1:ℕ):ZMod (p^9)))
        - ((p:ZMod (p^9)) * wsum 2 - wsum 1) := by
  rw [Finset.mul_sum]
  rw [show (∑ b ∈ Finset.range p, (2:ZMod (p^9)) * EBb (p:=p) 2 b)
        = ∑ b ∈ Finset.range p, ((Bpow 1 b)^2 - Bpow 2 b) from by
      apply Finset.sum_congr rfl; intro b _; rw [EBb2]]
  rw [Finset.sum_sub_distrib]
  rw [show (∑ b ∈ Finset.range p, (Bpow (p:=p) 1 b)^2) = ∑ b ∈ Finset.range p, (Hsum b)^2 from by
      apply Finset.sum_congr rfl; intro b _; rw [show Bpow (p:=p) 1 b = Hsum b from by simp only [Bpow, Hsum, pow_one]]]
  rw [sum_Hsq hp, sum_Bpow2]

theorem bsv_E1E2 [Fact p.Prime] (hp : 3 ≤ p) :
    (2:ZMod (p^9)) * (∑ b ∈ Finset.range p, EBb (p:=p) 1 b * EBb (p:=p) 2 b)
      = (∑ b ∈ Finset.range p, (Bpow (p:=p) 1 b)^3) - (∑ b ∈ Finset.range p, Bpow (p:=p) 1 b * Bpow (p:=p) 2 b) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro b _
  have h2 := EBb2 (p:=p) b
  have h1 := EBb1 (p:=p) b
  linear_combination (EBb (p:=p) 1 b) * h2 + ((Bpow (p:=p) 1 b)^2 - Bpow (p:=p) 2 b) * h1

theorem bsv_E3 [Fact p.Prime] (hp : 3 ≤ p) :
    (6:ZMod (p^9)) * (∑ b ∈ Finset.range p, EBb (p:=p) 3 b)
      = (∑ b ∈ Finset.range p, (Bpow (p:=p) 1 b)^3)
        - 3*(∑ b ∈ Finset.range p, Bpow (p:=p) 1 b * Bpow (p:=p) 2 b)
        + 2*(∑ b ∈ Finset.range p, Bpow (p:=p) 3 b) := by
  have key : ∑ b ∈ Finset.range p, (6:ZMod (p^9)) * EBb (p:=p) 3 b
      = ∑ b ∈ Finset.range p, ((Bpow (p:=p) 1 b)^3 - 3*(Bpow (p:=p) 1 b * Bpow (p:=p) 2 b) + 2*Bpow (p:=p) 3 b) := by
    apply Finset.sum_congr rfl; intro b _; linear_combination EBb3 (p:=p) b
  rw [Finset.mul_sum, key, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

-- gam block reindex + exact geometric inverse

theorem geo_inv [Fact p.Prime] (c d : ℕ) (hc : IsUnit ((c:ZMod (p^9)))) :
    (((c:ZMod (p^9)) + (p:ZMod (p^9)) * (d:ZMod (p^9)))⁻¹)
      = ∑ k ∈ Finset.range 9, (-1)^k * ((p:ZMod (p^9))*(d:ZMod (p^9)))^k * ((c:ZMod (p^9))⁻¹)^(k+1) := by
  set ci := ((c:ZMod (p^9)))⁻¹ with hci
  have hcci : (c:ZMod (p^9)) * ci = 1 := ZMod.mul_inv_of_unit _ hc
  set x : ZMod (p^9) := -(((p:ZMod (p^9))*(d:ZMod (p^9)))*ci) with hx
  set G : ZMod (p^9) := ∑ k ∈ Finset.range 9, x^k with hG
  -- S = ci * G
  have hSeq : (∑ k ∈ Finset.range 9, (-1:ZMod (p^9))^k * ((p:ZMod (p^9))*(d:ZMod (p^9)))^k * ci^(k+1))
      = ci * G := by
    rw [hG, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hx, neg_pow, mul_pow]
    ring
  rw [hSeq]
  -- (c+pd) * (ci*G) = 1
  have hx9 : x^9 = 0 := by
    rw [hx]; rw [neg_pow]
    have : (((p:ZMod (p^9))*(d:ZMod (p^9)))*ci)^9 = (p:ZMod (p^9))^9 * ((d:ZMod (p^9))^9 * ci^9) := by ring
    rw [this, hp9z]; ring
  have hgeom : G * (x - 1) = x^9 - 1 := by rw [hG]; exact geom_sum_mul x 9
  have hmul : ((c:ZMod (p^9)) + (p:ZMod (p^9)) * (d:ZMod (p^9))) * (ci * G) = 1 := by
    have hcpd : ((c:ZMod (p^9)) + (p:ZMod (p^9)) * (d:ZMod (p^9))) * ci = 1 - x := by
      rw [hx]; linear_combination hcci
    calc ((c:ZMod (p^9)) + (p:ZMod (p^9)) * (d:ZMod (p^9))) * (ci * G)
        = (((c:ZMod (p^9)) + (p:ZMod (p^9)) * (d:ZMod (p^9))) * ci) * G := by ring
      _ = (1 - x) * G := by rw [hcpd]
      _ = -(G * (x - 1)) := by ring
      _ = -(x^9 - 1) := by rw [hgeom]
      _ = 1 := by rw [hx9]; ring
  have hunit : IsUnit ((c:ZMod (p^9)) + (p:ZMod (p^9)) * (d:ZMod (p^9))) := isUnit_of_mul_eq_one _ hmul
  calc ((c:ZMod (p^9)) + (p:ZMod (p^9)) * (d:ZMod (p^9)))⁻¹
      = ((c:ZMod (p^9)) + (p:ZMod (p^9)) * (d:ZMod (p^9)))⁻¹ * (((c:ZMod (p^9)) + (p:ZMod (p^9)) * (d:ZMod (p^9))) * (ci * G)) := by rw [hmul, mul_one]
    _ = (((c:ZMod (p^9)) + (p:ZMod (p^9)) * (d:ZMod (p^9)))⁻¹ * ((c:ZMod (p^9)) + (p:ZMod (p^9)) * (d:ZMod (p^9)))) * (ci * G) := by ring
    _ = 1 * (ci * G) := by rw [ZMod.inv_mul_of_unit _ hunit]
    _ = ci * G := one_mul _

-- power-inverse negative-binomial expansion machinery
theorem hockey (s u : ℕ) :
    ∑ t ∈ Finset.range (u+1), Nat.choose (s+t-1) t = Nat.choose (s+u) u := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [Finset.sum_range_succ, ih]
    have : s + (u+1) - 1 = s + u := by omega
    rw [this, show s+(u+1) = (s+u)+1 from by ring, Nat.choose_succ_succ]


theorem conv_geom [Fact p.Prime] (a : ℕ → ZMod (p^9)) (X : ZMod (p^9)) (hX : X^9 = 0) :
    (∑ t ∈ Finset.range 9, a t * X^t) * (∑ k ∈ Finset.range 9, X^k)
      = ∑ u ∈ Finset.range 9, (∑ t ∈ Finset.range (u+1), a t) * X^u := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linear_combination (((1)*(a 8))*X^7 + ((1)*(a 7) + (1)*(a 8))*X^6 + ((1)*(a 6) + (1)*(a 7) + (1)*(a 8))*X^5 + ((1)*(a 5) + (1)*(a 6) + (1)*(a 7) + (1)*(a 8))*X^4 + ((1)*(a 4) + (1)*(a 5) + (1)*(a 6) + (1)*(a 7) + (1)*(a 8))*X^3 + ((1)*(a 3) + (1)*(a 4) + (1)*(a 5) + (1)*(a 6) + (1)*(a 7) + (1)*(a 8))*X^2 + ((1)*(a 2) + (1)*(a 3) + (1)*(a 4) + (1)*(a 5) + (1)*(a 6) + (1)*(a 7) + (1)*(a 8))*X^1 + ((1)*(a 1) + (1)*(a 2) + (1)*(a 3) + (1)*(a 4) + (1)*(a 5) + (1)*(a 6) + (1)*(a 7) + (1)*(a 8))*X^0) * hX

theorem pow_inv_expand [Fact p.Prime] (s c d : ℕ) (hc : IsUnit ((c:ZMod (p^9)))) :
    (((c:ZMod (p^9)) + (p:ZMod (p^9))*(d:ZMod (p^9)))⁻¹)^s
      = ∑ t ∈ Finset.range 9, (-1:ZMod (p^9))^t * (Nat.choose (s+t-1) t : ZMod (p^9))
          * ((p:ZMod (p^9)))^t * (d:ZMod (p^9))^t * ((c:ZMod (p^9))⁻¹)^(s+t) := by
  induction s with
  | zero =>
    simp only [pow_zero, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.choose]
  | succ s ih =>
    have hps : (((c:ZMod (p^9)) + (p:ZMod (p^9))*(d:ZMod (p^9)))⁻¹)^(s+1)
        = (((c:ZMod (p^9)) + (p:ZMod (p^9))*(d:ZMod (p^9)))⁻¹)^s * (((c:ZMod (p^9)) + (p:ZMod (p^9))*(d:ZMod (p^9)))⁻¹) := pow_succ _ _
    rw [hps, ih, geo_inv c d hc]
    set ci := ((c:ZMod (p^9)))⁻¹ with hci
    set X : ZMod (p^9) := -(((p:ZMod (p^9))*(d:ZMod (p^9)))*ci) with hX
    have hX9 : X^9 = 0 := by
      rw [hX, neg_pow]
      have : (((p:ZMod (p^9))*(d:ZMod (p^9)))*ci)^9 = (p:ZMod (p^9))^9 * ((d:ZMod (p^9))^9 * ci^9) := by ring
      rw [this, hp9z]; ring
    have e1 : (∑ t ∈ Finset.range 9, (-1:ZMod (p^9))^t * (Nat.choose (s+t-1) t : ZMod (p^9))
                * ((p:ZMod (p^9)))^t * (d:ZMod (p^9))^t * ci^(s+t))
              = ci^s * ∑ t ∈ Finset.range 9, (Nat.choose (s+t-1) t : ZMod (p^9)) * X^t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [hX, pow_add]; ring
    have e2 : (∑ k ∈ Finset.range 9, (-1:ZMod (p^9))^k * ((p:ZMod (p^9))*(d:ZMod (p^9)))^k * ci^(k+1))
              = ci * ∑ k ∈ Finset.range 9, X^k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [hX]; ring
    rw [e1, e2]
    have reshape : (ci^s * ∑ t ∈ Finset.range 9, (Nat.choose (s+t-1) t : ZMod (p^9)) * X^t) * (ci * ∑ k ∈ Finset.range 9, X^k)
        = ci^(s+1) * ((∑ t ∈ Finset.range 9, (Nat.choose (s+t-1) t : ZMod (p^9)) * X^t) * (∑ k ∈ Finset.range 9, X^k)) := by ring
    rw [reshape, conv_geom (fun t => (Nat.choose (s+t-1) t : ZMod (p^9))) X hX9]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    have hh : (∑ t ∈ Finset.range (u+1), (Nat.choose (s+t-1) t : ZMod (p^9)))
            = (Nat.choose (s+u) u : ZMod (p^9)) := by
      rw [← Nat.cast_sum, hockey s u]
    rw [hh, hX, neg_pow, mul_pow]
    have hsu : s + 1 + u - 1 = s + u := by omega
    rw [hsu]
    ring

-- gam block reindex + gam power-sum closed form
theorem gam_block [Fact p.Prime] (s l : ℕ) :
    gam (p:=p) s l = ∑ d ∈ Finset.range l, ∑ c ∈ Finset.Icc 1 (p-1),
      (((c + p * d : ℕ):ZMod (p^9))⁻¹)^s := by
  unfold gam Sset
  exact fullblocks_reindex p l (Nat.one_le_iff_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)) (fun i => (((i:ℕ):ZMod (p^9))⁻¹)^s)

theorem gam_expand [Fact p.Prime] (s l : ℕ) :
    gam (p:=p) s l = ∑ t ∈ Finset.range 9, (-1:ZMod (p^9))^t * (Nat.choose (s+t-1) t : ZMod (p^9))
        * (p:ZMod (p^9))^t * (∑ d ∈ Finset.range l, (d:ZMod (p^9))^t) * (HAsum (s+t) (p-1)) := by
  rw [gam_block]
  have key : ∀ d ∈ Finset.range l, ∀ c ∈ Finset.Icc 1 (p-1),
      (((c + p * d : ℕ):ZMod (p^9))⁻¹)^s
        = ∑ t ∈ Finset.range 9, (-1:ZMod (p^9))^t * (Nat.choose (s+t-1) t : ZMod (p^9))
            * (p:ZMod (p^9))^t * (d:ZMod (p^9))^t * ((c:ZMod (p^9))⁻¹)^(s+t) := by
    intro d _ c hc
    simp only [Finset.mem_Icc] at hc
    have hcu : IsUnit ((c:ZMod (p^9))) := isUnit_of_lt hc.1 (le_trans hc.2 (by omega))
    have hcast : ((c + p * d : ℕ):ZMod (p^9)) = (c:ZMod (p^9)) + (p:ZMod (p^9))*(d:ZMod (p^9)) := by
      push_cast; ring
    rw [hcast, pow_inv_expand s c d hcu]
  rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun c hc => key d hd c hc))]
  rw [Finset.sum_congr rfl (fun d _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [show (HAsum (s+t) (p-1)) = ∑ c ∈ Finset.Icc 1 (p-1), ((c:ZMod (p^9))⁻¹)^(s+t) from (asum_eq (s+t)).symm]
  conv_rhs => rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

-- esg (elementary symmetric) in terms of gam (power sums) via Newton
theorem esg1_eq [Fact p.Prime] (l : ℕ) : esg (p:=p) 1 l = gam (p:=p) 1 l := by
  unfold esg gam
  rw [esym_one_eq (fun i => (i:ZMod (p^9))⁻¹) (Sset (p:=p) l)]
  apply Finset.sum_congr rfl; intro i _; rw [pow_one]

theorem esg2_eq [Fact p.Prime] (l : ℕ) :
    2 * esg (p:=p) 2 l = (gam (p:=p) 1 l)^2 - gam (p:=p) 2 l := by
  have := newton2 (fun i => (i:ZMod (p^9))⁻¹) (Sset (p:=p) l)
  unfold esg gam; convert this using 2 <;> simp [pow_one]

theorem esg3_eq [Fact p.Prime] (l : ℕ) :
    6 * esg (p:=p) 3 l = (gam (p:=p) 1 l)^3 - 3 * (gam (p:=p) 1 l) * (gam (p:=p) 2 l)
      + 2 * (gam (p:=p) 3 l) := by
  have := newton3 (fun i => (i:ZMod (p^9))⁻¹) (Sset (p:=p) l)
  unfold esg gam; convert this using 2 <;> simp [pow_one]

theorem esg4_eq [Fact p.Prime] (l : ℕ) :
    24 * esg (p:=p) 4 l = (gam (p:=p) 1 l)^4 - 6 * (gam (p:=p) 1 l)^2 * (gam (p:=p) 2 l)
      + 3 * (gam (p:=p) 2 l)^2 + 8 * (gam (p:=p) 1 l) * (gam (p:=p) 3 l)
      - 6 * (gam (p:=p) 4 l) := by
  have := newton4 (fun i => (i:ZMod (p^9))⁻¹) (Sset (p:=p) l)
  unfold esg gam; convert this using 2 <;> simp [pow_one]

-- Gl product expansions and Gl^2-1, Gl^3-1
theorem esg0_eq [Fact p.Prime] (l : ℕ) : esg (p:=p) 0 l = 1 := by
  unfold esg; rw [Finset.powersetCard_zero]; simp

theorem Gl_expand [Fact p.Prime] (l : ℕ) :
    (∏ i ∈ Sset (p:=p) l, (1 + (p:ZMod (p^9))^2 * (i:ZMod (p^9))⁻¹))
      = 1 + (p:ZMod (p^9))^2 * esg (p:=p) 1 l + (p:ZMod (p^9))^4 * esg (p:=p) 2 l
        + (p:ZMod (p^9))^6 * esg (p:=p) 3 l + (p:ZMod (p^9))^8 * esg (p:=p) 4 l := by
  rw [Gl_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, esg0_eq]
  ring

theorem Gl2m1_eq [Fact p.Prime] (l : ℕ) :
    (∏ i ∈ Sset (p:=p) l, (1 + (p:ZMod (p^9))^2 * (i:ZMod (p^9))⁻¹))^2 - 1
      = 2*(p:ZMod (p^9))^8*(esg (p:=p) 1 l)*(esg (p:=p) 3 l) + (p:ZMod (p^9))^8*(esg (p:=p) 2 l)^2 + 2*(p:ZMod (p^9))^8*(esg (p:=p) 4 l) + 2*(p:ZMod (p^9))^6*(esg (p:=p) 1 l)*(esg (p:=p) 2 l) + 2*(p:ZMod (p^9))^6*(esg (p:=p) 3 l) + (p:ZMod (p^9))^4*(esg (p:=p) 1 l)^2 + 2*(p:ZMod (p^9))^4*(esg (p:=p) 2 l) + 2*(p:ZMod (p^9))^2*(esg (p:=p) 1 l) := by
  rw [Gl_expand]
  linear_combination ((p:ZMod (p^9))^7*(esg (p:=p) 4 l)^2 + 2*(p:ZMod (p^9))^5*(esg (p:=p) 3 l)*(esg (p:=p) 4 l) + 2*(p:ZMod (p^9))^3*(esg (p:=p) 2 l)*(esg (p:=p) 4 l) + (p:ZMod (p^9))^3*(esg (p:=p) 3 l)^2 + 2*(p:ZMod (p^9))*(esg (p:=p) 1 l)*(esg (p:=p) 4 l) + 2*(p:ZMod (p^9))*(esg (p:=p) 2 l)*(esg (p:=p) 3 l)) * (hp9z (p:=p))

theorem Gl3m1_eq [Fact p.Prime] (l : ℕ) :
    (∏ i ∈ Sset (p:=p) l, (1 + (p:ZMod (p^9))^2 * (i:ZMod (p^9))⁻¹))^3 - 1
      = 3*(p:ZMod (p^9))^8*(esg (p:=p) 1 l)^2*(esg (p:=p) 2 l) + 6*(p:ZMod (p^9))^8*(esg (p:=p) 1 l)*(esg (p:=p) 3 l) + 3*(p:ZMod (p^9))^8*(esg (p:=p) 2 l)^2 + 3*(p:ZMod (p^9))^8*(esg (p:=p) 4 l) + (p:ZMod (p^9))^6*(esg (p:=p) 1 l)^3 + 6*(p:ZMod (p^9))^6*(esg (p:=p) 1 l)*(esg (p:=p) 2 l) + 3*(p:ZMod (p^9))^6*(esg (p:=p) 3 l) + 3*(p:ZMod (p^9))^4*(esg (p:=p) 1 l)^2 + 3*(p:ZMod (p^9))^4*(esg (p:=p) 2 l) + 3*(p:ZMod (p^9))^2*(esg (p:=p) 1 l) := by
  rw [Gl_expand]
  linear_combination ((p:ZMod (p^9))^15*(esg (p:=p) 4 l)^3 + 3*(p:ZMod (p^9))^13*(esg (p:=p) 3 l)*(esg (p:=p) 4 l)^2 + 3*(p:ZMod (p^9))^11*(esg (p:=p) 2 l)*(esg (p:=p) 4 l)^2 + 3*(p:ZMod (p^9))^11*(esg (p:=p) 3 l)^2*(esg (p:=p) 4 l) + 3*(p:ZMod (p^9))^9*(esg (p:=p) 1 l)*(esg (p:=p) 4 l)^2 + 6*(p:ZMod (p^9))^9*(esg (p:=p) 2 l)*(esg (p:=p) 3 l)*(esg (p:=p) 4 l) + (p:ZMod (p^9))^9*(esg (p:=p) 3 l)^3 + 6*(p:ZMod (p^9))^7*(esg (p:=p) 1 l)*(esg (p:=p) 3 l)*(esg (p:=p) 4 l) + 3*(p:ZMod (p^9))^7*(esg (p:=p) 2 l)^2*(esg (p:=p) 4 l) + 3*(p:ZMod (p^9))^7*(esg (p:=p) 2 l)*(esg (p:=p) 3 l)^2 + 3*(p:ZMod (p^9))^7*(esg (p:=p) 4 l)^2 + 6*(p:ZMod (p^9))^5*(esg (p:=p) 1 l)*(esg (p:=p) 2 l)*(esg (p:=p) 4 l) + 3*(p:ZMod (p^9))^5*(esg (p:=p) 1 l)*(esg (p:=p) 3 l)^2 + 3*(p:ZMod (p^9))^5*(esg (p:=p) 2 l)^2*(esg (p:=p) 3 l) + 6*(p:ZMod (p^9))^5*(esg (p:=p) 3 l)*(esg (p:=p) 4 l) + 3*(p:ZMod (p^9))^3*(esg (p:=p) 1 l)^2*(esg (p:=p) 4 l) + 6*(p:ZMod (p^9))^3*(esg (p:=p) 1 l)*(esg (p:=p) 2 l)*(esg (p:=p) 3 l) + (p:ZMod (p^9))^3*(esg (p:=p) 2 l)^3 + 6*(p:ZMod (p^9))^3*(esg (p:=p) 2 l)*(esg (p:=p) 4 l) + 3*(p:ZMod (p^9))^3*(esg (p:=p) 3 l)^2 + 3*(p:ZMod (p^9))*(esg (p:=p) 1 l)^2*(esg (p:=p) 3 l) + 3*(p:ZMod (p^9))*(esg (p:=p) 1 l)*(esg (p:=p) 2 l)^2 + 6*(p:ZMod (p^9))*(esg (p:=p) 1 l)*(esg (p:=p) 4 l) + 6*(p:ZMod (p^9))*(esg (p:=p) 2 l)*(esg (p:=p) 3 l)) * (hp9z (p:=p))


-- bl factorial relation (l<p)
theorem prod_Icc1_factorial (n : ℕ) : ∏ i ∈ Finset.Icc 1 n, i = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ]; ring

theorem bl_fac [Fact p.Prime] {l : ℕ} (hl : 1 ≤ l) (hlp : l < p) :
    (Nat.choose (p+l-1) l : ZMod (p^9)) * (l.factorial : ZMod (p^9))
      = (p:ZMod (p^9)) * ∏ i ∈ Finset.Icc 1 (l-1), ((p:ZMod (p^9)) + (i:ZMod (p^9))) := by
  have hp1 : 1 ≤ p := (Fact.out (p := p.Prime)).one_le
  have hint := box_int_identity p 1 l hp1 (by norm_num) hl
  simp only [show (1:ℕ)-1 = 0 from rfl, pow_zero, pow_one] at hint
  have hb0 : (l-1)/p = 0 := Nat.div_eq_of_lt (by omega)
  rw [hb0] at hint
  have hfilt : (Finset.range l).filter (fun i => ¬ p ∣ i) = Finset.Icc 1 (l-1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨hi, hpi⟩
      rcases Nat.eq_zero_or_pos i with h | h
      · exact absurd (h ▸ Dvd.intro 0 rfl) hpi
      · exact ⟨h, by omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, fun hd => by have := Nat.le_of_dvd (by omega) hd; omega⟩
  rw [hfilt] at hint
  simp only [Finset.Icc_eq_empty (by norm_num : ¬ (1:ℕ) ≤ 0), Finset.prod_empty, mul_one, one_mul] at hint
  have hlfac : l * (∏ i ∈ Finset.Icc 1 (l-1), i) = l.factorial := by
    rw [← Nat.mul_factorial_pred (by omega : l ≠ 0)]
    congr 1
    rw [prod_Icc1_factorial]
  have hcast := congrArg (fun n : ℕ => (n : ZMod (p^9))) hint
  push_cast at hcast
  rw [show ((l:ZMod (p^9)) * ∏ i ∈ Finset.Icc 1 (l-1), (i:ZMod (p^9)))
        = ((l * ∏ i ∈ Finset.Icc 1 (l-1), i : ℕ) : ZMod (p^9)) from by push_cast; ring] at hcast
  rw [hlfac] at hcast
  push_cast at hcast
  linear_combination hcast

-- Ddiag in esg form
theorem Ddiag_esg [Fact p.Prime] :
    Ddiag (p:=p)
      = ∑ l ∈ Finset.Icc 1 p,
          (3 * (Nat.choose (p+l-1) l : ZMod (p^9))^2 *
              (2*(p:ZMod (p^9))^8*(esg (p:=p) 1 l)*(esg (p:=p) 3 l) + (p:ZMod (p^9))^8*(esg (p:=p) 2 l)^2
                + 2*(p:ZMod (p^9))^8*(esg (p:=p) 4 l) + 2*(p:ZMod (p^9))^6*(esg (p:=p) 1 l)*(esg (p:=p) 2 l)
                + 2*(p:ZMod (p^9))^6*(esg (p:=p) 3 l) + (p:ZMod (p^9))^4*(esg (p:=p) 1 l)^2
                + 2*(p:ZMod (p^9))^4*(esg (p:=p) 2 l) + 2*(p:ZMod (p^9))^2*(esg (p:=p) 1 l))
           + 2 * (Nat.choose (p+l-1) l : ZMod (p^9))^3 *
              (3*(p:ZMod (p^9))^8*(esg (p:=p) 1 l)^2*(esg (p:=p) 2 l) + 6*(p:ZMod (p^9))^8*(esg (p:=p) 1 l)*(esg (p:=p) 3 l)
                + 3*(p:ZMod (p^9))^8*(esg (p:=p) 2 l)^2 + 3*(p:ZMod (p^9))^8*(esg (p:=p) 4 l)
                + (p:ZMod (p^9))^6*(esg (p:=p) 1 l)^3 + 6*(p:ZMod (p^9))^6*(esg (p:=p) 1 l)*(esg (p:=p) 2 l)
                + 3*(p:ZMod (p^9))^6*(esg (p:=p) 3 l) + 3*(p:ZMod (p^9))^4*(esg (p:=p) 1 l)^2
                + 3*(p:ZMod (p^9))^4*(esg (p:=p) 2 l) + 3*(p:ZMod (p^9))^2*(esg (p:=p) 1 l))) := by
  unfold Ddiag
  apply Finset.sum_congr rfl
  intro l _
  simp only
  rw [show (Finset.range (p*l)).filter (fun i => ¬ p ∣ i) = Sset (p:=p) l from rfl,
      Gl2m1_eq, Gl3m1_eq]

-- esg solved in terms of gam (units of 2,6,24)
theorem ninv2 [Fact p.Prime] (hp : 5 ≤ p) : (2:ZMod (p^9))⁻¹ * 2 = 1 := by
  rw [mul_comm]; have e : ((2:ℕ):ZMod (p^9)) = 2 := by norm_num
  rw [← e]; exact ZMod.mul_inv_of_unit _ (isUnit_cast_of_not_dvd (a:=2) (by intro h; have := Nat.le_of_dvd (by norm_num) h; omega))

theorem ninv6 [Fact p.Prime] (hp : 7 ≤ p) : (6:ZMod (p^9))⁻¹ * 6 = 1 := by
  rw [mul_comm]; have e : ((6:ℕ):ZMod (p^9)) = 6 := by norm_num
  rw [← e]; exact ZMod.mul_inv_of_unit _ (isUnit_cast_of_not_dvd (a:=6) (by intro h; have := Nat.le_of_dvd (by norm_num) h; omega))

theorem ninv24 [Fact p.Prime] (hp : 5 ≤ p) : (24:ZMod (p^9))⁻¹ * 24 = 1 := by
  rw [mul_comm]; have e : ((24:ℕ):ZMod (p^9)) = 24 := by norm_num
  have hpr : p.Prime := Fact.out
  rw [← e]; refine ZMod.mul_inv_of_unit _ (isUnit_cast_of_not_dvd (a:=24) ?_)
  intro hd; have hle := Nat.le_of_dvd (by norm_num) hd
  interval_cases p <;> first | (exact absurd hpr (by decide)) | (revert hd; decide)

theorem esg_val2 [Fact p.Prime] (hp : 5 ≤ p) (l : ℕ) :
    esg (p:=p) 2 l = (2:ZMod (p^9))⁻¹ * ((gam (p:=p) 1 l)^2 - gam (p:=p) 2 l) := by
  have h2 := ninv2 (p:=p) hp
  calc esg (p:=p) 2 l = (2:ZMod (p^9))⁻¹ * 2 * esg (p:=p) 2 l := by rw [h2, one_mul]
    _ = (2:ZMod (p^9))⁻¹ * (2 * esg (p:=p) 2 l) := by ring
    _ = _ := by rw [esg2_eq]

theorem esg_val3 [Fact p.Prime] (hp : 7 ≤ p) (l : ℕ) :
    esg (p:=p) 3 l = (6:ZMod (p^9))⁻¹ * ((gam (p:=p) 1 l)^3 - 3*(gam (p:=p) 1 l)*(gam (p:=p) 2 l) + 2*(gam (p:=p) 3 l)) := by
  have h6 := ninv6 (p:=p) hp
  calc esg (p:=p) 3 l = (6:ZMod (p^9))⁻¹ * 6 * esg (p:=p) 3 l := by rw [h6, one_mul]
    _ = (6:ZMod (p^9))⁻¹ * (6 * esg (p:=p) 3 l) := by ring
    _ = _ := by rw [esg3_eq]

theorem esg_val4 [Fact p.Prime] (hp : 5 ≤ p) (l : ℕ) :
    esg (p:=p) 4 l = (24:ZMod (p^9))⁻¹ * ((gam (p:=p) 1 l)^4 - 6*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)
      + 3*(gam (p:=p) 2 l)^2 + 8*(gam (p:=p) 1 l)*(gam (p:=p) 3 l) - 6*(gam (p:=p) 4 l)) := by
  have h24 := ninv24 (p:=p) hp
  calc esg (p:=p) 4 l = (24:ZMod (p^9))⁻¹ * 24 * esg (p:=p) 4 l := by rw [h24, one_mul]
    _ = (24:ZMod (p^9))⁻¹ * (24 * esg (p:=p) 4 l) := by ring
    _ = _ := by rw [esg4_eq]

-- gam 2 p divisible by p^2 (p>=11)
theorem gam2p_dvd [Fact p.Prime] (hp : 11 ≤ p) :
    (p:ZMod (p^9))^2 ∣ gam (p:=p) 2 p := by
  rw [gam_expand 2 p]
  apply Finset.dvd_sum
  intro t ht
  simp only [Finset.mem_range] at ht
  -- term = (-1)^t * C(2+t-1,t) * p^t * (∑_{d<p} d^t) * HAsum (2+t) (p-1)
  rcases Nat.lt_or_ge t 2 with htlt | htge
  · interval_cases t
    · -- t=0: (-1)^0 * C(1,0) * p^0 * (∑ 1) * HAsum 2
      simp only [pow_zero, one_mul, Nat.choose, Nat.cast_one, mul_one]
      rw [sumone_eq]
      have h20 : (2:ℕ) + 0 = 2 := rfl
      rw [h20]
      obtain ⟨w, hw⟩ := wsum_dvd_p (s:=2) (by norm_num) (show (2:ℕ) < p - 1 by omega)
      exact ⟨w, by rw [hw]; ring⟩
    · -- t=1: (-1)^1 * C(2,1) * p^1 * (∑ d) * HAsum 3
      simp only [pow_one]
      obtain ⟨w, hw⟩ := sumb1_dvd (by omega : 3 ≤ p)
      refine ⟨(-1:ZMod (p^9)) * (Nat.choose 2 1 : ZMod (p^9)) * w * HAsum 3 (p-1), ?_⟩
      rw [hw]; push_cast; ring
  · -- t≥2: p^t divisible by p^2
    obtain ⟨w, hw⟩ : (p:ZMod (p^9))^2 ∣ (p:ZMod (p^9))^t := pow_dvd_pow _ htge
    refine ⟨(-1:ZMod (p^9))^t * (Nat.choose (2+t-1) t : ZMod (p^9)) * w * (∑ d ∈ Finset.range p, (d:ZMod (p^9))^t) * HAsum (2+t) (p-1), ?_⟩
    rw [hw]; ring

-- p^3 | (C(2p-1,p) - 1)  (Wolstenholme-type)
theorem cm1_dvd [Fact p.Prime] (hp : 11 ≤ p) :
    (p:ZMod (p^9))^3 ∣ ((Nat.choose (2*p-1) p : ZMod (p^9)) - 1) := by
  set S := (Finset.range p).filter (fun i => ¬ p ∣ i) with hSdef
  have hSeq : S = Finset.Icc 1 (p-1) := by
    rw [hSdef]; ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨hi, hpi⟩
      rcases Nat.eq_zero_or_pos i with h | h
      · exact absurd (h ▸ dvd_zero p) hpi
      · exact ⟨h, by omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, fun hd => by have := Nat.le_of_dvd (by omega) hd; omega⟩
  have hS1 : Sset (p:=p) 1 = S := by
    unfold Sset; rw [hSdef, mul_one]
  -- box identity, cancel p
  have hdivp : (p-1)/p = 0 := Nat.div_eq_of_lt (by omega)
  have hbox := box_int_identity p 1 p (by omega) le_rfl (by omega)
  rw [hdivp] at hbox
  simp only [pow_one, Finset.Icc_eq_empty (show ¬ (1:ℕ) ≤ 0 by omega),
    Finset.prod_empty, mul_one] at hbox
  rw [show p + p - 1 = 2*p - 1 by omega] at hbox
  have hbox2 : Nat.choose (2*p-1) p * (∏ i ∈ S, i) = ∏ i ∈ S, (p + i) := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < p by omega)
    rw [← hbox]; ring
  have hcast := congrArg (fun n : ℕ => (n : ZMod (p^9))) hbox2
  push_cast at hcast
  have hQ : (∏ i ∈ S, ((p:ZMod (p^9)) + (i:ZMod (p^9))))
      = (∏ i ∈ S, (i:ZMod (p^9))) * ∏ i ∈ S, (1 + (p:ZMod (p^9))*(i:ZMod (p^9))⁻¹) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hSeq, Finset.mem_Icc] at hi
    have hu : IsUnit (i:ZMod (p^9)) := isUnit_of_lt hi.1 (by omega)
    have e : (i:ZMod (p^9))*(i:ZMod (p^9))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu
    rw [mul_add, mul_one,
      show (i:ZMod (p^9))*((p:ZMod (p^9))*(i:ZMod (p^9))⁻¹)
        = (p:ZMod (p^9))*((i:ZMod (p^9))*(i:ZMod (p^9))⁻¹) by ring, e, mul_one, add_comm]
  have hPi : IsUnit (∏ i ∈ S, (i:ZMod (p^9))) := by
    have := prod_filter_isUnit (M:=9) S id (by
      intro i hi
      rw [hSdef, Finset.mem_filter] at hi
      exact hi.2)
    simpa using this
  have hCeq : (Nat.choose (2*p-1) p : ZMod (p^9))
      = ∏ i ∈ S, (1 + (p:ZMod (p^9))*(i:ZMod (p^9))⁻¹) := by
    rw [hQ] at hcast
    exact (IsUnit.mul_left_inj hPi).mp (hcast.trans (mul_comm _ _))
  -- B_expansion
  have hB := B_expansion (p:=p) (t:=9) S (fun i => (i:ZMod (p^9))⁻¹) (p:ZMod (p^9))
  simp only [] at hB
  obtain ⟨w, hw⟩ := hB
  -- helper: powerset sums = esg
  have hEsg : ∀ j, (∑ T ∈ S.powersetCard j, ∏ i ∈ T, (i:ZMod (p^9))⁻¹) = esg (p:=p) j 1 := by
    intro j; rw [← hS1]; rfl
  -- expand the range-5 sum in hw
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one] at hw
  rw [hEsg 0, hEsg 1, hEsg 2, hEsg 3, hEsg 4, esg0_eq, esg1_eq] at hw
  simp only [pow_zero, pow_one, mul_one] at hw
  -- now hw : ∏ - (1 + p*gam 1 1 + p^2*esg 2 1 + p^3*esg 3 1 + p^4*esg 4 1) = p^5 * w
  -- divisibilities
  have hgam11 : gam (p:=p) 1 1 = ∑ k ∈ Finset.Icc 1 (p-1), (k:ZMod (p^9))⁻¹ := by
    unfold gam; rw [hS1, hSeq]; apply Finset.sum_congr rfl; intro i _; rw [pow_one]
  have hg11dvd : (p:ZMod (p^9))^2 ∣ gam (p:=p) 1 1 := by
    rw [hgam11]; exact wol_div_p2 (by omega) (by norm_num)
  have hgam21 : gam (p:=p) 2 1 = HAsum (p:=p) 2 (p-1) := by
    unfold gam HAsum; rw [hS1, hSeq]
  have hg21dvd : (p:ZMod (p^9)) ∣ gam (p:=p) 2 1 := by
    rw [hgam21]; exact wsum_dvd_p (by norm_num) (by omega)
  have he2dvd : (p:ZMod (p^9)) ∣ esg (p:=p) 2 1 := by
    rw [esg_val2 (by omega)]
    have hpg11 : (p:ZMod (p^9)) ∣ gam (p:=p) 1 1 :=
      dvd_trans (dvd_pow_self _ (two_ne_zero)) hg11dvd
    have : (p:ZMod (p^9)) ∣ (gam (p:=p) 1 1)^2 - gam (p:=p) 2 1 :=
      dvd_sub (by rw [sq]; exact hpg11.mul_right _) hg21dvd
    exact this.mul_left _
  -- assemble
  have hc1 : (Nat.choose (2*p-1) p : ZMod (p^9)) - 1
      = (p:ZMod (p^9))*(gam (p:=p) 1 1) + (p:ZMod (p^9))^2*(esg (p:=p) 2 1)
        + (p:ZMod (p^9))^3*(esg (p:=p) 3 1) + (p:ZMod (p^9))^4*(esg (p:=p) 4 1)
        + (p:ZMod (p^9))^5 * w := by
    rw [hCeq]; linear_combination hw
  rw [hc1]
  refine dvd_add (dvd_add (dvd_add (dvd_add ?_ ?_) ?_) ?_) ?_
  · obtain ⟨a, ha⟩ := hg11dvd; exact ⟨a, by rw [ha]; ring⟩
  · obtain ⟨b, hbb⟩ := he2dvd; exact ⟨b, by rw [hbb]; ring⟩
  · exact ⟨esg (p:=p) 3 1, by ring⟩
  · exact (pow_dvd_pow (p:ZMod (p^9)) (by norm_num : 3 ≤ 4)).mul_right _
  · exact (pow_dvd_pow (p:ZMod (p^9)) (by norm_num : 3 ≤ 5)).mul_right _

-- Ddiag in pure gam form
theorem Ddiag_gam [Fact p.Prime] (hp : 7 ≤ p) :
    Ddiag (p:=p)
      = ∑ l ∈ Finset.Icc 1 p,
          (3 * (Nat.choose (p+l-1) l : ZMod (p^9))^2 * (2*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)*((6:ZMod (p^9))⁻¹)*((gam (p:=p) 1 l)^3 - 3*(gam (p:=p) 1 l)*(gam (p:=p) 2 l) + 2*(gam (p:=p) 3 l)) + (p:ZMod (p^9))^8*((2:ZMod (p^9))⁻¹)^2*((gam (p:=p) 1 l)^2 - (gam (p:=p) 2 l))^2 + 2*(p:ZMod (p^9))^8*((24:ZMod (p^9))⁻¹)*((gam (p:=p) 1 l)^4 - 6*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l) + 8*(gam (p:=p) 1 l)*(gam (p:=p) 3 l) + 3*(gam (p:=p) 2 l)^2 - 6*(gam (p:=p) 4 l)) + 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)*((2:ZMod (p^9))⁻¹)*((gam (p:=p) 1 l)^2 - (gam (p:=p) 2 l)) + 2*(p:ZMod (p^9))^6*((6:ZMod (p^9))⁻¹)*((gam (p:=p) 1 l)^3 - 3*(gam (p:=p) 1 l)*(gam (p:=p) 2 l) + 2*(gam (p:=p) 3 l)) + (p:ZMod (p^9))^4*(gam (p:=p) 1 l)^2 + 2*(p:ZMod (p^9))^4*((2:ZMod (p^9))⁻¹)*((gam (p:=p) 1 l)^2 - (gam (p:=p) 2 l)) + 2*(p:ZMod (p^9))^2*(gam (p:=p) 1 l))
           + 2 * (Nat.choose (p+l-1) l : ZMod (p^9))^3 * (3*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^2*((2:ZMod (p^9))⁻¹)*((gam (p:=p) 1 l)^2 - (gam (p:=p) 2 l)) + 6*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)*((6:ZMod (p^9))⁻¹)*((gam (p:=p) 1 l)^3 - 3*(gam (p:=p) 1 l)*(gam (p:=p) 2 l) + 2*(gam (p:=p) 3 l)) + 3*(p:ZMod (p^9))^8*((2:ZMod (p^9))⁻¹)^2*((gam (p:=p) 1 l)^2 - (gam (p:=p) 2 l))^2 + 3*(p:ZMod (p^9))^8*((24:ZMod (p^9))⁻¹)*((gam (p:=p) 1 l)^4 - 6*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l) + 8*(gam (p:=p) 1 l)*(gam (p:=p) 3 l) + 3*(gam (p:=p) 2 l)^2 - 6*(gam (p:=p) 4 l)) + (p:ZMod (p^9))^6*(gam (p:=p) 1 l)^3 + 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)*((2:ZMod (p^9))⁻¹)*((gam (p:=p) 1 l)^2 - (gam (p:=p) 2 l)) + 3*(p:ZMod (p^9))^6*((6:ZMod (p^9))⁻¹)*((gam (p:=p) 1 l)^3 - 3*(gam (p:=p) 1 l)*(gam (p:=p) 2 l) + 2*(gam (p:=p) 3 l)) + 3*(p:ZMod (p^9))^4*(gam (p:=p) 1 l)^2 + 3*(p:ZMod (p^9))^4*((2:ZMod (p^9))⁻¹)*((gam (p:=p) 1 l)^2 - (gam (p:=p) 2 l)) + 3*(p:ZMod (p^9))^2*(gam (p:=p) 1 l))) := by
  rw [Ddiag_esg]
  apply Finset.sum_congr rfl
  intro l _
  rw [esg1_eq, esg_val2 (by omega), esg_val3 (by omega), esg_val4 (by omega)]
  ring

-- endgame cancellation: -6 p^4 (c-1) W2 = 0
theorem endgame_zero [Fact p.Prime] (hp : 11 ≤ p) :
    (-6:ZMod (p^9)) * (p:ZMod (p^9))^4 * ((Nat.choose (2*p-1) p : ZMod (p^9)) - 1)
        * (gam (p:=p) 2 p) = 0 := by
  obtain ⟨a, ha⟩ := cm1_dvd (p:=p) hp
  obtain ⟨b, hb⟩ := gam2p_dvd (p:=p) hp
  apply eq0_of_p9
  refine ⟨(-6:ZMod (p^9)) * a * b, ?_⟩
  rw [ha, hb]
  ring

-- base case r=2, p>=11, conditional on bridge identity
theorem base_p11_cond [Fact p.Prime] (hp : 11 ≤ p)
    (hbridge : CU (p:=p) + Ddiag (p:=p)
        = (-6:ZMod (p^9)) * (p:ZMod (p^9))^4 * ((Nat.choose (2*p-1) p : ZMod (p^9)) - 1)
            * (gam (p:=p) 2 p)) :
    (A357565 (p^2) : ZMod (p^9)) - (A357565 p : ZMod (p^9)) = 0 := by
  rw [base_split (by omega), Uoff_closed hp, hbridge]
  exact endgame_zero hp

-- bl = p * l⁻¹ * ∏(1+p m⁻¹) for 1≤l<p
theorem bl_expand [Fact p.Prime] {l : ℕ} (hl : 1 ≤ l) (hlp : l < p) :
    (Nat.choose (p+l-1) l : ZMod (p^9))
      = (p:ZMod (p^9)) * (l:ZMod (p^9))⁻¹
          * ∏ m ∈ Finset.Icc 1 (l-1), (1 + (p:ZMod (p^9))*(m:ZMod (p^9))⁻¹) := by
  have hfac := bl_fac (p:=p) hl hlp
  set X := ∏ i ∈ Finset.Icc 1 (l-1), (i:ZMod (p^9)) with hX
  set R := ∏ m ∈ Finset.Icc 1 (l-1), (1 + (p:ZMod (p^9))*(m:ZMod (p^9))⁻¹) with hR
  have hlfac : (l.factorial : ZMod (p^9)) = X * (l:ZMod (p^9)) := by
    have h1 : (l.factorial : ZMod (p^9)) = ∏ i ∈ Finset.Icc 1 l, (i:ZMod (p^9)) := by
      rw [← prod_Icc1_factorial]; push_cast; rfl
    rw [h1, hX]
    conv_lhs => rw [show l = (l-1)+1 by omega]
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ (l-1)+1), show (l-1)+1 = l by omega]
  have hQ : (∏ i ∈ Finset.Icc 1 (l-1), ((p:ZMod (p^9)) + (i:ZMod (p^9)))) = X * R := by
    rw [hX, hR, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hu : IsUnit (i:ZMod (p^9)) := isUnit_of_lt hi.1 (by omega)
    have e : (i:ZMod (p^9))*(i:ZMod (p^9))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu
    rw [mul_add, mul_one,
      show (i:ZMod (p^9))*((p:ZMod (p^9))*(i:ZMod (p^9))⁻¹)
        = (p:ZMod (p^9))*((i:ZMod (p^9))*(i:ZMod (p^9))⁻¹) by ring, e, mul_one, add_comm]
  have hlu : IsUnit (l:ZMod (p^9)) := isUnit_of_lt hl (by omega)
  have hPu : IsUnit X := by
    rw [hX, ← Nat.cast_prod, prod_Icc1_factorial]
    apply isUnit_cast_of_not_dvd
    intro hd
    have := (Nat.Prime.dvd_factorial (Fact.out)).mp hd
    omega
  rw [hlfac, hQ] at hfac
  have hbll : (Nat.choose (p+l-1) l : ZMod (p^9)) * (l:ZMod (p^9)) = (p:ZMod (p^9)) * R := by
    have h2 : X * ((Nat.choose (p+l-1) l : ZMod (p^9)) * (l:ZMod (p^9))) = X * ((p:ZMod (p^9)) * R) := by
      linear_combination hfac
    exact (IsUnit.mul_right_inj hPu).mp h2
  have hll : (l:ZMod (p^9))*(l:ZMod (p^9))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hlu
  calc (Nat.choose (p+l-1) l : ZMod (p^9))
      = (Nat.choose (p+l-1) l : ZMod (p^9)) * ((l:ZMod (p^9))*(l:ZMod (p^9))⁻¹) := by rw [hll, mul_one]
    _ = ((Nat.choose (p+l-1) l : ZMod (p^9)) * (l:ZMod (p^9)))*(l:ZMod (p^9))⁻¹ := by ring
    _ = ((p:ZMod (p^9)) * R)*(l:ZMod (p^9))⁻¹ := by rw [hbll]
    _ = (p:ZMod (p^9)) * (l:ZMod (p^9))⁻¹ * R := by ring

-- p^2 | gam(1,p) (W1 Wolstenholme harmonic fact)
theorem gam1p_dvd [Fact p.Prime] (hp : 11 ≤ p) :
    (p:ZMod (p^9))^2 ∣ gam (p:=p) 1 p := by
  rw [gam_expand 1 p]
  apply Finset.dvd_sum
  intro t ht
  simp only [Finset.mem_range] at ht
  rcases Nat.lt_or_ge t 2 with htlt | htge
  · interval_cases t
    · -- t=0: (∑ 1) * HAsum 1
      simp only [pow_zero, one_mul, Nat.choose, Nat.cast_one, mul_one]
      rw [sumone_eq]
      have h10 : (1:ℕ) + 0 = 1 := rfl
      rw [h10]
      obtain ⟨w, hw⟩ := wsum_dvd_p (s:=1) (by norm_num) (show (1:ℕ) < p - 1 by omega)
      exact ⟨w, by rw [hw]; ring⟩
    · -- t=1: -p * (∑ d) * HAsum 2
      simp only [pow_one]
      obtain ⟨w, hw⟩ := sumb1_dvd (by omega : 3 ≤ p)
      refine ⟨(-1:ZMod (p^9)) * (Nat.choose 1 1 : ZMod (p^9)) * w * HAsum 2 (p-1), ?_⟩
      rw [hw]; push_cast; ring
  · -- t≥2
    obtain ⟨w, hw⟩ : (p:ZMod (p^9))^2 ∣ (p:ZMod (p^9))^t := pow_dvd_pow _ htge
    refine ⟨(-1:ZMod (p^9))^t * (Nat.choose (1+t-1) t : ZMod (p^9)) * w * (∑ d ∈ Finset.range p, (d:ZMod (p^9))^t) * HAsum (1+t) (p-1), ?_⟩
    rw [hw]; ring

-- Ddiag split: off-diagonal (l<p) + diagonal (l=p)
theorem Ddiag_split [Fact p.Prime] (hp : 7 ≤ p) :
    Ddiag (p:=p)
      = (∑ l ∈ Finset.Icc 1 (p-1), (3 * (Nat.choose (p+l-1) l : ZMod (p^9))^2 * (2*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)*((6:ZMod (p^9))⁻¹)*((gam (p:=p) 1 l)^3 - 3*(gam (p:=p) 1 l)*(gam (p:=p) 2 l) + 2*(gam (p:=p) 3 l)) + (p:ZMod (p^9))^8*((2:ZMod (p^9))⁻¹)^2*((gam (p:=p) 1 l)^2 - (gam (p:=p) 2 l))^2 + 2*(p:ZMod (p^9))^8*((24:ZMod (p^9))⁻¹)*((gam (p:=p) 1 l)^4 - 6*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l) + 8*(gam (p:=p) 1 l)*(gam (p:=p) 3 l) + 3*(gam (p:=p) 2 l)^2 - 6*(gam (p:=p) 4 l)) + 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)*((2:ZMod (p^9))⁻¹)*((gam (p:=p) 1 l)^2 - (gam (p:=p) 2 l)) + 2*(p:ZMod (p^9))^6*((6:ZMod (p^9))⁻¹)*((gam (p:=p) 1 l)^3 - 3*(gam (p:=p) 1 l)*(gam (p:=p) 2 l) + 2*(gam (p:=p) 3 l)) + (p:ZMod (p^9))^4*(gam (p:=p) 1 l)^2 + 2*(p:ZMod (p^9))^4*((2:ZMod (p^9))⁻¹)*((gam (p:=p) 1 l)^2 - (gam (p:=p) 2 l)) + 2*(p:ZMod (p^9))^2*(gam (p:=p) 1 l)) + 2 * (Nat.choose (p+l-1) l : ZMod (p^9))^3 * (3*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^2*((2:ZMod (p^9))⁻¹)*((gam (p:=p) 1 l)^2 - (gam (p:=p) 2 l)) + 6*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)*((6:ZMod (p^9))⁻¹)*((gam (p:=p) 1 l)^3 - 3*(gam (p:=p) 1 l)*(gam (p:=p) 2 l) + 2*(gam (p:=p) 3 l)) + 3*(p:ZMod (p^9))^8*((2:ZMod (p^9))⁻¹)^2*((gam (p:=p) 1 l)^2 - (gam (p:=p) 2 l))^2 + 3*(p:ZMod (p^9))^8*((24:ZMod (p^9))⁻¹)*((gam (p:=p) 1 l)^4 - 6*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l) + 8*(gam (p:=p) 1 l)*(gam (p:=p) 3 l) + 3*(gam (p:=p) 2 l)^2 - 6*(gam (p:=p) 4 l)) + (p:ZMod (p^9))^6*(gam (p:=p) 1 l)^3 + 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)*((2:ZMod (p^9))⁻¹)*((gam (p:=p) 1 l)^2 - (gam (p:=p) 2 l)) + 3*(p:ZMod (p^9))^6*((6:ZMod (p^9))⁻¹)*((gam (p:=p) 1 l)^3 - 3*(gam (p:=p) 1 l)*(gam (p:=p) 2 l) + 2*(gam (p:=p) 3 l)) + 3*(p:ZMod (p^9))^4*(gam (p:=p) 1 l)^2 + 3*(p:ZMod (p^9))^4*((2:ZMod (p^9))⁻¹)*((gam (p:=p) 1 l)^2 - (gam (p:=p) 2 l)) + 3*(p:ZMod (p^9))^2*(gam (p:=p) 1 l))))
        + (3 * (Nat.choose (p+p-1) p : ZMod (p^9))^2 * (2*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)*((6:ZMod (p^9))⁻¹)*((gam (p:=p) 1 p)^3 - 3*(gam (p:=p) 1 p)*(gam (p:=p) 2 p) + 2*(gam (p:=p) 3 p)) + (p:ZMod (p^9))^8*((2:ZMod (p^9))⁻¹)^2*((gam (p:=p) 1 p)^2 - (gam (p:=p) 2 p))^2 + 2*(p:ZMod (p^9))^8*((24:ZMod (p^9))⁻¹)*((gam (p:=p) 1 p)^4 - 6*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p) + 8*(gam (p:=p) 1 p)*(gam (p:=p) 3 p) + 3*(gam (p:=p) 2 p)^2 - 6*(gam (p:=p) 4 p)) + 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)*((2:ZMod (p^9))⁻¹)*((gam (p:=p) 1 p)^2 - (gam (p:=p) 2 p)) + 2*(p:ZMod (p^9))^6*((6:ZMod (p^9))⁻¹)*((gam (p:=p) 1 p)^3 - 3*(gam (p:=p) 1 p)*(gam (p:=p) 2 p) + 2*(gam (p:=p) 3 p)) + (p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2 + 2*(p:ZMod (p^9))^4*((2:ZMod (p^9))⁻¹)*((gam (p:=p) 1 p)^2 - (gam (p:=p) 2 p)) + 2*(p:ZMod (p^9))^2*(gam (p:=p) 1 p)) + 2 * (Nat.choose (p+p-1) p : ZMod (p^9))^3 * (3*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^2*((2:ZMod (p^9))⁻¹)*((gam (p:=p) 1 p)^2 - (gam (p:=p) 2 p)) + 6*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)*((6:ZMod (p^9))⁻¹)*((gam (p:=p) 1 p)^3 - 3*(gam (p:=p) 1 p)*(gam (p:=p) 2 p) + 2*(gam (p:=p) 3 p)) + 3*(p:ZMod (p^9))^8*((2:ZMod (p^9))⁻¹)^2*((gam (p:=p) 1 p)^2 - (gam (p:=p) 2 p))^2 + 3*(p:ZMod (p^9))^8*((24:ZMod (p^9))⁻¹)*((gam (p:=p) 1 p)^4 - 6*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p) + 8*(gam (p:=p) 1 p)*(gam (p:=p) 3 p) + 3*(gam (p:=p) 2 p)^2 - 6*(gam (p:=p) 4 p)) + (p:ZMod (p^9))^6*(gam (p:=p) 1 p)^3 + 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)*((2:ZMod (p^9))⁻¹)*((gam (p:=p) 1 p)^2 - (gam (p:=p) 2 p)) + 3*(p:ZMod (p^9))^6*((6:ZMod (p^9))⁻¹)*((gam (p:=p) 1 p)^3 - 3*(gam (p:=p) 1 p)*(gam (p:=p) 2 p) + 2*(gam (p:=p) 3 p)) + 3*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2 + 3*(p:ZMod (p^9))^4*((2:ZMod (p^9))⁻¹)*((gam (p:=p) 1 p)^2 - (gam (p:=p) 2 p)) + 3*(p:ZMod (p^9))^2*(gam (p:=p) 1 p))) := by
  rw [Ddiag_gam hp]
  have hins : Finset.Icc 1 p = insert p (Finset.Icc 1 (p-1)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hins, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
  ring

-- off-diagonal part of Ddiag (l<p) is p^4-divisible
set_option maxHeartbeats 2000000 in
theorem offdiag_p4 [Fact p.Prime] (hp : 11 ≤ p) :
    (p:ZMod (p^9))^4 ∣
      ∑ l ∈ Finset.Icc 1 (p-1),
        (3 * (Nat.choose (p+l-1) l : ZMod (p^9))^2 * ((p:ZMod (p^9))^8*(gam (p:=p) 1 l)^4*((2:ZMod (p^9))⁻¹)^2 + 2*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^4*((24:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^4*((6:ZMod (p^9))⁻¹) - 2*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹)^2 - 12*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((24:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((6:ZMod (p^9))⁻¹) + 16*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)*(gam (p:=p) 3 l)*((24:ZMod (p^9))⁻¹) + 4*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)*(gam (p:=p) 3 l)*((6:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^8*(gam (p:=p) 2 l)^2*((2:ZMod (p^9))⁻¹)^2 + 6*(p:ZMod (p^9))^8*(gam (p:=p) 2 l)^2*((24:ZMod (p^9))⁻¹) - 12*(p:ZMod (p^9))^8*(gam (p:=p) 4 l)*((24:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^3*((2:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^3*((6:ZMod (p^9))⁻¹) - 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)*(gam (p:=p) 2 l)*((6:ZMod (p^9))⁻¹) + 4*(p:ZMod (p^9))^6*(gam (p:=p) 3 l)*((6:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^4*(gam (p:=p) 1 l)^2*((2:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^4*(gam (p:=p) 1 l)^2 - 2*(p:ZMod (p^9))^4*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^2*(gam (p:=p) 1 l)) + 2 * (Nat.choose (p+l-1) l : ZMod (p^9))^3 * (3*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^4*((2:ZMod (p^9))⁻¹)^2 + 3*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^4*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^4*((24:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^4*((6:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹)^2 - 3*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((24:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((6:ZMod (p^9))⁻¹) + 24*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)*(gam (p:=p) 3 l)*((24:ZMod (p^9))⁻¹) + 12*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)*(gam (p:=p) 3 l)*((6:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^8*(gam (p:=p) 2 l)^2*((2:ZMod (p^9))⁻¹)^2 + 9*(p:ZMod (p^9))^8*(gam (p:=p) 2 l)^2*((24:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^8*(gam (p:=p) 4 l)*((24:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^3*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^3*((6:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^6*(gam (p:=p) 1 l)^3 - 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹) - 9*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)*(gam (p:=p) 2 l)*((6:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^6*(gam (p:=p) 3 l)*((6:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^4*(gam (p:=p) 1 l)^2*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^4*(gam (p:=p) 1 l)^2 - 3*(p:ZMod (p^9))^4*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^2*(gam (p:=p) 1 l))) := by
  apply Finset.dvd_sum
  intro l hl
  rw [Finset.mem_Icc] at hl
  have hl1 : 1 ≤ l := hl.1
  have hlp : l < p := by omega
  have hbl1 : (p:ZMod (p^9)) ∣ (Nat.choose (p+l-1) l : ZMod (p^9)) := by
    rw [bl_expand hl1 hlp]; exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hE2 : (p:ZMod (p^9))^2 ∣ ((p:ZMod (p^9))^8*(gam (p:=p) 1 l)^4*((2:ZMod (p^9))⁻¹)^2 + 2*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^4*((24:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^4*((6:ZMod (p^9))⁻¹) - 2*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹)^2 - 12*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((24:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((6:ZMod (p^9))⁻¹) + 16*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)*(gam (p:=p) 3 l)*((24:ZMod (p^9))⁻¹) + 4*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)*(gam (p:=p) 3 l)*((6:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^8*(gam (p:=p) 2 l)^2*((2:ZMod (p^9))⁻¹)^2 + 6*(p:ZMod (p^9))^8*(gam (p:=p) 2 l)^2*((24:ZMod (p^9))⁻¹) - 12*(p:ZMod (p^9))^8*(gam (p:=p) 4 l)*((24:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^3*((2:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^3*((6:ZMod (p^9))⁻¹) - 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)*(gam (p:=p) 2 l)*((6:ZMod (p^9))⁻¹) + 4*(p:ZMod (p^9))^6*(gam (p:=p) 3 l)*((6:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^4*(gam (p:=p) 1 l)^2*((2:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^4*(gam (p:=p) 1 l)^2 - 2*(p:ZMod (p^9))^4*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^2*(gam (p:=p) 1 l)) := ⟨(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^4*((2:ZMod (p^9))⁻¹)^2 + 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^4*((24:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^4*((6:ZMod (p^9))⁻¹) - 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹)^2 - 12*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((24:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((6:ZMod (p^9))⁻¹) + 16*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)*(gam (p:=p) 3 l)*((24:ZMod (p^9))⁻¹) + 4*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)*(gam (p:=p) 3 l)*((6:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^6*(gam (p:=p) 2 l)^2*((2:ZMod (p^9))⁻¹)^2 + 6*(p:ZMod (p^9))^6*(gam (p:=p) 2 l)^2*((24:ZMod (p^9))⁻¹) - 12*(p:ZMod (p^9))^6*(gam (p:=p) 4 l)*((24:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^4*(gam (p:=p) 1 l)^3*((2:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^4*(gam (p:=p) 1 l)^3*((6:ZMod (p^9))⁻¹) - 2*(p:ZMod (p^9))^4*(gam (p:=p) 1 l)*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^4*(gam (p:=p) 1 l)*(gam (p:=p) 2 l)*((6:ZMod (p^9))⁻¹) + 4*(p:ZMod (p^9))^4*(gam (p:=p) 3 l)*((6:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^2*(gam (p:=p) 1 l)^2*((2:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^2*(gam (p:=p) 1 l)^2 - 2*(p:ZMod (p^9))^2*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹) + 2*(gam (p:=p) 1 l), by ring⟩
  have hE3 : (p:ZMod (p^9))^2 ∣ (3*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^4*((2:ZMod (p^9))⁻¹)^2 + 3*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^4*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^4*((24:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^4*((6:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹)^2 - 3*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((24:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((6:ZMod (p^9))⁻¹) + 24*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)*(gam (p:=p) 3 l)*((24:ZMod (p^9))⁻¹) + 12*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)*(gam (p:=p) 3 l)*((6:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^8*(gam (p:=p) 2 l)^2*((2:ZMod (p^9))⁻¹)^2 + 9*(p:ZMod (p^9))^8*(gam (p:=p) 2 l)^2*((24:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^8*(gam (p:=p) 4 l)*((24:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^3*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^3*((6:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^6*(gam (p:=p) 1 l)^3 - 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹) - 9*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)*(gam (p:=p) 2 l)*((6:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^6*(gam (p:=p) 3 l)*((6:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^4*(gam (p:=p) 1 l)^2*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^4*(gam (p:=p) 1 l)^2 - 3*(p:ZMod (p^9))^4*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^2*(gam (p:=p) 1 l)) := ⟨3*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^4*((2:ZMod (p^9))⁻¹)^2 + 3*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^4*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^4*((24:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^4*((6:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹)^2 - 3*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((24:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((6:ZMod (p^9))⁻¹) + 24*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)*(gam (p:=p) 3 l)*((24:ZMod (p^9))⁻¹) + 12*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)*(gam (p:=p) 3 l)*((6:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^6*(gam (p:=p) 2 l)^2*((2:ZMod (p^9))⁻¹)^2 + 9*(p:ZMod (p^9))^6*(gam (p:=p) 2 l)^2*((24:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^6*(gam (p:=p) 4 l)*((24:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^4*(gam (p:=p) 1 l)^3*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^4*(gam (p:=p) 1 l)^3*((6:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^4*(gam (p:=p) 1 l)^3 - 6*(p:ZMod (p^9))^4*(gam (p:=p) 1 l)*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹) - 9*(p:ZMod (p^9))^4*(gam (p:=p) 1 l)*(gam (p:=p) 2 l)*((6:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^4*(gam (p:=p) 3 l)*((6:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^2*(gam (p:=p) 1 l)^2*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^2*(gam (p:=p) 1 l)^2 - 3*(p:ZMod (p^9))^2*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹) + 3*(gam (p:=p) 1 l), by ring⟩
  have t1 : (p:ZMod (p^9))^4 ∣ 3 * (Nat.choose (p+l-1) l : ZMod (p^9))^2 * ((p:ZMod (p^9))^8*(gam (p:=p) 1 l)^4*((2:ZMod (p^9))⁻¹)^2 + 2*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^4*((24:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^4*((6:ZMod (p^9))⁻¹) - 2*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹)^2 - 12*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((24:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((6:ZMod (p^9))⁻¹) + 16*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)*(gam (p:=p) 3 l)*((24:ZMod (p^9))⁻¹) + 4*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)*(gam (p:=p) 3 l)*((6:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^8*(gam (p:=p) 2 l)^2*((2:ZMod (p^9))⁻¹)^2 + 6*(p:ZMod (p^9))^8*(gam (p:=p) 2 l)^2*((24:ZMod (p^9))⁻¹) - 12*(p:ZMod (p^9))^8*(gam (p:=p) 4 l)*((24:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^3*((2:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^3*((6:ZMod (p^9))⁻¹) - 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)*(gam (p:=p) 2 l)*((6:ZMod (p^9))⁻¹) + 4*(p:ZMod (p^9))^6*(gam (p:=p) 3 l)*((6:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^4*(gam (p:=p) 1 l)^2*((2:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^4*(gam (p:=p) 1 l)^2 - 2*(p:ZMod (p^9))^4*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^2*(gam (p:=p) 1 l)) := by
    obtain ⟨q, hq⟩ := mul_dvd_mul (pow_dvd_pow_of_dvd hbl1 2) hE2
    exact ⟨3*q, by linear_combination (3:ZMod (p^9))*hq⟩
  have t2 : (p:ZMod (p^9))^4 ∣ 2 * (Nat.choose (p+l-1) l : ZMod (p^9))^3 * (3*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^4*((2:ZMod (p^9))⁻¹)^2 + 3*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^4*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^4*((24:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^4*((6:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹)^2 - 3*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((24:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)^2*(gam (p:=p) 2 l)*((6:ZMod (p^9))⁻¹) + 24*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)*(gam (p:=p) 3 l)*((24:ZMod (p^9))⁻¹) + 12*(p:ZMod (p^9))^8*(gam (p:=p) 1 l)*(gam (p:=p) 3 l)*((6:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^8*(gam (p:=p) 2 l)^2*((2:ZMod (p^9))⁻¹)^2 + 9*(p:ZMod (p^9))^8*(gam (p:=p) 2 l)^2*((24:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^8*(gam (p:=p) 4 l)*((24:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^3*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)^3*((6:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^6*(gam (p:=p) 1 l)^3 - 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹) - 9*(p:ZMod (p^9))^6*(gam (p:=p) 1 l)*(gam (p:=p) 2 l)*((6:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^6*(gam (p:=p) 3 l)*((6:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^4*(gam (p:=p) 1 l)^2*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^4*(gam (p:=p) 1 l)^2 - 3*(p:ZMod (p^9))^4*(gam (p:=p) 2 l)*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^2*(gam (p:=p) 1 l)) := by
    obtain ⟨q, hq⟩ := mul_dvd_mul (pow_dvd_pow_of_dvd hbl1 3) hE3
    exact ⟨2*(p:ZMod (p^9))*q, by linear_combination (2:ZMod (p^9))*hq⟩
  exact dvd_add t1 t2

-- diagonal term (l=p) of Ddiag is p^4-divisible
set_option maxHeartbeats 2000000 in
theorem diag_p4 [Fact p.Prime] (hp : 11 ≤ p) :
    (p:ZMod (p^9))^4 ∣ (3 * (Nat.choose (p+p-1) p : ZMod (p^9))^2 * ((p:ZMod (p^9))^8*(gam (p:=p) 1 p)^4*((2:ZMod (p^9))⁻¹)^2 + 2*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^4*((24:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^4*((6:ZMod (p^9))⁻¹) - 2*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹)^2 - 12*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((24:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((6:ZMod (p^9))⁻¹) + 16*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)*(gam (p:=p) 3 p)*((24:ZMod (p^9))⁻¹) + 4*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)*(gam (p:=p) 3 p)*((6:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^8*(gam (p:=p) 2 p)^2*((2:ZMod (p^9))⁻¹)^2 + 6*(p:ZMod (p^9))^8*(gam (p:=p) 2 p)^2*((24:ZMod (p^9))⁻¹) - 12*(p:ZMod (p^9))^8*(gam (p:=p) 4 p)*((24:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)^3*((2:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)^3*((6:ZMod (p^9))⁻¹) - 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)*(gam (p:=p) 2 p)*((6:ZMod (p^9))⁻¹) + 4*(p:ZMod (p^9))^6*(gam (p:=p) 3 p)*((6:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2*((2:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2 - 2*(p:ZMod (p^9))^4*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^2*(gam (p:=p) 1 p)) + 2 * (Nat.choose (p+p-1) p : ZMod (p^9))^3 * (3*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^4*((2:ZMod (p^9))⁻¹)^2 + 3*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^4*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^4*((24:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^4*((6:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹)^2 - 3*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((24:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((6:ZMod (p^9))⁻¹) + 24*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)*(gam (p:=p) 3 p)*((24:ZMod (p^9))⁻¹) + 12*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)*(gam (p:=p) 3 p)*((6:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^8*(gam (p:=p) 2 p)^2*((2:ZMod (p^9))⁻¹)^2 + 9*(p:ZMod (p^9))^8*(gam (p:=p) 2 p)^2*((24:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^8*(gam (p:=p) 4 p)*((24:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)^3*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)^3*((6:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^6*(gam (p:=p) 1 p)^3 - 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹) - 9*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)*(gam (p:=p) 2 p)*((6:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^6*(gam (p:=p) 3 p)*((6:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2 - 3*(p:ZMod (p^9))^4*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^2*(gam (p:=p) 1 p))) := by
  have hgp := gam1p_dvd (p:=p) hp
  have hE2p : (p:ZMod (p^9))^4 ∣ ((p:ZMod (p^9))^8*(gam (p:=p) 1 p)^4*((2:ZMod (p^9))⁻¹)^2 + 2*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^4*((24:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^4*((6:ZMod (p^9))⁻¹) - 2*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹)^2 - 12*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((24:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((6:ZMod (p^9))⁻¹) + 16*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)*(gam (p:=p) 3 p)*((24:ZMod (p^9))⁻¹) + 4*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)*(gam (p:=p) 3 p)*((6:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^8*(gam (p:=p) 2 p)^2*((2:ZMod (p^9))⁻¹)^2 + 6*(p:ZMod (p^9))^8*(gam (p:=p) 2 p)^2*((24:ZMod (p^9))⁻¹) - 12*(p:ZMod (p^9))^8*(gam (p:=p) 4 p)*((24:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)^3*((2:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)^3*((6:ZMod (p^9))⁻¹) - 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)*(gam (p:=p) 2 p)*((6:ZMod (p^9))⁻¹) + 4*(p:ZMod (p^9))^6*(gam (p:=p) 3 p)*((6:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2*((2:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2 - 2*(p:ZMod (p^9))^4*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^2*(gam (p:=p) 1 p)) := by
    have hd1 : (p:ZMod (p^9))^4 ∣ (p:ZMod (p^9))^2*(2*(gam (p:=p) 1 p)) := by
      obtain ⟨g,hgg⟩ := hgp; exact ⟨2*g, by rw [hgg]; ring⟩
    have heq : ((p:ZMod (p^9))^8*(gam (p:=p) 1 p)^4*((2:ZMod (p^9))⁻¹)^2 + 2*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^4*((24:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^4*((6:ZMod (p^9))⁻¹) - 2*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹)^2 - 12*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((24:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((6:ZMod (p^9))⁻¹) + 16*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)*(gam (p:=p) 3 p)*((24:ZMod (p^9))⁻¹) + 4*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)*(gam (p:=p) 3 p)*((6:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^8*(gam (p:=p) 2 p)^2*((2:ZMod (p^9))⁻¹)^2 + 6*(p:ZMod (p^9))^8*(gam (p:=p) 2 p)^2*((24:ZMod (p^9))⁻¹) - 12*(p:ZMod (p^9))^8*(gam (p:=p) 4 p)*((24:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)^3*((2:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)^3*((6:ZMod (p^9))⁻¹) - 2*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)*(gam (p:=p) 2 p)*((6:ZMod (p^9))⁻¹) + 4*(p:ZMod (p^9))^6*(gam (p:=p) 3 p)*((6:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2*((2:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2 - 2*(p:ZMod (p^9))^4*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^2*(gam (p:=p) 1 p)) = (p:ZMod (p^9))^2*(2*(gam (p:=p) 1 p)) + (p:ZMod (p^9))^4*((p:ZMod (p^9))^4*(gam (p:=p) 1 p)^4*((2:ZMod (p^9))⁻¹)^2 + 2*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^4*((24:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^4*((6:ZMod (p^9))⁻¹) - 2*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹)^2 - 12*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((24:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((6:ZMod (p^9))⁻¹) + 16*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)*(gam (p:=p) 3 p)*((24:ZMod (p^9))⁻¹) + 4*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)*(gam (p:=p) 3 p)*((6:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^4*(gam (p:=p) 2 p)^2*((2:ZMod (p^9))⁻¹)^2 + 6*(p:ZMod (p^9))^4*(gam (p:=p) 2 p)^2*((24:ZMod (p^9))⁻¹) - 12*(p:ZMod (p^9))^4*(gam (p:=p) 4 p)*((24:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^2*(gam (p:=p) 1 p)^3*((2:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^2*(gam (p:=p) 1 p)^3*((6:ZMod (p^9))⁻¹) - 2*(p:ZMod (p^9))^2*(gam (p:=p) 1 p)*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^2*(gam (p:=p) 1 p)*(gam (p:=p) 2 p)*((6:ZMod (p^9))⁻¹) + 4*(p:ZMod (p^9))^2*(gam (p:=p) 3 p)*((6:ZMod (p^9))⁻¹) + 2*(gam (p:=p) 1 p)^2*((2:ZMod (p^9))⁻¹) + (gam (p:=p) 1 p)^2 - 2*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹)) := by ring
    rw [heq]; exact dvd_add hd1 ⟨(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^4*((2:ZMod (p^9))⁻¹)^2 + 2*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^4*((24:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^4*((6:ZMod (p^9))⁻¹) - 2*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹)^2 - 12*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((24:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((6:ZMod (p^9))⁻¹) + 16*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)*(gam (p:=p) 3 p)*((24:ZMod (p^9))⁻¹) + 4*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)*(gam (p:=p) 3 p)*((6:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^4*(gam (p:=p) 2 p)^2*((2:ZMod (p^9))⁻¹)^2 + 6*(p:ZMod (p^9))^4*(gam (p:=p) 2 p)^2*((24:ZMod (p^9))⁻¹) - 12*(p:ZMod (p^9))^4*(gam (p:=p) 4 p)*((24:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^2*(gam (p:=p) 1 p)^3*((2:ZMod (p^9))⁻¹) + 2*(p:ZMod (p^9))^2*(gam (p:=p) 1 p)^3*((6:ZMod (p^9))⁻¹) - 2*(p:ZMod (p^9))^2*(gam (p:=p) 1 p)*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^2*(gam (p:=p) 1 p)*(gam (p:=p) 2 p)*((6:ZMod (p^9))⁻¹) + 4*(p:ZMod (p^9))^2*(gam (p:=p) 3 p)*((6:ZMod (p^9))⁻¹) + 2*(gam (p:=p) 1 p)^2*((2:ZMod (p^9))⁻¹) + (gam (p:=p) 1 p)^2 - 2*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹), by ring⟩
  have hE3p : (p:ZMod (p^9))^4 ∣ (3*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^4*((2:ZMod (p^9))⁻¹)^2 + 3*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^4*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^4*((24:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^4*((6:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹)^2 - 3*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((24:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((6:ZMod (p^9))⁻¹) + 24*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)*(gam (p:=p) 3 p)*((24:ZMod (p^9))⁻¹) + 12*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)*(gam (p:=p) 3 p)*((6:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^8*(gam (p:=p) 2 p)^2*((2:ZMod (p^9))⁻¹)^2 + 9*(p:ZMod (p^9))^8*(gam (p:=p) 2 p)^2*((24:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^8*(gam (p:=p) 4 p)*((24:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)^3*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)^3*((6:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^6*(gam (p:=p) 1 p)^3 - 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹) - 9*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)*(gam (p:=p) 2 p)*((6:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^6*(gam (p:=p) 3 p)*((6:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2 - 3*(p:ZMod (p^9))^4*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^2*(gam (p:=p) 1 p)) := by
    have hd1 : (p:ZMod (p^9))^4 ∣ (p:ZMod (p^9))^2*(3*(gam (p:=p) 1 p)) := by
      obtain ⟨g,hgg⟩ := hgp; exact ⟨3*g, by rw [hgg]; ring⟩
    have heq : (3*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^4*((2:ZMod (p^9))⁻¹)^2 + 3*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^4*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^4*((24:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^4*((6:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹)^2 - 3*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((24:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((6:ZMod (p^9))⁻¹) + 24*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)*(gam (p:=p) 3 p)*((24:ZMod (p^9))⁻¹) + 12*(p:ZMod (p^9))^8*(gam (p:=p) 1 p)*(gam (p:=p) 3 p)*((6:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^8*(gam (p:=p) 2 p)^2*((2:ZMod (p^9))⁻¹)^2 + 9*(p:ZMod (p^9))^8*(gam (p:=p) 2 p)^2*((24:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^8*(gam (p:=p) 4 p)*((24:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)^3*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)^3*((6:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^6*(gam (p:=p) 1 p)^3 - 6*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹) - 9*(p:ZMod (p^9))^6*(gam (p:=p) 1 p)*(gam (p:=p) 2 p)*((6:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^6*(gam (p:=p) 3 p)*((6:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2 - 3*(p:ZMod (p^9))^4*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^2*(gam (p:=p) 1 p)) = (p:ZMod (p^9))^2*(3*(gam (p:=p) 1 p)) + (p:ZMod (p^9))^4*(3*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^4*((2:ZMod (p^9))⁻¹)^2 + 3*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^4*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^4*((24:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^4*((6:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹)^2 - 3*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((24:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((6:ZMod (p^9))⁻¹) + 24*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)*(gam (p:=p) 3 p)*((24:ZMod (p^9))⁻¹) + 12*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)*(gam (p:=p) 3 p)*((6:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^4*(gam (p:=p) 2 p)^2*((2:ZMod (p^9))⁻¹)^2 + 9*(p:ZMod (p^9))^4*(gam (p:=p) 2 p)^2*((24:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^4*(gam (p:=p) 4 p)*((24:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^2*(gam (p:=p) 1 p)^3*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^2*(gam (p:=p) 1 p)^3*((6:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^2*(gam (p:=p) 1 p)^3 - 6*(p:ZMod (p^9))^2*(gam (p:=p) 1 p)*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹) - 9*(p:ZMod (p^9))^2*(gam (p:=p) 1 p)*(gam (p:=p) 2 p)*((6:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^2*(gam (p:=p) 3 p)*((6:ZMod (p^9))⁻¹) + 3*(gam (p:=p) 1 p)^2*((2:ZMod (p^9))⁻¹) + 3*(gam (p:=p) 1 p)^2 - 3*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹)) := by ring
    rw [heq]; exact dvd_add hd1 ⟨3*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^4*((2:ZMod (p^9))⁻¹)^2 + 3*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^4*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^4*((24:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^4*((6:ZMod (p^9))⁻¹) - 6*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹)^2 - 3*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((24:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)^2*(gam (p:=p) 2 p)*((6:ZMod (p^9))⁻¹) + 24*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)*(gam (p:=p) 3 p)*((24:ZMod (p^9))⁻¹) + 12*(p:ZMod (p^9))^4*(gam (p:=p) 1 p)*(gam (p:=p) 3 p)*((6:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^4*(gam (p:=p) 2 p)^2*((2:ZMod (p^9))⁻¹)^2 + 9*(p:ZMod (p^9))^4*(gam (p:=p) 2 p)^2*((24:ZMod (p^9))⁻¹) - 18*(p:ZMod (p^9))^4*(gam (p:=p) 4 p)*((24:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^2*(gam (p:=p) 1 p)^3*((2:ZMod (p^9))⁻¹) + 3*(p:ZMod (p^9))^2*(gam (p:=p) 1 p)^3*((6:ZMod (p^9))⁻¹) + (p:ZMod (p^9))^2*(gam (p:=p) 1 p)^3 - 6*(p:ZMod (p^9))^2*(gam (p:=p) 1 p)*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹) - 9*(p:ZMod (p^9))^2*(gam (p:=p) 1 p)*(gam (p:=p) 2 p)*((6:ZMod (p^9))⁻¹) + 6*(p:ZMod (p^9))^2*(gam (p:=p) 3 p)*((6:ZMod (p^9))⁻¹) + 3*(gam (p:=p) 1 p)^2*((2:ZMod (p^9))⁻¹) + 3*(gam (p:=p) 1 p)^2 - 3*(gam (p:=p) 2 p)*((2:ZMod (p^9))⁻¹), by ring⟩
  obtain ⟨q2,hq2⟩ := hE2p
  obtain ⟨q3,hq3⟩ := hE3p
  refine dvd_add ⟨3*(Nat.choose (p+p-1) p : ZMod (p^9))^2*q2, by linear_combination (3*(Nat.choose (p+p-1) p : ZMod (p^9))^2)*hq2⟩ ⟨2*(Nat.choose (p+p-1) p : ZMod (p^9))^3*q3, by linear_combination (2*(Nat.choose (p+p-1) p : ZMod (p^9))^3)*hq3⟩

-- all of Ddiag is p^4-divisible
theorem Ddiag_p4 [Fact p.Prime] (hp : 11 ≤ p) :
    (p:ZMod (p^9))^4 ∣ Ddiag (p:=p) := by
  rw [Ddiag_split (by omega)]
  refine dvd_add ?_ ?_
  · have h := offdiag_p4 hp
    refine h.trans (dvd_of_eq ?_)
    exact Finset.sum_congr rfl (fun l _ => by ring)
  · have h := diag_p4 hp
    exact h.trans (dvd_of_eq (by ring))

-- CU is p^4-divisible (each term carries p^k, k>=4)
theorem CU_p4 [Fact p.Prime] : (p:ZMod (p^9))^4 ∣ CU (p:=p) := by
  have key : ∀ (co a b : ZMod (p^9)) (k : ℕ), 4 ≤ k →
      (p:ZMod (p^9))^4 ∣ co * (p:ZMod (p^9))^k * a * b := by
    intro co a b k hk
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ((pow_dvd_pow _ hk).mul_left co) a) b
  rw [CU]
  repeat' apply dvd_add
  all_goals exact key _ _ _ _ (by norm_num)

-- weak base case: A(p^2) ≡ A(p) mod p^4 for p≥11
theorem base_p11_mod_p4 [Fact p.Prime] (hp : 11 ≤ p) :
    (p:ZMod (p^9))^4 ∣ ((A357565 (p^2) : ZMod (p^9)) - (A357565 p : ZMod (p^9))) := by
  rw [base_split (by omega), Uoff_closed hp]
  exact dvd_add CU_p4 (Ddiag_p4 hp)

-- weak base case in native ModEq form: A(p^2) ≡ A(p) [MOD p^4]
theorem base_modeq_p4 [Fact p.Prime] (hp : 11 ≤ p) :
    A357565 (p^2) ≡ A357565 p [MOD p^4] := by
  obtain ⟨c, hc⟩ := base_p11_mod_p4 (p:=p) hp
  rw [← ZMod.natCast_eq_natCast_iff]
  have hdvd : (p:ℕ)^4 ∣ p^9 := pow_dvd_pow p (by norm_num)
  have key := congrArg (ZMod.castHom hdvd (ZMod (p^4))) hc
  rw [map_sub, map_mul, map_pow, map_natCast, map_natCast, map_natCast] at key
  have hp4 : ((p:ZMod (p^4)))^4 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [hp4, zero_mul] at key
  exact sub_eq_zero.mp key
