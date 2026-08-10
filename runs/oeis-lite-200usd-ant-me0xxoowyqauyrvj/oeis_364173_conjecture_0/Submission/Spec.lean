import FormalConjectures.Util.ProblemImports

open scoped Real
open scoped BigOperators

/--
A364173: The sequence defined by the factorial ratio
$$a(n) = \frac{(9n)! (2n)! (3n/2)!}{(9n/2)! (4n)! (3n)! n!}$$
where fractional factorials $x!$ are defined as $\Gamma(x+1)$.
-/
noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

-- ===== Units / coprimality helpers =====

lemma coprime_of_prime_pow {p u t : ℕ} (hp : Nat.Prime p) (h : ¬ p ∣ u) :
    Nat.Coprime u (p ^ (t+1)) := by
  have : Nat.Coprime p u := (hp.coprime_iff_not_dvd).mpr h
  exact (Nat.Coprime.pow_right (t+1) this.symm)

lemma isUnit_iff_notdvd {p u t : ℕ} (hp : Nat.Prime p) :
    IsUnit ((u : ZMod (p^(t+1)))) ↔ ¬ p ∣ u := by
  rw [ZMod.isUnit_iff_coprime]
  constructor
  · intro h hd
    have h2 : Nat.Coprime u p :=
      Nat.Coprime.coprime_dvd_right (dvd_pow_self p (Nat.succ_ne_zero t)) h
    exact (hp.coprime_iff_not_dvd.mp h2.symm) hd
  · intro h
    exact coprime_of_prime_pow hp h

lemma two_unit {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    IsUnit ((2 : ZMod (p^(t+1)))) := by
  have : ((2 : ZMod (p^(t+1)))) = ((2 : ℕ) : ZMod (p^(t+1))) := by push_cast; ring
  rw [this]
  rw [isUnit_iff_notdvd hp]
  intro hd
  have := Nat.le_of_dvd (by norm_num) hd
  omega

lemma three_unit {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    IsUnit ((3 : ZMod (p^(t+1)))) := by
  have : ((3 : ZMod (p^(t+1)))) = ((3 : ℕ) : ZMod (p^(t+1))) := by push_cast; ring
  rw [this]
  rw [isUnit_iff_notdvd hp]
  intro hd
  have := Nat.le_of_dvd (by norm_num) hd
  omega

-- ===== Bridge: sum over p-free residues = sum over units =====

lemma bridge_sum {q : ℕ} [NeZero q] (hq : 1 < q) {A : Type*} [AddCommMonoid A] (g : ZMod q → A) :
    ∑ u ∈ (Finset.Ico 1 q).filter (fun u => IsUnit ((u : ℕ) : ZMod q)), g ((u : ℕ) : ZMod q)
      = ∑ w : (ZMod q)ˣ, g ((w : ZMod q)) := by
  haveI : Fact (1 < q) := ⟨hq⟩
  refine Finset.sum_bij'
    (fun (a : ℕ) (ha : a ∈ (Finset.Ico 1 q).filter (fun u => IsUnit ((u : ℕ) : ZMod q))) =>
      (((Finset.mem_filter.mp ha).2).unit : (ZMod q)ˣ))
    (fun (w : (ZMod q)ˣ) (_ : w ∈ (Finset.univ : Finset (ZMod q)ˣ)) => ((w : ZMod q)).val)
    ?hi ?hj ?left ?right ?h
  case hi => intro a ha; exact Finset.mem_univ _
  case hj =>
    intro w _
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨?_, ZMod.val_lt _⟩, ?_⟩
    · rcases Nat.eq_zero_or_pos ((w : ZMod q)).val with h | h
      · exfalso
        have hh : ((w : ZMod q)) = 0 := by
          have := ZMod.natCast_zmod_val (w : ZMod q)
          rw [h] at this; simpa using this.symm
        exact (w.isUnit.ne_zero) hh
      · exact h
    · rw [ZMod.natCast_zmod_val (w : ZMod q)]; exact w.isUnit
  case left =>
    intro a ha
    have ha2 := (Finset.mem_filter.mp ha)
    have hlt : a < q := (Finset.mem_Ico.mp ha2.1).2
    show ((((Finset.mem_filter.mp ha).2).unit : ZMod q)).val = a
    rw [IsUnit.unit_spec]
    exact ZMod.val_natCast_of_lt hlt
  case right =>
    intro w _
    apply Units.ext
    rw [IsUnit.unit_spec, ZMod.natCast_zmod_val]
  case h =>
    intro a ha
    show g ((a : ℕ) : ZMod q) = g ((((Finset.mem_filter.mp ha).2).unit : ZMod q))
    rw [IsUnit.unit_spec]

-- ===== Foundational sums over units (from Core) =====

lemma sum_units_sq_eq_zero {n : ℕ} [NeZero n] (h3u : IsUnit (3 : ZMod n))
    (hu : IsUnit (2 : ZMod n)) :
    ∑ u : (ZMod n)ˣ, ((u : ZMod n))^2 = 0 := by
  obtain ⟨c, hcval⟩ := hu
  have key : ∑ u : (ZMod n)ˣ, ((u : ZMod n))^2
      = ∑ u : (ZMod n)ˣ, (((c*u : (ZMod n)ˣ) : ZMod n))^2 :=
    (Equiv.sum_comp (Equiv.mulLeft c) (fun v => ((v : ZMod n))^2)).symm
  have expand : ∑ u : (ZMod n)ˣ, (((c*u : (ZMod n)ˣ) : ZMod n))^2
      = (4 : ZMod n) * ∑ u : (ZMod n)ˣ, ((u : ZMod n))^2 := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _
    push_cast; rw [hcval]; ring
  rw [expand] at key
  have h3 : (3 : ZMod n) * (∑ u : (ZMod n)ˣ, ((u : ZMod n))^2) = 0 := by linear_combination -key
  exact (h3u.mul_right_eq_zero).mp h3

lemma sum_units_eq_zero {n : ℕ} [NeZero n] (hu : IsUnit (2 : ZMod n)) :
    ∑ u : (ZMod n)ˣ, ((u : ZMod n)) = 0 := by
  obtain ⟨c, hcval⟩ := hu
  have key : ∑ u : (ZMod n)ˣ, ((u : ZMod n))
      = ∑ u : (ZMod n)ˣ, (((c*u : (ZMod n)ˣ) : ZMod n)) :=
    (Equiv.sum_comp (Equiv.mulLeft c) (fun v => ((v : ZMod n)))).symm
  have expand : ∑ u : (ZMod n)ˣ, (((c*u : (ZMod n)ˣ) : ZMod n))
      = (2 : ZMod n) * ∑ u : (ZMod n)ˣ, ((u : ZMod n)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _
    push_cast; rw [hcval]
  rw [expand] at key
  linear_combination -key

-- ===== prod_add_nilpotent: first-order expansion =====
open Finset in
lemma prod_add_nilpotent {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → R) (e : R) (he : e ^ 2 = 0) :
    ∏ u ∈ s, (a u + e) = (∏ u ∈ s, a u) + e * ∑ u ∈ s, ∏ v ∈ s.erase u, a v := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, ih, Finset.sum_insert hb, Finset.prod_insert hb]
    have key : ∏ v ∈ (insert b s).erase b, a v = ∏ v ∈ s, a v := by
      rw [Finset.erase_insert hb]
    rw [key]
    have key2 : ∀ u ∈ s, ∏ v ∈ (insert b s).erase u, a v = a b * ∏ v ∈ s.erase u, a v := by
      intro u hu
      have hub : u ≠ b := fun h => hb (h ▸ hu)
      have hset : (insert b s).erase u = insert b (s.erase u) := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2 | h3⟩
          · exact Or.inl h2
          · exact Or.inr ⟨h1, h3⟩
        · rintro (h | ⟨h1, h2⟩)
          · subst h; exact ⟨Ne.symm hub, Or.inl rfl⟩
          · exact ⟨h1, Or.inr h2⟩
      rw [hset, Finset.prod_insert (fun h => hb (Finset.mem_of_mem_erase h))]
    rw [Finset.sum_congr rfl key2, ← Finset.mul_sum]
    linear_combination (∑ u ∈ s, ∏ v ∈ s.erase u, a v) * he

-- ===== reflection reindex =====
open Finset in
lemma prod_reflect {M : Type*} [CommMonoid M] {q : ℕ} (S : Finset ℕ)
    (hS : ∀ u ∈ S, (q - u) ∈ S) (hb : ∀ u ∈ S, u ≤ q) (f : ℕ → M) :
    ∏ u ∈ S, f (q - u) = ∏ u ∈ S, f u := by
  apply Finset.prod_bij' (fun (u : ℕ) (_ : u ∈ S) => q - u) (fun (u : ℕ) (_ : u ∈ S) => q - u)
  · intro a ha; exact hS a ha
  · intro a ha; exact hS a ha
  · intro a ha; have := hb a ha; omega
  · intro a ha; have := hb a ha; omega
  · intro a ha; rfl

-- ===== q facts =====
lemma q_ge_five {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) : 5 ≤ p ^ (t+1) :=
  le_trans h5 (Nat.le_self_pow (Nat.succ_ne_zero t) p)

-- ===== F3 over I =====
def Ifs (p t : ℕ) : Finset ℕ := (Finset.Ico 1 (p^(t+1))).filter (fun u => ¬ p ∣ u)

lemma Ifs_eq_isUnit {p t : ℕ} [NeZero (p^(t+1))] (hp : Nat.Prime p) :
    Ifs p t = (Finset.Ico 1 (p^(t+1))).filter (fun u => IsUnit ((u : ℕ) : ZMod (p^(t+1)))) := by
  unfold Ifs
  apply Finset.filter_congr
  intro u _
  rw [isUnit_iff_notdvd hp]

lemma sum_inv_sq_I {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    ∑ u ∈ Ifs p t, (((u : ℕ) : ZMod (p^(t+1)))⁻¹)^2 = 0 := by
  haveI : NeZero (p^(t+1)) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  have hq1 : 1 < p^(t+1) := by have := q_ge_five (t := t) hp h5; omega
  rw [Ifs_eq_isUnit hp, bridge_sum hq1 (fun x => (x⁻¹)^2)]
  have h2u : IsUnit (2 : ZMod (p^(t+1))) := two_unit hp h5
  have h3u : IsUnit (3 : ZMod (p^(t+1))) := three_unit hp h5
  calc ∑ w : (ZMod (p^(t+1)))ˣ, (((w : ZMod (p^(t+1)))⁻¹))^2
      = ∑ w : (ZMod (p^(t+1)))ˣ, (((w⁻¹ : (ZMod (p^(t+1)))ˣ) : ZMod (p^(t+1))))^2 := by
        apply Finset.sum_congr rfl; intro w _; rw [ZMod.inv_coe_unit]
    _ = ∑ w : (ZMod (p^(t+1)))ˣ, (((w : ZMod (p^(t+1)))))^2 :=
        Equiv.sum_comp (Equiv.inv ((ZMod (p^(t+1)))ˣ)) (fun w => ((w : ZMod (p^(t+1))))^2)
    _ = 0 := sum_units_sq_eq_zero h3u h2u

-- ===== Ebar = 0 : the key vanishing =====
open Finset in
lemma Ebar_zero {q : ℕ} [NeZero q] (S : Finset ℕ) (hSlt : ∀ u ∈ S, u < q)
    (hSunit : ∀ u ∈ S, IsUnit ((u : ℕ) : ZMod q))
    (hF3 : ∑ u ∈ S, (((u : ℕ) : ZMod q)⁻¹) ^ 2 = 0) :
    ((∑ u ∈ S, ∏ v ∈ S.erase u, (v * (q - v)) : ℕ) : ZMod q) = 0 := by
  have gval : ∀ v ∈ S, ((q - v : ℕ) : ZMod q) = -((v : ℕ) : ZMod q) := by
    intro v hv
    rw [Nat.cast_sub (le_of_lt (hSlt v hv)), ZMod.natCast_self, zero_sub]
  rw [Nat.cast_sum]
  simp_rw [Nat.cast_prod, Nat.cast_mul]
  set g : ℕ → ZMod q := fun v => ((v : ℕ) : ZMod q) * ((q - v : ℕ) : ZMod q) with hg
  have hgunit : ∀ v ∈ S, IsUnit (g v) := by
    intro v hv
    rw [hg]; simp only
    refine (hSunit v hv).mul ?_
    rw [gval v hv]; exact (hSunit v hv).neg
  -- factor each term
  have factor : ∀ u ∈ S, ∏ v ∈ S.erase u, g v = (∏ v ∈ S, g v) * (g u)⁻¹ := by
    intro u hu
    have h := Finset.prod_erase_mul S g hu
    rw [← h, mul_assoc, ZMod.mul_inv_of_unit (g u) (hgunit u hu), mul_one]
  have hterm : ∀ u ∈ S, (g u)⁻¹ = -(((u : ℕ) : ZMod q)⁻¹) ^ 2 := by
    intro u hu
    have hgu : IsUnit (g u) := hgunit u hu
    have hmul : g u * (-(((u : ℕ) : ZMod q)⁻¹) ^ 2) = 1 := by
      rw [hg]; simp only
      rw [gval u hu]
      have huu : ((u : ℕ) : ZMod q) * ((u : ℕ) : ZMod q)⁻¹ = 1 :=
        ZMod.mul_inv_of_unit _ (hSunit u hu)
      have : ((u : ℕ) : ZMod q) * (-((u : ℕ) : ZMod q)) * (-(((u : ℕ) : ZMod q)⁻¹) ^ 2)
          = (((u : ℕ) : ZMod q) * ((u : ℕ) : ZMod q)⁻¹) ^ 2 := by ring
      rw [this, huu, one_pow]
    calc (g u)⁻¹ = (g u)⁻¹ * (g u * (-(((u : ℕ) : ZMod q)⁻¹) ^ 2)) := by rw [hmul, mul_one]
      _ = ((g u)⁻¹ * g u) * (-(((u : ℕ) : ZMod q)⁻¹) ^ 2) := by ring
      _ = -(((u : ℕ) : ZMod q)⁻¹) ^ 2 := by
          rw [ZMod.inv_mul_of_unit _ hgu, one_mul]
  rw [Finset.sum_congr rfl factor, ← Finset.mul_sum, Finset.sum_congr rfl hterm]
  rw [show (∑ u ∈ S, -(((u : ℕ) : ZMod q)⁻¹) ^ 2) = -(∑ u ∈ S, (((u : ℕ) : ZMod q)⁻¹) ^ 2) from by
    rw [Finset.sum_neg_distrib]]
  rw [hF3, neg_zero, mul_zero]

-- ===== Lifted Wilson (general) =====
open Finset in
lemma lifted_wilson_gen {q : ℕ} (hq5 : 5 ≤ q)
    (S : Finset ℕ) (hSlt : ∀ u ∈ S, u < q)
    (hSref : ∀ u ∈ S, q - u ∈ S)
    (hSunit : ∀ u ∈ S, IsUnit ((u : ℕ) : ZMod q))
    (h2 : IsUnit (2 : ZMod q))
    (hF3 : ∑ u ∈ S, (((u : ℕ) : ZMod q)⁻¹) ^ 2 = 0)
    (N : ℕ) :
    ∏ u ∈ S, ((N * q + u : ℕ) : ZMod (q ^ 3)) = ∏ u ∈ S, ((u : ℕ) : ZMod (q ^ 3)) := by
  haveI : NeZero q := ⟨by omega⟩
  haveI : NeZero (q ^ 3) := ⟨pow_ne_zero _ (by omega)⟩
  set R := ZMod (q ^ 3) with hR
  set Q : R := (q : R) with hQ
  have hQ3 : Q ^ 3 = 0 := by rw [hQ, ← Nat.cast_pow]; exact ZMod.natCast_self _
  set B0 : R := ∏ u ∈ S, ((u : ℕ) : R) with hB0
  set BN : R := ∏ u ∈ S, ((N * q + u : ℕ) : R) with hBN
  set a : ℕ → R := fun u => ((u : ℕ) : R) * ((q - u : ℕ) : R) with ha
  set e : R := (N : R) * ((N : R) + 1) * Q ^ 2 with he
  have he2 : e ^ 2 = 0 := by
    have : e ^ 2 = ((N : R) * ((N : R) + 1)) ^ 2 * (Q ^ 3 * Q) := by rw [he]; ring
    rw [this, hQ3]; ring
  -- term identity
  have term_id : ∀ u ∈ S, ((N * q + u : ℕ) : R) * ((N * q + (q - u) : ℕ) : R) = a u + e := by
    intro u hu
    have hule : u ≤ q := le_of_lt (hSlt u hu)
    have hcast : ((q - u : ℕ) : R) = Q - ((u : ℕ) : R) := by
      rw [Nat.cast_sub hule, hQ]
    have c1 : ((N * q + u : ℕ) : R) = (N : R) * Q + ((u : ℕ) : R) := by
      rw [Nat.cast_add, Nat.cast_mul, hQ]
    have c2 : ((N * q + (q - u) : ℕ) : R) = (N : R) * Q + (Q - ((u : ℕ) : R)) := by
      rw [Nat.cast_add, Nat.cast_mul, hQ, hcast]
    rw [c1, c2, ha]; simp only; rw [hcast, he]; ring
  -- reflection for BN
  have hrefl : ∏ u ∈ S, ((N * q + (q - u) : ℕ) : R) = BN := by
    rw [hBN]
    exact prod_reflect S hSref (fun u hu => le_of_lt (hSlt u hu)) (fun w => ((N * q + w : ℕ) : R))
  -- ∏ a = B0^2
  have ha_prod : ∏ u ∈ S, a u = B0 ^ 2 := by
    rw [ha]; simp only
    rw [Finset.prod_mul_distrib]
    have hp2 : ∏ u ∈ S, ((q - u : ℕ) : R) = ∏ u ∈ S, ((u : ℕ) : R) :=
      prod_reflect S hSref (fun u hu => le_of_lt (hSlt u hu)) (fun w => ((w : ℕ) : R))
    rw [hp2, hB0]; ring
  -- E vanishes
  have hE_zero : e * (∑ u ∈ S, ∏ v ∈ S.erase u, a v) = 0 := by
    set E : R := ∑ u ∈ S, ∏ v ∈ S.erase u, a v with hE
    have hE_cast : E = ((∑ u ∈ S, ∏ v ∈ S.erase u, (v * (q - v)) : ℕ) : R) := by
      rw [hE, Nat.cast_sum]
      apply Finset.sum_congr rfl; intro u hu
      rw [Nat.cast_prod]
      apply Finset.prod_congr rfl; intro v hv
      rw [ha]; simp only; rw [Nat.cast_mul]
    have hdvd : q ∣ (∑ u ∈ S, ∏ v ∈ S.erase u, (v * (q - v)) : ℕ) := by
      rw [← ZMod.natCast_eq_zero_iff]
      exact Ebar_zero S hSlt hSunit hF3
    obtain ⟨k, hk⟩ := hdvd
    have hq3z : ((q ^ 3 : ℕ) : R) = 0 := ZMod.natCast_self _
    have hQ2E : Q ^ 2 * E = 0 := by
      rw [hE_cast, hk, hQ,
        show (↑q : R) ^ 2 * ((q * k : ℕ) : R) = ((q ^ 3 : ℕ) : R) * (k : R) from by push_cast; ring,
        hq3z, zero_mul]
    rw [show e * E = (N : R) * ((N : R) + 1) * (Q ^ 2 * E) from by rw [he]; ring, hQ2E, mul_zero]
  -- BN^2 = B0^2
  have hsq : BN ^ 2 = B0 ^ 2 := by
    have step1 : BN ^ 2 = ∏ u ∈ S, (((N * q + u : ℕ) : R) * ((N * q + (q - u) : ℕ) : R)) := by
      rw [Finset.prod_mul_distrib, hrefl, ← hBN, sq]
    rw [step1, Finset.prod_congr rfl term_id, prod_add_nilpotent S a e he2, ha_prod, hE_zero,
      add_zero]
  -- BN + B0 is a unit
  have hbc : BN + B0 = ((∏ u ∈ S, (N * q + u) + ∏ u ∈ S, u : ℕ) : R) := by
    rw [hBN, hB0, Nat.cast_add, Nat.cast_prod, Nat.cast_prod]
  have hcunit : IsUnit (∏ u ∈ S, ((u : ℕ) : ZMod q)) :=
    Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one hSunit
  have hbq : ((∏ u ∈ S, (N * q + u) : ℕ) : ZMod q) = ∏ u ∈ S, ((u : ℕ) : ZMod q) := by
    rw [Nat.cast_prod]; apply Finset.prod_congr rfl; intro u hu
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
  have hsumq : ((∏ u ∈ S, (N * q + u) + ∏ u ∈ S, u : ℕ) : ZMod q)
      = 2 * ∏ u ∈ S, ((u : ℕ) : ZMod q) := by
    rw [Nat.cast_add, hbq, Nat.cast_prod]; ring
  have hcop : Nat.Coprime (∏ u ∈ S, (N * q + u) + ∏ u ∈ S, u) q := by
    rw [← ZMod.isUnit_iff_coprime, hsumq]; exact h2.mul hcunit
  have hunit : IsUnit (BN + B0) := by
    rw [hbc, ZMod.isUnit_iff_coprime]; exact Nat.Coprime.pow_right 3 hcop
  -- conclude BN = B0
  have hfac : (BN - B0) * (BN + B0) = 0 := by
    have : (BN - B0) * (BN + B0) = BN ^ 2 - B0 ^ 2 := by ring
    rw [this, hsq, sub_self]
  have hsub : BN - B0 = 0 := (IsUnit.mul_left_eq_zero hunit).mp hfac
  exact sub_eq_zero.mp hsub

-- ===== Ifs membership helpers and wilson_Ifs =====
lemma mem_Ifs {p t u : ℕ} : u ∈ Ifs p t ↔ 1 ≤ u ∧ u < p^(t+1) ∧ ¬ p ∣ u := by
  unfold Ifs; rw [Finset.mem_filter, Finset.mem_Ico]; tauto

lemma Ifs_lt {p t : ℕ} : ∀ u ∈ Ifs p t, u < p^(t+1) := fun u hu => (mem_Ifs.mp hu).2.1

lemma Ifs_reflect {p t : ℕ} (hp : Nat.Prime p) : ∀ u ∈ Ifs p t, p^(t+1) - u ∈ Ifs p t := by
  intro u hu; rw [mem_Ifs] at hu ⊢
  obtain ⟨h1, h2, h3⟩ := hu
  refine ⟨by omega, by omega, ?_⟩
  intro hd
  have hq : p ∣ p^(t+1) := dvd_pow_self p (Nat.succ_ne_zero t)
  have : p ∣ u := by
    have hh := Nat.dvd_sub hq hd
    rwa [Nat.sub_sub_self (le_of_lt h2)] at hh
  exact h3 this

lemma Ifs_unit {p t : ℕ} (hp : Nat.Prime p) :
    ∀ u ∈ Ifs p t, IsUnit ((u : ℕ) : ZMod (p^(t+1))) := by
  intro u hu; rw [mem_Ifs] at hu; rw [isUnit_iff_notdvd hp]; exact hu.2.2

lemma wilson_Ifs {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) (N : ℕ) :
    ∏ u ∈ Ifs p t, ((N * p^(t+1) + u : ℕ) : ZMod ((p^(t+1))^3))
      = ∏ u ∈ Ifs p t, ((u : ℕ) : ZMod ((p^(t+1))^3)) :=
  lifted_wilson_gen (q_ge_five hp h5) (Ifs p t) Ifs_lt (Ifs_reflect hp) (Ifs_unit hp)
    (two_unit hp h5) (sum_inv_sq_I hp h5) N

-- ===== W mod B0 =====
def Wp (p x : ℕ) : ℕ := ∏ j ∈ (Finset.Ico 1 (x+1)).filter (fun j => ¬ p ∣ j), j

lemma Wp_block_eq {p t s : ℕ} (hp : Nat.Prime p) :
    (Finset.Ico (s * p^(t+1) + 1) ((s+1) * p^(t+1) + 1)).filter (fun j => ¬ p ∣ j)
      = (Ifs p t).image (fun u => s * p^(t+1) + u) := by
  have hqd : p ∣ p^(t+1) := dvd_pow_self p (Nat.succ_ne_zero t)
  have hsq : p ∣ s * p^(t+1) := hqd.mul_left s
  ext j
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image, mem_Ifs]
  constructor
  · rintro ⟨⟨hj1, hj2⟩, hpj⟩
    have hsucc : (s+1) * p^(t+1) = s * p^(t+1) + p^(t+1) := by ring
    have hjlt : j < (s+1) * p^(t+1) := by
      rcases Nat.lt_or_ge j ((s+1) * p^(t+1)) with h | h
      · exact h
      · exfalso; apply hpj
        have hje : j = (s+1) * p^(t+1) := by omega
        rw [hje]; exact hqd.mul_left (s+1)
    refine ⟨j - s * p^(t+1), ⟨by omega, by omega, ?_⟩, by omega⟩
    intro hd
    apply hpj
    have : p ∣ (s * p^(t+1) + (j - s * p^(t+1))) := hsq.add hd
    have heq : s * p^(t+1) + (j - s * p^(t+1)) = j := by omega
    rwa [heq] at this
  · rintro ⟨u, ⟨hu1, hu2, hu3⟩, rfl⟩
    have hsucc : (s+1) * p^(t+1) = s * p^(t+1) + p^(t+1) := by ring
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro hd
    apply hu3
    have hh := Nat.dvd_sub hd hsq
    have heq : s * p^(t+1) + u - s * p^(t+1) = u := by omega
    rwa [heq] at hh

lemma Wp_modB0 {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) (s : ℕ) :
    ((Wp p (s * p^(t+1)) : ℕ) : ZMod ((p^(t+1))^3))
      = (∏ u ∈ Ifs p t, ((u : ℕ) : ZMod ((p^(t+1))^3)))^s := by
  induction s with
  | zero => rw [Nat.zero_mul, pow_zero]; simp [Wp]
  | succ s ih =>
    have hsplit : (Finset.Ico 1 ((s+1) * p^(t+1) + 1)).filter (fun j => ¬ p ∣ j)
        = ((Finset.Ico 1 (s * p^(t+1) + 1)).filter (fun j => ¬ p ∣ j))
          ∪ ((Finset.Ico (s * p^(t+1) + 1) ((s+1) * p^(t+1) + 1)).filter (fun j => ¬ p ∣ j)) := by
      rw [← Finset.filter_union, Finset.Ico_union_Ico_eq_Ico (by omega) (by nlinarith [pow_pos hp.pos (t+1)])]
    have hdisj : Disjoint ((Finset.Ico 1 (s * p^(t+1) + 1)).filter (fun j => ¬ p ∣ j))
        ((Finset.Ico (s * p^(t+1) + 1) ((s+1) * p^(t+1) + 1)).filter (fun j => ¬ p ∣ j)) := by
      apply Finset.disjoint_filter_filter
      rw [Finset.disjoint_left]; intro x hx hx2
      rw [Finset.mem_Ico] at hx hx2; omega
    have hWsucc : Wp p ((s+1) * p^(t+1))
        = Wp p (s * p^(t+1)) * ∏ j ∈ (Finset.Ico (s * p^(t+1) + 1) ((s+1) * p^(t+1) + 1)).filter (fun j => ¬ p ∣ j), j := by
      unfold Wp; rw [hsplit, Finset.prod_union hdisj]
    rw [hWsucc, Nat.cast_mul, ih, Wp_block_eq hp,
      Finset.prod_image (fun a _ b _ h => Nat.add_left_cancel h), Nat.cast_prod,
      wilson_Ifs hp h5 s]
    exact (pow_succ _ s).symm

-- ===== a, factorial decomposition, even real identity =====

lemma factorial_decomp (p M : ℕ) (hp : 0 < p) :
    (M * p).factorial = p ^ M * M.factorial * Wp p (M * p) := by
  have hfact : ∏ j ∈ Finset.Ico 1 (M*p+1), j = (M*p).factorial := Finset.prod_Ico_id_eq_factorial (M*p)
  have hsplit := Finset.prod_filter_mul_prod_filter_not (Finset.Ico 1 (M*p+1)) (fun j => ¬ p ∣ j) (fun j => j)
  have hdiv : ∏ j ∈ (Finset.Ico 1 (M*p+1)).filter (fun j => ¬ ¬ p ∣ j), j = p ^ M * M.factorial := by
    have hset : (Finset.Ico 1 (M*p+1)).filter (fun j => ¬ ¬ p ∣ j)
        = (Finset.Ico 1 (M+1)).image (fun i => p * i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image, not_not]
      constructor
      · rintro ⟨⟨hj1, hj2⟩, hpj⟩
        obtain ⟨i, rfl⟩ := hpj
        have hi0 : 0 < i := by
          rcases Nat.eq_zero_or_pos i with h | h
          · simp [h] at hj1
          · exact h
        have hiM : i ≤ M := by
          by_contra hc; push_neg at hc
          have : p * (M+1) ≤ p * i := Nat.mul_le_mul_left p hc
          nlinarith [this, hj2]
        exact ⟨i, ⟨hi0, by omega⟩, by ring⟩
      · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
        refine ⟨⟨?_, ?_⟩, Dvd.intro i rfl⟩
        · nlinarith
        · have : p * i ≤ p * M := Nat.mul_le_mul_left p (by omega)
          nlinarith
    rw [hset, Finset.prod_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hp h)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_Ico_id_eq_factorial]
    congr 1
    simp [Nat.card_Ico]
  rw [← hfact, ← hsplit, hdiv]
  unfold Wp
  ring

lemma a_even (k : ℕ) :
    a (2 * k) = (((18*k).factorial : ℝ) * ((4*k).factorial : ℝ) * ((3*k).factorial : ℝ)) /
      (((9*k).factorial : ℝ) * ((8*k).factorial : ℝ) * ((6*k).factorial : ℝ) * ((2*k).factorial : ℝ)) := by
  unfold a; simp only
  set nr : ℝ := ((2*k : ℕ) : ℝ) with hnr
  have g1 : (9:ℝ) * nr + 1 = ((18*k : ℕ):ℝ) + 1 := by rw [hnr]; push_cast; ring
  have g2 : (2:ℝ) * nr + 1 = ((4*k : ℕ):ℝ) + 1 := by rw [hnr]; push_cast; ring
  have g3 : (3/2:ℝ) * nr + 1 = ((3*k : ℕ):ℝ) + 1 := by rw [hnr]; push_cast; ring
  have g4 : (9/2:ℝ) * nr + 1 = ((9*k : ℕ):ℝ) + 1 := by rw [hnr]; push_cast; ring
  have g5 : (4:ℝ) * nr + 1 = ((8*k : ℕ):ℝ) + 1 := by rw [hnr]; push_cast; ring
  have g6 : (3:ℝ) * nr + 1 = ((6*k : ℕ):ℝ) + 1 := by rw [hnr]; push_cast; ring
  have g7 : nr + 1 = ((2*k : ℕ):ℝ) + 1 := by rw [hnr]
  rw [g1, g2, g3, g4, g5, g6, g7, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
    Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
    Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial]

-- ===== z and even integer identity =====
section Zsec
variable (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ))))

noncomputable def z (m : ℕ) : ℤ := Classical.choose (h_int m)

lemma z_spec (m : ℕ) : ((z h_int m : ℝ)) = a m := Classical.choose_spec (h_int m)

lemma even_int_id (k : ℕ) :
    z h_int (2 * k) * (((9*k).factorial * (8*k).factorial * (6*k).factorial * (2*k).factorial : ℕ) : ℤ)
      = (((18*k).factorial * (4*k).factorial * (3*k).factorial : ℕ) : ℤ) := by
  have hr := z_spec h_int (2 * k)
  rw [a_even] at hr
  have hne : (((9*k).factorial : ℝ) * ((8*k).factorial : ℝ) * ((6*k).factorial : ℝ) * ((2*k).factorial : ℝ)) ≠ 0 := by
    have h1 : (0:ℝ) < ((9*k).factorial : ℝ) := by exact_mod_cast (Nat.factorial_pos _)
    have h2 : (0:ℝ) < ((8*k).factorial : ℝ) := by exact_mod_cast (Nat.factorial_pos _)
    have h3 : (0:ℝ) < ((6*k).factorial : ℝ) := by exact_mod_cast (Nat.factorial_pos _)
    have h4 : (0:ℝ) < ((2*k).factorial : ℝ) := by exact_mod_cast (Nat.factorial_pos _)
    positivity
  have key : (z h_int (2*k) : ℝ) * (((9*k).factorial : ℝ) * ((8*k).factorial : ℝ) * ((6*k).factorial : ℝ) * ((2*k).factorial : ℝ))
      = (((18*k).factorial : ℝ) * ((4*k).factorial : ℝ) * ((3*k).factorial : ℝ)) := by
    rw [hr]; field_simp
  exact_mod_cast key
end Zsec

-- ===== W_cast and unit helpers =====
lemma W_cast {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) (c k sk : ℕ) (hk : k = p^t * sk) :
    ((Wp p (c * k * p) : ℕ) : ZMod ((p^(t+1))^3))
      = (∏ u ∈ Ifs p t, ((u : ℕ) : ZMod ((p^(t+1))^3)))^(c * sk) := by
  have harg : c * k * p = (c * sk) * p^(t+1) := by rw [hk, pow_succ]; ring
  rw [harg]; exact Wp_modB0 hp h5 (c * sk)

lemma Ifs_unit3 {p t : ℕ} (hp : Nat.Prime p) :
    ∀ u ∈ Ifs p t, IsUnit ((u : ℕ) : ZMod ((p^(t+1))^3)) := by
  intro u hu; rw [mem_Ifs] at hu; rw [ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.pow_right 3 (coprime_of_prime_pow hp hu.2.2)

lemma B0_unit {p t : ℕ} (hp : Nat.Prime p) :
    IsUnit (∏ u ∈ Ifs p t, ((u : ℕ) : ZMod ((p^(t+1))^3))) :=
  Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (Ifs_unit3 hp)

-- ===== EVEN STEP =====
lemma even_step (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ))))
    {p t k : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) (hdvd : p^t ∣ k) :
    (p : ℤ)^(3 + 3*t) ∣ (z h_int (2*(k*p)) - z h_int (2*k)) := by
  obtain ⟨sk, hsk⟩ := hdvd
  have fdec : ∀ c : ℕ, (c*(k*p)).factorial = p^(c*k) * (c*k).factorial * Wp p (c*k*p) := by
    intro c
    have hcc : c*(k*p) = (c*k)*p := by ring
    rw [hcc, factorial_decomp p (c*k) hp.pos]
  have IDk := even_int_id h_int k
  have IDkp := even_int_id h_int (k*p)
  have hQe : (((9*(k*p)).factorial * (8*(k*p)).factorial * (6*(k*p)).factorial * (2*(k*p)).factorial : ℕ))
     = p^(25*k) * ((9*k).factorial*(8*k).factorial*(6*k).factorial*(2*k).factorial)
       * (Wp p (9*k*p)*Wp p (8*k*p)*Wp p (6*k*p)*Wp p (2*k*p)) := by
     rw [fdec 9, fdec 8, fdec 6, fdec 2]; ring
  have hPe : (((18*(k*p)).factorial * (4*(k*p)).factorial * (3*(k*p)).factorial : ℕ))
     = p^(25*k) * ((18*k).factorial*(4*k).factorial*(3*k).factorial)
       * (Wp p (18*k*p)*Wp p (4*k*p)*Wp p (3*k*p)) := by
     rw [fdec 18, fdec 4, fdec 3]; ring
  rw [hQe, hPe] at IDkp
  push_cast at IDk IDkp
  have hF : ((p:ℤ)^(25*k) * (((9*k).factorial:ℤ)*((8*k).factorial:ℤ)*((6*k).factorial:ℤ)*((2*k).factorial:ℤ))) ≠ 0 := by
    positivity
  have evenID : z h_int (2*(k*p)) * (((Wp p (9*k*p):ℤ))*((Wp p (8*k*p):ℤ))*((Wp p (6*k*p):ℤ))*((Wp p (2*k*p):ℤ)))
              = z h_int (2*k) * (((Wp p (18*k*p):ℤ))*((Wp p (4*k*p):ℤ))*((Wp p (3*k*p):ℤ))) := by
    apply mul_left_cancel₀ hF
    push_cast
    linear_combination IDkp - ((p:ℤ)^(25*k) * (((Wp p (18*k*p):ℤ))*((Wp p (4*k*p):ℤ))*((Wp p (3*k*p):ℤ)))) * IDk
  -- mod q^3
  have hcast := congrArg (fun x : ℤ => ((x : ZMod ((p^(t+1))^3)))) evenID
  simp only at hcast
  push_cast at hcast
  rw [W_cast hp h5 9 k sk hsk, W_cast hp h5 8 k sk hsk, W_cast hp h5 6 k sk hsk,
      W_cast hp h5 2 k sk hsk, W_cast hp h5 18 k sk hsk, W_cast hp h5 4 k sk hsk,
      W_cast hp h5 3 k sk hsk] at hcast
  set Bp : ZMod ((p^(t+1))^3) := ∏ u ∈ Ifs p t, ((u:ℕ):ZMod ((p^(t+1))^3)) with hBp
  have hPdn : Bp^(9*sk)*Bp^(8*sk)*Bp^(6*sk)*Bp^(2*sk) = Bp^(18*sk)*Bp^(4*sk)*Bp^(3*sk) := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]; congr 1; ring
  have hBpunit : IsUnit Bp := hBp ▸ B0_unit hp
  have hPdunit : IsUnit (Bp^(9*sk)*Bp^(8*sk)*Bp^(6*sk)*Bp^(2*sk)) :=
    (((hBpunit.pow _).mul (hBpunit.pow _)).mul (hBpunit.pow _)).mul (hBpunit.pow _)
  rw [← hPdn] at hcast
  have hzero : ((z h_int (2*(k*p)) : ℤ) : ZMod ((p^(t+1))^3)) - ((z h_int (2*k) : ℤ) : ZMod ((p^(t+1))^3)) = 0 := by
    have hmul : (((z h_int (2*(k*p)) : ℤ) : ZMod ((p^(t+1))^3)) - ((z h_int (2*k) : ℤ) : ZMod ((p^(t+1))^3)))
        * (Bp^(9*sk)*Bp^(8*sk)*Bp^(6*sk)*Bp^(2*sk)) = 0 := by
      rw [sub_mul, hcast, sub_self]
    exact (IsUnit.mul_left_eq_zero hPdunit).mp hmul
  have hzz : ((z h_int (2*(k*p)) - z h_int (2*k) : ℤ) : ZMod ((p^(t+1))^3)) = 0 := by
    push_cast; linear_combination hzero
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hzz
  have hmod : (((p^(t+1))^3 : ℕ) : ℤ) = (p:ℤ)^(3 + 3*t) := by push_cast; ring
  rw [hmod] at hzz
  exact hzz

-- ===== Generalized Ebar and lifted Wilson (reflection point r*q) =====
open Finset in
lemma Ebar_zeroR {q : ℕ} [NeZero q] (r : ℕ) (S : Finset ℕ) (hSle : ∀ u ∈ S, u ≤ r * q)
    (hSunit : ∀ u ∈ S, IsUnit ((u : ℕ) : ZMod q))
    (hF3 : ∑ u ∈ S, (((u : ℕ) : ZMod q)⁻¹) ^ 2 = 0) :
    ((∑ u ∈ S, ∏ v ∈ S.erase u, (v * (r * q - v)) : ℕ) : ZMod q) = 0 := by
  have hrq0 : ((r * q : ℕ) : ZMod q) = 0 := by rw [Nat.cast_mul, ZMod.natCast_self, mul_zero]
  have gval : ∀ v ∈ S, ((r * q - v : ℕ) : ZMod q) = -((v : ℕ) : ZMod q) := by
    intro v hv
    rw [Nat.cast_sub (hSle v hv), hrq0, zero_sub]
  rw [Nat.cast_sum]
  simp_rw [Nat.cast_prod, Nat.cast_mul]
  set g : ℕ → ZMod q := fun v => ((v : ℕ) : ZMod q) * ((r * q - v : ℕ) : ZMod q) with hg
  have hgunit : ∀ v ∈ S, IsUnit (g v) := by
    intro v hv
    rw [hg]; simp only
    refine (hSunit v hv).mul ?_
    rw [gval v hv]; exact (hSunit v hv).neg
  have factor : ∀ u ∈ S, ∏ v ∈ S.erase u, g v = (∏ v ∈ S, g v) * (g u)⁻¹ := by
    intro u hu
    have h := Finset.prod_erase_mul S g hu
    rw [← h, mul_assoc, ZMod.mul_inv_of_unit (g u) (hgunit u hu), mul_one]
  have hterm : ∀ u ∈ S, (g u)⁻¹ = -(((u : ℕ) : ZMod q)⁻¹) ^ 2 := by
    intro u hu
    have hgu : IsUnit (g u) := hgunit u hu
    have hmul : g u * (-(((u : ℕ) : ZMod q)⁻¹) ^ 2) = 1 := by
      rw [hg]; simp only
      rw [gval u hu]
      have huu : ((u : ℕ) : ZMod q) * ((u : ℕ) : ZMod q)⁻¹ = 1 :=
        ZMod.mul_inv_of_unit _ (hSunit u hu)
      have : ((u : ℕ) : ZMod q) * (-((u : ℕ) : ZMod q)) * (-(((u : ℕ) : ZMod q)⁻¹) ^ 2)
          = (((u : ℕ) : ZMod q) * ((u : ℕ) : ZMod q)⁻¹) ^ 2 := by ring
      rw [this, huu, one_pow]
    calc (g u)⁻¹ = (g u)⁻¹ * (g u * (-(((u : ℕ) : ZMod q)⁻¹) ^ 2)) := by rw [hmul, mul_one]
      _ = ((g u)⁻¹ * g u) * (-(((u : ℕ) : ZMod q)⁻¹) ^ 2) := by ring
      _ = -(((u : ℕ) : ZMod q)⁻¹) ^ 2 := by
          rw [ZMod.inv_mul_of_unit _ hgu, one_mul]
  rw [Finset.sum_congr rfl factor, ← Finset.mul_sum, Finset.sum_congr rfl hterm]
  rw [show (∑ u ∈ S, -(((u : ℕ) : ZMod q)⁻¹) ^ 2) = -(∑ u ∈ S, (((u : ℕ) : ZMod q)⁻¹) ^ 2) from by
    rw [Finset.sum_neg_distrib]]
  rw [hF3, neg_zero, mul_zero]

open Finset in
lemma lifted_wilson_R {q : ℕ} (hq5 : 5 ≤ q) (r : ℕ)
    (S : Finset ℕ) (hSle : ∀ u ∈ S, u ≤ r * q)
    (hSref : ∀ u ∈ S, r * q - u ∈ S)
    (hSunit : ∀ u ∈ S, IsUnit ((u : ℕ) : ZMod q))
    (h2 : IsUnit (2 : ZMod q))
    (hF3 : ∑ u ∈ S, (((u : ℕ) : ZMod q)⁻¹) ^ 2 = 0)
    (N : ℕ) :
    ∏ u ∈ S, ((N * q + u : ℕ) : ZMod (q ^ 3)) = ∏ u ∈ S, ((u : ℕ) : ZMod (q ^ 3)) := by
  haveI : NeZero q := ⟨by omega⟩
  haveI : NeZero (q ^ 3) := ⟨pow_ne_zero _ (by omega)⟩
  set RR := ZMod (q ^ 3) with hRR
  set Q : RR := (q : RR) with hQ
  have hQ3 : Q ^ 3 = 0 := by rw [hQ, ← Nat.cast_pow]; exact ZMod.natCast_self _
  set B0 : RR := ∏ u ∈ S, ((u : ℕ) : RR) with hB0
  set BN : RR := ∏ u ∈ S, ((N * q + u : ℕ) : RR) with hBN
  set a : ℕ → RR := fun u => ((u : ℕ) : RR) * ((r * q - u : ℕ) : RR) with ha
  set e : RR := (N : RR) * ((N : RR) + (r : RR)) * Q ^ 2 with he
  have he2 : e ^ 2 = 0 := by
    have : e ^ 2 = ((N : RR) * ((N : RR) + (r : RR))) ^ 2 * (Q ^ 3 * Q) := by rw [he]; ring
    rw [this, hQ3]; ring
  have term_id : ∀ u ∈ S, ((N * q + u : ℕ) : RR) * ((N * q + (r * q - u) : ℕ) : RR) = a u + e := by
    intro u hu
    have hcast : ((r * q - u : ℕ) : RR) = (r : RR) * Q - ((u : ℕ) : RR) := by
      rw [Nat.cast_sub (hSle u hu), Nat.cast_mul, hQ]
    have c1 : ((N * q + u : ℕ) : RR) = (N : RR) * Q + ((u : ℕ) : RR) := by
      rw [Nat.cast_add, Nat.cast_mul, hQ]
    have c2 : ((N * q + (r * q - u) : ℕ) : RR) = (N : RR) * Q + ((r : RR) * Q - ((u : ℕ) : RR)) := by
      rw [Nat.cast_add, Nat.cast_mul, hQ, hcast]
    rw [c1, c2, ha]; simp only; rw [hcast, he]; ring
  have hrefl : ∏ u ∈ S, ((N * q + (r * q - u) : ℕ) : RR) = BN := by
    rw [hBN]
    exact prod_reflect (q := r * q) S hSref hSle (fun w => ((N * q + w : ℕ) : RR))
  have ha_prod : ∏ u ∈ S, a u = B0 ^ 2 := by
    rw [ha]; simp only
    rw [Finset.prod_mul_distrib]
    have hp2 : ∏ u ∈ S, ((r * q - u : ℕ) : RR) = ∏ u ∈ S, ((u : ℕ) : RR) :=
      prod_reflect (q := r * q) S hSref hSle (fun w => ((w : ℕ) : RR))
    rw [hp2, hB0]; ring
  have hE_zero : e * (∑ u ∈ S, ∏ v ∈ S.erase u, a v) = 0 := by
    set E : RR := ∑ u ∈ S, ∏ v ∈ S.erase u, a v with hE
    have hE_cast : E = ((∑ u ∈ S, ∏ v ∈ S.erase u, (v * (r * q - v)) : ℕ) : RR) := by
      rw [hE, Nat.cast_sum]
      apply Finset.sum_congr rfl; intro u hu
      rw [Nat.cast_prod]
      apply Finset.prod_congr rfl; intro v hv
      rw [ha]; simp only; rw [Nat.cast_mul]
    have hdvd : q ∣ (∑ u ∈ S, ∏ v ∈ S.erase u, (v * (r * q - v)) : ℕ) := by
      rw [← ZMod.natCast_eq_zero_iff]
      exact Ebar_zeroR r S hSle hSunit hF3
    obtain ⟨k, hk⟩ := hdvd
    have hq3z : ((q ^ 3 : ℕ) : RR) = 0 := ZMod.natCast_self _
    have hQ2E : Q ^ 2 * E = 0 := by
      rw [hE_cast, hk, hQ,
        show (↑q : RR) ^ 2 * ((q * k : ℕ) : RR) = ((q ^ 3 : ℕ) : RR) * (k : RR) from by push_cast; ring,
        hq3z, zero_mul]
    rw [show e * E = (N : RR) * ((N : RR) + (r : RR)) * (Q ^ 2 * E) from by rw [he]; ring, hQ2E, mul_zero]
  have hsq : BN ^ 2 = B0 ^ 2 := by
    have step1 : BN ^ 2 = ∏ u ∈ S, (((N * q + u : ℕ) : RR) * ((N * q + (r * q - u) : ℕ) : RR)) := by
      rw [Finset.prod_mul_distrib, hrefl, ← hBN, sq]
    rw [step1, Finset.prod_congr rfl term_id, prod_add_nilpotent S a e he2, ha_prod, hE_zero,
      add_zero]
  have hbc : BN + B0 = ((∏ u ∈ S, (N * q + u) + ∏ u ∈ S, u : ℕ) : RR) := by
    rw [hBN, hB0, Nat.cast_add, Nat.cast_prod, Nat.cast_prod]
  have hcunit : IsUnit (∏ u ∈ S, ((u : ℕ) : ZMod q)) :=
    Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one hSunit
  have hbq : ((∏ u ∈ S, (N * q + u) : ℕ) : ZMod q) = ∏ u ∈ S, ((u : ℕ) : ZMod q) := by
    rw [Nat.cast_prod]; apply Finset.prod_congr rfl; intro u hu
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
  have hsumq : ((∏ u ∈ S, (N * q + u) + ∏ u ∈ S, u : ℕ) : ZMod q)
      = 2 * ∏ u ∈ S, ((u : ℕ) : ZMod q) := by
    rw [Nat.cast_add, hbq, Nat.cast_prod]; ring
  have hcop : Nat.Coprime (∏ u ∈ S, (N * q + u) + ∏ u ∈ S, u) q := by
    rw [← ZMod.isUnit_iff_coprime, hsumq]; exact h2.mul hcunit
  have hunit : IsUnit (BN + B0) := by
    rw [hbc, ZMod.isUnit_iff_coprime]; exact Nat.Coprime.pow_right 3 hcop
  have hfac : (BN - B0) * (BN + B0) = 0 := by
    have : (BN - B0) * (BN + B0) = BN ^ 2 - B0 ^ 2 := by ring
    rw [this, hsq, sub_self]
  have hsub : BN - B0 = 0 := (IsUnit.mul_left_eq_zero hunit).mp hfac
  exact sub_eq_zero.mp hsub

-- ===== Half-range sets H, A and half-range F3 =====
def Hf (p t : ℕ) : Finset ℕ := (Finset.Ico 1 (p^(t+1)/2 + 1)).filter (fun u => ¬ p ∣ u)
def Af (p t : ℕ) : Finset ℕ := (Finset.Ico (p^(t+1)/2 + 1) (p^(t+1))).filter (fun u => ¬ p ∣ u)

lemma q_odd {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) : ¬ 2 ∣ p^(t+1) := by
  intro h
  have hdvd : (2:ℕ) ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hdvd
  omega

lemma Ifs_eq_HA {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    Ifs p t = Hf p t ∪ Af p t ∧ Disjoint (Hf p t) (Af p t) := by
  have hq5 : 5 ≤ p^(t+1) := q_ge_five hp h5
  constructor
  · unfold Ifs Hf Af
    rw [← Finset.filter_union, Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
  · apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]; intro x hx hx2
    rw [Finset.mem_Ico] at hx hx2; omega

lemma mem_Hf {p t u : ℕ} : u ∈ Hf p t ↔ 1 ≤ u ∧ u ≤ p^(t+1)/2 ∧ ¬ p ∣ u := by
  unfold Hf; rw [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨h1,h2⟩,h3⟩; exact ⟨h1, by omega, h3⟩
  · rintro ⟨h1,h2,h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩

lemma Af_eq_reflect {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    Af p t = (Hf p t).image (fun w => p^(t+1) - w) := by
  have hq5 : 5 ≤ p^(t+1) := q_ge_five hp h5
  have hodd : p^(t+1) % 2 = 1 := by have h2 := q_odd (t := t) hp h5; omega
  have hqd : p ∣ p^(t+1) := dvd_pow_self p (Nat.succ_ne_zero t)
  ext x
  simp only [Af, Finset.mem_filter, Finset.mem_Ico, Finset.mem_image, mem_Hf]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨p^(t+1) - x, ⟨by omega, by omega, ?_⟩, by omega⟩
    intro hd
    apply h3
    have hh := Nat.dvd_sub hqd hd
    rwa [Nat.sub_sub_self (by omega)] at hh
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, rfl⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro hd
    apply hw3
    have hh := Nat.dvd_sub hqd hd
    rwa [Nat.sub_sub_self (by omega)] at hh

lemma sum_inv_sq_Hf {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    ∑ w ∈ Hf p t, (((w : ℕ) : ZMod (p^(t+1)))⁻¹)^2 = 0 := by
  have hAH : ∑ w ∈ Af p t, (((w : ℕ) : ZMod (p^(t+1)))⁻¹)^2
      = ∑ w ∈ Hf p t, (((w : ℕ) : ZMod (p^(t+1)))⁻¹)^2 := by
    have hinj : Set.InjOn (fun w => p^(t+1) - w) ↑(Hf p t) := by
      intro x hx y hy h
      simp only [Finset.mem_coe] at hx hy
      have hx2 := (mem_Hf.mp hx).2.1
      have hy2 := (mem_Hf.mp hy).2.1
      simp only at h
      omega
    rw [Af_eq_reflect hp h5, Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro w hw
    have hwm := mem_Hf.mp hw
    have hle : w ≤ p^(t+1) := by omega
    have hux : IsUnit ((w : ℕ) : ZMod (p^(t+1))) := (isUnit_iff_notdvd hp).mpr hwm.2.2
    have hneg : ((p^(t+1) - w : ℕ) : ZMod (p^(t+1))) = -((w : ℕ) : ZMod (p^(t+1))) := by
      rw [Nat.cast_sub hle, ZMod.natCast_self, zero_sub]
    rw [hneg]
    have key : ((-(((w : ℕ) : ZMod (p^(t+1)))))⁻¹) = -(((w : ℕ) : ZMod (p^(t+1)))⁻¹) := by
      have h1 : (-(((w : ℕ) : ZMod (p^(t+1))))) * (-(((w : ℕ) : ZMod (p^(t+1)))⁻¹)) = 1 := by
        rw [neg_mul_neg]; exact ZMod.mul_inv_of_unit _ hux
      calc (-(((w : ℕ) : ZMod (p^(t+1)))))⁻¹
          = (-(((w : ℕ) : ZMod (p^(t+1)))))⁻¹ * ((-(((w : ℕ) : ZMod (p^(t+1))))) * (-(((w : ℕ) : ZMod (p^(t+1)))⁻¹))) := by rw [h1, mul_one]
        _ = ((-(((w : ℕ) : ZMod (p^(t+1)))))⁻¹ * (-(((w : ℕ) : ZMod (p^(t+1)))))) * (-(((w : ℕ) : ZMod (p^(t+1)))⁻¹)) := by ring
        _ = -(((w : ℕ) : ZMod (p^(t+1)))⁻¹) := by rw [ZMod.inv_mul_of_unit _ hux.neg, one_mul]
    rw [key]; ring
  have hsplit := Ifs_eq_HA (t := t) hp h5
  have hfull := sum_inv_sq_I (t := t) hp h5
  rw [hsplit.1, Finset.sum_union hsplit.2, hAH] at hfull
  have h2 := two_unit (t := t) hp h5
  have htwo : (2 : ZMod (p^(t+1))) * (∑ w ∈ Hf p t, (((w : ℕ) : ZMod (p^(t+1)))⁻¹)^2) = 0 := by
    linear_combination hfull
  exact (IsUnit.mul_right_eq_zero h2).mp htwo

-- ===== General factorial decomposition (no multiple-of-p assumption) =====
lemma factorial_decomp_gen (p N : ℕ) (hp : 0 < p) :
    N.factorial = p ^ (N / p) * (N / p).factorial * Wp p N := by
  have hfact : ∏ j ∈ Finset.Ico 1 (N+1), j = N.factorial := Finset.prod_Ico_id_eq_factorial N
  have hsplit := Finset.prod_filter_mul_prod_filter_not (Finset.Ico 1 (N+1)) (fun j => ¬ p ∣ j) (fun j => j)
  have hdiv : ∏ j ∈ (Finset.Ico 1 (N+1)).filter (fun j => ¬ ¬ p ∣ j), j = p ^ (N/p) * (N/p).factorial := by
    have hset : (Finset.Ico 1 (N+1)).filter (fun j => ¬ ¬ p ∣ j)
        = (Finset.Ico 1 (N/p+1)).image (fun i => p * i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image, not_not]
      constructor
      · rintro ⟨⟨hj1, hj2⟩, hpj⟩
        obtain ⟨i, rfl⟩ := hpj
        have hi0 : 0 < i := by
          rcases Nat.eq_zero_or_pos i with h | h
          · simp [h] at hj1
          · exact h
        have hiN : i ≤ N/p := by
          rw [Nat.le_div_iff_mul_le hp, mul_comm]; omega
        exact ⟨i, ⟨hi0, by omega⟩, by ring⟩
      · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
        have hiN : i ≤ N/p := by omega
        have hle : p * i ≤ N := by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hp).mp hiN
        refine ⟨⟨?_, ?_⟩, Dvd.intro i rfl⟩
        · nlinarith
        · omega
    rw [hset, Finset.prod_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hp h)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_Ico_id_eq_factorial]
    congr 1
    simp [Nat.card_Ico]
  rw [← hfact, ← hsplit, hdiv]
  unfold Wp
  ring

-- ===== Odd real identity and integer identity =====
open scoped Real

lemma halfGamma (m : ℕ) :
    Real.Gamma ((m:ℝ) + 3/2)
      = ((2*m+1).factorial : ℝ) * (2:ℝ)^(-(2*(m:ℝ)+1)) * Real.sqrt π / (m.factorial : ℝ) := by
  have hkey := Real.Gamma_mul_Gamma_add_half ((m:ℝ) + 1)
  have e1 : (m:ℝ) + 1 + 1/2 = (m:ℝ) + 3/2 := by ring
  have e3 : 2 * ((m:ℝ) + 1) = (((2*m+1 : ℕ)) : ℝ) + 1 := by push_cast; ring
  rw [e1, e3, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial] at hkey
  have hfac : ((m.factorial : ℝ)) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have e4 : (1:ℝ) - (((2*m+1 : ℕ):ℝ)+1) = -(2*(m:ℝ)+1) := by push_cast; ring
  rw [e4] at hkey
  rw [eq_div_iff hfac, mul_comm]
  exact hkey

lemma halfGamma' (m : ℕ) :
    Real.Gamma ((m:ℝ) + 3/2)
      = ((2*m+1).factorial : ℝ) * Real.sqrt π / ((2^(2*m+1):ℝ) * (m.factorial : ℝ)) := by
  rw [halfGamma]
  have h2 : (2:ℝ)^(-(2*(m:ℝ)+1)) = ((2^(2*m+1):ℝ))⁻¹ := by
    rw [show -(2*(m:ℝ)+1) = -(((2*m+1:ℕ)):ℝ) by push_cast; ring,
        Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [h2]
  field_simp

lemma sqrtpi_ne : Real.sqrt π ≠ 0 := by
  have : (0:ℝ) < π := Real.pi_pos
  positivity

lemma a_odd (j : ℕ) :
    a (2*j+1) = (2:ℝ)^(12*j+6) * ((4*j+2).factorial : ℝ) * ((9*j+4).factorial : ℝ) /
      (((3*j+1).factorial : ℝ) * ((8*j+4).factorial : ℝ) * ((2*j+1).factorial : ℝ)) := by
  unfold a
  simp only
  set nr : ℝ := ((2*j+1 : ℕ) : ℝ) with hnr
  have g1 : (9:ℝ) * nr + 1 = ((18*j+9 : ℕ):ℝ) + 1 := by rw [hnr]; push_cast; ring
  have g2 : (2:ℝ) * nr + 1 = ((4*j+2 : ℕ):ℝ) + 1 := by rw [hnr]; push_cast; ring
  have g3 : (3/2:ℝ) * nr + 1 = ((3*j+1 : ℕ):ℝ) + 3/2 := by rw [hnr]; push_cast; ring
  have g4 : (9/2:ℝ) * nr + 1 = ((9*j+4 : ℕ):ℝ) + 3/2 := by rw [hnr]; push_cast; ring
  have g5 : (4:ℝ) * nr + 1 = ((8*j+4 : ℕ):ℝ) + 1 := by rw [hnr]; push_cast; ring
  have g6 : (3:ℝ) * nr + 1 = ((6*j+3 : ℕ):ℝ) + 1 := by rw [hnr]; push_cast; ring
  have g7 : nr + 1 = ((2*j+1 : ℕ):ℝ) + 1 := by rw [hnr]
  rw [g1, g2, g3, g4, g5, g6, g7, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
    Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
    halfGamma', halfGamma']
  rw [show 2*(3*j+1)+1 = 6*j+3 from by ring, show 2*(9*j+4)+1 = 18*j+9 from by ring]
  have hpow : (2:ℝ)^(18*j+9) = (2:ℝ)^(12*j+6) * (2:ℝ)^(6*j+3) := by
    rw [← pow_add]; ring_nf
  have hf1 : ((18*j+9).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hf2 : ((6*j+3).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hf3 : ((3*j+1).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hf4 : ((9*j+4).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hf5 : ((8*j+4).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hf6 : ((2*j+1).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hsp := sqrtpi_ne
  rw [hpow]
  field_simp

section Zsec2
variable (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ))))

lemma odd_int_id (j : ℕ) :
    z h_int (2*j+1) * (((3*j+1).factorial * (8*j+4).factorial * (2*j+1).factorial : ℕ) : ℤ)
      = (2:ℤ)^(12*j+6) * (((4*j+2).factorial * (9*j+4).factorial : ℕ) : ℤ) := by
  have hr := z_spec h_int (2*j+1)
  rw [a_odd] at hr
  have hne : (((3*j+1).factorial : ℝ) * ((8*j+4).factorial : ℝ) * ((2*j+1).factorial : ℝ)) ≠ 0 := by
    have h1 : (0:ℝ) < ((3*j+1).factorial : ℝ) := by exact_mod_cast (Nat.factorial_pos _)
    have h2 : (0:ℝ) < ((8*j+4).factorial : ℝ) := by exact_mod_cast (Nat.factorial_pos _)
    have h3 : (0:ℝ) < ((2*j+1).factorial : ℝ) := by exact_mod_cast (Nat.factorial_pos _)
    positivity
  have key : (z h_int (2*j+1) : ℝ) * (((3*j+1).factorial : ℝ) * ((8*j+4).factorial : ℝ) * ((2*j+1).factorial : ℝ))
      = (2:ℝ)^(12*j+6) * ((4*j+2).factorial : ℝ) * ((9*j+4).factorial : ℝ) := by
    rw [hr]; field_simp
  have key2 : (z h_int (2*j+1) : ℝ) * (((3*j+1).factorial * (8*j+4).factorial * (2*j+1).factorial : ℕ) : ℝ)
      = ((2:ℤ)^(12*j+6) : ℝ) * (((4*j+2).factorial * (9*j+4).factorial : ℕ) : ℝ) := by
    push_cast
    push_cast at key
    linarith [key]
  exact_mod_cast key2
end Zsec2

-- ===== Symmetric shifted block set S2 = [(q+1)/2, (3q-1)/2] p-free =====
def S2 (p t : ℕ) : Finset ℕ :=
  (Finset.Ico (p^(t+1)/2 + 1) (3*p^(t+1)/2 + 1)).filter (fun u => ¬ p ∣ u)

lemma mem_S2 {p t u : ℕ} :
    u ∈ S2 p t ↔ p^(t+1)/2 + 1 ≤ u ∧ u ≤ 3*p^(t+1)/2 ∧ ¬ p ∣ u := by
  unfold S2; rw [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨h1,h2⟩,h3⟩; exact ⟨h1, by omega, h3⟩
  · rintro ⟨h1,h2,h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩

lemma S2_decomp {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    S2 p t = Af p t ∪ (Hf p t).image (fun w => p^(t+1) + w) ∧
    Disjoint (Af p t) ((Hf p t).image (fun w => p^(t+1) + w)) := by
  have hq5 : 5 ≤ p^(t+1) := q_ge_five hp h5
  have hodd : p^(t+1) % 2 = 1 := by have h2 := q_odd (t := t) hp h5; omega
  have hqd : p ∣ p^(t+1) := dvd_pow_self p (Nat.succ_ne_zero t)
  constructor
  · ext x
    simp only [Finset.mem_union, Finset.mem_image, mem_S2, mem_Hf, Af, Finset.mem_filter,
      Finset.mem_Ico]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases Nat.lt_or_ge x (p^(t+1)) with hlt | hge
      · left; exact ⟨⟨h1, hlt⟩, h3⟩
      · right
        have hxne : x ≠ p^(t+1) := by rintro rfl; exact h3 hqd
        refine ⟨x - p^(t+1), ⟨by omega, by omega, ?_⟩, by omega⟩
        intro hd
        apply h3
        have hh := hd.add hqd
        have heq : (x - p^(t+1)) + p^(t+1) = x := by omega
        rwa [heq] at hh
    · rintro (⟨⟨ha1, ha2⟩, ha3⟩ | ⟨w, ⟨hw1, hw2, hw3⟩, rfl⟩)
      · exact ⟨ha1, by omega, ha3⟩
      · refine ⟨by omega, by omega, ?_⟩
        intro hd
        apply hw3
        have hh := Nat.dvd_sub hd hqd
        have heq : p^(t+1) + w - p^(t+1) = w := by omega
        rwa [heq] at hh
  · rw [Finset.disjoint_left]
    intro x hx hx2
    simp only [Af, Finset.mem_filter, Finset.mem_Ico] at hx
    simp only [Finset.mem_image, mem_Hf] at hx2
    obtain ⟨w, ⟨hw1, hw2, hw3⟩, rfl⟩ := hx2
    omega

lemma S2_le {p t : ℕ} : ∀ u ∈ S2 p t, u ≤ 2 * p^(t+1) := by
  intro u hu; rw [mem_S2] at hu; omega

lemma S2_unit {p t : ℕ} (hp : Nat.Prime p) :
    ∀ u ∈ S2 p t, IsUnit ((u : ℕ) : ZMod (p^(t+1))) := by
  intro u hu; rw [mem_S2] at hu; rw [isUnit_iff_notdvd hp]; exact hu.2.2

lemma S2_reflect {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    ∀ u ∈ S2 p t, 2 * p^(t+1) - u ∈ S2 p t := by
  have hodd : p^(t+1) % 2 = 1 := by have h2 := q_odd (t := t) hp h5; omega
  have hqd : p ∣ p^(t+1) := dvd_pow_self p (Nat.succ_ne_zero t)
  intro u hu; rw [mem_S2] at hu ⊢
  obtain ⟨h1, h2, h3⟩ := hu
  refine ⟨by omega, by omega, ?_⟩
  intro hd
  apply h3
  have h2q : p ∣ 2 * p^(t+1) := hqd.mul_left 2
  have hh := Nat.dvd_sub h2q hd
  rwa [Nat.sub_sub_self (by omega)] at hh

lemma sum_inv_sq_S2 {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    ∑ u ∈ S2 p t, (((u : ℕ) : ZMod (p^(t+1)))⁻¹)^2 = 0 := by
  obtain ⟨hdec, hdisj⟩ := S2_decomp hp h5
  rw [hdec, Finset.sum_union hdisj]
  have hinj : Set.InjOn (fun w => p^(t+1) + w) ↑(Hf p t) := by
    intro x _ y _ h; simp only at h; omega
  rw [Finset.sum_image hinj]
  have hHf : ∑ w ∈ Hf p t, (((p^(t+1) + w : ℕ) : ZMod (p^(t+1)))⁻¹)^2
      = ∑ w ∈ Hf p t, (((w : ℕ) : ZMod (p^(t+1)))⁻¹)^2 := by
    apply Finset.sum_congr rfl
    intro w _
    congr 2
    rw [Nat.cast_add, ZMod.natCast_self, zero_add]
  rw [hHf]
  have hsplit := Ifs_eq_HA (t := t) hp h5
  have hfull := sum_inv_sq_I (t := t) hp h5
  rw [hsplit.1, Finset.sum_union hsplit.2] at hfull
  linear_combination hfull

-- ===== Wilson for S2 (reflection at 2q) and shifted block product =====
lemma wilson_S2 {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) (N : ℕ) :
    ∏ u ∈ S2 p t, ((N * p^(t+1) + u : ℕ) : ZMod ((p^(t+1))^3))
      = ∏ u ∈ S2 p t, ((u : ℕ) : ZMod ((p^(t+1))^3)) :=
  lifted_wilson_R (q_ge_five hp h5) 2 (S2 p t) S2_le (S2_reflect hp h5) (S2_unit hp)
    (two_unit hp h5) (sum_inv_sq_S2 hp h5) N

lemma S2_block_eq {p t s : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    (Finset.Ico (p^(t+1)/2 + s*p^(t+1) + 1) (p^(t+1)/2 + (s+1)*p^(t+1) + 1)).filter (fun j => ¬ p ∣ j)
      = (S2 p t).image (fun u => s * p^(t+1) + u) := by
  have hodd : p^(t+1) % 2 = 1 := by have h2 := q_odd (t := t) hp h5; omega
  have hqd : p ∣ p^(t+1) := dvd_pow_self p (Nat.succ_ne_zero t)
  have hsq : p ∣ s * p^(t+1) := hqd.mul_left s
  have hexp : (s+1) * p^(t+1) = s * p^(t+1) + p^(t+1) := by ring
  ext j
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image, mem_S2]
  constructor
  · rintro ⟨⟨hj1, hj2⟩, hpj⟩
    refine ⟨j - s * p^(t+1), ⟨by omega, by omega, ?_⟩, by omega⟩
    intro hd
    apply hpj
    have hh := hd.add hsq
    have heq : (j - s * p^(t+1)) + s * p^(t+1) = j := by omega
    rwa [heq] at hh
  · rintro ⟨u, ⟨hu1, hu2, hu3⟩, rfl⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro hd
    apply hu3
    have hh := Nat.dvd_sub hd hsq
    have heq : s * p^(t+1) + u - s * p^(t+1) = u := by omega
    rwa [heq] at hh

lemma Wp_shift {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) (n : ℕ) :
    ((Wp p (p^(t+1)/2 + n * p^(t+1)) : ℕ) : ZMod ((p^(t+1))^3))
      = (∏ u ∈ Hf p t, ((u : ℕ) : ZMod ((p^(t+1))^3)))
        * (∏ u ∈ S2 p t, ((u : ℕ) : ZMod ((p^(t+1))^3)))^n := by
  induction n with
  | zero =>
    simp only [Nat.zero_mul, Nat.add_zero, pow_zero, mul_one]
    have : Wp p (p^(t+1)/2) = ∏ j ∈ Hf p t, j := rfl
    rw [this, Nat.cast_prod]
  | succ n ih =>
    have hqpos : 0 < p^(t+1) := pow_pos hp.pos (t+1)
    have hsplit : (Finset.Ico 1 (p^(t+1)/2 + (n+1) * p^(t+1) + 1)).filter (fun j => ¬ p ∣ j)
        = ((Finset.Ico 1 (p^(t+1)/2 + n * p^(t+1) + 1)).filter (fun j => ¬ p ∣ j))
          ∪ ((Finset.Ico (p^(t+1)/2 + n * p^(t+1) + 1) (p^(t+1)/2 + (n+1) * p^(t+1) + 1)).filter (fun j => ¬ p ∣ j)) := by
      rw [← Finset.filter_union, Finset.Ico_union_Ico_eq_Ico (by omega) (by nlinarith [hqpos])]
    have hdisj : Disjoint ((Finset.Ico 1 (p^(t+1)/2 + n * p^(t+1) + 1)).filter (fun j => ¬ p ∣ j))
        ((Finset.Ico (p^(t+1)/2 + n * p^(t+1) + 1) (p^(t+1)/2 + (n+1) * p^(t+1) + 1)).filter (fun j => ¬ p ∣ j)) := by
      apply Finset.disjoint_filter_filter
      rw [Finset.disjoint_left]; intro x hx hx2
      rw [Finset.mem_Ico] at hx hx2; omega
    have hWsucc : Wp p (p^(t+1)/2 + (n+1) * p^(t+1))
        = Wp p (p^(t+1)/2 + n * p^(t+1))
          * ∏ j ∈ (Finset.Ico (p^(t+1)/2 + n * p^(t+1) + 1) (p^(t+1)/2 + (n+1) * p^(t+1) + 1)).filter (fun j => ¬ p ∣ j), j := by
      unfold Wp; rw [hsplit, Finset.prod_union hdisj]
    rw [hWsucc, Nat.cast_mul, ih, S2_block_eq hp h5,
      Finset.prod_image (fun a _ b _ h => Nat.add_left_cancel h), Nat.cast_prod,
      wilson_S2 hp h5 n]
    rw [pow_succ]
    ring

-- ===== Morley helper lemmas =====
-- generalized nilpotent product expansion: pairwise products of h vanish
lemma prod_add_sq_nilpotent {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g h : ι → R) (hh : ∀ w ∈ s, ∀ w' ∈ s, h w * h w' = 0) :
    ∏ u ∈ s, (g u + h u) = (∏ u ∈ s, g u) + ∑ u ∈ s, h u * ∏ v ∈ s.erase u, g v := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert b s hb ih =>
    have hsub : ∀ w ∈ s, ∀ w' ∈ s, h w * h w' = 0 := by
      intro w hw w' hw'
      exact hh w (Finset.mem_insert_of_mem hw) w' (Finset.mem_insert_of_mem hw')
    rw [Finset.prod_insert hb, ih hsub, Finset.sum_insert hb, Finset.prod_insert hb]
    have key : ∏ v ∈ (insert b s).erase b, g v = ∏ v ∈ s, g v := by
      rw [Finset.erase_insert hb]
    rw [key]
    have key2 : ∀ u ∈ s, ∏ v ∈ (insert b s).erase u, g v = g b * ∏ v ∈ s.erase u, g v := by
      intro u hu
      have hub : u ≠ b := fun h => hb (h ▸ hu)
      have hset : (insert b s).erase u = insert b (s.erase u) := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2 | h3⟩
          · exact Or.inl h2
          · exact Or.inr ⟨h1, h3⟩
        · rintro (h | ⟨h1, h2⟩)
          · subst h; exact ⟨Ne.symm hub, Or.inl rfl⟩
          · exact ⟨h1, Or.inr h2⟩
      rw [hset, Finset.prod_insert (fun h => hb (Finset.mem_of_mem_erase h))]
    have key3 : ∀ u ∈ s, h u * ∏ v ∈ (insert b s).erase u, g v
        = g b * (h u * ∏ v ∈ s.erase u, g v) := by
      intro u hu; rw [key2 u hu]; ring
    rw [Finset.sum_congr rfl key3, ← Finset.mul_sum]
    have hcross : h b * ∑ u ∈ s, h u * ∏ v ∈ s.erase u, g v = 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro u hu
      have hbu : h b * h u = 0 := hh b (Finset.mem_insert_self b s) u (Finset.mem_insert_of_mem hu)
      calc h b * (h u * ∏ v ∈ s.erase u, g v) = (h b * h u) * ∏ v ∈ s.erase u, g v := by ring
        _ = 0 := by rw [hbu, zero_mul]
    linear_combination hcross

lemma prod_oneAdd_Q {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (Q : R) (f : ι → R) :
    ∃ c : R, ∏ u ∈ s, (1 + Q * f u) = 1 + Q * c := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, by simp⟩
  | insert b s hb ih =>
    obtain ⟨c, hc⟩ := ih
    rw [Finset.prod_insert hb, hc]
    exact ⟨f b + c + Q * f b * c, by ring⟩

lemma Qsq_prod_oneAdd {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (Q : R) (f : ι → R) (hQ3 : Q^3 = 0) :
    Q^2 * ∏ u ∈ s, (1 + Q * f u) = Q^2 := by
  obtain ⟨c, hc⟩ := prod_oneAdd_Q s Q f
  rw [hc]
  have h : Q^2 * (1 + Q*c) = Q^2 + Q^3 * c := by ring
  rw [h, hQ3, zero_mul, add_zero]

lemma castHom_zmod_inv {a b : ℕ} [NeZero b] (h : b ∣ a) (x : ZMod a) (hx : IsUnit x) :
    (ZMod.castHom h (ZMod b)) (x⁻¹) = ((ZMod.castHom h (ZMod b)) x)⁻¹ := by
  have hu : IsUnit ((ZMod.castHom h (ZMod b)) x) := hx.map _
  have h1 : (ZMod.castHom h (ZMod b)) x * (ZMod.castHom h (ZMod b)) (x⁻¹) = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit x hx, map_one]
  symm
  calc ((ZMod.castHom h (ZMod b)) x)⁻¹
      = ((ZMod.castHom h (ZMod b)) x)⁻¹ * ((ZMod.castHom h (ZMod b)) x * (ZMod.castHom h (ZMod b)) (x⁻¹)) := by rw [h1, mul_one]
    _ = (((ZMod.castHom h (ZMod b)) x)⁻¹ * (ZMod.castHom h (ZMod b)) x) * (ZMod.castHom h (ZMod b)) (x⁻¹) := by ring
    _ = (ZMod.castHom h (ZMod b)) (x⁻¹) := by rw [ZMod.inv_mul_of_unit _ hu, one_mul]

lemma Qsq_mul_eq_zero {n : ℕ} [NeZero n] (x : ZMod (n^3))
    (hx : (ZMod.castHom (dvd_pow_self n (by norm_num : (3:ℕ) ≠ 0)) (ZMod n)) x = 0) :
    (n : ZMod (n^3))^2 * x = 0 := by
  haveI : NeZero (n^3) := ⟨pow_ne_zero _ (NeZero.ne n)⟩
  have hval : ((x.val : ℕ) : ZMod n) = 0 := by
    have h2 : (ZMod.castHom (dvd_pow_self n (by norm_num : (3:ℕ) ≠ 0)) (ZMod n)) ((x.val : ℕ) : ZMod (n^3))
        = ((x.val : ℕ) : ZMod n) := map_natCast _ _
    rw [ZMod.natCast_zmod_val x] at h2
    rw [← h2]; exact hx
  rw [ZMod.natCast_eq_zero_iff] at hval
  obtain ⟨k, hk⟩ := hval
  have hxeq : x = (n : ZMod (n^3)) * (k : ZMod (n^3)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x]
    rw [hk]; push_cast; ring
  rw [hxeq]
  have h3 : (n : ZMod (n^3))^2 * ((n:ZMod (n^3)) * (k:ZMod (n^3)))
      = ((n^3 : ℕ) : ZMod (n^3)) * (k : ZMod (n^3)) := by push_cast; ring
  rw [h3, ZMod.natCast_self, zero_mul]

-- ===== Doubling partition of Ifs into even (2*Hf) and odd (2*Af - q) =====
lemma Ifs_eq_EO {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    Ifs p t = (Hf p t).image (fun w => 2*w) ∪ (Af p t).image (fun u => 2*u - p^(t+1)) ∧
    Disjoint ((Hf p t).image (fun w => 2*w)) ((Af p t).image (fun u => 2*u - p^(t+1))) := by
  have hq5 : 5 ≤ p^(t+1) := q_ge_five hp h5
  have hodd : p^(t+1) % 2 = 1 := by have h2 := q_odd (t:=t) hp h5; omega
  have hqd : p ∣ p^(t+1) := dvd_pow_self p (Nat.succ_ne_zero t)
  refine ⟨?_, ?_⟩
  · ext v
    simp only [Finset.mem_union, Finset.mem_image, mem_Ifs, mem_Hf, Af, Finset.mem_filter,
      Finset.mem_Ico]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases Nat.even_or_odd v with ⟨w, hw⟩ | ⟨u, hu⟩
      · left
        refine ⟨w, ⟨by omega, by omega, ?_⟩, by omega⟩
        intro hd; apply h3; rw [hw]; exact hd.add hd
      · right
        refine ⟨(v + p^(t+1))/2, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
        intro hd; apply h3
        have h2u : p ∣ 2 * ((v + p^(t+1))/2) := hd.mul_left 2
        have heq : 2 * ((v + p^(t+1))/2) = v + p^(t+1) := by omega
        rw [heq] at h2u
        have := Nat.dvd_sub h2u hqd
        rwa [Nat.add_sub_cancel] at this
    · rintro (⟨w, ⟨hw1, hw2, hw3⟩, rfl⟩ | ⟨u, ⟨⟨hu1, hu2⟩, hu3⟩, rfl⟩)
      · refine ⟨by omega, by omega, ?_⟩
        intro hd
        apply hw3
        rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
        · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
        · exact h
      · refine ⟨by omega, by omega, ?_⟩
        intro hd
        apply hu3
        have h2u : p ∣ (2*u - p^(t+1)) + p^(t+1) := hd.add hqd
        have heq : (2*u - p^(t+1)) + p^(t+1) = 2*u := by omega
        rw [heq] at h2u
        rcases (Nat.Prime.dvd_mul hp).mp h2u with h | h
        · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
        · exact h
  · rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_image, mem_Hf, Af, Finset.mem_filter, Finset.mem_Ico] at hx hy
    obtain ⟨w, ⟨hw1, hw2, hw3⟩, rfl⟩ := hx
    obtain ⟨u, ⟨⟨hu1, hu2⟩, hu3⟩, hxe⟩ := hy
    omega

-- ===== factoring helpers =====
lemma add_eq_mul_oneAdd {n : ℕ} (a c : ZMod n) (ha : IsUnit a) :
    a + c = a * (1 + c * a⁻¹) := by
  have h := ZMod.mul_inv_of_unit a ha
  calc a + c = a + c * (a * a⁻¹) := by rw [h, mul_one]
    _ = a * (1 + c * a⁻¹) := by ring

lemma prod_add_factor {n : ℕ} (S : Finset ℕ) (base c : ℕ → ZMod n)
    (hu : ∀ u ∈ S, IsUnit (base u)) :
    ∏ u ∈ S, (base u + c u) = (∏ u ∈ S, base u) * ∏ u ∈ S, (1 + c u * (base u)⁻¹) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro u hu'
  exact add_eq_mul_oneAdd (base u) (c u) (hu u hu')

lemma M1_Ifs {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    ∏ u ∈ Ifs p t, (1 + ((p^(t+1):ℕ) : ZMod ((p^(t+1))^3)) * (((u:ℕ) : ZMod ((p^(t+1))^3))⁻¹)) = 1 := by
  set R := ZMod ((p^(t+1))^3)
  set Q : R := ((p^(t+1):ℕ) : R) with hQ
  have hw := wilson_Ifs (t := t) hp h5 1
  have hterm : ∀ u ∈ Ifs p t, ((1 * p^(t+1) + u : ℕ) : R) = ((u:ℕ):R) + Q := by
    intro u hu; rw [hQ]; push_cast; ring
  rw [Finset.prod_congr rfl hterm] at hw
  rw [prod_add_factor (Ifs p t) (fun u => ((u:ℕ):R)) (fun _ => Q) (Ifs_unit3 hp)] at hw
  -- hw : B0 * ∏(1+Q*u⁻¹) = B0
  have hB0 : IsUnit (∏ u ∈ Ifs p t, ((u:ℕ):R)) := B0_unit (t := t) hp
  have hw2 : (∏ u ∈ Ifs p t, ((u:ℕ):R)) * ∏ u ∈ Ifs p t, (1 + Q * (((u:ℕ):R)⁻¹))
      = (∏ u ∈ Ifs p t, ((u:ℕ):R)) * 1 := by rw [mul_one]; exact hw
  exact (IsUnit.mul_right_inj hB0).mp hw2

-- ===== unit helpers in ZMod (q^3) =====
lemma cast_unit3 {p t k : ℕ} (hp : Nat.Prime p) (hk : ¬ p ∣ k) :
    IsUnit ((k:ℕ) : ZMod ((p^(t+1))^3)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.pow_right 3 (coprime_of_prime_pow hp hk)

lemma two_unit3 {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    IsUnit (2 : ZMod ((p^(t+1))^3)) := by
  have h : (2 : ZMod ((p^(t+1))^3)) = ((2:ℕ) : ZMod ((p^(t+1))^3)) := by push_cast; ring
  rw [h]; exact cast_unit3 hp (by intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega)

lemma mem_Af {p t u : ℕ} : u ∈ Af p t ↔ p^(t+1)/2 + 1 ≤ u ∧ u < p^(t+1) ∧ ¬ p ∣ u := by
  unfold Af; rw [Finset.mem_filter, Finset.mem_Ico]; tauto

-- ===== Doubling: 2^φ = Π_O =====
lemma doubling {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    (2 : ZMod ((p^(t+1))^3))^((Ifs p t).card)
      = ∏ u ∈ Af p t, (1 + ((p^(t+1):ℕ):ZMod ((p^(t+1))^3))
          * (((2*u - p^(t+1):ℕ) : ZMod ((p^(t+1))^3))⁻¹)) := by
  set R := ZMod ((p^(t+1))^3)
  set Q : R := ((p^(t+1):ℕ):R) with hQ
  set B0 : R := ∏ u ∈ Ifs p t, ((u:ℕ):R) with hB0
  set PiO : R := ∏ u ∈ Af p t, (1 + Q * (((2*u - p^(t+1):ℕ):R)⁻¹)) with hPiO
  have hAfunit : ∀ u ∈ Af p t, IsUnit (((2*u - p^(t+1):ℕ):R)) := by
    intro u hu; rw [mem_Af] at hu
    apply cast_unit3 hp
    intro hd
    have h2u : p ∣ (2*u - p^(t+1)) + p^(t+1) := hd.add (dvd_pow_self p (Nat.succ_ne_zero t))
    have heq : (2*u - p^(t+1)) + p^(t+1) = 2*u := by omega
    rw [heq] at h2u
    rcases (Nat.Prime.dvd_mul hp).mp h2u with h | h
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
    · exact hu.2.2 h
  -- (A)
  have hA : ∏ u ∈ Ifs p t, ((2*u:ℕ):R) = (2:R)^((Ifs p t).card) * B0 := by
    have e : ∏ u ∈ Ifs p t, ((2*u:ℕ):R) = ∏ u ∈ Ifs p t, ((2:R)*((u:ℕ):R)) := by
      apply Finset.prod_congr rfl; intro u hu; push_cast; ring
    rw [e, Finset.prod_mul_distrib, Finset.prod_const, hB0]
  -- B0 decomposition via EO
  have hB0eo : (∏ w ∈ Hf p t, ((2*w:ℕ):R)) * (∏ u ∈ Af p t, ((2*u - p^(t+1):ℕ):R)) = B0 := by
    rw [hB0]
    obtain ⟨hEO, hdisjEO⟩ := Ifs_eq_EO hp h5
    have hinj1 : Set.InjOn (fun w => 2*w) ↑(Hf p t) := by
      intro a _ b _ h; simp only at h; omega
    have hinj2 : Set.InjOn (fun u => 2*u - p^(t+1)) ↑(Af p t) := by
      intro a ha b hb h
      simp only [Finset.mem_coe, mem_Af] at ha hb
      simp only at h; omega
    rw [hEO, Finset.prod_union hdisjEO, Finset.prod_image hinj1, Finset.prod_image hinj2]
  -- (B)
  have hB : ∏ u ∈ Ifs p t, ((2*u:ℕ):R) = B0 * PiO := by
    have hsplit := Ifs_eq_HA (t := t) hp h5
    rw [hsplit.1, Finset.prod_union hsplit.2]
    have hAf : ∏ u ∈ Af p t, ((2*u:ℕ):R) = (∏ u ∈ Af p t, ((2*u - p^(t+1):ℕ):R)) * PiO := by
      have e1 : ∏ u ∈ Af p t, ((2*u:ℕ):R) = ∏ u ∈ Af p t, (((2*u - p^(t+1):ℕ):R) + Q) := by
        apply Finset.prod_congr rfl; intro u hu
        rw [mem_Af] at hu
        have h2u : p^(t+1) ≤ 2*u := by omega
        rw [hQ, ← Nat.cast_add, Nat.sub_add_cancel h2u]
      rw [e1, prod_add_factor (Af p t) (fun u => ((2*u - p^(t+1):ℕ):R)) (fun _ => Q) hAfunit, hPiO]
    rw [hAf, ← mul_assoc, hB0eo]
  -- combine
  have hkey : (2:R)^((Ifs p t).card) * B0 = B0 * PiO := by rw [← hA, hB]
  have hB0u : IsUnit B0 := hB0 ▸ B0_unit (t := t) hp
  have hcancel : (2:R)^((Ifs p t).card) = PiO := by
    have h2 : B0 * (2:R)^((Ifs p t).card) = B0 * PiO := by rw [mul_comm B0, hkey]
    exact (IsUnit.mul_right_inj hB0u).mp h2
  rw [hcancel]

lemma zmod_mul_inv {n : ℕ} (a b : ZMod n) (ha : IsUnit a) (hb : IsUnit b) :
    (a*b)⁻¹ = a⁻¹ * b⁻¹ := by
  have hab : IsUnit (a*b) := ha.mul hb
  have h1 : (a*b) * (a⁻¹*b⁻¹) = 1 := by
    rw [show (a*b)*(a⁻¹*b⁻¹) = (a*a⁻¹)*(b*b⁻¹) from by ring,
       ZMod.mul_inv_of_unit a ha, ZMod.mul_inv_of_unit b hb, mul_one]
  calc (a*b)⁻¹ = (a*b)⁻¹ * ((a*b)*(a⁻¹*b⁻¹)) := by rw [h1, mul_one]
    _ = ((a*b)⁻¹*(a*b))*(a⁻¹*b⁻¹) := by ring
    _ = a⁻¹*b⁻¹ := by rw [ZMod.inv_mul_of_unit _ hab, one_mul]

-- Q^2 * ∑_{Hf} (w:R)⁻¹^2 = 0
lemma Q2_sum_inv_sq_Hf {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    ((p^(t+1):ℕ) : ZMod ((p^(t+1))^3))^2 * (∑ w ∈ Hf p t, (((w:ℕ) : ZMod ((p^(t+1))^3))⁻¹)^2) = 0 := by
  haveI : NeZero (p^(t+1)) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  apply Qsq_mul_eq_zero
  rw [map_sum]
  rw [show (0 : ZMod (p^(t+1))) = ∑ w ∈ Hf p t, (((w:ℕ) : ZMod (p^(t+1)))⁻¹)^2 from (sum_inv_sq_Hf hp h5).symm]
  apply Finset.sum_congr rfl
  intro w hw
  rw [map_pow, castHom_zmod_inv _ _ (cast_unit3 hp (mem_Hf.mp hw).2.2)]
  congr 2
  exact map_natCast _ _

lemma rho_eq_tau_sq {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    (∏ w ∈ Hf p t, (1 + ((p^(t+1):ℕ):ZMod ((p^(t+1))^3)) * (((w:ℕ):ZMod ((p^(t+1))^3))⁻¹)))
      = (∏ w ∈ Hf p t, (1 + ((p^(t+1):ℕ):ZMod ((p^(t+1))^3))
          * (((2*w:ℕ):ZMod ((p^(t+1))^3))⁻¹)))^2 := by
  set R := ZMod ((p^(t+1))^3)
  set Q : R := ((p^(t+1):ℕ):R) with hQ
  set ι : R := (2:R)⁻¹ with hι
  have hQ3 : Q^3 = 0 := by rw [hQ, ← Nat.cast_pow]; exact ZMod.natCast_self _
  have h2ι : (2:R) * ι = 1 := ZMod.mul_inv_of_unit _ (two_unit3 hp h5)
  -- rewrite τ² as ∏ (g + h)
  set g : ℕ → R := fun w => 1 + Q * (((w:ℕ):R)⁻¹) with hg
  set h : ℕ → R := fun w => Q^2 * ι^2 * (((w:ℕ):R)⁻¹)^2 with hh
  have htfac : ∀ w ∈ Hf p t,
      (1 + Q * (((2*w:ℕ):R)⁻¹))^2 = g w + h w := by
    intro w hw
    have hAB : ((2*w:ℕ):R)⁻¹ = ι * (((w:ℕ):R)⁻¹) := by
      have hc : ((2*w:ℕ):R) = (2:R) * ((w:ℕ):R) := by push_cast; ring
      rw [hc, zmod_mul_inv (2:R) ((w:ℕ):R) (two_unit3 hp h5) (cast_unit3 hp (mem_Hf.mp hw).2.2), hι]
    rw [hAB, hg, hh]; simp only
    linear_combination (Q * (((w:ℕ):R)⁻¹)) * h2ι
  have hpow : (∏ w ∈ Hf p t, (1 + Q * (((2*w:ℕ):R)⁻¹)))^2
      = ∏ w ∈ Hf p t, (g w + h w) := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl htfac
  rw [hpow]
  -- prod_add_sq_nilpotent
  have hhh : ∀ w ∈ Hf p t, ∀ w' ∈ Hf p t, h w * h w' = 0 := by
    intro w _ w' _
    rw [hh]; simp only
    rw [show Q^2*ι^2*(((w:ℕ):R)⁻¹)^2 * (Q^2*ι^2*(((w':ℕ):R)⁻¹)^2)
        = Q^3 * Q * (ι^2*(((w:ℕ):R)⁻¹)^2*(ι^2*(((w':ℕ):R)⁻¹)^2)) from by ring, hQ3, zero_mul, zero_mul]
  rw [prod_add_sq_nilpotent (Hf p t) g h hhh]
  -- show ∑ h w ∏ erase g = 0
  have hzero : ∑ w ∈ Hf p t, h w * ∏ v ∈ (Hf p t).erase w, g v = 0 := by
    have hterm : ∀ w ∈ Hf p t, h w * ∏ v ∈ (Hf p t).erase w, g v
        = (ι^2 * Q^2) * (((w:ℕ):R)⁻¹)^2 := by
      intro w hw
      have hgform : (∏ v ∈ (Hf p t).erase w, g v)
          = ∏ v ∈ (Hf p t).erase w, (1 + Q * (((v:ℕ):R)⁻¹)) := by
        apply Finset.prod_congr rfl; intro v hv; rw [hg]
      rw [hh]; simp only; rw [hgform]
      rw [show Q^2*ι^2*(((w:ℕ):R)⁻¹)^2 * ∏ v ∈ (Hf p t).erase w, (1 + Q * (((v:ℕ):R)⁻¹))
          = ι^2*(((w:ℕ):R)⁻¹)^2 * (Q^2 * ∏ v ∈ (Hf p t).erase w, (1 + Q * (((v:ℕ):R)⁻¹))) from by ring]
      rw [Qsq_prod_oneAdd ((Hf p t).erase w) Q (fun v => ((v:ℕ):R)⁻¹) hQ3]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hz := Q2_sum_inv_sq_Hf (t := t) hp h5
    rw [← hQ] at hz
    rw [show (ι^2 * Q^2) * (∑ w ∈ Hf p t, (((w:ℕ):R)⁻¹)^2)
        = ι^2 * (Q^2 * ∑ w ∈ Hf p t, (((w:ℕ):R)⁻¹)^2) from by ring, hz, mul_zero]
  rw [hzero, add_zero]

lemma Gcal_eq {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    (∏ u ∈ S2 p t, ((u:ℕ):ZMod ((p^(t+1))^3)))
      = (∏ u ∈ Ifs p t, ((u:ℕ):ZMod ((p^(t+1))^3)))
        * ∏ w ∈ Hf p t, (1 + ((p^(t+1):ℕ):ZMod ((p^(t+1))^3))
            * (((w:ℕ):ZMod ((p^(t+1))^3))⁻¹)) := by
  set R := ZMod ((p^(t+1))^3)
  set Q : R := ((p^(t+1):ℕ):R) with hQ
  obtain ⟨hdec, hdisj⟩ := S2_decomp hp h5
  rw [hdec, Finset.prod_union hdisj]
  have hinj : Set.InjOn (fun w => p^(t+1)+w) ↑(Hf p t) := by intro a _ b _ h; simp only at h; omega
  rw [Finset.prod_image hinj]
  have hterm : ∀ w ∈ Hf p t, ((p^(t+1)+w:ℕ):R) = ((w:ℕ):R) + Q := by
    intro w hw; rw [hQ]; push_cast; ring
  rw [Finset.prod_congr rfl hterm]
  rw [prod_add_factor (Hf p t) (fun w => ((w:ℕ):R)) (fun _ => Q)
      (fun w hw => cast_unit3 hp (mem_Hf.mp hw).2.2)]
  have hB0 : (∏ w ∈ Hf p t, ((w:ℕ):R)) * (∏ u ∈ Af p t, ((u:ℕ):R))
      = ∏ u ∈ Ifs p t, ((u:ℕ):R) := by
    have hsplit := Ifs_eq_HA (t:=t) hp h5
    rw [hsplit.1, Finset.prod_union hsplit.2]
  rw [← hB0]; ring

lemma tau_PiO {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    (∏ w ∈ Hf p t, (1 + ((p^(t+1):ℕ):ZMod ((p^(t+1))^3))
        * (((2*w:ℕ):ZMod ((p^(t+1))^3))⁻¹)))
    * (∏ u ∈ Af p t, (1 + ((p^(t+1):ℕ):ZMod ((p^(t+1))^3))
        * (((2*u - p^(t+1):ℕ):ZMod ((p^(t+1))^3))⁻¹))) = 1 := by
  have hM1 := M1_Ifs (t:=t) hp h5
  obtain ⟨hEO, hdisjEO⟩ := Ifs_eq_EO (t:=t) hp h5
  have hinj1 : Set.InjOn (fun w => 2*w) ↑(Hf p t) := by
    intro a _ b _ h; simp only at h; omega
  have hinj2 : Set.InjOn (fun u => 2*u - p^(t+1)) ↑(Af p t) := by
    intro a ha b hb h
    simp only [Finset.mem_coe, mem_Af] at ha hb; simp only at h; omega
  rw [hEO, Finset.prod_union hdisjEO, Finset.prod_image hinj1, Finset.prod_image hinj2] at hM1
  exact hM1

lemma morley {p t : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    (2 : ZMod ((p^(t+1))^3))^(2*(Ifs p t).card) * (∏ u ∈ S2 p t, ((u:ℕ):ZMod ((p^(t+1))^3)))
      = ∏ u ∈ Ifs p t, ((u:ℕ):ZMod ((p^(t+1))^3)) := by
  set R := ZMod ((p^(t+1))^3)
  have hG := Gcal_eq (t:=t) hp h5
  have hrt := rho_eq_tau_sq (t:=t) hp h5
  have hdbl := doubling (t:=t) hp h5
  have htp := tau_PiO (t:=t) hp h5
  rw [hG, hrt]
  have key : (2:R)^(2*(Ifs p t).card)
      * (∏ w ∈ Hf p t, (1 + ((p^(t+1):ℕ):R) * (((2*w:ℕ):R)⁻¹)))^2 = 1 := by
    have e1 : (2:R)^(2*(Ifs p t).card) = ((2:R)^((Ifs p t).card))^2 := by
      rw [two_mul, pow_add, sq]
    rw [e1, hdbl]
    rw [show (∏ u ∈ Af p t, (1 + ((p^(t+1):ℕ):R) * (((2*u - p^(t+1):ℕ):R)⁻¹)))^2
          * (∏ w ∈ Hf p t, (1 + ((p^(t+1):ℕ):R) * (((2*w:ℕ):R)⁻¹)))^2
        = ((∏ w ∈ Hf p t, (1 + ((p^(t+1):ℕ):R) * (((2*w:ℕ):R)⁻¹)))
            * (∏ u ∈ Af p t, (1 + ((p^(t+1):ℕ):R) * (((2*u - p^(t+1):ℕ):R)⁻¹))))^2 from by ring,
        htp, one_pow]
  rw [show (2:R)^(2*(Ifs p t).card) * ((∏ u ∈ Ifs p t, ((u:ℕ):R))
        * (∏ w ∈ Hf p t, (1 + ((p^(t+1):ℕ):R) * (((2*w:ℕ):R)⁻¹)))^2)
      = (∏ u ∈ Ifs p t, ((u:ℕ):R))
        * ((2:R)^(2*(Ifs p t).card)
          * (∏ w ∈ Hf p t, (1 + ((p^(t+1):ℕ):R) * (((2*w:ℕ):R)⁻¹)))^2) from by ring,
      key, mul_one]

-- ===== card of Ifs =====
lemma Ifs_card {p t : ℕ} (hp : Nat.Prime p) : (Ifs p t).card = p^t * (p-1) := by
  have hps : p^(t+1) = p * p^t := pow_succ' p t
  have hmul : ((Finset.Ico 1 (p^(t+1))).filter (fun u => p ∣ u))
      = (Finset.Ico 1 (p^t)).image (fun i => p*i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image]
    constructor
    · rintro ⟨⟨hj1, hj2⟩, i, rfl⟩
      have hi0 : 0 < i := by
        rcases Nat.eq_zero_or_pos i with h | h
        · simp [h] at hj1
        · exact h
      refine ⟨i, ⟨hi0, ?_⟩, rfl⟩
      have hlt : p*i < p*p^t := by rw [← hps]; exact hj2
      exact lt_of_mul_lt_mul_left hlt (Nat.zero_le p)
    · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, Dvd.intro i rfl⟩
      · nlinarith [hp.pos]
      · rw [hps]; nlinarith [hi2, hp.pos]
  have hmulcard : ((Finset.Ico 1 (p^(t+1))).filter (fun u => p ∣ u)).card = p^t - 1 := by
    rw [hmul, Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hp.pos h)]
    simp [Nat.card_Ico]
  have hpart := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.Ico 1 (p^(t+1))) (p := fun u => p ∣ u)
  have hIco : (Finset.Ico 1 (p^(t+1))).card = p^(t+1) - 1 := by simp [Nat.card_Ico]
  have hIfs : (Ifs p t).card = ((Finset.Ico 1 (p^(t+1))).filter (fun u => ¬ p ∣ u)).card := rfl
  rw [hIfs]
  have hpge : 1 ≤ p^t := Nat.one_le_pow _ _ hp.pos
  rw [hmulcard, hIco] at hpart
  have : p^t * (p-1) = p^(t+1) - p^t := by rw [hps, Nat.mul_comm p (p^t), Nat.mul_sub_one]
  omega

-- ===== shift index helpers =====
lemma div_shift (p a r : ℕ) (hp : 0 < p) (hr : r < p) : (p*a + r)/p = a := by
  rw [Nat.add_comm (p*a) r, Nat.add_mul_div_left r a hp, Nat.div_eq_of_lt hr, Nat.zero_add]

lemma half_shift (q M : ℕ) (hq : q % 2 = 1) (hM : M % 2 = 1) :
    (M*q - 1)/2 = q/2 + ((M-1)/2)*q := by
  have hMq : (M*q) % 2 = 1 := by rw [Nat.mul_mod, hM, hq]
  have hM0 : 0 < M := by omega
  have hq0 : 0 < q := by omega
  have hqle : q ≤ M*q := Nat.le_mul_of_pos_left q hM0
  have hsub : 2*(((M-1)/2)*q) = M*q - q := by
    have h2m : 2*((M-1)/2) = M-1 := by omega
    calc 2*(((M-1)/2)*q) = (2*((M-1)/2))*q := by ring
      _ = (M-1)*q := by rw [h2m]
      _ = M*q - q := by rw [Nat.sub_mul, one_mul]
  omega

section ZsecOdd
variable (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ))))

lemma oddID {p j : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    z h_int ((2*j+1)*p)
      * ((Wp p (3*(j*p+(p-1)/2)+1) : ℤ) * (Wp p ((8*j+4)*p) : ℤ) * (Wp p ((2*j+1)*p) : ℤ))
      = (2:ℤ)^(6*(2*j+1)*(p-1)) * z h_int (2*j+1)
        * ((Wp p ((4*j+2)*p) : ℤ) * (Wp p (9*(j*p+(p-1)/2)+4) : ℤ)) := by
  have hpodd : p % 2 = 1 := by
    rcases (Nat.Prime.eq_two_or_odd hp) with h | h
    · omega
    · exact h
  set m := (p-1)/2 with hmdef
  have hm : p = 2*m+1 := by omega
  set J := j*p + m with hJ
  -- key index equalities
  have h2J1 : 2*J+1 = (2*j+1)*p := by rw [hJ, hm]; ring
  have h8J : 8*J+4 = (8*j+4)*p := by rw [hJ, hm]; ring
  have h4J : 4*J+2 = (4*j+2)*p := by rw [hJ, hm]; ring
  have hN3 : 3*J+1 = p*(3*j+1)+m := by rw [hJ, hm]; ring
  have hN9 : 9*J+4 = p*(9*j+4)+m := by rw [hJ, hm]; ring
  have hmlt : m < p := by omega
  have hdiv3 : (3*J+1)/p = 3*j+1 := by rw [hN3]; exact div_shift p (3*j+1) m hp.pos hmlt
  have hdiv9 : (9*J+4)/p = 9*j+4 := by rw [hN9]; exact div_shift p (9*j+4) m hp.pos hmlt
  -- factorial decompositions
  have d1 : (2*J+1).factorial = p^(2*j+1)*(2*j+1).factorial*Wp p ((2*j+1)*p) := by
    rw [h2J1, factorial_decomp p (2*j+1) hp.pos]
  have d8 : (8*J+4).factorial = p^(8*j+4)*(8*j+4).factorial*Wp p ((8*j+4)*p) := by
    rw [h8J, factorial_decomp p (8*j+4) hp.pos]
  have d4 : (4*J+2).factorial = p^(4*j+2)*(4*j+2).factorial*Wp p ((4*j+2)*p) := by
    rw [h4J, factorial_decomp p (4*j+2) hp.pos]
  have d3 : (3*J+1).factorial = p^(3*j+1)*(3*j+1).factorial*Wp p (3*J+1) := by
    have hd := factorial_decomp_gen p (3*J+1) hp.pos
    rw [hdiv3] at hd; exact hd
  have d9 : (9*J+4).factorial = p^(9*j+4)*(9*j+4).factorial*Wp p (9*J+4) := by
    have hd := factorial_decomp_gen p (9*J+4) hp.pos
    rw [hdiv9] at hd; exact hd
  -- IDj, IDJ
  have IDj := odd_int_id h_int j
  have IDJ := odd_int_id h_int J
  -- decompose IDJ via push_cast and d's
  have hQoJ : ((3*J+1).factorial * (8*J+4).factorial * (2*J+1).factorial : ℕ)
      = p^(13*j+6) * ((3*j+1).factorial * (8*j+4).factorial * (2*j+1).factorial)
        * (Wp p (3*J+1) * Wp p ((8*j+4)*p) * Wp p ((2*j+1)*p)) := by
    rw [d3, d8, d1]; ring
  have hPoJ : ((4*J+2).factorial * (9*J+4).factorial : ℕ)
      = p^(13*j+6) * ((4*j+2).factorial * (9*j+4).factorial)
        * (Wp p ((4*j+2)*p) * Wp p (9*J+4)) := by
    rw [d4, d9]; ring
  rw [hQoJ, hPoJ] at IDJ
  rw [h2J1] at IDJ
  push_cast at IDj IDJ
  -- exponent relation for 2-powers
  have hexp : 12*J+6 = 6*(2*j+1)*(p-1) + (12*j+6) := by
    rw [hJ, hm, Nat.add_sub_cancel]; ring
  have h2pow : (2:ℤ)^(12*J+6) = 2^(6*(2*j+1)*(p-1)) * 2^(12*j+6) := by
    rw [← pow_add, hexp]
  -- cancel F = p^(13j+6) * Qo(j)
  have hFne : (p:ℤ)^(13*j+6) * (((3*j+1).factorial:ℤ) * ((8*j+4).factorial:ℤ) * ((2*j+1).factorial:ℤ)) ≠ 0 := by
    have : (0:ℤ) < (p:ℤ) := by exact_mod_cast hp.pos
    positivity
  apply mul_left_cancel₀ hFne
  linear_combination IDJ
    + ((p:ℤ)^(13*j+6) * ((4*j+2).factorial:ℤ) * ((9*j+4).factorial:ℤ)
        * ((Wp p ((4*j+2)*p):ℤ) * (Wp p (9*J+4):ℤ))) * h2pow
    - ((2:ℤ)^(6*(2*j+1)*(p-1)) * (p:ℤ)^(13*j+6)
        * ((Wp p ((4*j+2)*p):ℤ) * (Wp p (9*J+4):ℤ))) * IDj

end ZsecOdd

-- ===== ODD STEP =====
lemma odd_step (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ))))
    {p t j : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) (hdvd : p^t ∣ (2*j+1)) :
    (p : ℤ)^(3 + 3*t) ∣ (z h_int ((2*j+1)*p) - z h_int (2*j+1)) := by
  set R := ZMod ((p^(t+1))^3) with hRdef
  have hpodd : p % 2 = 1 := by
    rcases (Nat.Prime.eq_two_or_odd hp) with h | h
    · omega
    · exact h
  have hpt_odd : p^t % 2 = 1 := by rw [Nat.pow_mod, hpodd, one_pow]; rfl
  obtain ⟨s, hLs⟩ := hdvd
  have hsodd : s % 2 = 1 := by
    have h1 : (p^t*s) % 2 = 1 := by rw [← hLs]; omega
    rw [Nat.mul_mod, hpt_odd, one_mul, Nat.mod_mod] at h1; exact h1
  set m := (p-1)/2 with hmdef
  have hm : p = 2*m+1 := by omega
  set J := j*p + m with hJ
  have h2J1 : 2*J+1 = (2*j+1)*p := by rw [hJ, hm]; ring
  have hLpq : (2*j+1)*p = s*p^(t+1) := by rw [hLs, pow_succ]; ring
  have hsq : 2*J+1 = s*p^(t+1) := by rw [h2J1, hLpq]
  have hqodd : p^(t+1) % 2 = 1 := by rw [Nat.pow_mod, hpodd, one_pow]; rfl
  have hsqodd : (s*p^(t+1)) % 2 = 1 := by rw [Nat.mul_mod, hsodd, hqodd]
  -- products
  set B0 : R := ∏ u ∈ Ifs p t, ((u:ℕ):R) with hB0
  set G : R := ∏ u ∈ S2 p t, ((u:ℕ):R) with hG
  set H : R := ∏ u ∈ Hf p t, ((u:ℕ):R) with hH
  -- Wp casts
  have cw1 : ((Wp p ((2*j+1)*p):ℕ):R) = B0^s := by
    have hw := W_cast hp h5 1 (2*j+1) s hLs
    rw [one_mul, one_mul] at hw
    rw [hB0]; exact hw
  have cw4 : ((Wp p ((8*j+4)*p):ℕ):R) = B0^(4*s) := by
    have hw := W_cast hp h5 4 (2*j+1) s hLs
    rw [hB0, show (8*j+4)*p = 4*(2*j+1)*p from by ring]; exact hw
  have cw2 : ((Wp p ((4*j+2)*p):ℕ):R) = B0^(2*s) := by
    have hw := W_cast hp h5 2 (2*j+1) s hLs
    rw [hB0, show (4*j+2)*p = 2*(2*j+1)*p from by ring]; exact hw
  -- shifted casts
  have h3sodd : (3*s) % 2 = 1 := by rw [Nat.mul_mod, hsodd]
  have h9sodd : (9*s) % 2 = 1 := by rw [Nat.mul_mod, hsodd]
  have hVs3eq : 3*J+1 = p^(t+1)/2 + ((3*s-1)/2)*p^(t+1) := by
    have e : 3*J+1 = ((3*s)*p^(t+1) - 1)/2 := by
      have h3sq : (3*s)*p^(t+1) = 3*(s*p^(t+1)) := by ring
      omega
    rw [e]; exact half_shift (p^(t+1)) (3*s) hqodd h3sodd
  have hVs9eq : 9*J+4 = p^(t+1)/2 + ((9*s-1)/2)*p^(t+1) := by
    have e : 9*J+4 = ((9*s)*p^(t+1) - 1)/2 := by
      have h9sq : (9*s)*p^(t+1) = 9*(s*p^(t+1)) := by ring
      omega
    rw [e]; exact half_shift (p^(t+1)) (9*s) hqodd h9sodd
  have cvs3 : ((Wp p (3*J+1):ℕ):R) = H * G^((3*s-1)/2) := by
    rw [hH, hG, hVs3eq]; exact Wp_shift hp h5 ((3*s-1)/2)
  have cvs9 : ((Wp p (9*J+4):ℕ):R) = H * G^((9*s-1)/2) := by
    rw [hH, hG, hVs9eq]; exact Wp_shift hp h5 ((9*s-1)/2)
  -- morley to the 3s
  have hexpφ : 6*(2*j+1)*(p-1) = 2*(Ifs p t).card*(3*s) := by
    rw [Ifs_card hp, hLs]; ring
  have hmorley : (2:R)^(2*(Ifs p t).card) * G = B0 := by
    rw [hG, hB0]; exact morley hp h5
  have hmorley3s : (2:R)^(6*(2*j+1)*(p-1)) * G^(3*s) = B0^(3*s) := by
    have hh : ((2:R)^(2*(Ifs p t).card) * G)^(3*s) = B0^(3*s) := by rw [hmorley]
    rw [mul_pow] at hh
    rw [hexpφ, pow_mul]; exact hh
  -- cast ODDID
  have ODDID := oddID h_int (j := j) hp h5
  have hcast := congrArg (fun x : ℤ => ((x : R))) ODDID
  simp only at hcast
  push_cast at hcast
  rw [cvs3, cw4, cw1, cw2, cvs9] at hcast
  -- m9 = m3 + 3s
  have hm9 : (9*s-1)/2 = (3*s-1)/2 + 3*s := by omega
  have hG9 : G^((9*s-1)/2) = G^((3*s-1)/2) * G^(3*s) := by rw [← pow_add, ← hm9]
  rw [hG9] at hcast
  -- hkey
  set ZP : R := ((z h_int ((2*j+1)*p) : ℤ) : R) with hZP
  set ZL : R := ((z h_int (2*j+1) : ℤ) : R) with hZL
  have hkey : ZP * (H * G^((3*s-1)/2) * B0^(5*s)) = ZL * (H * G^((3*s-1)/2) * B0^(5*s)) := by
    linear_combination hcast + (ZL * H * G^((3*s-1)/2) * B0^(2*s)) * hmorley3s
  -- unit
  have hUnit : IsUnit (H * G^((3*s-1)/2) * B0^(5*s)) := by
    have hHu : IsUnit H := by
      rw [hH]
      exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
        (fun w hw => cast_unit3 hp (mem_Hf.mp hw).2.2)
    have hGu : IsUnit G := by
      rw [hG]
      exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
        (fun u hu => cast_unit3 hp (mem_S2.mp hu).2.2)
    have hB0u : IsUnit B0 := hB0 ▸ B0_unit (t := t) hp
    exact (hHu.mul (hGu.pow _)).mul (hB0u.pow _)
  have hsub : (ZP - ZL) * (H * G^((3*s-1)/2) * B0^(5*s)) = 0 := by
    rw [sub_mul, hkey, sub_self]
  have hZPL : ZP - ZL = 0 := (IsUnit.mul_left_eq_zero hUnit).mp hsub
  have hZeq : ((z h_int ((2*j+1)*p) - z h_int (2*j+1) : ℤ) : R) = 0 := by
    rw [hZP, hZL] at hZPL; push_cast; linear_combination hZPL
  have hZeq2 : ((z h_int ((2*j+1)*p) - z h_int (2*j+1) : ℤ) : ZMod ((p^(t+1))^3)) = 0 := hZeq
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hZeq2
  have hmod : (((p^(t+1))^3 : ℕ) : ℤ) = (p:ℤ)^(3 + 3*t) := by push_cast; ring
  rw [hmod] at hZeq2
  exact hZeq2

-- ===== STEP (combine even & odd) =====
lemma step (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ))))
    (p : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (L t : ℕ)
    (hLpos : 0 < L) (hdvd : p ^ t ∣ L) :
    (p : ℤ) ^ (3 + 3 * t) ∣ (z h_int (L * p) - z h_int L) := by
  rcases Nat.even_or_odd L with ⟨k, hk⟩ | ⟨j, hj⟩
  · -- L even, L = 2*k
    have hL2 : L = 2 * k := by omega
    have hdvd2 : p ^ t ∣ 2 * k := by rw [← hL2]; exact hdvd
    have hcop : Nat.Coprime (p ^ t) 2 :=
      Nat.Coprime.pow_left t ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
    have hdk : p ^ t ∣ k := hcop.dvd_of_dvd_mul_left hdvd2
    have he := even_step h_int hp h5 hdk
    have e1 : 2 * (k * p) = L * p := by rw [hL2]; ring
    have e2 : 2 * k = L := hL2.symm
    rw [e1, e2] at he
    exact he
  · -- L odd, L = 2*j+1
    have ho := odd_step h_int hp h5 (hj ▸ hdvd : p ^ t ∣ (2 * j + 1))
    rw [← hj] at ho
    exact ho

theorem main (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ))))
    (p : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (n r : ℕ) (hn : n > 0) (hr : r > 0) :
    (z h_int (n * p ^ r)) ≡ (z h_int (n * p ^ (r - 1))) [ZMOD ((p : ℤ) ^ (3 * r))] := by
  set L := n * p ^ (r - 1) with hL
  have hLpos : 0 < L := by positivity
  have hdvd : p ^ (r - 1) ∣ L := Dvd.intro_left n rfl
  have hstep := step h_int p hp h5 L (r - 1) hLpos hdvd
  have hLp : L * p = n * p ^ r := by
    rw [hL, mul_assoc, ← pow_succ]
    congr 2
    omega
  rw [hLp] at hstep
  have hexp : 3 * r ≤ 3 + 3 * (r - 1) := by omega
  have hdvd2 : (p : ℤ) ^ (3 * r) ∣ (z h_int (n * p ^ r) - z h_int L) :=
    dvd_trans (pow_dvd_pow _ hexp) hstep
  rw [Int.modEq_iff_dvd]
  exact dvd_sub_comm.mp hdvd2

theorem oeis_364173_conjecture_0
    (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] := by
  intro p hp h_p_ge_5 n r hn hr
  exact main h_int p hp h_p_ge_5 n r hn hr
