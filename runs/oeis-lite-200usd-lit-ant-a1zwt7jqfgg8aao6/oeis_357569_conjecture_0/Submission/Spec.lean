import FormalConjectures.Util.ProblemImports
open Nat


open Finset

variable {ι : Type*} [DecidableEq ι]


/-! ## Combinatorial reindexing -/

theorem reindex_neg {M : Type*} [CommMonoid M] (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r)
    (g : ℕ → M) :
    ∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), g j
    = ∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), g (p^r - j) := by
  have key : ∀ a ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i),
      a < p^r ∧ (p^r - a) ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_Ico] at ha ⊢
    obtain ⟨⟨ha1, ha2⟩, hap⟩ := ha
    have haN : a < p^r := by
      rcases Nat.lt_or_ge a (p^r) with h | h
      · exact h
      · exfalso; have : a = p^r := by omega
        exact hap (this ▸ dvd_pow_self p (by omega))
    refine ⟨haN, ⟨by omega, by omega⟩, ?_⟩
    intro hdvd
    have h1 : p ∣ p^r := dvd_pow_self p (by omega)
    have hd : p ∣ (p^r - (p^r - a)) := Nat.dvd_sub h1 hdvd
    rw [Nat.sub_sub_self haN.le] at hd
    exact hap hd
  apply Finset.prod_nbij' (fun j => p^r - j) (fun j => p^r - j)
  · intro a ha; exact (key a ha).2
  · intro a ha; exact (key a ha).2
  · intro a ha; have := (key a ha).1; omega
  · intro a ha; have := (key a ha).1; omega
  · intro a ha; have := (key a ha).1; rw [Nat.sub_sub_self this.le]

lemma Ufilter_eq (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) :
    (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i) = (Ico 1 (p^r)).filter (fun i => ¬ p ∣ i) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp'⟩
    refine ⟨⟨h1, ?_⟩, hp'⟩
    rcases Nat.lt_or_ge j (p^r) with h | h
    · exact h
    · exfalso; have : j = p^r := by omega
      exact hp' (this ▸ dvd_pow_self p (by omega))
  · rintro ⟨⟨h1, h2⟩, hp'⟩
    exact ⟨⟨h1, by omega⟩, hp'⟩

lemma castsub (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) (j : ℕ)
    (hj : j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i)) :
    ((p^r - j : ℕ) : ℤ) = (p:ℤ)^r - (j : ℤ) := by
  simp only [Finset.mem_filter, Finset.mem_Ico] at hj
  obtain ⟨⟨hj1, hj2⟩, hjp⟩ := hj
  have hjN : j < p^r := by
    rcases Nat.lt_or_ge j (p^r) with h | h
    · exact h
    · exfalso; have hj' : j = p^r := by omega
      exact hjp (hj' ▸ dvd_pow_self p (by omega))
  rw [Nat.cast_sub hjN.le, Nat.cast_pow]

/-! ## Bridge: sum over units = sum over coprime residues -/

theorem bridge {M : Type*} [AddCommMonoid M] (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r)
    [NeZero (p^r)] (F : ZMod (p^r) → M) :
    ∑ u : (ZMod (p^r))ˣ, F (↑u) =
    ∑ j ∈ (Finset.Ico 1 (p^r)).filter (fun j => ¬ (p ∣ j)), F (↑j) := by
  haveI : Fact (1 < p^r) := ⟨by calc 1 < p := hp.one_lt
                                  _ ≤ p^r := Nat.le_self_pow (by omega) p⟩
  apply Finset.sum_bij (fun (u : (ZMod (p^r))ˣ) (_ : u ∈ Finset.univ) => ZMod.val (u : ZMod (p^r)))
  · intro u _
    rw [Finset.mem_filter, Finset.mem_Ico]
    have hcop : (ZMod.val (u : ZMod (p^r))).Coprime (p^r) := ZMod.val_coe_unit_coprime u
    have hlt : ZMod.val (u : ZMod (p^r)) < p^r := ZMod.val_lt _
    have hpos : 1 ≤ ZMod.val (u : ZMod (p^r)) := by
      rcases Nat.eq_zero_or_pos (ZMod.val (u : ZMod (p^r))) with h | h
      · exfalso
        have h0 : (↑u : ZMod (p^r)) = 0 := by
          have := ZMod.natCast_zmod_val (↑u : ZMod (p^r)); rw [h] at this; simpa using this.symm
        exact u.isUnit.ne_zero h0
      · exact h
    refine ⟨⟨hpos, hlt⟩, ?_⟩
    intro hpdvd
    have hp1 : p ∣ p^r := dvd_pow_self p (by omega)
    have hd : p ∣ Nat.gcd (ZMod.val (u : ZMod (p^r))) (p^r) := Nat.dvd_gcd hpdvd hp1
    rw [Nat.Coprime] at hcop; rw [hcop] at hd
    have h1 := Nat.dvd_one.mp hd; have := hp.one_lt; omega
  · intro u _ v _ huv
    apply Units.ext
    have : ((ZMod.val (u : ZMod (p^r))) : ZMod (p^r)) = ((ZMod.val (v : ZMod (p^r))) : ZMod (p^r)) := by
      rw [huv]
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at this
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_Ico] at hj
    obtain ⟨⟨hj1, hj2⟩, hjp⟩ := hj
    have hcop : (j).Coprime (p^r) := (Nat.Coprime.pow_left r (hp.coprime_iff_not_dvd.mpr hjp)).symm
    have hu : IsUnit (↑j : ZMod (p^r)) := (ZMod.isUnit_iff_coprime j (p^r)).mpr hcop
    refine ⟨hu.unit, Finset.mem_univ _, ?_⟩
    rw [IsUnit.unit_spec, ZMod.val_cast_of_lt hj2]
  · intro u _; rw [ZMod.natCast_zmod_val]

theorem sum_units_sq_eq_zero (n : ℕ) [NeZero n] (h2 : IsUnit (2 : ZMod n)) (h3 : IsUnit (3 : ZMod n)) :
    ∑ u : (ZMod n)ˣ, ((u : ZMod n))^2 = 0 := by
  set S := ∑ u : (ZMod n)ˣ, ((u : ZMod n))^2 with hS
  set a := h2.unit with ha
  have hav : (↑a : ZMod n) = 2 := h2.unit_spec
  have h1 : S = ∑ u : (ZMod n)ˣ, ((↑(a*u) : ZMod n))^2 :=
    (Equiv.sum_comp (Equiv.mulLeft a) (fun u => ((u : ZMod n))^2)).symm
  have h2' : ∑ u : (ZMod n)ˣ, ((↑(a*u) : ZMod n))^2 = 4 * S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Units.val_mul, hav]; ring
  have hSS : S = 4 * S := h1.trans h2'
  have h3s : (3 : ZMod n) * S = 0 := by linear_combination -hSS
  exact (h3.mul_right_eq_zero).mp h3s

theorem sum_units_inv_sq (n : ℕ) [NeZero n] (h2 : IsUnit (2 : ZMod n)) (h3 : IsUnit (3 : ZMod n)) :
    ∑ u : (ZMod n)ˣ, ((u : ZMod n))⁻¹^2 = 0 := by
  have hreindex : ∑ u : (ZMod n)ˣ, ((u : ZMod n))⁻¹^2 = ∑ u : (ZMod n)ˣ, ((u : ZMod n))^2 := by
    rw [← Equiv.sum_comp (Equiv.inv (ZMod n)ˣ) (fun u => ((u : ZMod n))^2)]
    apply Finset.sum_congr rfl
    intro u _
    simp only [Equiv.inv_apply]
    rw [ZMod.inv_coe_unit]
  rw [hreindex]; exact sum_units_sq_eq_zero n h2 h3

/-! ## Units helpers -/

lemma two_unit (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) [NeZero (p^r)] :
    IsUnit (2 : ZMod (p^r)) := by
  have : ((2:ℕ) : ZMod (p^r)) = (2 : ZMod (p^r)) := by push_cast; ring
  rw [← this, ZMod.isUnit_iff_coprime]
  refine Nat.Coprime.pow_right r ((hp.coprime_iff_not_dvd.mpr ?_).symm)
  intro h; have := Nat.le_of_dvd (by norm_num) h; omega

lemma three_unit (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) [NeZero (p^r)] :
    IsUnit (3 : ZMod (p^r)) := by
  have : ((3:ℕ) : ZMod (p^r)) = (3 : ZMod (p^r)) := by push_cast; ring
  rw [← this, ZMod.isUnit_iff_coprime]
  refine Nat.Coprime.pow_right r ((hp.coprime_iff_not_dvd.mpr ?_).symm)
  intro h; have := Nat.le_of_dvd (by norm_num) h; omega

lemma jbar_unit (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) [NeZero (p^r)] (j : ℕ)
    (hj : j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i)) :
    IsUnit ((j : ZMod (p^r))) := by
  simp only [Finset.mem_filter, Finset.mem_Ico] at hj
  obtain ⟨⟨hj1, hj2⟩, hjp⟩ := hj
  rw [ZMod.isUnit_iff_coprime]
  exact (Nat.Coprime.pow_right r ((hp.coprime_iff_not_dvd.mpr hjp).symm))

/-! ## PAIR identities -/

theorem pairD (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) :
    (∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), (j : ℤ))^2
    = ∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), ((j:ℤ) * ((p:ℤ)^r - j)) := by
  have hrev := reindex_neg p r hp hr (fun j => (j:ℤ))
  rw [sq]; nth_rewrite 2 [hrev]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj; rw [castsub p r hp hr j hj]

theorem pairA2 (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) :
    (∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), ((p:ℤ)^r + j))^2
    = ∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), ((j:ℤ) * ((p:ℤ)^r - j) + 2*((p:ℤ)^r)^2) := by
  have hrev := reindex_neg p r hp hr (fun j => (p:ℤ)^r + (j:ℤ))
  rw [sq]; nth_rewrite 2 [hrev]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj; rw [castsub p r hp hr j hj]; ring

theorem pairA3 (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) :
    (∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), (2*(p:ℤ)^r + j))^2
    = ∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), ((j:ℤ) * ((p:ℤ)^r - j) + 6*((p:ℤ)^r)^2) := by
  have hrev := reindex_neg p r hp hr (fun j => 2*(p:ℤ)^r + (j:ℤ))
  rw [sq]; nth_rewrite 2 [hrev]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj; rw [castsub p r hp hr j hj]; ring

/-! ## Taylor expansions of products -/

theorem prod_add_const_mod_sq {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℤ) (a : ℤ) :
    (∏ i ∈ s, (c i + a)) ≡ (∏ i ∈ s, c i) + a * (∑ i ∈ s, ∏ j ∈ s.erase i, c j) [ZMOD a^2] := by
  induction s using Finset.induction with
  | empty => simp
  | @insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.prod_insert hk]
      have hsum : (∑ i ∈ insert k s, ∏ j ∈ (insert k s).erase i, c j)
          = (∏ j ∈ s, c j) + c k * (∑ i ∈ s, ∏ j ∈ s.erase i, c j) := by
        rw [Finset.sum_insert hk]
        congr 1
        · rw [Finset.erase_insert hk]
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          have hik : i ≠ k := fun h => hk (h ▸ hi)
          rw [Finset.erase_insert_of_ne (Ne.symm hik),
              Finset.prod_insert (fun h => hk (Finset.mem_of_mem_erase h))]
      rw [hsum]
      calc (c k + a) * ∏ i ∈ s, (c i + a)
          ≡ (c k + a) * ((∏ i ∈ s, c i) + a * (∑ i ∈ s, ∏ j ∈ s.erase i, c j)) [ZMOD a^2] :=
            Int.ModEq.mul_left _ ih
        _ = c k * (∏ i ∈ s, c i) + a * ((∏ j ∈ s, c j) + c k * (∑ i ∈ s, ∏ j ∈ s.erase i, c j)) + a^2 * (∑ i ∈ s, ∏ j ∈ s.erase i, c j) := by ring
        _ ≡ c k * (∏ i ∈ s, c i) + a * ((∏ j ∈ s, c j) + c k * (∑ i ∈ s, ∏ j ∈ s.erase i, c j)) + 0 [ZMOD a^2] := by
            apply Int.ModEq.add_left
            exact (Int.modEq_zero_iff_dvd.2 ⟨_, rfl⟩)
        _ = c k * (∏ i ∈ s, c i) + a * ((∏ j ∈ s, c j) + c k * (∑ i ∈ s, ∏ j ∈ s.erase i, c j)) := by ring

/-! ## HARM1 -/

theorem harm1 (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) :
    (p:ℤ)^r ∣ ∑ i ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i),
      ∏ j ∈ ((Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i)).erase i, ((j:ℤ)*((p:ℤ)^r-j)) := by
  haveI : NeZero (p^r) := ⟨by positivity⟩
  set U := (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i) with hU
  have hcast : ((p:ℤ)^r) = (((p^r : ℕ)) : ℤ) := by push_cast; ring
  rw [hcast, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  set c : ℕ → ZMod (p^r) := fun j => (j : ZMod (p^r)) * ((p : ZMod (p^r))^r - (j : ZMod (p^r))) with hc
  have hcj : ∀ j, c j = -((j : ZMod (p^r)))^2 := by
    intro j
    rw [hc]
    have : (p : ZMod (p^r))^r = 0 := by
      rw [← Nat.cast_pow]; exact ZMod.natCast_self _
    rw [this]; ring
  have hgoal : (∑ i ∈ U, ∏ j ∈ U.erase i, ((j:ZMod (p^r)) * ((p:ZMod (p^r))^r - (j:ZMod (p^r))))) = 0 := by
    have hcunit : ∀ i ∈ U, IsUnit (c i) := by
      intro i hi; rw [hcj]
      exact ((jbar_unit p r hp hr i hi).pow 2).neg
    set P := ∏ j ∈ U, c j with hP
    have hsplit : (∑ i ∈ U, ∏ j ∈ U.erase i, c j) = P * ∑ i ∈ U, (c i)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have he : (∏ j ∈ U.erase i, c j) * c i = P := Finset.prod_erase_mul U c hi
      have hui : c i * (c i)⁻¹ = 1 := ZMod.mul_inv_of_unit _ (hcunit i hi)
      calc ∏ j ∈ U.erase i, c j = (∏ j ∈ U.erase i, c j) * (c i * (c i)⁻¹) := by rw [hui, mul_one]
        _ = ((∏ j ∈ U.erase i, c j) * c i) * (c i)⁻¹ := by ring
        _ = P * (c i)⁻¹ := by rw [he]
    have hsum0 : (∑ i ∈ U, (c i)⁻¹) = 0 := by
      have hrw : ∀ i ∈ U, (c i)⁻¹ = -((i : ZMod (p^r))⁻¹^2) := by
        intro i hi
        have hu : IsUnit ((i:ZMod (p^r))) := jbar_unit p r hp hr i hi
        rw [hcj i]
        set x := (i : ZMod (p^r))
        have hii : x * x⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu
        have hunit : IsUnit (-x^2) := (hu.pow 2).neg
        have hmul : (-x^2) * (-(x⁻¹)^2) = 1 := by
          have h1 : (-x^2) * (-(x⁻¹)^2) = (x * x⁻¹)^2 := by ring
          rw [h1, hii, one_pow]
        have hinv : (-x^2) * (-x^2)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hunit
        calc (-x^2)⁻¹ = (-x^2)⁻¹ * 1 := by rw [mul_one]
          _ = (-x^2)⁻¹ * ((-x^2) * (-(x⁻¹)^2)) := by rw [hmul]
          _ = ((-x^2)⁻¹ * (-x^2)) * (-(x⁻¹)^2) := by ring
          _ = ((-x^2) * (-x^2)⁻¹) * (-(x⁻¹)^2) := by rw [mul_comm ((-x^2)⁻¹)]
          _ = 1 * (-(x⁻¹)^2) := by rw [hinv]
          _ = -(x⁻¹^2) := by rw [one_mul]
      rw [Finset.sum_congr rfl hrw, Finset.sum_neg_distrib]
      have hbr := bridge p r hp hr (fun x => x⁻¹^2)
      rw [← Ufilter_eq p r hp hr] at hbr
      rw [← hU] at hbr
      rw [← hbr, sum_units_inv_sq (p^r) (two_unit p r hp hp5) (three_unit p r hp hp5), neg_zero]
    rw [hsplit, hsum0, mul_zero]
  rw [← hgoal]

/-! ## General pair identity and valuation lemmas (p ≥ 5) -/

theorem pairAm (p r m : ℕ) (hp : p.Prime) (hr : 1 ≤ r) :
    (∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), ((m:ℤ)*(p:ℤ)^r + j))^2
    = ∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i),
        ((j:ℤ) * ((p:ℤ)^r - j) + ((m:ℤ)^2+(m:ℤ))*((p:ℤ)^r)^2) := by
  have hrev := reindex_neg p r hp hr (fun j => (m:ℤ)*(p:ℤ)^r + (j:ℤ))
  rw [sq]; nth_rewrite 2 [hrev]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj; rw [castsub p r hp hr j hj]; ring

lemma DZMod_ne (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) :
    (∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), (j : ZMod p)) ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_Ico] at hj
  obtain ⟨⟨hj1, hj2⟩, hjp⟩ := hj
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact hjp

lemma not_dvd_D (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) :
    ¬ (p:ℤ) ∣ ∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), (j:ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hdvd
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hdvd
  push_cast at hdvd
  exact DZMod_ne p r hp hr hdvd

lemma pdvd_Bm_sub_D (p r m : ℕ) (hp : p.Prime) (hr : 1 ≤ r) :
    (p:ℤ) ∣ (∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), ((m:ℤ)*(p:ℤ)^r + j))
            - (∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), (j:ℤ)) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [sub_eq_zero]
  apply Finset.prod_congr rfl
  intro j hj
  have hp0 : (p : ZMod p) = 0 := ZMod.natCast_self p
  rw [hp0, zero_pow (by omega : r ≠ 0)]; ring

lemma not_dvd_Bm_add_D (p r m : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 1 ≤ r) :
    ¬ (p:ℤ) ∣ ((∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), ((m:ℤ)*(p:ℤ)^r + j))
              + (∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), (j:ℤ))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hdvd
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hdvd
  push_cast at hdvd
  -- (B_m : ZMod p) = (D : ZMod p)
  have hB : (∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), ((m:ZMod p)*(p:ZMod p)^r + (j:ZMod p)))
          = (∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), (j : ZMod p)) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hp0 : (p : ZMod p) = 0 := ZMod.natCast_self p
    rw [hp0, zero_pow (by omega : r ≠ 0)]; ring
  rw [hB] at hdvd
  have h2 : (2 : ZMod p) * (∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), (j : ZMod p)) = 0 := by
    rw [two_mul]; exact hdvd
  rcases mul_eq_zero.mp h2 with h | h
  · have : ((2:ℕ) : ZMod p) = 0 := by push_cast; exact h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this; omega
  · exact DZMod_ne p r hp hr h

theorem valgen (p r m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) :
    (p:ℤ)^(3*r) ∣ (∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), ((m:ℤ)*(p:ℤ)^r + j))
                 - (∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), (j:ℤ)) := by
  set U := (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i) with hU
  set Bm := ∏ j ∈ U, ((m:ℤ)*(p:ℤ)^r + j) with hBm
  set D := ∏ j ∈ U, (j:ℤ) with hD
  set E1 := ∑ i ∈ U, ∏ j ∈ U.erase i, ((j:ℤ)*((p:ℤ)^r-j)) with hE1
  -- p^{3r} | Bm^2 - D^2
  have hsq : (p:ℤ)^(3*r) ∣ Bm^2 - D^2 := by
    have hpair : Bm^2 = ∏ j ∈ U, ((j:ℤ) * ((p:ℤ)^r - j) + ((m:ℤ)^2+(m:ℤ))*((p:ℤ)^r)^2) := pairAm p r m hp hr
    have hpairD : D^2 = ∏ j ∈ U, ((j:ℤ) * ((p:ℤ)^r - j)) := pairD p r hp hr
    set a := ((m:ℤ)^2+(m:ℤ))*((p:ℤ)^r)^2 with ha
    have ht := prod_add_const_mod_sq U (fun j => (j:ℤ)*((p:ℤ)^r-j)) a
    -- ht : ∏(c+a) ≡ ∏c + a*E1 [ZMOD a^2]
    rw [Int.modEq_iff_dvd] at ht
    -- ht : a^2 ∣ (∏c + a*E1) - ∏(c+a)
    have hBmsq : Bm^2 = ∏ j ∈ U, ((j:ℤ)*((p:ℤ)^r-j) + a) := by rw [hpair]
    have hDsq : D^2 = ∏ j ∈ U, ((j:ℤ)*((p:ℤ)^r-j)) := hpairD
    -- Bm^2 - D^2 = (∏(c+a)) - (∏ c)
    have hdiff : Bm^2 - D^2 = (∏ j ∈ U, ((j:ℤ)*((p:ℤ)^r-j) + a)) - (∏ j ∈ U, ((j:ℤ)*((p:ℤ)^r-j))) := by
      rw [hBmsq, hDsq]
    -- a*E1 divisible by p^{3r}
    have hE1dvd : (p:ℤ)^r ∣ E1 := harm1 p r hp hp5 hr
    obtain ⟨k, hk⟩ := hE1dvd
    set t := (p:ℤ)^r with htt
    have e3 : (p:ℤ)^(3*r) = t^3 := by rw [htt, ← pow_mul]; congr 1; ring
    have haE1 : (p:ℤ)^(3*r) ∣ a * E1 := by
      rw [ha, hk, e3]
      exact ⟨((m:ℤ)^2+(m:ℤ)) * k, by ring⟩
    have ha2 : (p:ℤ)^(3*r) ∣ a^2 := by
      rw [ha, e3]
      exact ⟨((m:ℤ)^2+(m:ℤ))^2 * t, by ring⟩
    -- combine: Bm^2-D^2 = a*E1 + (a^2 multiple)
    have hcomb : Bm^2 - D^2 = a * E1 - ((∏ j ∈ U, ((j:ℤ)*((p:ℤ)^r-j)) + a * E1) - (∏ j ∈ U, ((j:ℤ)*((p:ℤ)^r-j) + a))) := by
      rw [hdiff]; ring
    rw [hcomb]
    exact dvd_sub haE1 (dvd_trans ha2 ht)
  -- coprimality of Bm + D with p
  have hcop : IsCoprime ((p:ℤ)^(3*r)) (Bm + D) := by
    have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
    have h1 : IsCoprime (p:ℤ) (Bm + D) := hpp.coprime_iff_not_dvd.mpr (not_dvd_Bm_add_D p r m hp (by omega) hr)
    exact h1.pow_left
  -- Bm^2 - D^2 = (Bm - D)*(Bm + D)
  have hfact : Bm^2 - D^2 = (Bm - D) * (Bm + D) := by ring
  rw [hfact] at hsq
  exact hcop.dvd_of_dvd_mul_right hsq



def S1 (s : Finset ι) (c : ι → ℤ) : ℤ := ∑ i ∈ s, ∏ j ∈ s.erase i, c j
def S2 (s : Finset ι) (c : ι → ℤ) : ℤ :=
  ∑ i ∈ s, ∑ k ∈ s.erase i, ∏ j ∈ (s.erase i).erase k, c j

lemma S1_insert (s : Finset ι) (c : ι → ℤ) (k : ι) (hk : k ∉ s) :
    S1 (insert k s) c = (∏ j ∈ s, c j) + c k * S1 s c := by
  unfold S1
  rw [Finset.sum_insert hk, Finset.erase_insert hk]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≠ k := fun h => hk (h ▸ hi)
  rw [Finset.erase_insert_of_ne hik.symm, Finset.prod_insert (fun h => hk (Finset.mem_of_mem_erase h))]

lemma S2_insert (s : Finset ι) (c : ι → ℤ) (k : ι) (hk : k ∉ s) :
    S2 (insert k s) c = 2 * S1 s c + c k * S2 s c := by
  unfold S2 S1
  rw [Finset.sum_insert hk, Finset.erase_insert hk]
  have hthis : ∀ i ∈ s, (∑ k' ∈ (insert k s).erase i, ∏ j ∈ ((insert k s).erase i).erase k', c j)
      = (∏ j ∈ s.erase i, c j) + c k * (∑ k' ∈ s.erase i, ∏ j ∈ (s.erase i).erase k', c j) := by
    intro i hi
    have hik : i ≠ k := fun h => hk (h ▸ hi)
    rw [Finset.erase_insert_of_ne hik.symm]
    rw [Finset.sum_insert (fun h => hk (Finset.mem_of_mem_erase h))]
    rw [Finset.erase_insert (fun h => hk (Finset.mem_of_mem_erase h))]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k' hk'
    have hk'k : k' ≠ k := fun h => hk (h ▸ (Finset.mem_of_mem_erase hk'))
    rw [Finset.erase_insert_of_ne hk'k.symm, Finset.prod_insert
      (fun h => hk (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)))]
  rw [Finset.sum_congr rfl hthis, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem prod_add_const_mod_cube (s : Finset ι) (c : ι → ℤ) (t : ℤ) :
    2 * (∏ i ∈ s, (c i + t)) ≡ 2 * (∏ i ∈ s, c i) + 2*t*(S1 s c) + t^2*(S2 s c) [ZMOD t^3] := by
  induction s using Finset.induction with
  | empty => simp [S1, S2]
  | @insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.prod_insert hk, S1_insert s c k hk, S2_insert s c k hk]
      calc 2 * ((c k + t) * ∏ i ∈ s, (c i + t))
          = (c k + t) * (2 * ∏ i ∈ s, (c i + t)) := by ring
        _ ≡ (c k + t) * (2 * (∏ i ∈ s, c i) + 2*t*(S1 s c) + t^2*(S2 s c)) [ZMOD t^3] :=
            Int.ModEq.mul_left _ ih
        _ = (2 * (c k * ∏ i ∈ s, c i) + 2*t*((∏ j ∈ s, c j) + c k * S1 s c)
              + t^2*(2 * S1 s c + c k * S2 s c))
            + t^3*(S2 s c) := by ring
        _ ≡ (2 * (c k * ∏ i ∈ s, c i) + 2*t*((∏ j ∈ s, c j) + c k * S1 s c)
              + t^2*(2 * S1 s c + c k * S2 s c)) + 0 [ZMOD t^3] := by
            apply Int.ModEq.add_left
            exact (Int.modEq_zero_iff_dvd.2 ⟨_, rfl⟩)
        _ = 2 * (c k * ∏ i ∈ s, c i) + 2*t*((∏ j ∈ s, c j) + c k * S1 s c)
              + t^2*(2 * S1 s c + c k * S2 s c) := by ring



-- generic S1 for any commring image
def S1g {R : Type*} [CommRing R] (s : Finset ι) (c : ι → R) : R := ∑ i ∈ s, ∏ j ∈ s.erase i, c j
def S2g {R : Type*} [CommRing R] (s : Finset ι) (c : ι → R) : R :=
  ∑ i ∈ s, ∑ k ∈ s.erase i, ∏ j ∈ (s.erase i).erase k, c j

lemma cinv_eq (n : ℕ) [NeZero n] (x : ZMod n) (hu : IsUnit x) :
    (-x^2)⁻¹ = -(x⁻¹)^2 := by
  have hii : x * x⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu
  have hunit : IsUnit (-x^2) := (hu.pow 2).neg
  have hmul : (-x^2) * (-(x⁻¹)^2) = 1 := by
    have h1 : (-x^2) * (-(x⁻¹)^2) = (x * x⁻¹)^2 := by ring
    rw [h1, hii, one_pow]
  have hinv : (-x^2) * (-x^2)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hunit
  calc (-x^2)⁻¹ = (-x^2)⁻¹ * 1 := by rw [mul_one]
    _ = (-x^2)⁻¹ * ((-x^2) * (-(x⁻¹)^2)) := by rw [hmul]
    _ = ((-x^2)⁻¹ * (-x^2)) * (-(x⁻¹)^2) := by ring
    _ = ((-x^2) * (-x^2)⁻¹) * (-(x⁻¹)^2) := by rw [mul_comm ((-x^2)⁻¹)]
    _ = 1 * (-(x⁻¹)^2) := by rw [hinv]
    _ = -(x⁻¹)^2 := by rw [one_mul]

-- S1 over a set of units (in ZMod n)
lemma S1g_units (n : ℕ) [NeZero n] (s : Finset ι) (c : ι → ZMod n)
    (hc : ∀ i ∈ s, IsUnit (c i)) :
    S1g s c = (∏ j ∈ s, c j) * (∑ i ∈ s, (c i)⁻¹) := by
  unfold S1g
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : (∏ j ∈ s.erase i, c j) * c i = ∏ j ∈ s, c j := Finset.prod_erase_mul s c hi
  have hui : c i * (c i)⁻¹ = 1 := ZMod.mul_inv_of_unit _ (hc i hi)
  calc ∏ j ∈ s.erase i, c j = (∏ j ∈ s.erase i, c j) * (c i * (c i)⁻¹) := by rw [hui, mul_one]
    _ = ((∏ j ∈ s.erase i, c j) * c i) * (c i)⁻¹ := by ring
    _ = (∏ j ∈ s, c j) * (c i)⁻¹ := by rw [he]

lemma S2g_units (n : ℕ) [NeZero n] (s : Finset ι) (c : ι → ZMod n)
    (hc : ∀ i ∈ s, IsUnit (c i)) :
    S2g s c = (∏ j ∈ s, c j) * ((∑ i ∈ s, (c i)⁻¹)^2 - ∑ i ∈ s, ((c i)⁻¹)^2) := by
  have hrfl : S2g s c = ∑ i ∈ s, S1g (s.erase i) c := rfl
  rw [hrfl]
  have hstep : ∀ i ∈ s, S1g (s.erase i) c
      = (∏ j ∈ s, c j) * ((c i)⁻¹ * ((∑ k ∈ s, (c k)⁻¹) - (c i)⁻¹)) := by
    intro i hi
    rw [S1g_units n (s.erase i) c (fun j hj => hc j (Finset.mem_of_mem_erase hj))]
    have hpe : (∏ j ∈ s.erase i, c j) = (∏ j ∈ s, c j) * (c i)⁻¹ := by
      have he : (∏ j ∈ s.erase i, c j) * (c i) = ∏ j ∈ s, c j := Finset.prod_erase_mul s c hi
      have hui : c i * (c i)⁻¹ = 1 := ZMod.mul_inv_of_unit _ (hc i hi)
      calc ∏ j ∈ s.erase i, c j = (∏ j ∈ s.erase i, c j) * (c i * (c i)⁻¹) := by rw [hui, mul_one]
        _ = ((∏ j ∈ s.erase i, c j) * c i) * (c i)⁻¹ := by ring
        _ = (∏ j ∈ s, c j) * (c i)⁻¹ := by rw [he]
    have hse : (∑ k ∈ s.erase i, (c k)⁻¹) = (∑ k ∈ s, (c k)⁻¹) - (c i)⁻¹ :=
      Finset.sum_erase_eq_sub hi
    rw [hpe, hse]; ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  congr 1
  have hexp : ∀ i ∈ s, (c i)⁻¹ * ((∑ k ∈ s, (c k)⁻¹) - (c i)⁻¹)
      = (c i)⁻¹ * (∑ k ∈ s, (c k)⁻¹) - ((c i)⁻¹)^2 := by
    intro i hi; ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

lemma res_count (p r : ℕ) (hp : p.Prime) (hr : 2 ≤ r) (h : ZMod p → ZMod p) :
    ∑ i ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), h (i : ZMod p) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set U := (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i) with hU
  set T := (Ico 1 p) ×ˢ (range (p^(r-1))) with hT
  have hppos : 0 < p := hp.pos
  have hbij : (∑ i ∈ U, h (i : ZMod p)) = ∑ x ∈ T, h (((x.1 + x.2 * p : ℕ)) : ZMod p) := by
    apply Finset.sum_nbij' (fun i => (i % p, i / p)) (fun x => x.1 + x.2 * p)
    · intro a ha
      simp only [hU, Finset.mem_filter, Finset.mem_Ico] at ha
      obtain ⟨⟨ha1, ha2⟩, hap⟩ := ha
      simp only [hT, Finset.mem_product, Finset.mem_Ico, Finset.mem_range]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rcases Nat.eq_zero_or_pos (a % p) with h0 | h0
        · exact absurd (Nat.dvd_of_mod_eq_zero h0) hap
        · exact h0
      · exact Nat.mod_lt a hppos
      · have haN : a < p^r := by
          rcases Nat.lt_or_ge a (p^r) with hlt | hge
          · exact hlt
          · exfalso; have : a = p^r := by omega
            exact hap (this ▸ dvd_pow_self p (by omega))
        rw [Nat.div_lt_iff_lt_mul hppos]
        calc a < p^r := haN
          _ = p^(r-1)*p := by rw [← pow_succ]; congr 1; omega
    · intro x hx
      simp only [hT, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hx
      obtain ⟨⟨h1, h2⟩, h3⟩ := hx
      simp only [hU, Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨by omega, ?_⟩, ?_⟩
      · have hpp : p^(r-1)*p = p^r := by rw [← pow_succ]; congr 1; omega
        have hb : x.2 * p ≤ p^r - p := by
          calc x.2 * p ≤ (p^(r-1)-1)*p := Nat.mul_le_mul_right p (by omega)
            _ = p^(r-1)*p - p := by rw [Nat.sub_mul, one_mul]
            _ = p^r - p := by rw [hpp]
        have hge : p ≤ p^r := Nat.le_self_pow (by omega) p
        omega
      · intro hdvd
        have : p ∣ x.1 := by
          have hd2 : p ∣ x.2 * p := Dvd.intro_left _ rfl
          have := (Nat.dvd_add_right hd2).mp (by rwa [Nat.add_comm] at hdvd)
          exact this
        have := Nat.le_of_dvd (by omega) this
        omega
    · intro a ha
      rw [Nat.mul_comm]; exact Nat.mod_add_div a p
    · intro x hx
      simp only [hT, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hx
      obtain ⟨⟨h1, h2⟩, h3⟩ := hx
      have hm : (x.1 + x.2 * p) % p = x.1 := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]
      have hd : (x.1 + x.2 * p) / p = x.2 := by
        rw [Nat.add_mul_div_right _ _ hppos, Nat.div_eq_of_lt h2, Nat.zero_add]
      ext <;> simp [hm, hd]
    · intro a ha
      have hh : (a % p) + (a / p) * p = a := by rw [Nat.mul_comm]; exact Nat.mod_add_div a p
      show h ((a:ℕ):ZMod p) = h (((a % p) + (a / p) * p : ℕ) : ZMod p)
      rw [hh]
  rw [hbij, Finset.sum_product]
  apply Finset.sum_eq_zero
  intro a ha
  have hcongr : ∀ c ∈ range (p^(r-1)), h (((a + c * p : ℕ)) : ZMod p) = h ((a : ℕ) : ZMod p) := by
    intro c hc
    congr 1
    push_cast
    rw [ZMod.natCast_self]; ring
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : ((p^(r-1) : ℕ) : ZMod p) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; exact dvd_pow_self p (by omega)
  rw [this, zero_mul]

-- IsUnit of (i : ZMod p) for i coprime to p
lemma iunit (p : ℕ) (hp : p.Prime) (i : ℕ) (hi : ¬ p ∣ i) : IsUnit ((i : ZMod p)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact (hp.coprime_iff_not_dvd.mpr hi).symm

theorem harm2 (p r : ℕ) (hp : p.Prime) (hr : 2 ≤ r) :
    (p:ℤ) ∣ S2 ((Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i)) (fun j => (j:ℤ)*((p:ℤ)^r-j)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  set U := (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i) with hU
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  set cb : ℕ → ZMod p := fun j => (j : ZMod p) * ((p : ZMod p)^r - (j : ZMod p)) with hcbdef
  have hcast : (((S2 U (fun j => (j:ℤ)*((p:ℤ)^r-j))) : ℤ) : ZMod p) = S2g U cb := by
    unfold S2 S2g
    push_cast
    rfl
  rw [hcast]
  -- c̄ j = -(j)^2
  have hcj : ∀ j, cb j = -((j : ZMod p))^2 := by
    intro j; rw [hcbdef]
    have : (p : ZMod p)^r = 0 := by rw [ZMod.natCast_self]; exact zero_pow (by omega)
    simp only; rw [this]; ring
  have hunit : ∀ i ∈ U, IsUnit (cb i) := by
    intro i hi
    simp only [hU, Finset.mem_filter] at hi
    rw [hcj i]; exact ((iunit p hp i hi.2).pow 2).neg
  rw [S2g_units p U cb hunit]
  -- ∑ (cb i)⁻¹ = 0 and ∑ ((cb i)⁻¹)^2 = 0
  have hT1 : (∑ i ∈ U, (cb i)⁻¹) = 0 := by
    have hrw : ∀ i ∈ U, (cb i)⁻¹ = (fun x : ZMod p => -(x⁻¹)^2) ((i:ZMod p)) := by
      intro i hi
      simp only [hU, Finset.mem_filter] at hi
      rw [hcj i, cinv_eq p ((i:ZMod p)) (iunit p hp i hi.2)]
    rw [Finset.sum_congr rfl hrw]
    exact res_count p r hp hr (fun x => -(x⁻¹)^2)
  have hT2 : (∑ i ∈ U, ((cb i)⁻¹)^2) = 0 := by
    have hrw : ∀ i ∈ U, ((cb i)⁻¹)^2 = (fun x : ZMod p => ((x⁻¹)^2)^2) ((i:ZMod p)) := by
      intro i hi
      simp only [hU, Finset.mem_filter] at hi
      rw [hcj i, cinv_eq p ((i:ZMod p)) (iunit p hp i hi.2)]
      ring
    rw [Finset.sum_congr rfl hrw]
    exact res_count p r hp hr (fun x => ((x⁻¹)^2)^2)
  rw [hT1, hT2]; ring



lemma assembly (p : ℕ) (hp : p.Prime) (k : ℕ)
    (D A2 A3 β2 β3 b2 b3 : ℤ) (vA vC : ℕ)
    (hI1 : D * β2 = A2 * b2)
    (hI2 : D * β3 = A3 * b3)
    (hR : (p:ℤ)^k ∣ A3^2 - 3*A2^2 + 2*D^2)
    (hvA : (p:ℤ)^vA ∣ A2 - D)
    (hvC : (p:ℤ)^vC ∣ 2*b3^2 - 9*b2)
    (h2vA : k ≤ 2*vA)
    (hsum : k ≤ vA + vC)
    (hD : ¬ (p:ℤ) ∣ D) :
    (p:ℤ)^k ∣ (β3^2 - 27*β2 - b3^2 + 27*b2) := by
  have hid : (β3^2 - 27*β2 - b3^2 + 27*b2) * D^2
      = b3^2 * (A3^2 - 3*A2^2 + 2*D^2)
        + 3*b3^2*(A2-D)^2
        + 3*D*(2*b3^2-9*b2)*(A2-D) := by
    linear_combination (β3*D + b3*A3) * hI2 - 27*D * hI1
  have hP1 : (p:ℤ)^k ∣ b3^2 * (A3^2 - 3*A2^2 + 2*D^2) := Dvd.dvd.mul_left hR _
  have hP2sq : (p:ℤ)^k ∣ (A2-D)^2 := by
    have h1 : (p:ℤ)^k ∣ (p:ℤ)^(2*vA) := pow_dvd_pow _ h2vA
    have h2 : (p:ℤ)^(2*vA) ∣ (A2-D)^2 := by
      rw [Nat.mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd hvA 2
    exact h1.trans h2
  have hP2 : (p:ℤ)^k ∣ 3*b3^2*(A2-D)^2 := by
    have := hP2sq.mul_left (3*b3^2)
    rwa [show (3*b3^2)*(A2-D)^2 = 3*b3^2*(A2-D)^2 from by ring] at this
  have hP3 : (p:ℤ)^k ∣ 3*D*(2*b3^2-9*b2)*(A2-D) := by
    have h1 : (p:ℤ)^(vC+vA) ∣ (2*b3^2-9*b2)*(A2-D) := by
      rw [pow_add]; exact mul_dvd_mul hvC hvA
    have h2 : (p:ℤ)^k ∣ (p:ℤ)^(vC+vA) := pow_dvd_pow _ (by omega)
    have h3 : (p:ℤ)^k ∣ (2*b3^2-9*b2)*(A2-D) := h2.trans h1
    rw [show 3*D*(2*b3^2-9*b2)*(A2-D) = (3*D)*((2*b3^2-9*b2)*(A2-D)) from by ring]
    exact Dvd.dvd.mul_left h3 _
  have hsum2 : (p:ℤ)^k ∣ (β3^2 - 27*β2 - b3^2 + 27*b2) * D^2 := by
    rw [hid]; exact dvd_add (dvd_add hP1 hP2) hP3
  have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have hc1 : IsCoprime (p:ℤ) D := hpp.coprime_iff_not_dvd.mpr hD
  have hc2 : IsCoprime ((p:ℤ)^k) D := hc1.pow_left
  have hcop : IsCoprime ((p:ℤ)^k) (D^2) := hc2.pow_right
  exact hcop.dvd_of_dvd_mul_right hsum2

theorem C1 (p r : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 2 ≤ r) :
    (p:ℤ)^(3*r+3) ∣ (∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), (2*(p:ℤ)^r + (j:ℤ)))^2
        - 3*(∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), ((p:ℤ)^r + (j:ℤ)))^2
        + 2*(∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), (j:ℤ))^2 := by
  set U := (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i) with hU
  have hD2 := pairD p r hp (by omega)
  have hA2 := pairA2 p r hp (by omega)
  have hA3 := pairA3 p r hp (by omega)
  rw [← hU] at hD2 hA2 hA3
  set t := (p:ℤ)^r with ht
  rw [hA3, hA2, hD2]
  set S1v := S1 U (fun j => (j:ℤ)*(t-(j:ℤ))) with hS1v
  set S2v := S2 U (fun j => (j:ℤ)*(t-(j:ℤ))) with hS2v
  have hM2 := prod_add_const_mod_cube U (fun j => (j:ℤ)*(t-(j:ℤ))) (2*t^2)
  have hM6 := prod_add_const_mod_cube U (fun j => (j:ℤ)*(t-(j:ℤ))) (6*t^2)
  rw [Int.modEq_iff_dvd] at hM2 hM6
  rw [← hS1v, ← hS2v] at hM2 hM6
  obtain ⟨k2, hk2⟩ := hM2
  obtain ⟨k6, hk6⟩ := hM6
  set Q0 := ∏ j ∈ U, ((j:ℤ)*(t-(j:ℤ))) with hQ0
  set Q2 := ∏ j ∈ U, ((j:ℤ)*(t-(j:ℤ)) + 2*t^2) with hQ2
  set Q6 := ∏ j ∈ U, ((j:ℤ)*(t-(j:ℤ)) + 6*t^2) with hQ6
  -- key equation
  have h2R : 2*(Q6 - 3*Q2 + 2*Q0) = 24*t^4*S2v + 24*t^6*(k2 - 9*k6) := by
    linear_combination 3*hk2 - hk6
  have hReq : Q6 - 3*Q2 + 2*Q0 = 12*t^4*S2v + 12*t^6*(k2 - 9*k6) := by linarith
  rw [hReq]
  -- divisibility
  have hS2dvd : (p:ℤ) ∣ S2v := harm2 p r hp hr
  obtain ⟨w, hw⟩ := hS2dvd
  have e4 : t^4 = (p:ℤ)^(4*r) := by rw [ht, ← pow_mul]; congr 1; ring
  have e6 : t^6 = (p:ℤ)^(6*r) := by rw [ht, ← pow_mul]; congr 1; ring
  apply dvd_add
  · -- p^{3r+3} | 12*t^4*S2v
    rw [hw, e4]
    have hle : 3*r+3 ≤ 4*r+1 := by omega
    have : (12:ℤ)*(p:ℤ)^(4*r)*((p:ℤ)*w) = (p:ℤ)^(4*r+1)*(12*w) := by
      rw [pow_succ]; ring
    rw [this]
    exact Dvd.dvd.mul_right (pow_dvd_pow _ hle) _
  · -- p^{3r+3} | 12*t^6*(k2-9k6)
    rw [e6]
    have hle : 3*r+3 ≤ 6*r := by omega
    exact ((pow_dvd_pow _ hle).mul_left 12).mul_right (k2 - 9*k6)

theorem three_sum_units_inv_sq (n : ℕ) [NeZero n] (h2 : IsUnit (2 : ZMod n)) :
    (3:ZMod n) * (∑ u : (ZMod n)ˣ, ((u : ZMod n))⁻¹^2) = 0 := by
  have hreindex : ∑ u : (ZMod n)ˣ, ((u : ZMod n))⁻¹^2 = ∑ u : (ZMod n)ˣ, ((u : ZMod n))^2 := by
    rw [← Equiv.sum_comp (Equiv.inv (ZMod n)ˣ) (fun u => ((u : ZMod n))^2)]
    apply Finset.sum_congr rfl; intro u _; simp only [Equiv.inv_apply]; rw [ZMod.inv_coe_unit]
  rw [hreindex]
  set S := ∑ u : (ZMod n)ˣ, ((u : ZMod n))^2 with hS
  set a := h2.unit with ha
  have hav : (↑a : ZMod n) = 2 := h2.unit_spec
  have h1 : S = ∑ u : (ZMod n)ˣ, ((↑(a*u) : ZMod n))^2 :=
    (Equiv.sum_comp (Equiv.mulLeft a) (fun u => ((u : ZMod n))^2)).symm
  have h2' : ∑ u : (ZMod n)ˣ, ((↑(a*u) : ZMod n))^2 = 4 * S := by
    rw [hS, Finset.mul_sum]; refine Finset.sum_congr rfl (fun u _ => ?_); rw [Units.val_mul, hav]; ring
  linear_combination -(h1.trans h2')

lemma two_unit3 (p r : ℕ) (hp : p.Prime) (hodd : p ≠ 2) [NeZero (p^r)] :
    IsUnit (2 : ZMod (p^r)) := by
  have : ((2:ℕ) : ZMod (p^r)) = (2 : ZMod (p^r)) := by push_cast; ring
  rw [← this, ZMod.isUnit_iff_coprime]
  refine Nat.Coprime.pow_right r ((hp.coprime_iff_not_dvd.mpr ?_).symm)
  intro h; have := Nat.le_of_dvd (by norm_num) h
  have := hp.two_le; omega

theorem harm1_p3 (p r : ℕ) (hp : p.Prime) (hpe : p = 3) (hr : 1 ≤ r) :
    (p:ℤ)^(r-1) ∣ ∑ i ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i),
      ∏ j ∈ ((Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i)).erase i, ((j:ℤ)*((p:ℤ)^r-j)) := by
  haveI : NeZero (p^r) := ⟨by positivity⟩
  have hodd : p ≠ 2 := by omega
  set U := (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i) with hU
  set E1 := ∑ i ∈ U, ∏ j ∈ U.erase i, ((j:ℤ)*((p:ℤ)^r-j)) with hE1
  -- show p^r | 3 * E1
  have hp3dvd : (p:ℤ)^r ∣ 3 * E1 := by
    have hcast : ((p:ℤ)^r) = (((p^r : ℕ)) : ℤ) := by push_cast; ring
    nth_rewrite 1 [hcast]
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hE1]
    push_cast
    set c : ℕ → ZMod (p^r) := fun j => (j : ZMod (p^r)) * ((p : ZMod (p^r))^r - (j : ZMod (p^r))) with hc
    have hcj : ∀ j, c j = -((j : ZMod (p^r)))^2 := by
      intro j; rw [hc]
      have : (p : ZMod (p^r))^r = 0 := by rw [← Nat.cast_pow]; exact ZMod.natCast_self _
      rw [this]; ring
    have hcunit : ∀ i ∈ U, IsUnit (c i) := by
      intro i hi; rw [hcj]; exact ((jbar_unit p r hp hr i hi).pow 2).neg
    set P := ∏ j ∈ U, c j with hP
    have hsplit : (∑ i ∈ U, ∏ j ∈ U.erase i, c j) = P * ∑ i ∈ U, (c i)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have he : (∏ j ∈ U.erase i, c j) * c i = P := Finset.prod_erase_mul U c hi
      have hui : c i * (c i)⁻¹ = 1 := ZMod.mul_inv_of_unit _ (hcunit i hi)
      calc ∏ j ∈ U.erase i, c j = (∏ j ∈ U.erase i, c j) * (c i * (c i)⁻¹) := by rw [hui, mul_one]
        _ = ((∏ j ∈ U.erase i, c j) * c i) * (c i)⁻¹ := by ring
        _ = P * (c i)⁻¹ := by rw [he]
    have h3sum : (3 : ZMod (p^r)) * (∑ i ∈ U, (c i)⁻¹) = 0 := by
      have hrw : ∀ i ∈ U, (c i)⁻¹ = -((i : ZMod (p^r))⁻¹^2) := by
        intro i hi
        have hu : IsUnit ((i:ZMod (p^r))) := jbar_unit p r hp hr i hi
        rw [hcj i]
        set x := (i : ZMod (p^r))
        have hii : x * x⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu
        have hunit : IsUnit (-x^2) := (hu.pow 2).neg
        have hmul : (-x^2) * (-(x⁻¹)^2) = 1 := by
          have h1 : (-x^2) * (-(x⁻¹)^2) = (x * x⁻¹)^2 := by ring
          rw [h1, hii, one_pow]
        have hinv : (-x^2) * (-x^2)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hunit
        calc (-x^2)⁻¹ = (-x^2)⁻¹ * 1 := by rw [mul_one]
          _ = (-x^2)⁻¹ * ((-x^2) * (-(x⁻¹)^2)) := by rw [hmul]
          _ = ((-x^2)⁻¹ * (-x^2)) * (-(x⁻¹)^2) := by ring
          _ = ((-x^2) * (-x^2)⁻¹) * (-(x⁻¹)^2) := by rw [mul_comm ((-x^2)⁻¹)]
          _ = 1 * (-(x⁻¹)^2) := by rw [hinv]
          _ = -(x⁻¹^2) := by rw [one_mul]
      rw [Finset.sum_congr rfl hrw, Finset.sum_neg_distrib]
      have hbr := bridge p r hp hr (fun x => x⁻¹^2)
      rw [← Ufilter_eq p r hp hr, ← hU] at hbr
      rw [mul_neg, ← hbr]
      rw [three_sum_units_inv_sq (p^r) (two_unit3 p r hp hodd), neg_zero]
    -- 3 * (∑∑) = 0
    have hfin : (3 : ZMod (p^r)) * (∑ i ∈ U, ∏ j ∈ U.erase i,
        ((j:ZMod (p^r)) * ((p:ZMod (p^r))^r - (j:ZMod (p^r))))) = 0 := by
      have : (∑ i ∈ U, ∏ j ∈ U.erase i, ((j:ZMod (p^r)) * ((p:ZMod (p^r))^r - (j:ZMod (p^r)))))
          = ∑ i ∈ U, ∏ j ∈ U.erase i, c j := rfl
      rw [this, hsplit]
      calc (3 : ZMod (p^r)) * (P * ∑ i ∈ U, (c i)⁻¹)
          = P * ((3 : ZMod (p^r)) * (∑ i ∈ U, (c i)⁻¹)) := by ring
        _ = P * 0 := by rw [h3sum]
        _ = 0 := by ring
    -- relate to goal
    exact hfin
  -- p^r | 3*E1 implies p^(r-1) | E1
  obtain ⟨k, hk⟩ := hp3dvd
  refine ⟨k, ?_⟩
  have hp3' : (p:ℤ) = 3 := by rw [hpe]; norm_num
  have hpr : (p:ℤ)^r = (p:ℤ) * (p:ℤ)^(r-1) := by
    rw [mul_comm, ← pow_succ]; congr 1; omega
  have h1 : (3:ℤ) * E1 = (3:ℤ) * ((p:ℤ)^(r-1) * k) := by
    rw [hk, hpr, hp3']; ring
  exact mul_left_cancel₀ (by norm_num : (3:ℤ) ≠ 0) h1

theorem valgen_core (p r m e f : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 1 ≤ r)
    (hbound : e ≤ 2*r + f)
    (hE : (p:ℤ)^e ∣ ∑ i ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i),
      ∏ j ∈ ((Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i)).erase i, ((j:ℤ)*((p:ℤ)^r-j)))
    (hf : (p:ℤ)^f ∣ ((m:ℤ)^2+(m:ℤ))) :
    (p:ℤ)^(2*r+e+f) ∣ (∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), ((m:ℤ)*(p:ℤ)^r + j))
                 - (∏ j ∈ (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i), (j:ℤ)) := by
  set U := (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i) with hU
  set Bm := ∏ j ∈ U, ((m:ℤ)*(p:ℤ)^r + j) with hBm
  set D := ∏ j ∈ U, (j:ℤ) with hD
  set E1 := ∑ i ∈ U, ∏ j ∈ U.erase i, ((j:ℤ)*((p:ℤ)^r-j)) with hE1
  have hsq : (p:ℤ)^(2*r+e+f) ∣ Bm^2 - D^2 := by
    have hpair : Bm^2 = ∏ j ∈ U, ((j:ℤ) * ((p:ℤ)^r - j) + ((m:ℤ)^2+(m:ℤ))*((p:ℤ)^r)^2) := pairAm p r m hp hr
    have hpairD : D^2 = ∏ j ∈ U, ((j:ℤ) * ((p:ℤ)^r - j)) := pairD p r hp hr
    set a := ((m:ℤ)^2+(m:ℤ))*((p:ℤ)^r)^2 with ha
    have ht := prod_add_const_mod_sq U (fun j => (j:ℤ)*((p:ℤ)^r-j)) a
    rw [Int.modEq_iff_dvd] at ht
    have hdiff : Bm^2 - D^2 = (∏ j ∈ U, ((j:ℤ)*((p:ℤ)^r-j) + a)) - (∏ j ∈ U, ((j:ℤ)*((p:ℤ)^r-j))) := by
      rw [hpair, hpairD]
    obtain ⟨kE, hkE⟩ := hE
    obtain ⟨uf, huf⟩ := hf
    have haE1 : (p:ℤ)^(2*r+e+f) ∣ a * E1 := by
      rw [ha, hkE, huf]
      refine ⟨uf*kE, ?_⟩
      rw [pow_add, pow_add]
      rw [show (p:ℤ)^(2*r) = ((p:ℤ)^r)^2 from by rw [← pow_mul]; congr 1; ring]
      ring
    have ha2 : (p:ℤ)^(2*r+e+f) ∣ a^2 := by
      have h1 : (p:ℤ)^(2*r+e+f) ∣ (p:ℤ)^(2*f+4*r) := pow_dvd_pow _ (by omega)
      have h2 : (p:ℤ)^(2*f+4*r) ∣ a^2 := by
        rw [ha]
        refine ⟨uf^2, ?_⟩
        rw [huf, pow_add]
        rw [show (p:ℤ)^(4*r) = ((p:ℤ)^r)^4 from by rw [← pow_mul]; congr 1; ring]
        rw [show (p:ℤ)^(2*f) = ((p:ℤ)^f)^2 from by rw [← pow_mul]; congr 1; ring]
        ring
      exact h1.trans h2
    have hcomb : Bm^2 - D^2 = a * E1 - ((∏ j ∈ U, ((j:ℤ)*((p:ℤ)^r-j)) + a * E1) - (∏ j ∈ U, ((j:ℤ)*((p:ℤ)^r-j) + a))) := by
      rw [hdiff]; ring
    rw [hcomb]
    exact dvd_sub haE1 (dvd_trans ha2 ht)
  have hcop : IsCoprime ((p:ℤ)^(2*r+e+f)) (Bm + D) := by
    have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
    have h1 : IsCoprime (p:ℤ) (Bm + D) := hpp.coprime_iff_not_dvd.mpr (not_dvd_Bm_add_D p r m hp hp3 hr)
    exact h1.pow_left
  have hfact : Bm^2 - D^2 = (Bm - D) * (Bm + D) := by ring
  rw [hfact] at hsq
  exact hcop.dvd_of_dvd_mul_right hsq

/- ===== ratio_gen and helpers ===== -/

theorem split_prod (p N' : ℕ) (hp : 0 < p) (f : ℕ → ℕ) :
    ∏ i ∈ Ico 1 (p*N'+1), f i
    = (∏ i ∈ (Ico 1 (p*N'+1)).filter (fun i => ¬ p ∣ i), f i)
      * (∏ k ∈ Ico 1 (N'+1), f (p*k)) := by
  rw [← Finset.prod_filter_mul_prod_filter_not (Ico 1 (p*N'+1)) (fun i => p ∣ i) f, mul_comm]
  congr 1
  have himg : (Ico 1 (p*N'+1)).filter (fun i => p ∣ i) = (Ico 1 (N'+1)).image (fun k => p*k) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image]
    constructor
    · rintro ⟨⟨hi1, hi2⟩, k, rfl⟩
      refine ⟨k, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos k with h | h
        · subst h; simp at hi1
        · exact h
      · have : p * k ≤ p * N' := by omega
        have := Nat.le_of_mul_le_mul_left this hp; omega
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ⟨k, rfl⟩⟩
      · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
      · have : p * k ≤ p * N' := Nat.mul_le_mul_left p (by omega)
        omega
  rw [himg, Finset.prod_image]
  intro x _ y _ h; exact Nat.eq_of_mul_eq_mul_left hp h

theorem prod_consec (M N : ℕ) :
    ∏ i ∈ Ico 1 (N+1), (M + i) = N.factorial * (M+N).choose N := by
  have h1 : ∏ i ∈ Ico 1 (N+1), (M + i) = ∏ j ∈ range N, (M + 1 + j) := by
    rw [Finset.prod_Ico_eq_prod_range]; simp only [Nat.add_sub_cancel]
    apply Finset.prod_congr rfl; intro j _; ring
  rw [h1, ← Nat.ascFactorial_eq_prod_range, Nat.ascFactorial_eq_factorial_mul_choose]

theorem ratio_gen (p M' N' : ℕ) (hp : 0 < p) :
    (∏ i ∈ (Ico 1 (p*N'+1)).filter (fun i => ¬ p ∣ i), i) * ((p*M' + p*N').choose (p*N'))
    = (∏ i ∈ (Ico 1 (p*N'+1)).filter (fun i => ¬ p ∣ i), (p*M' + i)) * ((M' + N').choose N') := by
  set U := (Ico 1 (p*N'+1)).filter (fun i => ¬ p ∣ i) with hU
  have hII : (p*N').factorial = (∏ i ∈ U, i) * (p^N' * N'.factorial) := by
    have h := split_prod p N' hp (fun i => i)
    rw [Finset.prod_Ico_id_eq_factorial] at h
    rw [h]; congr 1
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_Ico_id_eq_factorial, Nat.card_Ico,
        Nat.add_sub_cancel]
  have hI : (p*N').factorial * ((p*M' + p*N').choose (p*N'))
      = (∏ i ∈ U, (p*M' + i)) * (p^N' * (N'.factorial * ((M'+N').choose N'))) := by
    have hpc := prod_consec (p*M') (p*N')
    rw [show p*M' + p*N' = p*M' + p*N' from rfl] at hpc ⊢
    rw [← hpc]
    have h := split_prod p N' hp (fun i => p*M' + i)
    rw [h]
    have hrw : ∏ k ∈ Ico 1 (N'+1), (p*M' + p*k) = p^N' * (N'.factorial * ((M'+N').choose N')) := by
      have h2 : ∏ k ∈ Ico 1 (N'+1), (p*M' + p*k) = ∏ k ∈ Ico 1 (N'+1), (p*(M'+k)) := by
        apply Finset.prod_congr rfl; intro k _; ring
      rw [h2, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico, Nat.add_sub_cancel,
          ← prod_consec M' N']
    rw [hrw]
  rw [hII] at hI
  have hpos : 0 < p^N' * N'.factorial := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc (∏ i ∈ U, i) * ((p*M' + p*N').choose (p*N')) * (p^N' * N'.factorial)
      = (∏ i ∈ U, i) * (p^N' * N'.factorial) * ((p*M' + p*N').choose (p*N')) := by ring
    _ = (∏ i ∈ U, (p*M' + i)) * (p^N' * (N'.factorial * ((M'+N').choose N'))) := hI
    _ = (∏ i ∈ U, (p*M' + i)) * ((M'+N').choose N') * (p^N' * N'.factorial) := by ring

/- ===== CCC binomial supercongruence lemmas ===== -/
lemma ratio_int (p j m : ℕ) (hp : p.Prime) (hj : 1 ≤ j) :
    (∏ i ∈ (Ico 1 (p^j+1)).filter (fun i => ¬ p ∣ i), (i:ℤ))
        * ((((m+1)*p^j).choose (p^j) : ℕ):ℤ)
    = (∏ i ∈ (Ico 1 (p^j+1)).filter (fun i => ¬ p ∣ i), ((m:ℤ)*(p:ℤ)^j + i))
        * ((((m+1)*p^(j-1)).choose (p^(j-1)) : ℕ):ℤ) := by
  have hpj : p * p^(j-1) = p^j := by rw [← _root_.pow_succ']; congr 1; omega
  have hraw := ratio_gen p (m*p^(j-1)) (p^(j-1)) hp.pos
  -- rewrite indices
  have e1 : p * (m * p^(j-1)) = m * p^j := by rw [← hpj]; ring
  have e2 : p * (m*p^(j-1)) + p^j = (m+1)*p^j := by rw [e1]; ring
  have e3 : m*p^(j-1) + p^(j-1) = (m+1)*p^(j-1) := by ring
  rw [hpj, e2, e3] at hraw
  -- cast to ℤ
  have := congrArg (fun n : ℕ => (n:ℤ)) hraw
  push_cast at this ⊢
  -- now match products
  rw [this]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have : ((p:ℤ)) * ((m:ℤ) * (p:ℤ)^(j-1)) = (m:ℤ)*(p:ℤ)^j := by
    rw [show (p:ℤ)^j = (p:ℤ)*(p:ℤ)^(j-1) from by rw [← _root_.pow_succ']; congr 1; omega]; ring
  rw [this]

lemma ccc_step (p j m e f : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hj : 1 ≤ j)
    (hbound : e ≤ 2*j + f)
    (hE : (p:ℤ)^e ∣ ∑ i ∈ (Ico 1 (p^j+1)).filter (fun i => ¬ p ∣ i),
      ∏ k ∈ ((Ico 1 (p^j+1)).filter (fun i => ¬ p ∣ i)).erase i, ((k:ℤ)*((p:ℤ)^j-k)))
    (hf : (p:ℤ)^f ∣ ((m:ℤ)^2+(m:ℤ))) :
    (p:ℤ)^(2*j+e+f) ∣ ((((m+1)*p^j).choose (p^j) : ℕ):ℤ)
                     - ((((m+1)*p^(j-1)).choose (p^(j-1)) : ℕ):ℤ) := by
  set U := (Ico 1 (p^j+1)).filter (fun i => ¬ p ∣ i) with hU
  set D := ∏ i ∈ U, (i:ℤ) with hD
  set Am := ∏ i ∈ U, ((m:ℤ)*(p:ℤ)^j + i) with hAm
  set Bj := ((((m+1)*p^j).choose (p^j) : ℕ):ℤ) with hBj
  set Bj1 := ((((m+1)*p^(j-1)).choose (p^(j-1)) : ℕ):ℤ) with hBj1
  have hr := ratio_int p j m hp hj
  rw [← hU, ← hD, ← hAm, ← hBj, ← hBj1] at hr
  have hvg := valgen_core p j m e f hp hp3 hj hbound hE hf
  rw [← hU, ← hD, ← hAm] at hvg
  -- D*(Bj - Bj1) = (Am - D)*Bj1
  have key : D * (Bj - Bj1) = (Am - D) * Bj1 := by
    have : D * Bj = Am * Bj1 := hr
    ring_nf
    linear_combination this
  have hdvd : (p:ℤ)^(2*j+e+f) ∣ D * (Bj - Bj1) := by
    rw [key]; exact hvg.mul_right _
  -- coprimality with D
  have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have hc1 : IsCoprime (p:ℤ) D := hpp.coprime_iff_not_dvd.mpr (not_dvd_D p j hp hj)
  have hcop : IsCoprime ((p:ℤ)^(2*j+e+f)) D := hc1.pow_left
  exact hcop.dvd_of_dvd_mul_left hdvd

lemma ccc_chain (p m w : ℕ) (hp : p.Prime)
    (step : ∀ j, 1 ≤ j → (p:ℤ)^w ∣ ((((m+1)*p^j).choose (p^j) : ℕ):ℤ)
                     - ((((m+1)*p^(j-1)).choose (p^(j-1)) : ℕ):ℤ)) :
    ∀ j, (p:ℤ)^w ∣ ((((m+1)*p^j).choose (p^j) : ℕ):ℤ) - ((m:ℤ)+1) := by
  intro j
  induction j with
  | zero =>
    simp only [pow_zero, mul_one, Nat.choose_one_right]
    have h0 : (((m+1 : ℕ)):ℤ) - ((m:ℤ)+1) = 0 := by push_cast; ring
    rw [h0]; exact dvd_zero _
  | succ n ih =>
    have hs := step (n+1) (by omega)
    have hn : (n+1) - 1 = n := by omega
    rw [hn] at hs
    have : ((((m+1)*p^(n+1)).choose (p^(n+1)) : ℕ):ℤ) - ((m:ℤ)+1)
        = (((((m+1)*p^(n+1)).choose (p^(n+1)) : ℕ):ℤ) - ((((m+1)*p^n).choose (p^n) : ℕ):ℤ))
          + (((((m+1)*p^n).choose (p^n) : ℕ):ℤ) - ((m:ℤ)+1)) := by ring
    rw [this]
    exact dvd_add hs ih

-- p ≥ 5 : C(2 p^L, p^L) ≡ 2 mod p^3
lemma b2_p5 (p L : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p:ℤ)^3 ∣ ((((2)*p^L).choose (p^L):ℕ):ℤ) - 2 := by
  have hstep : ∀ j, 1 ≤ j → (p:ℤ)^3 ∣ ((((1+1)*p^j).choose (p^j):ℕ):ℤ)
                     - ((((1+1)*p^(j-1)).choose (p^(j-1)):ℕ):ℤ) := by
    intro j hj
    have hc := ccc_step p j 1 j 0 hp (by omega) hj (by omega) (harm1 p j hp hp5 hj) (by norm_num)
    have : (p:ℤ)^3 ∣ (p:ℤ)^(2*j+j+0) := pow_dvd_pow _ (by omega)
    exact this.trans hc
  have := ccc_chain p 1 3 hp hstep L
  simpa using this

-- p ≥ 5 : C(3 p^L, p^L) ≡ 3 mod p^3
lemma b3_p5 (p L : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p:ℤ)^3 ∣ ((((3)*p^L).choose (p^L):ℕ):ℤ) - 3 := by
  have hstep : ∀ j, 1 ≤ j → (p:ℤ)^3 ∣ ((((2+1)*p^j).choose (p^j):ℕ):ℤ)
                     - ((((2+1)*p^(j-1)).choose (p^(j-1)):ℕ):ℤ) := by
    intro j hj
    have hc := ccc_step p j 2 j 0 hp (by omega) hj (by omega) (harm1 p j hp hp5 hj) (by norm_num)
    have : (p:ℤ)^3 ∣ (p:ℤ)^(2*j+j+0) := pow_dvd_pow _ (by omega)
    exact this.trans hc
  have := ccc_chain p 2 3 hp hstep L
  simpa using this

-- p = 3 : C(2 p^L, p^L) ≡ 2 mod p^2
lemma b2_p3 (p L : ℕ) (hp : p.Prime) (hpe : p = 3) :
    (p:ℤ)^2 ∣ ((((2)*p^L).choose (p^L):ℕ):ℤ) - 2 := by
  have hstep : ∀ j, 1 ≤ j → (p:ℤ)^2 ∣ ((((1+1)*p^j).choose (p^j):ℕ):ℤ)
                     - ((((1+1)*p^(j-1)).choose (p^(j-1)):ℕ):ℤ) := by
    intro j hj
    have hc := ccc_step p j 1 (j-1) 0 hp (by omega) hj (by omega) (harm1_p3 p j hp hpe hj) (by norm_num)
    have : (p:ℤ)^2 ∣ (p:ℤ)^(2*j+(j-1)+0) := pow_dvd_pow _ (by omega)
    exact this.trans hc
  have := ccc_chain p 1 2 hp hstep L
  simpa using this

-- p = 3 : C(3 p^L, p^L) ≡ 3 mod p^3
lemma b3_p3 (p L : ℕ) (hp : p.Prime) (hpe : p = 3) :
    (p:ℤ)^3 ∣ ((((3)*p^L).choose (p^L):ℕ):ℤ) - 3 := by
  have hstep : ∀ j, 1 ≤ j → (p:ℤ)^3 ∣ ((((2+1)*p^j).choose (p^j):ℕ):ℤ)
                     - ((((2+1)*p^(j-1)).choose (p^(j-1)):ℕ):ℤ) := by
    intro j hj
    have hf : (p:ℤ)^1 ∣ ((2:ℤ)^2+(2:ℤ)) := by rw [hpe]; norm_num
    have hc := ccc_step p j 2 (j-1) 1 hp (by omega) hj (by omega) (harm1_p3 p j hp hpe hj) (by exact_mod_cast hf)
    have : (p:ℤ)^3 ∣ (p:ℤ)^(2*j+(j-1)+1) := pow_dvd_pow _ (by omega)
    exact this.trans hc
  have := ccc_chain p 2 3 hp hstep L
  simpa using this

lemma comb5 (P b2 b3 : ℤ) (hb3 : P ∣ b3 - 3) (hb2 : P ∣ b2 - 2) :
    P ∣ 2*b3^2 - 9*b2 := by
  have h : 2*b3^2 - 9*b2 = 2*(b3-3)*(b3+3) - 9*(b2-2) := by ring
  rw [h]
  exact dvd_sub ((hb3.mul_left 2).mul_right _) (hb2.mul_left 9)

lemma comb3 (b2 b3 : ℤ) (hb3 : (27:ℤ) ∣ b3 - 3) (hb2 : (9:ℤ) ∣ b2 - 2) :
    (81:ℤ) ∣ 2*b3^2 - 9*b2 := by
  obtain ⟨a, ha⟩ := hb3
  obtain ⟨d, hd⟩ := hb2
  have hb3v : b3 = 27*a + 3 := by linarith
  have hb2v : b2 = 9*d + 2 := by linarith
  refine ⟨18*a^2 + 4*a - d, ?_⟩
  rw [hb3v, hb2v]; ring

/--
A357569: $a(n) = \binom{3n}{n}^2 - 27 \binom{2n}{n}$.
-/
def a (n : ℕ) : ℤ :=
  (Int.ofNat ((3 * n).choose n)) ^ 2 - (27 : ℤ) * Int.ofNat ((2 * n).choose n)

/-- Conjecture 1: a(p^r) \equiv a(p^(r-1)) ( mod p^(3*r+3) ) for r >= 2 and all primes p >= 3. -/
theorem oeis_357569_conjecture_0 (p r : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (hr : r ≥ 2) :
  a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] :=
by
  have hr1 : 1 ≤ r := by omega
  set U := (Ico 1 (p^r+1)).filter (fun i => ¬ p ∣ i) with hU
  set D := ∏ i ∈ U, (i:ℤ) with hD
  set A2 := ∏ i ∈ U, ((p:ℤ)^r + (i:ℤ)) with hA2
  set A3 := ∏ i ∈ U, (2*(p:ℤ)^r + (i:ℤ)) with hA3
  set β2 := (((2*p^r).choose (p^r):ℕ):ℤ) with hβ2
  set β3 := (((3*p^r).choose (p^r):ℕ):ℤ) with hβ3
  set b2 := (((2*p^(r-1)).choose (p^(r-1)):ℕ):ℤ) with hb2
  set b3 := (((3*p^(r-1)).choose (p^(r-1)):ℕ):ℤ) with hb3
  -- I1
  have hI1 : D * β2 = A2 * b2 := by
    have h := ratio_int p r 1 hp hr1
    rw [← hU, ← hD] at h
    have e2 : (∏ i ∈ U, (((1:ℕ):ℤ)*(p:ℤ)^r + (i:ℤ))) = A2 := by
      rw [hA2]; apply Finset.prod_congr rfl; intro i _; push_cast; ring
    rw [e2] at h
    exact h
  -- I2
  have hI2 : D * β3 = A3 * b3 := by
    have h := ratio_int p r 2 hp hr1
    rw [← hU, ← hD] at h
    have e3 : (∏ i ∈ U, (((2:ℕ):ℤ)*(p:ℤ)^r + (i:ℤ))) = A3 := by
      rw [hA3]; apply Finset.prod_congr rfl; intro i _; push_cast; ring
    rw [e3] at h
    exact h
  -- R
  have hR : (p:ℤ)^(3*r+3) ∣ A3^2 - 3*A2^2 + 2*D^2 := by
    have := C1 p r hp hp3 hr
    rw [← hU, ← hD, ← hA2, ← hA3] at this
    exact this
  -- hD
  have hDne : ¬ (p:ℤ) ∣ D := by rw [hD]; exact not_dvd_D p r hp hr1
  -- case split
  by_cases hpe : p = 3
  · -- p = 3 case
    -- vA = 3r-1, vC = 4
    have hvA : (p:ℤ)^(3*r-1) ∣ A2 - D := by
      have hvg := valgen_core p r 1 (r-1) 0 hp hp3 hr1 (by omega) (harm1_p3 p r hp hpe hr1) (by norm_num)
      rw [← hU, ← hD] at hvg
      have e2 : (∏ i ∈ U, (((1:ℕ):ℤ)*(p:ℤ)^r + (i:ℤ))) = A2 := by
        rw [hA2]; apply Finset.prod_congr rfl; intro i _; push_cast; ring
      rw [e2] at hvg
      have hexp : 2*r+(r-1)+0 = 3*r-1 := by omega
      rwa [hexp] at hvg
    have hvC : (p:ℤ)^4 ∣ 2*b3^2 - 9*b2 := by
      have h27 : ((27:ℤ)) = (p:ℤ)^3 := by rw [hpe]; norm_num
      have h9 : ((9:ℤ)) = (p:ℤ)^2 := by rw [hpe]; norm_num
      have h81 : ((81:ℤ)) = (p:ℤ)^4 := by rw [hpe]; norm_num
      have hb3d : (27:ℤ) ∣ b3 - 3 := by rw [h27]; exact b3_p3 p (r-1) hp hpe
      have hb2d : (9:ℤ) ∣ b2 - 2 := by rw [h9]; exact b2_p3 p (r-1) hp hpe
      have hcc := comb3 b2 b3 hb3d hb2d
      rw [h81] at hcc; exact hcc
    have hk2vA : 3*r+3 ≤ 2*(3*r-1) := by omega
    have hksum : 3*r+3 ≤ (3*r-1) + 4 := by omega
    have hΔ := assembly p hp (3*r+3) D A2 A3 β2 β3 b2 b3 (3*r-1) 4 hI1 hI2 hR hvA hvC hk2vA hksum hDne
    -- convert to ModEq
    rw [Int.modEq_iff_dvd]
    show (p:ℤ)^(3*r+3) ∣ a (p^(r-1)) - a (p^r)
    have ha : a (p^(r-1)) - a (p^r) = -(β3^2 - 27*β2 - b3^2 + 27*b2) := by
      simp only [a, hβ2, hβ3, hb2, hb3, Int.ofNat_eq_natCast]; ring
    rw [ha]; exact (dvd_neg).mpr hΔ
  · -- p ≥ 5 case
    have hp5 : 5 ≤ p := by
      have h4 : p ≠ 4 := by rintro rfl; exact absurd hp (by norm_num)
      omega
    have hvA : (p:ℤ)^(3*r) ∣ A2 - D := by
      have hvg := valgen_core p r 1 r 0 hp hp3 hr1 (by omega) (harm1 p r hp hp5 hr1) (by norm_num)
      rw [← hU, ← hD] at hvg
      have e2 : (∏ i ∈ U, (((1:ℕ):ℤ)*(p:ℤ)^r + (i:ℤ))) = A2 := by
        rw [hA2]; apply Finset.prod_congr rfl; intro i _; push_cast; ring
      rw [e2] at hvg
      have hexp : 2*r+r+0 = 3*r := by omega
      rwa [hexp] at hvg
    have hvC : (p:ℤ)^3 ∣ 2*b3^2 - 9*b2 := by
      exact comb5 _ b2 b3 (b3_p5 p (r-1) hp hp5) (b2_p5 p (r-1) hp hp5)
    have hk2vA : 3*r+3 ≤ 2*(3*r) := by omega
    have hksum : 3*r+3 ≤ (3*r) + 3 := by omega
    have hΔ := assembly p hp (3*r+3) D A2 A3 β2 β3 b2 b3 (3*r) 3 hI1 hI2 hR hvA hvC hk2vA hksum hDne
    rw [Int.modEq_iff_dvd]
    show (p:ℤ)^(3*r+3) ∣ a (p^(r-1)) - a (p^r)
    have ha : a (p^(r-1)) - a (p^r) = -(β3^2 - 27*β2 - b3^2 + 27*b2) := by
      simp only [a, hβ2, hβ3, hb2, hb3, Int.ofNat_eq_natCast]; ring
    rw [ha]; exact (dvd_neg).mpr hΔ
