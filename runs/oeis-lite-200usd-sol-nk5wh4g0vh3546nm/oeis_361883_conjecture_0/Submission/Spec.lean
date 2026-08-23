import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
The sequence $a(n)$ defined by
$$a(n) = \frac{1}{n} \sum_{k = 0}^n (n+2k) \binom{n+k-1}{k}^3$$
for $n \ge 1$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- Calculate the numerator sum S in ℕ
    -- We use binomial(n+k-1, n-1) which is equal to binomial(n+k-1, k)
    -- This makes the dependency on 'n - 1' explicit for the lower index.
    let S : ℕ := Finset.sum (range (n + 1)) fun k =>
      (n + 2 * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 3

    -- Division is exact since a(n) is an integer sequence.
    S / n

noncomputable section

local instance (n : ℕ) : Fintype (ZMod n)ˣ := Fintype.ofFinite _


private def term (n k : ℕ) : ℕ :=
  let C := Nat.choose (n + k - 1) k
  let D := Nat.choose (n + k - 1) (k - 1)
  C ^ 3 + 2 * C ^ 2 * D

private lemma choose_relation {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    k * Nat.choose (n + k - 1) k =
      n * Nat.choose (n + k - 1) (k - 1) := by
  have h := Nat.choose_succ_right_eq (n + k - 1) (k - 1)
  have hsub : n + k - 1 - (k - 1) = n := by omega
  have hks : k - 1 + 1 = k := by omega
  rw [hks, hsub] at h
  simpa [mul_comm] using h

private lemma summand_eq_term {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    ((n + 2 * k) * Nat.choose (n + k - 1) k ^ 3) / n = term n k := by
  let C := Nat.choose (n + k - 1) k
  let D := Nat.choose (n + k - 1) (k - 1)
  have hrel : k * C = n * D := choose_relation hn hk
  have hmul : (n + 2 * k) * C ^ 3 = n * (C ^ 3 + 2 * C ^ 2 * D) := by
    calc
      (n + 2 * k) * C ^ 3 = n * C ^ 3 + 2 * C ^ 2 * (k * C) := by ring
      _ = n * C ^ 3 + 2 * C ^ 2 * (n * D) := by rw [hrel]
      _ = n * (C ^ 3 + 2 * C ^ 2 * D) := by ring
  rw [hmul, Nat.mul_div_cancel_left _ hn]
  rfl

private lemma choose_reindex {n k : ℕ} (hn : 0 < n) :
    Nat.choose (n + k - 1) (n - 1) = Nat.choose (n + k - 1) k := by
  have h := Nat.choose_symm_add (a := n - 1) (b := k)
  have htop : n - 1 + k = n + k - 1 := by omega
  simpa [htop] using h

private lemma numerator_eq {n k : ℕ} (hn : 0 < n) :
    (n + 2 * k) * Nat.choose (n + k - 1) (n - 1) ^ 3 =
      n * (if k = 0 then 1 else term n k) := by
  rw [choose_reindex hn]
  by_cases hk : k = 0
  · subst k
    simp
  · simp only [hk, ↓reduceIte]
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    let C := Nat.choose (n + k - 1) k
    let D := Nat.choose (n + k - 1) (k - 1)
    have hrel : k * C = n * D := choose_relation hn hkpos
    change (n + 2 * k) * C ^ 3 = n * (C ^ 3 + 2 * C ^ 2 * D)
    calc
      _ = n * C ^ 3 + 2 * C ^ 2 * (k * C) := by ring
      _ = n * C ^ 3 + 2 * C ^ 2 * (n * D) := by rw [hrel]
      _ = _ := by ring

private lemma sum_division_free {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ range (n+1), (n + 2*k) * Nat.choose (n+k-1) (n-1) ^ 3) / n =
      ∑ k ∈ range (n+1), if k = 0 then 1 else term n k := by
  rw [Nat.sum_div (fun k hk => ⟨if k = 0 then 1 else term n k, numerator_eq hn⟩)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [numerator_eq hn, Nat.mul_div_cancel_left _ hn]


private lemma cast_choose_add_product (N k : ℕ) :
    (Nat.choose (N + k) k : ℚ) =
      ∏ h ∈ Finset.Icc 1 k, ((N + h : ℕ) : ℚ) / h := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ← ih]
      have hrec' : Nat.choose (N + (k + 1)) (k + 1) * (k + 1) =
          Nat.choose (N + k) k * (N + k + 1) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, mul_comm] using
          (Nat.add_one_mul_choose_eq (N + k) k).symm
      field_simp
      exact_mod_cast hrec'

private def unitRange (p k : ℕ) : Finset ℕ :=
  (Finset.Icc 1 k).filter fun h => ¬ p ∣ h

private lemma prod_multiples_ratio {p M j : ℕ} (hp : 0 < p) :
    (∏ h ∈ (Finset.Icc 1 (p * j)).filter (p ∣ ·),
        ((p * M + h : ℕ) : ℚ) / h) =
      ∏ q ∈ Finset.Icc 1 j, ((M + q : ℕ) : ℚ) / q := by
  apply Finset.prod_bij (fun h _ => h / p)
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_Icc] at hh
    simp only [Finset.mem_Icc]
    constructor
    · exact (Nat.one_le_div_iff hp).2 (Nat.le_of_dvd (by omega) hh.2)
    · exact Nat.div_le_of_le_mul (by simpa [mul_comm] using hh.1.2)
  · intro h₁ hh₁ h₂ hh₂ heq
    simp only [Finset.mem_filter] at hh₁ hh₂
    exact (Nat.mul_div_cancel' hh₁.2).symm.trans
      ((congrArg (p * ·) heq).trans (Nat.mul_div_cancel' hh₂.2))
  · intro q hq
    refine ⟨p * q, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · constructor
        · exact Nat.mul_pos hp (Finset.mem_Icc.1 hq).1
        · exact Nat.mul_le_mul_left p (Finset.mem_Icc.1 hq).2
      · exact dvd_mul_right p q
    · exact Nat.mul_div_cancel_left q hp
  · intro h hh
    simp only [Finset.mem_filter] at hh
    have heq : p * (h / p) = h := Nat.mul_div_cancel' hh.2
    have hqpos : 0 < h / p := (Nat.one_le_div_iff hp).2
      (Nat.le_of_dvd (Finset.mem_Icc.1 hh.1).1 hh.2)
    rw [← heq, Nat.mul_div_cancel_left _ hp]
    push_cast
    field_simp

private lemma cast_choose_scaled_product {p M j : ℕ} (hp : 0 < p) :
    (Nat.choose (p * M + p * j) (p * j) : ℚ) =
      Nat.choose (M + j) j *
        ∏ h ∈ unitRange p (p * j), ((p * M + h : ℕ) : ℚ) / h := by
  rw [cast_choose_add_product, cast_choose_add_product]
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (p * j)) (p ∣ ·)
    (fun h => ((p * M + h : ℕ) : ℚ) / h)]
  rw [prod_multiples_ratio hp]
  rfl


private def VGe (p e : ℕ) (x : ℚ) : Prop :=
  x = 0 ∨ (e : ℤ) ≤ padicValRat p x

private lemma VGe.zero (p e : ℕ) : VGe p e 0 := Or.inl rfl

private lemma VGe.of_val {p e : ℕ} {x : ℚ}
    (h : (e : ℤ) ≤ padicValRat p x) : VGe p e x := Or.inr h

private lemma VGe.add {p e : ℕ} [Fact p.Prime] {x y : ℚ}
    (hx : VGe p e x) (hy : VGe p e y) : VGe p e (x + y) := by
  by_cases hx0 : x = 0
  · subst x; simpa using hy
  by_cases hy0 : y = 0
  · subst y; simpa using hx
  have hxv : (e : ℤ) ≤ padicValRat p x := hx.resolve_left hx0
  have hyv : (e : ℤ) ≤ padicValRat p y := hy.resolve_left hy0
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  right
  exact le_trans (le_min hxv hyv) (padicValRat.min_le_padicValRat_add hxy)

private lemma VGe.neg {p e : ℕ} {x : ℚ} (hx : VGe p e x) : VGe p e (-x) := by
  rcases hx with rfl | hx
  · simp [VGe]
  exact Or.inr (by simpa [padicValRat.neg] using hx)

private lemma VGe.sub {p e : ℕ} [Fact p.Prime] {x y : ℚ}
    (hx : VGe p e x) (hy : VGe p e y) : VGe p e (x - y) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

private lemma VGe.mul {p e f : ℕ} [Fact p.Prime] {x y : ℚ}
    (hx : VGe p e x) (hy : VGe p f y) : VGe p (e + f) (x * y) := by
  by_cases hx0 : x = 0
  · subst x; simp [VGe]
  by_cases hy0 : y = 0
  · subst y; simp [VGe]
  have hxv : (e : ℤ) ≤ padicValRat p x := hx.resolve_left hx0
  have hyv : (f : ℤ) ≤ padicValRat p y := hy.resolve_left hy0
  right
  rw [padicValRat.mul hx0 hy0]
  exact_mod_cast add_le_add hxv hyv

private lemma VGe.mono {p e f : ℕ} {x : ℚ} (hef : e ≤ f)
    (hx : VGe p f x) : VGe p e x := by
  rcases hx with rfl | hx
  · exact VGe.zero _ _
  right
  exact_mod_cast (show (e : ℤ) ≤ f from mod_cast hef).trans hx

private lemma VGe.sum {p e : ℕ} [Fact p.Prime] {ι : Type*} {s : Finset ι} {f : ι → ℚ}
    (h : ∀ i ∈ s, VGe p e (f i)) : VGe p e (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [VGe]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self ..)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private lemma VGe.natCast_of_dvd {p e n : ℕ} (hp : p.Prime) (hd : p ^ e ∣ n) :
    VGe p e (n : ℚ) := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne n 0 with rfl | hn
  · exact VGe.zero _ _
  right
  rw [padicValRat.of_nat]
  exact_mod_cast (padicValNat_dvd_iff_le hn).1 hd

private lemma VGe.intCast_iff_dvd {p e : ℕ} (hp : p.Prime) {z : ℤ} :
    VGe p e (z : ℚ) ↔ (p : ℤ) ^ e ∣ z := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [VGe, padicValRat.of_int, Rat.intCast_eq_zero_iff]
  constructor
  · intro h
    rw [padicValInt_dvd_iff (p := p)]
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by exact_mod_cast h)
  · intro h
    rw [padicValInt_dvd_iff (p := p)] at h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by exact_mod_cast h)


private lemma VGe.div_nat_not_dvd {p e d : ℕ} [Fact p.Prime] {x : ℚ}
    (hd0 : d ≠ 0) (hd : ¬ p ∣ d) (hx : VGe p e x) : VGe p e (x / d) := by
  by_cases hx0 : x = 0
  · subst x; simp [VGe]
  right
  rw [padicValRat.div hx0 (by exact_mod_cast hd0), padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd hd]
  norm_num
  exact hx.resolve_left hx0

private lemma VGe.mul_nat {p e c : ℕ} [Fact p.Prime] {x : ℚ}
    (hx : VGe p e x) : VGe p e ((c : ℚ) * x) := by
  have hc : VGe p 0 (c : ℚ) := VGe.natCast_of_dvd (Fact.out) (by simp)
  simpa [mul_comm] using hx.mul hc

private lemma VGe.div_nat_padicVal {p e s d : ℕ} [Fact p.Prime] {x : ℚ}
    (hd : d ≠ 0) (hs : padicValNat p d = s) (hx : VGe p (e + s) x) :
    VGe p e (x / d) := by
  by_cases hx0 : x = 0
  · subst x; simp [VGe]
  right
  rw [padicValRat.div hx0 (by exact_mod_cast hd), padicValRat.of_nat, hs]
  have hv := hx.resolve_left hx0
  norm_num at hv ⊢
  omega


private lemma VGe.prod_one_add_sub_one {p e : ℕ} [Fact p.Prime]
    {ι : Type*} {s : Finset ι} {x : ι → ℚ}
    (hx : ∀ i ∈ s, VGe p e (x i)) :
    VGe p e ((∏ i ∈ s, (1 + x i)) - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [VGe]
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      have hxi := hx i (Finset.mem_insert_self ..)
      have hrest := ih (fun j hj => hx j (Finset.mem_insert_of_mem hj))
      have hid : (1 + x i) * (∏ j ∈ s, (1 + x j)) - 1 =
          x i + ((∏ j ∈ s, (1 + x j)) - 1) +
            x i * ((∏ j ∈ s, (1 + x j)) - 1) := by ring
      rw [hid]
      exact (hxi.add hrest).add ((hxi.mul hrest).mono (by omega))

private lemma coprime_prime_pow_iff_not_dvd {p E k : ℕ} (hp : p.Prime) (hE : 0 < E) :
    k.Coprime (p ^ E) ↔ ¬ p ∣ k := by
  rw [Nat.coprime_pow_right_iff hE, Nat.coprime_comm]
  exact hp.coprime_iff_not_dvd

private lemma sum_unitRange_cast_sq_eq_units {p E : ℕ} (hp : p.Prime) (hE : 0 < E) :
    let q := p ^ E
    (∑ k ∈ unitRange p (q - 1), ((k : ZMod q) ^ 2)) =
      ∑ u : (ZMod q)ˣ, ((u : ZMod q) ^ 2) := by
  let q := p ^ E
  have hqpos : 0 < q := pow_pos hp.pos _
  letI : NeZero q := ⟨hqpos.ne'⟩
  have hq2 : q ≠ 1 := by
    have : 2 ≤ p := hp.two_le
    have : 2 ≤ q := (Nat.le_pow hE).trans' this
    omega
  letI : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr hq2
  letI : Fintype (ZMod q)ˣ := Fintype.ofFinite _
  apply Finset.sum_bij (fun k hk =>
    ZMod.unitOfCoprime k ((coprime_prime_pow_iff_not_dvd hp hE).2
      (Finset.mem_filter.1 hk).2))
  · intro k hk
    exact Finset.mem_univ _
  · intro k₁ hk₁ k₂ hk₂ heq
    apply_fun fun u : (ZMod q)ˣ => (u : ZMod q) at heq
    have hk1lt : k₁ < q := by
      have := (Finset.mem_Icc.1 (Finset.mem_filter.1 hk₁).1).2
      omega
    have hk2lt : k₂ < q := by
      have := (Finset.mem_Icc.1 (Finset.mem_filter.1 hk₂).1).2
      omega
    have hm : k₁ ≡ k₂ [MOD q] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      simpa only [ZMod.coe_unitOfCoprime] using heq
    exact hm.eq_of_lt_of_lt hk1lt hk2lt
  · intro u hu
    let k := (u : ZMod q).val
    have hkcop : k.Coprime q := ZMod.val_coe_unit_coprime u
    have hknot : ¬ p ∣ k := (coprime_prime_pow_iff_not_dvd hp hE).1 hkcop
    have hkpos : 0 < k := by
      by_contra hk
      have hk0 : k = 0 := by omega
      have hu0 : (u : ZMod q) = 0 := (ZMod.val_eq_zero (u : ZMod q)).mp hk0
      exact Units.ne_zero u hu0
    have hklt : k < q := ZMod.val_lt _
    refine ⟨k, ?_, ?_⟩
    · simp only [unitRange, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hkpos, by omega⟩, hknot⟩
    · apply Units.ext
      simp [k]
  · intro k hk
    simp

private lemma sum_units_sq_eq_zero {p E : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hE : 0 < E) :
    ∑ u : (ZMod (p ^ E))ˣ, ((u : ZMod (p ^ E)) ^ 2) = 0 := by
  let q := p ^ E
  have hqpos : 0 < q := pow_pos hp.pos _
  have hq5 : 5 ≤ q := by
    calc 5 ≤ p := hp5
      _ ≤ p ^ E := Nat.le_pow hE
  letI : NeZero q := ⟨hqpos.ne'⟩
  have hq1 : q ≠ 1 := by omega
  letI : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr hq1
  letI : Fintype (ZMod q)ˣ := Fintype.ofFinite _
  have h2cop : Nat.Coprime 2 q := by
    rw [coprime_prime_pow_iff_not_dvd hp hE]
    intro h
    have hp2 := Nat.le_of_dvd (by norm_num : 0 < 2) h
    omega
  let v : (ZMod q)ˣ := ZMod.unitOfCoprime 2 h2cop
  let S : ZMod q := ∑ u : (ZMod q)ˣ, ((u : ZMod q) ^ 2)
  have hperm := Equiv.sum_comp (Equiv.mulLeft v)
    (fun u : (ZMod q)ˣ => ((u : ZMod q) ^ 2))
  have hfour' : 4 * S = S := by
    calc
      4 * S = ∑ u : (ZMod q)ˣ, (((v * u : (ZMod q)ˣ) : ZMod q) ^ 2) := by
        simp only [Units.val_mul]
        simp [v, S]
        simp only [mul_pow]
        norm_num
        rw [← Finset.mul_sum]
      _ = S := hperm
  have hfour : S = 4 * S := hfour'.symm
  have hthree : (3 : ZMod q) * S = 0 := by
    rw [show (3 : ZMod q) * S = 4 * S - S by ring, ← hfour]
    ring
  have h3unit : IsUnit (3 : ZMod q) := by
    apply (ZMod.isUnit_iff_coprime 3 q).2
    rw [coprime_prime_pow_iff_not_dvd hp hE]
    intro h
    have hp3 := Nat.le_of_dvd (by norm_num : 0 < 3) h
    omega
  exact h3unit.mul_left_cancel (by simpa using hthree)

private lemma pow_dvd_sum_unitRange_sq {p E : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hE : 0 < E) :
    p ^ E ∣ ∑ k ∈ unitRange p (p ^ E - 1), k ^ 2 := by
  rw [← ZMod.natCast_eq_zero_iff (∑ k ∈ unitRange p (p ^ E - 1), k ^ 2) (p ^ E)]
  push_cast
  rw [sum_unitRange_cast_sq_eq_units hp hE]
  exact sum_units_sq_eq_zero hp hp5 hE


private def invRep (q k : ℕ) : ℕ := ((k : ZMod q)⁻¹).val

private lemma sum_unitRange_cast_inv_sq_eq_units {p E : ℕ} (hp : p.Prime) (hE : 0 < E) :
    let q := p ^ E
    (∑ k ∈ unitRange p (q - 1), (((k : ZMod q)⁻¹) ^ 2)) =
      ∑ u : (ZMod q)ˣ, (((u : ZMod q)⁻¹) ^ 2) := by
  let q := p ^ E
  have hqpos : 0 < q := pow_pos hp.pos _
  letI : NeZero q := ⟨hqpos.ne'⟩
  have hq2 : q ≠ 1 := by
    have hp2 : 2 ≤ p := hp.two_le
    have hq2' : 2 ≤ q := hp2.trans (Nat.le_pow hE)
    omega
  letI : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr hq2
  apply Finset.sum_bij (fun k hk =>
    ZMod.unitOfCoprime k ((coprime_prime_pow_iff_not_dvd hp hE).2
      (Finset.mem_filter.1 hk).2))
  · simp
  · intro k₁ hk₁ k₂ hk₂ heq
    apply_fun fun u : (ZMod q)ˣ => (u : ZMod q) at heq
    have hk1lt : k₁ < q := by
      have := (Finset.mem_Icc.1 (Finset.mem_filter.1 hk₁).1).2; omega
    have hk2lt : k₂ < q := by
      have := (Finset.mem_Icc.1 (Finset.mem_filter.1 hk₂).1).2; omega
    apply Nat.ModEq.eq_of_lt_of_lt (m := q) _ hk1lt hk2lt
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa only [ZMod.coe_unitOfCoprime] using heq
  · intro u hu
    let k := (u : ZMod q).val
    have hkcop : k.Coprime q := ZMod.val_coe_unit_coprime u
    have hknot : ¬ p ∣ k := (coprime_prime_pow_iff_not_dvd hp hE).1 hkcop
    have hkpos : 0 < k := by
      by_contra hk
      have hk0 : k = 0 := by omega
      exact Units.ne_zero u ((ZMod.val_eq_zero (u : ZMod q)).mp hk0)
    refine ⟨k, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hkpos, by have := ZMod.val_lt (u : ZMod q); omega⟩, hknot⟩
    · apply Units.ext
      simp [k]
  · intro k hk
    simp

private lemma sum_units_inv_sq_eq_sum_sq {q : ℕ} :
    (∑ u : (ZMod q)ˣ, (((u : ZMod q)⁻¹) ^ 2)) =
      ∑ u : (ZMod q)ˣ, ((u : ZMod q) ^ 2) := by
  simpa using Equiv.sum_comp (Equiv.inv ((ZMod q)ˣ))
    (fun u : (ZMod q)ˣ => ((u : ZMod q) ^ 2))

private lemma pow_dvd_sum_invRep_sq {p E : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hE : 0 < E) :
    p ^ E ∣ ∑ k ∈ unitRange p (p ^ E - 1), (invRep (p ^ E) k) ^ 2 := by
  have hqpos : 0 < p ^ E := pow_pos hp.pos _
  letI : NeZero (p ^ E) := ⟨hqpos.ne'⟩
  rw [← ZMod.natCast_eq_zero_iff
    (∑ k ∈ unitRange p (p ^ E - 1), (invRep (p ^ E) k) ^ 2) (p ^ E)]
  push_cast
  simp only [invRep, ZMod.natCast_zmod_val]
  rw [sum_unitRange_cast_inv_sq_eq_units hp hE, sum_units_inv_sq_eq_sum_sq]
  exact sum_units_sq_eq_zero hp hp5 hE

private lemma reciprocal_sq_sub_invRep_sq {p E k : ℕ} (hp : p.Prime) (hE : 0 < E)
    (hk0 : k ≠ 0) (hk : ¬ p ∣ k) :
    VGe p E ((1 / (k : ℚ) ^ 2) - (invRep (p ^ E) k : ℚ) ^ 2) := by
  let q := p ^ E
  have hqpos : 0 < q := pow_pos hp.pos _
  have hq1 : q ≠ 1 := by
    have hp2 := hp.two_le
    have := hp2.trans (Nat.le_pow hE)
    omega
  letI : NeZero q := ⟨hqpos.ne'⟩
  letI : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr hq1
  letI : Fact p.Prime := ⟨hp⟩
  let u := invRep q k
  have hkcop : k.Coprime q := (coprime_prime_pow_iff_not_dvd hp hE).2 hk
  have hkunit : IsUnit (k : ZMod q) := (ZMod.isUnit_iff_coprime k q).2 hkcop
  have hkuZ : (k : ZMod q) * (u : ZMod q) = 1 := by
    dsimp [u, invRep]
    rw [ZMod.natCast_zmod_val]
    exact ZMod.mul_inv_of_unit _ hkunit
  have hmod : 1 ≡ (k * u) ^ 2 [MOD q] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [hkuZ]
    norm_num
  have hdvd : (q : ℤ) ∣ ((k * u : ℕ) ^ 2 : ℤ) - 1 := hmod.dvd
  have hnum : VGe p E ((((k * u : ℕ) ^ 2 : ℤ) - 1 : ℤ) : ℚ) := by
    apply (VGe.intCast_iff_dvd hp).2
    simpa [q] using hdvd
  have hid : (1 / (k : ℚ) ^ 2) - (u : ℚ) ^ 2 =
      -(((((k * u : ℕ) ^ 2 : ℤ) - 1 : ℤ) : ℚ) / (k : ℚ) / k) := by
    push_cast
    field_simp
    ring
  rw [show invRep (p ^ E) k = u from rfl, hid]
  exact (hnum.div_nat_not_dvd hk0 hk).div_nat_not_dvd hk0 hk |>.neg

private lemma full_unit_reciprocal_sq {p E : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hE : 0 < E) :
    VGe p E (∑ k ∈ unitRange p (p ^ E - 1), (1 / (k : ℚ) ^ 2)) := by
  letI : Fact p.Prime := ⟨hp⟩
  let q := p ^ E
  have hdiff : VGe p E (∑ k ∈ unitRange p (q - 1),
      ((1 / (k : ℚ) ^ 2) - (invRep q k : ℚ) ^ 2)) := by
    apply VGe.sum
    intro k hk
    have hmem := Finset.mem_filter.1 hk
    apply reciprocal_sq_sub_invRep_sq hp hE
    · exact (Nat.ne_of_gt (Finset.mem_Icc.1 hmem.1).1)
    · exact hmem.2
  have hinv : VGe p E (∑ k ∈ unitRange p (q - 1), (invRep q k : ℚ) ^ 2) := by
    have hcast : (∑ k ∈ unitRange p (q - 1), (invRep q k : ℚ) ^ 2) =
        ((∑ k ∈ unitRange p (q - 1), (invRep q k) ^ 2 : ℕ) : ℚ) := by
      norm_cast
    rw [hcast]
    apply VGe.natCast_of_dvd hp
    exact pow_dvd_sum_invRep_sq hp hp5 hE
  have hid : (∑ k ∈ unitRange p (q - 1), (1 / (k : ℚ) ^ 2)) =
      (∑ k ∈ unitRange p (q - 1),
        ((1 / (k : ℚ) ^ 2) - (invRep q k : ℚ) ^ 2)) +
      ∑ k ∈ unitRange p (q - 1), (invRep q k : ℚ) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hid]
  exact hdiff.add hinv




private lemma sum_unitRange_blocks_fn {p q b : ℕ} (hpq : p ∣ q) (hq : 0 < q)
    (f : ℕ → ℚ) :
    (∑ k ∈ unitRange p (q * b - 1), f k) =
      ∑ tr ∈ Finset.range b ×ˢ unitRange p (q - 1), f (tr.1 * q + tr.2) := by
  symm
  apply Finset.sum_bij (fun tr _ => tr.1 * q + tr.2)
  · intro tr htr
    simp only [Finset.mem_product, Finset.mem_range] at htr
    simp only [unitRange, Finset.mem_filter, Finset.mem_Icc]
    have hr := Finset.mem_filter.1 htr.2
    have hrI := Finset.mem_Icc.1 hr.1
    constructor
    · constructor
      · exact Nat.add_pos_right _ hrI.1
      · have ht : tr.1 + 1 ≤ b := by omega
        have hm := Nat.mul_le_mul_right q ht
        have hrlt : tr.2 < q := by omega
        have hlt : tr.1 * q + tr.2 < q * b := calc
          tr.1 * q + tr.2 < tr.1 * q + q := Nat.add_lt_add_left hrlt _
          _ = (tr.1 + 1) * q := by ring
          _ ≤ b * q := hm
          _ = q * b := by ring
        exact Nat.le_sub_one_of_lt hlt
    · intro hd
      apply hr.2
      have hfirst : p ∣ tr.1 * q := dvd_mul_of_dvd_right hpq _
      exact (Nat.dvd_add_iff_right hfirst).2 hd
  · intro x hx y hy heq
    simp only [Finset.mem_product, Finset.mem_range] at hx hy
    have hx2 := Finset.mem_filter.1 hx.2
    have hy2 := Finset.mem_filter.1 hy.2
    have hxr : x.2 < q := by
      have := (Finset.mem_Icc.1 hx2.1).2; omega
    have hyr : y.2 < q := by
      have := (Finset.mem_Icc.1 hy2.1).2; omega
    have hfst : x.1 = y.1 := by
      have hdiv := congrArg (fun z => z / q) heq
      simpa [mul_comm, Nat.mul_add_div hq, Nat.div_eq_of_lt hxr,
        Nat.div_eq_of_lt hyr] using hdiv
    have hsnd : x.2 = y.2 := by
      rw [hfst] at heq
      exact Nat.add_left_cancel heq
    exact Prod.ext hfst hsnd
  · intro k hk
    have hkm := Finset.mem_filter.1 hk
    have hkI := Finset.mem_Icc.1 hkm.1
    let t := k / q
    let r := k % q
    have hrlt : r < q := Nat.mod_lt _ hq
    have hklt : k < b * q := by
      have hh := hkI.2
      rw [mul_comm q b] at hh
      omega
    have htlt : t < b := (Nat.div_lt_iff_lt_mul hq).2 hklt
    have hrpos : 0 < r := by
      by_contra hr
      have hr0 : r = 0 := by omega
      have hqdk : q ∣ k := Nat.dvd_iff_mod_eq_zero.2 hr0
      exact hkm.2 (dvd_trans hpq hqdk)
    have hrnot : ¬ p ∣ r := by
      intro hpr
      have hpqt : p ∣ q * t := dvd_mul_of_dvd_left hpq _
      have hpkr : p ∣ q * t + r := dvd_add hpqt hpr
      apply hkm.2
      simpa [Nat.mul_comm, t, r, Nat.div_add_mod] using hpkr
    refine ⟨(t, r), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range, unitRange,
        Finset.mem_filter, Finset.mem_Icc]
      exact ⟨htlt, ⟨⟨hrpos, by omega⟩, hrnot⟩⟩
    · simp [t, r, Nat.div_add_mod, Nat.mul_comm]
  · intro tr htr
    norm_cast

private lemma sum_unitRange_blocks {p q b : ℕ} (hpq : p ∣ q) (hq : 0 < q) :
    (∑ k ∈ unitRange p (q * b - 1), (1 / (k : ℚ) ^ 2)) =
      ∑ tr ∈ Finset.range b ×ˢ unitRange p (q - 1),
        (1 / (tr.1 * q + tr.2 : ℚ) ^ 2) := by
  simpa only [Nat.cast_add, Nat.cast_mul] using
    sum_unitRange_blocks_fn hpq hq (fun k => 1 / (k : ℚ) ^ 2)


private lemma shifted_reciprocal_sq {p E t r : ℕ} (hp : p.Prime) (hE : 0 < E)
    (hr0 : r ≠ 0) (hr : ¬ p ∣ r) :
    VGe p E ((1 / (t * p ^ E + r : ℚ) ^ 2) - (1 / (r : ℚ) ^ 2)) := by
  letI : Fact p.Prime := ⟨hp⟩
  let k := t * p ^ E + r
  have hk0 : k ≠ 0 := by dsimp [k]; omega
  have hk : ¬ p ∣ k := by
    intro hpk
    apply hr
    have hpt : p ∣ t * p ^ E := by
      apply dvd_mul_of_dvd_right
      exact dvd_pow_self p (Nat.ne_of_gt hE)
    exact (Nat.dvd_add_iff_right hpt).2 hpk
  have hnumdvd : p ^ E ∣ k ^ 2 - r ^ 2 := by
    have hd : p ^ E ∣ k - r := by
      simp [k]
    exact dvd_trans hd (Nat.sub_dvd_pow_sub_pow k r 2)
  have hnum : VGe p E ((k ^ 2 - r ^ 2 : ℕ) : ℚ) := VGe.natCast_of_dvd hp hnumdvd
  have hid : (1 / (k : ℚ) ^ 2) - (1 / (r : ℚ) ^ 2) =
      -(((k ^ 2 - r ^ 2 : ℕ) : ℚ) / k / k / r / r) := by
    have hrle : r ≤ k := by dsimp [k]; omega
    rw [Nat.cast_sub (Nat.pow_le_pow_left hrle 2)]
    push_cast
    field_simp
    ring
  have hkcast : (k : ℚ) = (t : ℚ) * (p : ℚ) ^ E + r := by simp [k]
  rw [← hkcast, hid]
  have h1 := hnum.div_nat_not_dvd hk0 hk
  have h2 := h1.div_nat_not_dvd hk0 hk
  have h3 := h2.div_nat_not_dvd hr0 hr
  exact (h3.div_nat_not_dvd hr0 hr).neg

private lemma unit_reciprocal_sq_prefix {p s a : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (ha : p ^ s ∣ a) :
    VGe p (s + 1) (∑ k ∈ unitRange p (p * a - 1), (1 / (k : ℚ) ^ 2)) := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases ha with ⟨b, rfl⟩
  let q := p ^ (s + 1)
  have hqpos : 0 < q := pow_pos hp.pos _
  have hpq : p ∣ q := by
    dsimp [q]
    exact dvd_pow_self p (by omega)
  have hpa : p * (p ^ s * b) = q * b := by
    dsimp [q]
    rw [pow_succ]
    ring
  rw [hpa, sum_unitRange_blocks hpq hqpos]
  let T := Finset.range b ×ˢ unitRange p (q - 1)
  have hdiff : VGe p (s + 1) (∑ tr ∈ T,
      ((1 / (tr.1 * q + tr.2 : ℚ) ^ 2) - (1 / (tr.2 : ℚ) ^ 2))) := by
    apply VGe.sum
    intro tr htr
    have hr := Finset.mem_filter.1 (Finset.mem_product.1 htr).2
    simpa [q] using shifted_reciprocal_sq hp (by omega : 0 < s + 1)
      (t := tr.1) (r := tr.2) (Nat.ne_of_gt (Finset.mem_Icc.1 hr.1).1) hr.2
  have hbase : VGe p (s + 1) (∑ tr ∈ T, (1 / (tr.2 : ℚ) ^ 2)) := by
    have hfull := full_unit_reciprocal_sq hp hp5 (by omega : 0 < s + 1)
    have heq : (∑ tr ∈ T, (1 / (tr.2 : ℚ) ^ 2)) =
        (b : ℚ) * ∑ r ∈ unitRange p (q - 1), (1 / (r : ℚ) ^ 2) := by
      simp [T, Finset.sum_product, q]
    rw [heq]
    exact hfull.mul_nat
  have hid : (∑ tr ∈ T, (1 / (tr.1 * q + tr.2 : ℚ) ^ 2)) =
      (∑ tr ∈ T,
        ((1 / (tr.1 * q + tr.2 : ℚ) ^ 2) - (1 / (tr.2 : ℚ) ^ 2))) +
      ∑ tr ∈ T, (1 / (tr.2 : ℚ) ^ 2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro tr htr
    ring
  rw [hid]
  exact hdiff.add hbase


private lemma filter_multiples_upper {p a i : ℕ} (hp : 0 < p) (hi : 0 < i) (hip : i ≤ p) :
    (Finset.Icc 1 (p * a + i - 1)).filter (p ∣ ·) =
      (Finset.Icc 1 (p * a)).filter (p ∣ ·) := by
  ext h
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hh1, hh2⟩, ⟨c, rfl⟩⟩
    constructor
    · constructor
      · exact hh1
      · have heq : p * (a + 1) = p * a + p := by ring
        have hlt : p * c < p * (a + 1) := by
          rw [heq]
          omega
        exact Nat.mul_le_mul_left p (Nat.lt_succ_iff.1 ((Nat.mul_lt_mul_left hp).1 hlt))
    · exact dvd_mul_right p c
  · rintro ⟨⟨hh1, hh2⟩, hd⟩
    exact ⟨⟨hh1, hh2.trans (by omega)⟩, hd⟩

private lemma cast_choose_shift_product {p M a i : ℕ} (hp : 0 < p)
    (hi : 0 < i) (hip : i ≤ p) :
    (Nat.choose (p * M + (p * a + i) - 1) (p * a + i - 1) : ℚ) =
      Nat.choose (M + a) a *
        ∏ h ∈ unitRange p (p * a + i - 1), ((p * M + h : ℕ) : ℚ) / h := by
  have htop : p * M + (p * a + i) - 1 = p * M + (p * a + i - 1) := by omega
  rw [htop, cast_choose_add_product]
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (p * a + i - 1)) (p ∣ ·)
    (fun h => ((p * M + h : ℕ) : ℚ) / h)]
  rw [filter_multiples_upper hp hi hip, prod_multiples_ratio hp]
  rw [cast_choose_add_product]
  rfl

private lemma choose_shift_VGe {p r M a i : ℕ} (hp : p.Prime) (hr : 0 < r)
    (hM : p ^ (r - 1) ∣ M) (hi : 0 < i) (hip : i ≤ p) :
    VGe p r (((Nat.choose (p * M + (p * a + i) - 1) (p * a + i - 1) : ℕ) : ℚ) -
      Nat.choose (M + a) a) := by
  letI : Fact p.Prime := ⟨hp⟩
  let E := Nat.choose (M + a) a
  let P : ℚ := ∏ h ∈ unitRange p (p * a + i - 1),
    (1 + (p * M : ℚ) / h)
  have hpMr : p ^ r ∣ p * M := by
    rcases hM with ⟨c, rfl⟩
    use c
    have hpow : p ^ r = p * p ^ (r - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hpow]
    ring
  have hfac : VGe p r (P - 1) := by
    apply VGe.prod_one_add_sub_one
    intro h hh
    have hm := Finset.mem_filter.1 hh
    apply VGe.div_nat_not_dvd (Nat.ne_of_gt (Finset.mem_Icc.1 hm.1).1) hm.2
    simpa only [Nat.cast_mul] using VGe.natCast_of_dvd hp hpMr
  have hprod : (Nat.choose (p * M + (p * a + i) - 1) (p * a + i - 1) : ℚ) = E * P := by
    rw [cast_choose_shift_product hp.pos hi hip]
    dsimp [E, P]
    congr 1
    apply Finset.prod_congr rfl
    intro h hh
    have hm := Finset.mem_filter.1 hh
    have hh0 : (h : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.1 hm.1).1)
    push_cast
    field_simp [hh0]
    ring
  rw [hprod]
  have hid : (E : ℚ) * P - E = (E : ℚ) * (P - 1) := by ring
  rw [hid]
  exact hfac.mul_nat


private lemma sum_mul_succ_sub (N : ℕ) (A G : ℕ → ℚ) :
    (∑ a ∈ Finset.range (N + 1), A a * (G (a + 1) - G a)) =
      A N * G (N + 1) - A 0 * G 0 +
        ∑ a ∈ Finset.range N, (A a - A (a + 1)) * G (a + 1) := by
  induction N with
  | zero => simp; ring
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      rw [Finset.sum_range_succ]
      ring

private lemma weighted_choose_reciprocal_sum {p r M : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 0 < r) (hMpos : 0 < M) (hM : p ^ (r - 1) ∣ M) :
    let E := fun a => Nat.choose (M + a) a
    let G := fun a => ∑ k ∈ unitRange p (p * a - 1), (1 / (k : ℚ) ^ 2)
    VGe p r (∑ a ∈ Finset.range M, (E a : ℚ) ^ 3 * (G (a + 1) - G a)) := by
  dsimp only

  letI : Fact p.Prime := ⟨hp⟩
  let E := fun a => Nat.choose (M + a) a
  let G := fun a => ∑ k ∈ unitRange p (p * a - 1), (1 / (k : ℚ) ^ 2)
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hMpos.ne'
  rw [sum_mul_succ_sub N (fun a => (E a : ℚ) ^ 3) G]
  have hG0 : G 0 = 0 := by simp [G, unitRange]
  rw [hG0]
  norm_num
  have hboundG : VGe p r (G (N + 1)) := by
    have hh := unit_reciprocal_sq_prefix hp hp5 hM
    simpa [G, show r - 1 + 1 = r by omega] using hh
  have hbound : VGe p r ((E N : ℚ) ^ 3 * G (N + 1)) := by
    simpa [mul_comm] using hboundG.mul_nat (c := (E N) ^ 3)
  have hinterior : VGe p r (∑ a ∈ Finset.range N,
      (((E a : ℚ) ^ 3 - (E (a + 1) : ℚ) ^ 3) * G (a + 1))) := by
    apply VGe.sum
    intro a ha
    have haj : 0 < a + 1 := by omega
    let s := padicValNat p (a + 1)
    have hpowj : p ^ s ∣ a + 1 := pow_padicValNat_dvd
    have hGj : VGe p (s + 1) (G (a + 1)) := by
      simpa [G] using unit_reciprocal_sq_prefix hp hp5 hpowj
    have hGjdiv : VGe p 1 (G (a + 1) / (a + 1)) := by
      have hh := VGe.div_nat_padicVal (p := p) (e := 1) (s := s) (d := a + 1)
        haj.ne' (by rfl : padicValNat p (a + 1) = s) (by simpa [add_comm] using hGj)
      simpa [Nat.cast_add] using hh
    have hMcast : VGe p (r - 1) ((N + 1 : ℕ) : ℚ) :=
      VGe.natCast_of_dvd hp hM
    have hcore : VGe p r (((N + 1 : ℕ) : ℚ) * (G (a + 1) / (a + 1))) := by
      have hh := hMcast.mul hGjdiv
      simpa [show r - 1 + 1 = r by omega] using hh
    let e0 := E a
    let e1 := E (a + 1)
    have hrec : (a + 1) * e1 = (N + 1 + (a + 1)) * e0 := by
      dsimp [e0, e1, E]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, mul_comm] using
        (Nat.add_one_mul_choose_eq (N + 1 + a) a).symm
    have hdiff : (e1 : ℚ) - e0 = ((N + 1 : ℕ) : ℚ) * e0 / (a + 1) := by
      have hrecQ : ((a + 1 : ℕ) : ℚ) * e1 =
          ((N + 1 + (a + 1) : ℕ) : ℚ) * e0 := by exact_mod_cast hrec
      rw [eq_div_iff (by positivity)]
      push_cast at hrecQ ⊢
      linarith
    let Q : ℕ := e0 ^ 2 + e0 * e1 + e1 ^ 2
    have hid : (((E a : ℚ) ^ 3 - (E (a + 1) : ℚ) ^ 3) * G (a + 1)) =
        -(((e0 * Q : ℕ) : ℚ) * (((N + 1 : ℕ) : ℚ) * (G (a + 1) / (a + 1)))) := by
      change (((e0 : ℚ) ^ 3 - (e1 : ℚ) ^ 3) * G (a + 1)) =
        -(((e0 * Q : ℕ) : ℚ) * (((N + 1 : ℕ) : ℚ) * (G (a + 1) / (a + 1))))
      calc
        ((e0 : ℚ) ^ 3 - (e1 : ℚ) ^ 3) * G (a + 1) =
            -((e1 : ℚ) - e0) * (e0 ^ 2 + e0 * e1 + e1 ^ 2) * G (a + 1) := by ring
        _ = _ := by
          rw [hdiff]
          dsimp [Q]
          push_cast
          field_simp
    rw [hid]
    exact (hcore.mul_nat (c := e0 * Q)).neg
  exact hbound.add hinterior






private lemma unit_choose_reciprocal_sum {p r M : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 0 < r) (hMpos : 0 < M) (hM : p ^ (r - 1) ∣ M) :
    VGe p r (∑ k ∈ unitRange p (p * M - 1),
      (Nat.choose (p * M + k - 1) (k - 1) : ℚ) ^ 3 / (k : ℚ) ^ 2) := by
  letI : Fact p.Prime := ⟨hp⟩
  let T := Finset.range M ×ˢ unitRange p (p - 1)
  let D := fun k => Nat.choose (p * M + k - 1) (k - 1)
  let E := fun a => Nat.choose (M + a) a
  have hreindex : (∑ k ∈ unitRange p (p * M - 1),
      (D k : ℚ) ^ 3 / (k : ℚ) ^ 2) =
      ∑ ai ∈ T, (D (ai.1 * p + ai.2) : ℚ) ^ 3 /
        (ai.1 * p + ai.2 : ℚ) ^ 2 := by
    simpa [T] using sum_unitRange_blocks_fn (p := p) (q := p) (b := M)
      (dvd_refl p) hp.pos (fun k => (D k : ℚ) ^ 3 / (k : ℚ) ^ 2)
  rw [hreindex]
  have hdiff : VGe p r (∑ ai ∈ T,
      ((D (ai.1 * p + ai.2) : ℚ) ^ 3 - (E ai.1 : ℚ) ^ 3) /
        (ai.1 * p + ai.2 : ℚ) ^ 2) := by
    apply VGe.sum
    intro ai hai
    have hmem := Finset.mem_product.1 hai
    have hi := Finset.mem_filter.1 hmem.2
    have hiI := Finset.mem_Icc.1 hi.1
    let k := ai.1 * p + ai.2
    have hkpos : 0 < k := by dsimp [k]; omega
    have hknot : ¬ p ∣ k := by
      intro hpk
      apply hi.2
      have hfirst : p ∣ ai.1 * p := dvd_mul_left p ai.1
      exact (Nat.dvd_add_iff_right hfirst).2 hpk
    have hDE : VGe p r ((D k : ℚ) - E ai.1) := by
      dsimp [D, E, k]
      have hh := choose_shift_VGe hp hr hM (a := ai.1) (i := ai.2) hiI.1 (by omega)
      convert hh using 1 <;> ring
    let Q : ℕ := D k ^ 2 + D k * E ai.1 + E ai.1 ^ 2
    have hcub : VGe p r ((D k : ℚ) ^ 3 - (E ai.1 : ℚ) ^ 3) := by
      have hh := hDE.mul_nat (c := Q)
      have heq : ((D k : ℚ) ^ 3 - (E ai.1 : ℚ) ^ 3) =
          ((Q : ℕ) : ℚ) * ((D k : ℚ) - E ai.1) := by
        dsimp [Q]
        push_cast
        ring
      rw [heq]
      simpa [mul_comm] using hh
    have h1 := hcub.div_nat_not_dvd hkpos.ne' hknot
    have h2 := h1.div_nat_not_dvd hkpos.ne' hknot
    simpa [k, div_eq_mul_inv, pow_two, mul_assoc] using h2
  have hbase : VGe p r (∑ ai ∈ T,
      (E ai.1 : ℚ) ^ 3 / (ai.1 * p + ai.2 : ℚ) ^ 2) := by
    have hw := weighted_choose_reciprocal_sum hp hp5 hr hMpos hM
    have heq : (∑ ai ∈ T, (E ai.1 : ℚ) ^ 3 /
        (ai.1 * p + ai.2 : ℚ) ^ 2) =
        ∑ a ∈ Finset.range M, (E a : ℚ) ^ 3 *
          ((∑ k ∈ unitRange p (p * (a + 1) - 1), (1 / (k : ℚ) ^ 2)) -
           ∑ k ∈ unitRange p (p * a - 1), (1 / (k : ℚ) ^ 2)) := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro a ha
      have hb1 := sum_unitRange_blocks (p := p) (q := p) (b := a + 1) (dvd_refl p) hp.pos
      have hb0 := sum_unitRange_blocks (p := p) (q := p) (b := a) (dvd_refl p) hp.pos
      rw [hb1, hb0, Finset.sum_product, Finset.sum_product,
        Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_mul]
      ring_nf
      rw [Finset.mul_sum]
    rw [heq]
    simpa [E] using hw
  have hid : (∑ ai ∈ T, (D (ai.1 * p + ai.2) : ℚ) ^ 3 /
      (ai.1 * p + ai.2 : ℚ) ^ 2) =
      (∑ ai ∈ T, ((D (ai.1 * p + ai.2) : ℚ) ^ 3 - (E ai.1 : ℚ) ^ 3) /
        (ai.1 * p + ai.2 : ℚ) ^ 2) +
      ∑ ai ∈ T, (E ai.1 : ℚ) ^ 3 / (ai.1 * p + ai.2 : ℚ) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ai hai
    ring
  rw [hid]
  exact hdiff.add hbase

private lemma unit_term_sum {p r M : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 0 < r) (hMpos : 0 < M) (hM : p ^ (r - 1) ∣ M) :
    VGe p (3 * r) (∑ k ∈ unitRange p (p * M - 1), (term (p * M) k : ℚ)) := by
  letI : Fact p.Prime := ⟨hp⟩
  let X := p * M
  have hXpos : 0 < X := mul_pos hp.pos hMpos
  have hXdiv : p ^ r ∣ X := by
    rcases hM with ⟨c, rfl⟩
    use c
    dsimp [X]
    have hpow : p ^ r = p * p ^ (r - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hpow]
    ring
  have hX : VGe p r (X : ℚ) := VGe.natCast_of_dvd hp hXdiv
  let D := fun k => Nat.choose (X + k - 1) (k - 1)
  have hU : VGe p r (∑ k ∈ unitRange p (X - 1),
      (D k : ℚ) ^ 3 / (k : ℚ) ^ 2) := by
    simpa [X, D] using unit_choose_reciprocal_sum hp hp5 hr hMpos hM
  have hfirst : VGe p (3 * r) (∑ k ∈ unitRange p (X - 1),
      (X : ℚ) ^ 3 * (D k : ℚ) ^ 3 / (k : ℚ) ^ 3) := by
    apply VGe.sum
    intro k hk
    have hm := Finset.mem_filter.1 hk
    have hk0 := Nat.ne_of_gt (Finset.mem_Icc.1 hm.1).1
    have hx3 := (hX.mul hX).mul hX
    have hx3' : VGe p (3 * r) ((X : ℚ) ^ 3) := by
      convert hx3 using 1 <;> ring
    have hh := hx3'.mul_nat (c := (D k) ^ 3)
    have h1 := hh.div_nat_not_dvd hk0 hm.2
    have h2 := h1.div_nat_not_dvd hk0 hm.2
    have h3 := h2.div_nat_not_dvd hk0 hm.2
    convert h3 using 1 <;> simp [div_eq_mul_inv] <;> ring
  have hsecond : VGe p (3 * r) ((2 : ℚ) * (X : ℚ) ^ 2 *
      (∑ k ∈ unitRange p (X - 1), (D k : ℚ) ^ 3 / (k : ℚ) ^ 2)) := by
    have hx2 := hX.mul hX
    have hh := hx2.mul hU
    have hh' : VGe p (3 * r) ((X : ℚ) ^ 2 *
        (∑ k ∈ unitRange p (X - 1), (D k : ℚ) ^ 3 / (k : ℚ) ^ 2)) := by
      convert hh using 1 <;> ring
    simpa [mul_assoc] using hh'.mul_nat (c := 2)
  have hid : (∑ k ∈ unitRange p (X - 1), (term X k : ℚ)) =
      (∑ k ∈ unitRange p (X - 1), (X : ℚ) ^ 3 * (D k : ℚ) ^ 3 / (k : ℚ) ^ 3) +
      (2 : ℚ) * (X : ℚ) ^ 2 *
        (∑ k ∈ unitRange p (X - 1), (D k : ℚ) ^ 3 / (k : ℚ) ^ 2) := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hm := Finset.mem_filter.1 hk
    have hkpos := (Finset.mem_Icc.1 hm.1).1
    let C := Nat.choose (X + k - 1) k
    have hrel : k * C = X * D k := by
      dsimp [C, D]
      exact choose_relation hXpos hkpos
    have hrelQ : (k : ℚ) * C = X * D k := by exact_mod_cast hrel
    have hC : (C : ℚ) = (X : ℚ) * D k / k := by
      rw [eq_div_iff (by exact_mod_cast (Nat.ne_of_gt hkpos))]
      simpa [mul_comm] using hrelQ
    change (((C ^ 3 + 2 * C ^ 2 * D k : ℕ) : ℚ)) = _
    push_cast
    rw [hC]
    field_simp
  change VGe p (3 * r) (∑ k ∈ unitRange p (X - 1), (term X k : ℚ))
  rw [hid]
  exact hfirst.add hsecond


private lemma sum_reflect_unitRange {p L : ℕ} (hL : 0 < L) (hpL : p ∣ L) :
    (∑ k ∈ unitRange p (L - 1), (1 / (((L - k : ℕ) : ℚ)))) =
      ∑ k ∈ unitRange p (L - 1), (1 / (k : ℚ)) := by
  apply Finset.sum_bij (fun k _ => L - k)
  · intro k hk
    have hm := Finset.mem_filter.1 hk
    have hI := Finset.mem_Icc.1 hm.1
    change L - k ∈ (Finset.Icc 1 (L - 1)).filter (fun x => ¬ p ∣ x)
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩,
      fun hd => hm.2 ((Nat.dvd_sub_iff_right (by omega) hpL).1 hd)⟩
  · intro k₁ hk₁ k₂ hk₂ heq
    have h1 := Finset.mem_Icc.1 (Finset.mem_filter.1 hk₁).1
    have h2 := Finset.mem_Icc.1 (Finset.mem_filter.1 hk₂).1
    omega
  · intro k hk
    have hm := Finset.mem_filter.1 hk
    have hI := Finset.mem_Icc.1 hm.1
    refine ⟨L - k, ?_, ?_⟩
    · change L - k ∈ (Finset.Icc 1 (L - 1)).filter (fun x => ¬ p ∣ x)
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩,
        fun hd => hm.2 ((Nat.dvd_sub_iff_right (by omega) hpL).1 hd)⟩
    · omega
  · intro k hk
    rfl

private lemma unit_reciprocal_prefix {p s a : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hapos : 0 < a) (ha : p ^ s ∣ a) :
    VGe p (2 * (s + 1)) (∑ k ∈ unitRange p (p * a - 1), (1 / (k : ℚ))) := by
  letI : Fact p.Prime := ⟨hp⟩
  let L := p * a
  have hLdiv : p ^ (s + 1) ∣ L := by
    rcases ha with ⟨c, rfl⟩
    use c
    dsimp [L]
    rw [pow_succ']
    ring
  have hLpos : 0 < L := mul_pos hp.pos hapos
  have hL0 : L ≠ 0 := hLpos.ne'
  have hsq := unit_reciprocal_sq_prefix hp hp5 ha
  let H : ℚ := ∑ k ∈ unitRange p (L - 1), (1 / (k : ℚ))
  let K : ℚ := ∑ k ∈ unitRange p (L - 1),
    (1 / ((k : ℚ) * (((L - k : ℕ) : ℚ))))
  have hKplus : VGe p (s + 1) (K +
      ∑ k ∈ unitRange p (L - 1), (1 / (k : ℚ) ^ 2)) := by
    have hsum : VGe p (s + 1) (∑ k ∈ unitRange p (L - 1),
        ((1 / ((k : ℚ) * (((L - k : ℕ) : ℚ)))) + (1 / (k : ℚ) ^ 2))) := by
      apply VGe.sum
      intro k hk
      have hm := Finset.mem_filter.1 hk
      have hI := Finset.mem_Icc.1 hm.1
      have hk0 : k ≠ 0 := by omega
      have hsub0 : L - k ≠ 0 := by omega
      have hkn : ¬ p ∣ k := hm.2
      have hpL : p ∣ L := dvd_trans (dvd_pow_self p (by omega : s + 1 ≠ 0)) hLdiv
      have hsubn : ¬ p ∣ L - k := by
        intro hd
        exact hkn ((Nat.dvd_sub_iff_right (by omega) hpL).1 hd)
      have hLc : VGe p (s + 1) (L : ℚ) := VGe.natCast_of_dvd hp hLdiv
      have hid : (1 / ((k : ℚ) * (((L - k : ℕ) : ℚ)))) + (1 / (k : ℚ) ^ 2) =
          (L : ℚ) / k / k / ((L - k : ℕ) : ℚ) := by
        rw [Nat.cast_sub (by omega)]
        have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk0
        have hkLQ : (k : ℚ) < L := by exact_mod_cast (by omega : k < L)
        have hsQ : (L : ℚ) - k ≠ 0 := by linarith
        push_cast
        field_simp [hkQ, hsQ]
        ring
      rw [hid]
      have h1 := hLc.div_nat_not_dvd hk0 hkn
      have h2 := h1.div_nat_not_dvd hk0 hkn
      exact h2.div_nat_not_dvd hsub0 hsubn
    simpa [K, Finset.sum_add_distrib] using hsum
  have hK : VGe p (s + 1) K := by
    have hs : VGe p (s + 1) (∑ k ∈ unitRange p (L - 1), (1 / (k : ℚ) ^ 2)) := by
      simpa [L] using hsq
    have := hKplus.sub hs
    have heq : K + (∑ k ∈ unitRange p (L - 1), (1 / (k : ℚ) ^ 2)) -
        (∑ k ∈ unitRange p (L - 1), (1 / (k : ℚ) ^ 2)) = K := by ring
    rwa [heq] at this
  have hLK : VGe p (2 * (s + 1)) ((L : ℚ) * K) := by
    have hLc : VGe p (s + 1) (L : ℚ) := VGe.natCast_of_dvd hp hLdiv
    convert hLc.mul hK using 1 <;> ring
  have htwo : (2 : ℚ) * H = (L : ℚ) * K := by
    have hpL : p ∣ L := dvd_trans (dvd_pow_self p (by omega : s + 1 ≠ 0)) hLdiv
    have href := sum_reflect_unitRange (p := p) hLpos hpL
    dsimp [H, K]
    rw [Finset.mul_sum, Finset.mul_sum]
    calc
      (∑ k ∈ unitRange p (L - 1), 2 * (1 / (k : ℚ))) =
          ∑ k ∈ unitRange p (L - 1),
            ((1 / (k : ℚ)) + (1 / (((L - k : ℕ) : ℚ)))) := by
              rw [Finset.sum_add_distrib, href, ← two_mul, Finset.mul_sum]
      _ = ∑ k ∈ unitRange p (L - 1),
            (L : ℚ) * (1 / ((k : ℚ) * (((L - k : ℕ) : ℚ)))) := by
              apply Finset.sum_congr rfl
              intro k hk
              have hI := Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1
              have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
              have hkLQ : (k : ℚ) < L := by exact_mod_cast (by omega : k < L)
              have hsQ : (L : ℚ) - k ≠ 0 := by linarith
              rw [Nat.cast_sub (by omega)]
              push_cast
              field_simp [hkQ, hsQ]
              ring
  have h2unit : ¬ p ∣ 2 := by
    intro h
    have := Nat.le_of_dvd (by norm_num : 0 < 2) h
    omega
  have hres : VGe p (2 * (s + 1)) H := by
    have hh : VGe p (2 * (s + 1)) ((2 : ℚ) * H) := by rw [htwo]; exact hLK
    have hh' := hh.div_nat_not_dvd (by norm_num : (2 : ℕ) ≠ 0) h2unit
    simpa using hh'
  simpa [H, L] using hres



private lemma VGe.prod_approx_two {p e : ℕ} [Fact p.Prime]
    {ι : Type*} {s : Finset ι} {x : ι → ℚ} (h2unit : ¬ p ∣ 2)
    (hx : ∀ i ∈ s, VGe p e (x i)) :
    let P := ∏ i ∈ s, (1 + x i)
    let S₁ := ∑ i ∈ s, x i
    let S₂ := ∑ i ∈ s, (x i) ^ 2
    VGe p (2 * e) (P - 1 - S₁) ∧
      VGe p (3 * e) (P - 1 - S₁ - (S₁ ^ 2 - S₂) / 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [VGe]
  | @insert i s hi ih =>
      have hxi := hx i (Finset.mem_insert_self ..)
      have hxs : ∀ j ∈ s, VGe p e (x j) := fun j hj => hx j (Finset.mem_insert_of_mem hj)
      rcases ih hxs with ⟨hQ, hR⟩
      let P := ∏ j ∈ s, (1 + x j)
      let S₁ := ∑ j ∈ s, x j
      let S₂ := ∑ j ∈ s, (x j) ^ 2
      have hPm1 : VGe p e (P - 1) := VGe.prod_one_add_sub_one hxs
      have hQnew : VGe p (2 * e) ((1 + x i) * P - 1 - (x i + S₁)) := by
        have hid : (1 + x i) * P - 1 - (x i + S₁) =
            (P - 1 - S₁) + x i * (P - 1) := by ring
        rw [hid]
        have hm := hxi.mul hPm1
        exact hQ.add (by convert hm using 1 <;> omega)
      have hRnew : VGe p (3 * e) ((1 + x i) * P - 1 - (x i + S₁) -
          ((x i + S₁) ^ 2 - (x i ^ 2 + S₂)) / 2) := by
        have hid : (1 + x i) * P - 1 - (x i + S₁) -
              ((x i + S₁) ^ 2 - (x i ^ 2 + S₂)) / 2 =
            (P - 1 - S₁ - (S₁ ^ 2 - S₂) / 2) + x i * (P - 1 - S₁) := by
          ring
        rw [hid]
        have hm := hxi.mul hQ
        exact hR.add (by convert hm using 1 <;> omega)
      simpa [P, S₁, S₂, Finset.prod_insert hi, Finset.sum_insert hi] using
        And.intro hQnew hRnew


private lemma multiple_term_difference {p r M j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 0 < r) (hMpos : 0 < M) (hM : p ^ (r - 1) ∣ M) (hj : 0 < j) :
    VGe p (3 * r) ((term (p * M) (p * j) : ℚ) - term M j) := by
  letI : Fact p.Prime := ⟨hp⟩
  let X := p * M
  let v := padicValNat p j
  let S := unitRange p (p * j - 1)
  have hSfull : unitRange p (p * j) = S := by
    dsimp [S]
    ext h
    simp only [unitRange, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hh1, hh2⟩, hhn⟩
      refine ⟨⟨hh1, ?_⟩, hhn⟩
      by_contra hh
      have heq : h = p * j := by omega
      subst h
      exact hhn (dvd_mul_right p j)
    · rintro ⟨⟨hh1, hh2⟩, hhn⟩
      exact ⟨⟨hh1, by omega⟩, hhn⟩
  let R : ℚ := ∏ h ∈ S, (1 + (X : ℚ) / h)
  let H₁ : ℚ := ∑ h ∈ S, (1 / (h : ℚ))
  let H₂ : ℚ := ∑ h ∈ S, (1 / (h : ℚ) ^ 2)
  let S₁ : ℚ := ∑ h ∈ S, ((X : ℚ) / h)
  let S₂ : ℚ := ∑ h ∈ S, ((X : ℚ) / h) ^ 2
  have hXdiv : p ^ r ∣ X := by
    rcases hM with ⟨c, rfl⟩
    use c
    dsimp [X]
    have hpow : p ^ r = p * p ^ (r - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hpow]
    ring
  have hX : VGe p r (X : ℚ) := VGe.natCast_of_dvd hp hXdiv
  have hjpow : p ^ v ∣ j := pow_padicValNat_dvd
  have hH₁ : VGe p (2 * (v + 1)) H₁ := by
    simpa [H₁, S] using unit_reciprocal_prefix hp hp5 hj hjpow
  have hH₂ : VGe p (v + 1) H₂ := by
    simpa [H₂, S] using unit_reciprocal_sq_prefix hp hp5 hjpow
  have hS₁eq : S₁ = (X : ℚ) * H₁ := by
    dsimp [S₁, H₁]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  have hS₂eq : S₂ = (X : ℚ) ^ 2 * H₂ := by
    dsimp [S₂, H₂]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  have hS₁ : VGe p (r + 2 * (v + 1)) S₁ := by
    rw [hS₁eq]
    exact hX.mul hH₁
  have hS₂ : VGe p (2 * r + (v + 1)) S₂ := by
    rw [hS₂eq]
    have hx2 := hX.mul hX
    convert hx2.mul hH₂ using 1 <;> ring
  have h2unit : ¬ p ∣ 2 := by
    intro h
    have := Nat.le_of_dvd (by norm_num : 0 < 2) h
    omega
  have hfactor (h : ℕ) (hh : h ∈ S) : VGe p r ((X : ℚ) / h) := by
    have hm := Finset.mem_filter.1 hh
    exact hX.div_nat_not_dvd (Nat.ne_of_gt (Finset.mem_Icc.1 hm.1).1) hm.2
  have happ := VGe.prod_approx_two h2unit hfactor
  have hrem : VGe p (3 * r) (R - 1 - S₁ - (S₁ ^ 2 - S₂) / 2) := by
    simpa [R, S₁, S₂, S] using happ.2
  have hpair : VGe p (2 * r + (v + 1)) ((S₁ ^ 2 - S₂) / 2) := by
    have hs11 := hS₁.mul hS₁
    have hs11' : VGe p (2 * r + (v + 1)) (S₁ ^ 2) := by
      have hh := hs11.mono (by omega : 2 * r + (v + 1) ≤
        (r + 2 * (v + 1)) + (r + 2 * (v + 1)))
      simpa [pow_two] using hh
    have hd := hs11'.sub hS₂
    exact hd.div_nat_not_dvd (by norm_num : (2 : ℕ) ≠ 0) h2unit
  let C := Nat.choose (M + j - 1) j
  let D := Nat.choose (M + j - 1) (j - 1)
  have hterm0 : VGe p 0 (term M j : ℚ) :=
    VGe.natCast_of_dvd hp (by simp)
  have hterm : VGe p (2 * (r - 1 - v)) (term M j : ℚ) := by
    by_cases hv : v < r - 1
    · have hMcast : VGe p (r - 1) (M : ℚ) := VGe.natCast_of_dvd hp hM
      have hC : VGe p (r - 1 - v) (C : ℚ) := by
        have hrel : j * C = M * D := by
          dsimp [C, D]
          exact choose_relation hMpos hj
        have hrelQ : (j : ℚ) * C = M * D := by exact_mod_cast hrel
        have hmD : VGe p (r - 1) ((M : ℚ) * D) := by
          simpa [mul_comm] using hMcast.mul_nat (c := D)
        have hh := VGe.div_nat_padicVal (p := p) (e := r - 1 - v) (s := v) (d := j)
          hj.ne' (by rfl : padicValNat p j = v) (by
            simpa [show r - 1 - v + v = r - 1 by omega] using hmD)
        have heq : (C : ℚ) = (M : ℚ) * D / j := by
          rw [eq_div_iff (by exact_mod_cast hj.ne')]
          simpa [mul_comm] using hrelQ
        rwa [← heq] at hh
      have hc2 := hC.mul hC
      have hh := hc2.mul_nat (c := C + 2 * D)
      have heq : (term M j : ℚ) = (C : ℚ) ^ 2 * (C + 2 * D) := by
        dsimp [term, C, D]
        push_cast
        ring
      rw [heq]
      have hh' : VGe p (2 * (r - 1 - v))
          ((C : ℚ) ^ 2 * ((C : ℚ) + 2 * (D : ℚ))) := by
        convert hh using 1 <;> push_cast <;> ring
      exact hh'
    · have hz : r - 1 - v = 0 := by omega
      simpa [hz] using hterm0
  have hS₁term : VGe p (3 * r) (S₁ * (term M j : ℚ)) := by
    by_cases hv : v < r - 1
    · have hh := hS₁.mul hterm
      apply hh.mono
      omega
    · have hs : VGe p (3 * r) S₁ := hS₁.mono (by omega)
      simpa using hs.mul hterm0
  have hpairterm : VGe p (3 * r) (((S₁ ^ 2 - S₂) / 2) * (term M j : ℚ)) := by
    by_cases hv : v < r - 1
    · have hh := hpair.mul hterm
      apply hh.mono
      omega
    · have hs : VGe p (3 * r) ((S₁ ^ 2 - S₂) / 2) := hpair.mono (by omega)
      simpa using hs.mul hterm0
  have hremterm : VGe p (3 * r)
      ((R - 1 - S₁ - (S₁ ^ 2 - S₂) / 2) * (term M j : ℚ)) := by
    simpa using hrem.mul hterm0
  have hRm1term : VGe p (3 * r) ((R - 1) * (term M j : ℚ)) := by
    have hid : (R - 1) * (term M j : ℚ) =
        S₁ * term M j + ((S₁ ^ 2 - S₂) / 2) * term M j +
          (R - 1 - S₁ - (S₁ ^ 2 - S₂) / 2) * term M j := by ring
    rw [hid]
    exact (hS₁term.add hpairterm).add hremterm
  have hRm1 : VGe p r (R - 1) := by
    apply VGe.prod_one_add_sub_one
    exact hfactor
  have hR0 : VGe p 0 R := by
    have h1 : VGe p 0 (1 : ℚ) := VGe.natCast_of_dvd hp (by simp)
    have := h1.add (hRm1.mono (by omega))
    have heq : (1 : ℚ) + (R - 1) = R := by ring
    rwa [heq] at this
  have hpoly0 : VGe p 0 (R ^ 2 + R + 1) := by
    have hR2 := hR0.mul hR0
    have h1 : VGe p 0 (1 : ℚ) := VGe.natCast_of_dvd hp (by simp)
    convert (hR2.add hR0).add h1 using 1 <;> ring
  have hcubeTerm : VGe p (3 * r) ((R ^ 3 - 1) * (term M j : ℚ)) := by
    have hh := hRm1term.mul hpoly0
    have heq : (R ^ 3 - 1) * (term M j : ℚ) =
        ((R - 1) * term M j) * (R ^ 2 + R + 1) := by ring
    rwa [heq]
  have hscale : (term (p * M) (p * j) : ℚ) = R ^ 3 * term M j := by
    let T0 := Nat.choose (M + j) j
    let T1 := Nat.choose (p * M + p * j) (p * j)
    let C0 := Nat.choose (M + j - 1) j
    let D0 := Nat.choose (M + j - 1) (j - 1)
    let C1 := Nat.choose (p * M + p * j - 1) (p * j)
    let D1 := Nat.choose (p * M + p * j - 1) (p * j - 1)
    have hT : (T1 : ℚ) = T0 * R := by
      dsimp [T0, T1]
      rw [cast_choose_scaled_product hp.pos, hSfull]
      dsimp [R, S, X]
      congr 1
      apply Finset.prod_congr rfl
      intro h hh
      have hm := Finset.mem_filter.1 hh
      have hh0 : (h : ℚ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt (Finset.mem_Icc.1 hm.1).1
      push_cast
      field_simp [hh0]
      ring
    have hC0 : ((M + j : ℕ) : ℚ) * C0 = (M : ℚ) * T0 := by
      have hn := Nat.choose_mul_succ_eq (M + j - 1) j
      have ha : M + j - 1 + 1 = M + j := by omega
      rw [ha] at hn
      have hb : M + j - j = M := by omega
      rw [hb] at hn
      have hn' : (M + j) * C0 = M * T0 := by
        simpa [C0, T0, mul_comm] using hn
      exact_mod_cast hn'
    have hD0 : ((M + j : ℕ) : ℚ) * D0 = (j : ℚ) * T0 := by
      have hn := Nat.add_one_mul_choose_eq (M + j - 1) (j - 1)
      have ha : M + j - 1 + 1 = M + j := by omega
      have hb : j - 1 + 1 = j := by omega
      rw [ha, hb] at hn
      have hn' : (M + j) * D0 = j * T0 := by
        simpa [D0, T0, mul_comm] using hn
      exact_mod_cast hn'
    have hC1 : ((p * M + p * j : ℕ) : ℚ) * C1 = (p * M : ℚ) * T1 := by
      have hn := Nat.choose_mul_succ_eq (p * M + p * j - 1) (p * j)
      have ha : p * M + p * j - 1 + 1 = p * M + p * j := by
        have : 0 < p * M + p * j := by positivity
        omega
      rw [ha] at hn
      have hb : p * M + p * j - p * j = p * M := by omega
      rw [hb] at hn
      have hn' : (p * M + p * j) * C1 = (p * M) * T1 := by
        simpa [C1, T1, mul_comm] using hn
      exact_mod_cast hn'
    have hD1 : ((p * M + p * j : ℕ) : ℚ) * D1 = (p * j : ℚ) * T1 := by
      have hn := Nat.add_one_mul_choose_eq (p * M + p * j - 1) (p * j - 1)
      have ha : p * M + p * j - 1 + 1 = p * M + p * j := by
        have : 0 < p * M + p * j := by positivity
        omega
      have hb : p * j - 1 + 1 = p * j := by
        have : 0 < p * j := mul_pos hp.pos hj
        omega
      rw [ha, hb] at hn
      have hn' : (p * M + p * j) * D1 = (p * j) * T1 := by
        simpa [D1, T1, mul_comm] using hn
      exact_mod_cast hn'
    have hsum0 : (M + j : ℚ) ≠ 0 := by positivity
    have hsum1 : (p * M + p * j : ℚ) ≠ 0 := by positivity
    have hCR : (C1 : ℚ) = R * C0 := by
      apply (mul_left_cancel₀ hsum1)
      push_cast at hC1 hC0 ⊢
      rw [hC1, hT]
      calc
        (p * M : ℚ) * ((T0 : ℚ) * R) = (p : ℚ) * R * ((M : ℚ) * T0) := by ring
        _ = (p : ℚ) * R * (((M : ℚ) + j) * C0) := by rw [hC0]
        _ = ((p : ℚ) * M + p * j) * (R * C0) := by ring
    have hDR : (D1 : ℚ) = R * D0 := by
      apply (mul_left_cancel₀ hsum1)
      push_cast at hD1 hD0 ⊢
      rw [hD1, hT]
      calc
        (p * j : ℚ) * ((T0 : ℚ) * R) = (p : ℚ) * R * ((j : ℚ) * T0) := by ring
        _ = (p : ℚ) * R * (((M : ℚ) + j) * D0) := by rw [hD0]
        _ = ((p : ℚ) * M + p * j) * (R * D0) := by ring
    dsimp [term, C0, D0, C1, D1]
    push_cast
    rw [hCR, hDR]
    ring
  rw [hscale]
  have heq : R ^ 3 * (term M j : ℚ) - term M j =
      (R ^ 3 - 1) * term M j := by ring
  rw [heq]
  exact hcubeTerm


private def bterm (n k : ℕ) : ℕ := if k = 0 then 1 else term n k

private lemma range_bterm_eq {n : ℕ} :
    (∑ k ∈ range (n + 1), (bterm n k : ℚ)) =
      1 + ∑ k ∈ Finset.Icc 1 n, (term n k : ℚ) := by
  have hzero : 0 ∈ range (n + 1) := Finset.mem_range.2 (by omega)
  have herase : (range (n + 1)).erase 0 = Finset.Icc 1 n := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
    omega
  calc
    (∑ k ∈ range (n + 1), (bterm n k : ℚ)) =
        (∑ k ∈ (range (n + 1)).erase 0, (bterm n k : ℚ)) + bterm n 0 := by
          exact (Finset.sum_erase_add (range (n + 1)) (fun k => (bterm n k : ℚ)) hzero).symm
    _ = 1 + ∑ k ∈ Finset.Icc 1 n, (term n k : ℚ) := by
      rw [herase]
      simp only [bterm]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      have hkpos := (Finset.mem_Icc.1 hk).1
      have hk0 : k ≠ 0 := Nat.ne_of_gt hkpos
      simp [hk0]

private lemma unitRange_mul_endpoint {p M : ℕ} (hp : 0 < p) (hM : 0 < M) :
    unitRange p (p * M - 1) =
      (Finset.Icc 1 (p * M)).filter (fun k => ¬ p ∣ k) := by
  ext k
  simp only [unitRange, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hk1, hk2⟩, hkn⟩
    exact ⟨⟨hk1, by omega⟩, hkn⟩
  · rintro ⟨⟨hk1, hk2⟩, hkn⟩
    refine ⟨⟨hk1, ?_⟩, hkn⟩
    by_contra hh
    have heq : k = p * M := by omega
    subst k
    exact hkn (dvd_mul_right p M)

private lemma sum_multiples {p M : ℕ} (hp : 0 < p) {f : ℕ → ℚ} :
    (∑ k ∈ (Finset.Icc 1 (p * M)).filter (p ∣ ·), f k) =
      ∑ j ∈ Finset.Icc 1 M, f (p * j) := by
  apply Finset.sum_bij (fun k _ => k / p)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    simp only [Finset.mem_Icc]
    exact ⟨(Nat.one_le_div_iff hp).2 (Nat.le_of_dvd hk.1.1 hk.2),
      Nat.div_le_of_le_mul (by simpa [mul_comm] using hk.1.2)⟩
  · intro k₁ hk₁ k₂ hk₂ heq
    simp only [Finset.mem_filter] at hk₁ hk₂
    exact (Nat.mul_div_cancel' hk₁.2).symm.trans
      ((congrArg (p * ·) heq).trans (Nat.mul_div_cancel' hk₂.2))
  · intro j hj
    refine ⟨p * j, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.mul_pos hp (Finset.mem_Icc.1 hj).1,
        Nat.mul_le_mul_left p (Finset.mem_Icc.1 hj).2⟩, dvd_mul_right p j⟩
    · exact Nat.mul_div_cancel_left j hp
  · intro k hk
    simp only [Finset.mem_filter] at hk
    rw [Nat.mul_div_cancel' hk.2]

private lemma positive_term_partition {p M : ℕ} (hp : 0 < p) (hM : 0 < M) :
    (∑ k ∈ Finset.Icc 1 (p * M), (term (p * M) k : ℚ)) =
      (∑ k ∈ unitRange p (p * M - 1), (term (p * M) k : ℚ)) +
        ∑ j ∈ Finset.Icc 1 M, (term (p * M) (p * j) : ℚ) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (p * M))
    (p ∣ ·) (fun k => (term (p * M) k : ℚ))
  rw [sum_multiples hp] at hsplit
  rw [unitRange_mul_endpoint hp hM]
  rw [← hsplit]
  ring

private lemma one_step_VGe {p r M : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 0 < r) (hMpos : 0 < M) (hM : p ^ (r - 1) ∣ M) :
    VGe p (3 * r)
      ((∑ k ∈ range (p * M + 1), (bterm (p * M) k : ℚ)) -
        ∑ j ∈ range (M + 1), (bterm M j : ℚ)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hu := unit_term_sum hp hp5 hr hMpos hM
  have hm : VGe p (3 * r)
      (∑ j ∈ Finset.Icc 1 M,
        ((term (p * M) (p * j) : ℚ) - term M j)) := by
    apply VGe.sum
    intro j hj
    exact multiple_term_difference hp hp5 hr hMpos hM (Finset.mem_Icc.1 hj).1
  have hboth := hu.add hm
  rw [range_bterm_eq, range_bterm_eq, positive_term_partition hp.pos hMpos]
  convert hboth using 1
  rw [Finset.sum_sub_distrib]
  ring


private lemma one_step_modEq {p r M : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 0 < r) (hMpos : 0 < M) (hM : p ^ (r - 1) ∣ M) :
    (∑ k ∈ range (p * M + 1), bterm (p * M) k) ≡
      (∑ j ∈ range (M + 1), bterm M j) [MOD p ^ (3 * r)] := by
  let A : ℕ := ∑ k ∈ range (p * M + 1), bterm (p * M) k
  let B : ℕ := ∑ j ∈ range (M + 1), bterm M j
  have hv := one_step_VGe hp hp5 hr hMpos hM
  have hv' : VGe p (3 * r) ((((A : ℤ) - (B : ℤ) : ℤ) : ℚ)) := by
    convert hv using 1 <;> simp [A, B]
  have hd : (p : ℤ) ^ (3 * r) ∣ (A : ℤ) - (B : ℤ) :=
    (VGe.intCast_iff_dvd hp).1 hv'
  rw [Nat.modEq_iff_dvd]
  change ((p : ℤ) ^ (3 * r)) ∣ (B : ℤ) - (A : ℤ)
  have hdneg := dvd_neg.mpr hd
  convert hdneg using 1 <;> ring

private lemma a_eq_bsum {N : ℕ} (hN : 0 < N) :
    a N = ∑ k ∈ range (N + 1), bterm N k := by
  rw [a, if_neg hN.ne']
  simpa [bterm] using sum_division_free hN

/--
The central binomial coefficients $u(n) := \binom{2n}{n}$ satisfy the supercongruences
$u(n \cdot p^r) \equiv u(n \cdot p^{r-1}) \pmod{p^{3r}}$ for positive integers $n$ and $r$
and all primes $p \ge 5$. We conjecture that the present sequence $a(n)$ satisfies the same congruences.
-/
theorem oeis_361883_conjecture_0 {p n r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  let M := n * p ^ (r - 1)
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  have hMdiv : p ^ (r - 1) ∣ M := by
    dsimp [M]
    exact dvd_mul_left _ _
  have hs := one_step_modEq hp hp5 hr hMpos hMdiv
  have hpM : p * M = n * p ^ r := by
    dsimp [M]
    have hpow : p ^ r = p * p ^ (r - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hpow]
    ring
  rw [← a_eq_bsum (mul_pos hp.pos hMpos), ← a_eq_bsum hMpos, hpM] at hs
  exact hs
