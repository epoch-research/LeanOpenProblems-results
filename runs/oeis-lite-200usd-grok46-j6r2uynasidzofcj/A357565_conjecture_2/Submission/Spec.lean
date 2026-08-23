import FormalConjectures.Util.ProblemImports

set_option linter.style.moduleDocstring false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000

open Finset Nat PowerSeries
open scoped BigOperators ZMod

/-!
# A357565 Conjecture 2

We prove that for an odd prime `p` and `r ≥ 2`,
`a(p^r) ≡ a(p^{r-1}) (mod p^{3r+3})`, where
`a(n) = ∑_{k=0}^n (3 b_k^2 + 2 b_k^3)` and `b_k = C(n+k-1, k)`.
-/

def A357565 (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k =>
    let b := choose (n + k - 1) k
    3 * b ^ 2 + 2 * b ^ 3

def A357565_u (n m : ℕ) : ℕ :=
  (range (m * n + 1)).sum fun k =>
    (m + 2) * (choose (n + k - 1) k) ^ 2 + (2 * m) * (choose (n + k - 1) k) ^ 3

def A357565.term (n k : ℕ) : ℕ :=
  3 * choose (n + k - 1) k ^ 2 + 2 * choose (n + k - 1) k ^ 3

lemma A357565_eq_sum_term (n : ℕ) :
    A357565 n = ∑ k ∈ range (n + 1), A357565.term n k := rfl

lemma A357565.term_zero (n : ℕ) : A357565.term n 0 = 5 := by
  simp [A357565.term]

def rising (n k : ℕ) : ℕ := choose (n + k - 1) k

lemma rising_zero_right (n : ℕ) : rising n 0 = 1 := by simp [rising]

lemma rising_one_right (n : ℕ) (hn : 0 < n) : rising n 1 = n := by
  have : n + 1 - 1 = n := by omega
  simp [rising, this]

lemma choose_rising_succ (n k : ℕ) (hn : 0 < n) :
    choose (n + (k + 1) - 1) (k + 1) * (k + 1) = choose (n + k - 1) k * (n + k) := by
  have h : n + (k + 1) - 1 = n + k := by omega
  have h' : n + k - 1 + 1 = n + k := by omega
  rw [h, ← h']
  simpa [mul_comm] using (add_one_mul_choose_eq (n + k - 1) k).symm

lemma rising_succ (n k : ℕ) (hn : 0 < n) :
    rising n (k + 1) * (k + 1) = rising n k * (n + k) :=
  choose_rising_succ n k hn

lemma choose_rising_succ_rat (n k : ℕ) (hn : 0 < n) :
    (choose (n + (k + 1) - 1) (k + 1) : ℚ) =
      (choose (n + k - 1) k : ℚ) * ((n + k : ℚ) / (k + 1)) := by
  have h := congrArg (fun x : ℕ => (x : ℚ)) (choose_rising_succ n k hn)
  push_cast at h
  field_simp
  linarith

lemma rising_eq_prod (n k : ℕ) (hn : 0 < n) :
    (rising n k : ℚ) = ∏ j ∈ range k, ((n + j : ℚ) / (j + 1)) := by
  induction k with
  | zero => simp [rising]
  | succ k ih =>
    rw [prod_range_succ, ← ih]
    simpa [rising] using choose_rising_succ_rat n k hn

lemma f_increment (y δ : ℤ) :
    (3 * (y + δ) ^ 2 + 2 * (y + δ) ^ 3) - (3 * y ^ 2 + 2 * y ^ 3) =
      6 * y * (y + 1) * δ + 3 * (2 * y + 1) * δ ^ 2 + 2 * δ ^ 3 := by
  ring

lemma A357565.term_eq_rising (n k : ℕ) :
    A357565.term n k = 3 * rising n k ^ 2 + 2 * rising n k ^ 3 := rfl

lemma A357565.term_int (n k : ℕ) :
    (A357565.term n k : ℤ) =
      3 * (rising n k : ℤ) ^ 2 + 2 * (rising n k : ℤ) ^ 3 := by
  simp [A357565.term, rising]

lemma f_int_zero : (3 * (0 : ℤ) ^ 2 + 2 * (0 : ℤ) ^ 3) = 0 := by ring

/-! ### p-adic lemmas -/

lemma padicValNat_pow_self (p n : ℕ) [Fact p.Prime] : padicValNat p (p ^ n) = n :=
  padicValNat.prime_pow n

lemma padicValNat_pow_add {p j r : ℕ} [hp : Fact p.Prime] (hj : j ≠ 0)
    (hjt : padicValNat p j < r) :
    padicValNat p (p ^ r + j) = padicValNat p j := by
  apply le_antisymm
  · by_contra h
    push_neg at h
    have hsum0 : p ^ r + j ≠ 0 :=
      Nat.ne_zero_of_lt (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hj))
    have : r ≤ padicValNat p (p ^ r + j) ∨ padicValNat p j + 1 ≤ padicValNat p (p ^ r + j) := by
      omega
    cases this with
    | inl h1 =>
      have hdvd : p ^ r ∣ p ^ r + j := by
        rwa [padicValNat_dvd_iff_le hsum0]
      have : p ^ r ∣ j := (Nat.dvd_add_right (dvd_refl _)).mp hdvd
      have : r ≤ padicValNat p j := by
        rwa [← padicValNat_dvd_iff_le hj]
      omega
    | inr h1 =>
      have hpr_dvd : p ^ (padicValNat p j + 1) ∣ p ^ r := pow_dvd_pow p (by omega)
      have hsum_dvd : p ^ (padicValNat p j + 1) ∣ p ^ r + j := by
        rwa [padicValNat_dvd_iff_le hsum0]
      have : p ^ (padicValNat p j + 1) ∣ j :=
        (Nat.dvd_add_iff_right hpr_dvd).mpr hsum_dvd
      have : padicValNat p j + 1 ≤ padicValNat p j := by
        rwa [← padicValNat_dvd_iff_le hj]
      omega
  · have h1 : p ^ padicValNat p j ∣ p ^ r := pow_dvd_pow p (le_of_lt hjt)
    have h2 : p ^ padicValNat p j ∣ j := pow_padicValNat_dvd
    have hdiv : p ^ padicValNat p j ∣ p ^ r + j := dvd_add h1 h2
    have hsum0 : p ^ r + j ≠ 0 :=
      Nat.ne_zero_of_lt (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hj))
    exact (padicValNat_dvd_iff_le hsum0).mp hdiv

lemma padicValNat_lt_of_lt_pow {p k r : ℕ} [hp : Fact p.Prime]
    (hk0 : 0 < k) (hk : k < p ^ r) : padicValNat p k < r := by
  have h1 : padicValNat p k ≤ Nat.log p k := padicValNat_le_nat_log k
  have h2 : Nat.log p k < r := Nat.log_lt_of_lt_pow (ne_zero_of_lt hk0) hk
  omega

lemma padicValNat_le_of_le_pow {p k r : ℕ} [hp : Fact p.Prime]
    (hk0 : 0 < k) (hk : k ≤ p ^ r) : padicValNat p k ≤ r := by
  rcases lt_or_eq_of_le hk with h | h
  · exact le_of_lt (padicValNat_lt_of_lt_pow hk0 h)
  · subst h
    exact le_of_eq (padicValNat.prime_pow r)

lemma padicValNat_factorial_succ (p k : ℕ) [hp : Fact p.Prime] (hk0 : 0 < k) :
    padicValNat p k.factorial = padicValNat p (k - 1).factorial + padicValNat p k := by
  have hk : k = (k - 1) + 1 := by omega
  nth_rw 1 [hk]
  rw [factorial_succ]
  have hmul := padicValNat.mul (p := p) (a := k) (b := (k - 1).factorial)
    (ne_zero_of_lt hk0) (factorial_ne_zero _)
  have hkeq : k - 1 + 1 = k := Nat.sub_add_cancel hk0
  rw [hkeq, hmul, add_comm]

lemma padicValNat_ascFactorial_prime_pow {p r k : ℕ} [hp : Fact p.Prime]
    (hk0 : 0 < k) (hk : k ≤ p ^ r) :
    padicValNat p ((p ^ r).ascFactorial k) = r + padicValNat p (k - 1).factorial := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => exact (lt_irrefl 0 hk0).elim
    | 1 =>
      simp [ascFactorial_succ, padicValNat.prime_pow, ascFactorial_zero]
    | k + 2 =>
      set k' := k + 1 with hk'def
      have hk'0 : 0 < k' := by omega
      have hk'le : k' ≤ p ^ r := by omega
      rw [show k + 2 = k' + 1 from by omega, ascFactorial_succ]
      have hmul0 : p ^ r + k' ≠ 0 :=
        Nat.ne_zero_of_lt (Nat.lt_add_of_pos_right hk'0)
      have hasc0 : (p ^ r).ascFactorial k' ≠ 0 := by
        have hprpos : 1 ≤ p ^ r := Nat.one_le_pow r p hp.out.pos
        have heq : p ^ r = (p ^ r - 1) + 1 := by omega
        rw [heq]
        exact (ascFactorial_pos (p ^ r - 1) k').ne'
      rw [padicValNat.mul (p := p) hmul0 hasc0]
      have hval : padicValNat p k' < r := by
        have : k' < p ^ r := by omega
        exact padicValNat_lt_of_lt_pow hk'0 this
      have hpeq : padicValNat p (p ^ r + k') = padicValNat p k' :=
        padicValNat_pow_add (ne_zero_of_lt hk'0) hval
      rw [hpeq]
      have ih' := ih k' (by omega) hk'0 hk'le
      rw [ih']
      have hfac := padicValNat_factorial_succ p (k' + 1) (by omega)
      simp only [show k' + 1 - 1 = k' from by omega] at hfac ⊢
      have hfac' := padicValNat_factorial_succ p k' hk'0
      omega

lemma padicValNat_rising_prime_pow {p r k : ℕ} [hp : Fact p.Prime]
    (hk0 : 0 < k) (hk : k ≤ p ^ r) :
    padicValNat p (rising (p ^ r) k) = r - padicValNat p k := by
  have hne : rising (p ^ r) k ≠ 0 := by
    unfold rising
    exact choose_ne_zero (by
      have : k ≤ p ^ r + k - 1 := by
        have : 1 ≤ p ^ r := Nat.one_le_pow r p hp.out.pos
        omega
      exact this)
  have hkf : k.factorial ≠ 0 := factorial_ne_zero k
  have hasc_eq : (p ^ r).ascFactorial k = k.factorial * rising (p ^ r) k := by
    simpa [rising] using (ascFactorial_eq_factorial_mul_choose' (p ^ r) k)
  have hsum : padicValNat p ((p ^ r).ascFactorial k) =
      padicValNat p k.factorial + padicValNat p (rising (p ^ r) k) := by
    rw [hasc_eq, padicValNat.mul hkf hne]
  have hfac := padicValNat_factorial_succ p k hk0
  have hasc_val := padicValNat_ascFactorial_prime_pow (p := p) (r := r) (k := k) hk0 hk
  omega

lemma padicValNat_rising_of_not_dvd {p r k : ℕ} [hp : Fact p.Prime]
    (hk0 : 0 < k) (hk : k ≤ p ^ r) (hnd : ¬ p ∣ k) :
    padicValNat p (rising (p ^ r) k) = r := by
  rw [padicValNat_rising_prime_pow hk0 hk, padicValNat.eq_zero_of_not_dvd hnd, tsub_zero]

/-! ### The old contribution y_k -/

def risingY (p r k : ℕ) : ℕ :=
  if p ∣ k then rising (p ^ (r - 1)) (k / p) else 0

lemma risingY_of_not_dvd {p r k : ℕ} (h : ¬ p ∣ k) : risingY p r k = 0 := by
  simp [risingY, h]

lemma risingY_of_dvd {p r k : ℕ} (h : p ∣ k) :
    risingY p r k = rising (p ^ (r - 1)) (k / p) := by
  simp [risingY, h]

lemma risingY_zero (p r : ℕ) : risingY p r 0 = 1 := by
  simp [risingY, rising_zero_right]

/-! ### p-free residues -/

def pfree (p r : ℕ) : Finset ℕ :=
  (range (p ^ r)).filter (fun k => ¬ p ∣ k)

lemma mem_pfree {p r k : ℕ} :
    k ∈ pfree p r ↔ k < p ^ r ∧ ¬ p ∣ k := by
  simp [pfree, mem_filter, mem_range]

lemma pfree_pos {p r k : ℕ} (hp : p.Prime) (hk : k ∈ pfree p r) : 0 < k := by
  have ⟨hklt, hnd⟩ := mem_pfree.mp hk
  exact Nat.pos_of_ne_zero (fun h => hnd (by simp [h]))

lemma coprime_of_not_dvd_prime_pow {p r k : ℕ} (hp : p.Prime) (hr : 0 < r)
    (hnd : ¬ p ∣ k) : k.Coprime (p ^ r) := by
  rw [Nat.coprime_pow_right_iff hr]
  exact (hp.coprime_iff_not_dvd).2 hnd |>.symm

lemma isUnit_of_mem_pfree {p r k : ℕ} (hp : p.Prime) (hr : 0 < r)
    (hk : k ∈ pfree p r) : IsUnit (k : ZMod (p ^ r)) := by
  have ⟨_, hnd⟩ := mem_pfree.mp hk
  rw [ZMod.isUnit_iff_coprime]
  exact coprime_of_not_dvd_prime_pow hp hr hnd

lemma geom_sum_eq_zero_of_isUnit_sub_one {R : Type*} [CommRing R]
    (x : R) {n : ℕ} (hx : x ^ n = 1) (hunit : IsUnit (x - 1)) :
    ∑ i ∈ range n, x ^ i = 0 := by
  have hgeom := geom_sum_mul x n
  rw [hx, sub_self] at hgeom
  obtain ⟨u, hu⟩ := hunit
  have h0 : (∑ i ∈ range n, x ^ i) * (u : R) = 0 := by
    rw [hu, hgeom]
  have := congrArg (fun z : R => z * ((u⁻¹ : Rˣ) : R)) h0
  simpa [mul_assoc] using this

lemma pow_ne_one_of_prime_pow {p r : ℕ} (hp : p.Prime) (hr : 0 < r) :
    (p ^ r : ℕ) ≠ 1 := by
  have : 1 < p ^ r := one_lt_pow' hp.one_lt (ne_zero_of_lt hr)
  omega

lemma one_ne_zero_zmod_prime_pow {p r : ℕ} (hp : p.Prime) (hr : 0 < r) :
    (1 : ZMod (p ^ r)) ≠ 0 := by
  intro h
  have : p ^ r ∣ 1 := (ZMod.natCast_eq_zero_iff (1 : ℕ) (p ^ r)).mp (by simpa using h)
  have : p ^ r = 1 := Nat.eq_one_of_dvd_one this
  exact pow_ne_one_of_prime_pow hp hr this

lemma isUnit_iff_not_dvd_val {p r : ℕ} (hp : p.Prime) (hr : 0 < r)
    (x : ZMod (p ^ r)) : IsUnit x ↔ ¬ p ∣ x.val := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff hr,
    Nat.coprime_comm, hp.coprime_iff_not_dvd, ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt x)]

lemma isUnit_of_cast_ne_zero {p r : ℕ} (hp : p.Prime) (hr : 0 < r)
    (x : ZMod (p ^ r))
    (hne : (ZMod.castHom (dvd_pow_self p (ne_zero_of_lt hr)) (ZMod p) x) ≠ 0) :
    IsUnit x := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  rw [isUnit_iff_not_dvd_val hp hr]
  intro hd
  have hval0 : (x.val : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff x.val p).mpr hd
  have hcast : ZMod.castHom (dvd_pow_self p (ne_zero_of_lt hr)) (ZMod p) x = (x.val : ZMod p) := by
    rw [ZMod.castHom_apply, ZMod.natCast_val]
  exact hne (hcast.trans hval0)

lemma pfree_mul_mod {p r : ℕ} (hp : p.Prime) (hr : 0 < r)
    {γ k : ℕ} (hg : γ ∈ pfree p r) (hk : k ∈ pfree p r) :
    (γ * k) % (p ^ r) ∈ pfree p r := by
  have ⟨hγlt, hγnd⟩ := mem_pfree.mp hg
  have ⟨hklt, hknd⟩ := mem_pfree.mp hk
  refine mem_pfree.mpr ⟨Nat.mod_lt _ (pow_pos hp.pos r), ?_⟩
  intro hdvd
  have : p ∣ γ * k := (Nat.dvd_mod_iff (dvd_pow_self p (ne_zero_of_lt hr))).mp hdvd
  rcases hp.dvd_mul.mp this with h | h
  · exact hγnd h
  · exact hknd h

lemma eq_of_zmod_eq_of_lt {n a b : ℕ} (h : (a : ZMod n) = (b : ZMod n))
    (ha : a < n) (hb : b < n) : a = b := by
  cases n with
  | zero => simp at ha
  | succ n =>
    haveI : NeZero (n + 1) := inferInstance
    rw [ZMod.natCast_eq_natCast_iff'] at h
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
    exact h

/-- If `p-1 ∤ m` then the sum of `m`-th powers of p-free residues vanishes in `ZMod (p^r)`. -/
lemma sum_pfree_zmod_pow_eq_zero {p r m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : 0 < r) (hdiv : ¬ (p - 1) ∣ m) :
    (∑ k ∈ pfree p r, (k : ZMod (p ^ r)) ^ m) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcycp : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp
  obtain ⟨g0, hg0⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hcycp
  have hord : orderOf g0 = p - 1 := by
    rw [hg0, Nat.card_eq_fintype_card, ZMod.card_units]
  have hg0m : g0 ^ m ≠ 1 := by
    intro h
    have : orderOf g0 ∣ m := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hord] at this
    exact hdiv this
  have hsurj : Function.Surjective
      (ZMod.unitsMap (dvd_pow_self p (ne_zero_of_lt hr))) :=
    ZMod.unitsMap_surjective (dvd_pow_self p (ne_zero_of_lt hr))
  obtain ⟨g, hg⟩ := hsurj g0
  set γ := (g : ZMod (p ^ r)).val with hγdef
  have hγlt : γ < p ^ r := ZMod.val_lt _
  have hγeq : (γ : ZMod (p ^ r)) = (g : ZMod (p ^ r)) := ZMod.natCast_zmod_val _
  have hγnd : ¬ p ∣ γ := by
    intro hd
    have hgu : IsUnit (g : ZMod (p ^ r)) := g.isUnit
    rw [isUnit_iff_not_dvd_val hp hr] at hgu
    simpa [hγdef] using hgu hd
  have hγmem : γ ∈ pfree p r := mem_pfree.mpr ⟨hγlt, hγnd⟩
  have hsum_perm :
      (∑ k ∈ pfree p r, (k : ZMod (p ^ r)) ^ m) =
        ∑ k ∈ pfree p r, ((γ : ZMod (p ^ r)) * k) ^ m := by
    refine (Finset.sum_nbij (fun k => (γ * k) % (p ^ r)) ?_ ?_ ?_ ?_).symm
    · intro k hk; exact pfree_mul_mod hp hr hγmem hk
    · intro k hk k' hk' heq
      have h1 : (γ : ZMod (p ^ r)) * k = (γ : ZMod (p ^ r)) * k' := by
        have := congrArg (fun x : ℕ => (x : ZMod (p ^ r))) heq
        simpa [ZMod.natCast_mod] using this
      have hγu : IsUnit (γ : ZMod (p ^ r)) := isUnit_of_mem_pfree hp hr hγmem
      obtain ⟨u, hu⟩ := hγu
      have : (k : ZMod (p ^ r)) = (k' : ZMod (p ^ r)) := by
        have h1' : (u : ZMod (p ^ r)) * k = (u : ZMod (p ^ r)) * k' := by
          simpa [hu] using h1
        apply_fun (fun z : ZMod (p ^ r) => (u⁻¹ : ZMod (p ^ r)) * z) at h1'
        simpa [← mul_assoc] using h1'
      have ⟨hklt, _⟩ := mem_pfree.mp hk
      have ⟨hk'lt, _⟩ := mem_pfree.mp hk'
      exact eq_of_zmod_eq_of_lt this hklt hk'lt
    · intro t ht
      have hγu : IsUnit (γ : ZMod (p ^ r)) := isUnit_of_mem_pfree hp hr hγmem
      obtain ⟨u, hu⟩ := hγu
      set γinv := (u⁻¹ : ZMod (p ^ r)).val with hinvdef
      have hγinv_mul : (γinv : ZMod (p ^ r)) * γ = 1 := by
        have : (γinv : ZMod (p ^ r)) = (u⁻¹ : ZMod (p ^ r)) := ZMod.natCast_zmod_val _
        rw [this, ← hu]
        simp
      have hγinv_nd : ¬ p ∣ γinv := by
        have : ¬ p ∣ ((u⁻¹ : (ZMod (p ^ r))ˣ) : ZMod (p ^ r)).val :=
          (isUnit_iff_not_dvd_val hp hr _).mp (u⁻¹).isUnit
        simpa [hinvdef] using this
      have hγinv_mem : γinv ∈ pfree p r :=
        mem_pfree.mpr ⟨ZMod.val_lt _, hγinv_nd⟩
      refine ⟨(γinv * t) % (p ^ r), pfree_mul_mod hp hr hγinv_mem ht, ?_⟩
      have hcast : ((((γ * ((γinv * t) % p ^ r)) % p ^ r) : ℕ) : ZMod (p ^ r)) =
          (t : ZMod (p ^ r)) := by
        rw [ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod, Nat.cast_mul]
        rw [← mul_assoc, mul_comm (γ : ZMod (p ^ r)) γinv, hγinv_mul, one_mul]
      have ⟨htlt, _⟩ := mem_pfree.mp ht
      exact eq_of_zmod_eq_of_lt hcast (Nat.mod_lt _ (pow_pos hp.pos r)) htlt
    · intro k hk
      simp [ZMod.natCast_mod]
  have hmul :
      ∑ k ∈ pfree p r, ((γ : ZMod (p ^ r)) * k) ^ m =
        (γ : ZMod (p ^ r)) ^ m * ∑ k ∈ pfree p r, (k : ZMod (p ^ r)) ^ m := by
    simp [mul_pow, mul_sum]
  have heq : ∑ k ∈ pfree p r, (k : ZMod (p ^ r)) ^ m =
      (γ : ZMod (p ^ r)) ^ m * ∑ k ∈ pfree p r, (k : ZMod (p ^ r)) ^ m := by
    calc
      ∑ k ∈ pfree p r, (k : ZMod (p ^ r)) ^ m =
          ∑ k ∈ pfree p r, ((γ : ZMod (p ^ r)) * k) ^ m := hsum_perm
      _ = (γ : ZMod (p ^ r)) ^ m * ∑ k ∈ pfree p r, (k : ZMod (p ^ r)) ^ m := hmul
  have hfactor : ((γ : ZMod (p ^ r)) ^ m - 1) *
      ∑ k ∈ pfree p r, (k : ZMod (p ^ r)) ^ m = 0 := by
    linear_combination -heq
  have hunit : IsUnit ((γ : ZMod (p ^ r)) ^ m - 1) := by
    apply isUnit_of_cast_ne_zero hp hr
    rw [map_sub, map_pow, map_one, hγeq]
    have hcastg :
        ZMod.castHom (dvd_pow_self p (ne_zero_of_lt hr)) (ZMod p) (g : ZMod (p ^ r)) =
          (g0 : ZMod p) := by
      rw [← hg, ZMod.unitsMap_val, ZMod.castHom_apply]
    rw [hcastg]
    intro h1
    have hg0eq : (g0 : ZMod p) ^ m = 1 := by
      linear_combination h1
    have : g0 ^ m = 1 := by
      ext
      simpa using hg0eq
    exact hg0m this
  obtain ⟨u, hu⟩ := hunit
  have h0 : (∑ k ∈ pfree p r, (k : ZMod (p ^ r)) ^ m) * (u : ZMod (p ^ r)) = 0 := by
    rw [hu, mul_comm, hfactor]
  have := congrArg (fun z : ZMod (p ^ r) =>
      z * ((u⁻¹ : (ZMod (p ^ r))ˣ) : ZMod (p ^ r))) h0
  simpa [mul_assoc] using this



/-! ### Reindexing and the increment formula -/

lemma prime_mul_pow_pred {p r : ℕ} (hr : 1 ≤ r) : p * p ^ (r - 1) = p ^ r := by
  rw [← Nat.pow_succ']
  congr 1
  exact Nat.sub_add_cancel hr

lemma mul_lt_pow_succ {p r j : ℕ} (hp0 : 0 < p) (hr : 1 ≤ r)
    (hj : j < p ^ (r - 1) + 1) : p * j < p ^ r + 1 := by
  have hjle : j ≤ p ^ (r - 1) := Nat.lt_succ_iff.mp hj
  have : p * j ≤ p * p ^ (r - 1) := Nat.mul_le_mul_left p hjle
  have hpow : p * p ^ (r - 1) = p ^ r := prime_mul_pow_pred hr
  omega

lemma sum_old_reindex (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) :
    ∑ j ∈ range (p ^ (r - 1) + 1), (A357565.term (p ^ (r - 1)) j : ℤ) =
      ∑ k ∈ (range (p ^ r + 1)).filter (p ∣ ·),
        (A357565.term (p ^ (r - 1)) (k / p) : ℤ) := by
  refine Finset.sum_bij (fun j _ => p * j) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [mem_filter, mem_range]
    exact ⟨mul_lt_pow_succ hp.pos hr (mem_range.mp hj), dvd_mul_right p j⟩
  · intro j _ j' _ heq
    exact Nat.eq_of_mul_eq_mul_left hp.pos heq
  · intro k hk
    have hklt : k < p ^ r + 1 := mem_range.mp (mem_filter.mp hk).1
    have hkd : p ∣ k := (mem_filter.mp hk).2
    refine ⟨k / p, ?_, ?_⟩
    · rw [mem_range]
      have hkN : k ≤ p ^ r := Nat.lt_succ_iff.mp hklt
      have : k / p ≤ p ^ (r - 1) := by
        have hle : k ≤ p * p ^ (r - 1) := by rw [prime_mul_pow_pred hr]; exact hkN
        exact Nat.div_le_of_le_mul hle
      exact Nat.lt_succ_iff.mpr this
    · exact Nat.mul_div_cancel' hkd
  · intro j hj
    rw [Nat.mul_div_cancel_left j hp.pos]

lemma A357565_sub_eq_sum_increment (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) :
    (A357565 (p ^ r) : ℤ) - A357565 (p ^ (r - 1)) =
      ∑ k ∈ range (p ^ r + 1),
        ((3 * (rising (p ^ r) k : ℤ) ^ 2 + 2 * (rising (p ^ r) k : ℤ) ^ 3) -
          (3 * (risingY p r k : ℤ) ^ 2 + 2 * (risingY p r k : ℤ) ^ 3)) := by
  have hL : (A357565 (p ^ r) : ℤ) =
      ∑ k ∈ range (p ^ r + 1), (A357565.term (p ^ r) k : ℤ) := by
    simp [A357565_eq_sum_term]
  have hR : (A357565 (p ^ (r - 1)) : ℤ) =
      ∑ k ∈ (range (p ^ r + 1)).filter (p ∣ ·),
        (A357565.term (p ^ (r - 1)) (k / p) : ℤ) := by
    simp only [A357565_eq_sum_term, Nat.cast_sum]
    exact sum_old_reindex p r hp hr
  have hR' : (A357565 (p ^ (r - 1)) : ℤ) =
      ∑ k ∈ range (p ^ r + 1),
        (if p ∣ k then (A357565.term (p ^ (r - 1)) (k / p) : ℤ) else 0) := by
    rw [hR, sum_filter]
  rw [hL, hR', ← sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp only [A357565.term_int, rising]
  by_cases hdv : p ∣ k
  · simp [risingY, rising, hdv]
  · simp [risingY, rising, hdv]

lemma increment_as_poly (p r k : ℕ) :
    (3 * (rising (p ^ r) k : ℤ) ^ 2 + 2 * (rising (p ^ r) k : ℤ) ^ 3) -
      (3 * (risingY p r k : ℤ) ^ 2 + 2 * (risingY p r k : ℤ) ^ 3) =
    6 * (risingY p r k : ℤ) * ((risingY p r k : ℤ) + 1) *
      ((rising (p ^ r) k : ℤ) - risingY p r k) +
    3 * (2 * (risingY p r k : ℤ) + 1) *
      ((rising (p ^ r) k : ℤ) - risingY p r k) ^ 2 +
    2 * ((rising (p ^ r) k : ℤ) - risingY p r k) ^ 3 := by
  ring

/-- `p^{a+1}` divides `C(p^a, j) * p^j` for `j ≥ 1`. -/
lemma pow_dvd_choose_prime_pow_mul {p a j : ℕ} (hp : p.Prime) (hj : 0 < j) :
    p ^ (a + 1) ∣ choose (p ^ a) j * p ^ j := by
  by_cases hle : j ≤ p ^ a
  · haveI : Fact p.Prime := ⟨hp⟩
    have hj0 : j ≠ 0 := ne_zero_of_lt hj
    have hfac := factorization_choose_prime_pow hp hle hj0
    have hcv : padicValNat p (choose (p ^ a) j) = a - padicValNat p j := by
      rw [← factorization_def (choose (p ^ a) j) hp, hfac, factorization_def j hp]
    have hne : choose (p ^ a) j * p ^ j ≠ 0 :=
      mul_ne_zero (choose_pos hle).ne' (pow_ne_zero _ hp.ne_zero)
    have hmulv : padicValNat p (choose (p ^ a) j * p ^ j) =
        padicValNat p (choose (p ^ a) j) + padicValNat p (p ^ j) :=
      padicValNat.mul (p := p) (choose_pos hle).ne' (pow_ne_zero _ hp.ne_zero)
    have hpj : padicValNat p (p ^ j) = j := padicValNat.prime_pow j
    have hge : a + 1 ≤ padicValNat p (choose (p ^ a) j * p ^ j) := by
      rw [hmulv, hcv, hpj]
      have hvlt : padicValNat p j < j :=
        lt_of_le_of_lt (padicValNat_le_nat_log j) (Nat.log_lt_self p (ne_zero_of_lt hj))
      omega
    exact (padicValNat_dvd_iff_le hne).mpr hge
  · have : choose (p ^ a) j = 0 := choose_eq_zero_of_lt (lt_of_not_ge hle)
    simp [this]

lemma pow_dvd_int_rising_sub_risingY_not_dvd {p r k : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hk : k ≤ p ^ r) (hdv : ¬ p ∣ k) :
    (p : ℤ) ^ r ∣ (rising (p ^ r) k : ℤ) - (risingY p r k : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hk0 : 0 < k := Nat.pos_of_ne_zero (fun h => hdv (by simp [h]))
  have hkn : k < p ^ r :=
    lt_of_le_of_ne hk (fun h => hdv (by rw [h]; exact dvd_pow_self p (ne_zero_of_lt hr)))
  have hval := padicValNat_rising_of_not_dvd hk0 (le_of_lt hkn) hdv
  have hne : rising (p ^ r) k ≠ 0 := by
    unfold rising
    exact choose_ne_zero (by
      have : 1 ≤ p ^ r := Nat.one_le_pow r p hp.pos
      omega)
  have hdvd : p ^ r ∣ rising (p ^ r) k :=
    (padicValNat_dvd_iff_le hne).mpr (le_of_eq hval.symm)
  rw [risingY_of_not_dvd hdv, Int.natCast_zero, sub_zero]
  simpa [Int.natCast_pow] using (Int.natCast_dvd_natCast.mpr hdvd)


/-! ### Product formula for `(p * n)!` -/

lemma factorial_mul_asc (n k : ℕ) :
    (n + k).factorial = n.factorial * (n + 1).ascFactorial k :=
  (factorial_mul_ascFactorial n k).symm

lemma ascFactorial_eq_prod (n k : ℕ) :
    n.ascFactorial k = ∏ i ∈ range k, (n + i) := by
  induction k with
  | zero => simp [ascFactorial_zero]
  | succ k ih =>
    rw [ascFactorial_succ, ih, prod_range_succ, mul_comm]

lemma prod_range_add_one_eq_Icc (n k : ℕ) :
    ∏ i ∈ range k, (n + 1 + i) = ∏ t ∈ Icc 1 k, (n + t) := by
  refine Finset.prod_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    have : i < k := mem_range.mp hi
    exact mem_Icc.mpr ⟨Nat.succ_le_succ (Nat.zero_le i), Nat.succ_le_of_lt this⟩
  · intro i _ j _ h
    exact Nat.succ_injective h
  · intro t ht
    have ⟨ht1, ht2⟩ := mem_Icc.mp ht
    refine ⟨t - 1, mem_range.mpr (by omega), ?_⟩
    exact Nat.sub_add_cancel ht1
  · intro i hi
    ring

lemma Icc_succ_right_eq_insert (a b : ℕ) (h : a ≤ b + 1) :
    Icc a (b + 1) = insert (b + 1) (Icc a b) := by
  ext t
  simp only [mem_insert, mem_Icc]
  constructor
  · intro ⟨h1, h2⟩
    rcases eq_or_lt_of_le h2 with heq | hlt
    · exact Or.inl heq
    · exact Or.inr ⟨h1, Nat.lt_succ_iff.mp hlt⟩
  · intro ht
    rcases ht with rfl | ⟨h1, h2⟩
    · exact ⟨h, le_rfl⟩
    · exact ⟨h1, le_succ_of_le h2⟩

lemma Icc_pred_eq_insert {p : ℕ} (hp : 1 ≤ p) :
    Icc 1 p = insert p (Icc 1 (p - 1)) := by
  have heq : p = (p - 1) + 1 := (Nat.sub_add_cancel hp).symm
  rw [heq]
  exact Icc_succ_right_eq_insert 1 (p - 1) (by simp [Nat.sub_add_cancel hp, hp])

lemma not_mem_Icc_self_pred {p : ℕ} (hp : 1 ≤ p) :
    p ∉ Icc 1 (p - 1) := by
  simp [mem_Icc]
  omega

lemma mem_Icc_p_sub {p t : ℕ} (hp : 1 ≤ p) (ht : t ∈ Icc 1 (p - 1)) :
    p - t ∈ Icc 1 (p - 1) := by
  have ⟨h1, h2⟩ := mem_Icc.mp ht
  refine mem_Icc.mpr ⟨?_, ?_⟩
  · omega
  · omega

lemma p_sub_p_sub {p s : ℕ} (hs : s ∈ Icc 1 (p - 1)) (hp : 1 ≤ p) :
    p - (p - s) = s := by
  have ⟨h1, h2⟩ := mem_Icc.mp hs
  omega

lemma prod_Icc_pn_reindex {p n : ℕ} (hp : 1 ≤ p) :
    ∏ t ∈ Icc 1 (p - 1), (p * n + t) =
      ∏ s ∈ Icc 1 (p - 1), (p * (n + 1) - s) := by
  refine Finset.prod_bij (fun t _ => p - t) (fun t ht => mem_Icc_p_sub hp ht)
    ?_ (fun s hs => ⟨p - s, mem_Icc_p_sub hp hs, p_sub_p_sub hs hp⟩) ?_
  · intro t ht s hs heq
    have ⟨ht1, ht2⟩ := mem_Icc.mp ht
    have ⟨hs1, hs2⟩ := mem_Icc.mp hs
    have ht_le : t ≤ p := by omega
    have hs_le : s ≤ p := by omega
    have hps : p - t = p - s := heq
    omega
  · intro t ht
    have ⟨ht1, ht2⟩ := mem_Icc.mp ht
    have htle : t ≤ p := by omega
    have : p * (n + 1) - (p - t) = p * n + t := by
      have h1 : p * (n + 1) = p * n + p := by ring
      rw [h1]
      omega
    exact this.symm

lemma prod_Icc_succ_right (f : ℕ → ℕ) (n : ℕ) :
    ∏ j ∈ Icc 1 (n + 1), f j = (∏ j ∈ Icc 1 n, f j) * f (n + 1) := by
  have h : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  have hI : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) :=
    Icc_succ_right_eq_insert 1 n h
  have hnot : n + 1 ∉ Icc 1 n := by simp [mem_Icc]
  rw [hI, prod_insert hnot]
  ring

/-- `(p n)! = p^n n! ∏_{s=1}^{p-1} ∏_{j=1}^{n} (p j - s)`. -/
lemma factorial_mul_prime {p n : ℕ} (hp : p.Prime) :
    (p * n).factorial =
      p ^ n * n.factorial *
        ∏ s ∈ Icc 1 (p - 1), ∏ j ∈ Icc 1 n, (p * j - s) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have hp1 : 1 ≤ p := hp.pos
    have hrew : p * (n + 1) = p * n + p := by ring
    rw [hrew, factorial_mul_asc (p * n) p, ih]
    have hasc : (p * n + 1).ascFactorial p = ∏ t ∈ Icc 1 p, (p * n + t) := by
      rw [ascFactorial_eq_prod]
      simpa [add_assoc] using (prod_range_add_one_eq_Icc (p * n) p)
    rw [hasc, Icc_pred_eq_insert hp1, prod_insert (not_mem_Icc_self_pred hp1)]
    have htop : p * n + p = p * (n + 1) := by ring
    rw [htop, prod_Icc_pn_reindex hp1]
    have hfac : n.factorial * (n + 1) = (n + 1).factorial := by
      rw [factorial_succ, mul_comm]
    have hpow : p ^ n * p = p ^ (n + 1) := by rw [pow_succ]
    have hprod :
        (∏ s ∈ Icc 1 (p - 1), ∏ j ∈ Icc 1 n, (p * j - s)) *
          (∏ s ∈ Icc 1 (p - 1), (p * (n + 1) - s)) =
        ∏ s ∈ Icc 1 (p - 1), ∏ j ∈ Icc 1 (n + 1), (p * j - s) := by
      rw [← prod_mul_distrib]
      refine Finset.prod_congr rfl ?_
      intro s hs
      rw [prod_Icc_succ_right]
    calc
      p ^ n * n.factorial *
          (∏ s ∈ Icc 1 (p - 1), ∏ j ∈ Icc 1 n, (p * j - s)) *
          (p * (n + 1) * ∏ s ∈ Icc 1 (p - 1), (p * (n + 1) - s)) =
        p ^ n * p * (n.factorial * (n + 1)) *
          ((∏ s ∈ Icc 1 (p - 1), ∏ j ∈ Icc 1 n, (p * j - s)) *
            (∏ s ∈ Icc 1 (p - 1), (p * (n + 1) - s))) := by ring
      _ = p ^ (n + 1) * (n + 1).factorial *
          (∏ s ∈ Icc 1 (p - 1), ∏ j ∈ Icc 1 (n + 1), (p * j - s)) := by
        rw [hpow, hfac, hprod]

/-- The p-free product `P_t = ∏_{s=1}^{p-1} ∏_{j=1}^{t} (p j - s)`. -/
def pProd (p t : ℕ) : ℕ :=
  ∏ s ∈ Icc 1 (p - 1), ∏ j ∈ Icc 1 t, (p * j - s)

lemma factorial_mul_prime' {p n : ℕ} (hp : p.Prime) :
    (p * n).factorial = p ^ n * n.factorial * pProd p n :=
  factorial_mul_prime hp

lemma pProd_pos {p t : ℕ} (hp : 1 ≤ p) : 0 < pProd p t := by
  refine prod_pos fun s hs => prod_pos fun j hj => ?_
  have ⟨hs1, hs2⟩ := mem_Icc.mp hs
  have ⟨hj1, hj2⟩ := mem_Icc.mp hj
  have hlt : s < p := by omega
  have hge : p ≤ p * j := Nat.le_mul_of_pos_right p hj1
  have : s < p * j := lt_of_lt_of_le hlt hge
  exact Nat.sub_pos_of_lt this

lemma p_not_dvd_pProd {p t : ℕ} (hp : p.Prime) : ¬ p ∣ pProd p t := by
  intro h
  obtain ⟨s, hs, hsdiv⟩ := (Prime.dvd_finset_prod_iff (Nat.prime_iff.mp hp) _).mp h
  obtain ⟨j, hj, hjdiv⟩ := (Prime.dvd_finset_prod_iff (Nat.prime_iff.mp hp) _).mp hsdiv
  have ⟨hs1, hs2⟩ := mem_Icc.mp hs
  have ⟨hj1, hj2⟩ := mem_Icc.mp hj
  have hs_lt : s < p := by omega
  have hpj : p ∣ p * j := dvd_mul_right p j
  have hle : s ≤ p * j := by
    have : p ≤ p * j := Nat.le_mul_of_pos_right p hj1
    omega
  have hsub : p * j - (p * j - s) = s := Nat.sub_sub_self hle
  have : p ∣ s := by
    have hdiff : p ∣ p * j - (p * j - s) := Nat.dvd_sub hpj hjdiv
    rwa [hsub] at hdiff
  exact (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero (ne_zero_of_lt hs1)) hs_lt) this

lemma choose_mul_pProd_eq {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ n) :
    choose (p * n) (p * k) * pProd p k * pProd p (n - k) =
      choose n k * pProd p n := by
  have hle : p * k ≤ p * n := Nat.mul_le_mul_left p hkn
  have hpnk : p * n - p * k = p * (n - k) := (Nat.mul_sub p n k).symm
  have hf1 := choose_mul_factorial_mul_factorial hle
  have hf2 := choose_mul_factorial_mul_factorial hkn
  have Hn := factorial_mul_prime' (p := p) (n := n) hp
  have Hk := factorial_mul_prime' (p := p) (n := k) hp
  have Hnk := factorial_mul_prime' (p := p) (n := n - k) hp
  have hpow : p ^ k * p ^ (n - k) = p ^ n := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  have hpos : p ^ n * k.factorial * (n - k).factorial ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (factorial_ne_zero _))
      (factorial_ne_zero _)
  apply mul_left_cancel₀ hpos
  calc
    p ^ n * k.factorial * (n - k).factorial *
        (choose (p * n) (p * k) * pProd p k * pProd p (n - k)) =
      choose (p * n) (p * k) *
        (p ^ k * k.factorial * pProd p k) *
        (p ^ (n - k) * (n - k).factorial * pProd p (n - k)) := by
      rw [← hpow]; ring
    _ = choose (p * n) (p * k) * (p * k).factorial * (p * (n - k)).factorial := by
      rw [← Hk, ← Hnk]
    _ = choose (p * n) (p * k) * (p * k).factorial * (p * n - p * k).factorial := by
      rw [hpnk]
    _ = (p * n).factorial := hf1
    _ = p ^ n * n.factorial * pProd p n := Hn
    _ = p ^ n * k.factorial * (n - k).factorial * (choose n k * pProd p n) := by
      rw [← hf2]; ring


/-! ### Splitting `pProd` and the binomial ratio -/

lemma pProd_add {p a b : ℕ} (hp : 1 ≤ p) :
    pProd p (a + b) =
      pProd p a * ∏ s ∈ Icc 1 (p - 1), ∏ j ∈ Icc 1 b, (p * (a + j) - s) := by
  unfold pProd
  rw [← prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro s hs
  -- ∏_{j=1}^{a+b} = (∏_{j=1}^{a}) * (∏_{j=1}^{b} (p(a+j)-s))
  have hI : Icc 1 (a + b) = Icc 1 a ∪ (Icc 1 b).image (fun j => a + j) := by
    ext t
    simp only [mem_union, mem_image, mem_Icc]
    constructor
    · intro ⟨h1, h2⟩
      by_cases ht : t ≤ a
      · exact Or.inl ⟨h1, ht⟩
      · refine Or.inr ⟨t - a, ⟨?_, ?_⟩, ?_⟩
        · omega
        · omega
        · omega
    · intro h
      rcases h with ⟨h1, h2⟩ | ⟨j, ⟨hj1, hj2⟩, rfl⟩
      · exact ⟨h1, le_trans h2 (Nat.le_add_right a b)⟩
      · exact ⟨by omega, by omega⟩
  have hdisj : Disjoint (Icc 1 a) ((Icc 1 b).image (fun j => a + j)) := by
    refine disjoint_left.mpr ?_
    intro t ht ht'
    obtain ⟨j, hj, rfl⟩ := mem_image.mp ht'
    have ⟨h1, h2⟩ := mem_Icc.mp ht
    have ⟨hj1, hj2⟩ := mem_Icc.mp hj
    omega
  rw [hI, prod_union hdisj]
  congr 1
  refine Finset.prod_image ?_
  intro x hx y hy heq
  exact Nat.add_left_cancel heq

lemma pProd_add_shift {p a b : ℕ} (hp : 1 ≤ p) :
    pProd p (a + b) = pProd p a *
      ∏ s ∈ Icc 1 (p - 1), ∏ j ∈ Icc 1 b, (p * j - s + p * a) := by
  rw [pProd_add hp]
  congr 1
  refine Finset.prod_congr rfl ?_
  intro s hs
  refine Finset.prod_congr rfl ?_
  intro j hj
  have ⟨hs1, hs2⟩ := mem_Icc.mp hs
  have ⟨hj1, hj2⟩ := mem_Icc.mp hj
  have hs_lt : s < p := by omega
  have : s ≤ p * (a + j) := by
    have : 1 ≤ a + j := by omega
    have : p ≤ p * (a + j) := Nat.le_mul_of_pos_right p this
    omega
  have h1 : p * (a + j) - s = p * a + p * j - s := by
    rw [mul_add]
  have h2 : p * j - s + p * a = p * a + p * j - s := by
    have : s ≤ p * j := by
      have : p ≤ p * j := Nat.le_mul_of_pos_right p hj1
      omega
    omega
  omega

lemma choose_ratio_pProd {p A B : ℕ} (hp : p.Prime) (hBA : B ≤ A) :
    choose (p * A) (p * B) * pProd p B =
      choose A B * ∏ s ∈ Icc 1 (p - 1), ∏ j ∈ Icc 1 B, (p * j - s + p * (A - B)) := by
  have h := choose_mul_pProd_eq (p := p) (n := A) (k := B) hp hBA
  have hsplit := pProd_add_shift (p := p) (a := A - B) (b := B) hp.pos
  have hab : A - B + B = A := Nat.sub_add_cancel hBA
  rw [hab] at hsplit
  -- C(pA,pB) * P_B * P_{A-B} = C(A,B) * P_A
  -- P_A = P_{A-B} * ∏∏ (pj-s + p(A-B))
  -- cancel P_{A-B} > 0
  have hP : pProd p (A - B) ≠ 0 := ne_zero_of_lt (pProd_pos (p := p) (t := A - B) hp.pos)
  apply mul_right_cancel₀ hP
  calc
    choose (p * A) (p * B) * pProd p B * pProd p (A - B) =
      choose A B * pProd p A := h
    _ = choose A B * (pProd p (A - B) *
        ∏ s ∈ Icc 1 (p - 1), ∏ j ∈ Icc 1 B, (p * j - s + p * (A - B))) := by
      rw [hsplit]
    _ = choose A B * (∏ s ∈ Icc 1 (p - 1), ∏ j ∈ Icc 1 B,
          (p * j - s + p * (A - B))) * pProd p (A - B) := by ring

/-- `C(N-1, K) = C(N, K) * (N-K) / N` as an integer identity. -/
lemma choose_pred_mul {N K : ℕ} (hK : K ≤ N) (hN : 0 < N) :
    choose (N - 1) K * N = choose N K * (N - K) := by
  by_cases hK' : K = N
  · subst hK'
    have : (K - 1).choose K = 0 := choose_eq_zero_of_lt (Nat.sub_lt hN (by omega))
    simp [this, choose_self]
  · have hKlt : K < N := lt_of_le_of_ne hK hK'
    have hle : K ≤ N - 1 := Nat.le_pred_of_lt hKlt
    have h1 := choose_mul_factorial_mul_factorial (Nat.le_of_lt hKlt)
    have h2 := choose_mul_factorial_mul_factorial hle
    have hNfac : N.factorial = N * (N - 1).factorial := by
      have hN' : N = (N - 1) + 1 := (Nat.sub_add_cancel hN).symm
      rw [hN', factorial_succ, Nat.sub_add_cancel hN, mul_comm]
    have hNK : N - K = (N - 1 - K) + 1 := by omega
    have hNKfac : (N - K).factorial = (N - K) * (N - 1 - K).factorial := by
      rw [hNK, factorial_succ, mul_comm]
    have pos : K.factorial * (N - 1 - K).factorial ≠ 0 :=
      mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)
    apply mul_right_cancel₀ pos
    calc
      choose (N - 1) K * N * (K.factorial * (N - 1 - K).factorial) =
        N * (choose (N - 1) K * K.factorial * (N - 1 - K).factorial) := by ring
      _ = N * (N - 1).factorial := by rw [h2]
      _ = N.factorial := hNfac.symm
      _ = choose N K * K.factorial * (N - K).factorial := h1.symm
      _ = choose N K * (N - K) * (K.factorial * (N - 1 - K).factorial) := by
        rw [hNKfac]; ring

/-- Rising binomials at `p A` vs `A`:
`C(p A - 1, p B) / C(A - 1, B) = C(p A, p B) / C(A, B)`. -/
lemma rising_ratio_eq_choose_ratio {p A B : ℕ} (hp : p.Prime)
    (hB : B ≤ A) (hA : 0 < A) :
    choose (p * A - 1) (p * B) * choose A B =
      choose (A - 1) B * choose (p * A) (p * B) := by
  have hN : 0 < p * A := mul_pos hp.pos hA
  have hK : p * B ≤ p * A := Nat.mul_le_mul_left p hB
  have h1 := choose_pred_mul hK hN
  have h2 := choose_pred_mul hB hA
  have hpAB : p * A - p * B = p * (A - B) := (Nat.mul_sub p A B).symm
  rw [hpAB] at h1
  -- C(pA-1, pB) * p * A = C(pA, pB) * p * (A-B)
  -- cancel p: C(pA-1, pB) * A = C(pA, pB) * (A-B)
  have hp0 : p ≠ 0 := hp.ne_zero
  have h1' : choose (p * A - 1) (p * B) * A = choose (p * A) (p * B) * (A - B) := by
    apply mul_left_cancel₀ hp0
    calc
      p * (choose (p * A - 1) (p * B) * A) =
        choose (p * A - 1) (p * B) * (p * A) := by ring
      _ = choose (p * A) (p * B) * (p * (A - B)) := h1
      _ = p * (choose (p * A) (p * B) * (A - B)) := by ring
  have posA : A ≠ 0 := ne_zero_of_lt hA
  apply mul_right_cancel₀ posA
  calc
    choose (p * A - 1) (p * B) * choose A B * A =
      choose A B * (choose (p * A - 1) (p * B) * A) := by ring
    _ = choose A B * (choose (p * A) (p * B) * (A - B)) := by rw [h1']
    _ = choose (p * A) (p * B) * (choose A B * (A - B)) := by ring
    _ = choose (p * A) (p * B) * (choose (A - 1) B * A) := by rw [← h2]
    _ = choose (A - 1) B * choose (p * A) (p * B) * A := by ring

/-! ### Congruences for the binomial ratio -/

lemma prod_add_mod (s : Finset ℕ) (f : ℕ → ℕ) (N : ℕ) :
    ∏ i ∈ s, (f i + N) ≡ ∏ i ∈ s, f i [MOD N] := by
  refine Nat.ModEq.prod ?_
  intro i hi
  have : N + f i ≡ f i [MOD N] := by
    simpa using (Nat.ModEq.modulus_mul_add (m := N) (a := 1) (b := f i))
  simpa [add_comm] using this

lemma prod_prod_add_mod (s t : Finset ℕ) (f : ℕ → ℕ → ℕ) (N : ℕ) :
    ∏ i ∈ s, ∏ j ∈ t, (f i j + N) ≡ ∏ i ∈ s, ∏ j ∈ t, f i j [MOD N] := by
  refine Nat.ModEq.prod ?_
  intro i hi
  exact prod_add_mod t (f i) N

lemma choose_mul_pProd_mod {p A B : ℕ} (hp : p.Prime) (hBA : B ≤ A) :
    choose (p * A) (p * B) * pProd p B ≡
      choose A B * pProd p B [MOD (p * (A - B))] := by
  have hrat := choose_ratio_pProd (p := p) (A := A) (B := B) hp hBA
  have hPdef : pProd p B = ∏ s ∈ Icc 1 (p - 1), ∏ j ∈ Icc 1 B, (p * j - s) := rfl
  have hmod : ∏ s ∈ Icc 1 (p - 1), ∏ j ∈ Icc 1 B, (p * j - s + p * (A - B)) ≡
      pProd p B [MOD (p * (A - B))] := by
    simpa [hPdef] using
      (prod_prod_add_mod (Icc 1 (p - 1)) (Icc 1 B) (fun s j => p * j - s) (p * (A - B)))
  rw [hrat]
  exact Nat.ModEq.mul (Nat.ModEq.refl _) hmod

lemma pProd_coprime_pow {p B k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    (pProd p B).Coprime (p ^ k) := by
  rw [Nat.coprime_pow_right_iff hk]
  exact ((Nat.coprime_or_dvd_of_prime hp _).resolve_right (p_not_dvd_pProd hp)).symm

lemma choose_prime_mul_mod_pow' {p A B : ℕ} (hp : p.Prime) (hBA : B ≤ A) :
    choose (p * A) (p * B) ≡ choose A B [MOD p ^ (1 + padicValNat p (A - B))] := by
  have hmul := choose_mul_pProd_mod hp hBA
  haveI : Fact p.Prime := ⟨hp⟩
  set N := p * (A - B)
  have hv : p ^ (1 + padicValNat p (A - B)) ∣ N := by
    change p ^ (1 + padicValNat p (A - B)) ∣ p * (A - B)
    by_cases h0 : A - B = 0
    · simp [h0]
    · have hmulv : padicValNat p (p * (A - B)) = 1 + padicValNat p (A - B) := by
        rw [padicValNat.mul (p := p) hp.ne_zero h0, padicValNat_self]
      exact (padicValNat_dvd_iff_le (mul_ne_zero hp.ne_zero h0)).mpr (le_of_eq hmulv.symm)
  have hmul' : choose (p * A) (p * B) * pProd p B ≡
      choose A B * pProd p B [MOD p ^ (1 + padicValNat p (A - B))] :=
    hmul.of_dvd hv
  have hkpos : 0 < 1 + padicValNat p (A - B) := Nat.add_pos_left Nat.one_pos _
  have hcop : (pProd p B).Coprime (p ^ (1 + padicValNat p (A - B))) :=
    pProd_coprime_pow hp hkpos
  exact Nat.ModEq.cancel_right_of_coprime (Nat.coprime_iff_gcd_eq_one.mp hcop.symm) hmul'

lemma choose_prime_mul_mod_pr {p r B : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hB : B ≤ p ^ (r - 1)) :
    choose (p * (p ^ (r - 1) + B)) (p * B) ≡
      choose (p ^ (r - 1) + B) B [MOD p ^ r] := by
  have hBA : B ≤ p ^ (r - 1) + B := Nat.le_add_left _ _
  have h := choose_prime_mul_mod_pow' (p := p) (A := p ^ (r - 1) + B) (B := B) hp hBA
  have hAB : p ^ (r - 1) + B - B = p ^ (r - 1) := Nat.add_sub_cancel _ _
  rw [hAB] at h
  haveI : Fact p.Prime := ⟨hp⟩
  have hv : padicValNat p (p ^ (r - 1)) = r - 1 := padicValNat.prime_pow (r - 1)
  rw [hv] at h
  have : 1 + (r - 1) = r := Nat.add_sub_cancel' hr
  rwa [this] at h

lemma pow_dvd_int_choose_sub {p r B : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hB : B ≤ p ^ (r - 1)) :
    (p : ℤ) ^ r ∣
      (choose (p * (p ^ (r - 1) + B)) (p * B) : ℤ) -
        choose (p ^ (r - 1) + B) B := by
  have h := choose_prime_mul_mod_pr hp hr hB
  have hZ : (choose (p * (p ^ (r - 1) + B)) (p * B) : ℤ) ≡
      (choose (p ^ (r - 1) + B) B : ℤ) [ZMOD (p ^ r : ℕ)] :=
    (Int.natCast_modEq_iff).mpr h
  have hdvd := (Int.modEq_iff_dvd).mp hZ
  -- p^r ∣ C(A,B) - C(pA,pB)
  have : ((p ^ r : ℕ) : ℤ) ∣
      -((choose (p ^ (r - 1) + B) B : ℤ) -
        choose (p * (p ^ (r - 1) + B)) (p * B)) :=
    dvd_neg.mpr hdvd
  simpa [neg_sub, Int.natCast_pow] using this

/-- Relate rising binomials to ordinary ones:
`rising (p^r) (p B) = C(p^r + p B - 1, p B)` and
`rising (p^{r-1}) B = C(p^{r-1} + B - 1, B)`. -/
lemma rising_eq_choose_pred (n k : ℕ) : rising n k = choose (n + k - 1) k := rfl

lemma rising_prime_eq {p r B : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    rising (p ^ r) (p * B) = choose (p * (p ^ (r - 1) + B) - 1) (p * B) := by
  unfold rising
  have hpow : p ^ r = p * p ^ (r - 1) := (prime_mul_pow_pred hr).symm
  have : p ^ r + p * B - 1 = p * (p ^ (r - 1) + B) - 1 := by
    rw [hpow, mul_add]
  rw [this]

lemma risingY_dvd_eq {p r B : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    risingY p r (p * B) = choose (p ^ (r - 1) + B - 1) B := by
  rw [risingY_of_dvd (dvd_mul_right p B), rising]
  have : p * B / p = B := Nat.mul_div_cancel_left B hp.pos
  rw [this]

/-- `(C(pA-1, pB) - C(A-1, B)) * A = (C(pA, pB) - C(A, B)) * ↑(A - B)`. -/
lemma rising_sub_mul_A {p A B : ℕ} (hp : p.Prime) (hBA : B ≤ A) (hA : 0 < A) :
    ((choose (p * A - 1) (p * B) : ℤ) - choose (A - 1) B) * (A : ℤ) =
      ((choose (p * A) (p * B) : ℤ) - choose A B) * (A - B : ℕ) := by
  have hN : 0 < p * A := mul_pos hp.pos hA
  have hK : p * B ≤ p * A := Nat.mul_le_mul_left p hBA
  have h1 := choose_pred_mul hK hN
  have h2 := choose_pred_mul hBA hA
  have hpAB : p * A - p * B = p * (A - B) := (Nat.mul_sub p A B).symm
  rw [hpAB] at h1
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h1Z : (choose (p * A - 1) (p * B) : ℤ) * (p * A : ℕ) =
      (choose (p * A) (p * B) : ℤ) * (p * (A - B) : ℕ) := by exact_mod_cast h1
  have h1' : (choose (p * A - 1) (p * B) : ℤ) * (A : ℤ) =
      (choose (p * A) (p * B) : ℤ) * (A - B : ℕ) := by
    apply mul_left_cancel₀ hp0
    push_cast at h1Z ⊢
    linear_combination h1Z
  have h2' : (choose (A - 1) B : ℤ) * (A : ℤ) =
      (choose A B : ℤ) * (A - B : ℕ) := by exact_mod_cast h2
  linear_combination h1' - h2'

/-- `p^r` divides `rising(p^r, pB) - risingY` in ℤ, when `B ≤ p^{r-1}` and `p ≥ 3`. -/
lemma pow_dvd_int_rising_sub_of_dvd {p r B : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hr : 1 ≤ r) (hB : B ≤ p ^ (r - 1)) :
    (p : ℤ) ^ r ∣
      (rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B) := by
  rw [rising_prime_eq hp hr, risingY_dvd_eq hp hr]
  set A := p ^ (r - 1) + B
  have hA : 0 < A := by
    have : 1 ≤ p ^ (r - 1) := Nat.one_le_pow (r - 1) p hp.pos
    omega
  have hBA : B ≤ A := Nat.le_add_left _ _
  have hid := rising_sub_mul_A (p := p) (A := A) (B := B) hp hBA hA
  have hch := pow_dvd_int_choose_sub (p := p) (r := r) (B := B) hp hr hB
  have hAB : A - B = p ^ (r - 1) := Nat.add_sub_cancel _ _
  have hAlt : A < p ^ r := by
    have hle : A ≤ 2 * p ^ (r - 1) := by omega
    have hlt : 2 * p ^ (r - 1) < p * p ^ (r - 1) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos hp.pos _)
    have hpow : p * p ^ (r - 1) = p ^ r := prime_mul_pow_pred hr
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  have hδA :
      ((choose (p * A - 1) (p * B) : ℤ) - choose (A - 1) B) * (A : ℤ) =
        ((choose (p * A) (p * B) : ℤ) - choose A B) * (p ^ (r - 1) : ℕ) := by
    simpa [hAB] using hid
  have hR : (p : ℤ) ^ r * (p : ℤ) ^ (r - 1) ∣
      ((choose (p * A) (p * B) : ℤ) - choose A B) * (p ^ (r - 1) : ℕ) := by
    simpa [Int.natCast_pow] using mul_dvd_mul hch (dvd_refl (p ^ (r - 1) : ℤ))
  have hL : (p : ℤ) ^ r * (p : ℤ) ^ (r - 1) ∣
      ((choose (p * A - 1) (p * B) : ℤ) - choose (A - 1) B) * (A : ℤ) := by
    rw [hδA]
    simpa [A] using hR
  have hpow : (p : ℤ) ^ r * (p : ℤ) ^ (r - 1) = (p : ℤ) ^ (r + (r - 1)) := by
    rw [pow_add]
  rw [hpow] at hL
  have hsum : r + (r - 1) = 2 * r - 1 := by omega
  rw [hsum] at hL
  set δ : ℤ := (choose (p * A - 1) (p * B) : ℤ) - choose (A - 1) B
  change (p : ℤ) ^ (2 * r - 1) ∣ δ * (A : ℤ) at hL
  by_cases hδ0 : δ = 0
  · simp [hδ0]
  · have hAne : (A : ℤ) ≠ 0 := by exact_mod_cast (ne_zero_of_lt hA)
    have hvA : padicValInt p (A : ℤ) < r := by
      rw [padicValInt.of_nat]
      exact padicValNat_lt_of_lt_pow hA hAlt
    have hmulv : padicValInt p (δ * (A : ℤ)) = padicValInt p δ + padicValInt p (A : ℤ) :=
      padicValInt.mul (p := p) hδ0 hAne
    have hge : 2 * r - 1 ≤ padicValInt p (δ * (A : ℤ)) :=
      (padicValInt_dvd_iff (p := p) (2 * r - 1) (δ * (A : ℤ))).mp hL |>.resolve_left
        (mul_ne_zero hδ0 hAne)
    have : r ≤ padicValInt p δ := by omega
    exact (padicValInt_dvd_iff (p := p) r δ).mpr (Or.inr this)


/-! ### Unified divisibility `p^r ∣ b_k - y_k` -/

lemma pow_dvd_int_rising_sub_risingY {p r k : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hr : 1 ≤ r) (hk : k ≤ p ^ r) :
    (p : ℤ) ^ r ∣ (rising (p ^ r) k : ℤ) - risingY p r k := by
  by_cases hdv : p ∣ k
  · obtain ⟨B, rfl⟩ := hdv
    have hB : B ≤ p ^ (r - 1) := by
      have : p * B ≤ p * p ^ (r - 1) := by
        rw [prime_mul_pow_pred hr]; exact hk
      exact Nat.le_of_mul_le_mul_left this hp.pos
    exact pow_dvd_int_rising_sub_of_dvd hp hp3 hr hB
  · exact pow_dvd_int_rising_sub_risingY_not_dvd hp hr hk hdv

/-! ### Elementary Wolstenholme: `p ∣ H_{p-1}` in the sense of numerators -/

lemma harmonic_sum_mod_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∑ k ∈ Icc 1 (p - 1), (k : ZMod p)⁻¹ = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpair : ∀ k ∈ Icc 1 (p - 1),
      (k : ZMod p)⁻¹ + ((p - k : ℕ) : ZMod p)⁻¹ = 0 := by
    intro k hk
    have ⟨hk1, hk2⟩ := mem_Icc.mp hk
    have hklt : k < p := by omega
    have hpk : ((p - k : ℕ) : ZMod p) = - (k : ZMod p) := by
      rw [Nat.cast_sub (le_of_lt hklt), ZMod.natCast_self, zero_sub]
    rw [hpk, inv_neg]
    ring
  have hmap : ∀ k ∈ Icc 1 (p - 1), p - k ∈ Icc 1 (p - 1) :=
    fun k hk => mem_Icc_p_sub (le_of_lt hp.one_lt) hk
  have hsum :
      ∑ k ∈ Icc 1 (p - 1), (k : ZMod p)⁻¹ =
        ∑ k ∈ Icc 1 (p - 1), ((p - k : ℕ) : ZMod p)⁻¹ := by
    refine (Finset.sum_bij (fun k _ => p - k) (fun k hk => hmap k hk) ?_
      (fun s hs => ⟨p - s, hmap s hs, p_sub_p_sub hs (le_of_lt hp.one_lt)⟩) ?_).symm
    · intro a ha b hb heq
      have ⟨ha1, ha2⟩ := mem_Icc.mp ha
      have ⟨hb1, hb2⟩ := mem_Icc.mp hb
      have hps : p - a = p - b := heq
      omega
    · intro k hk; rfl
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
    rcases (Nat.dvd_prime Nat.prime_two).mp this with h1 | h2'
    · exact hp.ne_one h1
    · exact hp2 h2'
  have h2sum : (2 : ZMod p) * ∑ k ∈ Icc 1 (p - 1), (k : ZMod p)⁻¹ =
      ∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹ + ((p - k : ℕ) : ZMod p)⁻¹) := by
    calc
      (2 : ZMod p) * ∑ k ∈ Icc 1 (p - 1), (k : ZMod p)⁻¹ =
          ∑ k ∈ Icc 1 (p - 1), (k : ZMod p)⁻¹ +
            ∑ k ∈ Icc 1 (p - 1), (k : ZMod p)⁻¹ := by rw [two_mul]
      _ = ∑ k ∈ Icc 1 (p - 1), (k : ZMod p)⁻¹ +
            ∑ k ∈ Icc 1 (p - 1), ((p - k : ℕ) : ZMod p)⁻¹ := by rw [hsum]
      _ = ∑ k ∈ Icc 1 (p - 1),
            ((k : ZMod p)⁻¹ + ((p - k : ℕ) : ZMod p)⁻¹) := by
        rw [← sum_add_distrib]
  have hpairs : ∑ k ∈ Icc 1 (p - 1),
      ((k : ZMod p)⁻¹ + ((p - k : ℕ) : ZMod p)⁻¹) = 0 :=
    sum_eq_zero hpair
  rw [hpairs] at h2sum
  exact (_root_.mul_eq_zero.mp h2sum).resolve_left h2


/-! ### First-order expansion of `∏ (x_i + N)` -/

lemma prod_add_const_mod_sq {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℤ) (N : ℤ) :
    ∏ i ∈ s, (x i + N) ≡
      ∏ i ∈ s, x i + N * ∑ i ∈ s, ∏ j ∈ s.erase i, x j [ZMOD N ^ 2] := by
  induction s using Finset.induction_on with
  | empty =>
    simp
  | insert a s ha ih =>
    have hmul : ∏ i ∈ insert a s, (x i + N) = (x a + N) * ∏ i ∈ s, (x i + N) :=
      prod_insert ha
    rw [hmul]
    have ih' := Int.ModEq.mul (Int.ModEq.refl (x a + N)) ih
    have hstep : (x a + N) * (∏ i ∈ s, x i + N * ∑ i ∈ s, ∏ j ∈ s.erase i, x j) ≡
        ∏ i ∈ insert a s, x i + N * ∑ i ∈ insert a s, ∏ j ∈ (insert a s).erase i, x j
        [ZMOD N ^ 2] := by
      have hN2 : (N * N : ℤ) ≡ 0 [ZMOD N ^ 2] := by
        simp [pow_two, Int.modEq_iff_dvd]
      -- expand left: x_a * ∏s x + N * ∏s x + N * x_a * ∑ + N² * ∑
      have hexpand :
          (x a + N) * (∏ i ∈ s, x i + N * ∑ i ∈ s, ∏ j ∈ s.erase i, x j) =
            x a * ∏ i ∈ s, x i +
              N * (∏ i ∈ s, x i + x a * ∑ i ∈ s, ∏ j ∈ s.erase i, x j) +
              N * N * ∑ i ∈ s, ∏ j ∈ s.erase i, x j := by ring
      have hright :
          ∏ i ∈ insert a s, x i + N * ∑ i ∈ insert a s, ∏ j ∈ (insert a s).erase i, x j =
            x a * ∏ i ∈ s, x i +
              N * (∏ i ∈ s, x i + x a * ∑ i ∈ s, ∏ j ∈ s.erase i, x j) := by
        rw [prod_insert ha]
        have hsum : ∑ i ∈ insert a s, ∏ j ∈ (insert a s).erase i, x j =
            ∏ i ∈ s, x i + ∑ i ∈ s, x a * ∏ j ∈ s.erase i, x j := by
          rw [sum_insert ha, erase_insert ha]
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hne : i ≠ a := fun h => ha (h ▸ hi)
          rw [erase_insert_of_ne hne.symm, prod_insert (by
            simp [mem_erase, ha])]
        rw [hsum]
        simp [Finset.mul_sum]
      rw [hexpand, hright]
      have htail : N * N * ∑ i ∈ s, ∏ j ∈ s.erase i, x j ≡ 0 [ZMOD N ^ 2] := by
        simpa [pow_two] using
          (Int.ModEq.mul hN2 (Int.ModEq.refl (∑ i ∈ s, ∏ j ∈ s.erase i, x j)))
      have hleft := Int.ModEq.add_left
        (x a * ∏ i ∈ s, x i + N * (∏ i ∈ s, x i + x a * ∑ i ∈ s, ∏ j ∈ s.erase i, x j))
        htail
      simpa using hleft
    exact ih'.trans hstep


lemma pval_eq_neg {p s j : ℕ} (hp : p.Prime) (hs : s ∈ Icc 1 (p - 1))
    (hj : 1 ≤ j) :
    ((p * j - s : ℕ) : ZMod p) = - (s : ZMod p) := by
  have ⟨hs1, hs2⟩ := mem_Icc.mp hs
  have hs_lt : s < p := by omega
  have hle : s ≤ p * j :=
    le_trans (Nat.le_of_lt hs_lt) (Nat.le_mul_of_pos_right p hj)
  rw [Nat.cast_sub hle, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_sub]

lemma pval_ne_zero {p s j : ℕ} (hp : p.Prime) (hs : s ∈ Icc 1 (p - 1))
    (hj : 1 ≤ j) :
    ((p * j - s : ℕ) : ZMod p) ≠ 0 := by
  rw [pval_eq_neg hp hs hj]
  have ⟨hs1, hs2⟩ := mem_Icc.mp hs
  have hs_lt : s < p := by omega
  intro h
  have : (s : ZMod p) = 0 := by
    have := neg_eq_zero.mp h
    exact this
  have : p ∣ s := (ZMod.natCast_eq_zero_iff s p).mp this
  exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero (ne_zero_of_lt hs1)) hs_lt this

/-- The sum of inverse first-coordinates over the rectangle vanishes. -/
lemma sum_inv_fst_eq_zero {p B : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∑ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
      ((ij.1 : ZMod p)⁻¹) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Finset.sum_product]
  simp only [sum_const, nsmul_eq_mul]
  have hH := harmonic_sum_mod_prime hp hp2
  -- ∑_s ∑_j s⁻¹ = ∑_s (B * s⁻¹) = B * ∑ s⁻¹ = 0
  have : ∑ s ∈ Icc 1 (p - 1), ∑ _j ∈ Icc 1 B, (s : ZMod p)⁻¹ =
      ∑ s ∈ Icc 1 (p - 1), (B : ZMod p) * (s : ZMod p)⁻¹ := by
    refine Finset.sum_congr rfl ?_
    intro s hs
    simp [sum_const, nsmul_eq_mul]
  have hcard : ((#(Icc 1 B) : ZMod p) = (B : ZMod p)) := by
    simp [Nat.card_Icc]
  rw [hcard, ← mul_sum, hH, mul_zero]


/-! ### Rectangle product form of `pProd` and cofactor vanishing -/

lemma pProd_eq_prod_product (p B : ℕ) :
    pProd p B = ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B, (p * ij.2 - ij.1) := by
  unfold pProd
  rw [Finset.prod_product]

lemma pval_pos {p s j : ℕ} (hp : 1 ≤ p) (hs : s ∈ Icc 1 (p - 1)) (hj : 1 ≤ j) :
    0 < p * j - s := by
  have ⟨hs1, hs2⟩ := mem_Icc.mp hs
  have hs_lt : s < p := by omega
  have : p ≤ p * j := Nat.le_mul_of_pos_right p hj
  omega

lemma pval_cast_eq {p B : ℕ} (hp : p.Prime)
    {ij : ℕ × ℕ} (hij : ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B) :
    ((p * ij.2 - ij.1 : ℕ) : ZMod p) = - (ij.1 : ZMod p) := by
  have hij' := mem_product.mp hij
  have ⟨hj1, _⟩ := mem_Icc.mp hij'.2
  exact pval_eq_neg hp hij'.1 hj1

lemma fst_cast_ne_zero {p B : ℕ} (hp : p.Prime)
    {ij : ℕ × ℕ} (hij : ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B) :
    (ij.1 : ZMod p) ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hs := (mem_product.mp hij).1
  have ⟨hs1, hs2⟩ := mem_Icc.mp hs
  have hs_lt : ij.1 < p := by omega
  intro h0
  have : p ∣ ij.1 := (ZMod.natCast_eq_zero_iff ij.1 p).mp h0
  exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero (ne_zero_of_lt hs1)) hs_lt this

lemma neg_fst_ne_zero {p B : ℕ} (hp : p.Prime)
    {ij : ℕ × ℕ} (hij : ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B) :
    (-(ij.1 : ZMod p)) ≠ 0 :=
  neg_ne_zero.mpr (fst_cast_ne_zero hp hij)

/-- Cofactors of the `pVal` product reduce to cofactors of `-s`. -/
lemma cofactor_mod_p {p B : ℕ} (hp : p.Prime)
    {ij : ℕ × ℕ} (hij : ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B) :
    ((∏ kl ∈ (Icc 1 (p - 1) ×ˢ Icc 1 B).erase ij, (p * kl.2 - kl.1 : ℕ)) : ZMod p) =
      ∏ kl ∈ (Icc 1 (p - 1) ×ˢ Icc 1 B).erase ij, (-(kl.1 : ZMod p)) := by
  refine Finset.prod_congr rfl ?_
  intro kl hkl
  exact pval_cast_eq hp (mem_of_mem_erase hkl)

/-- Sum of cofactors of `pProd` vanishes modulo `p`. -/
lemma sum_cofactor_eq_zero {p B : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (∑ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
      (∏ kl ∈ (Icc 1 (p - 1) ×ˢ Icc 1 B).erase ij,
        (p * kl.2 - kl.1 : ℕ) : ZMod p)) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set s : Finset (ℕ × ℕ) := Icc 1 (p - 1) ×ˢ Icc 1 B
  have hred :
      ∑ ij ∈ s,
        (∏ kl ∈ s.erase ij, (p * kl.2 - kl.1 : ℕ) : ZMod p) =
      ∑ ij ∈ s, ∏ kl ∈ s.erase ij, (-(kl.1 : ZMod p)) :=
    Finset.sum_congr rfl (fun ij hij => cofactor_mod_p hp hij)
  rw [hred]
  by_cases hempty : s = ∅
  · simp [hempty]
  · have hfactor :
        ∀ ij ∈ s,
          ∏ kl ∈ s.erase ij, (-(kl.1 : ZMod p)) =
            (∏ kl ∈ s, (-(kl.1 : ZMod p))) * (-(ij.1 : ZMod p))⁻¹ := by
      intro ij hij
      have hne0 := neg_fst_ne_zero hp hij
      have hmul := Finset.mul_prod_erase s (fun kl => (-(kl.1 : ZMod p))) hij
      calc
        ∏ kl ∈ s.erase ij, (-(kl.1 : ZMod p)) =
            (-(ij.1 : ZMod p))⁻¹ *
              ((-(ij.1 : ZMod p)) * ∏ kl ∈ s.erase ij, (-(kl.1 : ZMod p))) := by
          rw [← mul_assoc, inv_mul_cancel₀ hne0, one_mul]
        _ = (-(ij.1 : ZMod p))⁻¹ * ∏ kl ∈ s, (-(kl.1 : ZMod p)) := by
          rw [hmul]
        _ = (∏ kl ∈ s, (-(kl.1 : ZMod p))) * (-(ij.1 : ZMod p))⁻¹ := mul_comm _ _
    rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum]
    have hinvsum : ∑ ij ∈ s, (-(ij.1 : ZMod p))⁻¹ = 0 := by
      have h1 : ∑ ij ∈ s, (-(ij.1 : ZMod p))⁻¹ =
          ∑ ij ∈ s, -((ij.1 : ZMod p)⁻¹) :=
        Finset.sum_congr rfl (fun _ _ => inv_neg)
      rw [h1, Finset.sum_neg_distrib, sum_inv_fst_eq_zero hp hp2, neg_zero]
    rw [hinvsum, mul_zero]

lemma sum_cofactor_int_dvd {p B : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (p : ℤ) ∣
      ∑ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
        ∏ kl ∈ (Icc 1 (p - 1) ×ˢ Icc 1 B).erase ij, ((p * kl.2 - kl.1 : ℕ) : ℤ) := by
  have h := sum_cofactor_eq_zero (p := p) (B := B) hp hp2
  set Sℤ :=
    ∑ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
      ∏ kl ∈ (Icc 1 (p - 1) ×ˢ Icc 1 B).erase ij, ((p * kl.2 - kl.1 : ℕ) : ℤ)
  have hZ : (Sℤ : ZMod p) = 0 := by
    simp only [Sℤ, Int.cast_sum, Int.cast_prod, Int.cast_natCast]
    exact h
  exact (CharP.intCast_eq_zero_iff (ZMod p) p Sℤ).mp hZ

/-- Specialisation: `N = p^r`, cofactor sum divisible by `p`, `r ≥ 1`. -/
lemma prod_add_pow_of_cofactor {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℤ) {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hcof : (p : ℤ) ∣ ∑ i ∈ s, ∏ j ∈ s.erase i, x j) :
    ∏ i ∈ s, (x i + (p : ℤ) ^ r) ≡ ∏ i ∈ s, x i [ZMOD (p : ℤ) ^ (r + 1)] := by
  have hexp := prod_add_const_mod_sq (s := s) (x := x) (N := (p : ℤ) ^ r)
  have hN2 : ((p : ℤ) ^ r) ^ 2 = (p : ℤ) ^ (2 * r) := by
    rw [← pow_mul, mul_comm]
  have hdvdN2 :
      (p : ℤ) ^ (2 * r) ∣
        (∏ i ∈ s, x i + (p : ℤ) ^ r * ∑ i ∈ s, ∏ j ∈ s.erase i, x j -
          ∏ i ∈ s, (x i + (p : ℤ) ^ r)) := by
    have := (Int.modEq_iff_dvd).mp hexp
    simpa [hN2] using this
  obtain ⟨K, hK⟩ := hdvdN2
  have hdecomp :
      ∏ i ∈ s, (x i + (p : ℤ) ^ r) - ∏ i ∈ s, x i =
        (p : ℤ) ^ r * ∑ i ∈ s, ∏ j ∈ s.erase i, x j - (p : ℤ) ^ (2 * r) * K := by
    linear_combination -hK
  obtain ⟨c, hc⟩ := hcof
  have hr2 : r + 1 ≤ 2 * r := by omega
  have hpow : (p : ℤ) ^ (2 * r) = (p : ℤ) ^ (r + 1) * (p : ℤ) ^ (2 * r - (r + 1)) := by
    rw [← pow_add, Nat.add_sub_cancel' hr2]
  have hdiff :
      ∏ i ∈ s, (x i + (p : ℤ) ^ r) - ∏ i ∈ s, x i =
        (p : ℤ) ^ (r + 1) * (c - (p : ℤ) ^ (2 * r - (r + 1)) * K) := by
    rw [hdecomp, hc, hpow]
    ring
  refine (Int.modEq_iff_dvd).mpr ?_
  refine ⟨-(c - (p : ℤ) ^ (2 * r - (r + 1)) * K), ?_⟩
  linear_combination -hdiff

/-! ### Upgrade of the binomial congruence to `p^{r+1}` -/

lemma choose_prime_mul_mod_pr_succ {p r B : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : 1 ≤ r) (hB : B ≤ p ^ (r - 1)) :
    choose (p * (p ^ (r - 1) + B)) (p * B) ≡
      choose (p ^ (r - 1) + B) B [MOD p ^ (r + 1)] := by
  have hBA : B ≤ p ^ (r - 1) + B := Nat.le_add_left _ _
  have hrat := choose_ratio_pProd (p := p) (A := p ^ (r - 1) + B) (B := B) hp hBA
  have hAB : p ^ (r - 1) + B - B = p ^ (r - 1) := Nat.add_sub_cancel _ _
  rw [hAB] at hrat
  have hpowN : p * p ^ (r - 1) = p ^ r := prime_mul_pow_pred hr
  set s : Finset (ℕ × ℕ) := Icc 1 (p - 1) ×ˢ Icc 1 B
  set x : ℕ × ℕ → ℤ := fun ij => ((p * ij.2 - ij.1 : ℕ) : ℤ)
  have hcof := sum_cofactor_int_dvd (p := p) (B := B) hp hp2
  have hprod :=
    prod_add_pow_of_cofactor (s := s) (x := x) (p := p) (r := r) hp hr hcof
  have hxN : ∏ ij ∈ s, x ij = ((pProd p B : ℕ) : ℤ) := by
    simp only [s, x, pProd_eq_prod_product, Nat.cast_prod]
  have hshift :
      ∏ s' ∈ Icc 1 (p - 1), ∏ j ∈ Icc 1 B, (p * j - s' + p * p ^ (r - 1)) =
        ∏ ij ∈ s, (p * ij.2 - ij.1 + p ^ r) := by
    simp only [s, hpowN]
    rw [Finset.prod_product]
  have hrat' :
      choose (p * (p ^ (r - 1) + B)) (p * B) * pProd p B =
        choose (p ^ (r - 1) + B) B *
          ∏ ij ∈ s, (p * ij.2 - ij.1 + p ^ r) := by
    rwa [hshift] at hrat
  have hratZ :
      (choose (p * (p ^ (r - 1) + B)) (p * B) : ℤ) * (pProd p B : ℤ) =
        (choose (p ^ (r - 1) + B) B : ℤ) *
          (∏ ij ∈ s, (p * ij.2 - ij.1 + p ^ r) : ℕ) := by
    exact_mod_cast hrat'
  have hQmod :
      ((∏ ij ∈ s, (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) ≡
        (pProd p B : ℤ) [ZMOD (p : ℤ) ^ (r + 1)] := by
    have : ∏ ij ∈ s, (x ij + (p : ℤ) ^ r) =
        ((∏ ij ∈ s, (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) := by
      simp only [x, Nat.cast_prod, Nat.cast_add, Nat.cast_pow, Nat.cast_mul]
    simpa [this, hxN] using hprod
  have hmul :
      (choose (p * (p ^ (r - 1) + B)) (p * B) : ℤ) * pProd p B ≡
        (choose (p ^ (r - 1) + B) B : ℤ) * pProd p B
        [ZMOD (p : ℤ) ^ (r + 1)] := by
    rw [hratZ]
    exact Int.ModEq.mul (Int.ModEq.refl _) hQmod
  haveI : Fact p.Prime := ⟨hp⟩
  have hkpos : 0 < r + 1 := Nat.succ_pos _
  have hcop : (pProd p B).Coprime (p ^ (r + 1)) := pProd_coprime_pow hp hkpos
  have hmulN' :
      choose (p * (p ^ (r - 1) + B)) (p * B) * pProd p B ≡
        choose (p ^ (r - 1) + B) B * pProd p B [MOD p ^ (r + 1)] :=
    (Int.natCast_modEq_iff (n := p ^ (r + 1))).mp (by
      simpa [Int.natCast_pow, Int.natCast_mul] using hmul)
  exact Nat.ModEq.cancel_right_of_coprime (Nat.coprime_iff_gcd_eq_one.mp hcop.symm) hmulN'

lemma pow_dvd_int_choose_sub_succ {p r B : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : 1 ≤ r) (hB : B ≤ p ^ (r - 1)) :
    (p : ℤ) ^ (r + 1) ∣
      (choose (p * (p ^ (r - 1) + B)) (p * B) : ℤ) -
        choose (p ^ (r - 1) + B) B := by
  have h := choose_prime_mul_mod_pr_succ hp hp2 hr hB
  have hZ : (choose (p * (p ^ (r - 1) + B)) (p * B) : ℤ) ≡
      (choose (p ^ (r - 1) + B) B : ℤ) [ZMOD (p ^ (r + 1) : ℕ)] :=
    (Int.natCast_modEq_iff).mpr h
  have hdvd := (Int.modEq_iff_dvd).mp hZ
  have : ((p ^ (r + 1) : ℕ) : ℤ) ∣
      -((choose (p ^ (r - 1) + B) B : ℤ) -
        choose (p * (p ^ (r - 1) + B)) (p * B)) :=
    dvd_neg.mpr hdvd
  simpa [neg_sub, Int.natCast_pow] using this

/-- Integer identity: `b * P = y * Q`. -/
lemma rising_mul_pProd {p r B : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hB : B ≤ p ^ (r - 1)) :
    rising (p ^ r) (p * B) * pProd p B =
      risingY p r (p * B) *
        ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B, (p * ij.2 - ij.1 + p ^ r) := by
  rw [rising_prime_eq hp hr, risingY_dvd_eq hp hr]
  set A := p ^ (r - 1) + B
  have hA : 0 < A := by
    have : 1 ≤ p ^ (r - 1) := Nat.one_le_pow (r - 1) p hp.pos
    omega
  have hBA : B ≤ A := Nat.le_add_left _ _
  have h1 := rising_ratio_eq_choose_ratio (p := p) (A := A) (B := B) hp hBA hA
  have h2 := choose_ratio_pProd (p := p) (A := A) (B := B) hp hBA
  have hAB : A - B = p ^ (r - 1) := Nat.add_sub_cancel _ _
  rw [hAB] at h2
  have hpow : p * p ^ (r - 1) = p ^ r := prime_mul_pow_pred hr
  have hQ :
      ∏ s ∈ Icc 1 (p - 1), ∏ j ∈ Icc 1 B, (p * j - s + p * p ^ (r - 1)) =
        ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B, (p * ij.2 - ij.1 + p ^ r) := by
    rw [Finset.prod_product, hpow]
  rw [hQ] at h2
  -- C(pA-1,pB) * C(A,B) = C(A-1,B) * C(pA,pB)
  -- C(pA,pB) * P = C(A,B) * Q
  -- hence C(pA-1,pB) * P * C(A,B) = C(A-1,B) * C(A,B) * Q
  have hCpos : 0 < choose A B := choose_pos hBA
  have hmul :
      choose (p * A - 1) (p * B) * choose A B * pProd p B =
        choose (A - 1) B * choose A B *
          ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B, (p * ij.2 - ij.1 + p ^ r) := by
    calc
      choose (p * A - 1) (p * B) * choose A B * pProd p B =
          choose (A - 1) B * (choose (p * A) (p * B) * pProd p B) := by
        rw [h1]; ring
      _ = choose (A - 1) B * (choose A B *
            ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B, (p * ij.2 - ij.1 + p ^ r)) := by
        rw [h2]
      _ = choose (A - 1) B * choose A B *
            ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B, (p * ij.2 - ij.1 + p ^ r) := by
        ring
  have hmul' :
      choose A B * (choose (p * A - 1) (p * B) * pProd p B) =
        choose A B * (choose (A - 1) B *
          ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B, (p * ij.2 - ij.1 + p ^ r)) := by
    convert hmul using 1 <;> ring
  exact mul_left_cancel₀ (Nat.ne_zero_of_lt hCpos) hmul'

/-- `δ * P = y * (Q - P)` as an integer identity. -/
lemma rising_sub_mul_pProd {p r B : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hB : B ≤ p ^ (r - 1)) :
    ((rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B)) * (pProd p B : ℤ) =
      (risingY p r (p * B) : ℤ) *
        (((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
            (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) - pProd p B) := by
  have h := rising_mul_pProd hp hr hB
  have hZ := congrArg (fun n : ℕ => (n : ℤ)) h
  push_cast at hZ
  have hprod :
      ((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
          (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) =
        ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
          (((p * ij.2 - ij.1 : ℕ) : ℤ) + (p : ℤ) ^ r) := by
    simp [Nat.cast_prod, Nat.cast_add, Nat.cast_pow]
  rw [hprod]
  linear_combination hZ

/-- Upgraded divisibility: `p^{r+1}` divides `δ` after accounting for `A`. -/
lemma pow_dvd_int_rising_sub_of_dvd_succ {p r B : ℕ} (hp : p.Prime)
    (hp3 : 3 ≤ p) (hr : 1 ≤ r) (hB : B ≤ p ^ (r - 1)) :
    (p : ℤ) ^ (r + 1) ∣
      (rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B) := by
  have hp2 : p ≠ 2 := by omega
  rw [rising_prime_eq hp hr, risingY_dvd_eq hp hr]
  set A := p ^ (r - 1) + B
  have hA : 0 < A := by
    have : 1 ≤ p ^ (r - 1) := Nat.one_le_pow (r - 1) p hp.pos
    omega
  have hBA : B ≤ A := Nat.le_add_left _ _
  have hid := rising_sub_mul_A (p := p) (A := A) (B := B) hp hBA hA
  have hch := pow_dvd_int_choose_sub_succ (p := p) (r := r) (B := B) hp hp2 hr hB
  have hAB : A - B = p ^ (r - 1) := Nat.add_sub_cancel _ _
  have hAlt : A < p ^ r := by
    have hle : A ≤ 2 * p ^ (r - 1) := by omega
    have hlt : 2 * p ^ (r - 1) < p * p ^ (r - 1) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos hp.pos _)
    have hpow : p * p ^ (r - 1) = p ^ r := prime_mul_pow_pred hr
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  have hδA :
      ((choose (p * A - 1) (p * B) : ℤ) - choose (A - 1) B) * (A : ℤ) =
        ((choose (p * A) (p * B) : ℤ) - choose A B) * (p ^ (r - 1) : ℕ) := by
    simpa [hAB] using hid
  have hR : (p : ℤ) ^ (r + 1) * (p : ℤ) ^ (r - 1) ∣
      ((choose (p * A) (p * B) : ℤ) - choose A B) * (p ^ (r - 1) : ℕ) := by
    simpa [Int.natCast_pow] using mul_dvd_mul hch (dvd_refl (p ^ (r - 1) : ℤ))
  have hL : (p : ℤ) ^ (r + 1) * (p : ℤ) ^ (r - 1) ∣
      ((choose (p * A - 1) (p * B) : ℤ) - choose (A - 1) B) * (A : ℤ) := by
    rw [hδA]
    simpa [A] using hR
  have hpow : (p : ℤ) ^ (r + 1) * (p : ℤ) ^ (r - 1) = (p : ℤ) ^ (r + 1 + (r - 1)) := by
    rw [← pow_add]
  rw [hpow] at hL
  have hsum : r + 1 + (r - 1) = 2 * r := by omega
  rw [hsum] at hL
  set δ : ℤ := (choose (p * A - 1) (p * B) : ℤ) - choose (A - 1) B
  change (p : ℤ) ^ (2 * r) ∣ δ * (A : ℤ) at hL
  by_cases hδ0 : δ = 0
  · simp [hδ0]
  · have hAne : (A : ℤ) ≠ 0 := by exact_mod_cast (ne_zero_of_lt hA)
    have hvA : padicValInt p (A : ℤ) < r := by
      rw [padicValInt.of_nat]
      exact padicValNat_lt_of_lt_pow hA hAlt
    have hmulv : padicValInt p (δ * (A : ℤ)) = padicValInt p δ + padicValInt p (A : ℤ) :=
      padicValInt.mul (p := p) hδ0 hAne
    have hge : 2 * r ≤ padicValInt p (δ * (A : ℤ)) :=
      (padicValInt_dvd_iff (p := p) (2 * r) (δ * (A : ℤ))).mp hL |>.resolve_left
        (mul_ne_zero hδ0 hAne)
    have : r + 1 ≤ padicValInt p δ := by omega
    exact (padicValInt_dvd_iff (p := p) (r + 1) δ).mpr (Or.inr this)

/-! ### Wolstenholme: `∑_{k=1}^{p-1} k⁻¹ = 0` in `ZMod (p^2)` for `p ≥ 5` -/

lemma pfree_eq_Icc {p : ℕ} (hp : p.Prime) :
    pfree p 1 = Icc 1 (p - 1) := by
  ext k
  simp only [mem_pfree, pow_one, mem_Icc]
  constructor
  · intro ⟨hklt, hnd⟩
    have hk0 : 0 < k := Nat.pos_of_ne_zero (fun h => hnd (by simp [h]))
    exact ⟨hk0, Nat.le_pred_of_lt hklt⟩
  · intro ⟨hk0, hk1⟩
    have hklt : k < p := by omega
    refine ⟨hklt, ?_⟩
    exact Nat.not_dvd_of_pos_of_lt hk0 hklt

lemma sum_Icc_pow_eq_zero {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiv : ¬ (p - 1) ∣ m) :
    (∑ k ∈ Icc 1 (p - 1), (k : ZMod p) ^ m) = 0 := by
  have h := sum_pfree_zmod_pow_eq_zero (p := p) (r := 1) (m := m) hp hp2
    (Nat.succ_pos 0) hdiv
  rw [pfree_eq_Icc hp, pow_one] at h
  exact h

lemma Icc_cast_ne_zero {p k : ℕ} (hp : p.Prime) (hk : k ∈ Icc 1 (p - 1)) :
    (k : ZMod p) ≠ 0 := by
  have ⟨hk1, hk2⟩ := mem_Icc.mp hk
  have hklt : k < p := by omega
  intro h0
  have : p ∣ k := (ZMod.natCast_eq_zero_iff k p).mp h0
  exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero (ne_zero_of_lt hk1)) hklt this

lemma sum_inv_sq_mod_prime {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hpow : ∀ k ∈ Icc 1 (p - 1),
      ((k : ZMod p)⁻¹) ^ 2 = (k : ZMod p) ^ (p - 3) := by
    intro k hk
    have hne := Icc_cast_ne_zero hp hk
    have hfermat : (k : ZMod p) ^ (p - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one hne
    have hsub : p - 3 + 2 = p - 1 := by omega
    have hmul : (k : ZMod p) ^ (p - 3) * (k : ZMod p) ^ 2 = 1 := by
      rw [← pow_add, hsub, hfermat]
    have : (k : ZMod p) ^ (p - 3) = ((k : ZMod p) ^ 2)⁻¹ :=
      eq_inv_of_mul_eq_one_left hmul
    rw [this, inv_pow]
  rw [Finset.sum_congr rfl hpow]
  have hdiv : ¬ (p - 1) ∣ (p - 3) := by
    intro h
    have h2 : p - 1 ∣ 2 := by
      have : p - 1 - (p - 3) = 2 := by omega
      have hd := Nat.dvd_sub (dvd_refl (p - 1)) h
      simpa [this] using hd
    have : p - 1 ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    omega
  exact sum_Icc_pow_eq_zero hp hp2 hdiv


lemma two_ne_zero_zmod_pow {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n) :
    (2 : ZMod (p ^ n)) ≠ 0 := by
  intro h
  have : p ^ n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (p ^ n)).mp (by simpa using h)
  have hle : p ^ n ≤ 2 := Nat.le_of_dvd (by norm_num) this
  have : p = 2 := by
    have hge : 2 ≤ p := hp.two_le
    have hple : p ≤ 2 := le_trans (Nat.le_self_pow (ne_zero_of_lt hn) p) hle
    omega
  exact hp2 this

lemma Icc_cast_unit_pow {p n k : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hk : k ∈ Icc 1 (p - 1)) :
    IsUnit (k : ZMod (p ^ n)) := by
  have ⟨hk1, hk2⟩ := mem_Icc.mp hk
  have hklt : k < p := by omega
  rw [ZMod.isUnit_iff_coprime]
  have hnd : ¬ p ∣ k :=
    Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero (ne_zero_of_lt hk1)) hklt
  exact coprime_of_not_dvd_prime_pow hp hn hnd

lemma unit_mul_inv {n : ℕ} {a : ZMod n} (h : IsUnit a) : a * a⁻¹ = 1 :=
  ZMod.mul_inv_of_unit a h

lemma unit_inv_mul {n : ℕ} {a : ZMod n} (h : IsUnit a) : a⁻¹ * a = 1 :=
  ZMod.inv_mul_of_unit a h

lemma castHom_inv_Icc {p n k : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hk : k ∈ Icc 1 (p - 1)) :
    ZMod.castHom (dvd_pow_self p (ne_zero_of_lt hn)) (ZMod p)
        ((k : ZMod (p ^ n))⁻¹) =
      (k : ZMod p)⁻¹ := by
  haveI : Fact p.Prime := ⟨hp⟩
  let π := ZMod.castHom (dvd_pow_self p (ne_zero_of_lt hn)) (ZMod p)
  have hπk : π (k : ZMod (p ^ n)) = (k : ZMod p) := by
    simp [π, ZMod.castHom_apply]
  have hu := Icc_cast_unit_pow (n := n) hp hn hk
  have hmul : (k : ZMod p) * π ((k : ZMod (p ^ n))⁻¹) = 1 := by
    rw [← hπk, ← map_mul, unit_mul_inv hu, map_one]
  have hinv : (k : ZMod p)⁻¹ = π ((k : ZMod (p ^ n))⁻¹) :=
    ZMod.inv_eq_of_mul_eq_one p _ _ hmul
  simpa [π] using hinv.symm

lemma p_pow_sq_eq_zero (p : ℕ) : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
  have h : ((p ^ 2 : ℕ) : ZMod (p ^ 2)) = 0 := ZMod.natCast_self (p ^ 2)
  have hmul : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = ((p ^ 2 : ℕ) : ZMod (p ^ 2)) := by
    rw [← Nat.cast_mul, pow_two]
  rw [pow_two (p : ZMod (p ^ 2)), hmul, h]

lemma isUnit_one_add_p_mul {p : ℕ} (hp : p.Prime) (c : ZMod (p ^ 2)) :
    IsUnit (1 + (p : ZMod (p ^ 2)) * c) := by
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hnd : ¬ p ∣ (1 + (p : ZMod (p ^ 2)) * c).val := by
    intro hd
    have hval0 : ((1 + (p : ZMod (p ^ 2)) * c).val : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ p).mpr hd
    have hcast :
        ZMod.castHom (dvd_pow_self p (by decide : (2 : ℕ) ≠ 0)) (ZMod p)
          (1 + (p : ZMod (p ^ 2)) * c) = 0 := by
      rw [ZMod.castHom_apply, ← ZMod.natCast_val]
      exact hval0
    have h1 : ZMod.castHom (dvd_pow_self p (by decide : (2 : ℕ) ≠ 0)) (ZMod p)
        (1 + (p : ZMod (p ^ 2)) * c) = 1 := by
      simp [map_add, map_one, map_mul, ZMod.castHom_apply]
    have h10 : (1 : ZMod p) = 0 := h1.symm.trans hcast
    have : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).mp (by simpa using h10)
    exact hp.ne_one (Nat.eq_one_of_dvd_one this)
  exact (isUnit_iff_not_dvd_val hp (by decide : (0 : ℕ) < 2) _).mpr hnd

lemma inv_one_add_p_mul {p : ℕ} (hp : p.Prime) (c : ZMod (p ^ 2)) :
    (1 + (p : ZMod (p ^ 2)) * c)⁻¹ = 1 - (p : ZMod (p ^ 2)) * c := by
  have hmul : (1 + (p : ZMod (p ^ 2)) * c) * (1 - (p : ZMod (p ^ 2)) * c) = 1 := by
    have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := p_pow_sq_eq_zero p
    have : (1 + (p : ZMod (p ^ 2)) * c) * (1 - (p : ZMod (p ^ 2)) * c) =
        1 - ((p : ZMod (p ^ 2)) * c) ^ 2 := by ring
    rw [this, mul_pow, hp2, zero_mul, sub_zero]
  exact (ZMod.inv_eq_of_mul_eq_one (p ^ 2) _ _ hmul)


lemma inv_add_p_mul {p : ℕ} (hp : p.Prime) {a b : ZMod (p ^ 2)}
    (ha : IsUnit a) :
    (a + (p : ZMod (p ^ 2)) * b)⁻¹ =
      a⁻¹ - (p : ZMod (p ^ 2)) * b * (a⁻¹) ^ 2 := by
  have hfac : a + (p : ZMod (p ^ 2)) * b =
      a * (1 + (p : ZMod (p ^ 2)) * (b * a⁻¹)) := by
    have hua := unit_mul_inv ha
    calc
      a + (p : ZMod (p ^ 2)) * b =
          a * 1 + (p : ZMod (p ^ 2)) * (b * 1) := by simp
      _ = a * 1 + (p : ZMod (p ^ 2)) * (b * (a * a⁻¹)) := by rw [hua]
      _ = a * (1 + (p : ZMod (p ^ 2)) * (b * a⁻¹)) := by ring
  have hu : IsUnit (a + (p : ZMod (p ^ 2)) * b) := by
    rw [hfac]
    exact ha.mul (isUnit_one_add_p_mul hp (b * a⁻¹))
  rw [hfac]
  have hmul_inv :
      (a * (1 + (p : ZMod (p ^ 2)) * (b * a⁻¹)))⁻¹ =
        (1 + (p : ZMod (p ^ 2)) * (b * a⁻¹))⁻¹ * a⁻¹ := by
    have h1 := unit_mul_inv (ha.mul (isUnit_one_add_p_mul hp (b * a⁻¹)))
    have h2 := unit_mul_inv (isUnit_one_add_p_mul hp (b * a⁻¹))
    have h3 := unit_mul_inv ha
    -- (xy)⁻¹ = y⁻¹ x⁻¹ because (xy)(y⁻¹ x⁻¹) = 1
    apply ZMod.inv_eq_of_mul_eq_one
    calc
      (a * (1 + (p : ZMod (p ^ 2)) * (b * a⁻¹))) *
          ((1 + (p : ZMod (p ^ 2)) * (b * a⁻¹))⁻¹ * a⁻¹) =
        a * (((1 + (p : ZMod (p ^ 2)) * (b * a⁻¹)) *
          (1 + (p : ZMod (p ^ 2)) * (b * a⁻¹))⁻¹) * a⁻¹) := by ring
      _ = a * (1 * a⁻¹) := by rw [unit_mul_inv (isUnit_one_add_p_mul hp (b * a⁻¹))]
      _ = 1 := by rw [one_mul, unit_mul_inv ha]
  rw [hmul_inv, inv_one_add_p_mul hp]
  ring

lemma pair_inv_sum {p k : ℕ} (hp : p.Prime) (hk : k ∈ Icc 1 (p - 1)) :
    (k : ZMod (p ^ 2))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ =
      (p : ZMod (p ^ 2)) *
        ((k : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) - k))⁻¹ := by
  have ⟨hk1, hk2⟩ := mem_Icc.mp hk
  have hklt : k < p := by omega
  have hpk : ((p - k : ℕ) : ZMod (p ^ 2)) =
      (p : ZMod (p ^ 2)) - (k : ZMod (p ^ 2)) :=
    Nat.cast_sub (le_of_lt hklt)
  have hu := Icc_cast_unit_pow (n := 2) hp (by decide) hk
  have hmem : p - k ∈ Icc 1 (p - 1) := mem_Icc_p_sub (le_of_lt hp.one_lt) hk
  have hup := Icc_cast_unit_pow (n := 2) hp (by decide) hmem
  have hsum : (k : ZMod (p ^ 2)) + ((p - k : ℕ) : ZMod (p ^ 2)) =
      (p : ZMod (p ^ 2)) := by
    rw [hpk]; ring
  have hxy :
      ((k : ZMod (p ^ 2))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 2))⁻¹) *
        ((k : ZMod (p ^ 2)) * ((p - k : ℕ) : ZMod (p ^ 2))) =
        (p : ZMod (p ^ 2)) := by
    have hx : (k : ZMod (p ^ 2))⁻¹ * ((k : ZMod (p ^ 2)) *
        ((p - k : ℕ) : ZMod (p ^ 2))) = ((p - k : ℕ) : ZMod (p ^ 2)) := by
      rw [← mul_assoc, unit_inv_mul hu, one_mul]
    have hy : ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ *
        ((k : ZMod (p ^ 2)) * ((p - k : ℕ) : ZMod (p ^ 2))) =
        (k : ZMod (p ^ 2)) := by
      rw [mul_left_comm, unit_inv_mul hup, mul_one]
    rw [add_mul, hx, hy, add_comm, hsum]
  have huprod : IsUnit ((k : ZMod (p ^ 2)) * ((p - k : ℕ) : ZMod (p ^ 2))) :=
    hu.mul hup
  have hfinal :
      (k : ZMod (p ^ 2))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ =
        (p : ZMod (p ^ 2)) *
          ((k : ZMod (p ^ 2)) * ((p - k : ℕ) : ZMod (p ^ 2)))⁻¹ := by
    have h :
        (((k : ZMod (p ^ 2))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 2))⁻¹) *
          ((k : ZMod (p ^ 2)) * ((p - k : ℕ) : ZMod (p ^ 2)))) *
            ((k : ZMod (p ^ 2)) * ((p - k : ℕ) : ZMod (p ^ 2)))⁻¹ =
          (p : ZMod (p ^ 2)) *
            ((k : ZMod (p ^ 2)) * ((p - k : ℕ) : ZMod (p ^ 2)))⁻¹ :=
      congrArg (fun z : ZMod (p ^ 2) =>
        z * ((k : ZMod (p ^ 2)) * ((p - k : ℕ) : ZMod (p ^ 2)))⁻¹) hxy
    rwa [mul_assoc, unit_mul_inv huprod, mul_one] at h
  rw [hpk]
  simpa [hpk] using hfinal

lemma pair_inv_wolstenholme {p k : ℕ} (hp : p.Prime) (hk : k ∈ Icc 1 (p - 1)) :
    (k : ZMod (p ^ 2))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ =
      - (p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 2 := by
  have hu := Icc_cast_unit_pow (n := 2) hp (by decide) hk
  have hsum := pair_inv_sum hp hk
  have ⟨hk1, hk2⟩ := mem_Icc.mp hk
  have hklt : k < p := by omega
  have hpk : ((p - k : ℕ) : ZMod (p ^ 2)) =
      (p : ZMod (p ^ 2)) - (k : ZMod (p ^ 2)) :=
    Nat.cast_sub (le_of_lt hklt)
  have hprod : (k : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) - k) =
      - ((k : ZMod (p ^ 2)) ^ 2) + (p : ZMod (p ^ 2)) * k := by ring
  have ha : IsUnit (-((k : ZMod (p ^ 2)) ^ 2)) := (hu.pow 2).neg
  have hinv := inv_add_p_mul (p := p) hp (a := -((k : ZMod (p ^ 2)) ^ 2))
    (b := (k : ZMod (p ^ 2))) ha
  have ha_inv : (-((k : ZMod (p ^ 2)) ^ 2))⁻¹ = - ((k : ZMod (p ^ 2))⁻¹) ^ 2 := by
    have hmul' : (-((k : ZMod (p ^ 2)) ^ 2)) * (- ((k : ZMod (p ^ 2))⁻¹) ^ 2) = 1 := by
      have hsq : (k : ZMod (p ^ 2)) ^ 2 * ((k : ZMod (p ^ 2))⁻¹) ^ 2 = 1 := by
        rw [← mul_pow, unit_mul_inv hu, one_pow]
      rw [neg_mul_neg]
      exact hsq
    exact ZMod.inv_eq_of_mul_eq_one (p ^ 2) _ _ hmul'
  have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := p_pow_sq_eq_zero p
  have : (p : ZMod (p ^ 2)) *
      ((k : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) - k))⁻¹ =
        - (p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 2 := by
    rw [hprod, hinv, ha_inv]
    -- p * ( -k^{-2} - p k (-k^{-2})² ) = -p k^{-2} - p² * ...
    have hexpand :
        (p : ZMod (p ^ 2)) *
          (- ((k : ZMod (p ^ 2))⁻¹) ^ 2 -
            (p : ZMod (p ^ 2)) * k * ((- ((k : ZMod (p ^ 2))⁻¹) ^ 2) ^ 2)) =
          - (p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 2 := by
      have htail :
          (p : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * k *
            ((- ((k : ZMod (p ^ 2))⁻¹) ^ 2) ^ 2)) = 0 := by
        calc
          (p : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * k *
              ((- ((k : ZMod (p ^ 2))⁻¹) ^ 2) ^ 2)) =
              ((p : ZMod (p ^ 2)) ^ 2) *
                (k * ((- ((k : ZMod (p ^ 2))⁻¹) ^ 2) ^ 2)) := by ring
          _ = 0 := by rw [hp2, zero_mul]
      linear_combination -htail
    exact hexpand
  rw [hsum]
  exact this


lemma sum_inv_sq_cast_zero {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ZMod.castHom (dvd_pow_self p (by decide : (2 : ℕ) ≠ 0)) (ZMod p)
      (∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [map_sum]
  have : ∑ k ∈ Icc 1 (p - 1),
      ZMod.castHom (dvd_pow_self p (by decide : (2 : ℕ) ≠ 0)) (ZMod p)
        (((k : ZMod (p ^ 2))⁻¹) ^ 2) =
      ∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [map_pow, castHom_inv_Icc hp (by decide) hk]
  rw [this, sum_inv_sq_mod_prime hp hp5]

lemma sum_inv_sq_is_p_mul {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∃ c : ZMod (p ^ 2),
      ∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2 =
        (p : ZMod (p ^ 2)) * c := by
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hπ := sum_inv_sq_cast_zero hp hp5
  have hval :
      ((∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2).val : ZMod p) = 0 := by
    have : ZMod.castHom (dvd_pow_self p (by decide : (2 : ℕ) ≠ 0)) (ZMod p)
        (∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2) =
      ((∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2).val : ZMod p) := by
      rw [ZMod.castHom_apply, ← ZMod.natCast_val]
    exact this.symm.trans hπ
  have hdvd : p ∣ (∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2).val :=
    (ZMod.natCast_eq_zero_iff _ p).mp hval
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨c, ?_⟩
  have hcoe :
      ∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2 =
        ((∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2).val : ZMod (p ^ 2)) :=
    (ZMod.natCast_zmod_val _).symm
  rw [hcoe, hc, Nat.cast_mul]

/-- Wolstenholme: `∑_{k=1}^{p-1} k⁻¹ = 0` in `ZMod (p^2)` for `p ≥ 5`. -/
lemma harmonic_sum_mod_prime_sq {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∑ k ∈ Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ = 0 := by
  have hp2ne : p ≠ 2 := by omega
  have h2 : (2 : ZMod (p ^ 2)) ≠ 0 := two_ne_zero_zmod_pow hp hp2ne (by decide)
  have hmap : ∀ k ∈ Icc 1 (p - 1), p - k ∈ Icc 1 (p - 1) :=
    fun k hk => mem_Icc_p_sub (le_of_lt hp.one_lt) hk
  have hreindex :
      ∑ k ∈ Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ =
        ∑ k ∈ Icc 1 (p - 1), ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ := by
    refine (Finset.sum_bij (fun k _ => p - k) (fun k hk => hmap k hk) ?_
      (fun s hs => ⟨p - s, hmap s hs, p_sub_p_sub hs (le_of_lt hp.one_lt)⟩)
      (fun k hk => rfl)).symm
    intro a ha b hb heq
    have ⟨ha1, ha2⟩ := mem_Icc.mp ha
    have ⟨hb1, hb2⟩ := mem_Icc.mp hb
    have hpeq : p - a = p - b := heq
    omega
  have h2sum :
      (2 : ZMod (p ^ 2)) * ∑ k ∈ Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ =
        ∑ k ∈ Icc 1 (p - 1),
          ((k : ZMod (p ^ 2))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 2))⁻¹) := by
    calc
      (2 : ZMod (p ^ 2)) * ∑ k ∈ Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ =
          ∑ k ∈ Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ +
            ∑ k ∈ Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ := by rw [two_mul]
      _ = ∑ k ∈ Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ +
            ∑ k ∈ Icc 1 (p - 1), ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ := by
        rw [hreindex]
      _ = ∑ k ∈ Icc 1 (p - 1),
            ((k : ZMod (p ^ 2))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 2))⁻¹) := by
        rw [← sum_add_distrib]
  have hcong := Finset.sum_congr rfl (fun k hk => pair_inv_wolstenholme hp hk)
  rw [hcong] at h2sum
  obtain ⟨c, hc⟩ := sum_inv_sq_is_p_mul hp hp5
  have : (2 : ZMod (p ^ 2)) * ∑ k ∈ Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ = 0 := by
    rw [h2sum, ← Finset.mul_sum, hc]
    have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := p_pow_sq_eq_zero p
    have : (p : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * c) = 0 := by
      calc
        (p : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * c) =
            ((p : ZMod (p ^ 2)) ^ 2) * c := by ring
        _ = 0 := by rw [hp2, zero_mul]
    rw [← mul_assoc]
    have : - (p : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * c) = 0 := by
      rw [neg_mul, this, neg_zero]
    -- h2sum after rewrites is ∑ -p * k^{-2} = -p * ∑ k^{-2} = -p * (p c)
    convert this using 1
    ring
  have h2u : IsUnit (2 : ZMod (p ^ 2)) := by
    have : IsUnit ((2 : ℕ) : ZMod (p ^ 2)) := by
      rw [ZMod.isUnit_iff_coprime]
      rw [Nat.coprime_pow_right_iff (by decide : 0 < 2)]
      exact (Nat.prime_two.coprime_iff_not_dvd).2 (by
        intro hd
        have : 2 = p := (Nat.dvd_prime hp).mp hd |>.resolve_left (by decide)
        exact hp2ne this.symm)
    exact this
  have hcancel := congrArg (fun z => (2 : ZMod (p ^ 2))⁻¹ * z) this
  simpa [← mul_assoc, unit_inv_mul h2u] using hcancel


/-! ### Valuation consequences of the upgraded congruence -/

lemma padicValInt_ge_of_pow_dvd {p n : ℕ} {a : ℤ} (hp : p.Prime)
    (hne : a ≠ 0) (h : (p : ℤ) ^ n ∣ a) : n ≤ padicValInt p a := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact (padicValInt_dvd_iff (p := p) n a).mp h |>.resolve_left hne

lemma pow_dvd_int_rising_sub_not_dvd {p r k : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hk : k ≤ p ^ r) (hdv : ¬ p ∣ k) :
    (p : ℤ) ^ r ∣ (rising (p ^ r) k : ℤ) := by
  simpa [risingY_of_not_dvd hdv, sub_zero] using
    (pow_dvd_int_rising_sub_risingY_not_dvd hp hr hk hdv)

/-- For `p ∤ k`, `v_p(b_k) = r` exactly (when `0 < k ≤ p^r`). -/
lemma padicValInt_rising_not_dvd {p r k : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hk0 : 0 < k) (hk : k ≤ p ^ r) (hdv : ¬ p ∣ k) :
    padicValInt p (rising (p ^ r) k : ℤ) = r := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hkn : k < p ^ r :=
    lt_of_le_of_ne hk (fun h => hdv (by rw [h]; exact dvd_pow_self p (ne_zero_of_lt hr)))
  have hval := padicValNat_rising_of_not_dvd (p := p) (r := r) (k := k) hk0 (le_of_lt hkn) hdv
  have hne : rising (p ^ r) k ≠ 0 := by
    unfold rising
    exact choose_ne_zero (by
      have : 1 ≤ p ^ r := Nat.one_le_pow r p hp.pos
      omega)
  rw [padicValInt.of_nat, hval]

lemma increment_dvd_of_val {p r k : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hr : 1 ≤ r) (hk : k ≤ p ^ r) :
    (p : ℤ) ^ r ∣
      (3 * (rising (p ^ r) k : ℤ) ^ 2 + 2 * (rising (p ^ r) k : ℤ) ^ 3) -
        (3 * (risingY p r k : ℤ) ^ 2 + 2 * (risingY p r k : ℤ) ^ 3) := by
  have hδ := pow_dvd_int_rising_sub_risingY hp hp3 hr hk
  obtain ⟨t, ht⟩ := hδ
  -- δ = p^r t, increment = 6y(y+1)δ + 3(2y+1)δ² + 2δ³
  have hexp := increment_as_poly p r k
  rw [hexp, ht]
  refine dvd_add (dvd_add ?_ ?_) ?_
  · refine ⟨6 * (risingY p r k : ℤ) * ((risingY p r k : ℤ) + 1) * t, ?_⟩
    ring
  · refine ⟨3 * (2 * (risingY p r k : ℤ) + 1) * ((p : ℤ) ^ r * t ^ 2), ?_⟩
    ring
  · refine ⟨2 * ((p : ℤ) ^ r) ^ 2 * t ^ 3, ?_⟩
    ring



/-- `C(p^r + m, p^r) ≡ 1 [MOD p]` for `m < p^r`. -/
lemma choose_prime_pow_add_self_mod_p {p r m : ℕ} (hp : p.Prime)
    (hm : m < p ^ r) :
    choose (p ^ r + m) (p ^ r) ≡ 1 [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  induction r generalizing m with
  | zero =>
    simp at hm
    subst hm
    rfl
  | succ r ih =>
    have hmod := Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (n := p ^ (r + 1) + m) (k := p ^ (r + 1)) (p := p)
    have hpr : (p ^ (r + 1)) % p = 0 := by
      have : p ∣ p ^ (r + 1) := dvd_pow_self p (Nat.succ_ne_zero r)
      exact Nat.mod_eq_zero_of_dvd this
    have hsum : (p ^ (r + 1) + m) % p = m % p := by
      rw [Nat.add_mod, hpr, zero_add, Nat.mod_mod]
    have hdivk : p ^ (r + 1) / p = p ^ r := by
      rw [pow_succ, Nat.mul_div_left _ hp.pos]
    have hdivn : (p ^ (r + 1) + m) / p = p ^ r + m / p := by
      have : p ∣ p ^ (r + 1) := dvd_pow_self p (Nat.succ_ne_zero r)
      rw [Nat.add_div_of_dvd_right this, hdivk]
    have hm' : m / p < p ^ r := by
      rw [Nat.div_lt_iff_lt_mul hp.pos]
      simpa [pow_succ, mul_comm] using hm
    have ih' := ih hm'
    have hmod1 : choose ((p ^ (r + 1) + m) % p) ((p ^ (r + 1)) % p) = 1 := by
      rw [hpr, hsum, choose_zero_right]
    have : choose (p ^ (r + 1) + m) (p ^ (r + 1)) ≡
        1 * choose (p ^ r + m / p) (p ^ r) [MOD p] := by
      convert hmod using 2
      · exact hmod1.symm
      · rw [hdivn, hdivk]
    exact this.trans (by simpa using ih')

lemma choose_prime_pow_add_mod_p {p r m : ℕ} (hp : p.Prime)
    (hm : m < p ^ r) :
    choose (p ^ r + m) m ≡ 1 [MOD p] := by
  have hle : m ≤ p ^ r + m := Nat.le_add_left _ _
  have : choose (p ^ r + m) m = choose (p ^ r + m) (p ^ r) := by
    have := choose_symm hle
    simpa [add_comm] using this.symm
  rw [this]
  exact choose_prime_pow_add_self_mod_p hp hm

/-- For p-free `k`, `u_k * k ≡ 1 [MOD p]`. -/
lemma rising_div_pow_mul_mod_p {p r k : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hk0 : 0 < k) (hk : k ≤ p ^ r) (hdv : ¬ p ∣ k) :
    (rising (p ^ r) k / p ^ r) * k ≡ 1 [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hkn : k < p ^ r :=
    lt_of_le_of_ne hk (fun h => hdv (by rw [h]; exact dvd_pow_self p (ne_zero_of_lt hr)))
  have hval := padicValNat_rising_of_not_dvd (p := p) (r := r) (k := k) hk0 (le_of_lt hkn) hdv
  have hne : rising (p ^ r) k ≠ 0 := by
    unfold rising
    exact choose_ne_zero (by
      have : 1 ≤ p ^ r := Nat.one_le_pow r p hp.pos
      omega)
  have hdiv : p ^ r ∣ rising (p ^ r) k :=
    (padicValNat_dvd_iff_le hne).mpr (le_of_eq hval.symm)
  have hident : rising (p ^ r) k / p ^ r * k = choose (p ^ r + k - 1) (k - 1) := by
    have hmul : rising (p ^ r) k * k = choose (p ^ r + k - 1) (k - 1) * p ^ r := by
      unfold rising
      have hkpred : k = k - 1 + 1 := (Nat.sub_add_cancel hk0).symm
      rw [hkpred, choose_succ_right_eq]
      congr 1
      have : 1 ≤ p ^ r := Nat.one_le_pow r p hp.pos
      omega
    rw [Nat.mul_comm, ← Nat.mul_div_assoc k hdiv, Nat.mul_comm k, hmul,
      Nat.mul_div_cancel _ (pow_pos hp.pos r)]
  have hm : k - 1 < p ^ r := by omega
  have hch := choose_prime_pow_add_mod_p (p := p) (r := r) (m := k - 1) hp hm
  have : p ^ r + (k - 1) = p ^ r + k - 1 := by omega
  rw [hident, ← this]
  exact hch


/-! ### Increment splitting and the cubic term `S3d` -/

def incrementZ (p r k : ℕ) : ℤ :=
  (3 * (rising (p ^ r) k : ℤ) ^ 2 + 2 * (rising (p ^ r) k : ℤ) ^ 3) -
    (3 * (risingY p r k : ℤ) ^ 2 + 2 * (risingY p r k : ℤ) ^ 3)

lemma incrementZ_eq_poly (p r k : ℕ) :
    incrementZ p r k =
      6 * (risingY p r k : ℤ) * ((risingY p r k : ℤ) + 1) *
        ((rising (p ^ r) k : ℤ) - risingY p r k) +
      3 * (2 * (risingY p r k : ℤ) + 1) *
        ((rising (p ^ r) k : ℤ) - risingY p r k) ^ 2 +
      2 * ((rising (p ^ r) k : ℤ) - risingY p r k) ^ 3 :=
  increment_as_poly p r k

lemma A357565_sub_eq_sum_incrementZ (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) :
    (A357565 (p ^ r) : ℤ) - A357565 (p ^ (r - 1)) =
      ∑ k ∈ range (p ^ r + 1), incrementZ p r k :=
  A357565_sub_eq_sum_increment p r hp hr

/-- The cubic increment is divisible by `p^{3r+3}` whenever `p ∣ k`. -/
lemma increment_cubic_dvd {p r k : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hr : 1 ≤ r) (hk : k ≤ p ^ r) (hdv : p ∣ k) :
    (p : ℤ) ^ (3 * r + 3) ∣
      2 * ((rising (p ^ r) k : ℤ) - risingY p r k) ^ 3 := by
  obtain ⟨B, hB⟩ := hdv
  have hBle : B ≤ p ^ (r - 1) := by
    have : p * B ≤ p * p ^ (r - 1) := by
      rw [← hB, prime_mul_pow_pred hr]; exact hk
    exact Nat.le_of_mul_le_mul_left this hp.pos
  have hδ := pow_dvd_int_rising_sub_of_dvd_succ (p := p) (r := r) (B := B) hp hp3 hr hBle
  subst hB
  obtain ⟨t, ht⟩ := hδ
  refine ⟨2 * t ^ 3, ?_⟩
  rw [ht]
  ring

lemma sum_increment_cubic_dvd {p r : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hr : 1 ≤ r) :
    (p : ℤ) ^ (3 * r + 3) ∣
      ∑ k ∈ range (p ^ r + 1),
        2 * ((rising (p ^ r) k : ℤ) - risingY p r k) ^ 3 *
          if p ∣ k then 1 else 0 := by
  refine dvd_sum ?_
  intro k hk
  have hkle : k ≤ p ^ r := Nat.lt_succ_iff.mp (mem_range.mp hk)
  by_cases hdv : p ∣ k
  · simp [hdv]
    exact increment_cubic_dvd hp hp3 hr hkle hdv
  · simp [hdv]


/-! ### Rectangle inverses in `ZMod (p^2)` -/

lemma pval_cast_mod_sq {p s j : ℕ} (hp : p.Prime)
    (hs : s ∈ Icc 1 (p - 1)) (hj : 1 ≤ j) :
    ((p * j - s : ℕ) : ZMod (p ^ 2)) =
      (p : ZMod (p ^ 2)) * j - s := by
  have ⟨hs1, hs2⟩ := mem_Icc.mp hs
  have hs_lt : s < p := by omega
  have hle : s ≤ p * j :=
    le_trans (Nat.le_of_lt hs_lt) (Nat.le_mul_of_pos_right p hj)
  rw [Nat.cast_sub hle, Nat.cast_mul]

lemma isUnit_neg_Icc {p n s : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hs : s ∈ Icc 1 (p - 1)) :
    IsUnit (-(s : ZMod (p ^ n))) :=
  (Icc_cast_unit_pow hp hn hs).neg

lemma pval_isUnit_mod_sq {p s j : ℕ} (hp : p.Prime)
    (hs : s ∈ Icc 1 (p - 1)) (hj : 1 ≤ j) :
    IsUnit ((p * j - s : ℕ) : ZMod (p ^ 2)) := by
  rw [pval_cast_mod_sq hp hs hj]
  have ha : IsUnit (-(s : ZMod (p ^ 2))) := isUnit_neg_Icc hp (by decide : 0 < 2) hs
  have hrew : (p : ZMod (p ^ 2)) * j - (s : ZMod (p ^ 2)) =
      -(s : ZMod (p ^ 2)) + (p : ZMod (p ^ 2)) * j := by ring
  rw [hrew]
  have hfac : -(s : ZMod (p ^ 2)) + (p : ZMod (p ^ 2)) * j =
      (-(s : ZMod (p ^ 2))) *
        (1 + (p : ZMod (p ^ 2)) * (j * (-(s : ZMod (p ^ 2)))⁻¹)) := by
    have hua := unit_mul_inv ha
    calc
      -(s : ZMod (p ^ 2)) + (p : ZMod (p ^ 2)) * j =
          (-(s : ZMod (p ^ 2))) * 1 + (p : ZMod (p ^ 2)) * (j * 1) := by simp
      _ = (-(s : ZMod (p ^ 2))) * 1 +
            (p : ZMod (p ^ 2)) *
              (j * ((-(s : ZMod (p ^ 2))) * (-(s : ZMod (p ^ 2)))⁻¹)) := by
        rw [hua]
      _ = (-(s : ZMod (p ^ 2))) *
            (1 + (p : ZMod (p ^ 2)) * (j * (-(s : ZMod (p ^ 2)))⁻¹)) := by ring
  rw [hfac]
  exact ha.mul (isUnit_one_add_p_mul hp _)

lemma pval_inv_mod_sq {p s j : ℕ} (hp : p.Prime)
    (hs : s ∈ Icc 1 (p - 1)) (hj : 1 ≤ j) :
    ((p * j - s : ℕ) : ZMod (p ^ 2))⁻¹ =
      -((s : ZMod (p ^ 2))⁻¹) -
        (p : ZMod (p ^ 2)) * j * ((s : ZMod (p ^ 2))⁻¹) ^ 2 := by
  have hcast := pval_cast_mod_sq hp hs hj
  rw [hcast]
  have ha : IsUnit (-(s : ZMod (p ^ 2))) := isUnit_neg_Icc hp (by decide : 0 < 2) hs
  have hrew : (p : ZMod (p ^ 2)) * j - (s : ZMod (p ^ 2)) =
      -(s : ZMod (p ^ 2)) + (p : ZMod (p ^ 2)) * j := by ring
  rw [hrew, inv_add_p_mul hp ha]
  have hneg : (-(s : ZMod (p ^ 2)))⁻¹ = -((s : ZMod (p ^ 2))⁻¹) := by
    have hu := Icc_cast_unit_pow (n := 2) hp (by decide : 0 < 2) hs
    apply ZMod.inv_eq_of_mul_eq_one
    rw [neg_mul_neg, unit_mul_inv hu]
  rw [hneg]
  ring

/-- Rectangle harmonic vanishes in `ZMod (p^2)` for `p ≥ 5`. -/
lemma sum_rectangle_inv_mod_sq {p B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∑ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
      ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ 2))⁻¹ = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  rw [Finset.sum_product]
  have hterm : ∀ s ∈ Icc 1 (p - 1), ∀ j ∈ Icc 1 B,
      ((p * j - s : ℕ) : ZMod (p ^ 2))⁻¹ =
        -((s : ZMod (p ^ 2))⁻¹) -
          (p : ZMod (p ^ 2)) * j * ((s : ZMod (p ^ 2))⁻¹) ^ 2 := by
    intro s hs j hj
    have ⟨hj1, _⟩ := mem_Icc.mp hj
    exact pval_inv_mod_sq hp hs hj1
  have hsum :
      ∑ s ∈ Icc 1 (p - 1), ∑ j ∈ Icc 1 B,
        ((p * j - s : ℕ) : ZMod (p ^ 2))⁻¹ =
      ∑ s ∈ Icc 1 (p - 1), ∑ j ∈ Icc 1 B,
        (-((s : ZMod (p ^ 2))⁻¹) -
          (p : ZMod (p ^ 2)) * j * ((s : ZMod (p ^ 2))⁻¹) ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro s hs
    refine Finset.sum_congr rfl ?_
    intro j hj
    exact hterm s hs j hj
  rw [hsum]
  have hsplit :
      ∑ s ∈ Icc 1 (p - 1), ∑ j ∈ Icc 1 B,
        (-((s : ZMod (p ^ 2))⁻¹) -
          (p : ZMod (p ^ 2)) * j * ((s : ZMod (p ^ 2))⁻¹) ^ 2) =
      -∑ s ∈ Icc 1 (p - 1), ∑ j ∈ Icc 1 B, (s : ZMod (p ^ 2))⁻¹ -
        ∑ s ∈ Icc 1 (p - 1), ∑ j ∈ Icc 1 B,
          (p : ZMod (p ^ 2)) * j * ((s : ZMod (p ^ 2))⁻¹) ^ 2 := by
    simp [sum_sub_distrib, sum_neg_distrib]
  rw [hsplit]
  have hW := harmonic_sum_mod_prime_sq hp hp5
  have h1 :
      ∑ s ∈ Icc 1 (p - 1), ∑ _j ∈ Icc 1 B, (s : ZMod (p ^ 2))⁻¹ =
        (B : ZMod (p ^ 2)) * ∑ s ∈ Icc 1 (p - 1), (s : ZMod (p ^ 2))⁻¹ := by
    have : ∑ s ∈ Icc 1 (p - 1), ∑ _j ∈ Icc 1 B, (s : ZMod (p ^ 2))⁻¹ =
        ∑ s ∈ Icc 1 (p - 1), (#(Icc 1 B) : ZMod (p ^ 2)) * (s : ZMod (p ^ 2))⁻¹ := by
      refine Finset.sum_congr rfl ?_
      intro s hs
      simp [sum_const, nsmul_eq_mul]
    rw [this, ← Finset.mul_sum]
    have hcard : (#(Icc 1 B) : ZMod (p ^ 2)) = (B : ZMod (p ^ 2)) := by
      simp [Nat.card_Icc]
    rw [hcard]
  have h1' :
      ∑ s ∈ Icc 1 (p - 1), ∑ j ∈ Icc 1 B, (s : ZMod (p ^ 2))⁻¹ = 0 := by
    rw [h1, hW, mul_zero]
  have h2inner :
      ∑ s ∈ Icc 1 (p - 1), ∑ j ∈ Icc 1 B,
          (p : ZMod (p ^ 2)) * j * ((s : ZMod (p ^ 2))⁻¹) ^ 2 =
        (p : ZMod (p ^ 2)) *
          (∑ j ∈ Icc 1 B, (j : ZMod (p ^ 2))) *
          (∑ s ∈ Icc 1 (p - 1), ((s : ZMod (p ^ 2))⁻¹) ^ 2) := by
    have hinner :
        ∑ s ∈ Icc 1 (p - 1), ∑ j ∈ Icc 1 B,
            (p : ZMod (p ^ 2)) * j * ((s : ZMod (p ^ 2))⁻¹) ^ 2 =
          ∑ s ∈ Icc 1 (p - 1),
            ((s : ZMod (p ^ 2))⁻¹) ^ 2 *
              ∑ j ∈ Icc 1 B, (p : ZMod (p ^ 2)) * j := by
      refine Finset.sum_congr rfl ?_
      intro s hs
      have hcomm : ∀ j ∈ Icc 1 B,
          (p : ZMod (p ^ 2)) * j * ((s : ZMod (p ^ 2))⁻¹) ^ 2 =
            ((s : ZMod (p ^ 2))⁻¹) ^ 2 * ((p : ZMod (p ^ 2)) * j) :=
        fun j _ => mul_comm _ _
      rw [Finset.sum_congr rfl hcomm, Finset.mul_sum]
    rw [hinner, ← Finset.sum_mul]
    have hswap :
        ∑ j ∈ Icc 1 B, (p : ZMod (p ^ 2)) * j =
          (p : ZMod (p ^ 2)) * ∑ j ∈ Icc 1 B, (j : ZMod (p ^ 2)) := by
      simp [mul_sum]
    rw [hswap]
    ring
  have hsqp := sum_inv_sq_is_p_mul hp hp5
  obtain ⟨c, hc⟩ := hsqp
  have hp2z : (p : ZMod (p ^ 2)) ^ 2 = 0 := p_pow_sq_eq_zero p
  have h2zero :
      (p : ZMod (p ^ 2)) *
        (∑ j ∈ Icc 1 B, (j : ZMod (p ^ 2))) *
        (∑ s ∈ Icc 1 (p - 1), ((s : ZMod (p ^ 2))⁻¹) ^ 2) = 0 := by
    rw [hc]
    have : (p : ZMod (p ^ 2)) * (∑ j ∈ Icc 1 B, (j : ZMod (p ^ 2))) *
        ((p : ZMod (p ^ 2)) * c) =
      ((p : ZMod (p ^ 2)) ^ 2) * ((∑ j ∈ Icc 1 B, (j : ZMod (p ^ 2))) * c) := by ring
    rw [this, hp2z, zero_mul]
  rw [h1', neg_zero, h2inner, h2zero, sub_zero]


/-- `p²` divides the integer cofactor sum for `p ≥ 5`. -/
lemma sum_cofactor_int_dvd_sq {p B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p : ℤ) ^ 2 ∣
      ∑ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
        ∏ kl ∈ (Icc 1 (p - 1) ×ˢ Icc 1 B).erase ij,
          ((p * kl.2 - kl.1 : ℕ) : ℤ) := by
  set s : Finset (ℕ × ℕ) := Icc 1 (p - 1) ×ˢ Icc 1 B
  set Pℤ : ℤ := ∏ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ℤ)
  set Sℤ : ℤ :=
    ∑ ij ∈ s, ∏ kl ∈ s.erase ij, ((p * kl.2 - kl.1 : ℕ) : ℤ)
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hsumZ : (Sℤ : ZMod (p ^ 2)) =
      ∑ ij ∈ s, ∏ kl ∈ s.erase ij, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ 2)) := by
    simp only [Sℤ, Int.cast_sum, Int.cast_prod, Int.cast_natCast]
  have hPZ : (Pℤ : ZMod (p ^ 2)) =
      ∏ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ 2)) := by
    simp only [Pℤ, Int.cast_prod, Int.cast_natCast]
  have hterm : ∀ ij ∈ s,
      ∏ kl ∈ s.erase ij, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ 2)) =
        ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ 2))⁻¹ *
          ∏ kl ∈ s, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ 2)) := by
    intro ij hij
    have hij' := mem_product.mp hij
    have ⟨hj1, _⟩ := mem_Icc.mp hij'.2
    have hu : IsUnit ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ 2)) :=
      pval_isUnit_mod_sq hp hij'.1 hj1
    have hmul := Finset.mul_prod_erase s
      (fun kl => ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ 2))) hij
    calc
      ∏ kl ∈ s.erase ij, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ 2)) =
          ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ 2))⁻¹ *
            (((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ 2)) *
              ∏ kl ∈ s.erase ij, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ 2))) := by
        rw [← mul_assoc, unit_inv_mul hu, one_mul]
      _ = ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ 2))⁻¹ *
            ∏ kl ∈ s, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ 2)) := by
        rw [hmul]
  have hfactor : (Sℤ : ZMod (p ^ 2)) =
      (Pℤ : ZMod (p ^ 2)) *
        ∑ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ 2))⁻¹ := by
    rw [hsumZ, Finset.sum_congr rfl hterm, ← Finset.sum_mul, mul_comm, hPZ]
  have hH := sum_rectangle_inv_mod_sq (p := p) (B := B) hp hp5
  have : (Sℤ : ZMod (p ^ 2)) = 0 := by
    rw [hfactor, hH, mul_zero]
  exact (CharP.intCast_eq_zero_iff (ZMod (p ^ 2)) (p ^ 2) Sℤ).mp this

/-- `Q ≡ P [ZMOD p^{r+2}]` for `p ≥ 5` and `r ≥ 2`. -/
lemma prod_add_pow_of_cofactor_sq {p r B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 2 ≤ r) :
    (∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
        (((p * ij.2 - ij.1 : ℕ) : ℤ) + (p : ℤ) ^ r)) ≡
      (∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B, ((p * ij.2 - ij.1 : ℕ) : ℤ))
      [ZMOD (p : ℤ) ^ (r + 2)] := by
  set s : Finset (ℕ × ℕ) := Icc 1 (p - 1) ×ˢ Icc 1 B
  set x : ℕ × ℕ → ℤ := fun ij => ((p * ij.2 - ij.1 : ℕ) : ℤ)
  have hr1 : 1 ≤ r := by omega
  have hexp := prod_add_const_mod_sq (s := s) (x := x) (N := (p : ℤ) ^ r)
  have hcof := sum_cofactor_int_dvd_sq (p := p) (B := B) hp hp5
  have hN2 : ((p : ℤ) ^ r) ^ 2 = (p : ℤ) ^ (2 * r) := by
    rw [← pow_mul, mul_comm]
  have hdvdN2 :
      (p : ℤ) ^ (2 * r) ∣
        (∏ i ∈ s, x i + (p : ℤ) ^ r * ∑ i ∈ s, ∏ j ∈ s.erase i, x j -
          ∏ i ∈ s, (x i + (p : ℤ) ^ r)) := by
    have := (Int.modEq_iff_dvd).mp hexp
    simpa [hN2] using this
  obtain ⟨K, hK⟩ := hdvdN2
  have hdecomp :
      ∏ i ∈ s, (x i + (p : ℤ) ^ r) - ∏ i ∈ s, x i =
        (p : ℤ) ^ r * ∑ i ∈ s, ∏ j ∈ s.erase i, x j - (p : ℤ) ^ (2 * r) * K := by
    linear_combination -hK
  obtain ⟨c, hc⟩ := hcof
  have hr2 : r + 2 ≤ 2 * r := by omega
  have hpow : (p : ℤ) ^ (2 * r) = (p : ℤ) ^ (r + 2) * (p : ℤ) ^ (2 * r - (r + 2)) := by
    rw [← pow_add, Nat.add_sub_cancel' hr2]
  have hdiff :
      ∏ i ∈ s, (x i + (p : ℤ) ^ r) - ∏ i ∈ s, x i =
        (p : ℤ) ^ (r + 2) * (c - (p : ℤ) ^ (2 * r - (r + 2)) * K) := by
    rw [hdecomp, hc, hpow]
    ring
  refine (Int.modEq_iff_dvd).mpr ?_
  refine ⟨-(c - (p : ℤ) ^ (2 * r - (r + 2)) * K), ?_⟩
  linear_combination -hdiff

/-- For `p ≥ 5` and `r ≥ 2`, `p^{r+2}` divides `δ` when `k = pB`. -/
lemma pow_dvd_int_rising_sub_of_dvd_sq {p r B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 2 ≤ r) (hB : B ≤ p ^ (r - 1)) :
    (p : ℤ) ^ (r + 2) ∣
      (rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B) := by
  have hr1 : 1 ≤ r := by omega
  have hid := rising_sub_mul_pProd (p := p) (r := r) (B := B) hp hr1 hB
  have hQmod := prod_add_pow_of_cofactor_sq (p := p) (r := r) (B := B) hp hp5 hr
  have hcastQ :
      ((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
          (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) =
        ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
          (((p * ij.2 - ij.1 : ℕ) : ℤ) + (p : ℤ) ^ r) := by
    simp [Nat.cast_prod, Nat.cast_add, Nat.cast_pow]
  have hcastP : (pProd p B : ℤ) =
      ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B, ((p * ij.2 - ij.1 : ℕ) : ℤ) := by
    simp [pProd_eq_prod_product, Nat.cast_prod]
  have hQP : (p : ℤ) ^ (r + 2) ∣
      ((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
          (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) - (pProd p B : ℤ) := by
    have h := (Int.modEq_iff_dvd).mp hQmod
    -- h : p^{r+2} ∣ P - Q, flip to Q - P
    rw [hcastQ, hcastP]
    exact dvd_neg.mp (by simpa [neg_sub] using h)
  have hyQP : (p : ℤ) ^ (r + 2) ∣
      (risingY p r (p * B) : ℤ) *
        (((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
            (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) - pProd p B) :=
    dvd_mul_of_dvd_right hQP _
  have hδP : (p : ℤ) ^ (r + 2) ∣
      ((rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B)) * (pProd p B : ℤ) := by
    rwa [hid]
  haveI : Fact p.Prime := ⟨hp⟩
  have hPne : (pProd p B : ℤ) ≠ 0 := by
    exact_mod_cast (ne_zero_of_lt (pProd_pos (p := p) hp.pos))
  by_cases hδ0 : ((rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B)) = 0
  · simp [hδ0]
  · have hge : r + 2 ≤
        padicValInt p
          (((rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B)) * pProd p B) :=
      (padicValInt_dvd_iff (p := p) (r + 2)
        (((rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B)) * pProd p B)).mp
        hδP |>.resolve_left (mul_ne_zero hδ0 hPne)
    have hmulv :
        padicValInt p
            (((rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B)) * pProd p B) =
          padicValInt p ((rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B)) +
            padicValInt p (pProd p B : ℤ) :=
      padicValInt.mul (p := p) hδ0 hPne
    have hP0 : padicValInt p (pProd p B : ℤ) = 0 := by
      rw [padicValInt.of_nat]
      exact padicValNat.eq_zero_of_not_dvd (p_not_dvd_pProd hp)
    have : r + 2 ≤
        padicValInt p ((rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B)) := by
      omega
    exact (padicValInt_dvd_iff (p := p) (r + 2)
      ((rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B))).mpr (Or.inr this)

/-- Combining `v(y)` with `p^{r+2} | (Q-P)` gives `v(δ) ≥ v(y) + r + 2`. -/
lemma pow_dvd_delta_with_y {p r B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 2 ≤ r) (hB : B ≤ p ^ (r - 1)) :
    (p : ℤ) ^ (padicValInt p (risingY p r (p * B) : ℤ) + r + 2) ∣
      (rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B) := by
  have hr1 : 1 ≤ r := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  have hid := rising_sub_mul_pProd (p := p) (r := r) (B := B) hp hr1 hB
  have hQP : (p : ℤ) ^ (r + 2) ∣
      ((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
          (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) - pProd p B := by
    have hQmod := prod_add_pow_of_cofactor_sq (p := p) (r := r) (B := B) hp hp5 hr
    have hcastQ :
        ((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
            (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) =
          ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
            (((p * ij.2 - ij.1 : ℕ) : ℤ) + (p : ℤ) ^ r) := by
      simp [Nat.cast_prod, Nat.cast_add, Nat.cast_pow]
    have hcastP : (pProd p B : ℤ) =
        ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B, ((p * ij.2 - ij.1 : ℕ) : ℤ) := by
      simp [pProd_eq_prod_product, Nat.cast_prod]
    have h := (Int.modEq_iff_dvd).mp hQmod
    rw [hcastQ, hcastP]
    exact dvd_neg.mp (by simpa [neg_sub] using h)
  set y : ℤ := (risingY p r (p * B) : ℤ)
  set δ : ℤ := (rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B)
  set QP : ℤ :=
    ((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
        (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) - pProd p B
  have hid' : δ * (pProd p B : ℤ) = y * QP := hid
  have hPne : (pProd p B : ℤ) ≠ 0 := by
    exact_mod_cast (ne_zero_of_lt (pProd_pos (p := p) hp.pos))
  by_cases hy0 : y = 0
  · -- then δ * P = 0 so δ = 0
    have : δ * (pProd p B : ℤ) = 0 := by rw [hid', hy0, zero_mul]
    have hδ0 : δ = 0 := by
      exact (mul_eq_zero.mp this).resolve_right hPne
    simp [hδ0]
  · by_cases hδ0 : δ = 0
    · simp [hδ0]
    · have hQP0 : QP ≠ 0 := by
        intro h
        have : δ * (pProd p B : ℤ) = 0 := by rw [hid', h, mul_zero]
        exact hδ0 ((mul_eq_zero.mp this).resolve_right hPne)
      have hv :
          padicValInt p (δ * (pProd p B : ℤ)) =
            padicValInt p y + padicValInt p QP := by
        rw [hid']
        exact padicValInt.mul (p := p) hy0 hQP0
      have hP0 : padicValInt p (pProd p B : ℤ) = 0 := by
        rw [padicValInt.of_nat]
        exact padicValNat.eq_zero_of_not_dvd (p_not_dvd_pProd hp)
      have hδP : padicValInt p (δ * (pProd p B : ℤ)) = padicValInt p δ := by
        rw [padicValInt.mul (p := p) hδ0 hPne, hP0, add_zero]
      have hQPge : r + 2 ≤ padicValInt p QP :=
        (padicValInt_dvd_iff (p := p) (r + 2) QP).mp hQP |>.resolve_left hQP0
      have : padicValInt p y + r + 2 ≤ padicValInt p δ := by
        omega
      exact (padicValInt_dvd_iff (p := p) (padicValInt p y + r + 2) δ).mpr
        (Or.inr this)

lemma padicValInt_risingY {p r B : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hB0 : 0 < B) (hB : B ≤ p ^ (r - 1)) :
    padicValInt p (risingY p r (p * B) : ℤ) =
      (r - 1) - padicValNat p B := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hy : risingY p r (p * B) = rising (p ^ (r - 1)) B := by
    rw [risingY_of_dvd (dvd_mul_right p B), Nat.mul_div_right B hp.pos]
  rw [hy, padicValInt.of_nat]
  exact padicValNat_rising_prime_pow (p := p) (r := r - 1) (k := B) hB0 hB

/-- When `p ∤ B` (so `v(y) = r-1`), we get `v(δ) ≥ 2r+1`. -/
lemma pow_dvd_delta_pfree_B {p r B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 2 ≤ r) (hB0 : 0 < B) (hB : B ≤ p ^ (r - 1)) (hnd : ¬ p ∣ B) :
    (p : ℤ) ^ (2 * r + 1) ∣
      (rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B) := by
  have hr1 : 1 ≤ r := by omega
  have h := pow_dvd_delta_with_y (p := p) (r := r) (B := B) hp hp5 hr hB
  have hy : padicValInt p (risingY p r (p * B) : ℤ) = r - 1 := by
    rw [padicValInt_risingY hp hr1 hB0 hB, padicValNat.eq_zero_of_not_dvd hnd,
      tsub_zero]
  have : padicValInt p (risingY p r (p * B) : ℤ) + r + 2 = 2 * r + 1 := by
    rw [hy]; omega
  rwa [this] at h


/-- p=3 (or any odd p): `v(δ) ≥ v(y) + r + 1` from the `p^{r+1}` upgrade. -/
lemma pow_dvd_delta_with_y_succ {p r B : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hr : 1 ≤ r) (hB : B ≤ p ^ (r - 1)) :
    (p : ℤ) ^ (padicValInt p (risingY p r (p * B) : ℤ) + r + 1) ∣
      (rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hid := rising_sub_mul_pProd (p := p) (r := r) (B := B) hp hr hB
  have hp2 : p ≠ 2 := by omega
  -- Q ≡ P [ZMOD p^{r+1}]
  have hQmod :
      (∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
          (((p * ij.2 - ij.1 : ℕ) : ℤ) + (p : ℤ) ^ r)) ≡
        (∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B, ((p * ij.2 - ij.1 : ℕ) : ℤ))
        [ZMOD (p : ℤ) ^ (r + 1)] := by
    have hcof := sum_cofactor_int_dvd (p := p) (B := B) hp hp2
    exact prod_add_pow_of_cofactor (s := Icc 1 (p - 1) ×ˢ Icc 1 B)
      (x := fun ij => ((p * ij.2 - ij.1 : ℕ) : ℤ)) hp hr hcof
  have hcastQ :
      ((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
          (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) =
        ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
          (((p * ij.2 - ij.1 : ℕ) : ℤ) + (p : ℤ) ^ r) := by
    simp [Nat.cast_prod, Nat.cast_add, Nat.cast_pow]
  have hcastP : (pProd p B : ℤ) =
      ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B, ((p * ij.2 - ij.1 : ℕ) : ℤ) := by
    simp [pProd_eq_prod_product, Nat.cast_prod]
  have hQP : (p : ℤ) ^ (r + 1) ∣
      ((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
          (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) - pProd p B := by
    have h := (Int.modEq_iff_dvd).mp hQmod
    rw [hcastQ, hcastP]
    exact dvd_neg.mp (by simpa [neg_sub] using h)
  set y : ℤ := (risingY p r (p * B) : ℤ)
  set δ : ℤ := (rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B)
  set QP : ℤ :=
    ((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
        (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) - pProd p B
  have hid' : δ * (pProd p B : ℤ) = y * QP := hid
  have hPne : (pProd p B : ℤ) ≠ 0 := by
    exact_mod_cast (ne_zero_of_lt (pProd_pos (p := p) hp.pos))
  by_cases hy0 : y = 0
  · have : δ * (pProd p B : ℤ) = 0 := by rw [hid', hy0, zero_mul]
    have hδ0 : δ = 0 := (mul_eq_zero.mp this).resolve_right hPne
    simp [hδ0]
  · by_cases hδ0 : δ = 0
    · simp [hδ0]
    · have hQP0 : QP ≠ 0 := by
        intro h
        have : δ * (pProd p B : ℤ) = 0 := by rw [hid', h, mul_zero]
        exact hδ0 ((mul_eq_zero.mp this).resolve_right hPne)
      have hP0 : padicValInt p (pProd p B : ℤ) = 0 := by
        rw [padicValInt.of_nat]
        exact padicValNat.eq_zero_of_not_dvd (p_not_dvd_pProd hp)
      have hδeq : padicValInt p (δ * (pProd p B : ℤ)) = padicValInt p δ := by
        rw [padicValInt.mul (p := p) hδ0 hPne, hP0, add_zero]
      have hyQP : padicValInt p (δ * (pProd p B : ℤ)) =
          padicValInt p y + padicValInt p QP := by
        rw [hid']
        exact padicValInt.mul (p := p) hy0 hQP0
      have hQPge : r + 1 ≤ padicValInt p QP :=
        (padicValInt_dvd_iff (p := p) (r + 1) QP).mp hQP |>.resolve_left hQP0
      have : padicValInt p y + r + 1 ≤ padicValInt p δ := by
        omega
      exact (padicValInt_dvd_iff (p := p) (padicValInt p y + r + 1) δ).mpr
        (Or.inr this)

/-- `S2d` term is divisible by `p^{3r+3}` when `p ∤ B` and `p ≥ 5`. -/
lemma increment_quad_dvd_pfreeB {p r B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 2 ≤ r) (hB0 : 0 < B) (hB : B ≤ p ^ (r - 1)) (hnd : ¬ p ∣ B) :
    (p : ℤ) ^ (3 * r + 3) ∣
      3 * (2 * (risingY p r (p * B) : ℤ) + 1) *
        ((rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B)) ^ 2 := by
  have hδ := pow_dvd_delta_pfree_B hp hp5 hr hB0 hB hnd
  obtain ⟨t, ht⟩ := hδ
  refine ⟨3 * (2 * (risingY p r (p * B) : ℤ) + 1) *
      ((p : ℤ) ^ (r - 1) * t ^ 2), ?_⟩
  have hpow : ((p : ℤ) ^ (2 * r + 1)) ^ 2 = (p : ℤ) ^ (4 * r + 2) := by
    rw [← pow_mul]; ring
  have hge : 3 * r + 3 ≤ 4 * r + 2 := by omega
  -- 3(2y+1) δ² = 3(2y+1) p^{4r+2} t² = p^{3r+3} * (3(2y+1) p^{r-1} t²)
  have : ((rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B)) ^ 2 =
      (p : ℤ) ^ (4 * r + 2) * t ^ 2 := by
    rw [ht, mul_pow, hpow]
  rw [this]
  have hsplit : (p : ℤ) ^ (4 * r + 2) =
      (p : ℤ) ^ (3 * r + 3) * (p : ℤ) ^ (r - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit]
  ring

/-- `S2d` term for `p = 3` and `p ∤ B`: `v(3 δ²) ≥ 1 + 4r ≥ 3r+3`. -/
lemma increment_quad_dvd_pfreeB_three {r B : ℕ} (hr : 2 ≤ r)
    (hB0 : 0 < B) (hB : B ≤ 3 ^ (r - 1)) (hnd : ¬ 3 ∣ B) :
    (3 : ℤ) ^ (3 * r + 3) ∣
      3 * (2 * (risingY 3 r (3 * B) : ℤ) + 1) *
        ((rising (3 ^ r) (3 * B) : ℤ) - risingY 3 r (3 * B)) ^ 2 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp3 : (3 : ℕ) ≤ 3 := le_rfl
  have hr1 : 1 ≤ r := by omega
  have hδ := pow_dvd_delta_with_y_succ (p := 3) (r := r) (B := B) hp hp3 hr1 hB
  have hy : padicValInt 3 (risingY 3 r (3 * B) : ℤ) = r - 1 := by
    rw [padicValInt_risingY hp hr1 hB0 hB, padicValNat.eq_zero_of_not_dvd hnd,
      tsub_zero]
  have hexp : padicValInt 3 (risingY 3 r (3 * B) : ℤ) + r + 1 = 2 * r := by
    rw [hy]; omega
  rw [hexp] at hδ
  obtain ⟨t, ht⟩ := hδ
  -- δ = 3^{2r} t, so 3(2y+1)δ² = 3(2y+1) 3^{4r} t² = 3^{4r+1} (2y+1) t²
  -- and 4r+1 = (3r+3) + (r-2)
  refine ⟨(2 * (risingY 3 r (3 * B) : ℤ) + 1) * ((3 : ℤ) ^ (r - 2) * t ^ 2), ?_⟩
  have hδ2 : ((rising (3 ^ r) (3 * B) : ℤ) - risingY 3 r (3 * B)) ^ 2 =
      ((3 : ℤ) ^ (2 * r)) ^ 2 * t ^ 2 := by
    rw [ht]; ring
  have hpow : ((3 : ℤ) ^ (2 * r)) ^ 2 = (3 : ℤ) ^ (4 * r) := by
    rw [← pow_mul, show (2 * r) * 2 = 4 * r by ring]
  rw [hδ2, hpow]
  have hsplit : 4 * r + 1 = (3 * r + 3) + (r - 2) := by omega
  calc
    (3 : ℤ) * (2 * (risingY 3 r (3 * B) : ℤ) + 1) *
        ((3 : ℤ) ^ (4 * r) * t ^ 2) =
      (2 * (risingY 3 r (3 * B) : ℤ) + 1) *
        ((3 : ℤ) ^ 1 * (3 : ℤ) ^ (4 * r) * t ^ 2) := by ring
    _ = (2 * (risingY 3 r (3 * B) : ℤ) + 1) *
          ((3 : ℤ) ^ (4 * r + 1) * t ^ 2) := by
      rw [← pow_add]; ring
    _ = (2 * (risingY 3 r (3 * B) : ℤ) + 1) *
          ((3 : ℤ) ^ ((3 * r + 3) + (r - 2)) * t ^ 2) := by
      simp [hsplit]
    _ = (3 : ℤ) ^ (3 * r + 3) *
          ((2 * (risingY 3 r (3 * B) : ℤ) + 1) *
            ((3 : ℤ) ^ (r - 2) * t ^ 2)) := by
      rw [pow_add]; ring


/-! ### Last-term rectangle = p-free residues, and pairing -/

lemma pfree_sub {p r k : ℕ} (hp : p.Prime) (hr : 0 < r)
    (hk : k ∈ pfree p r) :
    p ^ r - k ∈ pfree p r := by
  have ⟨hklt, hnd⟩ := mem_pfree.mp hk
  have hk0 : 0 < k := pfree_pos hp hk
  have hsublt : p ^ r - k < p ^ r := Nat.sub_lt (pow_pos hp.pos r) hk0
  have hnd' : ¬ p ∣ p ^ r - k := by
    intro hd
    have hpr0 : p ^ r % p = 0 :=
      Nat.mod_eq_zero_of_dvd (dvd_pow_self p (ne_zero_of_lt hr))
    have hsum : k + (p ^ r - k) = p ^ r := Nat.add_sub_of_le (Nat.le_of_lt hklt)
    have hmod : (k + (p ^ r - k)) % p = p ^ r % p := congrArg (· % p) hsum
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, add_zero, Nat.mod_mod, hpr0] at hmod
    have : p ∣ k := Nat.dvd_of_mod_eq_zero hmod
    exact hnd this
  exact mem_pfree.mpr ⟨hsublt, hnd'⟩

lemma pfree_sub_sub {p r k : ℕ} (hp : p.Prime)
    (hk : k ∈ pfree p r) :
    p ^ r - (p ^ r - k) = k := by
  have ⟨hklt, _⟩ := mem_pfree.mp hk
  exact Nat.sub_sub_self (Nat.le_of_lt hklt)

lemma pfree_cast_add {p r k : ℕ} (hp : p.Prime) (hr : 0 < r)
    (hk : k ∈ pfree p r) :
    ((p ^ r - k : ℕ) : ZMod (p ^ r)) = - (k : ZMod (p ^ r)) := by
  have ⟨hklt, _⟩ := mem_pfree.mp hk
  have hle : k ≤ p ^ r := Nat.le_of_lt hklt
  rw [Nat.cast_sub hle, ZMod.natCast_self, zero_sub]

lemma pair_inv_pfree {p r k : ℕ} (hp : p.Prime) (hr : 0 < r)
    (hk : k ∈ pfree p r) :
    (k : ZMod (p ^ r))⁻¹ + ((p ^ r - k : ℕ) : ZMod (p ^ r))⁻¹ = 0 := by
  have hu := isUnit_of_mem_pfree hp hr hk
  have hk' := pfree_sub hp hr hk
  have hu' := isUnit_of_mem_pfree hp hr hk'
  rw [pfree_cast_add hp hr hk]
  have : (-(k : ZMod (p ^ r)))⁻¹ = -((k : ZMod (p ^ r))⁻¹) := by
    apply ZMod.inv_eq_of_mul_eq_one
    rw [neg_mul_neg, unit_mul_inv hu]
  rw [this, add_neg_cancel]

lemma sum_pfree_inv_eq_zero {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : 0 < r) :
    ∑ k ∈ pfree p r, (k : ZMod (p ^ r))⁻¹ = 0 := by
  have h2u : IsUnit (2 : ZMod (p ^ r)) := by
    have : IsUnit ((2 : ℕ) : ZMod (p ^ r)) := by
      rw [ZMod.isUnit_iff_coprime]
      rw [Nat.coprime_pow_right_iff hr]
      exact (Nat.prime_two.coprime_iff_not_dvd).2 (by
        intro hd
        have : 2 = p := (Nat.dvd_prime hp).mp hd |>.resolve_left (by decide)
        exact hp2 this.symm)
    exact this
  have hperm :
      ∑ k ∈ pfree p r, ((p ^ r - k : ℕ) : ZMod (p ^ r))⁻¹ =
        ∑ k ∈ pfree p r, (k : ZMod (p ^ r))⁻¹ := by
    refine Finset.sum_bij (fun k _ => p ^ r - k) ?_ ?_ ?_ ?_
    · intro k hk; exact pfree_sub hp hr hk
    · intro k hk k' hk' h
      have := congrArg (fun t => p ^ r - t) h
      simpa [pfree_sub_sub hp hk, pfree_sub_sub hp hk'] using this
    · intro k hk
      refine ⟨p ^ r - k, pfree_sub hp hr hk, pfree_sub_sub hp hk⟩
    · intro k hk; rfl
  have hsum2 :
      ∑ k ∈ pfree p r,
        ((k : ZMod (p ^ r))⁻¹ + ((p ^ r - k : ℕ) : ZMod (p ^ r))⁻¹) =
      2 * ∑ k ∈ pfree p r, (k : ZMod (p ^ r))⁻¹ := by
    rw [sum_add_distrib, hperm, two_mul]
  have hpairs :
      ∑ k ∈ pfree p r,
        ((k : ZMod (p ^ r))⁻¹ + ((p ^ r - k : ℕ) : ZMod (p ^ r))⁻¹) = 0 :=
    Finset.sum_eq_zero (fun k hk => pair_inv_pfree hp hr hk)
  have : 2 * ∑ k ∈ pfree p r, (k : ZMod (p ^ r))⁻¹ = 0 := hsum2.symm.trans hpairs
  have hcancel := congrArg (fun z => (2 : ZMod (p ^ r))⁻¹ * z) this
  simpa [← mul_assoc, unit_inv_mul h2u] using hcancel


lemma rectangle_mem_pfree {p r s j : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hs : s ∈ Icc 1 (p - 1)) (hj : j ∈ Icc 1 (p ^ (r - 1))) :
    p * j - s ∈ pfree p r := by
  have ⟨hs1, hs2⟩ := mem_Icc.mp hs
  have ⟨hj1, hj2⟩ := mem_Icc.mp hj
  have hs_lt : s < p := by omega
  have hpos : 0 < p * j - s := pval_pos hp.pos hs hj1
  have hlt : p * j - s < p ^ r := by
    have : p * j ≤ p * p ^ (r - 1) := Nat.mul_le_mul_left p hj2
    have hpow : p * p ^ (r - 1) = p ^ r := prime_mul_pow_pred hr
    have : p * j - s < p * j := Nat.sub_lt (Nat.mul_pos hp.pos hj1) (by omega)
    omega
  have hnd : ¬ p ∣ p * j - s := by
    intro hd
    have hz : ((p * j - s : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hd
    exact (pval_ne_zero hp hs hj1) hz
  exact mem_pfree.mpr ⟨hlt, hnd⟩

lemma pfree_eq_rectangle_image {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    (Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1))).image (fun ij => p * ij.2 - ij.1) =
      pfree p r := by
  ext t
  simp only [mem_image, mem_product]
  constructor
  · intro ⟨ij, ⟨hs, hj⟩, h⟩
    rw [← h]
    exact rectangle_mem_pfree hp hr hs hj
  · intro ht
    have ⟨htlt, hnd⟩ := mem_pfree.mp ht
    have ht0 : 0 < t := pfree_pos hp ht
    have hmodpos : 0 < t % p := by
      have : t % p ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
      exact Nat.pos_of_ne_zero this
    have hmodlt : t % p < p := Nat.mod_lt t hp.pos
    refine ⟨(p - t % p, t / p + 1), ?_, ?_⟩
    · constructor
      · refine mem_Icc.mpr ⟨?_, ?_⟩
        · have : t % p ≤ p - 1 := Nat.le_pred_of_lt hmodlt
          omega
        · have : 1 ≤ t % p := hmodpos
          omega
      · refine mem_Icc.mpr ⟨Nat.succ_pos _, ?_⟩
        have : t / p < p ^ (r - 1) := by
          rw [Nat.div_lt_iff_lt_mul hp.pos, mul_comm, prime_mul_pow_pred hr]
          exact htlt
        exact Nat.succ_le_iff.mpr this
    · have hle : p - t % p ≤ p * (t / p + 1) := by
        have : p - t % p ≤ p := Nat.sub_le _ _
        have : p ≤ p * (t / p + 1) := Nat.le_mul_of_pos_right p (Nat.succ_pos _)
        omega
      have : p * (t / p + 1) - (p - t % p) = t := by
        rw [Nat.mul_add, mul_one]
        have h1 : p * (t / p) + p - (p - t % p) = p * (t / p) + t % p := by
          omega
        rw [h1, Nat.div_add_mod]
      exact this

/-- Last-term cofactor sum is divisible by `p^r`. -/
lemma rectangle_map_inj {p B : ℕ} (hp : p.Prime)
    {ij kl : ℕ × ℕ}
    (hij : ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B)
    (hkl : kl ∈ Icc 1 (p - 1) ×ˢ Icc 1 B)
    (heq : p * ij.2 - ij.1 = p * kl.2 - kl.1) :
    ij = kl := by
  have hij' := mem_product.mp hij
  have hkl' := mem_product.mp hkl
  have ⟨hs1, hs2⟩ := mem_Icc.mp hij'.1
  have ⟨hs1', hs2'⟩ := mem_Icc.mp hkl'.1
  have ⟨hj1, _⟩ := mem_Icc.mp hij'.2
  have ⟨hj1', _⟩ := mem_Icc.mp hkl'.2
  have hs_lt : ij.1 < p := by omega
  have hs_lt' : kl.1 < p := by omega
  have hle : ij.1 ≤ p * ij.2 :=
    le_trans (Nat.le_of_lt hs_lt) (Nat.le_mul_of_pos_right p hj1)
  have hle' : kl.1 ≤ p * kl.2 :=
    le_trans (Nat.le_of_lt hs_lt') (Nat.le_mul_of_pos_right p hj1')
  have hZ : ((p * ij.2 : ℕ) : ℤ) - ij.1 = ((p * kl.2 : ℕ) : ℤ) - kl.1 := by
    have := congrArg (fun n : ℕ => (n : ℤ)) heq
    simpa [Nat.cast_sub hle, Nat.cast_sub hle'] using this
  have hdiff : (p : ℤ) * ((ij.2 : ℤ) - kl.2) = (ij.1 : ℤ) - kl.1 := by
    push_cast at hZ
    linear_combination hZ
  have habs : |(ij.1 : ℤ) - (kl.1 : ℤ)| < (p : ℤ) := by
    have h1 : (ij.1 : ℤ) < (p : ℤ) := by exact_mod_cast hs_lt
    have h2 : (kl.1 : ℤ) < (p : ℤ) := by exact_mod_cast hs_lt'
    have h3 : (0 : ℤ) ≤ ij.1 := Nat.cast_nonneg _
    have h4 : (0 : ℤ) ≤ kl.1 := Nat.cast_nonneg _
    rw [abs_lt]
    constructor <;> linarith
  have hdvd : (p : ℤ) ∣ (ij.1 : ℤ) - kl.1 := ⟨ij.2 - kl.2, by simpa using hdiff.symm⟩
  have hseq : (ij.1 : ℤ) - kl.1 = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  have hs_eq : ij.1 = kl.1 := by exact_mod_cast (sub_eq_zero.mp hseq)
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hj_eq : ij.2 = kl.2 := by
    have : (p : ℤ) * ((ij.2 : ℤ) - kl.2) = 0 := by
      rw [hdiff, hseq]
    have : (ij.2 : ℤ) - kl.2 = 0 :=
      (mul_eq_zero.mp this).resolve_left hp0
    exact_mod_cast (sub_eq_zero.mp this)
  exact Prod.ext hs_eq hj_eq

lemma sum_cofactor_last_dvd {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : 1 ≤ r) :
    (p : ℤ) ^ r ∣
      ∑ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)),
        ∏ kl ∈ (Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1))).erase ij,
          ((p * kl.2 - kl.1 : ℕ) : ℤ) := by
  set s : Finset (ℕ × ℕ) := Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1))
  set Pℤ : ℤ := ∏ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ℤ)
  set Sℤ : ℤ :=
    ∑ ij ∈ s, ∏ kl ∈ s.erase ij, ((p * kl.2 - kl.1 : ℕ) : ℤ)
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  have hsumZ : (Sℤ : ZMod (p ^ r)) =
      ∑ ij ∈ s, ∏ kl ∈ s.erase ij, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ r)) := by
    simp only [Sℤ, Int.cast_sum, Int.cast_prod, Int.cast_natCast]
  have hPZ : (Pℤ : ZMod (p ^ r)) =
      ∏ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ r)) := by
    simp only [Pℤ, Int.cast_prod, Int.cast_natCast]
  have hunit : ∀ ij ∈ s, IsUnit ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ r)) := by
    intro ij hij
    have hij' := mem_product.mp hij
    have mem := rectangle_mem_pfree hp hr hij'.1 hij'.2
    exact isUnit_of_mem_pfree hp (by omega) mem
  have hterm : ∀ ij ∈ s,
      ∏ kl ∈ s.erase ij, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ r)) =
        ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ r))⁻¹ *
          ∏ kl ∈ s, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ r)) := by
    intro ij hij
    have hu := hunit ij hij
    have hmul := Finset.mul_prod_erase s
      (fun kl => ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ r))) hij
    calc
      ∏ kl ∈ s.erase ij, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ r)) =
          ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ r))⁻¹ *
            (((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ r)) *
              ∏ kl ∈ s.erase ij, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ r))) := by
        rw [← mul_assoc, unit_inv_mul hu, one_mul]
      _ = ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ r))⁻¹ *
            ∏ kl ∈ s, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ r)) := by
        rw [hmul]
  have hH : ∑ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ r))⁻¹ = 0 := by
    have himg := pfree_eq_rectangle_image (p := p) (r := r) hp hr
    have hinj : Set.InjOn (fun ij : ℕ × ℕ => p * ij.2 - ij.1) s := by
      intro ij hij kl hkl heq
      exact rectangle_map_inj hp hij hkl heq
    have :
        ∑ t ∈ s.image (fun ij => p * ij.2 - ij.1), (t : ZMod (p ^ r))⁻¹ =
          ∑ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ r))⁻¹ :=
      Finset.sum_image hinj
    rw [← this, himg]
    exact sum_pfree_inv_eq_zero hp hp2 (by omega)
  have hfactor : (Sℤ : ZMod (p ^ r)) =
      (Pℤ : ZMod (p ^ r)) *
        ∑ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ r))⁻¹ := by
    rw [hsumZ, Finset.sum_congr rfl hterm, ← Finset.sum_mul, mul_comm, hPZ]
  have : (Sℤ : ZMod (p ^ r)) = 0 := by
    rw [hfactor, hH, mul_zero]
  exact (CharP.intCast_eq_zero_iff (ZMod (p ^ r)) (p ^ r) Sℤ).mp this

/-- Last-term `Q ≡ P [ZMOD p^{2r}]`. -/
lemma prod_add_pow_last {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r) :
    (∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)),
        (((p * ij.2 - ij.1 : ℕ) : ℤ) + (p : ℤ) ^ r)) ≡
      (∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)), ((p * ij.2 - ij.1 : ℕ) : ℤ))
      [ZMOD (p : ℤ) ^ (2 * r)] := by
  set s : Finset (ℕ × ℕ) := Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1))
  set x : ℕ × ℕ → ℤ := fun ij => ((p * ij.2 - ij.1 : ℕ) : ℤ)
  have hr1 : 1 ≤ r := by omega
  have hexp := prod_add_const_mod_sq (s := s) (x := x) (N := (p : ℤ) ^ r)
  have hcof := sum_cofactor_last_dvd (p := p) (r := r) hp hp2 hr1
  have hN2 : ((p : ℤ) ^ r) ^ 2 = (p : ℤ) ^ (2 * r) := by
    rw [← pow_mul, mul_comm]
  have hdvdN2 :
      (p : ℤ) ^ (2 * r) ∣
        (∏ i ∈ s, x i + (p : ℤ) ^ r * ∑ i ∈ s, ∏ j ∈ s.erase i, x j -
          ∏ i ∈ s, (x i + (p : ℤ) ^ r)) := by
    have := (Int.modEq_iff_dvd).mp hexp
    simpa [hN2] using this
  obtain ⟨K, hK⟩ := hdvdN2
  have hdecomp :
      ∏ i ∈ s, (x i + (p : ℤ) ^ r) - ∏ i ∈ s, x i =
        (p : ℤ) ^ r * ∑ i ∈ s, ∏ j ∈ s.erase i, x j - (p : ℤ) ^ (2 * r) * K := by
    linear_combination -hK
  obtain ⟨c, hc⟩ := hcof
  have hdiff :
      ∏ i ∈ s, (x i + (p : ℤ) ^ r) - ∏ i ∈ s, x i =
        (p : ℤ) ^ (2 * r) * (c - K) := by
    rw [hdecomp, hc]
    ring
  refine (Int.modEq_iff_dvd).mpr ?_
  refine ⟨-(c - K), ?_⟩
  linear_combination -hdiff

/-- Last-term `v(δ) ≥ 2r`. -/
lemma pow_dvd_delta_last {p r : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 2 ≤ r) :
    (p : ℤ) ^ (2 * r) ∣
      (rising (p ^ r) (p * p ^ (r - 1)) : ℤ) -
        risingY p r (p * p ^ (r - 1)) := by
  have hr1 : 1 ≤ r := by omega
  have hp2 : p ≠ 2 := by omega
  have hB : p ^ (r - 1) ≤ p ^ (r - 1) := le_rfl
  have hid := rising_sub_mul_pProd (p := p) (r := r) (B := p ^ (r - 1)) hp hr1 hB
  have hQmod := prod_add_pow_last (p := p) (r := r) hp hp2 hr
  have hcastQ :
      ((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)),
          (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) =
        ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)),
          (((p * ij.2 - ij.1 : ℕ) : ℤ) + (p : ℤ) ^ r) := by
    simp [Nat.cast_prod, Nat.cast_add, Nat.cast_pow]
  have hcastP : (pProd p (p ^ (r - 1)) : ℤ) =
      ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)),
        ((p * ij.2 - ij.1 : ℕ) : ℤ) := by
    simp [pProd_eq_prod_product, Nat.cast_prod]
  have hQP : (p : ℤ) ^ (2 * r) ∣
      ((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)),
          (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) -
        pProd p (p ^ (r - 1)) := by
    have h := (Int.modEq_iff_dvd).mp hQmod
    rw [hcastQ, hcastP]
    exact dvd_neg.mp (by simpa [neg_sub] using h)
  have hyQP : (p : ℤ) ^ (2 * r) ∣
      (risingY p r (p * p ^ (r - 1)) : ℤ) *
        (((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)),
            (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) - pProd p (p ^ (r - 1))) :=
    dvd_mul_of_dvd_right hQP _
  have hδP : (p : ℤ) ^ (2 * r) ∣
      ((rising (p ^ r) (p * p ^ (r - 1)) : ℤ) -
        risingY p r (p * p ^ (r - 1))) * (pProd p (p ^ (r - 1)) : ℤ) := by
    rwa [hid]
  haveI : Fact p.Prime := ⟨hp⟩
  have hPne : (pProd p (p ^ (r - 1)) : ℤ) ≠ 0 := by
    exact_mod_cast (ne_zero_of_lt (pProd_pos (p := p) hp.pos))
  by_cases hδ0 :
      ((rising (p ^ r) (p * p ^ (r - 1)) : ℤ) -
        risingY p r (p * p ^ (r - 1))) = 0
  · simp [hδ0]
  · have hge : 2 * r ≤
        padicValInt p
          (((rising (p ^ r) (p * p ^ (r - 1)) : ℤ) -
            risingY p r (p * p ^ (r - 1))) * pProd p (p ^ (r - 1))) :=
      (padicValInt_dvd_iff (p := p) (2 * r) _).mp hδP |>.resolve_left
        (mul_ne_zero hδ0 hPne)
    have hP0 : padicValInt p (pProd p (p ^ (r - 1)) : ℤ) = 0 := by
      rw [padicValInt.of_nat]
      exact padicValNat.eq_zero_of_not_dvd (p_not_dvd_pProd hp)
    have : 2 * r ≤
        padicValInt p
          ((rising (p ^ r) (p * p ^ (r - 1)) : ℤ) -
            risingY p r (p * p ^ (r - 1))) := by
      have hmulv := padicValInt.mul (p := p) hδ0 hPne
      omega
    exact (padicValInt_dvd_iff (p := p) (2 * r) _).mpr (Or.inr this)

/-- Last-term `S2d` for `p ≥ 5`, `r ≥ 3` (uses `v(δ) ≥ 2r`). -/
lemma increment_quad_dvd_last_ge3 {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 3 ≤ r) :
    (p : ℤ) ^ (3 * r + 3) ∣
      3 * (2 * (risingY p r (p * p ^ (r - 1)) : ℤ) + 1) *
        ((rising (p ^ r) (p * p ^ (r - 1)) : ℤ) -
          risingY p r (p * p ^ (r - 1))) ^ 2 := by
  have hp3 : 3 ≤ p := by omega
  have hr2 : 2 ≤ r := by omega
  have hδ := pow_dvd_delta_last hp hp3 hr2
  obtain ⟨t, ht⟩ := hδ
  refine ⟨3 * (2 * (risingY p r (p * p ^ (r - 1)) : ℤ) + 1) *
      ((p : ℤ) ^ (r - 3) * t ^ 2), ?_⟩
  have hδ2 :
      ((rising (p ^ r) (p * p ^ (r - 1)) : ℤ) -
        risingY p r (p * p ^ (r - 1))) ^ 2 =
      ((p : ℤ) ^ (2 * r)) ^ 2 * t ^ 2 := by
    rw [ht]; ring
  have hpow : ((p : ℤ) ^ (2 * r)) ^ 2 = (p : ℤ) ^ (4 * r) := by
    rw [← pow_mul, show (2 * r) * 2 = 4 * r by ring]
  rw [hδ2, hpow]
  have hsplit : 4 * r = (3 * r + 3) + (r - 3) := by omega
  calc
    3 * (2 * (risingY p r (p * p ^ (r - 1)) : ℤ) + 1) *
        ((p : ℤ) ^ (4 * r) * t ^ 2) =
      (3 * (2 * (risingY p r (p * p ^ (r - 1)) : ℤ) + 1) * t ^ 2) *
        (p : ℤ) ^ (4 * r) := by ring
    _ = (3 * (2 * (risingY p r (p * p ^ (r - 1)) : ℤ) + 1) * t ^ 2) *
          (p : ℤ) ^ ((3 * r + 3) + (r - 3)) := by simp [hsplit]
    _ = (p : ℤ) ^ (3 * r + 3) *
          (3 * (2 * (risingY p r (p * p ^ (r - 1)) : ℤ) + 1) *
            ((p : ℤ) ^ (r - 3) * t ^ 2)) := by
      rw [pow_add]; ring

/-- Last-term `S2d` for `p = 3`: `v(3δ²) ≥ 1+4r ≥ 3r+3`. -/
lemma increment_quad_dvd_last_three {r : ℕ} (hr : 2 ≤ r) :
    (3 : ℤ) ^ (3 * r + 3) ∣
      3 * (2 * (risingY 3 r (3 * 3 ^ (r - 1)) : ℤ) + 1) *
        ((rising (3 ^ r) (3 * 3 ^ (r - 1)) : ℤ) -
          risingY 3 r (3 * 3 ^ (r - 1))) ^ 2 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp3 : (3 : ℕ) ≤ 3 := le_rfl
  have hδ := pow_dvd_delta_last hp hp3 hr
  obtain ⟨t, ht⟩ := hδ
  refine ⟨(2 * (risingY 3 r (3 * 3 ^ (r - 1)) : ℤ) + 1) *
      ((3 : ℤ) ^ (r - 2) * t ^ 2), ?_⟩
  have hδ2 :
      ((rising (3 ^ r) (3 * 3 ^ (r - 1)) : ℤ) -
        risingY 3 r (3 * 3 ^ (r - 1))) ^ 2 =
      ((3 : ℤ) ^ (2 * r)) ^ 2 * t ^ 2 := by
    rw [ht]; ring
  have hpow : ((3 : ℤ) ^ (2 * r)) ^ 2 = (3 : ℤ) ^ (4 * r) := by
    rw [← pow_mul, show (2 * r) * 2 = 4 * r by ring]
  rw [hδ2, hpow]
  have hsplit : 4 * r + 1 = (3 * r + 3) + (r - 2) := by omega
  calc
    (3 : ℤ) * (2 * (risingY 3 r (3 * 3 ^ (r - 1)) : ℤ) + 1) *
        ((3 : ℤ) ^ (4 * r) * t ^ 2) =
      (2 * (risingY 3 r (3 * 3 ^ (r - 1)) : ℤ) + 1) *
        ((3 : ℤ) ^ 1 * (3 : ℤ) ^ (4 * r) * t ^ 2) := by ring
    _ = (2 * (risingY 3 r (3 * 3 ^ (r - 1)) : ℤ) + 1) *
          ((3 : ℤ) ^ (4 * r + 1) * t ^ 2) := by
      rw [← pow_add]; ring
    _ = (2 * (risingY 3 r (3 * 3 ^ (r - 1)) : ℤ) + 1) *
          ((3 : ℤ) ^ ((3 * r + 3) + (r - 2)) * t ^ 2) := by
      simp [hsplit]
    _ = (3 : ℤ) ^ (3 * r + 3) *
          ((2 * (risingY 3 r (3 * 3 ^ (r - 1)) : ℤ) + 1) *
            ((3 : ℤ) ^ (r - 2) * t ^ 2)) := by
      rw [pow_add]; ring


/-- General `S2d` bound from `v(δ) ≥ v(y)+r+2` when this is enough. -/
lemma increment_quad_dvd_of_val {p r B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 2 ≤ r) (hB0 : 0 < B) (hB : B ≤ p ^ (r - 1))
    (hval : 2 * ((r - 1) - padicValNat p B) + 2 * r + 4 ≥ 3 * r + 3) :
    (p : ℤ) ^ (3 * r + 3) ∣
      3 * (2 * (risingY p r (p * B) : ℤ) + 1) *
        ((rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B)) ^ 2 := by
  have hr1 : 1 ≤ r := by omega
  have hδ := pow_dvd_delta_with_y (p := p) (r := r) (B := B) hp hp5 hr hB
  have hy : padicValInt p (risingY p r (p * B) : ℤ) =
      (r - 1) - padicValNat p B :=
    padicValInt_risingY hp hr1 hB0 hB
  rw [hy] at hδ
  set e := (r - 1) - padicValNat p B + r + 2
  have hδ' : (p : ℤ) ^ e ∣
      (rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B) := hδ
  obtain ⟨t, ht⟩ := hδ'
  have h2e : 2 * e ≥ 3 * r + 3 := by
    have : e = (r - 1) - padicValNat p B + r + 2 := rfl
    omega
  refine ⟨3 * (2 * (risingY p r (p * B) : ℤ) + 1) *
      ((p : ℤ) ^ (2 * e - (3 * r + 3)) * t ^ 2), ?_⟩
  have hδ2 :
      ((rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B)) ^ 2 =
      ((p : ℤ) ^ e) ^ 2 * t ^ 2 := by
    rw [ht]; ring
  have hpow : ((p : ℤ) ^ e) ^ 2 = (p : ℤ) ^ (2 * e) := by
    rw [← pow_mul, mul_comm]
  rw [hδ2, hpow]
  have hexp : (p : ℤ) ^ (2 * e) =
      (p : ℤ) ^ (3 * r + 3) * (p : ℤ) ^ (2 * e - (3 * r + 3)) := by
    rw [← pow_add, Nat.add_sub_of_le h2e]
  rw [hexp]
  ring


/-! ### Exact formula for the p-free reduced binomial `u_k` -/

lemma choose_mul_right_of_rising (n k : ℕ) (hk : 0 < k) :
    rising n k * k = choose (n + k - 1) (k - 1) * n := by
  unfold rising
  have hkpred : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
  rw [hkpred, choose_succ_right_eq]
  congr 1
  omega



/-! ### Splitting the increment sum -/

lemma incrementZ_split (p r k : ℕ) :
    incrementZ p r k =
      6 * (risingY p r k : ℤ) * ((risingY p r k : ℤ) + 1) *
        ((rising (p ^ r) k : ℤ) - risingY p r k) +
      3 * (2 * (risingY p r k : ℤ) + 1) *
        ((rising (p ^ r) k : ℤ) - risingY p r k) ^ 2 +
      2 * ((rising (p ^ r) k : ℤ) - risingY p r k) ^ 3 :=
  incrementZ_eq_poly p r k

def S1d (p r : ℕ) : ℤ :=
  ∑ k ∈ (range (p ^ r + 1)).filter (p ∣ ·),
    6 * (risingY p r k : ℤ) * ((risingY p r k : ℤ) + 1) *
      ((rising (p ^ r) k : ℤ) - risingY p r k)

def S2d (p r : ℕ) : ℤ :=
  ∑ k ∈ (range (p ^ r + 1)).filter (p ∣ ·),
    3 * (2 * (risingY p r k : ℤ) + 1) *
      ((rising (p ^ r) k : ℤ) - risingY p r k) ^ 2

def S3d (p r : ℕ) : ℤ :=
  ∑ k ∈ (range (p ^ r + 1)).filter (p ∣ ·),
    2 * ((rising (p ^ r) k : ℤ) - risingY p r k) ^ 3

def S2f (p r : ℕ) : ℤ :=
  ∑ k ∈ (range (p ^ r + 1)).filter (¬p ∣ ·),
    3 * (rising (p ^ r) k : ℤ) ^ 2

def S3f (p r : ℕ) : ℤ :=
  ∑ k ∈ (range (p ^ r + 1)).filter (¬p ∣ ·),
    2 * (rising (p ^ r) k : ℤ) ^ 3

lemma increment_sum_split (p r : ℕ) :
    ∑ k ∈ range (p ^ r + 1), incrementZ p r k =
      S1d p r + S2d p r + S3d p r + S2f p r + S3f p r := by
  have hsplit :=
    (Finset.sum_filter_add_sum_filter_not (range (p ^ r + 1)) (p ∣ ·)
      (incrementZ p r))
  unfold S1d S2d S3d S2f S3f
  have hdiv : ∑ k ∈ (range (p ^ r + 1)).filter (p ∣ ·), incrementZ p r k =
      ∑ k ∈ (range (p ^ r + 1)).filter (p ∣ ·),
        (6 * (risingY p r k : ℤ) * ((risingY p r k : ℤ) + 1) *
          ((rising (p ^ r) k : ℤ) - risingY p r k) +
        3 * (2 * (risingY p r k : ℤ) + 1) *
          ((rising (p ^ r) k : ℤ) - risingY p r k) ^ 2 +
        2 * ((rising (p ^ r) k : ℤ) - risingY p r k) ^ 3) := by
    refine Finset.sum_congr rfl ?_
    intro k hk; exact incrementZ_split p r k
  have hnd : ∑ k ∈ (range (p ^ r + 1)).filter (¬p ∣ ·), incrementZ p r k =
      ∑ k ∈ (range (p ^ r + 1)).filter (¬p ∣ ·),
        (3 * (rising (p ^ r) k : ℤ) ^ 2 +
          2 * (rising (p ^ r) k : ℤ) ^ 3) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hdv : ¬ p ∣ k := (mem_filter.mp hk).2
    have hy : risingY p r k = 0 := risingY_of_not_dvd hdv
    rw [incrementZ_split, hy]
    ring
  rw [← hsplit, hdiv, hnd, sum_add_distrib, sum_add_distrib, sum_add_distrib]
  abel

lemma S3d_dvd {p r : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 1 ≤ r) :
    (p : ℤ) ^ (3 * r + 3) ∣ S3d p r := by
  unfold S3d
  refine dvd_sum ?_
  intro k hk
  have hkle : k ≤ p ^ r :=
    Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hk).1)
  have hdv : p ∣ k := (mem_filter.mp hk).2
  exact increment_cubic_dvd hp hp3 hr hkle hdv





/-! ### Elementary symmetric sums for the product expansion -/

def esym1 {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℤ) : ℤ :=
  ∑ i ∈ s, ∏ j ∈ s.erase i, x j

def esym2 {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℤ) : ℤ :=
  ∑ i ∈ s, ∑ j ∈ s.erase i, ∏ k ∈ (s.erase i).erase j, x k

lemma insert_erase_comm {ι : Type*} [DecidableEq ι] {a i : ι} {s : Finset ι}
    (ha : a ∉ s) (hi : i ∈ s) :
    (insert a s).erase i = insert a (s.erase i) := by
  ext z
  simp [mem_erase, mem_insert]
  constructor
  · rintro ⟨hzi, rfl | hz⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hzi, hz⟩
  · rintro (rfl | ⟨hzi, hz⟩)
    · exact ⟨(ne_of_mem_of_not_mem hi ha).symm, Or.inl rfl⟩
    · exact ⟨hzi, Or.inr hz⟩

lemma esym1_insert {ι : Type*} [DecidableEq ι] {a : ι} {s : Finset ι} (ha : a ∉ s)
    (x : ι → ℤ) :
    esym1 (insert a s) x = (∏ i ∈ s, x i) + x a * esym1 s x := by
  unfold esym1
  rw [sum_insert ha, erase_insert ha, Finset.mul_sum]
  refine congrArg (fun t => (∏ i ∈ s, x i) + t) ?_
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hne : i ≠ a := fun h => ha (h ▸ hi)
  rw [erase_insert_of_ne hne.symm, prod_insert (by simp [mem_erase, ha])]

lemma inner_esym2_insert {ι : Type*} [DecidableEq ι] {a i : ι} {s : Finset ι}
    (ha : a ∉ s) (hi : i ∈ s) (x : ι → ℤ) :
    ∑ j ∈ (insert a s).erase i, ∏ k ∈ ((insert a s).erase i).erase j, x k =
      (∏ k ∈ s.erase i, x k) +
        x a * ∑ j ∈ s.erase i, ∏ k ∈ (s.erase i).erase j, x k := by
  rw [insert_erase_comm ha hi, sum_insert (by simp [ha]),
    erase_insert (by simp [ha]), Finset.mul_sum]
  refine congrArg (fun t => (∏ k ∈ s.erase i, x k) + t) ?_
  refine Finset.sum_congr rfl ?_
  intro j hj
  have : (insert a (s.erase i)).erase j = insert a ((s.erase i).erase j) := by
    exact insert_erase_comm (by simp [ha]) hj
  rw [this, prod_insert (by simp [mem_erase, ha])]

lemma esym2_insert {ι : Type*} [DecidableEq ι] {a : ι} {s : Finset ι} (ha : a ∉ s)
    (x : ι → ℤ) :
    esym2 (insert a s) x = 2 * esym1 s x + x a * esym2 s x := by
  unfold esym2
  rw [sum_insert ha, erase_insert ha]
  have hsum := Finset.sum_congr (rfl : s = s)
    (fun i hi => inner_esym2_insert ha hi x)
  rw [hsum, sum_add_distrib, Finset.mul_sum]
  simp only [esym1]
  ring

/-- The cubic expansion identity: `2(Q - P - N σ₁) ≡ N² σ₂ [ZMOD N³]`. -/
lemma prod_add_const_mod_cube {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (x : ι → ℤ) (N : ℤ) :
    2 * (∏ i ∈ s, (x i + N) - ∏ i ∈ s, x i - N * esym1 s x) ≡
      N ^ 2 * esym2 s x [ZMOD N ^ 3] := by
  induction s using Finset.induction_on with
  | empty =>
    simp [esym1, esym2]
  | insert a s ha ih =>
    set P := ∏ i ∈ s, x i with hPdef
    set Q := ∏ i ∈ s, (x i + N) with hQdef
    have hP' : ∏ i ∈ insert a s, x i = x a * P := by
      rw [hPdef]; exact prod_insert ha
    have hQ' : ∏ i ∈ insert a s, (x i + N) = (x a + N) * Q := by
      rw [hQdef]; exact prod_insert ha
    have hσ1 := esym1_insert (a := a) (s := s) ha x
    have hσ2 := esym2_insert (a := a) (s := s) ha x
    have htarget :
        2 * ((∏ i ∈ insert a s, (x i + N)) - (∏ i ∈ insert a s, x i) -
          N * esym1 (insert a s) x) =
          2 * x a * (Q - P - N * esym1 s x) + 2 * N * (Q - P) := by
      rw [hQ', hP', hσ1]; ring
    have hQP_split : 2 * N * (Q - P) =
        2 * N * (Q - P - N * esym1 s x) + 2 * N ^ 2 * esym1 s x := by ring
    have hmid : 2 * N * (Q - P - N * esym1 s x) ≡ 0 [ZMOD N ^ 3] := by
      have hmul := Int.ModEq.mul (Int.ModEq.refl N) ih
      have h' : 2 * N * (Q - P - N * esym1 s x) ≡ N ^ 3 * esym2 s x [ZMOD N ^ 3] := by
        convert hmul using 1 <;> ring
      exact h'.trans (Int.modEq_zero_iff_dvd.mpr ⟨esym2 s x, by ring⟩)
    have hQP : 2 * N * (Q - P) ≡ 2 * N ^ 2 * esym1 s x [ZMOD N ^ 3] := by
      rw [hQP_split]
      simpa using Int.ModEq.add hmid (Int.ModEq.refl (2 * N ^ 2 * esym1 s x))
    have hxa : 2 * x a * (Q - P - N * esym1 s x) ≡
        x a * (N ^ 2 * esym2 s x) [ZMOD N ^ 3] := by
      have hmul := Int.ModEq.mul (Int.ModEq.refl (x a)) ih
      convert hmul using 1 <;> ring
    have hsum := Int.ModEq.add hxa hQP
    rw [htarget]
    have hrhs : x a * (N ^ 2 * esym2 s x) + 2 * N ^ 2 * esym1 s x =
        N ^ 2 * esym2 (insert a s) x := by
      rw [hσ2]; ring
    rwa [← hrhs]


/-! ### Last-term harmonic sum in `ZMod (p^3)` for `r = 2` -/

lemma inv_add_inv_of_unit {n : ℕ} {a b : ZMod n} (ha : IsUnit a) (hb : IsUnit b) :
    a⁻¹ + b⁻¹ = (a + b) * (a * b)⁻¹ := by
  have hab : IsUnit (a * b) := ha.mul hb
  have hL : a * b * (a⁻¹ + b⁻¹) = a + b := by
    rw [mul_add]
    have h1 : a * b * a⁻¹ = b := by
      calc
        a * b * a⁻¹ = a * a⁻¹ * b := by ring
        _ = 1 * b := by rw [unit_mul_inv ha]
        _ = b := by ring
    have h2 : a * b * b⁻¹ = a := by
      rw [mul_assoc, unit_mul_inv hb, mul_one]
    rw [h1, h2, add_comm]
  have hR : a * b * ((a + b) * (a * b)⁻¹) = a + b := by
    have h := unit_mul_inv hab
    linear_combination (a + b) * h
  have heq := hL.trans hR.symm
  have := congrArg (fun z : ZMod n => (a * b)⁻¹ * z) heq
  simpa [← mul_assoc, unit_inv_mul hab] using this

lemma pfree_isUnit_pow {p r k n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hk : k ∈ pfree p r) :
    IsUnit (k : ZMod (p ^ n)) := by
  have hnd := (mem_pfree.mp hk).2
  rw [ZMod.isUnit_iff_coprime]
  have : Nat.Coprime p k := (hp.coprime_iff_not_dvd).mpr hnd
  exact this.symm.pow_right n

lemma pair_inv_sum_p3 {p k : ℕ} (hp : p.Prime) (hk : k ∈ pfree p 2) :
    (k : ZMod (p ^ 3))⁻¹ + ((p ^ 2 - k : ℕ) : ZMod (p ^ 3))⁻¹ =
      (p : ZMod (p ^ 3)) ^ 2 *
        ((k : ZMod (p ^ 3)) * ((p ^ 2 - k : ℕ) : ZMod (p ^ 3)))⁻¹ := by
  have hu := pfree_isUnit_pow (p := p) (r := 2) (k := k) (n := 3) hp (by decide) hk
  have hk' : p ^ 2 - k ∈ pfree p 2 := pfree_sub hp (by decide) hk
  have hu' := pfree_isUnit_pow (p := p) (r := 2) (k := p ^ 2 - k) (n := 3)
    hp (by decide) hk'
  have hadd : (k : ZMod (p ^ 3)) + ((p ^ 2 - k : ℕ) : ZMod (p ^ 3)) =
      (p : ZMod (p ^ 3)) ^ 2 := by
    have hle : k ≤ p ^ 2 := le_of_lt (mem_pfree.mp hk).1
    rw [Nat.cast_sub hle, Nat.cast_pow]
    ring
  rw [inv_add_inv_of_unit hu hu', hadd]


lemma two_isUnit_p3 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    IsUnit (2 : ZMod (p ^ 3)) := by
  rw [isUnit_iff_not_dvd_val hp (by decide : 0 < 3)]
  intro h
  have hval : (2 : ZMod (p ^ 3)).val = 2 := by
    apply ZMod.val_natCast_of_lt
    have : 2 ≤ p := hp.two_le
    have h8 : 8 ≤ p ^ 3 :=
      calc
        8 = 2 ^ 3 := by decide
        _ ≤ p ^ 3 := Nat.pow_le_pow_left this 3
    exact Nat.lt_of_lt_of_le (by decide : 2 < 8) h8
  rw [hval] at h
  have hcases := (Nat.dvd_prime Nat.prime_two).mp h
  rcases hcases with h1 | h2'
  · exact hp.ne_one h1
  · exact hp2 h2'

lemma sum_pair_inv_p3 {p : ℕ} (hp : p.Prime) :
    ∑ k ∈ pfree p 2,
        ((k : ZMod (p ^ 3))⁻¹ + ((p ^ 2 - k : ℕ) : ZMod (p ^ 3))⁻¹) =
      2 * ∑ k ∈ pfree p 2, (k : ZMod (p ^ 3))⁻¹ := by
  have hperm :
      ∑ k ∈ pfree p 2, ((p ^ 2 - k : ℕ) : ZMod (p ^ 3))⁻¹ =
        ∑ k ∈ pfree p 2, (k : ZMod (p ^ 3))⁻¹ := by
    refine Finset.sum_bij (fun k _ => p ^ 2 - k) ?_ ?_ ?_ ?_
    · intro k hk; exact pfree_sub hp (by decide) hk
    · intro k hk k' hk' h
      have := congrArg (fun t => p ^ 2 - t) h
      simpa [pfree_sub_sub hp hk, pfree_sub_sub hp hk'] using this
    · intro k hk
      refine ⟨p ^ 2 - k, pfree_sub hp (by decide) hk, pfree_sub_sub hp hk⟩
    · intro k hk; rfl
  rw [sum_add_distrib, hperm, two_mul]

lemma pfree_prod_sub_eq {p k : ℕ} (hp : p.Prime) (hk : k ∈ pfree p 2) :
    ((k * (p ^ 2 - k) : ℕ) : ZMod (p ^ 3)) =
      (k : ZMod (p ^ 3)) * ((p ^ 2 - k : ℕ) : ZMod (p ^ 3)) := by
  simp [Nat.cast_mul]

lemma pfree_prod_cong_neg_sq {p k : ℕ} (hp : p.Prime) (hk : k ∈ pfree p 2) :
    ((k : ZMod p) * ((p ^ 2 - k : ℕ) : ZMod p)) = -((k : ZMod p) ^ 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hle : k ≤ p ^ 2 := le_of_lt (mem_pfree.mp hk).1
  have hp0 : (p : ZMod p) = 0 := CharP.cast_eq_zero (ZMod p) p
  rw [Nat.cast_sub hle, Nat.cast_pow]
  have : (p : ZMod p) ^ 2 = 0 := by rw [hp0]; simp
  rw [this]
  ring

lemma castHom_eq_zero_iff_p_dvd {p : ℕ} [Fact p.Prime] (x : ZMod (p ^ 3)) :
    ZMod.castHom (dvd_pow_self p (by decide : (3 : ℕ) ≠ 0)) (ZMod p) x = 0 ↔
      p ∣ x.val := by
  constructor
  · intro h
    have : (x.val : ZMod p) = 0 := by
      simpa [ZMod.castHom_apply] using h
    exact (ZMod.natCast_eq_zero_iff x.val p).mp this
  · intro h
    have : (x.val : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff x.val p).mpr h
    simpa [ZMod.castHom_apply] using this

lemma p2_mul_of_castHom_zero {p : ℕ} [Fact p.Prime] {x : ZMod (p ^ 3)}
    (h : ZMod.castHom (dvd_pow_self p (by decide : (3 : ℕ) ≠ 0)) (ZMod p) x = 0) :
    (p : ZMod (p ^ 3)) ^ 2 * x = 0 := by
  have hdvd : p ∣ x.val := (castHom_eq_zero_iff_p_dvd x).mp h
  obtain ⟨t, ht⟩ := hdvd
  have hx : x = (x.val : ZMod (p ^ 3)) := (ZMod.natCast_zmod_val x).symm
  have hxt : x = ((p * t : ℕ) : ZMod (p ^ 3)) := by
    rw [hx, ht]
  rw [hxt]
  have hmul : (p : ZMod (p ^ 3)) ^ 2 * ((p * t : ℕ) : ZMod (p ^ 3)) =
      ((p ^ 3 : ℕ) : ZMod (p ^ 3)) * t := by
    simp [pow_three, Nat.cast_pow, Nat.cast_mul]
    ring
  rw [hmul, ZMod.natCast_self, zero_mul]

lemma pair_inv_eq_neg_p2_invsq {p k : ℕ} (hp : p.Prime) (hk : k ∈ pfree p 2) :
    (k : ZMod (p ^ 3))⁻¹ + ((p ^ 2 - k : ℕ) : ZMod (p ^ 3))⁻¹ =
      -((p : ZMod (p ^ 3)) ^ 2 * ((k : ZMod (p ^ 3))⁻¹) ^ 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hu := pfree_isUnit_pow (p := p) (r := 2) (n := 3) hp (by decide) hk
  rw [pair_inv_sum_p3 hp hk]
  have hgoal :
      (p : ZMod (p ^ 3)) ^ 2 *
        (((k : ZMod (p ^ 3)) * ((p ^ 2 - k : ℕ) : ZMod (p ^ 3)))⁻¹ +
          ((k : ZMod (p ^ 3))⁻¹) ^ 2) = 0 := by
    apply p2_mul_of_castHom_zero
    set π := ZMod.castHom (dvd_pow_self p (by decide : (3 : ℕ) ≠ 0)) (ZMod p)
    have hu' : IsUnit ((k : ZMod (p ^ 3)) * ((p ^ 2 - k : ℕ) : ZMod (p ^ 3))) := by
      have hk' : p ^ 2 - k ∈ pfree p 2 := pfree_sub hp (by decide) hk
      exact (pfree_isUnit_pow (n := 3) hp (by decide) hk).mul
        (pfree_isUnit_pow (n := 3) hp (by decide) hk')
    have hle : k ≤ p ^ 2 := le_of_lt (mem_pfree.mp hk).1
    have hp0 : (p : ZMod p) = 0 := CharP.cast_eq_zero (ZMod p) p
    have hcast_p : π (p : ZMod (p ^ 3)) = 0 := by
      simp [π, ZMod.castHom_apply, hp0]
    have hcast_sub : π ((p ^ 2 - k : ℕ) : ZMod (p ^ 3)) = - π (k : ZMod (p ^ 3)) := by
      have hrew : ((p ^ 2 - k : ℕ) : ZMod (p ^ 3)) =
          (p : ZMod (p ^ 3)) ^ 2 - k := by
        rw [Nat.cast_sub hle, Nat.cast_pow]
      rw [hrew, map_sub, map_pow, hcast_p]
      simp
    have hcast_prod :
        π ((k : ZMod (p ^ 3)) * ((p ^ 2 - k : ℕ) : ZMod (p ^ 3))) =
          - (π (k : ZMod (p ^ 3))) ^ 2 := by
      rw [map_mul, hcast_sub]
      ring
    have hcast_inv :
        π (((k : ZMod (p ^ 3)) * ((p ^ 2 - k : ℕ) : ZMod (p ^ 3)))⁻¹) =
          (π ((k : ZMod (p ^ 3)) * ((p ^ 2 - k : ℕ) : ZMod (p ^ 3))))⁻¹ := by
      refine (ZMod.inv_eq_of_mul_eq_one p
          (π ((k : ZMod (p ^ 3)) * ((p ^ 2 - k : ℕ) : ZMod (p ^ 3))))
          (π (((k : ZMod (p ^ 3)) * ((p ^ 2 - k : ℕ) : ZMod (p ^ 3)))⁻¹))
          ?_).symm
      rw [← map_mul, unit_mul_inv hu', map_one]
    rw [map_add, hcast_inv, hcast_prod, map_pow]
    have hkinv : π ((k : ZMod (p ^ 3))⁻¹) = (π (k : ZMod (p ^ 3)))⁻¹ := by
      refine (ZMod.inv_eq_of_mul_eq_one p (π (k : ZMod (p ^ 3)))
          (π ((k : ZMod (p ^ 3))⁻¹)) ?_).symm
      rw [← map_mul, unit_mul_inv hu, map_one]
    rw [hkinv]
    set a := π (k : ZMod (p ^ 3))
    have hk0 : a ≠ 0 := by
      intro h0
      have : p ∣ k := by
        have : (k : ZMod p) = 0 := by
          simpa [a, π, ZMod.castHom_apply] using h0
        exact (ZMod.natCast_eq_zero_iff k p).mp this
      exact (mem_pfree.mp hk).2 this
    have hneg : (-(a ^ 2))⁻¹ = - (a⁻¹) ^ 2 := by
      refine ZMod.inv_eq_of_mul_eq_one p _ _ ?_
      have ha_unit : IsUnit a := isUnit_iff_ne_zero.mpr hk0
      have hsq : a ^ 2 * (a⁻¹) ^ 2 = 1 := by
        rw [← mul_pow, unit_mul_inv ha_unit, one_pow]
      rw [neg_mul_neg]
      exact hsq
    rw [hneg]
    ring
  linear_combination hgoal

lemma sum_pfree_inv_sq_mod_p {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∑ k ∈ pfree p 2, ((k : ZMod p)⁻¹) ^ 2) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hr : 1 ≤ 2 := by decide
  set s : Finset (ℕ × ℕ) := Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (2 - 1))
  have himg := pfree_eq_rectangle_image (p := p) (r := 2) hp hr
  have hinj : Set.InjOn (fun ij : ℕ × ℕ => p * ij.2 - ij.1) s := by
    intro ij hij kl hkl heq
    exact rectangle_map_inj hp hij hkl heq
  have hsum :
      ∑ k ∈ pfree p 2, ((k : ZMod p)⁻¹) ^ 2 =
        ∑ ij ∈ s, (((p * ij.2 - ij.1 : ℕ) : ZMod p)⁻¹) ^ 2 := by
    rw [← himg, Finset.sum_image hinj]
  rw [hsum]
  have hsB : s = Icc 1 (p - 1) ×ˢ Icc 1 p := by
    simp [s]
  rw [hsB]
  have hterm : ∀ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 p,
      (((p * ij.2 - ij.1 : ℕ) : ZMod p)⁻¹) ^ 2 = ((-(ij.1 : ZMod p))⁻¹) ^ 2 := by
    intro ij hij
    have hij' := mem_product.mp hij
    have ⟨hs1, hs2⟩ := mem_Icc.mp hij'.1
    have ⟨hj1, _⟩ := mem_Icc.mp hij'.2
    have hs_lt : ij.1 < p := by omega
    have hle : ij.1 ≤ p * ij.2 :=
      le_trans (Nat.le_of_lt hs_lt) (Nat.le_mul_of_pos_right p hj1)
    have hp0 : (p : ZMod p) = 0 := CharP.cast_eq_zero (ZMod p) p
    have : ((p * ij.2 - ij.1 : ℕ) : ZMod p) = - (ij.1 : ZMod p) := by
      rw [Nat.cast_sub hle, Nat.cast_mul, hp0, zero_mul, zero_sub]
    rw [this]
  rw [Finset.sum_congr rfl hterm, Finset.sum_product]
  have : ∑ t ∈ Icc 1 (p - 1), ∑ _j ∈ Icc 1 p,
      ((-(t : ZMod p))⁻¹) ^ 2 =
      ∑ t ∈ Icc 1 (p - 1), (p : ZMod p) * ((-(t : ZMod p))⁻¹) ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro t ht
    rw [Finset.sum_const, nsmul_eq_mul, card_Icc]
    simp
  rw [this]
  have hp0 : (p : ZMod p) = 0 := CharP.cast_eq_zero (ZMod p) p
  simp [hp0]

lemma sum_pfree_inv_p3_eq_zero {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∑ k ∈ pfree p 2, (k : ZMod (p ^ 3))⁻¹ = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have h2u := two_isUnit_p3 hp hp2
  have hpairs := sum_pair_inv_p3 (p := p) hp
  have hterm : ∀ k ∈ pfree p 2,
      (k : ZMod (p ^ 3))⁻¹ + ((p ^ 2 - k : ℕ) : ZMod (p ^ 3))⁻¹ =
        -((p : ZMod (p ^ 3)) ^ 2 * ((k : ZMod (p ^ 3))⁻¹) ^ 2) :=
    fun k hk => pair_inv_eq_neg_p2_invsq hp hk
  have hsum :
      ∑ k ∈ pfree p 2,
          ((k : ZMod (p ^ 3))⁻¹ + ((p ^ 2 - k : ℕ) : ZMod (p ^ 3))⁻¹) =
        -((p : ZMod (p ^ 3)) ^ 2 *
          ∑ k ∈ pfree p 2, ((k : ZMod (p ^ 3))⁻¹) ^ 2) := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, Finset.mul_sum]
  have hcast :
      ZMod.castHom (dvd_pow_self p (by decide : (3 : ℕ) ≠ 0)) (ZMod p)
        (∑ k ∈ pfree p 2, ((k : ZMod (p ^ 3))⁻¹) ^ 2) = 0 := by
    rw [map_sum]
    have hcongr : ∀ k ∈ pfree p 2,
        ZMod.castHom (dvd_pow_self p (by decide : (3 : ℕ) ≠ 0)) (ZMod p)
          (((k : ZMod (p ^ 3))⁻¹) ^ 2) = ((k : ZMod p)⁻¹) ^ 2 := by
      intro k hk
      rw [map_pow]
      have hu := pfree_isUnit_pow (n := 3) hp (by decide) hk
      have hinv :
          ZMod.castHom (dvd_pow_self p (by decide : (3 : ℕ) ≠ 0)) (ZMod p)
            ((k : ZMod (p ^ 3))⁻¹) =
          (ZMod.castHom (dvd_pow_self p (by decide : (3 : ℕ) ≠ 0)) (ZMod p)
            (k : ZMod (p ^ 3)))⁻¹ := by
        refine (ZMod.inv_eq_of_mul_eq_one p _ _ ?_).symm
        rw [← map_mul, unit_mul_inv hu, map_one]
      rw [hinv]
      simp [ZMod.castHom_apply]
    rw [Finset.sum_congr rfl hcongr, sum_pfree_inv_sq_mod_p hp hp5]
  have hmul0 :
      (p : ZMod (p ^ 3)) ^ 2 * ∑ k ∈ pfree p 2, ((k : ZMod (p ^ 3))⁻¹) ^ 2 = 0 :=
    p2_mul_of_castHom_zero hcast
  have : 2 * ∑ k ∈ pfree p 2, (k : ZMod (p ^ 3))⁻¹ = 0 := by
    rw [← hpairs, hsum, hmul0, neg_zero]
  have hcancel := congrArg (fun z => (2 : ZMod (p ^ 3))⁻¹ * z) this
  simpa [← mul_assoc, unit_inv_mul h2u] using hcancel

/-- Last-term cofactor sum is divisible by `p^3` when `r = 2`. -/
lemma sum_cofactor_last_dvd_cube {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p : ℤ) ^ 3 ∣
      ∑ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 p,
        ∏ kl ∈ (Icc 1 (p - 1) ×ˢ Icc 1 p).erase ij,
          ((p * kl.2 - kl.1 : ℕ) : ℤ) := by
  set s : Finset (ℕ × ℕ) := Icc 1 (p - 1) ×ˢ Icc 1 p
  set Pℤ : ℤ := ∏ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ℤ)
  set Sℤ : ℤ :=
    ∑ ij ∈ s, ∏ kl ∈ s.erase ij, ((p * kl.2 - kl.1 : ℕ) : ℤ)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  have hr : 1 ≤ 2 := by decide
  have hp2 : p ≠ 2 := by omega
  have hsumZ : (Sℤ : ZMod (p ^ 3)) =
      ∑ ij ∈ s, ∏ kl ∈ s.erase ij, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ 3)) := by
    simp only [Sℤ, Int.cast_sum, Int.cast_prod, Int.cast_natCast]
  have hPZ : (Pℤ : ZMod (p ^ 3)) =
      ∏ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ 3)) := by
    simp only [Pℤ, Int.cast_prod, Int.cast_natCast]
  have hsB : Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (2 - 1)) = s := by
    simp [s]
  have hunit : ∀ ij ∈ s, IsUnit ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ 3)) := by
    intro ij hij
    have : ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (2 - 1)) := by
      rwa [hsB]
    have hij' := mem_product.mp this
    have mem := rectangle_mem_pfree hp hr hij'.1 hij'.2
    exact pfree_isUnit_pow (n := 3) hp (by decide) mem
  have hterm : ∀ ij ∈ s,
      ∏ kl ∈ s.erase ij, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ 3)) =
        ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ 3))⁻¹ *
          ∏ kl ∈ s, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ 3)) := by
    intro ij hij
    have hu := hunit ij hij
    have hmul := Finset.mul_prod_erase s
      (fun kl => ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ 3))) hij
    calc
      ∏ kl ∈ s.erase ij, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ 3)) =
          ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ 3))⁻¹ *
            (((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ 3)) *
              ∏ kl ∈ s.erase ij, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ 3))) := by
        rw [← mul_assoc, unit_inv_mul hu, one_mul]
      _ = ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ 3))⁻¹ *
            ∏ kl ∈ s, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ 3)) := by
        rw [hmul]
  have hH : ∑ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ 3))⁻¹ = 0 := by
    have himg : s.image (fun ij => p * ij.2 - ij.1) = pfree p 2 := by
      simpa [hsB] using pfree_eq_rectangle_image (p := p) (r := 2) hp hr
    have hinj : Set.InjOn (fun ij : ℕ × ℕ => p * ij.2 - ij.1) s := by
      intro ij hij kl hkl heq
      exact rectangle_map_inj hp hij hkl heq
    have :
        ∑ t ∈ s.image (fun ij => p * ij.2 - ij.1), (t : ZMod (p ^ 3))⁻¹ =
          ∑ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ 3))⁻¹ :=
      Finset.sum_image hinj
    rw [← this, himg]
    exact sum_pfree_inv_p3_eq_zero hp hp5
  have hfactor : (Sℤ : ZMod (p ^ 3)) =
      (Pℤ : ZMod (p ^ 3)) *
        ∑ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ 3))⁻¹ := by
    rw [hsumZ, Finset.sum_congr rfl hterm, ← Finset.sum_mul, mul_comm, hPZ]
  have : (Sℤ : ZMod (p ^ 3)) = 0 := by
    rw [hfactor, hH, mul_zero]
  exact (CharP.intCast_eq_zero_iff (ZMod (p ^ 3)) (p ^ 3) Sℤ).mp this

lemma last_x_cast_mod_p {p : ℕ} (hp : p.Prime)
    {ij : ℕ × ℕ} (hij : ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 p) :
    ((p * ij.2 - ij.1 : ℕ) : ZMod p) = - (ij.1 : ZMod p) := by
  have hij' := mem_product.mp hij
  have ⟨hs1, hs2⟩ := mem_Icc.mp hij'.1
  have ⟨hj1, _⟩ := mem_Icc.mp hij'.2
  have hs_lt : ij.1 < p := by omega
  have hle : ij.1 ≤ p * ij.2 :=
    le_trans (Nat.le_of_lt hs_lt) (Nat.le_mul_of_pos_right p hj1)
  have hp0 : (p : ZMod p) = 0 := CharP.cast_eq_zero (ZMod p) p
  rw [Nat.cast_sub hle, Nat.cast_mul, hp0, zero_mul, zero_sub]

lemma last_x_isUnit_mod_p {p : ℕ} (hp : p.Prime)
    {ij : ℕ × ℕ} (hij : ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 p) :
    IsUnit ((p * ij.2 - ij.1 : ℕ) : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [last_x_cast_mod_p hp hij]
  have hij' := mem_product.mp hij
  exact (isUnit_iff_ne_zero.mpr (Icc_cast_ne_zero hp hij'.1)).neg

lemma last_inner_prod_eq {p : ℕ} (hp : p.Prime)
    {i j : ℕ × ℕ} {s : Finset (ℕ × ℕ)}
    (hs : s = Icc 1 (p - 1) ×ˢ Icc 1 p)
    (hi : i ∈ s) (hj : j ∈ s.erase i) :
    ∏ k ∈ (s.erase i).erase j, ((p * k.2 - k.1 : ℕ) : ZMod p) =
      (∏ k ∈ s, ((p * k.2 - k.1 : ℕ) : ZMod p)) *
        ((p * i.2 - i.1 : ℕ) : ZMod p)⁻¹ *
        ((p * j.2 - j.1 : ℕ) : ZMod p)⁻¹ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hj' : j ∈ s := (mem_erase.mp hj).2
  have hi' : i ∈ Icc 1 (p - 1) ×ˢ Icc 1 p := by rwa [hs] at hi
  have hj'' : j ∈ Icc 1 (p - 1) ×ˢ Icc 1 p := by rwa [hs] at hj'
  have hui := last_x_isUnit_mod_p hp hi'
  have huj := last_x_isUnit_mod_p hp hj''
  set f : ℕ × ℕ → ZMod p := fun k => ((p * k.2 - k.1 : ℕ) : ZMod p)
  have hprod : f i * ∏ k ∈ s.erase i, f k = ∏ k ∈ s, f k :=
    Finset.mul_prod_erase s f hi
  have hprod2 : f j * ∏ k ∈ (s.erase i).erase j, f k = ∏ k ∈ s.erase i, f k :=
    Finset.mul_prod_erase (s.erase i) f hj
  have hmul : f i * f j * ∏ k ∈ (s.erase i).erase j, f k = ∏ k ∈ s, f k := by
    rw [mul_assoc, hprod2, hprod]
  have hcancel : (f i)⁻¹ * (f j)⁻¹ * (f i * f j * ∏ k ∈ (s.erase i).erase j, f k) =
      ∏ k ∈ (s.erase i).erase j, f k := by
    calc
      (f i)⁻¹ * (f j)⁻¹ * (f i * f j * ∏ k ∈ (s.erase i).erase j, f k) =
          ((f i)⁻¹ * f i) * ((f j)⁻¹ * f j) *
            ∏ k ∈ (s.erase i).erase j, f k := by ring
      _ = 1 * 1 * ∏ k ∈ (s.erase i).erase j, f k := by
        rw [unit_inv_mul hui, unit_inv_mul huj]
      _ = ∏ k ∈ (s.erase i).erase j, f k := by ring
  have hgoal : ∏ k ∈ (s.erase i).erase j, f k =
      (∏ k ∈ s, f k) * (f i)⁻¹ * (f j)⁻¹ := by
    calc
      ∏ k ∈ (s.erase i).erase j, f k =
          (f i)⁻¹ * (f j)⁻¹ * (f i * f j * ∏ k ∈ (s.erase i).erase j, f k) :=
        hcancel.symm
      _ = (f i)⁻¹ * (f j)⁻¹ * ∏ k ∈ s, f k := by rw [hmul]
      _ = (∏ k ∈ s, f k) * (f i)⁻¹ * (f j)⁻¹ := by ring
  simpa [f] using hgoal

lemma last_sum_inv_mod_p {p : ℕ} (hp : p.Prime) :
    ∑ i ∈ Icc 1 (p - 1) ×ˢ Icc 1 p,
      ((p * i.2 - i.1 : ℕ) : ZMod p)⁻¹ = 0 := by
  set s : Finset (ℕ × ℕ) := Icc 1 (p - 1) ×ˢ Icc 1 p
  have hterm : ∀ i ∈ s, ((p * i.2 - i.1 : ℕ) : ZMod p)⁻¹ =
      (-(i.1 : ZMod p))⁻¹ := by
    intro i hi
    rw [last_x_cast_mod_p hp hi]
  rw [Finset.sum_congr rfl hterm, Finset.sum_product]
  have : ∑ t ∈ Icc 1 (p - 1), ∑ _j ∈ Icc 1 p, ((-(t : ZMod p))⁻¹) =
      ∑ t ∈ Icc 1 (p - 1), (p : ZMod p) * ((-(t : ZMod p))⁻¹) := by
    refine Finset.sum_congr rfl ?_
    intro t ht
    rw [Finset.sum_const, nsmul_eq_mul, card_Icc]
    simp
  rw [this]
  have hp0 : (p : ZMod p) = 0 := CharP.cast_eq_zero (ZMod p) p
  simp [hp0]

lemma last_sum_invsq_mod_p {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∑ i ∈ Icc 1 (p - 1) ×ˢ Icc 1 p,
      (((p * i.2 - i.1 : ℕ) : ZMod p)⁻¹) ^ 2 = 0 := by
  set s : Finset (ℕ × ℕ) := Icc 1 (p - 1) ×ˢ Icc 1 p
  have hsB : Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (2 - 1)) = s := by simp [s]
  have hr : 1 ≤ 2 := by decide
  have himg : s.image (fun ij => p * ij.2 - ij.1) = pfree p 2 := by
    simpa [hsB] using pfree_eq_rectangle_image (p := p) (r := 2) hp hr
  have hinj : Set.InjOn (fun ij : ℕ × ℕ => p * ij.2 - ij.1) s := by
    intro ij hij kl hkl heq
    exact rectangle_map_inj hp hij hkl heq
  have :
      ∑ t ∈ s.image (fun ij => p * ij.2 - ij.1), ((t : ZMod p)⁻¹) ^ 2 =
        ∑ i ∈ s, (((p * i.2 - i.1 : ℕ) : ZMod p)⁻¹) ^ 2 :=
    Finset.sum_image hinj
  rw [← this, himg]
  exact sum_pfree_inv_sq_mod_p hp hp5

lemma esym2_last_mod_p {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ((esym2 (Icc 1 (p - 1) ×ˢ Icc 1 p)
        (fun ij => ((p * ij.2 - ij.1 : ℕ) : ℤ))) : ZMod p) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set s : Finset (ℕ × ℕ) := Icc 1 (p - 1) ×ˢ Icc 1 p
  set x : ℕ × ℕ → ℤ := fun ij => ((p * ij.2 - ij.1 : ℕ) : ℤ)
  have hcast : (esym2 s x : ZMod p) =
      ∑ i ∈ s, ∑ j ∈ s.erase i,
        ∏ k ∈ (s.erase i).erase j, ((p * k.2 - k.1 : ℕ) : ZMod p) := by
    simp only [esym2, x, Int.cast_sum, Int.cast_prod, Int.cast_natCast]
  rw [hcast]
  have hterm : ∀ i ∈ s, ∀ j ∈ s.erase i,
      ∏ k ∈ (s.erase i).erase j, ((p * k.2 - k.1 : ℕ) : ZMod p) =
        (∏ k ∈ s, ((p * k.2 - k.1 : ℕ) : ZMod p)) *
          ((p * i.2 - i.1 : ℕ) : ZMod p)⁻¹ *
          ((p * j.2 - j.1 : ℕ) : ZMod p)⁻¹ :=
    fun i hi j hj => last_inner_prod_eq (p := p) hp (s := s) rfl hi hj
  have hrew :
      ∑ i ∈ s, ∑ j ∈ s.erase i,
          ∏ k ∈ (s.erase i).erase j, ((p * k.2 - k.1 : ℕ) : ZMod p) =
        (∏ k ∈ s, ((p * k.2 - k.1 : ℕ) : ZMod p)) *
          ∑ i ∈ s, ∑ j ∈ s.erase i,
            ((p * i.2 - i.1 : ℕ) : ZMod p)⁻¹ *
              ((p * j.2 - j.1 : ℕ) : ZMod p)⁻¹ := by
    rw [Finset.sum_congr rfl (fun i hi =>
      Finset.sum_congr rfl (fun j hj => hterm i hi j hj))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    ring
  rw [hrew]
  have hdouble :
      ∑ i ∈ s, ∑ j ∈ s.erase i,
          ((p * i.2 - i.1 : ℕ) : ZMod p)⁻¹ *
            ((p * j.2 - j.1 : ℕ) : ZMod p)⁻¹ =
        (∑ i ∈ s, ((p * i.2 - i.1 : ℕ) : ZMod p)⁻¹) ^ 2 -
          ∑ i ∈ s, (((p * i.2 - i.1 : ℕ) : ZMod p)⁻¹) ^ 2 := by
    set inv : ℕ × ℕ → ZMod p := fun i => ((p * i.2 - i.1 : ℕ) : ZMod p)⁻¹
    have hprod : (∑ i ∈ s, inv i) * (∑ j ∈ s, inv j) =
        ∑ i ∈ s, ∑ j ∈ s, inv i * inv j :=
      Finset.sum_mul_sum s s inv inv
    have hsq : (∑ i ∈ s, inv i) * (∑ j ∈ s, inv j) = (∑ i ∈ s, inv i) ^ 2 := by
      rw [pow_two]
    have hinter : ∀ i ∈ s,
        ∑ j ∈ s, inv i * inv j =
          ∑ j ∈ s.erase i, inv i * inv j + inv i * inv i :=
      fun i hi => (Finset.sum_erase_add s (fun j => inv i * inv j) hi).symm
    have hsum := Finset.sum_congr (rfl : s = s) hinter
    have hsplit :
        ∑ i ∈ s, ∑ j ∈ s, inv i * inv j =
          ∑ i ∈ s, ∑ j ∈ s.erase i, inv i * inv j +
            ∑ i ∈ s, inv i * inv i := by
      rw [hsum, Finset.sum_add_distrib]
    have hdiag : ∑ i ∈ s, inv i * inv i = ∑ i ∈ s, (inv i) ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro i hi; rw [pow_two]
    rw [← hsq, hprod, hsplit, hdiag]
    abel
  rw [hdouble, last_sum_inv_mod_p hp, last_sum_invsq_mod_p hp hp5]
  ring

lemma esym2_last_dvd {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p : ℤ) ∣ esym2 (Icc 1 (p - 1) ×ˢ Icc 1 p)
      (fun ij => ((p * ij.2 - ij.1 : ℕ) : ℤ)) :=
  (CharP.intCast_eq_zero_iff (ZMod p) p _).mp (esym2_last_mod_p hp hp5)

/-- Last-term `Q ≡ P [ZMOD p^5]` for `r = 2`, `p ≥ 5`. -/
lemma prod_add_pow_last_r2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 p,
        (((p * ij.2 - ij.1 : ℕ) : ℤ) + (p : ℤ) ^ 2)) ≡
      (∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 p, ((p * ij.2 - ij.1 : ℕ) : ℤ))
      [ZMOD (p : ℤ) ^ 5] := by
  set s : Finset (ℕ × ℕ) := Icc 1 (p - 1) ×ˢ Icc 1 p
  set x : ℕ × ℕ → ℤ := fun ij => ((p * ij.2 - ij.1 : ℕ) : ℤ)
  set N : ℤ := (p : ℤ) ^ 2
  have hexp := prod_add_const_mod_cube (s := s) (x := x) (N := N)
  have hcof := sum_cofactor_last_dvd_cube (p := p) hp hp5
  have hσ2 := esym2_last_dvd hp hp5
  -- 2(Q - P - N σ₁) ≡ N² σ₂ [ZMOD N³], N³ = p^6
  have hN3 : N ^ 3 = (p : ℤ) ^ 6 := by
    simp [N]; ring
  have hN2 : N ^ 2 = (p : ℤ) ^ 4 := by
    simp [N]; ring
  obtain ⟨c1, hc1⟩ := hcof
  obtain ⟨c2, hc2⟩ := hσ2
  -- 2(Q - P) = 2 N σ₁ + 2(Q - P - N σ₁)
  -- 2(Q - P - N σ₁) = N² σ₂ + N³ K   for some K
  have hmid := (Int.modEq_iff_dvd).mp hexp
  -- hmid : N³ ∣ N² σ₂ - 2(Q - P - N σ₁)
  obtain ⟨K, hK⟩ := hmid
  have hdecomp :
      2 * (∏ i ∈ s, (x i + N) - ∏ i ∈ s, x i) =
        2 * N * esym1 s x + N ^ 2 * esym2 s x - N ^ 3 * K := by
    -- from hK : N² σ₂ - 2(Q-P-Nσ₁) = N³ K
    have : 2 * (∏ i ∈ s, (x i + N) - ∏ i ∈ s, x i - N * esym1 s x) =
        N ^ 2 * esym2 s x - N ^ 3 * K := by
      linear_combination -hK
    linear_combination this
  have hesym1 : esym1 s x =
      ∑ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 p,
        ∏ kl ∈ (Icc 1 (p - 1) ×ˢ Icc 1 p).erase ij,
          ((p * kl.2 - kl.1 : ℕ) : ℤ) := by
    simp [esym1, s, x]
  have hesym2 : esym2 s x =
      esym2 (Icc 1 (p - 1) ×ˢ Icc 1 p)
        (fun ij => ((p * ij.2 - ij.1 : ℕ) : ℤ)) := by
    simp [s, x]
  rw [hesym1, hc1, hesym2, hc2, hN2, hN3] at hdecomp
  have hN : N = (p : ℤ) ^ 2 := rfl
  have hdiff :
      2 * (∏ i ∈ s, (x i + N) - ∏ i ∈ s, x i) =
        (p : ℤ) ^ 5 * (2 * c1 + c2 - (p : ℤ) * K) := by
    rw [hdecomp, hN]
    ring
  have h2div : (p : ℤ) ^ 5 ∣ 2 * (∏ i ∈ s, (x i + N) - ∏ i ∈ s, x i) :=
    ⟨2 * c1 + c2 - (p : ℤ) * K, hdiff⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hdiv : (p : ℤ) ^ 5 ∣ (∏ i ∈ s, (x i + N) - ∏ i ∈ s, x i) := by
    set D := ∏ i ∈ s, (x i + N) - ∏ i ∈ s, x i
    by_cases hD0 : D = 0
    · simp [hD0]
    · have hne2 : (2 : ℤ) ≠ 0 := by decide
      have hge : 5 ≤ padicValInt p (2 * D) :=
        (padicValInt_dvd_iff (p := p) 5 (2 * D)).mp h2div |>.resolve_left
          (mul_ne_zero hne2 hD0)
      have h2val : padicValInt p (2 : ℤ) = 0 := by
        rw [padicValInt.eq_zero_of_not_dvd]
        intro hd
        have : (p : ℤ) ∣ 2 := hd
        have : p ∣ 2 := Int.ofNat_dvd.mp (by simpa using this)
        have hcases := (Nat.dvd_prime Nat.prime_two).mp this
        rcases hcases with h1 | h2'
        · exact hp.ne_one h1
        · omega
      have : 5 ≤ padicValInt p D := by
        have hmul := padicValInt.mul (p := p) hne2 hD0
        omega
      exact (padicValInt_dvd_iff (p := p) 5 D).mpr (Or.inr this)
  refine (Int.modEq_iff_dvd).mpr ?_
  simpa [neg_sub] using (dvd_neg.mpr hdiv)

lemma pow_dvd_delta_last_r2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p : ℤ) ^ 5 ∣
      (rising (p ^ 2) (p * p) : ℤ) - risingY p 2 (p * p) := by
  have hr1 : 1 ≤ 2 := by decide
  have hB : p ≤ p ^ (2 - 1) := by simp
  have hid := rising_sub_mul_pProd (p := p) (r := 2) (B := p) hp hr1 hB
  have hQmod := prod_add_pow_last_r2 hp hp5
  have hcastQ :
      ((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 p,
          (p * ij.2 - ij.1 + p ^ 2) : ℕ) : ℤ) =
        ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 p,
          (((p * ij.2 - ij.1 : ℕ) : ℤ) + (p : ℤ) ^ 2) := by
    simp [Nat.cast_prod, Nat.cast_add, Nat.cast_pow]
  have hcastP : (pProd p p : ℤ) =
      ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 p, ((p * ij.2 - ij.1 : ℕ) : ℤ) := by
    simp [pProd_eq_prod_product, Nat.cast_prod]
  have hQP : (p : ℤ) ^ 5 ∣
      ((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 p,
          (p * ij.2 - ij.1 + p ^ 2) : ℕ) : ℤ) - pProd p p := by
    have h := (Int.modEq_iff_dvd).mp hQmod
    rw [hcastQ, hcastP]
    exact dvd_neg.mp (by simpa [neg_sub] using h)
  have hyQP : (p : ℤ) ^ 5 ∣
      (risingY p 2 (p * p) : ℤ) *
        (((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 p,
            (p * ij.2 - ij.1 + p ^ 2) : ℕ) : ℤ) - pProd p p) :=
    dvd_mul_of_dvd_right hQP _
  have hδP : (p : ℤ) ^ 5 ∣
      ((rising (p ^ 2) (p * p) : ℤ) - risingY p 2 (p * p)) * (pProd p p : ℤ) := by
    rwa [hid]
  haveI : Fact p.Prime := ⟨hp⟩
  have hPne : (pProd p p : ℤ) ≠ 0 := by
    exact_mod_cast (ne_zero_of_lt (pProd_pos (p := p) hp.pos))
  by_cases hδ0 : ((rising (p ^ 2) (p * p) : ℤ) - risingY p 2 (p * p)) = 0
  · simp [hδ0]
  · have hge : 5 ≤
        padicValInt p
          (((rising (p ^ 2) (p * p) : ℤ) - risingY p 2 (p * p)) * pProd p p) :=
      (padicValInt_dvd_iff (p := p) 5 _).mp hδP |>.resolve_left
        (mul_ne_zero hδ0 hPne)
    have hP0 : padicValInt p (pProd p p : ℤ) = 0 := by
      rw [padicValInt.of_nat]
      exact padicValNat.eq_zero_of_not_dvd (p_not_dvd_pProd hp)
    have : 5 ≤ padicValInt p
        ((rising (p ^ 2) (p * p) : ℤ) - risingY p 2 (p * p)) := by
      have hmulv := padicValInt.mul (p := p) hδ0 hPne
      omega
    exact (padicValInt_dvd_iff (p := p) 5 _).mpr (Or.inr this)

lemma increment_quad_dvd_last_r2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p : ℤ) ^ (3 * 2 + 3) ∣
      3 * (2 * (risingY p 2 (p * p) : ℤ) + 1) *
        ((rising (p ^ 2) (p * p) : ℤ) - risingY p 2 (p * p)) ^ 2 := by
  have hδ := pow_dvd_delta_last_r2 hp hp5
  obtain ⟨t, ht⟩ := hδ
  refine ⟨3 * (2 * (risingY p 2 (p * p) : ℤ) + 1) * ((p : ℤ) * t ^ 2), ?_⟩
  have hδ2 :
      ((rising (p ^ 2) (p * p) : ℤ) - risingY p 2 (p * p)) ^ 2 =
      ((p : ℤ) ^ 5) ^ 2 * t ^ 2 := by
    rw [ht]; ring
  have hpow : ((p : ℤ) ^ 5) ^ 2 = (p : ℤ) ^ 10 := by
    rw [← pow_mul]
  rw [hδ2, hpow]
  ring

/-- In `ZMod (p^{2n})`, `p^n * x = 0` whenever `x` reduces to `0` mod `p^n`. -/
lemma pn_mul_of_castHom_zero {p n : ℕ} [Fact p.Prime] (hn : 0 < n)
    {x : ZMod (p ^ (2 * n))}
    (h : ZMod.castHom (pow_dvd_pow p (by omega : n ≤ 2 * n)) (ZMod (p ^ n)) x = 0) :
    (p : ZMod (p ^ (2 * n))) ^ n * x = 0 := by
  have hval : (x.val : ZMod (p ^ n)) = 0 := by
    simpa [ZMod.castHom_apply] using h
  have hdvd : p ^ n ∣ x.val := (ZMod.natCast_eq_zero_iff x.val (p ^ n)).mp hval
  obtain ⟨t, ht⟩ := hdvd
  have hx : x = ((p ^ n * t : ℕ) : ZMod (p ^ (2 * n))) := by
    rw [(ZMod.natCast_zmod_val x).symm, ht]
  rw [hx]
  have hmul : (p : ZMod (p ^ (2 * n))) ^ n * ((p ^ n * t : ℕ) : ZMod (p ^ (2 * n))) =
      ((p ^ (2 * n) * t : ℕ) : ZMod (p ^ (2 * n))) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
    have hpow : (p : ZMod (p ^ (2 * n))) ^ n * (p : ZMod (p ^ (2 * n))) ^ n =
        (p : ZMod (p ^ (2 * n))) ^ (n + n) := (pow_add _ n n).symm
    have hn2 : n + n = 2 * n := by ring
    rw [← mul_assoc, hpow, hn2]
  rw [hmul, Nat.cast_mul, ZMod.natCast_self, zero_mul]

lemma pair_inv_sum_pow {p n k : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hk : k ∈ pfree p n) :
    (k : ZMod (p ^ (2 * n)))⁻¹ + ((p ^ n - k : ℕ) : ZMod (p ^ (2 * n)))⁻¹ =
      (p : ZMod (p ^ (2 * n))) ^ n *
        ((k : ZMod (p ^ (2 * n))) * ((p ^ n - k : ℕ) : ZMod (p ^ (2 * n))))⁻¹ := by
  have hu := pfree_isUnit_pow (p := p) (r := n) (k := k) (n := 2 * n) hp
    (by omega) hk
  have hk' : p ^ n - k ∈ pfree p n := pfree_sub hp hn hk
  have hu' := pfree_isUnit_pow (p := p) (r := n) (k := p ^ n - k) (n := 2 * n)
    hp (by omega) hk'
  have hadd : (k : ZMod (p ^ (2 * n))) + ((p ^ n - k : ℕ) : ZMod (p ^ (2 * n))) =
      (p : ZMod (p ^ (2 * n))) ^ n := by
    have hle : k ≤ p ^ n := le_of_lt (mem_pfree.mp hk).1
    rw [Nat.cast_sub hle, Nat.cast_pow]
    ring
  rw [inv_add_inv_of_unit hu hu', hadd]

lemma pair_inv_eq_neg_pn_invsq {p n k : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hk : k ∈ pfree p n) :
    (k : ZMod (p ^ (2 * n)))⁻¹ + ((p ^ n - k : ℕ) : ZMod (p ^ (2 * n)))⁻¹ =
      -((p : ZMod (p ^ (2 * n))) ^ n * ((k : ZMod (p ^ (2 * n)))⁻¹) ^ 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hu := pfree_isUnit_pow (p := p) (r := n) (n := 2 * n) hp (by omega) hk
  rw [pair_inv_sum_pow hp hn hk]
  have hgoal :
      (p : ZMod (p ^ (2 * n))) ^ n *
        (((k : ZMod (p ^ (2 * n))) * ((p ^ n - k : ℕ) : ZMod (p ^ (2 * n))))⁻¹ +
          ((k : ZMod (p ^ (2 * n)))⁻¹) ^ 2) = 0 := by
    apply pn_mul_of_castHom_zero hn
    set π := ZMod.castHom (pow_dvd_pow p (by omega : n ≤ 2 * n)) (ZMod (p ^ n))
    have hu' : IsUnit ((k : ZMod (p ^ (2 * n))) *
        ((p ^ n - k : ℕ) : ZMod (p ^ (2 * n)))) := by
      have hk' : p ^ n - k ∈ pfree p n := pfree_sub hp hn hk
      exact (pfree_isUnit_pow (n := 2 * n) hp (by omega) hk).mul
        (pfree_isUnit_pow (n := 2 * n) hp (by omega) hk')
    have hle : k ≤ p ^ n := le_of_lt (mem_pfree.mp hk).1
    have hcast_p : π ((p : ZMod (p ^ (2 * n))) ^ n) = 0 := by
      have hpmap : π (p : ZMod (p ^ (2 * n))) = (p : ZMod (p ^ n)) := by
        simp [π, ZMod.castHom_apply]
      rw [map_pow, hpmap]
      have : ((p ^ n : ℕ) : ZMod (p ^ n)) = 0 := ZMod.natCast_self (p ^ n)
      rw [← Nat.cast_pow]
      exact this
    have hcast_sub : π ((p ^ n - k : ℕ) : ZMod (p ^ (2 * n))) =
        - π (k : ZMod (p ^ (2 * n))) := by
      have hrew : ((p ^ n - k : ℕ) : ZMod (p ^ (2 * n))) =
          (p : ZMod (p ^ (2 * n))) ^ n - k := by
        rw [Nat.cast_sub hle, Nat.cast_pow]
      rw [hrew, map_sub, hcast_p]
      simp
    have hcast_prod :
        π ((k : ZMod (p ^ (2 * n))) * ((p ^ n - k : ℕ) : ZMod (p ^ (2 * n)))) =
          - (π (k : ZMod (p ^ (2 * n)))) ^ 2 := by
      rw [map_mul, hcast_sub]
      ring
    have hcast_inv :
        π (((k : ZMod (p ^ (2 * n))) * ((p ^ n - k : ℕ) : ZMod (p ^ (2 * n))))⁻¹) =
          (π ((k : ZMod (p ^ (2 * n))) *
            ((p ^ n - k : ℕ) : ZMod (p ^ (2 * n)))))⁻¹ := by
      refine (ZMod.inv_eq_of_mul_eq_one (p ^ n)
          (π ((k : ZMod (p ^ (2 * n))) * ((p ^ n - k : ℕ) : ZMod (p ^ (2 * n)))))
          (π (((k : ZMod (p ^ (2 * n))) *
            ((p ^ n - k : ℕ) : ZMod (p ^ (2 * n))))⁻¹)) ?_).symm
      rw [← map_mul, unit_mul_inv hu', map_one]
    rw [map_add, hcast_inv, hcast_prod, map_pow]
    have hkinv : π ((k : ZMod (p ^ (2 * n)))⁻¹) =
        (π (k : ZMod (p ^ (2 * n))))⁻¹ := by
      refine (ZMod.inv_eq_of_mul_eq_one (p ^ n) (π (k : ZMod (p ^ (2 * n))))
          (π ((k : ZMod (p ^ (2 * n)))⁻¹)) ?_).symm
      rw [← map_mul, unit_mul_inv hu, map_one]
    rw [hkinv]
    set a := π (k : ZMod (p ^ (2 * n)))
    have hk0 : IsUnit a := by
      have : a = (k : ZMod (p ^ n)) := by
        simp [a, π, ZMod.castHom_apply]
      rw [this]
      exact pfree_isUnit_pow (n := n) hp hn hk
    have hneg : (-(a ^ 2))⁻¹ = - (a⁻¹) ^ 2 := by
      refine ZMod.inv_eq_of_mul_eq_one (p ^ n) _ _ ?_
      have hsq : a ^ 2 * (a⁻¹) ^ 2 = 1 := by
        rw [← mul_pow, unit_mul_inv hk0, one_pow]
      rw [neg_mul_neg]
      exact hsq
    rw [hneg]
    ring
  linear_combination hgoal


lemma two_isUnit_pow {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n) :
    IsUnit (2 : ZMod (p ^ n)) := by
  have : IsUnit ((2 : ℕ) : ZMod (p ^ n)) := by
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff hn]
    exact (Nat.prime_two.coprime_iff_not_dvd).2 (fun hd =>
      hp2 ((Nat.dvd_prime hp).mp hd |>.resolve_left (by decide)).symm)
  exact this

lemma isUnit_zmod_inv {n : ℕ} {a : ZMod n} (h : IsUnit a) : IsUnit a⁻¹ := by
  obtain ⟨u, hu⟩ := h
  refine ⟨u⁻¹, ?_⟩
  rw [← hu, ZMod.inv_coe_unit]

lemma unit_inv_inv {n : ℕ} {a : ZMod n} (h : IsUnit a) : (a⁻¹)⁻¹ = a :=
  ZMod.inv_eq_of_mul_eq_one n a⁻¹ a (unit_inv_mul h)

lemma inv_val_mem_pfree {p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    {k : ℕ} (hk : k ∈ pfree p n) :
    ((k : ZMod (p ^ n))⁻¹).val ∈ pfree p n := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  have hu := pfree_isUnit_pow (n := n) hp hn hk
  have hnd : ¬ p ∣ ((k : ZMod (p ^ n))⁻¹).val :=
    (isUnit_iff_not_dvd_val hp hn ((k : ZMod (p ^ n))⁻¹)).mp (isUnit_zmod_inv hu)
  exact mem_pfree.mpr ⟨ZMod.val_lt _, hnd⟩

lemma sum_pfree_inv_sq_mod_pn {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : 0 < n) :
    (∑ k ∈ pfree p n, ((k : ZMod (p ^ n))⁻¹) ^ 2) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hdiv : ¬ (p - 1) ∣ (2 : ℕ) := by
    intro h
    have : p - 1 ≤ 2 := Nat.le_of_dvd (by decide) h
    omega
  have hperm :
      ∑ k ∈ pfree p n, ((k : ZMod (p ^ n))⁻¹) ^ 2 =
        ∑ k ∈ pfree p n, (k : ZMod (p ^ n)) ^ 2 := by
    refine (Finset.sum_bij (fun k (_ : k ∈ pfree p n) =>
        ((k : ZMod (p ^ n))⁻¹).val) ?_ ?_ ?_ ?_).symm
    · intro k hk; exact inv_val_mem_pfree hp hn hk
    · intro k hk k' hk' h
      have hinv : (k : ZMod (p ^ n))⁻¹ = (k' : ZMod (p ^ n))⁻¹ := by
        have := congrArg (fun t : ℕ => (t : ZMod (p ^ n))) h
        simpa [ZMod.natCast_zmod_val] using this
      have hu := pfree_isUnit_pow (n := n) hp hn hk
      have heq : (k : ZMod (p ^ n)) = (k' : ZMod (p ^ n)) := by
        calc
          (k : ZMod (p ^ n)) = ((k : ZMod (p ^ n))⁻¹)⁻¹ := (unit_inv_inv hu).symm
          _ = ((k' : ZMod (p ^ n))⁻¹)⁻¹ := by rw [hinv]
          _ = (k' : ZMod (p ^ n)) := unit_inv_inv (pfree_isUnit_pow (n := n) hp hn hk')
      exact eq_of_zmod_eq_of_lt heq (mem_pfree.mp hk).1 (mem_pfree.mp hk').1
    · intro t ht
      refine ⟨((t : ZMod (p ^ n))⁻¹).val, inv_val_mem_pfree hp hn ht, ?_⟩
      apply eq_of_zmod_eq_of_lt _ (ZMod.val_lt _) (mem_pfree.mp ht).1
      have hu := pfree_isUnit_pow (n := n) hp hn ht
      simp [ZMod.natCast_zmod_val, unit_inv_inv hu]
    · intro k hk
      have hu := pfree_isUnit_pow (n := n) hp hn hk
      simp [ZMod.natCast_zmod_val, unit_inv_inv hu]
  rw [hperm]
  exact sum_pfree_zmod_pow_eq_zero hp hp2 hn hdiv

lemma sum_pfree_inv_mod_two_pow {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : 0 < n) :
    ∑ k ∈ pfree p n, (k : ZMod (p ^ (2 * n)))⁻¹ = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have h2n : 0 < 2 * n := by omega
  have h2u := two_isUnit_pow (p := p) (n := 2 * n) hp hp2 h2n
  have hperm :
      ∑ k ∈ pfree p n, ((p ^ n - k : ℕ) : ZMod (p ^ (2 * n)))⁻¹ =
        ∑ k ∈ pfree p n, (k : ZMod (p ^ (2 * n)))⁻¹ := by
    refine Finset.sum_bij (fun k _ => p ^ n - k) ?_ ?_ ?_ ?_
    · intro k hk; exact pfree_sub hp hn hk
    · intro k hk k' hk' h
      have := congrArg (fun t => p ^ n - t) h
      simpa [pfree_sub_sub hp hk, pfree_sub_sub hp hk'] using this
    · intro k hk
      refine ⟨p ^ n - k, pfree_sub hp hn hk, pfree_sub_sub hp hk⟩
    · intro k hk; rfl
  have hpairs :
      ∑ k ∈ pfree p n,
          ((k : ZMod (p ^ (2 * n)))⁻¹ +
            ((p ^ n - k : ℕ) : ZMod (p ^ (2 * n)))⁻¹) =
        (2 : ZMod (p ^ (2 * n))) *
          ∑ k ∈ pfree p n, (k : ZMod (p ^ (2 * n)))⁻¹ := by
    rw [sum_add_distrib, hperm]
    exact (two_mul _).symm
  have hterm : ∀ k ∈ pfree p n,
      (k : ZMod (p ^ (2 * n)))⁻¹ + ((p ^ n - k : ℕ) : ZMod (p ^ (2 * n)))⁻¹ =
        -((p : ZMod (p ^ (2 * n))) ^ n *
          ((k : ZMod (p ^ (2 * n)))⁻¹) ^ 2) :=
    fun k hk => pair_inv_eq_neg_pn_invsq hp hn hk
  have hsum :
      ∑ k ∈ pfree p n,
          ((k : ZMod (p ^ (2 * n)))⁻¹ +
            ((p ^ n - k : ℕ) : ZMod (p ^ (2 * n)))⁻¹) =
        -((p : ZMod (p ^ (2 * n))) ^ n *
          ∑ k ∈ pfree p n, ((k : ZMod (p ^ (2 * n)))⁻¹) ^ 2) := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, Finset.mul_sum]
  have hcast :
      ZMod.castHom (pow_dvd_pow p (by omega : n ≤ 2 * n)) (ZMod (p ^ n))
        (∑ k ∈ pfree p n, ((k : ZMod (p ^ (2 * n)))⁻¹) ^ 2) = 0 := by
    rw [map_sum]
    have hcongr : ∀ k ∈ pfree p n,
        ZMod.castHom (pow_dvd_pow p (by omega : n ≤ 2 * n)) (ZMod (p ^ n))
          (((k : ZMod (p ^ (2 * n)))⁻¹) ^ 2) =
        ((k : ZMod (p ^ n))⁻¹) ^ 2 := by
      intro k hk
      rw [map_pow]
      have hu := pfree_isUnit_pow (n := 2 * n) hp h2n hk
      have hinv :
          ZMod.castHom (pow_dvd_pow p (by omega : n ≤ 2 * n)) (ZMod (p ^ n))
            ((k : ZMod (p ^ (2 * n)))⁻¹) =
          (ZMod.castHom (pow_dvd_pow p (by omega : n ≤ 2 * n)) (ZMod (p ^ n))
            (k : ZMod (p ^ (2 * n))))⁻¹ := by
        refine (ZMod.inv_eq_of_mul_eq_one (p ^ n) _ _ ?_).symm
        rw [← map_mul, unit_mul_inv hu, map_one]
      rw [hinv]
      simp [ZMod.castHom_apply]
    rw [Finset.sum_congr rfl hcongr, sum_pfree_inv_sq_mod_pn hp hp5 hn]
  have hmul0 :
      (p : ZMod (p ^ (2 * n))) ^ n *
        ∑ k ∈ pfree p n, ((k : ZMod (p ^ (2 * n)))⁻¹) ^ 2 = 0 :=
    pn_mul_of_castHom_zero hn hcast
  have : (2 : ZMod (p ^ (2 * n))) *
      ∑ k ∈ pfree p n, (k : ZMod (p ^ (2 * n)))⁻¹ = 0 := by
    rw [← hpairs, hsum, hmul0, neg_zero]
  have hcancel :=
    congrArg (fun z => (2 : ZMod (p ^ (2 * n)))⁻¹ * z) this
  simpa [← mul_assoc, unit_inv_mul h2u] using hcancel

/-! ### Last-term pairing in `ZMod (p^{2r})`: `p^{2r} ∣ σ₁` and `p^r ∣ σ₂` -/

lemma sum_cofactor_last_dvd_two_pow {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 1 ≤ r) :
    (p : ℤ) ^ (2 * r) ∣
      ∑ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)),
        ∏ kl ∈ (Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1))).erase ij,
          ((p * kl.2 - kl.1 : ℕ) : ℤ) := by
  set s : Finset (ℕ × ℕ) := Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1))
  set Pℤ : ℤ := ∏ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ℤ)
  set Sℤ : ℤ :=
    ∑ ij ∈ s, ∏ kl ∈ s.erase ij, ((p * kl.2 - kl.1 : ℕ) : ℤ)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ (2 * r)) := ⟨pow_ne_zero (2 * r) hp.ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  have h2r : 0 < 2 * r := by omega
  have hsumZ : (Sℤ : ZMod (p ^ (2 * r))) =
      ∑ ij ∈ s, ∏ kl ∈ s.erase ij,
        ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ (2 * r))) := by
    simp only [Sℤ, Int.cast_sum, Int.cast_prod, Int.cast_natCast]
  have hPZ : (Pℤ : ZMod (p ^ (2 * r))) =
      ∏ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ (2 * r))) := by
    simp only [Pℤ, Int.cast_prod, Int.cast_natCast]
  have hunit : ∀ ij ∈ s,
      IsUnit ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ (2 * r))) := by
    intro ij hij
    have hij' := mem_product.mp hij
    have mem := rectangle_mem_pfree hp hr hij'.1 hij'.2
    exact pfree_isUnit_pow (n := 2 * r) hp h2r mem
  have hterm : ∀ ij ∈ s,
      ∏ kl ∈ s.erase ij, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ (2 * r))) =
        ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ (2 * r)))⁻¹ *
          ∏ kl ∈ s, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ (2 * r))) := by
    intro ij hij
    have hu := hunit ij hij
    have hmul := Finset.mul_prod_erase s
      (fun kl => ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ (2 * r)))) hij
    calc
      ∏ kl ∈ s.erase ij, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ (2 * r))) =
          ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ (2 * r)))⁻¹ *
            (((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ (2 * r))) *
              ∏ kl ∈ s.erase ij,
                ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ (2 * r)))) := by
        rw [← mul_assoc, unit_inv_mul hu, one_mul]
      _ = ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ (2 * r)))⁻¹ *
            ∏ kl ∈ s, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ (2 * r))) := by
        rw [hmul]
  have hH : ∑ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ (2 * r)))⁻¹ = 0 := by
    have himg := pfree_eq_rectangle_image (p := p) (r := r) hp hr
    have hinj : Set.InjOn (fun ij : ℕ × ℕ => p * ij.2 - ij.1) s := by
      intro ij hij kl hkl heq
      exact rectangle_map_inj hp hij hkl heq
    have :
        ∑ t ∈ s.image (fun ij => p * ij.2 - ij.1),
            (t : ZMod (p ^ (2 * r)))⁻¹ =
          ∑ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ (2 * r)))⁻¹ :=
      Finset.sum_image hinj
    rw [← this, himg]
    exact sum_pfree_inv_mod_two_pow hp hp5 (by omega)
  have hfactor : (Sℤ : ZMod (p ^ (2 * r))) =
      (Pℤ : ZMod (p ^ (2 * r))) *
        ∑ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ (2 * r)))⁻¹ := by
    rw [hsumZ, Finset.sum_congr rfl hterm]
    have hsmul :
        ∑ ij ∈ s,
            ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ (2 * r)))⁻¹ *
              ∏ kl ∈ s, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ (2 * r))) =
          (∑ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ (2 * r)))⁻¹) *
            ∏ kl ∈ s, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ (2 * r))) :=
      (Finset.sum_mul _ _ _).symm
    rw [hsmul, ← hPZ]
    ac_rfl
  have : (Sℤ : ZMod (p ^ (2 * r))) = 0 := by
    rw [hfactor, hH, mul_zero]
  exact (CharP.intCast_eq_zero_iff (ZMod (p ^ (2 * r))) (p ^ (2 * r)) Sℤ).mp this

lemma rectangle_inner_prod {p r n : ℕ} (hp : p.Prime) (hr : 1 ≤ r) (hn : 0 < n)
    {i j : ℕ × ℕ} {s : Finset (ℕ × ℕ)}
    (hs : s = Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)))
    (hi : i ∈ s) (hj : j ∈ s.erase i) :
    ∏ k ∈ (s.erase i).erase j, ((p * k.2 - k.1 : ℕ) : ZMod (p ^ n)) =
      (∏ k ∈ s, ((p * k.2 - k.1 : ℕ) : ZMod (p ^ n))) *
        ((p * i.2 - i.1 : ℕ) : ZMod (p ^ n))⁻¹ *
        ((p * j.2 - j.1 : ℕ) : ZMod (p ^ n))⁻¹ := by
  have hj' : j ∈ s := (mem_erase.mp hj).2
  have hi' : i ∈ Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)) := by rwa [hs] at hi
  have hj'' : j ∈ Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)) := by rwa [hs] at hj'
  have memi := rectangle_mem_pfree hp hr (mem_product.mp hi').1 (mem_product.mp hi').2
  have memj := rectangle_mem_pfree hp hr (mem_product.mp hj'').1 (mem_product.mp hj'').2
  have hui := pfree_isUnit_pow (n := n) hp hn memi
  have huj := pfree_isUnit_pow (n := n) hp hn memj
  set f : ℕ × ℕ → ZMod (p ^ n) := fun k => ((p * k.2 - k.1 : ℕ) : ZMod (p ^ n))
  have hprod : f i * ∏ k ∈ s.erase i, f k = ∏ k ∈ s, f k :=
    Finset.mul_prod_erase s f hi
  have hprod2 : f j * ∏ k ∈ (s.erase i).erase j, f k = ∏ k ∈ s.erase i, f k :=
    Finset.mul_prod_erase (s.erase i) f hj
  have hmul : f i * f j * ∏ k ∈ (s.erase i).erase j, f k = ∏ k ∈ s, f k := by
    rw [mul_assoc, hprod2, hprod]
  have hcancel : (f i)⁻¹ * (f j)⁻¹ * (f i * f j * ∏ k ∈ (s.erase i).erase j, f k) =
      ∏ k ∈ (s.erase i).erase j, f k := by
    calc
      (f i)⁻¹ * (f j)⁻¹ * (f i * f j * ∏ k ∈ (s.erase i).erase j, f k) =
          ((f i)⁻¹ * f i) * ((f j)⁻¹ * f j) *
            ∏ k ∈ (s.erase i).erase j, f k := by ring
      _ = 1 * 1 * ∏ k ∈ (s.erase i).erase j, f k := by
        rw [unit_inv_mul hui, unit_inv_mul huj]
      _ = ∏ k ∈ (s.erase i).erase j, f k := by ring
  have hgoal : ∏ k ∈ (s.erase i).erase j, f k =
      (∏ k ∈ s, f k) * (f i)⁻¹ * (f j)⁻¹ := by
    calc
      ∏ k ∈ (s.erase i).erase j, f k =
          (f i)⁻¹ * (f j)⁻¹ * (f i * f j * ∏ k ∈ (s.erase i).erase j, f k) :=
        hcancel.symm
      _ = (f i)⁻¹ * (f j)⁻¹ * ∏ k ∈ s, f k := by rw [hmul]
      _ = (∏ k ∈ s, f k) * (f i)⁻¹ * (f j)⁻¹ := by ring
  simpa [f] using hgoal

lemma last_sum_inv_mod_pow {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) :
    ∑ i ∈ Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)),
      ((p * i.2 - i.1 : ℕ) : ZMod (p ^ r))⁻¹ = 0 := by
  set s : Finset (ℕ × ℕ) := Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1))
  have himg := pfree_eq_rectangle_image (p := p) (r := r) hp hr
  have hinj : Set.InjOn (fun ij : ℕ × ℕ => p * ij.2 - ij.1) s := by
    intro ij hij kl hkl heq
    exact rectangle_map_inj hp hij hkl heq
  have :
      ∑ t ∈ s.image (fun ij => p * ij.2 - ij.1), (t : ZMod (p ^ r))⁻¹ =
        ∑ i ∈ s, ((p * i.2 - i.1 : ℕ) : ZMod (p ^ r))⁻¹ :=
    Finset.sum_image hinj
  rw [← this, himg]
  exact sum_pfree_inv_eq_zero hp (by omega) (by omega)

lemma last_sum_invsq_mod_pow {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) :
    ∑ i ∈ Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)),
      (((p * i.2 - i.1 : ℕ) : ZMod (p ^ r))⁻¹) ^ 2 = 0 := by
  set s : Finset (ℕ × ℕ) := Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1))
  have himg := pfree_eq_rectangle_image (p := p) (r := r) hp hr
  have hinj : Set.InjOn (fun ij : ℕ × ℕ => p * ij.2 - ij.1) s := by
    intro ij hij kl hkl heq
    exact rectangle_map_inj hp hij hkl heq
  have :
      ∑ t ∈ s.image (fun ij => p * ij.2 - ij.1), ((t : ZMod (p ^ r))⁻¹) ^ 2 =
        ∑ i ∈ s, (((p * i.2 - i.1 : ℕ) : ZMod (p ^ r))⁻¹) ^ 2 :=
    Finset.sum_image hinj
  rw [← this, himg]
  exact sum_pfree_inv_sq_mod_pn hp hp5 (by omega)

lemma esym2_last_mod_pow {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) :
    ((esym2 (Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)))
        (fun ij => ((p * ij.2 - ij.1 : ℕ) : ℤ))) : ZMod (p ^ r)) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set s : Finset (ℕ × ℕ) := Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1))
  set x : ℕ × ℕ → ℤ := fun ij => ((p * ij.2 - ij.1 : ℕ) : ℤ)
  have hcast : (esym2 s x : ZMod (p ^ r)) =
      ∑ i ∈ s, ∑ j ∈ s.erase i,
        ∏ k ∈ (s.erase i).erase j, ((p * k.2 - k.1 : ℕ) : ZMod (p ^ r)) := by
    simp only [esym2, x, Int.cast_sum, Int.cast_prod, Int.cast_natCast]
  rw [hcast]
  have hterm : ∀ i ∈ s, ∀ j ∈ s.erase i,
      ∏ k ∈ (s.erase i).erase j, ((p * k.2 - k.1 : ℕ) : ZMod (p ^ r)) =
        (∏ k ∈ s, ((p * k.2 - k.1 : ℕ) : ZMod (p ^ r))) *
          ((p * i.2 - i.1 : ℕ) : ZMod (p ^ r))⁻¹ *
          ((p * j.2 - j.1 : ℕ) : ZMod (p ^ r))⁻¹ :=
    fun i hi j hj =>
      rectangle_inner_prod (p := p) (r := r) (n := r) hp hr (by omega) rfl hi hj
  have hrew :
      ∑ i ∈ s, ∑ j ∈ s.erase i,
          ∏ k ∈ (s.erase i).erase j, ((p * k.2 - k.1 : ℕ) : ZMod (p ^ r)) =
        (∏ k ∈ s, ((p * k.2 - k.1 : ℕ) : ZMod (p ^ r))) *
          ∑ i ∈ s, ∑ j ∈ s.erase i,
            ((p * i.2 - i.1 : ℕ) : ZMod (p ^ r))⁻¹ *
              ((p * j.2 - j.1 : ℕ) : ZMod (p ^ r))⁻¹ := by
    rw [Finset.sum_congr rfl (fun i hi =>
      Finset.sum_congr rfl (fun j hj => hterm i hi j hj))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    ring
  rw [hrew]
  have hdouble :
      ∑ i ∈ s, ∑ j ∈ s.erase i,
          ((p * i.2 - i.1 : ℕ) : ZMod (p ^ r))⁻¹ *
            ((p * j.2 - j.1 : ℕ) : ZMod (p ^ r))⁻¹ =
        (∑ i ∈ s, ((p * i.2 - i.1 : ℕ) : ZMod (p ^ r))⁻¹) ^ 2 -
          ∑ i ∈ s, (((p * i.2 - i.1 : ℕ) : ZMod (p ^ r))⁻¹) ^ 2 := by
    set inv : ℕ × ℕ → ZMod (p ^ r) :=
      fun i => ((p * i.2 - i.1 : ℕ) : ZMod (p ^ r))⁻¹
    have hprod : (∑ i ∈ s, inv i) * (∑ j ∈ s, inv j) =
        ∑ i ∈ s, ∑ j ∈ s, inv i * inv j :=
      Finset.sum_mul_sum s s inv inv
    have hsq : (∑ i ∈ s, inv i) * (∑ j ∈ s, inv j) = (∑ i ∈ s, inv i) ^ 2 := by
      rw [pow_two]
    have hinter : ∀ i ∈ s,
        ∑ j ∈ s, inv i * inv j =
          ∑ j ∈ s.erase i, inv i * inv j + inv i * inv i :=
      fun i hi => (Finset.sum_erase_add s (fun j => inv i * inv j) hi).symm
    have hsum := Finset.sum_congr (rfl : s = s) hinter
    have hsplit :
        ∑ i ∈ s, ∑ j ∈ s, inv i * inv j =
          ∑ i ∈ s, ∑ j ∈ s.erase i, inv i * inv j +
            ∑ i ∈ s, inv i * inv i := by
      rw [hsum, Finset.sum_add_distrib]
    have hdiag : ∑ i ∈ s, inv i * inv i = ∑ i ∈ s, (inv i) ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro i hi; rw [pow_two]
    rw [← hsq, hprod, hsplit, hdiag]
    abel
  rw [hdouble, last_sum_inv_mod_pow hp hp5 hr, last_sum_invsq_mod_pow hp hp5 hr]
  ring

lemma esym2_last_dvd_pow {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) :
    (p : ℤ) ^ r ∣ esym2 (Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)))
      (fun ij => ((p * ij.2 - ij.1 : ℕ) : ℤ)) :=
  (CharP.intCast_eq_zero_iff (ZMod (p ^ r)) (p ^ r) _).mp
    (esym2_last_mod_pow hp hp5 hr)

/-- Last-term `Q ≡ P [ZMOD p^{3r}]` for `p ≥ 5`. -/
lemma prod_add_pow_last_strong {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 1 ≤ r) :
    (∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)),
        (((p * ij.2 - ij.1 : ℕ) : ℤ) + (p : ℤ) ^ r)) ≡
      (∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)),
        ((p * ij.2 - ij.1 : ℕ) : ℤ))
      [ZMOD (p : ℤ) ^ (3 * r)] := by
  set s : Finset (ℕ × ℕ) := Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1))
  set x : ℕ × ℕ → ℤ := fun ij => ((p * ij.2 - ij.1 : ℕ) : ℤ)
  set N : ℤ := (p : ℤ) ^ r
  have hexp := prod_add_const_mod_cube (s := s) (x := x) (N := N)
  have hcof := sum_cofactor_last_dvd_two_pow (p := p) (r := r) hp hp5 hr
  have hσ2 := esym2_last_dvd_pow (p := p) (r := r) hp hp5 hr
  have hN3 : N ^ 3 = (p : ℤ) ^ (3 * r) := by
    simp [N]; rw [← pow_mul, mul_comm]
  have hN2 : N ^ 2 = (p : ℤ) ^ (2 * r) := by
    simp [N]; rw [← pow_mul, mul_comm]
  obtain ⟨c1, hc1⟩ := hcof
  obtain ⟨c2, hc2⟩ := hσ2
  have hmid := (Int.modEq_iff_dvd).mp hexp
  obtain ⟨K, hK⟩ := hmid
  have hdecomp :
      2 * (∏ i ∈ s, (x i + N) - ∏ i ∈ s, x i) =
        2 * N * esym1 s x + N ^ 2 * esym2 s x - N ^ 3 * K := by
    have : 2 * (∏ i ∈ s, (x i + N) - ∏ i ∈ s, x i - N * esym1 s x) =
        N ^ 2 * esym2 s x - N ^ 3 * K := by
      linear_combination -hK
    linear_combination this
  have hesym1 : esym1 s x =
      ∑ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)),
        ∏ kl ∈ (Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1))).erase ij,
          ((p * kl.2 - kl.1 : ℕ) : ℤ) := by
    simp [esym1, s, x]
  have hesym2 : esym2 s x =
      esym2 (Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)))
        (fun ij => ((p * ij.2 - ij.1 : ℕ) : ℤ)) := by
    simp [s, x]
  rw [hesym1, hc1, hesym2, hc2, hN2, hN3] at hdecomp
  have hN : N = (p : ℤ) ^ r := rfl
  have hdiff :
      2 * (∏ i ∈ s, (x i + N) - ∏ i ∈ s, x i) =
        (p : ℤ) ^ (3 * r) * (2 * c1 + c2 - K) := by
    rw [hdecomp, hN]
    ring
  have h2div : (p : ℤ) ^ (3 * r) ∣
      2 * (∏ i ∈ s, (x i + N) - ∏ i ∈ s, x i) :=
    ⟨2 * c1 + c2 - K, hdiff⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hdiv : (p : ℤ) ^ (3 * r) ∣
      (∏ i ∈ s, (x i + N) - ∏ i ∈ s, x i) := by
    set D := ∏ i ∈ s, (x i + N) - ∏ i ∈ s, x i
    by_cases hD0 : D = 0
    · simp [hD0]
    · have hne2 : (2 : ℤ) ≠ 0 := by decide
      have hge : 3 * r ≤ padicValInt p (2 * D) :=
        (padicValInt_dvd_iff (p := p) (3 * r) (2 * D)).mp h2div |>.resolve_left
          (mul_ne_zero hne2 hD0)
      have h2val : padicValInt p (2 : ℤ) = 0 := by
        rw [padicValInt.eq_zero_of_not_dvd]
        intro hd
        have : (p : ℤ) ∣ 2 := hd
        have : p ∣ 2 := Int.ofNat_dvd.mp (by simpa using this)
        have hcases := (Nat.dvd_prime Nat.prime_two).mp this
        rcases hcases with h1 | h2'
        · exact hp.ne_one h1
        · omega
      have : 3 * r ≤ padicValInt p D := by
        have hmul := padicValInt.mul (p := p) hne2 hD0
        omega
      exact (padicValInt_dvd_iff (p := p) (3 * r) D).mpr (Or.inr this)
  refine (Int.modEq_iff_dvd).mpr ?_
  simpa [neg_sub] using (dvd_neg.mpr hdiv)

lemma pow_dvd_delta_last_strong {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 1 ≤ r) :
    (p : ℤ) ^ (3 * r) ∣
      (rising (p ^ r) (p * p ^ (r - 1)) : ℤ) -
        risingY p r (p * p ^ (r - 1)) := by
  have hB : p ^ (r - 1) ≤ p ^ (r - 1) := le_rfl
  have hid := rising_sub_mul_pProd (p := p) (r := r) (B := p ^ (r - 1)) hp hr hB
  have hQmod := prod_add_pow_last_strong (p := p) (r := r) hp hp5 hr
  have hcastQ :
      ((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)),
          (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) =
        ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)),
          (((p * ij.2 - ij.1 : ℕ) : ℤ) + (p : ℤ) ^ r) := by
    simp [Nat.cast_prod, Nat.cast_add, Nat.cast_pow]
  have hcastP : (pProd p (p ^ (r - 1)) : ℤ) =
      ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)),
        ((p * ij.2 - ij.1 : ℕ) : ℤ) := by
    simp [pProd_eq_prod_product, Nat.cast_prod]
  have hQP : (p : ℤ) ^ (3 * r) ∣
      ((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)),
          (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) -
        pProd p (p ^ (r - 1)) := by
    have h := (Int.modEq_iff_dvd).mp hQmod
    rw [hcastQ, hcastP]
    exact dvd_neg.mp (by simpa [neg_sub] using h)
  have hyQP : (p : ℤ) ^ (3 * r) ∣
      (risingY p r (p * p ^ (r - 1)) : ℤ) *
        (((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 (p ^ (r - 1)),
            (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) -
          pProd p (p ^ (r - 1))) :=
    dvd_mul_of_dvd_right hQP _
  have hδP : (p : ℤ) ^ (3 * r) ∣
      ((rising (p ^ r) (p * p ^ (r - 1)) : ℤ) -
        risingY p r (p * p ^ (r - 1))) * (pProd p (p ^ (r - 1)) : ℤ) := by
    rwa [hid]
  haveI : Fact p.Prime := ⟨hp⟩
  have hPne : (pProd p (p ^ (r - 1)) : ℤ) ≠ 0 := by
    exact_mod_cast (ne_zero_of_lt (pProd_pos (p := p) hp.pos))
  by_cases hδ0 :
      ((rising (p ^ r) (p * p ^ (r - 1)) : ℤ) -
        risingY p r (p * p ^ (r - 1))) = 0
  · simp [hδ0]
  · have hge : 3 * r ≤
        padicValInt p
          (((rising (p ^ r) (p * p ^ (r - 1)) : ℤ) -
            risingY p r (p * p ^ (r - 1))) * pProd p (p ^ (r - 1))) :=
      (padicValInt_dvd_iff (p := p) (3 * r) _).mp hδP |>.resolve_left
        (mul_ne_zero hδ0 hPne)
    have hP0 : padicValInt p (pProd p (p ^ (r - 1)) : ℤ) = 0 := by
      rw [padicValInt.of_nat]
      exact padicValNat.eq_zero_of_not_dvd (p_not_dvd_pProd hp)
    have : 3 * r ≤
        padicValInt p
          ((rising (p ^ r) (p * p ^ (r - 1)) : ℤ) -
            risingY p r (p * p ^ (r - 1))) := by
      have hmulv := padicValInt.mul (p := p) hδ0 hPne
      omega
    exact (padicValInt_dvd_iff (p := p) (3 * r) _).mpr (Or.inr this)

lemma increment_quad_dvd_last_strong {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 2 ≤ r) :
    (p : ℤ) ^ (3 * r + 3) ∣
      3 * (2 * (risingY p r (p * p ^ (r - 1)) : ℤ) + 1) *
        ((rising (p ^ r) (p * p ^ (r - 1)) : ℤ) -
          risingY p r (p * p ^ (r - 1))) ^ 2 := by
  have hr1 : 1 ≤ r := by omega
  have hδ := pow_dvd_delta_last_strong hp hp5 hr1
  obtain ⟨t, ht⟩ := hδ
  refine ⟨3 * (2 * (risingY p r (p * p ^ (r - 1)) : ℤ) + 1) *
      ((p : ℤ) ^ (3 * r - 3) * t ^ 2), ?_⟩
  have hδ2 :
      ((rising (p ^ r) (p * p ^ (r - 1)) : ℤ) -
        risingY p r (p * p ^ (r - 1))) ^ 2 =
      ((p : ℤ) ^ (3 * r)) ^ 2 * t ^ 2 := by
    rw [ht]; ring
  have hpow : ((p : ℤ) ^ (3 * r)) ^ 2 = (p : ℤ) ^ (6 * r) := by
    rw [← pow_mul]; ring
  rw [hδ2, hpow]
  have hsplit : 6 * r = (3 * r + 3) + (3 * r - 3) := by omega
  calc
    3 * (2 * (risingY p r (p * p ^ (r - 1)) : ℤ) + 1) *
        ((p : ℤ) ^ (6 * r) * t ^ 2) =
      (3 * (2 * (risingY p r (p * p ^ (r - 1)) : ℤ) + 1) * t ^ 2) *
        (p : ℤ) ^ (6 * r) := by ring
    _ = (3 * (2 * (risingY p r (p * p ^ (r - 1)) : ℤ) + 1) * t ^ 2) *
          (p : ℤ) ^ ((3 * r + 3) + (3 * r - 3)) := by simp [hsplit]
    _ = (p : ℤ) ^ (3 * r + 3) *
          (3 * (2 * (risingY p r (p * p ^ (r - 1)) : ℤ) + 1) *
            ((p : ℤ) ^ (3 * r - 3) * t ^ 2)) := by
      rw [pow_add]; ring

/-! ### Intermediate pairing: p-free residues below `p * B` -/

def pfreeBelow (p m : ℕ) : Finset ℕ :=
  (range m).filter (fun k => ¬ p ∣ k)

lemma mem_pfreeBelow {p m k : ℕ} :
    k ∈ pfreeBelow p m ↔ k < m ∧ ¬ p ∣ k := by
  simp [pfreeBelow, mem_filter, mem_range]

lemma pfreeBelow_pos {p m k : ℕ} (hp : p.Prime) (hk : k ∈ pfreeBelow p m) :
    0 < k := by
  have ⟨_, hnd⟩ := mem_pfreeBelow.mp hk
  exact Nat.pos_of_ne_zero (fun h => hnd (by simp [h]))

lemma pfreeBelow_sub {p m k : ℕ} (hp : p.Prime) (hdvd : p ∣ m)
    (hk : k ∈ pfreeBelow p m) :
    m - k ∈ pfreeBelow p m := by
  have ⟨hklt, hnd⟩ := mem_pfreeBelow.mp hk
  have hk0 : 0 < k := pfreeBelow_pos hp hk
  have hm : 0 < m := Nat.pos_of_ne_zero (fun h => by
    rw [h] at hklt; exact Nat.not_lt_zero _ hklt)
  refine mem_pfreeBelow.mpr ⟨Nat.sub_lt hm hk0, ?_⟩
  intro hd
  have hsumd : p ∣ k + (m - k) := by
    rw [Nat.add_sub_of_le (Nat.le_of_lt hklt)]; exact hdvd
  exact hnd ((Nat.dvd_add_iff_left hd).mpr hsumd)

lemma pfreeBelow_sub_sub {p m k : ℕ}
    (hk : k ∈ pfreeBelow p m) :
    m - (m - k) = k := by
  have ⟨hklt, _⟩ := mem_pfreeBelow.mp hk
  exact Nat.sub_sub_self (Nat.le_of_lt hklt)

lemma rectangle_mem_pfreeBelow {p B s j : ℕ} (hp : p.Prime)
    (hs : s ∈ Icc 1 (p - 1)) (hj : j ∈ Icc 1 B) :
    p * j - s ∈ pfreeBelow p (p * B) := by
  have ⟨hs1, hs2⟩ := mem_Icc.mp hs
  have ⟨hj1, hj2⟩ := mem_Icc.mp hj
  have hs_lt : s < p := by omega
  have hpos : 0 < p * j - s := pval_pos hp.pos hs hj1
  have hlt : p * j - s < p * B := by
    have : p * j ≤ p * B := Nat.mul_le_mul_left p hj2
    have : p * j - s < p * j := Nat.sub_lt (Nat.mul_pos hp.pos hj1) (by omega)
    omega
  have hnd : ¬ p ∣ p * j - s := by
    intro hd
    have hz : ((p * j - s : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hd
    exact (pval_ne_zero hp hs hj1) hz
  exact mem_pfreeBelow.mpr ⟨hlt, hnd⟩

lemma pfreeBelow_eq_rectangle {p B : ℕ} (hp : p.Prime) (hB : 0 < B) :
    (Icc 1 (p - 1) ×ˢ Icc 1 B).image (fun ij => p * ij.2 - ij.1) =
      pfreeBelow p (p * B) := by
  ext t
  simp only [mem_image, mem_product]
  constructor
  · intro ⟨ij, ⟨hs, hj⟩, h⟩
    rw [← h]
    exact rectangle_mem_pfreeBelow hp hs hj
  · intro ht
    have ⟨htlt, hnd⟩ := mem_pfreeBelow.mp ht
    have ht0 : 0 < t := pfreeBelow_pos hp ht
    have hmodpos : 0 < t % p := by
      have : t % p ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
      exact Nat.pos_of_ne_zero this
    have hmodlt : t % p < p := Nat.mod_lt t hp.pos
    refine ⟨(p - t % p, t / p + 1), ?_, ?_⟩
    · constructor
      · refine mem_Icc.mpr ⟨?_, ?_⟩
        · have : t % p ≤ p - 1 := Nat.le_pred_of_lt hmodlt
          omega
        · have : 1 ≤ t % p := hmodpos
          omega
      · refine mem_Icc.mpr ⟨Nat.succ_pos _, ?_⟩
        have : t / p < B := by
          rw [Nat.div_lt_iff_lt_mul hp.pos, mul_comm]
          exact htlt
        exact Nat.succ_le_iff.mpr this
    · have hle : p - t % p ≤ p * (t / p + 1) := by
        have : p - t % p ≤ p := Nat.sub_le _ _
        have : p ≤ p * (t / p + 1) := Nat.le_mul_of_pos_right p (Nat.succ_pos _)
        omega
      have : p * (t / p + 1) - (p - t % p) = t := by
        rw [Nat.mul_add, mul_one]
        have h1 : p * (t / p) + p - (p - t % p) = p * (t / p) + t % p := by
          omega
        rw [h1, Nat.div_add_mod]
      exact this


lemma pfreeBelow_decomp_mem {p n c q ρ : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hq : q < c) (hρ : ρ ∈ pfree p n) :
    q * p ^ n + ρ ∈ pfreeBelow p (c * p ^ n) := by
  have ⟨hρlt, hρnd⟩ := mem_pfree.mp hρ
  refine mem_pfreeBelow.mpr ⟨?_, ?_⟩
  · have h1 : q * p ^ n + ρ < q * p ^ n + p ^ n := Nat.add_lt_add_left hρlt _
    have h2 : q * p ^ n + p ^ n = (q + 1) * p ^ n := by ring
    have h3 : (q + 1) * p ^ n ≤ c * p ^ n :=
      Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hq)
    omega
  · intro hd
    have hpn : p ∣ q * p ^ n :=
      dvd_mul_of_dvd_right (dvd_pow_self p (ne_zero_of_lt hn)) _
    exact hρnd ((Nat.dvd_add_iff_right hpn).mpr hd)

lemma pfreeBelow_eq_image {p n c : ℕ} (hp : p.Prime) (hn : 0 < n) :
    (range c ×ˢ pfree p n).image (fun qρ : ℕ × ℕ => qρ.1 * p ^ n + qρ.2) =
      pfreeBelow p (c * p ^ n) := by
  ext k
  simp only [mem_image, mem_product]
  constructor
  · intro ⟨qρ, ⟨hq, hρ⟩, h⟩
    rw [← h]
    exact pfreeBelow_decomp_mem hp hn (mem_range.mp hq) hρ
  · intro hk
    have ⟨hklt, hnd⟩ := mem_pfreeBelow.mp hk
    have hq : k / p ^ n < c := by
      rw [Nat.div_lt_iff_lt_mul (pow_pos hp.pos n)]
      exact hklt
    have hmodlt : k % p ^ n < p ^ n := Nat.mod_lt _ (pow_pos hp.pos n)
    have hmodnd : ¬ p ∣ k % p ^ n := by
      intro hd
      have hpn : p ∣ p ^ n := dvd_pow_self p (ne_zero_of_lt hn)
      have : p ∣ p ^ n * (k / p ^ n) + k % p ^ n :=
        dvd_add (dvd_mul_of_dvd_left hpn _) hd
      rw [Nat.div_add_mod] at this
      exact hnd this
    refine ⟨(k / p ^ n, k % p ^ n),
      ⟨mem_range.mpr hq, mem_pfree.mpr ⟨hmodlt, hmodnd⟩⟩, ?_⟩
    rw [mul_comm]
    exact Nat.div_add_mod k (p ^ n)

lemma pfreeBelow_image_inj {p n c : ℕ} (hp : p.Prime) (hn : 0 < n) :
    Set.InjOn (fun qρ : ℕ × ℕ => qρ.1 * p ^ n + qρ.2)
      ↑(range c ×ˢ pfree p n) := by
  intro qρ hqρ qρ' hqρ' heq
  have ⟨_, hρ⟩ := mem_product.mp (by exact hqρ : qρ ∈ range c ×ˢ pfree p n)
  have ⟨_, hρ'⟩ := mem_product.mp (by exact hqρ' : qρ' ∈ range c ×ˢ pfree p n)
  have hρlt := (mem_pfree.mp hρ).1
  have hρ'lt := (mem_pfree.mp hρ').1
  dsimp at heq
  have hmod : qρ.2 = qρ'.2 := by
    have h1 : (qρ.1 * p ^ n + qρ.2) % p ^ n = qρ.2 :=
      Nat.mul_add_mod_of_lt hρlt
    have h2 : (qρ'.1 * p ^ n + qρ'.2) % p ^ n = qρ'.2 :=
      Nat.mul_add_mod_of_lt hρ'lt
    calc
      qρ.2 = (qρ.1 * p ^ n + qρ.2) % p ^ n := h1.symm
      _ = (qρ'.1 * p ^ n + qρ'.2) % p ^ n := by rw [heq]
      _ = qρ'.2 := h2
  have hdiv : qρ.1 = qρ'.1 := by
    have hp0 : 0 < p ^ n := pow_pos hp.pos n
    have h1 : (qρ.1 * p ^ n + qρ.2) / p ^ n = qρ.1 := by
      rw [Nat.mul_comm qρ.1, Nat.mul_add_div hp0, Nat.div_eq_of_lt hρlt, add_zero]
    have h2 : (qρ'.1 * p ^ n + qρ'.2) / p ^ n = qρ'.1 := by
      rw [Nat.mul_comm qρ'.1, Nat.mul_add_div hp0, Nat.div_eq_of_lt hρ'lt, add_zero]
    calc
      qρ.1 = (qρ.1 * p ^ n + qρ.2) / p ^ n := h1.symm
      _ = (qρ'.1 * p ^ n + qρ'.2) / p ^ n := by rw [heq]
      _ = qρ'.1 := h2
  exact Prod.ext hdiv hmod

lemma sum_pfreeBelow_inv_sq {p n c : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : 0 < n) :
    (∑ k ∈ pfreeBelow p (c * p ^ n), ((k : ZMod (p ^ n))⁻¹) ^ 2) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have himg := pfreeBelow_eq_image (p := p) (n := n) (c := c) hp hn
  have hinj := pfreeBelow_image_inj (p := p) (n := n) (c := c) hp hn
  have hsum :
      ∑ k ∈ pfreeBelow p (c * p ^ n), ((k : ZMod (p ^ n))⁻¹) ^ 2 =
        ∑ qρ ∈ range c ×ˢ pfree p n,
          (((qρ.1 * p ^ n + qρ.2 : ℕ) : ZMod (p ^ n))⁻¹) ^ 2 := by
    rw [← himg, Finset.sum_image hinj]
  rw [hsum, Finset.sum_product]
  have hterm : ∀ q ∈ range c, ∀ ρ ∈ pfree p n,
      (((q * p ^ n + ρ : ℕ) : ZMod (p ^ n))⁻¹) ^ 2 =
        ((ρ : ZMod (p ^ n))⁻¹) ^ 2 := by
    intro q hq ρ hρ
    have : ((q * p ^ n + ρ : ℕ) : ZMod (p ^ n)) = (ρ : ZMod (p ^ n)) := by
      rw [Nat.cast_add, Nat.cast_mul]
      have : ((p ^ n : ℕ) : ZMod (p ^ n)) = 0 := ZMod.natCast_self (p ^ n)
      rw [this, mul_zero, zero_add]
    rw [this]
  have : ∑ q ∈ range c, ∑ ρ ∈ pfree p n,
      (((q * p ^ n + ρ : ℕ) : ZMod (p ^ n))⁻¹) ^ 2 =
      ∑ q ∈ range c, ∑ ρ ∈ pfree p n, ((ρ : ZMod (p ^ n))⁻¹) ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro q hq
    exact Finset.sum_congr rfl (fun ρ hρ => hterm q hq ρ hρ)
  rw [this]
  simp [sum_pfree_inv_sq_mod_pn hp hp5 hn]


lemma pfreeBelow_isUnit_pow {p m k n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hk : k ∈ pfreeBelow p m) :
    IsUnit (k : ZMod (p ^ n)) := by
  have hnd := (mem_pfreeBelow.mp hk).2
  rw [ZMod.isUnit_iff_coprime]
  have : Nat.Coprime p k := (hp.coprime_iff_not_dvd).mpr hnd
  exact this.symm.pow_right n

lemma pair_inv_pfreeBelow {p n c k : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hk : k ∈ pfreeBelow p (c * p ^ n)) :
    (k : ZMod (p ^ (2 * n)))⁻¹ +
      (((c * p ^ n - k : ℕ) : ZMod (p ^ (2 * n))))⁻¹ =
        (c : ZMod (p ^ (2 * n))) * (p : ZMod (p ^ (2 * n))) ^ n *
          ((k : ZMod (p ^ (2 * n))) *
            ((c * p ^ n - k : ℕ) : ZMod (p ^ (2 * n))))⁻¹ := by
  have hu := pfreeBelow_isUnit_pow (p := p) (m := c * p ^ n) (n := 2 * n) hp
    (by omega) hk
  have hdvd : p ∣ c * p ^ n :=
    dvd_mul_of_dvd_right (dvd_pow_self p (ne_zero_of_lt hn)) _
  have hk' : c * p ^ n - k ∈ pfreeBelow p (c * p ^ n) :=
    pfreeBelow_sub hp hdvd hk
  have hu' := pfreeBelow_isUnit_pow (p := p) (m := c * p ^ n) (n := 2 * n) hp
    (by omega) hk'
  have hadd : (k : ZMod (p ^ (2 * n))) +
      ((c * p ^ n - k : ℕ) : ZMod (p ^ (2 * n))) =
        (c : ZMod (p ^ (2 * n))) * (p : ZMod (p ^ (2 * n))) ^ n := by
    have hle : k ≤ c * p ^ n := le_of_lt (mem_pfreeBelow.mp hk).1
    rw [Nat.cast_sub hle, Nat.cast_mul, Nat.cast_pow]
    ring
  rw [inv_add_inv_of_unit hu hu', hadd]

lemma pair_inv_pfreeBelow_neg {p n c k : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hk : k ∈ pfreeBelow p (c * p ^ n)) :
    (k : ZMod (p ^ (2 * n)))⁻¹ +
      ((c * p ^ n - k : ℕ) : ZMod (p ^ (2 * n)))⁻¹ =
        -((c : ZMod (p ^ (2 * n))) * (p : ZMod (p ^ (2 * n))) ^ n *
          ((k : ZMod (p ^ (2 * n)))⁻¹) ^ 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hu := pfreeBelow_isUnit_pow (n := 2 * n) hp (by omega) hk
  rw [pair_inv_pfreeBelow hp hn hk]
  have hgoal :
      (c : ZMod (p ^ (2 * n))) * (p : ZMod (p ^ (2 * n))) ^ n *
        (((k : ZMod (p ^ (2 * n))) *
            ((c * p ^ n - k : ℕ) : ZMod (p ^ (2 * n))))⁻¹ +
          ((k : ZMod (p ^ (2 * n)))⁻¹) ^ 2) = 0 := by
    have hpn : (p : ZMod (p ^ (2 * n))) ^ n *
        (((k : ZMod (p ^ (2 * n))) *
            ((c * p ^ n - k : ℕ) : ZMod (p ^ (2 * n))))⁻¹ +
          ((k : ZMod (p ^ (2 * n)))⁻¹) ^ 2) = 0 := by
      apply pn_mul_of_castHom_zero hn
      set π := ZMod.castHom (pow_dvd_pow p (by omega : n ≤ 2 * n)) (ZMod (p ^ n))
      have hdvd : p ∣ c * p ^ n :=
        dvd_mul_of_dvd_right (dvd_pow_self p (ne_zero_of_lt hn)) _
      have hk' : c * p ^ n - k ∈ pfreeBelow p (c * p ^ n) :=
        pfreeBelow_sub hp hdvd hk
      have hu' : IsUnit ((k : ZMod (p ^ (2 * n))) *
          ((c * p ^ n - k : ℕ) : ZMod (p ^ (2 * n)))) :=
        (pfreeBelow_isUnit_pow (n := 2 * n) hp (by omega) hk).mul
          (pfreeBelow_isUnit_pow (n := 2 * n) hp (by omega) hk')
      have hle : k ≤ c * p ^ n := le_of_lt (mem_pfreeBelow.mp hk).1
      have hcast_m : π ((c : ZMod (p ^ (2 * n))) *
          (p : ZMod (p ^ (2 * n))) ^ n) = 0 := by
        have : ((c * p ^ n : ℕ) : ZMod (p ^ n)) = 0 :=
          (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_mul_left (p ^ n) c)
        have hpmap : π (p : ZMod (p ^ (2 * n))) = (p : ZMod (p ^ n)) := by
          simp [π, ZMod.castHom_apply]
        have hcmap : π (c : ZMod (p ^ (2 * n))) = (c : ZMod (p ^ n)) := by
          simp [π, ZMod.castHom_apply]
        rw [map_mul, map_pow, hpmap, hcmap, ← Nat.cast_pow, ← Nat.cast_mul]
        exact this
      have hcast_p : π ((p : ZMod (p ^ (2 * n))) ^ n) = 0 := by
        have : ((p ^ n : ℕ) : ZMod (p ^ n)) = 0 := ZMod.natCast_self (p ^ n)
        rw [map_pow]
        have hpmap : π (p : ZMod (p ^ (2 * n))) = (p : ZMod (p ^ n)) := by
          simp [π, ZMod.castHom_apply]
        rw [hpmap, ← Nat.cast_pow]
        exact this
      have hcast_sub : π ((c * p ^ n - k : ℕ) : ZMod (p ^ (2 * n))) =
          - π (k : ZMod (p ^ (2 * n))) := by
        have hrew : ((c * p ^ n - k : ℕ) : ZMod (p ^ (2 * n))) =
            (c : ZMod (p ^ (2 * n))) * (p : ZMod (p ^ (2 * n))) ^ n - k := by
          rw [Nat.cast_sub hle, Nat.cast_mul, Nat.cast_pow]
        rw [hrew, map_sub, hcast_m]
        simp
      have hcast_prod :
          π ((k : ZMod (p ^ (2 * n))) *
              ((c * p ^ n - k : ℕ) : ZMod (p ^ (2 * n)))) =
            - (π (k : ZMod (p ^ (2 * n)))) ^ 2 := by
        rw [map_mul, hcast_sub]; ring
      have hcast_inv :
          π (((k : ZMod (p ^ (2 * n))) *
              ((c * p ^ n - k : ℕ) : ZMod (p ^ (2 * n))))⁻¹) =
            (π ((k : ZMod (p ^ (2 * n))) *
              ((c * p ^ n - k : ℕ) : ZMod (p ^ (2 * n)))))⁻¹ := by
        refine (ZMod.inv_eq_of_mul_eq_one (p ^ n) _ _ ?_).symm
        rw [← map_mul, unit_mul_inv hu', map_one]
      rw [map_add, hcast_inv, hcast_prod, map_pow]
      have hkinv : π ((k : ZMod (p ^ (2 * n)))⁻¹) =
          (π (k : ZMod (p ^ (2 * n))))⁻¹ := by
        refine (ZMod.inv_eq_of_mul_eq_one (p ^ n) _ _ ?_).symm
        rw [← map_mul, unit_mul_inv hu, map_one]
      rw [hkinv]
      set a := π (k : ZMod (p ^ (2 * n)))
      have hk0 : IsUnit a := by
        have : a = (k : ZMod (p ^ n)) := by
          simp [a, π, ZMod.castHom_apply]
        rw [this]
        exact pfreeBelow_isUnit_pow (n := n) hp hn hk
      have hneg : (-(a ^ 2))⁻¹ = - (a⁻¹) ^ 2 := by
        refine ZMod.inv_eq_of_mul_eq_one (p ^ n) _ _ ?_
        have hsq : a ^ 2 * (a⁻¹) ^ 2 = 1 := by
          rw [← mul_pow, unit_mul_inv hk0, one_pow]
        rw [neg_mul_neg]
        exact hsq
      rw [hneg]
      ring
    linear_combination (c : ZMod (p ^ (2 * n))) * hpn
  linear_combination hgoal

lemma sum_pfreeBelow_inv_two_pow {p n c : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : 0 < n) :
    ∑ k ∈ pfreeBelow p (c * p ^ n), (k : ZMod (p ^ (2 * n)))⁻¹ = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have h2n : 0 < 2 * n := by omega
  have h2u := two_isUnit_pow (p := p) (n := 2 * n) hp hp2 h2n
  have hdvd : p ∣ c * p ^ n :=
    dvd_mul_of_dvd_right (dvd_pow_self p (ne_zero_of_lt hn)) _
  have hperm :
      ∑ k ∈ pfreeBelow p (c * p ^ n),
          ((c * p ^ n - k : ℕ) : ZMod (p ^ (2 * n)))⁻¹ =
        ∑ k ∈ pfreeBelow p (c * p ^ n), (k : ZMod (p ^ (2 * n)))⁻¹ := by
    refine Finset.sum_bij (fun k _ => c * p ^ n - k) ?_ ?_ ?_ ?_
    · intro k hk; exact pfreeBelow_sub hp hdvd hk
    · intro k hk k' hk' h
      have := congrArg (fun t => c * p ^ n - t) h
      simpa [pfreeBelow_sub_sub hk, pfreeBelow_sub_sub hk'] using this
    · intro k hk
      refine ⟨c * p ^ n - k, pfreeBelow_sub hp hdvd hk, pfreeBelow_sub_sub hk⟩
    · intro k hk; rfl
  have hpairs :
      ∑ k ∈ pfreeBelow p (c * p ^ n),
          ((k : ZMod (p ^ (2 * n)))⁻¹ +
            ((c * p ^ n - k : ℕ) : ZMod (p ^ (2 * n)))⁻¹) =
        (2 : ZMod (p ^ (2 * n))) *
          ∑ k ∈ pfreeBelow p (c * p ^ n), (k : ZMod (p ^ (2 * n)))⁻¹ := by
    rw [sum_add_distrib, hperm]
    exact (two_mul _).symm
  have hterm : ∀ k ∈ pfreeBelow p (c * p ^ n),
      (k : ZMod (p ^ (2 * n)))⁻¹ +
        ((c * p ^ n - k : ℕ) : ZMod (p ^ (2 * n)))⁻¹ =
        -((c : ZMod (p ^ (2 * n))) * (p : ZMod (p ^ (2 * n))) ^ n *
          ((k : ZMod (p ^ (2 * n)))⁻¹) ^ 2) :=
    fun k hk => pair_inv_pfreeBelow_neg hp hn hk
  have hsum :
      ∑ k ∈ pfreeBelow p (c * p ^ n),
          ((k : ZMod (p ^ (2 * n)))⁻¹ +
            ((c * p ^ n - k : ℕ) : ZMod (p ^ (2 * n)))⁻¹) =
        -((c : ZMod (p ^ (2 * n))) * (p : ZMod (p ^ (2 * n))) ^ n *
          ∑ k ∈ pfreeBelow p (c * p ^ n),
            ((k : ZMod (p ^ (2 * n)))⁻¹) ^ 2) := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
    have h1 := Finset.mul_sum (s := pfreeBelow p (c * p ^ n))
      (f := fun k => ((k : ZMod (p ^ (2 * n)))⁻¹) ^ 2)
      (a := (c : ZMod (p ^ (2 * n))) * (p : ZMod (p ^ (2 * n))) ^ n)
    rw [← h1]
  have hcast :
      ZMod.castHom (pow_dvd_pow p (by omega : n ≤ 2 * n)) (ZMod (p ^ n))
        (∑ k ∈ pfreeBelow p (c * p ^ n),
          ((k : ZMod (p ^ (2 * n)))⁻¹) ^ 2) = 0 := by
    rw [map_sum]
    have hcongr : ∀ k ∈ pfreeBelow p (c * p ^ n),
        ZMod.castHom (pow_dvd_pow p (by omega : n ≤ 2 * n)) (ZMod (p ^ n))
          (((k : ZMod (p ^ (2 * n)))⁻¹) ^ 2) =
        ((k : ZMod (p ^ n))⁻¹) ^ 2 := by
      intro k hk
      rw [map_pow]
      have hu := pfreeBelow_isUnit_pow (n := 2 * n) hp h2n hk
      have hinv :
          ZMod.castHom (pow_dvd_pow p (by omega : n ≤ 2 * n)) (ZMod (p ^ n))
            ((k : ZMod (p ^ (2 * n)))⁻¹) =
          (ZMod.castHom (pow_dvd_pow p (by omega : n ≤ 2 * n)) (ZMod (p ^ n))
            (k : ZMod (p ^ (2 * n))))⁻¹ := by
        refine (ZMod.inv_eq_of_mul_eq_one (p ^ n) _ _ ?_).symm
        rw [← map_mul, unit_mul_inv hu, map_one]
      rw [hinv]
      simp [ZMod.castHom_apply]
    rw [Finset.sum_congr rfl hcongr, sum_pfreeBelow_inv_sq hp hp5 hn]
  have hmul0 :
      (p : ZMod (p ^ (2 * n))) ^ n *
        ∑ k ∈ pfreeBelow p (c * p ^ n),
          ((k : ZMod (p ^ (2 * n)))⁻¹) ^ 2 = 0 :=
    pn_mul_of_castHom_zero hn hcast
  have : (2 : ZMod (p ^ (2 * n))) *
      ∑ k ∈ pfreeBelow p (c * p ^ n), (k : ZMod (p ^ (2 * n)))⁻¹ = 0 := by
    rw [← hpairs, hsum, mul_assoc, hmul0, mul_zero, neg_zero]
  have hcancel :=
    congrArg (fun z => (2 : ZMod (p ^ (2 * n)))⁻¹ * z) this
  simpa [← mul_assoc, unit_inv_mul h2u] using hcancel

lemma pB_decomp {p B : ℕ} (hp : p.Prime) (hB0 : 0 < B) :
    p * B = (B / p ^ padicValNat p B) * p ^ (padicValNat p B + 1) := by
  have hB : p ^ padicValNat p B ∣ B := pow_padicValNat_dvd
  calc
    p * B = p * (p ^ padicValNat p B * (B / p ^ padicValNat p B)) := by
      rw [Nat.mul_div_cancel' hB]
    _ = (B / p ^ padicValNat p B) * (p * p ^ padicValNat p B) := by ring
    _ = (B / p ^ padicValNat p B) * p ^ (padicValNat p B + 1) := by
      rw [mul_comm p, ← pow_succ]

lemma sum_cofactor_inter_dvd {p B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hB0 : 0 < B) :
    (p : ℤ) ^ (2 * (padicValNat p B + 1)) ∣
      ∑ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
        ∏ kl ∈ (Icc 1 (p - 1) ×ˢ Icc 1 B).erase ij,
          ((p * kl.2 - kl.1 : ℕ) : ℤ) := by
  set n := padicValNat p B + 1
  set c := B / p ^ padicValNat p B
  have hn : 0 < n := Nat.succ_pos _
  have hpn : 0 < 2 * n := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ (2 * n)) := ⟨pow_ne_zero (2 * n) hp.ne_zero⟩
  set s : Finset (ℕ × ℕ) := Icc 1 (p - 1) ×ˢ Icc 1 B
  set Pℤ : ℤ := ∏ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ℤ)
  set Sℤ : ℤ :=
    ∑ ij ∈ s, ∏ kl ∈ s.erase ij, ((p * kl.2 - kl.1 : ℕ) : ℤ)
  have hsumZ : (Sℤ : ZMod (p ^ (2 * n))) =
      ∑ ij ∈ s, ∏ kl ∈ s.erase ij,
        ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ (2 * n))) := by
    simp only [Sℤ, Int.cast_sum, Int.cast_prod, Int.cast_natCast]
  have hPZ : (Pℤ : ZMod (p ^ (2 * n))) =
      ∏ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ (2 * n))) := by
    simp only [Pℤ, Int.cast_prod, Int.cast_natCast]
  have hunit : ∀ ij ∈ s,
      IsUnit ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ (2 * n))) := by
    intro ij hij
    have hij' := mem_product.mp hij
    have mem := rectangle_mem_pfreeBelow hp hij'.1 hij'.2
    exact pfreeBelow_isUnit_pow (n := 2 * n) hp hpn mem
  have hterm : ∀ ij ∈ s,
      ∏ kl ∈ s.erase ij, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ (2 * n))) =
        ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ (2 * n)))⁻¹ *
          ∏ kl ∈ s, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ (2 * n))) := by
    intro ij hij
    have hu := hunit ij hij
    have hmul := Finset.mul_prod_erase s
      (fun kl => ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ (2 * n)))) hij
    calc
      ∏ kl ∈ s.erase ij, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ (2 * n))) =
          ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ (2 * n)))⁻¹ *
            (((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ (2 * n))) *
              ∏ kl ∈ s.erase ij,
                ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ (2 * n)))) := by
        rw [← mul_assoc, unit_inv_mul hu, one_mul]
      _ = ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ (2 * n)))⁻¹ *
            ∏ kl ∈ s, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ (2 * n))) := by
        rw [hmul]
  have hH : ∑ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ (2 * n)))⁻¹ = 0 := by
    have himg := pfreeBelow_eq_rectangle (p := p) (B := B) hp hB0
    have hinj : Set.InjOn (fun ij : ℕ × ℕ => p * ij.2 - ij.1) ↑s := by
      intro ij hij kl hkl heq
      exact rectangle_map_inj hp (by exact hij) (by exact hkl) heq
    have :
        ∑ t ∈ s.image (fun ij => p * ij.2 - ij.1),
            (t : ZMod (p ^ (2 * n)))⁻¹ =
          ∑ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ (2 * n)))⁻¹ :=
      Finset.sum_image hinj
    rw [← this, himg]
    have hdecomp := pB_decomp (p := p) (B := B) hp hB0
    have : pfreeBelow p (p * B) = pfreeBelow p (c * p ^ n) := by
      rw [hdecomp]
    rw [this]
    exact sum_pfreeBelow_inv_two_pow hp hp5 hn
  have hfactor : (Sℤ : ZMod (p ^ (2 * n))) =
      (Pℤ : ZMod (p ^ (2 * n))) *
        ∑ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ (2 * n)))⁻¹ := by
    rw [hsumZ, Finset.sum_congr rfl hterm]
    have hsmul :
        ∑ ij ∈ s,
            ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ (2 * n)))⁻¹ *
              ∏ kl ∈ s, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ (2 * n))) =
          (∑ ij ∈ s, ((p * ij.2 - ij.1 : ℕ) : ZMod (p ^ (2 * n)))⁻¹) *
            ∏ kl ∈ s, ((p * kl.2 - kl.1 : ℕ) : ZMod (p ^ (2 * n))) :=
      (Finset.sum_mul _ _ _).symm
    rw [hsmul, ← hPZ]
    ac_rfl
  have : (Sℤ : ZMod (p ^ (2 * n))) = 0 := by
    rw [hfactor, hH, mul_zero]
  exact (CharP.intCast_eq_zero_iff (ZMod (p ^ (2 * n))) (p ^ (2 * n)) Sℤ).mp this

lemma prod_add_pow_inter {p r B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 2 ≤ r) (hB0 : 0 < B) :
    (p : ℤ) ^ min (r + 2 * (padicValNat p B + 1)) (2 * r) ∣
      (∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
          (((p * ij.2 - ij.1 : ℕ) : ℤ) + (p : ℤ) ^ r)) -
        (∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
          ((p * ij.2 - ij.1 : ℕ) : ℤ)) := by
  set s : Finset (ℕ × ℕ) := Icc 1 (p - 1) ×ˢ Icc 1 B
  set x : ℕ × ℕ → ℤ := fun ij => ((p * ij.2 - ij.1 : ℕ) : ℤ)
  set n := padicValNat p B + 1
  have hexp := prod_add_const_mod_sq (s := s) (x := x) (N := (p : ℤ) ^ r)
  have hcof := sum_cofactor_inter_dvd (p := p) (B := B) hp hp5 hB0
  have hN2 : ((p : ℤ) ^ r) ^ 2 = (p : ℤ) ^ (2 * r) := by
    rw [← pow_mul, mul_comm]
  have hdvdN2 :
      (p : ℤ) ^ (2 * r) ∣
        (∏ i ∈ s, x i + (p : ℤ) ^ r * ∑ i ∈ s, ∏ j ∈ s.erase i, x j -
          ∏ i ∈ s, (x i + (p : ℤ) ^ r)) := by
    have := (Int.modEq_iff_dvd).mp hexp
    simpa [hN2] using this
  obtain ⟨K, hK⟩ := hdvdN2
  have hdecomp :
      ∏ i ∈ s, (x i + (p : ℤ) ^ r) - ∏ i ∈ s, x i =
        (p : ℤ) ^ r * ∑ i ∈ s, ∏ j ∈ s.erase i, x j -
          (p : ℤ) ^ (2 * r) * K := by
    linear_combination -hK
  obtain ⟨c, hc⟩ := hcof
  have hD :
      ∏ i ∈ s, (x i + (p : ℤ) ^ r) - ∏ i ∈ s, x i =
        (p : ℤ) ^ (r + 2 * n) * c - (p : ℤ) ^ (2 * r) * K := by
    rw [hdecomp, hc, pow_add]; ring
  have hle1 : min (r + 2 * n) (2 * r) ≤ r + 2 * n := min_le_left _ _
  have hle2 : min (r + 2 * n) (2 * r) ≤ 2 * r := min_le_right _ _
  have hd1 : (p : ℤ) ^ min (r + 2 * n) (2 * r) ∣
      (p : ℤ) ^ (r + 2 * n) * c :=
    dvd_mul_of_dvd_left (pow_dvd_pow _ hle1) _
  have hd2 : (p : ℤ) ^ min (r + 2 * n) (2 * r) ∣
      (p : ℤ) ^ (2 * r) * K :=
    dvd_mul_of_dvd_left (pow_dvd_pow _ hle2) _
  rw [hD]
  exact dvd_sub hd1 hd2

lemma pow_dvd_delta_inter {p r B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 2 ≤ r) (hB0 : 0 < B) (hB : B ≤ p ^ (r - 1)) :
    (p : ℤ) ^ (padicValInt p (risingY p r (p * B) : ℤ) +
      min (r + 2 * (padicValNat p B + 1)) (2 * r)) ∣
      (rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B) := by
  have hr1 : 1 ≤ r := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  have hid := rising_sub_mul_pProd (p := p) (r := r) (B := B) hp hr1 hB
  have hQP0 := prod_add_pow_inter (p := p) (r := r) (B := B) hp hp5 hr hB0
  have hcastQ :
      ((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
          (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) =
        ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
          (((p * ij.2 - ij.1 : ℕ) : ℤ) + (p : ℤ) ^ r) := by
    simp [Nat.cast_prod, Nat.cast_add, Nat.cast_pow]
  have hcastP : (pProd p B : ℤ) =
      ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B, ((p * ij.2 - ij.1 : ℕ) : ℤ) := by
    simp [pProd_eq_prod_product, Nat.cast_prod]
  have hQP : (p : ℤ) ^ min (r + 2 * (padicValNat p B + 1)) (2 * r) ∣
      ((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
          (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) - pProd p B := by
    rwa [hcastQ, hcastP]
  set y : ℤ := (risingY p r (p * B) : ℤ)
  set δ : ℤ := (rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B)
  set QP : ℤ :=
    ((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
        (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) - pProd p B
  have hid' : δ * (pProd p B : ℤ) = y * QP := hid
  have hPne : (pProd p B : ℤ) ≠ 0 := by
    exact_mod_cast (ne_zero_of_lt (pProd_pos (p := p) hp.pos))
  by_cases hy0 : y = 0
  · have : δ * (pProd p B : ℤ) = 0 := by rw [hid', hy0, zero_mul]
    have hδ0 : δ = 0 := (mul_eq_zero.mp this).resolve_right hPne
    simp [hδ0]
  · by_cases hδ0 : δ = 0
    · simp [hδ0]
    · have hQPne : QP ≠ 0 := by
        intro h
        have : δ * (pProd p B : ℤ) = 0 := by rw [hid', h, mul_zero]
        exact hδ0 ((mul_eq_zero.mp this).resolve_right hPne)
      have hP0 : padicValInt p (pProd p B : ℤ) = 0 := by
        rw [padicValInt.of_nat]
        exact padicValNat.eq_zero_of_not_dvd (p_not_dvd_pProd hp)
      have hδP : padicValInt p (δ * (pProd p B : ℤ)) = padicValInt p δ := by
        rw [padicValInt.mul (p := p) hδ0 hPne, hP0, add_zero]
      have hv : padicValInt p (δ * (pProd p B : ℤ)) =
          padicValInt p y + padicValInt p QP := by
        rw [hid']
        exact padicValInt.mul (p := p) hy0 hQPne
      have hQPge : min (r + 2 * (padicValNat p B + 1)) (2 * r) ≤
          padicValInt p QP :=
        (padicValInt_dvd_iff (p := p) _ QP).mp hQP |>.resolve_left hQPne
      have : padicValInt p y +
          min (r + 2 * (padicValNat p B + 1)) (2 * r) ≤ padicValInt p δ := by
        omega
      exact (padicValInt_dvd_iff (p := p) _ δ).mpr (Or.inr this)

lemma increment_quad_dvd_inter {p r B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 2 ≤ r) (hB0 : 0 < B) (hB : B < p ^ (r - 1)) :
    (p : ℤ) ^ (3 * r + 3) ∣
      3 * (2 * (risingY p r (p * B) : ℤ) + 1) *
        ((rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B)) ^ 2 := by
  have hr1 : 1 ≤ r := by omega
  have hBle : B ≤ p ^ (r - 1) := Nat.le_of_lt hB
  have hδ := pow_dvd_delta_inter hp hp5 hr hB0 hBle
  have hy : padicValInt p (risingY p r (p * B) : ℤ) =
      (r - 1) - padicValNat p B :=
    padicValInt_risingY hp hr1 hB0 hBle
  rw [hy] at hδ
  set e := (r - 1) - padicValNat p B +
    min (r + 2 * (padicValNat p B + 1)) (2 * r)
  haveI : Fact p.Prime := ⟨hp⟩
  have h2e : 2 * e ≥ 3 * r + 3 := by
    have hs : padicValNat p B < r - 1 :=
      padicValNat_lt_of_lt_pow (p := p) (k := B) (r := r - 1) hB0 hB
    omega
  obtain ⟨t, ht⟩ := hδ
  refine ⟨3 * (2 * (risingY p r (p * B) : ℤ) + 1) *
      ((p : ℤ) ^ (2 * e - (3 * r + 3)) * t ^ 2), ?_⟩
  have hδ2 :
      ((rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B)) ^ 2 =
      ((p : ℤ) ^ e) ^ 2 * t ^ 2 := by
    rw [ht]; ring
  have hpow : ((p : ℤ) ^ e) ^ 2 = (p : ℤ) ^ (2 * e) := by
    rw [← pow_mul, mul_comm]
  rw [hδ2, hpow]
  have hexp : (p : ℤ) ^ (2 * e) =
      (p : ℤ) ^ (3 * r + 3) * (p : ℤ) ^ (2 * e - (3 * r + 3)) := by
    rw [← pow_add, Nat.add_sub_of_le h2e]
  rw [hexp]
  ring

lemma increment_quad_dvd_zero {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    (p : ℤ) ^ (3 * r + 3) ∣
      3 * (2 * (risingY p r 0 : ℤ) + 1) *
        ((rising (p ^ r) 0 : ℤ) - risingY p r 0) ^ 2 := by
  have hδ : (rising (p ^ r) 0 : ℤ) - risingY p r 0 = 0 := by
    simp [rising_zero_right, risingY_zero]
  simp [hδ]

lemma S2d_dvd {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
    (p : ℤ) ^ (3 * r + 3) ∣ S2d p r := by
  unfold S2d
  refine dvd_sum ?_
  intro k hk
  have hkle : k ≤ p ^ r :=
    Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hk).1)
  have hdv : p ∣ k := (mem_filter.mp hk).2
  obtain ⟨B, hB⟩ := hdv
  have hBle : B ≤ p ^ (r - 1) := by
    have : p * B ≤ p * p ^ (r - 1) := by
      rw [← hB, prime_mul_pow_pred (by omega : 1 ≤ r)]; exact hkle
    exact Nat.le_of_mul_le_mul_left this hp.pos
  subst hB
  rcases eq_or_lt_of_le hBle with hEq | hLt
  · -- last term B = p^{r-1}
    have : p * B = p * p ^ (r - 1) := by rw [hEq]
    simpa [this] using increment_quad_dvd_last_strong hp hp5 hr
  · by_cases hB0 : B = 0
    · subst hB0
      simpa using increment_quad_dvd_zero hp (by omega : 1 ≤ r)
    · have hBpos : 0 < B := Nat.pos_of_ne_zero hB0
      exact increment_quad_dvd_inter hp hp5 hr hBpos hLt

/-! ### The reduced binomial `u_k` and the cubic p-free sum `S3f` -/

/-- `u k` is the p-unit `rising(p^r, k) / p^r` when `p ∤ k`. -/
def risingU (p r k : ℕ) : ℕ := rising (p ^ r) k / p ^ r

lemma risingU_mul {p r k : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hk0 : 0 < k) (hk : k ≤ p ^ r) (hdv : ¬ p ∣ k) :
    rising (p ^ r) k = risingU p r k * p ^ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hkn : k < p ^ r :=
    lt_of_le_of_ne hk (fun h => hdv (by rw [h]; exact dvd_pow_self p (ne_zero_of_lt hr)))
  have hval := padicValNat_rising_of_not_dvd (p := p) (r := r) (k := k) hk0 (le_of_lt hkn) hdv
  have hne : rising (p ^ r) k ≠ 0 := by
    unfold rising
    exact choose_ne_zero (by
      have : 1 ≤ p ^ r := Nat.one_le_pow r p hp.pos
      omega)
  have hdvd : p ^ r ∣ rising (p ^ r) k :=
    (padicValNat_dvd_iff_le hne).mpr (le_of_eq hval.symm)
  exact (Nat.div_mul_cancel hdvd).symm

lemma risingU_mul_k {p r k : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hk0 : 0 < k) (hk : k ≤ p ^ r) (hdv : ¬ p ∣ k) :
    risingU p r k * k = choose (p ^ r + k - 1) (k - 1) := by
  have hmul := choose_mul_right_of_rising (p ^ r) k hk0
  have hrw := risingU_mul hp hr hk0 hk hdv
  have hp0 : 0 < p ^ r := pow_pos hp.pos r
  have : risingU p r k * p ^ r * k = choose (p ^ r + k - 1) (k - 1) * p ^ r := by
    rw [← hrw]; exact hmul
  have : risingU p r k * k * p ^ r = choose (p ^ r + k - 1) (k - 1) * p ^ r := by
    convert this using 1; ring
  exact Nat.mul_right_cancel hp0 this

lemma S3f_eq_pow_sum {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    S3f p r = 2 * (p : ℤ) ^ (3 * r) *
      ∑ k ∈ (range (p ^ r + 1)).filter (¬p ∣ ·), (risingU p r k : ℤ) ^ 3 := by
  unfold S3f
  have hterm : ∀ k ∈ (range (p ^ r + 1)).filter (¬p ∣ ·),
      2 * (rising (p ^ r) k : ℤ) ^ 3 =
        2 * (p : ℤ) ^ (3 * r) * (risingU p r k : ℤ) ^ 3 := by
    intro k hk
    have ⟨hkR, hnd⟩ := mem_filter.mp hk
    have hkle : k ≤ p ^ r := Nat.lt_succ_iff.mp (mem_range.mp hkR)
    have hk0 : 0 < k := Nat.pos_of_ne_zero (fun h => hnd (by simp [h]))
    have hrw := risingU_mul hp hr hk0 hkle hnd
    have : (rising (p ^ r) k : ℤ) = (risingU p r k : ℤ) * (p : ℤ) ^ r := by
      exact_mod_cast hrw
    rw [this, mul_pow, ← pow_mul, show r * 3 = 3 * r by ring]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]


lemma pfree_eq_filter_succ (p r : ℕ) (hp : p.Prime) (hr : 0 < r) :
    (range (p ^ r + 1)).filter (¬p ∣ ·) = pfree p r := by
  ext k
  simp only [mem_filter, mem_range, mem_pfree]
  constructor
  · intro ⟨hk, hnd⟩
    exact ⟨lt_of_le_of_ne (Nat.lt_succ_iff.mp hk)
      (fun h => hnd (by rw [h]; exact dvd_pow_self p (ne_zero_of_lt hr))), hnd⟩
  · intro ⟨hk, hnd⟩
    exact ⟨Nat.lt_succ_of_lt hk, hnd⟩

lemma risingU_cast_inv {p r k : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hk : k ∈ pfree p r) :
    (risingU p r k : ZMod p) = (k : ZMod p)⁻¹ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ⟨hkl, hnd⟩ := mem_pfree.mp hk
  have hk0 : 0 < k := pfree_pos hp hk
  have hkle : k ≤ p ^ r := Nat.le_of_lt hkl
  have hmod := rising_div_pow_mul_mod_p hp hr hk0 hkle hnd
  have hmul : ((risingU p r k * k : ℕ) : ZMod p) = 1 := by
    unfold risingU
    simpa using (ZMod.natCast_eq_natCast_iff (rising (p ^ r) k / p ^ r * k) 1 p).mpr hmod
  have hku : IsUnit (k : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (hp.coprime_iff_not_dvd).2 hnd |>.symm
  have hmul' : (risingU p r k : ZMod p) * k = 1 := by
    rwa [Nat.cast_mul] at hmul
  have := congrArg (fun z : ZMod p => z * (k : ZMod p)⁻¹) hmul'
  simpa [mul_assoc, unit_mul_inv hku] using this


lemma pfree_mod_mem {p r k : ℕ} (hp : p.Prime) (hk : k ∈ pfree p r) :
    k % p ∈ Icc 1 (p - 1) := by
  have ⟨_, hnd⟩ := mem_pfree.mp hk
  have hmod0 : k % p ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
  have hlt : k % p < p := Nat.mod_lt k hp.pos
  exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero hmod0, Nat.le_pred_of_lt hlt⟩



lemma pfree_eq_add_image {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    pfree p r =
      (Icc 1 (p - 1) ×ˢ range (p ^ (r - 1))).image (fun sj => sj.1 + sj.2 * p) := by
  ext k
  constructor
  · intro hk
    have ⟨hkl, hnd⟩ := mem_pfree.mp hk
    refine mem_image.mpr ⟨(k % p, k / p), ?_, ?_⟩
    · exact mem_product.mpr ⟨pfree_mod_mem hp hk, mem_range.mpr (by
        have : k < p * p ^ (r - 1) := by
          rwa [← _root_.pow_succ', Nat.sub_add_cancel hr]
        exact Nat.div_lt_of_lt_mul this)⟩
    · rw [Nat.add_comm, Nat.mul_comm, Nat.div_add_mod]
  · intro hk
    obtain ⟨sj, hsj, rfl⟩ := mem_image.mp hk
    have ⟨hs, hj⟩ := mem_product.mp hsj
    have ⟨hs1, hs2⟩ := mem_Icc.mp hs
    have hslt : sj.1 < p := by omega
    have hjlt := mem_range.mp hj
    have hkl : sj.1 + sj.2 * p < p ^ r := by
      have : sj.2 + 1 ≤ p ^ (r - 1) := Nat.succ_le_of_lt hjlt
      have hmul : (sj.2 + 1) * p ≤ p ^ (r - 1) * p := Nat.mul_le_mul_right p this
      have hpr : p ^ (r - 1) * p = p ^ r := by
        rw [mul_comm, prime_mul_pow_pred hr]
      have : sj.2 * p + p ≤ p ^ r := by
        rw [hpr] at hmul
        convert hmul using 1; ring
      omega
    have hnd : ¬ p ∣ sj.1 + sj.2 * p := by
      intro hd
      have : p ∣ sj.1 := (Nat.dvd_add_iff_left (dvd_mul_left p sj.2)).mpr hd
      exact Nat.not_dvd_of_pos_of_lt hs1 hslt this
    exact mem_pfree.mpr ⟨hkl, hnd⟩

lemma add_image_inj {p : ℕ} (hp : p.Prime) {s : Finset ℕ}
    {sj kl : ℕ × ℕ}
    (hsj : sj ∈ Icc 1 (p - 1) ×ˢ s) (hkl : kl ∈ Icc 1 (p - 1) ×ˢ s)
    (heq : sj.1 + sj.2 * p = kl.1 + kl.2 * p) : sj = kl := by
  have hslt : sj.1 < p := by
    have := (mem_product.mp hsj).1; have := mem_Icc.mp this; omega
  have hklt : kl.1 < p := by
    have := (mem_product.mp hkl).1; have := mem_Icc.mp this; omega
  have hsmod : (sj.1 + sj.2 * p) % p = sj.1 := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hslt]
  have hkmod : (kl.1 + kl.2 * p) % p = kl.1 := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hklt]
  have h12 : sj.1 = kl.1 := by rw [← hsmod, heq, hkmod]
  have h22 : sj.2 = kl.2 := by
    have : sj.2 * p = kl.2 * p := by omega
    exact Nat.eq_of_mul_eq_mul_right hp.pos this
  ext <;> assumption

lemma sum_risingU_pow_mod_p {p r m : ℕ} (hp : p.Prime) (hr : 2 ≤ r) :
    (∑ k ∈ pfree p r, (risingU p r k : ZMod p) ^ m) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hr1 : 1 ≤ r := by omega
  rw [pfree_eq_add_image hp hr1]
  have hinj : Set.InjOn (fun sj : ℕ × ℕ => sj.1 + sj.2 * p)
      ↑(Icc 1 (p - 1) ×ˢ range (p ^ (r - 1))) := by
    intro sj hsj kl hkl heq
    exact add_image_inj hp (by exact hsj) (by exact hkl) heq
  rw [Finset.sum_image hinj]
  have hterm : ∀ sj ∈ Icc 1 (p - 1) ×ˢ range (p ^ (r - 1)),
      (risingU p r (sj.1 + sj.2 * p) : ZMod p) ^ m =
        ((sj.1 : ZMod p)⁻¹) ^ m := by
    intro sj hsj
    have hmem : sj.1 + sj.2 * p ∈ pfree p r := by
      rw [pfree_eq_add_image hp hr1]
      exact mem_image_of_mem _ hsj
    rw [risingU_cast_inv hp hr1 hmem]
    have hs := (mem_product.mp hsj).1
    have hslt : sj.1 < p := by have := mem_Icc.mp hs; omega
    have : ((sj.1 + sj.2 * p : ℕ) : ZMod p) = (sj.1 : ZMod p) := by
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero]
    rw [this]
  rw [Finset.sum_congr rfl hterm, Finset.sum_product]
  have hp0 : (p : ZMod p) ^ (r - 1) = 0 := by
    rw [ZMod.natCast_self, zero_pow (by omega : r - 1 ≠ 0)]
  have hinner : ∀ s ∈ Icc 1 (p - 1),
      ∑ _j ∈ range (p ^ (r - 1)), ((s : ZMod p)⁻¹) ^ m = 0 := by
    intro s hs
    simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_pow]
    rw [hp0, zero_mul]
  rw [Finset.sum_congr rfl hinner]
  simp



lemma sum_risingU_cube_mod_p {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r) :
    (∑ k ∈ pfree p r, (risingU p r k : ZMod p) ^ 3) = 0 :=
  sum_risingU_pow_mod_p hp hr

lemma S3f_dvd_three_r {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    (p : ℤ) ^ (3 * r) ∣ S3f p r := by
  rw [S3f_eq_pow_sum hp hr]
  refine ⟨2 * ∑ k ∈ (range (p ^ r + 1)).filter (¬p ∣ ·), (risingU p r k : ℤ) ^ 3, ?_⟩
  ring

lemma sum_risingU_cube_int_dvd {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r) :
    (p : ℤ) ∣ ∑ k ∈ pfree p r, (risingU p r k : ℤ) ^ 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h0 := sum_risingU_cube_mod_p hp hr
  have hcast :
      ((∑ k ∈ pfree p r, risingU p r k ^ 3 : ℕ) : ZMod p) =
        ∑ k ∈ pfree p r, (risingU p r k : ZMod p) ^ 3 := by
    simp [Nat.cast_sum, Nat.cast_pow]
  have hdvd : p ∣ ∑ k ∈ pfree p r, risingU p r k ^ 3 :=
    (ZMod.natCast_eq_zero_iff _ p).mp (hcast.trans h0)
  simpa [Nat.cast_sum, Nat.cast_pow] using (Int.natCast_dvd_natCast.mpr hdvd)

lemma S3f_dvd_succ {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r) :
    (p : ℤ) ^ (3 * r + 1) ∣ S3f p r := by
  have hr1 : 1 ≤ r := by omega
  rw [S3f_eq_pow_sum hp hr1, pfree_eq_filter_succ p r hp (by omega)]
  obtain ⟨t, ht⟩ := sum_risingU_cube_int_dvd hp hr
  refine ⟨2 * t, ?_⟩
  rw [ht, pow_succ]
  ring


lemma S2f_eq_pow_sum {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    S2f p r = 3 * (p : ℤ) ^ (2 * r) *
      ∑ k ∈ (range (p ^ r + 1)).filter (¬p ∣ ·), (risingU p r k : ℤ) ^ 2 := by
  unfold S2f
  have hterm : ∀ k ∈ (range (p ^ r + 1)).filter (¬p ∣ ·),
      3 * (rising (p ^ r) k : ℤ) ^ 2 =
        3 * (p : ℤ) ^ (2 * r) * (risingU p r k : ℤ) ^ 2 := by
    intro k hk
    have ⟨hkR, hnd⟩ := mem_filter.mp hk
    have hkle : k ≤ p ^ r := Nat.lt_succ_iff.mp (mem_range.mp hkR)
    have hk0 : 0 < k := Nat.pos_of_ne_zero (fun h => hnd (by simp [h]))
    have hrw := risingU_mul hp hr hk0 hkle hnd
    have : (rising (p ^ r) k : ℤ) = (risingU p r k : ℤ) * (p : ℤ) ^ r := by
      exact_mod_cast hrw
    rw [this, mul_pow, ← pow_mul, show r * 2 = 2 * r by ring]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]

lemma S2f_dvd_two_r {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    (p : ℤ) ^ (2 * r) ∣ S2f p r := by
  rw [S2f_eq_pow_sum hp hr]
  refine ⟨3 * ∑ k ∈ (range (p ^ r + 1)).filter (¬p ∣ ·), (risingU p r k : ℤ) ^ 2, ?_⟩
  ring

lemma sum_risingU_sq_int_dvd {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r) :
    (p : ℤ) ∣ ∑ k ∈ pfree p r, (risingU p r k : ℤ) ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h0 : (∑ k ∈ pfree p r, (risingU p r k : ZMod p) ^ 2) = 0 :=
    sum_risingU_pow_mod_p hp hr
  have hcast :
      ((∑ k ∈ pfree p r, risingU p r k ^ 2 : ℕ) : ZMod p) =
        ∑ k ∈ pfree p r, (risingU p r k : ZMod p) ^ 2 := by
    simp [Nat.cast_sum, Nat.cast_pow]
  have hdvd : p ∣ ∑ k ∈ pfree p r, risingU p r k ^ 2 :=
    (ZMod.natCast_eq_zero_iff _ p).mp (hcast.trans h0)
  simpa [Nat.cast_sum, Nat.cast_pow] using (Int.natCast_dvd_natCast.mpr hdvd)

lemma S2f_dvd_succ {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r) :
    (p : ℤ) ^ (2 * r + 1) ∣ S2f p r := by
  have hr1 : 1 ≤ r := by omega
  rw [S2f_eq_pow_sum hp hr1, pfree_eq_filter_succ p r hp (by omega)]
  obtain ⟨t, ht⟩ := sum_risingU_sq_int_dvd hp hr
  refine ⟨3 * t, ?_⟩
  rw [ht, pow_succ]
  ring

/-! ### Converting integer divisibility to `Nat.ModEq` -/

lemma modEq_of_int_sub_dvd {a b n : ℕ} (h : (n : ℤ) ∣ (a : ℤ) - b) :
    a ≡ b [MOD n] := by
  rw [Nat.modEq_iff_dvd]
  rwa [← dvd_neg, neg_sub]



lemma choose_pair_mod_p {p r k : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hk0 : 0 < k) (hk : k < p ^ r) :
    choose (p ^ r + k - 1) (k - 1) ≡
      choose (2 * p ^ r - k - 1) (p ^ r - k - 1) [MOD p] := by
  have hm1 : k - 1 < p ^ r := by omega
  have h1 := choose_prime_pow_add_mod_p (p := p) (r := r) (m := k - 1) hp hm1
  have hm2 : p ^ r - k - 1 < p ^ r := by omega
  have h2 := choose_prime_pow_add_mod_p (p := p) (r := r) (m := p ^ r - k - 1) hp hm2
  have heq1 : p ^ r + (k - 1) = p ^ r + k - 1 := by omega
  have heq2 : p ^ r + (p ^ r - k - 1) = 2 * p ^ r - k - 1 := by omega
  rw [heq1] at h1
  rw [heq2] at h2
  exact h1.trans h2.symm

lemma S1d_add_S2d_add_S3d_add_S2f_add_S3f_eq {p r : ℕ} :
    S1d p r + S2d p r + S3d p r + S2f p r + S3f p r =
      ∑ k ∈ range (p ^ r + 1), incrementZ p r k :=
  (increment_sum_split p r).symm

lemma increment_sum_eq_sub (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) :
    ∑ k ∈ range (p ^ r + 1), incrementZ p r k =
      (A357565 (p ^ r) : ℤ) - A357565 (p ^ (r - 1)) :=
  (A357565_sub_eq_sum_incrementZ p r hp hr).symm


/-! ### Faulhaber for cubes and the p-free cube sum -/

lemma sum_range_cube_mul_four (n : ℕ) :
    4 * ∑ k ∈ range n, (k : ℤ) ^ 3 = ((n : ℤ) * (n - 1)) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    simp only [Nat.cast_succ]
    ring

lemma sum_pfree_nat_cube {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    ∑ k ∈ pfree p r, (k : ℤ) ^ 3 =
      ∑ k ∈ range (p ^ r), (k : ℤ) ^ 3 -
        (p : ℤ) ^ 3 * ∑ j ∈ range (p ^ (r - 1)), (j : ℤ) ^ 3 := by
  have hsplit :
      ∑ k ∈ range (p ^ r), (k : ℤ) ^ 3 =
        ∑ k ∈ (range (p ^ r)).filter (p ∣ ·), (k : ℤ) ^ 3 +
          ∑ k ∈ pfree p r, (k : ℤ) ^ 3 := by
    rw [← sum_filter_add_sum_filter_not (range (p ^ r)) (p ∣ ·)]
    rfl
  have hreind :
      ∑ j ∈ range (p ^ (r - 1)), ((p * j : ℕ) : ℤ) ^ 3 =
        ∑ k ∈ (range (p ^ r)).filter (p ∣ ·), (k : ℤ) ^ 3 := by
    refine Finset.sum_bij (fun j _ => p * j) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [mem_filter, mem_range]
      have hj' : j < p ^ (r - 1) := mem_range.mp hj
      have : p * j < p * p ^ (r - 1) := Nat.mul_lt_mul_of_pos_left hj' hp.pos
      rw [prime_mul_pow_pred hr] at this
      exact ⟨this, dvd_mul_right p j⟩
    · intro j _ j' _ heq
      exact Nat.eq_of_mul_eq_mul_left hp.pos heq
    · intro k hk
      have ⟨hklt, hkd⟩ := mem_filter.mp hk
      refine ⟨k / p, ?_, Nat.mul_div_cancel' hkd⟩
      rw [mem_range]
      have : k < p * p ^ (r - 1) := by
        rw [prime_mul_pow_pred hr]; exact mem_range.mp hklt
      exact Nat.div_lt_of_lt_mul this
    · intro j hj
      rfl
  have hpow : ∑ j ∈ range (p ^ (r - 1)), ((p * j : ℕ) : ℤ) ^ 3 =
      (p : ℤ) ^ 3 * ∑ j ∈ range (p ^ (r - 1)), (j : ℤ) ^ 3 := by
    simp only [Nat.cast_mul, mul_pow, Finset.mul_sum]
  rw [hsplit, ← hreind, hpow]
  ring

lemma sum_pfree_cube_factor {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    4 * ∑ k ∈ pfree p r, (k : ℤ) ^ 3 =
      (p : ℤ) ^ (2 * r) *
        (((p : ℤ) ^ r - 1) ^ 2 - (p : ℤ) * ((p : ℤ) ^ (r - 1) - 1) ^ 2) := by
  rw [sum_pfree_nat_cube hp hr, mul_sub, sum_range_cube_mul_four,
    mul_left_comm, sum_range_cube_mul_four]
  simp only [Nat.cast_pow]
  have hpow2r : ((p : ℤ) ^ r) ^ 2 = (p : ℤ) ^ (2 * r) := by
    rw [← pow_mul, mul_comm]
  have h1 : ((p : ℤ) ^ r * ((p : ℤ) ^ r - 1)) ^ 2 =
      (p : ℤ) ^ (2 * r) * ((p : ℤ) ^ r - 1) ^ 2 := by
    rw [mul_pow, hpow2r]
  have hexp : 3 + 2 * (r - 1) = 2 * r + 1 := by omega
  have h2 :
      (p : ℤ) ^ 3 * ((p : ℤ) ^ (r - 1) * ((p : ℤ) ^ (r - 1) - 1)) ^ 2 =
        (p : ℤ) ^ (2 * r) * ((p : ℤ) * ((p : ℤ) ^ (r - 1) - 1) ^ 2) := by
    have hmid : ((p : ℤ) ^ (r - 1)) ^ 2 = (p : ℤ) ^ (2 * (r - 1)) := by
      rw [← pow_mul, mul_comm]
    calc
      (p : ℤ) ^ 3 * ((p : ℤ) ^ (r - 1) * ((p : ℤ) ^ (r - 1) - 1)) ^ 2 =
          (p : ℤ) ^ 3 * ((p : ℤ) ^ (2 * (r - 1)) * ((p : ℤ) ^ (r - 1) - 1) ^ 2) := by
        rw [mul_pow, hmid]
      _ = (p : ℤ) ^ (3 + 2 * (r - 1)) * ((p : ℤ) ^ (r - 1) - 1) ^ 2 := by
        rw [← mul_assoc, ← pow_add]
      _ = (p : ℤ) ^ (2 * r + 1) * ((p : ℤ) ^ (r - 1) - 1) ^ 2 := by
        rw [hexp]
      _ = (p : ℤ) ^ (2 * r) * (p : ℤ) * ((p : ℤ) ^ (r - 1) - 1) ^ 2 := by
        rw [pow_succ]
      _ = (p : ℤ) ^ (2 * r) * ((p : ℤ) * ((p : ℤ) ^ (r - 1) - 1) ^ 2) := by
        ring
  rw [h1, h2]
  ring

lemma odd_prime_not_dvd_four {p : ℕ} (hp : p.Prime) (hodd : Odd p) : ¬ p ∣ 4 := by
  intro h
  have : p ∣ 2 * 2 := h
  have h2 : p ∣ 2 := (hp.dvd_mul.mp this).elim id id
  have hp2 : p = 2 := (Nat.dvd_prime Nat.prime_two).mp h2 |>.resolve_left hp.ne_one
  have : ¬ Odd 2 := by decide
  exact this (hp2 ▸ hodd)

lemma sum_pfree_cube_dvd {p r : ℕ} (hp : p.Prime) (hodd : Odd p) (hr : 1 ≤ r) :
    (p : ℤ) ^ (2 * r) ∣ ∑ k ∈ pfree p r, (k : ℤ) ^ 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h4 := sum_pfree_cube_factor hp hr
  set S := ∑ k ∈ pfree p r, (k : ℤ) ^ 3
  have h4div : (p : ℤ) ^ (2 * r) ∣ 4 * S := ⟨_, h4⟩
  by_cases hS0 : S = 0
  · simp [hS0]
  · have hne4 : (4 : ℤ) ≠ 0 := by decide
    have hge : 2 * r ≤ padicValInt p (4 * S) :=
      (padicValInt_dvd_iff (p := p) (2 * r) (4 * S)).mp h4div |>.resolve_left
        (mul_ne_zero hne4 hS0)
    have h4val : padicValInt p (4 : ℤ) = 0 := by
      rw [padicValInt.eq_zero_of_not_dvd]
      intro hd
      exact odd_prime_not_dvd_four hp hodd (Int.ofNat_dvd.mp (by simpa using hd))
    have : 2 * r ≤ padicValInt p S := by
      have hmul := padicValInt.mul (p := p) hne4 hS0
      omega
    exact (padicValInt_dvd_iff (p := p) (2 * r) S).mpr (Or.inr this)

lemma S1d_term_zero (p r : ℕ) :
    6 * (risingY p r 0 : ℤ) * ((risingY p r 0 : ℤ) + 1) *
      ((rising (p ^ r) 0 : ℤ) - risingY p r 0) = 0 := by
  simp [rising_zero_right, risingY_zero]

lemma S1d_term_last_dvd {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) :
    (p : ℤ) ^ (3 * r) ∣
      6 * (risingY p r (p * p ^ (r - 1)) : ℤ) *
        ((risingY p r (p * p ^ (r - 1)) : ℤ) + 1) *
        ((rising (p ^ r) (p * p ^ (r - 1)) : ℤ) -
          risingY p r (p * p ^ (r - 1))) := by
  have hδ := pow_dvd_delta_last_strong hp hp5 hr
  obtain ⟨t, ht⟩ := hδ
  refine ⟨6 * (risingY p r (p * p ^ (r - 1)) : ℤ) *
      ((risingY p r (p * p ^ (r - 1)) : ℤ) + 1) * t, ?_⟩
  rw [ht]
  ring

lemma S1d_term_pfreeB_dvd {p r B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 2 ≤ r) (hB0 : 0 < B) (hB : B ≤ p ^ (r - 1)) (hnd : ¬ p ∣ B) :
    (p : ℤ) ^ (3 * r) ∣
      6 * (risingY p r (p * B) : ℤ) * ((risingY p r (p * B) : ℤ) + 1) *
        ((rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B)) := by
  have hr1 : 1 ≤ r := by omega
  have hδ := pow_dvd_delta_pfree_B hp hp5 hr hB0 hB hnd
  haveI : Fact p.Prime := ⟨hp⟩
  set y : ℤ := (risingY p r (p * B) : ℤ)
  set δ : ℤ := (rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B)
  have hyval : padicValInt p y = r - 1 := by
    rw [padicValInt_risingY hp hr1 hB0 hB, padicValNat.eq_zero_of_not_dvd hnd,
      tsub_zero]
  obtain ⟨t, ht⟩ := hδ
  have hdivy : (p : ℤ) ^ (r - 1) ∣ y :=
    (padicValInt_dvd_iff (p := p) (r - 1) y).mpr (Or.inr (by omega))
  obtain ⟨s, hs⟩ := hdivy
  refine ⟨6 * s * (y + 1) * t, ?_⟩
  have hpow : (p : ℤ) ^ (r - 1) * (p : ℤ) ^ (2 * r + 1) = (p : ℤ) ^ (3 * r) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    6 * y * (y + 1) * δ =
        6 * ((p : ℤ) ^ (r - 1) * s) * (y + 1) * ((p : ℤ) ^ (2 * r + 1) * t) := by
      rw [hs, ht]
    _ = 6 * s * (y + 1) * t * ((p : ℤ) ^ (r - 1) * (p : ℤ) ^ (2 * r + 1)) := by
      ring
    _ = 6 * s * (y + 1) * t * (p : ℤ) ^ (3 * r) := by
      rw [hpow]
    _ = (p : ℤ) ^ (3 * r) * (6 * s * (y + 1) * t) := by
      ring

/-! ### `S1d` has valuation `≥ 6` when `r = 2` -/

lemma S1d_dvd_r2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p : ℤ) ^ 6 ∣ S1d p 2 := by
  unfold S1d
  refine dvd_sum ?_
  intro k hk
  have ⟨hkR, hdv⟩ := mem_filter.mp hk
  have hkle : k ≤ p ^ 2 := Nat.lt_succ_iff.mp (mem_range.mp hkR)
  obtain ⟨B, hB⟩ := hdv
  have hpp : p ^ 2 = p * p := by rw [pow_two]
  have hBle : B ≤ p := by
    have : p * B ≤ p * p := by
      rw [← hB, ← hpp]; exact hkle
    exact Nat.le_of_mul_le_mul_left this hp.pos
  subst hB
  rcases eq_or_lt_of_le hBle with hEq | hLt
  · have hB : B = p ^ (2 - 1) := by simp [hEq]
    simpa [hB] using
      S1d_term_last_dvd (p := p) (r := 2) hp hp5 (by decide : 1 ≤ 2)
  · by_cases hB0 : B = 0
    · subst hB0
      simp [S1d_term_zero]
    · have hBpos : 0 < B := Nat.pos_of_ne_zero hB0
      have hnd : ¬ p ∣ B := by
        intro hd
        obtain ⟨t, ht⟩ := hd
        have hlt : p * B < p * p := Nat.mul_lt_mul_of_pos_left hLt hp.pos
        rw [ht] at hlt
        have hpt : p * t < p := Nat.lt_of_mul_lt_mul_left hlt
        have ht0 : t = 0 := by
          by_contra nt
          have : 1 ≤ t := Nat.pos_of_ne_zero nt
          have : p ≤ p * t := Nat.le_mul_of_pos_right p this
          exact Nat.not_le_of_gt hpt this
        have : B = 0 := by rw [ht, ht0, mul_zero]
        exact hB0 this
      have hBle' : B ≤ p ^ (2 - 1) := by simp [hBle]
      exact S1d_term_pfreeB_dvd (p := p) (r := 2) (B := B) hp hp5
        (by decide : 2 ≤ 2) hBpos hBle' hnd

lemma foo_three_two :
    A357565 (3 ^ 2) ≡ A357565 (3 ^ 1) [MOD 3 ^ 9] := by
  decide


lemma foo_three_three :
    A357565 (3 ^ 3) ≡ A357565 (3 ^ 2) [MOD 3 ^ 12] := by
  decide

lemma foo_five_two :
    A357565 (5 ^ 2) ≡ A357565 (5 ^ 1) [MOD 5 ^ 9] := by
  decide


lemma foo_seven_two :
    A357565 (7 ^ 2) ≡ A357565 (7 ^ 1) [MOD 7 ^ 9] := by
  decide


lemma foo_three_four :
    A357565 (3 ^ 4) ≡ A357565 (3 ^ 3) [MOD 3 ^ 15] := by
  set_option maxRecDepth 20000 in
  decide

lemma foo_three_five :
    A357565 (3 ^ 5) ≡ A357565 (3 ^ 4) [MOD 3 ^ 18] := by
  set_option maxRecDepth 50000 in
  decide


/-! ### Inverse cubes on `Icc 1 (p-1)` -/

lemma odd_prime_ne_two {p : ℕ} (hodd : Odd p) : p ≠ 2 := by
  intro h
  have : ¬ Odd 2 := by decide
  exact this (h ▸ hodd)

lemma p_sub_one_not_dvd_three {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    ¬ (p - 1) ∣ (3 : ℕ) := by
  intro h
  have hle : p - 1 ≤ 3 := Nat.le_of_dvd (by decide : 0 < 3) h
  have : 2 ≤ p := hp.two_le
  have : p ≤ 4 := by omega
  revert h
  interval_cases p
  · intro h; exact absurd hodd (by decide : ¬ Odd 2)
  · intro h; exact (by decide : ¬ (2 : ℕ) ∣ 3) h
  · intro h; exact absurd hp (by decide : ¬ Nat.Prime 4)

lemma Icc_isUnit_mod_p {p k : ℕ} (hp : p.Prime) (hk : k ∈ Icc 1 (p - 1)) :
    IsUnit (k : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [ZMod.isUnit_iff_coprime]
  have ⟨h1, h2⟩ := mem_Icc.mp hk
  have hlt : k < p := by omega
  exact (hp.coprime_iff_not_dvd).2
    (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero (ne_zero_of_lt h1)) hlt) |>.symm

lemma Icc_inv_val_mem {p k : ℕ} (hp : p.Prime) (hk : k ∈ Icc 1 (p - 1)) :
    ((k : ZMod p)⁻¹).val ∈ Icc 1 (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hu := Icc_isUnit_mod_p hp hk
  have hne : ((k : ZMod p)⁻¹).val ≠ 0 := by
    intro h
    have h0 : (k : ZMod p)⁻¹ = 0 := (ZMod.val_eq_zero ((k : ZMod p)⁻¹)).mp h
    have h1 := unit_mul_inv hu
    rw [h0, mul_zero] at h1
    exact one_ne_zero h1.symm
  have hlt : ((k : ZMod p)⁻¹).val < p := ZMod.val_lt _
  exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero hne, Nat.le_pred_of_lt hlt⟩

lemma sum_Icc_inv_cube_mod_p {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    (∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 3) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp2 := odd_prime_ne_two hodd
  have hperm :
      ∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 3 =
        ∑ k ∈ Icc 1 (p - 1), (k : ZMod p) ^ 3 := by
    refine (Finset.sum_bij (fun k (_ : k ∈ Icc 1 (p - 1)) =>
        ((k : ZMod p)⁻¹).val) ?_ ?_ ?_ ?_).symm
    · intro k hk; exact Icc_inv_val_mem hp hk
    · intro k hk k' hk' heq
      have hinv : (k : ZMod p)⁻¹ = (k' : ZMod p)⁻¹ := by
        have := congrArg (fun t : ℕ => (t : ZMod p)) heq
        simpa [ZMod.natCast_zmod_val] using this
      have hu := Icc_isUnit_mod_p hp hk
      have heq' : (k : ZMod p) = (k' : ZMod p) := by
        calc
          (k : ZMod p) = ((k : ZMod p)⁻¹)⁻¹ := (unit_inv_inv hu).symm
          _ = ((k' : ZMod p)⁻¹)⁻¹ := by rw [hinv]
          _ = (k' : ZMod p) := unit_inv_inv (Icc_isUnit_mod_p hp hk')
      have ⟨hk1, hk2⟩ := mem_Icc.mp hk
      have ⟨hk1', hk2'⟩ := mem_Icc.mp hk'
      exact eq_of_zmod_eq_of_lt heq' (by omega) (by omega)
    · intro t ht
      refine ⟨((t : ZMod p)⁻¹).val, Icc_inv_val_mem hp ht, ?_⟩
      have hu := Icc_isUnit_mod_p hp ht
      apply eq_of_zmod_eq_of_lt _ (ZMod.val_lt _) (by have := mem_Icc.mp ht; omega)
      simp [ZMod.natCast_zmod_val, unit_inv_inv hu]
    · intro k hk
      have hu := Icc_isUnit_mod_p hp hk
      simp [ZMod.natCast_zmod_val]
  rw [hperm]
  exact sum_Icc_pow_eq_zero hp hp2 (p_sub_one_not_dvd_three hp hodd)


lemma foo_eleven_two :
    A357565 (11 ^ 2) ≡ A357565 (11 ^ 1) [MOD 11 ^ 9] := by
  set_option maxRecDepth 10000 in
  decide

lemma foo_five_three :
    A357565 (5 ^ 3) ≡ A357565 (5 ^ 2) [MOD 5 ^ 12] := by
  set_option maxRecDepth 20000 in
  decide


lemma foo_thirteen_two :
    A357565 (13 ^ 2) ≡ A357565 (13 ^ 1) [MOD 13 ^ 9] := by
  set_option maxRecDepth 20000 in
  decide


lemma foo_seventeen_two :
    A357565 (17 ^ 2) ≡ A357565 (17 ^ 1) [MOD 17 ^ 9] := by
  set_option maxRecDepth 30000 in
  decide


lemma foo_nineteen_two :
    A357565 (19 ^ 2) ≡ A357565 (19 ^ 1) [MOD 19 ^ 9] := by
  set_option maxRecDepth 40000 in
  decide

lemma foo_seven_three :
    A357565 (7 ^ 3) ≡ A357565 (7 ^ 2) [MOD 7 ^ 12] := by
  set_option maxRecDepth 40000 in
  decide



/-! ### Intermediate cube expansion: `esym2` and `S1d` for `r ≥ 3` -/

lemma rectangle_inner_prod_B {p B n : ℕ} (hp : p.Prime) (hB0 : 0 < B) (hn : 0 < n)
    {i j : ℕ × ℕ} {s : Finset (ℕ × ℕ)}
    (hs : s = Icc 1 (p - 1) ×ˢ Icc 1 B)
    (hi : i ∈ s) (hj : j ∈ s.erase i) :
    ∏ k ∈ (s.erase i).erase j, ((p * k.2 - k.1 : ℕ) : ZMod (p ^ n)) =
      (∏ k ∈ s, ((p * k.2 - k.1 : ℕ) : ZMod (p ^ n))) *
        ((p * i.2 - i.1 : ℕ) : ZMod (p ^ n))⁻¹ *
        ((p * j.2 - j.1 : ℕ) : ZMod (p ^ n))⁻¹ := by
  have hj' : j ∈ s := (mem_erase.mp hj).2
  have hi' : i ∈ Icc 1 (p - 1) ×ˢ Icc 1 B := by rwa [hs] at hi
  have hj'' : j ∈ Icc 1 (p - 1) ×ˢ Icc 1 B := by rwa [hs] at hj'
  have memi := rectangle_mem_pfreeBelow hp (mem_product.mp hi').1 (mem_product.mp hi').2
  have memj := rectangle_mem_pfreeBelow hp (mem_product.mp hj'').1 (mem_product.mp hj'').2
  have hui := pfreeBelow_isUnit_pow (n := n) hp hn memi
  have huj := pfreeBelow_isUnit_pow (n := n) hp hn memj
  set f : ℕ × ℕ → ZMod (p ^ n) := fun k => ((p * k.2 - k.1 : ℕ) : ZMod (p ^ n))
  have hprod : f i * ∏ k ∈ s.erase i, f k = ∏ k ∈ s, f k :=
    Finset.mul_prod_erase s f hi
  have hprod2 : f j * ∏ k ∈ (s.erase i).erase j, f k = ∏ k ∈ s.erase i, f k :=
    Finset.mul_prod_erase (s.erase i) f hj
  have hmul : f i * f j * ∏ k ∈ (s.erase i).erase j, f k = ∏ k ∈ s, f k := by
    rw [mul_assoc, hprod2, hprod]
  have hcancel : (f i)⁻¹ * (f j)⁻¹ * (f i * f j * ∏ k ∈ (s.erase i).erase j, f k) =
      ∏ k ∈ (s.erase i).erase j, f k := by
    calc
      (f i)⁻¹ * (f j)⁻¹ * (f i * f j * ∏ k ∈ (s.erase i).erase j, f k) =
          ((f i)⁻¹ * f i) * ((f j)⁻¹ * f j) *
            ∏ k ∈ (s.erase i).erase j, f k := by ring
      _ = 1 * 1 * ∏ k ∈ (s.erase i).erase j, f k := by
        rw [unit_inv_mul hui, unit_inv_mul huj]
      _ = ∏ k ∈ (s.erase i).erase j, f k := by ring
  have hgoal : ∏ k ∈ (s.erase i).erase j, f k =
      (∏ k ∈ s, f k) * (f i)⁻¹ * (f j)⁻¹ := by
    calc
      ∏ k ∈ (s.erase i).erase j, f k =
          (f i)⁻¹ * (f j)⁻¹ * (f i * f j * ∏ k ∈ (s.erase i).erase j, f k) :=
        hcancel.symm
      _ = (f i)⁻¹ * (f j)⁻¹ * ∏ k ∈ s, f k := by rw [hmul]
      _ = (∏ k ∈ s, f k) * (f i)⁻¹ * (f j)⁻¹ := by ring
  simpa [f] using hgoal

lemma sum_pfreeBelow_inv {p n c : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) :
    ∑ k ∈ pfreeBelow p (c * p ^ n), (k : ZMod (p ^ n))⁻¹ = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have himg := pfreeBelow_eq_image (p := p) (n := n) (c := c) hp hn
  have hinj := pfreeBelow_image_inj (p := p) (n := n) (c := c) hp hn
  have hsum :
      ∑ k ∈ pfreeBelow p (c * p ^ n), (k : ZMod (p ^ n))⁻¹ =
        ∑ qρ ∈ range c ×ˢ pfree p n,
          ((qρ.1 * p ^ n + qρ.2 : ℕ) : ZMod (p ^ n))⁻¹ := by
    rw [← himg, Finset.sum_image hinj]
  rw [hsum, Finset.sum_product]
  have hterm : ∀ q ∈ range c, ∀ ρ ∈ pfree p n,
      ((q * p ^ n + ρ : ℕ) : ZMod (p ^ n))⁻¹ = (ρ : ZMod (p ^ n))⁻¹ := by
    intro q hq ρ hρ
    have : ((q * p ^ n + ρ : ℕ) : ZMod (p ^ n)) = (ρ : ZMod (p ^ n)) := by
      rw [Nat.cast_add, Nat.cast_mul]
      have : ((p ^ n : ℕ) : ZMod (p ^ n)) = 0 := ZMod.natCast_self (p ^ n)
      rw [this, mul_zero, zero_add]
    rw [this]
  have : ∑ q ∈ range c, ∑ ρ ∈ pfree p n,
      ((q * p ^ n + ρ : ℕ) : ZMod (p ^ n))⁻¹ =
      ∑ q ∈ range c, ∑ ρ ∈ pfree p n, (ρ : ZMod (p ^ n))⁻¹ := by
    refine Finset.sum_congr rfl ?_
    intro q hq
    exact Finset.sum_congr rfl (fun ρ hρ => hterm q hq ρ hρ)
  rw [this]
  simp [sum_pfree_inv_eq_zero hp (by omega) hn]

lemma inter_sum_inv_mod {p B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hB0 : 0 < B) :
    ∑ i ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
      ((p * i.2 - i.1 : ℕ) : ZMod (p ^ (padicValNat p B + 1)))⁻¹ = 0 := by
  set n := padicValNat p B + 1
  set c := B / p ^ padicValNat p B
  set s : Finset (ℕ × ℕ) := Icc 1 (p - 1) ×ˢ Icc 1 B
  have hn : 0 < n := Nat.succ_pos _
  have himg := pfreeBelow_eq_rectangle (p := p) (B := B) hp hB0
  have hinj : Set.InjOn (fun ij : ℕ × ℕ => p * ij.2 - ij.1) ↑s := by
    intro ij hij kl hkl heq
    exact rectangle_map_inj hp (by exact hij) (by exact hkl) heq
  have :
      ∑ t ∈ s.image (fun ij => p * ij.2 - ij.1), (t : ZMod (p ^ n))⁻¹ =
        ∑ i ∈ s, ((p * i.2 - i.1 : ℕ) : ZMod (p ^ n))⁻¹ :=
    Finset.sum_image hinj
  rw [← this, himg]
  have hdecomp := pB_decomp (p := p) (B := B) hp hB0
  have : pfreeBelow p (p * B) = pfreeBelow p (c * p ^ n) := by rw [hdecomp]
  rw [this]
  exact sum_pfreeBelow_inv hp hp5 hn

lemma inter_sum_invsq_mod {p B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hB0 : 0 < B) :
    ∑ i ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
      (((p * i.2 - i.1 : ℕ) : ZMod (p ^ (padicValNat p B + 1)))⁻¹) ^ 2 = 0 := by
  set n := padicValNat p B + 1
  set c := B / p ^ padicValNat p B
  set s : Finset (ℕ × ℕ) := Icc 1 (p - 1) ×ˢ Icc 1 B
  have hn : 0 < n := Nat.succ_pos _
  have himg := pfreeBelow_eq_rectangle (p := p) (B := B) hp hB0
  have hinj : Set.InjOn (fun ij : ℕ × ℕ => p * ij.2 - ij.1) ↑s := by
    intro ij hij kl hkl heq
    exact rectangle_map_inj hp (by exact hij) (by exact hkl) heq
  have :
      ∑ t ∈ s.image (fun ij => p * ij.2 - ij.1), ((t : ZMod (p ^ n))⁻¹) ^ 2 =
        ∑ i ∈ s, (((p * i.2 - i.1 : ℕ) : ZMod (p ^ n))⁻¹) ^ 2 :=
    Finset.sum_image hinj
  rw [← this, himg]
  have hdecomp := pB_decomp (p := p) (B := B) hp hB0
  have : pfreeBelow p (p * B) = pfreeBelow p (c * p ^ n) := by rw [hdecomp]
  rw [this]
  exact sum_pfreeBelow_inv_sq hp hp5 hn

lemma esym2_inter_mod {p B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hB0 : 0 < B) :
    ((esym2 (Icc 1 (p - 1) ×ˢ Icc 1 B)
        (fun ij => ((p * ij.2 - ij.1 : ℕ) : ℤ))) :
      ZMod (p ^ (padicValNat p B + 1))) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set n := padicValNat p B + 1
  set s : Finset (ℕ × ℕ) := Icc 1 (p - 1) ×ˢ Icc 1 B
  set x : ℕ × ℕ → ℤ := fun ij => ((p * ij.2 - ij.1 : ℕ) : ℤ)
  have hn : 0 < n := Nat.succ_pos _
  have hcast : (esym2 s x : ZMod (p ^ n)) =
      ∑ i ∈ s, ∑ j ∈ s.erase i,
        ∏ k ∈ (s.erase i).erase j, ((p * k.2 - k.1 : ℕ) : ZMod (p ^ n)) := by
    simp only [esym2, x, Int.cast_sum, Int.cast_prod, Int.cast_natCast]
  rw [hcast]
  have hterm : ∀ i ∈ s, ∀ j ∈ s.erase i,
      ∏ k ∈ (s.erase i).erase j, ((p * k.2 - k.1 : ℕ) : ZMod (p ^ n)) =
        (∏ k ∈ s, ((p * k.2 - k.1 : ℕ) : ZMod (p ^ n))) *
          ((p * i.2 - i.1 : ℕ) : ZMod (p ^ n))⁻¹ *
          ((p * j.2 - j.1 : ℕ) : ZMod (p ^ n))⁻¹ :=
    fun i hi j hj =>
      rectangle_inner_prod_B (p := p) (B := B) (n := n) hp hB0 hn rfl hi hj
  have hrew :
      ∑ i ∈ s, ∑ j ∈ s.erase i,
          ∏ k ∈ (s.erase i).erase j, ((p * k.2 - k.1 : ℕ) : ZMod (p ^ n)) =
        (∏ k ∈ s, ((p * k.2 - k.1 : ℕ) : ZMod (p ^ n))) *
          ∑ i ∈ s, ∑ j ∈ s.erase i,
            ((p * i.2 - i.1 : ℕ) : ZMod (p ^ n))⁻¹ *
              ((p * j.2 - j.1 : ℕ) : ZMod (p ^ n))⁻¹ := by
    rw [Finset.sum_congr rfl (fun i hi =>
      Finset.sum_congr rfl (fun j hj => hterm i hi j hj))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    ring
  rw [hrew]
  have hdouble :
      ∑ i ∈ s, ∑ j ∈ s.erase i,
          ((p * i.2 - i.1 : ℕ) : ZMod (p ^ n))⁻¹ *
            ((p * j.2 - j.1 : ℕ) : ZMod (p ^ n))⁻¹ =
        (∑ i ∈ s, ((p * i.2 - i.1 : ℕ) : ZMod (p ^ n))⁻¹) ^ 2 -
          ∑ i ∈ s, (((p * i.2 - i.1 : ℕ) : ZMod (p ^ n))⁻¹) ^ 2 := by
    set inv : ℕ × ℕ → ZMod (p ^ n) :=
      fun i => ((p * i.2 - i.1 : ℕ) : ZMod (p ^ n))⁻¹
    have hprod : (∑ i ∈ s, inv i) * (∑ j ∈ s, inv j) =
        ∑ i ∈ s, ∑ j ∈ s, inv i * inv j :=
      Finset.sum_mul_sum s s inv inv
    have hsq : (∑ i ∈ s, inv i) * (∑ j ∈ s, inv j) = (∑ i ∈ s, inv i) ^ 2 := by
      rw [pow_two]
    have hinter : ∀ i ∈ s,
        ∑ j ∈ s, inv i * inv j =
          ∑ j ∈ s.erase i, inv i * inv j + inv i * inv i :=
      fun i hi => (Finset.sum_erase_add s (fun j => inv i * inv j) hi).symm
    have hsum := Finset.sum_congr (rfl : s = s) hinter
    have hsplit :
        ∑ i ∈ s, ∑ j ∈ s, inv i * inv j =
          ∑ i ∈ s, ∑ j ∈ s.erase i, inv i * inv j +
            ∑ i ∈ s, inv i * inv i := by
      rw [hsum, Finset.sum_add_distrib]
    have hdiag : ∑ i ∈ s, inv i * inv i = ∑ i ∈ s, (inv i) ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro i hi; rw [pow_two]
    rw [← hsq, hprod, hsplit, hdiag]
    abel
  rw [hdouble, inter_sum_inv_mod hp hp5 hB0, inter_sum_invsq_mod hp hp5 hB0]
  ring

lemma esym2_inter_dvd {p B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hB0 : 0 < B) :
    (p : ℤ) ^ (padicValNat p B + 1) ∣
      esym2 (Icc 1 (p - 1) ×ˢ Icc 1 B)
        (fun ij => ((p * ij.2 - ij.1 : ℕ) : ℤ)) :=
  (CharP.intCast_eq_zero_iff (ZMod (p ^ (padicValNat p B + 1)))
      (p ^ (padicValNat p B + 1)) _).mp
    (esym2_inter_mod hp hp5 hB0)

lemma prod_add_pow_inter_cube {p r B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 2 ≤ r) (hB0 : 0 < B) :
    (p : ℤ) ^ min (r + 2 * (padicValNat p B + 1))
      (min (2 * r + (padicValNat p B + 1)) (3 * r)) ∣
      (∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
          (((p * ij.2 - ij.1 : ℕ) : ℤ) + (p : ℤ) ^ r)) -
        (∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
          ((p * ij.2 - ij.1 : ℕ) : ℤ)) := by
  set s : Finset (ℕ × ℕ) := Icc 1 (p - 1) ×ˢ Icc 1 B
  set x : ℕ × ℕ → ℤ := fun ij => ((p * ij.2 - ij.1 : ℕ) : ℤ)
  set n := padicValNat p B + 1
  set N : ℤ := (p : ℤ) ^ r
  have hexp := prod_add_const_mod_cube (s := s) (x := x) (N := N)
  have hcof := sum_cofactor_inter_dvd (p := p) (B := B) hp hp5 hB0
  have hσ2 := esym2_inter_dvd (p := p) (B := B) hp hp5 hB0
  have hN3 : N ^ 3 = (p : ℤ) ^ (3 * r) := by
    simp [N]; rw [← pow_mul, mul_comm]
  have hN2 : N ^ 2 = (p : ℤ) ^ (2 * r) := by
    simp [N]; rw [← pow_mul, mul_comm]
  obtain ⟨c1, hc1⟩ := hcof
  obtain ⟨c2, hc2⟩ := hσ2
  have hmid := (Int.modEq_iff_dvd).mp hexp
  obtain ⟨K, hK⟩ := hmid
  have hdecomp :
      2 * (∏ i ∈ s, (x i + N) - ∏ i ∈ s, x i) =
        2 * N * esym1 s x + N ^ 2 * esym2 s x - N ^ 3 * K := by
    have : 2 * (∏ i ∈ s, (x i + N) - ∏ i ∈ s, x i - N * esym1 s x) =
        N ^ 2 * esym2 s x - N ^ 3 * K := by
      linear_combination -hK
    linear_combination this
  have hesym1 : esym1 s x =
      ∑ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
        ∏ kl ∈ (Icc 1 (p - 1) ×ˢ Icc 1 B).erase ij,
          ((p * kl.2 - kl.1 : ℕ) : ℤ) := by
    simp [esym1, s, x]
  have hesym2 : esym2 s x =
      esym2 (Icc 1 (p - 1) ×ˢ Icc 1 B)
        (fun ij => ((p * ij.2 - ij.1 : ℕ) : ℤ)) := by
    simp [s, x]
  rw [hesym1, hc1, hesym2, hc2, hN2, hN3] at hdecomp
  have hN : N = (p : ℤ) ^ r := rfl
  have hn_eq : n = padicValNat p B + 1 := rfl
  have hdiff :
      2 * (∏ i ∈ s, (x i + N) - ∏ i ∈ s, x i) =
        2 * (p : ℤ) ^ (r + 2 * n) * c1 +
          (p : ℤ) ^ (2 * r + n) * c2 -
          (p : ℤ) ^ (3 * r) * K := by
    rw [hdecomp, hN, hn_eq]
    ring
  have h2div : (p : ℤ) ^ min (r + 2 * n) (min (2 * r + n) (3 * r)) ∣
      2 * (∏ i ∈ s, (x i + N) - ∏ i ∈ s, x i) := by
    rw [hdiff]
    have he : (p : ℤ) ^ min (r + 2 * n) (min (2 * r + n) (3 * r)) ∣
        (p : ℤ) ^ (r + 2 * n) := pow_dvd_pow _ (min_le_left _ _)
    have he2 : (p : ℤ) ^ min (r + 2 * n) (min (2 * r + n) (3 * r)) ∣
        (p : ℤ) ^ (2 * r + n) :=
      pow_dvd_pow _ (le_trans (min_le_right _ _) (min_le_left _ _))
    have he3 : (p : ℤ) ^ min (r + 2 * n) (min (2 * r + n) (3 * r)) ∣
        (p : ℤ) ^ (3 * r) :=
      pow_dvd_pow _ (le_trans (min_le_right _ _) (min_le_right _ _))
    refine dvd_sub (dvd_add ?_ ?_) ?_
    · convert dvd_mul_of_dvd_left he (2 * c1) using 1; ring
    · exact dvd_mul_of_dvd_left he2 _
    · exact dvd_mul_of_dvd_left he3 _
  haveI : Fact p.Prime := ⟨hp⟩
  set D := ∏ i ∈ s, (x i + N) - ∏ i ∈ s, x i
  set e := min (r + 2 * n) (min (2 * r + n) (3 * r))
  have hdiv : (p : ℤ) ^ e ∣ D := by
    by_cases hD0 : D = 0
    · simp [hD0]
    · have hne2 : (2 : ℤ) ≠ 0 := by decide
      have hge : e ≤ padicValInt p (2 * D) :=
        (padicValInt_dvd_iff (p := p) e (2 * D)).mp h2div |>.resolve_left
          (mul_ne_zero hne2 hD0)
      have h2val : padicValInt p (2 : ℤ) = 0 := by
        rw [padicValInt.eq_zero_of_not_dvd]
        intro hd
        have : (p : ℤ) ∣ 2 := hd
        have : p ∣ 2 := Int.ofNat_dvd.mp (by simpa using this)
        have hcases := (Nat.dvd_prime Nat.prime_two).mp this
        rcases hcases with h1 | h2'
        · exact hp.ne_one h1
        · omega
      have : e ≤ padicValInt p D := by
        have hmul := padicValInt.mul (p := p) hne2 hD0
        omega
      exact (padicValInt_dvd_iff (p := p) e D).mpr (Or.inr this)
  exact hdiv

lemma pow_dvd_delta_inter_strong {p r B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 2 ≤ r) (hB0 : 0 < B) (hB : B ≤ p ^ (r - 1)) :
    (p : ℤ) ^ (padicValInt p (risingY p r (p * B) : ℤ) +
      min (r + 2 * (padicValNat p B + 1))
        (min (2 * r + (padicValNat p B + 1)) (3 * r))) ∣
      (rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B) := by
  have hr1 : 1 ≤ r := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  have hid := rising_sub_mul_pProd (p := p) (r := r) (B := B) hp hr1 hB
  have hQP0 := prod_add_pow_inter_cube (p := p) (r := r) (B := B) hp hp5 hr hB0
  have hcastQ :
      ((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
          (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) =
        ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
          (((p * ij.2 - ij.1 : ℕ) : ℤ) + (p : ℤ) ^ r) := by
    simp [Nat.cast_prod, Nat.cast_add, Nat.cast_pow]
  have hcastP : (pProd p B : ℤ) =
      ∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B, ((p * ij.2 - ij.1 : ℕ) : ℤ) := by
    simp [pProd_eq_prod_product, Nat.cast_prod]
  set e := min (r + 2 * (padicValNat p B + 1))
    (min (2 * r + (padicValNat p B + 1)) (3 * r))
  have hQP : (p : ℤ) ^ e ∣
      ((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
          (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) - pProd p B := by
    rwa [hcastQ, hcastP]
  set y : ℤ := (risingY p r (p * B) : ℤ)
  set δ : ℤ := (rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B)
  set QP : ℤ :=
    ((∏ ij ∈ Icc 1 (p - 1) ×ˢ Icc 1 B,
        (p * ij.2 - ij.1 + p ^ r) : ℕ) : ℤ) - pProd p B
  have hid' : δ * (pProd p B : ℤ) = y * QP := hid
  have hPne : (pProd p B : ℤ) ≠ 0 := by
    exact_mod_cast (ne_zero_of_lt (pProd_pos (p := p) hp.pos))
  by_cases hy0 : y = 0
  · have : δ * (pProd p B : ℤ) = 0 := by rw [hid', hy0, zero_mul]
    have hδ0 : δ = 0 := (mul_eq_zero.mp this).resolve_right hPne
    simp [hδ0]
  · by_cases hδ0 : δ = 0
    · simp [hδ0]
    · have hQPne : QP ≠ 0 := by
        intro h
        have : δ * (pProd p B : ℤ) = 0 := by rw [hid', h, mul_zero]
        exact hδ0 ((mul_eq_zero.mp this).resolve_right hPne)
      have hP0 : padicValInt p (pProd p B : ℤ) = 0 := by
        rw [padicValInt.of_nat]
        exact padicValNat.eq_zero_of_not_dvd (p_not_dvd_pProd hp)
      have hδP : padicValInt p (δ * (pProd p B : ℤ)) = padicValInt p δ := by
        rw [padicValInt.mul (p := p) hδ0 hPne, hP0, add_zero]
      have hv : padicValInt p (δ * (pProd p B : ℤ)) =
          padicValInt p y + padicValInt p QP := by
        rw [hid']
        exact padicValInt.mul (p := p) hy0 hQPne
      have hQPge : e ≤ padicValInt p QP :=
        (padicValInt_dvd_iff (p := p) e QP).mp hQP |>.resolve_left hQPne
      have : padicValInt p y + e ≤ padicValInt p δ := by omega
      exact (padicValInt_dvd_iff (p := p) _ δ).mpr (Or.inr this)

lemma S1d_term_inter_dvd {p r B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 2 ≤ r) (hB0 : 0 < B) (hB : B < p ^ (r - 1)) :
    (p : ℤ) ^ (3 * r) ∣
      6 * (risingY p r (p * B) : ℤ) * ((risingY p r (p * B) : ℤ) + 1) *
        ((rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B)) := by
  have hr1 : 1 ≤ r := by omega
  have hBle : B ≤ p ^ (r - 1) := Nat.le_of_lt hB
  have hδ := pow_dvd_delta_inter_strong hp hp5 hr hB0 hBle
  haveI : Fact p.Prime := ⟨hp⟩
  have hy : padicValInt p (risingY p r (p * B) : ℤ) =
      (r - 1) - padicValNat p B :=
    padicValInt_risingY hp hr1 hB0 hBle
  rw [hy] at hδ
  set v := padicValNat p B
  set eδ := (r - 1) - v +
    min (r + 2 * (v + 1)) (min (2 * r + (v + 1)) (3 * r))
  have hvlt : v < r - 1 :=
    padicValNat_lt_of_lt_pow (p := p) (k := B) (r := r - 1) hB0 hB
  have hge : 3 * r ≤ ((r - 1) - v) + eδ := by
    have : 3 * r ≤ 2 * ((r - 1) - v) +
        min (r + 2 * (v + 1)) (min (2 * r + (v + 1)) (3 * r)) := by
      omega
    omega
  set y : ℤ := (risingY p r (p * B) : ℤ)
  set δ : ℤ := (rising (p ^ r) (p * B) : ℤ) - risingY p r (p * B)
  have hy' : padicValInt p y = (r - 1) - v := hy
  have hdivy : (p : ℤ) ^ ((r - 1) - v) ∣ y := by
    refine (padicValInt_dvd_iff (p := p) ((r - 1) - v) y).mpr (Or.inr ?_)
    rw [hy']
  obtain ⟨s, hs⟩ := hdivy
  obtain ⟨t, ht⟩ := hδ
  refine ⟨6 * s * (y + 1) * t * (p : ℤ) ^ (((r - 1) - v + eδ) - 3 * r), ?_⟩
  have hpow : (p : ℤ) ^ ((r - 1) - v) * (p : ℤ) ^ eδ =
      (p : ℤ) ^ (3 * r) * (p : ℤ) ^ (((r - 1) - v + eδ) - 3 * r) := by
    rw [← pow_add, ← pow_add, Nat.add_sub_of_le hge]
  calc
    6 * y * (y + 1) * δ =
        6 * ((p : ℤ) ^ ((r - 1) - v) * s) * (y + 1) *
          ((p : ℤ) ^ eδ * t) := by
      rw [hs, ht]
    _ = 6 * s * (y + 1) * t *
          ((p : ℤ) ^ ((r - 1) - v) * (p : ℤ) ^ eδ) := by ring
    _ = 6 * s * (y + 1) * t *
          ((p : ℤ) ^ (3 * r) *
            (p : ℤ) ^ (((r - 1) - v + eδ) - 3 * r)) := by
      rw [hpow]
    _ = (p : ℤ) ^ (3 * r) *
          (6 * s * (y + 1) * t *
            (p : ℤ) ^ (((r - 1) - v + eδ) - 3 * r)) := by ring

lemma S1d_dvd {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
    (p : ℤ) ^ (3 * r) ∣ S1d p r := by
  unfold S1d
  refine dvd_sum ?_
  intro k hk
  have ⟨hkR, hdv⟩ := mem_filter.mp hk
  have hkle : k ≤ p ^ r := Nat.lt_succ_iff.mp (mem_range.mp hkR)
  obtain ⟨B, hB⟩ := hdv
  have hr1 : 1 ≤ r := by omega
  have hBle : B ≤ p ^ (r - 1) := by
    have : p * B ≤ p * p ^ (r - 1) := by
      rw [← hB, prime_mul_pow_pred hr1]; exact hkle
    exact Nat.le_of_mul_le_mul_left this hp.pos
  subst hB
  rcases eq_or_lt_of_le hBle with hEq | hLt
  · have hB : B = p ^ (r - 1) := hEq
    simpa [hB] using S1d_term_last_dvd (p := p) (r := r) hp hp5 hr1
  · by_cases hB0 : B = 0
    · subst hB0
      simp [S1d_term_zero]
    · have hBpos : 0 < B := Nat.pos_of_ne_zero hB0
      by_cases hnd : p ∣ B
      · exact S1d_term_inter_dvd (p := p) (r := r) (B := B) hp hp5 hr hBpos hLt
      · exact S1d_term_pfreeB_dvd (p := p) (r := r) (B := B) hp hp5 hr
          hBpos hBle hnd


/-! ### Last `y` is `1` mod `p^3` via the `r = 1` last-term expansion -/

lemma risingY_one_p {p : ℕ} (hp : p.Prime) :
    risingY p 1 p = 1 := by
  rw [risingY_of_dvd dvd_rfl, Nat.div_self hp.pos]
  simp [rising]

lemma last_y_r2_eq {p : ℕ} (hp : p.Prime) :
    risingY p 2 (p * p) = rising p p := by
  rw [risingY_of_dvd (dvd_mul_right p p), Nat.mul_div_cancel_left p hp.pos]
  simp [rising]

lemma last_y_r2_mod {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (risingY p 2 (p * p) : ℤ) ≡ 1 [ZMOD (p : ℤ) ^ 3] := by
  have h := pow_dvd_delta_last_strong (p := p) (r := 1) hp hp5 le_rfl
  have hy1 := risingY_one_p hp
  have : (p : ℤ) ^ 3 ∣ (rising p p : ℤ) - 1 := by
    simpa [pow_one, Nat.mul_one, hy1] using h
  have hy2 := last_y_r2_eq hp
  refine (Int.modEq_iff_dvd).mpr ?_
  simpa [hy2, neg_sub] using (dvd_neg.mpr this)





lemma last_y_eq_rising {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    risingY p r (p * p ^ (r - 1)) = rising (p ^ (r - 1)) (p ^ (r - 1)) := by
  rw [risingY_of_dvd (dvd_mul_right p _)]
  simp [Nat.mul_div_cancel_left _ hp.pos]

lemma last_y_succ_mod {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
    (risingY p r (p * p ^ (r - 1)) : ℤ) ≡
      (risingY p (r - 1) (p * p ^ (r - 2)) : ℤ)
      [ZMOD (p : ℤ) ^ (3 * (r - 1))] := by
  have hr1 : 1 ≤ r - 1 := by omega
  have h := pow_dvd_delta_last_strong (p := p) (r := r - 1) hp hp5 hr1
  have hy : risingY p r (p * p ^ (r - 1)) =
      rising (p ^ (r - 1)) (p * p ^ (r - 2)) := by
    rw [last_y_eq_rising hp (by omega : 1 ≤ r)]
    have : p ^ (r - 1) = p * p ^ (r - 2) := by
      have : r - 1 = (r - 2) + 1 := by omega
      rw [this, pow_succ, mul_comm]
    rw [this]
  have hexp : (r - 1) - 1 = r - 2 := by omega
  refine (Int.modEq_iff_dvd).mpr ?_
  have : (rising (p ^ (r - 1)) (p * p ^ ((r - 1) - 1)) : ℤ) -
      risingY p (r - 1) (p * p ^ ((r - 1) - 1)) =
      (risingY p r (p * p ^ (r - 1)) : ℤ) -
        risingY p (r - 1) (p * p ^ (r - 2)) := by
    simp [hy, hexp]
  simpa [this, neg_sub] using (dvd_neg.mpr h)

lemma last_y_mod_cube {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
    (risingY p r (p * p ^ (r - 1)) : ℤ) ≡ 1 [ZMOD (p : ℤ) ^ 3] := by
  induction r, hr using Nat.le_induction with
  | base =>
    have : p * p ^ (2 - 1) = p * p := by simp
    simpa [this] using last_y_r2_mod hp hp5
  | succ n hn ih =>
    have hstep := last_y_succ_mod (p := p) (r := n + 1) hp hp5 (Nat.le_succ_of_le hn)
    have hle : 3 ≤ 3 * n := by omega
    have hcast : (p : ℤ) ^ 3 ∣ (p : ℤ) ^ (3 * n) := pow_dvd_pow _ hle
    have hcongr : (risingY p (n + 1) (p * p ^ n) : ℤ) ≡
        (risingY p n (p * p ^ (n - 1)) : ℤ) [ZMOD (p : ℤ) ^ 3] := by
      have hstep' : (risingY p (n + 1) (p * p ^ n) : ℤ) ≡
          (risingY p n (p * p ^ (n - 1)) : ℤ)
          [ZMOD (p : ℤ) ^ (3 * n)] := by
        convert hstep using 4 <;> omega
      exact Int.ModEq.of_dvd hcast hstep'
    exact hcongr.trans ih





/-! ### Pairing binomials modulo `p^2` -/

lemma rising_self (n : ℕ) : rising n n = choose (2 * n - 1) n := by
  unfold rising
  cases n with
  | zero => simp
  | succ n =>
    simp [Nat.succ_eq_add_one]
    congr 1
    omega

lemma choose_2nm1_symm {n : ℕ} (hn : 1 ≤ n) :
    choose (2 * n - 1) n = choose (2 * n - 1) (n - 1) := by
  have hle : n ≤ 2 * n - 1 := by omega
  rw [← choose_symm hle]
  congr 1
  omega

lemma last_rising_eq_central {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    rising (p ^ r) (p ^ r) = choose (2 * p ^ r - 1) (p ^ r - 1) := by
  have hn : 1 ≤ p ^ r := Nat.one_le_pow r p hp.pos
  rw [rising_self, choose_2nm1_symm hn]

lemma last_rising_mod_cube {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) :
    (rising (p ^ r) (p ^ r) : ℤ) ≡ 1 [ZMOD (p : ℤ) ^ 3] := by
  have h := last_y_mod_cube (p := p) (r := r + 1) hp hp5 (by omega)
  have heq : risingY p (r + 1) (p * p ^ r) = rising (p ^ r) (p ^ r) := by
    simpa [Nat.add_sub_cancel] using
      last_y_eq_rising (p := p) (r := r + 1) hp (by omega : 1 ≤ r + 1)
  simpa [heq] using h

lemma last_rising_mod_sq {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) :
    (rising (p ^ r) (p ^ r) : ℤ) ≡ 1 [ZMOD (p : ℤ) ^ 2] := by
  have h := last_rising_mod_cube hp hp5 hr
  exact Int.ModEq.of_dvd (pow_dvd_pow _ (by omega : 2 ≤ 3)) h

lemma choose_2n_pred_mul {n : ℕ} (hn : 2 ≤ n) :
    (2 * n - 1) * choose (2 * n - 2) (n - 2) =
      choose (2 * n - 1) (n - 1) * (n - 1) := by
  have h := add_one_mul_choose_eq (2 * n - 2) (n - 2)
  have h1 : 2 * n - 2 + 1 = 2 * n - 1 := by omega
  have h2 : n - 2 + 1 = n - 1 := by omega
  simpa [h1, h2] using h

lemma pair_base_mod_sq {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
    (choose (2 * p ^ r - 2) (p ^ r - 2) : ℤ) ≡ 1 [ZMOD (p : ℤ) ^ 2] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hn : 2 ≤ p ^ r := by
    have hpow : 1 ≤ p ^ (r - 1) := Nat.one_le_pow (r - 1) p hp.pos
    have hle : p ≤ p * p ^ (r - 1) := Nat.le_mul_of_pos_right p hpow
    have : p ≤ p ^ r := by rwa [prime_mul_pow_pred (by omega : 1 ≤ r)] at hle
    omega
  have hid := choose_2n_pred_mul hn
  have hC : choose (2 * p ^ r - 1) (p ^ r - 1) = rising (p ^ r) (p ^ r) :=
    (last_rising_eq_central hp (by omega)).symm
  have hrising := last_rising_mod_cube hp hp5 (by omega : 1 ≤ r)
  have hmul :
      ((2 * p ^ r - 1 : ℕ) : ℤ) * (choose (2 * p ^ r - 2) (p ^ r - 2) : ℤ) =
        (rising (p ^ r) (p ^ r) : ℤ) * ((p ^ r - 1 : ℕ) : ℤ) := by
    exact_mod_cast (by simpa [hC] using hid)
  set N : ℤ := (p : ℤ) ^ r
  set B1 : ℤ := (choose (2 * p ^ r - 2) (p ^ r - 2) : ℤ)
  set R : ℤ := (rising (p ^ r) (p ^ r) : ℤ)
  have h2N : ((2 * p ^ r - 1 : ℕ) : ℤ) = 2 * N - 1 := by
    have : 1 ≤ 2 * p ^ r := by omega
    have : ((2 * p ^ r - 1 : ℕ) : ℤ) = (2 * p ^ r : ℕ) - 1 :=
      Nat.cast_sub this
    simpa [N, Nat.cast_mul, Nat.cast_pow] using this
  have hN1 : ((p ^ r - 1 : ℕ) : ℤ) = N - 1 := by
    have : 1 ≤ p ^ r := Nat.one_le_pow r p hp.pos
    simpa [N, Nat.cast_pow] using Nat.cast_sub this
  have hmul' : (2 * N - 1) * B1 = R * (N - 1) := by
    simpa [h2N, hN1] using hmul
  have hdiff : (2 * N - 1) * (B1 - 1) = (R - 1) * (N - 1) - N := by
    linear_combination hmul'
  have hR1 : (p : ℤ) ^ 3 ∣ R - 1 := by
    simpa [R, neg_sub] using (dvd_neg.mpr ((Int.modEq_iff_dvd).mp hrising))
  have hNpow : (p : ℤ) ^ 2 ∣ N := pow_dvd_pow _ (by omega : 2 ≤ r)
  have hRHS : (p : ℤ) ^ 2 ∣ (R - 1) * (N - 1) - N := by
    have h1 : (p : ℤ) ^ 2 ∣ (R - 1) * (N - 1) :=
      dvd_mul_of_dvd_left (dvd_trans (pow_dvd_pow _ (by omega : 2 ≤ 3)) hR1) _
    exact dvd_sub h1 hNpow
  rw [← hdiff] at hRHS
  by_cases hB : B1 - 1 = 0
  · have : B1 = 1 := sub_eq_zero.mp hB
    simp [this]
  · have h2Nne : (2 * N - 1) ≠ 0 := by
      intro hz
      have : (2 * p ^ r - 1 : ℕ) = 0 := by
        have := congrArg Int.natAbs (by simpa [h2N] using hz)
        have hpos : 0 < 2 * p ^ r - 1 := by omega
        simp [Int.natAbs_eq_zero] at this
        omega
      omega
    have hge : 2 ≤ padicValInt p ((2 * N - 1) * (B1 - 1)) :=
      (padicValInt_dvd_iff (p := p) 2 _).mp hRHS |>.resolve_left
        (mul_ne_zero h2Nne hB)
    have h2Nval : padicValInt p (2 * N - 1) = 0 := by
      rw [padicValInt.eq_zero_of_not_dvd]
      intro hd
      have hcast : (p : ℤ) ∣ ((2 * p ^ r - 1 : ℕ) : ℤ) := by
        simpa [h2N] using hd
      have : p ∣ 2 * p ^ r - 1 := Int.ofNat_dvd.mp (by simpa using hcast)
      have hpr : p ∣ 2 * p ^ r :=
        dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) _
      have : p ∣ 1 := by
        have hsub := Nat.dvd_sub hpr this
        have heq : 2 * p ^ r - (2 * p ^ r - 1) = 1 := by omega
        rwa [heq] at hsub
      exact hp.ne_one (Nat.dvd_one.mp this)
    have : 2 ≤ padicValInt p (B1 - 1) := by
      have hmulv := padicValInt.mul (p := p) h2Nne hB
      omega
    have : (p : ℤ) ^ 2 ∣ B1 - 1 :=
      (padicValInt_dvd_iff (p := p) 2 (B1 - 1)).mpr (Or.inr this)
    refine (Int.modEq_iff_dvd).mpr ?_
    simpa [B1, neg_sub] using (dvd_neg.mpr this)




lemma pairA_succ (N j : ℕ) (hj : 0 < j) :
    choose (N + j) j * j = choose (N + j - 1) (j - 1) * (N + j) := by
  have h := add_one_mul_choose_eq (N + j - 1) (j - 1)
  have h1 : N + j - 1 + 1 = N + j := by omega
  have h2 : j - 1 + 1 = j := by omega
  simpa [h1, h2, mul_comm] using h.symm

lemma pairB_succ (N j : ℕ) (hj : j + 1 < N) :
    choose (2 * N - (j + 2)) (N - (j + 2)) * (2 * N - (j + 1)) =
      choose (2 * N - (j + 1)) (N - (j + 1)) * (N - (j + 1)) := by
  have hN : 2 ≤ N := by omega
  have h := add_one_mul_choose_eq (2 * N - (j + 2)) (N - (j + 2))
  have h1 : 2 * N - (j + 2) + 1 = 2 * N - (j + 1) := by omega
  have h2 : N - (j + 2) + 1 = N - (j + 1) := by omega
  rw [h1, h2, mul_comm] at h
  exact h

lemma pairA_succ_int (N j : ℕ) (hj : 0 < j) :
    (choose (N + j) j : ℤ) * (j : ℤ) =
      (choose (N + j - 1) (j - 1) : ℤ) * ((N + j : ℕ) : ℤ) := by
  exact_mod_cast pairA_succ N j hj

lemma pairB_succ_int (N j : ℕ) (hj : j + 1 < N) :
    (choose (2 * N - (j + 2)) (N - (j + 2)) : ℤ) *
        ((2 * N - (j + 1) : ℕ) : ℤ) =
      (choose (2 * N - (j + 1)) (N - (j + 1)) : ℤ) *
        ((N - (j + 1) : ℕ) : ℤ) := by
  exact_mod_cast pairB_succ N j hj

lemma cancel_unit_mod_sq {p : ℕ} [Fact p.Prime] {a b u : ℤ}
    (hu : ¬ (p : ℤ) ∣ u) (h : (p : ℤ) ^ 2 ∣ (a - b) * u) :
    (p : ℤ) ^ 2 ∣ a - b := by
  by_cases hab : a - b = 0
  · simp [hab]
  · by_cases hu0 : u = 0
    · exact (hu (by simp [hu0])).elim
    · have hge : 2 ≤ padicValInt p ((a - b) * u) :=
        (padicValInt_dvd_iff (p := p) 2 _).mp h |>.resolve_left
          (mul_ne_zero hab hu0)
      have huval : padicValInt p u = 0 := padicValInt.eq_zero_of_not_dvd hu
      have : 2 ≤ padicValInt p (a - b) := by
        have hmul := padicValInt.mul (p := p) hab hu0
        omega
      exact (padicValInt_dvd_iff (p := p) 2 (a - b)).mpr (Or.inr this)

/-- Single good step along p-free indices. -/
lemma pair_step_mod_sq {p r j : ℕ} (hp : p.Prime) (hr : 2 ≤ r)
    (hj0 : 0 < j) (hjN : j + 1 < p ^ r) (hndj : ¬ p ∣ j) (hndj1 : ¬ p ∣ (j + 1)) :
    (choose (p ^ r + j - 1) (j - 1) : ℤ) ≡
        (choose (2 * p ^ r - (j + 1)) (p ^ r - (j + 1)) : ℤ) [ZMOD (p : ℤ) ^ 2] →
      (choose (p ^ r + j) j : ℤ) ≡
        (choose (2 * p ^ r - (j + 2)) (p ^ r - (j + 2)) : ℤ)
        [ZMOD (p : ℤ) ^ 2] := by
  intro ih
  haveI : Fact p.Prime := ⟨hp⟩
  set N : ℕ := p ^ r
  have hN0 : (p : ℤ) ^ 2 ∣ (N : ℤ) := by
    simp [N]; exact pow_dvd_pow _ (by omega : 2 ≤ r)
  have hA := pairA_succ_int N j hj0
  have hB := pairB_succ_int N j hjN
  have hNj : (p : ℤ) ^ 2 ∣ ((N + j : ℕ) : ℤ) - (j : ℤ) := by
    have : ((N + j : ℕ) : ℤ) - (j : ℤ) = (N : ℤ) := by simp
    simpa [this] using hN0
  have hAdiff : (p : ℤ) ^ 2 ∣
      ((choose (N + j) j : ℤ) - choose (N + j - 1) (j - 1)) * (j : ℤ) := by
    have hex :
        ((choose (N + j) j : ℤ) - choose (N + j - 1) (j - 1)) * (j : ℤ) =
          (choose (N + j - 1) (j - 1) : ℤ) * (((N + j : ℕ) : ℤ) - (j : ℤ)) := by
      linear_combination hA
    rw [hex]
    exact dvd_mul_of_dvd_right hNj _
  have hAstep : (p : ℤ) ^ 2 ∣
      (choose (N + j) j : ℤ) - choose (N + j - 1) (j - 1) := by
    refine cancel_unit_mod_sq (u := (j : ℤ)) ?_ hAdiff
    intro hd
    exact hndj (Int.ofNat_dvd.mp (by simpa using hd))
  have hmulL : ((2 * N - (j + 1) : ℕ) : ℤ) ≡ ((N - (j + 1) : ℕ) : ℤ)
      [ZMOD (p : ℤ) ^ 2] := by
    refine (Int.modEq_iff_dvd).mpr ?_
    have hsub : ((N - (j + 1) : ℕ) : ℤ) - ((2 * N - (j + 1) : ℕ) : ℤ) =
        - (N : ℤ) := by
      have hge : N - (j + 1) ≤ 2 * N - (j + 1) := by omega
      have : (2 * N - (j + 1)) - (N - (j + 1)) = N := by omega
      have : ((2 * N - (j + 1) : ℕ) : ℤ) - ((N - (j + 1) : ℕ) : ℤ) = (N : ℤ) := by
        rw [← Nat.cast_sub hge]; exact_mod_cast this
      linarith
    simpa [hsub] using (dvd_neg.mpr hN0)
  have hBdiff : (p : ℤ) ^ 2 ∣
      ((choose (2 * N - (j + 2)) (N - (j + 2)) : ℤ) -
        choose (2 * N - (j + 1)) (N - (j + 1))) *
        ((2 * N - (j + 1) : ℕ) : ℤ) := by
    have hL := (Int.modEq_iff_dvd).mp hmulL
    have hex :
        ((choose (2 * N - (j + 2)) (N - (j + 2)) : ℤ) -
            choose (2 * N - (j + 1)) (N - (j + 1))) *
          ((2 * N - (j + 1) : ℕ) : ℤ) =
          (choose (2 * N - (j + 1)) (N - (j + 1)) : ℤ) *
            (((N - (j + 1) : ℕ) : ℤ) - ((2 * N - (j + 1) : ℕ) : ℤ)) := by
      linear_combination hB
    rw [hex]
    exact dvd_mul_of_dvd_right hL _
  have hBstep : (p : ℤ) ^ 2 ∣
      (choose (2 * N - (j + 2)) (N - (j + 2)) : ℤ) -
        choose (2 * N - (j + 1)) (N - (j + 1)) := by
    refine cancel_unit_mod_sq (u := ((2 * N - (j + 1) : ℕ) : ℤ)) ?_ hBdiff
    intro hd
    have : p ∣ 2 * N - (j + 1) := Int.ofNat_dvd.mp (by simpa using hd)
    have : p ∣ j + 1 := by
      have h2N : p ∣ 2 * N :=
        dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) _
      have hsub := Nat.dvd_sub h2N this
      have heq : 2 * N - (2 * N - (j + 1)) = j + 1 := by omega
      rwa [heq] at hsub
    exact hndj1 this
  have hAj : (choose (N + j) j : ℤ) ≡
      (choose (N + j - 1) (j - 1) : ℤ) [ZMOD (p : ℤ) ^ 2] :=
    (Int.modEq_iff_dvd).mpr (by simpa [neg_sub] using (dvd_neg.mpr hAstep))
  have hBj : (choose (2 * N - (j + 2)) (N - (j + 2)) : ℤ) ≡
      (choose (2 * N - (j + 1)) (N - (j + 1)) : ℤ) [ZMOD (p : ℤ) ^ 2] :=
    (Int.modEq_iff_dvd).mpr (by simpa [neg_sub] using (dvd_neg.mpr hBstep))
  have hrewA : N + j - 1 = p ^ r + j - 1 := by simp [N]
  have hrewB0 : 2 * N - (j + 1) = 2 * p ^ r - (j + 1) := by simp [N]
  have hrewB1 : N - (j + 1) = p ^ r - (j + 1) := by simp [N]
  have ih' : (choose (N + j - 1) (j - 1) : ℤ) ≡
      (choose (2 * N - (j + 1)) (N - (j + 1)) : ℤ) [ZMOD (p : ℤ) ^ 2] := by
    simpa [hrewA, hrewB0, hrewB1] using ih
  have hfinal : (choose (N + j) j : ℤ) ≡
      (choose (2 * N - (j + 2)) (N - (j + 2)) : ℤ) [ZMOD (p : ℤ) ^ 2] :=
    hAj.trans (ih'.trans hBj.symm)
  simpa [N] using hfinal





lemma pair_cross_id (N m : ℤ) :
    (N + m) * (N + m - 1) * ((2 * N - m) * (2 * N - m - 1)) -
      (m * (m - 1)) * ((N - m) * (N - m - 1)) =
      2 * N * (2 * N - 1) * (N * (N + m - 1) - m ^ 2) := by
  ring

lemma pairA_two_step (N m : ℕ) (hm : 2 ≤ m) :
    choose (N + m) m * (m * (m - 1)) =
      choose (N + m - 2) (m - 2) * ((N + m) * (N + m - 1)) := by
  have h1 := pairA_succ N m (by omega)
  have h0 := pairA_succ N (m - 1) (by omega)
  have h0' : choose (N + m - 1) (m - 1) * (m - 1) =
      choose (N + m - 2) (m - 2) * (N + m - 1) := by
    have he1 : N + (m - 1) = N + m - 1 := by omega
    have he2 : N + (m - 1) - 1 = N + m - 2 := by omega
    have he3 : m - 1 - 1 = m - 2 := by omega
    simpa [he1, he2, he3] using h0
  calc
    choose (N + m) m * (m * (m - 1)) =
        (choose (N + m) m * m) * (m - 1) := by ring
    _ = (choose (N + m - 1) (m - 1) * (N + m)) * (m - 1) := by rw [h1]
    _ = (choose (N + m - 1) (m - 1) * (m - 1)) * (N + m) := by ring
    _ = (choose (N + m - 2) (m - 2) * (N + m - 1)) * (N + m) := by rw [h0']
    _ = choose (N + m - 2) (m - 2) * ((N + m) * (N + m - 1)) := by ring


lemma pairB_two_step (N m : ℕ) (hm : 2 ≤ m) (hmN : m + 1 < N) :
    choose (2 * N - (m + 2)) (N - (m + 2)) *
        ((2 * N - (m + 1)) * (2 * N - m)) =
      choose (2 * N - m) (N - m) * ((N - (m + 1)) * (N - m)) := by
  have h1 := pairB_succ N m (by omega)
  have h0 := pairB_succ N (m - 1) (by omega)
  have heq : m - 1 + 1 = m := by omega
  have heq2 : m - 1 + 2 = m + 1 := by omega
  rw [heq, heq2] at h0
  calc
    choose (2 * N - (m + 2)) (N - (m + 2)) *
        ((2 * N - (m + 1)) * (2 * N - m)) =
      (choose (2 * N - (m + 2)) (N - (m + 2)) * (2 * N - (m + 1))) *
        (2 * N - m) := by ring
    _ = (choose (2 * N - (m + 1)) (N - (m + 1)) * (N - (m + 1))) *
          (2 * N - m) := by rw [h1]
    _ = (choose (2 * N - (m + 1)) (N - (m + 1)) * (2 * N - m)) *
          (N - (m + 1)) := by ring
    _ = (choose (2 * N - m) (N - m) * (N - m)) * (N - (m + 1)) := by rw [h0]
    _ = choose (2 * N - m) (N - m) * ((N - (m + 1)) * (N - m)) := by ring

lemma pair_double_step {p r m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 2 ≤ r)
    (hm : 2 ≤ m) (hmN : m + 1 < p ^ r) (hdv : p ∣ m) :
    (choose (p ^ r + m - 2) (m - 2) : ℤ) ≡
        (choose (2 * p ^ r - m) (p ^ r - m) : ℤ) [ZMOD (p : ℤ) ^ 2] →
      (choose (p ^ r + m) m : ℤ) ≡
        (choose (2 * p ^ r - (m + 2)) (p ^ r - (m + 2)) : ℤ) [ZMOD (p : ℤ) ^ 2] := by
  intro ih
  haveI : Fact p.Prime := ⟨hp⟩
  set N : ℕ := p ^ r
  have hN0 : (p : ℤ) ^ 2 ∣ (N : ℤ) := by
    simp [N]; exact pow_dvd_pow _ (by omega : 2 ≤ r)
  have hA := pairA_two_step N m hm
  have hB := pairB_two_step N m hm (by omega)
  set A1 : ℤ := (choose (N + m) m : ℤ)
  set A0 : ℤ := (choose (N + m - 2) (m - 2) : ℤ)
  set B1 : ℤ := (choose (2 * N - (m + 2)) (N - (m + 2)) : ℤ)
  set B0 : ℤ := (choose (2 * N - m) (N - m) : ℤ)
  set P : ℤ := ((N + m : ℕ) : ℤ) * ((N + m - 1 : ℕ) : ℤ)
  set Q : ℤ := (m : ℤ) * ((m - 1 : ℕ) : ℤ)
  set R : ℤ := ((N - (m + 1) : ℕ) : ℤ) * ((N - m : ℕ) : ℤ)
  set S : ℤ := ((2 * N - (m + 1) : ℕ) : ℤ) * ((2 * N - m : ℕ) : ℤ)
  have hA' : A1 * Q = A0 * P := by
    have := congrArg (fun x : ℕ => (x : ℤ)) hA
    push_cast at this
    simpa [A1, A0, P, Q] using this
  have hB' : B1 * S = B0 * R := by
    have := congrArg (fun x : ℕ => (x : ℤ)) hB
    push_cast at this
    simpa [B1, B0, S, R] using this
  have hih : (p : ℤ) ^ 2 ∣ A0 - B0 := by
    have : A0 ≡ B0 [ZMOD (p : ℤ) ^ 2] := by
      simpa [A0, B0, N] using ih
    simpa [neg_sub] using (dvd_neg.mpr ((Int.modEq_iff_dvd).mp this))
  have hcomb : (A1 - B1) * Q * S = A0 * (P * S - Q * R) + (A0 - B0) * Q * R := by
    linear_combination hA' * S - hB' * Q
  -- Evaluate P*S - Q*R via the polynomial identity
  have hPS :
      P * S - Q * R =
        2 * (N : ℤ) * (2 * (N : ℤ) - 1) *
          ((N : ℤ) * ((N : ℤ) + (m : ℤ) - 1) - (m : ℤ) ^ 2) := by
    have hid := pair_cross_id (N : ℤ) (m : ℤ)
    -- identify integer casts of Nat subtractions
    have hNm : ((N + m : ℕ) : ℤ) = (N : ℤ) + m := by simp
    have hNm1 : ((N + m - 1 : ℕ) : ℤ) = (N : ℤ) + m - 1 := by
      have : 1 ≤ N + m := by omega
      simp [Nat.cast_sub this]
    have hm1 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by
      have : 1 ≤ m := by omega
      simp [Nat.cast_sub this]
    have hNmm : ((N - m : ℕ) : ℤ) = (N : ℤ) - m := by
      have : m ≤ N := by omega
      simp [Nat.cast_sub this]
    have hNm1' : ((N - (m + 1) : ℕ) : ℤ) = (N : ℤ) - m - 1 := by
      have : m + 1 ≤ N := by omega
      simp [Nat.cast_sub this]; ring
    have h2Nm : ((2 * N - m : ℕ) : ℤ) = 2 * (N : ℤ) - m := by
      have : m ≤ 2 * N := by omega
      simp [Nat.cast_sub this]
    have h2Nm1 : ((2 * N - (m + 1) : ℕ) : ℤ) = 2 * (N : ℤ) - m - 1 := by
      have : m + 1 ≤ 2 * N := by omega
      simp [Nat.cast_sub this]; ring
    simp only [P, Q, R, S, hNm, hNm1, hm1, hNmm, hNm1', h2Nm, h2Nm1]
    convert hid using 1 <;> ring
  -- Valuation of the right-hand side is at least 2 + v(Q) + v(S) = 2 + 2 v(m)
  have hQne : Q ≠ 0 := by
    have : (m : ℤ) ≠ 0 := by exact_mod_cast (ne_zero_of_lt (by omega : 0 < m))
    have : ((m - 1 : ℕ) : ℤ) ≠ 0 := by
      have : 1 < m := by omega
      exact_mod_cast Nat.sub_ne_zero_iff_lt.mpr this
    exact mul_ne_zero ‹_› ‹_›
  have hSne : S ≠ 0 := by
    have hpos1 : 0 < 2 * N - (m + 1) := by omega
    have hpos2 : 0 < 2 * N - m := by omega
    have : ((2 * N - (m + 1) : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hpos1.ne'
    have : ((2 * N - m : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hpos2.ne'
    exact mul_ne_zero ‹_› ‹_›
  by_cases hAB : A1 - B1 = 0
  · have : A1 = B1 := sub_eq_zero.mp hAB
    simpa [A1, B1, N, this]
  · -- p^2 | (A1-B1) iff v(A1-B1) ≥ 2
    have hRne : (P * S - Q * R) = 2 * (N : ℤ) * (2 * (N : ℤ) - 1) *
        ((N : ℤ) * ((N : ℤ) + m - 1) - (m : ℤ) ^ 2) := hPS
    have h2N1 : ¬ (p : ℤ) ∣ (2 * (N : ℤ) - 1) := by
      intro hd
      have : p ∣ 2 * N - 1 := by
        have hcast : (2 * (N : ℤ) - 1) = ((2 * N - 1 : ℕ) : ℤ) := by
          have : 1 ≤ 2 * N := by omega
          simp [N, Nat.cast_sub this]
        exact Int.ofNat_dvd.mp (by simpa [hcast] using hd)
      have h2N : p ∣ 2 * N :=
        dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) _
      have hsub := Nat.dvd_sub h2N this
      have heq : 2 * N - (2 * N - 1) = 1 := by omega
      rw [heq] at hsub
      exact hp.ne_one (Nat.dvd_one.mp hsub)
    -- v(N) ≥ 2, so v(PS-QR) ≥ 2; also v(A0-B0) ≥ 2 so both terms on RHS have val ≥ 2 + v(Q)+v(R or 0)
    -- Directly: p^2 | N so p^2 | (PS-QR) (since 2, 2N-1, ... are integers)
    have hPSdiv : (p : ℤ) ^ 2 ∣ P * S - Q * R := by
      rw [hRne]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right hN0 _) _) _
    have hRHS : (p : ℤ) ^ 2 ∣ A0 * (P * S - Q * R) + (A0 - B0) * Q * R :=
      dvd_add (dvd_mul_of_dvd_right hPSdiv _)
        (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hih _) _)
    -- So p^2 | (A1-B1)*Q*S. Need to cancel Q*S.
    -- Q = m(m-1) has v = v(m) ≥ 1, S has v = v(m), so we lose precision!
    -- Need extra valuation on RHS.
    -- Use padicValInt more carefully.
    have hvN : 2 ≤ padicValInt p (N : ℤ) := by
      have : (p : ℤ) ^ 2 ∣ (N : ℤ) := hN0
      have hNne : (N : ℤ) ≠ 0 := by
        exact_mod_cast pow_ne_zero r hp.ne_zero
      exact (padicValInt_dvd_iff (p := p) 2 (N : ℤ)).mp this |>.resolve_left hNne
    have hvm : 1 ≤ padicValInt p (m : ℤ) := by
      have hmne : (m : ℤ) ≠ 0 := by exact_mod_cast (ne_zero_of_lt (by omega : 0 < m))
      have : (p : ℤ) ∣ (m : ℤ) := Int.ofNat_dvd.mpr hdv
      have := (padicValInt_dvd_iff (p := p) 1 (m : ℤ)).mp
        (by simpa using this)
      exact this.resolve_left hmne
    -- v(Q) = v(m) since v(m-1)=0
    have hm1nd : ¬ (p : ℤ) ∣ ((m - 1 : ℕ) : ℤ) := by
      intro hd
      have : p ∣ m - 1 := Int.ofNat_dvd.mp (by simpa using hd)
      have : p ∣ 1 := by
        have hsub := Nat.dvd_sub hdv this
        have : m - (m - 1) = 1 := by omega
        rwa [this] at hsub
      exact hp.ne_one (Nat.dvd_one.mp this)
    have hvQ : padicValInt p Q = padicValInt p (m : ℤ) := by
      have hmne : (m : ℤ) ≠ 0 := by exact_mod_cast (ne_zero_of_lt (by omega : 0 < m))
      have hm1ne : ((m - 1 : ℕ) : ℤ) ≠ 0 := by
        exact_mod_cast (Nat.sub_ne_zero_iff_lt.mpr (by omega : 1 < m))
      rw [padicValInt.mul hmne hm1ne, padicValInt.eq_zero_of_not_dvd hm1nd, add_zero]
    -- v(S) = v(2N-m) = v(m) since v(2N)=r > v(m) (m < p^r)
    have hvm_lt : padicValInt p (m : ℤ) < r := by
      have : m < p ^ r := by omega
      have := padicValNat_lt_of_lt_pow (p := p) (k := m) (r := r)
        (by omega) this
      simpa [padicValInt.of_nat] using this
    -- v(2N-m) = v(m): 2N-m = 2 p^r - m
    have hvS : padicValInt p S = padicValInt p (m : ℤ) := by
      have hpos2 : 0 < 2 * N - m := by omega
      have h2Nm_ne : ((2 * N - m : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hpos2.ne'
      have h2Nm1_nd : ¬ (p : ℤ) ∣ ((2 * N - (m + 1) : ℕ) : ℤ) := by
        intro hd
        have : p ∣ 2 * N - (m + 1) := Int.ofNat_dvd.mp (by simpa using hd)
        have h2N : p ∣ 2 * N :=
          dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) _
        have hsub := Nat.dvd_sub h2N this
        have heq : 2 * N - (2 * N - (m + 1)) = m + 1 := by omega
        rw [heq] at hsub
        have : p ∣ 1 := by
          have : p ∣ m + 1 - m := Nat.dvd_sub hsub hdv
          simpa using this
        exact hp.ne_one (Nat.dvd_one.mp this)
      have hpos1 : 0 < 2 * N - (m + 1) := by omega
      have h2Nm1_ne : ((2 * N - (m + 1) : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hpos1.ne'
      have hmne : (m : ℤ) ≠ 0 := by exact_mod_cast (ne_zero_of_lt (by omega : 0 < m))
      -- v(2N-m) = v(m)
      have hv2Nm : padicValInt p ((2 * N - m : ℕ) : ℤ) = padicValInt p (m : ℤ) := by
        have hsum : ((2 * N - m : ℕ) : ℤ) + (m : ℤ) = (2 * N : ℕ) := by
          have : 2 * N - m + m = 2 * N := by omega
          exact_mod_cast this
        have h2Nval : padicValInt p (2 * (N : ℤ)) = r := by
          have h2nd : ¬ (p : ℤ) ∣ (2 : ℤ) := by
            intro hd
            have : p ∣ 2 := Int.ofNat_dvd.mp (by simpa using hd)
            have hcases := (Nat.dvd_prime Nat.prime_two).mp this
            rcases hcases with h1 | h2'
            · exact hp.ne_one h1
            · omega
          have hNne : (N : ℤ) ≠ 0 := by
            exact_mod_cast pow_ne_zero r hp.ne_zero
          have hmul := padicValInt.mul (p := p) (a := (2 : ℤ)) (b := (N : ℤ))
            (by decide) hNne
          have h2z : padicValInt p (2 : ℤ) = 0 := padicValInt.eq_zero_of_not_dvd h2nd
          have hNz : padicValInt p (N : ℤ) = r := by
            have hNeq : N = p ^ r := rfl
            rw [hNeq, padicValInt.of_nat, padicValNat.prime_pow]
          omega
        -- v(a+b)=min when vals differ
        have : ((2 * N : ℕ) : ℤ) = 2 * (N : ℤ) := by simp
        have hv_ne : padicValInt p ((2 * N - m : ℕ) : ℤ) ≠ padicValInt p (m : ℤ) ∨
            True := Or.inr trivial
        -- Use: p^v(m) | 2N and p^v(m) | m so p^v(m) | 2N-m;
        -- p^{v(m)+1} doesn't divide 2N (v(2N)=r > v(m)), doesn't divide m,
        -- so if it divided 2N-m then it would divide 2N, contradiction? 
        -- Actually p^{v+1} | m is false, p^{v+1} | 2N is false (v+1 ≤ r? v < r so v+1 ≤ r.
        -- If v+1 < r, p^{v+1} | 2N. If v+1 = r, p^r | 2N = 2 p^r, yes p^r | 2 p^r.
        -- So the "doesn't divide 2N" is wrong when v+1 ≤ r always p^{v+1} | 2 p^r if v+1 ≤ r.
        -- Standard: v(2N - m) = v(m) because v(2N)=r > v(m).
        have hlt : padicValInt p (m : ℤ) < padicValInt p (2 * (N : ℤ)) := by
          simpa [h2Nval] using hvm_lt
        have hsum' : ((2 * N - m : ℕ) : ℤ) = 2 * (N : ℤ) - (m : ℤ) := by
          have : m ≤ 2 * N := by omega
          simp [Nat.cast_sub this]
        -- padicValInt of difference equals min when unequal
        have hne_sum : 2 * (N : ℤ) - m ≠ 0 := by
          rw [← hsum']; exact h2Nm_ne
        have := padicValInt.eq_zero_of_not_dvd (p := p) (z := (2 : ℤ))
        -- fallback: both divisible by p^v(m), and their difference too;
        -- not by p^{v(m)+1} because m is not
        set hv := padicValInt p (m : ℤ)
        have hdv_m : (p : ℤ) ^ hv ∣ (m : ℤ) :=
          (padicValInt_dvd_iff (p := p) hv (m : ℤ)).mpr (Or.inr le_rfl)
        have hdv_2N : (p : ℤ) ^ hv ∣ 2 * (N : ℤ) := by
          have : hv ≤ r := Nat.le_of_lt hvm_lt
          have hNpow : (p : ℤ) ^ hv ∣ (N : ℤ) := by
            simp [N]; exact pow_dvd_pow _ this
          exact dvd_mul_of_dvd_right hNpow _
        have hdv_diff : (p : ℤ) ^ hv ∣ 2 * (N : ℤ) - m :=
          dvd_sub hdv_2N hdv_m
        have hnot : ¬ (p : ℤ) ^ (hv + 1) ∣ (m : ℤ) := by
          intro hd
          have : hv + 1 ≤ padicValInt p (m : ℤ) :=
            (padicValInt_dvd_iff (p := p) (hv + 1) (m : ℤ)).mp hd |>.resolve_left hmne
          omega
        have hnot_diff : ¬ (p : ℤ) ^ (hv + 1) ∣ 2 * (N : ℤ) - m := by
          intro hd
          have : (p : ℤ) ^ (hv + 1) ∣ m := by
            have h2N' : (p : ℤ) ^ (hv + 1) ∣ 2 * (N : ℤ) := by
              have : hv + 1 ≤ r := Nat.succ_le_of_lt hvm_lt
              have hNpow : (p : ℤ) ^ (hv + 1) ∣ (N : ℤ) := by
                simp [N]; exact pow_dvd_pow _ this
              exact dvd_mul_of_dvd_right hNpow _
            exact (dvd_sub_right h2N').mp hd
          exact hnot this
        have hge : hv ≤ padicValInt p ((2 * N - m : ℕ) : ℤ) := by
          have : (p : ℤ) ^ hv ∣ ((2 * N - m : ℕ) : ℤ) := by
            simpa [hsum'] using hdv_diff
          exact (padicValInt_dvd_iff (p := p) hv _).mp this |>.resolve_left h2Nm_ne
        have hlt' : padicValInt p ((2 * N - m : ℕ) : ℤ) < hv + 1 := by
          by_contra h
          push_neg at h
          have : (p : ℤ) ^ (hv + 1) ∣ ((2 * N - m : ℕ) : ℤ) :=
            (padicValInt_dvd_iff (p := p) (hv + 1) _).mpr (Or.inr h)
          exact hnot_diff (by simpa [hsum'] using this)
        omega
      rw [padicValInt.mul h2Nm1_ne h2Nm_ne, padicValInt.eq_zero_of_not_dvd h2Nm1_nd,
        zero_add, hv2Nm]
    -- Now v((A1-B1)*Q*S) = v(RHS) ≥ 2 + v(Q) + v(S) = 2 + 2 v(m)
    have hge : 2 + padicValInt p Q + padicValInt p S ≤
        padicValInt p ((A1 - B1) * Q * S) := by
      have hRHS' : (A1 - B1) * Q * S =
          A0 * (P * S - Q * R) + (A0 - B0) * Q * R := hcomb
      rw [hRHS']
      -- both summands divisible by p^{2+vQ+vS}
      have hpow : (p : ℤ) ^ (2 + padicValInt p Q + padicValInt p S) ∣
          A0 * (P * S - Q * R) + (A0 - B0) * Q * R := by
        -- Use p^r | N and r ≥ 2, plus extra from m-powers
        have hvQS : padicValInt p Q + padicValInt p S = 2 * padicValInt p (m : ℤ) := by
          rw [hvQ, hvS]; ring
        have hterm2 : (p : ℤ) ^ (2 + padicValInt p Q + padicValInt p S) ∣
            (A0 - B0) * Q * R := by
          have h2 : (p : ℤ) ^ 2 ∣ A0 - B0 := hih
          have hQpow : (p : ℤ) ^ padicValInt p Q ∣ Q :=
            (padicValInt_dvd_iff (p := p) _ Q).mpr (Or.inr le_rfl)
          -- v(R) ≥ v(N-m) = v(m) = v(S)
          have hRpow : (p : ℤ) ^ padicValInt p S ∣ R := by
            have hNm : (p : ℤ) ^ padicValInt p (m : ℤ) ∣ ((N - m : ℕ) : ℤ) := by
              have hmne : (m : ℤ) ≠ 0 := by
                exact_mod_cast (ne_zero_of_lt (by omega : 0 < m))
              have hdv_m : (p : ℤ) ^ padicValInt p (m : ℤ) ∣ (m : ℤ) :=
                (padicValInt_dvd_iff (p := p) _ (m : ℤ)).mpr (Or.inr le_rfl)
              have hdv_N : (p : ℤ) ^ padicValInt p (m : ℤ) ∣ (N : ℤ) := by
                have : padicValInt p (m : ℤ) ≤ r := Nat.le_of_lt hvm_lt
                simp [N]; exact pow_dvd_pow _ this
              have heqNm : ((N - m : ℕ) : ℤ) = (N : ℤ) - m := by
                have : m ≤ N := by omega
                simp [Nat.cast_sub this]
              have hdivNm : (p : ℤ) ^ padicValInt p (m : ℤ) ∣ (N : ℤ) - m :=
                dvd_sub hdv_N hdv_m
              rwa [← heqNm] at hdivNm
            have : R = ((N - (m + 1) : ℕ) : ℤ) * ((N - m : ℕ) : ℤ) := rfl
            rw [this, hvS]
            exact dvd_mul_of_dvd_right hNm _
          have : (p : ℤ) ^ 2 * (p : ℤ) ^ padicValInt p Q *
              (p : ℤ) ^ padicValInt p S ∣ (A0 - B0) * Q * R :=
            mul_dvd_mul (mul_dvd_mul h2 hQpow) hRpow
          have hexp : (p : ℤ) ^ (2 + padicValInt p Q + padicValInt p S) =
              (p : ℤ) ^ 2 * (p : ℤ) ^ padicValInt p Q * (p : ℤ) ^ padicValInt p S := by
            rw [← pow_add, ← pow_add]
          rwa [hexp]
        have hterm1 : (p : ℤ) ^ (2 + padicValInt p Q + padicValInt p S) ∣
            A0 * (P * S - Q * R) := by
          -- p^r | (PS-QR) from the factor N, and r + something
          -- We use r ≥ 2 and 2 v(m) ≤ 2(r-1) so 2+2v(m) ≤ 2 + 2r-2 = 2r
          -- and v(PS-QR) ≥ r + min(r, 2v(m)) ≥ 2 + 2v(m)
          have : (p : ℤ) ^ (2 + 2 * padicValInt p (m : ℤ)) ∣ P * S - Q * R := by
            rw [hRne]
            have hNpow : (p : ℤ) ^ r ∣ (N : ℤ) := by simp [N]
            -- N(N+m-1) - m^2 : take min of the two terms
            set D : ℤ := (N : ℤ) * ((N : ℤ) + m - 1) - (m : ℤ) ^ 2
            have hD : (p : ℤ) ^ min r (2 * padicValInt p (m : ℤ)) ∣ D := by
              have htermN : (p : ℤ) ^ r ∣ (N : ℤ) * ((N : ℤ) + m - 1) :=
                dvd_mul_of_dvd_left hNpow _
              have htermM : (p : ℤ) ^ (2 * padicValInt p (m : ℤ)) ∣ (m : ℤ) ^ 2 := by
                have hmne : (m : ℤ) ≠ 0 := by
                  exact_mod_cast (ne_zero_of_lt (by omega : 0 < m))
                have : padicValInt p ((m : ℤ) ^ 2) = 2 * padicValInt p (m : ℤ) := by
                  rw [pow_two, padicValInt.mul hmne hmne]; ring
                exact (padicValInt_dvd_iff (p := p) _ _).mpr (Or.inr (le_of_eq this.symm))
              rcases le_total r (2 * padicValInt p (m : ℤ)) with h | h
              · rw [min_eq_left h]
                -- both terms divisible by p^r
                have hM' : (p : ℤ) ^ r ∣ (m : ℤ) ^ 2 :=
                  dvd_trans (pow_dvd_pow _ h) htermM
                exact dvd_sub htermN hM'
              · rw [min_eq_right h]
                have hN' : (p : ℤ) ^ (2 * padicValInt p (m : ℤ)) ∣
                    (N : ℤ) * ((N : ℤ) + m - 1) :=
                  dvd_trans (pow_dvd_pow _ h) htermN
                exact dvd_sub hN' htermM
            have : r + min r (2 * padicValInt p (m : ℤ)) ≥
                2 + 2 * padicValInt p (m : ℤ) := by
              rcases le_total r (2 * padicValInt p (m : ℤ)) with h | h
              · rw [min_eq_left h]; omega
              · rw [min_eq_right h]
                have : padicValInt p (m : ℤ) ≤ r - 1 := by omega
                omega
            have hPS' : (p : ℤ) ^ (r + min r (2 * padicValInt p (m : ℤ))) ∣
                2 * (N : ℤ) * (2 * (N : ℤ) - 1) * D := by
              have hN' : (p : ℤ) ^ r ∣ 2 * (N : ℤ) * (2 * (N : ℤ) - 1) * D :=
                dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
                  (dvd_mul_of_dvd_right hNpow _) _) _
              -- actually we need the extra min from D
              have : (p : ℤ) ^ r * (p : ℤ) ^ min r (2 * padicValInt p (m : ℤ)) ∣
                  2 * (N : ℤ) * (2 * (N : ℤ) - 1) * D :=
                mul_dvd_mul (dvd_mul_of_dvd_left
                  (dvd_mul_of_dvd_right hNpow _) _) hD
              rwa [← pow_add] at this
            exact dvd_trans (pow_dvd_pow _ this) (by simpa [D] using hPS')
          have hpow' : (p : ℤ) ^ (2 + padicValInt p Q + padicValInt p S) =
              (p : ℤ) ^ (2 + 2 * padicValInt p (m : ℤ)) := by
            congr 1
            linear_combination hvQS
          rw [hpow']
          exact dvd_mul_of_dvd_right this _
        exact dvd_add hterm1 hterm2
      have hne : A0 * (P * S - Q * R) + (A0 - B0) * Q * R ≠ 0 := by
        rw [← hRHS']
        exact mul_ne_zero (mul_ne_zero hAB hQne) hSne
      exact (padicValInt_dvd_iff (p := p) _ _).mp hpow |>.resolve_left hne
    have : 2 ≤ padicValInt p (A1 - B1) := by
      have hmul1 := padicValInt.mul (p := p) (mul_ne_zero hAB hQne) hSne
      have hmul0 := padicValInt.mul (p := p) hAB hQne
      omega
    have : (p : ℤ) ^ 2 ∣ A1 - B1 :=
      (padicValInt_dvd_iff (p := p) 2 (A1 - B1)).mpr (Or.inr this)
    refine (Int.modEq_iff_dvd).mpr ?_
    simpa [A1, B1, N, neg_sub] using (dvd_neg.mpr this)




/-! ### Pairing induction modulo `p^2` -/

lemma choose_pair_mod_p2 {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 2 ≤ r)
    {k : ℕ} (hk0 : 0 < k) (hk : k < p ^ r) (hnd : ¬ p ∣ k) :
    (choose (p ^ r + k - 1) (k - 1) : ℤ) ≡
      (choose (2 * p ^ r - (k + 1)) (p ^ r - (k + 1)) : ℤ) [ZMOD (p : ℤ) ^ 2] := by
  have hgen : ∀ k : ℕ, 0 < k → k < p ^ r → ¬ p ∣ k →
      (choose (p ^ r + k - 1) (k - 1) : ℤ) ≡
        (choose (2 * p ^ r - (k + 1)) (p ^ r - (k + 1)) : ℤ)
        [ZMOD (p : ℤ) ^ 2] := by
    intro k
    induction k using Nat.strong_induction_on with
    | h n ih =>
      intro hn0 hn hnd
      rcases n with _ | n
      · exact (lt_irrefl 0 hn0).elim
      · -- the index under consideration is `n + 1`
        by_cases hn1 : n = 0
        · -- base `k = 1`: `C(N, 0) = 1 ≡ C(2N-2, N-2)`
          subst hn1
          have hA : (choose (p ^ r + 1 - 1) (1 - 1) : ℤ) = 1 := by
            simp
          have hB : choose (2 * p ^ r - (1 + 1)) (p ^ r - (1 + 1)) =
              choose (2 * p ^ r - 2) (p ^ r - 2) := by
            simp
          have hb := pair_base_mod_sq (p := p) (r := r) hp hp5 hr
          simpa [hA, hB] using hb.symm
        · have hkge : 2 ≤ n + 1 := by omega
          by_cases hdv : p ∣ n
          · -- double step across the multiple `n` of `p`
            have hm : 2 ≤ n := by
              have : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn1) hdv
              omega
            have hmN : n + 1 < p ^ r := hn
            have hk2pos : 0 < n - 1 := by omega
            have hk2lt : n - 1 < p ^ r := by omega
            have hk2lt_n : n - 1 < n + 1 := by omega
            have hnd2 : ¬ p ∣ (n - 1) := by
              intro h
              have hsub := Nat.dvd_sub hdv h
              have heq : n - (n - 1) = 1 := by omega
              rw [heq] at hsub
              exact hp.not_dvd_one hsub
            have ih2 := ih (n - 1) hk2lt_n hk2pos hk2lt hnd2
            have heA : p ^ r + (n - 1) - 1 = p ^ r + n - 2 := by omega
            have heAk : (n - 1) - 1 = n - 2 := by omega
            have heB : 2 * p ^ r - ((n - 1) + 1) = 2 * p ^ r - n := by omega
            have heBk : p ^ r - ((n - 1) + 1) = p ^ r - n := by omega
            have ih2' :
                (choose (p ^ r + n - 2) (n - 2) : ℤ) ≡
                  (choose (2 * p ^ r - n) (p ^ r - n) : ℤ)
                  [ZMOD (p : ℤ) ^ 2] := by
              rw [← heA, ← heAk, ← heB, ← heBk]
              exact ih2
            have hstep := pair_double_step (p := p) (r := r) (m := n)
              hp hp5 hr hm hmN hdv ih2'
            have heA1 : p ^ r + n = p ^ r + (n + 1) - 1 := by omega
            rw [← heA1]
            exact hstep
          · -- single good step from `n`
            have hj0 : 0 < n := Nat.pos_of_ne_zero hn1
            have hjN : n + 1 < p ^ r := hn
            have hndj : ¬ p ∣ n := hdv
            have ih1 := ih n (by omega) hj0 (by omega) hndj
            have hstep := pair_step_mod_sq (p := p) (r := r) (j := n)
              hp hr hj0 hjN hndj hnd ih1
            have heA1 : p ^ r + n = p ^ r + (n + 1) - 1 := by omega
            rw [← heA1]
            exact hstep
  exact hgen k hk0 hk hnd

lemma risingU_mul_k_pair {p r k : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hk : k ∈ pfree p r) :
    risingU p r (p ^ r - k) * (p ^ r - k) =
      choose (2 * p ^ r - (k + 1)) (p ^ r - (k + 1)) := by
  have hk' := pfree_sub hp (by omega : 0 < r) hk
  have ⟨hkl, hnd⟩ := mem_pfree.mp hk'
  have hk0 : 0 < p ^ r - k := pfree_pos hp hk'
  have hkle : p ^ r - k ≤ p ^ r := Nat.le_of_lt hkl
  have h := risingU_mul_k (p := p) (r := r) hp hr hk0 hkle (mem_pfree.mp hk').2
  have he1 : p ^ r + (p ^ r - k) - 1 = 2 * p ^ r - (k + 1) := by
    have ⟨hklt, _⟩ := mem_pfree.mp hk
    omega
  have he2 : p ^ r - k - 1 = p ^ r - (k + 1) := by
    have ⟨hklt, _⟩ := mem_pfree.mp hk
    omega
  simpa [he1, he2] using h

lemma u_pair_int {p r k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 2 ≤ r)
    (hk : k ∈ pfree p r) :
    ((risingU p r k : ℤ) + risingU p r (p ^ r - k)) *
        (k : ℤ) * ((p ^ r - k : ℕ) : ℤ) =
      (choose (p ^ r + k - 1) (k - 1) : ℤ) * ((p ^ r - k : ℕ) : ℤ) +
        (choose (2 * p ^ r - (k + 1)) (p ^ r - (k + 1)) : ℤ) * (k : ℤ) := by
  have ⟨hkl, hnd⟩ := mem_pfree.mp hk
  have hk0 : 0 < k := pfree_pos hp hk
  have hkle : k ≤ p ^ r := Nat.le_of_lt hkl
  have hA := risingU_mul_k (p := p) (r := r) hp (by omega) hk0 hkle hnd
  have hB := risingU_mul_k_pair (p := p) (r := r) hp (by omega) hk
  have hAZ := congrArg (fun n : ℕ => (n : ℤ)) hA
  have hBZ := congrArg (fun n : ℕ => (n : ℤ)) hB
  push_cast at hAZ hBZ
  linear_combination hAZ * ((p ^ r - k : ℕ) : ℤ) + hBZ * (k : ℤ)

lemma u_pair_mod_sq {p r k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 2 ≤ r)
    (hk : k ∈ pfree p r) :
    (risingU p r k : ℤ) + risingU p r (p ^ r - k) ≡ 0 [ZMOD (p : ℤ) ^ 2] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ⟨hkl, hnd⟩ := mem_pfree.mp hk
  have hk0 : 0 < k := pfree_pos hp hk
  have hpair := choose_pair_mod_p2 (p := p) (r := r) hp hp5 hr hk0 hkl hnd
  have hid := u_pair_int hp hp5 hr hk
  set A : ℤ := (choose (p ^ r + k - 1) (k - 1) : ℤ)
  set B : ℤ := (choose (2 * p ^ r - (k + 1)) (p ^ r - (k + 1)) : ℤ)
  set u : ℤ := (risingU p r k : ℤ)
  set v : ℤ := (risingU p r (p ^ r - k) : ℤ)
  set nk : ℤ := ((p ^ r - k : ℕ) : ℤ)
  have hid' : (u + v) * (k : ℤ) * nk = A * nk + B * (k : ℤ) := by
    simpa [A, B, u, v, nk] using hid
  have hcongr : A ≡ B [ZMOD (p : ℤ) ^ 2] := hpair
  have hdiff : A * nk + B * (k : ℤ) - A * (p : ℤ) ^ r =
      (k : ℤ) * (B - A) + A * (nk - (p : ℤ) ^ r + (k : ℤ)) := by
    ring
  have hnk : nk + (k : ℤ) = (p : ℤ) ^ r := by
    have hle : k ≤ p ^ r := Nat.le_of_lt hkl
    dsimp [nk]
    rw [Nat.cast_sub hle, Nat.cast_pow]
    ring
  have hsimp : A * nk + B * (k : ℤ) = A * (p : ℤ) ^ r + (k : ℤ) * (B - A) := by
    have : nk = (p : ℤ) ^ r - (k : ℤ) := by linarith [hnk]
    rw [this]
    ring
  have hN : (p : ℤ) ^ 2 ∣ A * (p : ℤ) ^ r :=
    dvd_mul_of_dvd_right (pow_dvd_pow _ (by omega : 2 ≤ r)) _
  have hBA : (p : ℤ) ^ 2 ∣ B - A := (Int.modEq_iff_dvd).mp hcongr
  have hRHS : (p : ℤ) ^ 2 ∣ A * (p : ℤ) ^ r + (k : ℤ) * (B - A) :=
    dvd_add hN (dvd_mul_of_dvd_right hBA _)
  have hprod : (p : ℤ) ^ 2 ∣ (u + v) * (k : ℤ) * nk := by
    rwa [hid', hsimp]
  have hprod' : (p : ℤ) ^ 2 ∣ (u + v) * ((k : ℤ) * nk) := by
    simpa [mul_assoc] using hprod
  have hkunit : ¬ (p : ℤ) ∣ (k : ℤ) := by
    intro hd
    exact hnd (Int.ofNat_dvd.mp (by simpa using hd))
  have hnkunit : ¬ (p : ℤ) ∣ nk := by
    intro hd
    have : p ∣ p ^ r - k := Int.ofNat_dvd.mp (by simpa [nk] using hd)
    exact (mem_pfree.mp (pfree_sub hp (by omega : 0 < r) hk)).2 this
  have hcancel1 : (p : ℤ) ^ 2 ∣ (u + v) * (k : ℤ) - 0 := by
    refine cancel_unit_mod_sq (p := p) (a := (u + v) * (k : ℤ)) (b := 0)
      (u := nk) hnkunit ?_
    simpa [sub_zero] using hprod
  have hcancel2 : (p : ℤ) ^ 2 ∣ (u + v) - 0 :=
    cancel_unit_mod_sq (p := p) (a := u + v) (b := 0) (u := (k : ℤ)) hkunit
      (by simpa [sub_zero] using hcancel1)
  refine (Int.modEq_iff_dvd).mpr ?_
  simpa using (dvd_neg.mpr hcancel2)

lemma u_cube_pair_mod_sq {p r k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 2 ≤ r)
    (hk : k ∈ pfree p r) :
    (p : ℤ) ^ 2 ∣
      (risingU p r k : ℤ) ^ 3 + (risingU p r (p ^ r - k) : ℤ) ^ 3 := by
  have h := u_pair_mod_sq (p := p) (r := r) hp hp5 hr hk
  set u : ℤ := (risingU p r k : ℤ)
  set v : ℤ := (risingU p r (p ^ r - k) : ℤ)
  have hsum : (p : ℤ) ^ 2 ∣ u + v := by
    simpa [u, v, neg_sub] using (dvd_neg.mpr ((Int.modEq_iff_dvd).mp h))
  have hid : u ^ 3 + v ^ 3 = (u + v) * (u ^ 2 - u * v + v ^ 2) := by ring
  rw [hid]
  exact dvd_mul_of_dvd_left hsum _

lemma sum_risingU_cube_mod_sq {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
    (p : ℤ) ^ 2 ∣ ∑ k ∈ pfree p r, (risingU p r k : ℤ) ^ 3 := by
  have hr0 : 0 < r := by omega
  have hpair :
      ∑ k ∈ pfree p r, (risingU p r k : ℤ) ^ 3 =
        ∑ k ∈ pfree p r, (risingU p r (p ^ r - k) : ℤ) ^ 3 := by
    refine Finset.sum_bij (fun k _ => p ^ r - k) ?_ ?_ ?_ ?_
    · intro k hk; exact pfree_sub hp hr0 hk
    · intro k hk k' hk' h
      have := congrArg (fun t => p ^ r - t) h
      simpa [pfree_sub_sub hp hk, pfree_sub_sub hp hk'] using this
    · intro k hk
      refine ⟨p ^ r - k, pfree_sub hp hr0 hk, pfree_sub_sub hp hk⟩
    · intro k hk
      simp [pfree_sub_sub hp hk]
  have h2 :
      2 * ∑ k ∈ pfree p r, (risingU p r k : ℤ) ^ 3 =
        ∑ k ∈ pfree p r,
          ((risingU p r k : ℤ) ^ 3 + (risingU p r (p ^ r - k) : ℤ) ^ 3) := by
    calc
      2 * ∑ k ∈ pfree p r, (risingU p r k : ℤ) ^ 3 =
          ∑ k ∈ pfree p r, (risingU p r k : ℤ) ^ 3 +
            ∑ k ∈ pfree p r, (risingU p r k : ℤ) ^ 3 := by
        rw [two_mul]
      _ = ∑ k ∈ pfree p r, (risingU p r k : ℤ) ^ 3 +
            ∑ k ∈ pfree p r, (risingU p r (p ^ r - k) : ℤ) ^ 3 := by
        rw [hpair]
      _ = ∑ k ∈ pfree p r,
            ((risingU p r k : ℤ) ^ 3 + (risingU p r (p ^ r - k) : ℤ) ^ 3) :=
        (sum_add_distrib).symm
  have hterms : (p : ℤ) ^ 2 ∣
      ∑ k ∈ pfree p r,
        ((risingU p r k : ℤ) ^ 3 + (risingU p r (p ^ r - k) : ℤ) ^ 3) := by
    refine dvd_sum ?_
    intro k hk
    exact u_cube_pair_mod_sq hp hp5 hr hk
  have h2sum : (p : ℤ) ^ 2 ∣ 2 * ∑ k ∈ pfree p r, (risingU p r k : ℤ) ^ 3 := by
    rwa [h2]
  haveI : Fact p.Prime := ⟨hp⟩
  have hcancel : (p : ℤ) ^ 2 ∣
      (∑ k ∈ pfree p r, (risingU p r k : ℤ) ^ 3) - 0 := by
    refine cancel_unit_mod_sq (p := p)
        (a := ∑ k ∈ pfree p r, (risingU p r k : ℤ) ^ 3)
        (b := 0) (u := (2 : ℤ)) ?_ ?_
    · intro hd
      have : p ∣ 2 := Int.ofNat_dvd.mp (by simpa using hd)
      have : p ≤ 2 := Nat.le_of_dvd (by decide) this
      omega
    · convert h2sum using 1
      ring
  simpa using hcancel

lemma S3f_dvd_two {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
    (p : ℤ) ^ (3 * r + 2) ∣ S3f p r := by
  have hr1 : 1 ≤ r := by omega
  rw [S3f_eq_pow_sum hp hr1, pfree_eq_filter_succ p r hp (by omega)]
  obtain ⟨t, ht⟩ := sum_risingU_cube_mod_sq hp hp5 hr
  refine ⟨2 * t, ?_⟩
  rw [ht, pow_add, pow_two]
  ring

/-! ### Square-sum of `u_k` to order `p^r` via the `r = 2` product expansion -/

lemma risingU_eq_A_div {p r k : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hk : k ∈ pfree p r) :
    (risingU p r k : ℤ) * (k : ℤ) = (choose (p ^ r + k - 1) (k - 1) : ℤ) := by
  have ⟨hkl, hnd⟩ := mem_pfree.mp hk
  have hk0 : 0 < k := pfree_pos hp hk
  exact_mod_cast risingU_mul_k hp hr hk0 (Nat.le_of_lt hkl) hnd

lemma A_succ_mul (N j : ℕ) (hj : 0 < j) :
    choose (N + j) j * j = choose (N + j - 1) (j - 1) * (N + j) :=
  pairA_succ N j hj

/-- For `r = 2` and `k = s + j*p` with `1 ≤ s < p`, one has
`⌊(k-1)/p⌋ = j`. -/
lemma floor_pred_div (p s j : ℕ) (hs : 1 ≤ s) (hsp : s < p) :
    (s + j * p - 1) / p = j := by
  have h : s + j * p - 1 = (s - 1) + j * p := by omega
  rw [h, Nat.add_mul_div_right _ _ (by omega : 0 < p), Nat.div_eq_of_lt (by omega)]
  simp

lemma choose_A_mul_factorial (N k : ℕ) :
    choose (N + k - 1) (k - 1) * (k - 1).factorial =
      (N + 1).ascFactorial (k - 1) := by
  cases k with
  | zero =>
    simp [Nat.choose, Nat.ascFactorial]
  | succ k =>
    -- `C(N+k, k) * k! = (N+1).ascFactorial k`
    have h := Nat.ascFactorial_eq_factorial_mul_choose N k
    -- h : (N+1).ascFactorial k = k! * C(N+k, k)
    have heq : N + (k + 1) - 1 = N + k := by omega
    have hk : (k + 1) - 1 = k := by omega
    rw [heq, hk]
    simpa [mul_comm] using h.symm

lemma choose_A_mul_factorial_int (N k : ℕ) :
    (choose (N + k - 1) (k - 1) : ℤ) * ((k - 1).factorial : ℤ) =
      ∏ i ∈ range (k - 1), ((N + 1 + i : ℕ) : ℤ) := by
  have h := congrArg (fun n : ℕ => (n : ℤ)) (choose_A_mul_factorial N k)
  push_cast at h
  simpa [Nat.ascFactorial_eq_prod_range, Nat.cast_prod, Nat.cast_add] using h

lemma choose_succ_mul_succ (n k : ℕ) :
    choose (n + 1) (k + 1) * (k + 1) = choose n k * (n + 1) := by
  simpa [mul_comm] using (add_one_mul_choose_eq n k).symm

lemma choose_p_add_succ (p μ : ℕ) :
    choose (p + (μ + 1)) (μ + 1) * (μ + 1) =
      choose (p + μ) μ * (p + μ + 1) := by
  simpa [Nat.add_assoc] using choose_succ_mul_succ (p + μ) μ

lemma div_pred_of_not_dvd {p k : ℕ} (hp : 0 < p) (hk : 0 < k) (hnd : ¬ p ∣ k) :
    (k - 1) / p = k / p := by
  have hmod : k % p ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
  have hmpos : 1 ≤ k % p := Nat.pos_of_ne_zero hmod
  have hmlt : k % p < p := Nat.mod_lt k hp
  have hdecomp : k = p * (k / p) + k % p := (Nat.div_add_mod k p).symm
  have : k - 1 = (k % p - 1) + p * (k / p) := by omega
  rw [this, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (by omega)]
  simp

lemma div_pred_of_dvd {p k : ℕ} (hp : 0 < p) (hk : 0 < k) (hdv : p ∣ k) :
    (k - 1) / p = k / p - 1 := by
  obtain ⟨t, ht⟩ := hdv
  have ht0 : 0 < t := by
    subst ht
    exact Nat.pos_of_mul_pos_left hk
  have h1 : k - 1 = p * t - 1 := by rw [ht]
  have h2 : p * t - 1 = (p - 1) + p * (t - 1) := by
    have ht1 : t = t - 1 + 1 := by omega
    have hmul : p * t = p * (t - 1) + p := by
      conv_lhs => rw [ht1]
      rw [Nat.mul_add, mul_one]
    omega
  rw [h1, h2, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (by omega)]
  have : k / p = t := by rw [ht, Nat.mul_div_cancel_left t hp]
  omega

lemma choose_A_succ_int (N k : ℕ) (hk : 0 < k) :
    (choose (N + k) k : ℤ) * (k : ℤ) =
      (choose (N + k - 1) (k - 1) : ℤ) * ((N + k : ℕ) : ℤ) :=
  pairA_succ_int N k hk

lemma choose_A_step_not_dvd {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hnd : ¬ p ∣ k) :
    (choose (p ^ 2 + k) k : ℤ) ≡
      (choose (p ^ 2 + k - 1) (k - 1) : ℤ) [ZMOD (p : ℤ) ^ 2] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hA := choose_A_succ_int (p ^ 2) k hk
  have hkunit : ¬ (p : ℤ) ∣ (k : ℤ) := by
    intro hd
    exact hnd (Int.ofNat_dvd.mp (by simpa using hd))
  have hdiff' : (p : ℤ) ^ 2 ∣
      ((choose (p ^ 2 + k) k : ℤ) - choose (p ^ 2 + k - 1) (k - 1)) * (k : ℤ) := by
    have hex :
        ((choose (p ^ 2 + k) k : ℤ) - choose (p ^ 2 + k - 1) (k - 1)) * (k : ℤ) =
          (choose (p ^ 2 + k - 1) (k - 1) : ℤ) *
            (((p ^ 2 + k : ℕ) : ℤ) - (k : ℤ)) := by
      linear_combination hA
    rw [hex]
    have : ((p ^ 2 + k : ℕ) : ℤ) - (k : ℤ) = (p : ℤ) ^ 2 := by simp
    rw [this]
    exact dvd_mul_left _ _
  exact (Int.modEq_iff_dvd).mpr
    (by simpa [neg_sub] using
      (dvd_neg.mpr (cancel_unit_mod_sq (p := p) (u := (k : ℤ)) hkunit hdiff')))
lemma choose_A_step_of_dvd {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hkN : k < p ^ 2) (hdv : p ∣ k)
    (ih : (choose (p ^ 2 + k - 1) (k - 1) : ℤ) ≡
      (choose (p + (k - 1) / p) ((k - 1) / p) : ℤ) [ZMOD (p : ℤ) ^ 2]) :
    (choose (p ^ 2 + k) k : ℤ) ≡
      (choose (p + k / p) (k / p) : ℤ) [ZMOD (p : ℤ) ^ 2] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hA := choose_A_succ_int (p ^ 2) k hk
  have hμ : (k - 1) / p = k / p - 1 := div_pred_of_dvd hp.pos hk hdv
  have hμpos : 0 < k / p := by
    have : p ≤ k := Nat.le_of_dvd hk hdv
    exact Nat.div_pos this hp.pos
  set μ := k / p - 1
  have hμeq : k / p = μ + 1 := by omega
  have hkμ : (k : ℤ) = (p : ℤ) * ((μ + 1 : ℕ) : ℤ) := by
    have : k = p * (k / p) := (Nat.mul_div_cancel' hdv).symm
    rw [this, hμeq]
    simp [mul_comm]
  have hNk : ((p ^ 2 + k : ℕ) : ℤ) = (p : ℤ) * ((p + μ + 1 : ℕ) : ℤ) := by
    have : ((p ^ 2 + k : ℕ) : ℤ) = (p : ℤ) ^ 2 + (k : ℤ) := by simp
    rw [this, hkμ]
    push_cast
    ring
  have hch := choose_p_add_succ p μ
  have hC : (choose (p + (μ + 1)) (μ + 1) : ℤ) * ((μ + 1 : ℕ) : ℤ) =
      (choose (p + μ) μ : ℤ) * ((p + μ + 1 : ℕ) : ℤ) := by
    exact_mod_cast hch
  have hA' : (choose (p ^ 2 + k) k : ℤ) * (k : ℤ) =
      (choose (p ^ 2 + k - 1) (k - 1) : ℤ) * ((p ^ 2 + k : ℕ) : ℤ) := hA
  have hcancelp :
      (choose (p ^ 2 + k) k : ℤ) * ((μ + 1 : ℕ) : ℤ) =
        (choose (p ^ 2 + k - 1) (k - 1) : ℤ) * ((p + μ + 1 : ℕ) : ℤ) := by
    have hmul := hA'
    rw [hkμ, hNk] at hmul
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have : (p : ℤ) * ((choose (p ^ 2 + k) k : ℤ) * ((μ + 1 : ℕ) : ℤ)) =
        (p : ℤ) * ((choose (p ^ 2 + k - 1) (k - 1) : ℤ) * ((p + μ + 1 : ℕ) : ℤ)) := by
      linear_combination hmul
    exact Int.eq_of_mul_eq_mul_left hp0 this
  have hih : (choose (p ^ 2 + k - 1) (k - 1) : ℤ) ≡
      (choose (p + μ) μ : ℤ) [ZMOD (p : ℤ) ^ 2] := by
    simpa [hμ] using ih
  have hdiff :
      ((choose (p ^ 2 + k) k : ℤ) - choose (p + (μ + 1)) (μ + 1)) *
        ((μ + 1 : ℕ) : ℤ) =
      ((choose (p ^ 2 + k - 1) (k - 1) : ℤ) - choose (p + μ) μ) *
        ((p + μ + 1 : ℕ) : ℤ) := by
    linear_combination hcancelp - hC
  have hR : (p : ℤ) ^ 2 ∣
      ((choose (p ^ 2 + k - 1) (k - 1) : ℤ) - choose (p + μ) μ) *
        ((p + μ + 1 : ℕ) : ℤ) :=
    dvd_mul_of_dvd_left ((Int.modEq_iff_dvd).mp hih.symm) _
  have hL : (p : ℤ) ^ 2 ∣
      ((choose (p ^ 2 + k) k : ℤ) - choose (p + (μ + 1)) (μ + 1)) *
        ((μ + 1 : ℕ) : ℤ) := by
    rwa [hdiff]
  have hunit : ¬ (p : ℤ) ∣ ((μ + 1 : ℕ) : ℤ) := by
    intro hd
    have : p ∣ μ + 1 := Int.ofNat_dvd.mp (by simpa using hd)
    have hμ1 : μ + 1 = k / p := hμeq.symm
    rw [hμ1] at this
    have : p * p ∣ k := by
      have hdiv : p ∣ k / p := this
      have h2 : k = p * (k / p) := (Nat.mul_div_cancel' hdv).symm
      rw [h2]
      exact mul_dvd_mul_left p hdiv
    have : p ^ 2 ∣ k := by simpa [pow_two] using this
    have : p ^ 2 ≤ k := Nat.le_of_dvd hk this
    omega
  have hfin := cancel_unit_mod_sq (p := p) (u := ((μ + 1 : ℕ) : ℤ)) hunit hL
  refine (Int.modEq_iff_dvd).mpr ?_
  simpa [hμeq, neg_sub] using (dvd_neg.mpr hfin)


lemma choose_A_mod_sq_r2 {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hkN : k ≤ p ^ 2) :
    (choose (p ^ 2 + k - 1) (k - 1) : ℤ) ≡
      (choose (p + (k - 1) / p) ((k - 1) / p) : ℤ) [ZMOD (p : ℤ) ^ 2] := by
  induction k, hk using Nat.le_induction with
  | base =>
    simp
  | succ k hk ih =>
    have hk0 : 0 < k := by omega
    have hkle : k ≤ p ^ 2 := by omega
    have ih' := ih hkle
    have heqA : choose (p ^ 2 + (k + 1) - 1) ((k + 1) - 1) =
        choose (p ^ 2 + k) k := by
      congr 1 <;> omega
    rw [heqA]
    by_cases hdv : p ∣ k
    · have hklt : k < p ^ 2 := by omega
      have hstep := choose_A_step_of_dvd (p := p) (k := k) hp hk0 hklt hdv ih'
      have heqC : choose (p + k / p) (k / p) =
          choose (p + ((k + 1) - 1) / p) (((k + 1) - 1) / p) := by
        simp
      rwa [heqC] at hstep
    · have hstep := choose_A_step_not_dvd (p := p) (k := k) hp hk0 hdv
      have hμ : k / p = (k - 1) / p :=
        (div_pred_of_not_dvd hp.pos hk0 hdv).symm
      have : (choose (p ^ 2 + k - 1) (k - 1) : ℤ) ≡
          (choose (p + k / p) (k / p) : ℤ) [ZMOD (p : ℤ) ^ 2] := by
        simpa [hμ] using ih'
      exact hstep.trans this

lemma choose_p_add_mod_p {p μ : ℕ} (hp : p.Prime) (hμ : μ < p) :
    choose (p + μ) μ ≡ 1 [MOD p] := by
  have h := choose_prime_pow_add_mod_p (p := p) (r := 1) (m := μ) hp (by simpa using hμ)
  simpa [pow_one] using h

lemma mu_lt_p_of_lt_sq {p k : ℕ} (hp : p.Prime) (hk0 : 1 ≤ k) (hk : k ≤ p ^ 2) :
    (k - 1) / p < p := by
  have h1 : k - 1 < p * p := by
    have : k - 1 < p ^ 2 := by omega
    rwa [pow_two] at this
  exact Nat.div_lt_of_lt_mul h1

lemma risingU_mod_sq_r2 {p k : ℕ} (hp : p.Prime) (hk : k ∈ pfree p 2) :
    (risingU p 2 k : ZMod (p ^ 2)) =
      (choose (p + (k - 1) / p) ((k - 1) / p) : ZMod (p ^ 2)) *
        (k : ZMod (p ^ 2))⁻¹ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ⟨hkl, hnd⟩ := mem_pfree.mp hk
  have hk0 : 0 < k := pfree_pos hp hk
  have hkle : k ≤ p ^ 2 := Nat.le_of_lt hkl
  have hA := risingU_eq_A_div (p := p) (r := 2) hp (by decide) hk
  have hcongr := choose_A_mod_sq_r2 (p := p) (k := k) hp hk0 hkle
  have hcast : (choose (p ^ 2 + k - 1) (k - 1) : ZMod (p ^ 2)) =
      (choose (p + (k - 1) / p) ((k - 1) / p) : ZMod (p ^ 2)) := by
    have hI := (ZMod.intCast_eq_intCast_iff
        (choose (p ^ 2 + k - 1) (k - 1) : ℤ)
        (choose (p + (k - 1) / p) ((k - 1) / p) : ℤ)
        (p ^ 2)).mpr (by simpa [Nat.cast_pow] using hcongr)
    simpa using hI
  have hu : IsUnit (k : ZMod (p ^ 2)) := pfree_isUnit_pow (n := 2) hp (by decide) hk
  have hmul : (risingU p 2 k : ZMod (p ^ 2)) * k =
      (choose (p ^ 2 + k - 1) (k - 1) : ZMod (p ^ 2)) := by
    have := congrArg (fun n : ℤ => (n : ZMod (p ^ 2))) hA
    simpa [Int.cast_mul, Int.cast_natCast] using this
  calc
    (risingU p 2 k : ZMod (p ^ 2)) =
        (risingU p 2 k : ZMod (p ^ 2)) * k * (k : ZMod (p ^ 2))⁻¹ := by
      rw [mul_assoc, unit_mul_inv hu, mul_one]
    _ = (choose (p ^ 2 + k - 1) (k - 1) : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹ := by
      rw [hmul]
    _ = (choose (p + (k - 1) / p) ((k - 1) / p) : ZMod (p ^ 2)) *
          (k : ZMod (p ^ 2))⁻¹ := by
      rw [hcast]

lemma inv_s_add_jp {p s j : ℕ} (hp : p.Prime) (hs : s ∈ Icc 1 (p - 1)) :
    (((s + j * p : ℕ) : ZMod (p ^ 2))⁻¹) =
      (s : ZMod (p ^ 2))⁻¹ -
        (p : ZMod (p ^ 2)) * (j : ZMod (p ^ 2)) * ((s : ZMod (p ^ 2))⁻¹) ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hspos : 0 < s := (mem_Icc.mp hs).1
  have hslt : s < p := by have := mem_Icc.mp hs; omega
  have hsu : IsUnit (s : ZMod (p ^ 2)) := by
    rw [ZMod.isUnit_iff_coprime]
    have hcp : s.Coprime p :=
      (hp.coprime_iff_not_dvd).2 (Nat.not_dvd_of_pos_of_lt hspos hslt) |>.symm
    exact hcp.pow_right 2
  have hcast : ((s + j * p : ℕ) : ZMod (p ^ 2)) =
      (s : ZMod (p ^ 2)) + (p : ZMod (p ^ 2)) * (j : ZMod (p ^ 2)) := by
    simp [Nat.cast_add, Nat.cast_mul, mul_comm]
  rw [hcast, inv_add_p_mul hp hsu]

lemma zmod_sq_eq_one_add_p {p : ℕ} [Fact p.Prime] (x : ZMod (p ^ 2))
    (hx : ZMod.castHom (dvd_pow_self p (by decide : (2 : ℕ) ≠ 0)) (ZMod p) x = 1) :
    ∃ e : ZMod (p ^ 2), x = 1 + (p : ZMod (p ^ 2)) * e := by
  have h0 :
      ZMod.castHom (dvd_pow_self p (by decide : (2 : ℕ) ≠ 0)) (ZMod p) (x - 1) = 0 := by
    rw [map_sub, hx, map_one, sub_self]
  have hval : ((x - 1).val : ZMod p) = 0 := by
    have : ZMod.castHom (dvd_pow_self p (by decide : (2 : ℕ) ≠ 0)) (ZMod p) (x - 1) =
        ((x - 1).val : ZMod p) := by
      rw [ZMod.castHom_apply, ← ZMod.natCast_val]
    exact this.symm.trans h0
  obtain ⟨e, he⟩ := (ZMod.natCast_eq_zero_iff _ p).mp hval
  refine ⟨e, ?_⟩
  have hx1 : x - 1 = ((x - 1).val : ZMod (p ^ 2)) := (ZMod.natCast_zmod_val _).symm
  rw [eq_add_of_sub_eq hx1, he, Nat.cast_mul]
  ac_rfl

lemma choose_p_add_eq_one_add_p {p j : ℕ} (hp : p.Prime) (hj : j < p) :
    ∃ e : ZMod (p ^ 2),
      (choose (p + j) j : ZMod (p ^ 2)) = 1 + (p : ZMod (p ^ 2)) * e := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine zmod_sq_eq_one_add_p _ ?_
  have hmod := choose_p_add_mod_p hp hj
  have : ((choose (p + j) j : ℕ) : ZMod p) = (1 : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ 1 p).mpr hmod
  simpa [ZMod.castHom_apply] using this

