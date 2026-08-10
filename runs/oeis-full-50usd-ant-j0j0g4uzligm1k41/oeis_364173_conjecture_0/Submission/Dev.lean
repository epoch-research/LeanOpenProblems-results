import FormalConjectures.Util.ProblemImports

open scoped Real BigOperators
open Finset

noncomputable def Rrat (n : ℕ) : ℚ :=
  2^(3*n) * (Nat.factorial (2*n)) * (∏ j ∈ range (3*n), ((3*(n:ℚ)+1+2*j))) / ((Nat.factorial (4*n)) * (Nat.factorial n))

lemma Rrat_pos (n : ℕ) : 0 < Rrat n := by
  unfold Rrat
  apply div_pos
  · apply mul_pos
    apply mul_pos
    · positivity
    · exact_mod_cast Nat.factorial_pos _
    · apply Finset.prod_pos
      intro j _; positivity
  · apply mul_pos <;> exact_mod_cast Nat.factorial_pos _

/-- Wolstenholme-type: the sum of squared inverses over nonzero residues vanishes mod p. -/
lemma wolstenholme (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) :
    ∑ x : ZMod p, x ^ (p - 3) = 0 := by
  apply FiniteField.sum_pow_lt_card_sub_one
  rw [ZMod.card]
  omega

/-! ### Factorial block decomposition -/

/-- `(a+p)! = a! * ∏_{k<p}(a+k+1)`. -/
lemma fact_add (a : ℕ) : ∀ p, Nat.factorial (a + p) = Nat.factorial a * ∏ k ∈ range p, (a + k + 1) := by
  intro p
  induction p with
  | zero => simp
  | succ p ih =>
    rw [prod_range_succ, ← mul_assoc, ← ih,
        show a + (p+1) = (a+p) + 1 by ring, Nat.factorial_succ]
    ring

/-- Regroup `(M*p)!` into `M` blocks of length `p`. -/
lemma fact_regroup (p : ℕ) : ∀ M, Nat.factorial (M * p) = ∏ t ∈ range M, ∏ k ∈ range p, (t * p + k + 1) := by
  intro M
  induction M with
  | zero => simp
  | succ M ih =>
    rw [prod_range_succ, ← ih, show (M + 1) * p = M * p + p by ring, fact_add]

/-- The block of `p-1` units in `(t*p, (t+1)*p)`. -/
def block (p t : ℕ) : ℕ := ∏ k ∈ range (p - 1), (t * p + k + 1)

lemma inner_split (p t : ℕ) (hp : 1 ≤ p) :
    ∏ k ∈ range p, (t * p + k + 1) = block p t * ((t + 1) * p) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [prod_range_succ, block]
  simp only [Nat.add_sub_cancel]
  congr 1
  ring

lemma prod_range_add_one (M : ℕ) : ∏ t ∈ range M, (t + 1) = Nat.factorial M := by
  induction M with
  | zero => simp
  | succ M ih => rw [prod_range_succ, ih, Nat.factorial_succ]; ring

/-- `(M*p)! = p^M * M! * ∏_{t<M} block p t`. -/
lemma fact_pM (p : ℕ) (hp : 1 ≤ p) (M : ℕ) :
    Nat.factorial (M * p) = p ^ M * Nat.factorial M * ∏ t ∈ range M, block p t := by
  rw [fact_regroup]
  have : ∀ t ∈ range M, ∏ k ∈ range p, (t * p + k + 1) = block p t * ((t + 1) * p) :=
    fun t _ => inner_split p t hp
  rw [prod_congr rfl this]
  rw [show (∏ t ∈ range M, block p t * ((t + 1) * p))
        = (∏ t ∈ range M, block p t) * (∏ t ∈ range M, ((t + 1) * p)) from prod_mul_distrib]
  rw [show (∏ t ∈ range M, ((t + 1) * p)) = (∏ t ∈ range M, (t + 1)) * (∏ t ∈ range M, p) from prod_mul_distrib]
  rw [prod_range_add_one, prod_const, card_range]
  ring

/-! ### Block congruence mod p³ (pairing + weak Wolstenholme) -/

/-- `block p t` as a product over `Icc 1 (p-1)`. -/
lemma block_Icc (p t : ℕ) :
    (block p t : ℤ) = ∏ j ∈ Finset.Icc 1 (p-1), ((t*p + j : ℤ)) := by
  rw [block]
  rw [show Finset.Icc 1 (p-1) = Finset.image (fun k => k+1) (range (p-1)) by
        ext x
        constructor
        · intro hx; rw [Finset.mem_Icc] at hx; rw [Finset.mem_image]
          exact ⟨x-1, by rw [Finset.mem_range]; omega, by omega⟩
        · intro hx; rw [Finset.mem_image] at hx; obtain ⟨a, ha, rfl⟩ := hx
          rw [Finset.mem_range] at ha; rw [Finset.mem_Icc]; omega]
  rw [Finset.prod_image (fun a _ b _ h => by simpa using h)]
  push_cast
  apply Finset.prod_congr rfl
  intro k _; push_cast; ring

/-- Full-range inverse-square sum vanishes in `ZMod p`. -/
lemma wolstenholme_full_inv2 (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    ∑ k ∈ Finset.Icc 1 (p-1), ((k : ZMod p))⁻¹ ^ 2 = 0 := by
  have hpp : 0 < p := hp.out.pos
  haveI : NeZero p := ⟨by omega⟩
  have hcast0 : ∀ k, 1 ≤ k → k ≤ p - 1 → ((k : ZMod p)) ≠ 0 := by
    intro k hk1 hk2
    rw [ne_eq, CharP.cast_eq_zero_iff (ZMod p) p]
    intro hdvd; have := Nat.le_of_dvd (by omega) hdvd; omega
  have hbij : ∑ k ∈ Finset.Icc 1 (p-1), ((k : ZMod p))⁻¹ ^ 2
      = ∑ x ∈ (Finset.univ.erase (0 : ZMod p)), x ^ (p - 3) := by
    refine Finset.sum_bij' (fun k _ => ((k : ZMod p))) (fun x _ => x.val) ?_ ?_ ?_ ?_ ?_
    · intro k hk; rw [Finset.mem_Icc] at hk
      rw [Finset.mem_erase]
      exact ⟨hcast0 k hk.1 hk.2, Finset.mem_univ _⟩
    · intro x hx; rw [Finset.mem_erase] at hx
      rw [Finset.mem_Icc]
      have hlt : x.val < p := ZMod.val_lt x
      have hne : x.val ≠ 0 := by
        intro h; apply hx.1; rw [← ZMod.natCast_zmod_val x, h]; simp
      exact ⟨Nat.one_le_iff_ne_zero.mpr hne, Nat.le_sub_one_of_lt hlt⟩
    · intro k hk; rw [Finset.mem_Icc] at hk
      exact ZMod.val_cast_of_lt (by omega)
    · intro x hx; exact ZMod.natCast_zmod_val x
    · intro k hk; rw [Finset.mem_Icc] at hk
      have hk0 := hcast0 k hk.1 hk.2
      rw [inv_pow]
      exact (inv_eq_of_mul_eq_one_right (by
        rw [← pow_add, show 2 + (p - 3) = p - 1 by omega]
        exact ZMod.pow_card_sub_one_eq_one hk0))
  rw [hbij, Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  rw [wolstenholme p h5]
  rw [zero_pow (by omega)]
  ring

/-- Weak Wolstenholme, half range: `∑_{k=1}^{(p-1)/2} (k(p-k))⁻¹ = 0` in `ZMod p`. -/
lemma wolstenholme_half (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    ∑ k ∈ Finset.Icc 1 ((p-1)/2), ((k : ZMod p) * ((p:ZMod p) - k))⁻¹ = 0 := by
  have hpp : 0 < p := hp.out.pos
  haveI : NeZero p := ⟨by omega⟩
  have hp0 : (p : ZMod p) = 0 := by exact_mod_cast ZMod.natCast_self p
  set h := (p-1)/2 with hh
  obtain ⟨m, hm⟩ := hp.out.odd_of_ne_two (by omega)
  have hhm : p - 1 = 2 * h := by rw [hh, hm]; omega
  -- summand rewrite: (k(p-k))⁻¹ = -(k⁻¹)^2
  have hsummand : ∀ k : ℕ, ((k : ZMod p) * ((p:ZMod p) - k))⁻¹ = -(((k:ZMod p))⁻¹)^2 := by
    intro k; rw [hp0, zero_sub]; ring
  rw [Finset.sum_congr rfl (fun k _ => hsummand k)]
  rw [Finset.sum_neg_distrib]
  -- reduce to: ∑_{Icc 1 h} (k⁻¹)^2 = 0
  suffices hgoal : ∑ k ∈ Finset.Icc 1 h, (((k:ZMod p))⁻¹)^2 = 0 by
    rw [hgoal]; ring
  -- full = 2 * half
  have hfull := wolstenholme_full_inv2 p h5
  have hsplit : ∑ k ∈ Finset.Icc 1 (p-1), (((k:ZMod p))⁻¹)^2
      = 2 * ∑ k ∈ Finset.Icc 1 h, (((k:ZMod p))⁻¹)^2 := by
    rw [hhm]
    rw [show Finset.Icc 1 (2*h) = Finset.Icc 1 h ∪ Finset.Icc (h+1) (2*h) by
        ext x; rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]; omega]
    rw [Finset.sum_union (by
        rw [Finset.disjoint_left]; intro a ha hb
        rw [Finset.mem_Icc] at ha hb; omega)]
    have hrefl : ∑ k ∈ Finset.Icc (h+1) (2*h), (((k:ZMod p))⁻¹)^2
        = ∑ k ∈ Finset.Icc 1 h, (((k:ZMod p))⁻¹)^2 := by
      refine Finset.sum_nbij' (fun k => 2*h+1-k) (fun k => 2*h+1-k) ?_ ?_ ?_ ?_ ?_
      · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
      · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
      · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
      · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
      · intro a ha; simp only [Finset.mem_Icc] at ha
        have hle : a ≤ p := by omega
        have hcast : ((2*h+1-a : ℕ) : ZMod p) = -(a : ZMod p) := by
          rw [show 2*h+1-a = p - a by omega, Nat.cast_sub hle, hp0, zero_sub]
        show ((a:ZMod p)⁻¹)^2 = (((2*h+1-a:ℕ):ZMod p)⁻¹)^2
        rw [hcast]; ring
    rw [hrefl]; ring
  rw [hsplit] at hfull
  have h2 : (2 : ZMod p) ≠ 0 := by
    rw [Ne, show (2:ZMod p) = ((2:ℕ):ZMod p) by norm_cast, CharP.cast_eq_zero_iff (ZMod p) p]
    intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
  exact (mul_eq_zero.mp hfull).resolve_left h2

/-- Pairing identity: `block p t` as a product of paired terms. -/
lemma block_pair (p t : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    (block p t : ℤ)
      = ∏ k ∈ Finset.Icc 1 ((p-1)/2), (((k : ℤ) * ((p:ℤ) - k)) + (t:ℤ)*(t+1)*(p:ℤ)^2) := by
  have hpp : 0 < p := hp.out.pos
  set h := (p-1)/2 with hh
  obtain ⟨m, hm⟩ := hp.out.odd_of_ne_two (by omega)
  have hhm : p - 1 = 2 * h := by rw [hh, hm]; omega
  rw [block_Icc, hhm]
  rw [show Finset.Icc 1 (2*h) = Finset.Icc 1 h ∪ Finset.Icc (h+1) (2*h) by
      ext x; rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]; omega]
  rw [Finset.prod_union (by
      rw [Finset.disjoint_left]; intro a ha hb
      rw [Finset.mem_Icc] at ha hb; omega)]
  -- reflect the second half onto the first
  have hrefl : ∏ j ∈ Finset.Icc (h+1) (2*h), ((t:ℤ)*p + j)
      = ∏ k ∈ Finset.Icc 1 h, ((t:ℤ)*p + (p - k)) := by
    refine Finset.prod_nbij' (fun j => 2*h+1-j) (fun k => 2*h+1-k) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha
      show ((t:ℤ)*p + a) = (t:ℤ)*p + ((p:ℤ) - (2*h+1-a : ℕ))
      have : ((2*h+1-a : ℕ) : ℤ) = (p:ℤ) - a := by
        rw [show 2*h+1-a = p - a by omega, Nat.cast_sub (by omega)]
      rw [this]; ring
  rw [hrefl, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k hk; rw [Finset.mem_Icc] at hk
  push_cast; ring

/-- `block p 0 = (p-1)!`. -/
lemma block_zero (p : ℕ) : block p 0 = Nat.factorial (p-1) := by
  rw [block]
  simp only [Nat.zero_mul, Nat.zero_add]
  exact prod_range_add_one (p-1)

/-- First-order expansion of `∏(aᵢ + w)` modulo `N`, when `N ∣ w²`. -/
lemma prod_add_modeq {ι : Type*} [DecidableEq ι] (w N : ℤ) (hw : N ∣ w^2) :
    ∀ (s : Finset ι) (a : ι → ℤ),
    (∏ i ∈ s, (a i + w)) ≡ (∏ i ∈ s, a i) + w * ∑ i ∈ s, ∏ j ∈ s.erase i, a j [ZMOD N] := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro a; simp
  | @insert j s hjs ih =>
    intro a
    rw [Finset.prod_insert hjs, Finset.prod_insert hjs, Finset.sum_insert hjs,
        Finset.erase_insert hjs]
    have hsum : ∑ i ∈ s, ∏ x ∈ (insert j s).erase i, a x
        = a j * ∑ i ∈ s, ∏ x ∈ s.erase i, a x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.erase_insert_of_ne (by rintro rfl; exact hjs hi),
          Finset.prod_insert (by simp only [Finset.mem_erase]; tauto)]
    rw [hsum]
    refine Int.ModEq.trans ((ih a).mul_left (a j + w)) ?_
    refine Int.modEq_iff_dvd.mpr ?_
    have hrw : (a j * ∏ i ∈ s, a i + w * (∏ i ∈ s, a i + a j * ∑ i ∈ s, ∏ x ∈ s.erase i, a x))
        - (a j + w) * (∏ i ∈ s, a i + w * ∑ i ∈ s, ∏ x ∈ s.erase i, a x)
        = -(w^2 * ∑ i ∈ s, ∏ x ∈ s.erase i, a x) := by ring
    rw [hrw]
    exact (dvd_neg).mpr (hw.mul_right _)

/-- Block congruence: `block p t ≡ (p-1)! (mod p³)`. -/
lemma block_cong (p t : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    (p : ℤ)^3 ∣ (block p t : ℤ) - (Nat.factorial (p-1) : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpp : 0 < p := hp.pos
  set h := (p-1)/2 with hh
  set A : ℕ → ℤ := fun k => (k : ℤ) * ((p:ℤ) - k) with hA
  set w : ℤ := (t:ℤ)*(t+1)*(p:ℤ)^2 with hw
  -- (i) ∏ A = (p-1)!
  have hprodA : ∏ k ∈ Finset.Icc 1 h, A k = (Nat.factorial (p-1) : ℤ) := by
    have hb0 := block_pair p 0 h5
    rw [block_zero] at hb0
    simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, add_zero] at hb0
    exact hb0.symm
  -- (ii) block = ∏(A + w)
  have hblock : (block p t : ℤ) = ∏ k ∈ Finset.Icc 1 h, (A k + w) := block_pair p t h5
  -- (iii) p ∣ S₁
  set S₁ : ℤ := ∑ k ∈ Finset.Icc 1 h, ∏ j ∈ (Finset.Icc 1 h).erase k, A j with hS
  have hpS : (p:ℤ) ∣ S₁ := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast [hS, hA]
    have hAne : ∀ k ∈ Finset.Icc 1 h, ((k : ZMod p) * ((p:ZMod p) - k)) ≠ 0 := by
      intro k hk; rw [Finset.mem_Icc] at hk
      have hk0 : (k:ZMod p) ≠ 0 := by
        rw [ne_eq, CharP.cast_eq_zero_iff (ZMod p) p]
        intro hd; have := Nat.le_of_dvd (by omega) hd; omega
      have hpk0 : ((p:ZMod p) - k) ≠ 0 := by
        rw [show (p:ZMod p) = 0 from by exact_mod_cast ZMod.natCast_self p, zero_sub, neg_ne_zero]
        exact hk0
      exact mul_ne_zero hk0 hpk0
    have hstep : ∀ k ∈ Finset.Icc 1 h, ∏ j ∈ (Finset.Icc 1 h).erase k, ((j : ZMod p) * ((p:ZMod p) - j))
        = (∏ j ∈ Finset.Icc 1 h, ((j : ZMod p) * ((p:ZMod p) - j))) * ((k : ZMod p) * ((p:ZMod p) - k))⁻¹ := by
      intro k hk
      rw [eq_comm, mul_comm, ← Finset.mul_prod_erase _ _ hk, ← mul_assoc,
          inv_mul_cancel₀ (hAne k hk), one_mul]
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, wolstenholme_half p h5, mul_zero]
  -- assemble
  rw [hblock, ← hprodA]
  have hmod := prod_add_modeq w ((p:ℤ)^3) (by
      rw [hw]; ring_nf
      exact ⟨(t:ℤ)^2*(t+1)^2*(p:ℤ), by ring⟩) (Finset.Icc 1 h) A
  rw [Int.modEq_iff_dvd] at hmod ⊢
  have : (∏ k ∈ Finset.Icc 1 h, A k + w * S₁) - ∏ k ∈ Finset.Icc 1 h, (A k + w)
      = -(∏ k ∈ Finset.Icc 1 h, (A k + w) - (∏ k ∈ Finset.Icc 1 h, A k + w * S₁)) := by
    rw [hS]; ring
  -- p³ ∣ block - (p-1)! : split via wS₁ and hmod
  have hwS : (p:ℤ)^3 ∣ w * S₁ := by
    rw [hw]; obtain ⟨c, hc⟩ := hpS
    exact ⟨(t:ℤ)*(t+1)*c, by rw [hc]; ring⟩
  have key : (p:ℤ)^3 ∣ (∏ k ∈ Finset.Icc 1 h, (A k + w)) - ∏ k ∈ Finset.Icc 1 h, A k := by
    have h1 : (∏ k ∈ Finset.Icc 1 h, (A k + w)) - ∏ k ∈ Finset.Icc 1 h, A k
        = ((∏ k ∈ Finset.Icc 1 h, A k + w * S₁) - ∏ k ∈ Finset.Icc 1 h, A k)
          + ((∏ k ∈ Finset.Icc 1 h, (A k + w)) - (∏ k ∈ Finset.Icc 1 h, A k + w * S₁)) := by
      rw [hS]; ring
    rw [h1]
    refine dvd_add ?_ hmod
    have : (∏ k ∈ Finset.Icc 1 h, A k + w * S₁) - ∏ k ∈ Finset.Icc 1 h, A k = w * S₁ := by ring
    rw [this]; exact hwS
  exact key

/-- Crux supercongruence, stated via p-adic valuation on ℚ. -/
lemma crux (p m : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hm : 0 < m) :
    (3 * (1 + padicValNat p m) : ℤ) ≤ padicValRat p (Rrat (m * p) / Rrat m - 1) := by
  sorry

lemma single (p m : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hm : 0 < m)
    (hRint : ∀ k, ∃ z : ℤ, (z : ℚ) = Rrat k)
    (D : ℤ) (hD : (D : ℚ) = Rrat (m * p) - Rrat m) :
    (p : ℤ) ^ (3 * (1 + padicValNat p m)) ∣ D := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Nm, hNm⟩ := hRint m
  obtain ⟨Nmp, hNmp⟩ := hRint (m * p)
  have hRm : Rrat m ≠ 0 := (Rrat_pos m).ne'
  have hDeq : D = Nmp - Nm := by
    have : ((D : ℚ)) = ((Nmp - Nm : ℤ) : ℚ) := by
      rw [hD]; push_cast; rw [hNm, hNmp]
    exact_mod_cast this
  rw [padicValInt_dvd_iff (3 * (1 + padicValNat p m)) D]
  by_cases hD0 : D = 0
  · left; exact hD0
  · right
    -- work with padicValRat
    have hphi : Rrat (m * p) - Rrat m = Rrat m * (Rrat (m * p) / Rrat m - 1) := by
      field_simp
    have hDQ : (D : ℚ) = Rrat m * (Rrat (m * p) / Rrat m - 1) := by rw [hD, hphi]
    have hne : Rrat (m * p) / Rrat m - 1 ≠ 0 := by
      intro h
      apply hD0
      have : (D : ℚ) = 0 := by rw [hDQ, h, mul_zero]
      exact_mod_cast this
    have hval : padicValRat p (D : ℚ) = padicValRat p (Rrat m) + padicValRat p (Rrat (m * p) / Rrat m - 1) := by
      rw [hDQ, padicValRat.mul hRm hne]
    have hInt : padicValRat p (D : ℚ) = (padicValInt p D : ℤ) := padicValRat.of_int
    have hRmnn : (0 : ℤ) ≤ padicValRat p (Rrat m) := by
      rw [← hNm, padicValRat.of_int]
      exact_mod_cast Nat.zero_le _
    have hc := crux p m hp h5 hm
    -- combine
    have : (3 * (1 + padicValNat p m) : ℤ) ≤ padicValRat p (D : ℚ) := by
      rw [hval]; linarith
    rw [hInt] at this
    exact_mod_cast this
