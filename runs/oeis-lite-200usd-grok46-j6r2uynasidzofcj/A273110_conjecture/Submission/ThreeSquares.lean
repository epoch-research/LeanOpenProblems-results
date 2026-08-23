import FormalConjectures.Util.ProblemImports

/-
  Three-square theorem via:
  * characterisation of sums of two rational squares
  * Legendre's theorem on the conic X^2 - d Y^2 = N Z^2 (descent)
  * Dirichlet production of an auxiliary prime
  * Fermat's two-square theorem
-/

open scoped NumberTheorySymbols
open Nat Int

/- Clearing denominators -/

lemma rat_mul_den_eq_num (t : ℚ) : (t : ℚ) * t.den = t.num := by
  have hmul : (t : ℚ) * t.den = (t.num / t.den : ℚ) * t.den :=
    congrArg (· * (t.den : ℚ)) t.num_div_den.symm
  have : (t.num / t.den : ℚ) * t.den = t.num :=
    div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr t.den_pos.ne')
  rwa [this] at hmul

lemma natAbs_sq_eq (a : ℤ) : (a.natAbs : ℤ) ^ 2 = a ^ 2 := by
  rw [Int.natCast_natAbs, sq_abs]

/-- Clearing denominators for a sum of three rational squares. -/
lemma three_rat_sq_clear {n : ℕ} {t x y : ℚ} (ht : (n : ℚ) = t ^ 2 + x ^ 2 + y ^ 2) :
    ∃ a b c d : ℕ, 0 < d ∧ a ^ 2 + b ^ 2 + c ^ 2 = n * d ^ 2 := by
  let D : ℤ := t.den * x.den * y.den
  have hDpos : 0 < D :=
    Int.natCast_pos.mpr (mul_pos (mul_pos t.den_pos x.den_pos) y.den_pos)
  have htD : (t * D : ℚ) = t.num * x.den * y.den := by
    simp only [D, Int.cast_mul, Int.cast_natCast]
    have := rat_mul_den_eq_num t
    linear_combination (x.den : ℚ) * (y.den : ℚ) * this
  have hxD : (x * D : ℚ) = x.num * t.den * y.den := by
    simp only [D, Int.cast_mul, Int.cast_natCast]
    have := rat_mul_den_eq_num x
    linear_combination (t.den : ℚ) * (y.den : ℚ) * this
  have hyD : (y * D : ℚ) = y.num * t.den * x.den := by
    simp only [D, Int.cast_mul, Int.cast_natCast]
    have := rat_mul_den_eq_num y
    linear_combination (t.den : ℚ) * (x.den : ℚ) * this
  have hsumQ : ((t * D) ^ 2 + (x * D) ^ 2 + (y * D) ^ 2 : ℚ) = n * D ^ 2 := by
    rw [ht]; ring
  rw [htD, hxD, hyD] at hsumQ
  have hsumZ : (t.num * x.den * y.den : ℤ) ^ 2 + (x.num * t.den * y.den) ^ 2 +
      (y.num * t.den * x.den) ^ 2 = n * D ^ 2 := by
    exact_mod_cast hsumQ
  refine ⟨(t.num * x.den * y.den).natAbs,
          (x.num * t.den * y.den).natAbs,
          (y.num * t.den * x.den).natAbs,
          D.natAbs, Int.natAbs_pos.mpr hDpos.ne', ?_⟩
  apply Int.natCast_inj.mp
  push_cast
  simp only [sq_abs, abs_of_pos hDpos]
  exact hsumZ

/- Two rational squares -/

lemma padicValNat_eq_zero_or {p a b : ℕ} [Fact p.Prime]
    (hcop : Nat.Coprime a b) :
    padicValNat p a = 0 ∨ padicValNat p b = 0 := by
  by_contra h
  push_neg at h
  have ha0 : a ≠ 0 := fun ha => by simp [ha] at h
  have hb0 : b ≠ 0 := fun hb => by simp [hb] at h
  have hpdvd_a : p ∣ a := (dvd_iff_padicValNat_ne_zero ha0).mpr h.1
  have hpdvd_b : p ∣ b := (dvd_iff_padicValNat_ne_zero hb0).mpr h.2
  exact Nat.not_coprime_of_dvd_of_dvd (Fact.out (p := p.Prime)).one_lt hpdvd_a hpdvd_b hcop

lemma rat_eq_sq_add_sq_of_val {r : ℚ} (hr : 0 ≤ r)
    (hv : ∀ p : ℕ, p.Prime → p % 4 = 3 → Even (padicValRat p r)) :
    ∃ x y : ℚ, r = x ^ 2 + y ^ 2 := by
  rcases eq_or_ne r 0 with rfl | hne
  · exact ⟨0, 0, by simp⟩
  have hnum : 0 < r.num := Rat.num_pos.mpr (lt_of_le_of_ne hr hne.symm)
  have hcop : Nat.Coprime r.num.natAbs r.den := r.reduced
  have hval : ∀ p : ℕ, p.Prime → p % 4 = 3 →
      Even (padicValNat p r.num.natAbs) ∧ Even (padicValNat p r.den) := by
    intro p hp hp3
    haveI : Fact p.Prime := ⟨hp⟩
    have hpr : Even (padicValRat p r) := hv p hp hp3
    have hform : padicValRat p r =
        (padicValNat p r.num.natAbs : ℤ) - padicValNat p r.den := by
      rw [padicValRat_def, padicValInt]
    have hnd := padicValNat_eq_zero_or (p := p) hcop
    rw [hform] at hpr
    rcases hnd with hn0 | hd0
    · constructor
      · simp [hn0]
      · have : Even ((0 : ℤ) - (padicValNat p r.den : ℤ)) := by simpa [hn0] using hpr
        simpa using this
    · constructor
      · have : Even ((padicValNat p r.num.natAbs : ℤ) - 0) := by simpa [hd0] using hpr
        simpa using this
      · simp [hd0]
  have hN : ∃ a b : ℕ, r.num.natAbs = a ^ 2 + b ^ 2 := by
    refine (Nat.eq_sq_add_sq_iff).2 ?_
    intro q hq hq3
    exact (hval q (Nat.prime_of_mem_primeFactors hq) hq3).1
  have hD : ∃ c d : ℕ, r.den = c ^ 2 + d ^ 2 := by
    refine (Nat.eq_sq_add_sq_iff).2 ?_
    intro q hq hq3
    exact (hval q (Nat.prime_of_mem_primeFactors hq) hq3).2
  obtain ⟨a, b, hab⟩ := hN
  obtain ⟨c, d, hcd⟩ := hD
  refine ⟨((a : ℚ) * c - b * d) / ((c : ℚ) ^ 2 + d ^ 2),
          ((a : ℚ) * d + b * c) / ((c : ℚ) ^ 2 + d ^ 2), ?_⟩
  have hden0 : ((c : ℚ) ^ 2 + d ^ 2) ≠ 0 := by
    have : 0 < r.den := r.den_pos
    have : 0 < (c : ℕ) ^ 2 + d ^ 2 := by simpa [hcd] using this
    exact_mod_cast this.ne'
  have hnn : (r.num : ℚ) = (r.num.natAbs : ℚ) := by
    rw [← Int.cast_natCast]
    exact congrArg Int.cast (Int.natAbs_of_nonneg hnum.le).symm
  have hr' : r = (r.num.natAbs : ℚ) / r.den := by
    calc r = (r.num : ℚ) / r.den := (Rat.num_div_den r).symm
      _ = (r.num.natAbs : ℚ) / r.den := by rw [hnn]
  have : r = ((a : ℚ) ^ 2 + b ^ 2) / ((c : ℚ) ^ 2 + d ^ 2) := by
    rw [hr', hab, hcd]; norm_cast
  rw [this]
  field_simp
  ring

lemma even_padicValRat_of_sq_add_sq {r x y : ℚ} (h : r = x ^ 2 + y ^ 2)
    {p : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3) :
    Even (padicValRat p r) := by
  rcases eq_or_ne r 0 with rfl | hne
  · simp [padicValRat.zero]
  haveI : Fact p.Prime := ⟨hp⟩
  let D : ℕ := x.den * y.den
  have hDpos : 0 < D := mul_pos x.den_pos y.den_pos
  have hDne : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hxD : (x : ℚ) * x.den = x.num := rat_mul_den_eq_num x
  have hyD : (y : ℚ) * y.den = y.num := rat_mul_den_eq_num y
  have hclear : r * (D : ℚ) ^ 2 =
      (x.num * y.den : ℚ) ^ 2 + (y.num * x.den : ℚ) ^ 2 := by
    calc r * (D : ℚ) ^ 2
        = (x ^ 2 + y ^ 2) * (x.den * y.den : ℚ) ^ 2 := by rw [h]; simp [D]
      _ = (x * x.den) ^ 2 * (y.den : ℚ) ^ 2 + (y * y.den) ^ 2 * (x.den : ℚ) ^ 2 := by
          ring
      _ = (x.num : ℚ) ^ 2 * (y.den : ℚ) ^ 2 + (y.num : ℚ) ^ 2 * (x.den : ℚ) ^ 2 := by
          rw [hxD, hyD]
      _ = (x.num * y.den : ℚ) ^ 2 + (y.num * x.den : ℚ) ^ 2 := by ring
  set A : ℤ := x.num * y.den
  set B : ℤ := y.num * x.den
  have hAB : (x.num * y.den : ℚ) ^ 2 + (y.num * x.den : ℚ) ^ 2 =
      (A : ℚ) ^ 2 + (B : ℚ) ^ 2 := by simp [A, B]
  set N : ℕ := A.natAbs ^ 2 + B.natAbs ^ 2
  have hN : (A : ℚ) ^ 2 + (B : ℚ) ^ 2 = (N : ℚ) := by
    push_cast; simp [N, sq_abs]
  have hNpos : N ≠ 0 := by
    intro hZ
    have : r * (D : ℚ) ^ 2 = 0 := by
      rw [hclear, hAB, hN, hZ]; simp
    have : r = 0 := (mul_eq_zero.mp this).resolve_right (by positivity)
    exact hne this
  have hNeven : Even (padicValNat p N) := by
    have hex : ∃ u v, N = u ^ 2 + v ^ 2 := ⟨A.natAbs, B.natAbs, rfl⟩
    have := (Nat.eq_sq_add_sq_iff (n := N)).1 hex
    by_cases hmem : p ∈ N.primeFactors
    · exact this p hmem hp3
    · have : padicValNat p N = 0 :=
        padicValNat.eq_zero_of_not_dvd fun hdvd =>
          hmem (Nat.mem_primeFactors.mpr ⟨hp, hdvd, hNpos⟩)
      simp [this]
  have hmul : padicValRat p (r * (D : ℚ) ^ 2) =
      padicValRat p r + 2 * padicValRat p D := by
    rw [padicValRat.mul hne (pow_ne_zero 2 hDne), padicValRat.pow hDne]
    ring
  have hNval : padicValRat p (r * (D : ℚ) ^ 2) = padicValNat p N := by
    rw [hclear, hAB, hN, padicValRat.of_nat]
  have hsum : Even (padicValRat p r + 2 * padicValRat p D) := by
    rw [← hmul, hNval]
    exact (Int.even_coe_nat _).mpr hNeven
  have h2 : Even (2 * padicValRat p D) := even_two_mul _
  have hiff : Even (padicValRat p r) ↔ Even (2 * padicValRat p D) :=
    Int.even_add.mp hsum
  exact hiff.mpr h2

lemma rat_eq_sq_add_sq_iff {r : ℚ} :
    (∃ x y : ℚ, r = x ^ 2 + y ^ 2) ↔
      0 ≤ r ∧ ∀ p : ℕ, p.Prime → p % 4 = 3 → Even (padicValRat p r) := by
  constructor
  · rintro ⟨x, y, h⟩
    refine ⟨?_, fun p hp hp3 => even_padicValRat_of_sq_add_sq h hp hp3⟩
    rw [h]; nlinarith [sq_nonneg x, sq_nonneg y]
  · rintro ⟨hr, hv⟩
    exact rat_eq_sq_add_sq_of_val hr hv

/- Squares modulo n via CRT -/

lemma zmod_cast_int_fst {a b : ℕ} (hcop : a.Coprime b) (n : ℤ) :
    ((ZMod.chineseRemainder hcop) (n : ZMod (a * b))).1 = (n : ZMod a) := by
  simp [ZMod.chineseRemainder]

lemma zmod_cast_int_snd {a b : ℕ} (hcop : a.Coprime b) (n : ℤ) :
    ((ZMod.chineseRemainder hcop) (n : ZMod (a * b))).2 = (n : ZMod b) := by
  simp [ZMod.chineseRemainder]

lemma isSquare_mod_mul {a b : ℕ} (hcop : a.Coprime b) {n : ℤ}
    (h1 : IsSquare (n : ZMod a)) (h2 : IsSquare (n : ZMod b)) :
    IsSquare (n : ZMod (a * b)) := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  let e := ZMod.chineseRemainder hcop
  refine ⟨e.symm (x, y), ?_⟩
  have hprod : (x, y) * (x, y) = ((n : ZMod a), (n : ZMod b)) := by
    ext <;> simp [hx, hy]
  have : e (e.symm (x, y) * e.symm (x, y)) = e (n : ZMod (a * b)) := by
    rw [map_mul, e.apply_symm_apply, hprod]
    ext
    · simp [zmod_cast_int_fst hcop n]
    · simp [zmod_cast_int_snd hcop n]
  exact e.injective this.symm

lemma isSquare_mod_one (n : ℤ) : IsSquare (n : ZMod 1) := by
  refine ⟨0, ?_⟩
  have : Subsingleton (ZMod 1) := inferInstance
  exact Subsingleton.elim _ _

/-- A balanced representative of a square root modulo `d`. -/
lemma exists_int_sq_mod {N : ℤ} {d : ℕ} (hd : 0 < d)
    (h : IsSquare (N : ZMod d)) :
    ∃ s : ℤ, s ^ 2 ≡ N [ZMOD d] ∧ 2 * |s| ≤ d := by
  obtain ⟨x, hx⟩ := h
  haveI : NeZero d := ⟨hd.ne'⟩
  let s0 : ℤ := x.val
  have hs0 : (s0 : ZMod d) = x := by
    unfold s0
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val x
  have hsq : ((s0 ^ 2 : ℤ) : ZMod d) = (N : ZMod d) := by
    rw [pow_two, Int.cast_mul, hs0, hx]
  have hmod : s0 ^ 2 ≡ N [ZMOD d] :=
    (ZMod.intCast_eq_intCast_iff (s0 ^ 2) N d).mp hsq
  have hs0_nonneg : 0 ≤ s0 := by unfold s0; exact Int.natCast_nonneg _
  have hs0_lt : s0 < (d : ℤ) := by
    unfold s0
    exact Int.ofNat_lt.mpr (ZMod.val_lt x)
  by_cases hle : 2 * s0 ≤ d
  · exact ⟨s0, hmod, by rwa [abs_of_nonneg hs0_nonneg]⟩
  · refine ⟨s0 - d, ?_, ?_⟩
    · have : (s0 - (d : ℤ)) ^ 2 ≡ s0 ^ 2 [ZMOD d] := by
        refine Int.modEq_iff_dvd.mpr ?_
        refine ⟨2 * s0 - d, ?_⟩
        ring
      exact this.trans hmod
    · have hneg : s0 - (d : ℤ) ≤ 0 := by linarith
      rw [abs_of_nonpos hneg]
      linarith

lemma isSquare_mod_of_primes {n : ℕ} {a : ℤ} (hn : 0 < n)
    (hsq : Squarefree n)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → IsSquare (a : ZMod p)) :
    IsSquare (a : ZMod n) := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    rcases n.eq_zero_or_pos with rfl | hn'
    · exact (lt_irrefl 0 hn).elim
    rcases eq_or_ne n 1 with rfl | hn1
    · exact isSquare_mod_one a
    obtain ⟨p, hp, hpdvd⟩ := n.exists_prime_and_dvd hn1
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨m, hm⟩ := hpdvd
    have hmpos : 0 < m :=
      Nat.pos_of_ne_zero fun hm0 => by
        subst hm0
        simp at hm
        exact hn'.ne' hm
    have hp_ndvd : ¬ p ∣ m := by
      intro hpm
      have : p * p ∣ n := by
        rw [hm]; exact mul_dvd_mul_left p hpm
      exact (squarefree_iff_prime_squarefree.mp hsq) p hp this
    have hcop : p.Coprime m := hp.coprime_iff_not_dvd.mpr hp_ndvd
    have hsfm : Squarefree m := by
      have : m ∣ n := ⟨p, by rw [hm, mul_comm]⟩
      exact hsq.squarefree_of_dvd this
    have hsfp : Squarefree p := hp.squarefree
    have hsp : IsSquare (a : ZMod p) := h p hp (by rw [hm]; exact dvd_mul_right _ _)
    have hsm : IsSquare (a : ZMod m) := by
      refine ih m ?_ hmpos hsfm ?_
      · rw [hm]; exact (Nat.lt_mul_iff_one_lt_left hmpos).mpr hp.one_lt
      · intro q hq hqd
        exact h q hq (hqd.trans ⟨p, by rw [hm, mul_comm]⟩)
    have := isSquare_mod_mul hcop hsp hsm
    rwa [hm]

/- Composition identity for the conic -/

lemma conic_identity (s N x z : ℤ) :
    (s ^ 2 - N) * (x ^ 2 - N * z ^ 2) =
      (s * x + N * z) ^ 2 - N * (s * z + x) ^ 2 := by
  ring

lemma conic_compose (s N x z m y d : ℤ)
    (hs : s ^ 2 - N = d * m) (hx : x ^ 2 - N * z ^ 2 = m * y ^ 2) :
    (s * x + N * z) ^ 2 - d * (m * y) ^ 2 = N * (s * z + x) ^ 2 := by
  have hid := conic_identity s N x z
  have : (s * x + N * z) ^ 2 - N * (s * z + x) ^ 2 = d * (m * y) ^ 2 := by
    calc
      (s * x + N * z) ^ 2 - N * (s * z + x) ^ 2
          = (s ^ 2 - N) * (x ^ 2 - N * z ^ 2) := hid.symm
      _ = (d * m) * (m * y ^ 2) := by rw [hs, hx]
      _ = d * (m * y) ^ 2 := by ring
  linarith

/- Square-free kernel -/

/-- The square-free kernel of `n`: `n = sqFreeKernel n * (floorRoot 2 n)^2`. -/
def sqFreeKernel (n : ℕ) : ℕ := n / floorRoot 2 n ^ 2

lemma n_eq_sqFreeKernel_mul_sq (n : ℕ) :
    sqFreeKernel n * floorRoot 2 n ^ 2 = n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [sqFreeKernel]
  simpa [sqFreeKernel] using Nat.div_mul_cancel (floorRoot_pow_dvd (n := 2) (a := n))

lemma sqFreeKernel_ne_zero {n : ℕ} (hn : n ≠ 0) : sqFreeKernel n ≠ 0 := by
  intro hz
  have := n_eq_sqFreeKernel_mul_sq n
  simp [hz] at this
  exact hn this.symm

lemma factorization_sqFreeKernel (n : ℕ) (hn : n ≠ 0) (p : ℕ) :
    (sqFreeKernel n).factorization p = n.factorization p % 2 := by
  set K := sqFreeKernel n
  set F := floorRoot 2 n
  have h : K * F ^ 2 = n := n_eq_sqFreeKernel_mul_sq n
  have hk : K ≠ 0 := sqFreeKernel_ne_zero hn
  have hfr : F ≠ 0 := floorRoot_ne_zero.mpr ⟨by decide, hn⟩
  have hfr2 : F ^ 2 ≠ 0 := pow_ne_zero 2 hfr
  have hsum : n.factorization = K.factorization + 2 • F.factorization := by
    rw [← h, Nat.factorization_mul hk hfr2, Nat.factorization_pow]
  have hp : n.factorization p = K.factorization p + 2 * F.factorization p := by
    simpa [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
      using congrArg (fun f : ℕ →₀ ℕ => f p) hsum
  have hdiv : F.factorization p = n.factorization p / 2 := by
    simp [F, factorization_floorRoot, Finsupp.floorDiv_apply, Nat.floorDiv_eq_div]
  rw [hdiv] at hp
  simp [K] at hp ⊢
  omega

lemma squarefree_sqFreeKernel_of_pos {n : ℕ} (hn : 0 < n) :
    Squarefree (sqFreeKernel n) := by
  refine (squarefree_iff_factorization_le_one (sqFreeKernel_ne_zero hn.ne')).2 ?_
  intro p
  have := factorization_sqFreeKernel n hn.ne' p
  omega

/- Legendre's theorem on the conic X² - d Y² = N Z² -/

/-- The local (elementary) conditions for the conic `X^2 - d Y^2 - N Z^2 = 0`. -/
def ConicLocal (d N : ℤ) : Prop :=
  (0 < d ∨ 0 < N) ∧
  (d = 0 ∨ IsSquare (N : ZMod d.natAbs)) ∧
  (N = 0 ∨ IsSquare (d : ZMod N.natAbs))

lemma ConicLocal.swap {d N : ℤ} (h : ConicLocal d N) : ConicLocal N d := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1.symm, h3, h2⟩

/-- Trivial solution when `N` is a square. -/
lemma conic_sol_of_isSquare_N {d N : ℤ} (hN : IsSquare N) :
    ∃ X Y Z : ℤ, X ^ 2 - d * Y ^ 2 = N * Z ^ 2 ∧ (X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0) := by
  obtain ⟨s, hs⟩ := hN
  refine ⟨s, 0, 1, ?_, by simp⟩
  simp [hs, sq]

lemma conic_sol_of_isSquare_d {d N : ℤ} (hd : IsSquare d) :
    ∃ X Y Z : ℤ, X ^ 2 - d * Y ^ 2 = N * Z ^ 2 ∧ (X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0) := by
  obtain ⟨s, hs⟩ := hd
  refine ⟨s, 1, 0, ?_, by simp⟩
  simp [hs, sq]

lemma conic_sol_of_N_eq_one (d : ℤ) :
    ∃ X Y Z : ℤ, X ^ 2 - d * Y ^ 2 = (1 : ℤ) * Z ^ 2 ∧ (X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0) :=
  ⟨1, 0, 1, by ring, by simp⟩

lemma conic_sol_of_d_eq_one (N : ℤ) :
    ∃ X Y Z : ℤ, X ^ 2 - (1 : ℤ) * Y ^ 2 = N * Z ^ 2 ∧ (X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0) :=
  ⟨1, 1, 0, by ring, by simp⟩

/-- Strip squares from an integer: `n = sqFreeInt n * (intSqFactor n)^2`. -/
def intSqFactor (n : ℤ) : ℤ := floorRoot 2 n.natAbs

def sqFreeInt (n : ℤ) : ℤ := n.sign * sqFreeKernel n.natAbs

lemma n_eq_sqFreeInt_mul_sq (n : ℤ) :
    n = sqFreeInt n * intSqFactor n ^ 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [sqFreeInt, intSqFactor, sqFreeKernel]
  calc
    n = n.sign * n.natAbs := (Int.sign_mul_natAbs n).symm
    _ = n.sign * (sqFreeKernel n.natAbs * floorRoot 2 n.natAbs ^ 2 : ℕ) := by
        congr 1
        exact_mod_cast (n_eq_sqFreeKernel_mul_sq n.natAbs).symm
    _ = (n.sign * (sqFreeKernel n.natAbs : ℤ)) * (floorRoot 2 n.natAbs : ℤ) ^ 2 := by
        push_cast; ring
    _ = sqFreeInt n * intSqFactor n ^ 2 := rfl

lemma sqFreeInt_natAbs (n : ℤ) (hn : n ≠ 0) :
    (sqFreeInt n).natAbs = sqFreeKernel n.natAbs := by
  rw [sqFreeInt, Int.natAbs_mul, Int.natAbs_sign, if_neg hn]
  simp

lemma squarefree_sqFreeInt {n : ℤ} (hn : n ≠ 0) :
    Squarefree (sqFreeInt n).natAbs := by
  rw [sqFreeInt_natAbs n hn]
  exact squarefree_sqFreeKernel_of_pos (Int.natAbs_pos.mpr hn)
