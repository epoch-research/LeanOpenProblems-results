import FormalConjecturesUtil

/-!
# Erdős Problem 126

*Reference:* [erdosproblems.com/126](https://www.erdosproblems.com/126)

Proof (elementary): every finite set `A` with `n` elements has at least `(n/40)^(1/4)` distinct
primes dividing `∏_{a ≠ b ∈ A} (a+b)`.  The core is a polynomial bound on the size of a primitive
"S-unit clique" (all pairwise sums are `S`-units, `|S| = k`): `|A| ≤ 2k(1+8k(k+1)(k-1)) + 2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Filter

namespace E126


lemma log_eq_sum_fact (n : ℕ) (hn : n ≠ 0) (P : Finset ℕ) (hP : n.primeFactors ⊆ P) :
    Real.log n = ∑ p ∈ P, (n.factorization p : ℝ) * Real.log p := by
  have h1 : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
    have := Nat.factorization_prod_pow_eq_self hn
    conv_lhs => rw [← this]
    simp [Finsupp.prod, Nat.support_factorization]
  have h2 : Real.log n = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log p := by
    rw [h1, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro p hp
      rw [Real.log_pow]
    · intro p hp
      have : p ≠ 0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
      exact pow_ne_zero _ (by exact_mod_cast this)
  rw [h2]
  apply Finset.sum_subset hP
  intro p _ hp
  have : n.factorization p = 0 := by
    by_contra h
    apply hp
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr h
  simp [this]

lemma sum_fact_log_le (n : ℕ) (hn : n ≠ 0) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P, (n.factorization p : ℝ) * Real.log p ≤ Real.log n := by
  rw [log_eq_sum_fact n hn (P ∪ n.primeFactors) (Finset.subset_union_right)]
  apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
  intro p hp _
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Real.log_nonneg
  have : p ∈ P ∨ p ∈ n.primeFactors := Finset.mem_union.mp hp
  rcases this with h | h
  · exact_mod_cast (hP p h).one_lt.le
  · exact_mod_cast (Nat.prime_of_mem_primeFactors h).one_lt.le



/-- Mirror pairs vs. collision pairs: for every modulus `d`, the number of ordered pairs `(x,y) ∈ C²` with
`x + y ≡ 0 (mod d)` is at most the number with `x ≡ y (mod d)` (AM–GM on the residue-class counts). -/
lemma pair_count (C : Finset ℕ) (d : ℕ) [NeZero d] :
    ((C ×ˢ C).filter (fun p : ℕ × ℕ => ((p.1 : ZMod d) + p.2 = 0))).card ≤
    ((C ×ˢ C).filter (fun p : ℕ × ℕ => ((p.1 : ZMod d) = p.2))).card := by
  classical
  set cnt : ZMod d → ℕ := fun r => (C.filter (fun x : ℕ => (x : ZMod d) = r)).card with hcnt
  -- general fiber sum
  have fib : ∀ (g : ZMod d → ℕ), ∑ x ∈ C, g (x : ZMod d) = ∑ r : ZMod d, cnt r * g r := by
    intro g
    rw [← Finset.sum_fiberwise C (fun x : ℕ => (x : ZMod d)) (fun x => g (x : ZMod d))]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_congr rfl (g := fun _ => g r)]
    · simp [hcnt]
    · intro x hx
      have := (Finset.mem_filter.mp hx).2
      rw [this]
  have hL : ((C ×ˢ C).filter (fun p : ℕ × ℕ => ((p.1 : ZMod d) + p.2 = 0))).card
      = ∑ r : ZMod d, cnt r * cnt (-r) := by
    rw [Finset.card_filter, Finset.sum_product]
    have : ∀ x ∈ C, (∑ y ∈ C, if ((x : ZMod d) + (y : ZMod d) = 0) then 1 else 0) = cnt (-(x : ZMod d)) := by
      intro x _
      rw [← Finset.card_filter]
      simp only [hcnt]
      congr 1
      apply Finset.filter_congr
      intro y _
      constructor
      · intro h; exact (neg_eq_of_add_eq_zero_right h).symm
      · intro h; rw [h]; simp
    rw [Finset.sum_congr rfl this]
    exact fib (fun r => cnt (-r))
  have hR : ((C ×ˢ C).filter (fun p : ℕ × ℕ => ((p.1 : ZMod d) = p.2))).card
      = ∑ r : ZMod d, cnt r * cnt r := by
    rw [Finset.card_filter, Finset.sum_product]
    have : ∀ x ∈ C, (∑ y ∈ C, if ((x : ZMod d) = (y : ZMod d)) then 1 else 0) = cnt (x : ZMod d) := by
      intro x _
      rw [← Finset.card_filter]
      simp only [hcnt]
      congr 1
      apply Finset.filter_congr
      intro y _
      exact eq_comm
    rw [Finset.sum_congr rfl this]
    exact fib (fun r => cnt r)
  rw [hL, hR]
  have h2 : 2 * ∑ r : ZMod d, cnt r * cnt (-r) ≤ 2 * ∑ r : ZMod d, cnt r * cnt r := by
    have h3 : ∑ r : ZMod d, cnt (-r) * cnt (-r) = ∑ r : ZMod d, cnt r * cnt r :=
      Fintype.sum_equiv (Equiv.neg (ZMod d)) _ _ (fun r => rfl)
    calc 2 * ∑ r : ZMod d, cnt r * cnt (-r) = ∑ r : ZMod d, 2 * (cnt r * cnt (-r)) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ r : ZMod d, (cnt r * cnt r + cnt (-r) * cnt (-r)) := by
          apply Finset.sum_le_sum
          intro r _
          nlinarith [sq_nonneg ((cnt r : ℤ) - cnt (-r))]
      _ = ∑ r : ZMod d, cnt r * cnt r + ∑ r : ZMod d, cnt (-r) * cnt (-r) := Finset.sum_add_distrib
      _ = 2 * ∑ r : ZMod d, cnt r * cnt r := by rw [h3]; ring
  omega




lemma min_val_eq_card (p V n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    min (n.factorization p) V = ((Finset.Icc 1 V).filter (fun j => p ^ j ∣ n)).card := by
  have : (Finset.Icc 1 V).filter (fun j => p ^ j ∣ n) = Finset.Icc 1 (min (n.factorization p) V) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rw [hp.pow_dvd_iff_le_factorization hn]
    omega
  rw [this]
  simp

lemma sum_min_val (p V : ℕ) (hp : p.Prime) (s : Finset (ℕ × ℕ)) (n : ℕ × ℕ → ℕ)
    (hn : ∀ x ∈ s, n x ≠ 0) :
    ∑ x ∈ s, min ((n x).factorization p) V =
      ∑ j ∈ Finset.Icc 1 V, (s.filter (fun x => p ^ j ∣ n x)).card := by
  have h1 : ∀ x ∈ s, min ((n x).factorization p) V =
      ∑ j ∈ Finset.Icc 1 V, if p ^ j ∣ n x then 1 else 0 := by
    intro x hx
    rw [min_val_eq_card p V (n x) hp (hn x hx), Finset.card_filter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.card_filter]

/-- Truncated `p`-adic version of `pair_count`, summed over `j = 1..V`. -/
lemma val_ineq (C : Finset ℕ) (hC : ∀ x ∈ C, 0 < x) (p V : ℕ) (hp : p.Prime) :
    ∑ x ∈ C.offDiag, min (((x.1 + x.2 : ℕ)).factorization p) V ≤
    ∑ x ∈ C.offDiag, min ((Int.natAbs ((x.1:ℤ) - x.2)).factorization p) V + C.card * V := by
  classical
  have hne1 : ∀ x ∈ C.offDiag, (x.1 + x.2 : ℕ) ≠ 0 := by
    intro x hx
    have := hC x.1 (Finset.mem_offDiag.mp hx).1
    omega
  have hne2 : ∀ x ∈ C.offDiag, Int.natAbs ((x.1:ℤ) - x.2) ≠ 0 := by
    intro x hx
    have h := Finset.mem_offDiag.mp hx
    intro h0
    apply h.2.2
    have := Int.natAbs_eq_zero.mp h0
    exact_mod_cast (sub_eq_zero.mp this)
  rw [sum_min_val p V hp C.offDiag (fun x => x.1 + x.2) hne1,
      sum_min_val p V hp C.offDiag (fun x => Int.natAbs ((x.1:ℤ) - x.2)) hne2]
  have key : ∀ j ∈ Finset.Icc 1 V,
      (C.offDiag.filter (fun x => p ^ j ∣ x.1 + x.2)).card ≤
      (C.offDiag.filter (fun x => p ^ j ∣ Int.natAbs ((x.1:ℤ) - x.2))).card + C.card := by
    intro j _
    haveI : NeZero (p ^ j) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have h1 := pair_count C (p ^ j)
    -- translate
    have e1 : (C ×ˢ C).filter (fun q : ℕ × ℕ => ((q.1 : ZMod (p^j)) + q.2 = 0)) =
        (C ×ˢ C).filter (fun q : ℕ × ℕ => p ^ j ∣ q.1 + q.2) := by
      apply Finset.filter_congr
      intro q _
      rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
    have e2 : (C ×ˢ C).filter (fun q : ℕ × ℕ => ((q.1 : ZMod (p^j)) = q.2)) =
        (C ×ˢ C).filter (fun q : ℕ × ℕ => p ^ j ∣ Int.natAbs ((q.1:ℤ) - q.2)) := by
      apply Finset.filter_congr
      intro q _
      rw [ZMod.natCast_eq_natCast_iff, Nat.modEq_iff_dvd]
      constructor
      · intro h
        have := Int.natAbs_dvd_natAbs.mpr h
        simpa [Int.natAbs_natCast] using (by
          have h' : ((p ^ j : ℕ) : ℤ) ∣ ((q.1:ℤ) - q.2) := by
            have := dvd_neg.mpr h
            simpa using this
          exact Int.natCast_dvd.mp h')
      · intro h
        have h' : ((p ^ j : ℕ) : ℤ) ∣ ((q.1:ℤ) - q.2) := Int.natCast_dvd.mpr h
        have := dvd_neg.mpr h'
        simpa using this
    rw [e1, e2] at h1
    -- offDiag mirror ≤ product mirror
    have h2 : (C.offDiag.filter (fun x => p ^ j ∣ x.1 + x.2)).card ≤
        ((C ×ˢ C).filter (fun q : ℕ × ℕ => p ^ j ∣ q.1 + q.2)).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      have := Finset.mem_offDiag.mp hx.1
      exact ⟨Finset.mem_product.mpr ⟨this.1, this.2.1⟩, hx.2⟩
    have h3 : ((C ×ˢ C).filter (fun q : ℕ × ℕ => p ^ j ∣ Int.natAbs ((q.1:ℤ) - q.2))).card ≤
        (C.offDiag.filter (fun x => p ^ j ∣ Int.natAbs ((x.1:ℤ) - x.2))).card + C.card := by
      have hsub : (C ×ˢ C).filter (fun q : ℕ × ℕ => p ^ j ∣ Int.natAbs ((q.1:ℤ) - q.2)) ⊆
          (C.offDiag.filter (fun x => p ^ j ∣ Int.natAbs ((x.1:ℤ) - x.2))) ∪ C.diag := by
        intro x hx
        simp only [Finset.mem_filter] at hx
        rw [← Finset.diag_union_offDiag] at hx
        rcases Finset.mem_union.mp hx.1 with h | h
        · exact Finset.mem_union_right _ (by exact h)
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h, hx.2⟩)
      calc _ ≤ ((C.offDiag.filter (fun x => p ^ j ∣ Int.natAbs ((x.1:ℤ) - x.2))) ∪ C.diag).card :=
            Finset.card_le_card hsub
        _ ≤ _ := by
            apply (Finset.card_union_le _ _).trans
            rw [Finset.diag_card]
    omega
  calc ∑ j ∈ Finset.Icc 1 V, (C.offDiag.filter (fun x => p ^ j ∣ x.1 + x.2)).card
      ≤ ∑ j ∈ Finset.Icc 1 V, ((C.offDiag.filter (fun x => p ^ j ∣ Int.natAbs ((x.1:ℤ) - x.2))).card + C.card) :=
        Finset.sum_le_sum key
    _ = ∑ j ∈ Finset.Icc 1 V, (C.offDiag.filter (fun x => p ^ j ∣ Int.natAbs ((x.1:ℤ) - x.2))).card + C.card * V := by
        rw [Finset.sum_add_distrib]
        simp [mul_comm]

/-- **Mirror-ball bound.**  If the elements of `C` are pairwise congruent mod `q^F`, all pairwise sums have
exact `q`-valuation `G < F` and are `{q} ∪ Q`-units with `p`-valuations `≤ V p`, then
`(|C| - 1) (F - G) log q ≤ ∑_{p ∈ Q} V p log p`. -/
lemma lemmaC (C : Finset ℕ) (hC : ∀ x ∈ C, 0 < x) (q : ℕ) (hq : q.Prime) (F G : ℕ) (hGF : G < F)
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (hqQ : q ∉ Q)
    (hdiff : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → (q : ℤ) ^ F ∣ (x : ℤ) - y)
    (hsum : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → (x + y).factorization q = G)
    (hsmooth : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ∀ p, p.Prime → p ∣ x + y → p = q ∨ p ∈ Q)
    (V : ℕ → ℕ) (hV : ∀ p ∈ Q, ∀ x ∈ C, ∀ y ∈ C, x ≠ y → (x + y).factorization p ≤ V p) :
    ((C.card : ℝ) - 1) * ((F : ℝ) - G) * Real.log q ≤ ∑ p ∈ Q, (V p : ℝ) * Real.log p := by
  classical
  set m := C.card with hm
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hlogp : ∀ p ∈ Q, 0 ≤ Real.log p := by
    intro p hp
    exact Real.log_nonneg (by exact_mod_cast (hQ p hp).one_lt.le)
  have hqQ' : ∀ p ∈ insert q Q, p.Prime := by
    intro p hp
    rcases Finset.mem_insert.mp hp with h | h
    · rw [h]; exact hq
    · exact hQ p h
  -- notation
  let D : ℕ × ℕ → ℕ := fun x => Int.natAbs ((x.1:ℤ) - x.2)
  have hpos : ∀ x ∈ C.offDiag, 0 < x.1 ∧ 0 < x.2 ∧ x.1 ≠ x.2 := by
    intro x hx
    have h := Finset.mem_offDiag.mp hx
    exact ⟨hC _ h.1, hC _ h.2.1, h.2.2⟩
  have hD0 : ∀ x ∈ C.offDiag, D x ≠ 0 := by
    intro x hx
    have h := hpos x hx
    intro h0
    apply h.2.2
    have := Int.natAbs_eq_zero.mp h0
    exact_mod_cast (sub_eq_zero.mp this)
  -- (I)
  have hI : ∀ x ∈ C.offDiag, Real.log ((x.1 + x.2 : ℕ) : ℝ) =
      (G : ℝ) * Real.log q + ∑ p ∈ Q, (((x.1 + x.2 : ℕ)).factorization p : ℝ) * Real.log p := by
    intro x hx
    have h := hpos x hx
    have hne : (x.1 + x.2 : ℕ) ≠ 0 := by omega
    have hmem := Finset.mem_offDiag.mp hx
    have hsub : (x.1 + x.2 : ℕ).primeFactors ⊆ insert q Q := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hdvd := Nat.dvd_of_mem_primeFactors hp
      rcases hsmooth x.1 hmem.1 x.2 hmem.2.1 hmem.2.2 p hpp hdvd with h' | h'
      · exact Finset.mem_insert.mpr (Or.inl h')
      · exact Finset.mem_insert.mpr (Or.inr h')
    rw [log_eq_sum_fact _ hne (insert q Q) hsub, Finset.sum_insert hqQ,
      hsum x.1 hmem.1 x.2 hmem.2.1 hmem.2.2]
  -- (II)
  have hII : ∀ x ∈ C.offDiag, (F : ℝ) * Real.log q +
      ∑ p ∈ Q, ((min ((D x).factorization p) (V p) : ℕ) : ℝ) * Real.log p ≤ Real.log (D x : ℝ) := by
    intro x hx
    have hmem := Finset.mem_offDiag.mp hx
    have h1 := sum_fact_log_le (D x) (hD0 x hx) (insert q Q) hqQ'
    rw [Finset.sum_insert hqQ] at h1
    have hFle : F ≤ (D x).factorization q := by
      rw [← hq.pow_dvd_iff_le_factorization (hD0 x hx)]
      have := hdiff x.1 hmem.1 x.2 hmem.2.1 hmem.2.2
      have h2 : ((q ^ F : ℕ) : ℤ) ∣ ((x.1:ℤ) - x.2) := by exact_mod_cast this
      exact Int.natCast_dvd.mp h2
    have h2 : (F : ℝ) * Real.log q ≤ ((D x).factorization q : ℝ) * Real.log q :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hFle) hlogq.le
    have h3 : ∑ p ∈ Q, ((min ((D x).factorization p) (V p) : ℕ) : ℝ) * Real.log p ≤
        ∑ p ∈ Q, (((D x).factorization p : ℕ) : ℝ) * Real.log p := by
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_right _ (hlogp p hp)
      exact_mod_cast min_le_left _ _
    linarith
  -- (IV)
  have hIV : ∀ x ∈ C.offDiag, Real.log (D x : ℝ) ≤ Real.log ((x.1 + x.2 : ℕ) : ℝ) := by
    intro x hx
    have h := hpos x hx
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero (hD0 x hx)
    · have : D x ≤ x.1 + x.2 := by
        simp only [D]
        omega
      exact_mod_cast this
  -- (III)
  have hIII : ∀ p ∈ Q, ((∑ x ∈ C.offDiag, ((x.1 + x.2 : ℕ)).factorization p : ℕ) : ℝ) ≤
      ((∑ x ∈ C.offDiag, min ((D x).factorization p) (V p) : ℕ) : ℝ) + (m : ℝ) * (V p : ℝ) := by
    intro p hp
    have h1 := val_ineq C hC p (V p) (hQ p hp)
    have h2 : ∑ x ∈ C.offDiag, min (((x.1 + x.2 : ℕ)).factorization p) (V p) =
        ∑ x ∈ C.offDiag, ((x.1 + x.2 : ℕ)).factorization p := by
      apply Finset.sum_congr rfl
      intro x hx
      have hmem := Finset.mem_offDiag.mp hx
      exact min_eq_left (hV p hp x.1 hmem.1 x.2 hmem.2.1 hmem.2.2)
    rw [h2] at h1
    have h3 : (∑ x ∈ C.offDiag, ((x.1 + x.2 : ℕ)).factorization p) ≤
        (∑ x ∈ C.offDiag, min ((D x).factorization p) (V p)) + m * V p := h1
    have h4 := (Nat.cast_le (α := ℝ)).mpr h3
    push_cast at h4 ⊢
    exact h4
  -- combine
  set N : ℕ := C.offDiag.card with hN
  have hNcard : (N : ℝ) = (m : ℝ) * ((m : ℝ) - 1) := by
    have h1 : N = m * m - m := by rw [hN, Finset.offDiag_card]
    have h2 : m ≤ m * m := Nat.le_mul_self m
    rw [h1, Nat.cast_sub h2, Nat.cast_mul]
    ring
  have hA : ∑ x ∈ C.offDiag, Real.log ((x.1 + x.2 : ℕ) : ℝ) =
      (N : ℝ) * ((G : ℝ) * Real.log q) +
      ∑ p ∈ Q, Real.log p * ((∑ x ∈ C.offDiag, ((x.1 + x.2 : ℕ)).factorization p : ℕ) : ℝ) := by
    rw [Finset.sum_congr rfl hI, Finset.sum_add_distrib, Finset.sum_comm]
    simp only [Finset.sum_const, nsmul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hB : (N : ℝ) * ((F : ℝ) * Real.log q) +
      ∑ p ∈ Q, Real.log p * ((∑ x ∈ C.offDiag, min ((D x).factorization p) (V p) : ℕ) : ℝ) ≤
      ∑ x ∈ C.offDiag, Real.log (D x : ℝ) := by
    have h1 : ∑ x ∈ C.offDiag, ((F : ℝ) * Real.log q +
        ∑ p ∈ Q, ((min ((D x).factorization p) (V p) : ℕ) : ℝ) * Real.log p) ≤
        ∑ x ∈ C.offDiag, Real.log (D x : ℝ) := Finset.sum_le_sum hII
    rw [Finset.sum_add_distrib, Finset.sum_comm] at h1
    simp only [Finset.sum_const, nsmul_eq_mul] at h1
    have h2 : ∑ p ∈ Q, ∑ x ∈ C.offDiag, ((min ((D x).factorization p) (V p) : ℕ) : ℝ) * Real.log p =
        ∑ p ∈ Q, Real.log p * ((∑ x ∈ C.offDiag, min ((D x).factorization p) (V p) : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro p _
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [h2] at h1
    exact h1
  have hAB : ∑ x ∈ C.offDiag, Real.log (D x : ℝ) ≤ ∑ x ∈ C.offDiag, Real.log ((x.1 + x.2 : ℕ) : ℝ) :=
    Finset.sum_le_sum hIV
  have hS : ∑ p ∈ Q, Real.log p * ((∑ x ∈ C.offDiag, ((x.1 + x.2 : ℕ)).factorization p : ℕ) : ℝ) ≤
      ∑ p ∈ Q, Real.log p * (((∑ x ∈ C.offDiag, min ((D x).factorization p) (V p) : ℕ) : ℝ) +
        (m : ℝ) * (V p : ℝ)) := by
    apply Finset.sum_le_sum
    intro p hp
    exact mul_le_mul_of_nonneg_left (hIII p hp) (hlogp p hp)
  have hS2 : ∑ p ∈ Q, Real.log p * (((∑ x ∈ C.offDiag, min ((D x).factorization p) (V p) : ℕ) : ℝ) +
        (m : ℝ) * (V p : ℝ)) =
      ∑ p ∈ Q, Real.log p * ((∑ x ∈ C.offDiag, min ((D x).factorization p) (V p) : ℕ) : ℝ) +
      (m : ℝ) * ∑ p ∈ Q, (V p : ℝ) * Real.log p := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hfinal : (N : ℝ) * (((F : ℝ) - G) * Real.log q) ≤ (m : ℝ) * ∑ p ∈ Q, (V p : ℝ) * Real.log p := by
    nlinarith [hA, hB, hAB, hS, hS2]
  have hRHS : 0 ≤ ∑ p ∈ Q, (V p : ℝ) * Real.log p :=
    Finset.sum_nonneg (fun p hp => mul_nonneg (Nat.cast_nonneg _) (hlogp p hp))
  have hFG : (0 : ℝ) ≤ ((F : ℝ) - G) * Real.log q :=
    mul_nonneg (by have : (G : ℝ) < F := by exact_mod_cast hGF
                   linarith) hlogq.le
  rcases Nat.eq_zero_or_pos m with h0 | hpos'
  · have : (m : ℝ) = 0 := by exact_mod_cast h0
    rw [this]
    nlinarith
  · have hmpos : (0 : ℝ) < m := by exact_mod_cast hpos'
    rw [hNcard] at hfinal
    have : (m : ℝ) * (((m : ℝ) - 1) * (((F : ℝ) - G) * Real.log q)) ≤ (m : ℝ) * ∑ p ∈ Q, (V p : ℝ) * Real.log p := by
      nlinarith [hfinal]
    have := le_of_mul_le_mul_left this hmpos
    nlinarith [this]




/-- `ustar a b = (a+b)/gcd(a,b)`. -/
def ustar (a b : ℕ) : ℕ := (a + b) / Nat.gcd a b

lemma ustar_decomp (a b : ℕ) (ha : 0 < a) (_hb : 0 < b) :
    ∃ g x y : ℕ, 0 < g ∧ Nat.Coprime x y ∧ a = x * g ∧ b = y * g ∧ Nat.gcd a b = g ∧
      ustar a b = x + y := by
  obtain ⟨g, x, y, hg, hco, hx, hy⟩ := Nat.exists_coprime' (Nat.gcd_pos_of_pos_left b ha)
  have hgcd : Nat.gcd a b = g := by
    rw [hx, hy, Nat.gcd_mul_right, hco.gcd_eq_one, one_mul]
  refine ⟨g, x, y, hg, hco, hx, hy, hgcd, ?_⟩
  unfold ustar
  rw [hgcd, hx, hy, ← add_mul, Nat.mul_div_cancel _ hg]

lemma ustar_ge_three (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) : 3 ≤ ustar a b := by
  obtain ⟨g, x, y, hg, hco, hx, hy, hgcd, hu⟩ := ustar_decomp a b ha hb
  have hx0 : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · rw [h] at hx; omega
    · exact h
  have hy0 : 0 < y := by
    rcases Nat.eq_zero_or_pos y with h | h
    · rw [h] at hy; omega
    · exact h
  have hxy : x ≠ y := by
    intro h; apply hab; rw [hx, hy, h]
  rw [hu]; omega

lemma ustar_dvd (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : ustar a b ∣ a + b := by
  obtain ⟨g, x, y, hg, hco, hx, hy, hgcd, hu⟩ := ustar_decomp a b ha hb
  refine ⟨g, ?_⟩
  rw [hu]; rw [hx, hy]; ring

lemma ustar_mul_gcd (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ustar a b * Nat.gcd a b = a + b := by
  obtain ⟨g, x, y, hg, hco, hx, hy, hgcd, hu⟩ := ustar_decomp a b ha hb
  rw [hu, hgcd, hx, hy]; ring

lemma ustar_le_mul (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ustar a b ≤ ustar a c * ustar b c := by
  obtain ⟨g, x, y, hg, hco, hx, hy, hgcd, hu⟩ := ustar_decomp a b ha hb
  obtain ⟨g1, x1, y1, hg1, hco1, hx1, hy1, hgcd1, hu1⟩ := ustar_decomp a c ha hc
  obtain ⟨g2, x2, y2, hg2, hco2, hx2, hy2, hgcd2, hu2⟩ := ustar_decomp b c hb hc
  have hx0 : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · rw [h] at hx; omega
    · exact h
  have hy0 : 0 < y := by
    rcases Nat.eq_zero_or_pos y with h | h
    · rw [h] at hy; omega
    · exact h
  have hx10 : 0 < x1 := by
    rcases Nat.eq_zero_or_pos x1 with h | h
    · rw [h] at hx1; omega
    · exact h
  have hy10 : 0 < y1 := by
    rcases Nat.eq_zero_or_pos y1 with h | h
    · rw [h] at hy1; omega
    · exact h
  have hx20 : 0 < x2 := by
    rcases Nat.eq_zero_or_pos x2 with h | h
    · rw [h] at hx2; omega
    · exact h
  have hy20 : 0 < y2 := by
    rcases Nat.eq_zero_or_pos y2 with h | h
    · rw [h] at hy2; omega
    · exact h
  -- key identity: x * y1 * x2 = y * x1 * y2
  have key : x * y1 * x2 = y * x1 * y2 := by
    have e1 : a * y1 = x1 * c := by rw [hx1, hy1]; ring
    have e2 : b * y2 = x2 * c := by rw [hx2, hy2]; ring
    have e3 : a * y1 * x2 = b * y2 * x1 := by
      calc a * y1 * x2 = x1 * c * x2 := by rw [e1]
        _ = x2 * c * x1 := by ring
        _ = b * y2 * x1 := by rw [e2]
    have e4 : (x * y1 * x2) * g = (y * x1 * y2) * g := by
      have : a * y1 * x2 = (x * y1 * x2) * g := by rw [hx]; ring
      have h2 : b * y2 * x1 = (y * x1 * y2) * g := by rw [hy]; ring
      rw [← this, ← h2]; exact e3
    exact Nat.eq_of_mul_eq_mul_right hg e4
  have hxd : x ∣ x1 * y2 := by
    have : x ∣ y * (x1 * y2) := ⟨y1 * x2, by rw [← mul_assoc, ← key]; ring⟩
    exact hco.dvd_of_dvd_mul_left this
  have hyd : y ∣ y1 * x2 := by
    have : y ∣ x * (y1 * x2) := ⟨x1 * y2, by rw [← mul_assoc, mul_assoc x y1 x2, ← mul_assoc, key]; ring⟩
    exact hco.symm.dvd_of_dvd_mul_left this
  have hxle : x ≤ x1 * y2 := Nat.le_of_dvd (Nat.mul_pos hx10 hy20) hxd
  have hyle : y ≤ y1 * x2 := Nat.le_of_dvd (Nat.mul_pos hy10 hx20) hyd
  rw [hu, hu1, hu2]
  nlinarith

lemma ultra_lt (q : ℕ) (hq : q.Prime) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : a.factorization q < b.factorization q) :
    (a + b).factorization q = a.factorization q := by
  set v := a.factorization q with hv
  have h1 : q ^ v ∣ a := (hq.pow_dvd_iff_le_factorization ha.ne').mpr le_rfl
  have h2 : q ^ v ∣ b := (hq.pow_dvd_iff_le_factorization hb.ne').mpr h.le
  have h3 : q ^ v ∣ a + b := dvd_add h1 h2
  have h4 : v ≤ (a + b).factorization q :=
    (hq.pow_dvd_iff_le_factorization (by omega)).mp h3
  by_contra hne
  have h5 : v + 1 ≤ (a + b).factorization q := by omega
  have h6 : q ^ (v + 1) ∣ a + b := (hq.pow_dvd_iff_le_factorization (by omega)).mpr h5
  have h7 : q ^ (v + 1) ∣ b := (hq.pow_dvd_iff_le_factorization hb.ne').mpr (by omega)
  have h8 : q ^ (v + 1) ∣ a := (Nat.dvd_add_left h7).mp h6
  have h9 := (hq.pow_dvd_iff_le_factorization ha.ne').mp h8
  omega

lemma dom_val (q : ℕ) (hq : q.Prime) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : 1 ≤ (ustar a b).factorization q) :
    a.factorization q = b.factorization q ∧
    (a + b).factorization q = a.factorization q + (ustar a b).factorization q := by
  have hu0 : ustar a b ≠ 0 := by
    intro h0; rw [h0] at h; simp at h
  have hg0 : Nat.gcd a b ≠ 0 := (Nat.gcd_pos_of_pos_left b ha).ne'
  have hmul := ustar_mul_gcd a b ha hb
  have hfac : (a + b).factorization q = (ustar a b).factorization q + (Nat.gcd a b).factorization q := by
    rw [← hmul, Nat.factorization_mul hu0 hg0]; rfl
  have hgcd : (Nat.gcd a b).factorization q = min (a.factorization q) (b.factorization q) := by
    rw [Nat.factorization_gcd ha.ne' hb.ne']; rfl
  have hba : (b + a).factorization q = (a + b).factorization q := by rw [add_comm]
  have heq : a.factorization q = b.factorization q := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := ultra_lt q hq a b ha hb hlt
      rw [hfac, hgcd, min_eq_left hlt.le] at this
      omega
    · have := ultra_lt q hq b a hb ha hgt
      rw [hba, hfac, hgcd, min_eq_right hgt.le] at this
      omega
  refine ⟨heq, ?_⟩
  rw [hfac, hgcd, ← heq, min_self]; ring

lemma two_fact (q : ℕ) (_hq : q.Prime) :
    (2 : ℕ).factorization q = if q = 2 then 1 else 0 := by
  rw [Nat.prime_two.factorization, Finsupp.single_apply]
  by_cases h : q = 2
  · simp [h]
  · have : ¬ (2 = q) := fun h' => h h'.symm
    simp [h, this]


/-- Mirror balls `B(a,q,j) = {c ∈ A : q^(v_q(a)+v_q(2)+j) ∣ a + c}` are small: `(|B|-1) j log q ≤ (k-1) log (2M)`. -/
lemma class_bound (A S : Finset ℕ) (hApos : ∀ x ∈ A, 0 < x) (hSprime : ∀ p ∈ S, p.Prime)
    (hS : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ p, p.Prime → p ∣ a + b → p ∈ S)
    (M : ℕ) (hM : ∀ x ∈ A, x ≤ M) (a : ℕ) (ha : a ∈ A) (q : ℕ) (hqS : q ∈ S) (j : ℕ) (hj : 1 ≤ j) :
    (((A.filter (fun c => q ^ (a.factorization q + (2:ℕ).factorization q + j) ∣ a + c)).card : ℝ)
        - 1) * j * Real.log q ≤ ((S.card : ℝ) - 1) * Real.log (2 * M) := by
  classical
  have hq : q.Prime := hSprime q hqS
  set f := a.factorization q with hf
  set e := (2 : ℕ).factorization q with he
  set C := A.filter (fun c => q ^ (f + e + j) ∣ a + c) with hCdef
  have hCA : ∀ x ∈ C, x ∈ A := fun x hx => (Finset.mem_filter.mp hx).1
  have hCdvd : ∀ x ∈ C, q ^ (f + e + j) ∣ a + x := fun x hx => (Finset.mem_filter.mp hx).2
  have hapos : 0 < a := hApos a ha
  have h2a : (2 * a).factorization q = f + e := by
    rw [Nat.factorization_mul (by norm_num) hapos.ne']
    simp [hf, he, add_comm]
  have hM0 : 0 < M := lt_of_lt_of_le (hApos a ha) (hM a ha)
  have key := lemmaC C (fun x hx => hApos x (hCA x hx)) q hq (f + e + j) (f + e) (by omega)
    (S.erase q) (fun p hp => hSprime p (Finset.mem_of_mem_erase hp)) (Finset.notMem_erase q S)
    (by
      intro x hx y hy hxy
      have h1 := hCdvd x hx
      have h2 := hCdvd y hy
      have h1' : ((q ^ (f + e + j) : ℕ) : ℤ) ∣ ((a + x : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h1
      have h2' : ((q ^ (f + e + j) : ℕ) : ℤ) ∣ ((a + y : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h2
      have h3 := dvd_sub h2' h1'
      have h4 : (((a + y : ℕ) : ℤ) - ((a + x : ℕ) : ℤ)) = (y : ℤ) - x := by push_cast; ring
      rw [h4] at h3
      have h5 : (q : ℤ) ^ (f + e + j) ∣ (x : ℤ) - y := by
        have := dvd_neg.mpr h3
        have h6 : -((y : ℤ) - x) = (x : ℤ) - y := by ring
        rw [h6] at this
        exact_mod_cast this
      exact h5)
    (by
      intro x hx y hy hxy
      have hxpos := hApos x (hCA x hx)
      have hypos := hApos y (hCA y hy)
      have h1 := hCdvd x hx
      have h2 := hCdvd y hy
      have hs : q ^ (f + e + j) ∣ (x + y) + 2 * a := by
        have := dvd_add h1 h2
        have e1 : (a + x) + (a + y) = (x + y) + 2 * a := by ring
        rwa [e1] at this
      have hGF : q ^ (f + e) ∣ (x + y) + 2 * a :=
        (pow_dvd_pow q (by omega)).trans hs
      have h2a' : q ^ (f + e) ∣ 2 * a :=
        (hq.pow_dvd_iff_le_factorization (by omega)).mpr (by rw [h2a])
      have hge : q ^ (f + e) ∣ x + y := (Nat.dvd_add_left h2a').mp hGF
      have hge' : f + e ≤ (x + y).factorization q :=
        (hq.pow_dvd_iff_le_factorization (by omega)).mp hge
      by_contra hne
      have hgt : f + e + 1 ≤ (x + y).factorization q := by omega
      have h7 : q ^ (f + e + 1) ∣ x + y := (hq.pow_dvd_iff_le_factorization (by omega)).mpr hgt
      have h8 : q ^ (f + e + 1) ∣ (x + y) + 2 * a :=
        (pow_dvd_pow q (by omega)).trans hs
      have h9 : q ^ (f + e + 1) ∣ 2 * a := (Nat.dvd_add_right h7).mp h8
      have h10 := (hq.pow_dvd_iff_le_factorization (by omega)).mp h9
      rw [h2a] at h10
      omega)
    (by
      intro x hx y hy hxy p hp hpd
      have := hS x (hCA x hx) y (hCA y hy) hxy p hp hpd
      by_cases hpq : p = q
      · exact Or.inl hpq
      · exact Or.inr (Finset.mem_erase.mpr ⟨hpq, this⟩))
    (fun p => Nat.log p (2 * M))
    (by
      intro p hp x hx y hy hxy
      have hpp : p.Prime := hSprime p (Finset.mem_of_mem_erase hp)
      have hxpos := hApos x (hCA x hx)
      have hypos := hApos y (hCA y hy)
      apply Nat.le_log_of_pow_le hpp.one_lt
      have h1 : p ^ ((x + y).factorization p) ∣ x + y :=
        (hpp.pow_dvd_iff_le_factorization (by omega)).mpr le_rfl
      have h2 := Nat.le_of_dvd (by omega) h1
      have h3 := hM x (hCA x hx)
      have h4 := hM y (hCA y hy)
      omega)
  -- RHS bound
  have hrhs : ∑ p ∈ S.erase q, ((Nat.log p (2 * M) : ℕ) : ℝ) * Real.log p ≤
      ((S.card : ℝ) - 1) * Real.log (2 * M) := by
    have h1 : ∀ p ∈ S.erase q, ((Nat.log p (2 * M) : ℕ) : ℝ) * Real.log p ≤ Real.log (2 * M) := by
      intro p hp
      have hpp : p.Prime := hSprime p (Finset.mem_of_mem_erase hp)
      have h2 : p ^ (Nat.log p (2 * M)) ≤ 2 * M := Nat.pow_log_le_self p (by omega)
      have h3 : (0 : ℝ) < (p : ℝ) ^ (Nat.log p (2 * M)) := by
        have : (0 : ℝ) < p := by exact_mod_cast hpp.pos
        positivity
      have h4 : Real.log ((p : ℝ) ^ (Nat.log p (2 * M))) ≤ Real.log (2 * M) := by
        apply Real.log_le_log h3
        exact_mod_cast h2
      rw [Real.log_pow] at h4
      exact h4
    have h2 := Finset.sum_le_card_nsmul (S.erase q) (fun p => ((Nat.log p (2 * M) : ℕ) : ℝ) * Real.log p)
      (Real.log (2 * M)) h1
    rw [Finset.card_erase_of_mem hqS, nsmul_eq_mul] at h2
    have h5 : (((S.card - 1 : ℕ)) : ℝ) = (S.card : ℝ) - 1 := by
      have : 1 ≤ S.card := Finset.card_pos.mpr ⟨q, hqS⟩
      push_cast [Nat.cast_sub this]
      ring
    rw [h5] at h2
    exact h2
  have hFG : (((f + e + j : ℕ) : ℝ) - ((f + e : ℕ) : ℝ)) = (j : ℝ) := by push_cast; ring
  rw [hFG] at key
  calc _ ≤ _ := key
    _ ≤ _ := hrhs


/-- Dominant-prime pigeonhole: a partner `b` of `a` with `ustar a b ^ s ≥ 2M` lies in a mirror ball of `a`. -/
lemma bad_subset (A S : Finset ℕ) (hApos : ∀ x ∈ A, 0 < x) (hSprime : ∀ p ∈ S, p.Prime)
    (hS : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ p, p.Prime → p ∣ a + b → p ∈ S)
    (M : ℕ) (hM : ∀ x ∈ A, x ≤ M) (a : ℕ) (ha : a ∈ A) (s : ℕ) (hs : 1 ≤ s) :
    A.filter (fun b => b ≠ a ∧ 2 * M ≤ (ustar a b) ^ s) ⊆
      S.biUnion (fun q => A.filter (fun c => q ^ (a.factorization q + (2:ℕ).factorization q +
        ⌈Real.log (2 * M) / (2 * s * S.card * Real.log q)⌉₊) ∣ a + c)) := by
  classical
  intro b hb
  simp only [Finset.mem_filter] at hb
  obtain ⟨hbA, hba, hbig⟩ := hb
  have hapos : 0 < a := hApos a ha
  have hbpos : 0 < b := hApos b hbA
  have hM0 : 0 < M := lt_of_lt_of_le hapos (hM a ha)
  set u := ustar a b with hu
  have hu3 : 3 ≤ u := ustar_ge_three a b hapos hbpos (Ne.symm hba)
  have hudvd : u ∣ a + b := ustar_dvd a b hapos hbpos
  have huS : ∀ p, p.Prime → p ∣ u → p ∈ S := fun p hp hpu =>
    hS a ha b hbA (Ne.symm hba) p hp (hpu.trans hudvd)
  have hpf : u.primeFactors ⊆ S := fun p hp =>
    huS p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  have hlogu : Real.log u = ∑ p ∈ S, (u.factorization p : ℝ) * Real.log p :=
    log_eq_sum_fact u (by omega) S hpf
  have hT : 0 < Real.log (2 * M) := by
    apply Real.log_pos
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM0
    linarith
  have hTs : Real.log (2 * M) ≤ s * Real.log u := by
    have h1 : ((2 * M : ℕ) : ℝ) ≤ ((u ^ s : ℕ) : ℝ) := by exact_mod_cast hbig
    have h2 : Real.log ((2 * M : ℕ) : ℝ) ≤ Real.log ((u : ℝ) ^ s) := by
      apply Real.log_le_log
      · have : (0 : ℝ) < ((2 * M : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * M)
        exact this
      · push_cast at h1 ⊢; exact h1
    rw [Real.log_pow] at h2
    push_cast at h2
    exact h2
  -- S nonempty
  have hSne : S.Nonempty := by
    obtain ⟨p, hp, hpu⟩ := Nat.exists_prime_and_dvd (show u ≠ 1 by omega)
    exact ⟨p, huS p hp hpu⟩
  obtain ⟨q, hqS, hqmax⟩ := Finset.exists_max_image S
    (fun p => (u.factorization p : ℝ) * Real.log p) hSne
  have hq : q.Prime := hSprime q hqS
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  set α := u.factorization q with hα
  have hk : 0 < S.card := Finset.card_pos.mpr ⟨q, hqS⟩
  have hkR : (0 : ℝ) < S.card := by exact_mod_cast hk
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hsum_le : ∑ p ∈ S, (u.factorization p : ℝ) * Real.log p ≤ S.card * ((α : ℝ) * Real.log q) := by
    have := Finset.sum_le_card_nsmul S (fun p => (u.factorization p : ℝ) * Real.log p)
      ((α : ℝ) * Real.log q) hqmax
    rwa [nsmul_eq_mul] at this
  have hTle : Real.log (2 * M) ≤ s * S.card * ((α : ℝ) * Real.log q) := by
    calc Real.log (2 * M) ≤ s * Real.log u := hTs
      _ ≤ s * (S.card * ((α : ℝ) * Real.log q)) := by
          apply mul_le_mul_of_nonneg_left _ hsR.le
          rw [hlogu]; exact hsum_le
      _ = _ := by ring
  have hα1 : 1 ≤ α := by
    by_contra h
    have h0 : α = 0 := by omega
    rw [h0] at hTle
    simp at hTle
    linarith
  -- q = 2 → α ≥ 2
  have hα2 : q = 2 → 2 ≤ α := by
    intro hq2
    by_contra hlt
    have hα1' : α = 1 := by omega
    -- all other primes have exponent 0
    have hzero : ∀ p ∈ S, p ≠ 2 → u.factorization p = 0 := by
      intro p hp hp2
      by_contra hne
      have hpp := hSprime p hp
      have h1 := hqmax p hp
      have hp3 : 3 ≤ p := by
        have := hpp.two_le
        omega
      have hlogp : Real.log 2 < Real.log p := by
        apply Real.log_lt_log (by norm_num)
        exact_mod_cast (by omega : 2 < p)
      have hfp : 1 ≤ u.factorization p := Nat.one_le_iff_ne_zero.mpr hne
      have hlogp0 : 0 < Real.log p := lt_trans (Real.log_pos (by norm_num)) hlogp
      have h2 : Real.log p ≤ (u.factorization p : ℝ) * Real.log p := by
        have : (1 : ℝ) ≤ (u.factorization p : ℝ) := by exact_mod_cast hfp
        nlinarith
      rw [hα1', hq2] at h1
      simp at h1
      linarith
    have h2S : 2 ∈ S := by rw [← hq2]; exact hqS
    have hsum2 : ∑ p ∈ S, (u.factorization p : ℝ) * Real.log p = (u.factorization 2 : ℝ) * Real.log 2 := by
      apply Finset.sum_eq_single_of_mem 2 h2S
      intro p hp hp2
      rw [hzero p hp hp2]; simp
    have hu2 : u.factorization 2 = 1 := by rw [← hq2]; exact hα1'
    rw [hsum2, hu2] at hlogu
    simp at hlogu
    have : (u : ℝ) = 2 := by
      have h1 := Real.exp_log (show (0 : ℝ) < u by exact_mod_cast (by omega : 0 < u))
      rw [hlogu, Real.exp_log (by norm_num)] at h1
      exact h1.symm
    have : u = 2 := by exact_mod_cast this
    omega
  -- level bound
  set x : ℝ := Real.log (2 * M) / (2 * s * S.card * Real.log q) with hx
  have hxpos : 0 < x := by positivity
  have hxα : x ≤ (α : ℝ) / 2 := by
    rw [hx, div_le_iff₀ (by positivity)]
    nlinarith [hTle]
  have he : (2 : ℕ).factorization q = if q = 2 then 1 else 0 := two_fact q hq
  have hjle : ⌈x⌉₊ + (2 : ℕ).factorization q ≤ α := by
    rw [he]
    by_cases hq2 : q = 2
    · rw [if_pos hq2]
      have hα2' := hα2 hq2
      have : ⌈x⌉₊ ≤ α - 1 := by
        rw [Nat.ceil_le]
        have : ((α - 1 : ℕ) : ℝ) = (α : ℝ) - 1 := by
          push_cast [Nat.cast_sub hα1]; ring
        rw [this]
        have : (2 : ℝ) ≤ α := by exact_mod_cast hα2'
        linarith
      omega
    · rw [if_neg hq2]
      have : ⌈x⌉₊ ≤ α := by
        rw [Nat.ceil_le]
        have : (0 : ℝ) ≤ α := Nat.cast_nonneg _
        linarith
      omega
  -- divisibility
  have hα1' : 1 ≤ (ustar a b).factorization q := hα1
  obtain ⟨hfeq, hfsum⟩ := dom_val q hq a b hapos hbpos hα1'
  have hfsum' : (a + b).factorization q = a.factorization q + α := hfsum
  have hdvd : q ^ (a.factorization q + (2:ℕ).factorization q + ⌈x⌉₊) ∣ a + b := by
    rw [hq.pow_dvd_iff_le_factorization (by omega), hfsum']
    omega
  apply Finset.mem_biUnion.mpr
  exact ⟨q, hqS, Finset.mem_filter.mpr ⟨hbA, hdvd⟩⟩


/-- Every element has at most `k (1 + 2 s k (k-1))` "bad" partners. -/
lemma bad_card (A S : Finset ℕ) (hApos : ∀ x ∈ A, 0 < x) (hSprime : ∀ p ∈ S, p.Prime)
    (hS : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ p, p.Prime → p ∣ a + b → p ∈ S)
    (M : ℕ) (hM : ∀ x ∈ A, x ≤ M) (a : ℕ) (ha : a ∈ A) (s : ℕ) (hs : 1 ≤ s) :
    (A.filter (fun b => b ≠ a ∧ 2 * M ≤ (ustar a b) ^ s)).card ≤
      S.card * (1 + 2 * s * S.card * (S.card - 1)) := by
  classical
  have hapos : 0 < a := hApos a ha
  have hM0 : 0 < M := lt_of_lt_of_le hapos (hM a ha)
  have hT : 0 < Real.log (2 * M) := by
    apply Real.log_pos
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM0
    linarith
  have hsub := bad_subset A S hApos hSprime hS M hM a ha s hs
  calc (A.filter (fun b => b ≠ a ∧ 2 * M ≤ (ustar a b) ^ s)).card
      ≤ (S.biUnion (fun q => A.filter (fun c => q ^ (a.factorization q + (2:ℕ).factorization q +
        ⌈Real.log (2 * M) / (2 * s * S.card * Real.log q)⌉₊) ∣ a + c))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ q ∈ S, (A.filter (fun c => q ^ (a.factorization q + (2:ℕ).factorization q +
        ⌈Real.log (2 * M) / (2 * s * S.card * Real.log q)⌉₊) ∣ a + c)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ q ∈ S, (1 + 2 * s * S.card * (S.card - 1)) := by
        apply Finset.sum_le_sum
        intro q hqS
        have hq : q.Prime := hSprime q hqS
        have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
        have hk : 1 ≤ S.card := Finset.card_pos.mpr ⟨q, hqS⟩
        have hkR : (1 : ℝ) ≤ S.card := by exact_mod_cast hk
        have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
        set x : ℝ := Real.log (2 * M) / (2 * s * S.card * Real.log q) with hx
        have hxpos : 0 < x := by positivity
        have hj1 : 1 ≤ ⌈x⌉₊ := by
          rw [Nat.one_le_ceil_iff]; exact hxpos
        have hcb := class_bound A S hApos hSprime hS M hM a ha q hqS ⌈x⌉₊ hj1
        set c := (A.filter (fun c => q ^ (a.factorization q + (2:ℕ).factorization q + ⌈x⌉₊) ∣ a + c)).card
          with hc
        have hxj : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
        have h1 : Real.log (2 * M) / (2 * s * S.card) ≤ (⌈x⌉₊ : ℝ) * Real.log q := by
          have : x * Real.log q ≤ (⌈x⌉₊ : ℝ) * Real.log q := mul_le_mul_of_nonneg_right hxj hlogq.le
          have h2 : x * Real.log q = Real.log (2 * M) / (2 * s * S.card) := by
            rw [hx]; field_simp
          linarith
        have hbound : (c : ℝ) ≤ 1 + 2 * s * S.card * ((S.card : ℝ) - 1) := by
          by_cases hc1 : (c : ℝ) ≤ 1
          · have : (0 : ℝ) ≤ 2 * s * S.card * ((S.card : ℝ) - 1) := by
              have : (0 : ℝ) ≤ (S.card : ℝ) - 1 := by linarith
              positivity
            linarith
          · push_neg at hc1
            have hc1' : 0 ≤ (c : ℝ) - 1 := by linarith
            have h3 : ((c : ℝ) - 1) * (Real.log (2 * M) / (2 * s * S.card)) ≤
                ((c : ℝ) - 1) * ((⌈x⌉₊ : ℝ) * Real.log q) :=
              mul_le_mul_of_nonneg_left h1 hc1'
            have h4 : ((c : ℝ) - 1) * (⌈x⌉₊ : ℝ) * Real.log q ≤ ((S.card : ℝ) - 1) * Real.log (2 * M) := hcb
            have h5 : ((c : ℝ) - 1) * (Real.log (2 * M) / (2 * s * S.card)) ≤
                ((S.card : ℝ) - 1) * Real.log (2 * M) := by
              calc _ ≤ ((c : ℝ) - 1) * ((⌈x⌉₊ : ℝ) * Real.log q) := h3
                _ = ((c : ℝ) - 1) * (⌈x⌉₊ : ℝ) * Real.log q := by ring
                _ ≤ _ := h4
            have h6 : (c : ℝ) - 1 ≤ 2 * s * S.card * ((S.card : ℝ) - 1) := by
              have h7 : (0 : ℝ) < 2 * s * S.card := by positivity
              have h8 : ((c : ℝ) - 1) * Real.log (2 * M) ≤
                  (2 * s * S.card) * (((S.card : ℝ) - 1) * Real.log (2 * M)) := by
                have := mul_le_mul_of_nonneg_left h5 h7.le
                calc ((c : ℝ) - 1) * Real.log (2 * M)
                    = (2 * s * S.card) * (((c : ℝ) - 1) * (Real.log (2 * M) / (2 * s * S.card))) := by
                        field_simp
                  _ ≤ _ := this
              have h9 : ((c : ℝ) - 1) * Real.log (2 * M) ≤
                  (2 * s * S.card * ((S.card : ℝ) - 1)) * Real.log (2 * M) := by
                calc _ ≤ _ := h8
                  _ = _ := by ring
              exact le_of_mul_le_mul_right h9 hT
            linarith
        have : (c : ℝ) ≤ ((1 + 2 * s * S.card * (S.card - 1) : ℕ) : ℝ) := by
          push_cast [Nat.cast_sub hk]
          exact hbound
        exact_mod_cast this
    _ = S.card * (1 + 2 * s * S.card * (S.card - 1)) := by simp


lemma num_part (M b : ℕ) (hM : 0 < M) (hb : 0 < b) :
    ∃ x : ℕ, 0 < x ∧ x < ustar M b ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ b → M.factorization p = x.factorization p := by
  obtain ⟨g, x, y, hg, hco, hx, hy, hgcd, hu⟩ := ustar_decomp M b hM hb
  have hx0 : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · rw [h] at hx; omega
    · exact h
  have hy0 : 0 < y := by
    rcases Nat.eq_zero_or_pos y with h | h
    · rw [h] at hy; omega
    · exact h
  refine ⟨x, hx0, by rw [hu]; omega, ?_⟩
  intro p hp hpb
  have hgb : g ∣ b := ⟨y, by rw [hy]; ring⟩
  have hpg : ¬ p ∣ g := fun h => hpb (h.trans hgb)
  have hg0 : g.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpg
  rw [hx, Nat.factorization_mul hx0.ne' hg.ne']
  simp [hg0]

/-- **Main theorem.**  A primitive `S`-clique has at most `2k(1 + 8k(k+1)(k-1)) + 2` elements (`k = |S|`). -/
theorem main_primitive (A S : Finset ℕ) (hApos : ∀ x ∈ A, 0 < x) (hSprime : ∀ p ∈ S, p.Prime)
    (hS : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ p, p.Prime → p ∣ a + b → p ∈ S)
    (hprim : ∀ p, p.Prime → ∃ b ∈ A, ¬ p ∣ b) :
    A.card ≤ 2 * (S.card * (1 + 2 * (4 * (S.card + 1)) * S.card * (S.card - 1))) + 2 := by
  classical
  by_contra hcon
  push_neg at hcon
  set k := S.card with hk
  set s := 4 * (k + 1) with hsdef
  set Γ := k * (1 + 2 * s * k * (k - 1)) with hΓ
  have hn : 2 * Γ + 2 < A.card := hcon
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  set M := A.max' hAne with hMdef
  have hMA : M ∈ A := Finset.max'_mem A hAne
  have hMle : ∀ x ∈ A, x ≤ M := fun x hx => Finset.le_max' A x hx
  have hMpos : 0 < M := hApos M hMA
  have hs1 : 1 ≤ s := by omega
  set bad : ℕ → Finset ℕ := fun a => A.filter (fun b => b ≠ a ∧ 2 * M ≤ (ustar a b) ^ s) with hbad
  have hbadcard : ∀ a ∈ A, (bad a).card ≤ Γ := fun a ha =>
    bad_card A S hApos hSprime hS M hMle a ha s hs1
  -- Step 2
  have step2 : ∀ b ∈ A, b ≠ M → (ustar M b) ^ s < (2 * M) ^ 2 := by
    intro b hb hbM
    have hex : ∃ c ∈ A, c ≠ M ∧ c ≠ b ∧ ¬ (2 * M ≤ (ustar M c) ^ s) ∧ ¬ (2 * M ≤ (ustar b c) ^ s) := by
      by_contra hno
      push_neg at hno
      have hsub : A ⊆ ({M, b} : Finset ℕ) ∪ bad M ∪ bad b := by
        intro c hc
        by_cases hcM : c = M
        · simp [hcM]
        by_cases hcb : c = b
        · simp [hcb]
        by_cases h1 : 2 * M ≤ (ustar M c) ^ s
        · apply Finset.mem_union_left; apply Finset.mem_union_right
          simp only [hbad, Finset.mem_filter]
          exact ⟨hc, hcM, h1⟩
        · apply Finset.mem_union_right
          simp only [hbad, Finset.mem_filter]
          exact ⟨hc, hcb, hno c hc hcM hcb (not_le.mp h1)⟩
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le (({M, b} : Finset ℕ) ∪ bad M) (bad b)
      have h3 := Finset.card_union_le ({M, b} : Finset ℕ) (bad M)
      have h4 : ({M, b} : Finset ℕ).card ≤ 2 := Finset.card_le_two
      have h5 := hbadcard M hMA
      have h6 := hbadcard b hb
      omega
    obtain ⟨c, hcA, hcM, hcb, hc1, hc2⟩ := hex
    have hcpos := hApos c hcA
    have hbpos := hApos b hb
    have hle := ustar_le_mul M b c hMpos hbpos hcpos
    push_neg at hc1 hc2
    calc (ustar M b) ^ s ≤ (ustar M c * ustar b c) ^ s := Nat.pow_le_pow_left hle s
      _ = (ustar M c) ^ s * (ustar b c) ^ s := by rw [mul_pow]
      _ < (2 * M) * (2 * M) := Nat.mul_lt_mul'' hc1 hc2
      _ = (2 * M) ^ 2 := by ring
  -- log bound on ustar
  have hT : 0 < Real.log (2 * M) := by
    apply Real.log_pos
    have : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
    linarith
  have hsR : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  set Lmax : ℝ := 2 / s * Real.log (2 * M) with hLmax
  have hustar_log : ∀ b ∈ A, b ≠ M → Real.log (ustar M b) ≤ Lmax := by
    intro b hb hbM
    have h1 := step2 b hb hbM
    have hbpos := hApos b hb
    have hu0 : 0 < ustar M b := by have := ustar_ge_three M b hMpos hbpos (Ne.symm hbM); omega
    have h2 : Real.log (((ustar M b) ^ s : ℕ) : ℝ) ≤ Real.log (((2 * M) ^ 2 : ℕ) : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast (pow_pos hu0 s)
      · exact_mod_cast h1.le
    push_cast at h2
    rw [Real.log_pow, Real.log_pow] at h2
    push_cast at h2
    rw [hLmax]
    rw [div_mul_eq_mul_div, le_div_iff₀ hsR]
    linarith
  -- per prime bound
  have hprime_bound : ∀ p, p.Prime → p ∣ M → (M.factorization p : ℝ) * Real.log p ≤ Lmax := by
    intro p hp hpM
    obtain ⟨b, hb, hpb⟩ := hprim p hp
    have hbM : b ≠ M := by intro h; apply hpb; rw [h]; exact hpM
    obtain ⟨x, hx0, hxu, hxp⟩ := num_part M b hMpos (hApos b hb)
    have h1 := sum_fact_log_le x hx0.ne' {p} (by simpa using hp)
    simp only [Finset.sum_singleton] at h1
    rw [hxp p hp hpb]
    have h2 : Real.log x ≤ Real.log (ustar M b) := by
      apply Real.log_le_log (by exact_mod_cast hx0)
      exact_mod_cast hxu.le
    linarith [hustar_log b hb hbM]
  -- non-S primes
  obtain ⟨b0, hb0A, hb0M⟩ : ∃ b0 ∈ A, b0 ≠ M := by
    by_contra hno
    push_neg at hno
    have : A ⊆ {M} := fun x hx => by simp [hno x hx]
    have := Finset.card_le_card this
    simp at this
    omega
  have hnonS : ∑ p ∈ M.primeFactors.filter (fun p => p ∉ S), (M.factorization p : ℝ) * Real.log p ≤ Lmax := by
    obtain ⟨x, hx0, hxu, hxp⟩ := num_part M b0 hMpos (hApos b0 hb0A)
    have h1 := sum_fact_log_le x hx0.ne' (M.primeFactors.filter (fun p => p ∉ S))
      (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
    have h2 : ∑ p ∈ M.primeFactors.filter (fun p => p ∉ S), (M.factorization p : ℝ) * Real.log p =
        ∑ p ∈ M.primeFactors.filter (fun p => p ∉ S), (x.factorization p : ℝ) * Real.log p := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpp := Nat.prime_of_mem_primeFactors hp'.1
      have hpM := Nat.dvd_of_mem_primeFactors hp'.1
      have hpb0 : ¬ p ∣ b0 := by
        intro hpb
        apply hp'.2
        exact hS M hMA b0 hb0A (Ne.symm hb0M) p hpp (dvd_add hpM hpb)
      rw [hxp p hpp hpb0]
    have h3 : Real.log x ≤ Real.log (ustar M b0) := by
      apply Real.log_le_log (by exact_mod_cast hx0)
      exact_mod_cast hxu.le
    rw [h2]
    linarith [hustar_log b0 hb0A hb0M]
  have hSpart : ∑ p ∈ M.primeFactors.filter (fun p => p ∈ S), (M.factorization p : ℝ) * Real.log p ≤
      k * Lmax := by
    have h1 : ∀ p ∈ M.primeFactors.filter (fun p => p ∈ S), (M.factorization p : ℝ) * Real.log p ≤ Lmax := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      exact hprime_bound p (Nat.prime_of_mem_primeFactors hp'.1) (Nat.dvd_of_mem_primeFactors hp'.1)
    have h2 := Finset.sum_le_card_nsmul _ _ Lmax h1
    rw [nsmul_eq_mul] at h2
    have h3 : (M.primeFactors.filter (fun p => p ∈ S)).card ≤ k := by
      apply Finset.card_le_card
      intro p hp; exact (Finset.mem_filter.mp hp).2
    have h4 : ((M.primeFactors.filter (fun p => p ∈ S)).card : ℝ) ≤ k := by exact_mod_cast h3
    have hL0 : 0 ≤ Lmax := by rw [hLmax]; positivity
    calc _ ≤ _ := h2
      _ ≤ k * Lmax := mul_le_mul_of_nonneg_right h4 hL0
  have hlogM : Real.log M = ∑ p ∈ M.primeFactors, (M.factorization p : ℝ) * Real.log p :=
    log_eq_sum_fact M hMpos.ne' M.primeFactors (subset_refl _)
  have hsplit : ∑ p ∈ M.primeFactors, (M.factorization p : ℝ) * Real.log p =
      ∑ p ∈ M.primeFactors.filter (fun p => p ∈ S), (M.factorization p : ℝ) * Real.log p +
      ∑ p ∈ M.primeFactors.filter (fun p => p ∉ S), (M.factorization p : ℝ) * Real.log p :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hfin : Real.log M ≤ (k + 1) * Lmax := by
    rw [hlogM, hsplit]; linarith
  have hkL : ((k : ℝ) + 1) * Lmax = (1 / 2) * Real.log (2 * M) := by
    rw [hLmax, hsdef]
    push_cast
    field_simp
    ring
  have h2log : 2 * Real.log M ≤ Real.log (2 * M) := by linarith
  have hM2 : M ≤ 2 := by
    have h1 : Real.log ((M : ℝ) ^ 2) ≤ Real.log ((2 * M : ℕ) : ℝ) := by
      rw [Real.log_pow]; push_cast; linarith
    have h2 : (M : ℝ) ^ 2 ≤ ((2 * M : ℕ) : ℝ) := by
      have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
      have := (Real.log_le_log_iff (by positivity) (by push_cast; positivity)).mp h1
      exact this
    have h3 : M ^ 2 ≤ 2 * M := by exact_mod_cast h2
    nlinarith
  have hAsub : A ⊆ {1, 2} := by
    intro x hx
    have := hMle x hx
    have := hApos x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have := Finset.card_le_card hAsub
  have h2 : ({1, 2} : Finset ℕ).card ≤ 2 := Finset.card_le_two
  omega


/-- Reduction to the primitive case (remove `0`, divide by the gcd). -/
theorem general_bound (A : Finset ℕ) :
    A.card ≤ 37 * ((∏ x ∈ A.offDiag, (x.1 + x.2)).primeFactors.card) ^ 4 + 3 := by
  classical
  set P := (∏ x ∈ A.offDiag, (x.1 + x.2)).primeFactors with hP
  set ω := P.card with hω
  set A₁ := A.erase 0 with hA₁
  have hA₁pos : ∀ x ∈ A₁, 0 < x := fun x hx => Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hx)
  have hcardA₁ : A.card ≤ A₁.card + 1 := by
    have h : A.card - 1 ≤ A₁.card := Finset.pred_card_le_card_erase
    omega
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hprodne : (∏ x ∈ A.offDiag, (x.1 + x.2)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro x hx
    have h := Finset.mem_offDiag.mp hx
    have := h.2.2
    omega
  have hS₁ : ∀ a ∈ A₁, ∀ b ∈ A₁, a ≠ b → ∀ p, p.Prime → p ∣ a + b → p ∈ P := by
    intro a ha b hb hab p hp hpd
    have haA := Finset.mem_of_mem_erase ha
    have hbA := Finset.mem_of_mem_erase hb
    have hmem : (a, b) ∈ A.offDiag := Finset.mem_offDiag.mpr ⟨haA, hbA, hab⟩
    have hdvd : a + b ∣ ∏ x ∈ A.offDiag, (x.1 + x.2) :=
      Finset.dvd_prod_of_mem (fun x : ℕ × ℕ => x.1 + x.2) hmem
    exact Nat.mem_primeFactors.mpr ⟨hp, hpd.trans hdvd, hprodne⟩
  -- the numeric inequality
  have hnum : ∀ w : ℕ, 2 * (w * (1 + 2 * (4 * (w + 1)) * w * (w - 1))) + 2 + 1 ≤ 37 * w ^ 4 + 3 := by
    intro w
    rcases Nat.eq_zero_or_pos w with h0 | hpos
    · subst h0; simp
    · obtain ⟨t, rfl⟩ : ∃ t, w = t + 1 := ⟨w - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      nlinarith [Nat.zero_le (t ^ 4), Nat.zero_le (t ^ 3), Nat.zero_le (t ^ 2), Nat.zero_le t]
  by_cases h1 : A₁.card ≤ 1
  · have := Nat.zero_le (37 * ω ^ 4)
    omega
  push_neg at h1
  obtain ⟨x0, hx0⟩ : A₁.Nonempty := Finset.card_pos.mp (by omega)
  set g := A₁.gcd id with hg
  have hgdvd : ∀ x ∈ A₁, g ∣ x := fun x hx => Finset.gcd_dvd hx
  have hg0 : 0 < g := by
    apply Nat.pos_of_ne_zero
    intro h0
    have h2 := (Finset.gcd_eq_zero_iff).mp h0 x0 hx0
    have h3 := hA₁pos x0 hx0
    simp at h2
    omega
  set A₂ := A₁.image (fun x => x / g) with hA₂
  have hinj : Set.InjOn (fun x => x / g) (A₁ : Set ℕ) := by
    intro x hx y hy hxy
    have hx' := hgdvd x hx
    have hy' := hgdvd y hy
    have h1 : x = g * (x / g) := (Nat.mul_div_cancel' hx').symm
    have h2 : y = g * (y / g) := (Nat.mul_div_cancel' hy').symm
    simp only at hxy
    rw [h1, h2, hxy]
  have hcard₂ : A₂.card = A₁.card := Finset.card_image_of_injOn hinj
  have hA₂pos : ∀ y ∈ A₂, 0 < y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    apply Nat.div_pos (Nat.le_of_dvd (hA₁pos x hx) (hgdvd x hx)) hg0
  have hS₂ : ∀ a ∈ A₂, ∀ b ∈ A₂, a ≠ b → ∀ p, p.Prime → p ∣ a + b → p ∈ P := by
    intro a ha b hb hab p hp hpd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    have hx' := hgdvd x hx
    have hy' := hgdvd y hy
    have hxy : x ≠ y := by intro h; apply hab; rw [h]
    apply hS₁ x hx y hy hxy p hp
    have h1 : x = g * (x / g) := (Nat.mul_div_cancel' hx').symm
    have h2 : y = g * (y / g) := (Nat.mul_div_cancel' hy').symm
    have h3 : x + y = g * (x / g + y / g) := by
      calc x + y = g * (x / g) + g * (y / g) := by rw [← h1, ← h2]
        _ = _ := by ring
    rw [h3]
    exact Dvd.dvd.mul_left hpd g
  have hprim₂ : ∀ p, p.Prime → ∃ b ∈ A₂, ¬ p ∣ b := by
    intro p hp
    by_contra hno
    push_neg at hno
    have h1 : p ∣ A₁.gcd (fun j => j / g) := by
      apply Finset.dvd_gcd
      intro y hy
      exact hno (y / g) (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
    have h2 : A₁.gcd (fun j => id j / A₁.gcd id) = 1 :=
      Finset.gcd_div_eq_one hx0 (by have := hA₁pos x0 hx0; simp; omega)
    have h3 : A₁.gcd (fun j => j / g) = 1 := h2
    rw [h3] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hmain : A₂.card ≤ 2 * (ω * (1 + 2 * (4 * (ω + 1)) * ω * (ω - 1))) + 2 :=
    main_primitive A₂ P hA₂pos hPprime hS₂ hprim₂
  have hn := hnum ω
  rw [hcard₂] at hmain
  omega



/-- Final assembly: from the polynomial bound `general_bound` to `f n / log n → ∞`. -/
theorem final (f : ℕ → ℕ)
    (hf : ∀ n, IsGreatest
      { m | ∀ (A : Finset ℕ), A.card = n →
        m ≤ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card}
      (f n)) :
    Tendsto (fun n => f n / Real.log n) atTop atTop := by
  have key : ∀ n : ℕ, 4 ≤ n → (((n : ℝ) / 40) ^ ((1 : ℝ) / 4)) ≤ (f n : ℝ) := by
    intro n hn
    set L : ℕ := ⌈((n : ℝ) / 40) ^ ((1 : ℝ) / 4)⌉₊ with hL
    have hLmem : L ∈ { m | ∀ (A : Finset ℕ), A.card = n →
        m ≤ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card} := by
      intro A hA
      have hgb := E126.general_bound A
      set ω := (∏ x ∈ A.offDiag, (x.1 + x.2)).primeFactors.card with hω
      have hω1 : 1 ≤ ω := by
        by_contra h
        have h0 : ω = 0 := by omega
        rw [h0] at hgb
        omega
      have hn40 : n ≤ 40 * ω ^ 4 := by
        have : 1 ≤ ω ^ 4 := Nat.one_le_pow _ _ hω1
        omega
      have hnR : (n : ℝ) / 40 ≤ (ω : ℝ) ^ 4 := by
        have : (n : ℝ) ≤ 40 * (ω : ℝ) ^ 4 := by exact_mod_cast hn40
        linarith
      have h1 : ((n : ℝ) / 40) ^ ((1 : ℝ) / 4) ≤ ((ω : ℝ) ^ 4) ^ ((1 : ℝ) / 4) := by
        apply Real.rpow_le_rpow (by positivity) hnR (by norm_num)
      have h2 : ((ω : ℝ) ^ 4) ^ ((1 : ℝ) / 4) = (ω : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
        norm_num
      rw [h2] at h1
      show L ≤ _
      exact Nat.ceil_le.mpr h1
    have hLle : L ≤ f n := (hf n).2 hLmem
    calc _ ≤ (L : ℝ) := Nat.le_ceil _
      _ ≤ f n := by exact_mod_cast hLle
  have hlim : Tendsto (fun n : ℕ => ((n : ℝ) / 40) ^ ((1 : ℝ) / 4) / Real.log n) atTop atTop := by
    have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ ((1 : ℝ) / 4)) atTop (nhds 0) :=
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero
    have h2 : Tendsto (fun x : ℝ => Real.log x / x ^ ((1 : ℝ) / 4)) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
      apply tendsto_nhdsWithin_iff.mpr ⟨h1, ?_⟩
      filter_upwards [eventually_gt_atTop 1] with x hx
      exact div_pos (Real.log_pos hx) (Real.rpow_pos_of_pos (by linarith) _)
    have h3 := h2.inv_tendsto_nhdsGT_zero
    have h4 : (0 : ℝ) < ((40 : ℝ) ^ ((1 : ℝ) / 4))⁻¹ := by positivity
    have h5 := h3.const_mul_atTop h4
    have h6 : Tendsto (fun x : ℝ => ((x : ℝ) / 40) ^ ((1 : ℝ) / 4) / Real.log x) atTop atTop := by
      apply h5.congr'
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [Real.div_rpow hx.le (by norm_num)]
      simp only [Pi.inv_apply, inv_div]
      field_simp
    exact h6.comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop_mono' atTop _ hlim
  filter_upwards [eventually_ge_atTop 4] with n hn
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  exact div_le_div_of_nonneg_right (key n hn) hlog.le

end E126
