import Submission.ActivePrimeSupply

/-! Relative concentration estimates can fail at an exact quadratic scale even
when every old class has two private points. No optimality or interval cover is
asserted; in fact the construction explicitly preserves survivor 1. -/
namespace Erdos970.ActivePrimePadding
open Finset OptimalCoverCore LongIntervalConcentration

set_option maxHeartbeats 0 in
/-- An all-active strengthening of the exact-quadratic concentration obstruction.
This does not negate the largest-prime increment or the Jacobsthal conjecture. -/
theorem unbounded_active_exact (A B C K : ℕ) (hC : 0 < C) :
    ∃ (P : Finset ℕ) (r : ℕ → ℕ) (p m : ℕ),
      K ≤ P.card ∧ m = C * (P.card + 1) ^ 2 ∧
      (∀ q ∈ P, q.Prime ∧ q < p) ∧ p.Prime ∧
      (∀ q ∈ P, 2 ≤ (privatePositions m P r q).card) ∧
      (∀ q ∈ insert p P,
        2 ≤ (privatePositions m (insert p P) (Function.update r p 0) q).card) ∧
      1 ∈ survivors m P r ∧
      B * (survivors m P r).card + A * p <
        p * ((survivors m P r).filter (fun i => i ≡ 0 [MOD p])).card := by
  classical
  let T := A + 2
  let L := 2 * (T + 1)
  have hL : 0 < L := by dsimp [L, T]; omega
  obtain ⟨P₀, hP₀, hden⟩ := ConstructiveCover.exists_prime_tail_density T (2 * (B + 1) * L)
  let N := ∏ q ∈ P₀, q
  let F := ∏ q ∈ P₀, (q - 1)
  let W := coreWitnesses P₀
  have hN : 0 < N := Finset.prod_pos (fun q hq => (hP₀ q hq).1.pos)
  let D := 32 * C * N
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨k, H, R, hk, hkpos, hRcard, hH, hR⟩ := exists_prime_supply D (8 * N + L)
    (K + 2 * L + 2 * B * F + P₀.card + 2 + P₀.sup id + 2 * W.card + T + 2 + 64 * N)
  let m := C * (P₀.card + k + 1) ^ 2
  have hm : k ^ 2 ≤ m := by
    have hc : 1 ≤ C := hC
    have hh := Nat.mul_le_mul_right ((P₀.card + k + 1) ^ 2) hc
    dsimp [m]; nlinarith
  have hmupper : m ≤ 4 * C * k ^ 2 := by
    have hb : P₀.card + k + 1 ≤ 2 * k := by omega
    have hh := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hb 2)
    dsimp [m]; nlinarith only [hh]
  have hcore (q : ℕ) (hq : q ∈ P₀) : q < k := by
    have hqle : q ≤ P₀.sup id := Finset.le_sup (f := id) hq
    omega
  have hdis : Disjoint P₀ R := by
    rw [disjoint_left]
    intro q hq hqR
    have hqk := hcore q hq
    have hDk : k ≤ D * k := by nlinarith
    have := (hR q hqR).2.1
    omega
  have hHL : L * H < k ^ 2 := by nlinarith only [hH]
  have hHN : 8 * N * H < k ^ 2 := by nlinarith only [hH]
  let x := m / L
  have hkx : k ≤ x := by
    apply (Nat.le_div_iff_mul_le hL).mpr
    have hkL : L ≤ k := by omega
    nlinarith
  obtain ⟨p, hp, hxp, hpx⟩ := Nat.exists_prime_lt_and_le_two_mul x (by omega)
  have hkp : k < p := by omega
  have hqp (q : ℕ) (hq : q ∈ P₀ ∪ R) : q < p := by
    rcases mem_union.mp hq with hq | hq
    · exact (hcore q hq).trans hkp
    · have hHx : H ≤ x := (Nat.le_div_iff_mul_le hL).mpr (by nlinarith)
      exact (hR q hq).2.2.trans_le (by omega)
  have hTm : (T + 1) * p ≤ m := by
    have hd : x * L ≤ m := Nat.div_mul_le_self m L
    have hh := Nat.mul_le_mul_left (T + 1) hpx
    dsimp only [L] at hd
    nlinarith only [hd, hh]
  have hmLp : m < L * p := by
    have hd := Nat.lt_mul_div_succ m hL
    change m < L * (x + 1) at hd
    have hh := Nat.mul_le_mul_left L (show x + 1 ≤ p by omega)
    omega
  let Z := W ∪ insert 1 ((range L).image (fun j => j * p))
  have hZ : Z.card ≤ W.card + L + 1 := by
    have h0 := card_union_le W (insert 1 ((range L).image (fun j => j * p)))
    have h1 := card_insert_le 1 ((range L).image (fun j => j * p))
    have h2 := card_image_le (s := range L) (f := fun j => j * p)
    simp only [card_range] at h2
    dsimp [Z]; omega
  let d := k / (8 * N) + 1
  have hd (q : ℕ) (hq : q ∈ R) (a : ℕ) :
      ((range m).filter (fun i => i ≡ a [MOD q])).card ≤ d := by
    apply (residue_card_le m q a (hR q hq).1.pos).trans
    have hqD : 32 * C * N * k ≤ q := (hR q hq).2.1.le
    have hdiv : (4 * C * k) * ((m / q) * (8 * N)) ≤ (4 * C * k) * k := by
      calc
        _ = (32 * C * N * k) * (m / q) := by ring
        _ ≤ q * (m / q) := Nat.mul_le_mul_right _ hqD
        _ ≤ m := Nat.mul_div_le m q
        _ ≤ 4 * C * k ^ 2 := hmupper
        _ = _ := by ring
    have hfactor : 0 < 4 * C * k := by positivity
    have hdiv' : (m / q) * (8 * N) ≤ k := by nlinarith only [hdiv, hfactor]
    have hh := (Nat.le_div_iff_mul_le (by positivity : 0 < 8 * N)).mpr hdiv'
    dsimp [d]; omega
  have hw : HasWitnesses m P₀ (fun _ => 0) W := by
    apply core_witnesses m P₀ (fun q hq => (hP₀ q hq).1)
    intro q hq
    have hqk := hcore q hq
    nlinarith
  have hroom : H + (3 * R.card + W.card + Z.card) * d <
      (survivors m P₀ (fun _ => 0)).card := by
    rw [hRcard]
    have hh := padding_budget N k (W.card + Z.card) H m hN (by omega)
      (by omega) hHN hm
    apply (by simpa [d, Nat.add_assoc] using hh :
      H + (3 * k + W.card + Z.card) * d < m / N).trans_le
    exact zero_survivors_lower m P₀ (fun q hq => (hP₀ q hq).1)
  obtain ⟨r, hr, hsafe, hprivate⟩ := pad_active m H d R P₀ (fun _ => 0) W Z hdis hw
    (fun q hq => ⟨(hR q hq).1.pos, (hR q hq).2.2.le, hd q hq⟩) hroom
  let P := P₀ ∪ R
  have hPcard : P.card = P₀.card + k := by
    rw [show P = P₀ ∪ R from rfl, card_union_of_disjoint hdis, hRcard]
  have hprime (q : ℕ) (hq : q ∈ P) : q.Prime := by
    rcases mem_union.mp hq with hq | hq
    · exact (hP₀ q hq).1
    · exact (hR q hq).1
  have hcounts : (survivors m P r).card ≤ (survivors m P₀ (fun _ => 0)).card := by
    apply card_le_card
    intro i hi
    obtain ⟨him, hiP⟩ := (mem_survivors _ _ _ _).mp hi
    apply (mem_survivors _ _ _ _).mpr
    refine ⟨him, ?_⟩
    intro q hq hbad
    apply hiP q (mem_union_left _ hq)
    simpa only [hr q hq] using hbad
  have hsmall : B * (survivors m P r).card ≤ p := by
    have hcount := (Nat.mul_le_mul_left N hcounts).trans
      (zero_survivors_scaled_le m P₀ (fun q hq => (hP₀ q hq).1))
    change N * (survivors m P r).card ≤ F * (m + N) at hcount
    have hcount' : N * (survivors m P r).card ≤ F * (L * p + N) :=
      hcount.trans (Nat.mul_le_mul_left F (by omega))
    change 2 * (B + 1) * L * F ≤ N at hden
    have hd : 2 * B * L * F ≤ N := by nlinarith
    have hBF : 2 * B * F ≤ p := by omega
    have hd' := Nat.mul_le_mul_right p hd
    have hBF' := Nat.mul_le_mul_right N hBF
    have hcount'' := Nat.mul_le_mul_left (2 * B) hcount'
    nlinarith
  have htarget (j : ℕ) (hj : j < T) : (j + 1) * p ∈ survivors m P r := by
    apply (mem_survivors _ _ _ _).mpr
    refine ⟨lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (by omega) hp.pos) hTm, ?_⟩
    intro q hq hbad
    rcases mem_union.mp hq with hq | hq
    · rw [hr q hq] at hbad
      have hh := Nat.modEq_zero_iff_dvd.mp hbad
      rcases (hP₀ q hq).1.dvd_mul.mp hh with hd | hd
      · have := Nat.le_of_dvd (by omega : 0 < j + 1) hd
        have := (hP₀ q hq).2
        omega
      · have he : q = p := ((Nat.dvd_prime hp).mp hd).resolve_left (hP₀ q hq).1.ne_one
        exact (hqp q (mem_union_left _ hq)).ne he
    · exact hsafe q hq ((j + 1) * p)
        (mem_union_right _ (mem_insert_of_mem (mem_image.mpr
          ⟨j + 1, mem_range.mpr (by dsimp [L]; omega), rfl⟩))) hbad
  have hremoved : T ≤ ((survivors m P r).filter (fun i => i ≡ 0 [MOD p])).card := by
    have hinj : Function.Injective (fun j : ℕ => (j + 1) * p) := by
      intro i j he
      have := Nat.eq_of_mul_eq_mul_right hp.pos he
      omega
    have hsub : (range T).image (fun j => (j + 1) * p) ⊆
        (survivors m P r).filter (fun i => i ≡ 0 [MOD p]) := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
      exact mem_filter.mpr ⟨htarget j (mem_range.mp hj),
        Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left p (j + 1))⟩
    simpa only [card_image_of_injective _ hinj, card_range] using card_le_card hsub
  have hone : 1 ∈ survivors m P r := by
    apply (mem_survivors _ _ _ _).mpr
    have ht : 0 < T := by dsimp [T]; omega
    refine ⟨by nlinarith only [ht, hp.two_le, hTm], ?_⟩
    intro q hq hbad
    rcases mem_union.mp hq with hq | hq
    · rw [hr q hq] at hbad
      exact (hP₀ q hq).1.not_dvd_one (Nat.modEq_zero_iff_dvd.mp hbad)
    · exact hsafe q hq 1 (mem_union_right _ (mem_insert_self _ _)) hbad
  have hpP : p ∉ P := fun hh => (hqp p hh).false
  have hWsafe (u : ℕ) (hu : u ∈ W) : ¬u ≡ 0 [MOD p] := by
    have hpnot (q : ℕ) (hq : q ∈ P₀) : ¬p ∣ q := by
      intro hd
      have he : p = q := ((Nat.dvd_prime (hP₀ q hq).1).mp hd).resolve_left hp.ne_one
      exact (hqp q (mem_union_left _ hq)).ne he.symm
    rcases mem_union.mp hu with hu | hu
    · exact fun he => hpnot u hu (Nat.modEq_zero_iff_dvd.mp he)
    · obtain ⟨q, hq, rfl⟩ := mem_image.mp hu
      exact fun he => hpnot q hq (hp.dvd_of_dvd_pow (Nat.modEq_zero_iff_dvd.mp he))
  have hcoreprivate (q u : ℕ) (hu : u ∈ W)
      (hpriv : u ∈ privatePositions m P₀ (fun _ => 0) q) (hq : q ∈ P₀) :
      u ∈ privatePositions m P r q := by
    rw [mem_private_iff] at hpriv ⊢
    refine ⟨hpriv.1, by simpa [hr q hq] using hpriv.2.1, ?_⟩
    intro t ht htq
    rcases mem_union.mp ht with ht | ht
    · simpa only [hr t ht] using hpriv.2.2 t ht htq
    · exact hsafe t ht u (mem_union_left _ hu)
  have hnew_safe (q u : ℕ) (hq : q ∈ R)
      (hu : u ∈ privatePositions m P r q) : ¬u ≡ 0 [MOD p] := by
    intro hup
    have hpriv := (mem_private_iff _ _ _ _ _).mp hu
    have hidx : u / p < L := (Nat.div_lt_iff_lt_mul hp.pos).mpr (hpriv.1.trans hmLp)
    have hue : (u / p) * p = u := Nat.div_mul_cancel (Nat.modEq_zero_iff_dvd.mp hup)
    have huZ : u ∈ Z := mem_union_right _ (mem_insert_of_mem
      (mem_image.mpr ⟨u / p, mem_range.mpr hidx, hue⟩))
    exact hsafe q hq u huZ hpriv.2.1
  have hpost : ∀ q ∈ insert p P,
      2 ≤ (privatePositions m (insert p P) (Function.update r p 0) q).card := by
    intro q hq
    rcases mem_insert.mp hq with heq | hqP
    · subst q
      have h1 := new_private (q := p) (a := 0) (htarget 0 (by dsimp [T]; omega))
        (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left p 1))
      have h2 := new_private (q := p) (a := 0) (htarget 1 (by dsimp [T]; omega))
        (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left p 2))
      apply one_lt_card.mpr
      refine ⟨1 * p, h1, 2 * p, h2, ?_⟩
      nlinarith only [hp.pos]
    · rcases mem_union.mp hqP with hq₀ | hqR
      · obtain ⟨u, hu, v, hv, huv, hup, hvp⟩ := hw q hq₀
        apply one_lt_card.mpr
        exact ⟨u, private_preserved hpP hqP (hcoreprivate q u hu hup hq₀) (hWsafe u hu),
          v, private_preserved hpP hqP (hcoreprivate q v hv hvp hq₀) (hWsafe v hv), huv⟩
      · obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp (hprivate q hqP)
        apply one_lt_card.mpr
        exact ⟨u, private_preserved hpP hqP hu (hnew_safe q u hqR hu),
          v, private_preserved hpP hqP hv (hnew_safe q v hqR hv), huv⟩
  refine ⟨P, r, p, m, by omega, ?_, (fun q hq => ⟨hprime q hq, hqp q hq⟩),
    hp, hprivate, hpost, hone, ?_⟩
  · simp only [m, hPcard]
  · have hh := Nat.mul_le_mul_left p hremoved
    have hp0 := hp.pos
    dsimp only [T] at hh
    nlinarith

/-- The same obstruction stated against arbitrary real constants, with activity
required both before and after insertion of the largest prime. -/
theorem not_uniform_active_relative_estimate (C K : ℕ) (hC : 0 < C) :
    ¬∃ A B : ℝ, ∀ (P : Finset ℕ) (r : ℕ → ℕ) (p m : ℕ), K ≤ P.card →
      m = C * (P.card + 1) ^ 2 →
      (∀ q ∈ P, q.Prime ∧ q < p) → p.Prime →
      (∀ q ∈ P, 2 ≤ (privatePositions m P r q).card) →
      (∀ q ∈ insert p P,
        2 ≤ (privatePositions m (insert p P) (Function.update r p 0) q).card) →
      (((survivors m P r).filter
        (fun i => i ≡ 0 [MOD p])).card : ℝ) ≤
          B * (survivors m P r).card / p + A := by
  rintro ⟨A, B, h⟩
  obtain ⟨a, ha⟩ := exists_nat_gt A
  obtain ⟨b, hb⟩ := exists_nat_gt B
  obtain ⟨P, r, p, m, hK, hm, hP, hp, hpre, hpost, _, hbad⟩ :=
    unbounded_active_exact a b C K hC
  have hu := h P r p m hK hm hP hp hpre hpost
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hu' := mul_le_mul_of_nonneg_right hu hpR.le
  rw [add_mul, div_mul_cancel₀ _ hpR.ne'] at hu'
  have hbadR : (b : ℝ) * (survivors m P r).card + (a : ℝ) * p <
      (p : ℝ) * ((survivors m P r).filter (fun i => i ≡ 0 [MOD p])).card := by
    exact_mod_cast hbad
  have hA := mul_le_mul_of_nonneg_right ha.le hpR.le
  have hB := mul_le_mul_of_nonneg_right hb.le (Nat.cast_nonneg (survivors m P r).card)
  nlinarith only [hu', hbadR, hA, hB]

/-- In particular these counterexamples are not covers after insertion either. -/
lemma one_survives_insert {P : Finset ℕ} {r : ℕ → ℕ} {p m : ℕ}
    (hp : p.Prime) (hpP : p ∉ P) (hone : 1 ∈ survivors m P r) :
    1 ∈ survivors m (insert p P) (Function.update r p 0) := by
  rw [survivors_insert_update m P r p 0 hpP]
  exact mem_filter.mpr ⟨hone, fun hh => hp.not_dvd_one (Nat.modEq_zero_iff_dvd.mp hh)⟩

#print axioms not_uniform_active_relative_estimate
#print axioms one_survives_insert
#print axioms unbounded_active_exact
end Erdos970.ActivePrimePadding
