import Submission.Korselt

/-!
# Counting Carmichael numbers with a large Carmichael-function value

Korselt's congruence, a coprime block decomposition, and the Chinese remainder
theorem give a uniform count for Carmichael numbers whose Carmichael function
is large. No assertion about the unrestricted counting problem is used.
-/

namespace Erdos1057

/-- A Carmichael number bounded by `X`, whose Carmichael function is at least `Y²`. -/
def highLambdaCarmichaels (X Y : ℕ) : Set ℕ :=
  {n | IsCarmichael n ∧ n ≤ X ∧ Y * Y ≤ ArithmeticFunction.Carmichael n}

/-- A coprime, squarefree, positive decomposition into two blocks of size at most `B`. -/
def HasBalancedBlocks (n B : ℕ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Squarefree a ∧ Squarefree b ∧ a.Coprime b ∧
    n = a * b ∧ a ≤ B ∧ b ≤ B

/-- The restricted family, before providing a balanced decomposition. -/
def balancedHighLambdaCarmichaels (X Y B : ℕ) : Set ℕ :=
  {n | n ∈ highLambdaCarmichaels X Y ∧ HasBalancedBlocks n B}

/-- A divisor of a Carmichael number is coprime to its own Carmichael function. -/
theorem isCarmichael_coprime_divisor_lambda {n a : ℕ}
    (hn : IsCarmichael n) (ha : a ∣ n) : a.Coprime (ArithmeticFunction.Carmichael a) := by
  have hn1 : 1 ≤ n := by
    have hn' := (hn 1 (by omega) (by simp)).2.2
    omega
  have hdiv : ArithmeticFunction.Carmichael a ∣ n - 1 :=
    (ArithmeticFunction.carmichael_dvd ha).trans (isCarmichael_lambda_dvd_sub_one hn)
  have hmod : n ≡ 1 [MOD ArithmeticFunction.Carmichael a] :=
    ((Nat.modEq_iff_dvd' hn1).mpr hdiv).symm
  obtain ⟨b, hb⟩ := ha
  rw [hb] at hmod
  exact Nat.coprime_of_mul_modEq_one b hmod

private theorem residue_card_le (X M r : ℕ) (hM : 0 < M) :
    ((Finset.range (X + 1)).filter (fun n => n ≡ r [MOD M])).card ≤ X / M + 1 := by
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card (X + 1) hM r,
    Nat.succ_div]
  split_ifs with hd hr <;> try omega

/-- With a fixed divisor `a`, the Carmichael numbers at most `X` lie in a single
CRT residue class modulo `a * λ(a)`. The bound works even if there are none. -/
theorem fixedBlockCarmichaels_card_le (X a : ℕ)
    [DecidablePred (fun n : ℕ => IsCarmichael n)] (ha : 0 < a)
    (hLam : 0 < ArithmeticFunction.Carmichael a) :
    ((Finset.range (X + 1)).filter (fun n => IsCarmichael n ∧ a ∣ n)).card ≤
      X / (a * ArithmeticFunction.Carmichael a) + 1 := by
  classical
  let M : ℕ := a * ArithmeticFunction.Carmichael a
  have hM : 0 < M := Nat.mul_pos ha hLam
  by_cases hcop : a.Coprime (ArithmeticFunction.Carmichael a)
  · let r : ℕ := (Nat.chineseRemainder hcop 0 1).val
    have hsub :
        (Finset.range (X + 1)).filter (fun n => IsCarmichael n ∧ a ∣ n) ⊆
          (Finset.range (X + 1)).filter (fun n => n ≡ r [MOD M]) := by
      intro n hn
      obtain ⟨hX, hnC, han⟩ := Finset.mem_filter.mp hn
      have hn1 : 1 ≤ n := by
        have hn' := (hnC 1 (by omega) (by simp)).2.2
        omega
      have hmod0 : n ≡ 0 [MOD a] := Nat.modEq_zero_iff_dvd.mpr han
      have hmod1 : n ≡ 1 [MOD ArithmeticFunction.Carmichael a] :=
        ((Nat.modEq_iff_dvd' hn1).mpr
          ((ArithmeticFunction.carmichael_dvd han).trans
            (isCarmichael_lambda_dvd_sub_one hnC))).symm
      exact Finset.mem_filter.mpr
        ⟨hX, Nat.chineseRemainder_modEq_unique hcop hmod0 hmod1⟩
    exact (Finset.card_le_card hsub).trans (residue_card_le X M r hM)
  · have he : (Finset.range (X + 1)).filter (fun n => IsCarmichael n ∧ a ∣ n) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have h := (Finset.mem_filter.mp hn).2
      exact hcop (isCarmichael_coprime_divisor_lambda h.1 h.2)
    simp [he]

/-- In a coprime split, if `λ(n) ≥ Y²`, at least one block has Carmichael
function at least `Y`. -/
theorem highLambda_exists_block {n Y B : ℕ} (hY : 1 ≤ Y)
    (hLam : Y * Y ≤ ArithmeticFunction.Carmichael n) (hs : HasBalancedBlocks n B) :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ B ∧ a ∣ n ∧ Y ≤ ArithmeticFunction.Carmichael a := by
  obtain ⟨a, b, ha, hb, _, _, hcop, hn, haB, hbB⟩ := hs
  have hfun : ArithmeticFunction.Carmichael n =
      Nat.lcm (ArithmeticFunction.Carmichael a) (ArithmeticFunction.Carmichael b) := by
    rw [hn, ArithmeticFunction.carmichael_mul hcop]
  have hlcmpos : 0 < Nat.lcm (ArithmeticFunction.Carmichael a)
      (ArithmeticFunction.Carmichael b) := by
    rw [hfun] at hLam
    have hYY : 0 < Y * Y := Nat.mul_pos (by omega) (by omega)
    omega
  have hLama : 0 < ArithmeticFunction.Carmichael a := by
    by_contra h
    have hz : ArithmeticFunction.Carmichael a = 0 := by omega
    simp [hz] at hlcmpos
  have hLamb : 0 < ArithmeticFunction.Carmichael b := by
    by_contra h
    have hz : ArithmeticFunction.Carmichael b = 0 := by omega
    simp [hz] at hlcmpos
  have hprod : ArithmeticFunction.Carmichael n ≤
      ArithmeticFunction.Carmichael a * ArithmeticFunction.Carmichael b := by
    rw [hfun]
    exact Nat.lcm_le_mul hLama hLamb
  by_cases hlarge : Y ≤ ArithmeticFunction.Carmichael a
  · exact ⟨a, ha, haB, hn ▸ dvd_mul_right a b, hlarge⟩
  · have hbY : Y ≤ ArithmeticFunction.Carmichael b := by
      by_contra hbsmall
      have ha' : ArithmeticFunction.Carmichael a ≤ Y - 1 := by omega
      have hb' : ArithmeticFunction.Carmichael b ≤ Y - 1 := by omega
      have hsmall : ArithmeticFunction.Carmichael a * ArithmeticFunction.Carmichael b ≤
          (Y - 1) * (Y - 1) := Nat.mul_le_mul ha' hb'
      have hlt : (Y - 1) * (Y - 1) < Y * Y := by
        have hy : Y - 1 + 1 = Y := Nat.sub_add_cancel (by omega)
        nlinarith
      omega
    refine ⟨b, hb, hbB, ?_, hbY⟩
    rw [hn, Nat.mul_comm]
    exact dvd_mul_right b a

/-- A harmonic-sum bound for a cutoff `B ≤ X`. -/
private theorem harmonic_cutoff_le_log (X B : ℕ) (hB : B ≤ X) :
    (∑ a ∈ Finset.Icc 1 B, (1 : ℝ) / (a : ℝ)) ≤ 1 + Real.log (X : ℝ) := by
  have hsum : (∑ a ∈ Finset.Icc 1 B, (1 : ℝ) / (a : ℝ)) = (harmonic B : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    simp only [Rat.cast_inv, Rat.cast_natCast, one_div]
  rw [hsum]
  have hlog : Real.log (B : ℝ) ≤ Real.log (X : ℝ) := by
    by_cases hB0 : B = 0
    · simpa only [hB0, Nat.cast_zero, Real.log_zero] using Real.log_natCast_nonneg X
    · exact Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hB0))
        (by exact_mod_cast hB)
  exact (harmonic_le_one_add_log B).trans (by linarith)

/-- The high-lambda count whenever each member admits the indicated balanced split:
`B + (X/Y) * (1 + log X)`, without counting coprime CRT classes multiple times. -/
theorem balancedHighLambdaCarmichaels_card_le (X Y B : ℕ)
    (hY : 1 ≤ Y) (hBX : B ≤ X) :
    ((balancedHighLambdaCarmichaels X Y B).ncard : ℝ) ≤
      (B : ℝ) + (X : ℝ) / (Y : ℝ) * (1 + Real.log (X : ℝ)) := by
  classical
  let choices : Finset ℕ := (Finset.Icc 1 B).filter
    (fun a => Y ≤ ArithmeticFunction.Carmichael a)
  let fibers : ℕ → Finset ℕ := fun a =>
    (Finset.range (X + 1)).filter (fun n => IsCarmichael n ∧ a ∣ n)
  have hcover : balancedHighLambdaCarmichaels X Y B ⊆
      ((choices.biUnion fibers : Finset ℕ) : Set ℕ) := by
    intro n hn
    obtain ⟨⟨hnC, hnX, hLam⟩, hs⟩ := hn
    obtain ⟨a, ha, haB, han, haY⟩ := highLambda_exists_block hY hLam hs
    apply Finset.mem_biUnion.mpr
    refine ⟨a, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨ha, haB⟩, haY⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hnC, han⟩
  have hcard : (balancedHighLambdaCarmichaels X Y B).ncard ≤
      ∑ a ∈ choices, (fibers a).card := by
    calc
      _ ≤ (choices.biUnion fibers).card := by
        simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hcover
      _ ≤ ∑ a ∈ choices, (fibers a).card := Finset.card_biUnion_le
  have hsum : ((∑ a ∈ choices, (fibers a).card : ℕ) : ℝ) ≤
      (B : ℝ) + (X : ℝ) / (Y : ℝ) *
        (∑ a ∈ Finset.Icc 1 B, (1 : ℝ) / (a : ℝ)) := by
    have hs : ((∑ a ∈ choices, (fibers a).card : ℕ) : ℝ) ≤
        ∑ a ∈ choices, ((X : ℝ) / (Y : ℝ) * (1 / (a : ℝ)) + 1) := by
      rw [Nat.cast_sum]
      apply Finset.sum_le_sum
      intro a ha
      have haY : Y ≤ ArithmeticFunction.Carmichael a := (Finset.mem_filter.mp ha).2
      have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
      have hblock := fixedBlockCarmichaels_card_le X a (by omega)
        (by omega : 0 < ArithmeticFunction.Carmichael a)
      have hcast : (((fibers a).card : ℝ)) ≤
          (X : ℝ) / ((a : ℝ) * (ArithmeticFunction.Carmichael a : ℝ)) + 1 := by
        calc
          _ ≤ ((X / (a * ArithmeticFunction.Carmichael a) + 1 : ℕ) : ℝ) := by
            exact_mod_cast hblock
          _ ≤ (X : ℝ) / ((a : ℝ) * (ArithmeticFunction.Carmichael a : ℝ)) + 1 := by
            simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_mul] using
              (add_le_add_left (Nat.cast_div_le (α := ℝ)
                (m := X) (n := a * ArithmeticFunction.Carmichael a)) 1)
      have haR : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
      have hYR : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
      have hLamR : (Y : ℝ) ≤ ArithmeticFunction.Carmichael a := by exact_mod_cast haY
      have hd : (X : ℝ) / ((a : ℝ) * (ArithmeticFunction.Carmichael a : ℝ)) ≤
          (X : ℝ) / (Y : ℝ) * (1 / (a : ℝ)) := by
        have hden := mul_le_mul_of_nonneg_left hLamR haR.le
        have := div_le_div_of_nonneg_left (Nat.cast_nonneg X) (mul_pos haR hYR) hden
        convert this using 1; ring
      exact hcast.trans (add_le_add_left hd 1)
    calc
      _ ≤ ∑ a ∈ choices, ((X : ℝ) / (Y : ℝ) * (1 / (a : ℝ)) + 1) := hs
      _ = choices.card + (X : ℝ) / (Y : ℝ) *
          ∑ a ∈ choices, (1 : ℝ) / (a : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        ring
      _ ≤ (B : ℝ) + (X : ℝ) / (Y : ℝ) *
          (∑ a ∈ Finset.Icc 1 B, (1 : ℝ) / (a : ℝ)) := by
        have hchoices : choices ⊆ Finset.Icc 1 B := Finset.filter_subset _ _
        have hcardB : (choices.card : ℝ) ≤ B := by
          exact_mod_cast (Finset.card_le_card hchoices).trans (by simp [Nat.card_Icc])
        have hsumle : (∑ a ∈ choices, (1 : ℝ) / (a : ℝ)) ≤
            ∑ a ∈ Finset.Icc 1 B, (1 : ℝ) / (a : ℝ) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hchoices (by intros; positivity)
        exact add_le_add hcardB (mul_le_mul_of_nonneg_left hsumle (by positivity))
  calc
    ((balancedHighLambdaCarmichaels X Y B).ncard : ℝ) ≤
        ((∑ a ∈ choices, (fibers a).card : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ (B : ℝ) + (X : ℝ) / (Y : ℝ) *
        (∑ a ∈ Finset.Icc 1 B, (1 : ℝ) / (a : ℝ)) := hsum
    _ ≤ (B : ℝ) + (X : ℝ) / (Y : ℝ) * (1 + Real.log (X : ℝ)) := by
      have hXY : 0 ≤ (X : ℝ) / (Y : ℝ) :=
        div_nonneg (Nat.cast_nonneg X) (Nat.cast_nonneg Y)
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left (harmonic_cutoff_le_log X B hBX) hXY) _


/- ## Splitting a squarefree Carmichael number -/

/-- Multiplying factors at most `T` until the product first passes `T`
produces a subproduct between `T + 1` and `T²`. -/
private theorem exists_subproduct_between (s : Finset ℕ) (T : ℕ) (hT : 1 ≤ T) :
    (∀ p ∈ s, p ≤ T) → T + 1 ≤ ∏ p ∈ s, p →
      ∃ u : Finset ℕ, u ⊆ s ∧ T + 1 ≤ ∏ p ∈ u, p ∧ ∏ p ∈ u, p ≤ T * T := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro _ hprod
      simp only [Finset.prod_empty] at hprod
      omega
  | @insert p s hps ih =>
      intro hfac hprod
      by_cases hrest : T + 1 ≤ ∏ q ∈ s, q
      · obtain ⟨u, hu, hlo, hhi⟩ := ih
          (fun q hq => hfac q (Finset.mem_insert_of_mem hq)) hrest
        exact ⟨u, hu.trans (Finset.subset_insert p s), hlo, hhi⟩
      · refine ⟨insert p s, Finset.Subset.refl _, hprod, ?_⟩
        have hpT : p ≤ T := hfac p (Finset.mem_insert_self p s)
        have hsT : (∏ q ∈ s, q) ≤ T := by omega
        rw [Finset.prod_insert hps]
        exact Nat.mul_le_mul hpT hsT

/-- Purely integer cutoff assumptions that ensure a balanced, coprime, squarefree
factorization for every Carmichael number up to `X`. -/
theorem isCarmichael_hasBalancedBlocks_of_bounds {n X T B : ℕ}
    (hn : IsCarmichael n) (hnX : n ≤ X) (hT : 1 ≤ T)
    (hT2 : T * T ≤ B) (hXB : X ≤ B * B) (hXT : X ≤ (T + 1) * B) :
    HasBalancedBlocks n B := by
  classical
  have hnpos : 0 < n := by
    have hn' := (hn 1 (by omega) (by simp)).2.2
    omega
  have hsq : Squarefree n := isCarmichael_squarefree hn
  by_cases hsmall : n ≤ T
  · have hnB : n ≤ B := by
      calc
        n ≤ T := hsmall
        _ = T * 1 := by simp
        _ ≤ T * T := Nat.mul_le_mul_left T hT
        _ ≤ B := hT2
    have hBpos : 0 < B := by omega
    exact ⟨n, 1, hnpos, by omega, hsq, squarefree_one, by simp,
      by simp, hnB, by omega⟩
  have hnprod : (∏ p ∈ n.primeFactors, p) = n := Nat.prod_primeFactors_of_squarefree hsq
  by_cases hbig : ∃ p ∈ n.primeFactors, T + 1 ≤ p
  · obtain ⟨p, hp, hpbig⟩ := hbig
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    obtain ⟨b, hb⟩ := Nat.dvd_of_mem_primeFactors hp
    have hfac : n = p * b := hb
    have hp_le_b : p ≤ b := isCarmichael_prime_le_cofactor hn hprime hfac
    have hp2 : p ^ 2 ≤ B ^ 2 := by
      calc
        p ^ 2 = p * p := by ring
        _ ≤ p * b := Nat.mul_le_mul_left p hp_le_b
        _ = n := hfac.symm
        _ ≤ X := hnX
        _ ≤ B * B := hXB
        _ = B ^ 2 := by ring
    have hpB : p ≤ B := (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp hp2
    have hbB : b ≤ B := by
      apply Nat.le_of_mul_le_mul_left (c := T + 1) ?_ (Nat.succ_pos T)
      calc
        (T + 1) * b ≤ p * b := Nat.mul_le_mul_right b hpbig
        _ = n := hfac.symm
        _ ≤ X := hnX
        _ ≤ (T + 1) * B := hXT
    have hsqfac : Squarefree (p * b) := by rw [← hfac]; exact hsq
    obtain ⟨hcop, hsp, hsb⟩ := Nat.squarefree_mul_iff.mp hsqfac
    have hbpos : 0 < b := by
      have hmulpos : 0 < p * b := by rw [← hfac]; exact hnpos
      exact Nat.pos_of_mul_pos_left hmulpos
    exact ⟨p, b, hprime.pos, hbpos, hsp, hsb, hcop, hfac, hpB, hbB⟩
  · have hall : ∀ p ∈ n.primeFactors, p ≤ T := by
      intro p hp
      by_contra h
      exact hbig ⟨p, hp, by omega⟩
    have hprodlo : T + 1 ≤ ∏ p ∈ n.primeFactors, p := by rw [hnprod]; omega
    obtain ⟨u, hu, huLo, huHi⟩ :=
      exists_subproduct_between n.primeFactors T hT hall hprodlo
    let a : ℕ := ∏ p ∈ u, p
    let b : ℕ := ∏ p ∈ n.primeFactors \ u, p
    have hfac : n = a * b := by
      calc
        n = ∏ p ∈ n.primeFactors, p := hnprod.symm
        _ = (∏ p ∈ n.primeFactors \ u, p) * (∏ p ∈ u, p) :=
          (Finset.prod_sdiff hu).symm
        _ = a * b := by dsimp [a, b]; ac_rfl
    have haB : a ≤ B := huHi.trans hT2
    have hbB : b ≤ B := by
      apply Nat.le_of_mul_le_mul_left (c := T + 1) ?_ (Nat.succ_pos T)
      calc
        (T + 1) * b ≤ a * b := Nat.mul_le_mul_right b huLo
        _ = n := hfac.symm
        _ ≤ X := hnX
        _ ≤ (T + 1) * B := hXT
    have hsqfac : Squarefree (a * b) := by rw [← hfac]; exact hsq
    obtain ⟨hcop, hsa, hsb⟩ := Nat.squarefree_mul_iff.mp hsqfac
    have hbpos : 0 < b := by
      have hmulpos : 0 < a * b := by rw [← hfac]; exact hnpos
      exact Nat.pos_of_mul_pos_left hmulpos
    exact ⟨a, b, by omega, hbpos, hsa, hsb, hcop, hfac, haB, hbB⟩

/-- The exact ceiling of `X^(2/3)` used for the two blocks. -/
noncomputable def highLambdaBlockCutoff (X : ℕ) : ℕ :=
  ⌈(X : ℝ) ^ ((2 : ℝ) / 3)⌉₊

/-- The integer part of `X^(1/3)`: a combinatorial threshold, not a block cutoff. -/
private noncomputable def cubeThreshold (X : ℕ) : ℕ :=
  ⌊(X : ℝ) ^ ((1 : ℝ) / 3)⌋₊

private theorem cutoff_properties (X : ℕ) (hX : 1 ≤ X) :
    1 ≤ cubeThreshold X ∧ cubeThreshold X * cubeThreshold X ≤ highLambdaBlockCutoff X ∧
    X ≤ highLambdaBlockCutoff X * highLambdaBlockCutoff X ∧
    X ≤ (cubeThreshold X + 1) * highLambdaBlockCutoff X ∧
    highLambdaBlockCutoff X ≤ X := by
  set T := cubeThreshold X
  set B := highLambdaBlockCutoff X
  let u : ℝ := (X : ℝ) ^ ((1 : ℝ) / 3)
  let v : ℝ := (X : ℝ) ^ ((2 : ℝ) / 3)
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hxpos : (0 : ℝ) < X := by linarith
  have hu1 : 1 ≤ u := Real.one_le_rpow hx (by norm_num)
  have hv0 : 0 ≤ v := Real.rpow_nonneg (Nat.cast_nonneg X) _
  have hTu : (T : ℝ) ≤ u := by
    simpa only [T, cubeThreshold, u] using (Nat.floor_le (by positivity : 0 ≤ u))
  have huT : u ≤ (T + 1 : ℝ) := by
    have := Nat.lt_floor_add_one u
    have h : u ≤ ((⌊u⌋₊ : ℕ) : ℝ) + 1 := this.le
    simpa only [T, cubeThreshold, u, Nat.cast_add, Nat.cast_one] using h
  have hvB : v ≤ (B : ℝ) := by
    simpa only [B, highLambdaBlockCutoff, v] using (Nat.le_ceil v)
  have hu2 : u ^ 2 = v := by
    dsimp [u, v]
    calc
      ((X : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 =
          (X : ℝ) ^ (((1 : ℝ) / 3) * (2 : ℝ)) :=
        (Real.rpow_mul_natCast (Nat.cast_nonneg X) ((1 : ℝ) / 3) 2).symm
      _ = (X : ℝ) ^ ((2 : ℝ) / 3) := by norm_num
  have huv : u * v = (X : ℝ) := by
    dsimp [u, v]
    rw [← Real.rpow_add hxpos]
    norm_num
  have hT1 : 1 ≤ T := by
    change 1 ≤ ⌊u⌋₊
    exact Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ u by simpa using hu1)
  have hT2 : T * T ≤ B := by
    have hreal : ((T * T : ℕ) : ℝ) ≤ (B : ℝ) := by
      calc
        ((T * T : ℕ) : ℝ) = (T : ℝ) ^ 2 := by push_cast; ring
        _ ≤ u ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg T) hTu 2
        _ = v := hu2
        _ ≤ B := hvB
    exact_mod_cast hreal
  have hXuV : u ≤ v := by
    dsimp [u, v]
    exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hX2 : X ≤ B * B := by
    have hreal : (X : ℝ) ≤ ((B * B : ℕ) : ℝ) := by
      calc
        (X : ℝ) = u * v := huv.symm
        _ ≤ v ^ 2 := by
          simpa only [pow_two] using mul_le_mul_of_nonneg_right hXuV hv0
        _ ≤ (B : ℝ) ^ 2 := pow_le_pow_left₀ hv0 hvB 2
        _ = ((B * B : ℕ) : ℝ) := by push_cast; ring
    exact_mod_cast hreal
  have hXT : X ≤ (T + 1) * B := by
    have hreal : (X : ℝ) ≤ (((T + 1) * B : ℕ) : ℝ) := by
      calc
        (X : ℝ) = u * v := huv.symm
        _ ≤ (T + 1 : ℝ) * v := mul_le_mul_of_nonneg_right huT hv0
        _ ≤ (T + 1 : ℝ) * (B : ℝ) :=
          mul_le_mul_of_nonneg_left hvB (by positivity)
        _ = (((T + 1) * B : ℕ) : ℝ) := by push_cast; ring
    exact_mod_cast hreal
  have hBX : B ≤ X := by
    apply Nat.ceil_le.mpr
    change v ≤ (X : ℝ)
    dsimp [v]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (2 : ℝ) / 3 ≤ 1)
  exact ⟨hT1, hT2, hX2, hXT, hBX⟩

/-- Every Carmichael number `n ≤ X` splits into positive, coprime squarefree
factors, *both* at most `⌈X^(2/3)⌉`. The case of a unit factor is allowed. -/
theorem isCarmichael_hasBalancedBlocks {n X : ℕ}
    (hn : IsCarmichael n) (hnX : n ≤ X) :
    HasBalancedBlocks n (highLambdaBlockCutoff X) := by
  have hX : 1 ≤ X := by
    have h2 := (hn 1 (by omega) (by simp)).2.2
    omega
  obtain ⟨hT, hT2, hXB, hXT, _⟩ := cutoff_properties X hX
  exact isCarmichael_hasBalancedBlocks_of_bounds hn hnX hT hT2 hXB hXT

/-- The balanced split together with the Carmichael-function lcm identity. -/
theorem isCarmichael_exists_balanced_blocks_lambda {n X : ℕ}
    (hn : IsCarmichael n) (hnX : n ≤ X) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Squarefree a ∧ Squarefree b ∧ a.Coprime b ∧
      n = a * b ∧ a ≤ highLambdaBlockCutoff X ∧ b ≤ highLambdaBlockCutoff X ∧
      ArithmeticFunction.Carmichael n =
        Nat.lcm (ArithmeticFunction.Carmichael a) (ArithmeticFunction.Carmichael b) := by
  obtain ⟨a, b, ha, hb, hsa, hsb, hcop, hfac, haB, hbB⟩ :=
    isCarmichael_hasBalancedBlocks hn hnX
  refine ⟨a, b, ha, hb, hsa, hsb, hcop, hfac, haB, hbB, ?_⟩
  rw [hfac, ArithmeticFunction.carmichael_mul hcop]

/-- Unconditional high-Carmichael-function count for `X ≥ 1`, with the
**exact** ceiling `⌈X^(2/3)⌉` and no multiplicative loss on either term. -/
theorem highLambdaCarmichaels_card_le_of_pos (X Y : ℕ)
    (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    ((highLambdaCarmichaels X Y).ncard : ℝ) ≤
      (highLambdaBlockCutoff X : ℝ) +
        (X : ℝ) / (Y : ℝ) * (1 + Real.log (X : ℝ)) := by
  have hsubset : highLambdaCarmichaels X Y ⊆
      balancedHighLambdaCarmichaels X Y (highLambdaBlockCutoff X) := by
    intro n hn
    exact ⟨hn, isCarmichael_hasBalancedBlocks hn.1 hn.2.1⟩
  have hfinite : (balancedHighLambdaCarmichaels X Y (highLambdaBlockCutoff X)).Finite :=
    (Set.finite_le_nat X).subset (fun n hn => hn.1.2.1)
  have hcount : (highLambdaCarmichaels X Y).ncard ≤
      (balancedHighLambdaCarmichaels X Y (highLambdaBlockCutoff X)).ncard :=
    Set.ncard_le_ncard hsubset hfinite
  calc
    ((highLambdaCarmichaels X Y).ncard : ℝ) ≤
        ((balancedHighLambdaCarmichaels X Y (highLambdaBlockCutoff X)).ncard : ℝ) := by
      exact_mod_cast hcount
    _ ≤ _ := balancedHighLambdaCarmichaels_card_le X Y (highLambdaBlockCutoff X)
      hY (cutoff_properties X hX).2.2.2.2

/-- The same sharp-ceiling estimate including the endpoint `X = 0` (where the
count and both terms of the bound vanish). Valid even for `Y = 1`. -/
theorem highLambdaCarmichaels_card_le (X Y : ℕ) (hY : 1 ≤ Y) :
    ((highLambdaCarmichaels X Y).ncard : ℝ) ≤
      (highLambdaBlockCutoff X : ℝ) +
        (X : ℝ) / (Y : ℝ) * (1 + Real.log (X : ℝ)) := by
  by_cases hX : X = 0
  · subst X
    have hempty : highLambdaCarmichaels 0 Y = ∅ := by
      ext n
      constructor
      · intro hn
        have hnlarge := (hn.1 1 (by omega) (by simp)).2.2
        have hn0 : n ≤ 0 := hn.2.1
        omega
      · simp
    have hcut : highLambdaBlockCutoff 0 = 0 := by
      norm_num [highLambdaBlockCutoff]
    simp only [hempty, hcut, Set.ncard_empty, Nat.cast_zero, Real.log_zero,
      zero_div, zero_mul, add_zero, le_refl]
  · exact highLambdaCarmichaels_card_le_of_pos X Y (by omega) hY

/-- Carmichael numbers `n ≤ X` with `λ(n) ≥ X^κ`, for a real exponent `κ`. -/
def highLambdaRealCarmichaels (X : ℕ) (κ : ℝ) : Set ℕ :=
  {n | IsCarmichael n ∧ n ≤ X ∧
    (X : ℝ) ^ κ ≤ (ArithmeticFunction.Carmichael n : ℝ)}

/-- Real-exponent form of the high-lambda bound. The factor `2` comes only from
rounding `X^(κ/2)` down to an integer; the leading term has the *exact* ceiling. -/
theorem highLambdaRealCarmichaels_card_le_of_pos (X : ℕ) (κ : ℝ)
    (hX : 1 ≤ X) (hκ : 0 < κ) :
    ((highLambdaRealCarmichaels X κ).ncard : ℝ) ≤
      (highLambdaBlockCutoff X : ℝ) +
        2 * (X : ℝ) ^ (1 - κ / 2) * (1 + Real.log (X : ℝ)) := by
  let R : ℝ := (X : ℝ) ^ (κ / 2)
  let Y : ℕ := ⌊R⌋₊
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hxpos : (0 : ℝ) < X := by linarith
  have hR1 : 1 ≤ R := Real.one_le_rpow hx (by positivity)
  have hY1 : 1 ≤ Y := Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ R by simpa using hR1)
  have hYle : (Y : ℝ) ≤ R := Nat.floor_le (by positivity : 0 ≤ R)
  have hRle : R ≤ 2 * (Y : ℝ) := by
    have hh : R < (Y : ℝ) + 1 := by
      simpa only [Y] using Nat.lt_floor_add_one R
    have hy : (1 : ℝ) ≤ Y := by exact_mod_cast hY1
    linarith
  have hR2 : R ^ 2 = (X : ℝ) ^ κ := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg X) (κ / 2) 2]
    congr 1
    ring
  have hsubset : highLambdaRealCarmichaels X κ ⊆ highLambdaCarmichaels X Y := by
    intro n hn
    obtain ⟨hnC, hnX, hnlarge⟩ := hn
    have hlargeNat : Y * Y ≤ ArithmeticFunction.Carmichael n := by
      have hreal : ((Y * Y : ℕ) : ℝ) ≤ (ArithmeticFunction.Carmichael n : ℝ) := by
        calc
          ((Y * Y : ℕ) : ℝ) = (Y : ℝ) ^ 2 := by push_cast; ring
          _ ≤ R ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg Y) hYle 2
          _ = (X : ℝ) ^ κ := hR2
          _ ≤ _ := hnlarge
      exact_mod_cast hreal
    exact ⟨hnC, hnX, hlargeNat⟩
  have hfinite : (highLambdaCarmichaels X Y).Finite :=
    (Set.finite_le_nat X).subset (fun n hn => hn.2.1)
  have hcard : (highLambdaRealCarmichaels X κ).ncard ≤
      (highLambdaCarmichaels X Y).ncard := Set.ncard_le_ncard hsubset hfinite
  have hratio : (X : ℝ) / (Y : ℝ) ≤ 2 * (X : ℝ) ^ (1 - κ / 2) := by
    have hypos : (0 : ℝ) < Y := by exact_mod_cast hY1
    have hrpos : (0 : ℝ) < R := by linarith
    have hdiv : (X : ℝ) / (Y : ℝ) ≤ (2 * (X : ℝ)) / R := by
      apply (div_le_div_iff₀ hypos hrpos).mpr
      calc
        (X : ℝ) * R ≤ (X : ℝ) * (2 * (Y : ℝ)) :=
          mul_le_mul_of_nonneg_left hRle (Nat.cast_nonneg X)
        _ = (2 * (X : ℝ)) * (Y : ℝ) := by ring
    have hpow : (X : ℝ) / R = (X : ℝ) ^ (1 - κ / 2) := by
      dsimp [R]
      rw [Real.rpow_sub hxpos, Real.rpow_one]
    calc
      (X : ℝ) / (Y : ℝ) ≤ 2 * (X : ℝ) / R := by simpa only [mul_div_assoc] using hdiv
      _ = 2 * ((X : ℝ) / R) := by ring
      _ = 2 * (X : ℝ) ^ (1 - κ / 2) := by rw [hpow]
  have hlog : 0 ≤ 1 + Real.log (X : ℝ) := by
    have := Real.log_natCast_nonneg X
    linarith
  calc
    ((highLambdaRealCarmichaels X κ).ncard : ℝ) ≤
        ((highLambdaCarmichaels X Y).ncard : ℝ) := by exact_mod_cast hcard
    _ ≤ (highLambdaBlockCutoff X : ℝ) +
        (X : ℝ) / (Y : ℝ) * (1 + Real.log (X : ℝ)) :=
      highLambdaCarmichaels_card_le X Y hY1
    _ ≤ (highLambdaBlockCutoff X : ℝ) +
        2 * (X : ℝ) ^ (1 - κ / 2) * (1 + Real.log (X : ℝ)) := by
      exact add_le_add_right (mul_le_mul_of_nonneg_right hratio hlog) _

/-- The real-exponent high-lambda estimate for every natural cutoff, including
`X = 0`, at which the family is empty and the right-hand side is nonnegative. -/
theorem highLambdaRealCarmichaels_card_le (X : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ((highLambdaRealCarmichaels X κ).ncard : ℝ) ≤
      (highLambdaBlockCutoff X : ℝ) +
        2 * (X : ℝ) ^ (1 - κ / 2) * (1 + Real.log (X : ℝ)) := by
  by_cases hX : X = 0
  · subst X
    have hempty : highLambdaRealCarmichaels 0 κ = ∅ := by
      ext n
      constructor
      · intro hn
        have hnlarge := (hn.1 1 (by omega) (by simp)).2.2
        have hn0 : n ≤ 0 := hn.2.1
        omega
      · simp
    have hcut : highLambdaBlockCutoff 0 = 0 := by
      norm_num [highLambdaBlockCutoff]
    simp only [hempty, hcut, Set.ncard_empty, Nat.cast_zero, Real.log_zero,
      zero_add, add_zero, mul_one]
    positivity
  · exact highLambdaRealCarmichaels_card_le_of_pos X κ (by omega) hκ

end Erdos1057

#print axioms Erdos1057.isCarmichael_exists_balanced_blocks_lambda
#print axioms Erdos1057.highLambdaCarmichaels_card_le
#print axioms Erdos1057.highLambdaRealCarmichaels_card_le
