import Submission.HighLambda
import Submission.LargePrime

/-!
# Two blocks under a prime-factor cutoff

The greedy subproduct argument in `Submission.HighLambda` overshoots a threshold
`T` by at most one prime factor. When every prime factor is at most `Y`, the
overshoot is at most `T * Y`. Taking `T = X / (⌊√(X * Y)⌋ + 1)` yields two
coprime squarefree blocks of size at most `⌊√(X * Y)⌋ + 1`.

The minimum with `X` in the final cutoff permits direct use of the existing
high-Carmichael-function counting theorem. The complementary large-prime
family is bounded by `Submission.LargePrime`.
-/

namespace Erdos1057

/-- A first-crossing subproduct of factors at most `Y` overshoots `T` by at
most a factor of `Y`. This is the prime-cutoff version of the greedy step in
`isCarmichael_hasBalancedBlocks_of_bounds`. -/
private theorem exists_subproduct_between_cutoff (s : Finset ℕ) (T Y : ℕ)
    (hT : 1 ≤ T) (hfac : ∀ p ∈ s, p ≤ Y)
    (hprod : T + 1 ≤ ∏ p ∈ s, p) :
    ∃ u : Finset ℕ, u ⊆ s ∧ T + 1 ≤ ∏ p ∈ u, p ∧ ∏ p ∈ u, p ≤ T * Y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty] at hprod
      omega
  | @insert p s hps ih =>
      by_cases hrest : T + 1 ≤ ∏ q ∈ s, q
      · obtain ⟨u, hu, hlo, hhi⟩ := ih
          (fun q hq => hfac q (Finset.mem_insert_of_mem hq)) hrest
        exact ⟨u, hu.trans (Finset.subset_insert p s), hlo, hhi⟩
      · refine ⟨insert p s, Finset.Subset.refl _, hprod, ?_⟩
        have hpY : p ≤ Y := hfac p (Finset.mem_insert_self p s)
        have hsT : (∏ q ∈ s, q) ≤ T := by omega
        rw [Finset.prod_insert hps]
        calc
          p * (∏ q ∈ s, q) ≤ Y * T := Nat.mul_le_mul hpY hsT
          _ = T * Y := Nat.mul_comm Y T

/-- Integer hypotheses sufficient for a prime-cutoff split of any positive
squarefree number. Unlike the old `T²` criterion, only `T * Y ≤ B` is used. -/
private theorem squarefree_hasBalancedBlocks_of_cutoffs {n X Y T B : ℕ}
    (hsq : Squarefree n) (hnpos : 0 < n) (hnX : n ≤ X) (hY : 1 ≤ Y)
    (hprimes : ∀ p ∈ n.primeFactors, p ≤ Y)
    (hT : 1 ≤ T) (hTY : T * Y ≤ B) (hXB : X ≤ (T + 1) * B) :
    HasBalancedBlocks n B := by
  classical
  have hTB : T ≤ B := by
    calc
      T = T * 1 := by simp
      _ ≤ T * Y := Nat.mul_le_mul_left T hY
      _ ≤ B := hTY
  have hBpos : 0 < B := by omega
  by_cases hsmall : n ≤ T
  · exact ⟨n, 1, hnpos, by omega, hsq, squarefree_one, by simp,
      by simp, hsmall.trans hTB, by omega⟩
  have hnprod : (∏ p ∈ n.primeFactors, p) = n :=
    Nat.prod_primeFactors_of_squarefree hsq
  have hprodlo : T + 1 ≤ ∏ p ∈ n.primeFactors, p := by
    rw [hnprod]
    omega
  obtain ⟨u, hu, huLo, huHi⟩ :=
    exists_subproduct_between_cutoff n.primeFactors T Y hT hprimes hprodlo
  let a : ℕ := ∏ p ∈ u, p
  let b : ℕ := ∏ p ∈ n.primeFactors \ u, p
  have hfac : n = a * b := by
    calc
      n = ∏ p ∈ n.primeFactors, p := hnprod.symm
      _ = (∏ p ∈ n.primeFactors \ u, p) * (∏ p ∈ u, p) :=
        (Finset.prod_sdiff hu).symm
      _ = a * b := by dsimp [a, b]; ac_rfl
  have haB : a ≤ B := huHi.trans hTY
  have hbB : b ≤ B := by
    apply Nat.le_of_mul_le_mul_left (c := T + 1) ?_ (Nat.succ_pos T)
    calc
      (T + 1) * b ≤ a * b := Nat.mul_le_mul_right b huLo
      _ = n := hfac.symm
      _ ≤ X := hnX
      _ ≤ (T + 1) * B := hXB
  have hsqfac : Squarefree (a * b) := by rw [← hfac]; exact hsq
  obtain ⟨hcop, hsa, hsb⟩ := Nat.squarefree_mul_iff.mp hsqfac
  have hbpos : 0 < b := by
    have hmulpos : 0 < a * b := by rw [← hfac]; exact hnpos
    exact Nat.pos_of_mul_pos_left hmulpos
  exact ⟨a, b, by omega, hbpos, hsa, hsb, hcop, hfac, haB, hbB⟩

/-- A computable near-ceiling block cutoff, clipped at `X` for counting. -/
def primeCutoffBlockBound (X Y : ℕ) : ℕ :=
  min X ((X * Y).sqrt + 1)

theorem primeCutoffBlockBound_le_X (X Y : ℕ) :
    primeCutoffBlockBound X Y ≤ X := Nat.min_le_left _ _

theorem primeCutoffBlockBound_le_sqrt_add (X Y : ℕ) (hY : 1 ≤ Y) :
    primeCutoffBlockBound X Y ≤ (X * Y).sqrt + Y := by
  calc
    primeCutoffBlockBound X Y ≤ (X * Y).sqrt + 1 := Nat.min_le_right _ _
    _ ≤ (X * Y).sqrt + Y := Nat.add_le_add_left hY _

/-- A positive squarefree number `n ≤ X` with no prime factor above `Y`
splits into two positive coprime squarefree blocks, each at most
`⌊√(X * Y)⌋ + 1`. The extra `1` also covers a perfect-square radicand. -/
theorem squarefree_hasPrimeCutoffBlocks_sqrt_add_one {n X Y : ℕ}
    (hsq : Squarefree n) (hnpos : 0 < n) (hnX : n ≤ X) (hY : 1 ≤ Y)
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ n → p ≤ Y) :
    HasBalancedBlocks n ((X * Y).sqrt + 1) := by
  let B : ℕ := (X * Y).sqrt + 1
  have hBpos : 0 < B := by dsimp [B]; omega
  have hXY : X * Y ≤ B * B := by
    simpa only [B, Nat.succ_eq_add_one] using (Nat.lt_succ_sqrt (X * Y)).le
  by_cases hBX : B ≤ X
  · let T : ℕ := X / B
    have hT : 1 ≤ T := Nat.div_pos hBX hBpos
    have hTY : T * Y ≤ B := by
      apply Nat.le_of_mul_le_mul_left (c := B) ?_ hBpos
      calc
        B * (T * Y) = (X / B * B) * Y := by dsimp [T]; ac_rfl
        _ ≤ X * Y := Nat.mul_le_mul_right Y (Nat.div_mul_le_self X B)
        _ ≤ B * B := hXY
    have hXT : X ≤ (T + 1) * B := by
      calc
        X ≤ B * (T + 1) := (Nat.lt_mul_div_succ X hBpos).le
        _ = (T + 1) * B := by ac_rfl
    apply squarefree_hasBalancedBlocks_of_cutoffs hsq hnpos hnX hY
      (fun p hp => hprimes p (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)) hT hTY hXT
  · have hXB : X ≤ B := by omega
    exact ⟨n, 1, hnpos, by omega, hsq, squarefree_one, by simp,
      by simp, hnX.trans hXB, by omega⟩

/-- Since both positive blocks divide `n`, clipping the bound at `X` loses
nothing. In particular the cutoff is at most `⌊√(X * Y)⌋ + Y`. -/
theorem squarefree_hasPrimeCutoffBlocks {n X Y : ℕ}
    (hsq : Squarefree n) (hnpos : 0 < n) (hnX : n ≤ X) (hY : 1 ≤ Y)
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ n → p ≤ Y) :
    HasBalancedBlocks n (primeCutoffBlockBound X Y) := by
  obtain ⟨a, b, ha, hb, hsa, hsb, hcop, hfac, haB, hbB⟩ :=
    squarefree_hasPrimeCutoffBlocks_sqrt_add_one hsq hnpos hnX hY hprimes
  have haX : a ≤ X := by
    calc
      a ≤ a * b := Nat.le_mul_of_pos_right a hb
      _ = n := hfac.symm
      _ ≤ X := hnX
  have hbX : b ≤ X := by
    calc
      b ≤ b * a := Nat.le_mul_of_pos_right b ha
      _ = a * b := Nat.mul_comm b a
      _ = n := hfac.symm
      _ ≤ X := hnX
  exact ⟨a, b, ha, hb, hsa, hsb, hcop, hfac,
    le_min haX haB, le_min hbX hbB⟩

/-- The Carmichael specialization of the parameterized squarefree split. -/
theorem isCarmichael_hasPrimeCutoffBlocks {n X Y : ℕ}
    (hn : IsCarmichael n) (hnX : n ≤ X) (hY : 1 ≤ Y)
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ n → p ≤ Y) :
    HasBalancedBlocks n (primeCutoffBlockBound X Y) := by
  have hnpos : 0 < n := by
    have hn' := (hn 1 (by omega) (by simp)).2.2
    omega
  exact squarefree_hasPrimeCutoffBlocks (isCarmichael_squarefree hn)
    hnpos hnX hY hprimes

/-- An explicitly oriented version: both blocks obey the computable
`⌊√(X * Y)⌋ + Y` bound, with the larger block named `a`. -/
theorem isCarmichael_exists_primeCutoffBlocks {n X Y : ℕ}
    (hn : IsCarmichael n) (hnX : n ≤ X) (hY : 1 ≤ Y)
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ n → p ≤ Y) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Squarefree a ∧ Squarefree b ∧ a.Coprime b ∧
      n = a * b ∧ b ≤ a ∧ a ≤ (X * Y).sqrt + Y ∧ b ≤ (X * Y).sqrt + Y := by
  obtain ⟨a, b, ha, hb, hsa, hsb, hcop, hfac, haB, hbB⟩ :=
    isCarmichael_hasPrimeCutoffBlocks hn hnX hY hprimes
  have hbound := primeCutoffBlockBound_le_sqrt_add X Y hY
  by_cases horder : b ≤ a
  · exact ⟨a, b, ha, hb, hsa, hsb, hcop, hfac, horder,
      haB.trans hbound, hbB.trans hbound⟩
  · exact ⟨b, a, hb, ha, hsb, hsa, hcop.symm,
      hfac.trans (Nat.mul_comm a b), by omega,
      hbB.trans hbound, haB.trans hbound⟩

/-- The high-λ family restricted to primes at most `Y`. The Carmichael
function threshold is `Z²`, independently of the prime cutoff `Y`. -/
def primeCutoffHighLambdaCarmichaels (X Y Z : ℕ) : Set ℕ :=
  {n | n ∈ highLambdaCarmichaels X Z ∧
    ∀ p : ℕ, p.Prime → p ∣ n → p ≤ Y}

/-- The restricted high-λ bound uses the smaller cutoff
`B = min X (⌊√(X * Y)⌋ + 1)` in the CRT counting theorem. -/
theorem primeCutoffHighLambdaCarmichaels_card_le (X Y Z : ℕ)
    (hY : 1 ≤ Y) (hZ : 1 ≤ Z) :
    ((primeCutoffHighLambdaCarmichaels X Y Z).ncard : ℝ) ≤
      (primeCutoffBlockBound X Y : ℝ) +
        (X : ℝ) / (Z : ℝ) * (1 + Real.log (X : ℝ)) := by
  have hsubset : primeCutoffHighLambdaCarmichaels X Y Z ⊆
      balancedHighLambdaCarmichaels X Z (primeCutoffBlockBound X Y) := by
    intro n hn
    exact ⟨hn.1, isCarmichael_hasPrimeCutoffBlocks hn.1.1 hn.1.2.1 hY hn.2⟩
  have hfinite : (balancedHighLambdaCarmichaels X Z
      (primeCutoffBlockBound X Y)).Finite :=
    (Set.finite_le_nat X).subset (fun n hn => hn.1.2.1)
  have hcard : (primeCutoffHighLambdaCarmichaels X Y Z).ncard ≤
      (balancedHighLambdaCarmichaels X Z (primeCutoffBlockBound X Y)).ncard :=
    Set.ncard_le_ncard hsubset hfinite
  calc
    ((primeCutoffHighLambdaCarmichaels X Y Z).ncard : ℝ) ≤
        ((balancedHighLambdaCarmichaels X Z (primeCutoffBlockBound X Y)).ncard : ℝ) := by
      exact_mod_cast hcard
    _ ≤ _ := balancedHighLambdaCarmichaels_card_le X Z
      (primeCutoffBlockBound X Y) hZ (primeCutoffBlockBound_le_X X Y)

/-- High-λ numbers whose primes exceed `Y` form a large-prime tail. For
`Y ≥ 2`, the tail costs at most `2 X / (Y + 1)` (before taking a floor). -/
theorem highLambdaCarmichaels_card_le_primeCutoff_tail (X Y Z : ℕ)
    (hY : 2 ≤ Y) (hZ : 1 ≤ Z) :
    ((highLambdaCarmichaels X Z).ncard : ℝ) ≤
      (primeCutoffBlockBound X Y : ℝ) +
        (X : ℝ) / (Z : ℝ) * (1 + Real.log (X : ℝ)) +
          2 * (X : ℝ) / (Y + 1 : ℕ) := by
  have hcover : highLambdaCarmichaels X Z ⊆
      primeCutoffHighLambdaCarmichaels X Y Z ∪
        largePrimeCarmichaels X (Y + 1) := by
    intro n hn
    by_cases hsmall : ∀ p : ℕ, p.Prime → p ∣ n → p ≤ Y
    · exact Or.inl ⟨hn, hsmall⟩
    · push_neg at hsmall
      obtain ⟨p, hp, hpn, hYp⟩ := hsmall
      exact Or.inr ⟨hn.1, hn.2.1, p, hp, by omega, hpn⟩
  have hfinite : (primeCutoffHighLambdaCarmichaels X Y Z ∪
      largePrimeCarmichaels X (Y + 1)).Finite := by
    apply (Set.finite_le_nat X).subset
    intro n hn
    rcases hn with hs | hl
    · exact hs.1.2.1
    · exact hl.2.1
  have hcard : (highLambdaCarmichaels X Z).ncard ≤
      (primeCutoffHighLambdaCarmichaels X Y Z).ncard +
        (largePrimeCarmichaels X (Y + 1)).ncard := by
    calc
      _ ≤ (primeCutoffHighLambdaCarmichaels X Y Z ∪
          largePrimeCarmichaels X (Y + 1)).ncard :=
        Set.ncard_le_ncard hcover hfinite
      _ ≤ _ := Set.ncard_union_le _ _
  have htail : ((largePrimeCarmichaels X (Y + 1)).ncard : ℝ) ≤
      2 * (X : ℝ) / (Y + 1 : ℕ) := by
    calc
      ((largePrimeCarmichaels X (Y + 1)).ncard : ℝ) ≤
          ((2 * X / (Y + 1) : ℕ) : ℝ) := by
        exact_mod_cast (largePrimeCarmichaels_card_le X (Y + 1) (by omega))
      _ ≤ ((2 * X : ℕ) : ℝ) / ((Y + 1 : ℕ) : ℝ) :=
        Nat.cast_div_le (α := ℝ) (m := 2 * X) (n := Y + 1)
      _ = 2 * (X : ℝ) / (Y + 1 : ℕ) := by push_cast; ring
  calc
    ((highLambdaCarmichaels X Z).ncard : ℝ) ≤
        ((primeCutoffHighLambdaCarmichaels X Y Z).ncard : ℝ) +
          ((largePrimeCarmichaels X (Y + 1)).ncard : ℝ) := by
      exact_mod_cast hcard
    _ ≤ (primeCutoffBlockBound X Y : ℝ) +
        (X : ℝ) / (Z : ℝ) * (1 + Real.log (X : ℝ)) +
          2 * (X : ℝ) / (Y + 1 : ℕ) :=
      add_le_add (primeCutoffHighLambdaCarmichaels_card_le X Y Z (by omega) hZ) htail

end Erdos1057

#print axioms Erdos1057.squarefree_hasPrimeCutoffBlocks
#print axioms Erdos1057.isCarmichael_exists_primeCutoffBlocks
#print axioms Erdos1057.primeCutoffHighLambdaCarmichaels_card_le
#print axioms Erdos1057.highLambdaCarmichaels_card_le_primeCutoff_tail
