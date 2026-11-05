import Submission.PrimeCutoffSplit
import Submission.LowLambdaWeighted

/-!
# A prime-cutoff weighted bound for small Carmichael-function values

For `λ(n) ≤ H`, every prime divisor of `n` is at most `H + 1`. The
prime-cutoff splitting theorem therefore yields `n = a * b` with `b ≤ a ≤ B`,
where `B = primeCutoffBlockBound X (H + 1)`. For each possible larger block
`a`, the conditions `a ∣ n` and `λ(a) ∣ n - 1`, together with
`gcd(a, λ(a)) = 1`, pick out one CRT class modulo `a * λ(a)`. We count that
class directly, without introducing levels for `λ(n) / λ(a)`.
-/

namespace Erdos1057

/-- The larger squarefree blocks allowed by the prime-cutoff splitting theorem. -/
noncomputable def lowLambdaSharperBlocks (X H D : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (primeCutoffBlockBound X (H + 1))).filter (fun a =>
    Squarefree a ∧ a.Coprime (ArithmeticFunction.Carmichael a) ∧ D < a * a ∧
      ArithmeticFunction.Carmichael a ≤ H)

/-- The exact weight attached to the admissible larger blocks. -/
noncomputable def lowLambdaSharperWeight (X H D : ℕ) : ℝ :=
  ∑ a ∈ lowLambdaSharperBlocks X H D,
    (1 : ℝ) / ((a : ℝ) * (ArithmeticFunction.Carmichael a : ℝ))

/-- An auxiliary low-`λ` estimate using the prime-factor cutoff: there is only
one CRT class per larger block, so neither a harmonic factor nor an `H` factor
appears in the bound. -/
theorem lowLambdaCarmichaels_card_le_sharper (X H D : ℕ)
    (_hX : 1 ≤ X) (hH : 1 ≤ H) :
    ((lowLambdaCarmichaels X H).ncard : ℝ) ≤
      (D : ℝ) + (primeCutoffBlockBound X (H + 1) : ℝ) +
        (X : ℝ) * lowLambdaSharperWeight X H D := by
  classical
  let B : ℕ := primeCutoffBlockBound X (H + 1)
  let choices : Finset ℕ := lowLambdaSharperBlocks X H D
  let fibers : ℕ → Finset ℕ := fun a =>
    (Finset.range (X + 1)).filter (fun n => IsCarmichael n ∧ a ∣ n)
  have hcover : lowLambdaCarmichaels X H ⊆
      (((Finset.Icc 1 D) ∪ choices.biUnion fibers : Finset ℕ) : Set ℕ) := by
    intro n hn
    obtain ⟨hnC, hnX, hnH⟩ := hn
    have hn1 : 1 ≤ n := by
      have hn' := (hnC 1 (by omega) (by simp)).2.2
      omega
    by_cases hnD : n ≤ D
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_Icc.mpr ⟨hn1, hnD⟩))
    · have hLpos : 0 < ArithmeticFunction.Carmichael n :=
        Nat.pos_of_dvd_of_pos (ArithmeticFunction.carmichael_dvd_totient n)
          (Nat.totient_pos.mpr (by omega))
      have hprimes : ∀ p : ℕ, p.Prime → p ∣ n → p ≤ H + 1 := by
        intro p hp hpn
        have hpdvd : p - 1 ∣ ArithmeticFunction.Carmichael n := by
          rw [← carmichael_at_prime hp]
          exact ArithmeticFunction.carmichael_dvd hpn
        have hpH : p - 1 ≤ H := (Nat.le_of_dvd hLpos hpdvd).trans hnH
        omega
      obtain ⟨a, b, ha, hb, hsa, _, _, hnfac, haB, _, hba⟩ :
          ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Squarefree a ∧ Squarefree b ∧ a.Coprime b ∧
            n = a * b ∧ a ≤ B ∧ b ≤ B ∧ b ≤ a := by
        obtain ⟨a₀, b₀, ha₀, hb₀, hsa₀, hsb₀, hcop₀, hnfac₀, haB₀, hbB₀⟩ :=
          isCarmichael_hasPrimeCutoffBlocks hnC hnX (by omega : 1 ≤ H + 1) hprimes
        by_cases horder : b₀ ≤ a₀
        · exact ⟨a₀, b₀, ha₀, hb₀, hsa₀, hsb₀, hcop₀, hnfac₀, haB₀, hbB₀, horder⟩
        · exact ⟨b₀, a₀, hb₀, ha₀, hsb₀, hsa₀, hcop₀.symm,
            hnfac₀.trans (Nat.mul_comm a₀ b₀), hbB₀, haB₀, by omega⟩
      have hadiv : a ∣ n := hnfac ▸ dvd_mul_right a b
      have hda : ArithmeticFunction.Carmichael a ≤ H :=
        (Nat.le_of_dvd hLpos (ArithmeticFunction.carmichael_dvd hadiv)).trans hnH
      have hD : D < a * a := by
        calc
          D < n := by omega
          _ = a * b := hnfac
          _ ≤ a * a := Nat.mul_le_mul_left a hba
      have haChoice : a ∈ choices := by
        change a ∈ (Finset.Icc 1 B).filter (fun a =>
          Squarefree a ∧ a.Coprime (ArithmeticFunction.Carmichael a) ∧
            D < a * a ∧ ArithmeticFunction.Carmichael a ≤ H)
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha, haB⟩, hsa,
          isCarmichael_coprime_divisor_lambda hnC hadiv, hD, hda⟩
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
        ⟨a, haChoice, Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), hnC, hadiv⟩⟩))
  have hcard : (lowLambdaCarmichaels X H).ncard ≤
      (Finset.Icc 1 D).card + ∑ a ∈ choices, (fibers a).card := by
    calc
      _ ≤ ((Finset.Icc 1 D) ∪ choices.biUnion fibers).card := by
        simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hcover
      _ ≤ (Finset.Icc 1 D).card + (choices.biUnion fibers).card :=
        Finset.card_union_le _ _
      _ ≤ (Finset.Icc 1 D).card + ∑ a ∈ choices, (fibers a).card :=
        Nat.add_le_add_left Finset.card_biUnion_le _
  have hchoices : choices ⊆ Finset.Icc 1 B := Finset.filter_subset _ _
  have hchoicesCard : choices.card ≤ B :=
    (Finset.card_le_card hchoices).trans (by simp [Nat.card_Icc])
  have hsum : ((∑ a ∈ choices, (fibers a).card : ℕ) : ℝ) ≤
      (X : ℝ) * lowLambdaSharperWeight X H D + (B : ℝ) := by
    rw [Nat.cast_sum]
    calc
      (∑ a ∈ choices, ((fibers a).card : ℝ)) ≤
          ∑ a ∈ choices,
            ((X : ℝ) * ((1 : ℝ) /
              ((a : ℝ) * (ArithmeticFunction.Carmichael a : ℝ))) + 1) := by
        apply Finset.sum_le_sum
        intro a ha
        have ha0 : 0 < a :=
          (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
        have hda0 : 0 < ArithmeticFunction.Carmichael a :=
          Nat.pos_of_dvd_of_pos (ArithmeticFunction.carmichael_dvd_totient a)
            (Nat.totient_pos.mpr ha0)
        have hfiber := fixedBlockCarmichaels_card_le X a ha0 hda0
        calc
          ((fibers a).card : ℝ) ≤
              ((X / (a * ArithmeticFunction.Carmichael a) + 1 : ℕ) : ℝ) := by
            exact_mod_cast hfiber
          _ ≤ (X : ℝ) / ((a : ℝ) * (ArithmeticFunction.Carmichael a : ℝ)) + 1 := by
            simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_mul] using
              (add_le_add_left (Nat.cast_div_le (α := ℝ)
                (m := X) (n := a * ArithmeticFunction.Carmichael a)) 1)
          _ = _ := by ring
      _ = (X : ℝ) * lowLambdaSharperWeight X H D + (choices.card : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        rfl
      _ ≤ (X : ℝ) * lowLambdaSharperWeight X H D + (B : ℝ) := by
        have hcardR : (choices.card : ℝ) ≤ (B : ℝ) := by exact_mod_cast hchoicesCard
        exact add_le_add (le_refl _) hcardR
  have hsmall : (Finset.Icc 1 D).card ≤ D := by simp [Nat.card_Icc]
  calc
    ((lowLambdaCarmichaels X H).ncard : ℝ) ≤
        (((Finset.Icc 1 D).card + ∑ a ∈ choices, (fibers a).card : ℕ) : ℝ) := by
      exact_mod_cast hcard
    _ ≤ (D : ℝ) + ((∑ a ∈ choices, (fibers a).card : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hsmall _
    _ ≤ (D : ℝ) + ((X : ℝ) * lowLambdaSharperWeight X H D + (B : ℝ)) :=
      add_le_add (le_refl (D : ℝ)) hsum
    _ = _ := by ring

/-- An unconditional bound for *all* Carmichael numbers up to `X`.
Set `H = Z² - 1`, so that `H + 1 = Z²` and the low-`λ` prime-cutoff
bound uses `B = primeCutoffBlockBound X (Z * Z)`. Every Carmichael number
has either `λ(n) ≤ H` or `λ(n) ≥ Z²`; apply the two bounds to this union. -/
theorem carmichaelsUpTo_card_le_sharper_split (X Z D : ℕ)
    (hX : 1 ≤ X) (hZ : 2 ≤ Z) :
    (({n : ℕ | IsCarmichael n ∧ n ≤ X}).ncard : ℝ) ≤
      (D : ℝ) + (primeCutoffBlockBound X (Z * Z) : ℝ) +
        (X : ℝ) * lowLambdaSharperWeight X (Z * Z - 1) D +
          (highLambdaBlockCutoff X : ℝ) +
            (X : ℝ) / (Z : ℝ) * (1 + Real.log (X : ℝ)) := by
  let H : ℕ := Z * Z - 1
  have hZ2 : 2 ≤ Z * Z := by
    calc
      2 ≤ 2 * 2 := by norm_num
      _ ≤ Z * Z := Nat.mul_le_mul hZ hZ
  have hH : 1 ≤ H := by
    dsimp [H]
    omega
  have hHplus : H + 1 = Z * Z := by
    dsimp [H]
    omega
  have hcover : {n : ℕ | IsCarmichael n ∧ n ≤ X} ⊆
      lowLambdaCarmichaels X H ∪ highLambdaCarmichaels X Z := by
    intro n hn
    by_cases hsmall : ArithmeticFunction.Carmichael n ≤ H
    · exact Or.inl ⟨hn.1, hn.2, hsmall⟩
    · have hlarge : Z * Z ≤ ArithmeticFunction.Carmichael n := by omega
      exact Or.inr ⟨hn.1, hn.2, hlarge⟩
  have hfinite : (lowLambdaCarmichaels X H ∪ highLambdaCarmichaels X Z).Finite := by
    apply (Set.finite_le_nat X).subset
    intro n hn
    rcases hn with hn | hn
    · exact hn.2.1
    · exact hn.2.1
  have hcard : ({n : ℕ | IsCarmichael n ∧ n ≤ X}).ncard ≤
      (lowLambdaCarmichaels X H).ncard + (highLambdaCarmichaels X Z).ncard := by
    calc
      _ ≤ (lowLambdaCarmichaels X H ∪ highLambdaCarmichaels X Z).ncard :=
        Set.ncard_le_ncard hcover hfinite
      _ ≤ _ := Set.ncard_union_le _ _
  calc
    (({n : ℕ | IsCarmichael n ∧ n ≤ X}).ncard : ℝ) ≤
        ((lowLambdaCarmichaels X H).ncard : ℝ) +
          ((highLambdaCarmichaels X Z).ncard : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ((D : ℝ) + (primeCutoffBlockBound X (H + 1) : ℝ) +
          (X : ℝ) * lowLambdaSharperWeight X H D) +
          ((highLambdaBlockCutoff X : ℝ) +
            (X : ℝ) / (Z : ℝ) * (1 + Real.log (X : ℝ))) :=
      add_le_add (lowLambdaCarmichaels_card_le_sharper X H D hX hH)
        (highLambdaCarmichaels_card_le X Z (by omega))
    _ = _ := by
      rw [hHplus]
      dsimp [H]
      ring


end Erdos1057

#print axioms Erdos1057.lowLambdaCarmichaels_card_le_sharper
#print axioms Erdos1057.carmichaelsUpTo_card_le_sharper_split

