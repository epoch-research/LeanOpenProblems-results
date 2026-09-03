import Submission.FTBand
import Submission.FTParameters
import Submission.PrimeSieve

/-!
# A finite one-fifth-scale squarefree interval estimate

The finite FT band estimate and its arithmetic parameters bound the number of
large square bases by `H / 16`. The preliminary prime-square sieve removes at
most `13 * H / 16` further integers, so a squarefree integer remains in
`(x, x + H]`.

The hypotheses retain both `x ≤ q^5` and the finite terminal-scale condition
`x + H < FTParameters.A * H * 16^J`, together with
`2048 * q * (J + 1) ≤ H`. The final threshold is uniform in `x`, `q`, and `J`.
This is only a finite one-fifth estimate, not a squarefree-gap conjecture
completion.
-/

open Finset

namespace FifthInterval

/-- Bases in a closed interval whose square multiples hit `(x, x + H]`. -/
noncomputable def squareBases (x H L U : ℕ) : Finset ℕ := by
  classical
  exact (Icc L U).filter (fun d => ∃ m : ℕ, x < m * d ^ 2 ∧ m * d ^ 2 ≤ x + H)

/-- Every base with a square multiple in the interval is at most `x + H`. -/
theorem square_base_le (x H d : ℕ)
    (hd : ∃ m : ℕ, x < m * d ^ 2 ∧ m * d ^ 2 ≤ x + H) : d ≤ x + H := by
  obtain ⟨m, hmlo, hmhi⟩ := hd
  have hm : 0 < m := by
    by_contra h
    have : m = 0 := by omega
    simp [this] at hmlo
  exact (Nat.le_self_pow (by decide) d).trans
    ((Nat.le_mul_of_pos_left (d ^ 2) hm).trans hmhi)

/-- One of the four dyadic subbands at the factor-16 scale `j`. -/
noncomputable def bandBases (x H j s : ℕ) : Finset ℕ :=
  squareBases x H (FTParameters.N H j s) (2 * FTParameters.N H j s)

/-- The verified FT estimate applies to every dyadic subband. -/
theorem card_bandBases_le (x H q j s : ℕ) (hq : 0 < q) (hqH : q ≤ H)
    (hx : x ≤ q ^ 5) :
    ((bandBases x H j s).card : ℚ) ≤
      2 + 2 * (FTParameters.N H j s : ℚ) / (FTParameters.B H q j s : ℚ) +
        8 * (x : ℚ) * (FTParameters.B H q j s : ℚ) ^ 4 /
          (FTParameters.N H j s : ℚ) ^ 4 +
        1440 * (H : ℚ) * (FTParameters.B H q j s : ℚ) /
          (FTParameters.V H q j s : ℚ) := by
  classical
  obtain ⟨hN, hHN, hB, hV, hsmall⟩ := FTParameters.parameter_bounds j s hq hqH hx
  apply FTBand.finite_band_bound (bandBases x H j s) hN hHN hB hV hsmall
  · intro d hd
    exact (mem_filter.mp hd).1
  · intro d hd
    exact (mem_filter.mp hd).2

/-- A strict terminal endpoint gives a finite cover by geometric bands.
Keeping the upper endpoint strict allows successive geometric refinements. -/
private lemma geometric_cover (M r d J : ℕ) (hlo : M ≤ d) (hhi : d < M * r ^ J) :
    ∃ j < J, M * r ^ j ≤ d ∧ d < r * (M * r ^ j) := by
  induction J generalizing d with
  | zero =>
    simp only [pow_zero, mul_one] at hhi
    omega
  | succ J ih =>
    by_cases h : d < M * r ^ J
    · obtain ⟨j, hj, hdlo, hdhi⟩ := ih d hlo h
      exact ⟨j, by omega, hdlo, hdhi⟩
    · refine ⟨J, Nat.lt_succ_self J, Nat.le_of_not_gt h, ?_⟩
      have heq : M * r ^ (J + 1) = r * (M * r ^ J) := by rw [pow_succ]; ring
      rwa [heq] at hhi

/-- Relevant bases at or above the sieve cutoff. The harmless overlap at
`FTParameters.A * H` ensures that the lower endpoint is included. -/
noncomputable def largeBases (x H : ℕ) : Finset ℕ :=
  squareBases x H (FTParameters.A * H) (x + H)

/-- The factor-16 cover, refined into four dyadic subbands at each scale,
controls all the large relevant bases. -/
theorem card_largeBases_le (x H q J : ℕ) (hq : 0 < q) (hx : x ≤ q ^ 5)
    (hH : 2048 * q * (J + 1) ≤ H)
    (hterminal : x + H < FTParameters.A * H * 16 ^ J) :
    16 * (largeBases x H).card ≤ H := by
  classical
  have hsub : largeBases x H ⊆
      (univ : Finset (Fin J)).biUnion (fun j =>
        (univ : Finset (Fin 4)).biUnion (fun s => bandBases x H j s)) := by
    intro d hd
    obtain ⟨hdI, hhit⟩ := mem_filter.mp hd
    obtain ⟨j, hj, hdlo, hdhi⟩ := geometric_cover (FTParameters.A * H) 16 d J
      (mem_Icc.mp hdI).1 ((mem_Icc.mp hdI).2.trans_lt hterminal)
    have hdhi' : d < (FTParameters.A * H * 16 ^ j) * 2 ^ 4 := by
      simpa only [show (2 : ℕ) ^ 4 = 16 from rfl, mul_comm] using hdhi
    obtain ⟨s, hs, hdslo, hdshi⟩ :=
      geometric_cover (FTParameters.A * H * 16 ^ j) 2 d 4 hdlo hdhi'
    refine mem_biUnion.mpr ⟨⟨j, hj⟩, mem_univ _, ?_⟩
    refine mem_biUnion.mpr ⟨⟨s, hs⟩, mem_univ _, ?_⟩
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hdslo, hdshi.le⟩, hhit⟩
  have hcount : (largeBases x H).card ≤
      ∑ j : Fin J, ∑ s : Fin 4, (bandBases x H j s).card := by
    calc
      (largeBases x H).card ≤
          ((univ : Finset (Fin J)).biUnion (fun j =>
            (univ : Finset (Fin 4)).biUnion (fun s => bandBases x H j s))).card :=
        card_le_card hsub
      _ ≤ ∑ j : Fin J,
          ((univ : Finset (Fin 4)).biUnion (fun s => bandBases x H j s)).card :=
        card_biUnion_le
      _ ≤ ∑ j : Fin J, ∑ s : Fin 4, (bandBases x H j s).card :=
        sum_le_sum (fun _ _ => card_biUnion_le)
  calc
    16 * (largeBases x H).card ≤
        16 * (∑ j : Fin J, ∑ s : Fin 4, (bandBases x H j s).card) :=
      Nat.mul_le_mul_left 16 hcount
    _ ≤ H := FTParameters.total_bound (fun j s => (bandBases x H j s).card) hq hx hH
      (fun j s => card_bandBases_le x H q j s hq (FTParameters.q_le_H hH) hx)

/-- The interval integers divisible by the square of a relevant large base. -/
noncomputable def largeSquareBad (x H : ℕ) : Finset ℕ := by
  classical
  exact (largeBases x H).biUnion
    (fun d => (Ioc x (x + H)).filter (fun n => d ^ 2 ∣ n))

/-- Each large base removes at most one integer, since its square exceeds `H`. -/
theorem card_largeSquareBad_le_card_bases (x H : ℕ) (hH : 0 < H) :
    (largeSquareBad x H).card ≤ (largeBases x H).card := by
  classical
  have hc := card_biUnion_le_card_mul (largeBases x H)
    (fun d => (Ioc x (x + H)).filter (fun n => d ^ 2 ∣ n)) 1 (by
      intro d hd
      have hdlo := (mem_Icc.mp (mem_filter.mp hd).1).1
      have hcut : 2 * H ≤ FTParameters.A * H :=
        Nat.mul_le_mul_right H (by norm_num [FTParameters.A])
      have hd2 : H < d ^ 2 :=
        (show H < d by omega).trans_le (Nat.le_self_pow (by decide) d)
      have hdcard := ElementarySquarefree.card_multiples_Ioc_le x H (d ^ 2)
      rw [Nat.div_eq_of_lt hd2] at hdcard
      exact hdcard)
  simpa only [largeSquareBad, mul_one] using hc

/-- Large square divisors remove at most one sixteenth of the interval. -/
theorem card_largeSquareBad_le (x H q J : ℕ) (hq : 0 < q) (hx : x ≤ q ^ 5)
    (hH : 2048 * q * (J + 1) ≤ H)
    (hterminal : x + H < FTParameters.A * H * 16 ^ J) :
    16 * (largeSquareBad x H).card ≤ H :=
  (Nat.mul_le_mul_left 16
    (card_largeSquareBad_le_card_bases x H (hq.trans_le (FTParameters.q_le_H hH)))).trans
      (card_largeBases_le x H q J hq hx hH hterminal)

/-- Every nonsquarefree interval member is removed by the small-prime sieve
or by the large-square tail. -/
theorem nonsquarefree_mem_union (x H n : ℕ)
    (hn : n ∈ Ioc x (x + H)) (hns : ¬ Squarefree n) :
    n ∈ PrimeSieve.primeSquareBad x H (FTParameters.A * H) ∪ largeSquareBad x H := by
  classical
  rw [Nat.squarefree_iff_prime_squarefree] at hns
  push_neg at hns
  obtain ⟨p, hp, hpdvd⟩ := hns
  have hpsq : p ^ 2 ∣ n := by simpa only [pow_two] using hpdvd
  by_cases hpc : p ≤ FTParameters.A * H
  · apply mem_union_left
    exact (PrimeSieve.mem_primeSquareBad x H (FTParameters.A * H) n).mpr
      ⟨(mem_Ioc.mp hn).1, (mem_Ioc.mp hn).2, p, hp, hpc, hpsq⟩
  · obtain ⟨m, hnm⟩ := hpsq
    have hmn : m * p ^ 2 = n := by simpa only [mul_comm] using hnm.symm
    have hhit : ∃ m : ℕ, x < m * p ^ 2 ∧ m * p ^ 2 ≤ x + H :=
      ⟨m, by simpa only [hmn] using mem_Ioc.mp hn⟩
    have hpB : p ∈ largeBases x H :=
      mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, square_base_le x H p hhit⟩, hhit⟩
    apply mem_union_right
    exact mem_biUnion.mpr ⟨p, hpB, mem_filter.mpr ⟨hn, ⟨m, hnm⟩⟩⟩

open Classical in
/-- Together, the two bad sets contain at most `14 * H / 16` interval members. -/
theorem card_nonsquarefree_le (x H q J : ℕ) (hq : 0 < q) (hx : x ≤ q ^ 5)
    (hH : 2048 * q * (J + 1) ≤ H)
    (hterminal : x + H < FTParameters.A * H * 16 ^ J)
    (hsieve : 16 * (PrimeSieve.primeSquareBad x H (FTParameters.A * H)).card ≤ 13 * H) :
    16 * ((Ioc x (x + H)).filter (fun n => ¬ Squarefree n)).card ≤ 14 * H := by
  have hcard : ((Ioc x (x + H)).filter (fun n => ¬ Squarefree n)).card ≤
      (PrimeSieve.primeSquareBad x H (FTParameters.A * H)).card +
        (largeSquareBad x H).card := by
    calc
      _ ≤ (PrimeSieve.primeSquareBad x H (FTParameters.A * H) ∪
          largeSquareBad x H).card := by
        apply card_le_card
        intro n hn
        exact nonsquarefree_mem_union x H n (mem_filter.mp hn).1 (mem_filter.mp hn).2
      _ ≤ _ := card_union_le _ _
  have htail := card_largeSquareBad_le x H q J hq hx hH hterminal
  omega

/-- The explicit finite one-fifth interval conclusion, given the sieve bound
and the arithmetic and terminal-scale hypotheses. -/
theorem exists_squarefree_of_parameters (x H q J : ℕ) (hq : 0 < q) (hx : x ≤ q ^ 5)
    (hH : 2048 * q * (J + 1) ≤ H)
    (hterminal : x + H < FTParameters.A * H * 16 ^ J)
    (hsieve : 16 * (PrimeSieve.primeSquareBad x H (FTParameters.A * H)).card ≤ 13 * H) :
    ∃ n : ℕ, x < n ∧ n ≤ x + H ∧ Squarefree n := by
  classical
  have hHpos : 0 < H := hq.trans_le (FTParameters.q_le_H hH)
  by_contra he
  have hall : (Ioc x (x + H)).filter (fun n => ¬ Squarefree n) = Ioc x (x + H) := by
    apply filter_eq_self.mpr
    intro n hn hsq
    exact he ⟨n, (mem_Ioc.mp hn).1, (mem_Ioc.mp hn).2, hsq⟩
  have hc := card_nonsquarefree_le x H q J hq hx hH hterminal hsieve
  rw [hall, Nat.card_Ioc, Nat.add_sub_cancel_left] at hc
  omega

/-- A threshold uniform in `x`, `q`, and `J` supplies the sieve hypothesis in
the finite one-fifth estimate. No terminal-scale or length assumption is removed. -/
theorem exists_squarefree_in_fifth_interval :
    ∃ H₀ : ℕ, ∀ x H q J : ℕ, H₀ ≤ H → 0 < q → x ≤ q ^ 5 →
      2048 * q * (J + 1) ≤ H → x + H < FTParameters.A * H * 16 ^ J →
        ∃ n : ℕ, x < n ∧ n ≤ x + H ∧ Squarefree n := by
  obtain ⟨H₀, hH₀⟩ := PrimeSieve.exists_uniform_threshold FTParameters.A
  refine ⟨H₀, ?_⟩
  intro x H q J hthreshold hq hx hH hterminal
  exact exists_squarefree_of_parameters x H q J hq hx hH hterminal
    (hH₀ H hthreshold x)

#print axioms exists_squarefree_of_parameters
#print axioms exists_squarefree_in_fifth_interval

end FifthInterval
