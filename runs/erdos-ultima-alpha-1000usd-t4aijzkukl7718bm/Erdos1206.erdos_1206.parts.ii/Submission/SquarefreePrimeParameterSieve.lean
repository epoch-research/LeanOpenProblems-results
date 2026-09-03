import Submission.QuadraticSquareLocal

/-! Locally unit-admissible anisotropic positive quadratics simultaneously
represent squarefree numbers avoiding any summable set of forbidden primes.
The positive density asserted here is in the two parameter variables. -/
namespace Erdos1206.SquarefreePrimeParameterSieve
open Finset Filter QuadraticSquarefreeSieve QuadraticSquareLocal QuadraticRootLattice
  CoprimeBoxCRT
open scoped Classical
set_option maxHeartbeats 2000000

lemma product_lower (a b c : Fin 4 → ℕ) (B : Set ℕ)
    (ha : ∀ i, 0 < a i) (hQ : ∀ i, Anisotropic (c i) (b i) (a i))
    (hdisc : ∀ i, (b i:ℤ)^2-4*(a i)*(c i) ≠ 0)
    (hs : Summable (fun p : ℕ => if p∈B then (1:ℝ)/p else 0))
    (hloc : ∀ p, p.Prime → ∃ x : ℕ × ℕ,
      ∀ i, ¬p∣quad (a i) (b i) (c i) x.1 x.2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S : Finset ℕ, (∀ p∈S, p.Prime) →
      δ ≤ ∏p∈S,localDensity (fun p => p^2) (residues a b c B) p := by
  let f : ℕ → ℝ := fun p => if p.Prime then
    localDensity (fun p => p^2) (residues a b c B) p else 1
  have hf (p : ℕ) : 0 < f p ∧ f p ≤ 1 := by
    by_cases hp : p.Prime
    · have hh := density_bounds a b c B ha hQ hdisc hp (hloc p hp)
      simpa only [f,if_pos hp] using And.intro hh.1 hh.2.1
    · simp [f,hp]
  have hsq : Summable (fun p : ℕ => (squareMass a b c:ℝ)/(p:ℝ)^2) := by
    simpa only [mul_one_div] using
      ((Real.summable_one_div_nat_pow.mpr (by decide : 1<2)).mul_left (squareMass a b c:ℝ))
  have hsum : Summable (fun p => 1-f p) := by
    apply Summable.of_nonneg_of_le (fun p => sub_nonneg.mpr (hf p).2) _
      (hsq.add (hs.mul_left (primeMass a b c:ℝ)))
    intro p
    by_cases hp : p.Prime
    · have hh := (density_bounds a b c B ha hQ hdisc hp (hloc p hp)).2.2
      by_cases hpB : p∈B <;>
        simpa only [f,if_pos hp,hpB,if_true,if_false,mul_one_div,mul_zero] using hh
    · simp only [f,if_neg hp,sub_self]
      split_ifs <;> positivity
  obtain ⟨δ,hδ,hprod⟩ := PositiveLocalProducts.uniform_product_lower f hf hsum
  refine ⟨δ,hδ,fun S hS => ?_⟩
  calc
    δ ≤ ∏p∈S,f p := hprod S
    _ = _ := prod_congr rfl (fun p hp => if_pos (hS p hp))

lemma uniform_tail (a b c : Fin 4 → ℕ) (B : Set ℕ)
    (ha : ∀ i, 0 < a i) (hc : ∀ i, 0 < c i)
    (hQ : ∀ i, Anisotropic (c i) (b i) (a i))
    (hdisc : ∀ i, (b i:ℤ)^2-4*(a i)*(c i) ≠ 0)
    (hB : ∀ p∈B, p.Prime)
    (hs : Summable (fun p : ℕ => if p∈B then (1:ℝ)/p else 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℕ, ∀ᶠ N : ℕ in atTop,
      ((PeriodicParameterSieve.tail (fun p => p^2) (residues a b c B) H N).card:ℝ) ≤ ε*(N:ℝ)^2 := by
  have hε8 : 0 < ε/8 := by positivity
  choose Hp hHp using fun i => QuadraticPrimeTail.uniform_prime_tail (hQ i) B hB hs hε8
  choose Hs hHs using fun i => QuadraticSquareTail.uniform_square_tail
    (a i) (b i) (c i) (ha i) (hc i) (hdisc i) hε8
  let H := (univ : Finset (Fin 4)).sup (fun i => max (Hp i) (Hs i))
  have hpi (i : Fin 4) : Hp i ≤ H := (le_max_left _ _).trans (le_sup (f := fun i => max (Hp i) (Hs i)) (mem_univ i))
  have hsi (i : Fin 4) : Hs i ≤ H := (le_max_right _ _).trans (le_sup (f := fun i => max (Hp i) (Hs i)) (mem_univ i))
  have hevs : ∀ᶠ N : ℕ in atTop, ∀ i,
      ((QuadraticSquareTail.badTail (a i) (b i) (c i) (Hs i) N).card:ℝ) ≤ ε/8*(N:ℝ)^2 :=
    Filter.eventually_all.mpr hHs
  refine ⟨H,?_⟩
  filter_upwards [hevs] with N hsq
  let P (i : Fin 4) := QuadraticNaturalPrime.badTail (a i) (b i) (c i) B H N
  let Q (i : Fin 4) := QuadraticSquareTail.badTail (a i) (b i) (c i) H N
  have hP (i : Fin 4) : ((P i).card:ℝ) ≤ ε/8*(N:ℝ)^2 := by
    calc
      _ ≤ ((QuadraticNaturalPrime.badTail (a i) (b i) (c i) B (Hp i) N).card:ℝ) := by
        exact_mod_cast card_le_card (QuadraticNaturalPrime.badTail_mono (hpi i))
      _ ≤ ((QuadraticPrimeTail.badTail (c i) (b i) (a i) B (Hp i) N).card:ℝ) := by
        exact_mod_cast QuadraticNaturalPrime.badTail_card_le (a i) (b i) (c i) B (Hp i) N
      _ ≤ _ := hHp i N
  have hQ' (i : Fin 4) : ((Q i).card:ℝ) ≤ ε/8*(N:ℝ)^2 := by
    exact (show ((Q i).card:ℝ) ≤ (QuadraticSquareTail.badTail (a i) (b i) (c i) (Hs i) N).card by
      exact_mod_cast card_le_card (QuadraticSquareTail.badTail_mono (hsi i))).trans (hsq i)
  have hcover : PeriodicParameterSieve.tail (fun p => p^2) (residues a b c B) H N ⊆
      univ.biUnion (fun i => P i ∪ Q i) := by
    intro x hx
    obtain ⟨hxbox,hxpos,p,hp,hHp,hbad⟩ := mem_filter.mp hx
    have htest : ¬test a b c B p x := fun ht => hbad ((mem_residues_nat a b c B hp x).mpr ht)
    simp only [test,not_forall] at htest
    obtain ⟨i,hi⟩ := htest
    apply mem_biUnion.mpr
    refine ⟨i,mem_univ _,?_⟩
    by_cases hsq : p^2∣quad (a i) (b i) (c i) x.1 x.2
    · exact mem_union_right _ (mem_filter.mpr ⟨hxbox,hxpos,p,hp,hHp,hsq⟩)
    · have hpd : p∈B ∧ p∣quad (a i) (b i) (c i) x.1 x.2 := by
        simpa only [_root_.not_imp,not_not] using (not_and.mp hi) hsq
      exact mem_union_left _ (mem_filter.mpr ⟨hxbox,hxpos,p,hpd.1,hHp,hpd.2⟩)
  calc
    _ ≤ ∑i,((P i ∪ Q i).card:ℝ) := by
      exact_mod_cast (card_le_card hcover).trans card_biUnion_le
    _ ≤ ∑i,(((P i).card:ℝ)+(Q i).card) :=
      sum_le_sum (fun i _ => by exact_mod_cast card_union_le (P i) (Q i))
    _ ≤ ∑i : Fin 4, (ε/8*(N:ℝ)^2+ε/8*(N:ℝ)^2) :=
      sum_le_sum (fun i _ => add_le_add (hP i) (hQ' i))
    _ = _ := by simp; ring

/-- Positive density of parameters for the combined sieve. -/
theorem parameter_density (a b c : Fin 4 → ℕ) (B : Set ℕ)
    (ha : ∀ i, 0 < a i) (hc : ∀ i, 0 < c i)
    (hQ : ∀ i, Anisotropic (c i) (b i) (a i))
    (hdisc : ∀ i, (b i:ℤ)^2-4*(a i)*(c i) ≠ 0)
    (hB : ∀ p∈B, p.Prime)
    (hs : Summable (fun p : ℕ => if p∈B then (1:ℝ)/p else 0))
    (hloc : ∀ p, p.Prime → ∃ x : ℕ × ℕ,
      ∀ i, ¬p∣quad (a i) (b i) (c i) x.1 x.2) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ N : ℕ in atTop,
      η*(N:ℝ)^2 ≤ (PeriodicParameterSieve.good (fun p => p^2) (residues a b c B) N).card := by
  exact PeriodicParameterSieve.positive_parameter_density (fun p => p^2) (residues a b c B)
    (fun p hp => pow_pos hp.pos _)
    (fun p q hp hq hpq => Nat.coprime_pow_primes 2 2 hp hq hpq)
    (product_lower a b c B ha hQ hdisc hs hloc)
    (fun ε hε => uniform_tail a b c B ha hc hQ hdisc hB hs hε)

/-- In particular, one positive parameter pair gives four squarefree values,
none divisible by any forbidden prime. This is not a Sidon construction. -/
theorem exists_avoiding (a b c : Fin 4 → ℕ) (B : Set ℕ)
    (ha : ∀ i, 0 < a i) (hc : ∀ i, 0 < c i)
    (hQ : ∀ i, Anisotropic (c i) (b i) (a i))
    (hdisc : ∀ i, (b i:ℤ)^2-4*(a i)*(c i) ≠ 0)
    (hB : ∀ p∈B, p.Prime)
    (hs : Summable (fun p : ℕ => if p∈B then (1:ℝ)/p else 0))
    (hloc : ∀ p, p.Prime → ∃ x : ℕ × ℕ,
      ∀ i, ¬p∣quad (a i) (b i) (c i) x.1 x.2) :
    ∃ x : ℕ × ℕ, 0 < x.1 ∧ ∀ i, Squarefree (quad (a i) (b i) (c i) x.1 x.2) ∧
      ∀ p∈B, ¬p∣quad (a i) (b i) (c i) x.1 x.2 := by
  obtain ⟨η,hη,he⟩ := parameter_density a b c B ha hc hQ hdisc hB hs hloc
  obtain ⟨N,hN,hN1⟩ := (he.and (eventually_ge_atTop 1)).exists
  have hp : (0:ℝ) < η*(N:ℝ)^2 := mul_pos hη (sq_pos_of_pos (by exact_mod_cast hN1))
  have hcard : 0 < (PeriodicParameterSieve.good (fun p => p^2) (residues a b c B) N).card := by
    exact_mod_cast hp.trans_le hN
  obtain ⟨x,hx⟩ := card_pos.mp hcard
  obtain ⟨_,hxpos,hgood⟩ := mem_filter.mp hx
  refine ⟨x,hxpos,fun i => ⟨?_,?_⟩⟩
  · apply Nat.squarefree_iff_prime_squarefree.mpr
    intro p hp hd
    have hh := ((mem_residues_nat a b c B hp x).mp (hgood p hp) i).1
    exact hh (by simpa only [pow_two] using hd)
  · intro p hpB
    exact ((mem_residues_nat a b c B (hB p hpB) x).mp (hgood p (hB p hpB)) i).2 hpB

#print axioms product_lower
#print axioms uniform_tail
#print axioms parameter_density
#print axioms exists_avoiding
end Erdos1206.SquarefreePrimeParameterSieve
