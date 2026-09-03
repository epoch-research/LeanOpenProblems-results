import Submission.BuchstabLinearTransfer
import Submission.BuchstabIntervalSurvivor

/-! Quantitative survivor counts, including complete errors and virtual-hit
marginal domination. No independence of interval positions is assumed. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real FiniteSelberg
open scoped Classical

lemma count_of_scaled_linear_refinement {α : Type*} (A : Finset α) (w : α → ℝ)
    (ω : α → ℕ → Bool) (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime)
    (hmono : StrictMono p) (x D : ℝ) (K J : ℕ) (hKJ : K ≤ J) (hx : 0 ≤ x) (hD : 0 ≤ D)
    (hw : ∀ j ∈ A, 0 ≤ w j)
    (hmoment : ∀ T : Finset ℕ, T ⊆ range K →
      |moment A w ω T-x*∏ i ∈ T, 1/(p i : ℝ)| ≤ 1) (n : ℕ) :
    x*lowerStep (fun i => 1/(p i : ℝ)) (primeKeep p)
      (upperMain (fun i => 1/(p i : ℝ)) (primeKeep p) (scaledSelbergBase p) n) K D-
      4*(1+prefixReciprocal p J)^(2*n+1)*D ≤ sifted A w ω ∅ K := by
  have hs := (refinement_sound A w ω (fun i => 1/(p i : ℝ)) x D K (primeKeep p)
    (scaledSelbergBase p) scaledSelbergCost hw (fun i => by positivity) hx
      scaledSelbergCost_nonneg hmoment (by
        intro k hk T hTK hT
        simpa only [scaledSelbergBase,scaledSelbergCost,mul_assoc] using
          conditional_selberg_upper A w ω p hp hmono.injective x (4*D) K hw hmoment k hk T hTK hT)
      n K le_rfl ∅ (empty_subset _) (by simp)).1
  simp only [prod_empty,mul_one] at hs
  exact (sub_le_sub_left (scaled_refined_lowerError_le_linear p hp hmono n K J hKJ D hD) _).trans hs

lemma boosted_sifted_le_count (k m : ℕ) (b : Fin k → ℝ)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1) (ω : ℕ → Fin k → Bool) :
    sifted ((range m) ×ˢ (univ : Finset (Fin k → Bool)))
      (fun x => probability b x.2)
      (fun x => extendPattern (fun i => ω x.1 i || x.2 i)) ∅ k ≤
      ∑ j ∈ range m, if ∀ i, ω j i = false then (1 : ℝ) else 0 := by
  unfold sifted
  rw [sum_product]
  have he (v : ℕ → Bool) : hit ∅ v = 1 := by simp [hit]
  simp only [he,one_mul]
  apply sum_le_sum
  intro j hj
  change average b (fun η => avoid k (extendPattern (fun i => ω j i || η i))) ≤ _
  by_cases h : ∀ i, ω j i = false
  · rw [if_pos h,← average_const b 1]
    apply average_mono b hb
    intro η
    unfold avoid
    split_ifs <;> norm_num
  · rw [if_neg h,← average_const b 0]
    apply average_mono b hb
    intro η
    have hn : ¬∀ i < k, extendPattern (fun i => ω j i || η i) i = false := by
      intro hh
      apply h
      intro i
      have hi := hh i.val i.isLt
      simp only [extendPattern,i.isLt,↓reduceDIte] at hi
      exact (Bool.or_eq_false_iff.mp hi).1
    simp only [avoid,if_neg hn,le_refl]

/-- Virtual OR hits can only reduce the number of survivors. Thus the whole
quantitative lower bound, not just positivity, transfers to smaller marginals. -/
theorem count_from_dominating_linear_refinement (k J m : ℕ) (hkJ : k ≤ J) (q : Fin k → ℝ)
    (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime) (hmono : StrictMono p)
    (hq : ∀ i, q i < 1 ∧ q i ≤ 1/(p i.val : ℝ))
    (ω : ℕ → Fin k → Bool)
    (herr : ∀ T : Finset (Fin k),
      |(∑ j ∈ range m, hitMonomial T (ω j))-(m : ℝ)*∏ i ∈ T, q i| ≤ 1)
    (D : ℝ) (hD : 0 ≤ D) (n : ℕ) :
    (m : ℝ)*lowerStep (fun i => 1/(p i : ℝ)) (primeKeep p)
      (upperMain (fun i => 1/(p i : ℝ)) (primeKeep p) (scaledSelbergBase p) n) k D-
      4*(1+prefixReciprocal p J)^(2*n+1)*D ≤
      ∑ j ∈ range m, if ∀ i, ω j i = false then (1 : ℝ) else 0 := by
  classical
  let q' (i : Fin k) : ℝ := 1/(p i.val : ℝ)
  have hq' (i : Fin k) : q' i ≤ 1 := by
    have hp' : (1 : ℝ) < p i.val := by exact_mod_cast (hp i.val).one_lt
    exact ((div_lt_one (by linarith : (0 : ℝ) < p i.val)).mpr hp').le
  let b (i : Fin k) := (q' i-q i)/(1-q i)
  have hb (i : Fin k) : 0 ≤ b i ∧ b i ≤ 1 := by
    have hd : 0 < 1-q i := sub_pos.mpr (hq i).1
    exact ⟨div_nonneg (sub_nonneg.mpr (hq i).2) hd.le,
      (div_le_one hd).mpr (by linarith [hq' i])⟩
  have hbq (i : Fin k) : b i+(1-b i)*q i = q' i := by
    have hd : 1-q i ≠ 0 := (sub_pos.mpr (hq i).1).ne'
    dsimp [b]
    field_simp
    ring
  let A := (range m) ×ˢ (univ : Finset (Fin k → Bool))
  let w (x : ℕ × (Fin k → Bool)) := probability b x.2
  let v (x : ℕ × (Fin k → Bool)) := extendPattern (fun i => ω x.1 i || x.2 i)
  have hw : ∀ x ∈ A, 0 ≤ w x := by
    intro x hx
    apply prod_nonneg
    intro i hi
    split_ifs
    · exact (hb i).1
    · exact sub_nonneg.mpr (hb i).2
  have hmom (T : Finset ℕ) (hT : T ⊆ range k) :
      |moment A w v T-(m : ℝ)*∏ i ∈ T, 1/(p i : ℝ)| ≤ 1 := by
    have hh := added_hits_moment_error b q hb m ω herr (liftSet k T)
    simp_rw [hbq] at hh
    dsimp only [q'] at hh
    rw [liftSet_prod T hT (fun i => 1/(p i : ℝ))] at hh
    simpa only [A,w,v,boosted_moment] using hh
  have hc := count_of_scaled_linear_refinement A w v p hp hmono (m : ℝ) D k J hkJ
    (Nat.cast_nonneg m) hD hw hmom n
  exact hc.trans (boosted_sifted_le_count k m b hb ω)

/-- Actual arbitrary-prime interval count under the same numerical reference
main term and complete error budget. -/
theorem prime_count_of_linear_refinement (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ → ℕ) (k m : ℕ) (hPk : P.card ≤ k) (D : ℝ) (hD : 0 ≤ D)
    (hkeep : primeKeep nthPrime k D) :
    (m : ℝ)*referenceLower 1 k D-4*(1+prefixReciprocal nthPrime k)^3*D ≤
      (((range m).filter (fun j => ∀ p ∈ P, ¬j ≡ r p [MOD p])).card : ℝ) := by
  classical
  let p : Fin P.card → ℕ := P.orderEmbOfFin rfl
  have hp : ∀ i, (p i).Prime := fun i => hP _ (P.orderEmbOfFin_mem rfl i)
  have hmono : StrictMono p := (P.orderEmbOfFin rfl).strictMono
  let q : Fin P.card → ℝ := fun i => 1/(p i : ℝ)
  have hq (i : Fin P.card) : q i < 1 ∧ q i ≤ 1/(nthPrime i.val : ℝ) := by
    have ha : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
    have hb : (0 : ℝ) < nthPrime i.val := by exact_mod_cast (nthPrime_prime i.val).pos
    have hab : (nthPrime i.val : ℝ) ≤ p i := by exact_mod_cast nth_prime_le_sorted p hp hmono i
    exact ⟨(div_lt_one (by linarith)).mpr ha,one_div_le_one_div_of_le hb hab⟩
  have hc := count_from_dominating_linear_refinement P.card k m hPk q nthPrime nthPrime_prime nthPrime_strictMono
    hq (fun j i => decide (j ≡ r (p i) [MOD p i]))
    (prime_hits_intersection_error p hp hmono.injective r m) D hD 1
  have hind (j : ℕ) : (∀ i : Fin P.card, ¬j ≡ r (p i) [MOD p i]) ↔ ∀ b ∈ P, ¬j ≡ r b [MOD b] := by
    constructor
    · intro hh b hb
      have hrange : b ∈ Set.range p := by simpa only [p,Finset.range_orderEmbOfFin,mem_coe] using hb
      obtain ⟨i,rfl⟩ := hrange
      exact hh i
    · intro hh i
      exact hh _ (P.orderEmbOfFin_mem rfl i)
  simp only [decide_eq_false_iff_not,hind] at hc
  rw [sum_boole] at hc
  change (m : ℝ)*referenceLower 1 P.card D-4*(1+prefixReciprocal nthPrime k)^3*D ≤ _ at hc
  exact (sub_le_sub_right (mul_le_mul_of_nonneg_left
    (referenceLower_antitone_prefix 1 P.card k hPk D hkeep) (Nat.cast_nonneg m)) _).trans hc

#print axioms count_from_dominating_linear_refinement
#print axioms prime_count_of_linear_refinement
end Erdos970.RecursiveSieve.Buchstab
