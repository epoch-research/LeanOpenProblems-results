import Submission.SidonModularBound

/-!
An elementary residue sieve for Sidon subsets of squares. Only the Chinese
remainder theorem is used to make the density of square residues small;
no information about primes in arithmetic progressions is needed.
These bounds do not settle Erdős 773.
-/

namespace Erdos773
open Finset Filter
open scoped Topology

noncomputable def quadraticResidues (q : ℕ) [NeZero q] : Finset (ZMod q) :=
  univ.image (fun a : ZMod q => a ^ 2)

lemma mem_quadraticResidues {q : ℕ} [NeZero q] (r : ZMod q) :
    r ∈ quadraticResidues q ↔ ∃ a : ZMod q, a ^ 2 = r := by
  simp [quadraticResidues]

lemma quadraticResidues_card_le (q : ℕ) [NeZero q] :
    (quadraticResidues q).card ≤ q / 2 + 1 := by
  let T := (range (q / 2 + 1)).image (fun a : ℕ => (a : ZMod q) ^ 2)
  have hsub : quadraticResidues q ⊆ T := by
    intro r hr
    obtain ⟨a, rfl⟩ := (mem_quadraticResidues r).mp hr
    by_cases ha : a.val ≤ q / 2
    · exact mem_image.mpr ⟨a.val, mem_range.mpr (by omega), by simp⟩
    · have ha' := ZMod.val_lt a
      refine mem_image.mpr ⟨q - a.val, mem_range.mpr (by omega), ?_⟩
      have he : ((q - a.val : ℕ) : ZMod q) = -a := by
        rw [Nat.cast_sub ha'.le, ZMod.natCast_self, ZMod.natCast_zmod_val, zero_sub]
      rw [he, neg_sq]
  exact (card_le_card hsub).trans
    ((card_image_le (s := range (q / 2 + 1)) (f := fun a : ℕ => (a : ZMod q) ^ 2)).trans_eq
      (card_range _))

lemma quadraticResidues_card_mul_le (m n : ℕ) [NeZero m] [NeZero n]
    (hc : m.Coprime n) :
    (quadraticResidues (m * n)).card ≤
      (quadraticResidues m).card * (quadraticResidues n).card := by
  rw [← card_product]
  apply card_le_card_of_injOn (ZMod.chineseRemainder hc)
  · intro r hr
    obtain ⟨a, rfl⟩ := (mem_quadraticResidues r).mp hr
    rw [map_pow]
    exact mem_product.mpr ⟨(mem_quadraticResidues _).mpr
      ⟨(ZMod.chineseRemainder hc a).1, rfl⟩,
      (mem_quadraticResidues _).mpr ⟨(ZMod.chineseRemainder hc a).2, rfl⟩⟩
  · exact fun _ _ _ _ h => (ZMod.chineseRemainder hc).injective h

noncomputable def quadraticResidueDensity (q : ℕ) : ℝ :=
  if h : q = 0 then 1 else
    letI : NeZero q := ⟨h⟩
    (quadraticResidues q).card / (q : ℝ)

lemma quadraticResidueDensity_eq (q : ℕ) [NeZero q] :
    quadraticResidueDensity q = (quadraticResidues q).card / (q : ℝ) := by
  simp [quadraticResidueDensity, NeZero.ne q]

lemma quadraticResidueDensity_nonneg (q : ℕ) : 0 ≤ quadraticResidueDensity q := by
  unfold quadraticResidueDensity
  split <;> positivity

lemma quadraticResidueDensity_le_one (q : ℕ) [NeZero q] :
    quadraticResidueDensity q ≤ 1 := by
  rw [quadraticResidueDensity_eq]
  apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q))).mpr
  exact_mod_cast (by simpa using card_le_univ (quadraticResidues q) :
    (quadraticResidues q).card ≤ q)

lemma quadraticResidueDensity_mul_le (m n : ℕ) [NeZero m] [NeZero n]
    (hc : m.Coprime n) :
    quadraticResidueDensity (m * n) ≤
      quadraticResidueDensity m * quadraticResidueDensity n := by
  simp only [quadraticResidueDensity_eq, Nat.cast_mul, div_mul_div_comm]
  exact div_le_div_of_nonneg_right (by exact_mod_cast quadraticResidues_card_mul_le m n hc)
    (by positivity)

lemma quadraticResidueDensity_le_three_quarters (q : ℕ) (hq : 4 ≤ q) :
    quadraticResidueDensity q ≤ 3 / 4 := by
  letI : NeZero q := ⟨by omega⟩
  rw [quadraticResidueDensity_eq]
  apply (div_le_iff₀ (by exact_mod_cast (show 0 < q by omega))).mpr
  have hc : ((quadraticResidues q).card : ℝ) ≤ (q / 2 : ℕ) + 1 := by
    exact_mod_cast quadraticResidues_card_le q
  have hd : ((q / 2 : ℕ) : ℝ) ≤ (q : ℝ) / 2 := by
    exact_mod_cast (Nat.cast_div_le (m := q) (n := 2) (α := ℝ))
  have hq' : (4 : ℝ) ≤ q := by exact_mod_cast hq
  linarith

lemma exists_small_quadraticResidueDensity (δ : ℝ) (hδ : 0 < δ) :
    ∃ Q : ℕ, 0 < Q ∧ quadraticResidueDensity Q < δ := by
  have hconstruct (k : ℕ) : ∃ Q : ℕ, 0 < Q ∧
      quadraticResidueDensity Q ≤ (3 / 4 : ℝ) ^ k := by
    induction k with
    | zero => exact ⟨1, by omega, by simpa using quadraticResidueDensity_le_one 1⟩
    | succ k ih =>
      obtain ⟨Q, hQ, hd⟩ := ih
      letI : NeZero Q := ⟨hQ.ne'⟩
      letI : NeZero (4 * Q + 1) := ⟨by omega⟩
      have hc : Q.Coprime (4 * Q + 1) := by
        simp [Nat.coprime_mul_right_add_right]
      refine ⟨Q * (4 * Q + 1), by positivity, ?_⟩
      calc
        _ ≤ quadraticResidueDensity Q * quadraticResidueDensity (4 * Q + 1) :=
          quadraticResidueDensity_mul_le _ _ hc
        _ ≤ (3 / 4 : ℝ) ^ k * (3 / 4) :=
          mul_le_mul hd (quadraticResidueDensity_le_three_quarters _ (by omega))
            (quadraticResidueDensity_nonneg _) (by positivity)
        _ = _ := (pow_succ _ _).symm
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1)
  obtain ⟨k, hk⟩ := ((ht.eventually (gt_mem_nhds hδ)).exists)
  obtain ⟨Q, hQ, hd⟩ := hconstruct k
  exact ⟨Q, hQ, hd.trans_lt hk⟩

lemma square_sidon_modular_card_bound {A : Finset ℕ} {N Q : ℕ} [NeZero Q]
    (hA : A ⊆ (Icc 1 N).image (fun n : ℕ => n ^ 2))
    (hs : IsSidon (A : Set ℕ)) :
    A.card ^ 2 ≤ (quadraticResidues Q).card * (A.card + 2 * (N ^ 2 / Q) + 1) := by
  let C := (quadraticResidues Q).image ZMod.val
  have hc : C.card = (quadraticResidues Q).card :=
    card_image_iff.mpr (fun _ _ _ _ h => ZMod.val_injective Q h)
  rw [← hc]
  apply sidon_modular_card_bound hs
  · intro a ha
    obtain ⟨n, hn, rfl⟩ := mem_image.mp (hA ha)
    exact Nat.pow_le_pow_left (mem_Icc.mp hn).2 2
  · intro a ha
    obtain ⟨n, hn, rfl⟩ := mem_image.mp (hA ha)
    refine mem_image.mpr ⟨(n : ZMod Q) ^ 2, (mem_quadraticResidues _).mpr ⟨n, rfl⟩, ?_⟩
    rw [← Nat.cast_pow, ZMod.val_natCast]

lemma max_square_sidon_modular_card_bound (N Q : ℕ) [NeZero Q] :
    let M := Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2))
    M ^ 2 ≤ (quadraticResidues Q).card * (M + 2 * (N ^ 2 / Q) + 1) := by
  classical
  let S := (Icc 1 N).image (fun n : ℕ => n ^ 2)
  have hne : (S.powerset.filter (fun A : Finset ℕ => IsSidon (A : Set ℕ))).Nonempty := by
    refine ⟨∅, mem_filter.mpr ⟨by simp, ?_⟩⟩
    intro a ha
    simp at ha
  obtain ⟨A, hA, he⟩ := exists_mem_eq_sup _ hne Finset.card
  have hA' := mem_filter.mp hA
  change ((S.powerset.filter (fun A : Finset ℕ => IsSidon (A : Set ℕ))).sup
    Finset.card) ^ 2 ≤ _ * (((S.powerset.filter (fun A : Finset ℕ =>
      IsSidon (A : Set ℕ))).sup Finset.card) + 2 * (N ^ 2 / Q) + 1)
  rw [he]
  exact square_sidon_modular_card_bound (mem_powerset.mp hA'.1) hA'.2

lemma max_square_sidon_card_le (N : ℕ) :
    Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2)) ≤ N := by
  classical
  unfold Finset.maxSidonSubsetCard
  apply Finset.sup_le
  intro A hA
  have hsub := mem_powerset.mp (mem_filter.mp hA).1
  exact (card_le_card hsub).trans (by simpa using
    (card_image_le (s := Icc 1 N) (f := fun n : ℕ => n ^ 2)))

lemma max_square_sidon_real_modular_bound (N Q : ℕ) [NeZero Q] :
    (Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ) ^ 2 ≤
      2 * quadraticResidueDensity Q * (N : ℝ) ^ 2 +
        (quadraticResidues Q).card * ((N : ℝ) + 1) := by
  let M := Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2))
  have hb : (M : ℝ) ^ 2 ≤ (quadraticResidues Q).card *
      ((M : ℝ) + 2 * ((N ^ 2 / Q : ℕ) : ℝ) + 1) := by
    exact_mod_cast max_square_sidon_modular_card_bound N Q
  have hm : (M : ℝ) ≤ N := by exact_mod_cast max_square_sidon_card_le N
  have hd : ((N ^ 2 / Q : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 / Q := by
    apply (le_div_iff₀ (show (0 : ℝ) < Q by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q))).mpr
    exact_mod_cast Nat.div_mul_le_self (N ^ 2) Q
  have h := mul_le_mul_of_nonneg_left (show
      (M : ℝ) + 2 * ((N ^ 2 / Q : ℕ) : ℝ) + 1 ≤
        N + 2 * ((N : ℝ) ^ 2 / Q) + 1 by linarith)
    (Nat.cast_nonneg (α := ℝ) (quadraticResidues Q).card)
  rw [quadraticResidueDensity_eq]
  change (M : ℝ) ^ 2 ≤ _
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith

lemma square_sidon_elementary_eventually_small_linear (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      (Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ) ≤
        δ * N := by
  obtain ⟨Q, hQ, hsmall⟩ := exists_small_quadraticResidueDensity (δ ^ 2 / 4) (by positivity)
  letI : NeZero Q := ⟨hQ.ne'⟩
  have hNlim : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hNlim.eventually (eventually_ge_atTop (1 : ℝ)),
    hNlim.eventually (eventually_ge_atTop
      (4 * ((quadraticResidues Q).card : ℝ) / δ ^ 2))] with N hN1 hNc
  have hmain := max_square_sidon_real_modular_bound N Q
  have hsmall' : 2 * quadraticResidueDensity Q ≤ δ ^ 2 / 2 := by linarith
  have hsmallN := mul_le_mul_of_nonneg_right hsmall' (sq_nonneg (N : ℝ))
  have hNc' := (div_le_iff₀ (sq_pos_of_pos hδ)).mp hNc
  have hNcN := mul_le_mul_of_nonneg_right hNc' (Nat.cast_nonneg (α := ℝ) N)
  have hsN := mul_le_mul_of_nonneg_left hN1
    (Nat.cast_nonneg (α := ℝ) (quadraticResidues Q).card)
  apply (sq_le_sq₀ (Nat.cast_nonneg _) (mul_nonneg hδ.le (Nat.cast_nonneg N))).mp
  nlinarith

lemma square_sidon_elementary_density_zero :
    Tendsto (fun N : ℕ =>
      (Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ) / N)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [square_sidon_elementary_eventually_small_linear (ε / 2) (by positivity),
    eventually_ge_atTop 1] with N hN hN1
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  apply lt_of_le_of_lt ((div_le_iff₀ hNp).mpr hN)
  linarith

#print axioms max_square_sidon_modular_card_bound
#print axioms exists_small_quadraticResidueDensity
#print axioms square_sidon_elementary_density_zero

end Erdos773
