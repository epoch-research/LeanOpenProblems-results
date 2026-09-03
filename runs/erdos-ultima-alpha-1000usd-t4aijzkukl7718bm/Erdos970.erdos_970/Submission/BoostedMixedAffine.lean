import Submission.SieveCertificateTransfer

/-! Transport of affine lower bounds for mixed hit/avoidance populations under
independent added hits. The survival factor on avoided coordinates is retained.
These identities do not assert a quadratic Jacobsthal estimate. -/
namespace Erdos970.FiniteSelberg
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def avoidMonomial (B : Finset ι) (ω : ι → Bool) : ℝ :=
  if ∀ i ∈ B, ω i = false then 1 else 0

noncomputable def mixedMonomial (A B : Finset ι) (ω : ι → Bool) : ℝ :=
  hitMonomial A ω * avoidMonomial B ω

noncomputable def mixedMass (m : ℕ) (A B : Finset ι) (ω : ℕ → ι → Bool) : ℝ :=
  ∑ x ∈ range m, mixedMonomial A B (ω x)

lemma avoidMonomial_nonneg (B : Finset ι) (ω : ι → Bool) :
    0 ≤ avoidMonomial B ω := by unfold avoidMonomial; split_ifs <;> norm_num

lemma mixedMonomial_nonneg (A B : Finset ι) (ω : ι → Bool) :
    0 ≤ mixedMonomial A B ω := by
  apply mul_nonneg _ (avoidMonomial_nonneg B ω)
  simp only [hitMonomial_eq]
  split_ifs <;> norm_num

lemma avoidMonomial_prod (B : Finset ι) (ω : ι → Bool) :
    avoidMonomial B ω = ∏ i : ι, if i ∈ B then (if ω i then (0 : ℝ) else 1) else 1 := by
  rw [prod_ite_mem, univ_inter]
  by_cases h : ∀ i ∈ B, ω i = false
  · rw [avoidMonomial, if_pos h]
    symm
    apply prod_eq_one
    intro i hi
    simp only [h i hi, Bool.false_eq_true, if_false]
  · rw [avoidMonomial, if_neg h]
    symm
    push_neg at h
    obtain ⟨i,hi,hw⟩ := h
    apply prod_eq_zero hi
    cases he : ω i <;> simp_all

lemma avoidMonomial_or (B : Finset ι) (ω η : ι → Bool) :
    avoidMonomial B (fun i => ω i || η i) = avoidMonomial B ω * avoidMonomial B η := by
  have he : (∀ i ∈ B, (ω i || η i) = false) ↔
      (∀ i ∈ B, ω i = false) ∧ (∀ i ∈ B, η i = false) := by
    simp only [Bool.or_eq_false_iff]
    aesop
  simp only [avoidMonomial, he]
  split_ifs <;> simp_all

lemma mixedMass_or (m : ℕ) (A B : Finset ι) (ω : ℕ → ι → Bool) (η : ι → Bool) :
    mixedMass m A B (fun x i => ω x i || η i) =
      avoidMonomial B η * mixedMass m (A.filter (fun i => η i = false)) B ω := by
  simp only [mixedMass, mixedMonomial, hitMonomial_or, avoidMonomial_or, mul_sum]
  exact sum_congr rfl (fun _ _ => by ring)

/-- Independence between disjoint hit and avoided coordinates, with the latter
restricted to no added hits. No independence of arithmetic residue rows is used. -/
theorem average_avoid_restricted_prod (a q : ι → ℝ) (A B : Finset ι)
    (hd : Disjoint A B) :
    average a (fun η => avoidMonomial B η *
      ∏ i ∈ A.filter (fun i => η i = false), q i) =
      (∏ i ∈ B, (1-a i)) * (∏ i ∈ A, (a i+(1-a i)*q i)) := by
  have he (η : ι → Bool) :
      (∏ i ∈ A.filter (fun i => η i = false), q i) =
        ∏ i : ι, if i ∈ A then (if η i then 1 else q i) else 1 := by
    rw [prod_filter, prod_ite_mem, univ_inter]
    apply prod_congr rfl
    intro i hi
    cases η i <;> simp
  simp_rw [avoidMonomial_prod, he, ← prod_mul_distrib]
  rw [average_prod a (fun i b =>
    (if i ∈ B then (if b then (0 : ℝ) else 1) else 1)*
    (if i ∈ A then (if b then 1 else q i) else 1))]
  have hc (i : ι) :
      a i*((if i ∈ B then (0 : ℝ) else 1)*(if i ∈ A then 1 else 1))+
        (1-a i)*((if i ∈ B then (1 : ℝ) else 1)*(if i ∈ A then q i else 1)) =
      (if i ∈ B then (1-a i) else 1)*
        (if i ∈ A then (a i+(1-a i)*q i) else 1) := by
    by_cases hiA : i ∈ A
    · have hiB : i ∉ B := fun hiB => disjoint_left.mp hd hiA hiB
      simp [hiA,hiB]
    · by_cases hiB : i ∈ B <;> simp [hiA,hiB] <;> ring
  simp only [Bool.false_eq_true, ↓reduceIte]
  simp_rw [hc]
  rw [prod_mul_distrib]
  simp only [prod_ite_mem, univ_inter]

lemma average_avoidMonomial (a : ι → ℝ) (B : Finset ι) :
    average a (avoidMonomial B) = ∏ i ∈ B, (1-a i) := by
  simpa only [filter_empty, prod_empty, mul_one] using
    average_avoid_restricted_prod a (fun _ => 0) ∅ B (disjoint_empty_left B)

/-- Affine lower bounds on every relaxed required-hit set survive averaging.
The factor prod(1-a) is essential: it is the probability that the added pattern
leaves every avoided coordinate unhit. -/
theorem added_hits_mixed_affine_lower (a q : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (m : ℕ) (A B : Finset ι)
    (hd : Disjoint A B) (ω : ℕ → ι → Bool) (α β : ℝ)
    (hbase : ∀ U ⊆ A, α*((m : ℝ)*∏ i ∈ U, q i-1)-β ≤ mixedMass m U B ω) :
    (∏ i ∈ B, (1-a i)) * max 0
      (α*((m : ℝ)*∏ i ∈ A, (a i+(1-a i)*q i)-1)-β) ≤
        average a (fun η => mixedMass m A B (fun x i => ω x i || η i)) := by
  have hp : 0 ≤ ∏ i ∈ B, (1-a i) :=
    prod_nonneg (fun i _ => sub_nonneg.mpr (ha i).2)
  have hpoint (η : ι → Bool) :
      avoidMonomial B η * (α*((m : ℝ)*∏ i ∈ A.filter (fun i => η i = false), q i-1)-β) ≤
      mixedMass m A B (fun x i => ω x i || η i) := by
    rw [mixedMass_or]
    exact mul_le_mul_of_nonneg_left (hbase _ (filter_subset _ _)) (avoidMonomial_nonneg B η)
  have hh := average_mono a ha _ _ hpoint
  have he : (fun η => avoidMonomial B η *
      (α*((m : ℝ)*∏ i ∈ A.filter (fun i => η i = false), q i-1)-β)) =
      fun η => (α*(m : ℝ))*(avoidMonomial B η *
        ∏ i ∈ A.filter (fun i => η i = false), q i) -
        (α+β)*avoidMonomial B η := by
    funext η
    ring
  rw [he, average_sub, average_mul_const, average_mul_const,
    average_avoid_restricted_prod a q A B hd, average_avoidMonomial] at hh
  have hn : 0 ≤ average a (fun η => mixedMass m A B (fun x i => ω x i || η i)) := by
    apply average_nonneg a ha
    intro η
    exact sum_nonneg (fun x _ => mixedMonomial_nonneg A B (fun i => ω x i || η i))
  rw [mul_max_of_nonneg 0 _ hp, mul_zero]
  apply max_le hn
  nlinarith only [hh]

/-- The exact loss on avoided coordinates when boosting q to q'. -/
theorem added_hits_survival_ratio (q q' : ι → ℝ)
    (hq : ∀ i, q i < 1) (B : Finset ι) :
    (∏ i ∈ B, (1-(q' i-q i)/(1-q i))) =
      (∏ i ∈ B, (1-q' i))/(∏ i ∈ B, (1-q i)) := by
  rw [← prod_div_distrib]
  apply prod_congr rfl
  intro i hi
  have hn : 1-q i ≠ 0 := (sub_pos.mpr (hq i)).ne'
  field_simp
  ring

/-- A uniform, deliberately weaker bound replaces the exact survival ratio
by the reference density. It does not replace that factor by one. -/
theorem reference_mixed_affine_lower (q q' : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i < 1 ∧ q i ≤ q' i ∧ q' i ≤ 1)
    (m : ℕ) (A B : Finset ι) (hd : Disjoint A B) (ω : ℕ → ι → Bool)
    (α β : ℝ)
    (hbase : ∀ U ⊆ A, α*((m : ℝ)*∏ i ∈ U, q i-1)-β ≤ mixedMass m U B ω) :
    (∏ i ∈ B, (1-q' i)) * max 0
      (α*((m : ℝ)*∏ i ∈ A, q' i-1)-β) ≤
        average (fun i => (q' i-q i)/(1-q i))
          (fun η => mixedMass m A B (fun x i => ω x i || η i)) := by
  let a (i : ι) := (q' i-q i)/(1-q i)
  have ha (i : ι) : 0 ≤ a i ∧ a i ≤ 1 := by
    have hd0 : 0 < 1-q i := sub_pos.mpr (hq i).2.1
    constructor
    · exact div_nonneg (sub_nonneg.mpr (hq i).2.2.1) hd0.le
    · exact (div_le_one hd0).mpr (by linarith [(hq i).2.2.2])
  have he (i : ι) : a i+(1-a i)*q i = q' i := by
    have hn : 1-q i ≠ 0 := (sub_pos.mpr (hq i).2.1).ne'
    dsimp [a]
    field_simp
    ring
  have ha' (i : ι) : a i ≤ q' i := by
    apply (div_le_iff₀ (sub_pos.mpr (hq i).2.1)).mpr
    have hn := mul_nonneg (hq i).1 (sub_nonneg.mpr (hq i).2.2.2)
    nlinarith
  have hp : (∏ i ∈ B, (1-q' i)) ≤ ∏ i ∈ B, (1-a i) := by
    apply prod_le_prod
    · intro i hi
      exact sub_nonneg.mpr (hq i).2.2.2
    · intro i hi
      linarith [ha' i]
  have hh := added_hits_mixed_affine_lower a q ha m A B hd ω α β hbase
  simp only [he] at hh
  exact (mul_le_mul_of_nonneg_right hp (le_max_left 0 _)).trans hh

#print axioms average_avoid_restricted_prod
#print axioms added_hits_mixed_affine_lower
#print axioms added_hits_survival_ratio
#print axioms reference_mixed_affine_lower
end Erdos970.FiniteSelberg
