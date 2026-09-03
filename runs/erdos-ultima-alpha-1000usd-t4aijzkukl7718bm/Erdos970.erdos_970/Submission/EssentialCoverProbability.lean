import Submission.EssentialCoverOrder
import Submission.SparseVoidBound

/-! An unconditional ordered-exposure union bound for the covered phase
fraction. A bound for j-1 primes forces at least j residue assignments to be
exposed; their canonical orders then give a factorial elementary-symmetric
bound. This is not by itself a uniform quadratic Jacobsthal estimate. -/
namespace Erdos970.GapAverages
open Finset Real GreedyCoverOrder

/-- Extend a normalized phase vector by zero off its prime set. -/
def phaseResidues (P : Finset ℕ) (r : Phase P) (p : ℕ) : ℕ :=
  if hp : p ∈ P then (r ⟨p, hp⟩).val else 0

lemma phaseResidues_mem (P : Finset ℕ) (r : Phase P) (p : P) :
    phaseResidues P r p.val = (r p).val := by simp [phaseResidues, p.property]

/-- Indicator that all coordinates in Q match a prescribed residue assignment. -/
noncomputable def matchingWeight (P Q : Finset ℕ) (a : ℕ → ℕ) (r : Phase P) : ℝ :=
  ∏ p : P, if p.val ∈ Q then (if (r p).val = a p.val % p.val then 1 else 0) else 1

lemma matchingWeight_nonneg (P Q : Finset ℕ) (a : ℕ → ℕ) (r : Phase P) :
    0 ≤ matchingWeight P Q a r := by
  apply prod_nonneg
  intro p hp
  split_ifs <;> norm_num

lemma matchingWeight_eq_one (P Q : Finset ℕ) (a : ℕ → ℕ) (r : Phase P)
    (hr : ∀ q ∈ Q, phaseResidues P r q ≡ a q [MOD q]) :
    matchingWeight P Q a r = 1 := by
  apply prod_eq_one
  intro p hp
  by_cases hpQ : p.val ∈ Q
  · have hh := hr p.val hpQ
    rw [phaseResidues_mem] at hh
    have he : (r p).val = a p.val % p.val := by
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt (r p).isLt] using hh
    simp only [hpQ, if_true, he]
  · simp [hpQ]

lemma phaseMean_matchingWeight (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℕ) :
    phaseMean P (matchingWeight P Q a) = ∏ q ∈ Q, (q : ℝ)⁻¹ := by
  unfold matchingWeight
  rw [phaseMean_prod P (fun p b => if p.val ∈ Q then
    (if b.val = a p.val % p.val then (1 : ℝ) else 0) else 1)]
  have he (p : P) :
      (∑ b : Fin p.val, if p.val ∈ Q then
        (if b.val = a p.val % p.val then (1 : ℝ) else 0) else 1) / (p.val : ℝ) =
      if p.val ∈ Q then (p.val : ℝ)⁻¹ else 1 := by
    by_cases hpQ : p.val ∈ Q
    · simp only [hpQ, if_true]
      have hs : (∑ b : Fin p.val, if b.val = a p.val % p.val then (1 : ℝ) else 0) = 1 := by
        simpa only [eq_comm] using coordinate_hit_sum p.val (a p.val) (hP p.val p.property).pos
      rw [hs, one_div]
    · simp only [hpQ, if_false, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      exact div_self (by exact_mod_cast (hP p.val p.property).ne_zero)
  simp_rw [he]
  calc
    _ = ∏ p ∈ P, if p ∈ Q then (p : ℝ)⁻¹ else 1 :=
      prod_attach P (fun p : ℕ => if p ∈ Q then (p : ℝ)⁻¹ else 1)
    _ = _ := by rw [prod_ite_mem, inter_eq_right.mpr hQP]

/-- If j-1 primes never cover the interval, every covered phase exposes a
canonical ordered prefix of exactly j distinct prime residues. -/
lemma covered_phase_exposes_prefix (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (m j : ℕ) (hb : IsJacobsthalBound (j - 1) m)
    (r : Phase P) (hr : intervalCount P m r = 0) :
    ∃ Q ∈ P.powersetCard j, ∃ l ∈ (Q.sort (· ≤ ·)).permutations,
      matchingWeight P Q (greedyResidues (range m) l) r = 1 := by
  classical
  have hcov : Covers (range m) P (phaseResidues P r) := by
    intro i hi
    obtain ⟨p, hp⟩ := cover_of_count_zero P m r hr i (mem_range.mp hi)
    refine ⟨p.val, p.property, ?_⟩
    rw [phaseResidues_mem]
    change i % p.val = (r p).val % p.val
    simpa only [Nat.mod_eq_of_lt (r p).isLt] using hp
  obtain ⟨A, hAP, hA⟩ := exists_essential_subcover (range m) P (phaseResidues P r) hcov
  have hjA : j ≤ A.card := by
    by_contra hn
    have hc : A.card ≤ j - 1 := by omega
    apply ((not_isJacobsthalBound_iff_cover (j - 1) m).mpr ?_) hb
    exact ⟨A, fun p hp => hP p (hAP hp), hc, phaseResidues P r,
      fun i hi => hA.1 i (mem_range.mpr hi)⟩
  obtain ⟨l, hl, hlA, _, hres⟩ := exists_essential_order (range m) A (phaseResidues P r) hA
  let t := l.take j
  have ht : t.Nodup := (List.take_sublist j l).nodup hl
  have hjl : j ≤ l.length := by rw [← List.toFinset_card_of_nodup hl, hlA]; exact hjA
  have hlen : t.length = j := by simp [t, List.length_take, min_eq_left hjl]
  let Q := t.toFinset
  have hQA : Q ⊆ A := by
    intro p hp
    rw [← hlA]
    exact List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hp))
  have hQj : Q.card = j := (List.toFinset_card_of_nodup ht).trans hlen
  refine ⟨Q, mem_powersetCard.mpr ⟨hQA.trans hAP, hQj⟩, t, ?_, ?_⟩
  · apply List.mem_permutations.mpr
    apply List.perm_of_nodup_nodup_toFinset_eq ht (Q.sort_nodup _)
    simp [Q]
  · apply matchingWeight_eq_one
    intro p hp
    have hh := hres p (hQA hp)
    rw [greedyResidues_take_of_mem (range m) l j p (List.mem_toFinset.mp hp)] at hh
    exact hh

/-- Ordered exposure gives an unconditional factorial elementary-symmetric
bound. The only input is an already valid Jacobsthal bound for j-1 primes. -/
theorem coveredFraction_le_factorial_symmetric (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m j : ℕ) (hb : IsJacobsthalBound (j - 1) m) :
    coveredFraction P m ≤
      (j.factorial : ℝ) * ∑ Q ∈ P.powersetCard j, ∏ q ∈ Q, (q : ℝ)⁻¹ := by
  classical
  let orders (Q : Finset ℕ) := (Q.sort (· ≤ ·)).permutations.toFinset
  have hpoint (r : Phase P) :
      (if intervalCount P m r = 0 then (1 : ℝ) else 0) ≤
        ∑ Q ∈ P.powersetCard j, ∑ l ∈ orders Q,
          matchingWeight P Q (greedyResidues (range m) l) r := by
    split_ifs with hr
    · obtain ⟨Q, hQ, l, hl, he⟩ := covered_phase_exposes_prefix P hP m j hb r hr
      have hinner := single_le_sum (s := orders Q)
        (f := fun l => matchingWeight P Q (greedyResidues (range m) l) r)
        (fun l _ => matchingWeight_nonneg _ _ _ _) (List.mem_toFinset.mpr hl)
      have houter := single_le_sum (s := P.powersetCard j)
        (f := fun Q => ∑ l ∈ orders Q, matchingWeight P Q (greedyResidues (range m) l) r)
        (fun Q _ => sum_nonneg (fun l _ => matchingWeight_nonneg _ _ _ _)) hQ
      dsimp only at hinner houter
      rw [he] at hinner
      exact hinner.trans houter
    · exact sum_nonneg (fun Q _ => sum_nonneg (fun l _ => matchingWeight_nonneg _ _ _ _))
  have hh := phaseMean_mono P hpoint
  change coveredFraction P m ≤ _ at hh
  rw [phaseMean_sum] at hh
  simp_rw [phaseMean_sum] at hh
  calc
    _ ≤ _ := hh
    _ = ∑ Q ∈ P.powersetCard j, ((orders Q).card : ℝ) * (∏ q ∈ Q, (q : ℝ)⁻¹) := by
      apply sum_congr rfl
      intro Q hQ
      simp only [phaseMean_matchingWeight P Q (mem_powersetCard.mp hQ).1 hP,
        sum_const, nsmul_eq_mul]
    _ ≤ ∑ Q ∈ P.powersetCard j, (j.factorial : ℝ) * (∏ q ∈ Q, (q : ℝ)⁻¹) := by
      apply sum_le_sum
      intro Q hQ
      apply mul_le_mul_of_nonneg_right _ (prod_nonneg (fun _ _ => by positivity))
      have hc : (orders Q).card ≤ j.factorial := by
        calc
          _ ≤ (Q.sort (· ≤ ·)).permutations.length := List.toFinset_card_le _
          _ = j.factorial := by rw [List.length_permutations, length_sort, (mem_powersetCard.mp hQ).2]
      exact_mod_cast hc
    _ = _ := (mul_sum _ _ _).symm

#print axioms phaseMean_matchingWeight
#print axioms covered_phase_exposes_prefix
#print axioms coveredFraction_le_factorial_symmetric
end Erdos970.GapAverages
