import FormalConjecturesUtil

/-! An arithmetic translation of the ideal-valued covering-system statement. -/

open Set Pointwise
namespace Erdos7Reduction

theorem span_not_le_two_iff (m : ℤ) :
    ¬ Ideal.span {m} ≤ Ideal.span ({2} : Set ℤ) ↔ Odd m := by
  rw [Ideal.span_singleton_le_span_singleton, ← even_iff_two_dvd,
    Int.not_even_iff_odd]

theorem ideal_not_le_two_iff (I : Ideal ℤ) :
    ¬ I ≤ Ideal.span ({2} : Set ℤ) ↔ Odd I.absNorm := by
  conv_lhs => rw [← Int.ideal_span_absNorm_eq_self I]
  rw [span_not_le_two_iff, Int.odd_coe_nat]

theorem integer_coset_iff (a x : ℤ) (I : Ideal ℤ) :
    x ∈ ({a} : Set ℤ) + (I : Set ℤ) ↔ (I.absNorm : ℤ) ∣ x - a := by
  rw [Set.mem_add]
  constructor
  · rintro ⟨y, hy, z, hz, h⟩
    have hy' : y = a := Set.mem_singleton_iff.mp hy
    subst y
    have hx : x - a = z := by omega
    rw [hx, ← Ideal.mem_span_singleton, Int.ideal_span_absNorm_eq_self]
    exact hz
  · intro h
    refine ⟨a, Set.mem_singleton a, x - a, ?_, by omega⟩
    change x - a ∈ I
    rwa [← Int.ideal_span_absNorm_eq_self I, Ideal.mem_span_singleton]

theorem moduli_absNorm_injective (C : StrictCoveringSystem ℤ) :
    Function.Injective (fun i => (C.moduli i).absNorm) := by
  intro i j h
  dsimp only at h
  apply C.injective_moduli
  rw [← Int.ideal_span_absNorm_eq_self (C.moduli i),
    ← Int.ideal_span_absNorm_eq_self (C.moduli j), h]

theorem moduli_absNorm_gt_one (C : StrictCoveringSystem ℤ) (i : C.ι) :
    1 < (C.moduli i).absNorm := by
  have h0 : (C.moduli i).absNorm ≠ 0 := by
    intro h
    apply C.ne_bot i
    rw [← Int.ideal_span_absNorm_eq_self (C.moduli i), h]
    simp
  have h1 : (C.moduli i).absNorm ≠ 1 := by
    intro h
    apply C.ne_top i
    rw [← Int.ideal_span_absNorm_eq_self (C.moduli i), h]
    simp
  omega

theorem arithmetic_cover (C : StrictCoveringSystem ℤ) (x : ℤ) :
    ∃ i, ((C.moduli i).absNorm : ℤ) ∣ x - C.residue i := by
  have hx : x ∈ ⋃ i, ({C.residue i} : Set ℤ) + (C.moduli i : Set ℤ) := by
    rw [C.unionCovers]
    trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact ⟨i, (integer_coset_iff _ _ _).mp hi⟩

end Erdos7Reduction

namespace Erdos7Reduction
open Set Pointwise

theorem span_absNorm_nat (n : ℕ) :
    (Ideal.span {(n : ℤ)}).absNorm = n := by
  simp [Ideal.absNorm_span_singleton]

theorem arithmetic_formulation :
    (∃ C : StrictCoveringSystem ℤ, ∀ i,
      ¬ C.moduli i ≤ Ideal.span {2} ∧ C.moduli i ≠ ⊤) ↔
    ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ) (a : ι → ℤ),
      Function.Injective m ∧ (∀ i, 1 < m i ∧ Odd (m i)) ∧
      ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C.ι, C.fintypeIndex, fun i => (C.moduli i).absNorm, C.residue,
      moduli_absNorm_injective C,
      fun i => ⟨moduli_absNorm_gt_one C i,
        (ideal_not_le_two_iff _).mp (hC i).1⟩,
      arithmetic_cover C⟩
  · rintro ⟨ι, fι, m, a, hm, ho, hc⟩
    letI : Fintype ι := fι
    let C : StrictCoveringSystem ℤ := {
      ι := ι
      residue := a
      moduli := fun i => Ideal.span {(m i : ℤ)}
      unionCovers := by
        ext x
        simp only [mem_iUnion, mem_univ, iff_true]
        obtain ⟨i, hi⟩ := hc x
        refine ⟨i, (integer_coset_iff _ _ _).mpr ?_⟩
        simpa only [span_absNorm_nat] using hi
      ne_bot := by
        intro i h
        have hh := congrArg Ideal.absNorm h
        simp only [span_absNorm_nat, Ideal.absNorm_bot] at hh
        have := (ho i).1
        omega
      ne_top := by
        intro i h
        have hh := congrArg Ideal.absNorm h
        simp only [span_absNorm_nat, Ideal.absNorm_top] at hh
        have := (ho i).1
        omega
      injective_moduli := by
        intro i j h
        apply hm
        have hh := congrArg Ideal.absNorm h
        simpa only [span_absNorm_nat] using hh }
    refine ⟨C, fun i => ⟨?_, C.ne_top i⟩⟩
    change ¬ Ideal.span {(m i : ℤ)} ≤ Ideal.span {2}
    rw [span_not_le_two_iff, Int.odd_coe_nat]
    exact (ho i).2

#print axioms arithmetic_formulation
end Erdos7Reduction

namespace Erdos7Reduction
open Set Pointwise

theorem density_necessary (C : StrictCoveringSystem ℤ) :
    letI := C.fintypeIndex
    1 ≤ ∑ i, ((C.moduli i).absNorm : ℚ)⁻¹ := by
  letI := C.fintypeIndex
  have hc : ⋃ i ∈ (Finset.univ : Finset C.ι),
      C.residue i +ᵥ ((C.moduli i).toAddSubgroup : Set ℤ) = Set.univ := by
    simpa only [Finset.mem_univ, iUnion_true, Set.singleton_add] using C.unionCovers
  have h := AddSubgroup.one_le_sum_inv_index_of_leftCoset_cover hc
  simpa only [Ideal.absNorm_apply, Submodule.cardQuot] using h

end Erdos7Reduction

namespace Erdos7Reduction
open Set Pointwise

private theorem sorted_odd_lower_bound (s : Finset ℕ)
    (h : ∀ n ∈ s, 1 < n ∧ Odd n) (i : Fin s.card) :
    2 * (i : ℕ) + 3 ≤ s.orderEmbOfFin rfl i := by
  have H (k : ℕ) : ∀ hk : k < s.card,
      2 * k + 3 ≤ s.orderEmbOfFin rfl ⟨k, hk⟩ := by
    induction k with
    | zero =>
      intro hk
      obtain ⟨hgt, hodd⟩ := h _ (s.orderEmbOfFin_mem rfl ⟨0, hk⟩)
      have := Nat.odd_iff.mp hodd
      omega
    | succ k ih =>
      intro hk
      have hk' : k < s.card := by omega
      have hp := ih hk'
      have ht : s.orderEmbOfFin rfl ⟨k, hk'⟩ < s.orderEmbOfFin rfl ⟨k+1, hk⟩ :=
        (s.orderEmbOfFin rfl).strictMono (by simp)
      have ho₁ := Nat.odd_iff.mp (h _ (s.orderEmbOfFin_mem rfl ⟨k, hk'⟩)).2
      have ho₂ := Nat.odd_iff.mp (h _ (s.orderEmbOfFin_mem rfl ⟨k+1, hk⟩)).2
      omega
  exact H i.val i.isLt

private theorem odd_reciprocal_sum_lt_one (s : Finset ℕ) (hc : s.card ≤ 6)
    (h : ∀ n ∈ s, 1 < n ∧ Odd n) :
    ∑ n ∈ s, (n : ℚ)⁻¹ < 1 := by
  have heq : ∑ n ∈ s, (n : ℚ)⁻¹ =
      ∑ i : Fin s.card, (s.orderEmbOfFin rfl i : ℚ)⁻¹ := by
    conv_lhs => rw [← s.map_orderEmbOfFin_univ rfl]
    exact Finset.sum_map _ _ _
  rw [heq]
  calc
    _ ≤ ∑ i : Fin s.card, ((2 * (i : ℕ) + 3 : ℕ) : ℚ)⁻¹ := by
      apply Finset.sum_le_sum
      intro i _
      have hi := sorted_odd_lower_bound s h i
      have hiq : (((2 * (i : ℕ) + 3 : ℕ) : ℚ)) ≤ (s.orderEmbOfFin rfl i : ℚ) := by
        exact_mod_cast hi
      simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hiq
    _ = ∑ i ∈ Finset.range s.card, ((2 * i + 3 : ℕ) : ℚ)⁻¹ :=
      Fin.sum_univ_eq_sum_range (fun i : ℕ => ((2 * i + 3 : ℕ) : ℚ)⁻¹) s.card
    _ ≤ ∑ i ∈ Finset.range 6, ((2 * i + 3 : ℕ) : ℚ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hc)
      intro i _ _
      positivity
    _ < 1 := by norm_num [Finset.sum_range_succ]

theorem at_least_seven_moduli (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i, ¬ C.moduli i ≤ Ideal.span {2}) :
    letI := C.fintypeIndex
    7 ≤ Fintype.card C.ι := by
  classical
  letI := C.fintypeIndex
  by_contra hc
  have hc' : Fintype.card C.ι ≤ 6 := by omega
  let s := Finset.univ.image (fun i => (C.moduli i).absNorm)
  have hi := moduli_absNorm_injective C
  have hs : s.card ≤ 6 := by
    simpa only [s, Finset.card_image_of_injective _ hi, Finset.card_univ] using hc'
  have hprop : ∀ n ∈ s, 1 < n ∧ Odd n := by
    intro n hn
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
    exact ⟨moduli_absNorm_gt_one C i, (ideal_not_le_two_iff _).mp (hodd i)⟩
  have hsum := odd_reciprocal_sum_lt_one s hs hprop
  have heq : ∑ n ∈ s, (n : ℚ)⁻¹ = ∑ i, ((C.moduli i).absNorm : ℚ)⁻¹ :=
    Finset.sum_image (fun i _ j _ hh => hi hh)
  rw [heq] at hsum
  exact (not_lt_of_ge (density_necessary C)) hsum

#print axioms at_least_seven_moduli
end Erdos7Reduction

namespace Erdos7Reduction
open Set Pointwise

theorem integer_coset_mem_iff (a x : ℤ) (I : Ideal ℤ) :
    x ∈ ({a} : Set ℤ) + (I : Set ℤ) ↔ x - a ∈ I := by
  rw [integer_coset_iff, ← Ideal.mem_span_singleton, Int.ideal_span_absNorm_eq_self]

theorem coset_subset_of_le_of_inter (a b x : ℤ) (I J : Ideal ℤ)
    (hIJ : I ≤ J)
    (hxI : x ∈ ({a} : Set ℤ) + (I : Set ℤ))
    (hxJ : x ∈ ({b} : Set ℤ) + (J : Set ℤ)) :
    ({a} : Set ℤ) + (I : Set ℤ) ⊆ ({b} : Set ℤ) + (J : Set ℤ) := by
  rw [integer_coset_mem_iff] at hxI hxJ
  have hab : a - b ∈ J := by
    convert J.sub_mem hxJ (hIJ hxI) using 1 <;> ring
  intro y hy
  rw [integer_coset_mem_iff] at hy ⊢
  convert J.add_mem (hIJ hy) hab using 1 <;> ring

theorem exists_irredundant_subcover (C : StrictCoveringSystem ℤ) :
    ∃ s : Finset C.ι,
      (∀ x : ℤ, ∃ i ∈ s, x ∈ C.toCoveringSystem.coset i) ∧
      (∀ i ∈ s, ∃ x : ℤ, x ∈ C.toCoveringSystem.coset i ∧
        ∀ j ∈ s, j ≠ i → x ∉ C.toCoveringSystem.coset j) := by
  classical
  letI := C.fintypeIndex
  let P : Finset C.ι → Prop := fun s =>
    ∀ x : ℤ, ∃ i ∈ s, x ∈ C.toCoveringSystem.coset i
  have hP : P Finset.univ := by
    intro x
    have hx : x ∈ ⋃ i, C.toCoveringSystem.coset i := by simp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, Finset.mem_univ i, hi⟩
  obtain ⟨s, hs⟩ := exists_minimal_of_wellFoundedLT P ⟨Finset.univ, hP⟩
  refine ⟨s, hs.prop, ?_⟩
  intro i hi
  have hnot : ¬ P (s.erase i) := by
    intro he
    have hle := hs.le_of_le he (Finset.erase_subset i s)
    have : i ∈ s.erase i := hle hi
    exact Finset.notMem_erase i s this
  change ¬ (∀ x : ℤ, ∃ j ∈ s.erase i, x ∈ C.toCoveringSystem.coset j) at hnot
  push_neg at hnot
  obtain ⟨x, hx⟩ := hnot
  obtain ⟨j, hj, hxj⟩ := hs.prop x
  have hji : j = i := by
    by_contra hji
    exact hx j (Finset.mem_erase.mpr ⟨hji, hj⟩) hxj
  subst j
  refine ⟨x, hxj, ?_⟩
  intro j hj hji
  exact hx j (Finset.mem_erase.mpr ⟨hji, hj⟩)

theorem disjoint_of_irredundant_of_moduli_le (C : StrictCoveringSystem ℤ)
    (s : Finset C.ι)
    (hpriv : ∀ i ∈ s, ∃ x : ℤ, x ∈ C.toCoveringSystem.coset i ∧
      ∀ j ∈ s, j ≠ i → x ∉ C.toCoveringSystem.coset j)
    {i j : C.ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (hle : C.moduli i ≤ C.moduli j) :
    Disjoint (C.toCoveringSystem.coset i) (C.toCoveringSystem.coset j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hsub := coset_subset_of_le_of_inter _ _ x _ _ hle hxi hxj
  obtain ⟨y, hy, hprivate⟩ := hpriv i hi
  exact hprivate j hj hij.symm (hsub hy)

#print axioms exists_irredundant_subcover
#print axioms disjoint_of_irredundant_of_moduli_le
end Erdos7Reduction

namespace Erdos7Reduction

theorem finite_period_cover_iff {ι : Type} (m : ι → ℕ) (a : ι → ℤ)
    (N : ℕ) (hN : 0 < N) (hdiv : ∀ i, m i ∣ N) :
    (∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i) ↔
    (∀ x : Fin N, ∃ i, (m i : ℤ) ∣ (x : ℤ) - a i) := by
  constructor
  · intro h x
    exact h x
  · intro h x
    have hNz : (0 : ℤ) < N := by exact_mod_cast hN
    have hr0 : 0 ≤ x % (N : ℤ) := Int.emod_nonneg _ (ne_of_gt hNz)
    have hrN : x % (N : ℤ) < N := Int.emod_lt_of_pos _ hNz
    let r : Fin N := ⟨(x % (N : ℤ)).toNat, by omega⟩
    have hr : (r : ℤ) = x % (N : ℤ) := by
      exact Int.toNat_of_nonneg hr0
    obtain ⟨i, hi⟩ := h r
    rw [hr] at hi
    have hstep : (N : ℤ) ∣ x - x % (N : ℤ) := by
      refine ⟨x / (N : ℤ), ?_⟩
      have := Int.emod_add_ediv x (N : ℤ)
      omega
    have hdiv' : (m i : ℤ) ∣ (N : ℤ) := by exact_mod_cast hdiv i
    refine ⟨i, ?_⟩
    have := dvd_add (hdiv'.trans hstep) hi
    convert this using 1 <;> ring

#print axioms finite_period_cover_iff
end Erdos7Reduction

namespace Erdos7Reduction

private theorem half_geometric_sum_lt_one (s : Finset ℕ) (h0 : 0 ∉ s) :
    ∑ n ∈ s, (1 / 2 : ℚ) ^ n < 1 := by
  let N := s.sup id + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hsub : s ⊆ (Finset.range N).erase 0 := by
    intro n hn
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro hh
      subst n
      exact h0 hn
    · have hle : n ≤ s.sup id := Finset.le_sup (f := id) hn
      exact Finset.mem_range.mpr (by dsimp [N]; omega)
  have hle : ∑ n ∈ s, (1 / 2 : ℚ)^n ≤
      ∑ n ∈ (Finset.range N).erase 0, (1 / 2 : ℚ)^n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
  have he := Finset.sum_erase_add (Finset.range N) (fun n => (1 / 2 : ℚ)^n)
    (Finset.mem_range.mpr hN)
  have hg := geom_sum_mul (1 / 2 : ℚ) N
  have hp : 0 < (1 / 2 : ℚ)^N := pow_pos (by norm_num) N
  norm_num only [pow_zero, one_div] at he hg hp hle ⊢
  norm_num at hg
  linarith

theorem not_all_moduli_powers (C : StrictCoveringSystem ℤ) (p : ℕ) (hp : 2 ≤ p) :
    ¬ (∀ i, ∃ a : ℕ, (C.moduli i).absNorm = p ^ a) := by
  classical
  letI := C.fintypeIndex
  intro h
  choose a ha using h
  have hai : Function.Injective a := by
    intro i j hij
    apply moduli_absNorm_injective C
    dsimp only
    rw [ha i, ha j, hij]
  have ha0 : ∀ i, a i ≠ 0 := by
    intro i hi
    have hg := moduli_absNorm_gt_one C i
    rw [ha i, hi, pow_zero] at hg
    omega
  let s := Finset.univ.image a
  have hs0 : 0 ∉ s := by
    intro hh
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hh
    exact ha0 i hi
  have hsmall := half_geometric_sum_lt_one s hs0
  have heq : ∑ n ∈ s, (1 / 2 : ℚ)^n = ∑ i, (1 / 2 : ℚ)^(a i) :=
    Finset.sum_image (fun i _ j _ hh => hai hh)
  rw [heq] at hsmall
  have hrecip : (p : ℚ)⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 2) (by exact_mod_cast hp)
  have hupper : ∑ i, ((C.moduli i).absNorm : ℚ)⁻¹ ≤
      ∑ i, (1 / 2 : ℚ)^(a i) := by
    apply Finset.sum_le_sum
    intro i _
    rw [ha i, Nat.cast_pow, ← inv_pow]
    exact pow_le_pow_left₀ (by positivity) hrecip (a i)
  have hlarge := density_necessary C
  linarith

#print axioms not_all_moduli_powers
end Erdos7Reduction

namespace Erdos7Reduction

private theorem geometric_sum_le (r : ℚ) (h0 : 0 ≤ r) (h1 : r < 1) (N : ℕ) :
    ∑ a ∈ Finset.range N, r^a ≤ 1 / (1 - r) := by
  rw [le_div_iff₀ (sub_pos.mpr h1)]
  have hg := geom_sum_mul r N
  have hp := pow_nonneg h0 N
  nlinarith

private theorem two_geometric_sum_lt_one (s : Finset (ℕ × ℕ)) (h0 : (0,0) ∉ s) :
    ∑ ab ∈ s, (1/3 : ℚ)^ab.1 * (1/5 : ℚ)^ab.2 < 1 := by
  classical
  let A := s.sup Prod.fst + 1
  let B := s.sup Prod.snd + 1
  have hA : 0 < A := by dsimp [A]; omega
  have hB : 0 < B := by dsimp [B]; omega
  have hsub : insert (0,0) s ⊆ (Finset.range A) ×ˢ (Finset.range B) := by
    intro ab hab
    rcases Finset.mem_insert.mp hab with h | h
    · subst ab
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hA, Finset.mem_range.mpr hB⟩
    · have ha : ab.1 ≤ s.sup Prod.fst := Finset.le_sup (f := Prod.fst) h
      have hb : ab.2 ≤ s.sup Prod.snd := Finset.le_sup (f := Prod.snd) h
      exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by dsimp [A]; omega),
          Finset.mem_range.mpr (by dsimp [B]; omega)⟩
  have hle : ∑ ab ∈ insert (0,0) s, (1/3 : ℚ)^ab.1 * (1/5 : ℚ)^ab.2 ≤
      ∑ ab ∈ (Finset.range A) ×ˢ (Finset.range B),
        (1/3 : ℚ)^ab.1 * (1/5 : ℚ)^ab.2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
  have heq : (∑ ab ∈ (Finset.range A) ×ˢ (Finset.range B),
        (1/3 : ℚ)^ab.1 * (1/5 : ℚ)^ab.2) =
      (∑ a ∈ Finset.range A, (1/3 : ℚ)^a) *
        (∑ b ∈ Finset.range B, (1/5 : ℚ)^b) := by
    rw [Finset.sum_product]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [heq, Finset.sum_insert h0] at hle
  norm_num only [pow_zero, mul_one] at hle
  have ha := geometric_sum_le (1/3 : ℚ) (by norm_num) (by norm_num) A
  have hb := geometric_sum_le (1/5 : ℚ) (by norm_num) (by norm_num) B
  have ha0 : 0 ≤ ∑ a ∈ Finset.range A, (1/3 : ℚ)^a := Finset.sum_nonneg (by intros; positivity)
  have hb0 : 0 ≤ ∑ b ∈ Finset.range B, (1/5 : ℚ)^b := Finset.sum_nonneg (by intros; positivity)
  norm_num at ha hb
  nlinarith

theorem not_all_moduli_two_powers (C : StrictCoveringSystem ℤ)
    (p q : ℕ) (hp : 3 ≤ p) (hq : 5 ≤ q) :
    ¬ (∀ i, ∃ a b : ℕ, (C.moduli i).absNorm = p ^ a * q ^ b) := by
  classical
  letI := C.fintypeIndex
  intro h
  choose a b hab using h
  let f : C.ι → ℕ × ℕ := fun i => (a i, b i)
  have hfi : Function.Injective f := by
    intro i j hij
    have ha : a i = a j := congrArg Prod.fst hij
    have hb : b i = b j := congrArg Prod.snd hij
    apply moduli_absNorm_injective C
    dsimp only
    rw [hab i, hab j, ha, hb]
  let s := Finset.univ.image f
  have hs0 : (0,0) ∉ s := by
    intro hh
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hh
    have ha : a i = 0 := congrArg Prod.fst hi
    have hb : b i = 0 := congrArg Prod.snd hi
    have hg := moduli_absNorm_gt_one C i
    rw [hab i, ha, hb] at hg
    norm_num at hg
  have hsmall := two_geometric_sum_lt_one s hs0
  have heq : (∑ ab ∈ s, (1/3 : ℚ)^ab.1 * (1/5 : ℚ)^ab.2) =
      ∑ i, (1/3 : ℚ)^(a i) * (1/5 : ℚ)^(b i) :=
    Finset.sum_image (fun i _ j _ hh => hfi hh)
  rw [heq] at hsmall
  have hrecip_p : (p : ℚ)⁻¹ ≤ 1/3 := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 3) (by exact_mod_cast hp)
  have hrecip_q : (q : ℚ)⁻¹ ≤ 1/5 := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 5) (by exact_mod_cast hq)
  have hupper : ∑ i, ((C.moduli i).absNorm : ℚ)⁻¹ ≤
      ∑ i, (1/3 : ℚ)^(a i) * (1/5 : ℚ)^(b i) := by
    apply Finset.sum_le_sum
    intro i _
    rw [hab i, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, mul_inv, ← inv_pow, ← inv_pow]
    exact mul_le_mul
      (pow_le_pow_left₀ (by positivity) hrecip_p (a i))
      (pow_le_pow_left₀ (by positivity) hrecip_q (b i)) (by positivity) (by positivity)
  have hlarge := density_necessary C
  linarith

#print axioms not_all_moduli_two_powers
end Erdos7Reduction


/-! Necessary multiplicity of maximal prime-exponents in an irredundant cover. -/

namespace Erdos7Reduction

private theorem dvd_step_of_two_dvd {m D : ℤ} {p t : ℕ}
    (hp : p.Prime) (ht0 : 0 < t) (htp : t < p)
    (hm : m ∣ (p : ℤ) * D) (ht : m ∣ (t : ℤ) * D) : m ∣ D := by
  obtain ⟨u, v, huv⟩ := (Nat.coprime_of_lt_prime (by omega) htp hp).isCoprime
  have h := dvd_add (dvd_mul_of_dvd_right hm u) (dvd_mul_of_dvd_right ht v)
  convert h using 1
  calc
    D = (u * (p : ℤ) + v * (t : ℤ)) * D := by rw [huv, one_mul]
    _ = u * ((p : ℤ) * D) + v * ((t : ℤ) * D) := by ring

private theorem prime_step_unique {m D a x : ℤ} {p : ℕ} (hp : p.Prime)
    (hm : m ∣ (p : ℤ) * D) (hD : ¬ m ∣ D) (k l : Fin p)
    (hk : m ∣ x + (k : ℤ) * D - a) (hl : m ∣ x + (l : ℤ) * D - a) :
    k = l := by
  have helper : ∀ k l : Fin p, k.val < l.val →
      m ∣ x + (k : ℤ) * D - a → m ∣ x + (l : ℤ) * D - a → False := by
    intro k l hkl hk hl
    have hdiff : m ∣ ((l.val - k.val : ℕ) : ℤ) * D := by
      have h := dvd_sub hl hk
      rw [Nat.cast_sub (by omega : k.val ≤ l.val)]
      convert h using 1 <;> ring
    exact hD (dvd_step_of_two_dvd hp (by omega) (by omega) hm hdiff)
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact helper k l h hk hl
  · exact helper l k h hl hk

/-- If an arithmetic cover has a private point belonging to a modulus not dividing `D`,
while all its moduli divide `pD`, at least `p` moduli fail to divide `D`. -/
theorem prime_step_multiplicity {ι : Type} [Fintype ι]
    (m : ι → ℕ) (a : ι → ℤ) (p D : ℕ) (hp : p.Prime)
    (hdiv : ∀ i, m i ∣ p * D)
    (hcover : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i)
    (i₀ : ι) (hi₀ : ¬ m i₀ ∣ D)
    (x : ℤ) (hprivate : ∀ j, j ≠ i₀ → ¬ (m j : ℤ) ∣ x - a j) :
    p ≤ Fintype.card {i : ι // ¬ m i ∣ D} := by
  classical
  have hmem (k : Fin p) :
      ∃ i : {i : ι // ¬ m i ∣ D}, (m i.val : ℤ) ∣ x + (k : ℤ) * D - a i.val := by
    obtain ⟨i, hi⟩ := hcover (x + (k : ℤ) * D)
    have hni : ¬ m i ∣ D := by
      intro h
      have hh : (m i : ℤ) ∣ (D : ℤ) := by exact_mod_cast h
      have hbase : (m i : ℤ) ∣ x - a i := by
        have hs := dvd_sub hi (dvd_mul_of_dvd_right hh (k : ℤ))
        convert hs using 1 <;> ring
      by_cases hii : i = i₀
      · subst i
        exact hi₀ h
      · exact hprivate i hii hbase
    exact ⟨⟨i, hni⟩, hi⟩
  choose f hf using hmem
  have hinj : Function.Injective f := by
    intro k l hkl
    have hk := hf k
    have hl := hf l
    rw [hkl] at hk
    apply prime_step_unique hp (m := (m (f l).val : ℤ))
      (D := (D : ℤ)) (a := a (f l).val) (x := x) ?_ ?_ k l hk hl
    · exact_mod_cast hdiv (f l).val
    · exact_mod_cast (f l).property
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hinj


/-- Dropping a prime from a common multiple detects exactly the moduli having
maximal exponent at that prime. -/
theorem not_dvd_div_prime_iff {m N p : ℕ} (hm : m ≠ 0) (hN : N ≠ 0)
    (hp : p.Prime) (hpN : p ∣ N) (hmN : m ∣ N) :
    (¬ m ∣ N / p) ↔ m.factorization p = N.factorization p := by
  have hle := (Nat.factorization_le_iff_dvd hm hN).mpr hmN
  rw [Nat.dvd_div_iff_mul_dvd hpN,
    ← Nat.factorization_le_iff_dvd (mul_ne_zero hp.ne_zero hm) hN,
    Nat.factorization_mul hp.ne_zero hm, hp.factorization]
  constructor
  · intro hnot
    by_contra hne
    apply hnot
    intro q
    by_cases hqp : q = p
    · subst q
      have hmp := hle p
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
      omega
    · simpa [Finsupp.single_apply, hqp, Ne.symm hqp] using hle q
  · intro heq h
    have hh := h p
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at hh
    omega

/-- Every prime in the common period of an irredundant arithmetic cover attains
its maximal exponent in at least that many moduli. Distinctness is not needed. -/
theorem maximal_prime_exponent_multiplicity {ι : Type} [Fintype ι]
    (m : ι → ℕ) (a : ι → ℤ) (hm : ∀ i, m i ≠ 0)
    (hcover : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i)
    (hprivate : ∀ i, ∃ x : ℤ, ∀ j, j ≠ i → ¬ (m j : ℤ) ∣ x - a j)
    (p : ℕ) (hp : p.Prime) (hpN : p ∣ Finset.univ.lcm m) :
    p ≤ Fintype.card {i : ι //
      (m i).factorization p = (Finset.univ.lcm m).factorization p} := by
  classical
  let N := Finset.univ.lcm m
  have hN : N ≠ 0 := Finset.lcm_ne_zero_iff.mpr (by simpa using hm)
  have hmN (i : ι) : m i ∣ N := Finset.dvd_lcm (Finset.mem_univ i)
  have hex : ∃ i, ¬ m i ∣ N / p := by
    by_contra hh
    push_neg at hh
    have hNd : N ∣ N / p := Finset.lcm_dvd (by simpa using hh)
    have heq : N = N / p := Nat.dvd_antisymm hNd (Nat.div_dvd_of_dvd hpN)
    have hlt := Nat.div_lt_self (Nat.pos_of_ne_zero hN) hp.one_lt
    omega
  obtain ⟨i, hi⟩ := hex
  obtain ⟨x, hx⟩ := hprivate i
  have hbound := prime_step_multiplicity m a p (N / p) hp
    (fun j => by rw [Nat.mul_div_cancel' hpN]; exact hmN j) hcover i hi x hx
  let e : {i : ι // ¬ m i ∣ N / p} ≃
      {i : ι // (m i).factorization p = N.factorization p} :=
    Equiv.subtypeEquivRight (fun i => not_dvd_div_prime_iff (hm i) hN hp hpN (hmN i))
  rwa [Fintype.card_congr e] at hbound

#print axioms maximal_prime_exponent_multiplicity

/-- An essential congruence cannot have a period component absent from all other
congruences in the cover. -/
theorem private_modulus_dvd_common_period {ι : Type}
    (m : ι → ℕ) (a : ι → ℤ)
    (hcover : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i)
    (i₀ : ι) (D : ℕ) (hD : ∀ j, j ≠ i₀ → m j ∣ D)
    (x : ℤ) (hprivate : ∀ j, j ≠ i₀ → ¬ (m j : ℤ) ∣ x - a j) :
    m i₀ ∣ D := by
  have hx : (m i₀ : ℤ) ∣ x - a i₀ := by
    obtain ⟨j, hj⟩ := hcover x
    by_cases heq : j = i₀
    · simpa [heq] using hj
    · exact False.elim (hprivate j heq hj)
  obtain ⟨j, hj⟩ := hcover (x + D)
  have heq : j = i₀ := by
    by_contra hne
    have hDj : (m j : ℤ) ∣ (D : ℤ) := by exact_mod_cast hD j hne
    apply hprivate j hne
    convert dvd_sub hj hDj using 1 <;> ring
  subst j
  have hDz : (m i₀ : ℤ) ∣ (D : ℤ) := by
    convert dvd_sub hj hx using 1 <;> ring
  exact_mod_cast hDz

#print axioms private_modulus_dvd_common_period


#print axioms prime_step_multiplicity
end Erdos7Reduction


/- A character-weighted necessary density inequality for arithmetic covers. -/

namespace Erdos7Reduction
open Finset

private theorem twisted_sum_eq_zero {G : Type*} [AddCommGroup G] [Fintype G]
    (χ : AddChar G ℂ) (P : G → Prop) [DecidablePred P] (a h : G)
    (hP : ∀ x, P (x + h) ↔ P x) (hχ : χ h ≠ 1) :
    (∑ x, if P x then χ (x - a) else 0) = 0 := by
  let S : ℂ := ∑ x, if P x then χ (x - a) else 0
  have hsum : (∑ x, if P (x + h) then χ (x + h - a) else 0) = S :=
    Fintype.sum_bijective _ (AddGroup.addRight_bijective h) _ _ (fun _ => rfl)
  have hterm (x : G) :
      (if P (x + h) then χ (x + h - a) else 0) =
        χ h * (if P x then χ (x - a) else 0) := by
    simp only [hP x]
    have heq : x + h - a = h + (x - a) := by abel
    rw [heq, χ.map_add_eq_mul]
    split_ifs <;> simp
  simp_rw [hterm] at hsum
  rw [← Finset.mul_sum] at hsum
  exact eq_zero_of_mul_eq_self_left hχ hsum

private theorem fiber_sum_one {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] [DecidableEq H] (f : G →+ H)
    (hf : Function.Surjective f) (b : H) :
    (∑ x : G, if f x = b then (1 : ℝ) else 0) =
      (Fintype.card G : ℝ) / Fintype.card H := by
  classical
  have heq (y : H) : (Finset.univ.filter (fun x => f x = y)).card =
      (Finset.univ.filter (fun x => f x = b)).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf b)
  have hcard : Fintype.card G =
      Fintype.card H * (Finset.univ.filter (fun x => f x = b)).card := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset G))
      (t := (Finset.univ : Finset H)) (f := f) (fun _ _ => Finset.mem_univ _)
    simpa only [heq, Finset.card_univ, Finset.sum_const, nsmul_eq_mul] using h
  have hc : (Fintype.card H : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card H))
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  apply (eq_div_iff hc).mpr
  exact_mod_cast (Nat.mul_comm _ _).trans hcard.symm

/-- A nonnegative character weight lets us omit one class from the density bound,
provided its character vanishes in average on every other class. -/
private theorem weighted_cover_bound {G ι : Type*} [AddCommGroup G]
    [Fintype G] [Fintype ι] [DecidableEq ι]
    (P : ι → G → Prop) [∀ i, DecidablePred (P i)]
    (hcover : ∀ x, ∃ i, P i x) (i₀ : ι) (w : G → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hzero : ∀ x, P i₀ x → w x = 0) :
    ∑ x, w x ≤ ∑ i ∈ Finset.univ.erase i₀, ∑ x, if P i x then w x else 0 := by
  have hpoint (x : G) : w x ≤ ∑ i ∈ Finset.univ.erase i₀,
      if P i x then w x else 0 := by
    obtain ⟨i, hi⟩ := hcover x
    by_cases heq : i = i₀
    · subst i
      rw [hzero x hi]
      exact Finset.sum_nonneg (by intro i _; split_ifs <;> positivity)
    · calc
        w x = if P i x then w x else 0 := by simp [hi]
        _ ≤ ∑ j ∈ Finset.univ.erase i₀, if P j x then w x else 0 :=
          Finset.single_le_sum (f := fun j => if P j x then w x else 0)
            (by intro j _; dsimp only; split_ifs; exact hw x; exact le_rfl) (by simp [heq])
  calc
    _ ≤ ∑ x, ∑ i ∈ Finset.univ.erase i₀, if P i x then w x else 0 :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    _ = _ := Finset.sum_comm


/-- In a finite arithmetic cover, a modulus dividing no other modulus can be
omitted from the usual reciprocal-density lower bound. -/
theorem density_omit_divisibility_maximal {ι : Type} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (a : ι → ℤ) (hm : ∀ i, 0 < m i)
    (hcover : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i)
    (i₀ : ι) (hi₀ : 1 < m i₀) (hmax : ∀ i, i ≠ i₀ → ¬ m i₀ ∣ m i)
    (N : ℕ) (hN : 0 < N) (hdiv : ∀ i, m i ∣ N) :
    1 ≤ ∑ i ∈ Finset.univ.erase i₀, ((m i : ℝ)⁻¹) := by
  classical
  letI : NeZero N := ⟨by omega⟩
  letI (i : ι) : NeZero (m i) := ⟨by have := hm i; omega⟩
  let f (i : ι) := ZMod.castHom (hdiv i) (ZMod (m i))
  let χ : AddChar (ZMod N) ℂ :=
    ZMod.stdAddChar.compAddMonoidHom (f i₀).toAddMonoidHom
  have hχnat (n : ℕ) : χ (n : ZMod N) = 1 ↔ m i₀ ∣ n := by
    change ZMod.stdAddChar ((f i₀) (n : ZMod N)) = 1 ↔ _
    rw [map_natCast, ← (ZMod.stdAddChar (N := m i₀)).map_zero_eq_one,
      ZMod.injective_stdAddChar.eq_iff]
    exact CharP.cast_eq_zero_iff (ZMod (m i₀)) (m i₀) n
  have hχone : χ 1 ≠ 1 := by
    simpa only [Nat.cast_one] using
      (hχnat 1).not.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hi₀)
  let P (i : ι) (x : ZMod N) : Prop := f i x = (a i : ZMod (m i))
  have hPcover (x : ZMod N) : ∃ i, P i x := by
    obtain ⟨i, hi⟩ := hcover (x.val : ℤ)
    refine ⟨i, ?_⟩
    dsimp [P]
    rw [← ZMod.natCast_zmod_val x, map_natCast]
    symm
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (a i) (x.val : ℤ) (m i)).mpr hi
  let a₀ : ZMod N := (a i₀ : ZMod N)
  let w (x : ZMod N) : ℝ := 1 - (χ (x - a₀)).re
  have hw (x : ZMod N) : 0 ≤ w x := by
    dsimp [w]
    have h := Complex.re_le_norm (χ (x - a₀))
    rw [χ.norm_apply] at h
    linarith
  have hzero (x : ZMod N) (hx : P i₀ x) : w x = 0 := by
    have hval : χ (x - a₀) = 1 := by
      change ZMod.stdAddChar (f i₀ (x - a₀)) = 1
      rw [map_sub]
      change ZMod.stdAddChar (f i₀ x - f i₀ (a i₀ : ZMod N)) = 1
      rw [map_intCast, hx, sub_self, AddChar.map_zero_eq_one]
    simp [w, hval]
  have hsumχ : ∑ x : ZMod N, χ (x - a₀) = 0 := by
    simpa using twisted_sum_eq_zero χ (fun _ => True) a₀ 1 (by simp) hχone
  have hsumw : ∑ x : ZMod N, w x = (N : ℝ) := by
    simp only [w, Finset.sum_sub_distrib, ← Complex.re_sum, hsumχ,
      Complex.zero_re, sub_zero, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, mul_one]
  have hsum_other (i : ι) (hi : i ≠ i₀) :
      (∑ x : ZMod N, if P i x then w x else 0) = (N : ℝ) / m i := by
    have hPstep (x : ZMod N) : P i (x + (m i : ZMod N)) ↔ P i x := by
      dsimp [P]
      rw [map_add, map_natCast, ZMod.natCast_self, add_zero]
    have hχstep : χ (m i : ZMod N) ≠ 1 := by
      exact (hχnat (m i)).not.mpr (hmax i hi)
    have hz := twisted_sum_eq_zero χ (P i) a₀ (m i : ZMod N) hPstep hχstep
    have ht (x : ZMod N) : (if P i x then w x else 0) =
        (if P i x then (1 : ℝ) else 0) -
          (if P i x then χ (x - a₀) else 0).re := by
      dsimp [w]
      split_ifs <;> simp
    simp_rw [ht]
    rw [Finset.sum_sub_distrib, ← Complex.re_sum, hz, Complex.zero_re, sub_zero]
    simpa only [ZMod.card] using
      fiber_sum_one (f i).toAddMonoidHom (ZMod.castHom_surjective (hdiv i)) (a i)
  have hbound := weighted_cover_bound P hPcover i₀ w hw hzero
  rw [hsumw] at hbound
  have heq : (∑ i ∈ Finset.univ.erase i₀,
        ∑ x : ZMod N, if P i x then w x else 0) =
      (N : ℝ) * ∑ i ∈ Finset.univ.erase i₀, ((m i : ℝ)⁻¹) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hsum_other i (Finset.mem_erase.mp hi).1, div_eq_mul_inv]
  rw [heq] at hbound
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  nlinarith

#print axioms density_omit_divisibility_maximal

end Erdos7Reduction

namespace Erdos7Reduction

/-- The largest-modulus density bound improves the elementary bound by one. -/
theorem at_least_eight_moduli (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i, ¬ C.moduli i ≤ Ideal.span {2}) :
    letI := C.fintypeIndex
    8 ≤ Fintype.card C.ι := by
  classical
  letI := C.fintypeIndex
  obtain ⟨j, _⟩ := arithmetic_cover C 0
  letI : Nonempty C.ι := ⟨j⟩
  let m (i : C.ι) := (C.moduli i).absNorm
  obtain ⟨i₀, hmax⟩ := Finite.exists_max m
  have hm (i : C.ι) : 1 < m i := moduli_absNorm_gt_one C i
  have hmi : Function.Injective m := moduli_absNorm_injective C
  have hdivmax (i : C.ι) (hi : i ≠ i₀) : ¬ m i₀ ∣ m i := by
    intro hd
    have hle := Nat.le_of_dvd (by have := hm i; omega) hd
    exact hi (hmi (Nat.le_antisymm (hmax i) hle))
  have hbound := density_omit_divisibility_maximal m C.residue
    (fun i => by have := hm i; omega) (arithmetic_cover C) i₀ (hm i₀) hdivmax
    (∏ i, m i) (Finset.prod_pos (by intro i _; have := hm i; omega))
    (fun i => Finset.dvd_prod_of_mem m (Finset.mem_univ i))
  have hboundQ : (1 : ℚ) ≤ ∑ i ∈ Finset.univ.erase i₀, (m i : ℚ)⁻¹ := by
    apply (Rat.cast_le (K := ℝ)).mp
    simpa using hbound
  by_contra hc
  have hc' : Fintype.card C.ι ≤ 7 := by omega
  let s := (Finset.univ.erase i₀).image m
  have hs : s.card ≤ 6 := by
    simp only [s, Finset.card_image_of_injective _ hmi,
      Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ]
    omega
  have hprop : ∀ n ∈ s, 1 < n ∧ Odd n := by
    intro n hn
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
    exact ⟨hm i, (ideal_not_le_two_iff _).mp (hodd i)⟩
  have hsmall := odd_reciprocal_sum_lt_one s hs hprop
  have heq : (∑ n ∈ s, (n : ℚ)⁻¹) =
      ∑ i ∈ Finset.univ.erase i₀, (m i : ℚ)⁻¹ :=
    Finset.sum_image (fun i _ j _ hij => hmi hij)
  rw [heq] at hsmall
  linarith

#print axioms at_least_eight_moduli
end Erdos7Reduction



/- Pairwise nonresonance for the two largest odd moduli. -/

namespace Erdos7Reduction

private theorem stdAddChar_mul_int (m k : ℕ) [NeZero m] [NeZero k] (u v : ℤ) :
    ZMod.stdAddChar (u : ZMod m) * ZMod.stdAddChar (v : ZMod k) =
      ZMod.stdAddChar ((u * k + v * m : ℤ) : ZMod (m * k)) := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe,
    ← Complex.exp_add]
  congr 1
  push_cast
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hk : (k : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne k)
  field_simp

private theorem stdAddChar_int_eq_one_iff (m : ℕ) [NeZero m] (u : ℤ) :
    ZMod.stdAddChar (u : ZMod m) = 1 ↔ (m : ℤ) ∣ u := by
  rw [← (ZMod.stdAddChar (N := m)).map_zero_eq_one,
    ZMod.injective_stdAddChar.eq_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- An odd pair cannot resonate positively with a smaller modulus. -/
theorem odd_pair_add_nonresonance (m k n : ℕ) (hm : Odd m) (hk : Odd k)
    (hn : 0 < n) (hnm : n < m) (hnk : n < k) :
    ¬ m * k ∣ n * k + n * m := by
  intro hd
  have hk0 : 0 < k := by omega
  have hp : 0 < n * k + n * m := by positivity
  have hlt : n * k + n * m < 2 * (m * k) := by
    have h₁ := Nat.mul_lt_mul_of_pos_right hnm (by omega : 0 < k)
    have h₂ := Nat.mul_lt_mul_of_pos_right hnk (by omega : 0 < m)
    nlinarith
  have heq := Nat.eq_of_dvd_of_lt_two_mul (ne_of_gt hp) hd hlt
  have he : Even (m * k) := by
    rw [← heq, ← Nat.mul_add]
    exact (hk.add_odd hm).mul_left n
  exact (Nat.not_even_iff_odd.mpr (hm.mul hk)) he

/-- The difference of reciprocal characters of distinct moduli cannot resonate
with a smaller modulus. This part does not require oddness. -/
theorem pair_sub_nonresonance (m k n : ℕ) (hn : 0 < n)
    (hnk : n < k) (hkm : k < m) :
    ¬ (m * k : ℤ) ∣ (n : ℤ) * k - (n : ℤ) * m := by
  intro hd
  have hd' : m * k ∣ n * (m - k) := by
    apply Int.natCast_dvd_natCast.mp
    convert dvd_neg.mpr hd using 1
    push_cast [Nat.cast_sub hkm.le]
    ring
  have hpos : 0 < n * (m - k) := Nat.mul_pos hn (Nat.sub_pos_of_lt hkm)
  have hlt : n * (m - k) < m * k := by
    have h₁ := Nat.mul_lt_mul_of_pos_right hnk (Nat.sub_pos_of_lt hkm)
    have hsub : m - k + k = m := Nat.sub_add_cancel hkm.le
    nlinarith
  exact (not_lt_of_ge (Nat.le_of_dvd hpos hd')) hlt

/-- Both mixed character frequencies are nontrivial below the two largest odd moduli. -/
theorem odd_pair_character_nonresonance (m k n : ℕ) (hm : Odd m) (hk : Odd k)
    (hn : 0 < n) (hnk : n < k) (hkm : k < m) :
    letI : NeZero m := ⟨by omega⟩
    letI : NeZero k := ⟨by omega⟩
    ZMod.stdAddChar (n : ZMod m) * ZMod.stdAddChar (n : ZMod k) ≠ 1 ∧
      ZMod.stdAddChar (n : ZMod m) * ZMod.stdAddChar (-(n : ℤ) : ZMod k) ≠ 1 := by
  letI : NeZero m := ⟨by omega⟩
  letI : NeZero k := ⟨by omega⟩
  constructor
  · intro h
    have hz : (m * k : ℤ) ∣ (n : ℤ) * k + (n : ℤ) * m := by
      apply (stdAddChar_int_eq_one_iff (m * k) _).mp
      rw [← stdAddChar_mul_int]
      simpa only [Int.cast_natCast, Int.cast_neg] using h
    have hnat : m * k ∣ n * k + n * m := by exact_mod_cast hz
    exact odd_pair_add_nonresonance m k n hm hk hn (lt_trans hnk hkm) hnk hnat
  · intro h
    have hz : (m * k : ℤ) ∣ (n : ℤ) * k - (n : ℤ) * m := by
      apply (stdAddChar_int_eq_one_iff (m * k) _).mp
      rw [sub_eq_add_neg, ← neg_mul, ← stdAddChar_mul_int]
      simpa only [Int.cast_natCast, Int.cast_neg] using h
    exact pair_sub_nonresonance m k n hn hnk hkm hz

#print axioms odd_pair_character_nonresonance
end Erdos7Reduction

namespace Erdos7Reduction
open Finset

private theorem eigen_sum_eq_zero {G : Type*} [AddCommGroup G] [Fintype G]
    (P : G → Prop) [DecidablePred P] (h : G) (g : G → ℂ) (c : ℂ)
    (hP : ∀ x, P (x + h) ↔ P x) (hg : ∀ x, g (x + h) = c * g x)
    (hc : c ≠ 1) : (∑ x, if P x then g x else 0) = 0 := by
  have hsum : (∑ x, if P (x + h) then g (x + h) else 0) =
      ∑ x, if P x then g x else 0 :=
    Fintype.sum_bijective _ (AddGroup.addRight_bijective h) _ _ (fun _ => rfl)
  have ht (x : G) : (if P (x + h) then g (x + h) else 0) =
      c * (if P x then g x else 0) := by
    simp only [hP, hg]
    split_ifs <;> simp
  simp_rw [ht] at hsum
  rw [← Finset.mul_sum] at hsum
  exact eq_zero_of_mul_eq_self_left hc hsum

private theorem pair_weight_sum {G : Type*} [AddCommGroup G] [Fintype G]
    (χ ψ : AddChar G ℂ) (a b h : G) (P : G → Prop) [DecidablePred P]
    (hP : ∀ x, P (x + h) ↔ P x)
    (hχ : χ h ≠ 1) (hψ : ψ h ≠ 1)
    (hplus : χ h * ψ h ≠ 1) (hminus : χ h * ψ (-h) ≠ 1) :
    (∑ x, if P x then (1 - (χ (x - a)).re) * (1 - (ψ (x - b)).re) else 0) =
      ∑ x, if P x then (1 : ℝ) else 0 := by
  have hzχ := twisted_sum_eq_zero χ P a h hP hχ
  have hzψ := twisted_sum_eq_zero ψ P b h hP hψ
  have hshift (x c : G) : x + h - c = h + (x - c) := by abel
  have hzplus : (∑ x, if P x then χ (x - a) * ψ (x - b) else 0) = 0 := by
    apply eigen_sum_eq_zero P h _ (χ h * ψ h) hP _ hplus
    intro x
    dsimp only
    simp only [hshift, AddChar.map_add_eq_mul]
    ring
  have hm' : χ h * (starRingEnd ℂ) (ψ h) ≠ 1 := by
    simpa only [ψ.map_neg_eq_inv, Complex.inv_eq_conj (ψ.norm_apply h)] using hminus
  have hzminus : (∑ x, if P x then
      χ (x - a) * (starRingEnd ℂ) (ψ (x - b)) else 0) = 0 := by
    apply eigen_sum_eq_zero P h _ (χ h * (starRingEnd ℂ) (ψ h)) hP _ hm'
    intro x
    dsimp only
    simp only [hshift, AddChar.map_add_eq_mul, map_mul]
    ring
  have ht (x : G) :
      (if P x then (1 - (χ (x - a)).re) * (1 - (ψ (x - b)).re) else 0) =
        (if P x then (1 : ℝ) else 0) - (if P x then χ (x - a) else 0).re -
        (if P x then ψ (x - b) else 0).re +
        ((if P x then χ (x - a) * ψ (x - b) else 0).re +
          (if P x then χ (x - a) * (starRingEnd ℂ) (ψ (x - b)) else 0).re) / 2 := by
    split_ifs
    · simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    · simp
  simp_rw [ht]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
    ← Complex.re_sum, hzχ, hzψ, hzplus, hzminus, Complex.zero_re,
    sub_zero, add_zero, zero_div]

private theorem weighted_cover_omit {G ι : Type*} [Fintype G] [Fintype ι]
    [DecidableEq ι] (P : ι → G → Prop) [∀ i, DecidablePred (P i)]
    (hcover : ∀ x, ∃ i, P i x) (s : Finset ι) (w : G → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hzero : ∀ i ∈ s, ∀ x, P i x → w x = 0) :
    ∑ x, w x ≤ ∑ i ∈ Finset.univ \ s, ∑ x, if P i x then w x else 0 := by
  have hpoint (x : G) : w x ≤ ∑ i ∈ Finset.univ \ s, if P i x then w x else 0 := by
    obtain ⟨i, hi⟩ := hcover x
    by_cases his : i ∈ s
    · rw [hzero i his x hi]
      simp
    · calc
        w x = if P i x then w x else 0 := by simp [hi]
        _ ≤ ∑ j ∈ Finset.univ \ s, if P j x then w x else 0 :=
          Finset.single_le_sum (f := fun j => if P j x then w x else 0)
            (by intro j _; dsimp only; split_ifs; exact hw x; exact le_rfl) (by simp [his])
  calc
    _ ≤ ∑ x, ∑ i ∈ Finset.univ \ s, if P i x then w x else 0 :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    _ = _ := Finset.sum_comm

end Erdos7Reduction

namespace Erdos7Reduction
open Finset

/-- For a covering with distinct largest two moduli, both odd, the reciprocal
sum after omitting those two moduli is still at least one. -/
theorem density_omit_two_largest_odd {ι : Type} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (a : ι → ℤ) (hm : ∀ i, 0 < m i)
    (hcover : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i)
    (i₀ i₁ : ι) (hodd₀ : Odd (m i₀)) (hodd₁ : Odd (m i₁))
    (hi₁ : 1 < m i₁) (h10 : m i₁ < m i₀)
    (hmax : ∀ i, i ≠ i₀ → i ≠ i₁ → m i < m i₁)
    (N : ℕ) (hN : 0 < N) (hdiv : ∀ i, m i ∣ N) :
    1 ≤ ∑ i ∈ Finset.univ \ {i₀, i₁}, (m i : ℝ)⁻¹ := by
  classical
  letI : NeZero N := ⟨by omega⟩
  letI (i : ι) : NeZero (m i) := ⟨by have := hm i; omega⟩
  let f (i : ι) := ZMod.castHom (hdiv i) (ZMod (m i))
  let χ (i : ι) : AddChar (ZMod N) ℂ :=
    ZMod.stdAddChar.compAddMonoidHom (f i).toAddMonoidHom
  have hχnat (i : ι) (n : ℕ) : χ i (n : ZMod N) = 1 ↔ m i ∣ n := by
    change ZMod.stdAddChar ((f i) (n : ZMod N)) = 1 ↔ _
    rw [map_natCast, ← (ZMod.stdAddChar (N := m i)).map_zero_eq_one,
      ZMod.injective_stdAddChar.eq_iff]
    exact CharP.cast_eq_zero_iff (ZMod (m i)) (m i) n
  have hnr (n : ℕ) (hn : 0 < n) (hn₁ : n < m i₁) :
      χ i₀ (n : ZMod N) ≠ 1 ∧ χ i₁ (n : ZMod N) ≠ 1 ∧
      χ i₀ (n : ZMod N) * χ i₁ (n : ZMod N) ≠ 1 ∧
      χ i₀ (n : ZMod N) * χ i₁ (-(n : ZMod N)) ≠ 1 := by
    refine ⟨(hχnat i₀ n).not.mpr (Nat.not_dvd_of_pos_of_lt hn (lt_trans hn₁ h10)),
      (hχnat i₁ n).not.mpr (Nat.not_dvd_of_pos_of_lt hn hn₁), ?_⟩
    have hp := odd_pair_character_nonresonance (m i₀) (m i₁) n hodd₀ hodd₁ hn hn₁ h10
    change ZMod.stdAddChar (f i₀ (n : ZMod N)) *
        ZMod.stdAddChar (f i₁ (n : ZMod N)) ≠ 1 ∧
      ZMod.stdAddChar (f i₀ (n : ZMod N)) *
        ZMod.stdAddChar (f i₁ (-(n : ZMod N))) ≠ 1
    simpa only [map_natCast, map_neg, Int.cast_natCast] using hp
  let P (i : ι) (x : ZMod N) : Prop := f i x = (a i : ZMod (m i))
  have hPcover (x : ZMod N) : ∃ i, P i x := by
    obtain ⟨i, hi⟩ := hcover (x.val : ℤ)
    refine ⟨i, ?_⟩
    dsimp [P]
    rw [← ZMod.natCast_zmod_val x, map_natCast]
    symm
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (a i) (x.val : ℤ) (m i)).mpr hi
  let u (i : ι) (x : ZMod N) : ℝ := 1 - (χ i (x - a i)).re
  let w (x : ZMod N) : ℝ := u i₀ x * u i₁ x
  have hu (i : ι) (x : ZMod N) : 0 ≤ u i x := by
    dsimp [u]
    have h := Complex.re_le_norm (χ i (x - a i))
    rw [(χ i).norm_apply] at h
    linarith
  have hw (x : ZMod N) : 0 ≤ w x := mul_nonneg (hu i₀ x) (hu i₁ x)
  have huzero (i : ι) (x : ZMod N) (hx : P i x) : u i x = 0 := by
    have hval : χ i (x - a i) = 1 := by
      change ZMod.stdAddChar (f i (x - a i)) = 1
      rw [map_sub, map_intCast, hx, sub_self, AddChar.map_zero_eq_one]
    simp [u, hval]
  have hzero (i : ι) (hi : i ∈ ({i₀, i₁} : Finset ι)) (x : ZMod N)
      (hx : P i x) : w x = 0 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · simp [w, huzero i x hx]
    · simp [w, huzero i x hx]
  have hsumw : ∑ x : ZMod N, w x = (N : ℝ) := by
    obtain ⟨hc₀, hc₁, hp, hm⟩ := hnr 1 (by omega) hi₁
    have hh := pair_weight_sum (χ i₀) (χ i₁) (a i₀) (a i₁) (1 : ZMod N)
      (fun _ => True) (by simp) (by simpa using hc₀) (by simpa using hc₁)
      (by simpa using hp) (by simpa using hm)
    simpa only [w, u, if_true, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, mul_one] using hh
  have hsum_other (i : ι) (hi₀ : i ≠ i₀) (hi₁ : i ≠ i₁) :
      (∑ x : ZMod N, if P i x then w x else 0) = (N : ℝ) / m i := by
    have hPstep (x : ZMod N) : P i (x + (m i : ZMod N)) ↔ P i x := by
      dsimp [P]
      rw [map_add, map_natCast, ZMod.natCast_self, add_zero]
    obtain ⟨hc₀, hc₁, hp, hm⟩ := hnr (m i) (hm i) (hmax i hi₀ hi₁)
    have hh := pair_weight_sum (χ i₀) (χ i₁) (a i₀) (a i₁) (m i : ZMod N)
      (P i) hPstep hc₀ hc₁ hp hm
    change (∑ x : ZMod N, if P i x then w x else 0) = _ at hh
    rw [hh]
    simpa only [ZMod.card] using
      fiber_sum_one (f i).toAddMonoidHom (ZMod.castHom_surjective (hdiv i)) (a i)
  have hbound := weighted_cover_omit P hPcover {i₀, i₁} w hw hzero
  rw [hsumw] at hbound
  have heq : (∑ i ∈ Finset.univ \ {i₀, i₁},
        ∑ x : ZMod N, if P i x then w x else 0) =
      (N : ℝ) * ∑ i ∈ Finset.univ \ {i₀, i₁}, ((m i : ℝ)⁻¹) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hn := (Finset.mem_sdiff.mp hi).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    rw [hsum_other i hn.1 hn.2, div_eq_mul_inv]
  rw [heq] at hbound
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  nlinarith

#print axioms density_omit_two_largest_odd
end Erdos7Reduction

namespace Erdos7Reduction

/-- Pairwise nonresonance for odd moduli gives a two-class improvement to the
basic density obstruction. -/
theorem at_least_nine_moduli (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i, ¬ C.moduli i ≤ Ideal.span {2}) :
    letI := C.fintypeIndex
    9 ≤ Fintype.card C.ι := by
  classical
  letI := C.fintypeIndex
  have hcard := at_least_eight_moduli C hodd
  obtain ⟨j, _⟩ := arithmetic_cover C 0
  letI : Nonempty C.ι := ⟨j⟩
  let m (i : C.ι) := (C.moduli i).absNorm
  have hm (i : C.ι) : 1 < m i := moduli_absNorm_gt_one C i
  have hmi : Function.Injective m := moduli_absNorm_injective C
  have ho (i : C.ι) : Odd (m i) := (ideal_not_le_two_iff _).mp (hodd i)
  obtain ⟨i₀, hmax₀⟩ := Finite.exists_max m
  have hne : (Finset.univ.erase i₀).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ]
    omega
  obtain ⟨i₁, hi₁, hmax₁⟩ := Finset.exists_max_image (Finset.univ.erase i₀) m hne
  have h10ne : i₁ ≠ i₀ := (Finset.mem_erase.mp hi₁).1
  have h10 : m i₁ < m i₀ := lt_of_le_of_ne (hmax₀ i₁) (fun h => h10ne (hmi h))
  have hmax (i : C.ι) (hi₀ : i ≠ i₀) (hi₁ : i ≠ i₁) : m i < m i₁ :=
    lt_of_le_of_ne (hmax₁ i (by simp [hi₀])) (fun h => hi₁ (hmi h))
  have hbound := density_omit_two_largest_odd m C.residue
    (fun i => by have := hm i; omega) (arithmetic_cover C) i₀ i₁ (ho i₀) (ho i₁)
    (hm i₁) h10 hmax (∏ i, m i)
    (Finset.prod_pos (by intro i _; have := hm i; omega))
    (fun i => Finset.dvd_prod_of_mem m (Finset.mem_univ i))
  have hboundQ : (1 : ℚ) ≤ ∑ i ∈ Finset.univ \ {i₀, i₁}, (m i : ℚ)⁻¹ := by
    apply (Rat.cast_le (K := ℝ)).mp
    simpa using hbound
  by_contra hc
  have hc' : Fintype.card C.ι ≤ 8 := by omega
  let s := (Finset.univ \ {i₀, i₁}).image m
  have hs : s.card ≤ 6 := by
    simp only [s, Finset.card_image_of_injective _ hmi,
      Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have hp : ({i₀, i₁} : Finset C.ι).card = 2 := by simp [Ne.symm h10ne]
    rw [hp]
    omega
  have hprop : ∀ n ∈ s, 1 < n ∧ Odd n := by
    intro n hn
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
    exact ⟨hm i, ho i⟩
  have hsmall := odd_reciprocal_sum_lt_one s hs hprop
  have heq : (∑ n ∈ s, (n : ℚ)⁻¹) =
      ∑ i ∈ Finset.univ \ {i₀, i₁}, (m i : ℚ)⁻¹ :=
    Finset.sum_image (fun i _ j _ hij => hmi hij)
  rw [heq] at hsmall
  linarith

#print axioms at_least_nine_moduli
end Erdos7Reduction


/- Counting obstruction for covers by boxes with distinct nonempty supports. -/

namespace Erdos7Reduction
open Finset

private theorem choose_forbidden_singleton {ι κ : Type*}
    (A : ι → Type*) [∀ i, Nonempty (A i)]
    (s : κ → Finset ι) (hs : Function.Injective s) (a : κ → ∀ i, A i) :
    ∃ t : ∀ i, A i, ∀ k i, s k = {i} → a k i = t i := by
  classical
  have h (i : ι) : ∃ t : A i, ∀ k, s k = {i} → a k i = t := by
    by_cases hex : ∃ k, s k = {i}
    · obtain ⟨k, hk⟩ := hex
      refine ⟨a k i, ?_⟩
      intro j hj
      have heq : j = k := hs (hj.trans hk.symm)
      simp [heq]
    · refine ⟨Classical.choice inferInstance, ?_⟩
      intro k hk
      exact False.elim (hex ⟨k, hk⟩)
  choose t ht using h
  exact ⟨t, fun k i hi => ht i k hi⟩

/-- After avoiding every singleton-supported box, the remaining boxes must
cover the product of the punctured coordinate sets. -/
theorem distinct_box_composite_bound {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (s : κ → Finset ι) (hs : Function.Injective s) (hs0 : ∀ k, (s k).Nonempty)
    (a : κ → ∀ i, A i)
    (hcover : ∀ x : ∀ i, A i, ∃ k, ∀ i ∈ s k, x i = a k i) :
    (∏ i, (Fintype.card (A i) - 1)) ≤
      ∑ S ∈ (Finset.univ : Finset ι).powerset with 2 ≤ S.card,
        ∏ i ∈ Finset.univ \ S, (Fintype.card (A i) - 1) := by
  classical
  obtain ⟨t, ht⟩ := choose_forbidden_singleton A s hs a
  let T (i : ι) : Finset (A i) := Finset.univ.erase (t i)
  let Ω := Fintype.piFinset T
  let B (k : κ) := Ω.filter (fun x => ∀ i ∈ s k, x i = a k i)
  let K := Finset.univ.filter (fun k => 2 ≤ (s k).card)
  have hBsub (k : κ) : B k ⊆ Fintype.piFinset
      (fun i => if i ∈ s k then {a k i} else T i) := by
    intro x hx
    obtain ⟨hxΩ, hxmatch⟩ := Finset.mem_filter.mp hx
    apply Fintype.mem_piFinset.mpr
    intro i
    split_ifs with hi
    · simpa using hxmatch i hi
    · exact Fintype.mem_piFinset.mp hxΩ i
  have hBcard (k : κ) : (B k).card ≤
      ∏ i ∈ Finset.univ \ s k, (Fintype.card (A i) - 1) := by
    have h := Finset.card_le_card (hBsub k)
    rw [Fintype.card_piFinset] at h
    have heq : (∏ i, (if i ∈ s k then ({a k i} : Finset (A i)) else T i).card) =
        ∏ i ∈ Finset.univ \ s k, (Fintype.card (A i) - 1) := by
      simp only [apply_ite Finset.card, Finset.card_singleton, T,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      rw [Finset.prod_ite]
      simp only [Finset.prod_const_one, one_mul]
      congr 1
      ext i
      simp
    rwa [heq] at h
  have hcov : Ω ⊆ K.biUnion B := by
    intro x hx
    obtain ⟨k, hk⟩ := hcover x
    have hklarge : 2 ≤ (s k).card := by
      by_contra hlt
      have hcard : (s k).card = 1 := by
        have := (hs0 k).card_pos
        omega
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
      have hxi := Fintype.mem_piFinset.mp hx i
      have hne : x i ≠ t i := (Finset.mem_erase.mp hxi).1
      apply hne
      exact (hk i (by simp [hi])).trans (ht k i hi)
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hklarge⟩,
      Finset.mem_filter.mpr ⟨hx, hk⟩⟩
  have hcount : Ω.card ≤ ∑ k ∈ K, ∏ i ∈ Finset.univ \ s k, (Fintype.card (A i) - 1) := by
    exact (Finset.card_le_card hcov).trans
      (Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun k _ => hBcard k)))
  have hΩ : Ω.card = ∏ i, (Fintype.card (A i) - 1) := by
    simp only [Ω, Fintype.card_piFinset, T,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  rw [hΩ] at hcount
  have himg : K.image s ⊆ (Finset.univ : Finset ι).powerset.filter (fun S => 2 ≤ S.card) := by
    intro S hS
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hS
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
      (Finset.mem_filter.mp hk).2⟩
  have heq : (∑ S ∈ K.image s, ∏ i ∈ Finset.univ \ S, (Fintype.card (A i) - 1)) =
      ∑ k ∈ K, ∏ i ∈ Finset.univ \ s k, (Fintype.card (A i) - 1) :=
    Finset.sum_image (fun k _ l _ h => hs h)
  rw [← heq] at hcount
  exact hcount.trans (Finset.sum_le_sum_of_subset himg)

#print axioms distinct_box_composite_bound
end Erdos7Reduction

namespace Erdos7Reduction
open Finset

private theorem composite_capacity_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℕ) :
    (∑ S ∈ (Finset.univ : Finset ι).powerset with 2 ≤ S.card,
      ∏ i ∈ Finset.univ \ S, q i) + (∏ i, q i) +
        (∑ j, ∏ i ∈ Finset.univ.erase j, q i) = ∏ i, (1 + q i) := by
  classical
  let minor : Finset (Finset ι) := insert ∅ (Finset.univ.image (fun i : ι => {i}))
  let cap (S : Finset ι) := ∏ i ∈ Finset.univ \ S, q i
  have hmem (S : Finset ι) : S ∈ minor ↔ S.card ≤ 1 := by
    simp only [minor, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro (rfl | ⟨i, rfl⟩) <;> simp
    · intro h
      by_cases h0 : S = ∅
      · exact Or.inl h0
      · have hp : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0)
        obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (by omega : S.card = 1)
        exact Or.inr ⟨i, hi.symm⟩
  have hminor : minor ⊆ (Finset.univ : Finset ι).powerset := by
    intro S _
    exact Finset.mem_powerset.mpr (Finset.subset_univ _)
  have hmajor : (Finset.univ : Finset ι).powerset.filter (fun S => 2 ≤ S.card) =
      (Finset.univ : Finset ι).powerset \ minor := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_sdiff, hmem]
    exact and_congr_right (fun _ => by omega)
  have hnone : (∅ : Finset ι) ∉ Finset.univ.image (fun i : ι => {i}) := by simp
  have hminsum : ∑ S ∈ minor, cap S =
      (∏ i, q i) + ∑ j, ∏ i ∈ Finset.univ.erase j, q i := by
    rw [Finset.sum_insert hnone, Finset.sum_image]
    · simp only [cap, Finset.sdiff_empty, Finset.sdiff_singleton_eq_erase]
    · intro i _ j _ h
      exact Finset.singleton_injective h
  have hall : ∑ S ∈ (Finset.univ : Finset ι).powerset, cap S = ∏ i, (1 + q i) := by
    simpa only [cap, Finset.prod_const_one, one_mul] using
      (Finset.prod_add (fun _ : ι => (1 : ℕ)) q Finset.univ).symm
  have hsum := Finset.sum_sdiff (f := cap) hminor
  rw [← hmajor, hminsum, hall] at hsum
  simpa only [cap, add_assoc] using hsum

/-- A volume inequality independent of the residues for a box cover with
at most one box for every nonempty coordinate support. -/
theorem distinct_box_volume_bound {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (s : κ → Finset ι) (hs : Function.Injective s) (hs0 : ∀ k, (s k).Nonempty)
    (a : κ → ∀ i, A i)
    (hcover : ∀ x : ∀ i, A i, ∃ k, ∀ i ∈ s k, x i = a k i) :
    2 * (∏ i, (Fintype.card (A i) - 1)) +
      (∑ j, ∏ i ∈ Finset.univ.erase j, (Fintype.card (A i) - 1)) ≤
        ∏ i, Fintype.card (A i) := by
  have h := distinct_box_composite_bound A s hs hs0 a hcover
  have hid := composite_capacity_identity (fun i => Fintype.card (A i) - 1)
  have hc (i : ι) : 1 + (Fintype.card (A i) - 1) = Fintype.card (A i) := by
    have := Fintype.card_pos (α := A i)
    omega
  simp_rw [hc] at hid
  omega

#print axioms distinct_box_volume_bound
end Erdos7Reduction

namespace Erdos7Reduction
open Finset

/-- CRT converts a cover by products of distinct coprime coordinate moduli into
a box cover, giving the same punctured-volume obstruction. -/
theorem coprime_support_cover_bound {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hcop : Pairwise (Function.onFun Nat.Coprime p))
    (s : κ → Finset ι) (hs : Function.Injective s) (hs0 : ∀ k, (s k).Nonempty)
    (a : κ → ℤ)
    (hcover : ∀ x : ℤ, ∃ k, ((∏ i ∈ s k, p i : ℕ) : ℤ) ∣ x - a k) :
    2 * (∏ i, (p i - 1)) + (∑ j, ∏ i ∈ Finset.univ.erase j, (p i - 1)) ≤ ∏ i, p i := by
  classical
  letI (i : ι) : NeZero (p i) := ⟨by have := hp i; omega⟩
  let A (i : ι) := ZMod (p i)
  let b (k : κ) (i : ι) : A i := (a k : ZMod (p i))
  have hbox : ∀ x : ∀ i, A i, ∃ k, ∀ i ∈ s k, x i = b k i := by
    intro x
    let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) p Finset.univ
      (fun i _ => by have := hp i; omega) (fun i _ j _ hij => hcop hij)
    have hz (i : ι) : (z.val : ZMod (p i)) = x i := by
      rw [← ZMod.natCast_zmod_val (x i)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
    obtain ⟨k, hk⟩ := hcover (z.val : ℤ)
    refine ⟨k, ?_⟩
    intro i hi
    have hpi : p i ∣ ∏ j ∈ s k, p j := Finset.dvd_prod_of_mem p hi
    have hpi' : (p i : ℤ) ∣ ((∏ j ∈ s k, p j : ℕ) : ℤ) := by exact_mod_cast hpi
    have heq : (a k : ZMod (p i)) = ((z.val : ℤ) : ZMod (p i)) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (hpi'.trans hk)
    change x i = (a k : ZMod (p i))
    rw [← hz i]
    simpa only [Int.cast_natCast] using heq.symm
  simpa only [A, ZMod.card] using distinct_box_volume_bound A s hs hs0 b hbox

#print axioms coprime_support_cover_bound
end Erdos7Reduction

namespace Erdos7Reduction
open Finset

private theorem divisor_prime_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (m : ℕ) (hm : m ∣ ∏ i, p i) :
    ∃ S : Finset ι, m = ∏ i ∈ S, p i := by
  classical
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hinj h))
  have hsf : Squarefree (∏ i, p i) :=
    Finset.squarefree_prod_of_pairwise_isCoprime
      (fun i _ j _ hij => Nat.coprime_iff_isRelPrime.mp (hcop hij))
      (fun i _ => (hp i).squarefree)
  have hmsf : Squarefree m := Squarefree.squarefree_of_dvd hm hsf
  let P := Finset.univ.image p
  have hPprime : ∀ r ∈ P, r.Prime := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact hp i
  have hprodP : (∏ r ∈ P, r) = ∏ i, p i :=
    Finset.prod_image (fun i _ j _ hij => hinj hij)
  have hPF : (∏ i, p i).primeFactors = P := by
    rw [← hprodP]
    exact Nat.primeFactors_prod hPprime
  have hsub : m.primeFactors ⊆ P := by
    rw [← hPF]
    exact Nat.primeFactors_mono hm hsf.ne_zero
  let S := Finset.univ.filter (fun i => p i ∈ m.primeFactors)
  have heq : S.image p = m.primeFactors := by
    ext r
    constructor
    · intro hr
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
      exact (Finset.mem_filter.mp hi).2
    · intro hr
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hsub hr)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, by simpa [hi] using hr⟩, hi⟩
  refine ⟨S, ?_⟩
  rw [← Nat.prod_primeFactors_of_squarefree hmsf, ← heq,
    Finset.prod_image (fun i _ j _ hij => hinj hij)]

/-- A necessary bound for a covering whose moduli divide a squarefree prime product. -/
theorem prime_product_cover_bound {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hp_inj : Function.Injective p)
    (m : κ → ℕ) (a : κ → ℤ) (hm : ∀ k, 1 < m k) (hm_inj : Function.Injective m)
    (hdiv : ∀ k, m k ∣ ∏ i, p i)
    (hcover : ∀ x : ℤ, ∃ k, (m k : ℤ) ∣ x - a k) :
    2 * (∏ i, (p i - 1)) + (∑ j, ∏ i ∈ Finset.univ.erase j, (p i - 1)) ≤ ∏ i, p i := by
  classical
  choose S hS using fun k => divisor_prime_support p hp hp_inj (m k) (hdiv k)
  have hSi : Function.Injective S := by
    intro k l hkl
    apply hm_inj
    rw [hS k, hS l, hkl]
  have hS0 (k : κ) : (S k).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    have hh := hm k
    rw [hS k, he, Finset.prod_empty] at hh
    omega
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hp_inj h))
  apply coprime_support_cover_bound p (fun i => (hp i).pos) hcop S hSi hS0 a
  intro x
  obtain ⟨k, hk⟩ := hcover x
  exact ⟨k, by rwa [← hS k]⟩

#print axioms prime_product_cover_bound
end Erdos7Reduction

namespace Erdos7Reduction

private def firstTenOddPrimes : Fin 10 → ℕ := ![3, 5, 7, 11, 13, 17, 19, 23, 29, 31]

/-- No arithmetic cover with distinct nontrivial moduli can have every modulus
dividing the product of the first ten odd primes. -/
theorem not_arithmetic_cover_period_100280245065 {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hm : ∀ k, 1 < m k) (hm_inj : Function.Injective m)
    (hdiv : ∀ k, m k ∣ 100280245065) :
    ¬ (∀ x : ℤ, ∃ k, (m k : ℤ) ∣ x - a k) := by
  intro hcover
  have hp : ∀ i, (firstTenOddPrimes i).Prime := by decide
  have hinj : Function.Injective firstTenOddPrimes := by decide
  have hprod : (∏ i, firstTenOddPrimes i) = 100280245065 := by decide
  have hbound := prime_product_cover_bound firstTenOddPrimes hp hinj m a hm hm_inj
    (fun k => by rw [hprod]; exact hdiv k) hcover
  have hnum : ¬ (2 * (∏ i, (firstTenOddPrimes i - 1)) +
      (∑ j, ∏ i ∈ Finset.univ.erase j, (firstTenOddPrimes i - 1)) ≤
      ∏ i, firstTenOddPrimes i) := by decide
  exact hnum hbound

#print axioms not_arithmetic_cover_period_100280245065
end Erdos7Reduction

namespace Erdos7Reduction
open Finset

/-- Restricting each coordinate set cannot destroy the existence of a cover with
specified supports: boxes missing the restriction may be relocated arbitrarily. -/
theorem box_cover_restrict_coordinates {ι κ : Type*}
    (A B : ι → Type*) [∀ i, Nonempty (B i)] (f : ∀ i, B i ↪ A i)
    (s : κ → Finset ι) (a : κ → ∀ i, A i)
    (hcover : ∀ x : ∀ i, A i, ∃ k, ∀ i ∈ s k, x i = a k i) :
    ∃ b : κ → ∀ i, B i, ∀ x : ∀ i, B i, ∃ k, ∀ i ∈ s k, x i = b k i := by
  classical
  let b (k : κ) (i : ι) := Function.invFun (f i) (a k i)
  refine ⟨b, ?_⟩
  intro x
  obtain ⟨k, hk⟩ := hcover (fun i => f i (x i))
  refine ⟨k, ?_⟩
  intro i hi
  change x i = Function.invFun (f i) (a k i)
  rw [← hk i hi, Function.leftInverse_invFun (f i).injective]

/-- The prime-product obstruction can be evaluated on any smaller coordinate sizes. -/
theorem prime_product_cover_bound_mono {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hp_inj : Function.Injective p)
    (q : ι → ℕ) (hq : ∀ i, 0 < q i) (hqp : ∀ i, q i ≤ p i)
    (m : κ → ℕ) (a : κ → ℤ) (hm : ∀ k, 1 < m k) (hm_inj : Function.Injective m)
    (hdiv : ∀ k, m k ∣ ∏ i, p i)
    (hcover : ∀ x : ℤ, ∃ k, (m k : ℤ) ∣ x - a k) :
    2 * (∏ i, (q i - 1)) + (∑ j, ∏ i ∈ Finset.univ.erase j, (q i - 1)) ≤ ∏ i, q i := by
  classical
  choose S hS using fun k => divisor_prime_support p hp hp_inj (m k) (hdiv k)
  have hSi : Function.Injective S := by
    intro k l hkl
    apply hm_inj
    rw [hS k, hS l, hkl]
  have hS0 (k : κ) : (S k).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    have hh := hm k
    rw [hS k, he, Finset.prod_empty] at hh
    omega
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hp_inj h))
  letI (i : ι) : NeZero (p i) := ⟨(hp i).ne_zero⟩
  letI (i : ι) : NeZero (q i) := ⟨by have := hq i; omega⟩
  let A (i : ι) := ZMod (p i)
  let B (i : ι) := ZMod (q i)
  let b (k : κ) (i : ι) : A i := (a k : ZMod (p i))
  have hbox : ∀ x : ∀ i, A i, ∃ k, ∀ i ∈ S k, x i = b k i := by
    intro x
    let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) p Finset.univ
      (fun i _ => (hp i).ne_zero) (fun i _ j _ hij => hcop hij)
    have hz (i : ι) : (z.val : ZMod (p i)) = x i := by
      rw [← ZMod.natCast_zmod_val (x i)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
    obtain ⟨k, hk⟩ := hcover (z.val : ℤ)
    refine ⟨k, ?_⟩
    intro i hi
    have hpi : p i ∣ m k := by rw [hS k]; exact Finset.dvd_prod_of_mem p hi
    have hpi' : (p i : ℤ) ∣ (m k : ℤ) := by exact_mod_cast hpi
    have heq : (a k : ZMod (p i)) = ((z.val : ℤ) : ZMod (p i)) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (hpi'.trans hk)
    change x i = (a k : ZMod (p i))
    rw [← hz i]
    simpa only [Int.cast_natCast] using heq.symm
  let f (i : ι) : B i ↪ A i := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by simpa only [A, B, ZMod.card] using hqp i))
  obtain ⟨c, hc⟩ := box_cover_restrict_coordinates A B f S b hbox
  simpa only [B, ZMod.card] using distinct_box_volume_bound B S hSi hS0 c hc

#print axioms prime_product_cover_bound_mono
end Erdos7Reduction

namespace Erdos7Reduction
open Finset

private theorem first_ten_prime_lower_bound (p : Fin 10 → ℕ)
    (hp : ∀ i, (p i).Prime) (ho : ∀ i, Odd (p i)) (hmono : StrictMono p) :
    ∀ i, firstTenOddPrimes i ≤ p i := by
  have htable : ∀ i : Fin 9, ∀ n : Fin 32, n.val.Prime →
      firstTenOddPrimes i.castSucc < n.val → firstTenOddPrimes i.succ ≤ n.val := by decide
  have hmax : ∀ i, firstTenOddPrimes i ≤ 31 := by decide
  have H (k : ℕ) : ∀ hk : k < 10, firstTenOddPrimes ⟨k, hk⟩ ≤ p ⟨k, hk⟩ := by
    induction k with
    | zero =>
      intro hk
      have h2 := (hp ⟨0, hk⟩).two_le
      have hodd := Nat.odd_iff.mp (ho ⟨0, hk⟩)
      change 3 ≤ p ⟨0, hk⟩
      omega
    | succ k ih =>
      intro hk
      have hk' : k < 10 := by omega
      have hprev := ih hk'
      have hinc := hmono (show (⟨k, hk'⟩ : Fin 10) < ⟨k+1, hk⟩ by simp)
      by_cases hb : p ⟨k+1, hk⟩ < 32
      · have ht := htable ⟨k, by omega⟩ ⟨p ⟨k+1, hk⟩, hb⟩ (hp ⟨k+1, hk⟩)
        apply ht
        exact lt_of_le_of_lt hprev hinc
      · exact (hmax ⟨k+1, hk⟩).trans (by omega)
  exact fun i => H i.val i.isLt

private theorem not_cover_ten_odd_primes {κ : Type*} [Fintype κ]
    (P : Finset ℕ) (hPcard : P.card = 10)
    (hP : ∀ p ∈ P, p.Prime ∧ Odd p)
    (m : κ → ℕ) (a : κ → ℤ) (hm : ∀ k, 1 < m k) (hm_inj : Function.Injective m)
    (hdiv : ∀ k, m k ∣ ∏ p ∈ P, p)
    (hcover : ∀ x : ℤ, ∃ k, (m k : ℤ) ∣ x - a k) : False := by
  let p := P.orderEmbOfFin hPcard
  have hp (i : Fin 10) : (p i).Prime := (hP _ (P.orderEmbOfFin_mem hPcard i)).1
  have ho (i : Fin 10) : Odd (p i) := (hP _ (P.orderEmbOfFin_mem hPcard i)).2
  have hprod : (∏ i, p i) = ∏ r ∈ P, r := by
    conv_rhs => rw [← P.map_orderEmbOfFin_univ hPcard]
    exact (Finset.prod_map _ _ (fun n : ℕ => n)).symm
  have hbound := prime_product_cover_bound_mono p hp p.injective firstTenOddPrimes
    (by decide) (first_ten_prime_lower_bound p hp ho p.strictMono) m a hm hm_inj
    (fun k => by rw [hprod]; exact hdiv k) hcover
  have hnum : ¬ (2 * (∏ i, (firstTenOddPrimes i - 1)) +
      (∑ j, ∏ i ∈ Finset.univ.erase j, (firstTenOddPrimes i - 1)) ≤
      ∏ i, firstTenOddPrimes i) := by decide
  exact hnum hbound

private theorem extend_odd_primes_to_ten (P : Finset ℕ) (hcard : P.card ≤ 10)
    (hP : ∀ p ∈ P, p.Prime ∧ Odd p) :
    ∃ T : Finset ℕ, P ⊆ T ∧ T.card = 10 ∧ ∀ p ∈ T, p.Prime ∧ Odd p := by
  classical
  let A : Set ℕ := {p | p.Prime} \ {2}
  have hA : A.Infinite := Nat.infinite_setOf_prime.diff (Set.finite_singleton 2)
  have hAP : (A \ (P : Set ℕ)).Infinite := hA.diff P.finite_toSet
  obtain ⟨U, hU, hUc⟩ := hAP.exists_subset_card_eq (10 - P.card)
  have hdis : Disjoint P U := by
    apply Finset.disjoint_left.mpr
    intro p hp hu
    exact (hU hu).2 hp
  refine ⟨P ∪ U, Finset.subset_union_left, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdis, hUc]
    omega
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hP p hp
    · have hh := (hU hp).1
      exact ⟨hh.1, hh.1.odd_of_ne_two (by simpa using hh.2)⟩

/-- Every odd covering system with squarefree distinct moduli involves at least
eleven distinct prime factors. -/
theorem squarefree_arithmetic_cover_prime_count {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hm : ∀ k, 1 < m k) (hm_inj : Function.Injective m)
    (hsf : ∀ k, Squarefree (m k)) (hodd : ∀ k, Odd (m k))
    (hcover : ∀ x : ℤ, ∃ k, (m k : ℤ) ∣ x - a k) :
    11 ≤ (Finset.univ.biUnion (fun k => (m k).primeFactors)).card := by
  classical
  let P := Finset.univ.biUnion (fun k => (m k).primeFactors)
  have hP : ∀ p ∈ P, p.Prime ∧ Odd p := by
    intro p hp
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hp
    have hpf := Nat.mem_primeFactors.mp hk
    exact ⟨hpf.1, (hodd k).of_dvd_nat hpf.2.1⟩
  by_contra hc
  have hcard : P.card ≤ 10 := by dsimp [P]; omega
  obtain ⟨T, hPT, hTc, hT⟩ := extend_odd_primes_to_ten P hcard hP
  apply not_cover_ten_odd_primes T hTc hT m a hm hm_inj _ hcover
  intro k
  rw [← Nat.prod_primeFactors_of_squarefree (hsf k)]
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  apply hPT
  exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hp⟩

#print axioms squarefree_arithmetic_cover_prime_count
end Erdos7Reduction

namespace Erdos7Reduction

/-- An ideal-valued strict cover cannot have every modulus dividing the first
ten odd primes' product. -/
theorem not_all_moduli_divide_100280245065 (C : StrictCoveringSystem ℤ) :
    ¬ (∀ i, (C.moduli i).absNorm ∣ 100280245065) := by
  letI := C.fintypeIndex
  intro hdiv
  exact not_arithmetic_cover_period_100280245065
    (fun i => (C.moduli i).absNorm) C.residue (moduli_absNorm_gt_one C)
    (moduli_absNorm_injective C) hdiv (arithmetic_cover C)

/-- Any odd strict cover with squarefree moduli requires at least eleven primes. -/
theorem squarefree_cover_prime_count (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i, ¬ C.moduli i ≤ Ideal.span {2})
    (hsf : ∀ i, Squarefree (C.moduli i).absNorm) :
    letI := C.fintypeIndex
    11 ≤ (Finset.univ.biUnion (fun i => (C.moduli i).absNorm.primeFactors)).card := by
  letI := C.fintypeIndex
  exact squarefree_arithmetic_cover_prime_count
    (fun i => (C.moduli i).absNorm) C.residue (moduli_absNorm_gt_one C)
    (moduli_absNorm_injective C) hsf (fun i => (ideal_not_le_two_iff _).mp (hodd i))
    (arithmetic_cover C)

#print axioms not_all_moduli_divide_100280245065
#print axioms squarefree_cover_prime_count
end Erdos7Reduction


/- Product-set counting tools for a pure-prime-power sieve. -/

namespace Erdos7Reduction
open Finset

/-- The sum of the relative volumes of boxes covering a finite product is at least one. -/
theorem finite_product_cover_density {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, DecidableEq (A i)]
    (U : ∀ i, Finset (A i)) (hU : ∀ i, (U i).Nonempty)
    (K : Finset κ) (B : κ → ∀ i, Finset (A i))
    (hcover : ∀ x ∈ Fintype.piFinset U, ∃ k ∈ K, ∀ i, x i ∈ B k i) :
    (1 : ℚ) ≤ ∑ k ∈ K, ∏ i, (((U i ∩ B k i).card : ℚ) / (U i).card) := by
  classical
  let C (k : κ) := Fintype.piFinset (fun i => U i ∩ B k i)
  have hsub : Fintype.piFinset U ⊆ K.biUnion C := by
    intro x hx
    obtain ⟨k, hk, hxi⟩ := hcover x hx
    refine Finset.mem_biUnion.mpr ⟨k, hk, Fintype.mem_piFinset.mpr ?_⟩
    intro i
    exact Finset.mem_inter.mpr ⟨Fintype.mem_piFinset.mp hx i, hxi i⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  simp only [C, Fintype.card_piFinset] at hcard
  have hpos : (0 : ℚ) < ∏ i, ((U i).card : ℚ) := by
    apply Finset.prod_pos
    intro i _
    exact_mod_cast (hU i).card_pos
  simp_rw [Finset.prod_div_distrib]
  rw [← Finset.sum_div, le_div_iff₀ hpos, one_mul]
  exact_mod_cast hcard

/-- A finite union of small sets leaves a quantitatively large complement. -/
theorem relative_complement_bound {A κ : Type*} [Fintype A] [DecidableEq A]
    (K : Finset κ) (B : κ → Finset A) (w : κ → ℚ) (r : ℚ)
    (hB : ∀ k ∈ K, (B k).card ≤ (Fintype.card A : ℚ) * w k)
    (hw : ∑ k ∈ K, w k ≤ r) :
    (Fintype.card A : ℚ) * (1 - r) ≤
      ((Finset.univ \ K.biUnion B).card : ℚ) := by
  have hcard : ((K.biUnion B).card : ℚ) ≤ ∑ k ∈ K, (B k).card := by
    exact_mod_cast (Finset.card_biUnion_le (s := K) (t := B))
  push_cast at hcard
  have hsum : (∑ k ∈ K, (B k).card : ℚ) ≤ (Fintype.card A : ℚ) * r := by
    calc
      _ ≤ ∑ k ∈ K, (Fintype.card A : ℚ) * w k :=
        Finset.sum_le_sum (fun k hk => hB k hk)
      _ = (Fintype.card A : ℚ) * ∑ k ∈ K, w k := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)
  have heq : (Finset.univ \ K.biUnion B).card + (K.biUnion B).card = Fintype.card A := by
    simpa only [Finset.univ_inter, Finset.card_univ] using
      Finset.card_sdiff_add_card_inter Finset.univ (K.biUnion B)
  have heq' : ((Finset.univ \ K.biUnion B).card : ℚ) + (K.biUnion B).card =
      Fintype.card A := by exact_mod_cast heq
  nlinarith

/-- A geometric bound for distinct positive exponents. -/
theorem positive_geometric_sum_le (p : ℕ) (hp : 1 < p) (s : Finset ℕ)
    (hs : ∀ a ∈ s, 0 < a) :
    (∑ a ∈ s, ((p : ℚ)⁻¹)^a) ≤ 1 / (p - 1 : ℚ) := by
  let N := s.sup id + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hsub : s ⊆ (Finset.range N).erase 0 := by
    intro a ha
    refine Finset.mem_erase.mpr ⟨by have := hs a ha; omega, ?_⟩
    have hle : a ≤ s.sup id := Finset.le_sup (f := id) ha
    exact Finset.mem_range.mpr (by dsimp [N]; omega)
  have hle : (∑ a ∈ s, ((p : ℚ)⁻¹)^a) ≤
      ∑ a ∈ (Finset.range N).erase 0, ((p : ℚ)⁻¹)^a :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
  have he := Finset.sum_erase_add (Finset.range N) (fun a => ((p : ℚ)⁻¹)^a)
    (Finset.mem_range.mpr hN)
  have hg := geom_sum_mul ((p : ℚ)⁻¹) N
  have hp0 : (0 : ℚ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp
  have hn0 : (0 : ℚ) ≤ ((p : ℚ)⁻¹)^N := by positivity
  have hrecip : (p : ℚ)⁻¹ * p = 1 := inv_mul_cancel₀ (ne_of_gt hp0)
  have hbound : (∑ a ∈ (Finset.range N).erase 0, ((p : ℚ)⁻¹)^a) * (p - 1) ≤ 1 := by
    simp only [pow_zero] at he
    have hg' := congrArg (fun x : ℚ => x * p) hg
    dsimp only at hg'
    rw [mul_assoc, sub_mul, hrecip, one_mul] at hg'
    nlinarith [mul_nonneg hn0 hp0.le]
  rw [le_div_iff₀ (by linarith : (0 : ℚ) < p - 1)]
  exact (mul_le_mul_of_nonneg_right hle (by linarith)).trans hbound

#print axioms finite_product_cover_density
#print axioms relative_complement_bound
#print axioms positive_geometric_sum_le
end Erdos7Reduction

namespace Erdos7Reduction
open Finset

/-- Sum tensor-product weights over distinct vectors supported on at least two
coordinates, using an upper bound for the sum of positive-level weights. -/
theorem mixed_vector_weight_bound {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (K : Finset κ) (e : κ → ι → ℕ) (he : Set.InjOn e K)
    (E : ι → Finset ℕ) (hE : ∀ k ∈ K, ∀ i, e k i ∈ E i)
    (hmixed : ∀ k ∈ K, 2 ≤ (Finset.univ.filter (fun i => e k i ≠ 0)).card)
    (w : ι → ℕ → ℚ) (hw : ∀ i n, 0 ≤ w i n) (hw0 : ∀ i, w i 0 = 1)
    (z : ι → ℚ) (hz : ∀ i, ∑ n ∈ (E i).erase 0, w i n ≤ z i) :
    (∑ k ∈ K, ∏ i, w i (e k i)) ≤
      ∑ S ∈ (Finset.univ : Finset ι).powerset with 2 ≤ S.card, ∏ i ∈ S, z i := by
  classical
  let supp (k : κ) := Finset.univ.filter (fun i => e k i ≠ 0)
  let T := (Finset.univ : Finset ι).powerset.filter (fun S => 2 ≤ S.card)
  have hmemT (k : κ) (hk : k ∈ K) : supp k ∈ T :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hmixed k hk⟩
  have hfiber : (∑ S ∈ T, ∑ k ∈ K with supp k = S, ∏ i, w i (e k i)) =
      ∑ k ∈ K, ∏ i, w i (e k i) := by
    rw [Finset.sum_fiberwise_eq_sum_filter]
    congr 1
    exact Finset.filter_eq_self.mpr hmemT
  rw [← hfiber]
  apply Finset.sum_le_sum
  intro S hS
  let L := K.filter (fun k => supp k = S)
  let Q (i : ι) := if i ∈ S then (E i).erase 0 else {0}
  have himg : L.image e ⊆ Fintype.piFinset Q := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hkK, hkS⟩ := Finset.mem_filter.mp hk
    apply Fintype.mem_piFinset.mpr
    intro i
    have hsi : i ∈ S ↔ e k i ≠ 0 := by rw [← hkS]; simp [supp]
    dsimp [Q]
    split_ifs with hi
    · exact Finset.mem_erase.mpr ⟨hsi.mp hi, hE k hkK i⟩
    · have h0 : e k i = 0 := by simpa only [not_not] using mt hsi.mpr hi
      simp [h0]
  have hsum_image : (∑ x ∈ L.image e, ∏ i, w i (x i)) =
      ∑ k ∈ L, ∏ i, w i (e k i) :=
    Finset.sum_image (fun k hk l hl hkl => he (Finset.mem_filter.mp hk).1
      (Finset.mem_filter.mp hl).1 hkl)
  have hle : (∑ k ∈ L, ∏ i, w i (e k i)) ≤
      ∑ x ∈ Fintype.piFinset Q, ∏ i, w i (x i) := by
    rw [← hsum_image]
    exact Finset.sum_le_sum_of_subset_of_nonneg himg
      (by intro x _ _; exact Finset.prod_nonneg (fun i _ => hw i (x i)))
  rw [← Finset.prod_univ_sum] at hle
  have hcoord (i : ι) : (∑ n ∈ Q i, w i n) ≤ if i ∈ S then z i else 1 := by
    dsimp [Q]
    split_ifs
    · exact hz i
    · simp [hw0]
  have hprod : (∏ i, ∑ n ∈ Q i, w i n) ≤ ∏ i, if i ∈ S then z i else 1 :=
    Finset.prod_le_prod (fun i _ => Finset.sum_nonneg (fun n _ => hw i n))
      (fun i _ => hcoord i)
  have heq : (∏ i, if i ∈ S then z i else 1) = ∏ i ∈ S, z i := by
    rw [← Finset.prod_filter]
    simp
  rw [heq] at hprod
  exact hle.trans hprod

#print axioms mixed_vector_weight_bound
end Erdos7Reduction

namespace Erdos7Reduction
open Finset

private theorem conditioned_geometric_sum_le (p : ℕ) (hp : 2 < p) (E : Finset ℕ) :
    (∑ n ∈ E.erase 0, if n = 0 then (1 : ℚ) else
      ((p : ℚ) - 1) / (p - 2) * ((p : ℚ)⁻¹)^n) ≤ 1 / (p - 2 : ℚ) := by
  have hp' : (2 : ℚ) < p := by exact_mod_cast hp
  have hp1 : (0 : ℚ) < p - 1 := by linarith
  have hp2 : (0 : ℚ) < p - 2 := by linarith
  have heq : (∑ n ∈ E.erase 0, if n = 0 then (1 : ℚ) else
      ((p : ℚ) - 1) / (p - 2) * ((p : ℚ)⁻¹)^n) =
      ((p : ℚ) - 1) / (p - 2) * ∑ n ∈ E.erase 0, ((p : ℚ)⁻¹)^n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [if_neg (Finset.mem_erase.mp hn).1]
  rw [heq]
  have hgeom := positive_geometric_sum_le p (by omega) (E.erase 0)
    (fun n hn => by have := (Finset.mem_erase.mp hn).1; omega)
  calc
    _ ≤ (((p : ℚ) - 1) / (p - 2)) * (1 / (p - 1)) :=
      mul_le_mul_of_nonneg_left hgeom (div_nonneg hp1.le hp2.le)
    _ = _ := by field_simp

private theorem conditioned_ratio_bound (N u b : ℕ) (p : ℕ) (hp : 2 < p)
    (hN : 0 < N) (hu : (N : ℚ) * (1 - 1 / (p - 1 : ℚ)) ≤ u)
    (r : ℚ) (hr : 0 ≤ r) (hb : (b : ℚ) ≤ N * r) :
    0 < u ∧ (b : ℚ) / u ≤ ((p : ℚ) - 1) / (p - 2) * r := by
  have hp' : (2 : ℚ) < p := by exact_mod_cast hp
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  have hp1 : (0 : ℚ) < p - 1 := by linarith
  have hp2 : (0 : ℚ) < p - 2 := by linarith
  have heq : (1 - 1 / (p - 1 : ℚ)) = (p - 2 : ℚ) / (p - 1) := by field_simp; ring
  rw [heq] at hu
  have hu' : (0 : ℚ) < u := lt_of_lt_of_le (mul_pos hN' (div_pos hp2 hp1)) hu
  refine ⟨by exact_mod_cast hu', ?_⟩
  rw [div_le_iff₀ hu']
  have hcancel : (N : ℚ) ≤ u * ((p - 1 : ℚ) / (p - 2)) := by
    have h := mul_le_mul_of_nonneg_right hu (div_nonneg hp1.le hp2.le)
    have hc : (p - 2 : ℚ) / (p - 1) * ((p - 1) / (p - 2)) = 1 := by field_simp
    rw [mul_assoc, hc, mul_one] at h
    exact h
  have h := hb.trans (mul_le_mul_of_nonneg_right hcancel hr)
  nlinarith

#print axioms conditioned_ratio_bound
end Erdos7Reduction

namespace Erdos7Reduction
open Finset

/-- A finite product-space sieve for uniquely labelled prime-power boxes.
Removing all one-coordinate boxes gives a bound involving only mixed supports. -/
theorem pure_power_box_sieve {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (p : ι → ℕ) (hp : ∀ i, 2 < p i)
    (e : κ → ι → ℕ) (he : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (B : κ → ∀ i, Finset (A i))
    (hB0 : ∀ k i, e k i = 0 → B k i = Finset.univ)
    (hBcard : ∀ k i, ((B k i).card : ℚ) ≤
      (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(e k i))
    (hcover : ∀ x : ∀ i, A i, ∃ k, ∀ i, x i ∈ B k i) :
    (1 : ℚ) ≤ ∑ S ∈ (Finset.univ : Finset ι).powerset with 2 ≤ S.card,
      ∏ i ∈ S, (1 / (p i - 2 : ℚ)) := by
  classical
  let supp (k : κ) := Finset.univ.filter (fun i => e k i ≠ 0)
  have hmem (k : κ) (i : ι) : i ∈ supp k ↔ e k i ≠ 0 := by simp [supp]
  let Pure (i : ι) := Finset.univ.filter (fun k => supp k = {i})
  have hpure (i : ι) (k : κ) (hk : k ∈ Pure i) : supp k = {i} :=
    (Finset.mem_filter.mp hk).2
  have hppos (i : ι) (k : κ) (hk : k ∈ Pure i) : 0 < e k i := by
    have hh : i ∈ supp k := by rw [hpure i k hk]; simp
    have := (hmem k i).mp hh
    omega
  have hpinj (i : ι) : Set.InjOn (fun k => e k i) (Pure i) := by
    intro k hk l hl hkl
    apply he
    funext j
    by_cases hji : j = i
    · simpa [hji] using hkl
    · have hk0 : e k j = 0 := by
        by_contra hh
        have hmem' := (hmem k j).mpr hh
        rw [hpure i k hk] at hmem'
        exact hji (Finset.mem_singleton.mp hmem')
      have hl0 : e l j = 0 := by
        by_contra hh
        have hmem' := (hmem l j).mpr hh
        rw [hpure i l hl] at hmem'
        exact hji (Finset.mem_singleton.mp hmem')
      rw [hk0, hl0]
  have hpsum (i : ι) : (∑ k ∈ Pure i, ((p i : ℚ)⁻¹)^(e k i)) ≤
      1 / (p i - 1 : ℚ) := by
    have heq : (∑ n ∈ (Pure i).image (fun k => e k i), ((p i : ℚ)⁻¹)^n) =
        ∑ k ∈ Pure i, ((p i : ℚ)⁻¹)^(e k i) := Finset.sum_image (hpinj i)
    rw [← heq]
    apply positive_geometric_sum_le (p i) (by have := hp i; omega)
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
    exact hppos i k hk
  let U (i : ι) := Finset.univ \ (Pure i).biUnion (fun k => B k i)
  have hUlower (i : ι) : (Fintype.card (A i) : ℚ) * (1 - 1 / (p i - 1 : ℚ)) ≤
      (U i).card :=
    relative_complement_bound (Pure i) (fun k => B k i)
      (fun k => ((p i : ℚ)⁻¹)^(e k i)) _ (fun k _ => hBcard k i) (hpsum i)
  have hU (i : ι) : (U i).Nonempty := by
    apply Finset.card_pos.mp
    exact (conditioned_ratio_bound (Fintype.card (A i)) (U i).card 0 (p i) (hp i)
      Fintype.card_pos (hUlower i) 0 (by norm_num) (by simp)).1
  let K := Finset.univ.filter (fun k => 2 ≤ (supp k).card)
  have hUcover : ∀ x ∈ Fintype.piFinset U, ∃ k ∈ K, ∀ i, x i ∈ B k i := by
    intro x hx
    obtain ⟨k, hk⟩ := hcover x
    have hkm : 2 ≤ (supp k).card := by
      by_contra hlt
      obtain ⟨i, hi⟩ := he0 k
      have hpos : 0 < (supp k).card :=
        Finset.card_pos.mpr ⟨i, (hmem k i).mpr hi⟩
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (by omega : (supp k).card = 1)
      have hxj := Fintype.mem_piFinset.mp hx j
      have hnot := (Finset.mem_sdiff.mp hxj).2
      apply hnot
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, hk j⟩
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkm⟩, hk⟩
  let w (i : ι) (n : ℕ) : ℚ := if n = 0 then 1 else
    ((p i : ℚ) - 1) / (p i - 2) * ((p i : ℚ)⁻¹)^n
  have hw (i : ι) (n : ℕ) : 0 ≤ w i n := by
    have hpi : (2 : ℚ) < p i := by exact_mod_cast hp i
    dsimp [w]
    split_ifs
    · norm_num
    · exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (by positivity)
  have hw0 (i : ι) : w i 0 = 1 := by simp [w]
  have hratio (k : κ) (i : ι) : (((U i ∩ B k i).card : ℚ) / (U i).card) ≤ w i (e k i) := by
    by_cases hzero : e k i = 0
    · rw [hB0 k i hzero, Finset.inter_univ, hzero, hw0]
      have hn : ((U i).card : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hU i).card_pos)
      rw [div_self hn]
    · have hc : ((U i ∩ B k i).card : ℚ) ≤ (Fintype.card (A i) : ℚ) *
          ((p i : ℚ)⁻¹)^(e k i) := by
        have hh : ((U i ∩ B k i).card : ℚ) ≤ (B k i).card := by
          exact_mod_cast Finset.card_le_card Finset.inter_subset_right
        exact hh.trans (hBcard k i)
      simpa only [w, if_neg hzero] using
        (conditioned_ratio_bound (Fintype.card (A i)) (U i).card (U i ∩ B k i).card
          (p i) (hp i) Fintype.card_pos (hUlower i) _ (by positivity) hc).2
  have hbound := finite_product_cover_density A U hU K B hUcover
  have hprod : (∑ k ∈ K, ∏ i, (((U i ∩ B k i).card : ℚ) / (U i).card)) ≤
      ∑ k ∈ K, ∏ i, w i (e k i) := by
    apply Finset.sum_le_sum
    intro k _
    exact Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hratio k i)
  have hmixed := mixed_vector_weight_bound K e he.injOn
    (fun i => Finset.univ.image (fun k => e k i))
    (fun k _ i => Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
    (fun k hk => (Finset.mem_filter.mp hk).2) w hw hw0
    (fun i => 1 / (p i - 2 : ℚ))
    (fun i => conditioned_geometric_sum_le (p i) (hp i) _)
  exact hbound.trans (hprod.trans hmixed)

#print axioms pure_power_box_sieve
end Erdos7Reduction

namespace Erdos7Reduction
open Finset

private theorem fiber_card_rat {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] [DecidableEq H] (f : G →+ H)
    (hf : Function.Surjective f) (b : H) :
    ((Finset.univ.filter (fun x => f x = b)).card : ℚ) =
      (Fintype.card G : ℚ) / Fintype.card H := by
  classical
  have heq (y : H) : (Finset.univ.filter (fun x => f x = y)).card =
      (Finset.univ.filter (fun x => f x = b)).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf b)
  have hcard : Fintype.card G =
      Fintype.card H * (Finset.univ.filter (fun x => f x = b)).card := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset G))
      (t := (Finset.univ : Finset H)) (f := f) (fun _ _ => Finset.mem_univ _)
    simpa only [heq, Finset.card_univ, Finset.sum_const, nsmul_eq_mul] using h
  have hc : (Fintype.card H : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card H))
  apply (eq_div_iff hc).mpr
  exact_mod_cast (Nat.mul_comm _ _).trans hcard.symm

/-- A residue-independent necessary bound when the distinct moduli are products
of powers of pairwise coprime odd bases. -/
theorem coprime_power_cover_bound {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, 2 < p i) (hcop : Pairwise (Function.onFun Nat.Coprime p))
    (e : κ → ι → ℕ) (he : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (a : κ → ℤ)
    (hcover : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k) :
    (1 : ℚ) ≤ ∑ S ∈ (Finset.univ : Finset ι).powerset with 2 ≤ S.card,
      ∏ i ∈ S, (1 / (p i - 2 : ℚ)) := by
  classical
  let E (i : ι) := Finset.univ.sup (fun k => e k i)
  have heE (k : κ) (i : ι) : e k i ≤ E i := Finset.le_sup (f := fun k => e k i) (Finset.mem_univ k)
  letI (i : ι) : NeZero (p i) := ⟨by have := hp i; omega⟩
  let A (i : ι) := ZMod (p i ^ E i)
  let f (k : κ) (i : ι) := ZMod.castHom (pow_dvd_pow (p i) (heE k i)) (ZMod (p i ^ e k i))
  let B (k : κ) (i : ι) := Finset.univ.filter (fun x : A i => f k i x = (a k : ZMod (p i ^ e k i)))
  have hB0 (k : κ) (i : ι) (hzero : e k i = 0) : B k i = Finset.univ := by
    haveI : Subsingleton (ZMod (p i ^ e k i)) := by rw [hzero, pow_zero]; infer_instance
    ext x
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact Subsingleton.elim _ _
  have hBcard (k : κ) (i : ι) : ((B k i).card : ℚ) ≤
      (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(e k i) := by
    have hh := fiber_card_rat (f k i).toAddMonoidHom
      (ZMod.castHom_surjective (pow_dvd_pow (p i) (heE k i))) (a k)
    change ((B k i).card : ℚ) = _ at hh
    rw [hh]
    simp only [A, ZMod.card, Nat.cast_pow, div_eq_mul_inv, inv_pow]
    exact le_rfl
  have hbox : ∀ x : ∀ i, A i, ∃ k, ∀ i, x i ∈ B k i := by
    intro x
    let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) (fun i => p i ^ E i) Finset.univ
      (fun i _ => pow_ne_zero _ (NeZero.ne _))
      (fun i _ j _ hij => (hcop hij).pow _ _)
    have hz (i : ι) : (z.val : A i) = x i := by
      rw [← ZMod.natCast_zmod_val (x i)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
    obtain ⟨k, hk⟩ := hcover (z.val : ℤ)
    refine ⟨k, ?_⟩
    intro i
    have hpi : p i ^ e k i ∣ ∏ j, p j ^ e k j :=
      Finset.dvd_prod_of_mem (fun j => p j ^ e k j) (Finset.mem_univ i)
    have hpi' : ((p i ^ e k i : ℕ) : ℤ) ∣ ((∏ j, p j ^ e k j : ℕ) : ℤ) := by exact_mod_cast hpi
    have hqi := hpi'.trans hk
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hz i, map_natCast]
    symm
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (a k) (z.val : ℤ) (p i ^ e k i)).mpr hqi
  exact pure_power_box_sieve A p hp e he he0 B hB0 hBcard hbox

#print axioms coprime_power_cover_bound
end Erdos7Reduction

namespace Erdos7Reduction
open Finset

private theorem factorization_product_superset (m : ℕ) (hm : m ≠ 0)
    (P : Finset ℕ) (hP : m.primeFactors ⊆ P) :
    m = ∏ r ∈ P, r ^ m.factorization r := by
  have heq : m = ∏ r ∈ m.primeFactors, r ^ m.factorization r := by
    simpa only [Finsupp.prod, Nat.support_factorization] using
      (Nat.factorization_prod_pow_eq_self hm).symm
  nth_rw 1 [heq]
  apply Finset.prod_subset hP
  intro r _ hr
  have hzero : m.factorization r = 0 := by
    apply Finsupp.notMem_support_iff.mp
    rwa [Nat.support_factorization]
  simp [hzero]

private theorem sorted_four_odd_lower (p : Fin 4 → ℕ)
    (hp : ∀ i, 1 < p i) (ho : ∀ i, Odd (p i)) (hmono : StrictMono p) :
    ∀ i : Fin 4, 2 * (i : ℕ) + 3 ≤ p i := by
  have H (k : ℕ) : ∀ hk : k < 4, 2 * k + 3 ≤ p ⟨k, hk⟩ := by
    induction k with
    | zero =>
      intro hk
      have h2 := hp ⟨0, hk⟩
      have hodd := Nat.odd_iff.mp (ho ⟨0, hk⟩)
      omega
    | succ k ih =>
      intro hk
      have hk' : k < 4 := by omega
      have hprev := ih hk'
      have hinc := hmono (show (⟨k, hk'⟩ : Fin 4) < ⟨k+1, hk⟩ by simp)
      have ho1 := Nat.odd_iff.mp (ho ⟨k, hk'⟩)
      have ho2 := Nat.odd_iff.mp (ho ⟨k+1, hk⟩)
      omega
  exact fun i => H i.val i.isLt

set_option maxHeartbeats 1000000 in
private theorem four_capacity_lt_one :
    (∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset with 2 ≤ S.card,
      ∏ i ∈ S, (1 / ((2 * (i : ℕ) + 1 : ℕ) : ℚ))) < 1 := by
  let sets : Fin 11 → Finset (Fin 4) := ![{0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3},
        {0,1,2}, {0,1,3}, {0,2,3}, {1,2,3}, {0,1,2,3}]
  have hinj : Function.Injective sets := by decide
  let emb : Fin 11 ↪ Finset (Fin 4) := ⟨sets, hinj⟩
  have hsets : (Finset.univ : Finset (Fin 4)).powerset.filter (fun S => 2 ≤ S.card) =
      Finset.univ.map emb := by decide +revert
  rw [hsets, Finset.sum_map]
  norm_num [emb, sets, Fin.sum_univ_succ, Finset.prod_insert, Fin.ext_iff]

private theorem not_cover_four_odd_primes {κ : Type*} [Fintype κ]
    (P : Finset ℕ) (hPcard : P.card = 4) (hP : ∀ p ∈ P, p.Prime ∧ Odd p)
    (m : κ → ℕ) (a : κ → ℤ) (hm : ∀ k, 1 < m k) (hmi : Function.Injective m)
    (hPF : ∀ k, (m k).primeFactors ⊆ P)
    (hcover : ∀ x : ℤ, ∃ k, (m k : ℤ) ∣ x - a k) : False := by
  classical
  let p := P.orderEmbOfFin hPcard
  have hprime (i : Fin 4) : (p i).Prime := (hP _ (P.orderEmbOfFin_mem hPcard i)).1
  have hodd (i : Fin 4) : Odd (p i) := (hP _ (P.orderEmbOfFin_mem hPcard i)).2
  have hlower := sorted_four_odd_lower p (fun i => (hprime i).one_lt) hodd p.strictMono
  have hp (i : Fin 4) : 2 < p i := by have := hlower i; omega
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hprime i) (hprime j)).mpr (fun h => hij (p.injective h))
  let e (k : κ) (i : Fin 4) := (m k).factorization (p i)
  have hprod (k : κ) : m k = ∏ i, p i ^ e k i := by
    have heq := factorization_product_superset (m k) (by have := hm k; omega) P (hPF k)
    rw [heq]
    conv_lhs => rw [← P.map_orderEmbOfFin_univ hPcard]
    exact Finset.prod_map _ _ (fun r : ℕ => r ^ (m k).factorization r)
  have he : Function.Injective e := by
    intro k l hkl
    apply hmi
    rw [hprod k, hprod l, hkl]
  have he0 (k : κ) : ∃ i, e k i ≠ 0 := by
    by_contra h
    push_neg at h
    have hh := hm k
    rw [hprod k] at hh
    simp only [h, pow_zero, Finset.prod_const_one] at hh
    omega
  have hbound := coprime_power_cover_bound p hp hcop e he he0 a (by
    intro x
    obtain ⟨k, hk⟩ := hcover x
    exact ⟨k, by rwa [← hprod k]⟩)
  have hle : (∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset with 2 ≤ S.card,
      ∏ i ∈ S, (1 / (p i - 2 : ℚ))) ≤
      ∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset with 2 ≤ S.card,
        ∏ i ∈ S, (1 / ((2 * (i : ℕ) + 1 : ℕ) : ℚ)) := by
    apply Finset.sum_le_sum
    intro S _
    apply Finset.prod_le_prod
    · intro i _
      have hp' : (2 : ℚ) < p i := by exact_mod_cast hp i
      exact div_nonneg (by norm_num) (by linarith)
    · intro i _
      have hh : ((2 * (i : ℕ) + 3 : ℕ) : ℚ) ≤ p i := by exact_mod_cast hlower i
      apply one_div_le_one_div_of_le (by positivity)
      push_cast at hh ⊢
      linarith
  have hsmall : (∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset with 2 ≤ S.card,
      ∏ i ∈ S, (1 / ((2 * (i : ℕ) + 1 : ℕ) : ℚ))) < 1 := four_capacity_lt_one
  exact (not_lt_of_ge (hbound.trans hle)) hsmall

private theorem extend_odd_prime_set (P : Finset ℕ) (n : ℕ) (hcard : P.card ≤ n)
    (hP : ∀ p ∈ P, p.Prime ∧ Odd p) :
    ∃ T : Finset ℕ, P ⊆ T ∧ T.card = n ∧ ∀ p ∈ T, p.Prime ∧ Odd p := by
  classical
  let A : Set ℕ := {p | p.Prime} \ {2}
  have hA : A.Infinite := Nat.infinite_setOf_prime.diff (Set.finite_singleton 2)
  have hAP : (A \ (P : Set ℕ)).Infinite := hA.diff P.finite_toSet
  obtain ⟨U, hU, hUc⟩ := hAP.exists_subset_card_eq (n - P.card)
  have hdis : Disjoint P U := by
    apply Finset.disjoint_left.mpr
    intro p hp hu
    exact (hU hu).2 hp
  refine ⟨P ∪ U, Finset.subset_union_left, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdis, hUc]
    omega
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hP p hp
    · have hh := (hU hp).1
      exact ⟨hh.1, hh.1.odd_of_ne_two (by simpa using hh.2)⟩

/-- An odd arithmetic cover with distinct nontrivial moduli requires at least
five distinct prime factors, without any squarefreeness assumption. -/
theorem arithmetic_cover_prime_count {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hm : ∀ k, 1 < m k) (hm_inj : Function.Injective m)
    (hodd : ∀ k, Odd (m k))
    (hcover : ∀ x : ℤ, ∃ k, (m k : ℤ) ∣ x - a k) :
    5 ≤ (Finset.univ.biUnion (fun k => (m k).primeFactors)).card := by
  classical
  let P := Finset.univ.biUnion (fun k => (m k).primeFactors)
  have hP : ∀ p ∈ P, p.Prime ∧ Odd p := by
    intro p hp
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hp
    have hpf := Nat.mem_primeFactors.mp hk
    exact ⟨hpf.1, (hodd k).of_dvd_nat hpf.2.1⟩
  by_contra hc
  have hcard : P.card ≤ 4 := by dsimp [P]; omega
  obtain ⟨T, hPT, hTc, hT⟩ := extend_odd_prime_set P 4 hcard hP
  apply not_cover_four_odd_primes T hTc hT m a hm hm_inj _ hcover
  intro k p hp
  exact hPT (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hp⟩)

#print axioms arithmetic_cover_prime_count
end Erdos7Reduction

namespace Erdos7Reduction

/-- Any odd strict cover requires at least five distinct prime factors. -/
theorem cover_prime_count (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i, ¬ C.moduli i ≤ Ideal.span {2}) :
    letI := C.fintypeIndex
    5 ≤ (Finset.univ.biUnion (fun i => (C.moduli i).absNorm.primeFactors)).card := by
  letI := C.fintypeIndex
  exact arithmetic_cover_prime_count
    (fun i => (C.moduli i).absNorm) C.residue (moduli_absNorm_gt_one C)
    (moduli_absNorm_injective C) (fun i => (ideal_not_le_two_iff _).mp (hodd i))
    (arithmetic_cover C)

#print axioms cover_prime_count
end Erdos7Reduction

namespace Erdos7Reduction

/-- The prime-count obstruction and maximal-prime-exponent multiplicity give a
stronger lower bound on the number of classes. -/
theorem at_least_thirteen_moduli (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i, ¬ C.moduli i ≤ Ideal.span {2}) :
    letI := C.fintypeIndex
    13 ≤ Fintype.card C.ι := by
  classical
  letI := C.fintypeIndex
  obtain ⟨s, hs, hpriv⟩ := exists_irredundant_subcover C
  let m (i : ↥s) := (C.moduli i.val).absNorm
  let a (i : ↥s) := C.residue i.val
  have hm (i : ↥s) : 1 < m i := moduli_absNorm_gt_one C i.val
  have hmi : Function.Injective m := by
    intro i j hij
    apply Subtype.ext
    exact moduli_absNorm_injective C hij
  have ho (i : ↥s) : Odd (m i) := (ideal_not_le_two_iff _).mp (hodd i.val)
  have hc (x : ℤ) : ∃ i : ↥s, (m i : ℤ) ∣ x - a i := by
    obtain ⟨i, hi, hxi⟩ := hs x
    exact ⟨⟨i, hi⟩, (integer_coset_iff _ _ _).mp hxi⟩
  have hpr (i : ↥s) : ∃ x : ℤ, ∀ j : ↥s, j ≠ i → ¬ (m j : ℤ) ∣ x - a j := by
    obtain ⟨x, _, hx⟩ := hpriv i.val i.property
    refine ⟨x, ?_⟩
    intro j hji hdiv
    apply hx j.val j.property (fun h => hji (Subtype.ext h))
    exact (integer_coset_iff _ _ _).mpr hdiv
  let P := Finset.univ.biUnion (fun i : ↥s => (m i).primeFactors)
  have hcard : 5 ≤ P.card := arithmetic_cover_prime_count m a hm hmi ho hc
  have hex : ∃ p ∈ P, 13 ≤ p := by
    by_contra hh
    push_neg at hh
    have hsub : P ⊆ ({3, 5, 7, 11} : Finset ℕ) := by
      intro p hp
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
      have hpf := Nat.mem_primeFactors.mp hi
      have hpo := (ho i).of_dvd_nat hpf.2.1
      have hlt := hh p hp
      interval_cases p <;> (try norm_num at hpf) <;> (try norm_num at hpo) <;> norm_num
    have hle := Finset.card_le_card hsub
    norm_num at hle
    omega
  obtain ⟨p, hpP, hp13⟩ := hex
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hpP
  have hpf := Nat.mem_primeFactors.mp hi
  have hpN : p ∣ Finset.univ.lcm m := hpf.2.1.trans (Finset.dvd_lcm (Finset.mem_univ i))
  have hb := maximal_prime_exponent_multiplicity m a
    (fun i => by have := hm i; omega) hc hpr p hpf.1 hpN
  have hsubcard : Fintype.card {i : ↥s //
      (m i).factorization p = (Finset.univ.lcm m).factorization p} ≤ Fintype.card ↥s :=
    Fintype.card_subtype_le _
  have hsC : Fintype.card ↥s ≤ Fintype.card C.ι := by
    simpa only [Fintype.card_coe] using Finset.card_le_univ s
  exact hp13.trans (hb.trans (hsubcard.trans hsC))

#print axioms at_least_thirteen_moduli
end Erdos7Reduction



/- A reciprocal bound combined with prime-exponent multiplicity. -/
namespace Erdos7Reduction
open Set Pointwise

private theorem sorted_positive_odd_lower (s : Finset ℕ) (b : ℕ)
    (h : ∀ n ∈ s, b ≤ n ∧ Odd n) (i : Fin s.card) :
    2 * (i : ℕ) + b ≤ s.orderEmbOfFin rfl i := by
  have H (k : ℕ) : ∀ hk : k < s.card,
      2 * k + b ≤ s.orderEmbOfFin rfl ⟨k, hk⟩ := by
    induction k with
    | zero =>
      intro hk
      simpa using (h _ (s.orderEmbOfFin_mem rfl ⟨0, hk⟩)).1
    | succ k ih =>
      intro hk
      have hk' : k < s.card := by omega
      have hp := ih hk'
      have ht : s.orderEmbOfFin rfl ⟨k, hk'⟩ < s.orderEmbOfFin rfl ⟨k+1, hk⟩ :=
        (s.orderEmbOfFin rfl).strictMono (by simp)
      have ho₁ := Nat.odd_iff.mp (h _ (s.orderEmbOfFin_mem rfl ⟨k, hk'⟩)).2
      have ho₂ := Nat.odd_iff.mp (h _ (s.orderEmbOfFin_mem rfl ⟨k+1, hk⟩)).2
      omega
  exact H i.val i.isLt

/-- Distinct odd positive numbers have reciprocal sum bounded by the initial
odd numbers above a common lower bound. -/
theorem odd_reciprocal_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (m : ι → ℕ) (b N : ℕ) (hb : 0 < b)
    (hcard : s.card ≤ N) (hmi : Set.InjOn m s)
    (hm : ∀ i ∈ s, b ≤ m i ∧ Odd (m i)) :
    (∑ i ∈ s, (m i : ℚ)⁻¹) ≤
      ∑ j ∈ Finset.range N, ((2 * j + b : ℕ) : ℚ)⁻¹ := by
  classical
  let t := s.image m
  have htcard : t.card = s.card := Finset.card_image_iff.mpr hmi
  have ht : ∀ n ∈ t, b ≤ n ∧ Odd n := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    exact hm i hi
  have heq : (∑ i ∈ s, (m i : ℚ)⁻¹) =
      ∑ i : Fin t.card, (t.orderEmbOfFin rfl i : ℚ)⁻¹ := by
    rw [← Finset.sum_image (f := fun n : ℕ => (n : ℚ)⁻¹)
      (fun i hi j hj hij => hmi hi hj hij)]
    change (∑ n ∈ t, (n : ℚ)⁻¹) = _
    conv_lhs => rw [← t.map_orderEmbOfFin_univ rfl]
    exact Finset.sum_map _ _ _
  rw [heq]
  calc
    _ ≤ ∑ i : Fin t.card, ((2 * (i : ℕ) + b : ℕ) : ℚ)⁻¹ := by
      apply Finset.sum_le_sum
      intro i _
      have hi := sorted_positive_odd_lower t b ht i
      have hiq : (((2 * (i : ℕ) + b : ℕ) : ℚ)) ≤ (t.orderEmbOfFin rfl i : ℚ) := by
        exact_mod_cast hi
      have hpos : (0 : ℚ) < ((2 * (i : ℕ) + b : ℕ) : ℚ) := by
        exact_mod_cast (by omega : 0 < 2 * (i : ℕ) + b)
      simpa only [one_div] using one_div_le_one_div_of_le hpos hiq
    _ = ∑ j ∈ Finset.range t.card, ((2 * j + b : ℕ) : ℚ)⁻¹ :=
      Fin.sum_univ_eq_sum_range (fun j : ℕ => ((2 * j + b : ℕ) : ℚ)⁻¹) t.card
    _ ≤ ∑ j ∈ Finset.range N, ((2 * j + b : ℕ) : ℚ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (htcard.trans_le hcard))
      intro i _ _
      positivity

/-- Arithmetic version of the elementary necessary reciprocal density. -/
theorem arithmetic_density_necessary {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (a : ι → ℤ)
    (hcover : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i) :
    (1 : ℚ) ≤ ∑ i, (m i : ℚ)⁻¹ := by
  let H (i : ι) := (Ideal.span ({(m i : ℤ)} : Set ℤ)).toAddSubgroup
  have hc : ⋃ i ∈ (Finset.univ : Finset ι), a i +ᵥ (H i : Set ℤ) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left, Set.mem_univ, iff_true]
    obtain ⟨i, hi⟩ := hcover x
    refine ⟨i, ?_⟩
    have hx : x ∈ ({a i} : Set ℤ) + (Ideal.span ({(m i : ℤ)} : Set ℤ) : Set ℤ) :=
      (integer_coset_iff _ _ _).mpr (by simpa only [span_absNorm_nat] using hi)
    simpa only [Set.singleton_add] using hx
  have hi (i : ι) : (H i).index = m i := by
    change (Ideal.span ({(m i : ℤ)} : Set ℤ)).absNorm = m i
    exact span_absNorm_nat _
  have hd := AddSubgroup.one_le_sum_inv_index_of_leftCoset_cover hc
  simpa only [hi] using hd

/-- Thirteen distinct moduli divisible by a number at least thirteen, together
with at most four further odd nontrivial moduli, have density below one. -/
theorem density_lt_one_of_seventeen_of_thirteen_divisible
    {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hmi : Function.Injective m) (hm : ∀ i, 1 < m i ∧ Odd (m i))
    (hcard : Fintype.card ι ≤ 17) (p : ℕ) (hp : 13 ≤ p)
    (hcount : 13 ≤ Fintype.card {i // p ∣ m i}) :
    (∑ i, (m i : ℚ)⁻¹) < 1 := by
  classical
  let B := Finset.univ.filter (fun i => p ∣ m i)
  have hBc : 13 ≤ B.card := by simpa only [Fintype.card_subtype] using hcount
  obtain ⟨s, hsB, hsc⟩ := Finset.exists_subset_card_eq hBc
  have hsd (i : ι) (hi : i ∈ s) : p ∣ m i := (Finset.mem_filter.mp (hsB hi)).2
  have hsU : s ⊆ (Finset.univ : Finset ι) := Finset.subset_univ _
  have houtcard : (Finset.univ \ s).card ≤ 4 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hsc]
    omega
  have hout := odd_reciprocal_bound (Finset.univ \ s) m 3 4 (by omega)
    houtcard (hmi.injOn) (by
      intro i hi
      have hh := hm i
      have ho := Nat.odd_iff.mp hh.2
      exact ⟨by omega, hh.2⟩)
  let q (i : ι) := m i / p
  have hqmi : Set.InjOn q s := by
    intro i hi j hj hij
    apply hmi
    rw [← Nat.mul_div_cancel' (hsd i hi), ← Nat.mul_div_cancel' (hsd j hj)]
    exact congrArg (p * ·) hij
  have hq (i : ι) (hi : i ∈ s) : 1 ≤ q i ∧ Odd (q i) := by
    have hd := hsd i hi
    have he := Nat.mul_div_cancel' hd
    have hh := hm i
    refine ⟨?_, hh.2.of_dvd_nat (Nat.div_dvd_of_dvd hd)⟩
    dsimp only [q]
    by_contra h
    have hz : m i / p = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, mul_zero] at he
    omega
  have hqs := odd_reciprocal_bound s q 1 13 (by omega) (by omega) hqmi hq
  have hseq : (∑ i ∈ s, (m i : ℚ)⁻¹) =
      (p : ℚ)⁻¹ * ∑ i ∈ s, (q i : ℚ)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have he : (m i : ℚ) = (p : ℚ) * (q i : ℚ) := by
      exact_mod_cast (Nat.mul_div_cancel' (hsd i hi)).symm
    rw [he, mul_inv_rev, mul_comm]
  have hpq : (13 : ℚ) ≤ p := by exact_mod_cast hp
  have hpinv : (p : ℚ)⁻¹ ≤ (13 : ℚ)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 13) hpq
  have hsbound : (∑ i ∈ s, (m i : ℚ)⁻¹) ≤
      (13 : ℚ)⁻¹ * ∑ j ∈ Finset.range 13, ((2 * j + 1 : ℕ) : ℚ)⁻¹ := by
    rw [hseq]
    exact (mul_le_mul_of_nonneg_left hqs (by positivity)).trans
      (mul_le_mul_of_nonneg_right hpinv (by positivity))
  have hsum := Finset.sum_sdiff (f := fun i => (m i : ℚ)⁻¹) hsU
  have hnum : (∑ j ∈ Finset.range 4, ((2 * j + 3 : ℕ) : ℚ)⁻¹) +
      (13 : ℚ)⁻¹ * ∑ j ∈ Finset.range 13, ((2 * j + 1 : ℕ) : ℚ)⁻¹ < 1 := by
    norm_num [Finset.sum_range_succ]
  linarith

#print axioms odd_reciprocal_bound
#print axioms arithmetic_density_necessary
#print axioms density_lt_one_of_seventeen_of_thirteen_divisible
end Erdos7Reduction

namespace Erdos7Reduction

/-- An irredundant odd cover with distinct nontrivial moduli has a prime at
least thirteen that divides at least that many moduli. -/
theorem exists_large_prime_many_moduli {ι : Type} [Fintype ι]
    (m : ι → ℕ) (a : ι → ℤ) (hm : ∀ i, 1 < m i)
    (hmi : Function.Injective m) (ho : ∀ i, Odd (m i))
    (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i)
    (hpr : ∀ i, ∃ x : ℤ, ∀ j, j ≠ i → ¬ (m j : ℤ) ∣ x - a j) :
    ∃ p : ℕ, p.Prime ∧ 13 ≤ p ∧ p ≤ Fintype.card {i // p ∣ m i} := by
  classical
  let P := Finset.univ.biUnion (fun i => (m i).primeFactors)
  have hcard : 5 ≤ P.card := arithmetic_cover_prime_count m a hm hmi ho hc
  have hex : ∃ p ∈ P, 13 ≤ p := by
    by_contra hh
    push_neg at hh
    have hsub : P ⊆ ({3, 5, 7, 11} : Finset ℕ) := by
      intro p hp
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
      have hpf := Nat.mem_primeFactors.mp hi
      have hpo := (ho i).of_dvd_nat hpf.2.1
      have hlt := hh p hp
      interval_cases p <;> (try norm_num at hpf) <;> (try norm_num at hpo) <;> norm_num
    have hle := Finset.card_le_card hsub
    norm_num at hle
    omega
  obtain ⟨p, hpP, hp13⟩ := hex
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hpP
  have hpf := Nat.mem_primeFactors.mp hi
  have hpN : p ∣ Finset.univ.lcm m := hpf.2.1.trans (Finset.dvd_lcm (Finset.mem_univ i))
  have hnonzero (i : ι) : m i ≠ 0 := by have := hm i; omega
  have hN : Finset.univ.lcm m ≠ 0 := Finset.lcm_ne_zero_iff.mpr (by simpa using hnonzero)
  have hb := maximal_prime_exponent_multiplicity m a hnonzero hc hpr p hpf.1 hpN
  have hfac := hpf.1.factorization_pos_of_dvd hN hpN
  have hcount : Fintype.card {i : ι //
      (m i).factorization p = (Finset.univ.lcm m).factorization p} ≤
      Fintype.card {i : ι // p ∣ m i} := by
    apply Fintype.card_subtype_mono
    intro j hj
    exact Nat.dvd_of_factorization_pos (by rw [hj]; omega)
  exact ⟨p, hpf.1, hp13, hb.trans hcount⟩

/-- Every odd strict covering system needs at least eighteen moduli. -/
theorem at_least_eighteen_moduli (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i, ¬ C.moduli i ≤ Ideal.span {2}) :
    letI := C.fintypeIndex
    18 ≤ Fintype.card C.ι := by
  classical
  letI := C.fintypeIndex
  by_contra hcard
  have hcard' : Fintype.card C.ι ≤ 17 := by omega
  obtain ⟨s, hs, hpriv⟩ := exists_irredundant_subcover C
  let m (i : ↥s) := (C.moduli i.val).absNorm
  let a (i : ↥s) := C.residue i.val
  have hm (i : ↥s) : 1 < m i := moduli_absNorm_gt_one C i.val
  have hmi : Function.Injective m := by
    intro i j hij
    apply Subtype.ext
    exact moduli_absNorm_injective C hij
  have ho (i : ↥s) : Odd (m i) := (ideal_not_le_two_iff _).mp (hodd i.val)
  have hc (x : ℤ) : ∃ i : ↥s, (m i : ℤ) ∣ x - a i := by
    obtain ⟨i, hi, hxi⟩ := hs x
    exact ⟨⟨i, hi⟩, (integer_coset_iff _ _ _).mp hxi⟩
  have hpr (i : ↥s) : ∃ x : ℤ, ∀ j : ↥s, j ≠ i → ¬ (m j : ℤ) ∣ x - a j := by
    obtain ⟨x, _, hx⟩ := hpriv i.val i.property
    refine ⟨x, ?_⟩
    intro j hji hdiv
    apply hx j.val j.property (fun h => hji (Subtype.ext h))
    exact (integer_coset_iff _ _ _).mpr hdiv
  obtain ⟨p, _, hp13, hpmult⟩ := exists_large_prime_many_moduli m a hm hmi ho hc hpr
  have hsC : Fintype.card ↥s ≤ 17 := by
    calc
      Fintype.card ↥s ≤ Fintype.card C.ι := by
        simpa only [Fintype.card_coe] using Finset.card_le_univ s
      _ ≤ 17 := hcard'
  have hsmall := density_lt_one_of_seventeen_of_thirteen_divisible m hmi
    (fun i => ⟨hm i, ho i⟩) hsC p hp13 (hp13.trans hpmult)
  exact (not_lt_of_ge (arithmetic_density_necessary m a hc)) hsmall

#print axioms exists_large_prime_many_moduli
#print axioms at_least_eighteen_moduli
end Erdos7Reduction



/- Restricting a covering system to a prime residue class without creating
repeated moduli. -/
namespace Erdos7Reduction

/-- The modulus after substituting `x = p*y + r`. -/
def primeReducedMod (p m : ℕ) : ℕ := if p ∣ m then m / p else m

private theorem affine_residue_pullback (p m : ℕ) (a r : ℤ)
    (hp : p.Prime) (hcompat : p ∣ m → (p : ℤ) ∣ a - r) :
    ∃ b : ℤ, ∀ y : ℤ, (m : ℤ) ∣ (p : ℤ) * y + r - a →
      (primeReducedMod p m : ℤ) ∣ y - b := by
  by_cases hpm : p ∣ m
  · obtain ⟨b, hb⟩ := hcompat hpm
    refine ⟨b, fun y hy => ?_⟩
    rw [primeReducedMod, if_pos hpm]
    have hm : (m : ℤ) = (p : ℤ) * (m / p : ℕ) := by
      exact_mod_cast (Nat.mul_div_cancel' hpm).symm
    have hh : (p : ℤ) * (m / p : ℕ) ∣ (p : ℤ) * (y - b) := by
      rw [← hm]
      convert hy using 1 <;> nlinarith
    exact (Int.mul_dvd_mul_iff_left (by exact_mod_cast hp.ne_zero)).mp hh
  · obtain ⟨u, v, huv⟩ := ((hp.coprime_iff_not_dvd).mpr hpm).isCoprime
    refine ⟨u * (a - r), fun y hy => ?_⟩
    rw [primeReducedMod, if_neg hpm]
    have h₁ := dvd_mul_of_dvd_right hy u
    have h₂ : (m : ℤ) ∣ (m : ℤ) * (v * y) := dvd_mul_right _ _
    have he : u * ((p : ℤ) * y + r - a) + (m : ℤ) * (v * y) =
        y - u * (a - r) := by
      have hh := congrArg (fun z : ℤ => z * y) huv
      dsimp only at hh
      nlinarith
    rw [← he]
    exact dvd_add h₁ h₂

/-- If fewer than `p-1` original moduli are prime to `p`, some residue class
avoids both a unit reduced modulus and every collision after reduction. -/
theorem exists_collision_free_prime_residue {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (a : ι → ℤ) (hmi : Function.Injective m)
    (p : ℕ) (hp : p.Prime)
    (hsmall : Fintype.card {i // ¬ p ∣ m i} + 1 < p) :
    ∃ r : ZMod p, ∀ i, p ∣ m i → (a i : ZMod p) = r →
      m i / p ≠ 1 ∧ ∀ j, ¬ p ∣ m j → m i / p ≠ m j := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  let A := Finset.univ.filter (fun i => ¬ p ∣ m i)
  let T := insert 1 (A.image m)
  let B := Finset.univ.filter (fun i => p ∣ m i ∧ m i / p ∈ T)
  have hBcard : B.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun i => m i / p)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2.2
    · intro i hi j hj hij
      apply hmi
      have hi' := (Finset.mem_filter.mp hi).2.1
      have hj' := (Finset.mem_filter.mp hj).2.1
      rw [← Nat.mul_div_cancel' hi', ← Nat.mul_div_cancel' hj']
      exact congrArg (p * ·) hij
  have hTcard : T.card ≤ Fintype.card {i // ¬ p ∣ m i} + 1 := by
    have hh := Finset.card_insert_le 1 (A.image m)
    simpa only [T, A, Finset.card_image_of_injective _ hmi,
      Fintype.card_subtype] using hh
  let R := B.image (fun i => (a i : ZMod p))
  have hRcard : R.card < p :=
    (Finset.card_image_le.trans (hBcard.trans hTcard)).trans_lt hsmall
  have hex : ∃ r : ZMod p, r ∉ R := by
    by_contra h
    push_neg at h
    have hh : (Finset.univ : Finset (ZMod p)) ⊆ R := by intro r _; exact h r
    have hb := Finset.card_le_card hh
    have he : Fintype.card (ZMod p) = p := ZMod.card p
    simp only [Finset.card_univ, he] at hb
    omega
  obtain ⟨r, hr⟩ := hex
  refine ⟨r, fun i hpi hai => ?_⟩
  have hiB : i ∉ B := by
    intro hi
    apply hr
    exact Finset.mem_image.mpr ⟨i, hi, hai⟩
  have hiT : m i / p ∉ T := by
    intro hi
    exact hiB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpi, hi⟩)
  refine ⟨fun h => hiT (Finset.mem_insert.mpr (Or.inl h)), ?_⟩
  intro j hpj hij
  apply hiT
  apply Finset.mem_insert.mpr
  right
  exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpj⟩, hij.symm⟩

/-- A collision-free prime residue restriction preserves distinct, nontrivial,
odd moduli and divides a common period by the prime. -/
theorem restrict_odd_cover_to_prime_residue {ι : Type} [Fintype ι]
    (m : ι → ℕ) (a : ι → ℤ) (hm : ∀ i, 1 < m i ∧ Odd (m i))
    (hmi : Function.Injective m) (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i)
    (N p : ℕ) (hp : p.Prime) (hpN : p ∣ N) (hmN : ∀ i, m i ∣ N)
    (r : ZMod p)
    (hsafe : ∀ i, p ∣ m i → (a i : ZMod p) = r →
      m i / p ≠ 1 ∧ ∀ j, ¬ p ∣ m j → m i / p ≠ m j) :
    ∃ (κ : Type) (_ : Fintype κ) (n : κ → ℕ) (b : κ → ℤ),
      Function.Injective n ∧ (∀ i, 1 < n i ∧ Odd (n i)) ∧
      (∀ y : ℤ, ∃ i, (n i : ℤ) ∣ y - b i) ∧
      (∀ i, n i ∣ N / p) ∧ Fintype.card κ ≤ Fintype.card ι := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  let active (i : ι) := ¬ p ∣ m i ∨ (a i : ZMod p) = r
  let κ := {i : ι // active i}
  let n (i : κ) := primeReducedMod p (m i.val)
  have hres (i : κ) : p ∣ m i.val → (p : ℤ) ∣ a i.val - (r.val : ℤ) := by
    intro hpi
    have ha := i.property.resolve_left (not_not.mpr hpi)
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub (r.val : ℤ) (a i.val) p).mp
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using ha.symm
  choose b hb using fun i : κ => affine_residue_pullback p (m i.val) (a i.val)
    (r.val : ℤ) hp (hres i)
  refine ⟨κ, inferInstance, n, b, ?_, ?_, ?_, ?_, Fintype.card_subtype_le _⟩
  · intro i j hij
    apply Subtype.ext
    dsimp only [n, primeReducedMod] at hij
    by_cases hi : p ∣ m i.val <;> by_cases hj : p ∣ m j.val
    · simp only [if_pos hi, if_pos hj] at hij
      apply hmi
      rw [← Nat.mul_div_cancel' hi, ← Nat.mul_div_cancel' hj]
      exact congrArg (p * ·) hij
    · simp only [if_pos hi, if_neg hj] at hij
      exact False.elim ((hsafe i.val hi (i.property.resolve_left (not_not.mpr hi))).2
        j.val hj hij)
    · simp only [if_neg hi, if_pos hj] at hij
      exact False.elim ((hsafe j.val hj (j.property.resolve_left (not_not.mpr hj))).2
        i.val hi hij.symm)
    · simp only [if_neg hi, if_neg hj] at hij
      exact hmi hij
  · intro i
    dsimp only [n, primeReducedMod]
    by_cases hi : p ∣ m i.val
    · rw [if_pos hi]
      have hn1 := (hsafe i.val hi (i.property.resolve_left (not_not.mpr hi))).1
      have hn0 : m i.val / p ≠ 0 := by
        intro hz
        have he := Nat.mul_div_cancel' hi
        rw [hz, mul_zero] at he
        have hh := (hm i.val).1
        omega
      exact ⟨lt_of_le_of_ne (Nat.pos_of_ne_zero hn0) hn1.symm,
        (hm i.val).2.of_dvd_nat (Nat.div_dvd_of_dvd hi)⟩
    · simpa only [if_neg hi] using hm i.val
  · intro y
    obtain ⟨i, hi⟩ := hc ((p : ℤ) * y + r.val)
    have hact : active i := by
      by_cases hpi : p ∣ m i
      · right
        have hpi' : (p : ℤ) ∣ (m i : ℤ) := by exact_mod_cast hpi
        have hd : (p : ℤ) ∣ (r.val : ℤ) - a i := by
          have hh := dvd_sub (hpi'.trans hi) (dvd_mul_right (p : ℤ) y)
          convert hh using 1 <;> ring
        have hh := (ZMod.intCast_eq_intCast_iff_dvd_sub (a i) (r.val : ℤ) p).mpr hd
        simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hh
      · exact Or.inl hpi
    exact ⟨⟨i, hact⟩, hb ⟨i, hact⟩ y hi⟩
  · intro i
    dsimp only [n, primeReducedMod]
    by_cases hi : p ∣ m i.val
    · rw [if_pos hi]
      exact Nat.div_dvd_div hi (hmN i.val)
    · rw [if_neg hi]
      apply ((hp.coprime_iff_not_dvd.mpr hi).symm).dvd_of_dvd_mul_left
      rw [Nat.mul_div_cancel' hpN]
      exact hmN i.val

#print axioms exists_collision_free_prime_residue
#print axioms restrict_odd_cover_to_prime_residue
end Erdos7Reduction

namespace Erdos7Reduction

/-- A finite arithmetic cover has an irredundant subcover. -/
theorem arithmetic_irredundant_subcover {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (a : ι → ℤ)
    (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i) :
    ∃ s : Finset ι,
      (∀ x : ℤ, ∃ i ∈ s, (m i : ℤ) ∣ x - a i) ∧
      (∀ i ∈ s, ∃ x : ℤ, ∀ j ∈ s, j ≠ i → ¬ (m j : ℤ) ∣ x - a j) := by
  classical
  let P (s : Finset ι) := ∀ x : ℤ, ∃ i ∈ s, (m i : ℤ) ∣ x - a i
  have hP : P Finset.univ := by
    intro x
    obtain ⟨i, hi⟩ := hc x
    exact ⟨i, Finset.mem_univ i, hi⟩
  obtain ⟨s, hs⟩ := exists_minimal_of_wellFoundedLT P ⟨Finset.univ, hP⟩
  refine ⟨s, hs.prop, ?_⟩
  intro i hi
  have hn : ¬ P (s.erase i) := by
    intro h
    exact Finset.notMem_erase i s (hs.le_of_le h (Finset.erase_subset i s) hi)
  change ¬ (∀ x : ℤ, ∃ j ∈ s.erase i, (m j : ℤ) ∣ x - a j) at hn
  push_neg at hn
  obtain ⟨x, hx⟩ := hn
  exact ⟨x, fun j hj hji => hx j (Finset.mem_erase.mpr ⟨hji, hj⟩)⟩

/-- The parameter `N` is a positive common period, not necessarily the lcm. -/
def HasOddArithmeticCover (N K : ℕ) : Prop :=
  0 < N ∧ ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ) (a : ι → ℤ),
    Function.Injective m ∧ (∀ i, 1 < m i ∧ Odd (m i)) ∧
    (∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i) ∧
    (∀ i, m i ∣ N) ∧ Fintype.card ι ≤ K

/-- The prime restriction and the five-prime obstruction exclude all covers
with at most twenty-four classes. -/
theorem not_hasOddArithmeticCover_twentyfour (N : ℕ) :
    ¬ HasOddArithmeticCover N 24 := by
  classical
  intro h
  have hex : ∃ M, HasOddArithmeticCover M 24 := ⟨N, h⟩
  let M := Nat.find hex
  obtain ⟨hM, ι, fι, m, a, hmi, hm, hc, hmM, hcard⟩ := Nat.find_spec hex
  letI : Fintype ι := fι
  change 0 < M at hM
  change ∀ i, m i ∣ M at hmM
  obtain ⟨s, hs, hpriv⟩ := arithmetic_irredundant_subcover m a hc
  let n (i : ↥s) := m i.val
  let b (i : ↥s) := a i.val
  have hnmi : Function.Injective n := by
    intro i j hij
    exact Subtype.ext (hmi hij)
  have hn (i : ↥s) : 1 < n i ∧ Odd (n i) := hm i.val
  have hnc (x : ℤ) : ∃ i : ↥s, (n i : ℤ) ∣ x - b i := by
    obtain ⟨i, hi, hxi⟩ := hs x
    exact ⟨⟨i, hi⟩, hxi⟩
  have hnpr (i : ↥s) : ∃ x : ℤ, ∀ j : ↥s, j ≠ i → ¬ (n j : ℤ) ∣ x - b j := by
    obtain ⟨x, hx⟩ := hpriv i.val i.property
    refine ⟨x, fun j hji => ?_⟩
    exact hx j.val j.property (fun h => hji (Subtype.ext h))
  have hncard : Fintype.card ↥s ≤ 24 := by
    calc
      Fintype.card ↥s ≤ Fintype.card ι := by
        simpa only [Fintype.card_coe] using Finset.card_le_univ s
      _ ≤ 24 := hcard
  obtain ⟨p, hp, hp13, hcount⟩ := exists_large_prime_many_moduli n b
    (fun i => (hn i).1) hnmi (fun i => (hn i).2) hnc hnpr
  have hpM : p ∣ M := by
    have hpos : 0 < Fintype.card {i : ↥s // p ∣ n i} := by omega
    obtain ⟨i⟩ := Fintype.card_pos_iff.mp hpos
    exact i.property.trans (hmM i.val.val)
  have hsmall : Fintype.card {i : ↥s // ¬ p ∣ n i} + 1 < p := by
    rw [Fintype.card_subtype_compl]
    omega
  obtain ⟨r, hr⟩ := exists_collision_free_prime_residue n b hnmi p hp hsmall
  obtain ⟨κ, fκ, n', b', hinj, hodd, hcov, hdiv, hc'⟩ :=
    restrict_odd_cover_to_prime_residue n b hn hnmi hnc M p hp hpM
      (fun i => hmM i.val) r hr
  letI : Fintype κ := fκ
  have hnew : HasOddArithmeticCover (M / p) 24 := by
    refine ⟨Nat.div_pos (Nat.le_of_dvd hM hpM) hp.pos,
      κ, fκ, n', b', hinj, hodd, hcov, hdiv, hc'.trans hncard⟩
  have hmin : M ≤ M / p := Nat.find_min' hex hnew
  exact (not_lt_of_ge hmin) (Nat.div_lt_self hM hp.one_lt)

/-- Every odd strict covering system needs at least twenty-five moduli. -/
theorem at_least_twentyfive_moduli (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i, ¬ C.moduli i ≤ Ideal.span {2}) :
    letI := C.fintypeIndex
    25 ≤ Fintype.card C.ι := by
  classical
  letI := C.fintypeIndex
  by_contra hc
  have hcard : Fintype.card C.ι ≤ 24 := by omega
  let m (i : C.ι) := (C.moduli i).absNorm
  let N := Finset.univ.lcm m
  have hn (i : C.ι) : m i ≠ 0 := by
    have hh := moduli_absNorm_gt_one C i
    dsimp only [m]
    omega
  have hN : 0 < N := Nat.pos_of_ne_zero
    (Finset.lcm_ne_zero_iff.mpr (by simpa using hn))
  apply not_hasOddArithmeticCover_twentyfour N
  exact ⟨hN, C.ι, C.fintypeIndex, m, C.residue, moduli_absNorm_injective C,
    fun i => ⟨moduli_absNorm_gt_one C i, (ideal_not_le_two_iff _).mp (hodd i)⟩,
    arithmetic_cover C, fun i => Finset.dvd_lcm (Finset.mem_univ i), hcard⟩

#print axioms arithmetic_irredundant_subcover
#print axioms not_hasOddArithmeticCover_twentyfour
#print axioms at_least_twentyfive_moduli
end Erdos7Reduction

namespace Erdos7Reduction

/-- In a cover whose positive common period is minimal under a cardinality
bound, every residue modulo a prime factor must create either a unit modulus
or a collision between an original modulus `m` and `p*m`. -/
theorem minimal_period_forces_collision_in_every_residue
    {ι : Type} [Fintype ι] (m : ι → ℕ) (a : ι → ℤ)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (hmi : Function.Injective m)
    (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i)
    (N K p : ℕ) (hN : 0 < N) (hp : p.Prime) (hpN : p ∣ N)
    (hmN : ∀ i, m i ∣ N) (hcard : Fintype.card ι ≤ K)
    (hmin : ∀ M, M < N → ¬ HasOddArithmeticCover M K) (r : ZMod p) :
    ∃ i, p ∣ m i ∧ (a i : ZMod p) = r ∧
      (m i / p = 1 ∨ ∃ j, ¬ p ∣ m j ∧ m i / p = m j) := by
  classical
  by_contra h
  have hsafe : ∀ i, p ∣ m i → (a i : ZMod p) = r →
      m i / p ≠ 1 ∧ ∀ j, ¬ p ∣ m j → m i / p ≠ m j := by
    intro i hi hai
    refine ⟨fun h₁ => h ⟨i, hi, hai, Or.inl h₁⟩, ?_⟩
    intro j hj hij
    exact h ⟨i, hi, hai, Or.inr ⟨j, hj, hij⟩⟩
  obtain ⟨κ, fκ, n, b, hninj, hn, hcov, hdiv, hc'⟩ :=
    restrict_odd_cover_to_prime_residue m a hm hmi hc N p hp hpN hmN r hsafe
  exact hmin (N / p) (Nat.div_lt_self hN hp.one_lt)
    ⟨Nat.div_pos (Nat.le_of_dvd hN hpN) hp.pos,
      κ, fκ, n, b, hninj, hn, hcov, hdiv, hc'.trans hcard⟩

#print axioms minimal_period_forces_collision_in_every_residue
end Erdos7Reduction



/- Divisor-closed reductions for hypothetical odd covering systems. -/
namespace Erdos7Reduction

/-- The arithmetic form of an odd strict cover, on a fixed finite index type. -/
def IsOddArithmeticCover {ι : Type*} (m : ι → ℕ) (a : ι → ℤ) : Prop :=
  Function.Injective m ∧ (∀ i, 1 < m i ∧ Odd (m i)) ∧
    ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i

/-- Replacing a modulus by a missing nontrivial divisor preserves an odd strict
cover. No change of residues is needed. -/
theorem replace_modulus_by_divisor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (a : ι → ℤ) (hc : IsOddArithmeticCover m a)
    (i : ι) (d : ℕ) (hd : 1 < d) (hdm : d ∣ m i)
    (hmissing : ∀ j, m j ≠ d) :
    IsOddArithmeticCover (Function.update m i d) a ∧
      (∑ j, Function.update m i d j) < ∑ j, m j := by
  obtain ⟨hmi, hm, hcov⟩ := hc
  have hlt : d < m i := Nat.lt_of_le_of_ne
    (Nat.le_of_dvd (by have := (hm i).1; omega) hdm) (hmissing i).symm
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro j k hjk
      by_cases hji : j = i <;> by_cases hki : k = i
      · exact hji.trans hki.symm
      · subst j
        have h : d = m k := by simpa [hki] using hjk
        exact False.elim (hmissing k h.symm)
      · subst k
        have h : m j = d := by simpa [hji] using hjk
        exact False.elim (hmissing j h)
      · apply hmi
        simpa [hji, hki] using hjk
    · intro j
      by_cases hji : j = i
      · subst j
        simpa using (show 1 < d ∧ Odd d from ⟨hd, (hm i).2.of_dvd_nat hdm⟩)
      · simpa [hji] using hm j
    · intro x
      obtain ⟨j, hj⟩ := hcov x
      refine ⟨j, ?_⟩
      by_cases hji : j = i
      · subst j
        have hd' : (d : ℤ) ∣ (m i : ℤ) := by exact_mod_cast hdm
        simpa using hd'.trans hj
      · simpa [hji] using hj
  · rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    have hs := Finset.sum_erase_add (Finset.univ : Finset ι) m (Finset.mem_univ i)
    have he : (Finset.univ : Finset ι) \ {i} = Finset.univ.erase i := by ext j; simp
    rw [he]
    omega

/-- Among odd covers on a fixed finite index type and with a given common
period, one can choose one whose moduli contain every nontrivial divisor of
each modulus. Its sum of moduli is no larger than the original sum. -/
theorem exists_divisor_closed_odd_cover {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (a : ι → ℤ) (hc : IsOddArithmeticCover m a)
    (N : ℕ) (hmN : ∀ i, m i ∣ N) :
    ∃ (n : ι → ℕ) (b : ι → ℤ), IsOddArithmeticCover n b ∧
      (∀ i, n i ∣ N) ∧ (∑ i, n i) ≤ ∑ i, m i ∧
      ∀ i d, 1 < d → d ∣ n i → ∃ j, n j = d := by
  classical
  let P (W : ℕ) := ∃ (n : ι → ℕ) (b : ι → ℤ), IsOddArithmeticCover n b ∧
    (∀ i, n i ∣ N) ∧ ∑ i, n i = W
  have hex : ∃ W, P W := ⟨∑ i, m i, m, a, hc, hmN, rfl⟩
  obtain ⟨n, b, hn, hnN, hsum⟩ := Nat.find_spec hex
  refine ⟨n, b, hn, hnN, ?_, ?_⟩
  · rw [hsum]
    exact Nat.find_min' hex ⟨m, a, hc, hmN, rfl⟩
  · intro i d hd hdi
    by_contra h
    push_neg at h
    obtain ⟨hnew, hlt⟩ := replace_modulus_by_divisor n b hn i d hd hdi h
    have hnewN : ∀ j, Function.update n i d j ∣ N := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa using hdi.trans (hnN i)
      · simpa [hji] using hnN j
    have hP : P (∑ j, Function.update n i d j) :=
      ⟨Function.update n i d, b, hnew, hnewN, rfl⟩
    have hmin := Nat.find_min' hex hP
    omega

/-- In a divisor-closed strict system, the divisor count of each modulus is
bounded by the number of classes plus one. -/
theorem divisor_count_le_card_add_one {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (hm : ∀ i, 1 < m i)
    (hclosed : ∀ i d, 1 < d → d ∣ m i → ∃ j, m j = d) (i : ι) :
    (m i).divisors.card ≤ Fintype.card ι + 1 := by
  classical
  have hmi0 : m i ≠ 0 := by have := hm i; omega
  have hsub : (m i).divisors ⊆ insert 1 (Finset.univ.image m) := by
    intro d hd
    obtain ⟨hdiv, _⟩ := Nat.mem_divisors.mp hd
    by_cases hd1 : d = 1
    · exact Finset.mem_insert.mpr (Or.inl hd1)
    · have hd0 : d ≠ 0 := by
        intro hzero
        rw [hzero, zero_dvd_iff] at hdiv
        exact hmi0 hdiv
      have hdgt : 1 < d := by omega
      obtain ⟨j, hj⟩ := hclosed i d hdgt hdiv
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩))
  calc
    _ ≤ (insert 1 (Finset.univ.image m)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.image m).card + 1 := Finset.card_insert_le _ _
    _ ≤ Fintype.card ι + 1 := by
      have hh := Finset.card_image_le (s := (Finset.univ : Finset ι)) (f := m)
      simpa only [Finset.card_univ] using Nat.add_le_add_right hh 1

#print axioms replace_modulus_by_divisor
#print axioms exists_divisor_closed_odd_cover
#print axioms divisor_count_le_card_add_one
end Erdos7Reduction

namespace Erdos7Reduction

/-- A hypothetical odd cover can be made both irredundant and divisor-closed
without increasing its cardinality or its common period. -/
theorem exists_irredundant_divisor_closed_odd_cover (N K : ℕ)
    (h : HasOddArithmeticCover N K) :
    ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ) (a : ι → ℤ),
      IsOddArithmeticCover m a ∧ (∀ i, m i ∣ N) ∧ Fintype.card ι ≤ K ∧
      (∀ i d, 1 < d → d ∣ m i → ∃ j, m j = d) ∧
      (∀ i, ∃ x : ℤ, ∀ j, j ≠ i → ¬ (m j : ℤ) ∣ x - a j) := by
  classical
  have hex : ∃ k, HasOddArithmeticCover N k := ⟨K, h⟩
  obtain ⟨hN, ι, fι, m, a, hmi, hm, hc, hmN, hcard⟩ := Nat.find_spec hex
  letI : Fintype ι := fι
  obtain ⟨n, b, hn, hnN, _, hclosed⟩ :=
    exists_divisor_closed_odd_cover m a ⟨hmi, hm, hc⟩ N hmN
  have hcardK : Fintype.card ι ≤ K := hcard.trans (Nat.find_min' hex h)
  refine ⟨ι, fι, n, b, hn, hnN, hcardK, hclosed, ?_⟩
  intro i
  by_contra hpriv
  push_neg at hpriv
  let κ := {j : ι // j ≠ i}
  have hκcard : Fintype.card κ < Fintype.card ι :=
    Fintype.card_subtype_lt (by simp : ¬ i ≠ i)
  have hnew : HasOddArithmeticCover N (Fintype.card κ) := by
    refine ⟨hN, κ, inferInstance, (fun j : κ => n j.val),
      (fun j : κ => b j.val), ?_, ?_, ?_, ?_, le_rfl⟩
    · intro j k hjk
      exact Subtype.ext (hn.1 hjk)
    · intro j
      exact hn.2.1 j.val
    · intro x
      obtain ⟨j, hji, hj⟩ := hpriv x
      exact ⟨⟨j, hji⟩, hj⟩
    · intro j
      exact hnN j.val
  have hmin := Nat.find_min' hex hnew
  omega

/-- In an irredundant cover, a class cannot meet a class with a proper divisor
modulus. This arithmetic form does not need oddness. -/
theorem residue_not_congruent_of_proper_modulus_divisor
    {ι : Type*} (m : ι → ℕ) (a : ι → ℤ)
    (hpriv : ∀ i, ∃ x : ℤ, ∀ j, j ≠ i → ¬ (m j : ℤ) ∣ x - a j)
    (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i)
    {i j : ι} (hji : j ≠ i) (hd : m j ∣ m i) :
    ¬ (m j : ℤ) ∣ a i - a j := by
  intro hcong
  obtain ⟨x, hx⟩ := hpriv i
  obtain ⟨k, hk⟩ := hc x
  have hki : k = i := by
    by_contra h
    exact hx k h hk
  subst k
  have hd' : (m j : ℤ) ∣ (m i : ℤ) := by exact_mod_cast hd
  have hh := dvd_add (hd'.trans hk) hcong
  apply hx j hji
  convert hh using 1 <;> ring

#print axioms exists_irredundant_divisor_closed_odd_cover
#print axioms residue_not_congruent_of_proper_modulus_divisor
end Erdos7Reduction

namespace Erdos7Reduction

/-- Distinct prime-modulus classes can be simultaneously translated to zero. -/
theorem exists_prime_residue_normalization {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (a : ι → ℤ) (hmi : Function.Injective m) :
    ∃ z : ℤ, ∀ i, (m i).Prime → (m i : ℤ) ∣ a i - z := by
  classical
  let P := Finset.univ.filter (fun i => (m i).Prime)
  let r (i : ι) := (a i % (m i : ℤ)).toNat
  have hp (i : ι) (hi : i ∈ P) : (m i).Prime := (Finset.mem_filter.mp hi).2
  have hne : ∀ i ∈ P, m i ≠ 0 := fun i hi => (hp i hi).ne_zero
  have hcop : (P : Set ι).Pairwise (Function.onFun Nat.Coprime m) := by
    intro i hi j hj hij
    exact (Nat.coprime_primes (hp i hi) (hp j hj)).mpr (fun heq => hij (hmi heq))
  let z := Nat.chineseRemainderOfFinset r m P hne hcop
  refine ⟨(z.val : ℤ), ?_⟩
  intro i hpi
  have hi : i ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpi⟩
  have hr : (r i : ℤ) = a i % (m i : ℤ) := by
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hpi.ne_zero))
  have hz : (m i : ℤ) ∣ (r i : ℤ) - (z.val : ℤ) := (z.property i hi).dvd
  rw [hr] at hz
  have ha : (m i : ℤ) ∣ a i - a i % (m i : ℤ) := by
    refine ⟨a i / (m i : ℤ), ?_⟩
    have he := Int.emod_add_ediv (a i) (m i : ℤ)
    omega
  convert dvd_add ha hz using 1 <;> ring

/-- In an irredundant, divisor-closed cover, every composite-modulus residue
is a unit after the prime-modulus residues have been translated to zero. -/
theorem composite_residues_coprime_after_normalization
    {ι : Type*} [Fintype ι] (m : ι → ℕ) (a : ι → ℤ)
    (hc : IsOddArithmeticCover m a)
    (hclosed : ∀ i d, 1 < d → d ∣ m i → ∃ j, m j = d)
    (hpriv : ∀ i, ∃ x : ℤ, ∀ j, j ≠ i → ¬ (m j : ℤ) ∣ x - a j) :
    ∃ z : ℤ, (∀ i, (m i).Prime → (m i : ℤ) ∣ a i - z) ∧
      (∀ i, ¬ (m i).Prime → IsCoprime (a i - z) (m i : ℤ)) ∧
      IsOddArithmeticCover m (fun i => a i - z) := by
  classical
  obtain ⟨z, hz⟩ := exists_prime_residue_normalization m a hc.1
  refine ⟨z, hz, ?_, hc.1, hc.2.1, ?_⟩
  · intro i hni
    apply Int.isCoprime_iff_nat_coprime.mpr
    simp only [Int.natAbs_natCast]
    apply Nat.Coprime.symm
    apply Nat.coprime_of_dvd
    intro p hp hpm hpa
    obtain ⟨j, hj⟩ := hclosed i p hp.one_lt hpm
    have hji : j ≠ i := by
      intro h
      subst j
      exact hni (hj.symm ▸ hp)
    have hcong := residue_not_congruent_of_proper_modulus_divisor m a hpriv hc.2.2
      hji (by rwa [hj])
    have hjprime : (m j).Prime := hj.symm ▸ hp
    have hjz := hz j hjprime
    have hiaz : (m j : ℤ) ∣ a i - z := by
      rw [hj]
      exact Int.natCast_dvd.mpr hpa
    apply hcong
    convert dvd_sub hiaz hjz using 1 <;> ring
  · intro x
    obtain ⟨i, hi⟩ := hc.2.2 (x + z)
    refine ⟨i, ?_⟩
    convert hi using 1 <;> ring

#print axioms exists_prime_residue_normalization
#print axioms composite_residues_coprime_after_normalization
end Erdos7Reduction


/- Hall-deficiency bounds for irredundant finite product covers. -/

namespace Erdos7Tarsi
open Finset

/-- A set maximizing Hall deficiency leaves a matchable complement. -/
theorem hall_complement_of_max_deficiency
    {J A : Type*} [Fintype J] [DecidableEq J] [DecidableEq A]
    (t : J → Finset A) (s : Finset J)
    (hmax : ∀ u : Finset J,
      (u.card : ℤ) - (u.biUnion t).card ≤ (s.card : ℤ) - (s.biUnion t).card) :
    ∃ f : {j // j ∉ s} → A, Function.Injective f ∧
      ∀ j, f j ∈ t j.val ∧ f j ∉ s.biUnion t := by
  classical
  suffices hh : ∀ u : Finset {j // j ∉ s},
      u.card ≤ (u.biUnion (fun j => t j.val \ s.biUnion t)).card by
    obtain ⟨f, hf, hft⟩ :=
      (Finset.all_card_le_biUnion_card_iff_existsInjective' _).mp hh
    exact ⟨f, hf, fun j => Finset.mem_sdiff.mp (hft j)⟩
  intro u
  let v := u.image (fun j => j.val)
  have hvcard : v.card = u.card := card_image_of_injective _ Subtype.val_injective
  have hdis : Disjoint s v := by
    apply Finset.disjoint_left.mpr
    intro j hj hv
    obtain ⟨k, _, hkj⟩ := Finset.mem_image.mp hv
    exact k.property (hkj ▸ hj)
  have hbi : (s ∪ v).biUnion t = (s.biUnion t) ∪ (v.biUnion t) := union_biUnion
  have hdiff : (v.biUnion t) \ (s.biUnion t) =
      u.biUnion (fun j => t j.val \ s.biUnion t) := by
    ext a
    simp only [v, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_image]
    aesop
  have hcard : ((s ∪ v).biUnion t).card =
      (s.biUnion t).card + (u.biUnion (fun j => t j.val \ s.biUnion t)).card := by
    rw [hbi, Finset.union_comm, ← card_sdiff_add_card, hdiff, Nat.add_comm]
  have hh := hmax (s ∪ v)
  rw [card_union_of_disjoint hdis, hvcard, hcard] at hh
  omega

/-- If total Hall capacity is at least the number of sets, and every slot is
used, either all sets can be matched or some proper deficient set has a
matchable complement. -/
theorem hall_or_proper_deficient_complement
    {J A : Type*} [Fintype J] [Fintype A] [Nonempty J] [DecidableEq A]
    (t : J → Finset A)
    (hused : ∀ a, ∃ j, a ∈ t j)
    (hcard : Fintype.card J ≤ Fintype.card A) :
    ∃ s : Finset J, s ≠ Finset.univ ∧
      (∃ f : {j // j ∉ s} → A, Function.Injective f ∧
        ∀ j, f j ∈ t j.val ∧ f j ∉ s.biUnion t) := by
  classical
  by_cases hh : ∀ u : Finset J, u.card ≤ (u.biUnion t).card
  · refine ⟨∅, (Ne.symm Finset.univ_nonempty.ne_empty), ?_⟩
    obtain ⟨f, hf, hft⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' _).mp hh
    exact ⟨fun j => f j.val, hf.comp Subtype.val_injective, fun j => by simp [hft]⟩
  · push_neg at hh
    obtain ⟨u, hu⟩ := hh
    obtain ⟨s, _, hs⟩ := (Finset.univ : Finset (Finset J)).exists_max_image
      (fun s => (s.card : ℤ) - (s.biUnion t).card) (by simp)
    have hmax : ∀ v : Finset J,
        (v.card : ℤ) - (v.biUnion t).card ≤ (s.card : ℤ) - (s.biUnion t).card :=
      fun v => hs v (Finset.mem_univ _)
    have hspos : (s.biUnion t).card < s.card := by
      have := hmax u
      omega
    refine ⟨s, ?_, hall_complement_of_max_deficiency t s hmax⟩
    intro hsfull
    have hfull : (Finset.univ : Finset J).biUnion t = Finset.univ := by
      ext a
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
      exact hused a
    rw [hsfull, hfull, card_univ, card_univ] at hspos
    omega

/-- A matching into `q i - 1` slots per coordinate gives an assignment
avoiding the forbidden value of each matched constraint. -/
theorem avoiding_assignment_of_slot_matching
    {I J : Type*} [Fintype J] (q : I → ℕ) (hq : ∀ i, 0 < q i)
    (a : J → (i : I) → Fin (q i))
    (f : J → Σ i, Fin (q i - 1)) (hf : Function.Injective f) :
    ∃ y : (i : I) → Fin (q i), ∀ j, y (f j).1 ≠ a j (f j).1 := by
  classical
  have hex (i : I) : ∃ y : Fin (q i),
      ∀ j, (f j).1 = i → y ≠ a j i := by
    let B := Finset.univ.filter (fun j => (f j).1 = i)
    let T := ({i} : Finset I).sigma (fun k => (Finset.univ : Finset (Fin (q k - 1))))
    have hT : T.card = q i - 1 := by simp [T, card_sigma]
    have hB : B.card ≤ q i - 1 := by
      rw [← hT]
      apply card_le_card_of_injOn f
      · intro j hj
        simpa [T] using (Finset.mem_filter.mp hj).2
      · exact hf.injOn
    let V := B.image (fun j => a j i)
    have hV : V.card < q i := by
      have hh : V.card ≤ B.card := card_image_le
      have := hq i
      omega
    have hn : ¬ (Finset.univ : Finset (Fin (q i))) ⊆ V := by
      intro h
      have hh := Finset.card_le_card h
      simp only [card_univ, Fintype.card_fin] at hh
      omega
    obtain ⟨y, _, hy⟩ := Finset.not_subset.mp hn
    refine ⟨y, fun j hj heq => hy ?_⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, heq.symm⟩
  choose y hy using hex
  exact ⟨y, fun j => hy (f j).1 j rfl⟩

/-- Generalized Tarsi bound for irredundant covers by atomic boxes.
Each box fixes a single value in each coordinate in its support. -/
theorem irredundant_box_cover_tarsi_bound
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (q : I → ℕ) (hq : ∀ i, 0 < q i)
    (supp : J → Finset I) (a : J → (i : I) → Fin (q i))
    (hc : ∀ x : (i : I) → Fin (q i), ∃ j, ∀ i ∈ supp j, x i = a j i)
    (hpriv : ∀ j, ∃ x : (i : I) → Fin (q i),
      ∀ k, k ≠ j → ∃ i ∈ supp k, x i ≠ a k i)
    (hused : ∀ i, ∃ j, i ∈ supp j) :
    (∑ i, (q i - 1)) < Fintype.card J := by
  classical
  by_contra hbound
  have hcard : Fintype.card J ≤ ∑ i, (q i - 1) := Nat.le_of_not_gt hbound
  haveI : Nonempty J := by
    obtain ⟨j, _⟩ := hc (fun i => ⟨0, hq i⟩)
    exact ⟨j⟩
  let A := Σ i, Fin (q i - 1)
  let t (j : J) : Finset A := Finset.univ.filter (fun v => v.1 ∈ supp j)
  have htused : ∀ v : A, ∃ j, v ∈ t j := by
    intro v
    obtain ⟨j, hj⟩ := hused v.1
    exact ⟨j, by simp [t, hj]⟩
  have htcard : Fintype.card J ≤ Fintype.card A := by
    simpa [A, Fintype.card_sigma] using hcard
  obtain ⟨s, hs, f, hf, hft⟩ := hall_or_proper_deficient_complement t htused htcard
  have hex : ∃ j : J, j ∉ s := by
    by_contra! h
    exact hs (Finset.eq_univ_of_forall h)
  obtain ⟨j₀, hj₀⟩ := hex
  obtain ⟨x, hx⟩ := hpriv j₀
  obtain ⟨y, hy⟩ := avoiding_assignment_of_slot_matching q hq
    (fun j : {j // j ∉ s} => a j.val) f hf
  let W := s.biUnion supp
  let z (i : I) : Fin (q i) := if i ∈ W then x i else y i
  obtain ⟨j, hj⟩ := hc z
  by_cases hjs : j ∈ s
  · have hjne : j ≠ j₀ := fun h => hj₀ (h ▸ hjs)
    obtain ⟨i, hi, hxi⟩ := hx j hjne
    have hiW : i ∈ W := Finset.mem_biUnion.mpr ⟨j, hjs, hi⟩
    exact hxi (by simpa [z, hiW] using hj i hi)
  · let j' : {j // j ∉ s} := ⟨j, hjs⟩
    have hi : (f j').1 ∈ supp j := by simpa [t] using (hft j').1
    have hiW : (f j').1 ∉ W := by
      intro h
      obtain ⟨k, hk, hik⟩ := Finset.mem_biUnion.mp h
      apply (hft j').2
      exact Finset.mem_biUnion.mpr ⟨k, hk, by simp [t, hik]⟩
    exact hy j' (by simpa [z, hiW] using hj (f j').1 hi)

/-- The same bound holds for boxes whose nontrivial coordinate sections
lie in fibers of surjective maps to `q i` values. -/
theorem irredundant_thin_box_cover_tarsi_bound
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (A : I → Type*) (q : I → ℕ) (hq : ∀ i, 0 < q i)
    (π : (i : I) → A i → Fin (q i)) (hπ : ∀ i, Function.Surjective (π i))
    (supp : J → Finset I) (a : J → (i : I) → Fin (q i))
    (B : J → (i : I) → A i → Prop)
    (hfull : ∀ j i, i ∉ supp j → ∀ x, B j i x)
    (hthin : ∀ j i, i ∈ supp j → ∀ x, B j i x → π i x = a j i)
    (hc : ∀ x : (i : I) → A i, ∃ j, ∀ i, B j i (x i))
    (hpriv : ∀ j, ∃ x : (i : I) → A i, ∀ k, k ≠ j → ¬ ∀ i, B k i (x i))
    (hused : ∀ i, ∃ j, i ∈ supp j) :
    (∑ i, (q i - 1)) < Fintype.card J := by
  classical
  by_contra hbound
  have hcard : Fintype.card J ≤ ∑ i, (q i - 1) := Nat.le_of_not_gt hbound
  choose lift hlift using hπ
  haveI : Nonempty J := by
    obtain ⟨j, _⟩ := hc (fun i => lift i ⟨0, hq i⟩)
    exact ⟨j⟩
  let Slot := Σ i, Fin (q i - 1)
  let t (j : J) : Finset Slot := Finset.univ.filter (fun v => v.1 ∈ supp j)
  have htused : ∀ v : Slot, ∃ j, v ∈ t j := by
    intro v
    obtain ⟨j, hj⟩ := hused v.1
    exact ⟨j, by simp [t, hj]⟩
  have htcard : Fintype.card J ≤ Fintype.card Slot := by
    simpa [Slot, Fintype.card_sigma] using hcard
  obtain ⟨s, hs, f, hf, hft⟩ := hall_or_proper_deficient_complement t htused htcard
  have hex : ∃ j : J, j ∉ s := by
    by_contra! h
    exact hs (Finset.eq_univ_of_forall h)
  obtain ⟨j₀, hj₀⟩ := hex
  obtain ⟨x, hx⟩ := hpriv j₀
  obtain ⟨y, hy⟩ := avoiding_assignment_of_slot_matching q hq
    (fun j : {j // j ∉ s} => a j.val) f hf
  let W := s.biUnion supp
  let z (i : I) : A i := if i ∈ W then x i else lift i (y i)
  obtain ⟨j, hj⟩ := hc z
  by_cases hjs : j ∈ s
  · apply hx j (fun h => hj₀ (h ▸ hjs))
    intro i
    by_cases hi : i ∈ supp j
    · have hiW : i ∈ W := Finset.mem_biUnion.mpr ⟨j, hjs, hi⟩
      simpa [z, hiW] using hj i
    · exact hfull j i hi (x i)
  · let j' : {j // j ∉ s} := ⟨j, hjs⟩
    have hi : (f j').1 ∈ supp j := by simpa [t] using (hft j').1
    have hiW : (f j').1 ∉ W := by
      intro h
      obtain ⟨k, hk, hik⟩ := Finset.mem_biUnion.mp h
      apply (hft j').2
      exact Finset.mem_biUnion.mpr ⟨k, hk, by simp [t, hik]⟩
    apply hy j'
    have hh := hthin j (f j').1 hi (z (f j').1) (hj (f j').1)
    simpa [z, hiW, hlift] using hh

#print axioms irredundant_box_cover_tarsi_bound
#print axioms irredundant_thin_box_cover_tarsi_bound
end Erdos7Tarsi


/- Prime-sum bounds for irredundant arithmetic covers. -/
namespace Erdos7Reduction
open Finset

/-- Irredundant arithmetic covers have more classes than the sum of the
capacities `p i - 1` of their coprime primary coordinates. -/
theorem coprime_power_irredundant_tarsi_bound {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, 1 < p i) (hcop : Pairwise (Function.onFun Nat.Coprime p))
    (e : κ → ι → ℕ) (hused : ∀ i, ∃ k, e k i ≠ 0)
    (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k)
    (hpriv : ∀ k, ∃ x : ℤ, ∀ l, l ≠ k →
      ¬ ((∏ i, p i ^ e l i : ℕ) : ℤ) ∣ x - a l) :
    (∑ i, (p i - 1)) < Fintype.card κ := by
  classical
  let E (i : ι) := Finset.univ.sup (fun k => e k i)
  have heE (k : κ) (i : ι) : e k i ≤ E i :=
    Finset.le_sup (f := fun k => e k i) (Finset.mem_univ k)
  have hE (i : ι) : 0 < E i := by
    obtain ⟨k, hk⟩ := hused i
    have := heE k i
    omega
  letI (i : ι) : NeZero (p i) := ⟨by have := hp i; omega⟩
  let A (i : ι) := ZMod (p i ^ E i)
  let f (k : κ) (i : ι) := ZMod.castHom (pow_dvd_pow (p i) (heE k i))
    (ZMod (p i ^ e k i))
  let B (k : κ) (i : ι) (x : A i) := f k i x = (a k : ZMod (p i ^ e k i))
  let supp (k : κ) := Finset.univ.filter (fun i => e k i ≠ 0)
  let π₀ (i : ι) : A i →+* ZMod (p i) :=
    ZMod.castHom (dvd_pow_self (p i) (Nat.ne_of_gt (hE i))) _
  let π (i : ι) (x : A i) : Fin (p i) := ⟨(π₀ i x).val, ZMod.val_lt _⟩
  let b (k : κ) (i : ι) : Fin (p i) := ⟨(a k : ZMod (p i)).val, ZMod.val_lt _⟩
  have hπ (i : ι) : Function.Surjective (π i) := by
    intro y
    refine ⟨(y.val : A i), ?_⟩
    apply Fin.ext
    simp only [π, map_natCast]
    exact (ZMod.val_natCast _ _).trans (Nat.mod_eq_of_lt y.isLt)
  have hfull (k : κ) (i : ι) (hi : i ∉ supp k) (x : A i) : B k i x := by
    have hzero : e k i = 0 := by simpa [supp] using hi
    haveI : Subsingleton (ZMod (p i ^ e k i)) := by rw [hzero, pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  have hthin (k : κ) (i : ι) (hi : i ∈ supp k) (x : A i) (hx : B k i x) :
      π i x = b k i := by
    have hepos : e k i ≠ 0 := by simpa [supp] using hi
    let g := ZMod.castHom (dvd_pow_self (p i) hepos) (ZMod (p i))
    have hcomp : g.comp (f k i) = π₀ i := by exact Subsingleton.elim _ _
    have heq := congrArg g hx
    change g (f k i x) = g (a k) at heq
    rw [← RingHom.comp_apply, hcomp, map_intCast] at heq
    exact Fin.ext (congrArg ZMod.val heq)
  have hbox : ∀ x : ∀ i, A i, ∃ k, ∀ i, B k i (x i) := by
    intro x
    let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) (fun i => p i ^ E i) Finset.univ
      (fun i _ => pow_ne_zero _ (NeZero.ne _))
      (fun i _ j _ hij => (hcop hij).pow _ _)
    have hz (i : ι) : (z.val : A i) = x i := by
      rw [← ZMod.natCast_zmod_val (x i)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
    obtain ⟨k, hk⟩ := hc (z.val : ℤ)
    refine ⟨k, fun i => ?_⟩
    have hpi : p i ^ e k i ∣ ∏ j, p j ^ e k j := dvd_prod_of_mem _ (Finset.mem_univ i)
    have hpi' : ((p i ^ e k i : ℕ) : ℤ) ∣ ((∏ j, p j ^ e k j : ℕ) : ℤ) := by
      exact_mod_cast hpi
    dsimp only [B]
    rw [← hz i, map_natCast]
    symm
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (a k) (z.val : ℤ) (p i ^ e k i)).mpr
        (hpi'.trans hk)
  have hboxpriv : ∀ k, ∃ x : ∀ i, A i, ∀ l, l ≠ k → ¬ ∀ i, B l i (x i) := by
    intro k
    obtain ⟨x, hx⟩ := hpriv k
    refine ⟨fun i => (x : A i), fun l hl h => hx l hl ?_⟩
    have hcoord (i : ι) : ((p i ^ e l i : ℕ) : ℤ) ∣ x - a l := by
      have hh := h i
      change f l i (x : A i) = (a l : ZMod (p i ^ e l i)) at hh
      rw [map_intCast] at hh
      exact (ZMod.intCast_eq_intCast_iff_dvd_sub (a l) x (p i ^ e l i)).mp hh.symm
    have hcop' : ((Finset.univ : Finset ι) : Set ι).Pairwise
        (Function.onFun IsCoprime (fun i => ((p i ^ e l i : ℕ) : ℤ))) := by
      intro i _ j _ hij
      exact Int.isCoprime_iff_nat_coprime.mpr (by simpa using (hcop hij).pow (e l i) (e l j))
    rw [Nat.cast_prod]
    exact Finset.prod_dvd_of_coprime hcop' (fun i _ => hcoord i)
  apply Erdos7Tarsi.irredundant_thin_box_cover_tarsi_bound A p (fun i => by have := hp i; omega)
    π hπ supp b B hfull hthin hbox hboxpriv
  intro i
  obtain ⟨k, hk⟩ := hused i
  exact ⟨k, by simp [supp, hk]⟩

/-- Prime-sum lower bound for any irredundant finite arithmetic cover. -/
theorem arithmetic_irredundant_prime_sum_bound {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hm : ∀ k, m k ≠ 0)
    (hc : ∀ x : ℤ, ∃ k, (m k : ℤ) ∣ x - a k)
    (hpriv : ∀ k, ∃ x : ℤ, ∀ l, l ≠ k → ¬ (m l : ℤ) ∣ x - a l) :
    (∑ p ∈ Finset.univ.biUnion (fun k => (m k).primeFactors), (p - 1)) < Fintype.card κ := by
  classical
  let P := Finset.univ.biUnion (fun k => (m k).primeFactors)
  let p (i : P) := i.val
  let e (k : κ) (i : P) := (m k).factorization i.val
  have hprime (i : P) : (p i).Prime := by
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp i.property
    exact (Nat.mem_primeFactors.mp hk).1
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hprime i) (hprime j)).mpr
      (fun h => hij (Subtype.ext h))
  have hused (i : P) : ∃ k, e k i ≠ 0 := by
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp i.property
    refine ⟨k, ?_⟩
    apply Nat.ne_of_gt
    exact (hprime i).factorization_pos_of_dvd (hm k) (Nat.mem_primeFactors.mp hk).2.1
  have hprod (k : κ) : m k = ∏ i : P, p i ^ e k i := by
    have hsub : (m k).primeFactors ⊆ P := by
      intro r hr
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hr⟩
    have heq : m k = ∏ r ∈ (m k).primeFactors, r ^ (m k).factorization r := by
      simpa only [Finsupp.prod, Nat.support_factorization] using
        (Nat.factorization_prod_pow_eq_self (hm k)).symm
    have heq' : m k = ∏ r ∈ P, r ^ (m k).factorization r := by
      nth_rw 1 [heq]
      apply Finset.prod_subset hsub
      intro r _ hr
      have hzero : (m k).factorization r = 0 := by
        apply Finsupp.notMem_support_iff.mp
        rwa [Nat.support_factorization]
      simp [hzero]
    nth_rw 1 [heq']
    exact (Finset.prod_attach P (fun r => r ^ (m k).factorization r)).symm
  have hb := coprime_power_irredundant_tarsi_bound p (fun i => (hprime i).one_lt)
    hcop e hused a (by simpa only [← hprod] using hc)
    (by simpa only [← hprod] using hpriv)
  change (∑ i : P, (i.val - 1)) < Fintype.card κ at hb
  rw [Finset.sum_coe_sort P (fun r => r - 1)] at hb
  exact hb

private theorem five_odd_prime_capacity (P : Finset ℕ)
    (hcard : 5 ≤ P.card) (hp : ∀ p ∈ P, p.Prime ∧ Odd p) :
    34 ≤ ∑ p ∈ P, (p - 1) := by
  classical
  obtain ⟨S, hSP, hSc⟩ := Finset.exists_subset_card_eq hcard
  let p := S.orderEmbOfFin hSc
  have hprime (i : Fin 5) : (p i).Prime := (hp _ (hSP (S.orderEmbOfFin_mem hSc i))).1
  have hodd (i : Fin 5) : Odd (p i) := (hp _ (hSP (S.orderEmbOfFin_mem hSc i))).2
  have h0 : 3 ≤ p 0 := by have := (hprime 0).two_le; have := Nat.odd_iff.mp (hodd 0); omega
  have h1 : 5 ≤ p 1 := by
    have := p.strictMono (by decide : (0 : Fin 5) < 1)
    have := Nat.odd_iff.mp (hodd 1)
    omega
  have h2 : 7 ≤ p 2 := by
    have := p.strictMono (by decide : (1 : Fin 5) < 2)
    have := Nat.odd_iff.mp (hodd 2)
    omega
  have h3 : 11 ≤ p 3 := by
    have := p.strictMono (by decide : (2 : Fin 5) < 3)
    have := Nat.odd_iff.mp (hodd 3)
    have hn9 : p 3 ≠ 9 := by intro he; have hh := hprime 3; norm_num [he] at hh
    omega
  have h4 : 13 ≤ p 4 := by
    have := p.strictMono (by decide : (3 : Fin 5) < 4)
    have := Nat.odd_iff.mp (hodd 4)
    omega
  have hS : 34 ≤ ∑ r ∈ S, (r - 1) := by
    rw [← S.map_orderEmbOfFin_univ hSc, sum_map]
    change 34 ≤ ∑ i : Fin 5, (p i - 1)
    rw [show (∑ i : Fin 5, (p i - 1)) =
      (p 0 - 1) + (p 1 - 1) + (p 2 - 1) + (p 3 - 1) + (p 4 - 1) by
        simp [Fin.sum_univ_succ]; omega]
    omega
  exact hS.trans (Finset.sum_le_sum_of_subset hSP)

/-- Every odd strict covering system needs at least thirty-five moduli. -/
theorem at_least_thirtyfive_moduli (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i, ¬ C.moduli i ≤ Ideal.span {2}) :
    letI := C.fintypeIndex
    35 ≤ Fintype.card C.ι := by
  classical
  letI := C.fintypeIndex
  let m (i : C.ι) := (C.moduli i).absNorm
  have hm : ∀ i, 1 < m i := moduli_absNorm_gt_one C
  have hmi : Function.Injective m := moduli_absNorm_injective C
  have ho : ∀ i, Odd (m i) := fun i => (ideal_not_le_two_iff _).mp (hodd i)
  have hc := arithmetic_cover C
  obtain ⟨s, hs, hpriv⟩ := arithmetic_irredundant_subcover m C.residue hc
  let n (i : s) := m i.val
  let a (i : s) := C.residue i.val
  have hn : ∀ i : s, 1 < n i := fun i => hm i.val
  have hni : Function.Injective n := fun i j hij => Subtype.ext (hmi hij)
  have hno : ∀ i : s, Odd (n i) := fun i => ho i.val
  have hnc : ∀ x : ℤ, ∃ i : s, (n i : ℤ) ∣ x - a i := by
    intro x
    obtain ⟨i, hi, hxi⟩ := hs x
    exact ⟨⟨i, hi⟩, hxi⟩
  have hnpriv : ∀ i : s, ∃ x : ℤ, ∀ j : s, j ≠ i → ¬ (n j : ℤ) ∣ x - a j := by
    intro i
    obtain ⟨x, hx⟩ := hpriv i.val i.property
    refine ⟨x, fun j hji => hx j.val j.property (fun hh => hji (Subtype.ext hh))⟩
  have hprimecount := arithmetic_cover_prime_count n a hn hni hno hnc
  have hsum := arithmetic_irredundant_prime_sum_bound n a
    (fun i => by have := hn i; omega) hnc hnpriv
  have hcap := five_odd_prime_capacity _ hprimecount (by
    intro p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    have hh := Nat.mem_primeFactors.mp hi
    exact ⟨hh.1, (hno i).of_dvd_nat hh.2.1⟩)
  have hscard : Fintype.card s ≤ Fintype.card C.ι := by
    simpa only [Fintype.card_coe] using Finset.card_le_univ s
  omega

#print axioms coprime_power_irredundant_tarsi_bound
#print axioms arithmetic_irredundant_prime_sum_bound
#print axioms at_least_thirtyfive_moduli
end Erdos7Reduction


/- Digit-level refinements of the Tarsi bound for arithmetic covers. -/

namespace Erdos7Digits
open Finset

/-- Congruence modulo a power is equality of the corresponding low digits. -/
theorem modEq_pow_iff_digits (p n x y : ℕ) :
    Nat.ModEq (p ^ n) x y ↔ ∀ k < n, x / p ^ k % p = y / p ^ k % p := by
  constructor
  · intro h k hk
    have hh : Nat.ModEq (p ^ (k + 1)) x y :=
      h.of_dvd (pow_dvd_pow p (by omega))
    change x % p ^ (k + 1) = y % p ^ (k + 1) at hh
    have he := congrArg (fun t => t / p ^ k) hh
    simpa only [pow_succ, Nat.mod_mul_right_div_self] using he
  · induction n with
    | zero => simp [Nat.ModEq, Nat.mod_one]
    | succ n ih =>
      intro h
      have hh := ih (fun k hk => h k (by omega))
      have hn := h n (by omega)
      change x % p ^ n = y % p ^ n at hh
      change x % p ^ (n + 1) = y % p ^ (n + 1)
      rw [pow_succ, Nat.mod_mul, Nat.mod_mul, hh, hn]

/-- Digits of an element of a prime-power residue ring. Primality is not needed. -/
def zmodDigits (p n : ℕ) [NeZero p] (x : ZMod (p ^ n)) : Fin n → Fin p :=
  finFunctionFinEquiv.symm ⟨x.val, ZMod.val_lt x⟩

theorem zmodDigits_val (p n : ℕ) [NeZero p] (x : ZMod (p ^ n)) (k : Fin n) :
    (zmodDigits p n x k).val = x.val / p ^ k.val % p := rfl

/-- The digit representation respects every reduction to a smaller power. -/
theorem castHom_eq_iff_digits (p n e : ℕ) [NeZero p] (he : e ≤ n)
    (x y : ZMod (p ^ n)) :
    ZMod.castHom (pow_dvd_pow p he) (ZMod (p ^ e)) x =
      ZMod.castHom (pow_dvd_pow p he) (ZMod (p ^ e)) y ↔
      ∀ k : Fin n, k.val < e → zmodDigits p n x k = zmodDigits p n y k := by
  rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y]
  simp only [map_natCast]
  rw [ZMod.natCast_eq_natCast_iff, modEq_pow_iff_digits]
  constructor
  · intro h k hk
    apply Fin.ext
    simpa only [zmodDigits_val, ZMod.natCast_zmod_val] using h k.val hk
  · intro h k hk
    have hh := congrArg Fin.val (h ⟨k, by omega⟩ hk)
    simpa only [zmodDigits_val, ZMod.natCast_zmod_val] using hh

/-- Encoding a digit vector and reading it back gives the original vector. -/
theorem zmodDigits_encode (p n : ℕ) [NeZero p] (f : Fin n → Fin p) :
    zmodDigits p n ((finFunctionFinEquiv f).val : ZMod (p ^ n)) = f := by
  unfold zmodDigits
  have he : (⟨(((finFunctionFinEquiv f).val : ZMod (p ^ n))).val,
      ZMod.val_lt _⟩ : Fin (p ^ n)) = finFunctionFinEquiv f := by
    apply Fin.ext
    exact ZMod.val_cast_of_lt (finFunctionFinEquiv f).isLt
  rw [he, Equiv.symm_apply_apply]

/-- The full digit-level Tarsi bound for coprime prime-power coordinates. -/
theorem coprime_power_irredundant_digit_bound {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hcop : Pairwise (Function.onFun Nat.Coprime p))
    (e : κ → ι → ℕ) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k)
    (hpriv : ∀ k, ∃ x : ℤ, ∀ l, l ≠ k →
      ¬ ((∏ i, p i ^ e l i : ℕ) : ℤ) ∣ x - a l) :
    (∑ i, (Finset.univ.sup (fun k => e k i)) * (p i - 1)) < Fintype.card κ := by
  classical
  haveI : Nonempty κ := by obtain ⟨k, _⟩ := hc 0; exact ⟨k⟩
  let E (i : ι) := Finset.univ.sup (fun k => e k i)
  have heE (k : κ) (i : ι) : e k i ≤ E i :=
    Finset.le_sup (f := fun k => e k i) (Finset.mem_univ k)
  letI (i : ι) : NeZero (p i) := ⟨Nat.ne_of_gt (hp i)⟩
  let D := Σ i, Fin (E i)
  let q (d : D) := p d.1
  let supp (k : κ) : Finset D := Finset.univ.filter (fun d => d.2.val < e k d.1)
  let b (k : κ) (d : D) : Fin (q d) := zmodDigits (p d.1) (E d.1) (a k) d.2
  have hbox : ∀ x : (d : D) → Fin (q d), ∃ k, ∀ d ∈ supp k, x d = b k d := by
    intro x
    let y (i : ι) := finFunctionFinEquiv (fun j : Fin (E i) => x ⟨i, j⟩)
    let z := Nat.chineseRemainderOfFinset (fun i => (y i).val)
      (fun i => p i ^ E i) Finset.univ
      (fun i _ => pow_ne_zero _ (NeZero.ne _))
      (fun i _ j _ hij => (hcop hij).pow _ _)
    have hz (i : ι) : (z.val : ZMod (p i ^ E i)) = ((y i).val : ZMod (p i ^ E i)) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
    obtain ⟨k, hk⟩ := hc (z.val : ℤ)
    refine ⟨k, fun d hd => ?_⟩
    have hde : d.2.val < e k d.1 := (Finset.mem_filter.mp hd).2
    have hpi : p d.1 ^ e k d.1 ∣ ∏ i, p i ^ e k i :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ d.1)
    have hpi' : ((p d.1 ^ e k d.1 : ℕ) : ℤ) ∣ ((∏ i, p i ^ e k i : ℕ) : ℤ) := by
      exact_mod_cast hpi
    have heq : ZMod.castHom (pow_dvd_pow (p d.1) (heE k d.1))
        (ZMod (p d.1 ^ e k d.1)) (z.val : ZMod (p d.1 ^ E d.1)) =
        ZMod.castHom (pow_dvd_pow (p d.1) (heE k d.1))
        (ZMod (p d.1 ^ e k d.1)) (a k : ZMod (p d.1 ^ E d.1)) := by
      simp only [map_natCast, map_intCast]
      symm
      have hh := (ZMod.intCast_eq_intCast_iff_dvd_sub (a k) (z.val : ℤ)
          (p d.1 ^ e k d.1)).mpr (hpi'.trans hk)
      rw [Int.cast_natCast] at hh
      exact hh
    have hh := (castHom_eq_iff_digits _ _ _ (heE k d.1) _ _).mp heq d.2 hde
    rw [hz, zmodDigits_encode] at hh
    exact hh
  have hboxpriv : ∀ k, ∃ x : (d : D) → Fin (q d),
      ∀ l, l ≠ k → ∃ d ∈ supp l, x d ≠ b l d := by
    intro k
    obtain ⟨x, hx⟩ := hpriv k
    refine ⟨fun d => zmodDigits (p d.1) (E d.1) x d.2, fun l hl => ?_⟩
    by_contra! h
    apply hx l hl
    have hcoord (i : ι) : ((p i ^ e l i : ℕ) : ℤ) ∣ x - a l := by
      have heq := (castHom_eq_iff_digits (p i) (E i) (e l i) (heE l i)
        (x : ZMod (p i ^ E i)) (a l : ZMod (p i ^ E i))).mpr (by
          intro d hd
          exact h ⟨i, d⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩))
      simp only [map_intCast] at heq
      exact (ZMod.intCast_eq_intCast_iff_dvd_sub (a l) x (p i ^ e l i)).mp heq.symm
    have hcop' : ((Finset.univ : Finset ι) : Set ι).Pairwise
        (Function.onFun IsCoprime (fun i => ((p i ^ e l i : ℕ) : ℤ))) := by
      intro i _ j _ hij
      exact Int.isCoprime_iff_nat_coprime.mpr (by simpa using (hcop hij).pow (e l i) (e l j))
    rw [Nat.cast_prod]
    exact Finset.prod_dvd_of_coprime hcop' (fun i _ => hcoord i)
  have hused (d : D) : ∃ k, d ∈ supp k := by
    obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup Finset.univ
      Finset.univ_nonempty (fun k => e k d.1)
    have he : E d.1 = e k d.1 := hk
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [← he]
    exact d.2.isLt
  have hb := Erdos7Tarsi.irredundant_box_cover_tarsi_bound q (fun d => hp d.1)
    supp b hbox hboxpriv hused
  simpa [q, D, Fintype.sum_sigma, Finset.sum_const, E] using hb

/-- Factorization turns the finite lcm into a coordinatewise supremum. -/
theorem factorization_finset_lcm {κ : Type*} (s : Finset κ) (m : κ → ℕ)
    (hm : ∀ k ∈ s, m k ≠ 0) (p : ℕ) :
    (s.lcm m).factorization p = s.sup (fun k => (m k).factorization p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Nat.factorization_one]
  | @insert k s hks ih =>
    have hmk := hm k (Finset.mem_insert_self _ _)
    have hms : ∀ l ∈ s, m l ≠ 0 := fun l hl => hm l (Finset.mem_insert_of_mem hl)
    rw [Finset.lcm_insert, Finset.sup_insert]
    change (Nat.lcm (m k) (s.lcm m)).factorization p = _
    rw [Nat.factorization_lcm hmk (Finset.lcm_ne_zero_iff.mpr hms), Finsupp.sup_apply,
      ih hms]

/-- The full factorization-weight lower bound for an irredundant cover. -/
theorem arithmetic_irredundant_factorization_sum_bound {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hm : ∀ k, m k ≠ 0)
    (hc : ∀ x : ℤ, ∃ k, (m k : ℤ) ∣ x - a k)
    (hpriv : ∀ k, ∃ x : ℤ, ∀ l, l ≠ k → ¬ (m l : ℤ) ∣ x - a l) :
    (∑ p ∈ Finset.univ.biUnion (fun k => (m k).primeFactors),
      (Finset.univ.lcm m).factorization p * (p - 1)) < Fintype.card κ := by
  classical
  let P := Finset.univ.biUnion (fun k => (m k).primeFactors)
  let p (i : P) := i.val
  let e (k : κ) (i : P) := (m k).factorization i.val
  have hprime (i : P) : (p i).Prime := by
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp i.property
    exact (Nat.mem_primeFactors.mp hk).1
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hprime i) (hprime j)).mpr
      (fun h => hij (Subtype.ext h))
  have hprod (k : κ) : m k = ∏ i : P, p i ^ e k i := by
    have hsub : (m k).primeFactors ⊆ P := by
      intro r hr
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hr⟩
    have heq : m k = ∏ r ∈ (m k).primeFactors, r ^ (m k).factorization r := by
      simpa only [Finsupp.prod, Nat.support_factorization] using
        (Nat.factorization_prod_pow_eq_self (hm k)).symm
    have heq' : m k = ∏ r ∈ P, r ^ (m k).factorization r := by
      nth_rw 1 [heq]
      apply Finset.prod_subset hsub
      intro r _ hr
      have hzero : (m k).factorization r = 0 := by
        apply Finsupp.notMem_support_iff.mp
        rwa [Nat.support_factorization]
      simp [hzero]
    nth_rw 1 [heq']
    exact (Finset.prod_attach P (fun r => r ^ (m k).factorization r)).symm
  have hb := coprime_power_irredundant_digit_bound p (fun i => (hprime i).pos)
    hcop e a (by simpa only [← hprod] using hc)
    (by simpa only [← hprod] using hpriv)
  have hfac (i : P) : Finset.univ.sup (fun k => e k i) =
      (Finset.univ.lcm m).factorization i.val :=
    (factorization_finset_lcm Finset.univ m (fun k _ => hm k) i.val).symm
  simp only [hfac, p] at hb
  rw [Finset.sum_coe_sort P (fun r => (Finset.univ.lcm m).factorization r * (r - 1))] at hb
  exact hb

/-- The prime factors of a finite lcm are the union of the prime factors. -/
theorem primeFactors_finset_lcm {κ : Type*} (s : Finset κ) (m : κ → ℕ)
    (hm : ∀ k ∈ s, m k ≠ 0) :
    (s.lcm m).primeFactors = s.biUnion (fun k => (m k).primeFactors) := by
  classical
  have hmem (n p : ℕ) : p ∈ n.primeFactors ↔ 0 < n.factorization p := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff, Nat.pos_iff_ne_zero]
  ext p
  simp only [Finset.mem_biUnion, hmem, factorization_finset_lcm s m hm p,
    Finset.lt_sup_iff]

/-- The natural logarithm bound needed here can be expressed entirely in naturals. -/
theorem odd_le_three_pow_half (n : ℕ) (hn : Odd n) : n ≤ 3 ^ (n / 2) := by
  have h (k : ℕ) : 2 * k + 1 ≤ 3 ^ k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [pow_succ]
      nlinarith
  obtain ⟨k, hk⟩ := hn
  have heq : n = 2 * k + 1 := by omega
  rw [heq]
  rw [show (2 * k + 1) / 2 = k by omega]
  exact h k

/-- Half the Tarsi weight for an odd period. -/
def oddPeriodWeight (N : ℕ) : ℕ :=
  ∑ p ∈ N.primeFactors, N.factorization p * (p / 2)

theorem odd_period_le_weight_power (N : ℕ) (hN : N ≠ 0) (ho : Odd N) :
    N ≤ 3 ^ oddPeriodWeight N := by
  have heq : N = ∏ p ∈ N.primeFactors, p ^ N.factorization p := by
    simpa only [Finsupp.prod, Nat.support_factorization] using
      (Nat.factorization_prod_pow_eq_self hN).symm
  calc
    N = ∏ p ∈ N.primeFactors, p ^ N.factorization p := heq
    _ ≤ ∏ p ∈ N.primeFactors, (3 ^ (p / 2)) ^ N.factorization p := by
      apply Finset.prod_le_prod'
      intro p hp
      exact Nat.pow_le_pow_left
        (odd_le_three_pow_half p (ho.of_dvd_nat (Nat.mem_primeFactors.mp hp).2.1)) _
    _ = 3 ^ oddPeriodWeight N := by
      simp only [← pow_mul, Nat.mul_comm, Finset.prod_pow_eq_pow_sum, oddPeriodWeight]

theorem factorization_weight_eq_twice_oddPeriodWeight (N : ℕ) (ho : Odd N) :
    (∑ p ∈ N.primeFactors, N.factorization p * (p - 1)) = 2 * oddPeriodWeight N := by
  rw [oddPeriodWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpodd := Nat.odd_iff.mp (ho.of_dvd_nat (Nat.mem_primeFactors.mp hp).2.1)
  have he : p - 1 = 2 * (p / 2) := by omega
  rw [he]
  ring

/-- An irredundant odd arithmetic cover has an explicit bounded period for a
fixed number of classes. This is not a cardinality-independent obstruction. -/
theorem irredundant_odd_period_bound {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hm : ∀ k, m k ≠ 0) (ho : ∀ k, Odd (m k))
    (hc : ∀ x : ℤ, ∃ k, (m k : ℤ) ∣ x - a k)
    (hpriv : ∀ k, ∃ x : ℤ, ∀ l, l ≠ k → ¬ (m l : ℤ) ∣ x - a l) :
    Finset.univ.lcm m ≤ 3 ^ ((Fintype.card κ - 1) / 2) := by
  let N := Finset.univ.lcm m
  have hN : N ≠ 0 := Finset.lcm_ne_zero_iff.mpr (fun k _ => hm k)
  have hoN : Odd N := by
    have hp : Odd (∏ k, m k) := Finset.prod_induction m Odd
      (fun _ _ ha hb => ha.mul hb) (by norm_num) (fun k _ => ho k)
    exact hp.of_dvd_nat (Finset.lcm_dvd_prod Finset.univ m)
  have hb := arithmetic_irredundant_factorization_sum_bound m a hm hc hpriv
  rw [← primeFactors_finset_lcm Finset.univ m (fun k _ => hm k)] at hb
  change (∑ p ∈ N.primeFactors, N.factorization p * (p - 1)) < Fintype.card κ at hb
  rw [factorization_weight_eq_twice_oddPeriodWeight N hoN] at hb
  have hweight : oddPeriodWeight N ≤ (Fintype.card κ - 1) / 2 := by omega
  exact (odd_period_le_weight_power N hN hoN).trans
    (Nat.pow_le_pow_right (by norm_num) hweight)

/-- For each cardinality bound, existence reduces to finitely many possible
common periods. The bound still depends on the unrestricted cardinality. -/
theorem exists_bounded_period_odd_cover (N K : ℕ)
    (h : Erdos7Reduction.HasOddArithmeticCover N K) :
    ∃ M ≤ 3 ^ ((K - 1) / 2), Erdos7Reduction.HasOddArithmeticCover M K := by
  classical
  obtain ⟨_, ι, fι, m, a, hmi, hm, hc, _, hcard⟩ := h
  letI : Fintype ι := fι
  obtain ⟨s, hs, hpriv⟩ := Erdos7Reduction.arithmetic_irredundant_subcover m a hc
  let n (i : s) := m i.val
  let b (i : s) := a i.val
  have hn : ∀ i : s, 1 < n i ∧ Odd (n i) := fun i => hm i.val
  have hni : Function.Injective n := fun i j hij => Subtype.ext (hmi hij)
  have hnc : ∀ x : ℤ, ∃ i : s, (n i : ℤ) ∣ x - b i := by
    intro x
    obtain ⟨i, hi, hxi⟩ := hs x
    exact ⟨⟨i, hi⟩, hxi⟩
  have hnpriv : ∀ i : s, ∃ x : ℤ, ∀ j : s, j ≠ i → ¬ (n j : ℤ) ∣ x - b j := by
    intro i
    obtain ⟨x, hx⟩ := hpriv i.val i.property
    exact ⟨x, fun j hji => hx j.val j.property (fun hh => hji (Subtype.ext hh))⟩
  have hn0 : ∀ i : s, n i ≠ 0 := fun i => by have := (hn i).1; omega
  have hscard : Fintype.card s ≤ K := by
    have hsC : Fintype.card s ≤ Fintype.card ι := by
      simpa only [Fintype.card_coe] using Finset.card_le_univ s
    exact hsC.trans hcard
  let M := Finset.univ.lcm n
  have hM0 : M ≠ 0 := Finset.lcm_ne_zero_iff.mpr (fun i _ => hn0 i)
  have hb := irredundant_odd_period_bound n b hn0 (fun i => (hn i).2) hnc hnpriv
  refine ⟨M, hb.trans (Nat.pow_le_pow_right (by norm_num) ?_), ?_⟩
  · omega
  · exact ⟨Nat.pos_of_ne_zero hM0, s, inferInstance, n, b, hni, hn, hnc,
      fun i => Finset.dvd_lcm (Finset.mem_univ i), hscard⟩

#print axioms castHom_eq_iff_digits
#print axioms coprime_power_irredundant_digit_bound
#print axioms arithmetic_irredundant_factorization_sum_bound
#print axioms irredundant_odd_period_bound
#print axioms exists_bounded_period_odd_cover
end Erdos7Digits


/- Shrinking prime alphabets in hypothetical odd covering systems. -/
namespace Erdos7Compression
open Erdos7Digits

/-- CRT realizes every simultaneous prime-power digit vector by an integer. -/
theorem exists_integer_with_digits {ι : Type*} [Fintype ι]
    (p E : ι → ℕ) (hp : ∀ i, 0 < p i)
    (hcop : Pairwise (Function.onFun Nat.Coprime p))
    [∀ i, NeZero (p i)] (x : (i : ι) → Fin (E i) → Fin (p i)) :
    ∃ z : ℤ, ∀ i, zmodDigits (p i) (E i) (z : ZMod (p i ^ E i)) = x i := by
  classical
  let y (i : ι) := finFunctionFinEquiv (x i)
  let z := Nat.chineseRemainderOfFinset (fun i => (y i).val)
    (fun i => p i ^ E i) Finset.univ
    (fun i _ => pow_ne_zero _ (Nat.ne_of_gt (hp i)))
    (fun i _ j _ hij => (hcop hij).pow _ _)
  refine ⟨(z.val : ℤ), fun i => ?_⟩
  have hz : (z.val : ZMod (p i ^ E i)) = ((y i).val : ZMod (p i ^ E i)) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
  rw [Int.cast_natCast, hz, zmodDigits_encode]

/-- An arithmetic congruence is a prefix box in the digit coordinates. -/
theorem divisor_product_iff_digits {ι : Type*} [Fintype ι]
    (p E e : ι → ℕ) (he : ∀ i, e i ≤ E i)
    (hcop : Pairwise (Function.onFun Nat.Coprime p)) [∀ i, NeZero (p i)]
    (x a : ℤ) :
    ((∏ i, p i ^ e i : ℕ) : ℤ) ∣ x - a ↔
      ∀ i (j : Fin (E i)), j.val < e i →
        zmodDigits (p i) (E i) x j = zmodDigits (p i) (E i) a j := by
  constructor
  · intro hx i j hj
    have hpi : p i ^ e i ∣ ∏ k, p k ^ e k :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have hpi' : ((p i ^ e i : ℕ) : ℤ) ∣ ((∏ k, p k ^ e k : ℕ) : ℤ) := by
      exact_mod_cast hpi
    have heq := (ZMod.intCast_eq_intCast_iff_dvd_sub a x (p i ^ e i)).mpr
      (hpi'.trans hx)
    have heq' : ZMod.castHom (pow_dvd_pow (p i) (he i)) (ZMod (p i ^ e i))
        (x : ZMod (p i ^ E i)) =
        ZMod.castHom (pow_dvd_pow (p i) (he i)) (ZMod (p i ^ e i))
        (a : ZMod (p i ^ E i)) := by
      simp only [map_intCast]
      exact heq.symm
    exact (castHom_eq_iff_digits _ _ _ (he i) _ _).mp heq' j hj
  · intro hx
    have hcoord (i : ι) : ((p i ^ e i : ℕ) : ℤ) ∣ x - a := by
      have heq := (castHom_eq_iff_digits (p i) (E i) (e i) (he i)
        (x : ZMod (p i ^ E i)) (a : ZMod (p i ^ E i))).mpr (hx i)
      simp only [map_intCast] at heq
      exact (ZMod.intCast_eq_intCast_iff_dvd_sub a x (p i ^ e i)).mp heq.symm
    have hcop' : ((Finset.univ : Finset ι) : Set ι).Pairwise
        (Function.onFun IsCoprime (fun i => ((p i ^ e i : ℕ) : ℤ))) := by
      intro i _ j _ hij
      exact Int.isCoprime_iff_nat_coprime.mpr (by simpa using (hcop hij).pow (e i) (e j))
    rw [Nat.cast_prod]
    exact Finset.prod_dvd_of_coprime hcop' (fun i _ => hcoord i)

/-- An injective digit-alphabet restriction can delete any class with an
excluded digit. All other exponent vectors are retained unchanged. -/
theorem shrink_alphabets_delete_class {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p q E : ι → ℕ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hcp : Pairwise (Function.onFun Nat.Coprime p))
    (hcq : Pairwise (Function.onFun Nat.Coprime q))
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k)
    (g : (i : ι) → Fin (q i) ↪ Fin (p i))
    [∀ i, NeZero (p i)] (k₀ : κ) (i₀ : ι) (j₀ : Fin (E i₀))
    (hj₀ : j₀.val < e k₀ i₀)
    (hexcl : zmodDigits (p i₀) (E i₀) (a k₀) j₀ ∉ Set.range (g i₀)) :
    ∃ b : {k // k ≠ k₀} → ℤ, ∀ x : ℤ, ∃ k : {k // k ≠ k₀},
      ((∏ i, q i ^ e k.val i : ℕ) : ℤ) ∣ x - b k := by
  classical
  letI (i : ι) : NeZero (q i) := ⟨Nat.ne_of_gt (hq i)⟩
  let B (k : κ) (i : ι) (j : Fin (E i)) : Fin (q i) :=
    Function.invFun (g i) (zmodDigits (p i) (E i) (a k) j)
  choose b hb using fun k : {k // k ≠ k₀} =>
    exists_integer_with_digits q E hq hcq (B k.val)
  refine ⟨b, fun x => ?_⟩
  let X (i : ι) := zmodDigits (q i) (E i) (x : ZMod (q i ^ E i))
  obtain ⟨z, hz⟩ := exists_integer_with_digits p E hp hcp (fun i j => g i (X i j))
  obtain ⟨k, hk⟩ := hc z
  have hkd := (divisor_product_iff_digits p E (e k) (he k) hcp z (a k)).mp hk
  have hkne : k ≠ k₀ := by
    intro h
    subst k
    apply hexcl
    have hh := hkd i₀ j₀ hj₀
    rw [hz] at hh
    exact ⟨X i₀ j₀, hh⟩
  refine ⟨⟨k, hkne⟩, (divisor_product_iff_digits q E (e k) (he k) hcq x (b ⟨k, hkne⟩)).mpr ?_⟩
  intro i j hj
  rw [hb]
  have hh := hkd i j hj
  rw [hz] at hh
  change X i j = B k i j
  dsimp only [B]
  rw [← hh]
  exact (Function.leftInverse_invFun (g i).injective (X i j)).symm

/-- A smaller finite alphabet embeds while avoiding any prescribed value. -/
theorem exists_fin_embedding_avoiding (p q : ℕ) (hqp : q < p) (r : Fin p) :
    ∃ g : Fin q ↪ Fin p, r ∉ Set.range g := by
  let g (x : Fin q) : Fin p := if h : x.val < r.val then
    ⟨x.val, by omega⟩ else ⟨x.val + 1, by omega⟩
  have hgi : Function.Injective g := by
    intro x y hxy
    apply Fin.ext
    have hh := congrArg Fin.val hxy
    dsimp [g] at hh
    split_ifs at hh <;> simp only [Fin.val_mk] at hh <;> omega
  refine ⟨⟨g, hgi⟩, ?_⟩
  rintro ⟨x, hx⟩
  have hh := congrArg Fin.val hx
  dsimp [g] at hh
  split_ifs at hh <;> simp only [Fin.val_mk] at hh <;> omega

/-- Prime-power products retain the full exponent vector when the primes are distinct. -/
theorem factorization_prime_power_product {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hpi : Function.Injective p)
    (e : ι → ℕ) (i : ι) :
    (∏ j, p j ^ e j).factorization (p i) = e i := by
  classical
  rw [Nat.factorization_prod_apply (fun j _ => pow_ne_zero _ (hp j).ne_zero)]
  have heq : (∑ j, (p j ^ e j).factorization (p i)) =
      ∑ j, if j = i then e j else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [(hp j).factorization_pow, Finsupp.single_apply]
    simp [hpi.eq_iff]
  rw [heq]
  simp

/-- Shrinking alphabets preserves distinct nontrivial odd moduli, provided the
new bases are distinct odd primes, and removes the specified class. -/
theorem shrink_odd_cover_delete_class {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p q E : ι → ℕ) (hp : ∀ i, 0 < p i)
    (hq : ∀ i, (q i).Prime ∧ Odd (q i)) (hqi : Function.Injective q)
    (hcp : Pairwise (Function.onFun Nat.Coprime p))
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i)
    (hei : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k)
    (g : (i : ι) → Fin (q i) ↪ Fin (p i))
    [∀ i, NeZero (p i)] (k₀ : κ) (i₀ : ι) (j₀ : Fin (E i₀))
    (hj₀ : j₀.val < e k₀ i₀)
    (hexcl : zmodDigits (p i₀) (E i₀) (a k₀) j₀ ∉ Set.range (g i₀)) :
    ∃ b : {k // k ≠ k₀} → ℤ,
      Erdos7Reduction.IsOddArithmeticCover (fun k => ∏ i, q i ^ e k.val i) b := by
  classical
  have hcq : Pairwise (Function.onFun Nat.Coprime q) := by
    intro i j hij
    exact (Nat.coprime_primes (hq i).1 (hq j).1).mpr (fun h => hij (hqi h))
  obtain ⟨b, hb⟩ := shrink_alphabets_delete_class p q E hp (fun i => (hq i).1.pos)
    hcp hcq e he a hc g k₀ i₀ j₀ hj₀ hexcl
  refine ⟨b, ?_, ?_, hb⟩
  · intro k l hkl
    apply Subtype.ext
    apply hei
    funext i
    have hh := congrArg (fun n : ℕ => n.factorization (q i)) hkl
    simpa only [factorization_prime_power_product q (fun i => (hq i).1) hqi] using hh
  · intro k
    dsimp only
    have hpos : 0 < ∏ i, q i ^ e k.val i := Finset.prod_pos
      (fun i _ => pow_pos (hq i).1.pos _)
    have hne : (∏ i, q i ^ e k.val i) ≠ 1 := by
      intro h
      obtain ⟨i, hi⟩ := he0 k.val
      have hh := factorization_prime_power_product q (fun i => (hq i).1) hqi (e k.val) i
      rw [h, Nat.factorization_one, Finsupp.zero_apply] at hh
      exact hi hh.symm
    refine ⟨by omega, ?_⟩
    exact Finset.prod_induction (fun i => q i ^ e k.val i) Odd
      (fun _ _ ha hb => ha.mul hb) (by norm_num) (fun i _ => (hq i).2.pow)

/-- Replacing a used prime by a smaller unused odd prime gives an odd cover
with a specified class deleted and with the same surviving exponent vectors. -/
theorem compress_to_unused_smaller_prime {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) (E : ι → ℕ)
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i)
    (hei : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k)
    (q : ℕ) (hq : q.Prime ∧ Odd q) (hqnew : ∀ i, p i ≠ q)
    (i₀ : ι) (hqp : q < p i₀) (hused : ∃ k, e k i₀ ≠ 0) :
    ∃ (k₀ : κ) (b : {k // k ≠ k₀} → ℤ),
      Erdos7Reduction.IsOddArithmeticCover
        (fun k => ∏ i, Function.update p i₀ q i ^ e k.val i) b := by
  classical
  letI (i : ι) : NeZero (p i) := ⟨(hp i).1.ne_zero⟩
  obtain ⟨k₀, hk₀⟩ := hused
  have hEpos : 0 < E i₀ := by have := he k₀ i₀; omega
  let j₀ : Fin (E i₀) := ⟨0, hEpos⟩
  let r := zmodDigits (p i₀) (E i₀) (a k₀) j₀
  obtain ⟨g₀, hg₀⟩ := exists_fin_embedding_avoiding (p i₀) q hqp r
  let q' := Function.update p i₀ q
  have hq' : ∀ i, (q' i).Prime ∧ Odd (q' i) := by
    intro i
    by_cases hi : i = i₀
    · simpa [q', hi] using hq
    · simpa [q', hi] using hp i
  have hqi : Function.Injective q' := by
    intro i j hij
    by_cases hi : i = i₀ <;> by_cases hj : j = i₀
    · exact hi.trans hj.symm
    · subst i
      have hh : q = p j := by simpa [q', hj] using hij
      exact False.elim (hqnew j hh.symm)
    · subst j
      have hh : p i = q := by simpa [q', hi] using hij
      exact False.elim (hqnew i hh)
    · apply hpi
      simpa [q', hi, hj] using hij
  let g : (i : ι) → Fin (q' i) ↪ Fin (p i) := fun i =>
    if h : i = i₀ then by
      subst i
      exact (Fin.castLEEmb (by simp [q'] : q' i₀ ≤ q)).trans g₀
    else Fin.castLEEmb (by simp [q', h] : q' i ≤ p i)
  have hg : r ∉ Set.range (g i₀) := by
    rintro ⟨x, hx⟩
    apply hg₀
    simp only [g, dif_pos rfl, Function.Embedding.trans_apply] at hx
    exact ⟨_, hx⟩
  have hcp : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i).1 (hp j).1).mpr (fun h => hij (hpi h))
  obtain ⟨b, hb⟩ := shrink_odd_cover_delete_class p q' E (fun i => (hp i).1.pos)
    hq' hqi hcp e he hei he0 a hc g k₀ i₀ j₀ (by dsimp [j₀]; omega) hg
  exact ⟨k₀, b, hb⟩

/-- Expanding over any finite superset of the prime factors. -/
theorem factorization_product_over_superset (m : ℕ) (hm : m ≠ 0)
    (P : Finset ℕ) (hP : m.primeFactors ⊆ P) :
    m = ∏ i : P, i.val ^ m.factorization i.val := by
  classical
  have heq : m = ∏ r ∈ m.primeFactors, r ^ m.factorization r := by
    simpa only [Finsupp.prod, Nat.support_factorization] using
      (Nat.factorization_prod_pow_eq_self hm).symm
  have heq' : m = ∏ r ∈ P, r ^ m.factorization r := by
    nth_rw 1 [heq]
    apply Finset.prod_subset hP
    intro r _ hr
    have hzero : m.factorization r = 0 := by
      apply Finsupp.notMem_support_iff.mp
      rwa [Nat.support_factorization]
    simp [hzero]
  nth_rw 1 [heq']
  exact (Finset.prod_attach P (fun r => r ^ m.factorization r)).symm

/-- A gap in the odd-prime support allows a reduction in the number of classes. -/
theorem prime_gap_reduces_cardinality {κ : Type} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : Erdos7Reduction.IsOddArithmeticCover m a)
    (p₀ q : ℕ)
    (hp₀ : p₀ ∈ Finset.univ.biUnion (fun k => (m k).primeFactors))
    (hq : q.Prime ∧ Odd q) (hqp : q < p₀)
    (hqnew : q ∉ Finset.univ.biUnion (fun k => (m k).primeFactors)) :
    ∃ N, Erdos7Reduction.HasOddArithmeticCover N (Fintype.card κ - 1) := by
  classical
  let P := Finset.univ.biUnion (fun k => (m k).primeFactors)
  let p (i : P) := i.val
  let e (k : κ) (i : P) := (m k).factorization i.val
  let E (i : P) := Finset.univ.sup (fun k => e k i)
  have hp (i : P) : (p i).Prime ∧ Odd (p i) := by
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp i.property
    have hh := Nat.mem_primeFactors.mp hk
    exact ⟨hh.1, (hc.2.1 k).2.of_dvd_nat hh.2.1⟩
  have he (k : κ) (i : P) : e k i ≤ E i :=
    Finset.le_sup (f := fun k => e k i) (Finset.mem_univ k)
  have hprod (k : κ) : m k = ∏ i : P, p i ^ e k i := by
    apply factorization_product_over_superset (m k) (by have := (hc.2.1 k).1; omega) P
    intro r hr
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hr⟩
  have hei : Function.Injective e := by
    intro k l hkl
    apply hc.1
    rw [hprod k, hprod l, hkl]
  have he0 (k : κ) : ∃ i : P, e k i ≠ 0 := by
    by_contra! h
    have hh := (hc.2.1 k).1
    rw [hprod k] at hh
    simp only [h, pow_zero, Finset.prod_const_one] at hh
    omega
  let i₀ : P := ⟨p₀, hp₀⟩
  have hused : ∃ k, e k i₀ ≠ 0 := by
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hp₀
    refine ⟨k, ?_⟩
    apply Nat.ne_of_gt
    exact (hp i₀).1.factorization_pos_of_dvd
      (by have := (hc.2.1 k).1; omega) (Nat.mem_primeFactors.mp hk).2.1
  have hnew : ∀ i : P, p i ≠ q := by
    intro i hi
    exact hqnew (hi ▸ i.property)
  have hcov : ∀ x : ℤ, ∃ k, ((∏ i : P, p i ^ e k i : ℕ) : ℤ) ∣ x - a k := by
    simpa only [← hprod] using hc.2.2
  obtain ⟨k₀, b, hb⟩ := compress_to_unused_smaller_prime p hp Subtype.val_injective E
    e he hei he0 a hcov q hq hnew i₀ hqp hused
  let n (k : {k // k ≠ k₀}) := ∏ i : P, Function.update p i₀ q i ^ e k.val i
  let N := Finset.univ.lcm n
  have hN0 : N ≠ 0 := Finset.lcm_ne_zero_iff.mpr (by
    intro k _
    have hh := (hb.2.1 k).1
    change 1 < n k at hh
    omega)
  refine ⟨N, Nat.pos_of_ne_zero hN0, {k // k ≠ k₀}, inferInstance, n, b,
    hb.1, hb.2.1, hb.2.2, fun k => Finset.dvd_lcm (Finset.mem_univ k), ?_⟩
  exact le_of_eq (Set.card_ne_eq k₀)

/-- Minimum-cardinality odd covers cannot skip an odd prime. -/
theorem minimal_cardinality_prime_support_initial {κ : Type} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : Erdos7Reduction.IsOddArithmeticCover m a)
    (hmin : ∀ N K, Erdos7Reduction.HasOddArithmeticCover N K → Fintype.card κ ≤ K) :
    ∀ p ∈ Finset.univ.biUnion (fun k => (m k).primeFactors),
      ∀ q, q.Prime → Odd q → q < p →
        q ∈ Finset.univ.biUnion (fun k => (m k).primeFactors) := by
  classical
  intro p hp q hq hoq hqp
  by_contra hqnew
  obtain ⟨N, hN⟩ := prime_gap_reduces_cardinality m a hc p q hp ⟨hq, hoq⟩ hqp hqnew
  have hh := hmin N (Fintype.card κ - 1) hN
  haveI : Nonempty κ := by obtain ⟨k, _⟩ := hc.2.2 0; exact ⟨k⟩
  have hpos : 0 < Fintype.card κ := Fintype.card_pos
  omega

/-- A hypothetical odd cover admits a globally minimum-cardinality,
irredundant, divisor-closed normal form with no gaps in its odd-prime support.
The lcm remains bounded in terms of the original cardinality bound. -/
theorem exists_prime_initial_minimal_odd_cover (N K : ℕ)
    (h : Erdos7Reduction.HasOddArithmeticCover N K) :
    ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ) (a : ι → ℤ),
      Erdos7Reduction.IsOddArithmeticCover m a ∧ Fintype.card ι ≤ K ∧
      (∀ M L, Erdos7Reduction.HasOddArithmeticCover M L → Fintype.card ι ≤ L) ∧
      (∀ i d, 1 < d → d ∣ m i → ∃ j, m j = d) ∧
      (∀ i, ∃ x : ℤ, ∀ j, j ≠ i → ¬ (m j : ℤ) ∣ x - a j) ∧
      (∀ p ∈ Finset.univ.biUnion (fun i => (m i).primeFactors),
        ∀ q, q.Prime → Odd q → q < p →
          q ∈ Finset.univ.biUnion (fun i => (m i).primeFactors)) ∧
      Finset.univ.lcm m ≤ 3 ^ ((K - 1) / 2) := by
  classical
  have hex : ∃ k, ∃ M, Erdos7Reduction.HasOddArithmeticCover M k := ⟨K, N, h⟩
  obtain ⟨M, hM⟩ := Nat.find_spec hex
  obtain ⟨ι, fι, m, a, hc, _, hcard, hclosed, hpriv⟩ :=
    Erdos7Reduction.exists_irredundant_divisor_closed_odd_cover M (Nat.find hex) hM
  letI : Fintype ι := fι
  have hmin : ∀ M L, Erdos7Reduction.HasOddArithmeticCover M L → Fintype.card ι ≤ L := by
    intro M L hL
    exact hcard.trans (Nat.find_min' hex ⟨M, hL⟩)
  have hcardK := hmin N K h
  refine ⟨ι, fι, m, a, hc, hcardK, hmin, hclosed, hpriv,
    minimal_cardinality_prime_support_initial m a hc hmin, ?_⟩
  have hb := irredundant_odd_period_bound m a
    (fun i => by have := (hc.2.1 i).1; omega) (fun i => (hc.2.1 i).2) hc.2.2 hpriv
  exact hb.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

#print axioms shrink_alphabets_delete_class
#print axioms shrink_odd_cover_delete_class
#print axioms compress_to_unused_smaller_prime
#print axioms prime_gap_reduces_cardinality
#print axioms minimal_cardinality_prime_support_initial
#print axioms exists_prime_initial_minimal_odd_cover
end Erdos7Compression


/- Highest-digit restrictions and necessary collision conditions. -/
namespace Erdos7TopDigit
open Erdos7Digits Erdos7Compression Erdos7Reduction

/-- Cap one coordinate of an exponent vector. -/
def clampExponent {ι : Type*} [DecidableEq ι] (i₀ : ι) (t : ℕ) (e : ι → ℕ) : ι → ℕ :=
  Function.update e i₀ (min (e i₀) t)

@[simp] theorem clampExponent_self {ι : Type*} [DecidableEq ι]
    (i₀ : ι) (t : ℕ) (e : ι → ℕ) : clampExponent i₀ t e i₀ = min (e i₀) t := by
  simp [clampExponent]

theorem clampExponent_of_ne {ι : Type*} [DecidableEq ι]
    (i₀ : ι) (t : ℕ) (e : ι → ℕ) {i : ι} (hi : i ≠ i₀) :
    clampExponent i₀ t e i = e i := by simp [clampExponent, hi]

theorem clampExponent_le {ι : Type*} [DecidableEq ι]
    (i₀ : ι) (t : ℕ) (e : ι → ℕ) (i : ι) : clampExponent i₀ t e i ≤ e i := by
  by_cases hi : i = i₀
  · subst i; simp
  · rw [clampExponent_of_ne i₀ t e hi]

theorem clampExponent_eq_self {ι : Type*} [DecidableEq ι]
    (i₀ : ι) (t : ℕ) (e : ι → ℕ) (he : e i₀ ≤ t) : clampExponent i₀ t e = e := by
  ext i
  by_cases hi : i = i₀
  · subst i; simp [min_eq_left he]
  · exact clampExponent_of_ne i₀ t e hi

/-- Fix the top digit of one prime coordinate and delete it. The surviving
congruences keep their original residues and have that exponent capped. -/
theorem restrict_highest_digit_cover {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p E : ι → ℕ) (hp : ∀ i, 0 < p i)
    (hcp : Pairwise (Function.onFun Nat.Coprime p)) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k)
    (i₀ : ι) (t : ℕ) (hE : E i₀ = t + 1) (r : Fin (p i₀)) :
    ∀ x : ℤ, ∃ k,
      (e k i₀ ≤ t ∨ zmodDigits (p i₀) (E i₀) (a k)
        ⟨t, by omega⟩ = r) ∧
      ((∏ i, p i ^ clampExponent i₀ t (e k) i : ℕ) : ℤ) ∣ x - a k := by
  classical
  intro x
  let D := Σ i, Fin (E i)
  let d₀ : D := ⟨i₀, ⟨t, by omega⟩⟩
  let X (d : D) : Fin (p d.1) := zmodDigits (p d.1) (E d.1) x d.2
  let Y (i : ι) (j : Fin (E i)) : Fin (p i) := Function.update X d₀ r ⟨i, j⟩
  obtain ⟨z, hz⟩ := exists_integer_with_digits p E hp hcp Y
  obtain ⟨k, hk⟩ := hc z
  have hkd := (divisor_product_iff_digits p E (e k) (he k) hcp z (a k)).mp hk
  refine ⟨k, ?_, (divisor_product_iff_digits p E (clampExponent i₀ t (e k))
    (fun i => (clampExponent_le i₀ t (e k) i).trans (he k i)) hcp x (a k)).mpr ?_⟩
  · by_cases hkt : e k i₀ ≤ t
    · exact Or.inl hkt
    · right
      have hj : t < e k i₀ := by omega
      have hh := hkd i₀ ⟨t, by omega⟩ hj
      rw [hz] at hh
      have hY : Y i₀ ⟨t, by omega⟩ = r := Function.update_self d₀ r X
      exact hh.symm.trans hY
  · intro i j hj
    have hdne : (⟨i, j⟩ : D) ≠ d₀ := by
      intro hd
      have hi : i = i₀ := congrArg Sigma.fst hd
      have ht : j.val = t := congrArg (fun d : D => d.2.val) hd
      subst i
      rw [clampExponent_self] at hj
      omega
    have hh := hkd i j (hj.trans_le (clampExponent_le i₀ t (e k) i))
    rw [hz] at hh
    dsimp only [Y] at hh
    rw [Function.update_of_ne hdne] at hh
    exact hh

/-- A collision-free, nonunit highest-digit restriction is again an odd
strict cover with no more classes and a strictly smaller common period. -/
theorem safe_highest_digit_restriction {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p E : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k)
    (i₀ : ι) (t : ℕ) (hE : E i₀ = t + 1) (r : Fin (p i₀))
    (hunit : ∀ k, (e k i₀ ≤ t ∨ zmodDigits (p i₀) (E i₀) (a k) ⟨t, by omega⟩ = r) →
      ∃ i, clampExponent i₀ t (e k) i ≠ 0)
    (hinj : ∀ k l,
      (e k i₀ ≤ t ∨ zmodDigits (p i₀) (E i₀) (a k) ⟨t, by omega⟩ = r) →
      (e l i₀ ≤ t ∨ zmodDigits (p i₀) (E i₀) (a l) ⟨t, by omega⟩ = r) →
      clampExponent i₀ t (e k) = clampExponent i₀ t (e l) → k = l) :
    ∃ N < ∏ i, p i ^ E i, HasOddArithmeticCover N (Fintype.card κ) := by
  classical
  let active (k : κ) := e k i₀ ≤ t ∨
    zmodDigits (p i₀) (E i₀) (a k) ⟨t, by omega⟩ = r
  let E' := Function.update E i₀ t
  let N := ∏ i, p i ^ E' i
  let n (k : {k // active k}) := ∏ i, p i ^ clampExponent i₀ t (e k.val) i
  have hcq : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i).1 (hp j).1).mpr (fun h => hij (hpi h))
  have hE' (i : ι) : E' i ≤ E i := by
    by_cases hi : i = i₀
    · subst i; simp only [E', Function.update_self]; omega
    · simp [E', hi]
  have hnewle (k : κ) (i : ι) : clampExponent i₀ t (e k) i ≤ E' i := by
    by_cases hi : i = i₀
    · subst i; simp [E']
    · simpa [E', clampExponent, hi] using he k i
  have hNpos : 0 < N := Finset.prod_pos (fun i _ => pow_pos (hp i).1.pos _)
  have hNlt : N < ∏ i, p i ^ E i := by
    apply Finset.prod_lt_prod (fun i _ => pow_pos (hp i).1.pos _)
      (fun i _ => Nat.pow_le_pow_right (hp i).1.pos (hE' i))
    refine ⟨i₀, Finset.mem_univ _, ?_⟩
    simp only [E', Function.update_self, hE]
    exact Nat.pow_lt_pow_right (hp i₀).1.one_lt (by omega)
  refine ⟨N, hNlt, hNpos, {k // active k}, inferInstance, n, (fun k => a k.val),
    ?_, ?_, ?_, ?_, Fintype.card_subtype_le _⟩
  · intro k l hkl
    apply Subtype.ext
    apply hinj k.val l.val k.property l.property
    funext i
    have hh := congrArg (fun m : ℕ => m.factorization (p i)) hkl
    simpa only [n, factorization_prime_power_product p (fun i => (hp i).1) hpi] using hh
  · intro k
    have hnpos : 0 < n k := Finset.prod_pos (fun i _ => pow_pos (hp i).1.pos _)
    have hnne : n k ≠ 1 := by
      intro h
      obtain ⟨i, hi⟩ := hunit k.val k.property
      have hh := factorization_prime_power_product p (fun i => (hp i).1) hpi
        (clampExponent i₀ t (e k.val)) i
      change (n k).factorization (p i) = _ at hh
      rw [h, Nat.factorization_one, Finsupp.zero_apply] at hh
      exact hi hh.symm
    refine ⟨by omega, ?_⟩
    exact Finset.prod_induction (fun i => p i ^ clampExponent i₀ t (e k.val) i) Odd
      (fun _ _ ha hb => ha.mul hb) (by norm_num) (fun i _ => (hp i).2.pow)
  · intro x
    obtain ⟨k, hk, hdiv⟩ := restrict_highest_digit_cover p E (fun i => (hp i).1.pos)
      hcq e he a hc i₀ t hE r x
    exact ⟨⟨k, hk⟩, hdiv⟩
  · intro k
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => pow_dvd_pow (p i) (hnewle k.val i))

/-- In a minimal-period cover, every highest-digit value must activate either
a unit after restriction, or a collision with a modulus one exponent level below. -/
theorem minimal_period_highest_digit_collision {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p E : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i)
    (hei : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k)
    (K : ℕ) (hcard : Fintype.card κ ≤ K)
    (hmin : ∀ N, N < ∏ i, p i ^ E i → ¬ HasOddArithmeticCover N K)
    (i₀ : ι) (t : ℕ) (hE : E i₀ = t + 1) (r : Fin (p i₀)) :
    ∃ k, e k i₀ = t + 1 ∧
      zmodDigits (p i₀) (E i₀) (a k) ⟨t, by omega⟩ = r ∧
      ((∀ i, clampExponent i₀ t (e k) i = 0) ∨
        ∃ l, e l i₀ = t ∧ clampExponent i₀ t (e k) = e l) := by
  classical
  by_contra hbad
  let active (k : κ) := e k i₀ ≤ t ∨
    zmodDigits (p i₀) (E i₀) (a k) ⟨t, by omega⟩ = r
  have hhigh (k : κ) (hk : ¬ e k i₀ ≤ t) : e k i₀ = t + 1 := by
    have hh := he k i₀
    omega
  have hr (k : κ) (hk : ¬ e k i₀ ≤ t) (hact : active k) :
      zmodDigits (p i₀) (E i₀) (a k) ⟨t, by omega⟩ = r := hact.resolve_left hk
  have hunit (k : κ) (hact : active k) : ∃ i, clampExponent i₀ t (e k) i ≠ 0 := by
    by_contra! hz
    by_cases hk : e k i₀ ≤ t
    · rw [clampExponent_eq_self i₀ t (e k) hk] at hz
      obtain ⟨i, hi⟩ := he0 k
      exact hi (hz i)
    · exact hbad ⟨k, hhigh k hk, hr k hk hact, Or.inl hz⟩
  have hcollision (k l : κ) (hk : ¬ e k i₀ ≤ t) (hl : e l i₀ ≤ t)
      (hact : active k) (heq : clampExponent i₀ t (e k) = clampExponent i₀ t (e l)) : False := by
    rw [clampExponent_eq_self i₀ t (e l) hl] at heq
    have hlval : e l i₀ = t := by
      have hh := congrFun heq i₀
      rw [clampExponent_self, hhigh k hk] at hh
      omega
    exact hbad ⟨k, hhigh k hk, hr k hk hact, Or.inr ⟨l, hlval, heq⟩⟩
  have hinj (k l : κ) (hkact : active k) (hlact : active l)
      (heq : clampExponent i₀ t (e k) = clampExponent i₀ t (e l)) : k = l := by
    by_cases hk : e k i₀ ≤ t <;> by_cases hl : e l i₀ ≤ t
    · rw [clampExponent_eq_self i₀ t (e k) hk, clampExponent_eq_self i₀ t (e l) hl] at heq
      exact hei heq
    · exact False.elim (hcollision l k hl hk hlact heq.symm)
    · exact False.elim (hcollision k l hk hl hkact heq)
    · apply hei
      funext i
      by_cases hi : i = i₀
      · subst i; rw [hhigh k hk, hhigh l hl]
      · have hh := congrFun heq i
        simpa only [clampExponent_of_ne i₀ t (e k) hi,
          clampExponent_of_ne i₀ t (e l) hi] using hh
  obtain ⟨N, hNlt, hN⟩ := safe_highest_digit_restriction p E hp hpi e he a hc i₀ t hE r hunit hinj
  apply hmin N hNlt
  obtain ⟨hNpos, ν, fν, n, b, hni, hn, hnc, hnN, hncard⟩ := hN
  exact ⟨hNpos, ν, fν, n, b, hni, hn, hnc, hnN, hncard.trans hcard⟩

/-- If the maximal exponent is at least two, the immediately preceding
exponent level also contains at least `p` moduli in a minimal-period cover. -/
theorem minimal_period_penultimate_layer_multiplicity {ι κ : Type}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p E : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i)
    (hei : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k)
    (K : ℕ) (hcard : Fintype.card κ ≤ K)
    (hmin : ∀ N, N < ∏ i, p i ^ E i → ¬ HasOddArithmeticCover N K)
    (i₀ : ι) (t : ℕ) (ht : 0 < t) (hE : E i₀ = t + 1) :
    p i₀ ≤ Fintype.card {k // e k i₀ = t} ∧
      p i₀ ≤ Fintype.card {k // e k i₀ = t + 1} := by
  classical
  have hpair (r : Fin (p i₀)) : ∃ k l, e k i₀ = t + 1 ∧
      zmodDigits (p i₀) (E i₀) (a k) ⟨t, by omega⟩ = r ∧
      e l i₀ = t ∧ clampExponent i₀ t (e k) = e l := by
    obtain ⟨k, hk, hkr, hunit | ⟨l, hl, hkl⟩⟩ :=
      minimal_period_highest_digit_collision p E hp hpi e he hei he0 a hc K hcard hmin i₀ t hE r
    · have hh := hunit i₀
      rw [clampExponent_self, hk] at hh
      omega
    · exact ⟨k, l, hk, hkr, hl, hkl⟩
  choose k l hk hkr hl hkl using hpair
  have hki : Function.Injective k := by
    intro r s hrs
    have hh := congrArg (fun k => zmodDigits (p i₀) (E i₀) (a k) ⟨t, by omega⟩) hrs
    simpa only [hkr] using hh
  have hli : Function.Injective l := by
    intro r s hrs
    apply hki
    apply hei
    have hh : clampExponent i₀ t (e (k r)) = clampExponent i₀ t (e (k s)) := by
      rw [hkl r, hkl s, hrs]
    funext i
    by_cases hi : i = i₀
    · subst i; rw [hk r, hk s]
    · have hh' := congrFun hh i
      simpa only [clampExponent_of_ne i₀ t (e (k r)) hi,
        clampExponent_of_ne i₀ t (e (k s)) hi] using hh'
  constructor
  · let f (r : Fin (p i₀)) : {k // e k i₀ = t} := ⟨l r, hl r⟩
    have hfi : Function.Injective f := fun _ _ h => hli (congrArg Subtype.val h)
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hfi
  · let f (r : Fin (p i₀)) : {k // e k i₀ = t + 1} := ⟨k r, hk r⟩
    have hfi : Function.Injective f := fun _ _ h => hki (congrArg Subtype.val h)
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hfi

#print axioms restrict_highest_digit_cover
#print axioms safe_highest_digit_restriction
#print axioms minimal_period_highest_digit_collision
#print axioms minimal_period_penultimate_layer_multiplicity
end Erdos7TopDigit


/- Restrictions at arbitrary prime-adic digit levels. -/
namespace Erdos7AllDigits
open Erdos7Digits Erdos7Compression Erdos7Reduction

/-- The exponent after deleting the digit at position `t`. -/
def eraseLevel (t e : ℕ) : ℕ := if e ≤ t then e else e - 1

theorem eraseLevel_le (t e : ℕ) : eraseLevel t e ≤ e := by
  unfold eraseLevel
  split_ifs <;> omega

/-- Insert a digit, discarding the unused last entry of the ambient vector. -/
def insertDigit {α : Type*} {n : ℕ} (t : Fin n) (r : α) (x : Fin n → α)
    (j : Fin n) : α :=
  if j.val < t.val then x j else if j = t then r else
    x ⟨j.val - 1, by have := j.isLt; omega⟩

/-- Delete a digit, filling the unused last entry with an arbitrary default. -/
def deleteDigit {α : Type*} {n : ℕ} (t : Fin n) (d : α) (x : Fin n → α)
    (j : Fin n) : α :=
  if j.val < t.val then x j else if h : j.val + 1 < n then x ⟨j.val + 1, h⟩ else d

@[simp] theorem insertDigit_self {α : Type*} {n : ℕ} (t : Fin n) (r : α)
    (x : Fin n → α) : insertDigit t r x t = r := by simp [insertDigit]

theorem insertDigit_successor {α : Type*} {n : ℕ} (t : Fin n) (r : α)
    (x : Fin n → α) (j : Fin n) (hjt : t.val ≤ j.val) (hjn : j.val + 1 < n) :
    insertDigit t r x ⟨j.val + 1, hjn⟩ = x j := by
  have hlt : ¬ j.val + 1 < t.val := by omega
  have hne : (⟨j.val + 1, hjn⟩ : Fin n) ≠ t := by
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_mk] at hh
    omega
  simp only [insertDigit, Fin.val_mk, if_neg hlt, if_neg hne, Nat.add_sub_cancel]

/-- Prefix agreement survives insertion/deletion of a coordinate. -/
theorem prefix_agreement_after_deletion {α : Type*} {n : ℕ} (t : Fin n)
    (r d : α) (x a : Fin n → α) (e : ℕ) (hen : e ≤ n)
    (hmatch : ∀ j : Fin n, j.val < e → insertDigit t r x j = a j) :
    ∀ j : Fin n, j.val < eraseLevel t.val e → x j = deleteDigit t d a j := by
  intro j hj
  by_cases hjt : j.val < t.val
  · have hje : j.val < e := hj.trans_le (eraseLevel_le _ _)
    have hh := hmatch j hje
    simpa only [insertDigit, deleteDigit, if_pos hjt] using hh
  · have hje : j.val + 1 < e := by
      unfold eraseLevel at hj
      split_ifs at hj <;> omega
    have hjn : j.val + 1 < n := by omega
    have hh := hmatch ⟨j.val + 1, hjn⟩ hje
    rw [insertDigit_successor t r x j (by omega) hjn] at hh
    simpa only [deleteDigit, if_neg hjt, dif_pos hjn] using hh

/-- Remove one digit level from one coordinate of an exponent vector. -/
def eraseExponent {ι : Type*} [DecidableEq ι] (i₀ : ι) (t : ℕ) (e : ι → ℕ) : ι → ℕ :=
  Function.update e i₀ (eraseLevel t (e i₀))

@[simp] theorem eraseExponent_self {ι : Type*} [DecidableEq ι]
    (i₀ : ι) (t : ℕ) (e : ι → ℕ) : eraseExponent i₀ t e i₀ = eraseLevel t (e i₀) := by
  simp [eraseExponent]

theorem eraseExponent_of_ne {ι : Type*} [DecidableEq ι]
    (i₀ : ι) (t : ℕ) (e : ι → ℕ) {i : ι} (hi : i ≠ i₀) :
    eraseExponent i₀ t e i = e i := by simp [eraseExponent, hi]

theorem eraseExponent_le {ι : Type*} [DecidableEq ι]
    (i₀ : ι) (t : ℕ) (e : ι → ℕ) (i : ι) : eraseExponent i₀ t e i ≤ e i := by
  by_cases hi : i = i₀
  · subst i; rw [eraseExponent_self]; exact eraseLevel_le t (e i₀)
  · rw [eraseExponent_of_ne i₀ t e hi]

theorem eraseExponent_eq_self {ι : Type*} [DecidableEq ι]
    (i₀ : ι) (t : ℕ) (e : ι → ℕ) (he : e i₀ ≤ t) : eraseExponent i₀ t e = e := by
  ext i
  by_cases hi : i = i₀
  · subst i; simp [eraseLevel, he]
  · exact eraseExponent_of_ne i₀ t e hi

/-- Restrict any digit, then delete that digit from the surviving congruences.
Unlike highest-digit restriction, this generally changes the residues. -/
theorem restrict_arbitrary_digit_cover {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p E : ι → ℕ) (hp : ∀ i, 0 < p i)
    (hcp : Pairwise (Function.onFun Nat.Coprime p)) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k)
    (i₀ : ι) (t : Fin (E i₀)) (r : Fin (p i₀)) :
    ∃ b : κ → ℤ, ∀ x : ℤ, ∃ k,
      (e k i₀ ≤ t.val ∨ zmodDigits (p i₀) (E i₀) (a k) t = r) ∧
      ((∏ i, p i ^ eraseExponent i₀ t.val (e k) i : ℕ) : ℤ) ∣ x - b k := by
  classical
  let A (k : κ) (i : ι) := zmodDigits (p i) (E i) (a k : ZMod (p i ^ E i))
  let B (k : κ) := Function.update (A k) i₀ (deleteDigit t 0 (A k i₀))
  choose b hb using fun k => exists_integer_with_digits p E hp hcp (B k)
  refine ⟨b, fun x => ?_⟩
  let X (i : ι) := zmodDigits (p i) (E i) (x : ZMod (p i ^ E i))
  let Y := Function.update X i₀ (insertDigit t r (X i₀))
  obtain ⟨z, hz⟩ := exists_integer_with_digits p E hp hcp Y
  obtain ⟨k, hk⟩ := hc z
  have hkd := (divisor_product_iff_digits p E (e k) (he k) hcp z (a k)).mp hk
  have hmatch : ∀ j : Fin (E i₀), j.val < e k i₀ →
      insertDigit t r (X i₀) j = A k i₀ j := by
    intro j hj
    have hh := hkd i₀ j hj
    rw [hz] at hh
    simpa only [Y, Function.update_self] using hh
  refine ⟨k, ?_, (divisor_product_iff_digits p E (eraseExponent i₀ t.val (e k))
    (fun i => (eraseExponent_le i₀ t.val (e k) i).trans (he k i)) hcp x (b k)).mpr ?_⟩
  · by_cases hkt : e k i₀ ≤ t.val
    · exact Or.inl hkt
    · right
      have hh := hmatch t (by omega)
      rw [insertDigit_self] at hh
      exact hh.symm
  · intro i j hj
    rw [hb]
    by_cases hi : i = i₀
    · subst i
      change X i₀ j = B k i₀ j
      dsimp only [B]
      rw [Function.update_self]
      rw [eraseExponent_self] at hj
      exact prefix_agreement_after_deletion t r 0 (X i₀) (A k i₀) (e k i₀)
        (he k i₀) hmatch j hj
    · have hh := hkd i j (hj.trans_le (eraseExponent_le i₀ t.val (e k) i))
      rw [hz] at hh
      simp only [Y, Function.update_of_ne hi] at hh
      change X i j = B k i j
      simpa only [B, Function.update_of_ne hi] using hh

/-- If an arbitrary-digit restriction has neither units nor repeated exponent
vectors among its active classes, it gives a smaller-period odd strict cover. -/
theorem safe_arbitrary_digit_restriction {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p E : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k)
    (i₀ : ι) (t : Fin (E i₀)) (r : Fin (p i₀))
    (hunit : ∀ k, (e k i₀ ≤ t.val ∨ zmodDigits (p i₀) (E i₀) (a k) t = r) →
      ∃ i, eraseExponent i₀ t.val (e k) i ≠ 0)
    (hinj : ∀ k l,
      (e k i₀ ≤ t.val ∨ zmodDigits (p i₀) (E i₀) (a k) t = r) →
      (e l i₀ ≤ t.val ∨ zmodDigits (p i₀) (E i₀) (a l) t = r) →
      eraseExponent i₀ t.val (e k) = eraseExponent i₀ t.val (e l) → k = l) :
    ∃ N < ∏ i, p i ^ E i, HasOddArithmeticCover N (Fintype.card κ) := by
  classical
  let active (k : κ) := e k i₀ ≤ t.val ∨ zmodDigits (p i₀) (E i₀) (a k) t = r
  let E' := Function.update E i₀ (E i₀ - 1)
  let N := ∏ i, p i ^ E' i
  let n (k : {k // active k}) := ∏ i, p i ^ eraseExponent i₀ t.val (e k.val) i
  have hcq : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i).1 (hp j).1).mpr (fun h => hij (hpi h))
  obtain ⟨b, hb⟩ := restrict_arbitrary_digit_cover p E (fun i => (hp i).1.pos)
    hcq e he a hc i₀ t r
  have hE' (i : ι) : E' i ≤ E i := by
    by_cases hi : i = i₀
    · subst i; simp [E']
    · simp [E', hi]
  have hnewle (k : κ) (i : ι) : eraseExponent i₀ t.val (e k) i ≤ E' i := by
    by_cases hi : i = i₀
    · subst i
      simp only [eraseExponent_self, E', Function.update_self]
      unfold eraseLevel
      have hh := he k i₀
      have ht := t.isLt
      split_ifs <;> omega
    · simpa [E', eraseExponent, hi] using he k i
  have hNpos : 0 < N := Finset.prod_pos (fun i _ => pow_pos (hp i).1.pos _)
  have hNlt : N < ∏ i, p i ^ E i := by
    apply Finset.prod_lt_prod (fun i _ => pow_pos (hp i).1.pos _)
      (fun i _ => Nat.pow_le_pow_right (hp i).1.pos (hE' i))
    refine ⟨i₀, Finset.mem_univ _, ?_⟩
    simp only [E', Function.update_self]
    exact Nat.pow_lt_pow_right (hp i₀).1.one_lt (by have := t.isLt; omega)
  refine ⟨N, hNlt, hNpos, {k // active k}, inferInstance, n, (fun k => b k.val),
    ?_, ?_, ?_, ?_, Fintype.card_subtype_le _⟩
  · intro k l hkl
    apply Subtype.ext
    apply hinj k.val l.val k.property l.property
    funext i
    have hh := congrArg (fun m : ℕ => m.factorization (p i)) hkl
    simpa only [n, factorization_prime_power_product p (fun i => (hp i).1) hpi] using hh
  · intro k
    have hnpos : 0 < n k := Finset.prod_pos (fun i _ => pow_pos (hp i).1.pos _)
    have hnne : n k ≠ 1 := by
      intro h
      obtain ⟨i, hi⟩ := hunit k.val k.property
      have hh := factorization_prime_power_product p (fun i => (hp i).1) hpi
        (eraseExponent i₀ t.val (e k.val)) i
      change (n k).factorization (p i) = _ at hh
      rw [h, Nat.factorization_one, Finsupp.zero_apply] at hh
      exact hi hh.symm
    refine ⟨by omega, ?_⟩
    exact Finset.prod_induction (fun i => p i ^ eraseExponent i₀ t.val (e k.val) i) Odd
      (fun _ _ ha hb => ha.mul hb) (by norm_num) (fun i _ => (hp i).2.pow)
  · intro x
    obtain ⟨k, hk, hdiv⟩ := hb x
    exact ⟨⟨k, hk⟩, hdiv⟩
  · intro k
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => pow_dvd_pow (p i) (hnewle k.val i))

/-- Every value at every digit level of a minimal-period cover forces a unit
or a collision across the two adjacent exponent levels. -/
theorem minimal_period_every_digit_collision {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p E : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i)
    (hei : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k)
    (K : ℕ) (hcard : Fintype.card κ ≤ K)
    (hmin : ∀ N, N < ∏ i, p i ^ E i → ¬ HasOddArithmeticCover N K)
    (i₀ : ι) (t : Fin (E i₀)) (r : Fin (p i₀)) :
    ∃ k, e k i₀ = t.val + 1 ∧ zmodDigits (p i₀) (E i₀) (a k) t = r ∧
      ((∀ i, eraseExponent i₀ t.val (e k) i = 0) ∨
        ∃ l, e l i₀ = t.val ∧ eraseExponent i₀ t.val (e k) = e l) := by
  classical
  by_contra hbad
  let active (k : κ) := e k i₀ ≤ t.val ∨ zmodDigits (p i₀) (E i₀) (a k) t = r
  have hr (k : κ) (hk : ¬ e k i₀ ≤ t.val) (hact : active k) :
      zmodDigits (p i₀) (E i₀) (a k) t = r := hact.resolve_left hk
  have hunit (k : κ) (hact : active k) : ∃ i, eraseExponent i₀ t.val (e k) i ≠ 0 := by
    by_contra! hz
    by_cases hk : e k i₀ ≤ t.val
    · rw [eraseExponent_eq_self i₀ t.val (e k) hk] at hz
      obtain ⟨i, hi⟩ := he0 k
      exact hi (hz i)
    · have hh := hz i₀
      simp only [eraseExponent_self, eraseLevel, if_neg hk] at hh
      have heq : e k i₀ = t.val + 1 := by omega
      exact hbad ⟨k, heq, hr k hk hact, Or.inl hz⟩
  have hcollision (k l : κ) (hk : ¬ e k i₀ ≤ t.val) (hl : e l i₀ ≤ t.val)
      (hact : active k) (heq : eraseExponent i₀ t.val (e k) = eraseExponent i₀ t.val (e l)) :
      False := by
    rw [eraseExponent_eq_self i₀ t.val (e l) hl] at heq
    have hh := congrFun heq i₀
    simp only [eraseExponent_self, eraseLevel, if_neg hk] at hh
    have hkval : e k i₀ = t.val + 1 := by omega
    have hlval : e l i₀ = t.val := by omega
    exact hbad ⟨k, hkval, hr k hk hact, Or.inr ⟨l, hlval, heq⟩⟩
  have hinj (k l : κ) (hkact : active k) (hlact : active l)
      (heq : eraseExponent i₀ t.val (e k) = eraseExponent i₀ t.val (e l)) : k = l := by
    by_cases hk : e k i₀ ≤ t.val <;> by_cases hl : e l i₀ ≤ t.val
    · rw [eraseExponent_eq_self i₀ t.val (e k) hk, eraseExponent_eq_self i₀ t.val (e l) hl] at heq
      exact hei heq
    · exact False.elim (hcollision l k hl hk hlact heq.symm)
    · exact False.elim (hcollision k l hk hl hkact heq)
    · apply hei
      funext i
      have hh := congrFun heq i
      by_cases hi : i = i₀
      · subst i
        simp only [eraseExponent_self, eraseLevel, if_neg hk, if_neg hl] at hh
        omega
      · simpa only [eraseExponent_of_ne i₀ t.val (e k) hi,
          eraseExponent_of_ne i₀ t.val (e l) hi] using hh
  obtain ⟨N, hNlt, hN⟩ := safe_arbitrary_digit_restriction p E hp hpi e he a hc i₀ t r hunit hinj
  apply hmin N hNlt
  obtain ⟨hNpos, ν, fν, n, b, hni, hn, hnc, hnN, hncard⟩ := hN
  exact ⟨hNpos, ν, fν, n, b, hni, hn, hnc, hnN, hncard.trans hcard⟩

/-- Every positive exponent level in a minimal-period odd cover has at least
as many moduli as the underlying prime. -/
theorem minimal_period_adjacent_layer_multiplicity {ι κ : Type}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p E : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i)
    (hei : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k)
    (K : ℕ) (hcard : Fintype.card κ ≤ K)
    (hmin : ∀ N, N < ∏ i, p i ^ E i → ¬ HasOddArithmeticCover N K)
    (i₀ : ι) (t : Fin (E i₀)) :
    p i₀ ≤ Fintype.card {k // e k i₀ = t.val + 1} ∧
      (0 < t.val → p i₀ ≤ Fintype.card {k // e k i₀ = t.val}) := by
  classical
  have hpair := minimal_period_every_digit_collision p E hp hpi e he hei he0 a hc
    K hcard hmin i₀ t
  choose k hk hkr hkl using hpair
  have hki : Function.Injective k := by
    intro r s hrs
    have hh := congrArg (fun k => zmodDigits (p i₀) (E i₀) (a k) t) hrs
    simpa only [hkr] using hh
  constructor
  · let f (r : Fin (p i₀)) : {k // e k i₀ = t.val + 1} := ⟨k r, hk r⟩
    have hfi : Function.Injective f := fun _ _ h => hki (congrArg Subtype.val h)
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hfi
  · intro ht
    have hex (r : Fin (p i₀)) : ∃ l, e l i₀ = t.val ∧ eraseExponent i₀ t.val (e (k r)) = e l := by
      rcases hkl r with hunit | hcoll
      · have hh := hunit i₀
        rw [eraseExponent_self, eraseLevel, if_neg (by have := hk r; omega), hk r] at hh
        omega
      · exact hcoll
    choose l hl hle using hex
    have hli : Function.Injective l := by
      intro r s hrs
      apply hki
      apply hei
      have hh : eraseExponent i₀ t.val (e (k r)) = eraseExponent i₀ t.val (e (k s)) := by
        rw [hle r, hle s, hrs]
      funext i
      by_cases hi : i = i₀
      · subst i; rw [hk r, hk s]
      · have hh' := congrFun hh i
        simpa only [eraseExponent_of_ne i₀ t.val (e (k r)) hi,
          eraseExponent_of_ne i₀ t.val (e (k s)) hi] using hh'
    let f (r : Fin (p i₀)) : {k // e k i₀ = t.val} := ⟨l r, hl r⟩
    have hfi : Function.Injective f := fun _ _ h => hli (congrArg Subtype.val h)
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hfi

/-- At exponent zero the same argument allows at most one unit exception. -/
theorem minimal_period_zero_layer_multiplicity {ι κ : Type}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p E : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i)
    (hei : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k)
    (K : ℕ) (hcard : Fintype.card κ ≤ K)
    (hmin : ∀ N, N < ∏ i, p i ^ E i → ¬ HasOddArithmeticCover N K)
    (i₀ : ι) (hE : 0 < E i₀) :
    p i₀ - 1 ≤ Fintype.card {k // e k i₀ = 0} := by
  classical
  let t : Fin (E i₀) := ⟨0, hE⟩
  have hpair := minimal_period_every_digit_collision p E hp hpi e he hei he0 a hc
    K hcard hmin i₀ t
  choose k hk hkr hkl using hpair
  let V (r : Fin (p i₀)) := eraseExponent i₀ 0 (e (k r))
  have hVi : Function.Injective V := by
    intro r s hrs
    have hks : k r = k s := by
      apply hei
      funext i
      by_cases hi : i = i₀
      · subst i; rw [hk r, hk s]
      · have hh := congrFun hrs i
        simpa only [V, eraseExponent_of_ne i₀ 0 (e (k r)) hi,
          eraseExponent_of_ne i₀ 0 (e (k s)) hi] using hh
    have hh := congrArg (fun k => zmodDigits (p i₀) (E i₀) (a k) t) hks
    simpa only [hkr] using hh
  let L := Finset.univ.filter (fun k => e k i₀ = 0)
  let T := insert (fun _ : ι => 0) (L.image e)
  have hpT : p i₀ ≤ T.card := by
    have hle : (Finset.univ : Finset (Fin (p i₀))).card ≤ T.card := by
      apply Finset.card_le_card_of_injOn V
      · intro r _
        rcases hkl r with hz | ⟨l, hl, hvl⟩
        · apply Finset.mem_insert.mpr
          left
          exact funext hz
        · apply Finset.mem_insert.mpr
          right
          exact Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩, hvl.symm⟩
      · exact hVi.injOn
    simpa only [Finset.card_univ, Fintype.card_fin] using hle
  have hTcard : T.card ≤ Fintype.card {k // e k i₀ = 0} + 1 := by
    have hh := Finset.card_insert_le (fun _ : ι => 0) (L.image e)
    simpa only [T, L, Finset.card_image_of_injective _ hei, Fintype.card_subtype] using hh
  omega

/-- Summing the forced layer occupancies gives a prime/exponent class-count
bound in every minimal-period cover. -/
theorem minimal_period_prime_exponent_card_bound {ι κ : Type}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p E : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i)
    (hei : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k)
    (K : ℕ) (hcard : Fintype.card κ ≤ K)
    (hmin : ∀ N, N < ∏ i, p i ^ E i → ¬ HasOddArithmeticCover N K)
    (i₀ : ι) (hE : 0 < E i₀) :
    (E i₀ + 1) * p i₀ - 1 ≤ Fintype.card κ := by
  classical
  let c (j : ℕ) := Fintype.card {k // e k i₀ = j}
  have hz : p i₀ - 1 ≤ c 0 := minimal_period_zero_layer_multiplicity
    p E hp hpi e he hei he0 a hc K hcard hmin i₀ hE
  have hpos (j : ℕ) (hj : j < E i₀) : p i₀ ≤ c (j + 1) :=
    (minimal_period_adjacent_layer_multiplicity p E hp hpi e he hei he0 a hc
      K hcard hmin i₀ ⟨j, hj⟩).1
  have hsum : Fintype.card κ = ∑ j ∈ Finset.range (E i₀ + 1), c j := by
    have hh := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset κ))
      (t := Finset.range (E i₀ + 1)) (f := fun k => e k i₀) (by
        intro k _
        exact Finset.mem_range.mpr (by change e k i₀ < E i₀ + 1; have := he k i₀; omega))
    simpa only [Finset.card_univ, c, Fintype.card_subtype] using hh
  rw [Finset.sum_range_succ'] at hsum
  have hsumle : E i₀ * p i₀ ≤ ∑ j ∈ Finset.range (E i₀), c (j + 1) := by
    calc
      E i₀ * p i₀ = ∑ _j ∈ Finset.range (E i₀), p i₀ := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j hj => hpos j (Finset.mem_range.mp hj))
  have hp0 := (hp i₀).1.pos
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Global cardinality minimization can be followed by period minimization
without losing irredundance, divisor closure, or the initial-prime property. -/
theorem exists_cardinality_period_minimal_odd_cover (N K : ℕ)
    (h : HasOddArithmeticCover N K) :
    ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ) (a : ι → ℤ),
      IsOddArithmeticCover m a ∧ Fintype.card ι ≤ K ∧
      (∀ M L, HasOddArithmeticCover M L → Fintype.card ι ≤ L) ∧
      (∀ M, M < Finset.univ.lcm m → ¬ HasOddArithmeticCover M (Fintype.card ι)) ∧
      (∀ i d, 1 < d → d ∣ m i → ∃ j, m j = d) ∧
      (∀ i, ∃ x : ℤ, ∀ j, j ≠ i → ¬ (m j : ℤ) ∣ x - a j) ∧
      (∀ p ∈ Finset.univ.biUnion (fun i => (m i).primeFactors),
        ∀ q, q.Prime → Odd q → q < p →
          q ∈ Finset.univ.biUnion (fun i => (m i).primeFactors)) := by
  classical
  have hex : ∃ k, ∃ M, HasOddArithmeticCover M k := ⟨K, N, h⟩
  have hexN : ∃ M, HasOddArithmeticCover M (Nat.find hex) := Nat.find_spec hex
  let M := Nat.find hexN
  have hM : HasOddArithmeticCover M (Nat.find hex) := Nat.find_spec hexN
  have hMpos : 0 < M := hM.1
  obtain ⟨ι, fι, m, a, hc, hmM, hcard, hclosed, hpriv⟩ :=
    exists_irredundant_divisor_closed_odd_cover M (Nat.find hex) hM
  letI : Fintype ι := fι
  have hmin : ∀ M L, HasOddArithmeticCover M L → Fintype.card ι ≤ L := by
    intro M L hL
    exact hcard.trans (Nat.find_min' hex ⟨M, hL⟩)
  have hperiod : ∀ L, L < Finset.univ.lcm m → ¬ HasOddArithmeticCover L (Fintype.card ι) := by
    intro L hL hcover
    have hle : Finset.univ.lcm m ≤ M :=
      Nat.le_of_dvd hMpos (Finset.lcm_dvd (fun i _ => hmM i))
    obtain ⟨hLpos, ν, fν, n, b, hni, hn, hnc, hnL, hncard⟩ := hcover
    have hnew : HasOddArithmeticCover L (Nat.find hex) :=
      ⟨hLpos, ν, fν, n, b, hni, hn, hnc, hnL, hncard.trans hcard⟩
    have hh : M ≤ L := Nat.find_min' hexN hnew
    omega
  exact ⟨ι, fι, m, a, hc, hmin N K h, hmin, hperiod, hclosed, hpriv,
    minimal_cardinality_prime_support_initial m a hc hmin⟩

/-- Arithmetic form of the all-layer class-count bound. -/
theorem arithmetic_minimal_period_prime_exponent_bound {κ : Type} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a)
    (hmin : ∀ M, M < Finset.univ.lcm m → ¬ HasOddArithmeticCover M (Fintype.card κ))
    (p₀ : ℕ) (hp₀ : p₀.Prime) (hpN : p₀ ∣ Finset.univ.lcm m) :
    ((Finset.univ.lcm m).factorization p₀ + 1) * p₀ - 1 ≤ Fintype.card κ := by
  classical
  let N := Finset.univ.lcm m
  have hm0 : ∀ k, m k ≠ 0 := fun k => by have := (hc.2.1 k).1; omega
  have hN0 : N ≠ 0 := Finset.lcm_ne_zero_iff.mpr (fun k _ => hm0 k)
  have hmN (k : κ) : m k ∣ N := Finset.dvd_lcm (Finset.mem_univ k)
  have hoN : Odd N := by
    have ho : Odd (∏ k, m k) := Finset.prod_induction m Odd
      (fun _ _ ha hb => ha.mul hb) (by norm_num) (fun k _ => (hc.2.1 k).2)
    exact ho.of_dvd_nat (Finset.lcm_dvd_prod Finset.univ m)
  let P := N.primeFactors
  let p (i : P) := i.val
  let E (i : P) := N.factorization i.val
  let e (k : κ) (i : P) := (m k).factorization i.val
  have hp (i : P) : (p i).Prime ∧ Odd (p i) := by
    have hh := Nat.mem_primeFactors.mp i.property
    exact ⟨hh.1, hoN.of_dvd_nat hh.2.1⟩
  letI (i : P) : NeZero (p i) := ⟨(hp i).1.ne_zero⟩
  have he (k : κ) (i : P) : e k i ≤ E i :=
    (Nat.factorization_le_iff_dvd (hm0 k) hN0).mpr (hmN k) i.val
  have hprod (k : κ) : m k = ∏ i : P, p i ^ e k i := by
    apply factorization_product_over_superset (m k) (hm0 k) P
    intro q hq
    have hh := Nat.mem_primeFactors.mp hq
    exact Nat.mem_primeFactors.mpr ⟨hh.1, hh.2.1.trans (hmN k), hN0⟩
  have hNprod : N = ∏ i : P, p i ^ E i :=
    factorization_product_over_superset N hN0 P (by intro q hq; exact hq)
  have hei : Function.Injective e := by
    intro k l hkl
    apply hc.1
    rw [hprod k, hprod l, hkl]
  have he0 (k : κ) : ∃ i : P, e k i ≠ 0 := by
    by_contra! h
    have hh := (hc.2.1 k).1
    rw [hprod k] at hh
    simp only [h, pow_zero, Finset.prod_const_one] at hh
    omega
  have hcov : ∀ x : ℤ, ∃ k, ((∏ i : P, p i ^ e k i : ℕ) : ℤ) ∣ x - a k := by
    simpa only [← hprod] using hc.2.2
  have hmin' : ∀ M, M < ∏ i : P, p i ^ E i → ¬ HasOddArithmeticCover M (Fintype.card κ) := by
    simpa only [← hNprod] using hmin
  let i₀ : P := ⟨p₀, Nat.mem_primeFactors.mpr ⟨hp₀, hpN, hN0⟩⟩
  have hEpos : 0 < E i₀ := hp₀.factorization_pos_of_dvd hN0 hpN
  exact minimal_period_prime_exponent_card_bound p E hp Subtype.val_injective e he hei he0 a hcov
    (Fintype.card κ) le_rfl hmin' i₀ hEpos

#print axioms restrict_arbitrary_digit_cover
#print axioms safe_arbitrary_digit_restriction
#print axioms minimal_period_every_digit_collision
#print axioms minimal_period_adjacent_layer_multiplicity
#print axioms minimal_period_zero_layer_multiplicity
#print axioms minimal_period_prime_exponent_card_bound
#print axioms exists_cardinality_period_minimal_odd_cover
#print axioms arithmetic_minimal_period_prime_exponent_bound
end Erdos7AllDigits


/- Finite-exponent refinements of the pure-prime-power sieve. -/
namespace Erdos7FiniteSieve
open Erdos7Reduction

/-- The mixed-support capacity of a vector of nonnegative coordinate budgets. -/
def mixedCapacity {ι : Type*} [Fintype ι] [DecidableEq ι] (z : ι → ℚ) : ℚ :=
  ∑ S ∈ (Finset.univ : Finset ι).powerset with 2 ≤ S.card, ∏ i ∈ S, z i

theorem mixedCapacity_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z w : ι → ℚ) (hz : ∀ i, 0 ≤ z i) (hzw : ∀ i, z i ≤ w i) :
    mixedCapacity z ≤ mixedCapacity w := by
  apply Finset.sum_le_sum
  intro S _
  exact Finset.prod_le_prod (fun i _ => hz i) (fun i _ => hzw i)

private theorem ratio_after_deletion (N u b : ℕ) (s w : ℚ)
    (hN : 0 < N) (hs : s < 1) (hw : 0 ≤ w)
    (hu : (N : ℚ) * (1 - s) ≤ u) (hb : (b : ℚ) ≤ N * w) :
    0 < u ∧ (b : ℚ) / u ≤ w / (1 - s) := by
  have hden : 0 < 1 - s := by linarith
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  have hu' : (0 : ℚ) < u := (mul_pos hN' hden).trans_le hu
  refine ⟨by exact_mod_cast hu', (div_le_div_iff₀ hu' hden).mpr ?_⟩
  have h₁ := mul_le_mul_of_nonneg_right hb hden.le
  have h₂ := mul_le_mul_of_nonneg_right hu hw
  nlinarith

/-- Pure-support deletion bounds the weight of the mixed classes actually present. -/
theorem weighted_pure_box_sieve_actual {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (e : κ → ι → ℕ) (he : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (T : ι → Finset ℕ) (heT : ∀ k i, e k i ∈ T i)
    (w : ι → ℕ → ℚ) (hw : ∀ i n, 0 ≤ w i n)
    (s : ι → ℚ) (hs : ∀ i, s i < 1)
    (hws : ∀ i, ∑ n ∈ (T i).erase 0, w i n ≤ s i)
    (B : κ → ∀ i, Finset (A i))
    (hB0 : ∀ k i, e k i = 0 → B k i = Finset.univ)
    (hBcard : ∀ k i, ((B k i).card : ℚ) ≤ (Fintype.card (A i) : ℚ) * w i (e k i))
    (hcover : ∀ x : ∀ i, A i, ∃ k, ∀ i, x i ∈ B k i) :
    (1 : ℚ) ≤ ∑ k ∈ Finset.univ.filter
      (fun k => 2 ≤ (Finset.univ.filter (fun i => e k i ≠ 0)).card),
      ∏ i, (if e k i = 0 then 1 else w i (e k i) / (1 - s i)) := by
  classical
  let supp (k : κ) := Finset.univ.filter (fun i => e k i ≠ 0)
  have hmem (k : κ) (i : ι) : i ∈ supp k ↔ e k i ≠ 0 := by simp [supp]
  let Pure (i : ι) := Finset.univ.filter (fun k => supp k = {i})
  have hpure (i : ι) (k : κ) (hk : k ∈ Pure i) : supp k = {i} :=
    (Finset.mem_filter.mp hk).2
  have hppos (i : ι) (k : κ) (hk : k ∈ Pure i) : 0 < e k i := by
    have hh : i ∈ supp k := by rw [hpure i k hk]; simp
    have := (hmem k i).mp hh
    omega
  have hpinj (i : ι) : Set.InjOn (fun k => e k i) (Pure i) := by
    intro k hk l hl hkl
    apply he
    funext j
    by_cases hji : j = i
    · simpa [hji] using hkl
    · have hk0 : e k j = 0 := by
        by_contra hh
        have hmem' := (hmem k j).mpr hh
        rw [hpure i k hk] at hmem'
        exact hji (Finset.mem_singleton.mp hmem')
      have hl0 : e l j = 0 := by
        by_contra hh
        have hmem' := (hmem l j).mpr hh
        rw [hpure i l hl] at hmem'
        exact hji (Finset.mem_singleton.mp hmem')
      rw [hk0, hl0]
  have hpsum (i : ι) : (∑ k ∈ Pure i, w i (e k i)) ≤ s i := by
    have heq : (∑ n ∈ (Pure i).image (fun k => e k i), w i n) =
        ∑ k ∈ Pure i, w i (e k i) := Finset.sum_image (hpinj i)
    rw [← heq]
    apply le_trans _ (hws i)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_erase.mpr ⟨by have := hppos i k hk; omega, heT k i⟩
    · intro n _ _
      exact hw i n
  let U (i : ι) := Finset.univ \ (Pure i).biUnion (fun k => B k i)
  have hUlower (i : ι) : (Fintype.card (A i) : ℚ) * (1 - s i) ≤ (U i).card :=
    relative_complement_bound (Pure i) (fun k => B k i) (fun k => w i (e k i)) _
      (fun k _ => hBcard k i) (hpsum i)
  have hU (i : ι) : (U i).Nonempty := by
    apply Finset.card_pos.mp
    exact (ratio_after_deletion (Fintype.card (A i)) (U i).card 0 (s i) 0
      Fintype.card_pos (hs i) (by norm_num) (hUlower i) (by simp)).1
  let K := Finset.univ.filter (fun k => 2 ≤ (supp k).card)
  have hUcover : ∀ x ∈ Fintype.piFinset U, ∃ k ∈ K, ∀ i, x i ∈ B k i := by
    intro x hx
    obtain ⟨k, hk⟩ := hcover x
    have hkm : 2 ≤ (supp k).card := by
      by_contra hlt
      obtain ⟨i, hi⟩ := he0 k
      have hpos : 0 < (supp k).card := Finset.card_pos.mpr ⟨i, (hmem k i).mpr hi⟩
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (by omega : (supp k).card = 1)
      have hxj := Fintype.mem_piFinset.mp hx j
      have hnot := (Finset.mem_sdiff.mp hxj).2
      apply hnot
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, hk j⟩
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkm⟩, hk⟩
  let v (i : ι) (n : ℕ) : ℚ := if n = 0 then 1 else w i n / (1 - s i)
  have hv (i : ι) (n : ℕ) : 0 ≤ v i n := by
    dsimp [v]
    split_ifs
    · norm_num
    · exact div_nonneg (hw i n) (by have := hs i; linarith)
  have hv0 (i : ι) : v i 0 = 1 := by simp [v]
  have hratio (k : κ) (i : ι) : (((U i ∩ B k i).card : ℚ) / (U i).card) ≤ v i (e k i) := by
    by_cases hzero : e k i = 0
    · rw [hB0 k i hzero, Finset.inter_univ, hzero, hv0]
      have hn : ((U i).card : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (hU i).card_pos)
      rw [div_self hn]
    · have hb : ((U i ∩ B k i).card : ℚ) ≤ (Fintype.card (A i) : ℚ) * w i (e k i) := by
        have hh : ((U i ∩ B k i).card : ℚ) ≤ (B k i).card := by
          exact_mod_cast Finset.card_le_card Finset.inter_subset_right
        exact hh.trans (hBcard k i)
      simpa only [v, if_neg hzero] using
        (ratio_after_deletion (Fintype.card (A i)) (U i).card (U i ∩ B k i).card
          (s i) (w i (e k i)) Fintype.card_pos (hs i) (hw i _) (hUlower i) hb).2
  have hbound := finite_product_cover_density A U hU K B hUcover
  have hprod : (∑ k ∈ K, ∏ i, (((U i ∩ B k i).card : ℚ) / (U i).card)) ≤
      ∑ k ∈ K, ∏ i, v i (e k i) := by
    apply Finset.sum_le_sum
    intro k _
    exact Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hratio k i)
  exact hbound.trans hprod

/-- Pure-support deletion with arbitrary finite coordinate weight budgets. -/
theorem weighted_pure_box_sieve {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (e : κ → ι → ℕ) (he : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (T : ι → Finset ℕ) (heT : ∀ k i, e k i ∈ T i)
    (w : ι → ℕ → ℚ) (hw : ∀ i n, 0 ≤ w i n)
    (s : ι → ℚ) (hs : ∀ i, s i < 1)
    (hws : ∀ i, ∑ n ∈ (T i).erase 0, w i n ≤ s i)
    (B : κ → ∀ i, Finset (A i))
    (hB0 : ∀ k i, e k i = 0 → B k i = Finset.univ)
    (hBcard : ∀ k i, ((B k i).card : ℚ) ≤ (Fintype.card (A i) : ℚ) * w i (e k i))
    (hcover : ∀ x : ∀ i, A i, ∃ k, ∀ i, x i ∈ B k i) :
    (1 : ℚ) ≤ mixedCapacity (fun i => s i / (1 - s i)) := by
  classical
  have hactual := weighted_pure_box_sieve_actual A e he he0 T heT w hw s hs hws B hB0 hBcard hcover
  let K := Finset.univ.filter (fun k => 2 ≤ (Finset.univ.filter (fun i => e k i ≠ 0)).card)
  let v (i : ι) (n : ℕ) : ℚ := if n = 0 then 1 else w i n / (1 - s i)
  have hv (i : ι) (n : ℕ) : 0 ≤ v i n := by
    dsimp [v]
    split_ifs
    · norm_num
    · exact div_nonneg (hw i n) (by have := hs i; linarith)
  have hv0 (i : ι) : v i 0 = 1 := by simp [v]
  have hvs (i : ι) : ∑ n ∈ (T i).erase 0, v i n ≤ s i / (1 - s i) := by
    have hden : 0 < 1 - s i := by have := hs i; linarith
    have heq : (∑ n ∈ (T i).erase 0, v i n) =
        (∑ n ∈ (T i).erase 0, w i n) / (1 - s i) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [v, if_neg (Finset.mem_erase.mp hn).1]
    rw [heq]
    exact div_le_div_of_nonneg_right (hws i) hden.le
  have hmixed := mixed_vector_weight_bound K e he.injOn T (fun k _ i => heT k i)
    (fun k hk => (Finset.mem_filter.mp hk).2) v hv hv0 (fun i => s i / (1 - s i)) hvs
  exact hactual.trans hmixed

/-- Exact total weight of the available positive prime-power exponents. -/
def positivePowerSum (p E : ℕ) : ℚ :=
  ∑ n ∈ (Finset.range (E + 1)).erase 0, ((p : ℚ)⁻¹)^n

/-- The finite, rather than infinite, coordinate budget after pure-power deletion. -/
def finitePrimeCapacity (p E : ℕ) : ℚ :=
  positivePowerSum p E / (1 - positivePowerSum p E)

theorem positivePowerSum_nonneg (p E : ℕ) : 0 ≤ positivePowerSum p E := by
  apply Finset.sum_nonneg
  intro n _
  positivity

theorem positivePowerSum_lt_one (p E : ℕ) (hp : 2 < p) : positivePowerSum p E < 1 := by
  have hle : positivePowerSum p E ≤ 1 / ((p : ℚ) - 1) := by
    apply positive_geometric_sum_le p (by omega)
    intro n hn
    have hh := (Finset.mem_erase.mp hn).1
    omega
  have hpq : (2 : ℚ) < p := by exact_mod_cast hp
  exact hle.trans_lt ((div_lt_one (by linarith)).mpr (by linarith))

theorem positivePowerSum_mono (p E F : ℕ) (hEF : E ≤ F) :
    positivePowerSum p E ≤ positivePowerSum p F := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · apply Finset.erase_subset_erase
    exact Finset.range_mono (by omega)
  · intro n _ _
    positivity

theorem finitePrimeCapacity_nonneg (p E : ℕ) (hp : 2 < p) :
    0 ≤ finitePrimeCapacity p E :=
  div_nonneg (positivePowerSum_nonneg p E) (by have := positivePowerSum_lt_one p E hp; linarith)

theorem finitePrimeCapacity_mono (p E F : ℕ) (hp : 2 < p) (hEF : E ≤ F) :
    finitePrimeCapacity p E ≤ finitePrimeCapacity p F := by
  unfold finitePrimeCapacity
  have hE := positivePowerSum_lt_one p E hp
  have hF := positivePowerSum_lt_one p F hp
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have hh := positivePowerSum_mono p E F hEF
  nlinarith

private theorem surjective_fiber_card_rat {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] [DecidableEq H] (f : G →+ H)
    (hf : Function.Surjective f) (b : H) :
    ((Finset.univ.filter (fun x => f x = b)).card : ℚ) =
      (Fintype.card G : ℚ) / Fintype.card H := by
  classical
  have heq (y : H) : (Finset.univ.filter (fun x => f x = y)).card =
      (Finset.univ.filter (fun x => f x = b)).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf b)
  have hcard : Fintype.card G =
      Fintype.card H * (Finset.univ.filter (fun x => f x = b)).card := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset G))
      (t := (Finset.univ : Finset H)) (f := f) (fun _ _ => Finset.mem_univ _)
    simpa only [heq, Finset.card_univ, Finset.sum_const, nsmul_eq_mul] using h
  have hc : (Fintype.card H : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card H))
  apply (eq_div_iff hc).mpr
  exact_mod_cast (Nat.mul_comm _ _).trans hcard.symm

/-- Exact finite-exponent capacity obstruction for a strict arithmetic cover. -/
theorem finite_exponent_cover_bound_actual {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p E : ι → ℕ) (hp : ∀ i, 2 < p i) (hcop : Pairwise (Function.onFun Nat.Coprime p))
    (e : κ → ι → ℕ) (he : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (heE : ∀ k i, e k i ≤ E i) (a : κ → ℤ)
    (hcover : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k) :
    (1 : ℚ) ≤ ∑ k ∈ Finset.univ.filter
      (fun k => 2 ≤ (Finset.univ.filter (fun i => e k i ≠ 0)).card),
      ∏ i, (if e k i = 0 then 1 else
        ((p i : ℚ)⁻¹)^(e k i) / (1 - positivePowerSum (p i) (E i))) := by
  classical
  letI (i : ι) : NeZero (p i) := ⟨by have := hp i; omega⟩
  let A (i : ι) := ZMod (p i ^ E i)
  let f (k : κ) (i : ι) := ZMod.castHom (pow_dvd_pow (p i) (heE k i)) (ZMod (p i ^ e k i))
  let B (k : κ) (i : ι) := Finset.univ.filter (fun x : A i => f k i x = (a k : ZMod (p i ^ e k i)))
  have hB0 (k : κ) (i : ι) (hzero : e k i = 0) : B k i = Finset.univ := by
    haveI : Subsingleton (ZMod (p i ^ e k i)) := by rw [hzero, pow_zero]; infer_instance
    ext x
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact Subsingleton.elim _ _
  have hBcard (k : κ) (i : ι) : ((B k i).card : ℚ) ≤
      (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(e k i) := by
    have hh := surjective_fiber_card_rat (f k i).toAddMonoidHom
      (ZMod.castHom_surjective (pow_dvd_pow (p i) (heE k i))) (a k)
    change ((B k i).card : ℚ) = _ at hh
    rw [hh]
    simp only [A, ZMod.card, Nat.cast_pow, div_eq_mul_inv, inv_pow]
    exact le_rfl
  have hbox : ∀ x : ∀ i, A i, ∃ k, ∀ i, x i ∈ B k i := by
    intro x
    let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) (fun i => p i ^ E i) Finset.univ
      (fun i _ => pow_ne_zero _ (NeZero.ne _))
      (fun i _ j _ hij => (hcop hij).pow _ _)
    have hz (i : ι) : (z.val : A i) = x i := by
      rw [← ZMod.natCast_zmod_val (x i)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
    obtain ⟨k, hk⟩ := hcover (z.val : ℤ)
    refine ⟨k, ?_⟩
    intro i
    have hpi : p i ^ e k i ∣ ∏ j, p j ^ e k j :=
      Finset.dvd_prod_of_mem (fun j => p j ^ e k j) (Finset.mem_univ i)
    have hpi' : ((p i ^ e k i : ℕ) : ℤ) ∣ ((∏ j, p j ^ e k j : ℕ) : ℤ) := by exact_mod_cast hpi
    have hqi := hpi'.trans hk
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hz i, map_natCast]
    symm
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (a k) (z.val : ℤ) (p i ^ e k i)).mpr hqi
  exact weighted_pure_box_sieve_actual A e he he0 (fun i => Finset.range (E i + 1))
    (fun k i => Finset.mem_range.mpr (by have := heE k i; omega))
    (fun i n => ((p i : ℚ)⁻¹)^n) (by intros; positivity)
    (fun i => positivePowerSum (p i) (E i))
    (fun i => positivePowerSum_lt_one (p i) (E i) (hp i)) (fun _ => le_rfl)
    B hB0 hBcard hbox

/-- Exact finite-exponent capacity obstruction for a strict arithmetic cover. -/
theorem finite_exponent_cover_bound {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p E : ι → ℕ) (hp : ∀ i, 2 < p i) (hcop : Pairwise (Function.onFun Nat.Coprime p))
    (e : κ → ι → ℕ) (he : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (heE : ∀ k i, e k i ≤ E i) (a : κ → ℤ)
    (hcover : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k) :
    (1 : ℚ) ≤ mixedCapacity (fun i => finitePrimeCapacity (p i) (E i)) := by
  classical
  letI (i : ι) : NeZero (p i) := ⟨by have := hp i; omega⟩
  let A (i : ι) := ZMod (p i ^ E i)
  let f (k : κ) (i : ι) := ZMod.castHom (pow_dvd_pow (p i) (heE k i)) (ZMod (p i ^ e k i))
  let B (k : κ) (i : ι) := Finset.univ.filter (fun x : A i => f k i x = (a k : ZMod (p i ^ e k i)))
  have hB0 (k : κ) (i : ι) (hzero : e k i = 0) : B k i = Finset.univ := by
    haveI : Subsingleton (ZMod (p i ^ e k i)) := by rw [hzero, pow_zero]; infer_instance
    ext x
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact Subsingleton.elim _ _
  have hBcard (k : κ) (i : ι) : ((B k i).card : ℚ) ≤
      (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(e k i) := by
    have hh := surjective_fiber_card_rat (f k i).toAddMonoidHom
      (ZMod.castHom_surjective (pow_dvd_pow (p i) (heE k i))) (a k)
    change ((B k i).card : ℚ) = _ at hh
    rw [hh]
    simp only [A, ZMod.card, Nat.cast_pow, div_eq_mul_inv, inv_pow]
    exact le_rfl
  have hbox : ∀ x : ∀ i, A i, ∃ k, ∀ i, x i ∈ B k i := by
    intro x
    let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) (fun i => p i ^ E i) Finset.univ
      (fun i _ => pow_ne_zero _ (NeZero.ne _))
      (fun i _ j _ hij => (hcop hij).pow _ _)
    have hz (i : ι) : (z.val : A i) = x i := by
      rw [← ZMod.natCast_zmod_val (x i)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
    obtain ⟨k, hk⟩ := hcover (z.val : ℤ)
    refine ⟨k, ?_⟩
    intro i
    have hpi : p i ^ e k i ∣ ∏ j, p j ^ e k j :=
      Finset.dvd_prod_of_mem (fun j => p j ^ e k j) (Finset.mem_univ i)
    have hpi' : ((p i ^ e k i : ℕ) : ℤ) ∣ ((∏ j, p j ^ e k j : ℕ) : ℤ) := by exact_mod_cast hpi
    have hqi := hpi'.trans hk
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hz i, map_natCast]
    symm
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (a k) (z.val : ℤ) (p i ^ e k i)).mpr hqi
  exact weighted_pure_box_sieve A e he he0 (fun i => Finset.range (E i + 1))
    (fun k i => Finset.mem_range.mpr (by have := heE k i; omega))
    (fun i n => ((p i : ℚ)⁻¹)^n) (by intros; positivity)
    (fun i => positivePowerSum (p i) (E i))
    (fun i => positivePowerSum_lt_one (p i) (E i) (hp i)) (fun _ => le_rfl)
    B hB0 hBcard hbox

theorem positivePowerSum_eq_sum (p E : ℕ) :
    positivePowerSum p E = ∑ j ∈ Finset.range E, ((p : ℚ)⁻¹)^(j + 1) := by
  have hh := Finset.sum_erase_add (Finset.range (E + 1))
    (fun j => ((p : ℚ)⁻¹)^j) (Finset.mem_range.mpr (by omega : 0 < E + 1))
  rw [Finset.sum_range_succ'] at hh
  change positivePowerSum p E + _ = _ at hh
  linarith

/-- Separating empty, singleton, and mixed supports in the product expansion. -/
theorem mixedCapacity_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (z : ι → ℚ) :
    mixedCapacity z = (∏ i, (1 + z i)) - 1 - ∑ i, z i := by
  classical
  let U := (Finset.univ : Finset ι).powerset
  have hlow : U.filter (fun S => ¬ 2 ≤ S.card) =
      insert ∅ (Finset.univ.image (fun i : ι => ({i} : Finset ι))) := by
    ext S
    constructor
    · intro hS
      have hc : S.card < 2 := by have := (Finset.mem_filter.mp hS).2; omega
      by_cases h0 : S = ∅
      · exact Finset.mem_insert.mpr (Or.inl h0)
      · have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0)
        obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (by omega : S.card = 1)
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi.symm⟩))
    · intro hS
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
      rcases Finset.mem_insert.mp hS with h0 | h1
      · simp [h0]
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h1
        simp
  have hsumlow : (∑ S ∈ U with ¬ 2 ≤ S.card, ∏ i ∈ S, z i) = 1 + ∑ i, z i := by
    rw [hlow, Finset.sum_insert (by simp), Finset.prod_empty,
      Finset.sum_image (Finset.singleton_injective.injOn)]
    simp only [Finset.prod_singleton]
  have hh := Finset.sum_filter_add_sum_filter_not U (fun S => 2 ≤ S.card)
    (fun S => ∏ i ∈ S, z i)
  rw [hsumlow] at hh
  have hprod : (∑ S ∈ U, ∏ i ∈ S, z i) = ∏ i, (1 + z i) :=
    (Finset.prod_one_add Finset.univ).symm
  rw [hprod] at hh
  change mixedCapacity z + _ = _ at hh
  linarith

/-- The first five odd primes. -/
def firstFiveOddPrimes : Fin 5 → ℕ := ![3, 5, 7, 11, 13]

/-- Maximal exponent profiles of weight at most 48 above these five primes. -/
def profiles50 : Fin 11 → Fin 5 → ℕ := ![
  ![8,1,1,1,1], ![6,2,1,1,1], ![4,3,1,1,1], ![2,4,1,1,1],
  ![5,1,2,1,1], ![3,2,2,1,1], ![1,3,2,1,1], ![2,1,3,1,1],
  ![3,1,1,2,1], ![1,2,1,2,1], ![2,1,1,1,2]]

set_option maxHeartbeats 1000000 in
theorem profile50_domination (E : Fin 5 → ℕ) (hE : ∀ i, 1 ≤ E i)
    (hw : (∑ i, E i * (firstFiveOddPrimes i - 1)) < 50) :
    ∃ j : Fin 11, ∀ i, E i ≤ profiles50 j i := by
  have h0 := hE 0
  have h1 := hE 1
  have h2 := hE 2
  have h3 := hE 3
  have h4 := hE 4
  norm_num [firstFiveOddPrimes, Fin.sum_univ_succ] at hw
  change E 0 * 2 + (E 1 * 4 + (E 2 * 6 + (E 3 * 10 + E 4 * 12))) < 50 at hw
  norm_num [profiles50, Fin.exists_fin_succ, Fin.forall_fin_succ]
  simp only [show (Fin.succ (2 : Fin 4) : Fin 5) = 3 from rfl,
    show (Fin.succ (Fin.succ (2 : Fin 3)) : Fin 5) = 4 from rfl]
  omega

set_option maxHeartbeats 2000000 in
theorem profiles50_capacity_lt_one (j : Fin 11) :
    mixedCapacity (fun i => finitePrimeCapacity (firstFiveOddPrimes i) (profiles50 j i)) < 1 := by
  fin_cases j <;> norm_num [mixedCapacity_eq, firstFiveOddPrimes, profiles50,
    finitePrimeCapacity, positivePowerSum_eq_sum, Fin.sum_univ_succ, Fin.prod_univ_succ, Finset.sum_range_succ]

/-- Every positive exponent profile of Tarsi weight below 50 has capacity
strictly below one, for the first five odd primes. -/
theorem profile_weight_below_fifty_capacity_lt_one (E : Fin 5 → ℕ)
    (hE : ∀ i, 1 ≤ E i) (hw : (∑ i, E i * (firstFiveOddPrimes i - 1)) < 50) :
    mixedCapacity (fun i => finitePrimeCapacity (firstFiveOddPrimes i) (E i)) < 1 := by
  obtain ⟨j, hj⟩ := profile50_domination E hE hw
  apply lt_of_le_of_lt _ (profiles50_capacity_lt_one j)
  apply mixedCapacity_mono
  · intro i
    apply finitePrimeCapacity_nonneg
    fin_cases i <;> norm_num [firstFiveOddPrimes]
  · intro i
    apply finitePrimeCapacity_mono _ _ _ _ (hj i)
    fin_cases i <;> norm_num [firstFiveOddPrimes]

theorem finitePrimeCapacity_antitone_base (p q E : ℕ) (hp : 2 < p) (hpq : p ≤ q) :
    finitePrimeCapacity q E ≤ finitePrimeCapacity p E := by
  have hq : 2 < q := lt_of_lt_of_le hp hpq
  have hinv : (q : ℚ)⁻¹ ≤ (p : ℚ)⁻¹ := by
    have hp0 : (0 : ℚ) < p := by exact_mod_cast (by omega : 0 < p)
    have hpq' : (p : ℚ) ≤ q := by exact_mod_cast hpq
    simpa only [one_div] using one_div_le_one_div_of_le hp0 hpq'
  have hsum : positivePowerSum q E ≤ positivePowerSum p E := by
    apply Finset.sum_le_sum
    intro n _
    exact pow_le_pow_left₀ (by positivity) hinv n
  have hp1 := positivePowerSum_lt_one p E hp
  have hq1 := positivePowerSum_lt_one q E hq
  unfold finitePrimeCapacity
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Sorted odd primes dominate the first five odd primes coordinatewise. -/
theorem sorted_first_five_lower (p : Fin 5 → ℕ) (hp : ∀ i, (p i).Prime)
    (ho : ∀ i, Odd (p i)) (hmono : StrictMono p) :
    ∀ i, firstFiveOddPrimes i ≤ p i := by
  have h0 : 3 ≤ p 0 := by have := (hp 0).two_le; have := Nat.odd_iff.mp (ho 0); omega
  have h1 : 5 ≤ p 1 := by
    have := hmono (by decide : (0 : Fin 5) < 1)
    have := Nat.odd_iff.mp (ho 1)
    omega
  have h2 : 7 ≤ p 2 := by
    have := hmono (by decide : (1 : Fin 5) < 2)
    have := Nat.odd_iff.mp (ho 2)
    omega
  have h3 : 11 ≤ p 3 := by
    have := hmono (by decide : (2 : Fin 5) < 3)
    have := Nat.odd_iff.mp (ho 3)
    have hn9 : p 3 ≠ 9 := by intro he; have hh := hp 3; norm_num [he] at hh
    omega
  have h4 : 13 ≤ p 4 := by
    have := hmono (by decide : (3 : Fin 5) < 4)
    have := Nat.odd_iff.mp (ho 4)
    omega
  intro i
  fin_cases i <;> simpa [firstFiveOddPrimes] using (by assumption)

/-- Six distinct odd primes have total Tarsi capacity at least fifty. -/
theorem six_odd_prime_sum (P : Finset ℕ) (hcard : 6 ≤ P.card)
    (hp : ∀ p ∈ P, p.Prime ∧ Odd p) : 50 ≤ ∑ p ∈ P, (p - 1) := by
  classical
  obtain ⟨S, hSP, hSc⟩ := Finset.exists_subset_card_eq hcard
  let p := S.orderEmbOfFin hSc
  have hprime (i : Fin 6) : (p i).Prime := (hp _ (hSP (S.orderEmbOfFin_mem hSc i))).1
  have hodd (i : Fin 6) : Odd (p i) := (hp _ (hSP (S.orderEmbOfFin_mem hSc i))).2
  let q (i : Fin 5) := p i.castSucc
  have hlow : ∀ i : Fin 5, firstFiveOddPrimes i ≤ q i :=
    sorted_first_five_lower q (fun i => hprime i.castSucc) (fun i => hodd i.castSucc)
      (fun _ _ hij => p.strictMono hij)
  have h4 : 13 ≤ p 4 := hlow 4
  have h5 : 17 ≤ p 5 := by
    have := p.strictMono (by decide : (4 : Fin 6) < 5)
    have := Nat.odd_iff.mp (hodd 5)
    have hn15 : p 5 ≠ 15 := by intro he; have hh := hprime 5; norm_num [he] at hh
    omega
  have hfirst : 34 ≤ ∑ i : Fin 5, (q i - 1) := by
    calc
      34 = ∑ i : Fin 5, (firstFiveOddPrimes i - 1) := by
        norm_num [firstFiveOddPrimes, Fin.sum_univ_succ]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => Nat.sub_le_sub_right (hlow i) 1)
  have hS : 50 ≤ ∑ r ∈ S, (r - 1) := by
    rw [← S.map_orderEmbOfFin_univ hSc, Finset.sum_map]
    change 50 ≤ ∑ i : Fin 6, (p i - 1)
    rw [Fin.sum_univ_castSucc]
    change 50 ≤ (∑ i : Fin 5, (q i - 1)) + (p 5 - 1)
    omega
  exact hS.trans (Finset.sum_le_sum_of_subset hSP)

/-- The finite-exponent certificate excludes every irredundant odd strict
arithmetic cover with at most fifty classes. -/
theorem no_irredundant_odd_cover_fifty {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a)
    (hpriv : ∀ k, ∃ x : ℤ, ∀ l, l ≠ k → ¬ (m l : ℤ) ∣ x - a l)
    (hcard : Fintype.card κ ≤ 50) : False := by
  classical
  have hm : ∀ k, 1 < m k := fun k => (hc.2.1 k).1
  have hm0 : ∀ k, m k ≠ 0 := fun k => by have := hm k; omega
  have ho : ∀ k, Odd (m k) := fun k => (hc.2.1 k).2
  let P := Finset.univ.biUnion (fun k => (m k).primeFactors)
  have hpP : ∀ p ∈ P, p.Prime ∧ Odd p := by
    intro p hp
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hp
    have hh := Nat.mem_primeFactors.mp hk
    exact ⟨hh.1, (ho k).of_dvd_nat hh.2.1⟩
  have hPfive : 5 ≤ P.card := arithmetic_cover_prime_count m a hm hc.1 ho hc.2.2
  have hprimeSum : (∑ p ∈ P, (p - 1)) < Fintype.card κ :=
    arithmetic_irredundant_prime_sum_bound m a hm0 hc.2.2 hpriv
  have hPcard : P.card = 5 := by
    by_contra h
    have h6 : 6 ≤ P.card := by omega
    have hh := six_odd_prime_sum P h6 hpP
    omega
  let p := P.orderEmbOfFin hPcard
  have hprime (i : Fin 5) : (p i).Prime := (hpP _ (P.orderEmbOfFin_mem hPcard i)).1
  have hodd (i : Fin 5) : Odd (p i) := (hpP _ (P.orderEmbOfFin_mem hPcard i)).2
  have hlow := sorted_first_five_lower p hprime hodd p.strictMono
  have hp2 (i : Fin 5) : 2 < p i := by
    have hh := hlow i
    have hl : 3 ≤ firstFiveOddPrimes i := by fin_cases i <;> norm_num [firstFiveOddPrimes]
    omega
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hprime i) (hprime j)).mpr (fun h => hij (p.injective h))
  let e (k : κ) (i : Fin 5) := (m k).factorization (p i)
  let E (i : Fin 5) := Finset.univ.sup (fun k => e k i)
  have heE (k : κ) (i : Fin 5) : e k i ≤ E i :=
    Finset.le_sup (f := fun k => e k i) (Finset.mem_univ k)
  have hprod (k : κ) : m k = ∏ i : Fin 5, p i ^ e k i := by
    have hsub : (m k).primeFactors ⊆ P := by
      intro r hr
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hr⟩
    have hh := Erdos7Compression.factorization_product_over_superset (m k) (hm0 k) P hsub
    rw [Finset.prod_coe_sort P (fun r => r ^ (m k).factorization r)] at hh
    nth_rw 1 [hh]
    conv_lhs => rw [← P.map_orderEmbOfFin_univ hPcard]
    exact Finset.prod_map _ _ (fun r : ℕ => r ^ (m k).factorization r)
  have hei : Function.Injective e := by
    intro k l hkl
    apply hc.1
    rw [hprod k, hprod l, hkl]
  have he0 (k : κ) : ∃ i, e k i ≠ 0 := by
    by_contra! h
    have hh := hm k
    rw [hprod k] at hh
    simp only [h, pow_zero, Finset.prod_const_one] at hh
    omega
  have hEpos (i : Fin 5) : 1 ≤ E i := by
    have hiP := P.orderEmbOfFin_mem hPcard i
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hiP
    have hfac : 0 < e k i := (hprime i).factorization_pos_of_dvd (hm0 k)
      (Nat.mem_primeFactors.mp hk).2.1
    have hh := heE k i
    omega
  have hcov : ∀ x : ℤ, ∃ k, ((∏ i : Fin 5, p i ^ e k i : ℕ) : ℤ) ∣ x - a k := by
    simpa only [← hprod] using hc.2.2
  have hprivate : ∀ k, ∃ x : ℤ, ∀ l, l ≠ k →
      ¬ ((∏ i : Fin 5, p i ^ e l i : ℕ) : ℤ) ∣ x - a l := by
    simpa only [← hprod] using hpriv
  have hweight := Erdos7Digits.coprime_power_irredundant_digit_bound p
    (fun i => (hprime i).pos) hcop e a hcov hprivate
  change (∑ i, E i * (p i - 1)) < Fintype.card κ at hweight
  have hfixedWeight : (∑ i, E i * (firstFiveOddPrimes i - 1)) < 50 := by
    have hle : (∑ i, E i * (firstFiveOddPrimes i - 1)) ≤ ∑ i, E i * (p i - 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.mul_le_mul_left (E i) (Nat.sub_le_sub_right (hlow i) 1)
    exact hle.trans_lt (hweight.trans_le hcard)
  have hbound := finite_exponent_cover_bound p E hp2 hcop e hei he0 heE a hcov
  have hfixed := profile_weight_below_fifty_capacity_lt_one E hEpos hfixedWeight
  have hleCap : mixedCapacity (fun i => finitePrimeCapacity (p i) (E i)) ≤
      mixedCapacity (fun i => finitePrimeCapacity (firstFiveOddPrimes i) (E i)) := by
    apply mixedCapacity_mono
    · intro i
      exact finitePrimeCapacity_nonneg (p i) (E i) (hp2 i)
    · intro i
      apply finitePrimeCapacity_antitone_base _ _ _ _ (hlow i)
      fin_cases i <;> norm_num [firstFiveOddPrimes]
  exact (not_lt_of_ge (hbound.trans hleCap)) hfixed

/-- Every odd strict arithmetic cover needs at least fifty-one classes. -/
theorem arithmetic_cover_at_least_fiftyone {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a) :
    51 ≤ Fintype.card κ := by
  classical
  by_contra h
  have hcard : Fintype.card κ ≤ 50 := by omega
  obtain ⟨s, hs, hpriv⟩ := arithmetic_irredundant_subcover m a hc.2.2
  let n (i : s) := m i.val
  let b (i : s) := a i.val
  have hn : IsOddArithmeticCover n b := by
    refine ⟨fun i j hij => Subtype.ext (hc.1 hij), fun i => hc.2.1 i.val, ?_⟩
    intro x
    obtain ⟨i, hi, hxi⟩ := hs x
    exact ⟨⟨i, hi⟩, hxi⟩
  have hnpriv : ∀ i : s, ∃ x : ℤ, ∀ j : s, j ≠ i → ¬ (n j : ℤ) ∣ x - b j := by
    intro i
    obtain ⟨x, hx⟩ := hpriv i.val i.property
    exact ⟨x, fun j hji => hx j.val j.property (fun he => hji (Subtype.ext he))⟩
  have hncard : Fintype.card s ≤ 50 := by
    have hh : Fintype.card s ≤ Fintype.card κ := by
      simpa only [Fintype.card_coe] using Finset.card_le_univ s
    exact hh.trans hcard
  exact no_irredundant_odd_cover_fifty n b hn hnpriv hncard

/-- Every odd strict covering system needs at least fifty-one moduli. -/
theorem at_least_fiftyone_moduli (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i, ¬ C.moduli i ≤ Ideal.span {2}) :
    letI := C.fintypeIndex
    51 ≤ Fintype.card C.ι := by
  letI := C.fintypeIndex
  exact arithmetic_cover_at_least_fiftyone (fun i => (C.moduli i).absNorm) C.residue
    ⟨moduli_absNorm_injective C, fun i => ⟨moduli_absNorm_gt_one C i,
      (ideal_not_le_two_iff _).mp (hodd i)⟩, arithmetic_cover C⟩

#print axioms weighted_pure_box_sieve
#print axioms finite_exponent_cover_bound
#print axioms profile_weight_below_fifty_capacity_lt_one
#print axioms no_irredundant_odd_cover_fifty
#print axioms at_least_fiftyone_moduli
end Erdos7FiniteSieve



set_option maxHeartbeats 2000000

namespace Erdos7CardinalitySieve
open Erdos7FiniteSieve

/-- A dual threshold bounds the sum of any fixed number of selected weights. -/
theorem sum_le_threshold {α : Type*} [DecidableEq α] (S T : Finset α)
    (hST : S ⊆ T) (w : α → ℚ) (t : ℚ) :
    ∑ x ∈ S, w x ≤ (S.card : ℚ) * t + ∑ x ∈ T, max (w x - t) 0 := by
  have hpoint (x : α) : w x ≤ t + max (w x - t) 0 := by
    have := le_max_left (w x - t) 0
    linarith
  calc
    ∑ x ∈ S, w x ≤ ∑ x ∈ S, (t + max (w x - t) 0) :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    _ = (S.card : ℚ) * t + ∑ x ∈ S, max (w x - t) 0 := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := add_le_add le_rfl (Finset.sum_le_sum_of_subset_of_nonneg hST
      (fun x _ _ => le_max_right _ _))

/-- Injective selection gives a cardinality-constrained weight bound. -/
theorem sum_injective_le_threshold {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (f : α → β) (hf : Set.InjOn f S)
    (hST : ∀ x ∈ S, f x ∈ T) (w : β → ℚ) (t : ℚ) :
    ∑ x ∈ S, w (f x) ≤ (S.card : ℚ) * t + ∑ y ∈ T, max (w y - t) 0 := by
  have hsub : S.image f ⊆ T := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hST x hx
  have h := sum_le_threshold (S.image f) T hsub w t
  rwa [Finset.sum_image hf, Finset.card_image_of_injOn hf] at h

/-- The support of an exponent vector. -/
def exponentSupport {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℕ) : Finset ι :=
  Finset.univ.filter (fun i => v i ≠ 0)

/-- All available mixed-support exponent vectors. -/
def mixedExponentVectors {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → Finset ℕ) : Finset (ι → ℕ) :=
  (Fintype.piFinset T).filter (fun v => 2 ≤ (exponentSupport v).card)

/-- Weight of an exponent vector after deleting all possible pure powers. -/
def normalizedWeight {ι : Type*} [Fintype ι] (w : ι → ℕ → ℚ) (s : ι → ℚ)
    (v : ι → ℕ) : ℚ :=
  ∏ i, if v i = 0 then 1 else w i (v i) / (1 - s i)

/-- Pure deletion together with the class-count dual threshold bound. -/
theorem weighted_pure_box_sieve_threshold {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (e : κ → ι → ℕ) (he : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (T : ι → Finset ℕ) (heT : ∀ k i, e k i ∈ T i)
    (w : ι → ℕ → ℚ) (hw : ∀ i n, 0 ≤ w i n)
    (s : ι → ℚ) (hs : ∀ i, s i < 1)
    (hws : ∀ i, ∑ n ∈ (T i).erase 0, w i n ≤ s i)
    (B : κ → ∀ i, Finset (A i))
    (hB0 : ∀ k i, e k i = 0 → B k i = Finset.univ)
    (hBcard : ∀ k i, ((B k i).card : ℚ) ≤ (Fintype.card (A i) : ℚ) * w i (e k i))
    (hcover : ∀ x : ∀ i, A i, ∃ k, ∀ i, x i ∈ B k i)
    (K : ℕ) (hK : (Finset.univ.filter (fun k => 2 ≤ (exponentSupport (e k)).card)).card ≤ K)
    (t : ℚ) (ht : 0 ≤ t) :
    (1 : ℚ) ≤ K * t + ∑ v ∈ mixedExponentVectors T, max (normalizedWeight w s v - t) 0 := by
  classical
  have hb := weighted_pure_box_sieve_actual A e he he0 T heT w hw s hs hws B hB0 hBcard hcover
  let S := Finset.univ.filter (fun k => 2 ≤ (exponentSupport (e k)).card)
  have hST (k : κ) (hk : k ∈ S) : e k ∈ mixedExponentVectors T :=
    Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (heT k), (Finset.mem_filter.mp hk).2⟩
  have h := sum_injective_le_threshold S (mixedExponentVectors T) e he.injOn hST
    (normalizedWeight w s) t
  have hcard : (S.card : ℚ) ≤ K := by exact_mod_cast hK
  exact hb.trans (h.trans (add_le_add (mul_le_mul_of_nonneg_right hcard ht) le_rfl))

/-- A pure vector has singleton support. -/
theorem exponentSupport_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (n : ℕ) (hn : n ≠ 0) :
    exponentSupport (Function.update (fun _ : ι => 0) i n) = {i} := by
  ext j
  by_cases hji : j = i <;> simp [exponentSupport, hji, hn]

/-- If every pure exponent occurs, its class is unavailable for the mixed sum. -/
theorem mixed_card_add_pure_le {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : κ → ι → ℕ) (E : ι → ℕ)
    (hpure : ∀ i n, n < E i →
      ∃ k, e k = Function.update (fun _ : ι => 0) i (n + 1)) :
    (Finset.univ.filter (fun k => 2 ≤ (exponentSupport (e k)).card)).card +
      ∑ i, E i ≤ Fintype.card κ := by
  classical
  let D := Σ i, Fin (E i)
  have hex (z : D) : ∃ k, e k = Function.update (fun _ : ι => 0) z.1 (z.2.val + 1) :=
    hpure z.1 z.2.val z.2.isLt
  let f (z : D) : κ := (hex z).choose
  have hf (z : D) : e (f z) = Function.update (fun _ : ι => 0) z.1 (z.2.val + 1) :=
    (hex z).choose_spec
  have hfi : Function.Injective f := by
    intro x y hxy
    have h := congrArg e hxy
    rw [hf x, hf y] at h
    have hfst : x.1 = y.1 := by
      by_contra hn
      have hh := congrFun h x.1
      simp [hn] at hh
    cases x with
    | mk i n =>
      cases y with
      | mk j m =>
        dsimp at hfst
        subst j
        have hh := congrFun h i
        simp only [Function.update_self] at hh
        have heq : n = m := Fin.ext (by omega)
        subst m
        rfl
  let R := Finset.univ.filter (fun k => ¬ 2 ≤ (exponentSupport (e k)).card)
  have hfR (z : D) : f z ∈ R := by
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, hf z,
      exponentSupport_update _ _ (Nat.succ_ne_zero _), Finset.card_singleton]
    omega
  let g (z : D) : R := ⟨f z, hfR z⟩
  have hgi : Function.Injective g := by
    intro x y hxy
    exact hfi (congrArg Subtype.val hxy)
  have hcard := Fintype.card_le_of_injective g hgi
  have hD : Fintype.card D = ∑ i, E i := by simp [D, Fintype.card_sigma]
  rw [hD, Fintype.card_coe] at hcard
  have hh := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset κ))
    (fun k => 2 ≤ (exponentSupport (e k)).card)
  rw [Finset.card_univ] at hh
  change _ + R.card = _ at hh
  omega

/-- Divisor closure supplies all pure vectors up to the coordinate maxima. -/
theorem divisor_closed_has_pure_vectors {ι κ : Type*}
    [Fintype κ] [DecidableEq ι]
    (m : κ → ℕ) (hm0 : ∀ k, m k ≠ 0)
    (hclosed : ∀ k d, 1 < d → d ∣ m k → ∃ l, m l = d)
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hpi : Function.Injective p)
    (i : ι) (n : ℕ) (hn : n < Finset.univ.sup (fun k => (m k).factorization (p i))) :
    ∃ k, (fun j => (m k).factorization (p j)) =
      Function.update (fun _ : ι => 0) i (n + 1) := by
  classical
  have hle : n + 1 ≤ Finset.univ.sup (fun k => (m k).factorization (p i)) := by omega
  obtain ⟨k, _, hk⟩ := (Finset.le_sup_iff (by omega : 0 < n + 1)).mp hle
  have hd : p i ^ (n + 1) ∣ m k := (hp i).pow_dvd_iff_le_factorization (hm0 k) |>.mpr hk
  obtain ⟨l, hl⟩ := hclosed k (p i ^ (n + 1))
    (Nat.one_lt_pow (by omega) (hp i).one_lt) hd
  refine ⟨l, ?_⟩
  funext j
  rw [hl, (hp i).factorization_pow]
  by_cases hji : j = i
  · subst j
    simp only [Finsupp.single_eq_same, Function.update_self]
  · have hne : p i ≠ p j := fun h => hji (hpi h).symm
    simp [Finsupp.single_apply, hne, hji]

/-- The pure-class deduction applies directly to divisor-closed arithmetic systems. -/
theorem divisor_closed_mixed_card_bound {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (m : κ → ℕ) (hm0 : ∀ k, m k ≠ 0)
    (hclosed : ∀ k d, 1 < d → d ∣ m k → ∃ l, m l = d)
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hpi : Function.Injective p)
    (K : ℕ) (hK : Fintype.card κ ≤ K) :
    (Finset.univ.filter (fun k =>
      2 ≤ (exponentSupport (fun i => (m k).factorization (p i))).card)).card ≤
      K - ∑ i, Finset.univ.sup (fun k => (m k).factorization (p i)) := by
  have hh := mixed_card_add_pure_le (fun k i => (m k).factorization (p i))
    (fun i => Finset.univ.sup (fun k => (m k).factorization (p i)))
    (divisor_closed_has_pure_vectors m hm0 hclosed p hp hpi)
  dsimp only at hh
  omega

/-- Cardinality-constrained finite-exponent sieve for arithmetic classes. -/
theorem finite_exponent_cover_threshold {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (p E : ι → ℕ) (hp : ∀ i, 2 < p i) (hcop : Pairwise (Function.onFun Nat.Coprime p))
    (e : κ → ι → ℕ) (he : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (heE : ∀ k i, e k i ≤ E i) (a : κ → ℤ)
    (hcover : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k)
    (K : ℕ) (hK : (Finset.univ.filter (fun k => 2 ≤ (exponentSupport (e k)).card)).card ≤ K)
    (t : ℚ) (ht : 0 ≤ t) :
    (1 : ℚ) ≤ K * t + ∑ v ∈ mixedExponentVectors (fun i => Finset.range (E i + 1)),
      max (normalizedWeight (fun i n => ((p i : ℚ)⁻¹)^n)
        (fun i => positivePowerSum (p i) (E i)) v - t) 0 := by
  classical
  have hb := finite_exponent_cover_bound_actual p E hp hcop e he he0 heE a hcover
  let S := Finset.univ.filter (fun k => 2 ≤ (exponentSupport (e k)).card)
  have hST (k : κ) (hk : k ∈ S) :
      e k ∈ mixedExponentVectors (fun i => Finset.range (E i + 1)) := by
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, (Finset.mem_filter.mp hk).2⟩
    intro i
    exact Finset.mem_range.mpr (by have := heE k i; omega)
  have h := sum_injective_le_threshold S
    (mixedExponentVectors (fun i => Finset.range (E i + 1))) e he.injOn hST
    (normalizedWeight (fun i n => ((p i : ℚ)⁻¹)^n)
      (fun i => positivePowerSum (p i) (E i))) t
  have hcard : (S.card : ℚ) ≤ K := by exact_mod_cast hK
  exact hb.trans (h.trans (add_le_add (mul_le_mul_of_nonneg_right hcard ht) le_rfl))

/-- Normalized weight at finite prime-power exponent caps. -/
def primeVectorWeight {ι : Type*} [Fintype ι] (p E : ι → ℕ) (v : ι → ℕ) : ℚ :=
  normalizedWeight (fun i n => ((p i : ℚ)⁻¹)^n)
    (fun i => positivePowerSum (p i) (E i)) v

/-- Dual upper bound when at most `K` mixed vectors may be selected. -/
def thresholdCapacity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p E : ι → ℕ) (K : ℕ) (t : ℚ) : ℚ :=
  K * t + ∑ v ∈ mixedExponentVectors (fun i => Finset.range (E i + 1)),
    max (primeVectorWeight p E v - t) 0

theorem primeVectorWeight_nonneg {ι : Type*} [Fintype ι]
    (p E v : ι → ℕ) (hp : ∀ i, 2 < p i) : 0 ≤ primeVectorWeight p E v := by
  apply Finset.prod_nonneg
  intro i _
  dsimp
  split_ifs
  · norm_num
  · exact div_nonneg (by positivity) (by have := positivePowerSum_lt_one _ (E i) (hp i); linarith)

theorem primeVectorWeight_mono_exponents {ι : Type*} [Fintype ι]
    (p E F v : ι → ℕ) (hp : ∀ i, 2 < p i) (hEF : ∀ i, E i ≤ F i) :
    primeVectorWeight p E v ≤ primeVectorWeight p F v := by
  apply Finset.prod_le_prod
  · intro i _
    dsimp
    split_ifs
    · norm_num
    · exact div_nonneg (by positivity) (by have := positivePowerSum_lt_one _ (E i) (hp i); linarith)
  · intro i _
    dsimp
    split_ifs with hv
    · exact le_rfl
    · have hE := positivePowerSum_lt_one _ (E i) (hp i)
      have hF := positivePowerSum_lt_one _ (F i) (hp i)
      have hsum := positivePowerSum_mono (p i) (E i) (F i) (hEF i)
      apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem primeVectorWeight_antitone_base {ι : Type*} [Fintype ι]
    (p q E v : ι → ℕ) (hp : ∀ i, 2 < p i) (hpq : ∀ i, p i ≤ q i) :
    primeVectorWeight q E v ≤ primeVectorWeight p E v := by
  have hq (i : ι) : 2 < q i := (hp i).trans_le (hpq i)
  apply Finset.prod_le_prod
  · intro i _
    dsimp
    split_ifs
    · norm_num
    · exact div_nonneg (by positivity) (by have := positivePowerSum_lt_one _ (E i) (hq i); linarith)
  · intro i _
    dsimp
    split_ifs with hv
    · exact le_rfl
    · have hinv : (q i : ℚ)⁻¹ ≤ (p i : ℚ)⁻¹ := by
        have hp0 : (0 : ℚ) < p i := by exact_mod_cast (by have := hp i; omega : 0 < p i)
        have hle : (p i : ℚ) ≤ q i := by exact_mod_cast hpq i
        simpa only [one_div] using one_div_le_one_div_of_le hp0 hle
      have hpow (n : ℕ) : ((q i : ℚ)⁻¹)^n ≤ ((p i : ℚ)⁻¹)^n :=
        pow_le_pow_left₀ (by positivity) hinv n
      have hsum : positivePowerSum (q i) (E i) ≤ positivePowerSum (p i) (E i) :=
        Finset.sum_le_sum (fun n _ => hpow n)
      have hp1 := positivePowerSum_lt_one _ (E i) (hp i)
      have hq1 := positivePowerSum_lt_one _ (E i) (hq i)
      apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
      have h₁ := mul_le_mul_of_nonneg_right (hpow (v i)) (by linarith : 0 ≤ 1 - positivePowerSum (p i) (E i))
      have h₂ := mul_le_mul_of_nonneg_left
        (by linarith : 1 - positivePowerSum (p i) (E i) ≤ 1 - positivePowerSum (q i) (E i))
        (show 0 ≤ ((p i : ℚ)⁻¹)^(v i) by positivity)
      exact h₁.trans h₂

theorem thresholdCapacity_mono_exponents {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p E F : ι → ℕ) (K : ℕ) (t : ℚ) (hp : ∀ i, 2 < p i) (hEF : ∀ i, E i ≤ F i) :
    thresholdCapacity p E K t ≤ thresholdCapacity p F K t := by
  apply add_le_add le_rfl
  have hsub : mixedExponentVectors (fun i => Finset.range (E i + 1)) ⊆
      mixedExponentVectors (fun i => Finset.range (F i + 1)) := by
    intro v hv
    obtain ⟨hv, hm⟩ := Finset.mem_filter.mp hv
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, hm⟩
    intro i
    have hh := Finset.mem_range.mp (Fintype.mem_piFinset.mp hv i)
    exact Finset.mem_range.mpr (by have := hEF i; omega)
  calc
    _ ≤ ∑ v ∈ mixedExponentVectors (fun i => Finset.range (E i + 1)),
        max (primeVectorWeight p F v - t) 0 := by
      apply Finset.sum_le_sum
      intro v _
      exact max_le_max (sub_le_sub_right (primeVectorWeight_mono_exponents p E F v hp hEF) t) le_rfl
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => le_max_right _ _)

theorem thresholdCapacity_antitone_base {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q E : ι → ℕ) (K : ℕ) (t : ℚ) (hp : ∀ i, 2 < p i) (hpq : ∀ i, p i ≤ q i) :
    thresholdCapacity q E K t ≤ thresholdCapacity p E K t := by
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro v _
  exact max_le_max (sub_le_sub_right (primeVectorWeight_antitone_base p q E v hp hpq) t) le_rfl

#print axioms thresholdCapacity_mono_exponents
#print axioms thresholdCapacity_antitone_base
#print axioms divisor_closed_mixed_card_bound
#print axioms mixed_card_add_pure_le
#print axioms finite_exponent_cover_threshold
#print axioms sum_injective_le_threshold
#print axioms weighted_pure_box_sieve_threshold
end Erdos7CardinalitySieve


/-! Kernel-checked finite rational certificates for fifty-eight classes. -/
namespace Erdos7CardinalitySieve
open Erdos7FiniteSieve
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def firstSixOddPrimes : Fin 6 → ℕ := ![3, 5, 7, 11, 13, 17]

/-- Either the full budget or the budget for 52 selected mixed vectors is too small. -/
def ProfileCondition {ι : Type*} [Fintype ι] [DecidableEq ι] (p E : ι → ℕ) : Prop :=
  mixedCapacity (fun i => finitePrimeCapacity (p i) (E i)) < 1 ∨
    ∃ t : ℚ, 0 ≤ t ∧ thresholdCapacity p E 52 t < 1

theorem ProfileCondition.mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p E F : ι → ℕ) (hp : ∀ i, 2 < p i) (hEF : ∀ i, E i ≤ F i)
    (hF : ProfileCondition p F) : ProfileCondition p E := by
  rcases hF with h | ⟨t, ht, h⟩
  · left
    apply lt_of_le_of_lt _ h
    apply mixedCapacity_mono
    · intro i
      exact finitePrimeCapacity_nonneg _ _ (hp i)
    · intro i
      exact finitePrimeCapacity_mono _ _ _ (hp i) (hEF i)
  · exact Or.inr ⟨t, ht, (thresholdCapacity_mono_exponents p E F 52 t hp hEF).trans_lt h⟩

def profiles58Five : Fin 30 → Fin 5 → ℕ := ![
  ![1, 1, 1, 2, 2],
  ![1, 1, 3, 2, 1],
  ![1, 2, 2, 1, 2],
  ![1, 2, 4, 1, 1],
  ![1, 4, 1, 2, 1],
  ![1, 5, 2, 1, 1],
  ![2, 1, 1, 3, 1],
  ![2, 2, 2, 2, 1],
  ![2, 3, 1, 1, 2],
  ![2, 3, 3, 1, 1],
  ![2, 6, 1, 1, 1],
  ![3, 1, 2, 1, 2],
  ![3, 1, 4, 1, 1],
  ![3, 3, 1, 2, 1],
  ![3, 4, 2, 1, 1],
  ![4, 1, 2, 2, 1],
  ![4, 2, 1, 1, 2],
  ![4, 2, 3, 1, 1],
  ![4, 5, 1, 1, 1],
  ![5, 2, 1, 2, 1],
  ![5, 3, 2, 1, 1],
  ![6, 1, 1, 1, 2],
  ![6, 1, 3, 1, 1],
  ![6, 4, 1, 1, 1],
  ![7, 1, 1, 2, 1],
  ![7, 2, 2, 1, 1],
  ![8, 3, 1, 1, 1],
  ![9, 1, 2, 1, 1],
  ![10, 2, 1, 1, 1],
  ![12, 1, 1, 1, 1]]

theorem profile58Five_domination (E : Fin 5 → ℕ) (hE : ∀ i, 1 ≤ E i)
    (hw : (∑ i, E i * (firstFiveOddPrimes i - 1)) < 58) :
    ∃ j : Fin 30, ∀ i, E i ≤ profiles58Five j i := by
  have h0 := hE 0
  have h1 := hE 1
  have h2 := hE 2
  have h3 := hE 3
  have h4 := hE 4
  norm_num [firstFiveOddPrimes, Fin.sum_univ_succ] at hw
  change E 0 * 2 + (E 1 * 4 + (E 2 * 6 + (E 3 * 10 + (E 4 * 12)))) < 58 at hw
  by_cases he4 : E 4 = 1
  ·
    by_cases he3 : E 3 = 1
    ·
      by_cases he2 : E 2 = 1
      ·
        by_cases he1 : E 1 = 1
        ·
          refine ⟨29, ?_⟩
          intro i
          fin_cases i
          · change E 0 ≤ 12
            omega
          · change E 1 ≤ 1
            omega
          · change E 2 ≤ 1
            omega
          · change E 3 ≤ 1
            omega
          · change E 4 ≤ 1
            omega
        ·
          by_cases he1 : E 1 = 2
          ·
            refine ⟨28, ?_⟩
            intro i
            fin_cases i
            · change E 0 ≤ 10
              omega
            · change E 1 ≤ 2
              omega
            · change E 2 ≤ 1
              omega
            · change E 3 ≤ 1
              omega
            · change E 4 ≤ 1
              omega
          ·
            by_cases he1 : E 1 = 3
            ·
              refine ⟨26, ?_⟩
              intro i
              fin_cases i
              · change E 0 ≤ 8
                omega
              · change E 1 ≤ 3
                omega
              · change E 2 ≤ 1
                omega
              · change E 3 ≤ 1
                omega
              · change E 4 ≤ 1
                omega
            ·
              by_cases he1 : E 1 = 4
              ·
                refine ⟨23, ?_⟩
                intro i
                fin_cases i
                · change E 0 ≤ 6
                  omega
                · change E 1 ≤ 4
                  omega
                · change E 2 ≤ 1
                  omega
                · change E 3 ≤ 1
                  omega
                · change E 4 ≤ 1
                  omega
              ·
                by_cases he1 : E 1 = 5
                ·
                  refine ⟨18, ?_⟩
                  intro i
                  fin_cases i
                  · change E 0 ≤ 4
                    omega
                  · change E 1 ≤ 5
                    omega
                  · change E 2 ≤ 1
                    omega
                  · change E 3 ≤ 1
                    omega
                  · change E 4 ≤ 1
                    omega
                ·
                  have he1 : E 1 = 6 := by omega
                  refine ⟨10, ?_⟩
                  intro i
                  fin_cases i
                  · change E 0 ≤ 2
                    omega
                  · change E 1 ≤ 6
                    omega
                  · change E 2 ≤ 1
                    omega
                  · change E 3 ≤ 1
                    omega
                  · change E 4 ≤ 1
                    omega
      ·
        by_cases he2 : E 2 = 2
        ·
          by_cases he1 : E 1 = 1
          ·
            refine ⟨27, ?_⟩
            intro i
            fin_cases i
            · change E 0 ≤ 9
              omega
            · change E 1 ≤ 1
              omega
            · change E 2 ≤ 2
              omega
            · change E 3 ≤ 1
              omega
            · change E 4 ≤ 1
              omega
          ·
            by_cases he1 : E 1 = 2
            ·
              refine ⟨25, ?_⟩
              intro i
              fin_cases i
              · change E 0 ≤ 7
                omega
              · change E 1 ≤ 2
                omega
              · change E 2 ≤ 2
                omega
              · change E 3 ≤ 1
                omega
              · change E 4 ≤ 1
                omega
            ·
              by_cases he1 : E 1 = 3
              ·
                refine ⟨20, ?_⟩
                intro i
                fin_cases i
                · change E 0 ≤ 5
                  omega
                · change E 1 ≤ 3
                  omega
                · change E 2 ≤ 2
                  omega
                · change E 3 ≤ 1
                  omega
                · change E 4 ≤ 1
                  omega
              ·
                by_cases he1 : E 1 = 4
                ·
                  refine ⟨14, ?_⟩
                  intro i
                  fin_cases i
                  · change E 0 ≤ 3
                    omega
                  · change E 1 ≤ 4
                    omega
                  · change E 2 ≤ 2
                    omega
                  · change E 3 ≤ 1
                    omega
                  · change E 4 ≤ 1
                    omega
                ·
                  have he1 : E 1 = 5 := by omega
                  refine ⟨5, ?_⟩
                  intro i
                  fin_cases i
                  · change E 0 ≤ 1
                    omega
                  · change E 1 ≤ 5
                    omega
                  · change E 2 ≤ 2
                    omega
                  · change E 3 ≤ 1
                    omega
                  · change E 4 ≤ 1
                    omega
        ·
          by_cases he2 : E 2 = 3
          ·
            by_cases he1 : E 1 = 1
            ·
              refine ⟨22, ?_⟩
              intro i
              fin_cases i
              · change E 0 ≤ 6
                omega
              · change E 1 ≤ 1
                omega
              · change E 2 ≤ 3
                omega
              · change E 3 ≤ 1
                omega
              · change E 4 ≤ 1
                omega
            ·
              by_cases he1 : E 1 = 2
              ·
                refine ⟨17, ?_⟩
                intro i
                fin_cases i
                · change E 0 ≤ 4
                  omega
                · change E 1 ≤ 2
                  omega
                · change E 2 ≤ 3
                  omega
                · change E 3 ≤ 1
                  omega
                · change E 4 ≤ 1
                  omega
              ·
                have he1 : E 1 = 3 := by omega
                refine ⟨9, ?_⟩
                intro i
                fin_cases i
                · change E 0 ≤ 2
                  omega
                · change E 1 ≤ 3
                  omega
                · change E 2 ≤ 3
                  omega
                · change E 3 ≤ 1
                  omega
                · change E 4 ≤ 1
                  omega
          ·
            have he2 : E 2 = 4 := by omega
            by_cases he1 : E 1 = 1
            ·
              refine ⟨12, ?_⟩
              intro i
              fin_cases i
              · change E 0 ≤ 3
                omega
              · change E 1 ≤ 1
                omega
              · change E 2 ≤ 4
                omega
              · change E 3 ≤ 1
                omega
              · change E 4 ≤ 1
                omega
            ·
              have he1 : E 1 = 2 := by omega
              refine ⟨3, ?_⟩
              intro i
              fin_cases i
              · change E 0 ≤ 1
                omega
              · change E 1 ≤ 2
                omega
              · change E 2 ≤ 4
                omega
              · change E 3 ≤ 1
                omega
              · change E 4 ≤ 1
                omega
    ·
      by_cases he3 : E 3 = 2
      ·
        by_cases he2 : E 2 = 1
        ·
          by_cases he1 : E 1 = 1
          ·
            refine ⟨24, ?_⟩
            intro i
            fin_cases i
            · change E 0 ≤ 7
              omega
            · change E 1 ≤ 1
              omega
            · change E 2 ≤ 1
              omega
            · change E 3 ≤ 2
              omega
            · change E 4 ≤ 1
              omega
          ·
            by_cases he1 : E 1 = 2
            ·
              refine ⟨19, ?_⟩
              intro i
              fin_cases i
              · change E 0 ≤ 5
                omega
              · change E 1 ≤ 2
                omega
              · change E 2 ≤ 1
                omega
              · change E 3 ≤ 2
                omega
              · change E 4 ≤ 1
                omega
            ·
              by_cases he1 : E 1 = 3
              ·
                refine ⟨13, ?_⟩
                intro i
                fin_cases i
                · change E 0 ≤ 3
                  omega
                · change E 1 ≤ 3
                  omega
                · change E 2 ≤ 1
                  omega
                · change E 3 ≤ 2
                  omega
                · change E 4 ≤ 1
                  omega
              ·
                have he1 : E 1 = 4 := by omega
                refine ⟨4, ?_⟩
                intro i
                fin_cases i
                · change E 0 ≤ 1
                  omega
                · change E 1 ≤ 4
                  omega
                · change E 2 ≤ 1
                  omega
                · change E 3 ≤ 2
                  omega
                · change E 4 ≤ 1
                  omega
        ·
          by_cases he2 : E 2 = 2
          ·
            by_cases he1 : E 1 = 1
            ·
              refine ⟨15, ?_⟩
              intro i
              fin_cases i
              · change E 0 ≤ 4
                omega
              · change E 1 ≤ 1
                omega
              · change E 2 ≤ 2
                omega
              · change E 3 ≤ 2
                omega
              · change E 4 ≤ 1
                omega
            ·
              have he1 : E 1 = 2 := by omega
              refine ⟨7, ?_⟩
              intro i
              fin_cases i
              · change E 0 ≤ 2
                omega
              · change E 1 ≤ 2
                omega
              · change E 2 ≤ 2
                omega
              · change E 3 ≤ 2
                omega
              · change E 4 ≤ 1
                omega
          ·
            have he2 : E 2 = 3 := by omega
            have he1 : E 1 = 1 := by omega
            refine ⟨1, ?_⟩
            intro i
            fin_cases i
            · change E 0 ≤ 1
              omega
            · change E 1 ≤ 1
              omega
            · change E 2 ≤ 3
              omega
            · change E 3 ≤ 2
              omega
            · change E 4 ≤ 1
              omega
      ·
        have he3 : E 3 = 3 := by omega
        have he2 : E 2 = 1 := by omega
        have he1 : E 1 = 1 := by omega
        refine ⟨6, ?_⟩
        intro i
        fin_cases i
        · change E 0 ≤ 2
          omega
        · change E 1 ≤ 1
          omega
        · change E 2 ≤ 1
          omega
        · change E 3 ≤ 3
          omega
        · change E 4 ≤ 1
          omega
  ·
    have he4 : E 4 = 2 := by omega
    by_cases he3 : E 3 = 1
    ·
      by_cases he2 : E 2 = 1
      ·
        by_cases he1 : E 1 = 1
        ·
          refine ⟨21, ?_⟩
          intro i
          fin_cases i
          · change E 0 ≤ 6
            omega
          · change E 1 ≤ 1
            omega
          · change E 2 ≤ 1
            omega
          · change E 3 ≤ 1
            omega
          · change E 4 ≤ 2
            omega
        ·
          by_cases he1 : E 1 = 2
          ·
            refine ⟨16, ?_⟩
            intro i
            fin_cases i
            · change E 0 ≤ 4
              omega
            · change E 1 ≤ 2
              omega
            · change E 2 ≤ 1
              omega
            · change E 3 ≤ 1
              omega
            · change E 4 ≤ 2
              omega
          ·
            have he1 : E 1 = 3 := by omega
            refine ⟨8, ?_⟩
            intro i
            fin_cases i
            · change E 0 ≤ 2
              omega
            · change E 1 ≤ 3
              omega
            · change E 2 ≤ 1
              omega
            · change E 3 ≤ 1
              omega
            · change E 4 ≤ 2
              omega
      ·
        have he2 : E 2 = 2 := by omega
        by_cases he1 : E 1 = 1
        ·
          refine ⟨11, ?_⟩
          intro i
          fin_cases i
          · change E 0 ≤ 3
            omega
          · change E 1 ≤ 1
            omega
          · change E 2 ≤ 2
            omega
          · change E 3 ≤ 1
            omega
          · change E 4 ≤ 2
            omega
        ·
          have he1 : E 1 = 2 := by omega
          refine ⟨2, ?_⟩
          intro i
          fin_cases i
          · change E 0 ≤ 1
            omega
          · change E 1 ≤ 2
            omega
          · change E 2 ≤ 2
            omega
          · change E 3 ≤ 1
            omega
          · change E 4 ≤ 2
            omega
    ·
      have he3 : E 3 = 2 := by omega
      have he2 : E 2 = 1 := by omega
      have he1 : E 1 = 1 := by omega
      refine ⟨0, ?_⟩
      intro i
      fin_cases i
      · change E 0 ≤ 1
        omega
      · change E 1 ≤ 1
        omega
      · change E 2 ≤ 1
        omega
      · change E 3 ≤ 2
        omega
      · change E 4 ≤ 2
        omega

theorem certificate58Five_0 : ProfileCondition firstFiveOddPrimes (profiles58Five 0) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![1, 1, 1, 2, 2]
  left
  decide +kernel

#print axioms certificate58Five_0

theorem certificate58Five_1 : ProfileCondition firstFiveOddPrimes (profiles58Five 1) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![1, 1, 3, 2, 1]
  left
  decide +kernel

#print axioms certificate58Five_1

theorem certificate58Five_2 : ProfileCondition firstFiveOddPrimes (profiles58Five 2) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![1, 2, 2, 1, 2]
  left
  decide +kernel

#print axioms certificate58Five_2

theorem certificate58Five_3 : ProfileCondition firstFiveOddPrimes (profiles58Five 3) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![1, 2, 4, 1, 1]
  left
  decide +kernel

#print axioms certificate58Five_3

theorem certificate58Five_4 : ProfileCondition firstFiveOddPrimes (profiles58Five 4) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![1, 4, 1, 2, 1]
  left
  decide +kernel

#print axioms certificate58Five_4

theorem certificate58Five_5 : ProfileCondition firstFiveOddPrimes (profiles58Five 5) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![1, 5, 2, 1, 1]
  left
  decide +kernel

#print axioms certificate58Five_5

theorem certificate58Five_6 : ProfileCondition firstFiveOddPrimes (profiles58Five 6) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![2, 1, 1, 3, 1]
  left
  decide +kernel

#print axioms certificate58Five_6

theorem certificate58Five_7 : ProfileCondition firstFiveOddPrimes (profiles58Five 7) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![2, 2, 2, 2, 1]
  left
  decide +kernel

#print axioms certificate58Five_7

theorem certificate58Five_8 : ProfileCondition firstFiveOddPrimes (profiles58Five 8) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![2, 3, 1, 1, 2]
  left
  decide +kernel

#print axioms certificate58Five_8

theorem certificate58Five_9 : ProfileCondition firstFiveOddPrimes (profiles58Five 9) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![2, 3, 3, 1, 1]
  left
  decide +kernel

#print axioms certificate58Five_9

theorem certificate58Five_10 : ProfileCondition firstFiveOddPrimes (profiles58Five 10) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![2, 6, 1, 1, 1]
  left
  decide +kernel

#print axioms certificate58Five_10

theorem certificate58Five_11 : ProfileCondition firstFiveOddPrimes (profiles58Five 11) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![3, 1, 2, 1, 2]
  left
  decide +kernel

#print axioms certificate58Five_11

theorem certificate58Five_12 : ProfileCondition firstFiveOddPrimes (profiles58Five 12) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![3, 1, 4, 1, 1]
  left
  decide +kernel

#print axioms certificate58Five_12

theorem certificate58Five_13 : ProfileCondition firstFiveOddPrimes (profiles58Five 13) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![3, 3, 1, 2, 1]
  left
  decide +kernel

#print axioms certificate58Five_13

theorem certificate58Five_14 : ProfileCondition firstFiveOddPrimes (profiles58Five 14) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![3, 4, 2, 1, 1]
  right
  refine ⟨(1/492 : ℚ), by norm_num, ?_⟩
  decide +kernel

#print axioms certificate58Five_14

theorem certificate58Five_15 : ProfileCondition firstFiveOddPrimes (profiles58Five 15) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![4, 1, 2, 2, 1]
  left
  decide +kernel

#print axioms certificate58Five_15

theorem certificate58Five_16 : ProfileCondition firstFiveOddPrimes (profiles58Five 16) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![4, 2, 1, 1, 2]
  left
  decide +kernel

#print axioms certificate58Five_16

theorem certificate58Five_17 : ProfileCondition firstFiveOddPrimes (profiles58Five 17) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![4, 2, 3, 1, 1]
  right
  refine ⟨(27/11726 : ℚ), by norm_num, ?_⟩
  decide +kernel

#print axioms certificate58Five_17

theorem certificate58Five_18 : ProfileCondition firstFiveOddPrimes (profiles58Five 18) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![4, 5, 1, 1, 1]
  right
  refine ⟨(375/192208 : ℚ), by norm_num, ?_⟩
  decide +kernel

#print axioms certificate58Five_18

theorem certificate58Five_19 : ProfileCondition firstFiveOddPrimes (profiles58Five 19) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![5, 2, 1, 2, 1]
  right
  refine ⟨(27/13298 : ℚ), by norm_num, ?_⟩
  decide +kernel

#print axioms certificate58Five_19

theorem certificate58Five_20 : ProfileCondition firstFiveOddPrimes (profiles58Five 20) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![5, 3, 2, 1, 1]
  right
  refine ⟨(1/410 : ℚ), by norm_num, ?_⟩
  decide +kernel

#print axioms certificate58Five_20

theorem certificate58Five_21 : ProfileCondition firstFiveOddPrimes (profiles58Five 21) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![6, 1, 1, 1, 2]
  left
  decide +kernel

#print axioms certificate58Five_21

theorem certificate58Five_22 : ProfileCondition firstFiveOddPrimes (profiles58Five 22) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![6, 1, 3, 1, 1]
  left
  decide +kernel

#print axioms certificate58Five_22

theorem certificate58Five_23 : ProfileCondition firstFiveOddPrimes (profiles58Five 23) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![6, 4, 1, 1, 1]
  right
  refine ⟨(135/68474 : ℚ), by norm_num, ?_⟩
  decide +kernel

#print axioms certificate58Five_23

theorem certificate58Five_24 : ProfileCondition firstFiveOddPrimes (profiles58Five 24) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![7, 1, 1, 2, 1]
  left
  decide +kernel

#print axioms certificate58Five_24

theorem certificate58Five_25 : ProfileCondition firstFiveOddPrimes (profiles58Five 25) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![7, 2, 2, 1, 1]
  right
  refine ⟨(1/456 : ℚ), by norm_num, ?_⟩
  decide +kernel

#print axioms certificate58Five_25

theorem certificate58Five_26 : ProfileCondition firstFiveOddPrimes (profiles58Five 26) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![8, 3, 1, 1, 1]
  right
  refine ⟨(1215/616828 : ℚ), by norm_num, ?_⟩
  decide +kernel

#print axioms certificate58Five_26

theorem certificate58Five_27 : ProfileCondition firstFiveOddPrimes (profiles58Five 27) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![9, 1, 2, 1, 1]
  left
  decide +kernel

#print axioms certificate58Five_27

theorem certificate58Five_28 : ProfileCondition firstFiveOddPrimes (profiles58Five 28) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![10, 2, 1, 1, 1]
  left
  decide +kernel

#print axioms certificate58Five_28

theorem certificate58Five_29 : ProfileCondition firstFiveOddPrimes (profiles58Five 29) := by
  change ProfileCondition ![3, 5, 7, 11, 13] ![12, 1, 1, 1, 1]
  left
  decide +kernel

#print axioms certificate58Five_29

theorem profiles58Five_certificate (j : Fin 30) :
    ProfileCondition firstFiveOddPrimes (profiles58Five j) := by
  fin_cases j
  · exact certificate58Five_0
  · exact certificate58Five_1
  · exact certificate58Five_2
  · exact certificate58Five_3
  · exact certificate58Five_4
  · exact certificate58Five_5
  · exact certificate58Five_6
  · exact certificate58Five_7
  · exact certificate58Five_8
  · exact certificate58Five_9
  · exact certificate58Five_10
  · exact certificate58Five_11
  · exact certificate58Five_12
  · exact certificate58Five_13
  · exact certificate58Five_14
  · exact certificate58Five_15
  · exact certificate58Five_16
  · exact certificate58Five_17
  · exact certificate58Five_18
  · exact certificate58Five_19
  · exact certificate58Five_20
  · exact certificate58Five_21
  · exact certificate58Five_22
  · exact certificate58Five_23
  · exact certificate58Five_24
  · exact certificate58Five_25
  · exact certificate58Five_26
  · exact certificate58Five_27
  · exact certificate58Five_28
  · exact certificate58Five_29

theorem profile_weight_below_fiftyeight_five (E : Fin 5 → ℕ)
    (hE : ∀ i, 1 ≤ E i) (hw : (∑ i, E i * (firstFiveOddPrimes i - 1)) < 58) :
    ProfileCondition firstFiveOddPrimes E := by
  obtain ⟨j, hj⟩ := profile58Five_domination E hE hw
  exact ProfileCondition.mono firstFiveOddPrimes E (profiles58Five j)
    (by intro i; fin_cases i <;> norm_num [firstFiveOddPrimes]) hj (profiles58Five_certificate j)

#print axioms profile_weight_below_fiftyeight_five

def profiles58Six : Fin 3 → Fin 6 → ℕ := ![
  ![1, 1, 2, 1, 1, 1],
  ![2, 2, 1, 1, 1, 1],
  ![4, 1, 1, 1, 1, 1]]

theorem profile58Six_domination (E : Fin 6 → ℕ) (hE : ∀ i, 1 ≤ E i)
    (hw : (∑ i, E i * (firstSixOddPrimes i - 1)) < 58) :
    ∃ j : Fin 3, ∀ i, E i ≤ profiles58Six j i := by
  have h0 := hE 0
  have h1 := hE 1
  have h2 := hE 2
  have h3 := hE 3
  have h4 := hE 4
  have h5 := hE 5
  norm_num [firstSixOddPrimes, Fin.sum_univ_succ] at hw
  change E 0 * 2 + (E 1 * 4 + (E 2 * 6 + (E 3 * 10 + (E 4 * 12 + (E 5 * 16))))) < 58 at hw
  have he5 : E 5 = 1 := by omega
  have he4 : E 4 = 1 := by omega
  have he3 : E 3 = 1 := by omega
  by_cases he2 : E 2 = 1
  ·
    by_cases he1 : E 1 = 1
    ·
      refine ⟨2, ?_⟩
      intro i
      fin_cases i
      · change E 0 ≤ 4
        omega
      · change E 1 ≤ 1
        omega
      · change E 2 ≤ 1
        omega
      · change E 3 ≤ 1
        omega
      · change E 4 ≤ 1
        omega
      · change E 5 ≤ 1
        omega
    ·
      have he1 : E 1 = 2 := by omega
      refine ⟨1, ?_⟩
      intro i
      fin_cases i
      · change E 0 ≤ 2
        omega
      · change E 1 ≤ 2
        omega
      · change E 2 ≤ 1
        omega
      · change E 3 ≤ 1
        omega
      · change E 4 ≤ 1
        omega
      · change E 5 ≤ 1
        omega
  ·
    have he2 : E 2 = 2 := by omega
    have he1 : E 1 = 1 := by omega
    refine ⟨0, ?_⟩
    intro i
    fin_cases i
    · change E 0 ≤ 1
      omega
    · change E 1 ≤ 1
      omega
    · change E 2 ≤ 2
      omega
    · change E 3 ≤ 1
      omega
    · change E 4 ≤ 1
      omega
    · change E 5 ≤ 1
      omega

theorem certificate58Six_0 : ProfileCondition firstSixOddPrimes (profiles58Six 0) := by
  change ProfileCondition ![3, 5, 7, 11, 13, 17] ![1, 1, 2, 1, 1, 1]
  left
  decide +kernel

#print axioms certificate58Six_0

theorem certificate58Six_1 : ProfileCondition firstSixOddPrimes (profiles58Six 1) := by
  change ProfileCondition ![3, 5, 7, 11, 13, 17] ![2, 2, 1, 1, 1, 1]
  left
  decide +kernel

#print axioms certificate58Six_1

theorem certificate58Six_2 : ProfileCondition firstSixOddPrimes (profiles58Six 2) := by
  change ProfileCondition ![3, 5, 7, 11, 13, 17] ![4, 1, 1, 1, 1, 1]
  right
  refine ⟨(1/480 : ℚ), by norm_num, ?_⟩
  decide +kernel

#print axioms certificate58Six_2

theorem profiles58Six_certificate (j : Fin 3) :
    ProfileCondition firstSixOddPrimes (profiles58Six j) := by
  fin_cases j
  · exact certificate58Six_0
  · exact certificate58Six_1
  · exact certificate58Six_2

theorem profile_weight_below_fiftyeight_six (E : Fin 6 → ℕ)
    (hE : ∀ i, 1 ≤ E i) (hw : (∑ i, E i * (firstSixOddPrimes i - 1)) < 58) :
    ProfileCondition firstSixOddPrimes E := by
  obtain ⟨j, hj⟩ := profile58Six_domination E hE hw
  exact ProfileCondition.mono firstSixOddPrimes E (profiles58Six j)
    (by intro i; fin_cases i <;> norm_num [firstSixOddPrimes]) hj (profiles58Six_certificate j)

#print axioms profile_weight_below_fiftyeight_six

end Erdos7CardinalitySieve


/-! Application of the cardinality-constrained sieve to odd covers. -/
namespace Erdos7CardinalitySieve
open Erdos7Reduction Erdos7FiniteSieve
set_option maxHeartbeats 2000000

/-- Sorted odd primes dominate the first six odd primes. -/
theorem sorted_first_six_lower (p : Fin 6 → ℕ) (hp : ∀ i, (p i).Prime)
    (ho : ∀ i, Odd (p i)) (hmono : StrictMono p) :
    ∀ i, firstSixOddPrimes i ≤ p i := by
  let q (i : Fin 5) := p i.castSucc
  have hlow := sorted_first_five_lower q (fun i => hp i.castSucc)
    (fun i => ho i.castSucc) (fun _ _ hij => hmono hij)
  have h4 : 13 ≤ p 4 := hlow 4
  have h5 : 17 ≤ p 5 := by
    have := hmono (by decide : (4 : Fin 6) < 5)
    have := Nat.odd_iff.mp (ho 5)
    have hn15 : p 5 ≠ 15 := by intro he; have hh := hp 5; norm_num [he] at hh
    omega
  intro i
  fin_cases i
  · exact hlow 0
  · exact hlow 1
  · exact hlow 2
  · exact hlow 3
  · exact hlow 4
  · exact h5

/-- Seven distinct odd primes have total digit weight at least sixty-eight. -/
theorem seven_odd_prime_sum (P : Finset ℕ) (hcard : 7 ≤ P.card)
    (hp : ∀ p ∈ P, p.Prime ∧ Odd p) : 68 ≤ ∑ p ∈ P, (p - 1) := by
  classical
  obtain ⟨S, hSP, hSc⟩ := Finset.exists_subset_card_eq hcard
  let p := S.orderEmbOfFin hSc
  have hprime (i : Fin 7) : (p i).Prime := (hp _ (hSP (S.orderEmbOfFin_mem hSc i))).1
  have hodd (i : Fin 7) : Odd (p i) := (hp _ (hSP (S.orderEmbOfFin_mem hSc i))).2
  let q (i : Fin 6) := p i.castSucc
  have hlow : ∀ i : Fin 6, firstSixOddPrimes i ≤ q i :=
    sorted_first_six_lower q (fun i => hprime i.castSucc) (fun i => hodd i.castSucc)
      (fun _ _ hij => p.strictMono hij)
  have h5 : 17 ≤ p 5 := hlow 5
  have h6 : 19 ≤ p 6 := by
    have := p.strictMono (by decide : (5 : Fin 7) < 6)
    have := Nat.odd_iff.mp (hodd 6)
    omega
  have hfirst : 50 ≤ ∑ i : Fin 6, (q i - 1) := by
    calc
      50 = ∑ i : Fin 6, (firstSixOddPrimes i - 1) := by
        norm_num [firstSixOddPrimes, Fin.sum_univ_succ]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => Nat.sub_le_sub_right (hlow i) 1)
  have hS : 68 ≤ ∑ r ∈ S, (r - 1) := by
    rw [← S.map_orderEmbOfFin_univ hSc, Finset.sum_map]
    change 68 ≤ ∑ i : Fin 7, (p i - 1)
    rw [Fin.sum_univ_castSucc]
    change 68 ≤ (∑ i : Fin 6, (q i - 1)) + (p 6 - 1)
    omega
  exact hS.trans (Finset.sum_le_sum_of_subset hSP)

/-- The arithmetic application of a finite family of profile certificates. -/
theorem no_cover_of_fiftyeight_profile_certificates {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a)
    (hpriv : ∀ k, ∃ x : ℤ, ∀ l, l ≠ k → ¬ (m l : ℤ) ∣ x - a l)
    (hclosed : ∀ k d, 1 < d → d ∣ m k → ∃ l, m l = d)
    (hcard : Fintype.card κ ≤ 58)
    (r : ℕ) (q : Fin r → ℕ) (hq : ∀ i, 2 < q i)
    (hPcard : (Finset.univ.biUnion (fun k => (m k).primeFactors)).card = r)
    (hlower : ∀ i, q i ≤ (Finset.univ.biUnion (fun k => (m k).primeFactors)).orderEmbOfFin hPcard i)
    (hcert : ∀ E : Fin r → ℕ, (∀ i, 1 ≤ E i) → (∑ i, E i * (q i - 1)) < 58 →
      ProfileCondition q E)
    (hsmall : ∀ E : Fin r → ℕ, (∀ i, 1 ≤ E i) → (∑ i, E i) < 6 →
      mixedCapacity (fun i => finitePrimeCapacity (q i) (E i)) < 1) : False := by
  classical
  have hm : ∀ k, 1 < m k := fun k => (hc.2.1 k).1
  have hm0 : ∀ k, m k ≠ 0 := fun k => by have := hm k; omega
  have ho : ∀ k, Odd (m k) := fun k => (hc.2.1 k).2
  let P := Finset.univ.biUnion (fun k => (m k).primeFactors)
  have hpP : ∀ p ∈ P, p.Prime ∧ Odd p := by
    intro p hp
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hp
    have hh := Nat.mem_primeFactors.mp hk
    exact ⟨hh.1, (ho k).of_dvd_nat hh.2.1⟩
  let p := P.orderEmbOfFin hPcard
  have hprime (i : Fin r) : (p i).Prime := (hpP _ (P.orderEmbOfFin_mem hPcard i)).1
  have hlow (i : Fin r) : q i ≤ p i := hlower i
  have hp2 (i : Fin r) : 2 < p i := (hq i).trans_le (hlow i)
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hprime i) (hprime j)).mpr (fun h => hij (p.injective h))
  let e (k : κ) (i : Fin r) := (m k).factorization (p i)
  let E (i : Fin r) := Finset.univ.sup (fun k => e k i)
  have heE (k : κ) (i : Fin r) : e k i ≤ E i :=
    Finset.le_sup (f := fun k => e k i) (Finset.mem_univ k)
  have hprod (k : κ) : m k = ∏ i : Fin r, p i ^ e k i := by
    have hsub : (m k).primeFactors ⊆ P := by
      intro t ht
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, ht⟩
    have hh := Erdos7Compression.factorization_product_over_superset (m k) (hm0 k) P hsub
    rw [Finset.prod_coe_sort P (fun t => t ^ (m k).factorization t)] at hh
    nth_rw 1 [hh]
    conv_lhs => rw [← P.map_orderEmbOfFin_univ hPcard]
    exact Finset.prod_map _ _ (fun t : ℕ => t ^ (m k).factorization t)
  have hei : Function.Injective e := by
    intro k l hkl
    apply hc.1
    rw [hprod k, hprod l, hkl]
  have he0 (k : κ) : ∃ i, e k i ≠ 0 := by
    by_contra! h
    have hh := hm k
    rw [hprod k] at hh
    simp only [h, pow_zero, Finset.prod_const_one] at hh
    omega
  have hEpos (i : Fin r) : 1 ≤ E i := by
    have hiP := P.orderEmbOfFin_mem hPcard i
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hiP
    have hfac : 0 < e k i := (hprime i).factorization_pos_of_dvd (hm0 k)
      (Nat.mem_primeFactors.mp hk).2.1
    have hh := heE k i
    omega
  have hcov : ∀ x : ℤ, ∃ k, ((∏ i : Fin r, p i ^ e k i : ℕ) : ℤ) ∣ x - a k := by
    simpa only [← hprod] using hc.2.2
  have hprivate : ∀ k, ∃ x : ℤ, ∀ l, l ≠ k →
      ¬ ((∏ i : Fin r, p i ^ e l i : ℕ) : ℤ) ∣ x - a l := by
    simpa only [← hprod] using hpriv
  have hweight := Erdos7Digits.coprime_power_irredundant_digit_bound p
    (fun i => (hprime i).pos) hcop e a hcov hprivate
  change (∑ i, E i * (p i - 1)) < Fintype.card κ at hweight
  have hfixedWeight : (∑ i, E i * (q i - 1)) < 58 := by
    have hle : (∑ i, E i * (q i - 1)) ≤ ∑ i, E i * (p i - 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.mul_le_mul_left (E i) (Nat.sub_le_sub_right (hlow i) 1)
    exact hle.trans_lt (hweight.trans_le hcard)
  have hbound := finite_exponent_cover_bound p E hp2 hcop e hei he0 heE a hcov
  have hleCap : mixedCapacity (fun i => finitePrimeCapacity (p i) (E i)) ≤
      mixedCapacity (fun i => finitePrimeCapacity (q i) (E i)) := by
    apply mixedCapacity_mono
    · intro i
      exact finitePrimeCapacity_nonneg (p i) (E i) (hp2 i)
    · intro i
      exact finitePrimeCapacity_antitone_base _ _ _ (hq i) (hlow i)
  have hEtotal : 6 ≤ ∑ i, E i := by
    by_contra h
    exact (not_lt_of_ge (hbound.trans hleCap)) (hsmall E hEpos (by omega))
  rcases hcert E hEpos hfixedWeight with hfull | ⟨t, ht, hthreshold⟩
  · exact (not_lt_of_ge (hbound.trans hleCap)) hfull
  · have hmixed := divisor_closed_mixed_card_bound m hm0 hclosed p hprime p.injective 58 hcard
    have hK : (Finset.univ.filter (fun k => 2 ≤ (exponentSupport (e k)).card)).card ≤ 52 := by
      change (Finset.univ.filter (fun k => 2 ≤ (exponentSupport (e k)).card)).card ≤
        58 - ∑ i, E i at hmixed
      omega
    have hb := finite_exponent_cover_threshold p E hp2 hcop e hei he0 heE a hcov 52 hK t ht
    change (1 : ℚ) ≤ thresholdCapacity p E 52 t at hb
    have hle := thresholdCapacity_antitone_base q p E 52 t hq hlow
    exact (not_lt_of_ge (hb.trans hle)) hthreshold

theorem five_small_exponent_capacity (E : Fin 5 → ℕ) (hE : ∀ i, 1 ≤ E i)
    (hsum : (∑ i, E i) < 6) :
    mixedCapacity (fun i => finitePrimeCapacity (firstFiveOddPrimes i) (E i)) < 1 := by
  have h0 := hE 0
  have h1 := hE 1
  have h2 := hE 2
  have h3 := hE 3
  have h4 := hE 4
  have hEsum : E 0 + E 1 + E 2 + E 3 + E 4 < 6 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsum
  have hconst : E = fun _ => 1 := by
    funext i
    fin_cases i <;> dsimp <;> omega
  rw [hconst]
  norm_num [mixedCapacity_eq, firstFiveOddPrimes, finitePrimeCapacity,
    positivePowerSum_eq_sum, Fin.sum_univ_succ, Fin.prod_univ_succ, Finset.sum_range_succ]

theorem six_small_exponent_capacity (E : Fin 6 → ℕ) (hE : ∀ i, 1 ≤ E i)
    (hsum : (∑ i, E i) < 6) :
    mixedCapacity (fun i => finitePrimeCapacity (firstSixOddPrimes i) (E i)) < 1 := by
  have hle : 6 ≤ ∑ i, E i := by
    calc
      6 = ∑ _i : Fin 6, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hE i)
  omega

/-- No irredundant divisor-closed odd cover has at most fifty-eight classes. -/
theorem no_irredundant_divisor_closed_odd_cover_fiftyeight {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a)
    (hpriv : ∀ k, ∃ x : ℤ, ∀ l, l ≠ k → ¬ (m l : ℤ) ∣ x - a l)
    (hclosed : ∀ k d, 1 < d → d ∣ m k → ∃ l, m l = d)
    (hcard : Fintype.card κ ≤ 58) : False := by
  classical
  have hm : ∀ k, 1 < m k := fun k => (hc.2.1 k).1
  have hm0 : ∀ k, m k ≠ 0 := fun k => by have := hm k; omega
  have ho : ∀ k, Odd (m k) := fun k => (hc.2.1 k).2
  let P := Finset.univ.biUnion (fun k => (m k).primeFactors)
  have hpP : ∀ p ∈ P, p.Prime ∧ Odd p := by
    intro p hp
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hp
    have hh := Nat.mem_primeFactors.mp hk
    exact ⟨hh.1, (ho k).of_dvd_nat hh.2.1⟩
  have hPfive : 5 ≤ P.card := arithmetic_cover_prime_count m a hm hc.1 ho hc.2.2
  have hprimeSum : (∑ p ∈ P, (p - 1)) < Fintype.card κ :=
    arithmetic_irredundant_prime_sum_bound m a hm0 hc.2.2 hpriv
  have hPcard : P.card = 5 ∨ P.card = 6 := by
    by_contra h
    have h7 : 7 ≤ P.card := by omega
    have hh := seven_odd_prime_sum P h7 hpP
    omega
  rcases hPcard with h5 | h6
  · have hlow : ∀ i, firstFiveOddPrimes i ≤ P.orderEmbOfFin h5 i :=
      sorted_first_five_lower (P.orderEmbOfFin h5)
        (fun i => (hpP _ (P.orderEmbOfFin_mem h5 i)).1)
        (fun i => (hpP _ (P.orderEmbOfFin_mem h5 i)).2) (P.orderEmbOfFin h5).strictMono
    exact no_cover_of_fiftyeight_profile_certificates m a hc hpriv hclosed hcard 5 firstFiveOddPrimes
      (by intro i; fin_cases i <;> norm_num [firstFiveOddPrimes]) h5 hlow
      profile_weight_below_fiftyeight_five five_small_exponent_capacity
  · have hlow : ∀ i, firstSixOddPrimes i ≤ P.orderEmbOfFin h6 i :=
      sorted_first_six_lower (P.orderEmbOfFin h6)
        (fun i => (hpP _ (P.orderEmbOfFin_mem h6 i)).1)
        (fun i => (hpP _ (P.orderEmbOfFin_mem h6 i)).2) (P.orderEmbOfFin h6).strictMono
    exact no_cover_of_fiftyeight_profile_certificates m a hc hpriv hclosed hcard 6 firstSixOddPrimes
      (by intro i; fin_cases i <;> norm_num [firstSixOddPrimes]) h6 hlow
      profile_weight_below_fiftyeight_six six_small_exponent_capacity

/-- Every odd arithmetic covering system with distinct moduli has at least 59 classes. -/
theorem arithmetic_cover_at_least_fiftynine {κ : Type} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a) :
    59 ≤ Fintype.card κ := by
  classical
  by_contra h
  have hcard : Fintype.card κ ≤ 58 := by omega
  let N := Finset.univ.lcm m
  have hN0 : N ≠ 0 := Finset.lcm_ne_zero_iff.mpr
    (fun k _ => by have := (hc.2.1 k).1; omega)
  have hcover : HasOddArithmeticCover N 58 :=
    ⟨Nat.pos_of_ne_zero hN0, κ, inferInstance, m, a, hc.1, hc.2.1, hc.2.2,
      fun k => Finset.dvd_lcm (Finset.mem_univ k), hcard⟩
  obtain ⟨ι, fι, n, b, hn, _, hnc, hnclosed, hnpriv⟩ :=
    exists_irredundant_divisor_closed_odd_cover N 58 hcover
  letI : Fintype ι := fι
  exact no_irredundant_divisor_closed_odd_cover_fiftyeight n b hn hnpriv hnclosed hnc

/-- Every odd strict covering system needs at least fifty-nine moduli. -/
theorem at_least_fiftynine_moduli (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i, ¬ C.moduli i ≤ Ideal.span {2}) :
    letI := C.fintypeIndex
    59 ≤ Fintype.card C.ι := by
  letI := C.fintypeIndex
  exact arithmetic_cover_at_least_fiftynine (fun i => (C.moduli i).absNorm) C.residue
    ⟨moduli_absNorm_injective C, fun i => ⟨moduli_absNorm_gt_one C i,
      (ideal_not_le_two_iff _).mp (hodd i)⟩, arithmetic_cover C⟩

#print axioms no_irredundant_divisor_closed_odd_cover_fiftyeight
#print axioms arithmetic_cover_at_least_fiftynine
#print axioms at_least_fiftynine_moduli
#print axioms no_cover_of_fiftyeight_profile_certificates
end Erdos7CardinalitySieve


/-! Uniform saturation bounds for prime-support stars. -/
namespace Erdos7StarSieve
open Erdos7Reduction
set_option maxHeartbeats 2000000

/-- Tensor weights of an injective family are bounded by the full product. -/
theorem paired_weight_bound {κ : Type*} [DecidableEq κ]
    (K : Finset κ) (a b : κ → ℕ)
    (hinj : Set.InjOn (fun k => (a k, b k)) K)
    (A B : Finset ℕ) (hA : ∀ k ∈ K, a k ∈ A) (hB : ∀ k ∈ K, b k ∈ B)
    (u v : ℕ → ℚ) (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n) :
    ∑ k ∈ K, u (a k) * v (b k) ≤ (∑ n ∈ A, u n) * ∑ n ∈ B, v n := by
  have himg : K.image (fun k => (a k, b k)) ⊆ A ×ˢ B := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_product.mpr ⟨hA k hk, hB k hk⟩
  have hs := Finset.sum_le_sum_of_subset_of_nonneg himg
    (fun z _ _ => mul_nonneg (hu z.1) (hv z.2))
  rw [Finset.sum_image hinj, Finset.sum_product] at hs
  simpa only [← Finset.mul_sum, ← Finset.sum_mul] using hs

/-- The elementary weighted union bound for a cover of a nonempty finite set. -/
theorem finite_set_cover_weight {A κ : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (K : Finset κ) (B : κ → Finset A) (w : κ → ℚ)
    (hcard : ∀ k ∈ K, ((B k).card : ℚ) ≤ (Fintype.card A : ℚ) * w k)
    (hcover : ∀ x : A, ∃ k ∈ K, x ∈ B k) :
    (1 : ℚ) ≤ ∑ k ∈ K, w k := by
  classical
  have hU : (Finset.univ : Finset A) ⊆ K.biUnion B := by
    intro x _
    obtain ⟨k, hk, hx⟩ := hcover x
    exact Finset.mem_biUnion.mpr ⟨k, hk, hx⟩
  have hc : (Fintype.card A : ℚ) ≤ ∑ k ∈ K, ((B k).card : ℚ) := by
    exact_mod_cast (Finset.card_le_card hU).trans (Finset.card_biUnion_le (s := K) (t := B))
  have hs : (∑ k ∈ K, ((B k).card : ℚ)) ≤ (Fintype.card A : ℚ) * ∑ k ∈ K, w k := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hcard
  have hpos : (0 : ℚ) < Fintype.card A := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
  nlinarith [hc.trans hs]

/-- A collection saturates a hub fibre if its active leaf sections cover the leaf. -/
def saturatedHubSet {H A κ : Type*} [Fintype H] [Fintype A]
    [DecidableEq H] [DecidableEq A] [DecidableEq κ]
    (K : Finset κ) (X : κ → Finset H) (Y : κ → Finset A) : Finset H :=
  Finset.univ.filter (fun x => ∀ y : A, ∃ k ∈ K, x ∈ X k ∧ y ∈ Y k)

/-- If low-level sections cannot cover a leaf, saturation requires high-level mass. -/
theorem saturatedHubSet_weight_bound {H A κ : Type*}
    [Fintype H] [Fintype A] [Nonempty A]
    [DecidableEq H] [DecidableEq A] [DecidableEq κ]
    (K : Finset κ) (X : κ → Finset H) (Y : κ → Finset A)
    (Low : κ → Prop) [DecidablePred Low] (w : κ → ℚ) (hw : ∀ k, 0 ≤ w k)
    (L R : ℚ)
    (hY : ∀ k ∈ K, ((Y k).card : ℚ) ≤ (Fintype.card A : ℚ) * w k)
    (hLow : ∑ k ∈ K with Low k, w k ≤ L)
    (hHigh : ∑ k ∈ K with ¬ Low k, ((X k).card : ℚ) * w k ≤ (Fintype.card H : ℚ) * R) :
    ((saturatedHubSet K X Y).card : ℚ) * (1 - L) ≤ (Fintype.card H : ℚ) * R := by
  classical
  let D := saturatedHubSet K X Y
  have hpoint (x : H) (hx : x ∈ D) :
      1 - L ≤ ∑ k ∈ K with ¬ Low k, if x ∈ X k then w k else 0 := by
    have hcov : ∀ y : A, ∃ k ∈ K.filter (fun k => x ∈ X k), y ∈ Y k := by
      intro y
      obtain ⟨k, hk, hxk, hyk⟩ := (Finset.mem_filter.mp hx).2 y
      exact ⟨k, Finset.mem_filter.mpr ⟨hk, hxk⟩, hyk⟩
    have hb := finite_set_cover_weight (K.filter (fun k => x ∈ X k)) Y w
      (fun k hk => hY k (Finset.mem_filter.mp hk).1) hcov
    rw [Finset.sum_filter] at hb
    have hsplit := Finset.sum_filter_add_sum_filter_not K Low
      (fun k => if x ∈ X k then w k else 0)
    have hlo : (∑ k ∈ K with Low k, if x ∈ X k then w k else 0) ≤ L := by
      apply le_trans _ hLow
      apply Finset.sum_le_sum
      intro k _
      split_ifs
      · exact le_rfl
      · exact hw k
    linarith
  have hsum : (D.card : ℚ) * (1 - L) ≤
      ∑ x ∈ D, ∑ k ∈ K with ¬ Low k, if x ∈ X k then w k else 0 := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hpoint
  rw [Finset.sum_comm] at hsum
  have hbound : (∑ k ∈ K with ¬ Low k, ∑ x ∈ D, if x ∈ X k then w k else 0) ≤
      ∑ k ∈ K with ¬ Low k, ((X k).card : ℚ) * w k := by
    apply Finset.sum_le_sum
    intro k _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (hw k)
    exact_mod_cast Finset.card_le_card (show D.filter (fun x => x ∈ X k) ⊆ X k from
      fun x hx => (Finset.mem_filter.mp hx).2)
  exact hsum.trans (hbound.trans hHigh)

/-- A finite geometric sum starting at zero. -/
theorem geometric_sum_le (q : ℕ) (hq : 1 < q) (S : Finset ℕ) :
    ∑ a ∈ S, ((q : ℚ)⁻¹)^a ≤ (q : ℚ) / (q - 1) := by
  have hh := positive_geometric_sum_le q hq (S.erase 0)
    (fun a ha => by have := (Finset.mem_erase.mp ha).1; omega)
  have hqQ : (1 : ℚ) < q := by exact_mod_cast hq
  have hformula : (q : ℚ) / (q - 1) = 1 + 1 / (q - 1) := by field_simp [show (q : ℚ) - 1 ≠ 0 by linarith]; ring
  rw [hformula]
  by_cases h0 : 0 ∈ S
  · have hs := Finset.sum_erase_add S (fun a => ((q : ℚ)⁻¹)^a) h0
    simp only [pow_zero] at hs
    linarith
  · simpa [Finset.erase_eq_of_notMem h0] using hh.trans (by linarith : (1 : ℚ) / (q - 1) ≤ 1 + 1 / (q - 1))

/-- Geometric tails are uniformly small, independently of the exponent cap. -/
theorem geometric_tail_le (q T : ℕ) (hq : 1 < q) (S : Finset ℕ)
    (hS : ∀ a ∈ S, T ≤ a) :
    ∑ a ∈ S, ((q : ℚ)⁻¹)^a ≤ ((q : ℚ)⁻¹)^T * ((q : ℚ) / (q - 1)) := by
  have hinj : Set.InjOn (fun a => a - T) S := by
    intro a ha b hb hab
    have := hS a ha
    have := hS b hb
    dsimp only at hab
    omega
  have hh := geometric_sum_le q hq (S.image (fun a => a - T))
  rw [Finset.sum_image hinj] at hh
  have hs : (∑ a ∈ S, ((q : ℚ)⁻¹)^a) =
      ((q : ℚ)⁻¹)^T * ∑ a ∈ S, ((q : ℚ)⁻¹)^(a - T) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← pow_add, Nat.add_sub_of_le (hS a ha)]
  rw [hs]
  exact mul_le_mul_of_nonneg_left hh (by positivity)

/-- A leaf can saturate only on a geometrically small set of hub values. -/
theorem star_leaf_saturation_bound {H A κ : Type*}
    [Fintype H] [Fintype A] [Nonempty A]
    [DecidableEq H] [DecidableEq A] [DecidableEq κ]
    (q p : ℕ) (hq : 1 < q) (hp : 2 < p)
    (K : Finset κ) (a b : κ → ℕ)
    (hinj : Set.InjOn (fun k => (a k, b k)) K) (hb : ∀ k ∈ K, 0 < b k)
    (X : κ → Finset H) (Y : κ → Finset A)
    (hX : ∀ k ∈ K, ((X k).card : ℚ) ≤ (Fintype.card H : ℚ) * ((q : ℚ)⁻¹)^(a k))
    (hY : ∀ k ∈ K, ((Y k).card : ℚ) ≤ (Fintype.card A : ℚ) * ((p : ℚ)⁻¹)^(b k)) :
    ((saturatedHubSet K X Y).card : ℚ) ≤
      (Fintype.card H : ℚ) * (((q : ℚ)⁻¹)^(p - 2) * ((q : ℚ) / (q - 1))) := by
  let T := p - 2
  let B := K.image b
  let C := (K.image a).filter (fun n => T ≤ n)
  let tail : ℚ := ((q : ℚ)⁻¹)^T * ((q : ℚ) / (q - 1))
  have hpQ : (2 : ℚ) < p := by exact_mod_cast hp
  have hden : (0 : ℚ) < p - 1 := by linarith
  have hB : (∑ n ∈ B, ((p : ℚ)⁻¹)^n) ≤ 1 / (p - 1) := by
    apply positive_geometric_sum_le p (by omega)
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
    exact hb k hk
  have hC : (∑ n ∈ C, ((q : ℚ)⁻¹)^n) ≤ tail :=
    geometric_tail_le q T hq C (fun n hn => (Finset.mem_filter.mp hn).2)
  have hlow : (∑ k ∈ K with a k < T, ((p : ℚ)⁻¹)^(b k)) ≤ (T : ℚ) / (p - 1) := by
    have hh := paired_weight_bound (K.filter (fun k => a k < T)) a b
      (hinj.mono (Finset.filter_subset _ _)) (Finset.range T) B
      (fun k hk => Finset.mem_range.mpr (Finset.mem_filter.mp hk).2)
      (fun k hk => Finset.mem_image.mpr ⟨k, (Finset.mem_filter.mp hk).1, rfl⟩)
      (fun _ => 1) (fun n => ((p : ℚ)⁻¹)^n) (by intros; norm_num) (by intros; positivity)
    simp only [one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hh
    calc
      _ ≤ (T : ℚ) * ∑ n ∈ B, ((p : ℚ)⁻¹)^n := hh
      _ ≤ (T : ℚ) * (1 / (p - 1)) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = _ := by ring
  have hhigh : (∑ k ∈ K with ¬ a k < T, ((X k).card : ℚ) * ((p : ℚ)⁻¹)^(b k)) ≤
      (Fintype.card H : ℚ) * (tail / (p - 1)) := by
    have hh := paired_weight_bound (K.filter (fun k => ¬ a k < T)) a b
      (hinj.mono (Finset.filter_subset _ _)) C B
      (fun k hk => Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨k, (Finset.mem_filter.mp hk).1, rfl⟩,
          by have := (Finset.mem_filter.mp hk).2; omega⟩)
      (fun k hk => Finset.mem_image.mpr ⟨k, (Finset.mem_filter.mp hk).1, rfl⟩)
      (fun n => ((q : ℚ)⁻¹)^n) (fun n => ((p : ℚ)⁻¹)^n)
      (by intros; positivity) (by intros; positivity)
    have hprod : (∑ n ∈ C, ((q : ℚ)⁻¹)^n) * (∑ n ∈ B, ((p : ℚ)⁻¹)^n) ≤ tail / (p - 1) := by
      calc
        _ ≤ tail * (1 / (p - 1)) := mul_le_mul hC hB (by positivity) (by
          have hqQ : (1 : ℚ) < q := by exact_mod_cast hq
          have hqden : (0 : ℚ) < q - 1 := by linarith
          dsimp [tail]
          positivity)
        _ = _ := by ring
    calc
      _ ≤ ∑ k ∈ K with ¬ a k < T,
          (Fintype.card H : ℚ) * (((q : ℚ)⁻¹)^(a k) * ((p : ℚ)⁻¹)^(b k)) := by
        apply Finset.sum_le_sum
        intro k hk
        have h := mul_le_mul_of_nonneg_right (hX k (Finset.mem_filter.mp hk).1)
          (show 0 ≤ ((p : ℚ)⁻¹)^(b k) by positivity)
        simpa only [mul_assoc] using h
      _ = (Fintype.card H : ℚ) * ∑ k ∈ K with ¬ a k < T,
          ((q : ℚ)⁻¹)^(a k) * ((p : ℚ)⁻¹)^(b k) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hh.trans hprod) (by positivity)
  have hs := saturatedHubSet_weight_bound K X Y (fun k => a k < T)
    (fun k => ((p : ℚ)⁻¹)^(b k)) (by intros; positivity)
    ((T : ℚ) / (p - 1)) (tail / (p - 1)) hY hlow hhigh
  have hT : (T : ℚ) = (p : ℚ) - 2 := by
    dsimp [T]
    exact Nat.cast_sub (by omega)
  have hL : 1 - (T : ℚ) / (p - 1) = 1 / (p - 1) := by
    rw [hT]
    field_simp
    ring
  rw [hL, mul_one_div, ← mul_div_assoc] at hs
  exact (div_le_div_iff_of_pos_right hden).mp hs

/-- Hub-density cost of saturating a leaf prime. -/
def hubTail (q p : ℕ) : ℚ := ((q : ℚ)⁻¹)^(p - 2) * ((q : ℚ) / (q - 1))

theorem hubTail_eq (q p : ℕ) (hq : 1 < q) (hp : 2 < p) :
    hubTail q p = ((q : ℚ)⁻¹)^(p - 3) / (q - 1) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  unfold hubTail
  rw [show p - 2 = (p - 3) + 1 by omega, pow_succ]
  calc
    _ = (((q : ℚ)⁻¹)^(p - 3) * ((q : ℚ)⁻¹ * q)) / (q - 1) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hq0, mul_one]

theorem hubTail_antitone (q r p : ℕ) (hq : 1 < q) (hqr : q ≤ r) (hp : 2 < p) :
    hubTail r p ≤ hubTail q p := by
  have hr : 1 < r := hq.trans_le hqr
  rw [hubTail_eq r p hr hp, hubTail_eq q p hq hp]
  have hqQ : (1 : ℚ) < q := by exact_mod_cast hq
  have hqrQ : (q : ℚ) ≤ r := by exact_mod_cast hqr
  have hi : (r : ℚ)⁻¹ ≤ (q : ℚ)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by linarith : (0 : ℚ) < q) hqrQ
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℚ) ≤ (r : ℚ)⁻¹) hi (p - 3)
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  have h₁ := mul_le_mul_of_nonneg_right hpow (by linarith : (0 : ℚ) ≤ q - 1)
  have h₂ := mul_le_mul_of_nonneg_left
    (by linarith : (q : ℚ) - 1 ≤ r - 1) (show 0 ≤ ((q : ℚ)⁻¹)^(p - 3) by positivity)
  exact h₁.trans h₂

/-- Odd indices occupy only every second exponent in the geometric tail. -/
theorem odd_power_sum_le (q b : ℕ) (hq : 1 < q) (hb : Odd b)
    (P : Finset ℕ) (hP : ∀ p ∈ P, b ≤ p ∧ Odd p) :
    ∑ p ∈ P, ((q : ℚ)⁻¹)^(p - b) ≤ ((q^2 : ℕ) : ℚ) / (((q^2 : ℕ) : ℚ) - 1) := by
  let f (p : ℕ) := (p - b) / 2
  have hpform (p : ℕ) (hp : p ∈ P) : p = b + 2 * f p := by
    have hbodd := Nat.odd_iff.mp hb
    have hpodd := Nat.odd_iff.mp (hP p hp).2
    have hle := (hP p hp).1
    dsimp [f]
    omega
  have hfi : Set.InjOn f P := by
    intro p hp r hr hpr
    have h₁ := hpform p hp
    have h₂ := hpform r hr
    omega
  have hq2 : 1 < q^2 := Nat.one_lt_pow (by norm_num) hq
  have hg := geometric_sum_le (q^2) hq2 (P.image f)
  rw [Finset.sum_image hfi] at hg
  have heq : (∑ p ∈ P, ((q : ℚ)⁻¹)^(p - b)) =
      ∑ p ∈ P, ((((q^2 : ℕ) : ℚ)⁻¹)^(f p)) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hex : p - b = 2 * f p := by have := hpform p hp; omega
    rw [hex, pow_mul, Nat.cast_pow, inv_pow]
  rwa [heq]

theorem odd_hubTail_sum_le (q b : ℕ) (hq : 1 < q) (hb3 : 3 ≤ b) (hb : Odd b)
    (P : Finset ℕ) (hP : ∀ p ∈ P, b ≤ p ∧ Odd p) :
    ∑ p ∈ P, hubTail q p ≤
      (((q : ℚ)⁻¹)^(b - 3) / (q - 1)) * (((q^2 : ℕ) : ℚ) / (((q^2 : ℕ) : ℚ) - 1)) := by
  have hqQ : (1 : ℚ) < q := by exact_mod_cast hq
  have hden : (0 : ℚ) < q - 1 := by linarith
  have heq : (∑ p ∈ P, hubTail q p) =
      (((q : ℚ)⁻¹)^(b - 3) / (q - 1)) * ∑ p ∈ P, ((q : ℚ)⁻¹)^(p - b) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hpb := (hP p hp).1
    rw [hubTail_eq q p hq (by omega), show p - 3 = (b - 3) + (p - b) by omega, pow_add]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (odd_power_sum_le q b hq hb P hP) (by positivity)

/-- A uniform budget for any odd hub and arbitrarily many distinct odd leaves. -/
theorem star_budget_le_nine_sixteenths (q : ℕ) (hq : 2 < q) (hoq : Odd q)
    (P : Finset ℕ) (hP : ∀ p ∈ P, 2 < p ∧ Odd p) (hqP : q ∉ P) :
    1 / (q - 1 : ℚ) + ∑ p ∈ P, hubTail q p ≤ 9/16 := by
  by_cases hq3 : q = 3
  · subst q
    have hP5 : ∀ p ∈ P, 5 ≤ p ∧ Odd p := by
      intro p hp
      have hpo := Nat.odd_iff.mp (hP p hp).2
      have hp3 := (hP p hp).1
      have hne : p ≠ 3 := by intro he; subst p; exact hqP hp
      exact ⟨by omega, (hP p hp).2⟩
    have hh := odd_hubTail_sum_le 3 5 (by norm_num) (by norm_num) (by norm_num) P hP5
    norm_num at hh ⊢
    linarith
  · have hq5 : 5 ≤ q := by have := Nat.odd_iff.mp hoq; omega
    have hh := odd_hubTail_sum_le 5 3 (by norm_num) (by norm_num) (by norm_num) P
      (fun p hp => ⟨by have := (hP p hp).1; omega, (hP p hp).2⟩)
    have hle : (∑ p ∈ P, hubTail q p) ≤ ∑ p ∈ P, hubTail 5 p :=
      Finset.sum_le_sum (fun p hp => hubTail_antitone 5 q p (by norm_num) hq5 (hP p hp).1)
    have hqQ : (5 : ℚ) ≤ q := by exact_mod_cast hq5
    have hfirst : 1 / (q - 1 : ℚ) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    norm_num at hh
    linarith

/-- Saturating one leaf is necessary to cover all leaf choices at a fixed hub. -/
theorem star_cover_saturation {H ι κ : Type*} [Fintype ι]
    [Fintype H] [DecidableEq H] [DecidableEq κ]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (Pure : Finset κ) (K : ι → Finset κ) (X : κ → Finset H)
    (Y : ∀ i, κ → Finset (A i))
    (hcover : ∀ (x : H) (y : ∀ i, A i),
      (∃ k ∈ Pure, x ∈ X k) ∨ ∃ i, ∃ k ∈ K i, x ∈ X k ∧ y i ∈ Y i k) (x : H) :
    x ∈ Pure.biUnion X ∨ ∃ i, x ∈ saturatedHubSet (K i) X (Y i) := by
  classical
  by_contra h
  push_neg at h
  have hmiss (i : ι) : ∃ y : A i, ∀ k ∈ K i, x ∈ X k → y ∉ Y i k := by
    have hi := h.2 i
    simp only [saturatedHubSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    push_neg at hi
    simpa only [not_and] using hi
  choose y hy using hmiss
  rcases hcover x y with ⟨k, hk, hx⟩ | ⟨i, k, hk, hx, hxy⟩
  · exact h.1 (Finset.mem_biUnion.mpr ⟨k, hk, hx⟩)
  · exact hy i k hk hx hxy

/-- A cover with star-shaped support must exhaust the hub saturation budget. -/
theorem star_box_cover_budget {H ι κ : Type*} [Fintype ι]
    [Fintype H] [Nonempty H] [DecidableEq H] [DecidableEq κ]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (q : ℕ) (hq : 1 < q) (p : ι → ℕ) (hp : ∀ i, 2 < p i)
    (Pure : Finset κ) (K : ι → Finset κ) (a : κ → ℕ) (b : ι → κ → ℕ)
    (hap : Set.InjOn a Pure) (hapos : ∀ k ∈ Pure, 0 < a k)
    (hab : ∀ i, Set.InjOn (fun k => (a k, b i k)) (K i)) (hb : ∀ i k, k ∈ K i → 0 < b i k)
    (X : κ → Finset H) (Y : ∀ i, κ → Finset (A i))
    (hX : ∀ k, ((X k).card : ℚ) ≤ (Fintype.card H : ℚ) * ((q : ℚ)⁻¹)^(a k))
    (hY : ∀ i k, k ∈ K i → ((Y i k).card : ℚ) ≤ (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(b i k))
    (hcover : ∀ (x : H) (y : ∀ i, A i),
      (∃ k ∈ Pure, x ∈ X k) ∨ ∃ i, ∃ k ∈ K i, x ∈ X k ∧ y i ∈ Y i k) :
    (1 : ℚ) ≤ 1 / (q - 1 : ℚ) + ∑ i, hubTail q (p i) := by
  classical
  let D := fun i => saturatedHubSet (K i) X (Y i)
  have hD (i : ι) : ((D i).card : ℚ) ≤ (Fintype.card H : ℚ) * hubTail q (p i) :=
    star_leaf_saturation_bound q (p i) hq (hp i) (K i) a (b i) (hab i) (hb i) X (Y i)
      (fun k _ => hX k) (hY i)
  have hPure : ((Pure.biUnion X).card : ℚ) ≤ (Fintype.card H : ℚ) * (1 / (q - 1)) := by
    have hgeom := positive_geometric_sum_le q hq (Pure.image a) (by
      intro n hn
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
      exact hapos k hk)
    rw [Finset.sum_image hap] at hgeom
    calc
      _ ≤ ∑ k ∈ Pure, ((X k).card : ℚ) := by exact_mod_cast Finset.card_biUnion_le (s := Pure) (t := X)
      _ ≤ ∑ k ∈ Pure, (Fintype.card H : ℚ) * ((q : ℚ)⁻¹)^(a k) := Finset.sum_le_sum (fun k _ => hX k)
      _ = (Fintype.card H : ℚ) * ∑ k ∈ Pure, ((q : ℚ)⁻¹)^(a k) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hgeom (by positivity)
  have hU : (Finset.univ : Finset H) ⊆ Pure.biUnion X ∪ Finset.univ.biUnion D := by
    intro x _
    rcases star_cover_saturation A Pure K X Y hcover x with hx | ⟨i, hi⟩
    · exact Finset.mem_union_left _ hx
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩)
  have hc : Fintype.card H ≤ (Pure.biUnion X).card + ∑ i, (D i).card := by
    calc
      _ ≤ (Pure.biUnion X ∪ Finset.univ.biUnion D).card := by simpa using Finset.card_le_card hU
      _ ≤ (Pure.biUnion X).card + (Finset.univ.biUnion D).card := Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add_left (Finset.card_biUnion_le (s := Finset.univ) (t := D)) _
  have hcQ : (Fintype.card H : ℚ) ≤ ((Pure.biUnion X).card : ℚ) + ∑ i, ((D i).card : ℚ) := by
    exact_mod_cast hc
  have hsum : (∑ i, ((D i).card : ℚ)) ≤ (Fintype.card H : ℚ) * ∑ i, hubTail q (p i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hD i)
  have hpos : (0 : ℚ) < Fintype.card H := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card H)
  nlinarith

/-- No odd star-shaped box system of distinct exponent shapes can cover. -/
theorem not_odd_star_box_cover {H ι κ : Type*} [Fintype ι]
    [Fintype H] [Nonempty H] [DecidableEq H] [DecidableEq κ]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (q : ℕ) (hq : 2 < q) (hoq : Odd q) (p : ι → ℕ)
    (hp : ∀ i, 2 < p i ∧ Odd (p i)) (hpi : Function.Injective p) (hpq : ∀ i, p i ≠ q)
    (Pure : Finset κ) (K : ι → Finset κ) (a : κ → ℕ) (b : ι → κ → ℕ)
    (hap : Set.InjOn a Pure) (hapos : ∀ k ∈ Pure, 0 < a k)
    (hab : ∀ i, Set.InjOn (fun k => (a k, b i k)) (K i)) (hb : ∀ i k, k ∈ K i → 0 < b i k)
    (X : κ → Finset H) (Y : ∀ i, κ → Finset (A i))
    (hX : ∀ k, ((X k).card : ℚ) ≤ (Fintype.card H : ℚ) * ((q : ℚ)⁻¹)^(a k))
    (hY : ∀ i k, k ∈ K i → ((Y i k).card : ℚ) ≤ (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(b i k)) :
    ¬ (∀ (x : H) (y : ∀ i, A i),
      (∃ k ∈ Pure, x ∈ X k) ∨ ∃ i, ∃ k ∈ K i, x ∈ X k ∧ y i ∈ Y i k) := by
  intro hcover
  have hbnd := star_box_cover_budget A q (by omega) p (fun i => (hp i).1)
    Pure K a b hap hapos hab hb X Y hX hY hcover
  classical
  let P := Finset.univ.image p
  have hP : ∀ r ∈ P, 2 < r ∧ Odd r := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact hp i
  have hqP : q ∉ P := by
    intro hh
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hh
    exact hpq i hi
  have hsmall := star_budget_le_nine_sixteenths q hq hoq P hP hqP
  rw [Finset.sum_image hpi.injOn] at hsmall
  linarith

#print axioms not_odd_star_box_cover
#print axioms star_budget_le_nine_sixteenths
#print axioms star_leaf_saturation_bound
#print axioms paired_weight_bound
#print axioms saturatedHubSet_weight_bound
#print axioms geometric_tail_le
end Erdos7StarSieve


/-! Arithmetic consequences of the star saturation obstruction. -/
namespace Erdos7StarSieve
open Erdos7Reduction
set_option maxHeartbeats 2000000

/-- Uniform fibres of a surjective homomorphism of finite additive groups. -/
theorem surjective_fiber_card_rat {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] [DecidableEq H] (f : G →+ H)
    (hf : Function.Surjective f) (b : H) :
    ((Finset.univ.filter (fun x => f x = b)).card : ℚ) =
      (Fintype.card G : ℚ) / Fintype.card H := by
  classical
  have heq (y : H) : (Finset.univ.filter (fun x => f x = y)).card =
      (Finset.univ.filter (fun x => f x = b)).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf b)
  have hcard : Fintype.card G =
      Fintype.card H * (Finset.univ.filter (fun x => f x = b)).card := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset G))
      (t := (Finset.univ : Finset H)) (f := f) (fun _ _ => Finset.mem_univ _)
    simpa only [heq, Finset.card_univ, Finset.sum_const, nsmul_eq_mul] using h
  have hc : (Fintype.card H : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card H))
  apply (eq_div_iff hc).mpr
  exact_mod_cast (Nat.mul_comm _ _).trans hcard.symm

/-- Odd coprime-coordinate congruence boxes cannot cover if their supports form a star. -/
theorem not_star_coordinate_cover {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p E : Option ι → ℕ) (hp : ∀ i, 2 < p i ∧ Odd (p i))
    (hpi : Function.Injective p) (hcop : Pairwise (Function.onFun Nat.Coprime p))
    (e : κ → Option ι → ℕ) (he : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (heE : ∀ k i, e k i ≤ E i)
    (hstar : ∀ k, (Finset.univ.filter (fun i : ι => e k (some i) ≠ 0)).card ≤ 1)
    (a : κ → ℤ) :
    ¬ (∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k) := by
  classical
  intro hcover
  letI (i : Option ι) : NeZero (p i) := ⟨by have := (hp i).1; omega⟩
  let A (i : Option ι) := ZMod (p i ^ E i)
  let f (k : κ) (i : Option ι) := ZMod.castHom (pow_dvd_pow (p i) (heE k i)) (ZMod (p i ^ e k i))
  let B (k : κ) (i : Option ι) := Finset.univ.filter (fun x : A i => f k i x = (a k : ZMod (p i ^ e k i)))
  have hBcard (k : κ) (i : Option ι) : ((B k i).card : ℚ) ≤
      (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(e k i) := by
    have hh := surjective_fiber_card_rat (f k i).toAddMonoidHom
      (ZMod.castHom_surjective (pow_dvd_pow (p i) (heE k i))) (a k)
    change ((B k i).card : ℚ) = _ at hh
    rw [hh]
    simp only [A, ZMod.card, Nat.cast_pow, div_eq_mul_inv, inv_pow]
    exact le_rfl
  have hbox : ∀ x : ∀ i, A i, ∃ k, ∀ i, x i ∈ B k i := by
    intro x
    let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) (fun i => p i ^ E i) Finset.univ
      (fun i _ => pow_ne_zero _ (NeZero.ne _))
      (fun i _ j _ hij => (hcop hij).pow _ _)
    have hz (i : Option ι) : (z.val : A i) = x i := by
      rw [← ZMod.natCast_zmod_val (x i)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
    obtain ⟨k, hk⟩ := hcover (z.val : ℤ)
    refine ⟨k, ?_⟩
    intro i
    have hpi : p i ^ e k i ∣ ∏ j, p j ^ e k j :=
      Finset.dvd_prod_of_mem (fun j => p j ^ e k j) (Finset.mem_univ i)
    have hpi' : ((p i ^ e k i : ℕ) : ℤ) ∣ ((∏ j, p j ^ e k j : ℕ) : ℤ) := by exact_mod_cast hpi
    have hqi := hpi'.trans hk
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hz i, map_natCast]
    symm
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (a k) (z.val : ℤ) (p i ^ e k i)).mpr hqi
  let Pure := Finset.univ.filter (fun k => ∀ i : ι, e k (some i) = 0)
  let K (i : ι) := Finset.univ.filter (fun k => e k (some i) ≠ 0 ∧ ∀ j, j ≠ i → e k (some j) = 0)
  have hPure (k : κ) (hk : k ∈ Pure) (i : ι) : e k (some i) = 0 := (Finset.mem_filter.mp hk).2 i
  have hK (i : ι) (k : κ) (hk : k ∈ K i) : e k (some i) ≠ 0 ∧ ∀ j, j ≠ i → e k (some j) = 0 :=
    (Finset.mem_filter.mp hk).2
  have hap : Set.InjOn (fun k => e k none) Pure := by
    intro k hk l hl hkl
    apply he
    funext i
    cases i with
    | none => exact hkl
    | some i => rw [hPure k hk i, hPure l hl i]
  have hapos : ∀ k ∈ Pure, 0 < e k none := by
    intro k hk
    obtain ⟨i, hi⟩ := he0 k
    cases i with
    | none => omega
    | some i => exact False.elim (hi (hPure k hk i))
  have hab (i : ι) : Set.InjOn (fun k => (e k none, e k (some i))) (K i) := by
    intro k hk l hl hkl
    apply he
    funext j
    cases j with
    | none => exact congrArg Prod.fst hkl
    | some j =>
      by_cases hji : j = i
      · subst j
        exact congrArg Prod.snd hkl
      · rw [(hK i k hk).2 j hji, (hK i l hl).2 j hji]
  have hclass (k : κ) : k ∈ Pure ∨ ∃ i, k ∈ K i := by
    by_cases h : ∀ i : ι, e k (some i) = 0
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    · push_neg at h
      obtain ⟨i, hi⟩ := h
      refine Or.inr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, ?_⟩⟩
      intro j hji
      by_contra hj
      have heq := Finset.card_le_one.mp (hstar k) j
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩) i
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      exact hji heq
  apply not_odd_star_box_cover (fun i : ι => A (some i)) (p none) (hp none).1 (hp none).2
    (fun i : ι => p (some i)) (fun i => hp (some i))
    (fun _ _ hh => Option.some.inj (hpi hh)) (by intro i hh; have h := hpi hh; cases h)
    Pure K (fun k => e k none) (fun i k => e k (some i)) hap hapos hab
    (fun i k hk => Nat.pos_of_ne_zero (hK i k hk).1)
    (fun k => B k none) (fun i k => B k (some i)) (fun k => hBcard k none)
    (fun i k _ => hBcard k (some i))
  intro x y
  let v : ∀ i : Option ι, A i := fun i => Option.rec x y i
  obtain ⟨k, hk⟩ := hbox v
  rcases hclass k with hpure | ⟨i, hi⟩
  · exact Or.inl ⟨k, hpure, hk none⟩
  · exact Or.inr ⟨i, k, hi, hk none, hk (some i)⟩

/-- An odd arithmetic cover cannot have all its prime supports contained in a star. -/
theorem not_arithmetic_star_cover {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a)
    (q : ℕ) (hq : q.Prime) (hoq : Odd q) :
    ¬ (∀ k, ((m k).primeFactors.erase q).card ≤ 1) := by
  classical
  intro hstar
  have hm0 (k : κ) : m k ≠ 0 := by have := (hc.2.1 k).1; omega
  have hq2 : 2 < q := by have := hq.two_le; have := Nat.odd_iff.mp hoq; omega
  let F := Finset.univ.biUnion (fun k => (m k).primeFactors)
  let P := F.erase q
  have hpP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ Odd p ∧ p ≠ q := by
    obtain ⟨hpq, hpF⟩ := Finset.mem_erase.mp hp
    obtain ⟨k, _, hpk⟩ := Finset.mem_biUnion.mp hpF
    have hh := Nat.mem_primeFactors.mp hpk
    exact ⟨hh.1, (hc.2.1 k).2.of_dvd_nat hh.2.1, hpq⟩
  let r : Option P → ℕ := fun i => Option.rec q Subtype.val i
  have hrprime (i : Option P) : (r i).Prime := by
    cases i with
    | none => exact hq
    | some i => exact (hpP i.val i.property).1
  have hr (i : Option P) : 2 < r i ∧ Odd (r i) := by
    cases i with
    | none => exact ⟨hq2, hoq⟩
    | some i =>
      have hi := hpP i.val i.property
      have h2 : 2 < i.val := by have := hi.1.two_le; have := Nat.odd_iff.mp hi.2.1; omega
      exact ⟨h2, hi.2.1⟩
  have hri : Function.Injective r := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j => exact False.elim ((hpP j.val j.property).2.2 hij.symm)
    | some i =>
      cases j with
      | none => exact False.elim ((hpP i.val i.property).2.2 hij)
      | some j => exact congrArg some (Subtype.ext hij)
  have hcop : Pairwise (Function.onFun Nat.Coprime r) := by
    intro i j hij
    exact (Nat.coprime_primes (hrprime i) (hrprime j)).mpr (fun h => hij (hri h))
  let e (k : κ) (i : Option P) := (m k).factorization (r i)
  let E (i : Option P) := Finset.univ.sup (fun k => e k i)
  have heE (k : κ) (i : Option P) : e k i ≤ E i :=
    Finset.le_sup (f := fun k => e k i) (Finset.mem_univ k)
  have hprod (k : κ) : m k = ∏ i : Option P, r i ^ e k i := by
    have hsub : (m k).primeFactors ⊆ insert q P := by
      intro p hp
      by_cases hpq : p = q
      · simp [hpq]
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr
          ⟨hpq, Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hp⟩⟩))
    have hh := Erdos7Compression.factorization_product_over_superset (m k) (hm0 k) (insert q P) hsub
    rw [Finset.prod_coe_sort (insert q P) (fun p => p ^ (m k).factorization p),
      Finset.prod_insert (by simp [P])] at hh
    rw [Fintype.prod_option]
    change m k = q ^ (m k).factorization q * ∏ i : P, i.val ^ (m k).factorization i.val
    rw [Finset.prod_coe_sort P (fun p => p ^ (m k).factorization p)]
    exact hh
  have hei : Function.Injective e := by
    intro k l hkl
    apply hc.1
    rw [hprod k, hprod l, hkl]
  have he0 (k : κ) : ∃ i, e k i ≠ 0 := by
    by_contra! h
    have hh := (hc.2.1 k).1
    rw [hprod k] at hh
    simp only [h, pow_zero, Finset.prod_const_one] at hh
    omega
  have hes : ∀ k, (Finset.univ.filter (fun i : P => e k (some i) ≠ 0)).card ≤ 1 := by
    intro k
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have hmem (v : P) (hv : e k (some v) ≠ 0) : v.val ∈ (m k).primeFactors.erase q := by
      have hd : v.val ∣ m k := by
        by_contra hd
        exact hv (Nat.factorization_eq_zero_of_not_dvd hd)
      exact Finset.mem_erase.mpr ⟨(hpP v.val v.property).2.2,
        Nat.mem_primeFactors.mpr ⟨(hpP v.val v.property).1, hd, hm0 k⟩⟩
    exact Subtype.ext (Finset.card_le_one.mp (hstar k) i.val
      (hmem i (Finset.mem_filter.mp hi).2) j.val (hmem j (Finset.mem_filter.mp hj).2))
  apply not_star_coordinate_cover r E hr hri hcop e hei he0 heE hes a
  simpa only [← hprod] using hc.2.2

/-- Away from every odd prime, some class needs at least two further prime factors. -/
theorem arithmetic_two_prime_factors_away_from_hub {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a)
    (q : ℕ) (hq : q.Prime) (hoq : Odd q) :
    ∃ k, 2 ≤ ((m k).primeFactors.erase q).card := by
  by_contra! h
  exact not_arithmetic_star_cover m a hc q hq hoq (fun k => by have := h k; omega)

/-- Ideal-valued form of the uniform prime-support star obstruction. -/
theorem two_prime_factors_away_from_hub (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i, ¬ C.moduli i ≤ Ideal.span {2})
    (q : ℕ) (hq : q.Prime) (hoq : Odd q) :
    ∃ i, 2 ≤ (((C.moduli i).absNorm.primeFactors).erase q).card := by
  letI := C.fintypeIndex
  exact arithmetic_two_prime_factors_away_from_hub (fun i => (C.moduli i).absNorm) C.residue
    ⟨moduli_absNorm_injective C, fun i => ⟨moduli_absNorm_gt_one C i,
      (ideal_not_le_two_iff _).mp (hodd i)⟩, arithmetic_cover C⟩ q hq hoq

#print axioms not_arithmetic_star_cover
#print axioms arithmetic_two_prime_factors_away_from_hub
#print axioms two_prime_factors_away_from_hub
#print axioms not_star_coordinate_cover
end Erdos7StarSieve


/-! Saturation estimates and greedy avoidance for supports of size at most two. -/
namespace Erdos7GraphSaturation
open Erdos7Reduction Erdos7StarSieve
set_option maxHeartbeats 2000000

/-- The set of hub values whose active leaf weight exceeds a threshold. -/
def heavyHubSet {H κ : Type*} [Fintype H] [DecidableEq H] [DecidableEq κ]
    (K : Finset κ) (X : κ → Finset H) (w : κ → ℚ) (t : ℚ) : Finset H :=
  Finset.univ.filter (fun x => t ≤ ∑ k ∈ K, if x ∈ X k then w k else 0)

/-- Separating low levels from high levels sharpens the first-moment bound. -/
theorem heavyHubSet_weight_bound {H κ : Type*} [Fintype H]
    [DecidableEq H] [DecidableEq κ]
    (K : Finset κ) (X : κ → Finset H)
    (Low : κ → Prop) [DecidablePred Low] (w : κ → ℚ) (hw : ∀ k, 0 ≤ w k)
    (t L R : ℚ)
    (hLow : ∑ k ∈ K with Low k, w k ≤ L)
    (hHigh : ∑ k ∈ K with ¬ Low k, ((X k).card : ℚ) * w k ≤ (Fintype.card H : ℚ) * R) :
    ((heavyHubSet K X w t).card : ℚ) * (t - L) ≤ (Fintype.card H : ℚ) * R := by
  classical
  let D := heavyHubSet K X w t
  have hpoint (x : H) (hx : x ∈ D) :
      t - L ≤ ∑ k ∈ K with ¬ Low k, if x ∈ X k then w k else 0 := by
    have hb := (Finset.mem_filter.mp hx).2
    have hsplit := Finset.sum_filter_add_sum_filter_not K Low
      (fun k => if x ∈ X k then w k else 0)
    have hlo : (∑ k ∈ K with Low k, if x ∈ X k then w k else 0) ≤ L := by
      apply le_trans _ hLow
      apply Finset.sum_le_sum
      intro k _
      split_ifs
      · exact le_rfl
      · exact hw k
    linarith
  have hsum : (D.card : ℚ) * (t - L) ≤
      ∑ x ∈ D, ∑ k ∈ K with ¬ Low k, if x ∈ X k then w k else 0 := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hpoint
  rw [Finset.sum_comm] at hsum
  have hbound : (∑ k ∈ K with ¬ Low k, ∑ x ∈ D, if x ∈ X k then w k else 0) ≤
      ∑ k ∈ K with ¬ Low k, ((X k).card : ℚ) * w k := by
    apply Finset.sum_le_sum
    intro k _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (hw k)
    exact_mod_cast Finset.card_le_card (show D.filter (fun x => x ∈ X k) ⊆ X k from
      fun x hx => (Finset.mem_filter.mp hx).2)
  exact hsum.trans (hbound.trans hHigh)

/-- Positive hub exponents save one low level for a genuinely mixed edge. -/
theorem edge_heavy_bound {H κ : Type*} [Fintype H]
    [DecidableEq H] [DecidableEq κ]
    (q p T : ℕ) (hq : 1 < q) (hp : 1 < p) (hT : 1 ≤ T)
    (K : Finset κ) (a b : κ → ℕ)
    (hinj : Set.InjOn (fun k => (a k, b k)) K)
    (ha : ∀ k ∈ K, 0 < a k) (hb : ∀ k ∈ K, 0 < b k)
    (X : κ → Finset H)
    (hX : ∀ k ∈ K, ((X k).card : ℚ) ≤ (Fintype.card H : ℚ) * ((q : ℚ)⁻¹)^(a k)) :
    ((heavyHubSet K X (fun k => ((p : ℚ)⁻¹)^(b k)) ((T : ℚ) / (p - 1))).card : ℚ) ≤
      (Fintype.card H : ℚ) * (((q : ℚ)⁻¹)^(T - 1) / (q - 1)) := by
  let B := K.image b
  let C := (K.image a).filter (fun n => T ≤ n)
  let tail : ℚ := ((q : ℚ)⁻¹)^T * ((q : ℚ) / (q - 1))
  have hpQ : (1 : ℚ) < p := by exact_mod_cast hp
  have hden : (0 : ℚ) < p - 1 := by linarith
  have hB : (∑ n ∈ B, ((p : ℚ)⁻¹)^n) ≤ 1 / (p - 1) := by
    apply positive_geometric_sum_le p hp
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
    exact hb k hk
  have hC : (∑ n ∈ C, ((q : ℚ)⁻¹)^n) ≤ tail :=
    geometric_tail_le q T hq C (fun n hn => (Finset.mem_filter.mp hn).2)
  have hlow : (∑ k ∈ K with a k < T, ((p : ℚ)⁻¹)^(b k)) ≤ (T - 1 : ℚ) / (p - 1) := by
    have hh := paired_weight_bound (K.filter (fun k => a k < T)) a b
      (hinj.mono (Finset.filter_subset _ _)) ((Finset.range T).erase 0) B
      (fun k hk => Finset.mem_erase.mpr
        ⟨by have := ha k (Finset.mem_filter.mp hk).1; omega,
          Finset.mem_range.mpr (Finset.mem_filter.mp hk).2⟩)
      (fun k hk => Finset.mem_image.mpr ⟨k, (Finset.mem_filter.mp hk).1, rfl⟩)
      (fun _ => 1) (fun n => ((p : ℚ)⁻¹)^n) (by intros; norm_num) (by intros; positivity)
    have hc : ((Finset.range T).erase 0).card = T - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range]
    simp only [one_mul, Finset.sum_const, nsmul_eq_mul, mul_one, hc] at hh
    have hcast : ((T - 1 : ℕ) : ℚ) = T - 1 := Nat.cast_sub hT
    rw [hcast] at hh
    calc
      _ ≤ (T - 1 : ℚ) * ∑ n ∈ B, ((p : ℚ)⁻¹)^n := hh
      _ ≤ (T - 1 : ℚ) * (1 / (p - 1)) := mul_le_mul_of_nonneg_left hB (by exact_mod_cast Nat.zero_le (T - 1))
      _ = _ := by ring
  have hhigh : (∑ k ∈ K with ¬ a k < T, ((X k).card : ℚ) * ((p : ℚ)⁻¹)^(b k)) ≤
      (Fintype.card H : ℚ) * (tail / (p - 1)) := by
    have hh := paired_weight_bound (K.filter (fun k => ¬ a k < T)) a b
      (hinj.mono (Finset.filter_subset _ _)) C B
      (fun k hk => Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨k, (Finset.mem_filter.mp hk).1, rfl⟩,
          by have := (Finset.mem_filter.mp hk).2; omega⟩)
      (fun k hk => Finset.mem_image.mpr ⟨k, (Finset.mem_filter.mp hk).1, rfl⟩)
      (fun n => ((q : ℚ)⁻¹)^n) (fun n => ((p : ℚ)⁻¹)^n)
      (by intros; positivity) (by intros; positivity)
    have hprod : (∑ n ∈ C, ((q : ℚ)⁻¹)^n) * (∑ n ∈ B, ((p : ℚ)⁻¹)^n) ≤ tail / (p - 1) := by
      calc
        _ ≤ tail * (1 / (p - 1)) := mul_le_mul hC hB (by positivity) (by
          have hqQ : (1 : ℚ) < q := by exact_mod_cast hq
          have hqden : (0 : ℚ) < q - 1 := by linarith
          dsimp [tail]
          positivity)
        _ = _ := by ring
    calc
      _ ≤ ∑ k ∈ K with ¬ a k < T,
          (Fintype.card H : ℚ) * (((q : ℚ)⁻¹)^(a k) * ((p : ℚ)⁻¹)^(b k)) := by
        apply Finset.sum_le_sum
        intro k hk
        have h := mul_le_mul_of_nonneg_right (hX k (Finset.mem_filter.mp hk).1)
          (show 0 ≤ ((p : ℚ)⁻¹)^(b k) by positivity)
        simpa only [mul_assoc] using h
      _ = (Fintype.card H : ℚ) * ∑ k ∈ K with ¬ a k < T,
          ((q : ℚ)⁻¹)^(a k) * ((p : ℚ)⁻¹)^(b k) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hh.trans hprod) (by positivity)
  have hs := heavyHubSet_weight_bound K X (fun k => a k < T)
    (fun k => ((p : ℚ)⁻¹)^(b k)) (by intros; positivity)
    ((T : ℚ) / (p - 1)) ((T - 1 : ℚ) / (p - 1)) (tail / (p - 1)) hlow hhigh
  have hL : (T : ℚ) / (p - 1) - (T - 1 : ℚ) / (p - 1) = 1 / (p - 1) := by ring
  rw [hL, mul_one_div, ← mul_div_assoc] at hs
  have htail : tail = ((q : ℚ)⁻¹)^(T - 1) / (q - 1) := by
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    dsimp [tail]
    nth_rw 1 [show T = (T - 1) + 1 by omega]
    rw [pow_succ]
    calc
      _ = (((q : ℚ)⁻¹)^(T - 1) * ((q : ℚ)⁻¹ * q)) / (q - 1) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hq0, mul_one]
  rw [htail] at hs
  exact (div_le_div_iff_of_pos_right hden).mp hs

/-- Sequential choice on a finite ordered list of coordinate spaces. -/
theorem greedy_choice {n : ℕ} (A : Fin n → Type*) [∀ i, Nonempty (A i)]
    (Good : ∀ i, A i → Prop) (R : ∀ i j, A i → A j → Prop)
    (hstep : ∀ i (x : ∀ j, A j), (∀ j, j < i → Good j (x j)) →
      ∃ v : A i, Good i v ∧ ∀ j, j < i → R j i (x j) v) :
    ∃ x : ∀ i, A i, ∀ i, Good i (x i) ∧ ∀ j, j < i → R j i (x j) (x i) := by
  classical
  have aux (t : ℕ) (ht : t ≤ n) :
      ∃ x : ∀ i, A i, ∀ i, i.val < t → Good i (x i) ∧ ∀ j, j < i → R j i (x j) (x i) := by
    induction t with
    | zero =>
      exact ⟨Classical.choice (inferInstance : Nonempty (∀ i, A i)), fun i hi => by omega⟩
    | succ t ih =>
      obtain ⟨x, hx⟩ := ih (by omega)
      let i : Fin n := ⟨t, by omega⟩
      obtain ⟨v, hv, hrel⟩ := hstep i x (fun j hj => (hx j hj).1)
      refine ⟨Function.update x i v, ?_⟩
      intro j hj
      by_cases hji : j = i
      · subst j
        constructor
        · simpa only [Function.update_self] using hv
        · intro k hki
          have hkne : k ≠ i := ne_of_lt hki
          simpa only [Function.update_self, Function.update_of_ne hkne] using hrel k hki
      · have hjt : j.val < t := by
          have hne : j.val ≠ t := by intro he; exact hji (Fin.ext he)
          omega
        obtain ⟨hgj, hrj⟩ := hx j hjt
        constructor
        · simpa only [Function.update_of_ne hji] using hgj
        · intro k hkj
          have hkne : k ≠ i := by
            intro he
            have hh : k.val < j.val := hkj
            simp only [he] at hh
            change t < j.val at hh
            omega
          simpa only [Function.update_of_ne hji, Function.update_of_ne hkne] using hrj k hkj
  obtain ⟨x, hx⟩ := aux n le_rfl
  exact ⟨x, fun i => hx i i.isLt⟩

/-- A local density budget guarantees a global choice avoiding all oriented edges. -/
theorem greedy_edge_avoidance {n : ℕ} (A : Fin n → Type*)
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (D : ∀ i, Finset (A i)) (B : ∀ i j, A i → Finset (A j))
    (d : Fin n → ℚ) (r : Fin n → Fin n → ℚ)
    (hD : ∀ i, ((D i).card : ℚ) ≤ (Fintype.card (A i) : ℚ) * d i)
    (hB : ∀ i j, i < j → ∀ x, x ∉ D i →
      ((B i j x).card : ℚ) ≤ (Fintype.card (A j) : ℚ) * r i j)
    (hbudget : ∀ i, d i + ∑ j ∈ Finset.univ.filter (fun j => j < i), r j i < 1) :
    ∃ x : ∀ i, A i, (∀ i, x i ∉ D i) ∧ ∀ i j, i < j → x j ∉ B i j (x i) := by
  classical
  have hstep (i : Fin n) (x : ∀ j, A j) (hx : ∀ j, j < i → x j ∉ D j) :
      ∃ v : A i, v ∉ D i ∧ ∀ j, j < i → v ∉ B j i (x j) := by
    let S := Finset.univ.filter (fun j => j < i)
    let U := D i ∪ S.biUnion (fun j => B j i (x j))
    have hc : U.card ≤ (D i).card + ∑ j ∈ S, (B j i (x j)).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_biUnion_le (s := S)) _)
    have hcQ : (U.card : ℚ) ≤ ((D i).card : ℚ) + ∑ j ∈ S, ((B j i (x j)).card : ℚ) := by
      exact_mod_cast hc
    have hs : (∑ j ∈ S, ((B j i (x j)).card : ℚ)) ≤
        (Fintype.card (A i) : ℚ) * ∑ j ∈ S, r j i := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hji := (Finset.mem_filter.mp hj).2
      exact hB j i hji (x j) (hx j hji)
    have hN : (0 : ℚ) < Fintype.card (A i) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (A i))
    have hlt : (U.card : ℚ) < Fintype.card (A i) := by
      have hh := mul_lt_mul_of_pos_left (hbudget i) hN
      dsimp [S] at hs
      nlinarith [hD i]
    have hex : ∃ v : A i, v ∉ U := by
      by_contra! h
      have hsub : (Finset.univ : Finset (A i)) ⊆ U := fun v _ => h v
      have hh : Fintype.card (A i) ≤ U.card := by simpa using Finset.card_le_card hsub
      have hhQ : (Fintype.card (A i) : ℚ) ≤ U.card := by exact_mod_cast hh
      linarith
    obtain ⟨v, hv⟩ := hex
    refine ⟨v, ?_, ?_⟩
    · intro hd
      exact hv (Finset.mem_union_left _ hd)
    · intro j hji hb
      exact hv (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji⟩, hb⟩))
  obtain ⟨x, hx⟩ := greedy_choice A (fun i v => v ∉ D i) (fun i j u v => v ∉ B i j u) hstep
  exact ⟨x, fun i => (hx i).1, fun i j hij => (hx j).2 i hij⟩

#print axioms greedy_choice
#print axioms greedy_edge_avoidance
#print axioms edge_heavy_bound
end Erdos7GraphSaturation


/-! The abstract two-coordinate box obstruction from row and column budgets. -/
namespace Erdos7GraphSaturation
open Erdos7Reduction Erdos7StarSieve
set_option maxHeartbeats 3000000

/-- Row and column budgets exclude box covers with supports of size at most two. -/
theorem not_graph_box_cover {n : ℕ} {κ : Type*} [Fintype κ]
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (p : Fin n → ℕ) (hp : ∀ i, 2 < p i)
    (e : κ → Fin n → ℕ) (he : Function.Injective e)
    (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (he2 : ∀ k, (Finset.univ.filter (fun i => e k i ≠ 0)).card ≤ 2)
    (X : κ → ∀ i, Finset (A i))
    (hX : ∀ k i, ((X k i).card : ℚ) ≤ (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(e k i))
    (T : Fin n → Fin n → ℕ) (hT : ∀ i j, i < j → 1 ≤ T i j)
    (hcolumn : ∀ j, (∑ i ∈ Finset.univ.filter (fun i => i < j), T i j) ≤ p j - 3)
    (hrow : ∀ i, (∑ j ∈ Finset.univ.filter (fun j => i < j), ((p i : ℚ)⁻¹)^(T i j - 1)) < 1) :
    ¬ (∀ x : ∀ i, A i, ∃ k, ∀ i, x i ∈ X k i) := by
  classical
  let supp (k : κ) := Finset.univ.filter (fun i => e k i ≠ 0)
  let Pure (i : Fin n) := Finset.univ.filter (fun k => supp k = {i})
  let K (i j : Fin n) := Finset.univ.filter (fun k => supp k = {i,j})
  have hmem (k : κ) (i : Fin n) : i ∈ supp k ↔ e k i ≠ 0 := by simp [supp]
  have hpure (i : Fin n) (k : κ) (hk : k ∈ Pure i) : supp k = {i} := (Finset.mem_filter.mp hk).2
  have hedge (i j : Fin n) (k : κ) (hk : k ∈ K i j) : supp k = {i,j} := (Finset.mem_filter.mp hk).2
  have hpos (i j : Fin n) (k : κ) (hk : k ∈ K i j) : 0 < e k i ∧ 0 < e k j := by
    have hi : i ∈ supp k := by rw [hedge i j k hk]; simp
    have hj : j ∈ supp k := by rw [hedge i j k hk]; simp
    have := (hmem k i).mp hi
    have := (hmem k j).mp hj
    omega
  have hpair (i j : Fin n) : Set.InjOn (fun k => (e k i, e k j)) (K i j) := by
    intro k hk l hl hkl
    apply he
    funext t
    by_cases hti : t = i
    · subst t; exact congrArg Prod.fst hkl
    · by_cases htj : t = j
      · subst t; exact congrArg Prod.snd hkl
      · have hk0 : e k t = 0 := by
          by_contra h
          have hh := (hmem k t).mpr h
          rw [hedge i j k hk] at hh
          simp [hti, htj] at hh
        have hl0 : e l t = 0 := by
          by_contra h
          have hh := (hmem l t).mpr h
          rw [hedge i j l hl] at hh
          simp [hti, htj] at hh
        rw [hk0, hl0]
  let H (i j : Fin n) := heavyHubSet (K i j) (fun k => X k i)
    (fun k => ((p j : ℚ)⁻¹)^(e k j)) ((T i j : ℚ)/(p j-1))
  let D (i : Fin n) := (Pure i).biUnion (fun k => X k i) ∪
    (Finset.univ.filter (fun j => i < j)).biUnion (fun j => H i j)
  let B (i j : Fin n) (x : A i) := ((K i j).filter (fun k => x ∈ X k i)).biUnion (fun k => X k j)
  let d (i : Fin n) : ℚ := (1 + ∑ j ∈ Finset.univ.filter (fun j => i < j),
    ((p i : ℚ)⁻¹)^(T i j-1)) / (p i-1)
  let r (i j : Fin n) : ℚ := (T i j : ℚ)/(p j-1)
  have hD (i : Fin n) : ((D i).card : ℚ) ≤ (Fintype.card (A i) : ℚ) * d i := by
    have hpi : Set.InjOn (fun k => e k i) (Pure i) := by
      intro k hk l hl hkl
      apply he
      funext t
      by_cases hti : t = i
      · simpa [hti] using hkl
      · have hk0 : e k t = 0 := by
          by_contra h
          have hh := (hmem k t).mpr h
          rw [hpure i k hk] at hh
          exact hti (Finset.mem_singleton.mp hh)
        have hl0 : e l t = 0 := by
          by_contra h
          have hh := (hmem l t).mpr h
          rw [hpure i l hl] at hh
          exact hti (Finset.mem_singleton.mp hh)
        rw [hk0, hl0]
    have hpp (k : κ) (hk : k ∈ Pure i) : 0 < e k i := by
      have hh : i ∈ supp k := by rw [hpure i k hk]; simp
      have := (hmem k i).mp hh
      omega
    have hg := positive_geometric_sum_le (p i) (by have := hp i; omega)
      ((Pure i).image (fun k => e k i)) (by
        intro a ha
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
        exact hpp k hk)
    rw [Finset.sum_image hpi] at hg
    have hpc : (((Pure i).biUnion (fun k => X k i)).card : ℚ) ≤ (Fintype.card (A i) : ℚ)/(p i-1) := by
      calc
        _ ≤ ∑ k ∈ Pure i, ((X k i).card : ℚ) := by exact_mod_cast Finset.card_biUnion_le (s := Pure i) (t := fun k => X k i)
        _ ≤ ∑ k ∈ Pure i, (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(e k i) := Finset.sum_le_sum (fun k _ => hX k i)
        _ = (Fintype.card (A i) : ℚ) * ∑ k ∈ Pure i, ((p i : ℚ)⁻¹)^(e k i) := (Finset.mul_sum _ _ _).symm
        _ ≤ (Fintype.card (A i) : ℚ) * (1/(p i-1)) := mul_le_mul_of_nonneg_left hg (by positivity)
        _ = _ := by ring
    have hhc (j : Fin n) (hij : i < j) : ((H i j).card : ℚ) ≤ (Fintype.card (A i) : ℚ) *
        (((p i : ℚ)⁻¹)^(T i j-1)/(p i-1)) :=
      edge_heavy_bound (p i) (p j) (T i j) (by have := hp i; omega) (by have := hp j; omega) (hT i j hij)
        (K i j) (fun k => e k i) (fun k => e k j) (hpair i j)
        (fun k hk => (hpos i j k hk).1) (fun k hk => (hpos i j k hk).2)
        (fun k => X k i) (fun k _ => hX k i)
    have hc : ((D i).card : ℚ) ≤ (((Pure i).biUnion (fun k => X k i)).card : ℚ) +
        ∑ j ∈ Finset.univ.filter (fun j => i < j), ((H i j).card : ℚ) := by
      exact_mod_cast (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_biUnion_le (s := Finset.univ.filter (fun j => i < j))) _)
    apply hc.trans
    calc
      _ ≤ (Fintype.card (A i) : ℚ)/(p i-1) + ∑ j ∈ Finset.univ.filter (fun j => i < j),
          (Fintype.card (A i) : ℚ) * (((p i : ℚ)⁻¹)^(T i j-1)/(p i-1)) :=
        add_le_add hpc (Finset.sum_le_sum (fun j hj => hhc j (Finset.mem_filter.mp hj).2))
      _ = _ := by dsimp [d]; rw [← Finset.mul_sum, ← Finset.sum_div]; ring
  have hB (i j : Fin n) (hij : i < j) (x : A i) (hx : x ∉ D i) :
      ((B i j x).card : ℚ) ≤ (Fintype.card (A j) : ℚ) * r i j := by
    have hnot : x ∉ H i j := by
      intro h
      exact hx (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, h⟩))
    have hs : (∑ k ∈ K i j, if x ∈ X k i then ((p j : ℚ)⁻¹)^(e k j) else 0) < r i j := by
      simpa only [H, heavyHubSet, Finset.mem_filter, Finset.mem_univ, true_and, not_le, r] using hnot
    calc
      _ ≤ ∑ k ∈ (K i j).filter (fun k => x ∈ X k i), ((X k j).card : ℚ) := by exact_mod_cast Finset.card_biUnion_le (s := (K i j).filter (fun k => x ∈ X k i)) (t := fun k => X k j)
      _ ≤ ∑ k ∈ (K i j).filter (fun k => x ∈ X k i), (Fintype.card (A j) : ℚ) * ((p j : ℚ)⁻¹)^(e k j) := Finset.sum_le_sum (fun k _ => hX k j)
      _ = (Fintype.card (A j) : ℚ) * ∑ k ∈ K i j, if x ∈ X k i then ((p j : ℚ)⁻¹)^(e k j) else 0 := by rw [← Finset.mul_sum, Finset.sum_filter]
      _ ≤ _ := mul_le_mul_of_nonneg_left hs.le (by positivity)
  have hbudget (i : Fin n) : d i + ∑ j ∈ Finset.univ.filter (fun j => j < i), r j i < 1 := by
    have hpQ : (2 : ℚ) < p i := by exact_mod_cast hp i
    have hc : (∑ j ∈ Finset.univ.filter (fun j => j < i), (T j i : ℚ)) ≤ (p i : ℚ)-3 := by
      have h := hcolumn i
      have hcast : ((p i - 3 : ℕ) : ℚ) = (p i : ℚ)-3 := Nat.cast_sub (by have := hp i; omega)
      have hh : (∑ j ∈ Finset.univ.filter (fun j => j < i), (T j i : ℚ)) ≤ ((p i - 3 : ℕ) : ℚ) := by exact_mod_cast h
      rwa [hcast] at hh
    dsimp [d, r]
    rw [← Finset.sum_div, ← add_div]
    apply (div_lt_one (by linarith)).mpr
    have hh := hrow i
    linarith
  obtain ⟨x, hxD, hxB⟩ := greedy_edge_avoidance A D B d r hD hB hbudget
  intro hcover
  obtain ⟨k, hk⟩ := hcover x
  have hspos : 0 < (supp k).card := by
    obtain ⟨i, hi⟩ := he0 k
    exact Finset.card_pos.mpr ⟨i, (hmem k i).mpr hi⟩
  have hscard : (supp k).card = 1 ∨ (supp k).card = 2 := by have := he2 k; dsimp [supp] at *; omega
  rcases hscard with h1 | h2
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1
    exact hxD i (Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hk i⟩))
  · obtain ⟨i, j, hij, hs⟩ := Finset.card_eq_two.mp h2
    have hKi : k ∈ K i j := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact hxB i j hij (Finset.mem_biUnion.mpr ⟨k,
        Finset.mem_filter.mpr ⟨hKi, hk i⟩, hk j⟩)
    · have hKj : k ∈ K j i := by simpa [K, Finset.pair_comm] using hKi
      exact hxB j i hji (Finset.mem_biUnion.mpr ⟨k,
        Finset.mem_filter.mpr ⟨hKj, hk j⟩, hk i⟩)

#print axioms not_graph_box_cover
end Erdos7GraphSaturation


/-! Uniform prime budgets for the two-coordinate saturation sieve. -/
namespace Erdos7GraphBudget
set_option maxHeartbeats 2000000

def oddPrimesBelow (p : ℕ) : Finset ℕ := p.primesBelow.erase 2

def genericLevel (q p : ℕ) : ℕ := Nat.clog q (p^2)

/-- An elementary fourth-power comparison, with an explicit starting point. -/
theorem fourth_power_le_three_pow (n : ℕ) (hn : 16 ≤ n) :
    (4*n + 4)^4 ≤ 3^n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hg : (4*(n+1)+4)^4 ≤ 3*(4*n+4)^4 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      have heq : (4*(16+k+1)+4)^4 +
          (512*k^4 + 33792*k^3 + 834048*k^2 + 9120768*k + 37270272) =
          3*(4*(16+k)+4)^4 := by ring
      omega
    calc
      _ ≤ 3*(4*n+4)^4 := hg
      _ ≤ 3*3^n := Nat.mul_le_mul_left 3 ih
      _ = 3^(n+1) := by rw [pow_succ]; ring

/-- A deliberately loose but elementary logarithmic bound. -/
theorem square_le_three_pow_sqrt_quarter (p : ℕ) (hp : 4096 ≤ p) :
    p^2 ≤ 3^(Nat.sqrt p / 4) := by
  let s := Nat.sqrt p
  have hs : 64 ≤ s := (Nat.le_sqrt).mpr (by norm_num; exact hp)
  have hl : 16 ≤ s/4 := by omega
  have hroot : p < (s+1)^2 := by simpa [s, pow_two, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt p
  have hdiv : s+1 ≤ 4*(s/4)+4 := by omega
  have hp' : p ≤ (4*(s/4)+4)^2 := by
    have hh := Nat.pow_le_pow_left hdiv 2
    omega
  have hh := Nat.pow_le_pow_left hp' 2
  have hf := fourth_power_le_three_pow (s/4) hl
  rw [← pow_mul] at hh
  exact hh.trans hf

/-- The elementary wheel bound already supplied by Mathlib suffices here. -/
theorem oddPrimesBelow_card_bound (p : ℕ) (hp : 31 ≤ p) :
    30 * (oddPrimesBelow p).card ≤ 8*p + 540 := by
  have hh := Nat.primeCounting'_add_le (a := 30) (k := 31) (by norm_num) (by norm_num) (p-31)
  have h31 : Nat.primeCounting' 31 = 10 := by decide +kernel
  have htot : Nat.totient 30 = 8 := by decide +kernel
  rw [h31, htot, Nat.add_sub_of_le hp] at hh
  have hc : (oddPrimesBelow p).card ≤ Nat.primeCounting' p := by
    rw [← Nat.primesBelow_card_eq_primeCounting']
    exact Finset.card_le_card (Finset.erase_subset _ _)
  have hdiv : (p-31)/30 ≤ p/30 := Nat.div_le_div_right (by omega)
  have hd := Nat.div_mul_le_self p 30
  omega

theorem mem_oddPrimesBelow {p q : ℕ} (hq : q ∈ oddPrimesBelow p) :
    q.Prime ∧ Odd q ∧ q < p := by
  obtain ⟨hq2, hqp⟩ := Finset.mem_erase.mp hq
  have hh := Nat.mem_primesBelow.mp hqp
  exact ⟨hh.2, hh.2.odd_of_ne_two hq2, hh.1⟩

/-- Counting odd elements via their half-indices. -/
theorem odd_card_le (S : Finset ℕ) (N : ℕ) (ho : ∀ q ∈ S, Odd q)
    (hN : ∀ q ∈ S, q / 2 < N) : S.card ≤ N := by
  have hinj : Set.InjOn (fun q : ℕ => q / 2) S := by
    intro q hq r hr hqr
    have hqo := Nat.odd_iff.mp (ho q hq)
    have hro := Nat.odd_iff.mp (ho r hr)
    dsimp only at hqr
    omega
  have hsub : S.image (fun q => q / 2) ⊆ Finset.range N := by
    intro a ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_range.mpr (hN q hq)
  have hh := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injOn hinj, Finset.card_range] at hh

/-- The generic incoming exponent budget is sufficient for all large primes. -/
theorem large_column_bound (p : ℕ) (hp : 4096 ≤ p) :
    (∑ q ∈ oddPrimesBelow p, genericLevel q p) ≤ p - 3 := by
  let P := oddPrimesBelow p
  let C := P.filter (fun q => q^3 < p^2)
  let D := P.filter (fun q => q^4 < p^2)
  let s := Nat.sqrt p
  let L := s/4
  have hs : 64 ≤ s := (Nat.le_sqrt).mpr (by norm_num; exact hp)
  have hsq : s^2 ≤ p := by simpa [s, pow_two] using Nat.sqrt_le p
  have hL : 4*L ≤ s := by dsimp [L]; omega
  have h64s : 64*s ≤ p := by nlinarith
  have hpow : p^2 ≤ 3^L := square_le_three_pow_sqrt_quarter p hp
  have hcap (q : ℕ) (hq : q ∈ P) : genericLevel q p ≤ L := by
    have hh := mem_oddPrimesBelow hq
    have hq3 : 3 ≤ q := by have := hh.1.two_le; have := Nat.odd_iff.mp hh.2.1; omega
    apply Nat.clog_le_of_le_pow
    exact hpow.trans (Nat.pow_le_pow_left hq3 L)
  have hcount : (∑ q ∈ P, genericLevel q p) ≤ 3*P.card + C.card + L*D.card := by
    have hpoint (q : ℕ) (hq : q ∈ P) : genericLevel q p ≤
        3 + (if q^3 < p^2 then 1 else 0) + (if q^4 < p^2 then L else 0) := by
      by_cases h3 : q^3 < p^2
      · by_cases h4 : q^4 < p^2
        · have := hcap q hq
          simp only [if_pos h3, if_pos h4]
          omega
        · have hh : genericLevel q p ≤ 4 := Nat.clog_le_of_le_pow (by omega)
          simp only [if_pos h3, if_neg h4]
          omega
      · have hh : genericLevel q p ≤ 3 := Nat.clog_le_of_le_pow (by omega)
        split_ifs <;> omega
    have hh := Finset.sum_le_sum hpoint
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hh
    rw [← Finset.sum_filter, ← Finset.sum_filter] at hh
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm, mul_one, one_mul, C, D] using hh
  have hP : 30*P.card ≤ 8*p + 540 := oddPrimesBelow_card_bound p (by omega)
  have hC : 32*C.card ≤ p+32 := by
    have hh : C.card ≤ p/32+1 := odd_card_le C (p/32+1)
      (fun q hq => (mem_oddPrimesBelow (Finset.mem_filter.mp hq).1).2.1) (by
        intro q hq
        have hq3 := (Finset.mem_filter.mp hq).2
        have h16 : 16*q < p := by
          by_contra h
          have hle : p ≤ 16*q := by omega
          have hh := Nat.pow_le_pow_left hle 3
          have hmul := Nat.mul_le_mul_right (p^2) hp
          nlinarith
        omega)
    omega
  have hD : 2*D.card ≤ s+2 := by
    have hh : D.card ≤ s/2+1 := odd_card_le D (s/2+1)
      (fun q hq => (mem_oddPrimesBelow (Finset.mem_filter.mp hq).1).2.1) (by
        intro q hq
        have hq4 := (Finset.mem_filter.mp hq).2
        have hq2 : q^2 < p := by
          by_contra h
          have hh := Nat.pow_le_pow_left (show p ≤ q^2 by omega) 2
          rw [← pow_mul] at hh
          change p^2 ≤ q^4 at hh
          omega
        have hqs : q ≤ s := Nat.le_sqrt.mpr (by simpa [pow_two] using hq2.le)
        omega)
    omega
  have hprod := Nat.mul_le_mul hD hL
  change (∑ q ∈ P, genericLevel q p) ≤ p - 3
  have htotal : (∑ q ∈ P, genericLevel q p) + 3 ≤ p := by nlinarith
  omega

#print axioms large_column_bound
end Erdos7GraphBudget


/-! Kernel-checked finite certificates for the incoming prime budgets. -/
namespace Erdos7GraphBudget
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

@[irreducible] def columnSum (p : ℕ) : ℕ := ∑ q ∈ oddPrimesBelow p, genericLevel q p

theorem columnSum_mono : Monotone columnSum := by
  intro p r hpr
  unfold columnSum
  have hsub : oddPrimesBelow p ⊆ oddPrimesBelow r := by
    intro q hq
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hq
    have hh := Nat.mem_primesBelow.mp hmem
    exact Finset.mem_erase.mpr ⟨hne, Nat.mem_primesBelow.mpr ⟨hh.1.trans_le hpr, hh.2⟩⟩
  calc
    (∑ q ∈ oddPrimesBelow p, genericLevel q p) ≤ ∑ q ∈ oddPrimesBelow p, genericLevel q r :=
      Finset.sum_le_sum (fun q _ => Nat.clog_mono_right q (Nat.pow_le_pow_left hpr 2))
    _ ≤ (∑ q ∈ oddPrimesBelow r, genericLevel q r) := Finset.sum_le_sum_of_subset hsub

def fastPrimesBelow (p : ℕ) : Finset ℕ :=
  (@Finset.filter ℕ Nat.Prime Nat.decidablePrime' (Finset.range p)).erase 2

theorem fastPrimesBelow_eq (p : ℕ) : fastPrimesBelow p = oddPrimesBelow p := by
  ext q
  simp [fastPrimesBelow, oddPrimesBelow, Nat.primesBelow]

def computedLevel (q p : ℕ) : ℕ :=
  (List.range 32).findIdx (fun k => decide (p^2 ≤ q^k))

theorem columnSum_le_computed (p : ℕ)
    (h : ∀ q ∈ oddPrimesBelow p, p^2 ≤ q^(computedLevel q p)) :
    columnSum p ≤ ∑ q ∈ oddPrimesBelow p, computedLevel q p := by
  unfold columnSum
  exact Finset.sum_le_sum (fun q hq => Nat.clog_le_of_le_pow (h q hq))

def columnIntervals : Fin 19 → ℕ × ℕ := ![(67, 67), (69, 70), (71, 71), (73, 73), (76, 79), (80, 82), (83, 83), (84, 89), (90, 101), (102, 110), (111, 129), (130, 157), (158, 199), (200, 277), (278, 421), (422, 709), (710, 1361), (1362, 2957), (2958, 4095)]

theorem columnIntervals_cover (p : ℕ) (hp : p.Prime) (hlo : 67 ≤ p) (hhi : p < 4096) :
    ∃ j : Fin 19, (columnIntervals j).1 ≤ p ∧ p ≤ (columnIntervals j).2 := by
  have hn68 : p ≠ 68 := by intro h; subst p; norm_num at hp
  have hn72 : p ≠ 72 := by intro h; subst p; norm_num at hp
  have hn74 : p ≠ 74 := by intro h; subst p; norm_num at hp
  have hn75 : p ≠ 75 := by intro h; subst p; norm_num at hp
  by_cases h0 : p ≤ 67
  · refine ⟨0, ?_⟩
    change 67 ≤ p ∧ p ≤ 67
    omega
  ·
    by_cases h1 : p ≤ 70
    · refine ⟨1, ?_⟩
      change 69 ≤ p ∧ p ≤ 70
      omega
    ·
      by_cases h2 : p ≤ 71
      · refine ⟨2, ?_⟩
        change 71 ≤ p ∧ p ≤ 71
        omega
      ·
        by_cases h3 : p ≤ 73
        · refine ⟨3, ?_⟩
          change 73 ≤ p ∧ p ≤ 73
          omega
        ·
          by_cases h4 : p ≤ 79
          · refine ⟨4, ?_⟩
            change 76 ≤ p ∧ p ≤ 79
            omega
          ·
            by_cases h5 : p ≤ 82
            · refine ⟨5, ?_⟩
              change 80 ≤ p ∧ p ≤ 82
              omega
            ·
              by_cases h6 : p ≤ 83
              · refine ⟨6, ?_⟩
                change 83 ≤ p ∧ p ≤ 83
                omega
              ·
                by_cases h7 : p ≤ 89
                · refine ⟨7, ?_⟩
                  change 84 ≤ p ∧ p ≤ 89
                  omega
                ·
                  by_cases h8 : p ≤ 101
                  · refine ⟨8, ?_⟩
                    change 90 ≤ p ∧ p ≤ 101
                    omega
                  ·
                    by_cases h9 : p ≤ 110
                    · refine ⟨9, ?_⟩
                      change 102 ≤ p ∧ p ≤ 110
                      omega
                    ·
                      by_cases h10 : p ≤ 129
                      · refine ⟨10, ?_⟩
                        change 111 ≤ p ∧ p ≤ 129
                        omega
                      ·
                        by_cases h11 : p ≤ 157
                        · refine ⟨11, ?_⟩
                          change 130 ≤ p ∧ p ≤ 157
                          omega
                        ·
                          by_cases h12 : p ≤ 199
                          · refine ⟨12, ?_⟩
                            change 158 ≤ p ∧ p ≤ 199
                            omega
                          ·
                            by_cases h13 : p ≤ 277
                            · refine ⟨13, ?_⟩
                              change 200 ≤ p ∧ p ≤ 277
                              omega
                            ·
                              by_cases h14 : p ≤ 421
                              · refine ⟨14, ?_⟩
                                change 278 ≤ p ∧ p ≤ 421
                                omega
                              ·
                                by_cases h15 : p ≤ 709
                                · refine ⟨15, ?_⟩
                                  change 422 ≤ p ∧ p ≤ 709
                                  omega
                                ·
                                  by_cases h16 : p ≤ 1361
                                  · refine ⟨16, ?_⟩
                                    change 710 ≤ p ∧ p ≤ 1361
                                    omega
                                  ·
                                    by_cases h17 : p ≤ 2957
                                    · refine ⟨17, ?_⟩
                                      change 1362 ≤ p ∧ p ≤ 2957
                                      omega
                                    ·
                                      refine ⟨18, ?_⟩
                                      change 2958 ≤ p ∧ p ≤ 4095
                                      omega

theorem column_computed_0 : (∀ q ∈ oddPrimesBelow 67, 67^2 ≤ q^(computedLevel q 67)) ∧
    (∑ q ∈ oddPrimesBelow 67, computedLevel q 67) ≤ 64 := by
  simp only [← fastPrimesBelow_eq 67]
  decide +kernel
theorem column_cert_0 : columnSum 67 ≤ 64 :=
  (columnSum_le_computed 67 column_computed_0.1).trans column_computed_0.2
#print axioms column_cert_0

theorem column_computed_1 : (∀ q ∈ oddPrimesBelow 70, 70^2 ≤ q^(computedLevel q 70)) ∧
    (∑ q ∈ oddPrimesBelow 70, computedLevel q 70) ≤ 66 := by
  simp only [← fastPrimesBelow_eq 70]
  decide +kernel
theorem column_cert_1 : columnSum 70 ≤ 66 :=
  (columnSum_le_computed 70 column_computed_1.1).trans column_computed_1.2
#print axioms column_cert_1

theorem column_computed_2 : (∀ q ∈ oddPrimesBelow 71, 71^2 ≤ q^(computedLevel q 71)) ∧
    (∑ q ∈ oddPrimesBelow 71, computedLevel q 71) ≤ 68 := by
  simp only [← fastPrimesBelow_eq 71]
  decide +kernel
theorem column_cert_2 : columnSum 71 ≤ 68 :=
  (columnSum_le_computed 71 column_computed_2.1).trans column_computed_2.2
#print axioms column_cert_2

theorem column_computed_3 : (∀ q ∈ oddPrimesBelow 73, 73^2 ≤ q^(computedLevel q 73)) ∧
    (∑ q ∈ oddPrimesBelow 73, computedLevel q 73) ≤ 70 := by
  simp only [← fastPrimesBelow_eq 73]
  decide +kernel
theorem column_cert_3 : columnSum 73 ≤ 70 :=
  (columnSum_le_computed 73 column_computed_3.1).trans column_computed_3.2
#print axioms column_cert_3

theorem column_computed_4 : (∀ q ∈ oddPrimesBelow 79, 79^2 ≤ q^(computedLevel q 79)) ∧
    (∑ q ∈ oddPrimesBelow 79, computedLevel q 79) ≤ 73 := by
  simp only [← fastPrimesBelow_eq 79]
  decide +kernel
theorem column_cert_4 : columnSum 79 ≤ 73 :=
  (columnSum_le_computed 79 column_computed_4.1).trans column_computed_4.2
#print axioms column_cert_4

theorem column_computed_5 : (∀ q ∈ oddPrimesBelow 82, 82^2 ≤ q^(computedLevel q 82)) ∧
    (∑ q ∈ oddPrimesBelow 82, computedLevel q 82) ≤ 77 := by
  simp only [← fastPrimesBelow_eq 82]
  decide +kernel
theorem column_cert_5 : columnSum 82 ≤ 77 :=
  (columnSum_le_computed 82 column_computed_5.1).trans column_computed_5.2
#print axioms column_cert_5

theorem column_computed_6 : (∀ q ∈ oddPrimesBelow 83, 83^2 ≤ q^(computedLevel q 83)) ∧
    (∑ q ∈ oddPrimesBelow 83, computedLevel q 83) ≤ 80 := by
  simp only [← fastPrimesBelow_eq 83]
  decide +kernel
theorem column_cert_6 : columnSum 83 ≤ 80 :=
  (columnSum_le_computed 83 column_computed_6.1).trans column_computed_6.2
#print axioms column_cert_6

theorem column_computed_7 : (∀ q ∈ oddPrimesBelow 89, 89^2 ≤ q^(computedLevel q 89)) ∧
    (∑ q ∈ oddPrimesBelow 89, computedLevel q 89) ≤ 81 := by
  simp only [← fastPrimesBelow_eq 89]
  decide +kernel
theorem column_cert_7 : columnSum 89 ≤ 81 :=
  (columnSum_le_computed 89 column_computed_7.1).trans column_computed_7.2
#print axioms column_cert_7

theorem column_computed_8 : (∀ q ∈ oddPrimesBelow 101, 101^2 ≤ q^(computedLevel q 101)) ∧
    (∑ q ∈ oddPrimesBelow 101, computedLevel q 101) ≤ 87 := by
  simp only [← fastPrimesBelow_eq 101]
  decide +kernel
theorem column_cert_8 : columnSum 101 ≤ 87 :=
  (columnSum_le_computed 101 column_computed_8.1).trans column_computed_8.2
#print axioms column_cert_8

theorem column_computed_9 : (∀ q ∈ oddPrimesBelow 110, 110^2 ≤ q^(computedLevel q 110)) ∧
    (∑ q ∈ oddPrimesBelow 110, computedLevel q 110) ≤ 99 := by
  simp only [← fastPrimesBelow_eq 110]
  decide +kernel
theorem column_cert_9 : columnSum 110 ≤ 99 :=
  (columnSum_le_computed 110 column_computed_9.1).trans column_computed_9.2
#print axioms column_cert_9

theorem column_computed_10 : (∀ q ∈ oddPrimesBelow 129, 129^2 ≤ q^(computedLevel q 129)) ∧
    (∑ q ∈ oddPrimesBelow 129, computedLevel q 129) ≤ 108 := by
  simp only [← fastPrimesBelow_eq 129]
  decide +kernel
theorem column_cert_10 : columnSum 129 ≤ 108 :=
  (columnSum_le_computed 129 column_computed_10.1).trans column_computed_10.2
#print axioms column_cert_10

theorem column_computed_11 : (∀ q ∈ oddPrimesBelow 157, 157^2 ≤ q^(computedLevel q 157)) ∧
    (∑ q ∈ oddPrimesBelow 157, computedLevel q 157) ≤ 127 := by
  simp only [← fastPrimesBelow_eq 157]
  decide +kernel
theorem column_cert_11 : columnSum 157 ≤ 127 :=
  (columnSum_le_computed 157 column_computed_11.1).trans column_computed_11.2
#print axioms column_cert_11

theorem column_computed_12 : (∀ q ∈ oddPrimesBelow 199, 199^2 ≤ q^(computedLevel q 199)) ∧
    (∑ q ∈ oddPrimesBelow 199, computedLevel q 199) ≤ 155 := by
  simp only [← fastPrimesBelow_eq 199]
  decide +kernel
theorem column_cert_12 : columnSum 199 ≤ 155 :=
  (columnSum_le_computed 199 column_computed_12.1).trans column_computed_12.2
#print axioms column_cert_12

theorem column_computed_13 : (∀ q ∈ oddPrimesBelow 277, 277^2 ≤ q^(computedLevel q 277)) ∧
    (∑ q ∈ oddPrimesBelow 277, computedLevel q 277) ≤ 197 := by
  simp only [← fastPrimesBelow_eq 277]
  decide +kernel
theorem column_cert_13 : columnSum 277 ≤ 197 :=
  (columnSum_le_computed 277 column_computed_13.1).trans column_computed_13.2
#print axioms column_cert_13

theorem column_computed_14 : (∀ q ∈ oddPrimesBelow 421, 421^2 ≤ q^(computedLevel q 421)) ∧
    (∑ q ∈ oddPrimesBelow 421, computedLevel q 421) ≤ 275 := by
  simp only [← fastPrimesBelow_eq 421]
  decide +kernel
theorem column_cert_14 : columnSum 421 ≤ 275 :=
  (columnSum_le_computed 421 column_computed_14.1).trans column_computed_14.2
#print axioms column_cert_14

theorem column_computed_15 : (∀ q ∈ oddPrimesBelow 709, 709^2 ≤ q^(computedLevel q 709)) ∧
    (∑ q ∈ oddPrimesBelow 709, computedLevel q 709) ≤ 419 := by
  simp only [← fastPrimesBelow_eq 709]
  decide +kernel
theorem column_cert_15 : columnSum 709 ≤ 419 :=
  (columnSum_le_computed 709 column_computed_15.1).trans column_computed_15.2
#print axioms column_cert_15

theorem column_computed_16 : (∀ q ∈ oddPrimesBelow 1361, 1361^2 ≤ q^(computedLevel q 1361)) ∧
    (∑ q ∈ oddPrimesBelow 1361, computedLevel q 1361) ≤ 707 := by
  simp only [← fastPrimesBelow_eq 1361]
  decide +kernel
theorem column_cert_16 : columnSum 1361 ≤ 707 :=
  (columnSum_le_computed 1361 column_computed_16.1).trans column_computed_16.2
#print axioms column_cert_16

theorem column_computed_17 : (∀ q ∈ oddPrimesBelow 2957, 2957^2 ≤ q^(computedLevel q 2957)) ∧
    (∑ q ∈ oddPrimesBelow 2957, computedLevel q 2957) ≤ 1359 := by
  simp only [← fastPrimesBelow_eq 2957]
  decide +kernel
theorem column_cert_17 : columnSum 2957 ≤ 1359 :=
  (columnSum_le_computed 2957 column_computed_17.1).trans column_computed_17.2
#print axioms column_cert_17

theorem column_computed_18 : (∀ q ∈ oddPrimesBelow 4095, 4095^2 ≤ q^(computedLevel q 4095)) ∧
    (∑ q ∈ oddPrimesBelow 4095, computedLevel q 4095) ≤ 2955 := by
  simp only [← fastPrimesBelow_eq 4095]
  decide +kernel
theorem column_cert_18 : columnSum 4095 ≤ 2955 :=
  (columnSum_le_computed 4095 column_computed_18.1).trans column_computed_18.2
#print axioms column_cert_18

theorem columnIntervals_valid (j : Fin 19) :
    columnSum (columnIntervals j).2 ≤ (columnIntervals j).1 - 3 := by
  fin_cases j
  · exact column_cert_0
  · exact column_cert_1
  · exact column_cert_2
  · exact column_cert_3
  · exact column_cert_4
  · exact column_cert_5
  · exact column_cert_6
  · exact column_cert_7
  · exact column_cert_8
  · exact column_cert_9
  · exact column_cert_10
  · exact column_cert_11
  · exact column_cert_12
  · exact column_cert_13
  · exact column_cert_14
  · exact column_cert_15
  · exact column_cert_16
  · exact column_cert_17
  · exact column_cert_18

theorem generic_column_bound (p : ℕ) (hp : p.Prime) (hlo : 67 ≤ p) :
    (∑ q ∈ oddPrimesBelow p, genericLevel q p) ≤ p - 3 := by
  by_cases hlarge : 4096 ≤ p
  · exact large_column_bound p hlarge
  · rw [← columnSum]
    obtain ⟨j, hjlo, hjhi⟩ := columnIntervals_cover p hp hlo (by omega)
    exact (columnSum_mono hjhi).trans ((columnIntervals_valid j).trans (Nat.sub_le_sub_right hjlo 3))

#print axioms generic_column_bound
end Erdos7GraphBudget


/-! Elementary finite reciprocal-square tail bounds for graph saturation. -/
namespace Erdos7GraphBudget
set_option maxHeartbeats 2000000

/-- A one-step telescoping majorant for reciprocal squares. -/
theorem reciprocal_square_step (x : ℚ) (hx : 1 < x) :
    1/x^2 ≤ (1/2 : ℚ) * (1/(x-1) - 1/(x+1)) := by
  have hx1 : 0 < x-1 := by linarith
  have hx2 : 0 < x+1 := by linarith
  have hprod : 0 < (x-1)*(x+1) := mul_pos hx1 hx2
  have hsquare : (x-1)*(x+1) ≤ x^2 := by nlinarith
  have h := one_div_le_one_div_of_le hprod hsquare
  convert h using 1
  field_simp
  ring

/-- A finite telescope, with no use of an infinite sum or asymptotic estimate. -/
theorem reciprocal_square_range (b N : ℕ) (hb : 2 ≤ b) :
    (∑ k ∈ Finset.range N, 1 / ((b : ℚ) + 2*k)^2) ≤
      (1/2 : ℚ) * (1/((b : ℚ)-1) - 1/((b : ℚ)+2*N-1)) := by
  have hbQ : (2 : ℚ) ≤ b := by exact_mod_cast hb
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hx : (1 : ℚ) < (b : ℚ)+2*N := by nlinarith [show (0 : ℚ) ≤ N by positivity]
    have hs := reciprocal_square_step ((b : ℚ)+2*N) hx
    push_cast
    rw [show (b : ℚ) + 2*((N : ℚ)+1)-1 = (b : ℚ)+2*N+1 by ring]
    linarith

/-- Arbitrary finite sets of odd integers have a telescoping square-reciprocal bound. -/
theorem odd_reciprocal_square_sum_le (b : ℕ) (hb : 2 ≤ b) (hbo : Odd b)
    (P : Finset ℕ) (hP : ∀ p ∈ P, b ≤ p ∧ Odd p) :
    (∑ p ∈ P, 1 / (p : ℚ)^2) ≤ 1 / (2*((b : ℚ)-1)) := by
  let f (p : ℕ) := (p-b)/2
  have hpform (p : ℕ) (hp : p ∈ P) : p = b + 2*f p := by
    have hbodd := Nat.odd_iff.mp hbo
    have hpodd := Nat.odd_iff.mp (hP p hp).2
    have hle := (hP p hp).1
    dsimp [f]
    omega
  have hfi : Set.InjOn f P := by
    intro p hp q hq hpq
    have h₁ := hpform p hp
    have h₂ := hpform q hq
    omega
  let S := P.image f
  let N := S.sup id + 1
  have hsub : S ⊆ Finset.range N := by
    intro k hk
    have hh := Finset.le_sup (f := id) hk
    dsimp only [id] at hh
    exact Finset.mem_range.mpr (by dsimp [N]; omega)
  have heq : (∑ p ∈ P, 1 / (p : ℚ)^2) = ∑ k ∈ S, 1 / ((b : ℚ)+2*k)^2 := by
    rw [Finset.sum_image hfi]
    apply Finset.sum_congr rfl
    intro p hp
    have he : (p : ℚ) = (b : ℚ) + 2*f p := by exact_mod_cast hpform p hp
    rw [he]
  rw [heq]
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun k _ _ => (show (0 : ℚ) ≤ 1 / ((b : ℚ)+2*k)^2 by positivity))
  have hh := hle.trans (reciprocal_square_range b N hb)
  have hbQ : (2 : ℚ) ≤ b := by exact_mod_cast hb
  have hpos : (0 : ℚ) < (b : ℚ)+2*N-1 := by nlinarith [show (0 : ℚ) ≤ N by positivity]
  have hn : (0 : ℚ) ≤ 1 / ((b : ℚ)+2*N-1) := by positivity
  calc
    _ ≤ (1/2 : ℚ) * (1/((b : ℚ)-1) - 1/((b : ℚ)+2*N-1)) := hh
    _ ≤ (1/2 : ℚ) * (1/((b : ℚ)-1)) := by linarith
    _ = _ := by simp only [one_div, mul_inv_rev]; ring

/-- The generic exponent choice makes every edge cost at most a reciprocal square. -/
theorem genericLevel_tail_le (q p : ℕ) (hq : 1 < q) (hqp : q < p) :
    ((q : ℚ)⁻¹)^(genericLevel q p - 1) ≤ (q : ℚ) / (p : ℚ)^2 := by
  have hpow : p^2 ≤ q^(genericLevel q p) := Nat.le_pow_clog hq _
  have hT : genericLevel q p ≠ 0 := by
    intro h
    rw [h, pow_zero] at hpow
    nlinarith
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hT
  rw [hn, Nat.succ_sub_one]
  rw [hn] at hpow
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hpQ : (0 : ℚ) < p := by exact_mod_cast (by omega : 0 < p)
  have hpowQ : (p : ℚ)^2 ≤ (q : ℚ)^(n+1) := by exact_mod_cast hpow
  have heq : ((q : ℚ)⁻¹)^n = (q : ℚ) / (q : ℚ)^(n+1) := by
    rw [pow_succ, inv_pow]
    field_simp
  rw [heq]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hpowQ

theorem genericLevel_tail_sum (q b : ℕ) (hq : 1 < q) (hb : 2 ≤ b) (hbo : Odd b)
    (P : Finset ℕ) (hP : ∀ p ∈ P, b ≤ p ∧ Odd p ∧ q < p) :
    (∑ p ∈ P, ((q : ℚ)⁻¹)^(genericLevel q p - 1)) ≤ (q : ℚ)/(2*((b : ℚ)-1)) := by
  calc
    _ ≤ ∑ p ∈ P, (q : ℚ)/(p : ℚ)^2 :=
      Finset.sum_le_sum (fun p hp => genericLevel_tail_le q p hq (hP p hp).2.2)
    _ = (q : ℚ) * ∑ p ∈ P, 1/(p : ℚ)^2 := by rw [Finset.mul_sum]; congr 1; ext p; ring
    _ ≤ (q : ℚ) * (1/(2*((b : ℚ)-1))) := mul_le_mul_of_nonneg_left
      (odd_reciprocal_square_sum_le b hb hbo P (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1⟩)) (by positivity)
    _ = _ := by ring

#print axioms genericLevel_tail_sum
end Erdos7GraphBudget


/-! Explicit row and column allocation for all finite odd-prime sets. -/
namespace Erdos7GraphBudget
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def smallLevel (q p : ℕ) : ℕ :=
  match q,p with
  | 3, 11 => 4
  | 3, 13 => 4
  | 3, 17 => 5
  | 5, 17 => 3
  | 3, 19 => 5
  | 5, 19 => 3
  | 3, 23 => 5
  | 5, 23 => 4
  | 7, 23 => 3
  | 3, 29 => 6
  | 5, 29 => 4
  | 7, 29 => 4
  | 11, 29 => 3
  | 13, 29 => 3
  | 3, 31 => 6
  | 5, 31 => 4
  | 7, 31 => 4
  | 11, 31 => 3
  | 13, 31 => 3
  | 3, 37 => 7
  | 5, 37 => 5
  | 7, 37 => 4
  | 11, 37 => 3
  | 13, 37 => 3
  | 17, 37 => 3
  | 19, 37 => 3
  | 3, 41 => 8
  | 5, 41 => 5
  | 7, 41 => 4
  | 11, 41 => 3
  | 13, 41 => 3
  | 17, 41 => 3
  | 19, 41 => 3
  | 23, 41 => 3
  | 3, 43 => 8
  | 5, 43 => 5
  | 7, 43 => 4
  | 11, 43 => 3
  | 13, 43 => 3
  | 17, 43 => 3
  | 19, 43 => 3
  | 23, 43 => 3
  | 3, 47 => 8
  | 5, 47 => 6
  | 7, 47 => 4
  | 11, 47 => 4
  | 13, 47 => 3
  | 17, 47 => 3
  | 19, 47 => 3
  | 23, 47 => 3
  | 3, 53 => 9
  | 5, 53 => 6
  | 7, 53 => 5
  | 11, 53 => 4
  | 13, 53 => 3
  | 17, 53 => 3
  | 19, 53 => 3
  | 23, 53 => 3
  | 29, 53 => 3
  | 31, 53 => 3
  | 3, 59 => 9
  | 5, 59 => 6
  | 7, 59 => 5
  | 11, 59 => 4
  | 13, 59 => 4
  | 17, 59 => 3
  | 19, 59 => 3
  | 23, 59 => 3
  | 29, 59 => 3
  | 31, 59 => 3
  | 37, 59 => 3
  | 41, 59 => 3
  | 43, 59 => 3
  | 3, 61 => 9
  | 5, 61 => 6
  | 7, 61 => 5
  | 11, 61 => 4
  | 13, 61 => 4
  | 17, 61 => 3
  | 19, 61 => 3
  | 23, 61 => 3
  | 29, 61 => 3
  | 31, 61 => 3
  | 37, 61 => 3
  | 41, 61 => 3
  | 43, 61 => 3
  | _, _ => 2

def edgeLevel (q p : ℕ) : ℕ := if p < 67 then smallLevel q p else genericLevel q p

theorem smallLevel_ge_one (q p : ℕ) : 1 ≤ smallLevel q p := by
  unfold smallLevel
  split <;> norm_num

theorem prefix_column_certificate :
    ∀ p ∈ oddPrimesBelow 67, (∑ q ∈ oddPrimesBelow p, smallLevel q p) ≤ p - 3 := by
  decide +kernel

theorem prefix_row_certificate :
    ∀ q ∈ oddPrimesBelow 67,
      (∑ p ∈ (oddPrimesBelow 67).filter (fun p => q < p), ((q : ℚ)⁻¹)^(smallLevel q p - 1)) +
        (q : ℚ)/132 < 1 := by
  decide +kernel

theorem edgeLevel_ge_one (q p : ℕ) (hq : 1 < q) (hqp : q < p) : 1 ≤ edgeLevel q p := by
  by_cases hsmall : p < 67
  · simp only [edgeLevel, if_pos hsmall]
    exact smallLevel_ge_one q p
  · simp only [edgeLevel, if_neg hsmall]
    have hh := Nat.le_pow_clog hq (p^2)
    change p^2 ≤ q^(genericLevel q p) at hh
    by_contra h
    have hz : genericLevel q p = 0 := by omega
    rw [hz, pow_zero] at hh
    nlinarith

theorem edgeLevel_column_bound (p : ℕ) (hp : p.Prime) (hop : Odd p) :
    (∑ q ∈ oddPrimesBelow p, edgeLevel q p) ≤ p - 3 := by
  by_cases hsmall : p < 67
  · simp only [edgeLevel, if_pos hsmall]
    apply prefix_column_certificate
    exact Finset.mem_erase.mpr ⟨by intro h; subst p; norm_num at hop,
      Nat.mem_primesBelow.mpr ⟨hsmall, hp⟩⟩
  · simp only [edgeLevel, if_neg hsmall]
    exact generic_column_bound p hp (by omega)

theorem edgeLevel_row_bound (q : ℕ) (hq : q.Prime) (hoq : Odd q)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Odd p ∧ q < p) :
    (∑ p ∈ P, ((q : ℚ)⁻¹)^(edgeLevel q p - 1)) < 1 := by
  by_cases hsmall : q < 67
  · let Low := P.filter (fun p => p < 67)
    let High := P.filter (fun p => ¬p < 67)
    have hlow : (∑ p ∈ Low, ((q : ℚ)⁻¹)^(edgeLevel q p-1)) ≤
        ∑ p ∈ (oddPrimesBelow 67).filter (fun p => q < p), ((q : ℚ)⁻¹)^(smallLevel q p-1) := by
      have hsub : Low ⊆ (oddPrimesBelow 67).filter (fun p => q < p) := by
        intro p hp
        obtain ⟨hpP, hp67⟩ := Finset.mem_filter.mp hp
        have hh := hP p hpP
        exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr
          ⟨by intro h; subst p; norm_num at hh, Nat.mem_primesBelow.mpr ⟨hp67, hh.1⟩⟩, hh.2.2⟩
      calc
        _ = ∑ p ∈ Low, ((q : ℚ)⁻¹)^(smallLevel q p-1) := by
          apply Finset.sum_congr rfl
          intro p hp
          simp only [edgeLevel, if_pos (Finset.mem_filter.mp hp).2]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    have hhigh : (∑ p ∈ High, ((q : ℚ)⁻¹)^(edgeLevel q p-1)) ≤ (q : ℚ)/132 := by
      have hh := genericLevel_tail_sum q 67 hq.one_lt (by norm_num) (by norm_num) High (by
        intro p hp
        obtain ⟨hpP, hp67⟩ := Finset.mem_filter.mp hp
        have hh := hP p hpP
        exact ⟨by omega, hh.2.1, hh.2.2⟩)
      have heq : (∑ p ∈ High, ((q : ℚ)⁻¹)^(edgeLevel q p-1)) =
          ∑ p ∈ High, ((q : ℚ)⁻¹)^(genericLevel q p-1) := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [edgeLevel, if_neg (Finset.mem_filter.mp hp).2]
      rw [heq]
      norm_num at hh ⊢
      exact hh
    have hqP : q ∈ oddPrimesBelow 67 := Finset.mem_erase.mpr
      ⟨by intro h; subst q; norm_num at hoq, Nat.mem_primesBelow.mpr ⟨hsmall, hq⟩⟩
    have hcert := prefix_row_certificate q hqP
    have hs := Finset.sum_filter_add_sum_filter_not P (fun p => p < 67)
      (fun p => ((q : ℚ)⁻¹)^(edgeLevel q p-1))
    change (∑ p ∈ Low, _) + (∑ p ∈ High, _) = _ at hs
    linarith
  · have hhi (p : ℕ) (hp : p ∈ P) : q+2 ≤ p ∧ Odd p ∧ q < p := by
      have hh := hP p hp
      have hqo := Nat.odd_iff.mp hoq
      have hpo := Nat.odd_iff.mp hh.2.1
      exact ⟨by omega, hh.2.1, hh.2.2⟩
    have hh := genericLevel_tail_sum q (q+2) hq.one_lt (by omega) (hoq.add_even (by norm_num)) P hhi
    have heq : (∑ p ∈ P, ((q : ℚ)⁻¹)^(edgeLevel q p-1)) =
        ∑ p ∈ P, ((q : ℚ)⁻¹)^(genericLevel q p-1) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hh := hP p hp
      simp only [edgeLevel, if_neg (show ¬p < 67 by omega)]
    rw [heq]
    apply hh.trans_lt
    push_cast
    apply (div_lt_one (by nlinarith [show (0 : ℚ) ≤ q by positivity] : (0 : ℚ) < 2*((q : ℚ)+2-1))).mpr
    nlinarith [show (0 : ℚ) ≤ q by positivity]

theorem edgeLevel_column_on_sorted_primes {n : ℕ} (p : Fin n → ℕ)
    (hp : ∀ i, (p i).Prime ∧ Odd (p i)) (hmono : StrictMono p) (j : Fin n) :
    (∑ i ∈ Finset.univ.filter (fun i => i < j), edgeLevel (p i) (p j)) ≤ p j - 3 := by
  classical
  let S := Finset.univ.filter (fun i => i < j)
  have hsub : S.image p ⊆ oddPrimesBelow (p j) := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_erase.mpr ⟨by intro h; have hh := (hp i).2; rw [h] at hh; norm_num at hh,
      Nat.mem_primesBelow.mpr ⟨hmono (Finset.mem_filter.mp hi).2, (hp i).1⟩⟩
  have hh := Finset.sum_le_sum_of_subset (f := fun q => edgeLevel q (p j)) hsub
  rw [Finset.sum_image hmono.injective.injOn] at hh
  exact hh.trans (edgeLevel_column_bound (p j) (hp j).1 (hp j).2)

theorem edgeLevel_row_on_sorted_primes {n : ℕ} (p : Fin n → ℕ)
    (hp : ∀ i, (p i).Prime ∧ Odd (p i)) (hmono : StrictMono p) (i : Fin n) :
    (∑ j ∈ Finset.univ.filter (fun j => i < j), ((p i : ℚ)⁻¹)^(edgeLevel (p i) (p j)-1)) < 1 := by
  classical
  let S := Finset.univ.filter (fun j => i < j)
  have hh := edgeLevel_row_bound (p i) (hp i).1 (hp i).2 (S.image p) (by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨(hp j).1, (hp j).2, hmono (Finset.mem_filter.mp hj).2⟩)
  rwa [Finset.sum_image hmono.injective.injOn] at hh

#print axioms edgeLevel_column_bound
#print axioms edgeLevel_row_bound
#print axioms prefix_column_certificate
#print axioms prefix_row_certificate
end Erdos7GraphBudget


/-! Every odd strict cover requires a modulus with three distinct prime factors. -/
namespace Erdos7GraphSaturation
open Erdos7Reduction Erdos7StarSieve Erdos7GraphBudget
set_option maxHeartbeats 3000000

/-- Arithmetic specialization of the two-coordinate box obstruction. -/
theorem not_graph_coordinate_cover {n : ℕ} {κ : Type*} [Fintype κ]
    (p E : Fin n → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i)) (hmono : StrictMono p)
    (e : κ → Fin n → ℕ) (he : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (heE : ∀ k i, e k i ≤ E i)
    (he2 : ∀ k, (Finset.univ.filter (fun i => e k i ≠ 0)).card ≤ 2) (a : κ → ℤ) :
    ¬ (∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k) := by
  classical
  intro hcover
  have hp2 (i : Fin n) : 2 < p i := by
    have := (hp i).1.two_le
    have := Nat.odd_iff.mp (hp i).2
    omega
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i).1 (hp j).1).mpr (fun h => hij (hmono.injective h))
  letI (i : Fin n) : NeZero (p i) := ⟨by have := hp2 i; omega⟩
  let A (i : Fin n) := ZMod (p i ^ E i)
  let f (k : κ) (i : Fin n) := ZMod.castHom (pow_dvd_pow (p i) (heE k i)) (ZMod (p i ^ e k i))
  let B (k : κ) (i : Fin n) := Finset.univ.filter (fun x : A i => f k i x = (a k : ZMod (p i ^ e k i)))
  have hBcard (k : κ) (i : Fin n) : ((B k i).card : ℚ) ≤
      (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(e k i) := by
    have hh := surjective_fiber_card_rat (f k i).toAddMonoidHom
      (ZMod.castHom_surjective (pow_dvd_pow (p i) (heE k i))) (a k)
    change ((B k i).card : ℚ) = _ at hh
    rw [hh]
    simp only [A, ZMod.card, Nat.cast_pow, div_eq_mul_inv, inv_pow]
    exact le_rfl
  have hbox : ∀ x : ∀ i, A i, ∃ k, ∀ i, x i ∈ B k i := by
    intro x
    let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) (fun i => p i ^ E i) Finset.univ
      (fun i _ => pow_ne_zero _ (NeZero.ne _))
      (fun i _ j _ hij => (hcop hij).pow _ _)
    have hz (i : Fin n) : (z.val : A i) = x i := by
      rw [← ZMod.natCast_zmod_val (x i)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
    obtain ⟨k, hk⟩ := hcover (z.val : ℤ)
    refine ⟨k, ?_⟩
    intro i
    have hpi : p i ^ e k i ∣ ∏ j, p j ^ e k j :=
      Finset.dvd_prod_of_mem (fun j => p j ^ e k j) (Finset.mem_univ i)
    have hpi' : ((p i ^ e k i : ℕ) : ℤ) ∣ ((∏ j, p j ^ e k j : ℕ) : ℤ) := by exact_mod_cast hpi
    have hqi := hpi'.trans hk
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hz i, map_natCast]
    symm
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (a k) (z.val : ℤ) (p i ^ e k i)).mpr hqi
  exact not_graph_box_cover A p hp2 e he he0 he2 B hBcard
    (fun i j => edgeLevel (p i) (p j))
    (fun i j hij => edgeLevel_ge_one (p i) (p j) (hp i).1.one_lt (hmono hij))
    (edgeLevel_column_on_sorted_primes p hp hmono) (edgeLevel_row_on_sorted_primes p hp hmono) hbox

/-- Distinct odd moduli with at most two prime factors cannot cover the integers. -/
theorem not_arithmetic_graph_cover {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a) :
    ¬ (∀ k, (m k).primeFactors.card ≤ 2) := by
  classical
  intro hsmall
  have hm0 (k : κ) : m k ≠ 0 := by have := (hc.2.1 k).1; omega
  let P := Finset.univ.biUnion (fun k => (m k).primeFactors)
  have hP (q : ℕ) (hq : q ∈ P) : q.Prime ∧ Odd q := by
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hq
    have hh := Nat.mem_primeFactors.mp hk
    exact ⟨hh.1, (hc.2.1 k).2.of_dvd_nat hh.2.1⟩
  let p := P.orderEmbOfFin rfl
  have hp (i : Fin P.card) : (p i).Prime ∧ Odd (p i) := hP _ (P.orderEmbOfFin_mem rfl i)
  let e (k : κ) (i : Fin P.card) := (m k).factorization (p i)
  let E (i : Fin P.card) := Finset.univ.sup (fun k => e k i)
  have heE (k : κ) (i : Fin P.card) : e k i ≤ E i :=
    Finset.le_sup (f := fun k => e k i) (Finset.mem_univ k)
  have hprod (k : κ) : m k = ∏ i : Fin P.card, p i ^ e k i := by
    have hsub : (m k).primeFactors ⊆ P := by
      intro q hq
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hq⟩
    have hh := Erdos7Compression.factorization_product_over_superset (m k) (hm0 k) P hsub
    rw [Finset.prod_coe_sort P (fun q => q ^ (m k).factorization q)] at hh
    nth_rw 1 [hh]
    conv_lhs => rw [← P.map_orderEmbOfFin_univ rfl]
    exact Finset.prod_map _ _ (fun q : ℕ => q ^ (m k).factorization q)
  have hei : Function.Injective e := by
    intro k l hkl
    apply hc.1
    rw [hprod k, hprod l, hkl]
  have he0 (k : κ) : ∃ i, e k i ≠ 0 := by
    by_contra! h
    have hh := (hc.2.1 k).1
    rw [hprod k] at hh
    simp only [h, pow_zero, Finset.prod_const_one] at hh
    omega
  have he2 (k : κ) : (Finset.univ.filter (fun i => e k i ≠ 0)).card ≤ 2 := by
    let S := Finset.univ.filter (fun i => e k i ≠ 0)
    have hsub : S.image p ⊆ (m k).primeFactors := by
      intro q hq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      have hi' := (Finset.mem_filter.mp hi).2
      have hd : p i ∣ m k := by
        by_contra h
        exact hi' (Nat.factorization_eq_zero_of_not_dvd h)
      exact Nat.mem_primeFactors.mpr ⟨(hp i).1, hd, hm0 k⟩
    have hh := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn p.injective.injOn] at hh
    exact hh.trans (hsmall k)
  apply not_graph_coordinate_cover p E hp p.strictMono e hei he0 heE he2 a
  simpa only [← hprod] using hc.2.2

/-- Every odd cover needs a modulus involving at least three distinct primes. -/
theorem arithmetic_exists_three_prime_factors {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a) :
    ∃ k, 3 ≤ (m k).primeFactors.card := by
  by_contra! h
  exact not_arithmetic_graph_cover m a hc (fun k => by have := h k; omega)

/-- Ideal-valued form of the two-prime-support obstruction. -/
theorem exists_three_prime_factors (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i, ¬ C.moduli i ≤ Ideal.span {2}) :
    ∃ i, 3 ≤ (C.moduli i).absNorm.primeFactors.card := by
  letI := C.fintypeIndex
  exact arithmetic_exists_three_prime_factors (fun i => (C.moduli i).absNorm) C.residue
    ⟨moduli_absNorm_injective C, fun i => ⟨moduli_absNorm_gt_one C i,
      (ideal_not_le_two_iff _).mp (hodd i)⟩, arithmetic_cover C⟩

#print axioms exists_three_prime_factors
end Erdos7GraphSaturation



/-! Quantitative sequential avoidance. These are necessary conditions for an odd
cover, not a proof or disproof of the unrestricted odd covering conjecture. -/

namespace Erdos7GraphSaturation

set_option maxHeartbeats 2000000

/-- Conditional expectations can be bounded using only a finite admissible set
at each stage. No independence of the admissible sets is assumed. -/
theorem sequential_weighted_choice {n : ℕ} {κ : Type*} [Fintype κ]
    (A : Fin n → Type*) [∀ i, Nonempty (A i)]
    (G : ℕ → (∀ i, A i) → Prop) (hG0 : ∀ x, G 0 x)
    (w : κ → ∀ i, A i → ℚ) (c : κ → Fin n → ℚ)
    (hw : ∀ k i v, 0 ≤ w k i v) (hc : ∀ k i, 0 ≤ c k i)
    (hstep : ∀ (i : Fin n) x, G i.val x →
      ∃ L : Finset (A i), L.Nonempty ∧
        (∀ v ∈ L, G (i.val + 1) (Function.update x i v)) ∧
        ∀ k, ∑ v ∈ L, w k i v ≤ (L.card : ℚ) * c k i) :
    ∃ x : ∀ i, A i, G n x ∧
      (∑ k, ∏ i, w k i (x i)) ≤ ∑ k, ∏ i, c k i := by
  classical
  let f (t : ℕ) (x : ∀ i, A i) (k : κ) (j : Fin n) : ℚ :=
    if j.val < t then w k j (x j) else c k j
  let P (t : ℕ) (x : ∀ i, A i) : ℚ := ∑ k, ∏ j, f t x k j
  have hf (t : ℕ) (x : ∀ i, A i) (k : κ) (j : Fin n) : 0 ≤ f t x k j := by
    dsimp [f]
    split_ifs <;> [exact hw k j (x j); exact hc k j]
  have hmean (i : Fin n) (x : ∀ j, A j) (L : Finset (A i))
      (hL : ∀ k, ∑ v ∈ L, w k i v ≤ (L.card : ℚ) * c k i) :
      (∑ v ∈ L, P (i.val + 1) (Function.update x i v)) ≤
        (L.card : ℚ) * P i.val x := by
    let R (k : κ) := ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, f i.val x k j
    have hR (k : κ) : 0 ≤ R k := Finset.prod_nonneg (fun j _ => hf _ _ _ _)
    have hold (k : κ) : (∏ j, f i.val x k j) = c k i * R k := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      simp only [f, lt_self_iff_false, ↓reduceIte]
      rfl
    have hnew (k : κ) (v : A i) :
        (∏ j, f (i.val + 1) (Function.update x i v) k j) = w k i v * R k := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      have hself : f (i.val + 1) (Function.update x i v) k i = w k i v := by
        simp [f]
      rw [hself]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      have hji := (Finset.mem_erase.mp hj).1
      have hne : j.val ≠ i.val := by intro h; exact hji (Fin.ext h)
      have hiff : j.val < i.val + 1 ↔ j.val < i.val := by omega
      simp only [f, hiff, Function.update_of_ne hji]
    dsimp only [P]
    simp_rw [hnew]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    calc
      _ ≤ ∑ k, ((L.card : ℚ) * c k i) * R k :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hL k) (hR k))
      _ = (L.card : ℚ) * ∑ k, ∏ j, f i.val x k j := by
        simp_rw [hold, mul_assoc]
        rw [Finset.mul_sum]
  have aux (t : ℕ) (ht : t ≤ n) :
      ∃ x : ∀ i, A i, G t x ∧ P t x ≤ ∑ k, ∏ i, c k i := by
    induction t with
    | zero =>
      let x : ∀ i, A i := Classical.choice inferInstance
      exact ⟨x, hG0 x, by simp [P, f]⟩
    | succ t ih =>
      obtain ⟨x, hxG, hxP⟩ := ih (by omega)
      let i : Fin n := ⟨t, by omega⟩
      obtain ⟨L, hLne, hLG, hLw⟩ := hstep i x hxG
      have hm := hmean i x L hLw
      have hm' : (∑ v ∈ L, P (t + 1) (Function.update x i v)) ≤
          ∑ _v ∈ L, P t x := by
        simpa only [i, Finset.sum_const, nsmul_eq_mul] using hm
      obtain ⟨v, hvL, hvP⟩ := Finset.exists_le_of_sum_le hLne hm'
      exact ⟨Function.update x i v, hLG v hvL, hvP.trans hxP⟩
  obtain ⟨x, hxG, hxP⟩ := aux n le_rfl
  refine ⟨x, hxG, ?_⟩
  simpa only [P, f, Fin.isLt, ↓reduceIte] using hxP

/-- Weighted box avoidance with arbitrary history-dependent admissible sets.
The coefficient of a box need only bound its conditional one-coordinate hit
probability at every admissible history. -/
theorem sequential_box_avoidance {n : ℕ} {κ : Type*} [Fintype κ]
    (A : Fin n → Type*) [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (G : ℕ → (∀ i, A i) → Prop) (hG0 : ∀ x, G 0 x)
    (X : κ → ∀ i, Finset (A i)) (c : κ → Fin n → ℚ)
    (hc : ∀ k i, 0 ≤ c k i)
    (hstep : ∀ (i : Fin n) x, G i.val x →
      ∃ L : Finset (A i), L.Nonempty ∧
        (∀ v ∈ L, G (i.val + 1) (Function.update x i v)) ∧
        ∀ k, ((L.filter (fun v => v ∈ X k i)).card : ℚ) ≤
          (L.card : ℚ) * c k i)
    (hcost : (∑ k, ∏ i, c k i) < 1) :
    ∃ x : ∀ i, A i, G n x ∧ ∀ k, ¬ (∀ i, x i ∈ X k i) := by
  classical
  let w (k : κ) (i : Fin n) (v : A i) : ℚ := if v ∈ X k i then 1 else 0
  have hw (k : κ) (i : Fin n) (v : A i) : 0 ≤ w k i v := by
    dsimp [w]; split_ifs <;> norm_num
  have hs (i : Fin n) (x : ∀ j, A j) (hx : G i.val x) :
      ∃ L : Finset (A i), L.Nonempty ∧
        (∀ v ∈ L, G (i.val + 1) (Function.update x i v)) ∧
        ∀ k, ∑ v ∈ L, w k i v ≤ (L.card : ℚ) * c k i := by
    obtain ⟨L, hL, hLG, hLX⟩ := hstep i x hx
    refine ⟨L, hL, hLG, fun k => ?_⟩
    simpa only [w, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      using hLX k
  obtain ⟨x, hxG, hx⟩ := sequential_weighted_choice A G hG0 w c hw hc hs
  refine ⟨x, hxG, fun k hk => ?_⟩
  have hone : (∏ i, w k i (x i)) = 1 := by simp [w, hk]
  have hle : (∏ i, w k i (x i)) ≤ ∑ k, ∏ i, w k i (x i) :=
    Finset.single_le_sum (fun k _ => Finset.prod_nonneg (fun i _ => hw k i (x i))) (Finset.mem_univ k)
  rw [hone] at hle
  linarith

#print axioms sequential_weighted_choice
#print axioms sequential_box_avoidance
/-- A quantitative refinement of `greedy_edge_avoidance`. A box is charged
only for the coordinates it restricts: the factor is capped at one. -/
theorem greedy_edge_box_avoidance {n : ℕ} {κ : Type*} [Fintype κ]
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    [∀ i, DecidableEq (A i)]
    (D : ∀ i, Finset (A i)) (B : ∀ i j, A i → Finset (A j))
    (d : Fin n → ℚ) (r : Fin n → Fin n → ℚ) (δ : Fin n → ℚ)
    (hδ : ∀ i, 0 < δ i)
    (hD : ∀ i, ((D i).card : ℚ) ≤ (Fintype.card (A i) : ℚ) * d i)
    (hB : ∀ i j, i < j → ∀ x, x ∉ D i →
      ((B i j x).card : ℚ) ≤ (Fintype.card (A j) : ℚ) * r i j)
    (hbudget : ∀ i, d i + ∑ j ∈ Finset.univ.filter (fun j => j < i), r j i + δ i ≤ 1)
    (X : κ → ∀ i, Finset (A i)) (q : κ → Fin n → ℚ)
    (hq : ∀ k i, 0 ≤ q k i)
    (hX : ∀ k i, ((X k i).card : ℚ) ≤ (Fintype.card (A i) : ℚ) * q k i)
    (hcost : (∑ k, ∏ i, min 1 (q k i / δ i)) < 1) :
    ∃ x : ∀ i, A i, (∀ i, x i ∉ D i) ∧
      (∀ i j, i < j → x j ∉ B i j (x i)) ∧ ∀ k, ¬ (∀ i, x i ∈ X k i) := by
  classical
  let G (t : ℕ) (x : ∀ i, A i) : Prop :=
    ∀ i, i.val < t → x i ∉ D i ∧ ∀ j, j < i → x i ∉ B j i (x j)
  have hG0 (x : ∀ i, A i) : G 0 x := by simp [G]
  let c (k : κ) (i : Fin n) : ℚ := min 1 (q k i / δ i)
  have hc (k : κ) (i : Fin n) : 0 ≤ c k i :=
    le_min (by norm_num) (div_nonneg (hq k i) (hδ i).le)
  have hstep (i : Fin n) (x : ∀ j, A j) (hx : G i.val x) :
      ∃ L : Finset (A i), L.Nonempty ∧
        (∀ v ∈ L, G (i.val + 1) (Function.update x i v)) ∧
        ∀ k, ((L.filter (fun v => v ∈ X k i)).card : ℚ) ≤
          (L.card : ℚ) * c k i := by
    let S := Finset.univ.filter (fun j => j < i)
    let U := D i ∪ S.biUnion (fun j => B j i (x j))
    let L := Finset.univ \ U
    have hcU : (U.card : ℚ) ≤ (Fintype.card (A i) : ℚ) *
        (d i + ∑ j ∈ S, r j i) := by
      have hcard : (U.card : ℚ) ≤ ((D i).card : ℚ) + ∑ j ∈ S, ((B j i (x j)).card : ℚ) := by
        exact_mod_cast (Finset.card_union_le _ _).trans
          (Nat.add_le_add_left (Finset.card_biUnion_le (s := S)) _)
      calc
        _ ≤ ((D i).card : ℚ) + ∑ j ∈ S, ((B j i (x j)).card : ℚ) := hcard
        _ ≤ (Fintype.card (A i) : ℚ) * d i +
            ∑ j ∈ S, (Fintype.card (A i) : ℚ) * r j i := by
          apply add_le_add (hD i)
          apply Finset.sum_le_sum
          intro j hj
          have hji : j < i := (Finset.mem_filter.mp hj).2
          exact hB j i hji (x j) (hx j hji).1
        _ = _ := by rw [mul_add, Finset.mul_sum]
    have hN : (0 : ℚ) < Fintype.card (A i) := by exact_mod_cast Fintype.card_pos
    have hcards : (L.card : ℚ) + U.card = Fintype.card (A i) := by
      have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ U)
      exact_mod_cast h
    have hLcard : (Fintype.card (A i) : ℚ) * δ i ≤ L.card := by
      have hb := mul_le_mul_of_nonneg_left (hbudget i) hN.le
      dsimp [S] at hcU
      nlinarith
    have hLpos : (0 : ℚ) < L.card := (mul_pos hN (hδ i)).trans_le hLcard
    have hLne : L.Nonempty := Finset.card_pos.mp (by exact_mod_cast hLpos)
    have hvalid (v : A i) (hv : v ∈ L) : v ∉ D i ∧ ∀ j, j < i → v ∉ B j i (x j) := by
      have hnot : v ∉ U := (Finset.mem_sdiff.mp hv).2
      constructor
      · intro hd; exact hnot (Finset.mem_union_left _ hd)
      · intro j hji hb
        exact hnot (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji⟩, hb⟩))
    refine ⟨L, hLne, ?_, ?_⟩
    · intro v hv j hj
      obtain ⟨hvD, hvB⟩ := hvalid v hv
      by_cases hji : j = i
      · subst j
        constructor
        · simpa only [Function.update_self] using hvD
        · intro k hki
          simpa only [Function.update_self, Function.update_of_ne (ne_of_lt hki)] using hvB k hki
      · have hne : j.val ≠ i.val := by intro h; exact hji (Fin.ext h)
        have hjt : j.val < i.val := by omega
        obtain ⟨hjD, hjB⟩ := hx j hjt
        constructor
        · simpa only [Function.update_of_ne hji] using hjD
        · intro k hkj
          have hki : k ≠ i := ne_of_lt (lt_trans hkj hjt)
          simpa only [Function.update_of_ne hji, Function.update_of_ne hki] using hjB k hkj
    · intro k
      have hhL : ((L.filter (fun v => v ∈ X k i)).card : ℚ) ≤ L.card := by
        exact_mod_cast Finset.card_filter_le L (fun v => v ∈ X k i)
      have hhX : ((L.filter (fun v => v ∈ X k i)).card : ℚ) ≤ (X k i).card := by
        exact_mod_cast Finset.card_le_card (show L.filter (fun v => v ∈ X k i) ⊆ X k i from
          fun v hv => (Finset.mem_filter.mp hv).2)
      have hratio : ((L.filter (fun v => v ∈ X k i)).card : ℚ) ≤ (L.card : ℚ) * (q k i / δ i) := by
        apply (hhX.trans (hX k i)).trans
        rw [← mul_div_assoc, le_div_iff₀ (hδ i)]
        nlinarith [mul_le_mul_of_nonneg_right hLcard (hq k i)]
      dsimp only [c]
      rw [mul_min_of_nonneg _ _ hLpos.le, mul_one]
      exact le_min hhL hratio
  obtain ⟨x, hxG, hxX⟩ := sequential_box_avoidance A G hG0 X c hc hstep hcost
  exact ⟨x, fun i => (hxG i i.isLt).1, fun i j hij => (hxG j j.isLt).2 i hij, hxX⟩

#print axioms greedy_edge_box_avoidance
end Erdos7GraphSaturation



/-! Applying quantitative graph conditioning to arbitrary-support boxes. -/
namespace Erdos7GraphSaturation
open Erdos7Reduction Erdos7StarSieve
set_option maxHeartbeats 3000000

/-- After avoiding pure and two-coordinate boxes, the boxes on three or more
coordinates still need total conditional weight at least one. The slack may be
chosen separately in each coordinate. -/
theorem graph_conditioned_cover_bound {n : ℕ} {κ : Type*} [Fintype κ]
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (p : Fin n → ℕ) (hp : ∀ i, 2 < p i)
    (e : κ → Fin n → ℕ) (he : Function.Injective e)
    (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (X : κ → ∀ i, Finset (A i))
    (hX : ∀ k i, ((X k i).card : ℚ) ≤ (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(e k i))
    (T : Fin n → Fin n → ℕ) (hT : ∀ i j, i < j → 1 ≤ T i j)
    (δ : Fin n → ℚ) (hδ : ∀ i, 0 < δ i)
    (hslack : ∀ i,
      (1 + (∑ j ∈ Finset.univ.filter (fun j => i < j), ((p i : ℚ)⁻¹)^(T i j-1)) +
        (∑ j ∈ Finset.univ.filter (fun j => j < i), (T j i : ℚ))) / (p i-1) + δ i ≤ 1)
    (hcover : ∀ x : ∀ i, A i, ∃ k, ∀ i, x i ∈ X k i) :
    1 ≤ ∑ k ∈ Finset.univ.filter (fun k => 3 ≤ (Finset.univ.filter (fun i => e k i ≠ 0)).card),
      ∏ i, min 1 (((p i : ℚ)⁻¹)^(e k i) / δ i) := by
  classical
  let supp (k : κ) := Finset.univ.filter (fun i => e k i ≠ 0)
  let Pure (i : Fin n) := Finset.univ.filter (fun k => supp k = {i})
  let K (i j : Fin n) := Finset.univ.filter (fun k => supp k = {i,j})
  have hmem (k : κ) (i : Fin n) : i ∈ supp k ↔ e k i ≠ 0 := by simp [supp]
  have hpure (i : Fin n) (k : κ) (hk : k ∈ Pure i) : supp k = {i} := (Finset.mem_filter.mp hk).2
  have hedge (i j : Fin n) (k : κ) (hk : k ∈ K i j) : supp k = {i,j} := (Finset.mem_filter.mp hk).2
  have hpos (i j : Fin n) (k : κ) (hk : k ∈ K i j) : 0 < e k i ∧ 0 < e k j := by
    have hi : i ∈ supp k := by rw [hedge i j k hk]; simp
    have hj : j ∈ supp k := by rw [hedge i j k hk]; simp
    have := (hmem k i).mp hi
    have := (hmem k j).mp hj
    omega
  have hpair (i j : Fin n) : Set.InjOn (fun k => (e k i, e k j)) (K i j) := by
    intro k hk l hl hkl
    apply he
    funext t
    by_cases hti : t = i
    · subst t; exact congrArg Prod.fst hkl
    · by_cases htj : t = j
      · subst t; exact congrArg Prod.snd hkl
      · have hk0 : e k t = 0 := by
          by_contra h
          have hh := (hmem k t).mpr h
          rw [hedge i j k hk] at hh
          simp [hti, htj] at hh
        have hl0 : e l t = 0 := by
          by_contra h
          have hh := (hmem l t).mpr h
          rw [hedge i j l hl] at hh
          simp [hti, htj] at hh
        rw [hk0, hl0]
  let H (i j : Fin n) := heavyHubSet (K i j) (fun k => X k i)
    (fun k => ((p j : ℚ)⁻¹)^(e k j)) ((T i j : ℚ)/(p j-1))
  let D (i : Fin n) := (Pure i).biUnion (fun k => X k i) ∪
    (Finset.univ.filter (fun j => i < j)).biUnion (fun j => H i j)
  let B (i j : Fin n) (x : A i) := ((K i j).filter (fun k => x ∈ X k i)).biUnion (fun k => X k j)
  let d (i : Fin n) : ℚ := (1 + ∑ j ∈ Finset.univ.filter (fun j => i < j),
    ((p i : ℚ)⁻¹)^(T i j-1)) / (p i-1)
  let r (i j : Fin n) : ℚ := (T i j : ℚ)/(p j-1)
  have hD (i : Fin n) : ((D i).card : ℚ) ≤ (Fintype.card (A i) : ℚ) * d i := by
    have hpi : Set.InjOn (fun k => e k i) (Pure i) := by
      intro k hk l hl hkl
      apply he
      funext t
      by_cases hti : t = i
      · simpa [hti] using hkl
      · have hk0 : e k t = 0 := by
          by_contra h
          have hh := (hmem k t).mpr h
          rw [hpure i k hk] at hh
          exact hti (Finset.mem_singleton.mp hh)
        have hl0 : e l t = 0 := by
          by_contra h
          have hh := (hmem l t).mpr h
          rw [hpure i l hl] at hh
          exact hti (Finset.mem_singleton.mp hh)
        rw [hk0, hl0]
    have hpp (k : κ) (hk : k ∈ Pure i) : 0 < e k i := by
      have hh : i ∈ supp k := by rw [hpure i k hk]; simp
      have := (hmem k i).mp hh
      omega
    have hg := positive_geometric_sum_le (p i) (by have := hp i; omega)
      ((Pure i).image (fun k => e k i)) (by
        intro a ha
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
        exact hpp k hk)
    rw [Finset.sum_image hpi] at hg
    have hpc : (((Pure i).biUnion (fun k => X k i)).card : ℚ) ≤ (Fintype.card (A i) : ℚ)/(p i-1) := by
      calc
        _ ≤ ∑ k ∈ Pure i, ((X k i).card : ℚ) := by exact_mod_cast Finset.card_biUnion_le (s := Pure i) (t := fun k => X k i)
        _ ≤ ∑ k ∈ Pure i, (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(e k i) := Finset.sum_le_sum (fun k _ => hX k i)
        _ = (Fintype.card (A i) : ℚ) * ∑ k ∈ Pure i, ((p i : ℚ)⁻¹)^(e k i) := (Finset.mul_sum _ _ _).symm
        _ ≤ (Fintype.card (A i) : ℚ) * (1/(p i-1)) := mul_le_mul_of_nonneg_left hg (by positivity)
        _ = _ := by ring
    have hhc (j : Fin n) (hij : i < j) : ((H i j).card : ℚ) ≤ (Fintype.card (A i) : ℚ) *
        (((p i : ℚ)⁻¹)^(T i j-1)/(p i-1)) :=
      edge_heavy_bound (p i) (p j) (T i j) (by have := hp i; omega) (by have := hp j; omega) (hT i j hij)
        (K i j) (fun k => e k i) (fun k => e k j) (hpair i j)
        (fun k hk => (hpos i j k hk).1) (fun k hk => (hpos i j k hk).2)
        (fun k => X k i) (fun k _ => hX k i)
    have hc : ((D i).card : ℚ) ≤ (((Pure i).biUnion (fun k => X k i)).card : ℚ) +
        ∑ j ∈ Finset.univ.filter (fun j => i < j), ((H i j).card : ℚ) := by
      exact_mod_cast (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_biUnion_le (s := Finset.univ.filter (fun j => i < j))) _)
    apply hc.trans
    calc
      _ ≤ (Fintype.card (A i) : ℚ)/(p i-1) + ∑ j ∈ Finset.univ.filter (fun j => i < j),
          (Fintype.card (A i) : ℚ) * (((p i : ℚ)⁻¹)^(T i j-1)/(p i-1)) :=
        add_le_add hpc (Finset.sum_le_sum (fun j hj => hhc j (Finset.mem_filter.mp hj).2))
      _ = _ := by dsimp [d]; rw [← Finset.mul_sum, ← Finset.sum_div]; ring
  have hB (i j : Fin n) (hij : i < j) (x : A i) (hx : x ∉ D i) :
      ((B i j x).card : ℚ) ≤ (Fintype.card (A j) : ℚ) * r i j := by
    have hnot : x ∉ H i j := by
      intro h
      exact hx (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, h⟩))
    have hs : (∑ k ∈ K i j, if x ∈ X k i then ((p j : ℚ)⁻¹)^(e k j) else 0) < r i j := by
      simpa only [H, heavyHubSet, Finset.mem_filter, Finset.mem_univ, true_and, not_le, r] using hnot
    calc
      _ ≤ ∑ k ∈ (K i j).filter (fun k => x ∈ X k i), ((X k j).card : ℚ) := by exact_mod_cast Finset.card_biUnion_le (s := (K i j).filter (fun k => x ∈ X k i)) (t := fun k => X k j)
      _ ≤ ∑ k ∈ (K i j).filter (fun k => x ∈ X k i), (Fintype.card (A j) : ℚ) * ((p j : ℚ)⁻¹)^(e k j) := Finset.sum_le_sum (fun k _ => hX k j)
      _ = (Fintype.card (A j) : ℚ) * ∑ k ∈ K i j, if x ∈ X k i then ((p j : ℚ)⁻¹)^(e k j) else 0 := by rw [← Finset.mul_sum, Finset.sum_filter]
      _ ≤ _ := mul_le_mul_of_nonneg_left hs.le (by positivity)
  have hbudget (i : Fin n) :
      d i + ∑ j ∈ Finset.univ.filter (fun j => j < i), r j i + δ i ≤ 1 := by
    dsimp [d, r]
    rw [← Finset.sum_div, ← add_div]
    exact hslack i
  by_contra hbound
  have hlt : (∑ k ∈ Finset.univ.filter (fun k => 3 ≤ (supp k).card),
      ∏ i, min 1 (((p i : ℚ)⁻¹)^(e k i) / δ i)) < 1 := lt_of_not_ge hbound
  let High := {k : κ // 3 ≤ (supp k).card}
  have hsum : (∑ k : High, ∏ i, min 1 (((p i : ℚ)⁻¹)^(e k.val i) / δ i)) < 1 := by
    have heq := Finset.sum_subtype (p := fun k => 3 ≤ (supp k).card) (F := inferInstance)
      (Finset.univ.filter (fun k => 3 ≤ (supp k).card)) (by intro k; simp)
      (fun k => ∏ i, min 1 (((p i : ℚ)⁻¹)^(e k i) / δ i))
    exact heq ▸ hlt
  obtain ⟨x, hxD, hxB, hxHigh⟩ := greedy_edge_box_avoidance (κ := High) A D B d r δ hδ hD hB hbudget
    (fun k => X k.val) (fun k i => ((p i : ℚ)⁻¹)^(e k.val i))
    (fun k i => by positivity) (fun k i => hX k.val i) hsum
  obtain ⟨k, hk⟩ := hcover x
  have hspos : 0 < (supp k).card := by
    obtain ⟨i, hi⟩ := he0 k
    exact Finset.card_pos.mpr ⟨i, (hmem k i).mpr hi⟩
  by_cases hhigh : 3 ≤ (supp k).card
  · exact hxHigh ⟨k, hhigh⟩ hk
  have hscard : (supp k).card = 1 ∨ (supp k).card = 2 := by omega
  rcases hscard with h1 | h2
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1
    exact hxD i (Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hk i⟩))
  · obtain ⟨i, j, hij, hs⟩ := Finset.card_eq_two.mp h2
    have hKi : k ∈ K i j := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact hxB i j hij (Finset.mem_biUnion.mpr ⟨k,
        Finset.mem_filter.mpr ⟨hKi, hk i⟩, hk j⟩)
    · have hKj : k ∈ K j i := by simpa [K, Finset.pair_comm] using hKi
      exact hxB j i hji (Finset.mem_biUnion.mpr ⟨k,
        Finset.mem_filter.mpr ⟨hKj, hk j⟩, hk i⟩)

#print axioms graph_conditioned_cover_bound
/-- Guaranteed fraction of admissible values in the graph-saturation greedy
construction, for a specified threshold allocation. -/
def graphAllowedFraction {n : ℕ} (p : Fin n → ℕ) (T : Fin n → Fin n → ℕ) (i : Fin n) : ℚ :=
  1 - (1 + (∑ j ∈ Finset.univ.filter (fun j => i < j), ((p i : ℚ)⁻¹)^(T i j-1)) +
    (∑ j ∈ Finset.univ.filter (fun j => j < i), (T j i : ℚ))) / (p i-1)

/-- The original strict row budget and integer column budget give a positive
admissible fraction; no cardinality of the coordinate spaces is used here. -/
theorem graphAllowedFraction_pos {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, 2 < p i)
    (T : Fin n → Fin n → ℕ)
    (hcolumn : ∀ j, (∑ i ∈ Finset.univ.filter (fun i => i < j), T i j) ≤ p j - 3)
    (hrow : ∀ i, (∑ j ∈ Finset.univ.filter (fun j => i < j), ((p i : ℚ)⁻¹)^(T i j-1)) < 1)
    (i : Fin n) : 0 < graphAllowedFraction p T i := by
  have hpQ : (2 : ℚ) < p i := by exact_mod_cast hp i
  have hc : (∑ j ∈ Finset.univ.filter (fun j => j < i), (T j i : ℚ)) ≤ (p i : ℚ)-3 := by
    have h := hcolumn i
    have hcast : ((p i - 3 : ℕ) : ℚ) = (p i : ℚ)-3 := Nat.cast_sub (by have := hp i; omega)
    have hh : (∑ j ∈ Finset.univ.filter (fun j => j < i), (T j i : ℚ)) ≤ ((p i - 3 : ℕ) : ℚ) := by
      exact_mod_cast h
    rwa [hcast] at hh
  have hquot :
      (1 + (∑ j ∈ Finset.univ.filter (fun j => i < j), ((p i : ℚ)⁻¹)^(T i j-1)) +
        (∑ j ∈ Finset.univ.filter (fun j => j < i), (T j i : ℚ))) / (p i-1) < 1 := by
    apply (div_lt_one (by linarith)).mpr
    have hh := hrow i
    linarith
  exact sub_pos.mpr hquot

/-- The conditional weight inequality with the explicit slack of a graph
threshold allocation. -/
theorem graph_conditioned_cover_bound_of_budgets {n : ℕ} {κ : Type*} [Fintype κ]
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (p : Fin n → ℕ) (hp : ∀ i, 2 < p i)
    (e : κ → Fin n → ℕ) (he : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (X : κ → ∀ i, Finset (A i))
    (hX : ∀ k i, ((X k i).card : ℚ) ≤ (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(e k i))
    (T : Fin n → Fin n → ℕ) (hT : ∀ i j, i < j → 1 ≤ T i j)
    (hcolumn : ∀ j, (∑ i ∈ Finset.univ.filter (fun i => i < j), T i j) ≤ p j - 3)
    (hrow : ∀ i, (∑ j ∈ Finset.univ.filter (fun j => i < j), ((p i : ℚ)⁻¹)^(T i j-1)) < 1)
    (hcover : ∀ x : ∀ i, A i, ∃ k, ∀ i, x i ∈ X k i) :
    1 ≤ ∑ k ∈ Finset.univ.filter (fun k => 3 ≤ (Finset.univ.filter (fun i => e k i ≠ 0)).card),
      ∏ i, min 1 (((p i : ℚ)⁻¹)^(e k i) / graphAllowedFraction p T i) := by
  exact graph_conditioned_cover_bound A p hp e he he0 X hX T hT (graphAllowedFraction p T)
    (graphAllowedFraction_pos p hp T hcolumn hrow)
    (fun i => by dsimp [graphAllowedFraction]; linarith) hcover

#print axioms graphAllowedFraction_pos
#print axioms graph_conditioned_cover_bound_of_budgets
end Erdos7GraphSaturation



/-! Arithmetic specialization of the quantitative graph-conditioned sieve. -/
namespace Erdos7GraphSaturation
open Erdos7Reduction Erdos7StarSieve Erdos7GraphBudget
set_option maxHeartbeats 3000000

/-- A positive, explicitly defined local slack for every finite sorted list of
odd primes. -/
def primeGraphAllowedFraction {n : ℕ} (p : Fin n → ℕ) : Fin n → ℚ :=
  graphAllowedFraction p (fun i j => edgeLevel (p i) (p j))

theorem primeGraphAllowedFraction_pos {n : ℕ} (p : Fin n → ℕ)
    (hp : ∀ i, (p i).Prime ∧ Odd (p i)) (hmono : StrictMono p) (i : Fin n) :
    0 < primeGraphAllowedFraction p i := by
  have hp2 (j : Fin n) : 2 < p j := by
    have := (hp j).1.two_le
    have := Nat.odd_iff.mp (hp j).2
    omega
  exact graphAllowedFraction_pos p hp2 _
    (edgeLevel_column_on_sorted_primes p hp hmono) (edgeLevel_row_on_sorted_primes p hp hmono) i

/-- In an arbitrary odd congruence cover with distinct exponent vectors, the
classes involving at least three primes have conditional graph weight at least
one. There is no upper bound on support sizes or prime-power exponents here. -/
theorem graph_conditioned_coordinate_cover_bound {n : ℕ} {κ : Type*} [Fintype κ]
    (p E : Fin n → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i)) (hmono : StrictMono p)
    (e : κ → Fin n → ℕ) (he : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (heE : ∀ k i, e k i ≤ E i) (a : κ → ℤ)
    (hcover : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k) :
    1 ≤ ∑ k ∈ Finset.univ.filter (fun k => 3 ≤ (Finset.univ.filter (fun i => e k i ≠ 0)).card),
      ∏ i, min 1 (((p i : ℚ)⁻¹)^(e k i) / primeGraphAllowedFraction p i) := by
  classical
  have hp2 (i : Fin n) : 2 < p i := by
    have := (hp i).1.two_le
    have := Nat.odd_iff.mp (hp i).2
    omega
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i).1 (hp j).1).mpr (fun h => hij (hmono.injective h))
  letI (i : Fin n) : NeZero (p i) := ⟨by have := hp2 i; omega⟩
  let A (i : Fin n) := ZMod (p i ^ E i)
  let f (k : κ) (i : Fin n) := ZMod.castHom (pow_dvd_pow (p i) (heE k i)) (ZMod (p i ^ e k i))
  let B (k : κ) (i : Fin n) := Finset.univ.filter (fun x : A i => f k i x = (a k : ZMod (p i ^ e k i)))
  have hBcard (k : κ) (i : Fin n) : ((B k i).card : ℚ) ≤
      (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(e k i) := by
    have hh := surjective_fiber_card_rat (f k i).toAddMonoidHom
      (ZMod.castHom_surjective (pow_dvd_pow (p i) (heE k i))) (a k)
    change ((B k i).card : ℚ) = _ at hh
    rw [hh]
    simp only [A, ZMod.card, Nat.cast_pow, div_eq_mul_inv, inv_pow]
    exact le_rfl
  have hbox : ∀ x : ∀ i, A i, ∃ k, ∀ i, x i ∈ B k i := by
    intro x
    let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) (fun i => p i ^ E i) Finset.univ
      (fun i _ => pow_ne_zero _ (NeZero.ne _))
      (fun i _ j _ hij => (hcop hij).pow _ _)
    have hz (i : Fin n) : (z.val : A i) = x i := by
      rw [← ZMod.natCast_zmod_val (x i)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
    obtain ⟨k, hk⟩ := hcover (z.val : ℤ)
    refine ⟨k, ?_⟩
    intro i
    have hpi : p i ^ e k i ∣ ∏ j, p j ^ e k j :=
      Finset.dvd_prod_of_mem (fun j => p j ^ e k j) (Finset.mem_univ i)
    have hpi' : ((p i ^ e k i : ℕ) : ℤ) ∣ ((∏ j, p j ^ e k j : ℕ) : ℤ) := by exact_mod_cast hpi
    have hqi := hpi'.trans hk
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hz i, map_natCast]
    symm
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (a k) (z.val : ℤ) (p i ^ e k i)).mpr hqi
  exact graph_conditioned_cover_bound_of_budgets A p hp2 e he he0 B hBcard
    (fun i j => edgeLevel (p i) (p j))
    (fun i j hij => edgeLevel_ge_one (p i) (p j) (hp i).1.one_lt (hmono hij))
    (edgeLevel_column_on_sorted_primes p hp hmono) (edgeLevel_row_on_sorted_primes p hp hmono) hbox

#print axioms primeGraphAllowedFraction_pos
#print axioms graph_conditioned_coordinate_cover_bound
end Erdos7GraphSaturation



/-! A kernel-checked finite distortion step. This does not settle Erdős 7. -/
namespace Erdos7Distortion

set_option maxHeartbeats 2000000

/-- Proportion of mass retained on an excluded fibre by capped distortion. -/
def residual (c α : ℚ) : ℚ := max 0 (c * α - (c - 1))

/-- The density on an excluded or an allowed point of a fibre. Division by zero
at an empty part is harmless; its contribution to every finite sum is zero. -/
def density (c α : ℚ) (excluded : Bool) : ℚ :=
  if excluded then residual c α / α else min c (1 / (1 - α))

lemma residual_nonneg (c α : ℚ) : 0 ≤ residual c α := le_max_left _ _

lemma residual_le_fraction {c α : ℚ} (hc : 1 ≤ c) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    residual c α ≤ α := by
  apply max_le hα0
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hα1)]

lemma density_nonneg {c α : ℚ} (hc : 1 ≤ c) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (b : Bool) :
    0 ≤ density c α b := by
  cases b
  · exact le_min (by linarith) (div_nonneg (by norm_num) (by linarith))
  · exact div_nonneg (residual_nonneg _ _) hα0

lemma excluded_density_le_one {c α : ℚ} (hc : 1 ≤ c) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    density c α true ≤ 1 := by
  by_cases hα : α = 0
  · simp [density, hα]
  · have hpos : 0 < α := lt_of_le_of_ne hα0 (Ne.symm hα)
    exact (div_le_one hpos).mpr (residual_le_fraction hc hα0 hα1)

lemma density_le_cap {c α : ℚ} (hc : 1 ≤ c) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (b : Bool) :
    density c α b ≤ c := by
  cases b
  · exact min_le_left _ _
  · exact (excluded_density_le_one hc hα0 hα1).trans hc

/-- The density is also bounded by one plus the cap times the excluded fraction. -/
lemma density_le_adaptive {c α : ℚ} (hc : 1 ≤ c) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (b : Bool) :
    density c α b ≤ 1 + c * α := by
  cases b
  · change min c (1 / (1 - α)) ≤ _
    by_cases h : c * (1 - α) ≤ 1
    · exact (min_le_left _ _).trans (by nlinarith)
    · have hpos : 0 < 1 - α := by
        have := not_le.mp h
        by_contra! hn
        have hz : 1 - α = 0 := by linarith
        rw [hz, mul_zero] at this
        norm_num at this
      apply (min_le_right _ _).trans
      apply (div_le_iff₀ hpos).mpr
      have hh : 0 ≤ α * (c * (1 - α) - 1) :=
        mul_nonneg hα0 (by have := not_le.mp h; linarith)
      nlinarith
  · apply (excluded_density_le_one hc hα0 hα1).trans
    nlinarith

lemma excluded_density_mass {c α : ℚ} (hc : 1 ≤ c) (hα0 : 0 ≤ α) :
    α * density c α true = residual c α := by
  by_cases hα : α = 0
  · simp only [hα, zero_mul, density, residual, mul_zero, zero_sub]
    rw [max_eq_left (by linarith)]
  · change α * (residual c α / α) = residual c α
    field_simp

/-- The distorted fibre has the same total mass as the uniform fibre. -/
lemma density_normalization {c α : ℚ} (hc : 1 ≤ c) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    α * density c α true + (1 - α) * density c α false = 1 := by
  rw [excluded_density_mass hc hα0]
  change residual c α + (1 - α) * min c (1 / (1 - α)) = 1
  by_cases hα : α = 1
  · subst α
    simp [residual]
  · have hpos : 0 < 1 - α := by exact sub_pos.mpr (lt_of_le_of_ne hα1 hα)
    by_cases h : c * (1 - α) ≤ 1
    · have hmin : min c (1 / (1 - α)) = c := min_eq_left ((le_div_iff₀ hpos).mpr h)
      rw [hmin, residual, max_eq_right (by nlinarith)]
      ring
    · have hmin : min c (1 / (1 - α)) = 1 / (1 - α) :=
        min_eq_right ((div_le_iff₀ hpos).mpr (le_of_lt (not_le.mp h)))
      rw [hmin, residual, max_eq_left (by have := not_le.mp h; nlinarith), zero_add]
      field_simp

/-- A universal second-moment majorant for the residual mass. -/
lemma residual_le_second_moment {c α : ℚ} (hc : 1 < c) :
    residual c α ≤ c ^ 2 / (4 * (c - 1)) * α ^ 2 := by
  have hden : 0 < 4 * (c - 1) := by linarith
  apply max_le
  · positivity
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).mpr
    nlinarith [sq_nonneg (c * α - 2 * (c - 1))]

/-- A one-step self-bound for the density; iterating it gives nonnegative
polynomial upper bounds of every order. -/
lemma density_le_one_add_self {c α : ℚ} (hc : 1 ≤ c) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (b : Bool) :
    density c α b ≤ 1 + α * density c α b := by
  have hd0 := density_nonneg hc hα0 hα1 b
  cases b
  · by_cases ha : α = 1
    · rw [ha]; nlinarith
    · have hpos : 0 < 1 - α := sub_pos.mpr (lt_of_le_of_ne hα1 ha)
      have hd : density c α false ≤ 1 / (1 - α) := min_le_right _ _
      have hh := (le_div_iff₀ hpos).mp hd
      nlinarith
  · have hd := excluded_density_le_one hc hα0 hα1
    nlinarith [mul_nonneg hα0 hd0]

/-- The cap corresponds to order zero; order one is the adaptive estimate.
All coefficients in these majorants are nonnegative. -/
lemma density_le_polynomial {c α : ℚ} (hc : 1 ≤ c) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (b : Bool) (R : ℕ) :
    density c α b ≤ (∑ j ∈ Finset.range R, α ^ j) + c * α ^ R := by
  induction R with
  | zero => simpa using density_le_cap hc hα0 hα1 b
  | succ R ih =>
    have hm := mul_le_mul_of_nonneg_left ih hα0
    have hd := density_le_one_add_self hc hα0 hα1 b
    rw [geom_sum_succ, pow_succ]
    nlinarith

section Finite
variable {Y : Type*} [Fintype Y] [Nonempty Y] [DecidableEq Y]

/-- Uniform proportion of a finite coordinate fibre. -/
def fraction (B : Finset Y) : ℚ := (B.card : ℚ) / Fintype.card Y

lemma card_pos_rat : (0 : ℚ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos

lemma fraction_nonneg (B : Finset Y) : 0 ≤ fraction B := by
  exact div_nonneg (Nat.cast_nonneg _) card_pos_rat.le

lemma fraction_le_one (B : Finset Y) : fraction B ≤ 1 := by
  apply (div_le_one card_pos_rat).mpr
  exact_mod_cast Finset.card_le_univ B

lemma fraction_mul_card (B : Finset Y) : fraction B * Fintype.card Y = B.card := by
  exact div_mul_cancel₀ _ card_pos_rat.ne'

/-- The exact finite sum of the density is the number of fibre points. -/
lemma sum_density (B : Finset Y) {c : ℚ} (hc : 1 ≤ c) :
    (∑ y : Y, density c (fraction B) (decide (y ∈ B))) = Fintype.card Y := by
  classical
  let α := fraction B
  have hpoint (y : Y) : density c α (decide (y ∈ B)) =
      if y ∈ B then density c α true else density c α false := by
    split_ifs with h <;> simp [h]
  have hsum : (∑ y : Y, density c α (decide (y ∈ B))) =
      (B.card : ℚ) * density c α true + ((Fintype.card Y : ℚ) - B.card) * density c α false := by
    simp_rw [hpoint]
    rw [Finset.sum_ite]
    have hB : Finset.univ.filter (fun y : Y => y ∈ B) = B := by ext y; simp
    have hnot : Finset.univ.filter (fun y : Y => y ∉ B) = Finset.univ \ B := by ext y; simp
    rw [hB, hnot]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.univ \ B).card : ℚ) = (Fintype.card Y : ℚ) - B.card := by
      have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
      have hq : ((Finset.univ \ B).card : ℚ) + B.card = Fintype.card Y := by exact_mod_cast hh
      linarith
    rw [hcard]
  rw [hsum]
  have hm := density_normalization hc (fraction_nonneg B) (fraction_le_one B)
  have hb := fraction_mul_card B
  dsimp only [α] at *
  rw [← hb]
  calc
    _ = (Fintype.card Y : ℚ) *
        (fraction B * density c (fraction B) true + (1 - fraction B) * density c (fraction B) false) := by ring
    _ = _ := by rw [hm, mul_one]

lemma sum_density_on_excluded (B : Finset Y) {c : ℚ} (hc : 1 ≤ c) :
    (∑ y ∈ B, density c (fraction B) (decide (y ∈ B))) =
      (Fintype.card Y : ℚ) * residual c (fraction B) := by
  classical
  have hs : (∑ y ∈ B, density c (fraction B) (decide (y ∈ B))) =
      (B.card : ℚ) * density c (fraction B) true := by
    simp only [Finset.sum_congr rfl (show ∀ y ∈ B,
      density c (fraction B) (decide (y ∈ B)) = density c (fraction B) true from
        fun y hy => by simp [hy]), Finset.sum_const, nsmul_eq_mul]
  rw [hs, ← fraction_mul_card B]
  have hm := excluded_density_mass hc (fraction_nonneg B)
  nlinarith [congrArg (fun z : ℚ => (Fintype.card Y : ℚ) * z) hm]

/-- Extend finite old weights by one uniformly lifted and distorted coordinate. -/
def step {Ω : Type*} (μ : Ω → ℚ) (B : Ω → Finset Y) (c : ℚ) (z : Ω × Y) : ℚ :=
  μ z.1 * density c (fraction (B z.1)) (decide (z.2 ∈ B z.1)) / Fintype.card Y

lemma step_nonneg {Ω : Type*} (μ : Ω → ℚ) (hμ : ∀ x, 0 ≤ μ x) (B : Ω → Finset Y)
    {c : ℚ} (hc : 1 ≤ c) (z : Ω × Y) : 0 ≤ step μ B c z := by
  apply div_nonneg _ card_pos_rat.le
  exact mul_nonneg (hμ z.1) (density_nonneg hc (fraction_nonneg _) (fraction_le_one _) _)

/-- All old-coordinate marginal weights are exactly preserved. -/
lemma step_marginal {Ω : Type*} (μ : Ω → ℚ) (B : Ω → Finset Y) {c : ℚ} (hc : 1 ≤ c) (x : Ω) :
    (∑ y : Y, step μ B c (x,y)) = μ x := by
  simp only [step]
  rw [← Finset.sum_div, ← Finset.mul_sum, sum_density (B x) hc]
  exact mul_div_cancel_right₀ _ card_pos_rat.ne'

lemma step_total {Ω : Type*} [Fintype Ω] (μ : Ω → ℚ) (B : Ω → Finset Y) {c : ℚ} (hc : 1 ≤ c) :
    (∑ z : Ω × Y, step μ B c z) = ∑ x : Ω, μ x := by
  rw [Fintype.sum_prod_type]
  simp_rw [step_marginal μ B hc]

lemma step_on_excluded {Ω : Type*} (μ : Ω → ℚ) (B : Ω → Finset Y) {c : ℚ} (hc : 1 ≤ c) (x : Ω) :
    (∑ y ∈ B x, step μ B c (x,y)) = μ x * residual c (fraction (B x)) := by
  simp only [step]
  rw [← Finset.sum_div, ← Finset.mul_sum, sum_density_on_excluded (B x) hc]
  field_simp

lemma step_le_cap {Ω : Type*} (μ : Ω → ℚ) (hμ : ∀ x, 0 ≤ μ x) (B : Ω → Finset Y)
    {c : ℚ} (hc : 1 ≤ c) (z : Ω × Y) :
    step μ B c z ≤ c * μ z.1 / Fintype.card Y := by
  apply div_le_div_of_nonneg_right _ card_pos_rat.le
  have hh := mul_le_mul_of_nonneg_left
    (density_le_cap hc (fraction_nonneg (B z.1)) (fraction_le_one (B z.1)) (decide (z.2 ∈ B z.1))) (hμ z.1)
  nlinarith

lemma step_le_adaptive {Ω : Type*} (μ : Ω → ℚ) (hμ : ∀ x, 0 ≤ μ x) (B : Ω → Finset Y)
    {c : ℚ} (hc : 1 ≤ c) (z : Ω × Y) :
    step μ B c z ≤ (1 + c * fraction (B z.1)) * μ z.1 / Fintype.card Y := by
  apply div_le_div_of_nonneg_right _ card_pos_rat.le
  have hh := mul_le_mul_of_nonneg_left
    (density_le_adaptive hc (fraction_nonneg (B z.1)) (fraction_le_one (B z.1)) (decide (z.2 ∈ B z.1))) (hμ z.1)
  nlinarith

/-- Sum an arbitrary old-coordinate upper bound for the new density over a
rectangle. This is the basic residue-class estimate in the distortion sieve. -/
lemma step_rectangle_bound {Ω : Type*} (μ : Ω → ℚ) (hμ : ∀ x, 0 ≤ μ x)
    (B : Ω → Finset Y) (c : ℚ) (D : Finset Ω) (T : Finset Y) (u : Ω → ℚ)
    (hu : ∀ x ∈ D, ∀ y ∈ T, density c (fraction (B x)) (decide (y ∈ B x)) ≤ u x) :
    (∑ x ∈ D, ∑ y ∈ T, step μ B c (x,y)) ≤
      ((T.card : ℚ) / Fintype.card Y) * ∑ x ∈ D, μ x * u x := by
  calc
    _ ≤ ∑ x ∈ D, ∑ _y ∈ T, μ x * u x / Fintype.card Y := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hu x hx y hy) (hμ x)) card_pos_rat.le
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

/-- Both the cap and the adaptive estimate can be used for each old rectangle,
then the smaller of the resulting bounds can be retained. -/
lemma step_rectangle_min {Ω : Type*} (μ : Ω → ℚ) (hμ : ∀ x, 0 ≤ μ x)
    (B : Ω → Finset Y) {c : ℚ} (hc : 1 ≤ c) (D : Finset Ω) (T : Finset Y) :
    (∑ x ∈ D, ∑ y ∈ T, step μ B c (x,y)) ≤
      ((T.card : ℚ) / Fintype.card Y) *
        min (c * ∑ x ∈ D, μ x) ((∑ x ∈ D, μ x) + c * ∑ x ∈ D, μ x * fraction (B x)) := by
  have hcap := step_rectangle_bound μ hμ B c D T (fun _ => c)
    (fun x _ y _ => density_le_cap hc (fraction_nonneg _) (fraction_le_one _) _)
  have hadapt := step_rectangle_bound μ hμ B c D T (fun x => 1 + c * fraction (B x))
    (fun x _ y _ => density_le_adaptive hc (fraction_nonneg _) (fraction_le_one _) _)
  have hcap' : (∑ x ∈ D, μ x * c) = c * ∑ x ∈ D, μ x := by rw [← Finset.sum_mul, mul_comm]
  have hadapt' : (∑ x ∈ D, μ x * (1 + c * fraction (B x))) =
      (∑ x ∈ D, μ x) + c * ∑ x ∈ D, μ x * fraction (B x) := by
    simp_rw [mul_add, mul_one, show ∀ x, μ x * (c * fraction (B x)) = c * (μ x * fraction (B x)) by intro x; ring]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hcap'] at hcap
  rw [hadapt'] at hadapt
  rw [mul_min_of_nonneg _ _ (div_nonneg (Nat.cast_nonneg _) card_pos_rat.le)]
  exact le_min hcap hadapt

/-- Exact total residual mass on the new excluded fibres. -/
lemma step_excluded_total {Ω : Type*} [Fintype Ω] (μ : Ω → ℚ) (B : Ω → Finset Y)
    {c : ℚ} (hc : 1 ≤ c) :
    (∑ x : Ω, ∑ y ∈ B x, step μ B c (x,y)) = ∑ x : Ω, μ x * residual c (fraction (B x)) := by
  simp_rw [step_on_excluded μ B hc]

/-- A genuine finite second-moment distortion bound, with no probabilistic
independence assumption and no infinite-tail approximation. -/
lemma step_excluded_second_moment {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℚ) (hμ : ∀ x, 0 ≤ μ x) (B : Ω → Finset Y) {c : ℚ} (hc : 1 < c) :
    (∑ x : Ω, ∑ y ∈ B x, step μ B c (x,y)) ≤
      c ^ 2 / (4 * (c - 1)) * ∑ x : Ω, μ x * fraction (B x) ^ 2 := by
  rw [step_excluded_total μ B hc.le, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have hh := mul_le_mul_of_nonneg_left (residual_le_second_moment (α := fraction (B x)) hc) (hμ x)
  nlinarith

end Finite

#print axioms density_normalization
#print axioms residual_le_second_moment
#print axioms step_total
#print axioms step_le_adaptive
#print axioms density_le_polynomial
#print axioms step_rectangle_min
#print axioms step_excluded_second_moment
end Erdos7Distortion



/-! Distortion by resampling a coordinate of a fixed finite product. -/
namespace Erdos7Distortion

set_option maxHeartbeats 3000000

section Product
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

/-- Split off one coordinate, placing the other coordinates first. -/
def splitCoordinate (i : ι) : (∀ j, A j) ≃ (∀ j : {j // j ≠ i}, A j.val) × A i :=
  (Equiv.piSplitAt i A).trans (Equiv.prodComm _ _)

/-- Reconstruct a point from all other coordinates and the selected coordinate. -/
def joinCoordinate (i : ι) (z : ∀ j : {j // j ≠ i}, A j.val) (v : A i) : ∀ j, A j :=
  (splitCoordinate A i).symm (z,v)

lemma split_join (i : ι) (z : ∀ j : {j // j ≠ i}, A j.val) (v : A i) :
    splitCoordinate A i (joinCoordinate A i z v) = (z,v) :=
  (splitCoordinate A i).apply_symm_apply _

lemma join_split (i : ι) (x : ∀ j, A j) :
    joinCoordinate A i (splitCoordinate A i x).1 (splitCoordinate A i x).2 = x :=
  (splitCoordinate A i).symm_apply_apply x

lemma joinCoordinate_self (i : ι) (z : ∀ j : {j // j ≠ i}, A j.val) (v : A i) :
    joinCoordinate A i z v i = v := by
  simp [joinCoordinate, splitCoordinate]

lemma joinCoordinate_of_ne (i : ι) (z : ∀ j : {j // j ≠ i}, A j.val) (v : A i) (j : ι) (hj : j ≠ i) :
    joinCoordinate A i z v j = z ⟨j,hj⟩ := by
  simp [joinCoordinate, splitCoordinate, hj]

lemma splitCoordinate_update (i : ι) (x : ∀ j, A j) (v : A i) :
    splitCoordinate A i (Function.update x i v) = ((splitCoordinate A i x).1, v) := by
  apply Prod.ext
  · funext j
    simp [splitCoordinate, Function.update_of_ne j.property]
  · simp [splitCoordinate]

lemma joinCoordinate_update (i : ι) (z : ∀ j : {j // j ≠ i}, A j.val) (u v : A i) :
    Function.update (joinCoordinate A i z u) i v = joinCoordinate A i z v := by
  apply (splitCoordinate A i).injective
  rw [splitCoordinate_update, split_join, split_join]

lemma sum_splitCoordinate (i : ι) (f : (∀ j, A j) → ℚ) :
    (∑ x : ∀ j, A j, f x) = ∑ z : ∀ j : {j // j ≠ i}, A j.val, ∑ v : A i, f (joinCoordinate A i z v) := by
  rw [← (splitCoordinate A i).symm.sum_comp f, Fintype.sum_prod_type]
  rfl

/-- The old marginal on all coordinates except `i`. -/
def coordinateMarginal (i : ι) (μ : (∀ j, A j) → ℚ) (z : ∀ j : {j // j ≠ i}, A j.val) : ℚ :=
  ∑ v : A i, μ (joinCoordinate A i z v)

/-- Section of an excluded event in one coordinate. -/
def coordinateFibre (i : ι) (B : Finset (∀ j, A j)) (z : ∀ j : {j // j ≠ i}, A j.val) : Finset (A i) :=
  Finset.univ.filter (fun v => joinCoordinate A i z v ∈ B)

/-- Excluded fraction on the section through a full point. -/
def coordinateFraction (i : ι) (B : Finset (∀ j, A j)) (x : ∀ j, A j) : ℚ :=
  fraction (coordinateFibre A i B (splitCoordinate A i x).1)

/-- Resample coordinate `i` from a capped distorted uniform distribution.
Unlike multiplication by a density, this definition works for arbitrary old
weights; no conditional uniformity assumption is needed. -/
def resample (i : ι) (μ : (∀ j, A j) → ℚ) (B : Finset (∀ j, A j)) (c : ℚ) (x : ∀ j, A j) : ℚ :=
  step (coordinateMarginal A i μ) (coordinateFibre A i B) c (splitCoordinate A i x)

lemma resample_join (i : ι) (μ : (∀ j, A j) → ℚ) (B : Finset (∀ j, A j)) (c : ℚ)
    (z : ∀ j : {j // j ≠ i}, A j.val) (v : A i) :
    resample A i μ B c (joinCoordinate A i z v) =
      step (coordinateMarginal A i μ) (coordinateFibre A i B) c (z,v) := by
  simp [resample, split_join]

lemma coordinateMarginal_nonneg (i : ι) (μ : (∀ j, A j) → ℚ) (hμ : ∀ x, 0 ≤ μ x)
    (z : ∀ j : {j // j ≠ i}, A j.val) : 0 ≤ coordinateMarginal A i μ z :=
  Finset.sum_nonneg (fun v _ => hμ _)

lemma resample_nonneg (i : ι) (μ : (∀ j, A j) → ℚ) (hμ : ∀ x, 0 ≤ μ x)
    (B : Finset (∀ j, A j)) {c : ℚ} (hc : 1 ≤ c) (x : ∀ j, A j) : 0 ≤ resample A i μ B c x :=
  step_nonneg _ (coordinateMarginal_nonneg A i μ hμ) _ hc _

lemma resample_total (i : ι) (μ : (∀ j, A j) → ℚ) (B : Finset (∀ j, A j)) {c : ℚ} (hc : 1 ≤ c) :
    (∑ x : ∀ j, A j, resample A i μ B c x) = ∑ x : ∀ j, A j, μ x := by
  rw [sum_splitCoordinate A i, sum_splitCoordinate A i μ]
  simp_rw [resample_join, step_marginal _ _ hc]
  rfl

/-- Resampling preserves every test function independent of the coordinate
being resampled, including all events processed at earlier coordinates. -/
lemma resample_preserves_test (i : ι) (μ : (∀ j, A j) → ℚ) (B : Finset (∀ j, A j))
    {c : ℚ} (hc : 1 ≤ c) (f : (∀ j, A j) → ℚ)
    (hf : ∀ x v, f (Function.update x i v) = f x) :
    (∑ x : ∀ j, A j, resample A i μ B c x * f x) = ∑ x : ∀ j, A j, μ x * f x := by
  classical
  let u : A i := Classical.choice inferInstance
  have hinv (z : ∀ j : {j // j ≠ i}, A j.val) (v : A i) :
      f (joinCoordinate A i z v) = f (joinCoordinate A i z u) := by
    simpa only [joinCoordinate_update] using hf (joinCoordinate A i z u) v
  rw [sum_splitCoordinate A i, sum_splitCoordinate A i]
  simp_rw [hinv, resample_join, ← Finset.sum_mul, step_marginal _ _ hc]
  rfl

/-- A coordinate rectangle is charged by its uniform proportion times the cap;
its other-coordinate test function may be arbitrary and history dependent. -/
lemma resample_coordinate_test_bound (i : ι) (μ : (∀ j, A j) → ℚ) (hμ : ∀ x, 0 ≤ μ x)
    (B : Finset (∀ j, A j)) {c : ℚ} (hc : 1 ≤ c) (T : Finset (A i))
    (f : (∀ j, A j) → ℚ) (hf0 : ∀ x, 0 ≤ f x)
    (hf : ∀ x v, f (Function.update x i v) = f x) :
    (∑ x : ∀ j, A j, resample A i μ B c x * (if x i ∈ T then f x else 0)) ≤
      (c * ((T.card : ℚ) / Fintype.card (A i))) * ∑ x : ∀ j, A j, μ x * f x := by
  classical
  let u : A i := Classical.choice inferInstance
  have hinv (z : ∀ j : {j // j ≠ i}, A j.val) (v : A i) :
      f (joinCoordinate A i z v) = f (joinCoordinate A i z u) := by
    simpa only [joinCoordinate_update] using hf (joinCoordinate A i z u) v
  rw [sum_splitCoordinate A i, sum_splitCoordinate A i]
  simp_rw [joinCoordinate_self, hinv, resample_join]
  calc
    _ ≤ ∑ z : ∀ j : {j // j ≠ i}, A j.val,
        ∑ v : A i, (c * coordinateMarginal A i μ z / Fintype.card (A i)) *
          (if v ∈ T then f (joinCoordinate A i z u) else 0) := by
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro v _
      apply mul_le_mul_of_nonneg_right
        (step_le_cap _ (coordinateMarginal_nonneg A i μ hμ) _ hc (z,v))
      split_ifs <;> [exact hf0 _; exact le_rfl]
    _ = _ := by
      simp only [mul_ite, mul_zero, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      simp_rw [← Finset.sum_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      dsimp [coordinateMarginal]
      ring

/-- Exact mass of a newly processed excluded event. -/
lemma resample_excluded (i : ι) (μ : (∀ j, A j) → ℚ) (B : Finset (∀ j, A j))
    {c : ℚ} (hc : 1 ≤ c) :
    (∑ x ∈ B, resample A i μ B c x) =
      ∑ x : ∀ j, A j, μ x * residual c (coordinateFraction A i B x) := by
  classical
  have hsum : (∑ x ∈ B, resample A i μ B c x) =
      ∑ x : ∀ j, A j, if x ∈ B then resample A i μ B c x else 0 := by simp
  rw [hsum, sum_splitCoordinate A i, sum_splitCoordinate A i]
  simp_rw [resample_join]
  have hfrac (z : ∀ j : {j // j ≠ i}, A j.val) (v : A i) :
      coordinateFraction A i B (joinCoordinate A i z v) = fraction (coordinateFibre A i B z) := by
    simp [coordinateFraction, split_join]
  simp_rw [hfrac, ← Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  have hh := step_on_excluded (coordinateMarginal A i μ) (coordinateFibre A i B) hc z
  simpa only [coordinateFibre, Finset.sum_filter] using hh

lemma resample_excluded_second_moment (i : ι) (μ : (∀ j, A j) → ℚ) (hμ : ∀ x, 0 ≤ μ x)
    (B : Finset (∀ j, A j)) {c : ℚ} (hc : 1 < c) :
    (∑ x ∈ B, resample A i μ B c x) ≤
      c ^ 2 / (4 * (c - 1)) * ∑ x : ∀ j, A j, μ x * coordinateFraction A i B x ^ 2 := by
  rw [resample_excluded A i μ B hc.le, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have hh := mul_le_mul_of_nonneg_left
    (residual_le_second_moment (α := coordinateFraction A i B x) hc) (hμ x)
  nlinarith

end Product
#print axioms resample_total
#print axioms resample_preserves_test
#print axioms resample_coordinate_test_bound
#print axioms resample_excluded_second_moment
end Erdos7Distortion



/-! A finite tower of coordinate resamplings and its covering inequality. -/
namespace Erdos7Distortion

set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

section Cylinders
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

/-- Indicator of a box restricting only the coordinates in a specified set. -/
def boxIndicator (S : Finset ι) (X : ∀ i, Finset (A i)) (x : ∀ i, A i) : ℚ :=
  if ∀ i ∈ S, x i ∈ X i then 1 else 0

lemma boxIndicator_nonneg (S : Finset ι) (X : ∀ i, Finset (A i)) (x : ∀ i, A i) :
    0 ≤ boxIndicator A S X x := by
  unfold boxIndicator
  split_ifs <;> norm_num

lemma boxIndicator_empty (X : ∀ i, Finset (A i)) (x : ∀ i, A i) :
    boxIndicator A ∅ X x = 1 := by simp [boxIndicator]

lemma boxIndicator_update (S : Finset ι) (X : ∀ i, Finset (A i)) (i : ι) (hi : i ∉ S)
    (x : ∀ i, A i) (v : A i) :
    boxIndicator A S X (Function.update x i v) = boxIndicator A S X x := by
  have heq : (∀ j ∈ S, Function.update x i v j ∈ X j) ↔ ∀ j ∈ S, x j ∈ X j := by
    apply forall_congr'
    intro j
    by_cases hj : j ∈ S
    · have hji : j ≠ i := by intro h; subst j; exact hi hj
      simp only [Function.update_of_ne hji]
    · simp [hj]
  simp only [boxIndicator, heq]

lemma boxIndicator_erase (S : Finset ι) (X : ∀ i, Finset (A i)) (i : ι) (hi : i ∈ S)
    (x : ∀ i, A i) :
    boxIndicator A S X x = if x i ∈ X i then boxIndicator A (S.erase i) X x else 0 := by
  have heq : (∀ j ∈ S, x j ∈ X j) ↔ x i ∈ X i ∧ ∀ j ∈ S.erase i, x j ∈ X j := by
    constructor
    · intro h
      exact ⟨h i hi, fun j hj => h j (Finset.mem_of_mem_erase hj)⟩
    · rintro ⟨hiX,h⟩ j hj
      by_cases hji : j = i
      · subst j; exact hiX
      · exact h j (Finset.mem_erase.mpr ⟨hji,hj⟩)
  simp only [boxIndicator, heq, ite_and]

/-- Weight of a cylinder under arbitrary finite rational weights. -/
def boxMass (μ : (∀ i, A i) → ℚ) (S : Finset ι) (X : ∀ i, Finset (A i)) : ℚ :=
  ∑ x : ∀ i, A i, μ x * boxIndicator A S X x

lemma resample_boxMass_of_not_mem (i : ι) (μ : (∀ j, A j) → ℚ) (B : Finset (∀ j, A j))
    {c : ℚ} (hc : 1 ≤ c) (S : Finset ι) (hi : i ∉ S) (X : ∀ j, Finset (A j)) :
    boxMass A (resample A i μ B c) S X = boxMass A μ S X :=
  resample_preserves_test A i μ B hc (boxIndicator A S X) (boxIndicator_update A S X i hi)

lemma resample_boxMass_of_mem (i : ι) (μ : (∀ j, A j) → ℚ) (hμ : ∀ x, 0 ≤ μ x)
    (B : Finset (∀ j, A j)) {c : ℚ} (hc : 1 ≤ c) (S : Finset ι) (hi : i ∈ S)
    (X : ∀ j, Finset (A j)) :
    boxMass A (resample A i μ B c) S X ≤ (c * fraction (X i)) * boxMass A μ (S.erase i) X := by
  have hh := resample_coordinate_test_bound A i μ hμ B hc (X i)
    (boxIndicator A (S.erase i) X) (boxIndicator_nonneg A _ X)
    (boxIndicator_update A _ X i (Finset.notMem_erase _ _))
  simpa only [boxMass, boxIndicator_erase A S X i hi, fraction] using hh

end Cylinders

section Tower
variable {n : ℕ}
variable (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

/-- Start from uniform weights and successively resample the listed coordinates.
After the final coordinate the weights are left unchanged. -/
def towerWeights (B : Fin n → Finset (∀ i, A i)) (c : Fin n → ℚ) : ℕ → (∀ i, A i) → ℚ
  | 0 => fun _ => 1 / Fintype.card (∀ i, A i)
  | t+1 => if h : t < n then resample A ⟨t,h⟩ (towerWeights B c t) (B ⟨t,h⟩) (c ⟨t,h⟩)
      else towerWeights B c t

lemma towerWeights_succ (B : Fin n → Finset (∀ i, A i)) (c : Fin n → ℚ) (i : Fin n) :
    towerWeights A B c (i.val + 1) = resample A i (towerWeights A B c i.val) (B i) (c i) := by
  simp only [towerWeights, i.isLt, ↓reduceDIte]

lemma towerWeights_nonneg (B : Fin n → Finset (∀ i, A i)) (c : Fin n → ℚ)
    (hc : ∀ i, 1 ≤ c i) (t : ℕ) (x : ∀ i, A i) : 0 ≤ towerWeights A B c t x := by
  induction t generalizing x with
  | zero => exact div_nonneg (by norm_num) (Nat.cast_nonneg _)
  | succ t ih =>
    simp only [towerWeights]
    split_ifs with h
    · exact resample_nonneg A ⟨t,h⟩ _ (fun x => by exact ih x) _ (hc _) x
    · exact ih x

lemma towerWeights_total (B : Fin n → Finset (∀ i, A i)) (c : Fin n → ℚ)
    (hc : ∀ i, 1 ≤ c i) (t : ℕ) : (∑ x : ∀ i, A i, towerWeights A B c t x) = 1 := by
  induction t with
  | zero =>
    simp only [towerWeights, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hN : (Fintype.card (∀ i, A i) : ℚ) ≠ 0 := ne_of_gt card_pos_rat
    field_simp
  | succ t ih =>
    simp only [towerWeights]
    split_ifs with h
    · exact (resample_total A ⟨t,h⟩ _ _ (hc _)).trans ih
    · exact ih

/-- Every cylinder supported in the processed coordinates has at most the
product of its uniform coordinate densities and their individual caps. -/
theorem towerWeights_box_bound (B : Fin n → Finset (∀ i, A i)) (c : Fin n → ℚ)
    (hc : ∀ i, 1 ≤ c i) (t : ℕ) (ht : t ≤ n)
    (S : Finset (Fin n)) (hS : ∀ i ∈ S, i.val < t) (X : ∀ i, Finset (A i)) :
    boxMass A (towerWeights A B c t) S X ≤ ∏ i ∈ S, c i * fraction (X i) := by
  induction t generalizing S with
  | zero =>
    have hs : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun i hi => by have := hS i hi; omega)
    subst S
    simpa only [boxMass, boxIndicator_empty, mul_one, Finset.prod_empty] using
      (towerWeights_total A B c hc 0).le
  | succ t ih =>
    let i : Fin n := ⟨t, by omega⟩
    have hrec : towerWeights A B c (t+1) = resample A i (towerWeights A B c t) (B i) (c i) :=
      towerWeights_succ A B c i
    rw [hrec]
    by_cases hi : i ∈ S
    · have hSerase : ∀ j ∈ S.erase i, j.val < t := by
        intro j hj
        have hne : j.val ≠ t := by intro h; exact (Finset.mem_erase.mp hj).1 (Fin.ext h)
        have hh := hS j (Finset.mem_of_mem_erase hj)
        omega
      have hb := ih (by omega) (S.erase i) hSerase
      have hh := resample_boxMass_of_mem A i _ (towerWeights_nonneg A B c hc t) (B i) (hc i) S hi X
      apply hh.trans
      have hnon : 0 ≤ c i * fraction (X i) := mul_nonneg (by have := hc i; linarith) (fraction_nonneg _)
      have hmul := mul_le_mul_of_nonneg_left hb hnon
      rwa [Finset.mul_prod_erase S (fun j => c j * fraction (X j)) hi] at hmul
    · rw [resample_boxMass_of_not_mem A i _ _ (hc i) S hi]
      apply ih (by omega) S
      intro j hj
      have hne : j.val ≠ t := by intro h; exact hi (by convert hj using 1; exact Fin.ext h.symm)
      have hh := hS j hj
      omega

/-- Later resamplings do not change the weight of an earlier excluded event. -/
lemma towerWeights_retains_event (B : Fin n → Finset (∀ i, A i)) (c : Fin n → ℚ)
    (hc : ∀ i, 1 ≤ c i)
    (hB : ∀ i j : Fin n, j < i → ∀ x v, Function.update x i v ∈ B j ↔ x ∈ B j)
    (j : Fin n) (t : ℕ) (hjt : j.val + 1 ≤ t) (ht : t ≤ n) :
    (∑ x ∈ B j, towerWeights A B c t x) = ∑ x ∈ B j, towerWeights A B c (j.val + 1) x := by
  classical
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases heq : t = j.val
    · subst t; rfl
    · have hjt' : j.val + 1 ≤ t := by omega
      let i : Fin n := ⟨t, by omega⟩
      have hji : j < i := by change j.val < t; omega
      have hrec : towerWeights A B c (t+1) = resample A i (towerWeights A B c t) (B i) (c i) :=
        towerWeights_succ A B c i
      rw [hrec]
      have hh := resample_preserves_test A i (towerWeights A B c t) (B i) (hc i)
        (fun x => if x ∈ B j then (1 : ℚ) else 0)
        (by intro x v; simp only [hB i j hji x v])
      have he : (∑ x ∈ B j, resample A i (towerWeights A B c t) (B i) (c i) x) =
          ∑ x ∈ B j, towerWeights A B c t x := by
        simpa only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
          Finset.univ_inter] using hh
      exact he.trans (ih hjt' (by omega))

/-- The exact finite covering criterion for a sequence of coordinate-dependent
excluded events. This uses actual second moments of the constructed weights. -/
theorem coordinate_distortion_cover_bound
    (B : Fin n → Finset (∀ i, A i)) (c : Fin n → ℚ) (hc : ∀ i, 1 < c i)
    (hB : ∀ i j : Fin n, j < i → ∀ x v, Function.update x i v ∈ B j ↔ x ∈ B j)
    (hcover : ∀ x : ∀ i, A i, ∃ i, x ∈ B i) :
    1 ≤ ∑ i : Fin n, c i ^ 2 / (4 * (c i - 1)) *
      ∑ x : ∀ j, A j, towerWeights A B c i.val x * coordinateFraction A i (B i) x ^ 2 := by
  classical
  have hc1 : ∀ i, 1 ≤ c i := fun i => (hc i).le
  let μ := towerWeights A B c n
  have hμ : ∀ x, 0 ≤ μ x := towerWeights_nonneg A B c hc1 n
  have hpoint (x : ∀ i, A i) : μ x ≤ ∑ i : Fin n, if x ∈ B i then μ x else 0 := by
    obtain ⟨i,hi⟩ := hcover x
    have hh := Finset.single_le_sum (f := fun j : Fin n => if x ∈ B j then μ x else 0)
      (fun j _ => by dsimp only; split_ifs <;> [exact hμ x; exact le_rfl]) (Finset.mem_univ i)
    simpa only [if_pos hi] using hh
  have hunion : 1 ≤ ∑ i : Fin n, ∑ x ∈ B i, μ x := by
    have hh := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (∀ i, A i))) => hpoint x)
    rw [show (∑ x : ∀ i, A i, μ x) = 1 from towerWeights_total A B c hc1 n] at hh
    rw [Finset.sum_comm] at hh
    simpa only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter] using hh
  apply hunion.trans
  apply Finset.sum_le_sum
  intro i _
  have hret := towerWeights_retains_event A B c hc1 hB i n (by have := i.isLt; omega) le_rfl
  dsimp only [μ]
  rw [hret, towerWeights_succ A B c i]
  exact resample_excluded_second_moment A i _ (towerWeights_nonneg A B c hc1 i.val) (B i) (hc i)

end Tower
#print axioms towerWeights_box_bound
#print axioms towerWeights_retains_event
#print axioms coordinate_distortion_cover_bound
end Erdos7Distortion



/-! Finite second-moment expansions for the distortion sieve. -/
namespace Erdos7Distortion
set_option maxHeartbeats 3000000

/-- Expand a nonnegative finite majorant into all ordered pairs. This is an
inequality for arbitrary weights and functions, not an independence assertion. -/
theorem weighted_second_moment {Ω κ : Type*} [Fintype Ω]
    (μ α : Ω → ℚ) (hμ : ∀ x, 0 ≤ μ x) (hα : ∀ x, 0 ≤ α x)
    (K : Finset κ) (w : κ → ℚ) (hw : ∀ k ∈ K, 0 ≤ w k)
    (I : κ → Ω → ℚ) (hI : ∀ k ∈ K, ∀ x, 0 ≤ I k x)
    (hbound : ∀ x, α x ≤ ∑ k ∈ K, w k * I k x) :
    (∑ x, μ x * α x ^ 2) ≤
      ∑ k ∈ K, ∑ l ∈ K, w k * w l * ∑ x, μ x * (I k x * I l x) := by
  have hpoint (x : Ω) : μ x * α x ^ 2 ≤ μ x * (∑ k ∈ K, w k * I k x) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (hμ x)
    have hh := hbound x
    have hnon : 0 ≤ ∑ k ∈ K, w k * I k x :=
      Finset.sum_nonneg (fun k hk => mul_nonneg (hw k hk) (hI k hk x))
    nlinarith [hα x]
  apply (Finset.sum_le_sum (fun x _ => hpoint x)).trans_eq
  simp_rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro x _
  ring

section Box
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

/-- Product of two cylinder indicators is the indicator of their intersection.
The hypotheses only concern coordinates used by one box but not the other. -/
lemma boxIndicator_mul (S T : Finset ι) (X Y : ∀ i, Finset (A i))
    (hX : ∀ i ∈ T, i ∉ S → X i = Finset.univ)
    (hY : ∀ i ∈ S, i ∉ T → Y i = Finset.univ) (x : ∀ i, A i) :
    boxIndicator A S X x * boxIndicator A T Y x =
      boxIndicator A (S ∪ T) (fun i => X i ∩ Y i) x := by
  have heq : (∀ i ∈ S ∪ T, x i ∈ X i ∩ Y i) ↔
      (∀ i ∈ S, x i ∈ X i) ∧ (∀ i ∈ T, x i ∈ Y i) := by
    constructor
    · intro h
      exact ⟨fun i hi => (Finset.mem_inter.mp (h i (Finset.mem_union_left _ hi))).1,
        fun i hi => (Finset.mem_inter.mp (h i (Finset.mem_union_right _ hi))).2⟩
    · rintro ⟨hx,hy⟩ i hi
      apply Finset.mem_inter.mpr
      constructor
      · by_cases hsi : i ∈ S
        · exact hx i hsi
        · rw [hX i ((Finset.mem_union.mp hi).resolve_left hsi) hsi]
          exact Finset.mem_univ _
      · by_cases hti : i ∈ T
        · exact hy i hti
        · rw [hY i ((Finset.mem_union.mp hi).resolve_right hti) hti]
          exact Finset.mem_univ _
  simp only [boxIndicator, heq]
  split_ifs <;> simp_all

/-- A second-moment bound for a weighted union of cylinder conditions. -/
theorem box_second_moment {κ : Type*} (μ α : (∀ i, A i) → ℚ)
    (hμ : ∀ x, 0 ≤ μ x) (hα : ∀ x, 0 ≤ α x)
    (K : Finset κ) (w : κ → ℚ) (hw : ∀ k ∈ K, 0 ≤ w k)
    (S : κ → Finset ι) (X : κ → ∀ i, Finset (A i))
    (hX : ∀ k ∈ K, ∀ l ∈ K, ∀ i ∈ S l, i ∉ S k → X k i = Finset.univ)
    (hbound : ∀ x, α x ≤ ∑ k ∈ K, w k * boxIndicator A (S k) (X k) x) :
    (∑ x, μ x * α x ^ 2) ≤ ∑ k ∈ K, ∑ l ∈ K, w k * w l *
      boxMass A μ (S k ∪ S l) (fun i => X k i ∩ X l i) := by
  have hh := weighted_second_moment μ α hμ hα K w hw
    (fun k => boxIndicator A (S k) (X k)) (fun k _ => boxIndicator_nonneg A _ _) hbound
  apply hh.trans_eq
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [boxIndicator_mul A _ _ _ _ (hX k hk l hl) (hX l hl k hk)]

end Box
#print axioms weighted_second_moment
#print axioms box_second_moment
end Erdos7Distortion



/-! Exact finite geometric pair estimates used in the second-moment sieve. -/
namespace Erdos7Distortion
set_option maxHeartbeats 3000000

/-- There are exactly `2a+1` ordered pairs of nonnegative exponents with maximum
`a`. The sum is finite; no analytic summability result is needed. -/
theorem sum_square_max (f : ℕ → ℚ) (E : ℕ) :
    (∑ a ∈ Finset.range E, ∑ b ∈ Finset.range E, f (max a b)) =
      ∑ a ∈ Finset.range E, (2 * (a : ℚ) + 1) * f a := by
  induction E with
  | zero => simp
  | succ E ih =>
    rw [Finset.sum_range_succ]
    have hrow : (∑ b ∈ Finset.range (E+1), f (max E b)) = ((E : ℚ)+1)*f E := by
      have hh : (∑ b ∈ Finset.range (E+1), f (max E b)) = ∑ _b ∈ Finset.range (E+1), f E := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [max_eq_left (by have := Finset.mem_range.mp hb; omega)]
      rw [hh]
      simp [Nat.cast_add, Nat.cast_one]
    rw [hrow]
    have hpart : (∑ a ∈ Finset.range E, ∑ b ∈ Finset.range (E+1), f (max a b)) =
        (∑ a ∈ Finset.range E, ∑ b ∈ Finset.range E, f (max a b)) + (E : ℚ)*f E := by
      simp_rw [Finset.sum_range_succ]
      rw [Finset.sum_add_distrib]
      congr 1
      have hh : (∑ a ∈ Finset.range E, f (max a E)) = ∑ _a ∈ Finset.range E, f E := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [max_eq_right (by have := Finset.mem_range.mp ha; omega)]
      rw [hh]
      simp
    rw [hpart, ih, Finset.sum_range_succ]
    ring

/-- An explicit tail potential for the weighted geometric series. -/
def weightedGeometricTail (r : ℚ) (E : ℕ) : ℚ :=
  r ^ E * (((2 * (E : ℚ) + 1) * (1-r) + 2*r) / (1-r)^2)

lemma weightedGeometricTail_step {r : ℚ} (hr : r < 1) (E : ℕ) :
    weightedGeometricTail r E = (2*(E : ℚ)+1)*r^E + weightedGeometricTail r (E+1) := by
  have hne : 1-r ≠ 0 := by linarith
  simp only [weightedGeometricTail, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp
  ring

lemma weightedGeometricTail_nonneg {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1) (E : ℕ) :
    0 ≤ weightedGeometricTail r E := by
  have h : 0 ≤ 1-r := by linarith
  dsimp [weightedGeometricTail]
  positivity

lemma weightedGeometricTail_identity {r : ℚ} (hr : r < 1) (E : ℕ) :
    (∑ a ∈ Finset.range E, (2*(a : ℚ)+1)*r^a) + weightedGeometricTail r E = weightedGeometricTail r 0 := by
  induction E with
  | zero => simp
  | succ E ih =>
    rw [Finset.sum_range_succ]
    have hh := weightedGeometricTail_step hr E
    linarith

/-- Uniform bound for the positive terms of the weighted geometric series. -/
theorem weighted_positive_geometric_bound {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1) (E : ℕ) :
    (∑ a ∈ Finset.range (E+1), (2*(a : ℚ)+1)*r^a) - 1 ≤ r*(3-r)/(1-r)^2 := by
  have hid := weightedGeometricTail_identity hr1 (E+1)
  have hnon := weightedGeometricTail_nonneg hr0 hr1 (E+1)
  have htail : weightedGeometricTail r 0 - 1 = r*(3-r)/(1-r)^2 := by
    have hne : 1-r ≠ 0 := by linarith
    simp only [weightedGeometricTail, pow_zero, Nat.cast_zero, mul_zero, zero_add, one_mul]
    field_simp
    ring
  linarith

/-- The old-coordinate factor in a distinct-vector second moment. The terms
with exactly one positive exponent are included in the factor `3p-1`. -/
theorem geometric_pair_bound (p E : ℕ) (hp : 1 < p) (c : ℚ) (hc : 0 ≤ c) :
    (∑ a ∈ Finset.range (E+1), ∑ b ∈ Finset.range (E+1),
      if max a b = 0 then (1 : ℚ) else c * ((p : ℚ)⁻¹)^(max a b)) ≤
      1 + c * (3*(p : ℚ)-1)/(p-1)^2 := by
  let r : ℚ := (p : ℚ)⁻¹
  have hpQ : (1 : ℚ) < p := by exact_mod_cast hp
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; exact (inv_lt_one₀ (by linarith)).mpr hpQ
  rw [sum_square_max (fun a => if a = 0 then (1 : ℚ) else c * ((p : ℚ)⁻¹)^a)]
  have heq : (∑ a ∈ Finset.range (E+1), (2*(a : ℚ)+1) *
      (if a = 0 then (1 : ℚ) else c*r^a)) =
      1 + c * ((∑ a ∈ Finset.range (E+1), (2*(a : ℚ)+1)*r^a)-1) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.cast_zero,
      mul_zero, zero_add, one_mul, pow_zero]
    have hs : (∑ k ∈ Finset.range E, (2*((k+1 : ℕ) : ℚ)+1) * (c*r^(k+1))) =
        c * ∑ k ∈ Finset.range E, (2*((k+1 : ℕ) : ℚ)+1)*r^(k+1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hs]
    ring
  change (∑ a ∈ Finset.range (E+1), (2*(a : ℚ)+1) * (if a = 0 then (1 : ℚ) else c*r^a)) ≤ _
  rw [heq]
  have hh := mul_le_mul_of_nonneg_left (weighted_positive_geometric_bound hr0 hr1 E) hc
  have hformula : r*(3-r)/(1-r)^2 = (3*(p : ℚ)-1)/(p-1)^2 := by
    have hne : (p : ℚ) ≠ 0 := by linarith
    have hne1 : (p : ℚ)-1 ≠ 0 := by linarith
    dsimp [r]
    field_simp
  rw [hformula] at hh
  simpa only [mul_div_assoc] using add_le_add (le_refl (1 : ℚ)) hh

#print axioms sum_square_max
#print axioms geometric_pair_bound
end Erdos7Distortion



/-! A distortion covering criterion for arbitrary finite layered boxes. -/
namespace Erdos7Distortion
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

section Layers
variable {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
variable (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

/-- Boxes assigned to the stage where their last coordinate is processed. -/
def layerFamily (σ : κ → Fin n) (i : Fin n) : Finset κ := Finset.univ.filter (fun k => σ k = i)

/-- Union of the boxes that first appear at a given coordinate. -/
def layeredBad (S : κ → Finset (Fin n)) (X : κ → ∀ j, Finset (A j))
    (σ : κ → Fin n) (i : Fin n) : Finset (∀ j, A j) :=
  Finset.univ.filter (fun x => ∃ k ∈ layerFamily σ i, ∀ j ∈ S k, x j ∈ X k j)

lemma joinCoordinate_split_update (i : Fin n) (x : ∀ j, A j) (v : A i) :
    joinCoordinate A i (splitCoordinate A i x).1 v = Function.update x i v := by
  apply (splitCoordinate A i).injective
  rw [split_join, splitCoordinate_update]

lemma layeredBad_invariant (S : κ → Finset (Fin n)) (X : κ → ∀ j, Finset (A j))
    (σ : κ → Fin n) (hS : ∀ k j, j ∈ S k → j ≤ σ k)
    (i j : Fin n) (hji : j < i) (x : ∀ j, A j) (v : A i) :
    Function.update x i v ∈ layeredBad A S X σ j ↔ x ∈ layeredBad A S X σ j := by
  simp only [layeredBad, Finset.mem_filter, Finset.mem_univ, true_and]
  apply exists_congr
  intro k
  by_cases hk : k ∈ layerFamily σ j
  · have hkj : σ k = j := (Finset.mem_filter.mp hk).2
    have hne (a : Fin n) (ha : a ∈ S k) : a ≠ i := by
      have hh := hS k a ha
      rw [hkj] at hh
      exact ne_of_lt (lt_of_le_of_lt hh hji)
    have heq : (∀ a ∈ S k, Function.update x i v a ∈ X k a) ↔ ∀ a ∈ S k, x a ∈ X k a := by
      apply forall_congr'
      intro a
      by_cases ha : a ∈ S k
      · simp only [Function.update_of_ne (hne a ha)]
      · simp [ha]
    simp only [heq]
  · simp only [hk, false_and]

/-- Pointwise union bound for the fraction excluded from a coordinate fibre.
Only old-coordinate cylinder conditions appear on the right. -/
theorem layered_fraction_bound (S : κ → Finset (Fin n)) (X : κ → ∀ j, Finset (A j))
    (σ : κ → Fin n) (hσ : ∀ k, σ k ∈ S k) (i : Fin n) (x : ∀ j, A j) :
    coordinateFraction A i (layeredBad A S X σ i) x ≤
      ∑ k ∈ layerFamily σ i, fraction (X k i) * boxIndicator A ((S k).erase i) (X k) x := by
  classical
  let L := (layerFamily σ i).filter (fun k => ∀ j ∈ (S k).erase i, x j ∈ X k j)
  let U := L.biUnion (fun k => X k i)
  have hsub : coordinateFibre A i (layeredBad A S X σ i) (splitCoordinate A i x).1 ⊆ U := by
    intro v hv
    have hmem := (Finset.mem_filter.mp hv).2
    have hbad := (Finset.mem_filter.mp hmem).2
    obtain ⟨k,hk,hkx⟩ := hbad
    have hki : σ k = i := (Finset.mem_filter.mp hk).2
    have hiS : i ∈ S k := by simpa only [hki] using hσ k
    have hvX : v ∈ X k i := by
      have hh := hkx i hiS
      simpa only [joinCoordinate_self] using hh
    have hold : ∀ j ∈ (S k).erase i, x j ∈ X k j := by
      intro j hj
      have hh := hkx j (Finset.mem_of_mem_erase hj)
      rw [joinCoordinate_split_update, Function.update_of_ne (Finset.mem_erase.mp hj).1] at hh
      exact hh
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨hk,hold⟩, hvX⟩
  have hcard : ((coordinateFibre A i (layeredBad A S X σ i) (splitCoordinate A i x).1).card : ℚ) ≤
      ∑ k ∈ L, ((X k i).card : ℚ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_biUnion_le (s := L))
  have hfrac : coordinateFraction A i (layeredBad A S X σ i) x ≤ ∑ k ∈ L, fraction (X k i) := by
    dsimp only [coordinateFraction, fraction]
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right hcard card_pos_rat.le
  apply hfrac.trans_eq
  rw [show L = (layerFamily σ i).filter (fun k => ∀ j ∈ (S k).erase i, x j ∈ X k j) from rfl,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only [boxIndicator]
  split_ifs <;> ring

/-- The actual weighted pair sum bounds the second moment at each stage. -/
theorem layered_second_moment_bound (S : κ → Finset (Fin n)) (X : κ → ∀ j, Finset (A j))
    (σ : κ → Fin n) (hσ : ∀ k, σ k ∈ S k) (hS : ∀ k j, j ∈ S k → j ≤ σ k)
    (hX0 : ∀ k j, j ∉ S k → X k j = Finset.univ)
    (c : Fin n → ℚ) (hc : ∀ i, 1 ≤ c i) (i : Fin n) :
    (∑ x : ∀ j, A j, towerWeights A (layeredBad A S X σ) c i.val x *
      coordinateFraction A i (layeredBad A S X σ i) x ^ 2) ≤
    ∑ k ∈ layerFamily σ i, ∑ l ∈ layerFamily σ i,
      fraction (X k i) * fraction (X l i) *
        ∏ j ∈ (S k ∪ S l).erase i, c j * fraction (X k j ∩ X l j) := by
  classical
  let μ := towerWeights A (layeredBad A S X σ) c i.val
  have hμ : ∀ x, 0 ≤ μ x := towerWeights_nonneg A _ c hc i.val
  have hα : ∀ x, 0 ≤ coordinateFraction A i (layeredBad A S X σ i) x :=
    fun x => fraction_nonneg _
  have hcross : ∀ k ∈ layerFamily σ i, ∀ l ∈ layerFamily σ i,
      ∀ j ∈ (S l).erase i, j ∉ (S k).erase i → X k j = Finset.univ := by
    intro k hk l hl j hj hjk
    apply hX0 k j
    intro hjS
    exact hjk (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1,hjS⟩)
  have hb := box_second_moment A μ (coordinateFraction A i (layeredBad A S X σ i)) hμ hα
    (layerFamily σ i) (fun k => fraction (X k i)) (fun k _ => fraction_nonneg _)
    (fun k => (S k).erase i) X hcross (layered_fraction_bound A S X σ hσ i)
  apply hb.trans
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum
  intro l hl
  have hpre : ∀ j ∈ (S k).erase i ∪ (S l).erase i, j.val < i.val := by
    intro j hj
    have hik : σ k = i := (Finset.mem_filter.mp hk).2
    have hil : σ l = i := (Finset.mem_filter.mp hl).2
    rcases Finset.mem_union.mp hj with hj | hj
    · have hle := hS k j (Finset.mem_of_mem_erase hj)
      rw [hik] at hle
      exact lt_of_le_of_ne hle (fun h => (Finset.mem_erase.mp hj).1 (Fin.ext h))
    · have hle := hS l j (Finset.mem_of_mem_erase hj)
      rw [hil] at hle
      exact lt_of_le_of_ne hle (fun h => (Finset.mem_erase.mp hj).1 (Fin.ext h))
  have hbox := towerWeights_box_bound A (layeredBad A S X σ) c hc i.val (Nat.le_of_lt i.isLt)
    ((S k).erase i ∪ (S l).erase i) hpre (fun j => X k j ∩ X l j)
  have hnon : 0 ≤ fraction (X k i) * fraction (X l i) := mul_nonneg (fraction_nonneg _) (fraction_nonneg _)
  have hm := mul_le_mul_of_nonneg_left hbox hnon
  have heq : (S k).erase i ∪ (S l).erase i = (S k ∪ S l).erase i := by
    ext j
    simp only [Finset.mem_union, Finset.mem_erase]
    tauto
  simpa only [heq, μ] using hm

/-- A completely finite, residue-sensitive distortion inequality. Injectivity
of exponent vectors is not required until the pair sum is bounded further. -/
theorem layered_box_distortion_bound (S : κ → Finset (Fin n)) (X : κ → ∀ j, Finset (A j))
    (σ : κ → Fin n) (hσ : ∀ k, σ k ∈ S k) (hS : ∀ k j, j ∈ S k → j ≤ σ k)
    (hX0 : ∀ k j, j ∉ S k → X k j = Finset.univ)
    (c : Fin n → ℚ) (hc : ∀ i, 1 < c i)
    (hcover : ∀ x : ∀ j, A j, ∃ k, ∀ j ∈ S k, x j ∈ X k j) :
    1 ≤ ∑ i : Fin n, c i ^ 2 / (4 * (c i - 1)) *
      (∑ k ∈ layerFamily σ i, ∑ l ∈ layerFamily σ i,
        fraction (X k i) * fraction (X l i) *
          ∏ j ∈ (S k ∪ S l).erase i, c j * fraction (X k j ∩ X l j)) := by
  classical
  have hcover' : ∀ x : ∀ j, A j, ∃ i, x ∈ layeredBad A S X σ i := by
    intro x
    obtain ⟨k,hk⟩ := hcover x
    refine ⟨σ k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, hk⟩
  have hb := coordinate_distortion_cover_bound A (layeredBad A S X σ) c hc
    (layeredBad_invariant A S X σ hS) hcover'
  apply hb.trans
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left
    (layered_second_moment_bound A S X σ hσ hS hX0 c (fun j => (hc j).le) i)
  have hh := hc i
  exact div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (by linarith))

end Layers
#print axioms layered_fraction_bound
#print axioms layered_second_moment_bound
#print axioms layered_box_distortion_bound
end Erdos7Distortion



/-! Product majorization of distinct exponent-vector pairs. -/
namespace Erdos7Distortion
set_option maxHeartbeats 4000000

/-- Injectively labelled objects can be summed over a containing finite product. -/
theorem sum_injective_product_le {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    {D : ι → Type*} [∀ i, DecidableEq (D i)] (K : Finset κ) (e : κ → ∀ i, D i)
    (he : Function.Injective e) (Q : ∀ i, Finset (D i)) (heQ : ∀ k ∈ K, ∀ i, e k i ∈ Q i)
    (w : ∀ i, D i → ℚ) (hw : ∀ i v, 0 ≤ w i v) :
    (∑ k ∈ K, ∏ i, w i (e k i)) ≤ ∏ i, ∑ v ∈ Q i, w i v := by
  classical
  have hsub : K.image e ⊆ Fintype.piFinset Q := by
    intro v hv
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hv
    exact Fintype.mem_piFinset.mpr (heQ k hk)
  have hh : (∑ v ∈ K.image e, ∏ i, w i (v i)) ≤
      ∑ v ∈ Fintype.piFinset Q, ∏ i, w i (v i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun v _ _ => Finset.prod_nonneg (fun i _ => hw i (v i)))
  rw [Finset.sum_image he.injOn, ← Finset.prod_univ_sum] at hh
  exact hh

/-- Separate the present coordinate and omit trivial future factors. -/
lemma prod_past_with_current {n : ℕ} (i : Fin n) (w : Fin n → ℚ)
    (hw : ∀ j, i < j → w j = 1) :
    (∏ j, w j) = w i * ∏ j ∈ Finset.univ.filter (fun j => j < i), w j := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ w (Finset.mem_univ i)]
  congr 1
  symm
  apply Finset.prod_subset
  · intro j hj
    exact Finset.mem_erase.mpr ⟨ne_of_lt (Finset.mem_filter.mp hj).2, Finset.mem_univ _⟩
  · intro j hj hjpast
    have hne : j ≠ i := (Finset.mem_erase.mp hj).1
    have hnot : ¬ j < i := by intro h; exact hjpast (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    exact hw j (lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm hne))

/-- A single old-coordinate factor for a pair of exponent vectors. -/
def exponentPairFactor (p : ℕ) (c : ℚ) (a b : ℕ) : ℚ :=
  if max a b = 0 then 1 else c * ((p : ℚ)⁻¹)^(max a b)

lemma exponentPairFactor_nonneg (p a b : ℕ) {c : ℚ} (hc : 0 ≤ c) :
    0 ≤ exponentPairFactor p c a b := by
  unfold exponentPairFactor
  split_ifs
  · norm_num
  · positivity

/-- Sum all pairs from a layer, using only distinct exponent vectors, positive
current exponents, and zero future exponents. Arbitrary finite exponent caps
are allowed, and the resulting bound does not depend on those caps. -/
theorem exponent_layer_pair_bound {n : ℕ} {κ : Type*} [DecidableEq κ]
    (p E : Fin n → ℕ) (hp : ∀ j, 1 < p j) (c : Fin n → ℚ) (hc : ∀ j, 0 ≤ c j)
    (K : Finset κ) (e : κ → Fin n → ℕ) (he : Function.Injective e)
    (heE : ∀ k ∈ K, ∀ j, e k j ≤ E j) (i : Fin n)
    (hepos : ∀ k ∈ K, 0 < e k i) (hefuture : ∀ k ∈ K, ∀ j, i < j → e k j = 0) :
    (∑ k ∈ K, ∑ l ∈ K, ((p i : ℚ)⁻¹)^(e k i) * ((p i : ℚ)⁻¹)^(e l i) *
      ∏ j ∈ Finset.univ.filter (fun j => j < i), exponentPairFactor (p j) (c j) (e k j) (e l j)) ≤
    1 / (p i - 1 : ℚ)^2 *
      ∏ j ∈ Finset.univ.filter (fun j => j < i), (1 + c j * (3*(p j : ℚ)-1)/(p j-1)^2) := by
  classical
  let Q (j : Fin n) : Finset (ℕ × ℕ) :=
    if j = i then ((Finset.range (E j+1)).erase 0).product ((Finset.range (E j+1)).erase 0)
    else if j < i then (Finset.range (E j+1)).product (Finset.range (E j+1)) else {(0,0)}
  let w (j : Fin n) (v : ℕ × ℕ) : ℚ :=
    if j = i then ((p j : ℚ)⁻¹)^v.1 * ((p j : ℚ)⁻¹)^v.2
    else if j < i then exponentPairFactor (p j) (c j) v.1 v.2 else 1
  let label (z : κ × κ) (j : Fin n) := (e z.1 j, e z.2 j)
  have hlabel : Function.Injective label := by
    intro z z' hz
    apply Prod.ext
    · apply he
      funext j
      exact congrArg Prod.fst (congrFun hz j)
    · apply he
      funext j
      exact congrArg Prod.snd (congrFun hz j)
  have hmem : ∀ z ∈ K.product K, ∀ j, label z j ∈ Q j := by
    intro z hz j
    obtain ⟨hk,hl⟩ := Finset.mem_product.mp hz
    dsimp [Q, label]
    split_ifs with hji hj
    · subst j
      exact Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨by have := hepos z.1 hk; omega,
        Finset.mem_range.mpr (by have := heE z.1 hk i; omega)⟩,
        Finset.mem_erase.mpr ⟨by have := hepos z.2 hl; omega,
        Finset.mem_range.mpr (by have := heE z.2 hl i; omega)⟩⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by have := heE z.1 hk j; omega),
        Finset.mem_range.mpr (by have := heE z.2 hl j; omega)⟩
    · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hj) (Ne.symm hji)
      simp only [hefuture z.1 hk j hij, hefuture z.2 hl j hij, Finset.mem_singleton]
  have hw (j : Fin n) (v : ℕ × ℕ) : 0 ≤ w j v := by
    dsimp only [w]
    split_ifs
    · positivity
    · exact exponentPairFactor_nonneg _ _ _ (hc j)
    · norm_num
  have hprod (z : κ × κ) : (∏ j, w j (label z j)) =
      ((p i : ℚ)⁻¹)^(e z.1 i) * ((p i : ℚ)⁻¹)^(e z.2 i) *
        ∏ j ∈ Finset.univ.filter (fun j => j < i), exponentPairFactor (p j) (c j) (e z.1 j) (e z.2 j) := by
    rw [prod_past_with_current i _ (by intro j hj; simp [w, ne_of_gt hj, not_lt.mpr hj.le])]
    simp only [w, ↓reduceIte, label]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have hji := (Finset.mem_filter.mp hj).2
    simp [ne_of_lt hji, hji]
  have hsum := sum_injective_product_le (K.product K) label hlabel Q hmem w hw
  simp_rw [hprod] at hsum
  rw [Finset.product_eq_sprod, Finset.sum_product K K] at hsum
  have hcoord (j : Fin n) : (∑ v ∈ Q j, w j v) ≤
      if j = i then 1/(p i-1 : ℚ)^2 else if j < i then 1+c j*(3*(p j : ℚ)-1)/(p j-1)^2 else 1 := by
    by_cases hji : j = i
    · subst j
      simp only [Q, w, ↓reduceIte, Finset.product_eq_sprod, Finset.sum_product]
      rw [← Finset.sum_mul_sum]
      have hg := Erdos7Reduction.positive_geometric_sum_le (p i) (hp i)
        ((Finset.range (E i+1)).erase 0) (by intro a ha; have := (Finset.mem_erase.mp ha).1; omega)
      have hn : (0 : ℚ) ≤ ∑ a ∈ (Finset.range (E i+1)).erase 0, ((p i : ℚ)⁻¹)^a :=
        Finset.sum_nonneg (fun a _ => by positivity)
      have hm := mul_self_le_mul_self hn hg
      simpa only [one_div, pow_two, mul_inv_rev] using hm
    · by_cases hj : j < i
      · simp only [Q, w, hji, hj, ↓reduceIte, Finset.product_eq_sprod, Finset.sum_product, exponentPairFactor]
        exact geometric_pair_bound (p j) (E j) (hp j) (c j) (hc j)
      · simp [Q, w, hji, hj]
  have hpp := Finset.prod_le_prod (s := Finset.univ) (fun j _ => Finset.sum_nonneg (fun v _ => hw j v)) (fun j _ => hcoord j)
  have hfinal : (∏ j : Fin n, if j = i then 1/(p i-1 : ℚ)^2
      else if j < i then 1+c j*(3*(p j : ℚ)-1)/(p j-1)^2 else 1) =
      1/(p i-1 : ℚ)^2 * ∏ j ∈ Finset.univ.filter (fun j => j < i),
        (1+c j*(3*(p j : ℚ)-1)/(p j-1)^2) := by
    rw [prod_past_with_current i _ (by intro j hj; simp [ne_of_gt hj, not_lt.mpr hj.le])]
    simp only [↓reduceIte]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have hji := (Finset.mem_filter.mp hj).2
    simp [ne_of_lt hji, hji]
  rw [hfinal] at hpp
  exact hsum.trans hpp

#print axioms exponent_layer_pair_bound
end Erdos7Distortion



/-! The finite distinct-box second-moment distortion criterion. -/
namespace Erdos7Distortion
set_option maxHeartbeats 5000000

/-- The standard prime-by-prime second-moment distortion budget. -/
def secondMomentCost {n : ℕ} (p : Fin n → ℕ) (c : Fin n → ℚ) : ℚ :=
  ∑ i : Fin n, c i ^ 2 / (4 * (c i - 1)) * (1/(p i-1 : ℚ)^2 *
    ∏ j ∈ Finset.univ.filter (fun j => j < i), (1+c j*(3*(p j : ℚ)-1)/(p j-1)^2))

/-- Distinct exponent-vector boxes covering a finite product must have total
second-moment distortion cost at least one. There is no restriction on the
number of coordinates or the number of positive exponents of a single box. -/
theorem distinct_box_distortion_bound {n : ℕ} {κ : Type*} [Fintype κ]
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (p : Fin n → ℕ) (hp : ∀ i, 1 < p i)
    (e : κ → Fin n → ℕ) (he : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (X : κ → ∀ i, Finset (A i)) (hX0 : ∀ k i, e k i = 0 → X k i = Finset.univ)
    (hX : ∀ k i, ((X k i).card : ℚ) ≤ (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(e k i))
    (c : Fin n → ℚ) (hc : ∀ i, 1 < c i)
    (hcover : ∀ x : ∀ i, A i, ∃ k, ∀ i, x i ∈ X k i) :
    1 ≤ secondMomentCost p c := by
  classical
  let S (k : κ) := Finset.univ.filter (fun i => e k i ≠ 0)
  have hmem (k : κ) (i : Fin n) : i ∈ S k ↔ e k i ≠ 0 := by simp [S]
  have hne (k : κ) : (S k).Nonempty := by
    obtain ⟨i,hi⟩ := he0 k
    exact ⟨i,(hmem k i).mpr hi⟩
  let σ (k : κ) := (S k).max' (hne k)
  have hσ (k : κ) : σ k ∈ S k := Finset.max'_mem _ _
  have hS (k : κ) (j : Fin n) (hj : j ∈ S k) : j ≤ σ k := Finset.le_max' _ _ hj
  have hX0' (k : κ) (j : Fin n) (hj : j ∉ S k) : X k j = Finset.univ := by
    apply hX0 k j
    by_contra hh
    exact hj ((hmem k j).mpr hh)
  have hcover' : ∀ x : ∀ i, A i, ∃ k, ∀ j ∈ S k, x j ∈ X k j := by
    intro x
    obtain ⟨k,hk⟩ := hcover x
    exact ⟨k,fun j _ => hk j⟩
  have hb := layered_box_distortion_bound A S X σ hσ hS hX0' c hc hcover'
  have hc0 (j : Fin n) : 0 ≤ c j := by have := hc j; linarith
  have hfrac (k : κ) (j : Fin n) : fraction (X k j) ≤ ((p j : ℚ)⁻¹)^(e k j) := by
    apply (div_le_iff₀ card_pos_rat).mpr
    simpa only [mul_comm] using hX k j
  have hinter (k l : κ) (j : Fin n) :
      fraction (X k j ∩ X l j) ≤ ((p j : ℚ)⁻¹)^(max (e k j) (e l j)) := by
    by_cases hkl : e k j ≤ e l j
    · rw [max_eq_right hkl]
      apply (le_trans _ (hfrac l j))
      apply div_le_div_of_nonneg_right _ card_pos_rat.le
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : X k j ∩ X l j ⊆ X l j)
    · rw [max_eq_left (le_of_not_ge hkl)]
      apply (le_trans _ (hfrac k j))
      apply div_le_div_of_nonneg_right _ card_pos_rat.le
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_left : X k j ∩ X l j ⊆ X k j)
  let E (j : Fin n) := Finset.univ.sup (fun k => e k j)
  have heE (k : κ) (j : Fin n) : e k j ≤ E j :=
    Finset.le_sup (f := fun k => e k j) (Finset.mem_univ k)
  have hpair (i : Fin n) (k : κ) (hk : k ∈ layerFamily σ i) (l : κ) (hl : l ∈ layerFamily σ i) :
      fraction (X k i) * fraction (X l i) *
        (∏ j ∈ (S k ∪ S l).erase i, c j * fraction (X k j ∩ X l j)) ≤
      ((p i : ℚ)⁻¹)^(e k i) * ((p i : ℚ)⁻¹)^(e l i) *
        ∏ j ∈ Finset.univ.filter (fun j => j < i), exponentPairFactor (p j) (c j) (e k j) (e l j) := by
    have hki : σ k = i := (Finset.mem_filter.mp hk).2
    have hli : σ l = i := (Finset.mem_filter.mp hl).2
    let U := (S k ∪ S l).erase i
    let V := Finset.univ.filter (fun j : Fin n => j < i)
    have hUV : U ⊆ V := by
      intro j hj
      obtain ⟨hji,hju⟩ := Finset.mem_erase.mp hj
      have hle : j ≤ i := by
        rcases Finset.mem_union.mp hju with hjk | hjl
        · simpa only [hki] using hS k j hjk
        · simpa only [hli] using hS l j hjl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_le_of_ne hle hji⟩
    have hmax (j : Fin n) (hj : j ∈ U) : max (e k j) (e l j) ≠ 0 := by
      intro hzero
      rcases Finset.mem_union.mp (Finset.mem_erase.mp hj).2 with hjk | hjl
      · have hh := (hmem k j).mp hjk; omega
      · have hh := (hmem l j).mp hjl; omega
    have hprod : (∏ j ∈ U, c j * fraction (X k j ∩ X l j)) ≤
        ∏ j ∈ U, exponentPairFactor (p j) (c j) (e k j) (e l j) := by
      apply Finset.prod_le_prod
      · intro j _; exact mul_nonneg (hc0 j) (fraction_nonneg _)
      · intro j hj
        rw [exponentPairFactor, if_neg (hmax j hj)]
        exact mul_le_mul_of_nonneg_left (hinter k l j) (hc0 j)
    have hext : (∏ j ∈ U, exponentPairFactor (p j) (c j) (e k j) (e l j)) =
        ∏ j ∈ V, exponentPairFactor (p j) (c j) (e k j) (e l j) := by
      apply Finset.prod_subset hUV
      intro j hjV hjU
      have hji : j ≠ i := ne_of_lt (Finset.mem_filter.mp hjV).2
      have hk0 : e k j = 0 := by
        by_contra h
        exact hjU (Finset.mem_erase.mpr ⟨hji, Finset.mem_union_left _ ((hmem k j).mpr h)⟩)
      have hl0 : e l j = 0 := by
        by_contra h
        exact hjU (Finset.mem_erase.mpr ⟨hji, Finset.mem_union_right _ ((hmem l j).mpr h)⟩)
      simp [exponentPairFactor, hk0, hl0]
    have hnew := mul_le_mul (hfrac k i) (hfrac l i) (fraction_nonneg _) (by positivity)
    exact mul_le_mul hnew (hprod.trans_eq hext)
      (Finset.prod_nonneg (fun j _ => mul_nonneg (hc0 j) (fraction_nonneg _))) (by positivity)
  apply hb.trans
  apply Finset.sum_le_sum
  intro i _
  have hsum : (∑ k ∈ layerFamily σ i, ∑ l ∈ layerFamily σ i,
      fraction (X k i) * fraction (X l i) *
        ∏ j ∈ (S k ∪ S l).erase i, c j * fraction (X k j ∩ X l j)) ≤
      ∑ k ∈ layerFamily σ i, ∑ l ∈ layerFamily σ i,
        ((p i : ℚ)⁻¹)^(e k i) * ((p i : ℚ)⁻¹)^(e l i) *
          ∏ j ∈ Finset.univ.filter (fun j => j < i), exponentPairFactor (p j) (c j) (e k j) (e l j) :=
    Finset.sum_le_sum (fun k hk => Finset.sum_le_sum (fun l hl => hpair i k hk l hl))
  have hepos : ∀ k ∈ layerFamily σ i, 0 < e k i := by
    intro k hk
    have hki : σ k = i := (Finset.mem_filter.mp hk).2
    have hh := (hmem k (σ k)).mp (hσ k)
    rw [hki] at hh
    omega
  have hefuture : ∀ k ∈ layerFamily σ i, ∀ j, i < j → e k j = 0 := by
    intro k hk j hij
    by_contra h
    have hj := hS k j ((hmem k j).mpr h)
    have hki : σ k = i := (Finset.mem_filter.mp hk).2
    rw [hki] at hj
    exact (not_le_of_gt hij) hj
  have hbudget := exponent_layer_pair_bound p E hp c hc0 (layerFamily σ i) e he
    (fun k _ j => heE k j) i hepos hefuture
  have hcoeff : 0 ≤ c i ^ 2 / (4 * (c i - 1)) :=
    div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (by have := hc i; linarith))
  exact mul_le_mul_of_nonneg_left (hsum.trans hbudget) hcoeff

#print axioms distinct_box_distortion_bound
end Erdos7Distortion



/-! Arithmetic specialization of the second-moment distortion criterion. -/
namespace Erdos7Distortion
open Erdos7StarSieve
set_option maxHeartbeats 4000000

/-- Distinct congruence classes on powers of pairwise coprime bases obey the
same second-moment criterion as finite boxes. -/
theorem arithmetic_distortion_bound {n : ℕ} {κ : Type*} [Fintype κ]
    (p E : Fin n → ℕ) (hp : ∀ i, 1 < p i)
    (hcop : Pairwise (Function.onFun Nat.Coprime p))
    (e : κ → Fin n → ℕ) (he : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (heE : ∀ k i, e k i ≤ E i) (a : κ → ℤ)
    (c : Fin n → ℚ) (hc : ∀ i, 1 < c i)
    (hcover : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k) :
    1 ≤ secondMomentCost p c := by
  classical
  letI (i : Fin n) : NeZero (p i) := ⟨by have := hp i; omega⟩
  let A (i : Fin n) := ZMod (p i ^ E i)
  let f (k : κ) (i : Fin n) := ZMod.castHom (pow_dvd_pow (p i) (heE k i)) (ZMod (p i ^ e k i))
  let B (k : κ) (i : Fin n) := Finset.univ.filter (fun x : A i => f k i x = (a k : ZMod (p i ^ e k i)))
  have hBcard (k : κ) (i : Fin n) : ((B k i).card : ℚ) ≤
      (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(e k i) := by
    have hh := surjective_fiber_card_rat (f k i).toAddMonoidHom
      (ZMod.castHom_surjective (pow_dvd_pow (p i) (heE k i))) (a k)
    change ((B k i).card : ℚ) = _ at hh
    rw [hh]
    simp only [A, ZMod.card, Nat.cast_pow, div_eq_mul_inv, inv_pow]
    exact le_rfl
  have hbox : ∀ x : ∀ i, A i, ∃ k, ∀ i, x i ∈ B k i := by
    intro x
    let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) (fun i => p i ^ E i) Finset.univ
      (fun i _ => pow_ne_zero _ (NeZero.ne _))
      (fun i _ j _ hij => (hcop hij).pow _ _)
    have hz (i : Fin n) : (z.val : A i) = x i := by
      rw [← ZMod.natCast_zmod_val (x i)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
    obtain ⟨k, hk⟩ := hcover (z.val : ℤ)
    refine ⟨k, ?_⟩
    intro i
    have hpi : p i ^ e k i ∣ ∏ j, p j ^ e k j :=
      Finset.dvd_prod_of_mem (fun j => p j ^ e k j) (Finset.mem_univ i)
    have hpi' : ((p i ^ e k i : ℕ) : ℤ) ∣ ((∏ j, p j ^ e k j : ℕ) : ℤ) := by exact_mod_cast hpi
    have hqi := hpi'.trans hk
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hz i, map_natCast]
    symm
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (a k) (z.val : ℤ) (p i ^ e k i)).mpr hqi
  have hB0 (k : κ) (i : Fin n) (hi : e k i = 0) : B k i = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    have hsub : ∀ u v : ZMod (p i ^ e k i), u = v := by
      rw [hi, pow_zero]
      exact fun u v => Subsingleton.elim u v
    exact hsub _ _
  exact distinct_box_distortion_bound A p hp e he he0 B hB0 hBcard c hc hbox

#print axioms arithmetic_distortion_bound
end Erdos7Distortion



/-! A rounded finite-prefix certificate for the no-2-or-3 sieve subgoal.
This is not a proof or disproof of the unrestricted odd covering conjecture. -/
namespace Erdos7No23Sieve
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000

/-- The fixed cap is 5/4. -/
def multiplier (p : ℕ) : ℚ := 1 + (5/4 : ℚ)*(3*(p : ℚ)-1)/(p-1)^2

def charge (p : ℕ) : ℚ := (25/16 : ℚ)/(p-1)^2

/-- Upper-round product weights at scale 10^6 and accumulated loss at scale
10^9. All computation is integer arithmetic checked by the kernel. -/
def roundedStep (s : ℕ × ℕ) (p : ℕ) : ℕ × ℕ :=
  let d := 4*(p-1)^2
  (s.1*(d+5*(3*p-1)) ⌈/⌉ d,
   s.2 + (25000*s.1 ⌈/⌉ (16*(p-1)^2)))

def prefixPrimes : List ℕ :=
  (List.range 10080).filter (fun p => decide (5 ≤ p) && @decide (Nat.Prime p) (Nat.decidablePrime' p))

def roundedPrefix : ℕ × ℕ := prefixPrimes.foldl roundedStep (1000000,0)

/-- Exact integer evaluation, not native evaluation. -/
theorem roundedPrefix_certificate : roundedPrefix = (469185028,823155747) := by
  decide +kernel

/-- The certified rounded prefix leaves a positive margin for a proposed
terminal potential of (16/5)*P/10080. The tail estimate itself is separate. -/
theorem roundedPrefix_potential_lt_one :
    (roundedPrefix.2 : ℚ)/1000000000 + (16/5 : ℚ)*(roundedPrefix.1 : ℚ)/1000000/10080 < 1 := by
  rw [roundedPrefix_certificate]
  norm_num

lemma nat_div_le_rounded (a b : ℕ) (hb : 0 < b) :
    (a : ℚ)/b ≤ ((a ⌈/⌉ b : ℕ) : ℚ) := by
  apply (div_le_iff₀ (by exact_mod_cast hb : (0 : ℚ) < b)).mpr
  have hh : a ≤ b * (a ⌈/⌉ b) := (ceilDiv_le_iff_le_mul hb).mp le_rfl
  exact_mod_cast (by simpa only [mul_comm] using hh : a ≤ (a ⌈/⌉ b)*b)

lemma multiplier_nonneg (p : ℕ) (hp : 5 ≤ p) : 0 ≤ multiplier p := by
  have hpQ : (5 : ℚ) ≤ p := by exact_mod_cast hp
  dsimp [multiplier]
  have h : 0 ≤ 3*(p : ℚ)-1 := by linarith
  positivity

lemma charge_nonneg (p : ℕ) : 0 ≤ charge p := by dsimp [charge]; positivity

/-- One integer rounding step bounds the corresponding rational arithmetic
step in both components. -/
theorem roundedStep_bounds (s : ℕ × ℕ) (p : ℕ) (hp : 5 ≤ p) :
    (s.1 : ℚ)/1000000 * multiplier p ≤ ((roundedStep s p).1 : ℚ)/1000000 ∧
    (s.2 : ℚ)/1000000000 + (s.1 : ℚ)/1000000 * charge p ≤ ((roundedStep s p).2 : ℚ)/1000000000 := by
  have hp1 : 1 ≤ p := by omega
  have hp3 : 1 ≤ 3*p := by omega
  have hpQ : (5 : ℚ) ≤ p := by exact_mod_cast hp
  have hpNat : 0 < p-1 := by omega
  have hneq : (p : ℚ)-1 ≠ 0 := by linarith
  constructor
  · let d := 4*(p-1)^2
    let u := s.1*(d+5*(3*p-1))
    have hd : 0 < d := by dsimp [d]; positivity
    have hh := nat_div_le_rounded u d hd
    have heq : (s.1 : ℚ)/1000000 * multiplier p = ((u : ℚ)/d)/1000000 := by
      dsimp [multiplier, u, d]
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
        Nat.cast_sub hp1, Nat.cast_sub hp3]
      field_simp [hneq]
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right hh (by norm_num)
  · let d := 16*(p-1)^2
    let u := 25000*s.1
    have hd : 0 < d := by dsimp [d]; positivity
    have hh := nat_div_le_rounded u d hd
    have heq : (s.1 : ℚ)/1000000 * charge p = ((u : ℚ)/d)/1000000000 := by
      dsimp [charge, u, d]
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sub hp1]
      field_simp [hneq]
      ring
    rw [heq]
    have hstep : ((roundedStep s p).2 : ℚ) = (s.2 : ℚ) + ((u ⌈/⌉ d : ℕ) : ℚ) := by
      simp only [roundedStep, Nat.cast_add, u, d]
    rw [hstep, add_div]
    exact add_le_add (le_refl _) (div_le_div_of_nonneg_right hh (by norm_num))

/-- Exact arithmetic accumulation in product-weight and accumulated-cost order. -/
def rationalStep (s : ℚ × ℚ) (p : ℕ) : ℚ × ℚ :=
  (s.1*multiplier p, s.2+s.1*charge p)

def Dominates (s : ℕ × ℕ) (t : ℚ × ℚ) : Prop :=
  t.1 ≤ (s.1 : ℚ)/1000000 ∧ t.2 ≤ (s.2 : ℚ)/1000000000

lemma roundedStep_dominates (s : ℕ × ℕ) (t : ℚ × ℚ) (h : Dominates s t)
    (p : ℕ) (hp : 5 ≤ p) : Dominates (roundedStep s p) (rationalStep t p) := by
  obtain ⟨hP,hC⟩ := roundedStep_bounds s p hp
  constructor
  · exact (mul_le_mul_of_nonneg_right h.1 (multiplier_nonneg p hp)).trans hP
  · exact (add_le_add h.2 (mul_le_mul_of_nonneg_right h.1 (charge_nonneg p))).trans hC

lemma roundedFold_dominates (L : List ℕ) (hL : ∀ p ∈ L, 5 ≤ p)
    (s : ℕ × ℕ) (t : ℚ × ℚ) (h : Dominates s t) :
    Dominates (L.foldl roundedStep s) (L.foldl rationalStep t) := by
  induction L generalizing s t with
  | nil => exact h
  | cons p L ih =>
    simp only [List.foldl_cons]
    exact ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)) _ _
      (roundedStep_dominates s t h p (hL p (List.mem_cons_self)))

/-- This connects the kernel-computed integer state to the ACTUAL rational
prefix budget, not merely to an exploratory numerical recurrence. -/
theorem rationalPrefix_potential_lt_one :
    let t := prefixPrimes.foldl rationalStep (1,0)
    t.2 + (16/5 : ℚ)*t.1/10080 < 1 := by
  have hL : ∀ p ∈ prefixPrimes, 5 ≤ p := by
    intro p hp
    have hh := (List.mem_filter.mp hp).2
    have hh' : (decide (5 ≤ p) && @decide (Nat.Prime p) (Nat.decidablePrime' p)) = true := hh
    by_contra h
    simp only [decide_eq_false h, Bool.false_and] at hh'
    contradiction
  have hinit : Dominates (1000000,0) (1,0) := by norm_num [Dominates]
  have hd := roundedFold_dominates prefixPrimes hL (1000000,0) (1,0) hinit
  change Dominates roundedPrefix (prefixPrimes.foldl rationalStep (1,0)) at hd
  have hh := roundedPrefix_potential_lt_one
  dsimp only
  have hterm := mul_le_mul_of_nonneg_left hd.1 (by norm_num : (0 : ℚ) ≤ 16/5)
  have hterm' := div_le_div_of_nonneg_right hterm (by norm_num : (0 : ℚ) ≤ 10080)
  nlinarith [hd.2]

/-- Prime blocks of length 210 have at most 48 entries once all their members
are larger than 210. -/
theorem prime_block_card_le (N : ℕ) (hN : 210 < N) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ N ≤ p ∧ p < N+210) : P.card ≤ 48 := by
  have hsub : P ⊆ (Finset.Ico N (N+210)).filter (fun p => Nat.Coprime 210 p) := by
    intro p hp
    obtain ⟨hprime,hlo,hhi⟩ := hP p hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hlo,hhi⟩, ?_⟩
    exact (Nat.coprime_of_lt_prime (by norm_num : 210 ≠ 0) (hN.trans_le hlo) hprime).symm
  have hh := Finset.card_le_card hsub
  rw [Nat.filter_coprime_Ico_eq_totient] at hh
  norm_num [Nat.totient] at hh
  exact hh

/-- A rational arithmetic certificate for the block product majorant. -/
theorem block_increment_bound (n : ℚ) (hn : 10000 ≤ n) :
    (180/(n-1)+120/(n-1)^2) * (n+185) ≤ 185 := by
  have hpos : 0 < n-1 := by linarith
  have hden : 0 < (n-1)^2 := sq_pos_of_pos hpos
  apply (mul_le_mul_iff_of_pos_right hden).mp
  field_simp
  nlinarith [mul_nonneg (by linarith : 0 ≤ n-10000) (by linarith : 0 ≤ n)]

/-- The per-block loss bound and product growth fit inside the drop of the
terminal potential. This is an exact scalar inequality. -/
theorem block_potential_drop (n : ℚ) (hn : 10000 ≤ n) :
    75/(n-1)^2*(1+185/n) + (16/5 : ℚ)*(1+185/n)/(n+210) ≤ (16/5 : ℚ)/n := by
  have hn0 : 0 < n := by linarith
  have hm : 0 < n-1 := by linarith
  have hp : 0 < n+210 := by linarith
  have hden : 0 < 5*n*(n-1)^2*(n+210) := by positivity
  apply (mul_le_mul_iff_of_pos_right hden).mp
  field_simp
  nlinarith [mul_nonneg (by linarith : 0 ≤ n-10000) (by linarith : 0 ≤ n)]

#print axioms rationalPrefix_potential_lt_one
#print axioms roundedPrefix_certificate
#print axioms roundedPrefix_potential_lt_one
#print axioms prime_block_card_le
#print axioms block_potential_drop
end Erdos7No23Sieve



namespace Erdos7No23Sieve
open scoped BigOperators
set_option maxHeartbeats 2000000

noncomputable def budgetProduct (S : Finset ℕ) : ℚ := ∏ p ∈ S, multiplier p
noncomputable def budgetCost (S : Finset ℕ) : ℚ :=
  ∑ p ∈ S, charge p * budgetProduct (S.filter (· < p))

lemma multiplier_one_le (p : ℕ) (hp : 5 ≤ p) : 1 ≤ multiplier p := by
  have hpQ : (5 : ℚ) ≤ p := by exact_mod_cast hp
  have hh : 0 ≤ 3*(p : ℚ)-1 := by linarith
  dsimp [multiplier]
  exact le_add_of_nonneg_right (by positivity)

lemma budgetProduct_nonneg (S : Finset ℕ) (hS : ∀ p ∈ S, 5 ≤ p) :
    0 ≤ budgetProduct S :=
  Finset.prod_nonneg (fun p hp => multiplier_nonneg p (hS p hp))

lemma budgetProduct_one_le (S : Finset ℕ) (hS : ∀ p ∈ S, 5 ≤ p) :
    1 ≤ budgetProduct S :=
  by
    have hh := Finset.prod_le_prod (s := S) (f := fun _ => (1 : ℚ))
      (by intros; norm_num) (fun p hp => multiplier_one_le p (hS p hp))
    simpa only [Finset.prod_const_one] using hh

lemma budgetProduct_mono {S T : Finset ℕ} (hST : S ⊆ T)
    (hT : ∀ p ∈ T, 5 ≤ p) : budgetProduct S ≤ budgetProduct T := by
  have heq : budgetProduct (T \ S) * budgetProduct S = budgetProduct T :=
    Finset.prod_sdiff hST
  have h1 := budgetProduct_one_le (T \ S) (fun p hp => hT p (Finset.mem_sdiff.mp hp).1)
  have h0 := budgetProduct_nonneg S (fun p hp => hT p (hST hp))
  nlinarith

lemma budgetCost_nonneg (S : Finset ℕ) (hS : ∀ p ∈ S, 5 ≤ p) :
    0 ≤ budgetCost S := by
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (charge_nonneg p)
    (budgetProduct_nonneg _ (fun q hq => hS q (Finset.mem_filter.mp hq).1))

lemma budgetCost_mono {S T : Finset ℕ} (hST : S ⊆ T)
    (hT : ∀ p ∈ T, 5 ≤ p) : budgetCost S ≤ budgetCost T := by
  apply (Finset.sum_le_sum (fun p (hp : p ∈ S) =>
    mul_le_mul_of_nonneg_left
      (budgetProduct_mono (Finset.filter_subset_filter _ hST)
        (fun q hq => hT q (Finset.mem_filter.mp hq).1)) (charge_nonneg p))).trans
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun p hp _ =>
    mul_nonneg (charge_nonneg p)
      (budgetProduct_nonneg _ (fun q hq => hT q (Finset.mem_filter.mp hq).1)))

lemma budgetProduct_union {A B : Finset ℕ} (h : Disjoint A B) :
    budgetProduct (A ∪ B) = budgetProduct A * budgetProduct B :=
  Finset.prod_union h

lemma budgetCost_union {A B : Finset ℕ}
    (h : ∀ a ∈ A, ∀ b ∈ B, a < b) :
    budgetCost (A ∪ B) = budgetCost A + budgetProduct A * budgetCost B := by
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (lt_irrefl a) (h a ha a hb)
  have hA (a : ℕ) (ha : a ∈ A) :
      (A ∪ B).filter (· < a) = A.filter (· < a) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hp | hp, hpa⟩
      · exact ⟨hp, hpa⟩
      · exact False.elim ((not_lt_of_gt (h a ha p hp)) hpa)
    · rintro ⟨hp,hpa⟩; exact ⟨Or.inl hp,hpa⟩
  have hB (b : ℕ) (hb : b ∈ B) :
      (A ∪ B).filter (· < b) = A ∪ B.filter (· < b) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hp | hp,hpb⟩
      · exact Or.inl hp
      · exact Or.inr ⟨hp,hpb⟩
    · rintro (hp | ⟨hp,hpb⟩)
      · exact ⟨Or.inl hp,h p hp b hb⟩
      · exact ⟨Or.inr hp,hpb⟩
  unfold budgetCost
  rw [Finset.sum_union hd, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro a ha; rw [hA a ha]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [hB b hb, budgetProduct_union (hd.mono_right (Finset.filter_subset _ _))]
    ring

lemma budgetProduct_empty : budgetProduct ∅ = 1 := by simp [budgetProduct]
lemma budgetCost_empty : budgetCost ∅ = 0 := by simp [budgetCost]
lemma budgetProduct_singleton (p : ℕ) : budgetProduct {p} = multiplier p := by
  simp [budgetProduct]
lemma budgetCost_singleton (p : ℕ) : budgetCost {p} = charge p := by
  have hf : ({p} : Finset ℕ).filter (· < p) = ∅ := by ext; simp; omega
  simp [budgetCost, hf, budgetProduct_empty]

/-- An elementary finite product inequality, with no infinite products. -/
lemma product_one_sub_sum_le_one {ι : Type*} (S : Finset ι) (a : ι → ℚ)
    (ha : ∀ i ∈ S, 0 ≤ a i) :
    (1 - ∑ i ∈ S, a i) * (∏ i ∈ S, (1 + a i)) ≤ 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have haS : ∀ j ∈ S, 0 ≤ a j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hai := ha i (Finset.mem_insert_self _ _)
    have hsum := Finset.sum_nonneg haS
    have hprod := Finset.prod_nonneg (fun j hj => add_nonneg (by norm_num : (0:ℚ) ≤ 1) (haS j hj))
    have hnon := mul_nonneg (mul_nonneg hai (add_nonneg hsum hai)) hprod
    have hh := ih haS
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    nlinarith

lemma product_le_inverse_sum {ι : Type*} (S : Finset ι) (a : ι → ℚ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hsmall : ∑ i ∈ S, a i < 1) :
    (∏ i ∈ S, (1 + a i)) ≤ 1 / (1 - ∑ i ∈ S, a i) := by
  apply (le_div_iff₀ (sub_pos.mpr hsmall)).mpr
  simpa only [mul_comm] using product_one_sub_sum_le_one S a ha

lemma multiplier_increment (p : ℕ) (hp : 5 ≤ p) :
    multiplier p - 1 = (15/4 : ℚ)/(p-1) + (5/2 : ℚ)/(p-1)^2 := by
  have hpQ : (5 : ℚ) ≤ p := by exact_mod_cast hp
  have hn : (p : ℚ)-1 ≠ 0 := by linarith
  dsimp [multiplier]
  field_simp
  <;> ring

lemma multiplier_increment_le {n p : ℕ} (hn : 5 ≤ n) (hp : n ≤ p) :
    multiplier p - 1 ≤ (15/4 : ℚ)/(n-1) + (5/2 : ℚ)/(n-1)^2 := by
  have hnQ : (5 : ℚ) ≤ n := by exact_mod_cast hn
  have hpQ : (n : ℚ) ≤ p := by exact_mod_cast hp
  have hn1 : (0 : ℚ) < n-1 := by linarith
  have hnp : (n : ℚ)-1 ≤ p-1 := by linarith
  rw [multiplier_increment p (hn.trans hp)]
  apply add_le_add
  · exact div_le_div_of_nonneg_left (by norm_num) hn1 hnp
  · exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hn1)
      ((sq_le_sq₀ hn1.le (by linarith)).mpr hnp)

lemma charge_le {n p : ℕ} (hn : 5 ≤ n) (hp : n ≤ p) :
    charge p ≤ (25/16 : ℚ)/(n-1)^2 := by
  have hnQ : (5 : ℚ) ≤ n := by exact_mod_cast hn
  have hpQ : (n : ℚ) ≤ p := by exact_mod_cast hp
  have hn1 : (0 : ℚ) < n-1 := by linarith
  have hnp : (n : ℚ)-1 ≤ p-1 := by linarith
  exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hn1)
      (((sq_le_sq₀ hn1.le (by linarith)).mpr hnp))

lemma block_product_bound (n : ℕ) (hn : 10000 ≤ n) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ n ≤ p ∧ p < n+210) :
    budgetProduct S ≤ 1 + (185 : ℚ)/n := by
  have hnQ : (10000 : ℚ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℚ) < n := by linarith
  have hn1 : (0 : ℚ) < n-1 := by linarith
  have hcard := prime_block_card_le n (by omega) S hS
  have hcardQ : (S.card : ℚ) ≤ 48 := by exact_mod_cast hcard
  have hinc := block_increment_bound n hnQ
  let β : ℚ := 180/(n-1)+120/(n-1)^2
  have hsum : (∑ p ∈ S, (multiplier p - 1)) ≤ β := by
    have hb := Finset.sum_le_card_nsmul S (fun p => multiplier p - 1)
      ((15/4 : ℚ)/(n-1) + (5/2 : ℚ)/(n-1)^2)
      (fun p hp => multiplier_increment_le (by omega) (hS p hp).2.1)
    simp only [nsmul_eq_mul] at hb
    have hm := mul_le_mul_of_nonneg_right hcardQ
      (by positivity : 0 ≤ (15/4 : ℚ)/(n-1) + (5/2 : ℚ)/(n-1)^2)
    exact hb.trans (hm.trans_eq (by dsimp [β]; ring))
  have hβ : β < 1 := by
    have hh := (le_div_iff₀ (by linarith : (0 : ℚ) < n+185)).mpr hinc
    have hh' : (185 : ℚ)/(n+185) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    exact hh.trans_lt hh'
  have hbound := product_le_inverse_sum S (fun p => multiplier p - 1)
    (fun p hp => sub_nonneg.mpr (multiplier_one_le p (by have := (hS p hp).2.1; omega)))
    (hsum.trans_lt hβ)
  simp only [add_sub_cancel] at hbound
  apply hbound.trans
  apply (div_le_div_of_nonneg_left (by norm_num : (0:ℚ) ≤ 1)
    (sub_pos.mpr hβ) (by linarith : 1-β ≤ 1-∑ p ∈ S, (multiplier p - 1))).trans
  apply (div_le_iff₀ (sub_pos.mpr hβ)).mpr
  apply (mul_le_mul_iff_of_pos_right hn0).mp
  have hid : ((1 + (185:ℚ)/n) * (1-β))*n = n+185-β*(n+185) := by
    field_simp <;> ring
  rw [hid]
  dsimp [β]
  nlinarith

lemma block_cost_bound (n : ℕ) (hn : 10000 ≤ n) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ n ≤ p ∧ p < n+210) :
    budgetCost S ≤ 75 / (n-1 : ℚ)^2 * (1 + 185/(n : ℚ)) := by
  have hnQ : (10000 : ℚ) ≤ n := by exact_mod_cast hn
  have hS5 : ∀ p ∈ S, 5 ≤ p := by intro p hp; have := (hS p hp).2.1; omega
  have hP := block_product_bound n hn S hS
  have hcard : (S.card : ℚ) ≤ 48 := by
    exact_mod_cast prime_block_card_le n (by omega) S hS
  have hh := Finset.sum_le_card_nsmul S
    (fun p => charge p * budgetProduct (S.filter (· < p)))
    ((25/16 : ℚ)/(n-1)^2 * (1+185/(n:ℚ))) (by
      intro p hp
      exact mul_le_mul (charge_le (by omega) (hS p hp).2.1)
        ((budgetProduct_mono (Finset.filter_subset _ _) hS5).trans hP)
        (budgetProduct_nonneg _ (fun q hq => hS5 q (Finset.mem_filter.mp hq).1))
        (by positivity))
  simp only [nsmul_eq_mul] at hh
  have hm := mul_le_mul_of_nonneg_right hcard
    (by positivity : 0 ≤ (25/16 : ℚ)/(n-1)^2 * (1+185/(n:ℚ)))
  exact hh.trans (hm.trans_eq (by ring))

lemma block_budget_bound (n : ℕ) (hn : 10000 ≤ n) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ n ≤ p ∧ p < n+210) :
    budgetCost S + (16/5 : ℚ)*budgetProduct S/(n+210) ≤ (16/5 : ℚ)/n := by
  have hnQ : (10000 : ℚ) ≤ n := by exact_mod_cast hn
  have hC := block_cost_bound n hn S hS
  have hP := block_product_bound n hn S hS
  apply (add_le_add hC (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hP (by norm_num)) (by positivity))).trans
  exact block_potential_drop n hnQ

end Erdos7No23Sieve



/-! Finite iteration of the no-2-or-3 distortion budget. -/
namespace Erdos7No23Sieve
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

lemma bounded_tail_cost (k n : ℕ) (hn : 10000 ≤ n) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ n ≤ p ∧ p < n + 210*k) :
    budgetCost S ≤ (16/5 : ℚ)/n := by
  induction k generalizing n S with
  | zero =>
    have hSE : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have := hS p hp
      omega
    rw [hSE, budgetCost_empty]
    positivity
  | succ k ih =>
    let A := S.filter (· < n+210)
    let B := S.filter (fun p => ¬p < n+210)
    have hSAB : S = A ∪ B := (Finset.filter_union_filter_not_eq _ _).symm
    have hA (p : ℕ) (hp : p ∈ A) : p.Prime ∧ n ≤ p ∧ p < n+210 := by
      obtain ⟨hp,hlo⟩ := Finset.mem_filter.mp hp
      exact ⟨(hS p hp).1, (hS p hp).2.1, hlo⟩
    have hB (p : ℕ) (hp : p ∈ B) : p.Prime ∧ n+210 ≤ p ∧ p < (n+210)+210*k := by
      obtain ⟨hp,hhi⟩ := Finset.mem_filter.mp hp
      obtain ⟨hprime,hlo,hbound⟩ := hS p hp
      refine ⟨hprime,by omega,by omega⟩
    have hAB : ∀ a ∈ A, ∀ b ∈ B, a < b := by
      intro a ha b hb
      exact (hA a ha).2.2.trans_le (hB b hb).2.1
    have hPA : 0 ≤ budgetProduct A := budgetProduct_nonneg A (by
      intro p hp; have := (hA p hp).2.1; omega)
    have hb := ih (n+210) (by omega) B hB
    rw [hSAB, budgetCost_union hAB]
    apply (add_le_add_right (mul_le_mul_of_nonneg_left hb hPA) _).trans
    have hh := block_budget_bound n hn A hA
    simp only [Nat.cast_add, Nat.cast_ofNat] at *
    convert hh using 1 <;> ring

/-- The tail bound is uniform over all finite sets and all finite exponent caps. -/
theorem tail_cost_bound (n : ℕ) (hn : 10000 ≤ n) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ n ≤ p) :
    budgetCost S ≤ (16/5 : ℚ)/n := by
  apply bounded_tail_cost (S.sup id + 1) n hn S
  intro p hp
  have hpmax : p ≤ S.sup id := Finset.le_sup (f := id) hp
  exact ⟨(hS p hp).1, (hS p hp).2, by omega⟩

/-- Exact interpretation of a sorted list fold as the ordered Finset budget. -/
lemma rationalFold_eq (L : List ℕ) (hL : L.Pairwise (· < ·)) (P C : ℚ) :
    L.foldl rationalStep (P,C) =
      (P*budgetProduct L.toFinset, C+P*budgetCost L.toFinset) := by
  induction L generalizing P C with
  | nil => simp [budgetProduct_empty, budgetCost_empty]
  | cons p L ih =>
    obtain ⟨hp,hL⟩ := List.pairwise_cons.mp hL
    have hpN : p ∉ L.toFinset := by
      intro h
      exact (lt_irrefl p) (hp p (List.mem_toFinset.mp h))
    have hD : Disjoint ({p} : Finset ℕ) L.toFinset := Finset.disjoint_singleton_left.mpr hpN
    have hO : ∀ a ∈ ({p} : Finset ℕ), ∀ b ∈ L.toFinset, a < b := by
      intro a ha b hb
      rw [Finset.mem_singleton.mp ha]
      exact hp b (List.mem_toFinset.mp hb)
    have hU : (p :: L).toFinset = {p} ∪ L.toFinset := by simp
    rw [List.foldl_cons]
    change L.foldl rationalStep (P*multiplier p,C+P*charge p) = _
    rw [ih hL, hU, budgetProduct_union hD, budgetCost_union hO,
      budgetProduct_singleton, budgetCost_singleton]
    congr 1 <;> ring

lemma prefixPrimes_pairwise : prefixPrimes.Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

lemma mem_prefixPrimes (p : ℕ) : p ∈ prefixPrimes ↔ p.Prime ∧ 5 ≤ p ∧ p < 10080 := by
  simp only [prefixPrimes, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  tauto

lemma prefixPrimes_ge_five : ∀ p ∈ prefixPrimes.toFinset, 5 ≤ p := by
  intro p hp
  exact ((mem_prefixPrimes p).mp (List.mem_toFinset.mp hp)).2.1

lemma prefix_budget_bound :
    budgetCost prefixPrimes.toFinset + (16/5 : ℚ)*budgetProduct prefixPrimes.toFinset/10080 < 1 := by
  have hh := rationalPrefix_potential_lt_one
  dsimp only at hh
  rw [rationalFold_eq prefixPrimes prefixPrimes_pairwise 1 0] at hh
  simpa only [one_mul, zero_add] using hh

/-- All finite sets of primes at least five have second-moment budget below one. -/
theorem budgetCost_lt_one (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 5 ≤ p) :
    budgetCost S < 1 := by
  let A := S.filter (· < 10080)
  let B := S.filter (fun p => ¬p < 10080)
  have hSAB : S = A ∪ B := (Finset.filter_union_filter_not_eq _ _).symm
  have hA : A ⊆ prefixPrimes.toFinset := by
    intro p hp
    obtain ⟨hp,hlo⟩ := Finset.mem_filter.mp hp
    exact List.mem_toFinset.mpr ((mem_prefixPrimes p).mpr ⟨(hS p hp).1,(hS p hp).2,hlo⟩)
  have hB (p : ℕ) (hp : p ∈ B) : p.Prime ∧ 10080 ≤ p := by
    obtain ⟨hp,hhi⟩ := Finset.mem_filter.mp hp
    exact ⟨(hS p hp).1,by omega⟩
  have hAB : ∀ a ∈ A, ∀ b ∈ B, a < b := by
    intro a ha b hb
    exact (Finset.mem_filter.mp ha).2.trans_le (hB b hb).2
  have hPA := budgetProduct_mono hA prefixPrimes_ge_five
  have hCA := budgetCost_mono hA prefixPrimes_ge_five
  have hCB := tail_cost_bound 10080 (by omega) B hB
  have hPA0 := budgetProduct_nonneg A (fun p hp => prefixPrimes_ge_five p (hA hp))
  have hterm : budgetProduct A * budgetCost B ≤
      budgetProduct prefixPrimes.toFinset * ((16/5 : ℚ)/10080) := by
    exact (mul_le_mul_of_nonneg_left hCB hPA0).trans
      (mul_le_mul_of_nonneg_right hPA (by norm_num))
  rw [hSAB, budgetCost_union hAB]
  apply (add_le_add hCA hterm).trans_lt
  convert prefix_budget_bound using 1 <;> ring

#print axioms budgetCost_lt_one
end Erdos7No23Sieve



/-! A completed arithmetic obstruction for distinct moduli coprime to six. -/
namespace Erdos7No23Sieve
open scoped BigOperators
open Erdos7Distortion Erdos7Reduction
set_option maxHeartbeats 2000000

lemma secondMomentCost_eq_budgetCost {n : ℕ} (p : Fin n → ℕ) (hmono : StrictMono p) :
    secondMomentCost p (fun _ => 5/4) = budgetCost (Finset.univ.image p) := by
  unfold secondMomentCost budgetCost
  rw [Finset.sum_image hmono.injective.injOn]
  apply Finset.sum_congr rfl
  intro i _
  unfold budgetProduct
  rw [Finset.filter_image, Finset.prod_image hmono.injective.injOn]
  simp only [hmono.lt_iff_lt]
  dsimp [multiplier, charge]
  norm_num
  ring

lemma secondMomentCost_lt_one {n : ℕ} (p : Fin n → ℕ)
    (hp : ∀ i, (p i).Prime ∧ 5 ≤ p i) (hmono : StrictMono p) :
    secondMomentCost p (fun _ => 5/4) < 1 := by
  rw [secondMomentCost_eq_budgetCost p hmono]
  apply budgetCost_lt_one
  intro q hq
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
  exact hp i

/-- Distinct exponent vectors on prime coordinates at least five cannot cover. -/
theorem not_no23_coordinate_cover {n : ℕ} {κ : Type*} [Fintype κ]
    (p E : Fin n → ℕ) (hp : ∀ i, (p i).Prime ∧ 5 ≤ p i) (hmono : StrictMono p)
    (e : κ → Fin n → ℕ) (he : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (heE : ∀ k i, e k i ≤ E i) (a : κ → ℤ) :
    ¬ (∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x - a k) := by
  intro hcover
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact ((hp i).1.coprime_iff_not_dvd).mpr (fun hd => hij
      (hmono.injective ((Nat.prime_dvd_prime_iff_eq (hp i).1 (hp j).1).mp hd)))
  have hh := arithmetic_distortion_bound p E (fun i => (hp i).1.one_lt) hcop
    e he he0 heE a (fun _ => 5/4) (by intro i; norm_num) hcover
  exact (not_le_of_gt (secondMomentCost_lt_one p hp hmono)) hh

/-- Every finite distinct nontrivial arithmetic cover has a modulus divisible by
one of the primes two and three. -/
theorem arithmetic_exists_two_or_three {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hinj : Function.Injective m)
    (hm : ∀ k, 1 < m k) (hcover : ∀ x : ℤ, ∃ k, (m k : ℤ) ∣ x-a k) :
    ∃ k, 2 ∣ m k ∨ 3 ∣ m k := by
  classical
  by_contra! hno
  have hm0 (k : κ) : m k ≠ 0 := by have := hm k; omega
  let P := Finset.univ.biUnion (fun k => (m k).primeFactors)
  have hP (q : ℕ) (hq : q ∈ P) : q.Prime ∧ 5 ≤ q := by
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hprime,hdvd,_⟩ := Nat.mem_primeFactors.mp hk
    refine ⟨hprime,?_⟩
    have h2 : q ≠ 2 := by intro h; exact (hno k).1 (h ▸ hdvd)
    have h3 : q ≠ 3 := by intro h; exact (hno k).2 (h ▸ hdvd)
    have h4 : q ≠ 4 := by intro h; subst q; norm_num at hprime
    have := hprime.two_le
    omega
  let p := P.orderEmbOfFin rfl
  have hp (i : Fin P.card) : (p i).Prime ∧ 5 ≤ p i := hP _ (P.orderEmbOfFin_mem rfl i)
  let e (k : κ) (i : Fin P.card) := (m k).factorization (p i)
  let E (i : Fin P.card) := Finset.univ.sup (fun k => e k i)
  have heE (k : κ) (i : Fin P.card) : e k i ≤ E i :=
    Finset.le_sup (f := fun k => e k i) (Finset.mem_univ k)
  have hprod (k : κ) : m k = ∏ i : Fin P.card, p i ^ e k i := by
    have hsub : (m k).primeFactors ⊆ P := by
      intro q hq
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hq⟩
    have hh := Erdos7Compression.factorization_product_over_superset (m k) (hm0 k) P hsub
    rw [Finset.prod_coe_sort P (fun q => q ^ (m k).factorization q)] at hh
    nth_rw 1 [hh]
    conv_lhs => rw [← P.map_orderEmbOfFin_univ rfl]
    exact Finset.prod_map _ _ (fun q : ℕ => q ^ (m k).factorization q)
  have hei : Function.Injective e := by
    intro k l hkl
    apply hinj
    rw [hprod k, hprod l, hkl]
  have he0 (k : κ) : ∃ i, e k i ≠ 0 := by
    by_contra! h
    have hh := hm k
    rw [hprod k] at hh
    simp only [h, pow_zero, Finset.prod_const_one] at hh
    omega
  apply not_no23_coordinate_cover p E hp p.strictMono e hei he0 heE a
  simpa only [← hprod] using hcover

/-- In particular every odd arithmetic cover has a modulus divisible by three. -/
theorem arithmetic_exists_three {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a) :
    ∃ k, 3 ∣ m k := by
  obtain ⟨k,hk | hk⟩ := arithmetic_exists_two_or_three m a hc.1 (fun k => (hc.2.1 k).1) hc.2.2
  · exact False.elim ((Nat.not_even_iff_odd.mpr (hc.2.1 k).2) (even_iff_two_dvd.mpr hk))
  · exact ⟨k,hk⟩

/-- Ideal-valued version: an odd strict covering system must use three. -/
theorem exists_three (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i, ¬ C.moduli i ≤ Ideal.span {2}) :
    ∃ i, 3 ∣ (C.moduli i).absNorm := by
  letI := C.fintypeIndex
  exact arithmetic_exists_three (fun i => (C.moduli i).absNorm) C.residue
    ⟨moduli_absNorm_injective C, fun i => ⟨moduli_absNorm_gt_one C i,
      (ideal_not_le_two_iff _).mp (hodd i)⟩, arithmetic_cover C⟩

#print axioms arithmetic_exists_two_or_three
#print axioms exists_three
end Erdos7No23Sieve



/-! Finite one-coordinate convex compression. The unrestricted conjecture
is not settled by these comparison lemmas. -/
namespace Erdos7CompressionSieve
open scoped BigOperators
set_option maxHeartbeats 2000000

/-- The increasing-increments property of a convex scalar function. -/
def IncreasingIncrements (φ : ℚ → ℚ) : Prop :=
  ∀ x y d, x ≤ y → 0 ≤ d → φ (x+d)-φ x ≤ φ (y+d)-φ y

lemma convex_increasingIncrements (φ : ℚ → ℚ) (hφ : ConvexOn ℚ Set.univ φ) :
    IncreasingIncrements φ := by
  intro x y d hxy hd
  by_cases hzero : y-x+d = 0
  · have hyx : y = x := by linarith
    have hd0 : d = 0 := by linarith
    simp [hyx, hd0]
  have hpos : 0 < y-x+d := lt_of_le_of_ne (by linarith) (Ne.symm hzero)
  let a := d/(y-x+d)
  let b := (y-x)/(y-x+d)
  have ha : 0 ≤ a := div_nonneg hd hpos.le
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hxy) hpos.le
  have hab : a+b = 1 := by dsimp [a,b]; field_simp; ring
  have heq1 : a*(y+d)+b*x = x+d := by dsimp [a,b]; field_simp; ring
  have heq2 : b*(y+d)+a*x = y := by dsimp [a,b]; field_simp; ring
  have h1 := hφ.2 (Set.mem_univ (y+d)) (Set.mem_univ x) ha hb hab
  have h2 := hφ.2 (Set.mem_univ (y+d)) (Set.mem_univ x) hb ha (by linarith : b+a = 1)
  simp only [smul_eq_mul] at h1 h2
  rw [heq1] at h1
  rw [heq2] at h2
  have heq3 : (a*φ (y+d)+b*φ x)+(b*φ (y+d)+a*φ x) = φ (y+d)+φ x := by
    calc
      _ = (a+b)*φ (y+d)+(a+b)*φ x := by ring
      _ = _ := by rw [hab]; ring
  linarith

noncomputable def prefixWeight (w : ℕ → ℚ) (n : ℕ) : ℚ := ∑ i ∈ Finset.range n, w i
noncomputable def selectedWeight (w : ℕ → ℚ) (b : ℕ → Bool) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, if b i then w i else 0
noncomputable def chainIncrement (φ : ℚ → ℚ) (a : ℚ) (w : ℕ → ℚ) (i : ℕ) : ℚ :=
  φ (a+prefixWeight w (i+1))-φ (a+prefixWeight w i)

lemma selectedWeight_le (w : ℕ → ℚ) (b : ℕ → Bool) (n : ℕ)
    (hw : ∀ i < n, 0 ≤ w i) : selectedWeight w b n ≤ prefixWeight w n := by
  apply Finset.sum_le_sum
  intro i hi
  split_ifs <;> [exact le_rfl; exact hw i (Finset.mem_range.mp hi)]

lemma chainIncrement_nonneg (φ : ℚ → ℚ) (hmono : Monotone φ) (a : ℚ)
    (w : ℕ → ℚ) (i : ℕ) (hi : 0 ≤ w i) : 0 ≤ chainIncrement φ a w i := by
  apply sub_nonneg.mpr
  apply hmono
  simp only [prefixWeight, Finset.sum_range_succ]
  linarith

/-- A convex function on the Boolean cube is bounded by the modular function
obtained from its successive increments along any full chain. -/
theorem convex_chain_majorant (φ : ℚ → ℚ) (hφ : IncreasingIncrements φ)
    (a : ℚ) (w : ℕ → ℚ) (b : ℕ → Bool) (n : ℕ) (hw : ∀ i < n, 0 ≤ w i) :
    φ (a+selectedWeight w b n) ≤ φ a +
      ∑ i ∈ Finset.range n, if b i then chainIncrement φ a w i else 0 := by
  induction n with
  | zero => simp [selectedWeight]
  | succ n ih =>
    have hprev : ∀ i < n, 0 ≤ w i := fun i hi => hw i (by omega)
    have hih := ih hprev
    have hn := hw n (by omega)
    have hs := selectedWeight_le w b n hprev
    have hh := hφ (a+selectedWeight w b n) (a+prefixWeight w n) (w n) (by linarith) hn
    have heq : selectedWeight w b (n+1) = selectedWeight w b n + if b n then w n else 0 :=
      Finset.sum_range_succ _ _
    rw [heq, Finset.sum_range_succ]
    cases hbn : b n <;> simp only [hbn, Bool.false_eq_true, ↓reduceIte, add_zero] at *
    · exact hih
    · dsimp [chainIncrement] at *
      simp only [prefixWeight, Finset.sum_range_succ, add_assoc] at hh hih ⊢
      linarith

/-- Finite weighted expectation version. Marginal bounds suffice; the events
may be arbitrarily dependent. No independence assumption is present. -/
theorem weighted_convex_compression {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℚ) (hμ : ∀ x, 0 ≤ μ x) (φ : ℚ → ℚ)
    (hφ : IncreasingIncrements φ) (hmono : Monotone φ)
    (a : ℚ) (w : ℕ → ℚ) (n : ℕ) (hw : ∀ i < n, 0 ≤ w i)
    (b : ℕ → Ω → Bool) (q : ℕ → ℚ)
    (hq : ∀ i < n, (∑ x, μ x * if b i x then 1 else 0) ≤ q i) :
    (∑ x, μ x * φ (a+selectedWeight w (fun i => b i x) n)) ≤
      (∑ x, μ x) * φ a + ∑ i ∈ Finset.range n, q i * chainIncrement φ a w i := by
  calc
    _ ≤ ∑ x, μ x * (φ a + ∑ i ∈ Finset.range n,
        if b i x then chainIncrement φ a w i else 0) := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left (convex_chain_majorant φ hφ a w (fun i => b i x) n hw) (hμ x)
    _ = (∑ x, μ x)*φ a + ∑ i ∈ Finset.range n,
        (∑ x, μ x * if b i x then 1 else 0) * chainIncrement φ a w i := by
      simp_rw [mul_add, Finset.mul_sum]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      cases b i x <;> simp
    _ ≤ _ := by
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hq i (Finset.mem_range.mp hi))
        (chainIncrement_nonneg φ hmono a w i (hw i (Finset.mem_range.mp hi)))

lemma chain_summation_by_parts (f q : ℕ → ℚ) (n : ℕ) :
    f 0 + ∑ i ∈ Finset.range n, q i * (f (i+1)-f i) =
      (1-q 0)*f 0 + ∑ i ∈ Finset.range n, (q i-q (i+1))*f (i+1) + q n*f n := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith

/-- Positive-part affine functions are covered by the comparison theorem. -/
lemma hinge_convex (r s : ℚ) : ConvexOn ℚ Set.univ (fun x : ℚ => max 0 (r*x+s)) := by
  have hf : ConvexOn ℚ Set.univ (fun x : ℚ => r*x+s) := by
    constructor
    · exact convex_univ
    · intro x _ y _ a b ha hb hab
      simp only [smul_eq_mul]
      have hs : (a+b)*s = s := by rw [hab, one_mul]
      nlinarith only [hs]
  exact (convexOn_const 0 convex_univ).sup hf

lemma hinge_monotone (r s : ℚ) (hr : 0 ≤ r) : Monotone (fun x : ℚ => max 0 (r*x+s)) := by
  intro x y hxy
  exact max_le_max le_rfl (add_le_add_left (mul_le_mul_of_nonneg_left hxy hr) _)

lemma hinge_increasingIncrements (r s : ℚ) :
    IncreasingIncrements (fun x : ℚ => max 0 (r*x+s)) :=
  convex_increasingIncrements _ (hinge_convex r s)

open Erdos7Distortion

/-- The compression estimate for the ACTUAL finite distortion resampling
operator. Weights and the base term may depend on every other coordinate.
The coordinate sets need not be nested, compatible, or independent. -/
theorem resample_convex_compression {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (i : ι) (μ : (∀ j, A j) → ℚ) (hμ : ∀ x, 0 ≤ μ x)
    (B : Finset (∀ j, A j)) (c : ℚ) (hc : 1 ≤ c)
    (φ : ℚ → ℚ) (hφ : IncreasingIncrements φ) (hmono : Monotone φ)
    (a : (∀ j, A j) → ℚ) (w : ℕ → (∀ j, A j) → ℚ) (n : ℕ)
    (hw : ∀ k < n, ∀ x, 0 ≤ w k x)
    (haind : ∀ x (v : A i), a (Function.update x i v) = a x)
    (hwind : ∀ k x (v : A i), w k (Function.update x i v) = w k x)
    (T : ℕ → Finset (A i)) (q : ℕ → ℚ)
    (hT : ∀ k < n, c * ((T k).card : ℚ) / Fintype.card (A i) ≤ q k) :
    (∑ x, resample A i μ B c x *
        φ (a x + selectedWeight (fun k => w k x) (fun k => decide (x i ∈ T k)) n)) ≤
      (∑ x, μ x * φ (a x)) + ∑ k ∈ Finset.range n, q k *
        ∑ x, μ x * chainIncrement φ (a x) (fun k => w k x) k := by
  classical
  let inc (k : ℕ) (x : ∀ j, A j) := chainIncrement φ (a x) (fun l => w l x) k
  have hinc0 (k : ℕ) (hk : k < n) (x : ∀ j, A j) : 0 ≤ inc k x :=
    chainIncrement_nonneg φ hmono (a x) (fun l => w l x) k (hw k hk x)
  have hincind (k : ℕ) (x : ∀ j, A j) (v : A i) : inc k (Function.update x i v) = inc k x := by
    simp only [inc, chainIncrement, haind, hwind]
  have hbase : (∑ x, resample A i μ B c x * φ (a x)) = ∑ x, μ x * φ (a x) :=
    resample_preserves_test A i μ B hc (fun x => φ (a x)) (fun x v => by simp only [haind])
  have hterm (k : ℕ) (hk : k < n) :
      (∑ x, resample A i μ B c x * if x i ∈ T k then inc k x else 0) ≤
        q k * ∑ x, μ x * inc k x := by
    have hh := resample_coordinate_test_bound A i μ hμ B hc (T k)
      (inc k) (hinc0 k hk) (hincind k)
    have hm : 0 ≤ ∑ x, μ x * inc k x :=
      Finset.sum_nonneg (fun x _ => mul_nonneg (hμ x) (hinc0 k hk x))
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ hm
    simpa only [mul_div_assoc] using hT k hk
  calc
    _ ≤ ∑ x, resample A i μ B c x * (φ (a x) +
        ∑ k ∈ Finset.range n, if x i ∈ T k then inc k x else 0) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (resample_nonneg A i μ hμ B hc x)
      simpa only [decide_eq_true_eq, inc] using
        convex_chain_majorant φ hφ (a x) (fun k => w k x)
          (fun k => decide (x i ∈ T k)) n (fun k hk => hw k hk x)
    _ = (∑ x, μ x * φ (a x)) + ∑ k ∈ Finset.range n,
        ∑ x, resample A i μ B c x * if x i ∈ T k then inc k x else 0 := by
      simp_rw [mul_add, Finset.mul_sum]
      rw [Finset.sum_add_distrib, hbase, Finset.sum_comm]
    _ ≤ _ := by
      apply add_le_add_right
      exact Finset.sum_le_sum (fun k hk => hterm k (Finset.mem_range.mp hk))

#print axioms weighted_convex_compression
#print axioms resample_convex_compression
end Erdos7CompressionSieve



/-! Equal-size coordinate compression for finite distortion weights. -/
namespace Erdos7CompressionSieve
open scoped BigOperators
open Erdos7Distortion
set_option maxHeartbeats 2000000

lemma convex_chord_majorant (φ : ℚ → ℚ) (hφ : ConvexOn ℚ Set.univ φ)
    (a s W : ℚ) (hs : 0 ≤ s) (hsW : s ≤ W) :
    φ (a+s) ≤ φ a + (φ (a+W)-φ a)/W*s := by
  by_cases hW : W = 0
  · have hs0 : s = 0 := by linarith
    simp [hW, hs0]
  have hWp : 0 < W := lt_of_le_of_ne (hs.trans hsW) (Ne.symm hW)
  have hu : 0 ≤ s/W := div_nonneg hs hWp.le
  have hv : 0 ≤ 1-s/W := by have := (div_le_one hWp).mpr hsW; linarith
  have hh := hφ.2 (Set.mem_univ (a+W)) (Set.mem_univ a) hu hv (by ring : s/W+(1-s/W)=1)
  simp only [smul_eq_mul] at hh
  have hx : s/W*(a+W)+(1-s/W)*a = a+s := by field_simp; ring
  rw [hx] at hh
  convert hh using 1 <;> ring

/-- One-coordinate compression to a Bernoulli choice. This works with arbitrary
nonnegative weights measurable in the remaining coordinates. -/
theorem resample_binary_compression {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (i : ι) (μ : (∀ j, A j) → ℚ) (hμ : ∀ x, 0 ≤ μ x)
    (B : Finset (∀ j, A j)) (c : ℚ) (hc : 1 ≤ c)
    (φ : ℚ → ℚ) (hφ : ConvexOn ℚ Set.univ φ) (hmono : Monotone φ)
    (a : (∀ j, A j) → ℚ) (K : Finset κ) (w : κ → (∀ j, A j) → ℚ)
    (hw : ∀ k ∈ K, ∀ x, 0 ≤ w k x)
    (haind : ∀ x (v : A i), a (Function.update x i v) = a x)
    (hwind : ∀ k x (v : A i), w k (Function.update x i v) = w k x)
    (T : κ → Finset (A i)) (q : ℚ)
    (hT : ∀ k ∈ K, c * ((T k).card : ℚ) / Fintype.card (A i) ≤ q) :
    (∑ x, resample A i μ B c x * φ (a x + ∑ k ∈ K, if x i ∈ T k then w k x else 0)) ≤
      (1-q)*(∑ x, μ x * φ (a x)) + q*(∑ x, μ x * φ (a x + ∑ k ∈ K, w k x)) := by
  classical
  let W (x : ∀ j, A j) := ∑ k ∈ K, w k x
  let d (x : ∀ j, A j) := (φ (a x + W x)-φ (a x))/W x
  have hW0 (x : ∀ j, A j) : 0 ≤ W x := Finset.sum_nonneg (fun k hk => hw k hk x)
  have hWind (x : ∀ j, A j) (v : A i) : W (Function.update x i v) = W x := by
    simp only [W, hwind]
  have hd0 (x : ∀ j, A j) : 0 ≤ d x :=
    div_nonneg (sub_nonneg.mpr (hmono (by have := hW0 x; linarith))) (hW0 x)
  have hdind (x : ∀ j, A j) (v : A i) : d (Function.update x i v) = d x := by
    simp only [d, hWind, haind]
  have hid (x : ∀ j, A j) : W x * d x = φ (a x+W x)-φ (a x) := by
    by_cases hz : W x = 0
    · simp [d, hz]
    · dsimp [d]; field_simp
  have hpoint (x : ∀ j, A j) :
      φ (a x + ∑ k ∈ K, if x i ∈ T k then w k x else 0) ≤
      φ (a x) + ∑ k ∈ K, if x i ∈ T k then w k x*d x else 0 := by
    have hs : 0 ≤ ∑ k ∈ K, if x i ∈ T k then w k x else 0 := by
      apply Finset.sum_nonneg
      intro k hk; split_ifs <;> [exact hw k hk x; exact le_rfl]
    have hsw : (∑ k ∈ K, if x i ∈ T k then w k x else 0) ≤ W x := by
      apply Finset.sum_le_sum
      intro k hk; split_ifs <;> [exact le_rfl; exact hw k hk x]
    have hh := convex_chord_majorant φ hφ (a x) _ (W x) hs hsw
    dsimp only [d] at *
    apply hh.trans_eq
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs <;> ring
  have hbase : (∑ x, resample A i μ B c x * φ (a x)) = ∑ x, μ x * φ (a x) :=
    resample_preserves_test A i μ B hc (fun x => φ (a x)) (fun x v => by simp only [haind])
  have hterm (k : κ) (hk : k ∈ K) :
      (∑ x, resample A i μ B c x * if x i ∈ T k then w k x*d x else 0) ≤
      q * ∑ x, μ x * (w k x*d x) := by
    have hh := resample_coordinate_test_bound A i μ hμ B hc (T k)
      (fun x => w k x*d x) (fun x => mul_nonneg (hw k hk x) (hd0 x))
      (fun x v => by simp only [hwind, hdind])
    apply hh.trans
    apply mul_le_mul_of_nonneg_right (by simpa only [mul_div_assoc] using hT k hk)
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (hμ x) (mul_nonneg (hw k hk x) (hd0 x)))
  calc
    _ ≤ ∑ x, resample A i μ B c x * (φ (a x)+
        ∑ k ∈ K, if x i ∈ T k then w k x*d x else 0) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (resample_nonneg A i μ hμ B hc x))
    _ = (∑ x, μ x*φ (a x)) + ∑ k ∈ K,
        ∑ x, resample A i μ B c x * if x i ∈ T k then w k x*d x else 0 := by
      simp_rw [mul_add, Finset.mul_sum]
      rw [Finset.sum_add_distrib, hbase, Finset.sum_comm]
    _ ≤ (∑ x, μ x*φ (a x)) + ∑ k ∈ K, q * ∑ x, μ x * (w k x*d x) := by
      exact add_le_add_right (Finset.sum_le_sum (fun k hk => hterm k hk)) _
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      change _ + q * ∑ x, μ x * (W x*d x) = _
      simp_rw [hid, mul_sub]
      rw [Finset.sum_sub_distrib]
      dsimp [W]
      ring

#print axioms resample_binary_compression
end Erdos7CompressionSieve



/-! A finite binary-coordinate convex comparison for the distortion tower. -/
namespace Erdos7CompressionSieve
open scoped BigOperators
open Erdos7Distortion
set_option maxHeartbeats 4000000

section BoxCompression
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

lemma resample_boxCount_compression
    (i : ι) (μ : (∀ j, A j) → ℚ) (hμ : ∀ x, 0 ≤ μ x)
    (B : Finset (∀ j, A j)) (c : ℚ) (hc : 1 ≤ c)
    (φ : ℚ → ℚ) (hφ : ConvexOn ℚ Set.univ φ) (hmono : Monotone φ)
    (K : Finset κ) (S : κ → Finset ι) (X : κ → ∀ j, Finset (A j)) (q : ℚ)
    (hX : ∀ k ∈ K, i ∈ S k → c * fraction (X k i) ≤ q) :
    (∑ x, resample A i μ B c x * φ (∑ k ∈ K, boxIndicator A (S k) (X k) x)) ≤
      (1-q)*(∑ x, μ x * φ (∑ k ∈ K.filter (fun k => i ∉ S k), boxIndicator A ((S k).erase i) (X k) x)) +
      q*(∑ x, μ x * φ (∑ k ∈ K, boxIndicator A ((S k).erase i) (X k) x)) := by
  classical
  let K0 := K.filter (fun k => i ∉ S k)
  let K1 := K.filter (fun k => i ∈ S k)
  let a (x : ∀ j, A j) := ∑ k ∈ K0, boxIndicator A ((S k).erase i) (X k) x
  let w (k : κ) (x : ∀ j, A j) := boxIndicator A ((S k).erase i) (X k) x
  have hwind (k : κ) (x : ∀ j, A j) (v : A i) : w k (Function.update x i v) = w k x :=
    boxIndicator_update A _ _ i (Finset.notMem_erase _ _) x v
  have haind (x : ∀ j, A j) (v : A i) : a (Function.update x i v) = a x := by
    simp only [a, boxIndicator_update A _ _ i (Finset.notMem_erase _ _)]
  have hsum (x : ∀ j, A j) :
      a x + (∑ k ∈ K1, if x i ∈ X k i then w k x else 0) =
      ∑ k ∈ K, boxIndicator A (S k) (X k) x := by
    rw [← Finset.sum_filter_not_add_sum_filter K (fun k => i ∈ S k)]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      have hn := (Finset.mem_filter.mp hk).2
      simp only [Finset.erase_eq_of_notMem hn]
    · apply Finset.sum_congr rfl
      intro k hk
      exact (boxIndicator_erase A _ _ i (Finset.mem_filter.mp hk).2 x).symm
  have hsum' (x : ∀ j, A j) : a x + ∑ k ∈ K1, w k x =
      ∑ k ∈ K, boxIndicator A ((S k).erase i) (X k) x :=
    Finset.sum_filter_not_add_sum_filter K (fun k => i ∈ S k) _
  have hh := resample_binary_compression A i μ hμ B c hc φ hφ hmono a K1 w
    (fun k _ x => boxIndicator_nonneg A _ _ x) haind hwind (fun k => X k i) q (by
      intro k hk
      obtain ⟨hk,hi⟩ := Finset.mem_filter.mp hk
      simpa only [fraction, mul_div_assoc] using hX k hk hi)
  simpa only [hsum, hsum', a, K0] using hh
end BoxCompression

/-- Deleting one coordinate merges at most two support patterns. -/
lemma erase_pattern_multiplicity {ι κ : Type*} [DecidableEq ι] (K : Finset κ)
    (S : κ → Finset ι) (M : ℕ)
    (hM : ∀ U, (K.filter (fun k => S k = U)).card ≤ M) (i : ι) (U : Finset ι) :
    (K.filter (fun k => (S k).erase i = U)).card ≤ 2*M := by
  classical
  have hsub : K.filter (fun k => (S k).erase i = U) ⊆
      K.filter (fun k => S k = U) ∪ K.filter (fun k => S k = insert i U) := by
    intro k hk
    obtain ⟨hk,he⟩ := Finset.mem_filter.mp hk
    by_cases hi : i ∈ S k
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨hk, by rw [← he, Finset.insert_erase hi]⟩
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hk, by simpa only [Finset.erase_eq_of_notMem hi] using he⟩
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h1 := hM U
  have h2 := hM (insert i U)
  omega

lemma erase_absent_pattern_multiplicity {ι κ : Type*} [DecidableEq ι] (K : Finset κ)
    (S : κ → Finset ι) (M : ℕ)
    (hM : ∀ U, (K.filter (fun k => S k = U)).card ≤ M) (i : ι) (U : Finset ι) :
    ((K.filter (fun k => i ∉ S k)).filter (fun k => (S k).erase i = U)).card ≤ M := by
  classical
  apply (Finset.card_le_card (show (K.filter (fun k => i ∉ S k)).filter (fun k => (S k).erase i = U) ⊆
      K.filter (fun k => S k = U) from ?_)).trans (hM U)
  intro k hk
  obtain ⟨hk,he⟩ := Finset.mem_filter.mp hk
  obtain ⟨hk,hi⟩ := Finset.mem_filter.mp hk
  exact Finset.mem_filter.mpr ⟨hk, by simpa only [Finset.erase_eq_of_notMem hi] using he⟩

/-- The independent doubling envelope, defined by finite recursion only. -/
def binaryEnvelope {n : ℕ} (q : Fin n → ℚ) (φ : ℚ → ℚ) : ℕ → ℕ → ℚ
  | 0, M => φ M
  | t+1, M => if h : t < n then
      (1-q ⟨t,h⟩)*binaryEnvelope q φ t M + q ⟨t,h⟩*binaryEnvelope q φ t (2*M)
    else binaryEnvelope q φ t M

/-- A uniform support-multiplicity bound yields a genuine convex-order bound
for the finite distortion tower. Every active coordinate has one nonzero
exponent; no independence of the boxes or tower weights is assumed. -/
theorem tower_binary_convex_bound {n : ℕ} {κ : Type*}
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (B : Fin n → Finset (∀ i, A i)) (c q : Fin n → ℚ)
    (hc : ∀ i, 1 ≤ c i) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (φ : ℚ → ℚ) (hφ : ConvexOn ℚ Set.univ φ) (hmono : Monotone φ)
    (t : ℕ) (ht : t ≤ n) (M : ℕ) (K : Finset κ)
    (S : κ → Finset (Fin n)) (X : κ → ∀ i, Finset (A i))
    (hS : ∀ k ∈ K, ∀ i ∈ S k, i.val < t)
    (hX : ∀ k ∈ K, ∀ i ∈ S k, c i * fraction (X k i) ≤ q i)
    (hM : ∀ U, (K.filter (fun k => S k = U)).card ≤ M) :
    (∑ x, towerWeights A B c t x * φ (∑ k ∈ K, boxIndicator A (S k) (X k) x)) ≤
      binaryEnvelope q φ t M := by
  classical
  induction t generalizing M K S with
  | zero =>
    have hs (k : κ) (hk : k ∈ K) : S k = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have := hS k hk i hi
      omega
    have hcard : K.card ≤ M := by
      have hh := hM ∅
      have heq : K.filter (fun k => S k = ∅) = K := Finset.filter_true_of_mem hs
      rwa [heq] at hh
    have hvalue (x : ∀ i, A i) : (∑ k ∈ K, boxIndicator A (S k) (X k) x) = (K.card : ℚ) := by
      calc
        _ = ∑ _k ∈ K, (1 : ℚ) := Finset.sum_congr rfl (fun k hk => by rw [hs k hk, boxIndicator_empty])
        _ = _ := by simp
    simp_rw [hvalue]
    rw [← Finset.sum_mul, towerWeights_total A B c hc 0, one_mul]
    exact hmono (by exact_mod_cast hcard)
  | succ t ih =>
    let i : Fin n := ⟨t, by omega⟩
    let S' (k : κ) := (S k).erase i
    let K0 := K.filter (fun k => i ∉ S k)
    have hS' (k : κ) (hk : k ∈ K) (j : Fin n) (hj : j ∈ S' k) : j.val < t := by
      have hjmem := (Finset.mem_erase.mp hj).2
      have hjne := (Finset.mem_erase.mp hj).1
      have hh := hS k hk j hjmem
      have hne : j.val ≠ t := by intro he; exact hjne (Fin.ext he)
      omega
    have hX' (k : κ) (hk : k ∈ K) (j : Fin n) (hj : j ∈ S' k) :
        c j * fraction (X k j) ≤ q j := hX k hk j (Finset.mem_erase.mp hj).2
    have h0 := ih (by omega) M K0 S'
      (fun k hk => hS' k (Finset.mem_filter.mp hk).1)
      (fun k hk => hX' k (Finset.mem_filter.mp hk).1)
      (erase_absent_pattern_multiplicity K S M hM i)
    have h1 := ih (by omega) (2*M) K S' hS' hX' (erase_pattern_multiplicity K S M hM i)
    have hstep := resample_boxCount_compression A i (towerWeights A B c t)
      (towerWeights_nonneg A B c hc t) (B i) (c i) (hc i) φ hφ hmono K S X (q i)
      (fun k hk hi => hX k hk i hi)
    have hrec : towerWeights A B c (t+1) = resample A i (towerWeights A B c t) (B i) (c i) :=
      towerWeights_succ A B c i
    rw [hrec]
    apply hstep.trans
    have hh := add_le_add (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr (hq1 i)))
      (mul_le_mul_of_nonneg_left h1 (hq0 i))
    simpa only [binaryEnvelope, show t < n by omega, ↓reduceDIte, S', K0, i] using hh

#print axioms tower_binary_convex_bound
end Erdos7CompressionSieve



/-! A convex-compression covering criterion for distinct support patterns. -/
namespace Erdos7CompressionSieve
open scoped BigOperators
open Erdos7Distortion
set_option maxHeartbeats 4000000

/-- The covering inequality before any moment or convex-order majorization. -/
theorem coordinate_residual_cover_bound {n : ℕ}
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (B : Fin n → Finset (∀ i, A i)) (c : Fin n → ℚ) (hc : ∀ i, 1 ≤ c i)
    (hB : ∀ i j : Fin n, j < i → ∀ x v, Function.update x i v ∈ B j ↔ x ∈ B j)
    (hcover : ∀ x : ∀ i, A i, ∃ i, x ∈ B i) :
    1 ≤ ∑ i : Fin n, ∑ x : ∀ j, A j,
      towerWeights A B c i.val x * residual (c i) (coordinateFraction A i (B i) x) := by
  classical
  let μ := towerWeights A B c n
  have hμ : ∀ x, 0 ≤ μ x := towerWeights_nonneg A B c hc n
  have hpoint (x : ∀ i, A i) : μ x ≤ ∑ i : Fin n, if x ∈ B i then μ x else 0 := by
    obtain ⟨i,hi⟩ := hcover x
    have hh := Finset.single_le_sum (f := fun j : Fin n => if x ∈ B j then μ x else 0)
      (fun j _ => by dsimp only; split_ifs <;> [exact hμ x; exact le_rfl]) (Finset.mem_univ i)
    simpa only [if_pos hi] using hh
  have hunion : 1 ≤ ∑ i : Fin n, ∑ x ∈ B i, μ x := by
    have hh := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (∀ i, A i))) => hpoint x)
    rw [show (∑ x : ∀ i, A i, μ x) = 1 from towerWeights_total A B c hc n] at hh
    rw [Finset.sum_comm] at hh
    simpa only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter] using hh
  apply hunion.trans_eq
  apply Finset.sum_congr rfl
  intro i _
  have hret := towerWeights_retains_event A B c hc hB i n (by have := i.isLt; omega) le_rfl
  dsimp only [μ]
  rw [hret, towerWeights_succ A B c i]
  exact resample_excluded A i _ (B i) (hc i)

/-- The finite scalar budget associated with binary coordinate patterns. -/
def binaryCost {n : ℕ} (r c : Fin n → ℚ) : ℚ :=
  ∑ i, binaryEnvelope (fun j => c j*r j) (fun x => residual (c i) (r i*x)) i.val 1

lemma residual_scaled_convex (c r : ℚ) :
    ConvexOn ℚ Set.univ (fun x => residual c (r*x)) := by
  have heq : (fun x : ℚ => residual c (r*x)) = (fun x => max 0 ((c*r)*x+ (1-c))) := by
    funext x; dsimp [Erdos7Distortion.residual]; congr 1 <;> ring
  rw [heq]
  exact hinge_convex (c*r) (1-c)

lemma residual_scaled_monotone (c r : ℚ) (hc : 0 ≤ c) (hr : 0 ≤ r) :
    Monotone (fun x => residual c (r*x)) := by
  intro x y hxy
  apply max_le_max le_rfl
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxy hr) hc) _

/-- A cover by boxes with distinct nonempty support sets must have binary
compression cost at least one. This is the squarefree-support version of the
full distortion criterion, with the positive-part loss left exact. -/
theorem distinct_support_binary_bound {n : ℕ} {κ : Type*} [Fintype κ]
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (r c : Fin n → ℚ) (hr : ∀ i, 0 ≤ r i) (hc : ∀ i, 1 ≤ c i)
    (hcr : ∀ i, c i*r i ≤ 1)
    (S : κ → Finset (Fin n)) (hSinj : Function.Injective S) (hSne : ∀ k, (S k).Nonempty)
    (X : κ → ∀ i, Finset (A i)) (hX : ∀ k i, i ∈ S k → fraction (X k i) ≤ r i)
    (hcover : ∀ x : ∀ i, A i, ∃ k, ∀ i ∈ S k, x i ∈ X k i) :
    1 ≤ binaryCost r c := by
  classical
  let σ (k : κ) := (S k).max' (hSne k)
  have hσ (k : κ) : σ k ∈ S k := Finset.max'_mem _ _
  have hS (k : κ) (j : Fin n) (hj : j ∈ S k) : j ≤ σ k := Finset.le_max' _ _ hj
  let B := layeredBad A S X σ
  have hB : ∀ i j : Fin n, j < i → ∀ x v, Function.update x i v ∈ B j ↔ x ∈ B j := by
    intro i j hji x v
    exact layeredBad_invariant A S X σ hS i j hji x v
  have hbcover : ∀ x : ∀ i, A i, ∃ i, x ∈ B i := by
    intro x
    obtain ⟨k,hk⟩ := hcover x
    refine ⟨σ k,?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, by simp [layerFamily], hk⟩
  have hb := coordinate_residual_cover_bound A B c hc hB hbcover
  have hc0 : ∀ i, 0 ≤ c i := fun i => (by norm_num : (0:ℚ) ≤ 1).trans (hc i)
  apply hb.trans
  apply Finset.sum_le_sum
  intro i _
  let K := layerFamily σ i
  let S' (k : κ) := (S k).erase i
  let φ (x : ℚ) := residual (c i) (r i*x)
  have hprev (k : κ) (hk : k ∈ K) (j : Fin n) (hj : j ∈ S' k) : j.val < i.val := by
    have hki : σ k = i := (Finset.mem_filter.mp hk).2
    have hle := hS k j (Finset.mem_erase.mp hj).2
    rw [hki] at hle
    exact (show j < i from lt_of_le_of_ne hle (Finset.mem_erase.mp hj).1)
  have hmult (U : Finset (Fin n)) : (K.filter (fun k => S' k = U)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro k hk l hl
    have hkK := (Finset.mem_filter.mp hk).1
    have hlK := (Finset.mem_filter.mp hl).1
    have hki : i ∈ S k := by simpa only [(Finset.mem_filter.mp hkK).2] using hσ k
    have hli : i ∈ S l := by simpa only [(Finset.mem_filter.mp hlK).2] using hσ l
    apply hSinj
    have he : (S k).erase i = (S l).erase i :=
      (Finset.mem_filter.mp hk).2.trans (Finset.mem_filter.mp hl).2.symm
    have hh := congrArg (insert i) he
    simpa only [Finset.insert_erase hki, Finset.insert_erase hli] using hh
  have hpoint (x : ∀ j, A j) : coordinateFraction A i (B i) x ≤
      r i * ∑ k ∈ K, boxIndicator A (S' k) (X k) x := by
    apply (layered_fraction_bound A S X σ hσ i x).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hki : i ∈ S k := by simpa only [(Finset.mem_filter.mp hk).2] using hσ k
    exact mul_le_mul_of_nonneg_right (hX k i hki) (boxIndicator_nonneg A _ _ x)
  have hcomp := tower_binary_convex_bound A B c (fun j => c j*r j) hc
    (fun j => mul_nonneg (hc0 j) (hr j)) hcr φ
    (residual_scaled_convex _ _) (residual_scaled_monotone _ _ (hc0 i) (hr i))
    i.val i.isLt.le 1 K S' X hprev
    (fun k hk j hj => mul_le_mul_of_nonneg_left (hX k j (Finset.mem_erase.mp hj).2) (hc0 j)) hmult
  apply (Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (show
      residual (c i) (coordinateFraction A i (B i) x) ≤ φ (∑ k ∈ K, boxIndicator A (S' k) (X k) x) from
        max_le_max le_rfl (sub_le_sub_right (mul_le_mul_of_nonneg_left (hpoint x) (hc0 i)) _))
      (towerWeights_nonneg A B c hc i.val x))).trans hcomp

#print axioms distinct_support_binary_bound
end Erdos7CompressionSieve



/-! Integer-rounded finite-prefix candidate for the binary compression sieve.
The integer evaluation is checked by the kernel. Its connection to binaryCost
will be proved separately; this certificate alone does not settle Erdos 7. -/
namespace Erdos7BinarySieve
set_option maxHeartbeats 40000000
set_option maxRecDepth 200000

def scale : ℕ := 1000000000

def capData (p : ℕ) : ℕ × ℕ :=
  if p = 3 then (1,2) else
  if p = 5 then (1,3) else
  if p = 7 then (1,5) else
  if p = 11 then (1,7) else
  if p = 13 then (1,9) else
  if p = 17 then (1,13) else
  if p = 19 then (1,15) else
  if p = 23 then (1,15) else
  if p = 29 then (1,21) else
  if p = 31 then (1,23) else
  if p = 37 then (1,29) else
  if p = 41 then (1,25) else
  if p = 43 then (1,27) else
  if p = 47 then (1,31) else
  if p = 53 then (1,37) else
  if p = 59 then (1,43) else
  if p = 61 then (1,45) else
  (5,4*p)

structure RoundedState where
  mean : ℕ
  second : ℕ
  cost : ℕ
  probs : List ℕ
  deriving DecidableEq

def roundedInitial : RoundedState := ⟨scale,scale,0,scale :: List.replicate 11 0⟩

def roundedBinaryStep (s : RoundedState) (p : ℕ) : RoundedState :=
  let a := (capData p).1
  let b := (capData p).2
  let d := p*a-b
  let u := a*s.mean + ((List.range 12).map (fun k => (d-a*2^k)*s.probs[k]?.getD 0)).sum
  ⟨((b+a)*s.mean ⌈/⌉ b), ((b+3*a)*s.second ⌈/⌉ b),
    s.cost+((u-d*scale) ⌈/⌉ b),
    List.zipWith (fun x y => ((b-a)*x+a*y) ⌈/⌉ b) s.probs (0 :: s.probs)⟩

def binaryPrefixPrimes : List ℕ := 3 :: Erdos7No23Sieve.prefixPrimes

def roundedBinaryPrefix : RoundedState := binaryPrefixPrimes.foldl roundedBinaryStep roundedInitial

theorem roundedBinaryPrefix_certificate : roundedBinaryPrefix =
    ⟨13193269606,1140022148216,532950443,[45519299, 161772919, 255836680, 245569486, 163619413, 81694162, 32127951, 10307726, 2769469, 636112, 127238, 22825]⟩ := by
  decide +kernel

theorem roundedBinaryPrefix_potential_lt_one :
    (roundedBinaryPrefix.cost : ℚ)/scale +
      (16/5 : ℚ)*(roundedBinaryPrefix.second : ℚ)/scale/10080 < 1 := by
  rw [roundedBinaryPrefix_certificate]
  norm_num [scale]

#print axioms roundedBinaryPrefix_certificate
#print axioms roundedBinaryPrefix_potential_lt_one
end Erdos7BinarySieve



/-! Finite Bernoulli laws and their exact relation to the binary envelope. -/
namespace Erdos7BinarySieve
open scoped BigOperators
open Erdos7CompressionSieve Erdos7Distortion
set_option maxHeartbeats 3000000

noncomputable def expect (μ : ℕ →₀ ℚ) (f : ℕ → ℚ) : ℚ := μ.sum (fun k w => w*f k)
noncomputable def lawStep (q : ℚ) (μ : ℕ →₀ ℚ) : ℕ →₀ ℚ :=
  (1-q) • μ + q • μ.mapDomain Nat.succ
noncomputable def initialLaw : ℕ →₀ ℚ := Finsupp.single 0 1

lemma expect_congr (μ : ℕ →₀ ℚ) (f g : ℕ → ℚ) (h : ∀ k, f k = g k) :
    expect μ f = expect μ g := by unfold expect; exact Finsupp.sum_congr (fun k _ => by rw [h k])
lemma expect_add (μ : ℕ →₀ ℚ) (f g : ℕ → ℚ) :
    expect μ (fun k => f k+g k) = expect μ f + expect μ g := by
  simp only [expect, mul_add, Finsupp.sum_add]
lemma expect_sub (μ : ℕ →₀ ℚ) (f g : ℕ → ℚ) :
    expect μ (fun k => f k-g k) = expect μ f - expect μ g := by
  simp only [expect, mul_sub, Finsupp.sum, Finset.sum_sub_distrib]
lemma expect_mul (μ : ℕ →₀ ℚ) (a : ℚ) (f : ℕ → ℚ) :
    expect μ (fun k => a*f k) = a*expect μ f := by
  simp only [expect, Finsupp.sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
lemma expect_const (μ : ℕ →₀ ℚ) (a : ℚ) : expect μ (fun _ => a) = a*expect μ (fun _ => 1) := by
  simpa only [mul_one] using expect_mul μ a (fun _ => 1)
lemma expect_nonneg (μ : ℕ →₀ ℚ) (hμ : ∀ k, 0 ≤ μ k) (f : ℕ → ℚ) (hf : ∀ k, 0 ≤ f k) :
    0 ≤ expect μ f := Finsupp.sum_nonneg (fun k _ => mul_nonneg (hμ k) (hf k))
lemma expect_le (μ : ℕ →₀ ℚ) (hμ : ∀ k, 0 ≤ μ k) (f g : ℕ → ℚ) (h : ∀ k, f k ≤ g k) :
    expect μ f ≤ expect μ g := Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (h k) (hμ k))

lemma expect_lawStep (q : ℚ) (μ : ℕ →₀ ℚ) (f : ℕ → ℚ) :
    expect (lawStep q μ) f = (1-q)*expect μ f+q*expect μ (fun k => f (k+1)) := by
  unfold expect lawStep
  rw [Finsupp.sum_add_index (by intros; simp) (by intros; ring)]
  rw [Finsupp.sum_smul_index (by intros; simp), Finsupp.sum_smul_index (by intros; simp)]
  rw [Finsupp.sum_mapDomain_index (by intros; simp) (by intros; ring)]
  simp only [Finsupp.sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

lemma expect_initialLaw (f : ℕ → ℚ) : expect initialLaw f = f 0 := by
  simp [expect, initialLaw]

lemma lawStep_zero (q : ℚ) (μ : ℕ →₀ ℚ) : lawStep q μ 0 = (1-q)*μ 0 := by
  have h : μ.mapDomain Nat.succ 0 = 0 := by
    apply Finsupp.mapDomain_notin_range
    simp
  simp [lawStep, h]

lemma lawStep_succ (q : ℚ) (μ : ℕ →₀ ℚ) (k : ℕ) :
    lawStep q μ (k+1) = (1-q)*μ (k+1)+q*μ k := by
  simp only [lawStep, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.mapDomain_apply Nat.succ_injective]

lemma lawStep_nonneg (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (μ : ℕ →₀ ℚ)
    (hμ : ∀ k, 0 ≤ μ k) : ∀ k, 0 ≤ lawStep q μ k := by
  intro k
  cases k with
  | zero => rw [lawStep_zero]; exact mul_nonneg (sub_nonneg.mpr hq1) (hμ 0)
  | succ k =>
    rw [lawStep_succ]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hq1) (hμ _)) (mul_nonneg hq0 (hμ _))

lemma lawStep_mass (q : ℚ) (μ : ℕ →₀ ℚ) :
    expect (lawStep q μ) (fun _ => 1) = expect μ (fun _ => 1) := by rw [expect_lawStep]; ring
lemma lawStep_mean (q : ℚ) (μ : ℕ →₀ ℚ) :
    expect (lawStep q μ) (fun k => (2:ℚ)^k) = (1+q)*expect μ (fun k => (2:ℚ)^k) := by
  rw [expect_lawStep]
  have hh := expect_mul μ 2 (fun k => (2:ℚ)^k)
  simp_rw [pow_succ, mul_comm ((2:ℚ)^_) 2]
  rw [hh]; ring
lemma lawStep_second (q : ℚ) (μ : ℕ →₀ ℚ) :
    expect (lawStep q μ) (fun k => (4:ℚ)^k) = (1+3*q)*expect μ (fun k => (4:ℚ)^k) := by
  rw [expect_lawStep]
  have hh := expect_mul μ 4 (fun k => (4:ℚ)^k)
  simp_rw [pow_succ, mul_comm ((4:ℚ)^_) 4]
  rw [hh]; ring

noncomputable def prefixLaw {n : ℕ} (q : Fin n → ℚ) : ℕ → (ℕ →₀ ℚ)
  | 0 => initialLaw
  | t+1 => if h : t<n then lawStep (q ⟨t,h⟩) (prefixLaw q t) else prefixLaw q t

lemma prefixLaw_mass {n : ℕ} (q : Fin n → ℚ) (t : ℕ) :
    expect (prefixLaw q t) (fun _ => 1) = 1 := by
  induction t with
  | zero => simp only [prefixLaw, expect_initialLaw]
  | succ t ih => unfold prefixLaw; split_ifs <;> simp only [lawStep_mass, ih]

lemma prefixLaw_nonneg {n : ℕ} (q : Fin n → ℚ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (t k : ℕ) : 0 ≤ prefixLaw q t k := by
  induction t generalizing k with
  | zero => simp [prefixLaw, initialLaw, Finsupp.single_apply]; positivity
  | succ t ih =>
    unfold prefixLaw
    split_ifs with h
    · exact lawStep_nonneg _ (hq0 _) (hq1 _) _ ih k
    · exact ih k

/-- Exact interpretation of the envelope by a finite law. -/
theorem binaryEnvelope_eq_expect {n : ℕ} (q : Fin n → ℚ) (φ : ℚ → ℚ) (t M : ℕ) :
    binaryEnvelope q φ t M = expect (prefixLaw q t) (fun k => φ ((M:ℚ)*2^k)) := by
  induction t generalizing M with
  | zero => simp [binaryEnvelope, prefixLaw, expect_initialLaw]
  | succ t ih =>
    simp only [binaryEnvelope, prefixLaw]
    split_ifs with h
    · rw [expect_lawStep, ih, ih]
      congr 1
      congr 1
      apply expect_congr
      intro k
      congr 1
      simp only [Nat.cast_mul, Nat.cast_ofNat, pow_succ]
      ring
    · exact ih M

lemma expect_eq_sum_range (μ : ℕ →₀ ℚ) (f : ℕ → ℚ) (R : ℕ) (hf : ∀ k, R ≤ k → f k=0) :
    expect μ f = ∑ k ∈ Finset.range R, μ k*f k := by
  classical
  let S := μ.support.filter (fun k => k<R)
  have h1 : (∑ k ∈ S, μ k*f k) = expect μ f := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hkn
    have hh : ¬k<R := by intro h; exact hkn (Finset.mem_filter.mpr ⟨hk,h⟩)
    rw [hf k (by omega), mul_zero]
  have h2 : (∑ k ∈ S, μ k*f k) = ∑ k ∈ Finset.range R, μ k*f k := by
    apply Finset.sum_subset (show S ⊆ Finset.range R from fun k hk => Finset.mem_range.mpr (Finset.mem_filter.mp hk).2)
    intro k hk hkn
    have hh : k ∉ μ.support := by intro h; exact hkn (Finset.mem_filter.mpr ⟨h,Finset.mem_range.mp hk⟩)
    rw [Finsupp.notMem_support_iff.mp hh, zero_mul]
  exact h1.symm.trans h2

lemma natSub_cast (a b : ℕ) : ((a-b : ℕ) : ℚ) = max 0 ((a:ℚ)-b) := by
  by_cases h : b ≤ a
  · have hQ : (b:ℚ) ≤ a := by exact_mod_cast h
    rw [Nat.cast_sub h, max_eq_right (sub_nonneg.mpr hQ)]
  · rw [Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero, max_eq_left]
    have hh : (a:ℚ) ≤ b := by exact_mod_cast (by omega : a ≤ b)
    linarith

/-- The exact positive-part loss uses only a mean and finitely many low-count
probabilities once its threshold is bounded. -/
theorem expect_hinge_formula (μ : ℕ →₀ ℚ) (hmass : expect μ (fun _ => 1)=1)
    (a d b R : ℕ) (hb : 0 < b) (hR : d ≤ a*2^R) :
    expect μ (fun k => max 0 (((a:ℚ)*2^k-d)/b)) =
      ((a:ℚ)*expect μ (fun k => (2:ℚ)^k) - d +
        ∑ k ∈ Finset.range R, ((d-a*2^k : ℕ):ℚ)*μ k) / b := by
  have hbQ : (0:ℚ)<b := by exact_mod_cast hb
  have hpoint (k : ℕ) : max 0 (((a:ℚ)*2^k-d)/b) =
      ((a:ℚ)*2^k-d+((d-a*2^k : ℕ):ℚ))/b := by
    rw [natSub_cast]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    by_cases h : (d:ℚ) ≤ (a:ℚ)*2^k
    · rw [max_eq_left (by linarith : (d:ℚ)-a*2^k ≤ 0), add_zero,
        max_eq_right (div_nonneg (by linarith) hbQ.le)]
    · have hh : (a:ℚ)*2^k ≤ d := le_of_lt (lt_of_not_ge h)
      rw [max_eq_right (by linarith : 0 ≤ (d:ℚ)-a*2^k),
        max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hbQ.le)]
      ring
  rw [expect_congr μ _ _ hpoint]
  simp only [div_eq_mul_inv]
  have heq : expect μ (fun k => ((a:ℚ)*2^k-d+((d-a*2^k:ℕ):ℚ))*(b:ℚ)⁻¹) =
      (b:ℚ)⁻¹ * expect μ (fun k => (a:ℚ)*2^k-d+((d-a*2^k:ℕ):ℚ)) := by
    simpa only [mul_comm] using expect_mul μ (b:ℚ)⁻¹ (fun k => (a:ℚ)*2^k-d+((d-a*2^k:ℕ):ℚ))
  rw [heq, expect_add, expect_sub, expect_mul, expect_const, hmass, mul_one]
  have htrunc := expect_eq_sum_range μ (fun k => ((d-a*2^k:ℕ):ℚ)) R (by
    intro k hk
    have hh : d ≤ a*2^k := hR.trans (Nat.mul_le_mul_left a (Nat.pow_le_pow_right (by omega) hk))
    simp only [Nat.sub_eq_zero_of_le hh, Nat.cast_zero])
  rw [htrunc]
  simp only [mul_comm]

#print axioms binaryEnvelope_eq_expect
#print axioms expect_hinge_formula
end Erdos7BinarySieve



/-! Rational domination lemmas for the rounded binary prefix. -/
namespace Erdos7BinarySieve
open scoped BigOperators
open Erdos7CompressionSieve Erdos7Distortion
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

lemma scale_pos : (0:ℚ) < scale := by norm_num [scale]
lemma capData_bounds (p : ℕ) (hp : 3 ≤ p) :
    0 < (capData p).1 ∧ (capData p).1 ≤ (capData p).2 ∧ (capData p).2 < p*(capData p).1 := by
  by_cases h3 : p = 3
  · subst p; norm_num [capData]
  by_cases h5 : p = 5
  · subst p; norm_num [capData]
  by_cases h7 : p = 7
  · subst p; norm_num [capData]
  by_cases h11 : p = 11
  · subst p; norm_num [capData]
  by_cases h13 : p = 13
  · subst p; norm_num [capData]
  by_cases h17 : p = 17
  · subst p; norm_num [capData]
  by_cases h19 : p = 19
  · subst p; norm_num [capData]
  by_cases h23 : p = 23
  · subst p; norm_num [capData]
  by_cases h29 : p = 29
  · subst p; norm_num [capData]
  by_cases h31 : p = 31
  · subst p; norm_num [capData]
  by_cases h37 : p = 37
  · subst p; norm_num [capData]
  by_cases h41 : p = 41
  · subst p; norm_num [capData]
  by_cases h43 : p = 43
  · subst p; norm_num [capData]
  by_cases h47 : p = 47
  · subst p; norm_num [capData]
  by_cases h53 : p = 53
  · subst p; norm_num [capData]
  by_cases h59 : p = 59
  · subst p; norm_num [capData]
  by_cases h61 : p = 61
  · subst p; norm_num [capData]
  simp only [capData, if_neg h3, if_neg h5, if_neg h7, if_neg h11, if_neg h13, if_neg h17, if_neg h19, if_neg h23, if_neg h29, if_neg h31, if_neg h37, if_neg h41, if_neg h43, if_neg h47, if_neg h53, if_neg h59, if_neg h61]
  omega
lemma capData_threshold (p : ℕ) (hp : p < 10080) :
    p*(capData p).1-(capData p).2 ≤ (capData p).1*2^12 := by
  by_cases h3 : p = 3
  · subst p; norm_num [capData]
  by_cases h5 : p = 5
  · subst p; norm_num [capData]
  by_cases h7 : p = 7
  · subst p; norm_num [capData]
  by_cases h11 : p = 11
  · subst p; norm_num [capData]
  by_cases h13 : p = 13
  · subst p; norm_num [capData]
  by_cases h17 : p = 17
  · subst p; norm_num [capData]
  by_cases h19 : p = 19
  · subst p; norm_num [capData]
  by_cases h23 : p = 23
  · subst p; norm_num [capData]
  by_cases h29 : p = 29
  · subst p; norm_num [capData]
  by_cases h31 : p = 31
  · subst p; norm_num [capData]
  by_cases h37 : p = 37
  · subst p; norm_num [capData]
  by_cases h41 : p = 41
  · subst p; norm_num [capData]
  by_cases h43 : p = 43
  · subst p; norm_num [capData]
  by_cases h47 : p = 47
  · subst p; norm_num [capData]
  by_cases h53 : p = 53
  · subst p; norm_num [capData]
  by_cases h59 : p = 59
  · subst p; norm_num [capData]
  by_cases h61 : p = 61
  · subst p; norm_num [capData]
  simp only [capData, if_neg h3, if_neg h5, if_neg h7, if_neg h11, if_neg h13, if_neg h17, if_neg h19, if_neg h23, if_neg h29, if_neg h31, if_neg h37, if_neg h41, if_neg h43, if_neg h47, if_neg h53, if_neg h59, if_neg h61]
  omega
lemma capData_large (p : ℕ) (hp : 67 ≤ p) : capData p = (5,4*p) := by
  simp only [capData, if_neg (show p ≠ 3 by omega), if_neg (show p ≠ 5 by omega), if_neg (show p ≠ 7 by omega), if_neg (show p ≠ 11 by omega), if_neg (show p ≠ 13 by omega), if_neg (show p ≠ 17 by omega), if_neg (show p ≠ 19 by omega), if_neg (show p ≠ 23 by omega), if_neg (show p ≠ 29 by omega), if_neg (show p ≠ 31 by omega), if_neg (show p ≠ 37 by omega), if_neg (show p ≠ 41 by omega), if_neg (show p ≠ 43 by omega), if_neg (show p ≠ 47 by omega), if_neg (show p ≠ 53 by omega), if_neg (show p ≠ 59 by omega), if_neg (show p ≠ 61 by omega)]

def rate (p : ℕ) : ℚ := (capData p).1/(capData p).2
def cap (p : ℕ) : ℚ := p*rate p

lemma rate_nonneg (p : ℕ) : 0 ≤ rate p := by unfold rate; positivity
lemma rate_le_one (p : ℕ) (hp : 3 ≤ p) : rate p ≤ 1 := by
  have h := capData_bounds p hp
  exact (div_le_one (by exact_mod_cast h.1.trans_le h.2.1)).mpr (by exact_mod_cast h.2.1)
lemma cap_gt_one (p : ℕ) (hp : 3 ≤ p) : 1 < cap p := by
  have h := capData_bounds p hp
  dsimp [cap, rate]
  rw [← mul_div_assoc]
  apply (one_lt_div (by exact_mod_cast h.1.trans_le h.2.1)).mpr
  exact_mod_cast h.2.2
lemma cap_large (p : ℕ) (hp : 67 ≤ p) : cap p = 5/4 := by
  have hpQ : (0:ℚ)<p := by exact_mod_cast (by omega : 0<p)
  simp only [cap, rate, capData_large p hp, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

noncomputable def loss (μ : ℕ →₀ ℚ) (p : ℕ) : ℚ :=
  expect μ (fun k => Erdos7Distortion.residual (cap p) ((2:ℚ)^k/p))

lemma loss_nonneg (μ : ℕ →₀ ℚ) (hμ : ∀ k, 0 ≤ μ k) (p : ℕ) : 0 ≤ loss μ p :=
  expect_nonneg μ hμ _ (fun k => residual_nonneg _ _)

lemma loss_formula (μ : ℕ →₀ ℚ) (hmass : expect μ (fun _ => 1)=1)
    (p : ℕ) (hp : 3 ≤ p) (hpR : p < 10080) :
    loss μ p =
      ((capData p).1*expect μ (fun k => (2:ℚ)^k) - (p*(capData p).1-(capData p).2 : ℕ) +
        ∑ k ∈ Finset.range 12, ((p*(capData p).1-(capData p).2-(capData p).1*2^k : ℕ):ℚ)*μ k) /
        (capData p).2 := by
  have h := capData_bounds p hp
  have hb : 0 < (capData p).2 := h.1.trans_le h.2.1
  have hpQ : (p:ℚ) ≠ 0 := by exact_mod_cast (by omega : p≠0)
  have hbQ : ((capData p).2:ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hpoint (k : ℕ) : Erdos7Distortion.residual (cap p) ((2:ℚ)^k/p) =
      max 0 ((((capData p).1:ℚ)*2^k - ((p*(capData p).1-(capData p).2:ℕ):ℚ))/(capData p).2) := by
    dsimp [Erdos7Distortion.residual, cap, rate]
    congr 1
    rw [Nat.cast_sub h.2.2.le, Nat.cast_mul]
    field_simp <;> ring
  unfold loss
  rw [expect_congr μ _ _ hpoint]
  exact expect_hinge_formula μ hmass _ _ _ 12 hb (capData_threshold p hpR)

/-- Multiplicative rounding with a common scale. -/
lemma rounded_linear_bound (x : ℚ) (u a b : ℕ) (hb : 0 < b) (hx : x ≤ (u:ℚ)/scale) :
    (a:ℚ)/b*x ≤ ((a*u ⌈/⌉ b : ℕ):ℚ)/scale := by
  have hround := Erdos7No23Sieve.nat_div_le_rounded (a*u) b hb
  have hm := mul_le_mul_of_nonneg_left hx (by positivity : (0:ℚ) ≤ (a:ℚ)/b)
  apply hm.trans
  have hh := div_le_div_of_nonneg_right hround scale_pos.le
  simp only [Nat.cast_mul] at hh
  convert hh using 1 <;> ring

/-- Saturating natural subtraction is a valid upper rounding for a rational
loss expression; no unjustified subtraction of upper bounds is used. -/
lemma rounded_sub_bound (x : ℚ) (u v b : ℕ) (hb : 0 < b) (hx : x ≤ (u:ℚ)/scale) :
    (x-v)/b ≤ (((u-v*scale) ⌈/⌉ b : ℕ):ℚ)/scale := by
  have hxs := (le_div_iff₀ scale_pos).mp hx
  have hsub : (u:ℚ)-(v:ℚ)*scale ≤ ((u-v*scale:ℕ):ℚ) := by
    rw [natSub_cast, Nat.cast_mul]
    exact le_max_right _ _
  have hr := Erdos7No23Sieve.nat_div_le_rounded (u-v*scale) b hb
  have hbQ : (0:ℚ)<b := by exact_mod_cast hb
  have hr' := (div_le_iff₀ hbQ).mp hr
  apply (le_div_iff₀ scale_pos).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hbQ).mpr
  nlinarith

def probAt (s : RoundedState) (k : ℕ) : ℕ := s.probs[k]?.getD 0
def prevProbAt (s : RoundedState) (k : ℕ) : ℕ := (0 :: s.probs)[k]?.getD 0

lemma roundedBinaryStep_length (s : RoundedState) (p : ℕ) :
    (roundedBinaryStep s p).probs.length = s.probs.length := by
  simp [roundedBinaryStep, List.length_zipWith]

lemma roundedBinaryStep_prob (s : RoundedState) (p k : ℕ) (hk : k < s.probs.length) :
    probAt (roundedBinaryStep s p) k =
      (((capData p).2-(capData p).1)*probAt s k+(capData p).1*prevProbAt s k) ⌈/⌉ (capData p).2 := by
  simp only [probAt, prevProbAt, roundedBinaryStep, List.getElem?_zipWith,
    List.getElem?_eq_getElem hk, List.getElem?_eq_getElem (by simp; omega : k < (0::s.probs).length),
    Option.getD_some]

lemma prevProbAt_zero (s : RoundedState) : prevProbAt s 0 = 0 := rfl
lemma prevProbAt_succ (s : RoundedState) (k : ℕ) : prevProbAt s (k+1) = probAt s k := rfl

lemma listRange_sum (f : ℕ → ℕ) (R : ℕ) : ((List.range R).map f).sum = ∑ k ∈ Finset.range R, f k := by
  simpa only [List.toFinset_range] using (List.sum_toFinset f List.nodup_range).symm

#print axioms loss_formula
end Erdos7BinarySieve



/-! Domination of the exact finite Bernoulli computation by integer rounding. -/
namespace Erdos7BinarySieve
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

structure LawState where
  law : ℕ →₀ ℚ
  cost : ℚ

noncomputable def lawInitial : LawState := ⟨initialLaw,0⟩
noncomputable def stateStep (s : LawState) (p : ℕ) : LawState :=
  ⟨lawStep (rate p) s.law, s.cost+loss s.law p⟩

structure RoundDominates (s : RoundedState) (t : LawState) : Prop where
  len : s.probs.length = 12
  nonneg : ∀ k, 0 ≤ t.law k
  mass : expect t.law (fun _ => 1) = 1
  mean : expect t.law (fun k => (2:ℚ)^k) ≤ (s.mean:ℚ)/scale
  second : expect t.law (fun k => (4:ℚ)^k) ≤ (s.second:ℚ)/scale
  cost : t.cost ≤ (s.cost:ℚ)/scale
  prob : ∀ k < 12, t.law k ≤ (probAt s k:ℚ)/scale

lemma lawStep_rate (p : ℕ) (hp : 3 ≤ p) (μ : ℕ →₀ ℚ) (k : ℕ) :
    lawStep (rate p) μ k =
      ((((capData p).2-(capData p).1:ℕ):ℚ)*μ k + (capData p).1*(if k=0 then 0 else μ (k-1)))/(capData p).2 := by
  have h := capData_bounds p hp
  have hb : ((capData p).2:ℚ) ≠ 0 := by exact_mod_cast (h.1.trans_le h.2.1).ne'
  rw [Nat.cast_sub h.2.1]
  cases k with
  | zero => rw [lawStep_zero]; simp only [if_pos rfl, mul_zero, add_zero]; dsimp [rate]; field_simp <;> ring
  | succ k => rw [lawStep_succ]; simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]; dsimp [rate]; field_simp <;> ring

lemma roundedStep_dominates_law (s : RoundedState) (t : LawState) (h : RoundDominates s t)
    (p : ℕ) (hp : 3 ≤ p) (hpR : p < 10080) :
    RoundDominates (roundedBinaryStep s p) (stateStep t p) := by
  let a := (capData p).1
  let b := (capData p).2
  let d := p*a-b
  let u := a*s.mean + ((List.range 12).map (fun k => (d-a*2^k)*probAt s k)).sum
  have hb : 0 < b := (capData_bounds p hp).1.trans_le (capData_bounds p hp).2.1
  have hbQ : (b:ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  refine ⟨(roundedBinaryStep_length s p).trans h.len,
    lawStep_nonneg _ (rate_nonneg p) (rate_le_one p hp) _ h.nonneg,
    (lawStep_mass _ _).trans h.mass, ?_, ?_, ?_, ?_⟩
  · change expect (lawStep (rate p) t.law) (fun k => (2:ℚ)^k) ≤ _
    rw [lawStep_mean]
    have hh := rounded_linear_bound _ s.mean (b+a) b hb h.mean
    change _ ≤ ((roundedBinaryStep s p).mean:ℚ)/scale
    convert hh using 1
    dsimp [rate, a, b]
    push_cast
    field_simp [show ((capData p).2:ℚ) ≠ 0 from hbQ] <;> ring
  · change expect (lawStep (rate p) t.law) (fun k => (4:ℚ)^k) ≤ _
    rw [lawStep_second]
    have hh := rounded_linear_bound _ s.second (b+3*a) b hb h.second
    change _ ≤ ((roundedBinaryStep s p).second:ℚ)/scale
    convert hh using 1
    dsimp [rate, a, b]
    push_cast
    field_simp [show ((capData p).2:ℚ) ≠ 0 from hbQ] <;> ring
  · have hnum : (a:ℚ)*expect t.law (fun k => (2:ℚ)^k)+
        ∑ k ∈ Finset.range 12, ((d-a*2^k:ℕ):ℚ)*t.law k ≤ (u:ℚ)/scale := by
      have hfirst := mul_le_mul_of_nonneg_left h.mean (by positivity : (0:ℚ) ≤ a)
      have hsum := Finset.sum_le_sum (s := Finset.range 12) (fun k hk =>
        mul_le_mul_of_nonneg_left (h.prob k (Finset.mem_range.mp hk))
          (by positivity : (0:ℚ) ≤ (d-a*2^k:ℕ)))
      apply (add_le_add hfirst hsum).trans_eq
      dsimp [u]
      rw [listRange_sum]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sum, add_div, Finset.sum_div]
      congr 1
      · ring
      · apply Finset.sum_congr rfl; intro k hk; ring
    have hround := rounded_sub_bound _ u d b hb hnum
    have hloss : loss t.law p ≤ (((u-d*scale) ⌈/⌉ b:ℕ):ℚ)/scale := by
      rw [loss_formula t.law h.mass p hp hpR]
      convert hround using 1 <;> dsimp [a,b,d] <;> ring
    have hh := add_le_add h.cost hloss
    change t.cost+loss t.law p ≤ ((roundedBinaryStep s p).cost:ℚ)/scale
    apply hh.trans_eq
    simp only [roundedBinaryStep, Nat.cast_add, add_div]
    rfl
  · intro k hk
    have hprev : (if k=0 then (0:ℚ) else t.law (k-1)) ≤ (prevProbAt s k:ℚ)/scale := by
      cases k with
      | zero => simp only [if_pos rfl, prevProbAt_zero, Nat.cast_zero, zero_div]; exact le_rfl
      | succ k =>
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, prevProbAt_succ]
        exact h.prob k (by omega)
    have hcur := h.prob k hk
    have hnum : (((b-a:ℕ):ℚ)*t.law k+(a:ℚ)*(if k=0 then 0 else t.law (k-1))) ≤
        (((b-a)*probAt s k+a*prevProbAt s k:ℕ):ℚ)/scale := by
      apply (add_le_add (mul_le_mul_of_nonneg_left hcur (by positivity : (0:ℚ) ≤ (b-a:ℕ)))
        (mul_le_mul_of_nonneg_left hprev (by positivity : (0:ℚ) ≤ a))).trans_eq
      simp only [Nat.cast_add, Nat.cast_mul]
      ring
    have hh := rounded_linear_bound _ ((b-a)*probAt s k+a*prevProbAt s k) 1 b hb hnum
    change lawStep (rate p) t.law k ≤ (probAt (roundedBinaryStep s p) k:ℚ)/scale
    rw [roundedBinaryStep_prob s p k (by rw [h.len]; exact hk), lawStep_rate p hp]
    simpa only [Nat.one_mul, Nat.cast_one, one_div, inv_mul_eq_div, a, b] using hh

lemma roundedInitial_dominates : RoundDominates roundedInitial lawInitial := by
  constructor
  · simp [roundedInitial]
  · intro k; simp [lawInitial, initialLaw, Finsupp.single_apply]; positivity
  · exact expect_initialLaw _
  · norm_num [lawInitial, expect_initialLaw, roundedInitial, scale]
  · norm_num [lawInitial, expect_initialLaw, roundedInitial, scale]
  · norm_num [lawInitial, roundedInitial, scale]
  · intro k hk
    by_cases hz : k=0
    · subst k; norm_num [lawInitial, initialLaw, probAt, roundedInitial, scale]
    · have hh : lawInitial.law k = 0 := by simp [lawInitial, initialLaw, Finsupp.single_apply, hz]
      rw [hh]; positivity

lemma roundedFold_dominates_law (L : List ℕ) (hL : ∀ p ∈ L, 3 ≤ p ∧ p<10080)
    (s : RoundedState) (t : LawState) (h : RoundDominates s t) :
    RoundDominates (L.foldl roundedBinaryStep s) (L.foldl stateStep t) := by
  induction L generalizing s t with
  | nil => exact h
  | cons p L ih =>
    simp only [List.foldl_cons]
    have hp := hL p List.mem_cons_self
    exact ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)) _ _
      (roundedStep_dominates_law s t h p hp.1 hp.2)

noncomputable def lawPrefix : LawState := binaryPrefixPrimes.foldl stateStep lawInitial

/-- The kernel-rounded prefix now bounds the actual finite Bernoulli law and
its actual accumulated positive-part distortion cost. -/
theorem lawPrefix_dominated : RoundDominates roundedBinaryPrefix lawPrefix := by
  apply roundedFold_dominates_law binaryPrefixPrimes _ _ _ roundedInitial_dominates
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · norm_num
  · have hh := (Erdos7No23Sieve.mem_prefixPrimes p).mp hp
    exact ⟨by omega,hh.2.2⟩

theorem lawPrefix_potential_lt_one :
    lawPrefix.cost + (16/5:ℚ)*expect lawPrefix.law (fun k => (4:ℚ)^k)/10080 < 1 := by
  have h := lawPrefix_dominated
  have hh := add_le_add h.cost (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left h.second (by norm_num : (0:ℚ) ≤ 16/5)) (by norm_num : (0:ℚ) ≤ 10080))
  apply hh.trans_lt
  convert roundedBinaryPrefix_potential_lt_one using 1 <;> ring

#print axioms lawPrefix_potential_lt_one
end Erdos7BinarySieve



/-! Uniform finite-tail bound for the binary distortion cost. -/
namespace Erdos7BinarySieve
open scoped BigOperators
open Erdos7Distortion Erdos7No23Sieve
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

noncomputable def moment (s : LawState) : ℚ := expect s.law (fun k => (4:ℚ)^k)
lemma moment_nonneg (s : LawState) (h : ∀ k, 0 ≤ s.law k) : 0 ≤ moment s :=
  expect_nonneg s.law h _ (by intro k; positivity)
lemma stateStep_nonneg (s : LawState) (h : ∀ k, 0 ≤ s.law k) (p : ℕ) (hp : 3 ≤ p) :
    ∀ k, 0 ≤ (stateStep s p).law k := lawStep_nonneg _ (rate_nonneg p) (rate_le_one p hp) _ h

lemma binary_multiplier_le (p : ℕ) (hp : 67 ≤ p) : 1+3*rate p ≤ multiplier p := by
  have hpQ : (67:ℚ) ≤ p := by exact_mod_cast hp
  have hpm : (0:ℚ) < p-1 := by linarith
  have hden : (0:ℚ) < p*(p-1)^2 := by positivity
  apply (mul_le_mul_iff_of_pos_right hden).mp
  simp only [rate, capData_large p hp, Nat.cast_mul, Nat.cast_ofNat, multiplier]
  have hn : (p:ℚ)-1 ≠ 0 := by linarith
  have hp0 : (p:ℚ) ≠ 0 := by linarith
  field_simp [hn,hp0]
  field_simp [hn,hp0]
  nlinarith

lemma stateStep_moment_bound (s : LawState) (h : ∀ k, 0 ≤ s.law k)
    (p : ℕ) (hp : 67 ≤ p) : moment (stateStep s p) ≤ moment s*multiplier p := by
  dsimp only [moment, stateStep]
  rw [lawStep_second]
  have hh := mul_le_mul_of_nonneg_right (binary_multiplier_le p hp) (moment_nonneg s h)
  simpa only [moment, mul_comm] using hh

lemma loss_second_bound (μ : ℕ →₀ ℚ) (hμ : ∀ k, 0 ≤ μ k) (p : ℕ) (hp : 67 ≤ p) :
    loss μ p ≤ charge p*expect μ (fun k => (4:ℚ)^k) := by
  have hpQ : (67:ℚ) ≤ p := by exact_mod_cast hp
  have hpoint (k : ℕ) : Erdos7Distortion.residual (cap p) ((2:ℚ)^k/p) ≤
      (25/16:ℚ)/(p:ℚ)^2 * (4:ℚ)^k := by
    rw [cap_large p hp]
    have hh := residual_le_second_moment (α := (2:ℚ)^k/p) (by norm_num : (1:ℚ)<5/4)
    norm_num at hh
    convert hh using 1 <;> rw [div_pow, ← pow_mul, mul_comm k 2, pow_mul] <;> norm_num <;> ring
  have hb := expect_le μ hμ _ _ hpoint
  change loss μ p ≤ _ at hb
  rw [expect_mul] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (expect_nonneg μ hμ _ (by intro k; positivity))
  unfold charge
  exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos (by linarith : (0:ℚ)<p-1))
    ((sq_le_sq₀ (by linarith : (0:ℚ)≤p-1) (by positivity : (0:ℚ)≤p)).mpr (by linarith))

lemma fold_tail_bounds (L : List ℕ) (hL : L.Pairwise (· < ·))
    (hlarge : ∀ p ∈ L, 67 ≤ p) (s : LawState) (hs : ∀ k, 0 ≤ s.law k) :
    moment (L.foldl stateStep s) ≤ moment s*budgetProduct L.toFinset ∧
    (L.foldl stateStep s).cost ≤ s.cost+moment s*budgetCost L.toFinset := by
  induction L generalizing s with
  | nil => simp [budgetProduct_empty, budgetCost_empty]
  | cons p L ih =>
    obtain ⟨hpL,hL⟩ := List.pairwise_cons.mp hL
    have hp := hlarge p List.mem_cons_self
    have hlargeL : ∀ q ∈ L, 67 ≤ q := fun q hq => hlarge q (List.mem_cons_of_mem _ hq)
    have hge5 : ∀ q ∈ L.toFinset, 5 ≤ q := by intro q hq; have := hlargeL q (List.mem_toFinset.mp hq); omega
    have hdis : Disjoint ({p}:Finset ℕ) L.toFinset := by
      apply Finset.disjoint_singleton_left.mpr
      intro h
      exact (lt_irrefl p) (hpL p (List.mem_toFinset.mp h))
    have horder : ∀ a ∈ ({p}:Finset ℕ), ∀ b ∈ L.toFinset, a<b := by
      intro a ha b hb
      rw [Finset.mem_singleton.mp ha]
      exact hpL b (List.mem_toFinset.mp hb)
    have hU : (p::L).toFinset = {p} ∪ L.toFinset := by simp
    have hh := ih hL hlargeL (stateStep s p) (stateStep_nonneg s hs p (by omega))
    have hM := stateStep_moment_bound s hs p hp
    have hC := loss_second_bound s.law hs p hp
    have hP0 := budgetProduct_nonneg L.toFinset hge5
    have hC0 := budgetCost_nonneg L.toFinset hge5
    simp only [List.foldl_cons, hU, budgetProduct_union hdis, budgetCost_union horder,
      budgetProduct_singleton, budgetCost_singleton]
    constructor
    · apply hh.1.trans
      have hmul := mul_le_mul_of_nonneg_right hM hP0
      exact hmul.trans_eq (by ring)
    · apply hh.2.trans
      have hmul := mul_le_mul_of_nonneg_right hM hC0
      dsimp only [stateStep] at hmul ⊢
      change loss s.law p ≤ charge p*moment s at hC
      nlinarith

/-- ANY finite sorted prime tail after 10080 fits inside the certified prefix
potential. This uses the already proved no23 finite-block tail, not a limit. -/
theorem prefix_tail_cost_lt_one (L : List ℕ) (hL : L.Pairwise (· < ·))
    (hprime : ∀ p ∈ L, p.Prime ∧ 10080 ≤ p) :
    ((binaryPrefixPrimes++L).foldl stateStep lawInitial).cost < 1 := by
  rw [List.foldl_append]
  change (L.foldl stateStep lawPrefix).cost < 1
  have hd := lawPrefix_dominated
  have hb := (fold_tail_bounds L hL (by intro p hp; have := (hprime p hp).2; omega)
    lawPrefix hd.nonneg).2
  have htail := tail_cost_bound 10080 (by omega) L.toFinset (by
    intro p hp; exact hprime p (List.mem_toFinset.mp hp))
  have hm := mul_le_mul_of_nonneg_left htail (moment_nonneg lawPrefix hd.nonneg)
  apply hb.trans_lt
  apply (add_le_add_right hm _).trans_lt
  convert lawPrefix_potential_lt_one using 1 <;> dsimp [moment] <;> ring

#print axioms prefix_tail_cost_lt_one
end Erdos7BinarySieve



/-! Identification of the list-fold cost with the proved covering criterion. -/
namespace Erdos7BinarySieve
open scoped BigOperators
open Erdos7CompressionSieve Erdos7Distortion
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

lemma cap_div_prime (p : ℕ) (hp : 3 ≤ p) : cap p*(1/(p:ℚ)) = rate p := by
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast (by omega : p≠0)
  dsimp [cap]; field_simp

lemma take_fold_law (L : List ℕ) (t : ℕ) (ht : t ≤ L.length) :
    ((L.take t).foldl stateStep lawInitial).law = prefixLaw (fun i => rate (L.get i)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hlt : t < L.length := by omega
    rw [List.take_succ_eq_append_getElem hlt, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, stateStep, prefixLaw, hlt, ↓reduceDIte]
    rw [ih (by omega)]
    rfl

lemma take_fold_cost (L : List ℕ) (t : ℕ) (ht : t ≤ L.length) :
    ((L.take t).foldl stateStep lawInitial).cost =
      ∑ j ∈ Finset.range t, if h : j<L.length then
        loss (prefixLaw (fun i => rate (L.get i)) j) L[j] else 0 := by
  induction t with
  | zero => simp [lawInitial]
  | succ t ih =>
    have hlt : t < L.length := by omega
    rw [List.take_succ_eq_append_getElem hlt, List.foldl_append, Finset.sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil, stateStep, hlt, ↓reduceDIte]
    rw [ih (by omega), take_fold_law L t (by omega)]

/-- Exact equality: the actual accumulated law cost is the quantity appearing
in `distinct_support_binary_bound`. -/
theorem fold_cost_eq_binaryCost (L : List ℕ) (hL : ∀ p ∈ L, 3 ≤ p) :
    (L.foldl stateStep lawInitial).cost =
      binaryCost (fun i : Fin L.length => 1/(L.get i:ℚ)) (fun i => cap (L.get i)) := by
  have hh := take_fold_cost L L.length le_rfl
  rw [List.take_length, Finset.sum_range] at hh
  simp only [Fin.isLt, ↓reduceDIte] at hh
  rw [hh]
  unfold binaryCost
  have hq : (fun i : Fin L.length => cap (L.get i)*(1/(L.get i:ℚ))) =
      (fun i => rate (L.get i)) := by
    funext i
    exact cap_div_prime (L.get i) (hL _ (List.getElem_mem i.isLt))
  rw [hq]
  apply Finset.sum_congr rfl
  intro i _
  rw [binaryEnvelope_eq_expect]
  unfold loss
  apply expect_congr
  intro k
  simp only [Nat.cast_one, one_mul, List.get_eq_getElem]
  congr 2
  ring

#print axioms fold_cost_eq_binaryCost
end Erdos7BinarySieve



/-! A binary-compression obstruction for odd squarefree covering systems. -/
namespace Erdos7BinarySieve
open scoped BigOperators
open Erdos7CompressionSieve Erdos7Distortion Erdos7Reduction
set_option maxHeartbeats 5000000
set_option maxRecDepth 200000

/-- Arithmetic specialization for moduli given by distinct support sets. -/
theorem arithmetic_support_cost_bound {n : ℕ} {κ : Type*} [Fintype κ]
    (p : Fin n → ℕ) (hp : ∀ i, 3 ≤ p i)
    (hcop : Pairwise (Function.onFun Nat.Coprime p))
    (S : κ → Finset (Fin n)) (hinj : Function.Injective S) (hne : ∀ k, (S k).Nonempty)
    (a : κ → ℤ)
    (hcover : ∀ x : ℤ, ∃ k, ((∏ i ∈ S k, p i : ℕ):ℤ) ∣ x-a k) :
    1 ≤ binaryCost (fun i => 1/(p i:ℚ)) (fun i => cap (p i)) := by
  classical
  letI (i : Fin n) : NeZero (p i) := ⟨by have := hp i; omega⟩
  let A (i : Fin n) := ZMod (p i)
  let X (k : κ) (i : Fin n) : Finset (A i) := {(a k : ZMod (p i))}
  have hX (k : κ) (i : Fin n) (hi : i ∈ S k) : fraction (X k i) ≤ 1/(p i:ℚ) := by
    simp [fraction, X, A, ZMod.card]
  have hbox : ∀ x : ∀ i, A i, ∃ k, ∀ i ∈ S k, x i ∈ X k i := by
    intro x
    let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) p Finset.univ
      (fun i _ => NeZero.ne _) (fun i _ j _ hij => hcop hij)
    have hz (i : Fin n) : (z.val : A i) = x i := by
      rw [← ZMod.natCast_zmod_val (x i)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
    obtain ⟨k,hk⟩ := hcover (z.val:ℤ)
    refine ⟨k,?_⟩
    intro i hi
    have hd : p i ∣ ∏ j ∈ S k, p j := Finset.dvd_prod_of_mem p hi
    have hdZ : (p i:ℤ) ∣ ((∏ j ∈ S k, p j:ℕ):ℤ) := by exact_mod_cast hd
    have hcast := (ZMod.intCast_eq_intCast_iff_dvd_sub (a k) (z.val:ℤ) (p i)).mpr (hdZ.trans hk)
    simp only [Int.cast_natCast] at hcast
    simp only [X, Finset.mem_singleton]
    rw [← hz i]
    exact hcast.symm
  exact distinct_support_binary_bound A (fun i => 1/(p i:ℚ)) (fun i => cap (p i))
    (fun i => by positivity) (fun i => (cap_gt_one (p i) (hp i)).le)
    (fun i => by rw [cap_div_prime (p i) (hp i)]; exact rate_le_one (p i) (hp i))
    S hinj hne X hX hbox

lemma mem_binaryPrefixPrimes (p : ℕ) :
    p ∈ binaryPrefixPrimes ↔ p.Prime ∧ 3 ≤ p ∧ p < 10080 := by
  simp only [binaryPrefixPrimes, List.mem_cons, Erdos7No23Sieve.mem_prefixPrimes]
  constructor
  · rintro (rfl | ⟨hprime,hlo,hhi⟩)
    · norm_num
    · exact ⟨hprime,by omega,hhi⟩
  · rintro ⟨hprime,hlo,hhi⟩
    by_cases h3 : p=3
    · exact Or.inl h3
    · have h4 : p≠4 := by intro h; subst p; norm_num at hprime
      exact Or.inr ⟨hprime,by omega,hhi⟩

lemma binaryPrefixPrimes_pairwise : binaryPrefixPrimes.Pairwise (· < ·) := by
  apply List.pairwise_cons.mpr
  refine ⟨?_,Erdos7No23Sieve.prefixPrimes_pairwise⟩
  intro p hp
  have hh := (Erdos7No23Sieve.mem_prefixPrimes p).mp hp
  omega

/-- Distinct odd squarefree nontrivial moduli cannot cover the integers. -/
theorem not_squarefree_odd_arithmetic_cover {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a) :
    ¬ (∀ k, Squarefree (m k)) := by
  classical
  intro hsf
  let P := Finset.univ.biUnion (fun k => (m k).primeFactors)
  have hP (q : ℕ) (hq : q ∈ P) : q.Prime ∧ 3 ≤ q := by
    obtain ⟨k,_,hk⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hprime,hdvd,_⟩ := Nat.mem_primeFactors.mp hk
    have hodd := (hc.2.1 k).2.of_dvd_nat hdvd
    have hq2 : q≠2 := by intro he; subst q; norm_num at hodd
    exact ⟨hprime,by have := hprime.two_le; omega⟩
  let T := P.filter (fun q => 10080 ≤ q)
  let L := binaryPrefixPrimes ++ T.sort (· ≤ ·)
  have hT (q : ℕ) (hq : q ∈ T.sort (· ≤ ·)) : q.Prime ∧ 10080 ≤ q := by
    have hh := Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp hq)
    exact ⟨(hP q hh.1).1,hh.2⟩
  have hLprime (q : ℕ) (hq : q ∈ L) : q.Prime ∧ 3 ≤ q := by
    rcases List.mem_append.mp hq with hq | hq
    · have hh := (mem_binaryPrefixPrimes q).mp hq
      exact ⟨hh.1,hh.2.1⟩
    · exact ⟨(hT q hq).1,by have := (hT q hq).2; omega⟩
  have hLsorted : L.Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨binaryPrefixPrimes_pairwise,T.sortedLT_sort.pairwise,?_⟩
    intro u hu v hv
    exact ((mem_binaryPrefixPrimes u).mp hu).2.2.trans_le (hT v hv).2
  have hPinL (q : ℕ) (hq : q ∈ P) : q ∈ L := by
    by_cases hlo : q<10080
    · exact List.mem_append_left _ ((mem_binaryPrefixPrimes q).mpr ⟨(hP q hq).1,(hP q hq).2,hlo⟩)
    · exact List.mem_append_right _ ((Finset.mem_sort (· ≤ ·)).mpr
        (Finset.mem_filter.mpr ⟨hq,by omega⟩))
  let p : Fin L.length → ℕ := L.get
  have hp (i : Fin L.length) : (p i).Prime ∧ 3 ≤ p i := hLprime _ (List.getElem_mem i.isLt)
  have hmono : StrictMono p := List.pairwise_iff_get.mp hLsorted
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i).1 (hp j).1).mpr (fun he => hij (hmono.injective he))
  let S (k : κ) := Finset.univ.filter (fun i => p i ∈ (m k).primeFactors)
  have hprod (k : κ) : (∏ i ∈ S k, p i) = m k := by
    have heq : (S k).image p = (m k).primeFactors := by
      ext q
      constructor
      · rintro hq
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
        exact (Finset.mem_filter.mp hi).2
      · intro hq
        have hqP : q ∈ P := Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,hq⟩
        obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (hPinL q hqP)
        refine Finset.mem_image.mpr ⟨⟨i,hi⟩,?_,he⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [p, List.get_eq_getElem, he] using hq⟩
    rw [← Finset.prod_image (f := fun q : ℕ => q) hmono.injective.injOn, heq]
    exact Nat.prod_primeFactors_of_squarefree (hsf k)
  have hSinj : Function.Injective S := by
    intro k l hkl
    apply hc.1
    rw [← hprod k, ← hprod l, hkl]
  have hSne (k : κ) : (S k).Nonempty := by
    by_contra h
    have he : S k = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hh := hprod k
    rw [he, Finset.prod_empty] at hh
    have := (hc.2.1 k).1
    omega
  have hcover : ∀ x : ℤ, ∃ k, ((∏ i ∈ S k, p i:ℕ):ℤ) ∣ x-a k := by
    simpa only [hprod] using hc.2.2
  have hbound := arithmetic_support_cost_bound p (fun i => (hp i).2) hcop S hSinj hSne a hcover
  have hsmall := prefix_tail_cost_lt_one (T.sort (· ≤ ·)) T.sortedLT_sort.pairwise hT
  change (L.foldl stateStep lawInitial).cost < 1 at hsmall
  rw [fold_cost_eq_binaryCost L (fun q hq => (hLprime q hq).2)] at hsmall
  exact (not_le_of_gt hsmall) hbound

/-- Ideal-valued consequence of the completed squarefree obstruction. -/
theorem not_all_squarefree_moduli (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i, ¬ C.moduli i ≤ Ideal.span {2}) :
    ¬ (∀ i, Squarefree (C.moduli i).absNorm) := by
  letI := C.fintypeIndex
  exact not_squarefree_odd_arithmetic_cover (fun i => (C.moduli i).absNorm) C.residue
    ⟨moduli_absNorm_injective C, fun i => ⟨moduli_absNorm_gt_one C i,
      (ideal_not_le_two_iff _).mp (hodd i)⟩, arithmetic_cover C⟩

/-- Every hypothetical odd strict cover must use a repeated prime factor in
at least one modulus. -/
theorem exists_prime_square (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i, ¬ C.moduli i ≤ Ideal.span {2}) :
    ∃ i p, p.Prime ∧ p*p ∣ (C.moduli i).absNorm := by
  classical
  by_contra hnone
  apply not_all_squarefree_moduli C hodd
  intro i
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro p hp hd
  exact hnone ⟨i,p,hp,hd⟩

#print axioms exists_prime_square
#print axioms not_squarefree_odd_arithmetic_cover
#print axioms not_all_squarefree_moduli
end Erdos7BinarySieve



/-! Convex compression grouped by coordinate exponent. -/
namespace Erdos7CompressionSieve
open scoped BigOperators
open Erdos7Distortion
set_option maxHeartbeats 4000000

/-- A continuous version of the Boolean-chain majorant. -/
theorem bounded_chain_majorant (φ : ℚ → ℚ) (hφ : ConvexOn ℚ Set.univ φ)
    (a : ℚ) (W s : ℕ → ℚ) (R : ℕ)
    (hs : ∀ j<R, 0 ≤ s j) (hsW : ∀ j<R, s j ≤ W j) :
    φ (a+prefixWeight s R) ≤ φ a +
      ∑ j ∈ Finset.range R, chainIncrement φ a W j / W j * s j := by
  induction R with
  | zero => simp [prefixWeight]
  | succ R ih =>
    have hs0 : ∀ j<R, 0 ≤ s j := fun j hj => hs j (by omega)
    have hsW0 : ∀ j<R, s j ≤ W j := fun j hj => hsW j (by omega)
    have hprev : prefixWeight s R ≤ prefixWeight W R :=
      Finset.sum_le_sum (fun j hj => hsW0 j (Finset.mem_range.mp hj))
    have hincr := convex_increasingIncrements φ hφ
      (a+prefixWeight s R) (a+prefixWeight W R) (s R) (by linarith) (hs R (by omega))
    have hchord := convex_chord_majorant φ hφ (a+prefixWeight W R) (s R) (W R)
      (hs R (by omega)) (hsW R (by omega))
    have hih := ih hs0 hsW0
    rw [Finset.sum_range_succ]
    have heq : prefixWeight s (R+1) = prefixWeight s R+s R := Finset.sum_range_succ _ _
    have heq' : chainIncrement φ a W R =
        φ (a+prefixWeight W R+W R)-φ (a+prefixWeight W R) := by
      simp only [chainIncrement, prefixWeight, Finset.sum_range_succ, add_assoc]
    rw [heq, heq']
    simp only [add_assoc] at hincr hchord ⊢
    linarith

section Resample
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

/-- Equal-density events can be compressed together at each exponent level.
There is no assumption of independence between events or between levels. -/
theorem resample_group_compression
    (i : ι) (μ : (∀ j, A j) → ℚ) (hμ : ∀ x, 0 ≤ μ x)
    (B : Finset (∀ j, A j)) (c : ℚ) (hc : 1 ≤ c)
    (φ : ℚ → ℚ) (hφ : ConvexOn ℚ Set.univ φ) (hmono : Monotone φ)
    (a : (∀ j, A j) → ℚ) (K : ℕ → Finset κ) (w : ℕ → κ → (∀ j, A j) → ℚ) (R : ℕ)
    (hw : ∀ g<R, ∀ k∈K g, ∀ x, 0 ≤ w g k x)
    (haind : ∀ x (v : A i), a (Function.update x i v) = a x)
    (hwind : ∀ g k x (v : A i), w g k (Function.update x i v) = w g k x)
    (T : ℕ → κ → Finset (A i)) (q : ℕ → ℚ)
    (hT : ∀ g<R, ∀ k∈K g, c*fraction (T g k) ≤ q g) :
    (∑ x, resample A i μ B c x *
      φ (a x + ∑ g ∈ Finset.range R, ∑ k ∈ K g, if x i ∈ T g k then w g k x else 0)) ≤
    (∑ x, μ x*φ (a x)) + ∑ g ∈ Finset.range R, q g *
      ∑ x, μ x * chainIncrement φ (a x) (fun j => ∑ k ∈ K j, w j k x) g := by
  classical
  let W (g : ℕ) (x : ∀ j, A j) := ∑ k ∈ K g, w g k x
  let inc (g : ℕ) (x : ∀ j, A j) := chainIncrement φ (a x) (fun j => W j x) g
  let d (g : ℕ) (x : ∀ j, A j) := inc g x / W g x
  have hW0 (g : ℕ) (hg : g<R) (x : ∀ j, A j) : 0 ≤ W g x :=
    Finset.sum_nonneg (fun k hk => hw g hg k hk x)
  have hWind (g : ℕ) (x : ∀ j, A j) (v : A i) : W g (Function.update x i v) = W g x := by
    simp only [W, hwind]
  have hinc0 (g : ℕ) (hg : g<R) (x : ∀ j, A j) : 0 ≤ inc g x :=
    chainIncrement_nonneg φ hmono (a x) (fun j => W j x) g (hW0 g hg x)
  have hd0 (g : ℕ) (hg : g<R) (x : ∀ j, A j) : 0 ≤ d g x := div_nonneg (hinc0 g hg x) (hW0 g hg x)
  have hdind (g : ℕ) (x : ∀ j, A j) (v : A i) : d g (Function.update x i v) = d g x := by
    simp only [d, inc, chainIncrement, haind, hWind]
  have hid (g : ℕ) (x : ∀ j, A j) : W g x*d g x = inc g x := by
    by_cases hz : W g x=0
    · have hi : inc g x=0 := by simp [inc, chainIncrement, prefixWeight, Finset.sum_range_succ, hz]
      simp [d, hz, hi]
    · dsimp [d]; field_simp
  have hpoint (x : ∀ j, A j) :
      φ (a x+∑ g ∈ Finset.range R, ∑ k ∈ K g, if x i ∈ T g k then w g k x else 0) ≤
      φ (a x)+∑ g ∈ Finset.range R, ∑ k ∈ K g, if x i ∈ T g k then w g k x*d g x else 0 := by
    have hs0 (g : ℕ) (hg : g<R) : 0 ≤ ∑ k ∈ K g, if x i ∈ T g k then w g k x else 0 := by
      apply Finset.sum_nonneg
      intro k hk; split_ifs <;> [exact hw g hg k hk x; exact le_rfl]
    have hsW (g : ℕ) (hg : g<R) : (∑ k ∈ K g, if x i ∈ T g k then w g k x else 0) ≤ W g x := by
      apply Finset.sum_le_sum
      intro k hk; split_ifs <;> [exact le_rfl; exact hw g hg k hk x]
    have hh := bounded_chain_majorant φ hφ (a x) (fun g => W g x)
      (fun g => ∑ k ∈ K g, if x i ∈ T g k then w g k x else 0) R hs0 hsW
    apply hh.trans_eq
    congr 1
    apply Finset.sum_congr rfl
    intro g hg
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    change d g x*(if x i ∈ T g k then w g k x else 0) = _
    split_ifs <;> ring
  have hbase : (∑ x, resample A i μ B c x*φ (a x)) = ∑ x, μ x*φ (a x) :=
    resample_preserves_test A i μ B hc _ (fun x v => by simp only [haind])
  have hterm (g : ℕ) (hg : g<R) (k : κ) (hk : k∈K g) :
      (∑ x, resample A i μ B c x*(if x i ∈ T g k then w g k x*d g x else 0)) ≤
      q g * ∑ x, μ x*(w g k x*d g x) := by
    have hh := resample_coordinate_test_bound A i μ hμ B hc (T g k)
      (fun x => w g k x*d g x) (fun x => mul_nonneg (hw g hg k hk x) (hd0 g hg x))
      (fun x v => by simp only [hwind,hdind])
    apply hh.trans
    apply mul_le_mul_of_nonneg_right (by simpa only [fraction] using hT g hg k hk)
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (hμ x) (mul_nonneg (hw g hg k hk x) (hd0 g hg x)))
  calc
    _ ≤ ∑ x, resample A i μ B c x*(φ (a x)+
      ∑ g ∈ Finset.range R, ∑ k ∈ K g, if x i ∈ T g k then w g k x*d g x else 0) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (resample_nonneg A i μ hμ B hc x))
    _ = (∑ x, μ x*φ (a x))+∑ g ∈ Finset.range R, ∑ k ∈ K g,
      ∑ x, resample A i μ B c x*(if x i ∈ T g k then w g k x*d g x else 0) := by
      simp_rw [mul_add, Finset.mul_sum]
      rw [Finset.sum_add_distrib,hbase,Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro g hg
      rw [Finset.sum_comm]
    _ ≤ (∑ x, μ x*φ (a x))+∑ g ∈ Finset.range R, ∑ k ∈ K g,
      q g * ∑ x, μ x*(w g k x*d g x) := by
      apply add_le_add_right
      exact Finset.sum_le_sum (fun g hg => Finset.sum_le_sum (fun k hk => hterm g (Finset.mem_range.mp hg) k hk))
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro g hg
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      change q g*(∑ x, μ x*(W g x*d g x)) = _
      simp only [hid,inc,W]

/-- The same estimate in positive-mixture form when the terminal tail is zero. -/
theorem resample_group_mixture
    (i : ι) (μ : (∀ j, A j) → ℚ) (hμ : ∀ x, 0 ≤ μ x)
    (B : Finset (∀ j, A j)) (c : ℚ) (hc : 1 ≤ c)
    (φ : ℚ → ℚ) (hφ : ConvexOn ℚ Set.univ φ) (hmono : Monotone φ)
    (a : (∀ j, A j) → ℚ) (K : ℕ → Finset κ) (w : ℕ → κ → (∀ j, A j) → ℚ) (R : ℕ)
    (hw : ∀ g<R, ∀ k∈K g, ∀ x, 0 ≤ w g k x)
    (haind : ∀ x (v : A i), a (Function.update x i v) = a x)
    (hwind : ∀ g k x (v : A i), w g k (Function.update x i v) = w g k x)
    (T : ℕ → κ → Finset (A i)) (q : ℕ → ℚ)
    (hT : ∀ g<R, ∀ k∈K g, c*fraction (T g k) ≤ q g) (hqR : q R=0) :
    (∑ x, resample A i μ B c x *
      φ (a x + ∑ g ∈ Finset.range R, ∑ k ∈ K g, if x i ∈ T g k then w g k x else 0)) ≤
    (1-q 0)*(∑ x, μ x*φ (a x)) + ∑ g ∈ Finset.range R, (q g-q (g+1))*
      ∑ x, μ x*φ (a x+prefixWeight (fun j => ∑ k ∈ K j, w j k x) (g+1)) := by
  have hh := resample_group_compression A i μ hμ B c hc φ hφ hmono a K w R hw haind hwind T q hT
  let f (t : ℕ) := ∑ x, μ x*φ (a x+prefixWeight (fun j => ∑ k ∈ K j, w j k x) t)
  have hzero : f 0 = ∑ x, μ x*φ (a x) := by simp [f,prefixWeight]
  have hinc (g : ℕ) : (∑ x, μ x*chainIncrement φ (a x) (fun j => ∑ k ∈ K j, w j k x) g) = f (g+1)-f g := by
    simp only [chainIncrement,mul_sub,Finset.sum_sub_distrib,f]
  apply hh.trans_eq
  simp_rw [hinc]
  rw [← hzero, chain_summation_by_parts, hqR, zero_mul, add_zero, hzero]

end Resample
#print axioms resample_group_mixture
end Erdos7CompressionSieve



/-! Convex comparison for arbitrary finite exponent patterns. -/
namespace Erdos7CompressionSieve
open scoped BigOperators
open Erdos7Distortion
set_option maxHeartbeats 4000000

/-- The active coordinates of an exponent vector. -/
def expSupport {ι : Type*} [Fintype ι] (e : ι → ℕ) : Finset ι :=
  Finset.univ.filter (fun i => e i ≠ 0)

@[simp] lemma mem_expSupport {ι : Type*} [Fintype ι] (e : ι → ℕ) (i : ι) :
    i ∈ expSupport e ↔ e i ≠ 0 := by simp [expSupport]

lemma expSupport_update_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℕ) (i : ι) :
    expSupport (Function.update e i 0) = (expSupport e).erase i := by
  ext j
  by_cases hj : j=i <;> simp [hj, Function.update_of_ne]

/-- Deleting a coordinate merges at most `a+1` exponent patterns if only
exponents at most `a` are retained. -/
lemma erase_exponent_multiplicity {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (K : Finset κ) (e : κ → ι → ℕ) (M : ℕ)
    (hM : ∀ f, (K.filter (fun k => e k = f)).card ≤ M)
    (i : ι) (a : ℕ) (f : ι → ℕ) :
    ((K.filter (fun k => e k i ≤ a)).filter
      (fun k => Function.update (e k) i 0 = f)).card ≤ (a+1)*M := by
  classical
  have hsub : (K.filter (fun k => e k i ≤ a)).filter
      (fun k => Function.update (e k) i 0 = f) ⊆
      (Finset.range (a+1)).biUnion (fun b => K.filter (fun k => e k = Function.update f i b)) := by
    intro k hk
    obtain ⟨hk,he⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk,hka⟩ := Finset.mem_filter.mp hk
    apply Finset.mem_biUnion.mpr
    refine ⟨e k i, Finset.mem_range.mpr (by omega), Finset.mem_filter.mpr ⟨hk, ?_⟩⟩
    funext j
    by_cases hj : j=i
    · subst j
      simp only [Function.update_self]
    · have hh := congrFun he j
      simpa [Function.update_of_ne hj] using hh
  apply (Finset.card_le_card hsub).trans
  apply (Finset.card_biUnion_le).trans
  calc
    _ ≤ ∑ _b ∈ Finset.range (a+1), M := Finset.sum_le_sum (fun b _ => hM (Function.update f i b))
    _ = _ := by simp

/-- Partition a finite sum according to a bounded natural-valued label. -/
lemma sum_filter_nat_le {κ : Type*} (K : Finset κ) (e : κ → ℕ) (a : ℕ)
    (w : κ → ℚ) :
    (∑ k ∈ K.filter (fun k => e k ≤ a), w k) =
      (∑ k ∈ K.filter (fun k => e k=0), w k) +
      ∑ g ∈ Finset.range a, ∑ k ∈ K.filter (fun k => e k=g+1), w k := by
  classical
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih]
    have h1 : (K.filter (fun k => e k ≤ a+1)).filter (fun k => e k ≤ a) =
        K.filter (fun k => e k ≤ a) := by
      ext k
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hk,h1⟩,h2⟩
        exact ⟨hk, by omega⟩
      · rintro ⟨hk,h⟩
        exact ⟨⟨hk, by omega⟩, by omega⟩
    have h2 : (K.filter (fun k => e k ≤ a+1)).filter (fun k => ¬ e k ≤ a) =
        K.filter (fun k => e k=a+1) := by
      ext k
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hk,h1⟩,h2⟩
        exact ⟨hk, by omega⟩
      · rintro ⟨hk,h⟩
        exact ⟨⟨hk, by omega⟩, by omega⟩
    have hh := Finset.sum_filter_add_sum_filter_not (K.filter (fun k => e k ≤ a+1)) (fun k => e k ≤ a) w
    rw [h1,h2] at hh
    exact hh.symm

section ResampleExponents
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

/-- A coordinate is replaced by a positive mixture of its exponent truncations.
The terminal tail is zero; all finite exponent levels are included. -/
theorem resample_exponent_compression
    (i : ι) (μ : (∀ j, A j) → ℚ) (hμ : ∀ x, 0 ≤ μ x)
    (B : Finset (∀ j, A j)) (c : ℚ) (hc : 1 ≤ c)
    (φ : ℚ → ℚ) (hφ : ConvexOn ℚ Set.univ φ) (hmono : Monotone φ)
    (K : Finset κ) (e : κ → ι → ℕ) (X : κ → ∀ j, Finset (A j))
    (E : ℕ) (q : ℕ → ℚ) (hE : ∀ k∈K, e k i ≤ E)
    (hX : ∀ k∈K, e k i ≠ 0 → c*fraction (X k i) ≤ q (e k i-1))
    (hqE : q E=0) :
    (∑ x, resample A i μ B c x * φ (∑ k∈K, boxIndicator A (expSupport (e k)) (X k) x)) ≤
      (1-q 0)*(∑ x, μ x*φ (∑ k∈K.filter (fun k => e k i ≤ 0),
        boxIndicator A (expSupport (Function.update (e k) i 0)) (X k) x)) +
      ∑ g∈Finset.range E, (q g-q (g+1))*(∑ x, μ x*φ (∑ k∈K.filter (fun k => e k i ≤ g+1),
        boxIndicator A (expSupport (Function.update (e k) i 0)) (X k) x)) := by
  classical
  let w (k : κ) (x : ∀ j, A j) := boxIndicator A ((expSupport (e k)).erase i) (X k) x
  let a (x : ∀ j, A j) := ∑ k∈K.filter (fun k => e k i=0), w k x
  let Kg (g : ℕ) := K.filter (fun k => e k i=g+1)
  have hwind (k : κ) (x : ∀ j, A j) (v : A i) : w k (Function.update x i v)=w k x :=
    boxIndicator_update A _ _ i (Finset.notMem_erase _ _) x v
  have haind (x : ∀ j, A j) (v : A i) : a (Function.update x i v)=a x := by
    simp only [a,hwind]
  have hsum (x : ∀ j, A j) :
      a x+(∑ g∈Finset.range E, ∑ k∈Kg g, if x i∈X k i then w k x else 0) =
        ∑ k∈K, boxIndicator A (expSupport (e k)) (X k) x := by
    have heq : K.filter (fun k => e k i ≤ E)=K := Finset.filter_true_of_mem hE
    have hh := sum_filter_nat_le K (fun k => e k i) E
      (fun k => boxIndicator A (expSupport (e k)) (X k) x)
    rw [heq] at hh
    rw [hh]
    apply congrArg₂ (·+·)
    · apply Finset.sum_congr rfl
      intro k hk
      have hz := (Finset.mem_filter.mp hk).2
      have hn : i∉expSupport (e k) := by simp [hz]
      simp only [w, Finset.erase_eq_of_notMem hn]
    · apply Finset.sum_congr rfl
      intro g hg
      apply Finset.sum_congr rfl
      intro k hk
      have hz := (Finset.mem_filter.mp hk).2
      have hi : i∈expSupport (e k) := by simp [hz]
      exact (boxIndicator_erase A _ _ i hi x).symm
  have hsum' (x : ∀ j, A j) (g : ℕ) :
      a x+prefixWeight (fun j => ∑ k∈Kg j, w k x) g =
        ∑ k∈K.filter (fun k => e k i ≤ g), w k x :=
    (sum_filter_nat_le K (fun k => e k i) g (fun k => w k x)).symm
  have hh := resample_group_mixture A i μ hμ B c hc φ hφ hmono a Kg (fun _ k => w k) E
    (fun _ _ k _ x => boxIndicator_nonneg A _ _ x) haind (fun _ => hwind)
    (fun _ k => X k i) q (by
      intro g hg k hk
      obtain ⟨hk,hkg⟩ := Finset.mem_filter.mp hk
      have hkn : e k i ≠ 0 := by omega
      simpa only [hkg, Nat.add_sub_cancel] using hX k hk hkn) hqE
  have ha (x : ∀ j, A j) : a x = ∑ k∈K.filter (fun k => e k i ≤ 0), w k x := by
    simp only [Nat.le_zero_eq, a]
  simp_rw [hsum,hsum'] at hh
  simpa only [ha,w,expSupport_update_zero] using hh

end ResampleExponents

/-- The finite exponent-compression envelope. At level `a`, coordinate
truncation multiplies the pattern multiplicity by `a+1`. -/
def exponentEnvelope {n : ℕ} (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ)
    (φ : ℚ → ℚ) : ℕ → ℕ → ℚ
  | 0, M => φ M
  | t+1, M => if h : t<n then
      (1-q ⟨t,h⟩ 0)*exponentEnvelope E q φ t M +
      ∑ g∈Finset.range (E ⟨t,h⟩), (q ⟨t,h⟩ g-q ⟨t,h⟩ (g+1))*
        exponentEnvelope E q φ t ((g+2)*M)
    else exponentEnvelope E q φ t M

/-- Convex comparison of the actual finite distortion tower with arbitrary
finite exponent patterns. -/
theorem tower_exponent_convex_bound {n : ℕ} {κ : Type*}
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (B : Fin n → Finset (∀ i, A i)) (c : Fin n → ℚ)
    (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ)
    (hc : ∀ i, 1 ≤ c i) (hq1 : ∀ i, q i 0 ≤ 1)
    (hqdec : ∀ i g, g<E i → q i (g+1) ≤ q i g) (hqE : ∀ i, q i (E i)=0)
    (φ : ℚ → ℚ) (hφ : ConvexOn ℚ Set.univ φ) (hmono : Monotone φ)
    (t : ℕ) (ht : t≤n) (M : ℕ) (K : Finset κ)
    (e : κ → Fin n → ℕ) (X : κ → ∀ i, Finset (A i))
    (he : ∀ k∈K, ∀ i, e k i ≤ E i)
    (hS : ∀ k∈K, ∀ i∈expSupport (e k), i.val<t)
    (hX : ∀ k∈K, ∀ i∈expSupport (e k), c i*fraction (X k i) ≤ q i (e k i-1))
    (hM : ∀ f, (K.filter (fun k => e k=f)).card ≤ M) :
    (∑ x, towerWeights A B c t x * φ (∑ k∈K, boxIndicator A (expSupport (e k)) (X k) x)) ≤
      exponentEnvelope E q φ t M := by
  classical
  induction t generalizing M K e with
  | zero =>
    have hz (k : κ) (hk : k∈K) : e k = fun _ => 0 := by
      funext i
      by_contra hi
      have hh := hS k hk i (mem_expSupport _ _ |>.mpr hi)
      omega
    have hcard : K.card ≤ M := by
      have hh := hM (fun _ => 0)
      have heq : K.filter (fun k => e k=fun _ => 0)=K := Finset.filter_true_of_mem hz
      rwa [heq] at hh
    have hsupport (k : κ) (hk : k∈K) : expSupport (e k)=∅ := by simp [hz k hk,expSupport]
    have hvalue (x : ∀ i, A i) : (∑ k∈K, boxIndicator A (expSupport (e k)) (X k) x) = (K.card:ℚ) := by
      calc
        _ = ∑ _k∈K, (1:ℚ) := Finset.sum_congr rfl (fun k hk => by rw [hsupport k hk,boxIndicator_empty])
        _ = _ := by simp
    simp_rw [hvalue]
    rw [← Finset.sum_mul,towerWeights_total A B c hc 0,one_mul]
    exact hmono (by exact_mod_cast hcard)
  | succ t ih =>
    let i : Fin n := ⟨t,by omega⟩
    let e' (k : κ) := Function.update (e k) i 0
    let K' (a : ℕ) := K.filter (fun k => e k i ≤ a)
    have he' (k : κ) (hk : k∈K) (j : Fin n) : e' k j ≤ E j := by
      by_cases hj : j=i
      · subst j; simp [e']
      · simpa only [e',Function.update_of_ne hj] using he k hk j
    have hS' (k : κ) (hk : k∈K) (j : Fin n) (hj : j∈expSupport (e' k)) : j.val<t := by
      rw [expSupport_update_zero] at hj
      have hjne := (Finset.mem_erase.mp hj).1
      have hh := hS k hk j (Finset.mem_erase.mp hj).2
      have hne : j.val≠t := by intro heq; exact hjne (Fin.ext heq)
      omega
    have hX' (k : κ) (hk : k∈K) (j : Fin n) (hj : j∈expSupport (e' k)) :
        c j*fraction (X k j) ≤ q j (e' k j-1) := by
      rw [expSupport_update_zero] at hj
      have hjne := (Finset.mem_erase.mp hj).1
      simpa only [e',Function.update_of_ne hjne] using hX k hk j (Finset.mem_erase.mp hj).2
    have hbound (a : ℕ) :
        (∑ x, towerWeights A B c t x*φ (∑ k∈K' a, boxIndicator A (expSupport (e' k)) (X k) x)) ≤
          exponentEnvelope E q φ t ((a+1)*M) :=
      ih (by omega) ((a+1)*M) (K' a) e'
        (fun k hk => he' k (Finset.mem_filter.mp hk).1)
        (fun k hk => hS' k (Finset.mem_filter.mp hk).1)
        (fun k hk => hX' k (Finset.mem_filter.mp hk).1)
        (erase_exponent_multiplicity K e M hM i a)
    have hstep := resample_exponent_compression A i (towerWeights A B c t)
      (towerWeights_nonneg A B c hc t) (B i) (c i) (hc i) φ hφ hmono K e X (E i) (q i)
      (fun k hk => he k hk i) (fun k hk hi => hX k hk i ((mem_expSupport _ _).mpr hi)) (hqE i)
    have hrec : towerWeights A B c (t+1) = resample A i (towerWeights A B c t) (B i) (c i) :=
      towerWeights_succ A B c i
    rw [hrec]
    apply hstep.trans
    have h0 := mul_le_mul_of_nonneg_left (hbound 0) (sub_nonneg.mpr (hq1 i))
    have hsum := Finset.sum_le_sum (fun g (hg : g∈Finset.range (E i)) =>
      mul_le_mul_of_nonneg_left (hbound (g+1)) (sub_nonneg.mpr (hqdec i g (Finset.mem_range.mp hg))))
    have hh := add_le_add h0 hsum
    simpa only [Nat.zero_add,Nat.one_mul,Nat.add_assoc,exponentEnvelope,show t<n by omega,
      ↓reduceDIte,e',K',i] using hh

#print axioms resample_exponent_compression
#print axioms tower_exponent_convex_bound
end Erdos7CompressionSieve



/-! An exact residual criterion for arbitrary finite exponent patterns. -/
namespace Erdos7CompressionSieve
open scoped BigOperators
open Erdos7Distortion
set_option maxHeartbeats 4000000

/-- A finite subconvex combination bound for the positive-part residual.
The unused weight is assigned to zero, whose residual vanishes for `c≥1`. -/
lemma weighted_residual_bound {κ : Type*} (K : Finset κ) (c s : ℚ)
    (hc : 1≤c) (hs : 0 < s) (w y : κ → ℚ)
    (hw : ∀ k∈K, 0≤w k) (hws : (∑ k∈K, w k)≤s) :
    residual c (∑ k∈K, w k*y k) ≤ ∑ k∈K, (w k/s)*residual c (s*y k) := by
  have hsum0 : 0 ≤ ∑ k∈K, (w k/s)*residual c (s*y k) :=
    Finset.sum_nonneg (fun k hk => mul_nonneg (div_nonneg (hw k hk) hs.le) (le_max_left _ _))
  have hlin : (∑ k∈K, (w k/s)*(c*(s*y k)-(c-1))) ≤
      ∑ k∈K, (w k/s)*residual c (s*y k) :=
    Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (le_max_right _ _) (div_nonneg (hw k hk) hs.le))
  have heq : (∑ k∈K, (w k/s)*(c*(s*y k)-(c-1))) =
      c*(∑ k∈K, w k*y k) - ((∑ k∈K, w k)/s)*(c-1) := by
    have hterm (k : κ) : (w k/s)*(c*(s*y k)-(c-1)) = c*(w k*y k)-(w k/s)*(c-1) := by
      field_simp
      <;> ring
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,← Finset.sum_div]
  rw [heq] at hlin
  have hratio : (∑ k∈K, w k)/s≤1 := (div_le_one hs).mpr hws
  have hprod := mul_le_mul_of_nonneg_right hratio (sub_nonneg.mpr hc)
  exact max_le hsum0 ((sub_le_sub_left (by simpa only [one_mul] using hprod) _).trans hlin)

lemma exponentEnvelope_nonneg {n : ℕ} (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ)
    (hq1 : ∀ i, q i 0≤1) (hqdec : ∀ i g, g < E i → q i (g+1)≤q i g)
    (φ : ℚ → ℚ) (hφ : ∀ M : ℕ, 0≤φ M) (t M : ℕ) :
    0≤exponentEnvelope E q φ t M := by
  induction t generalizing M with
  | zero => exact hφ M
  | succ t ih =>
    simp only [exponentEnvelope]
    split_ifs with h
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr (hq1 _)) (ih _))
        (Finset.sum_nonneg (fun g hg => mul_nonneg
          (sub_nonneg.mpr (hqdec _ g (Finset.mem_range.mp hg))) (ih _)))
    · exact ih M

/-- The full-exponent scalar budget with the hinge loss left exact. -/
def exponentCost {n : ℕ} (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ) (c s : Fin n → ℚ) : ℚ :=
  ∑ i, exponentEnvelope E q (fun x => residual (c i) (s i*x)) i.val 1

/-- Distinct nonzero exponent patterns in a covering force the finite
exponent-compression budget to be at least one. The profile `r` bounds the
coordinate densities, and `s` bounds its positive-exponent sum. -/
theorem distinct_exponent_convex_bound {n : ℕ} {κ : Type*} [Fintype κ]
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (E : Fin n → ℕ) (c s : Fin n → ℚ) (r q : Fin n → ℕ → ℚ)
    (hc : ∀ i, 1≤c i) (hs : ∀ i, 0 < s i)
    (hr : ∀ i g, g < E i → 0≤r i (g+1))
    (hrs : ∀ i, (∑ g∈Finset.range (E i), r i (g+1))≤s i)
    (hq1 : ∀ i, q i 0≤1) (hqdec : ∀ i g, g < E i → q i (g+1)≤q i g)
    (hqE : ∀ i, q i (E i)=0)
    (hqr : ∀ i g, g < E i → c i*r i (g+1)≤q i g)
    (e : κ → Fin n → ℕ) (heinj : Function.Injective e)
    (he : ∀ k i, e k i≤E i) (hne : ∀ k, (expSupport (e k)).Nonempty)
    (X : κ → ∀ i, Finset (A i))
    (hX : ∀ k i, e k i≠0 → fraction (X k i)≤r i (e k i))
    (hcover : ∀ x : ∀ i, A i, ∃ k, ∀ i∈expSupport (e k), x i∈X k i) :
    1≤exponentCost E q c s := by
  classical
  let S (k : κ) := expSupport (e k)
  let σ (k : κ) := (S k).max' (hne k)
  have hσ (k : κ) : σ k∈S k := Finset.max'_mem _ _
  have hS (k : κ) (j : Fin n) (hj : j∈S k) : j≤σ k := Finset.le_max' _ _ hj
  let B := layeredBad A S X σ
  have hB : ∀ i j : Fin n, j < i → ∀ x v, Function.update x i v∈B j ↔ x∈B j := by
    intro i j hji x v
    exact layeredBad_invariant A S X σ hS i j hji x v
  have hbcover : ∀ x : ∀ i, A i, ∃ i, x∈B i := by
    intro x
    obtain ⟨k,hk⟩ := hcover x
    exact ⟨σ k,Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, by simp [layerFamily], hk⟩⟩
  have hb := coordinate_residual_cover_bound A B c hc hB hbcover
  have hc0 : ∀ i, 0≤c i := fun i => (by norm_num : (0:ℚ)≤1).trans (hc i)
  apply hb.trans
  apply Finset.sum_le_sum
  intro i _
  let K := layerFamily σ i
  let Kg (g : ℕ) := K.filter (fun k => e k i=g+1)
  let e' (k : κ) := Function.update (e k) i 0
  let W (k : κ) (x : ∀ j, A j) := boxIndicator A (expSupport (e' k)) (X k) x
  let N (g : ℕ) (x : ∀ j, A j) := ∑ k∈Kg g, W k x
  let φ (x : ℚ) := residual (c i) (s i*x)
  let G := exponentEnvelope E q φ i.val 1
  have hki (k : κ) (hk : k∈K) : i∈S k := by
    simpa only [(Finset.mem_filter.mp hk).2] using hσ k
  have he' (k : κ) (j : Fin n) : e' k j≤E j := by
    by_cases hj : j=i
    · subst j; simp [e']
    · simpa only [e',Function.update_of_ne hj] using he k j
  have hprev (k : κ) (hk : k∈K) (j : Fin n) (hj : j∈expSupport (e' k)) : j.val < i.val := by
    rw [expSupport_update_zero] at hj
    have hle := hS k j (Finset.mem_erase.mp hj).2
    rw [(Finset.mem_filter.mp hk).2] at hle
    exact (show j < i from lt_of_le_of_ne hle (Finset.mem_erase.mp hj).1)
  have hX' (k : κ) (j : Fin n) (hj : j∈expSupport (e' k)) :
      c j*fraction (X k j)≤q j (e' k j-1) := by
    rw [expSupport_update_zero] at hj
    have hjne := (Finset.mem_erase.mp hj).1
    have hpos := (mem_expSupport _ _).mp (Finset.mem_erase.mp hj).2
    have hEj : e k j-1 < E j := by have := he k j; omega
    have hq := hqr j (e k j-1) hEj
    have heq : e k j-1+1=e k j := by omega
    rw [heq] at hq
    simpa only [e',Function.update_of_ne hjne] using
      (mul_le_mul_of_nonneg_left (hX k j hpos) (hc0 j)).trans hq
  have hmult (g : ℕ) (f : Fin n → ℕ) : ((Kg g).filter (fun k => e' k=f)).card≤1 := by
    apply Finset.card_le_one.mpr
    intro k hk l hl
    obtain ⟨hk,hkf⟩ := Finset.mem_filter.mp hk
    obtain ⟨hl,hlf⟩ := Finset.mem_filter.mp hl
    have hkg := (Finset.mem_filter.mp hk).2
    have hlg := (Finset.mem_filter.mp hl).2
    apply heinj
    funext j
    by_cases hj : j=i
    · subst j; exact hkg.trans hlg.symm
    · have hh := congrFun (hkf.trans hlf.symm) j
      simpa only [e',Function.update_of_ne hj] using hh
  have hcomp (g : ℕ) : (∑ x, towerWeights A B c i.val x*φ (N g x))≤G :=
    tower_exponent_convex_bound A B c E q hc hq1 hqdec hqE φ
      (residual_scaled_convex _ _) (residual_scaled_monotone _ _ (hc0 i) (hs i).le)
      i.val i.isLt.le 1 (Kg g) e' X (fun k _ => he' k)
      (fun k hk => hprev k (Finset.mem_filter.mp hk).1) (fun k _ => hX' k) (hmult g)
  have hG : 0≤G := exponentEnvelope_nonneg E q hq1 hqdec φ (fun _ => le_max_left _ _) _ _
  have hpoint (x : ∀ j, A j) : coordinateFraction A i (B i) x ≤
      ∑ g∈Finset.range (E i), r i (g+1)*N g x := by
    have hzero : K.filter (fun k => e k i=0)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      obtain ⟨hk,hz⟩ := Finset.mem_filter.mp hk
      exact (mem_expSupport _ _).mp (hki k hk) hz
    have hfull : K.filter (fun k => e k i≤E i)=K := Finset.filter_true_of_mem (fun k _ => he k i)
    have hsum := sum_filter_nat_le K (fun k => e k i) (E i) (fun k => r i (e k i)*W k x)
    rw [hzero,hfull,Finset.sum_empty,zero_add] at hsum
    calc
      _ ≤ ∑ k∈K, fraction (X k i)*boxIndicator A ((S k).erase i) (X k) x :=
        layered_fraction_bound A S X σ hσ i x
      _ ≤ ∑ k∈K, r i (e k i)*W k x := by
        apply Finset.sum_le_sum
        intro k hk
        have hi := (mem_expSupport _ _).mp (hki k hk)
        simpa only [W,e',expSupport_update_zero,S] using
          mul_le_mul_of_nonneg_right (hX k i hi) (boxIndicator_nonneg A ((S k).erase i) (X k) x)
      _ = ∑ g∈Finset.range (E i), r i (g+1)*N g x := by
        rw [hsum]
        apply Finset.sum_congr rfl
        intro g hg
        rw [show r i (g+1)*N g x = ∑ k∈Kg g, r i (g+1)*W k x from Finset.mul_sum _ _ _]
        apply Finset.sum_congr rfl
        intro k hk
        rw [(Finset.mem_filter.mp hk).2]
  have hres (x : ∀ j, A j) : residual (c i) (coordinateFraction A i (B i) x) ≤
      ∑ g∈Finset.range (E i), (r i (g+1)/s i)*φ (N g x) := by
    apply (max_le_max le_rfl (sub_le_sub_right (mul_le_mul_of_nonneg_left (hpoint x) (hc0 i)) _)).trans
    exact weighted_residual_bound (Finset.range (E i)) (c i) (s i) (hc i) (hs i)
      (fun g => r i (g+1)) (fun g => N g x)
      (fun g hg => hr i g (Finset.mem_range.mp hg)) (hrs i)
  calc
    _ ≤ ∑ x, towerWeights A B c i.val x *
        (∑ g∈Finset.range (E i), (r i (g+1)/s i)*φ (N g x)) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hres x) (towerWeights_nonneg A B c hc i.val x))
    _ = ∑ g∈Finset.range (E i), (r i (g+1)/s i)*
        (∑ x, towerWeights A B c i.val x*φ (N g x)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g hg
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ ≤ ∑ g∈Finset.range (E i), (r i (g+1)/s i)*G :=
      Finset.sum_le_sum (fun g hg => mul_le_mul_of_nonneg_left (hcomp g)
        (div_nonneg (hr i g (Finset.mem_range.mp hg)) (hs i).le))
    _ ≤ G := by
      rw [← Finset.sum_mul,← Finset.sum_div]
      have hh := mul_le_mul_of_nonneg_right ((div_le_one (hs i)).mpr (hrs i)) hG
      simpa only [one_mul] using hh

#print axioms distinct_exponent_convex_bound
end Erdos7CompressionSieve



/-! Geometric tail profiles and arithmetic specialization. -/
namespace Erdos7CompressionSieve
open scoped BigOperators
open Erdos7Distortion Erdos7StarSieve
set_option maxHeartbeats 4000000

/-- Truncated geometric tail for the number of merged exponent patterns. -/
def powerTail (p : ℕ) (c : ℚ) (E g : ℕ) : ℚ :=
  if g < E then c*((p:ℚ)⁻¹)^(g+1) else 0

lemma powerTail_terminal (p : ℕ) (c : ℚ) (E : ℕ) : powerTail p c E E=0 := by
  simp [powerTail]

lemma powerTail_nonneg (p : ℕ) (c : ℚ) (hc : 0≤c) (E g : ℕ) :
    0≤powerTail p c E g := by
  unfold powerTail
  split_ifs <;> positivity

lemma powerTail_zero_le_one (p : ℕ) (hp : 1 < p) (c : ℚ) (hcp : c≤p) (E : ℕ) :
    powerTail p c E 0≤1 := by
  unfold powerTail
  split_ifs
  · have hp0 : (0:ℚ)<p := by exact_mod_cast (show 0 < p by omega)
    simpa only [zero_add,pow_one,← div_eq_mul_inv] using (div_le_one hp0).mpr hcp
  · norm_num

lemma powerTail_decreasing (p : ℕ) (hp : 1 < p) (c : ℚ) (hc : 0≤c) (E g : ℕ) :
    powerTail p c E (g+1)≤powerTail p c E g := by
  by_cases hg : g+1<E
  · have hg' : g<E := by omega
    simp only [powerTail,if_pos hg,if_pos hg']
    apply mul_le_mul_of_nonneg_left _ hc
    have hp1 : (1:ℚ)≤p := by exact_mod_cast hp.le
    have hi1 : (p:ℚ)⁻¹≤1 := (inv_le_one₀ (by positivity)).mpr hp1
    rw [pow_succ]
    exact mul_le_of_le_one_right (by positivity) hi1
  · simp only [powerTail,if_neg hg]
    exact powerTail_nonneg p c hc E g

lemma positive_power_sum_le (p : ℕ) (hp : 1 < p) (E : ℕ) :
    (∑ g∈Finset.range E, ((p:ℚ)⁻¹)^(g+1))≤1/(p-1:ℚ) := by
  have hh := Erdos7Reduction.positive_geometric_sum_le p hp
    ((Finset.range E).image Nat.succ) (by
      intro a ha
      obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp ha
      omega)
  rw [Finset.sum_image (fun a _ b _ hab => Nat.succ_inj.mp hab)] at hh
  exact hh

/-- Arithmetic form of the full finite exponent-compression criterion.
The normalizer `s i` may be the exact finite geometric sum or any positive
upper bound, such as `1/(p i-1)`. -/
theorem arithmetic_exponent_convex_bound {n : ℕ} {κ : Type*} [Fintype κ]
    (p E : Fin n → ℕ) (hp : ∀ i, 1 < p i)
    (hcop : Pairwise (Function.onFun Nat.Coprime p))
    (e : κ → Fin n → ℕ) (he : Function.Injective e) (he0 : ∀ k, ∃ i, e k i≠0)
    (heE : ∀ k i, e k i≤E i) (a : κ → ℤ)
    (c s : Fin n → ℚ) (hc : ∀ i, 1≤c i) (hcp : ∀ i, c i≤p i)
    (hs : ∀ i, 0<s i)
    (hsum : ∀ i, (∑ g∈Finset.range (E i), ((p i:ℚ)⁻¹)^(g+1))≤s i)
    (hcover : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k) :
    1≤exponentCost E (fun i => powerTail (p i) (c i) (E i)) c s := by
  classical
  letI (i : Fin n) : NeZero (p i) := ⟨by have := hp i; omega⟩
  let A (i : Fin n) := ZMod (p i ^ E i)
  let f (k : κ) (i : Fin n) := ZMod.castHom (pow_dvd_pow (p i) (heE k i)) (ZMod (p i ^ e k i))
  let B (k : κ) (i : Fin n) := Finset.univ.filter (fun x : A i => f k i x = (a k : ZMod (p i ^ e k i)))
  have hBcard (k : κ) (i : Fin n) : ((B k i).card : ℚ) ≤
      (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(e k i) := by
    have hh := surjective_fiber_card_rat (f k i).toAddMonoidHom
      (ZMod.castHom_surjective (pow_dvd_pow (p i) (heE k i))) (a k)
    change ((B k i).card : ℚ) = _ at hh
    rw [hh]
    simp only [A, ZMod.card, Nat.cast_pow, div_eq_mul_inv, inv_pow]
    exact le_rfl
  have hbox : ∀ x : ∀ i, A i, ∃ k, ∀ i, x i ∈ B k i := by
    intro x
    let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) (fun i => p i ^ E i) Finset.univ
      (fun i _ => pow_ne_zero _ (NeZero.ne _))
      (fun i _ j _ hij => (hcop hij).pow _ _)
    have hz (i : Fin n) : (z.val : A i) = x i := by
      rw [← ZMod.natCast_zmod_val (x i)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
    obtain ⟨k, hk⟩ := hcover (z.val : ℤ)
    refine ⟨k, ?_⟩
    intro i
    have hpi : p i ^ e k i ∣ ∏ j, p j ^ e k j :=
      Finset.dvd_prod_of_mem (fun j => p j ^ e k j) (Finset.mem_univ i)
    have hpi' : ((p i ^ e k i : ℕ) : ℤ) ∣ ((∏ j, p j ^ e k j : ℕ) : ℤ) := by exact_mod_cast hpi
    have hqi := hpi'.trans hk
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hz i, map_natCast]
    symm
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (a k) (z.val : ℤ) (p i ^ e k i)).mpr hqi
  have hc0 : ∀ i, 0≤c i := fun i => (by norm_num : (0:ℚ)≤1).trans (hc i)
  have hfrac (k : κ) (i : Fin n) : fraction (B k i)≤((p i:ℚ)⁻¹)^(e k i) := by
    apply (div_le_iff₀ card_pos_rat).mpr
    simpa only [mul_comm] using hBcard k i
  apply distinct_exponent_convex_bound A E c s (fun i g => ((p i:ℚ)⁻¹)^g)
    (fun i => powerTail (p i) (c i) (E i)) hc hs (fun _ _ _ => by positivity) hsum
    (fun i => powerTail_zero_le_one (p i) (hp i) (c i) (hcp i) (E i))
    (fun i g _ => powerTail_decreasing (p i) (hp i) (c i) (hc0 i) (E i) g)
    (fun i => powerTail_terminal (p i) (c i) (E i))
    (fun i g hg => by simp only [powerTail,if_pos hg,le_refl]) e he heE
  · intro k
    obtain ⟨i,hi⟩ := he0 k
    exact ⟨i,(mem_expSupport _ _).mpr hi⟩
  · exact fun k i _ => hfrac k i
  · intro x
    obtain ⟨k,hk⟩ := hbox x
    exact ⟨k,fun i _ => hk i⟩

#print axioms arithmetic_exponent_convex_bound
end Erdos7CompressionSieve



/-! Exact finitely supported laws for the exponent-compression envelope. -/
namespace Erdos7ExponentLaw
open scoped BigOperators
open Erdos7CompressionSieve
open Erdos7BinarySieve (expect expect_congr expect_mul expect_nonneg)
set_option maxHeartbeats 4000000

noncomputable def initial : ℕ →₀ ℚ := Finsupp.single 1 1
noncomputable def step (E : ℕ) (q : ℕ → ℚ) (μ : ℕ →₀ ℚ) : ℕ →₀ ℚ :=
  (1-q 0) • μ + ∑ g∈Finset.range E,
    (q g-q (g+1)) • μ.mapDomain (fun k => (g+2)*k)

lemma expect_add_law (μ ν : ℕ →₀ ℚ) (f : ℕ → ℚ) :
    expect (μ+ν) f=expect μ f+expect ν f := by
  unfold expect
  exact Finsupp.sum_add_index (by intros; simp) (by intros; ring)

lemma expect_smul_law (a : ℚ) (μ : ℕ →₀ ℚ) (f : ℕ → ℚ) :
    expect (a • μ) f=a*expect μ f := by
  unfold expect
  rw [Finsupp.sum_smul_index (by intros; simp)]
  simp only [Finsupp.sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros
  ring

lemma expect_sum_law {ι : Type*} (K : Finset ι) (μ : ι → ℕ →₀ ℚ) (f : ℕ → ℚ) :
    expect (∑ k∈K, μ k) f=∑ k∈K, expect (μ k) f := by
  classical
  induction K using Finset.induction_on with
  | empty => simp [expect]
  | @insert k K hk ih => rw [Finset.sum_insert hk,expect_add_law,Finset.sum_insert hk,ih]

lemma expect_map_law (d : ℕ) (μ : ℕ →₀ ℚ) (f : ℕ → ℚ) :
    expect (μ.mapDomain (fun k => d*k)) f=expect μ (fun k => f (d*k)) := by
  unfold expect
  exact Finsupp.sum_mapDomain_index (by intros; simp) (by intros; ring)

lemma expect_step (E : ℕ) (q : ℕ → ℚ) (μ : ℕ →₀ ℚ) (f : ℕ → ℚ) :
    expect (step E q μ) f=(1-q 0)*expect μ f +
      ∑ g∈Finset.range E, (q g-q (g+1))*expect μ (fun k => f ((g+2)*k)) := by
  simp only [step,expect_add_law,expect_smul_law,expect_sum_law,expect_map_law]

lemma expect_initial (f : ℕ → ℚ) : expect initial f=f 1 := by simp [initial,expect]

lemma step_mass (E : ℕ) (q : ℕ → ℚ) (hq : q E=0) (μ : ℕ →₀ ℚ) :
    expect (step E q μ) (fun _ => 1)=expect μ (fun _ => 1) := by
  rw [expect_step,← Finset.sum_mul]
  have hh : (∑ g∈Finset.range E, (q g-q (g+1)))=q 0 := by
    have hs := Finset.sum_range_sub' q E
    simpa only [hq,sub_zero] using hs
  rw [hh]
  ring

lemma step_nonneg (E : ℕ) (q : ℕ → ℚ) (hq1 : q 0≤1)
    (hqdec : ∀ g, g<E → q (g+1)≤q g) (μ : ℕ →₀ ℚ) (hμ : ∀ k, 0≤μ k) (k : ℕ) :
    0≤step E q μ k := by
  classical
  simp only [step,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,Finsupp.finset_sum_apply]
  apply add_nonneg (mul_nonneg (sub_nonneg.mpr hq1) (hμ k))
  apply Finset.sum_nonneg
  intro g hg
  apply mul_nonneg (sub_nonneg.mpr (hqdec g (Finset.mem_range.mp hg)))
  exact Finsupp.mapDomain_nonneg hμ k

noncomputable def prefixLaw {n : ℕ} (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ) : ℕ → (ℕ →₀ ℚ)
  | 0 => initial
  | t+1 => if h : t<n then step (E ⟨t,h⟩) (q ⟨t,h⟩) (prefixLaw E q t) else prefixLaw E q t

lemma prefix_mass {n : ℕ} (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ)
    (hqE : ∀ i, q i (E i)=0) (t : ℕ) : expect (prefixLaw E q t) (fun _ => 1)=1 := by
  induction t with
  | zero => simp only [prefixLaw,expect_initial]
  | succ t ih => unfold prefixLaw; split_ifs <;> simp only [step_mass _ _ (hqE _),ih]

lemma prefix_nonneg {n : ℕ} (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ)
    (hq1 : ∀ i, q i 0≤1) (hqdec : ∀ i g, g<E i → q i (g+1)≤q i g)
    (t k : ℕ) : 0≤prefixLaw E q t k := by
  induction t generalizing k with
  | zero => simp [prefixLaw,initial,Finsupp.single_apply]; positivity
  | succ t ih =>
    unfold prefixLaw
    split_ifs
    · exact step_nonneg _ _ (hq1 _) (hqdec _) _ ih k
    · exact ih k

/-- Exact interpretation by a finite law; no infinite distribution or
truncation approximation is used. -/
theorem exponentEnvelope_eq_expect {n : ℕ} (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ)
    (φ : ℚ → ℚ) (t M : ℕ) :
    exponentEnvelope E q φ t M=expect (prefixLaw E q t) (fun k => φ ((M:ℚ)*k)) := by
  induction t generalizing M with
  | zero => simp [exponentEnvelope,prefixLaw,expect_initial]
  | succ t ih =>
    simp only [exponentEnvelope,prefixLaw]
    split_ifs
    · rw [expect_step,ih]
      apply congrArg₂ (·+·) rfl
      apply Finset.sum_congr rfl
      intro g hg
      rw [ih]
      congr 1
      apply expect_congr
      intro k
      congr 1
      push_cast
      ring
    · exact ih M

/-- All integral moments have exact finite transition factors. -/
lemma step_moment (E : ℕ) (q : ℕ → ℚ) (hq : q E=0) (μ : ℕ →₀ ℚ) (r : ℕ) :
    expect (step E q μ) (fun k => (k:ℚ)^r) =
      (1+∑ g∈Finset.range E, q g*(((g+2:ℕ):ℚ)^r-((g+1:ℕ):ℚ)^r))*
        expect μ (fun k => (k:ℚ)^r) := by
  rw [expect_step]
  simp_rw [Nat.cast_mul,mul_pow,expect_mul,← mul_assoc]
  rw [← Finset.sum_mul,← add_mul]
  congr 1
  have hh := chain_summation_by_parts (fun g => ((g+1:ℕ):ℚ)^r) q E
  simpa only [hq,zero_mul,add_zero,zero_add,Nat.cast_one,one_pow,mul_one,Nat.add_assoc] using hh.symm

lemma step_mean (E : ℕ) (q : ℕ → ℚ) (hq : q E=0) (μ : ℕ →₀ ℚ) :
    expect (step E q μ) (fun k => (k:ℚ)) =
      (1+∑ g∈Finset.range E, q g)*expect μ (fun k => (k:ℚ)) := by
  have hh := step_moment E q hq μ 1
  have hid (g : ℕ) : (((g+2:ℕ):ℚ)^1-((g+1:ℕ):ℚ)^1)=1 := by push_cast; ring
  simp_rw [hid] at hh
  simpa only [pow_one,mul_one] using hh

lemma step_second (E : ℕ) (q : ℕ → ℚ) (hq : q E=0) (μ : ℕ →₀ ℚ) :
    expect (step E q μ) (fun k => (k:ℚ)^2) =
      (1+∑ g∈Finset.range E, q g*(2*(g:ℚ)+3))*expect μ (fun k => (k:ℚ)^2) := by
  rw [step_moment E q hq μ 2]
  congr 2
  apply Finset.sum_congr rfl
  intro g hg
  push_cast
  ring

#print axioms exponentEnvelope_eq_expect
#print axioms step_moment
end Erdos7ExponentLaw



/-! Removing excluded mass and thinning to a prescribed finite mass. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion
set_option maxHeartbeats 4000000

section Trim
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Available mass outside the excluded set. -/
def outsideMass (ν : Ω → ℚ) (B : Finset Ω) : ℚ :=
  ∑ x, if x∈B then 0 else ν x

/-- Restrict to the complement and thin uniformly to the requested mass. -/
def trimOutside (ν : Ω → ℚ) (B : Finset Ω) (m : ℚ) (x : Ω) : ℚ :=
  if x∈B then 0 else (m / outsideMass ν B)*ν x

lemma outsideMass_nonneg (ν : Ω → ℚ) (hν : ∀ x, 0≤ν x) (B : Finset Ω) :
    0≤outsideMass ν B := by
  apply Finset.sum_nonneg
  intro x hx
  split_ifs <;> [exact le_rfl; exact hν x]

lemma outsideMass_eq (ν : Ω → ℚ) (B : Finset Ω) :
    outsideMass ν B=(∑ x, ν x)-∑ x∈B, ν x := by
  have hh := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset Ω) (fun x => x∈B) ν
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter] at hh
  have heq : outsideMass ν B=∑ x∈Finset.univ.filter (fun x => x∉B), ν x := by
    simp only [outsideMass,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> rfl
  rw [heq]
  linarith

lemma trimOutside_nonneg (ν : Ω → ℚ) (hν : ∀ x, 0≤ν x) (B : Finset Ω)
    (m : ℚ) (hm : 0≤ m) (x : Ω) : 0≤trimOutside ν B m x := by
  unfold trimOutside
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (div_nonneg hm (outsideMass_nonneg ν hν B)) (hν x)

lemma trimOutside_le (ν : Ω → ℚ) (hν : ∀ x, 0≤ν x) (B : Finset Ω)
    (m : ℚ) (hm : 0≤ m) (hmb : m≤outsideMass ν B) (x : Ω) :
    trimOutside ν B m x≤ν x := by
  unfold trimOutside
  split_ifs
  · exact hν x
  · by_cases hz : outsideMass ν B=0
    · have hm0 : m=0 := by rw [hz] at hmb; linarith
      simpa only [hm0,zero_div,zero_mul] using hν x
    · have hb : 0 < outsideMass ν B := lt_of_le_of_ne (outsideMass_nonneg ν hν B) (Ne.symm hz)
      exact mul_le_of_le_one_left (hν x) ((div_le_one hb).mpr hmb)

lemma trimOutside_total (ν : Ω → ℚ) (B : Finset Ω) (m : ℚ)
    (hm : 0≤ m) (hmb : m≤outsideMass ν B) :
    (∑ x, trimOutside ν B m x)=m := by
  have heq : (∑ x, trimOutside ν B m x)=(m/outsideMass ν B)*outsideMass ν B := by
    rw [outsideMass,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    unfold trimOutside
    split_ifs <;> simp [outsideMass]
  rw [heq]
  by_cases hz : outsideMass ν B=0
  · have hm0 : m=0 := by rw [hz] at hmb; linarith
    simp [hz,hm0]
  · exact div_mul_cancel₀ _ hz

lemma trimOutside_zero (ν : Ω → ℚ) (B : Finset Ω) (m : ℚ)
    (x : Ω) (hx : x∈B) : trimOutside ν B m x=0 := by simp [trimOutside,hx]

/-- Deleting a known amount of mass removes at least that amount times the
pointwise lower bound on a test. The lower bound need not be positive. -/
theorem trimOutside_test (ν : Ω → ℚ) (hν : ∀ x, 0≤ν x) (B : Finset Ω)
    (m : ℚ) (hm : 0≤ m) (hmb : m≤outsideMass ν B)
    (f : Ω → ℚ) (b : ℚ) (hf : ∀ x, b≤f x) :
    (∑ x, trimOutside ν B m x*f x) ≤ (∑ x, ν x*f x)-((∑ x,ν x)-m)*b := by
  have hh := Finset.sum_le_sum (fun x (_ : x∈(Finset.univ : Finset Ω)) =>
    mul_le_mul_of_nonneg_left (hf x) (sub_nonneg.mpr (trimOutside_le ν hν B m hm hmb x)))
  simp_rw [sub_mul] at hh
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.sum_mul,
    trimOutside_total ν B m hm hmb] at hh
  linarith

end Trim

section Resample
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

/-- Resample, discard the new excluded set, and thin to the mass resulting
from the prescribed loss upper bound `L`. -/
def killedResample (i : ι) (μ : (∀ j, A j) → ℚ) (B : Finset (∀ j, A j))
    (c L : ℚ) : (∀ j, A j) → ℚ :=
  trimOutside (resample A i μ B c) B ((∑ x,μ x)-L)

lemma killedResample_available (i : ι) (μ : (∀ j, A j) → ℚ)
    (B : Finset (∀ j, A j)) (c L : ℚ) (hc : 1≤c)
    (hL : (∑ x, μ x*residual c (coordinateFraction A i B x))≤L) :
    (∑ x,μ x)-L≤outsideMass (resample A i μ B c) B := by
  rw [outsideMass_eq,resample_total A i μ B hc,resample_excluded A i μ B hc]
  linarith

lemma killedResample_nonneg (i : ι) (μ : (∀ j, A j) → ℚ) (hμ : ∀ x, 0≤μ x)
    (B : Finset (∀ j, A j)) (c L : ℚ) (hc : 1≤c) (hLm : L≤∑ x,μ x)
    (x : ∀ j, A j) : 0≤killedResample A i μ B c L x :=
  trimOutside_nonneg _ (resample_nonneg A i μ hμ B hc) B _ (sub_nonneg.mpr hLm) x

lemma killedResample_total (i : ι) (μ : (∀ j, A j) → ℚ)
    (B : Finset (∀ j, A j)) (c L : ℚ) (hc : 1≤c) (hLm : L≤∑ x,μ x)
    (hL : (∑ x, μ x*residual c (coordinateFraction A i B x))≤L) :
    (∑ x, killedResample A i μ B c L x)=(∑ x,μ x)-L :=
  trimOutside_total _ B _ (sub_nonneg.mpr hLm) (killedResample_available A i μ B c L hc hL)

lemma killedResample_zero (i : ι) (μ : (∀ j, A j) → ℚ)
    (B : Finset (∀ j, A j)) (c L : ℚ) (x : ∀ j, A j) (hx : x∈B) :
    killedResample A i μ B c L x=0 := trimOutside_zero _ B _ x hx

/-- The mandatory baseline contribution is subtracted exactly, even when the
comparison law used to bound the full-resampling term is signed. -/
theorem killedResample_test (i : ι) (μ : (∀ j, A j) → ℚ) (hμ : ∀ x, 0≤μ x)
    (B : Finset (∀ j, A j)) (c L : ℚ) (hc : 1≤c) (hLm : L≤∑ x,μ x)
    (hL : (∑ x, μ x*residual c (coordinateFraction A i B x))≤L)
    (f : (∀ j, A j) → ℚ) (b : ℚ) (hf : ∀ x, b≤f x) :
    (∑ x, killedResample A i μ B c L x*f x)≤
      (∑ x, resample A i μ B c x*f x)-L*b := by
  have hh := trimOutside_test _ (resample_nonneg A i μ hμ B hc) B _ (sub_nonneg.mpr hLm)
    (killedResample_available A i μ B c L hc hL) f b hf
  rw [resample_total A i μ B hc,sub_sub_cancel] at hh
  exact hh

end Resample
#print axioms killedResample_test
end Erdos7KilledSieve



/-! Exact multiplicities and mandatory baselines in complete exponent rectangles. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
set_option maxHeartbeats 4000000

/-- An exponent vector supported on the processed prefix and within its caps. -/
def PrefixPattern {n : ℕ} (E : Fin n → ℕ) (t : ℕ) (f : Fin n → ℕ) : Prop :=
  (∀ i, f i ≤ E i) ∧ (∀ i, t ≤ i.val → f i=0)

/-- Each prefix pattern is represented exactly `M` times. -/
def CompletePatterns {n : ℕ} {κ : Type*} (E : Fin n → ℕ) (t : ℕ)
    (K : Finset κ) (e : κ → Fin n → ℕ) (M : ℕ) : Prop :=
  ∀ f, PrefixPattern E t f → (K.filter (fun k => e k=f)).card=M

lemma prefixPattern_zero {n : ℕ} (E : Fin n → ℕ) (t : ℕ) :
    PrefixPattern E t (fun _ => 0) := ⟨fun _ => Nat.zero_le _, fun _ _ => rfl⟩

/-- Exact partition of an erased-pattern fibre by the deleted exponent. -/
lemma erase_exponent_card {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (K : Finset κ) (e : κ → ι → ℕ) (i : ι) (a : ℕ) (f : ι → ℕ) (hf : f i=0) :
    ((K.filter (fun k => e k i ≤ a)).filter
      (fun k => Function.update (e k) i 0=f)).card =
      ∑ b∈Finset.range (a+1), (K.filter (fun k => e k=Function.update f i b)).card := by
  classical
  have heq : (K.filter (fun k => e k i ≤ a)).filter
      (fun k => Function.update (e k) i 0=f) =
      (Finset.range (a+1)).biUnion (fun b => K.filter (fun k => e k=Function.update f i b)) := by
    ext k
    constructor
    · intro hk
      obtain ⟨hk,he⟩ := Finset.mem_filter.mp hk
      obtain ⟨hk,hka⟩ := Finset.mem_filter.mp hk
      refine Finset.mem_biUnion.mpr ⟨e k i,Finset.mem_range.mpr (by omega),Finset.mem_filter.mpr ⟨hk,?_⟩⟩
      funext j
      by_cases hj : j=i
      · subst j; simp only [Function.update_self]
      · have hh := congrFun he j
        simpa only [Function.update_of_ne hj] using hh
    · intro hk
      obtain ⟨b,hb,hk⟩ := Finset.mem_biUnion.mp hk
      obtain ⟨hk,he⟩ := Finset.mem_filter.mp hk
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        refine ⟨hk,?_⟩
        have hh := congrFun he i
        simp only [Function.update_self] at hh
        have hb' := Finset.mem_range.mp hb
        omega
      · rw [he,Function.update_idem,← hf,Function.update_eq_self]
  rw [heq]
  apply Finset.card_biUnion
  intro b hb d hd hbd
  apply Finset.disjoint_left.mpr
  intro k hk hkd
  have hh := (Finset.mem_filter.mp hk).2.symm.trans (Finset.mem_filter.mp hkd).2
  have hi := congrFun hh i
  simp only [Function.update_self] at hi
  exact hbd hi

lemma completePatterns_erase {n : ℕ} {κ : Type*} (E : Fin n → ℕ) (t : ℕ)
    (ht : t < n) (K : Finset κ) (e : κ → Fin n → ℕ) (M : ℕ)
    (hM : CompletePatterns E (t+1) K e M) (a : ℕ) (ha : a ≤ E ⟨t,ht⟩) :
    CompletePatterns E t (K.filter (fun k => e k ⟨t,ht⟩ ≤ a))
      (fun k => Function.update (e k) ⟨t,ht⟩ 0) ((a+1)*M) := by
  intro f hf
  have hfi : f ⟨t,ht⟩=0 := hf.2 _ le_rfl
  rw [erase_exponent_card K e ⟨t,ht⟩ a f hfi]
  calc
    _ = ∑ _b∈Finset.range (a+1), M := by
      apply Finset.sum_congr rfl
      intro b hb
      apply hM
      constructor
      · intro j
        by_cases hj : j=⟨t,ht⟩
        · subst j
          simp only [Function.update_self]
          exact (by have := Finset.mem_range.mp hb; omega : b ≤ a).trans ha
        · simpa only [Function.update_of_ne hj] using hf.1 j
      · intro j hj
        have hji : j≠⟨t,ht⟩ := by intro heq; subst j; simp only at hj; omega
        simpa only [Function.update_of_ne hji] using hf.2 j (by omega)
    _ = _ := by simp

/-- The zero exponent fibre supplies a pointwise lower bound on box count. -/
lemma completePatterns_boxCount_lower {n : ℕ} {κ : Type*}
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (E : Fin n → ℕ) (t : ℕ) (K : Finset κ) (e : κ → Fin n → ℕ) (M : ℕ)
    (hM : CompletePatterns E t K e M) (X : κ → ∀ i, Finset (A i)) (x : ∀ i, A i) :
    (M:ℚ) ≤ ∑ k∈K, boxIndicator A (expSupport (e k)) (X k) x := by
  have hz := hM (fun _ => 0) (prefixPattern_zero E t)
  calc
    (M:ℚ) = ∑ k∈K.filter (fun k => e k=fun _ => 0), boxIndicator A (expSupport (e k)) (X k) x := by
      symm
      calc
        _ = ∑ _k∈K.filter (fun k => e k=fun _ => 0), (1:ℚ) := by
          apply Finset.sum_congr rfl
          intro k hk
          have he := (Finset.mem_filter.mp hk).2
          simp [he,expSupport,boxIndicator_empty]
        _ = _ := by simp [hz]
    _  ≤  _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun k _ _ => boxIndicator_nonneg A _ _ x)

#print axioms completePatterns_erase
#print axioms completePatterns_boxCount_lower
end Erdos7KilledSieve



/-! Convex comparison after exact-mass killing, allowing signed comparison laws. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
open Erdos7BinarySieve (expect expect_congr)
set_option maxHeartbeats 4000000

noncomputable def signedStep (E : ℕ) (q : ℕ → ℚ) (ν : ℕ →₀ ℚ) (L : ℚ) : ℕ →₀ ℚ :=
  Erdos7ExponentLaw.step E q ν - Finsupp.single 1 L

lemma expect_signedStep (E : ℕ) (q : ℕ → ℚ) (ν : ℕ →₀ ℚ) (L : ℚ) (f : ℕ → ℚ) :
    expect (signedStep E q ν L) f=expect (Erdos7ExponentLaw.step E q ν) f-L*f 1 := by
  unfold signedStep expect
  rw [Finsupp.sum_sub_index (by intros; ring)]
  simp

lemma signedStep_mass (E : ℕ) (q : ℕ → ℚ) (hqE : q E=0) (ν : ℕ →₀ ℚ) (L : ℚ) :
    expect (signedStep E q ν L) (fun _ => 1)=expect ν (fun _ => 1)-L := by
  rw [expect_signedStep,Erdos7ExponentLaw.step_mass E q hqE,mul_one]

section Comparison
variable {n : ℕ} (κ : Type*) (A : Fin n → Type*)
variable [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

/-- A universal convex bound for complete prefix-pattern families.
The law `ν` is not assumed nonnegative. -/
def CompleteConvexBound (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (t : ℕ) (μ : (∀ i, A i) → ℚ) (ν : ℕ →₀ ℚ) : Prop :=
  ∀ (M : ℕ) (K : Finset κ) (e : κ → Fin n → ℕ) (X : κ → ∀ i, Finset (A i)),
    (∀ k∈K, PrefixPattern E t (e k)) →
    (∀ k∈K, ∀ i∈expSupport (e k), c i*fraction (X k i)  ≤  q i (e k i-1)) →
    CompletePatterns E t K e M →
    ∀ (φ : ℚ → ℚ), ConvexOn ℚ Set.univ φ → Monotone φ →
    (∑ x, μ x*φ (∑ k∈K, boxIndicator A (expSupport (e k)) (X k) x))  ≤ 
      expect ν (fun k => φ ((M:ℚ)*k))

lemma completeConvexBound_initial (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (μ : (∀ i, A i) → ℚ) (hμ : (∑ x,μ x)=1) :
    CompleteConvexBound κ A E c q 0 μ Erdos7ExponentLaw.initial := by
  intro M K e X he hX hM φ hφ hmono
  have hz (k : κ) (hk : k∈K) : e k=fun _ => 0 := funext (fun i => (he k hk).2 i (Nat.zero_le _))
  have hcard : K.card=M := by
    have hh := hM _ (prefixPattern_zero E 0)
    have heq : K.filter (fun k => e k=fun _ => 0)=K := Finset.filter_true_of_mem hz
    rwa [heq] at hh
  have hval (x : ∀ i, A i) : (∑ k∈K, boxIndicator A (expSupport (e k)) (X k) x)=(M:ℚ) := by
    calc
      _ = ∑ _k∈K, (1:ℚ) := Finset.sum_congr rfl (fun k hk => by simp [hz k hk,expSupport,boxIndicator_empty])
      _ = _ := by simp [hcard]
  simp_rw [hval]
  rw [← Finset.sum_mul,hμ,one_mul,Erdos7ExponentLaw.expect_initial,Nat.cast_one,mul_one]

/-- Positive coordinate-mixture coefficients preserve the comparison even
when the old comparison law is signed. -/
theorem completeConvexBound_resample (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (ht : t < n)
    (μ : (∀ i, A i) → ℚ) (hμ : ∀ x, 0 ≤ μ x) (ν : ℕ →₀ ℚ)
    (hcomp : CompleteConvexBound κ A E c q t μ ν)
    (B : Finset (∀ i, A i)) (hc : 1 ≤ c ⟨t,ht⟩)
    (hq1 : q ⟨t,ht⟩ 0 ≤ 1)
    (hqdec : ∀ g, g < E ⟨t,ht⟩ → q ⟨t,ht⟩ (g+1) ≤ q ⟨t,ht⟩ g)
    (hqE : q ⟨t,ht⟩ (E ⟨t,ht⟩)=0) :
    CompleteConvexBound κ A E c q (t+1) (resample A ⟨t,ht⟩ μ B (c ⟨t,ht⟩))
      (Erdos7ExponentLaw.step (E ⟨t,ht⟩) (q ⟨t,ht⟩) ν) := by
  intro M K e X he hX hM φ hφ hmono
  let i : Fin n := ⟨t,ht⟩
  let e' (k : κ) := Function.update (e k) i 0
  let K' (a : ℕ) := K.filter (fun k => e k i ≤ a)
  have he' (k : κ) (hk : k∈K) : PrefixPattern E t (e' k) := by
    constructor
    · intro j
      by_cases hj : j=i
      · subst j; simp [e']
      · simpa only [e',Function.update_of_ne hj] using (he k hk).1 j
    · intro j hj
      by_cases hji : j=i
      · subst j; simp [e']
      · have hjt : j.val≠t := by intro heq; exact hji (Fin.ext heq)
        have hh := (he k hk).2 j (by omega)
        simpa only [e',Function.update_of_ne hji] using hh
  have hX' (k : κ) (hk : k∈K) (j : Fin n) (hj : j∈expSupport (e' k)) :
      c j*fraction (X k j) ≤ q j (e' k j-1) := by
    rw [expSupport_update_zero] at hj
    have hjne := (Finset.mem_erase.mp hj).1
    simpa only [e',Function.update_of_ne hjne] using hX k hk j (Finset.mem_erase.mp hj).2
  have hbound (a : ℕ) (ha : a ≤ E i) :
      (∑ x, μ x*φ (∑ k∈K' a, boxIndicator A (expSupport (e' k)) (X k) x))  ≤ 
        expect ν (fun k => φ ((((a+1)*M:ℕ):ℚ)*k)) :=
    hcomp ((a+1)*M) (K' a) e' X
      (fun k hk => he' k (Finset.mem_filter.mp hk).1)
      (fun k hk => hX' k (Finset.mem_filter.mp hk).1)
      (completePatterns_erase E t ht K e M hM a ha) φ hφ hmono
  have hstep := resample_exponent_compression A i μ hμ B (c i) hc φ hφ hmono K e X (E i) (q i)
    (fun k hk => (he k hk).1 i)
    (fun k hk hi => hX k hk i ((mem_expSupport _ _).mpr hi)) hqE
  apply hstep.trans
  have h0 := mul_le_mul_of_nonneg_left (hbound 0 (Nat.zero_le _)) (sub_nonneg.mpr hq1)
  have hsum := Finset.sum_le_sum (fun g (hg : g∈Finset.range (E i)) =>
    mul_le_mul_of_nonneg_left (hbound (g+1) (by have := Finset.mem_range.mp hg; omega))
      (sub_nonneg.mpr (hqdec g (Finset.mem_range.mp hg))))
  apply (add_le_add h0 hsum).trans_eq
  rw [Erdos7ExponentLaw.expect_step]
  simp only [Nat.zero_add,Nat.one_mul,Nat.add_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro g hg
  congr 1
  apply expect_congr
  intro k
  congr 1
  push_cast
  ring

/-- Exact-mass killing preserves the complete-pattern comparison, with the
removed mass subtracted at the mandatory baseline state `1`. -/
theorem completeConvexBound_killed (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (ht : t < n)
    (μ : (∀ i, A i) → ℚ) (hμ : ∀ x, 0 ≤ μ x) (ν : ℕ →₀ ℚ)
    (hcomp : CompleteConvexBound κ A E c q t μ ν)
    (B : Finset (∀ i, A i)) (hc : 1 ≤ c ⟨t,ht⟩)
    (hq1 : q ⟨t,ht⟩ 0 ≤ 1)
    (hqdec : ∀ g, g < E ⟨t,ht⟩ → q ⟨t,ht⟩ (g+1) ≤ q ⟨t,ht⟩ g)
    (hqE : q ⟨t,ht⟩ (E ⟨t,ht⟩)=0)
    (L : ℚ) (hLm : L ≤ ∑ x,μ x)
    (hL : (∑ x, μ x*residual (c ⟨t,ht⟩) (coordinateFraction A ⟨t,ht⟩ B x)) ≤ L) :
    CompleteConvexBound κ A E c q (t+1) (killedResample A ⟨t,ht⟩ μ B (c ⟨t,ht⟩) L)
      (signedStep (E ⟨t,ht⟩) (q ⟨t,ht⟩) ν L) := by
  intro M K e X he hX hM φ hφ hmono
  have htst := killedResample_test A ⟨t,ht⟩ μ hμ B (c ⟨t,ht⟩) L hc hLm hL
    (fun x => φ (∑ k∈K, boxIndicator A (expSupport (e k)) (X k) x)) (φ M)
    (fun x => hmono (completePatterns_boxCount_lower A E (t+1) K e M hM X x))
  have hfull := completeConvexBound_resample κ A E c q t ht μ hμ ν hcomp B hc hq1 hqdec hqE
    M K e X he hX hM φ hφ hmono
  apply htst.trans
  rw [expect_signedStep,Nat.cast_one,mul_one]
  exact sub_le_sub_right hfull _

end Comparison
#print axioms completeConvexBound_killed
end Erdos7KilledSieve



/-! Residual losses from full-pattern families under a signed convex bound. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
open Erdos7BinarySieve (expect)
set_option maxHeartbeats 4000000

/-- Bound a layered loss using convex comparison on the actual nonnegative
measure. No monotonicity of expectation against the signed law is used. -/
theorem complete_layer_loss_bound {n : ℕ} {κ : Type*}
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (t : ℕ) (μ : (∀ i, A i) → ℚ) (hμ : ∀ x, 0 ≤ μ x) (ν : ℕ →₀ ℚ)
    (hcomp : CompleteConvexBound κ A E c q t μ ν)
    (d s : ℚ) (hd : 1 ≤ d) (hs : 0 < s) (R : ℕ) (hR : 0 < R)
    (r : ℕ → ℚ) (hr : ∀ a, a < R → 0 ≤ r a) (hrs : (∑ a∈Finset.range R,r a) ≤ s)
    (K : ℕ → Finset κ) (e : ℕ → κ → Fin n → ℕ) (X : ℕ → κ → ∀ i, Finset (A i))
    (he : ∀ a, a < R → ∀ k∈K a, PrefixPattern E t (e a k))
    (hX : ∀ a, a < R → ∀ k∈K a, ∀ i∈expSupport (e a k), c i*fraction (X a k i) ≤ q i (e a k i-1))
    (hM : ∀ a, a < R → CompletePatterns E t (K a) (e a) 1)
    (α : (∀ i, A i) → ℚ)
    (hα : ∀ x, α x ≤ ∑ a∈Finset.range R, r a*∑ k∈K a, boxIndicator A (expSupport (e a k)) (X a k) x) :
    (∑ x, μ x*residual d (α x)) ≤ expect ν (fun k => residual d (s*k)) := by
  let N (a : ℕ) (x : ∀ i, A i) := ∑ k∈K a, boxIndicator A (expSupport (e a k)) (X a k) x
  let φ (x : ℚ) := residual d (s*x)
  let G := expect ν (fun k => φ k)
  have hd0 : 0 ≤ d := (by norm_num : (0:ℚ) ≤ 1).trans hd
  have hcmp (a : ℕ) (ha : a < R) : (∑ x, μ x*φ (N a x)) ≤ G := by
    have hh := hcomp 1 (K a) (e a) (X a) (he a ha) (hX a ha) (hM a ha) φ
      (residual_scaled_convex _ _) (residual_scaled_monotone _ _ hd0 hs.le)
    simpa only [Nat.cast_one,one_mul] using hh
  have hG : 0 ≤ G :=
    (Finset.sum_nonneg (fun x _ => mul_nonneg (hμ x) (le_max_left _ _))).trans (hcmp 0 hR)
  have hres (x : ∀ i, A i) : residual d (α x) ≤
      ∑ a∈Finset.range R, (r a/s)*φ (N a x) := by
    apply (max_le_max le_rfl (sub_le_sub_right (mul_le_mul_of_nonneg_left (hα x) hd0) _)).trans
    exact weighted_residual_bound (Finset.range R) d s hd hs r (fun a => N a x)
      (fun a ha => hr a (Finset.mem_range.mp ha)) hrs
  calc
    _ ≤ ∑ x, μ x*(∑ a∈Finset.range R, (r a/s)*φ (N a x)) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hres x) (hμ x))
    _ = ∑ a∈Finset.range R, (r a/s)*(∑ x, μ x*φ (N a x)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ ≤ ∑ a∈Finset.range R, (r a/s)*G :=
      Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hcmp a (Finset.mem_range.mp ha))
        (div_nonneg (hr a (Finset.mem_range.mp ha)) hs.le))
    _ ≤ G := by
      rw [← Finset.sum_mul,← Finset.sum_div]
      have hh := mul_le_mul_of_nonneg_right ((div_le_one hs).mpr hrs) hG
      simpa only [one_mul] using hh

#print axioms complete_layer_loss_bound
end Erdos7KilledSieve



/-! A positive-mass avoidance theorem for the signed full-pattern sieve. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
open Erdos7BinarySieve (expect)
set_option maxHeartbeats 4000000

noncomputable def signedTower {n : ℕ} (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ)
    (loss : Fin n → (ℕ →₀ ℚ) → ℚ) : ℕ → (ℕ →₀ ℚ)
  | 0 => Erdos7ExponentLaw.initial
  | t+1 => if h : t < n then
      signedStep (E ⟨t,h⟩) (q ⟨t,h⟩) (signedTower E q loss t) (loss ⟨t,h⟩ (signedTower E q loss t))
    else signedTower E q loss t

section Tower
variable {n : ℕ} {κ : Type*} (A : Fin n → Type*)
variable [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

/-- Nonnegative old weights which vanish on a whole fibre also vanish there
after resampling, regardless of the new exclusion set. -/
lemma resample_zero_on_fibre (i : Fin n) (μ : (∀ j, A j) → ℚ)
    (B : Finset (∀ j, A j)) (c : ℚ) (x : ∀ j, A j)
    (hz : ∀ v : A i, μ (Function.update x i v)=0) : resample A i μ B c x=0 := by
  have hm : coordinateMarginal A i μ (splitCoordinate A i x).1=0 := by
    unfold coordinateMarginal
    simp_rw [joinCoordinate_split_update,hz]
    simp
  simp only [resample,Erdos7Distortion.step,hm,zero_mul,zero_div]

lemma killedResample_preserves_zero (i : Fin n) (μ : (∀ j, A j) → ℚ)
    (B D : Finset (∀ j, A j)) (c L : ℚ)
    (hD : ∀ x v, Function.update x i v∈D ↔ x∈D)
    (hz : ∀ x∈D, μ x=0) (x : ∀ j, A j) (hx : x∈D) :
    killedResample A i μ B c L x=0 := by
  have hh := resample_zero_on_fibre A i μ B c x (fun v => hz _ ((hD x v).mpr hx))
  simp only [killedResample,trimOutside,hh,mul_zero,ite_self]

noncomputable def killedTower (B : Fin n → Finset (∀ i, A i)) (c : Fin n → ℚ)
    (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ) (loss : Fin n → (ℕ →₀ ℚ) → ℚ) :
    ℕ → (∀ i, A i) → ℚ
  | 0 => towerWeights A B c 0
  | t+1 => if h : t < n then
      killedResample A ⟨t,h⟩ (killedTower B c E q loss t) (B ⟨t,h⟩) (c ⟨t,h⟩)
        (loss ⟨t,h⟩ (signedTower E q loss t))
    else killedTower B c E q loss t

/-- All finite-prefix invariants: actual positivity, exact signed-law mass,
complete-family comparison, and vanishing on every processed excluded set. -/
theorem killedTower_invariants (B : Fin n → Finset (∀ i, A i)) (c : Fin n → ℚ)
    (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ) (loss : Fin n → (ℕ →₀ ℚ) → ℚ)
    (hc : ∀ i, 1 ≤ c i) (hq1 : ∀ i, q i 0 ≤ 1)
    (hqdec : ∀ i g, g < E i → q i (g+1) ≤ q i g) (hqE : ∀ i, q i (E i)=0)
    (hB : ∀ i j : Fin n, j < i → ∀ x v, Function.update x i v∈B j ↔ x∈B j)
    (horacle : ∀ (i : Fin n) (μ : (∀ j, A j) → ℚ) (ν : ℕ →₀ ℚ),
      (∀ x, 0 ≤ μ x) → CompleteConvexBound κ A E c q i.val μ ν →
      (∑ x, μ x*residual (c i) (coordinateFraction A i (B i) x)) ≤ loss i ν)
    (hmass : ∀ t, t ≤ n → 0 ≤ expect (signedTower E q loss t) (fun _ => 1))
    (t : ℕ) (ht : t ≤ n) :
    (∀ x, 0 ≤ killedTower A B c E q loss t x) ∧
    (∑ x, killedTower A B c E q loss t x)=expect (signedTower E q loss t) (fun _ => 1) ∧
    CompleteConvexBound κ A E c q t (killedTower A B c E q loss t) (signedTower E q loss t) ∧
    (∀ j : Fin n, j.val < t → ∀ x∈B j, killedTower A B c E q loss t x=0) := by
  induction t with
  | zero =>
    refine ⟨towerWeights_nonneg A B c hc 0,?_,?_,?_⟩
    · simp only [killedTower,signedTower,Erdos7ExponentLaw.expect_initial,towerWeights_total A B c hc]
    · exact completeConvexBound_initial κ A E c q _ (towerWeights_total A B c hc 0)
    · intro j hj; omega
  | succ t ih =>
    have ht' : t ≤ n := by omega
    obtain ⟨hμ,hμtot,hcomp,hzero⟩ := ih ht'
    have htn : t < n := by omega
    let i : Fin n := ⟨t,htn⟩
    let μ := killedTower A B c E q loss t
    let ν := signedTower E q loss t
    let L := loss i ν
    have hνsucc : signedTower E q loss (t+1)=signedStep (E i) (q i) ν L := by
      simp only [signedTower,dif_pos htn,ν,L,i]
    have hμsucc : killedTower A B c E q loss (t+1)=killedResample A i μ (B i) (c i) L := by
      simp only [killedTower,dif_pos htn,μ,ν,L,i]
    have hL := horacle i μ ν hμ hcomp
    have hLm : L ≤ ∑ x, μ x := by
      have hh := hmass (t+1) ht
      rw [hνsucc,signedStep_mass _ _ (hqE i)] at hh
      change L ≤ ∑ x, killedTower A B c E q loss t x
      rw [hμtot]
      exact sub_nonneg.mp hh
    rw [hμsucc,hνsucc]
    refine ⟨killedResample_nonneg A i μ hμ (B i) (c i) L (hc i) hLm,?_,?_,?_⟩
    · rw [killedResample_total A i μ (B i) (c i) L (hc i) hLm hL,
        signedStep_mass _ _ (hqE i)]
      exact congrArg (fun z => z-L) hμtot
    · exact completeConvexBound_killed κ A E c q t htn μ hμ ν hcomp (B i) (hc i)
        (hq1 i) (hqdec i) (hqE i) L hLm hL
    · intro j hj x hx
      by_cases hji : j=i
      · subst j
        exact killedResample_zero A i μ (B i) (c i) L x hx
      · have hjt : j.val < t := by
          have hjne : j.val≠t := by intro heq; exact hji (Fin.ext heq)
          omega
        exact killedResample_preserves_zero A i μ (B i) (B j) (c i) L
          (hB i j hjt) (hzero j hjt) x hx

/-- Positive final comparison mass gives a point avoiding all layered bad
sets. This is a finite theorem, valid for signed comparison laws. -/
theorem killed_tower_avoids (B : Fin n → Finset (∀ i, A i)) (c : Fin n → ℚ)
    (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ) (loss : Fin n → (ℕ →₀ ℚ) → ℚ)
    (hc : ∀ i, 1 ≤ c i) (hq1 : ∀ i, q i 0 ≤ 1)
    (hqdec : ∀ i g, g < E i → q i (g+1) ≤ q i g) (hqE : ∀ i, q i (E i)=0)
    (hB : ∀ i j : Fin n, j < i → ∀ x v, Function.update x i v∈B j ↔ x∈B j)
    (horacle : ∀ (i : Fin n) (μ : (∀ j, A j) → ℚ) (ν : ℕ →₀ ℚ),
      (∀ x, 0 ≤ μ x) → CompleteConvexBound κ A E c q i.val μ ν →
      (∑ x, μ x*residual (c i) (coordinateFraction A i (B i) x)) ≤ loss i ν)
    (hmass : ∀ t, t ≤ n → 0 ≤ expect (signedTower E q loss t) (fun _ => 1))
    (hpos : 0 < expect (signedTower E q loss n) (fun _ => 1)) :
    ∃ x : ∀ i, A i, ∀ i, x∉B i := by
  obtain ⟨hμ,hμtot,hcomp,hzero⟩ := killedTower_invariants A B c E q loss hc hq1 hqdec hqE hB horacle hmass n le_rfl
  have hp : 0 < ∑ x, killedTower A B c E q loss n x := by rwa [hμtot]
  have hex : ∃ x, 0 < killedTower A B c E q loss n x := by
    by_contra hh
    push_neg at hh
    have hsum := Finset.sum_nonpos (fun x (_ : x∈(Finset.univ : Finset (∀ i,A i))) => hh x)
    exact (not_le_of_gt hp) hsum
  obtain ⟨x,hpx⟩ := hex
  refine ⟨x,fun i hi => ?_⟩
  have hz := hzero i i.isLt x hi
  rw [hz] at hpx
  exact (lt_irrefl _ hpx)

end Tower
#print axioms killed_tower_avoids
end Erdos7KilledSieve



/-! The signed killed-law criterion for complete nonzero exponent rectangles. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
open Erdos7BinarySieve (expect)
set_option maxHeartbeats 4000000

/-- A positive signed residual budget rules out a covering by a complete
nonzero exponent rectangle. All finite exponents and arbitrary residues are
permitted. Positivity is required for each prefix, since the actual measures
must retain nonnegative mass throughout. -/
theorem complete_box_killed_avoidance {n : ℕ} {κ : Type*} [Fintype κ]
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (E : Fin n → ℕ) (hE : ∀ i, 0 < E i) (c s : Fin n → ℚ) (r q : Fin n → ℕ → ℚ)
    (hc : ∀ i, 1 ≤ c i) (hs : ∀ i, 0 < s i)
    (hr : ∀ i g, g < E i → 0 ≤ r i (g+1))
    (hrs : ∀ i, (∑ g∈Finset.range (E i),r i (g+1)) ≤ s i)
    (hq1 : ∀ i, q i 0 ≤ 1) (hqdec : ∀ i g, g < E i → q i (g+1) ≤ q i g)
    (hqE : ∀ i, q i (E i)=0) (hqr : ∀ i g, g < E i → c i*r i (g+1) ≤ q i g)
    (e : κ → Fin n → ℕ) (heinj : Function.Injective e)
    (he : ∀ k i, e k i ≤ E i) (hne : ∀ k, (expSupport (e k)).Nonempty)
    (hfull : ∀ f : Fin n → ℕ, (∀ i, f i ≤ E i) → (∃ i, f i≠0) → ∃ k, e k=f)
    (X : κ → ∀ i, Finset (A i))
    (hX : ∀ k i, e k i≠0 → fraction (X k i) ≤ r i (e k i))
    (hmass : ∀ t, t ≤ n → 0 ≤ expect (signedTower E q
      (fun i ν => expect ν (fun k => residual (c i) (s i*k))) t) (fun _ => 1))
    (hpos : 0 < expect (signedTower E q
      (fun i ν => expect ν (fun k => residual (c i) (s i*k))) n) (fun _ => 1)) :
    ∃ x : ∀ i, A i, ∀ k, ¬ (∀ i∈expSupport (e k), x i∈X k i) := by
  classical
  let S (k : κ) := expSupport (e k)
  let σ (k : κ) := (S k).max' (hne k)
  have hσ (k : κ) : σ k∈S k := Finset.max'_mem _ _
  have hS (k : κ) (j : Fin n) (hj : j∈S k) : j ≤ σ k := Finset.le_max' _ _ hj
  let B := layeredBad A S X σ
  have hB : ∀ i j : Fin n, j < i → ∀ x v, Function.update x i v∈B j ↔ x∈B j := by
    intro i j hji x v
    exact layeredBad_invariant A S X σ hS i j hji x v
  have hc0 : ∀ i, 0 ≤ c i := fun i => (by norm_num : (0:ℚ) ≤ 1).trans (hc i)
  have horacle (i : Fin n) (μ : (∀ j, A j) → ℚ) (ν : ℕ →₀ ℚ)
      (hμ : ∀ x, 0 ≤ μ x) (hcomp : CompleteConvexBound κ A E c q i.val μ ν) :
      (∑ x, μ x*residual (c i) (coordinateFraction A i (B i) x)) ≤
        expect ν (fun k => residual (c i) (s i*k)) := by
    let K := layerFamily σ i
    let Kg (g : ℕ) := K.filter (fun k => e k i=g+1)
    let e' (k : κ) := Function.update (e k) i 0
    let W (k : κ) (x : ∀ j, A j) := boxIndicator A (expSupport (e' k)) (X k) x
    let N (g : ℕ) (x : ∀ j, A j) := ∑ k∈Kg g, W k x
    have hki (k : κ) (hk : k∈K) : i∈S k := by
      simpa only [(Finset.mem_filter.mp hk).2] using hσ k
    have he' (k : κ) (hk : k∈K) : PrefixPattern E i.val (e' k) := by
      constructor
      · intro j
        by_cases hj : j=i
        · subst j; simp [e']
        · simpa only [e',Function.update_of_ne hj] using he k j
      · intro j hj
        by_cases hji : j=i
        · subst j; simp [e']
        · have hz : e k j=0 := by
            by_contra h
            have hle := hS k j ((mem_expSupport _ _).mpr h)
            rw [(Finset.mem_filter.mp hk).2] at hle
            have hlt : i < j := lt_of_le_of_ne hj (Ne.symm hji)
            exact (not_le_of_gt hlt) hle
          simpa only [e',Function.update_of_ne hji] using hz
    have hX' (k : κ) (j : Fin n) (hj : j∈expSupport (e' k)) :
        c j*fraction (X k j) ≤ q j (e' k j-1) := by
      rw [expSupport_update_zero] at hj
      have hjne := (Finset.mem_erase.mp hj).1
      have hpos := (mem_expSupport _ _).mp (Finset.mem_erase.mp hj).2
      have hEj : e k j-1 < E j := by have := he k j; omega
      have hq := hqr j (e k j-1) hEj
      have heq : e k j-1+1=e k j := by omega
      rw [heq] at hq
      simpa only [e',Function.update_of_ne hjne] using
        (mul_le_mul_of_nonneg_left (hX k j hpos) (hc0 j)).trans hq
    have hmult (g : ℕ) (hg : g < E i) : CompletePatterns E i.val (Kg g) e' 1 := by
      intro f hf
      let v := Function.update f i (g+1)
      have hvE (j : Fin n) : v j ≤ E j := by
        by_cases hj : j=i
        · subst j; simpa only [v,Function.update_self] using (show g+1 ≤ E i by omega)
        · simpa only [v,Function.update_of_ne hj] using hf.1 j
      obtain ⟨k,hkv⟩ := hfull v hvE ⟨i,by simp [v]⟩
      have hki' : e k i=g+1 := by simp only [hkv,v,Function.update_self]
      have hσi : σ k=i := by
        apply le_antisymm
        · apply Finset.max'_le
          intro j hj
          by_contra h
          have hij : i < j := lt_of_not_ge h
          have hji : j≠i := ne_of_gt hij
          have hz := hf.2 j hij.le
          have hh := (mem_expSupport _ _).mp hj
          simp only [hkv,v,Function.update_of_ne hji,hz] at hh
          exact hh rfl
        · exact hS k i ((mem_expSupport _ _).mpr (by omega))
      have hkKg : k∈Kg g := by simp [Kg,K,layerFamily,hσi,hki']
      have hkf : e' k=f := by
        funext j
        by_cases hj : j=i
        · subst j
          simp only [e',Function.update_self,hf.2 i le_rfl]
        · simp only [e',Function.update_of_ne hj,hkv,v]
      have hle : ((Kg g).filter (fun k => e' k=f)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro u hu w hw
        obtain ⟨hu,huf⟩ := Finset.mem_filter.mp hu
        obtain ⟨hw,hwf⟩ := Finset.mem_filter.mp hw
        have hug := (Finset.mem_filter.mp hu).2
        have hwg := (Finset.mem_filter.mp hw).2
        apply heinj
        funext j
        by_cases hj : j=i
        · subst j; exact hug.trans hwg.symm
        · have hh := congrFun (huf.trans hwf.symm) j
          simpa only [e',Function.update_of_ne hj] using hh
      exact le_antisymm hle (Finset.card_pos.mpr ⟨k,Finset.mem_filter.mpr ⟨hkKg,hkf⟩⟩)
    have hpoint (x : ∀ j, A j) : coordinateFraction A i (B i) x ≤
        ∑ g∈Finset.range (E i), r i (g+1)*N g x := by
      have hzero : K.filter (fun k => e k i=0)=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro k hk
        obtain ⟨hk,hz⟩ := Finset.mem_filter.mp hk
        exact (mem_expSupport _ _).mp (hki k hk) hz
      have hfullK : K.filter (fun k => e k i ≤ E i)=K := Finset.filter_true_of_mem (fun k _ => he k i)
      have hsum := sum_filter_nat_le K (fun k => e k i) (E i) (fun k => r i (e k i)*W k x)
      rw [hzero,hfullK,Finset.sum_empty,zero_add] at hsum
      calc
        _ ≤ ∑ k∈K, fraction (X k i)*boxIndicator A ((S k).erase i) (X k) x :=
          layered_fraction_bound A S X σ hσ i x
        _ ≤ ∑ k∈K, r i (e k i)*W k x := by
          apply Finset.sum_le_sum
          intro k hk
          have hi := (mem_expSupport _ _).mp (hki k hk)
          simpa only [W,e',expSupport_update_zero,S] using
            mul_le_mul_of_nonneg_right (hX k i hi) (boxIndicator_nonneg A ((S k).erase i) (X k) x)
        _ = ∑ g∈Finset.range (E i), r i (g+1)*N g x := by
          rw [hsum]
          apply Finset.sum_congr rfl
          intro g hg
          rw [show r i (g+1)*N g x=∑ k∈Kg g, r i (g+1)*W k x from Finset.mul_sum _ _ _]
          apply Finset.sum_congr rfl
          intro k hk
          rw [(Finset.mem_filter.mp hk).2]
    exact complete_layer_loss_bound A E c q i.val μ hμ ν hcomp (c i) (s i) (hc i) (hs i)
      (E i) (hE i) (fun g => r i (g+1)) (hr i) (hrs i) Kg (fun _ => e') (fun _ => X)
      (fun g hg k hk => he' k (Finset.mem_filter.mp hk).1)
      (fun g hg k hk => hX' k) hmult (coordinateFraction A i (B i)) hpoint
  obtain ⟨x,hx⟩ := killed_tower_avoids A B c E q
    (fun i ν => expect ν (fun k => residual (c i) (s i*k))) hc hq1 hqdec hqE hB horacle hmass hpos
  refine ⟨x,fun k hk => hx (σ k) ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,k,by simp [layerFamily],hk⟩

#print axioms complete_box_killed_avoidance
end Erdos7KilledSieve



/-! Complete a distinct box family by inserting missing exponent patterns. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
open Erdos7BinarySieve (expect)
set_option maxHeartbeats 4000000

/-- The complete-rectangle criterion applies to arbitrary distinct nonzero
exponent families: missing patterns can be filled by empty boxes. -/
theorem distinct_box_killed_avoidance {n : ℕ} {κ : Type*} [Fintype κ]
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (E : Fin n → ℕ) (hE : ∀ i, 0 < E i) (c s : Fin n → ℚ) (r q : Fin n → ℕ → ℚ)
    (hc : ∀ i, 1 ≤ c i) (hs : ∀ i, 0 < s i)
    (hr : ∀ i g, g < E i → 0 ≤ r i (g+1))
    (hrs : ∀ i, (∑ g∈Finset.range (E i),r i (g+1)) ≤ s i)
    (hq1 : ∀ i, q i 0 ≤ 1) (hqdec : ∀ i g, g < E i → q i (g+1) ≤ q i g)
    (hqE : ∀ i, q i (E i)=0) (hqr : ∀ i g, g < E i → c i*r i (g+1) ≤ q i g)
    (e : κ → Fin n → ℕ) (heinj : Function.Injective e)
    (he : ∀ k i, e k i ≤ E i) (hne : ∀ k, (expSupport (e k)).Nonempty)
    (X : κ → ∀ i, Finset (A i))
    (hX : ∀ k i, e k i≠0 → fraction (X k i) ≤ r i (e k i))
    (hmass : ∀ t, t ≤ n → 0 ≤ expect (signedTower E q
      (fun i ν => expect ν (fun k => residual (c i) (s i*k))) t) (fun _ => 1))
    (hpos : 0 < expect (signedTower E q
      (fun i ν => expect ν (fun k => residual (c i) (s i*k))) n) (fun _ => 1)) :
    ∃ x : ∀ i, A i, ∀ k, ¬ (∀ i∈expSupport (e k), x i∈X k i) := by
  classical
  let V := ∀ i : Fin n, Fin (E i+1)
  let ρ := {v : V // ∃ i, (v i:ℕ)≠0}
  let e' (k : ρ) (i : Fin n) : ℕ := k.val i
  have he' (k : ρ) (i : Fin n) : e' k i ≤ E i := Nat.le_of_lt_succ (k.val i).isLt
  have hne' (k : ρ) : (expSupport (e' k)).Nonempty := by
    obtain ⟨i,hi⟩ := k.property
    exact ⟨i,(mem_expSupport _ _).mpr hi⟩
  have hinj' : Function.Injective e' := by
    intro k l hkl
    apply Subtype.ext
    funext i
    exact Fin.ext (congrFun hkl i)
  have hfull' (f : Fin n → ℕ) (hf : ∀ i, f i ≤ E i) (hfn : ∃ i, f i≠0) : ∃ k : ρ, e' k=f := by
    exact ⟨⟨fun i => ⟨f i,by have := hf i; omega⟩,hfn⟩,rfl⟩
  let X' (k : ρ) (i : Fin n) : Finset (A i) :=
    if h : ∃ l, e l=e' k then X h.choose i else ∅
  have hX' (k : ρ) (i : Fin n) (hi : e' k i≠0) : fraction (X' k i) ≤ r i (e' k i) := by
    dsimp only [X']
    split_ifs with h
    · have heq := congrFun h.choose_spec i
      simpa only [heq] using hX h.choose i (by simpa only [heq] using hi)
    · have hg : e' k i-1 < E i := by have := he' k i; omega
      have hh := hr i (e' k i-1) hg
      have heq : e' k i-1+1=e' k i := by omega
      simpa only [fraction,Finset.card_empty,Nat.cast_zero,zero_div,heq] using hh
  obtain ⟨x,hx⟩ := complete_box_killed_avoidance A E hE c s r q hc hs hr hrs hq1 hqdec hqE hqr
    e' hinj' he' hne' hfull' X' hX' hmass hpos
  refine ⟨x,fun k hk => ?_⟩
  obtain ⟨l,hl⟩ := hfull' (e k) (he k) (by
    obtain ⟨i,hi⟩ := hne k
    exact ⟨i,(mem_expSupport _ _).mp hi⟩)
  have hex : ∃ j, e j=e' l := ⟨k,hl.symm⟩
  have hchoice : hex.choose=k := heinj (hex.choose_spec.trans hl)
  apply hx l
  intro i hi
  have hi' : i∈expSupport (e k) := by simpa only [hl] using hi
  have hXi : X' l i=X k i := by simp only [X',dif_pos hex,hchoice]
  rw [hXi]
  exact hk i hi'

#print axioms distinct_box_killed_avoidance
end Erdos7KilledSieve



/-! Arithmetic specialization of the signed complete-pattern killed sieve. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve Erdos7StarSieve
open Erdos7BinarySieve (expect)
set_option maxHeartbeats 4000000

/-- Positive final signed mass, with nonnegative mass throughout, precludes
an arithmetic cover by distinct finite exponent patterns. -/
theorem arithmetic_killed_not_cover {n : ℕ} {κ : Type*} [Fintype κ]
    (p E : Fin n → ℕ) (hp : ∀ i, 1 < p i) (hE : ∀ i, 0 < E i)
    (hcop : Pairwise (Function.onFun Nat.Coprime p))
    (e : κ → Fin n → ℕ) (he : Function.Injective e) (he0 : ∀ k, ∃ i, e k i≠0)
    (heE : ∀ k i, e k i≤E i) (a : κ → ℤ)
    (c s : Fin n → ℚ) (hc : ∀ i, 1≤c i) (hcp : ∀ i, c i≤p i)
    (hs : ∀ i, 0<s i)
    (hsum : ∀ i, (∑ g∈Finset.range (E i), ((p i:ℚ)⁻¹)^(g+1))≤s i)
    (hmass : ∀ t, t ≤ n → 0 ≤ expect (signedTower E (fun i => powerTail (p i) (c i) (E i))
      (fun i ν => expect ν (fun k => residual (c i) (s i*k))) t) (fun _ => 1))
    (hpos : 0 < expect (signedTower E (fun i => powerTail (p i) (c i) (E i))
      (fun i ν => expect ν (fun k => residual (c i) (s i*k))) n) (fun _ => 1)) :
    ¬ (∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k) := by
  intro hcover
  classical
  letI (i : Fin n) : NeZero (p i) := ⟨by have := hp i; omega⟩
  let A (i : Fin n) := ZMod (p i ^ E i)
  let f (k : κ) (i : Fin n) := ZMod.castHom (pow_dvd_pow (p i) (heE k i)) (ZMod (p i ^ e k i))
  let B (k : κ) (i : Fin n) := Finset.univ.filter (fun x : A i => f k i x = (a k : ZMod (p i ^ e k i)))
  have hBcard (k : κ) (i : Fin n) : ((B k i).card : ℚ) ≤
      (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(e k i) := by
    have hh := surjective_fiber_card_rat (f k i).toAddMonoidHom
      (ZMod.castHom_surjective (pow_dvd_pow (p i) (heE k i))) (a k)
    change ((B k i).card : ℚ) = _ at hh
    rw [hh]
    simp only [A, ZMod.card, Nat.cast_pow, div_eq_mul_inv, inv_pow]
    exact le_rfl
  have hbox : ∀ x : ∀ i, A i, ∃ k, ∀ i, x i ∈ B k i := by
    intro x
    let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) (fun i => p i ^ E i) Finset.univ
      (fun i _ => pow_ne_zero _ (NeZero.ne _))
      (fun i _ j _ hij => (hcop hij).pow _ _)
    have hz (i : Fin n) : (z.val : A i) = x i := by
      rw [← ZMod.natCast_zmod_val (x i)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
    obtain ⟨k, hk⟩ := hcover (z.val : ℤ)
    refine ⟨k, ?_⟩
    intro i
    have hpi : p i ^ e k i ∣ ∏ j, p j ^ e k j :=
      Finset.dvd_prod_of_mem (fun j => p j ^ e k j) (Finset.mem_univ i)
    have hpi' : ((p i ^ e k i : ℕ) : ℤ) ∣ ((∏ j, p j ^ e k j : ℕ) : ℤ) := by exact_mod_cast hpi
    have hqi := hpi'.trans hk
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hz i, map_natCast]
    symm
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (a k) (z.val : ℤ) (p i ^ e k i)).mpr hqi
  have hc0 : ∀ i, 0≤c i := fun i => (by norm_num : (0:ℚ)≤1).trans (hc i)
  have hfrac (k : κ) (i : Fin n) : fraction (B k i)≤((p i:ℚ)⁻¹)^(e k i) := by
    apply (div_le_iff₀ card_pos_rat).mpr
    simpa only [mul_comm] using hBcard k i
  obtain ⟨x,hx⟩ := distinct_box_killed_avoidance A E hE c s (fun i g => ((p i:ℚ)⁻¹)^g)
    (fun i => powerTail (p i) (c i) (E i)) hc hs (fun _ _ _ => by positivity) hsum
    (fun i => powerTail_zero_le_one (p i) (hp i) (c i) (hcp i) (E i))
    (fun i g _ => powerTail_decreasing (p i) (hp i) (c i) (hc0 i) (E i) g)
    (fun i => powerTail_terminal (p i) (c i) (E i))
    (fun i g hg => by simp only [powerTail,if_pos hg,le_refl]) e he heE (by
      intro k
      obtain ⟨i,hi⟩ := he0 k
      exact ⟨i,(mem_expSupport _ _).mpr hi⟩) B (fun k i _ => hfrac k i) hmass hpos
  obtain ⟨k,hk⟩ := hbox x
  exact hx k (fun i _ => hk i)

#print axioms arithmetic_killed_not_cover
end Erdos7KilledSieve



/-! Mass-sensitive refinements of stop-loss bounds. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
open Erdos7BinarySieve (expect)
set_option maxHeartbeats 4000000

lemma hinge_shift_bound (x u v : ℚ) (huv : u ≤ v) :
    max 0 (x-u) ≤ max 0 (x-v)+(v-u) := by
  apply max_le
  · exact add_nonneg (le_max_left _ _) (sub_nonneg.mpr huv)
  · have hh := le_max_right 0 (x-v)
    linarith

/-- A stop-loss function of a nonnegative measure is Lipschitz with constant
its total mass. This remains available when its upper comparison law is signed. -/
theorem stopLoss_mass_bound {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℚ) (hμ : ∀ x, 0 ≤ μ x) (f : Ω → ℚ) (u v : ℚ) (huv : u ≤ v) :
    (∑ x, μ x*max 0 (f x-u)) ≤
      (∑ x, μ x*max 0 (f x-v))+(v-u)*(∑ x,μ x) := by
  calc
    _ ≤ ∑ x, μ x*(max 0 (f x-v)+(v-u)) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hinge_shift_bound (f x) u v huv) (hμ x))
    _ = _ := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib,← Finset.sum_mul,mul_comm (∑ x, μ x) (v-u)]

/-- Any known stop-loss upper bound can be tightened using the actual mass.
This does not integrate inequalities against the signed comparison law. -/
theorem stopLoss_compare_at_larger_threshold {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℚ) (hμ : ∀ x, 0 ≤ μ x) (f : Ω → ℚ)
    (ν : ℕ →₀ ℚ) (M m u v : ℚ) (hM : 0 ≤ M) (huv : u ≤ v)
    (hm : (∑ x,μ x)=m)
    (hcomp : (∑ x,μ x*max 0 (f x-M*v)) ≤ expect ν (fun k => max 0 (M*k-M*v))) :
    (∑ x,μ x*max 0 (f x-M*u)) ≤
      expect ν (fun k => max 0 (M*k-M*v))+M*(v-u)*m := by
  have hh := stopLoss_mass_bound μ hμ f (M*u) (M*v) (mul_le_mul_of_nonneg_left huv hM)
  rw [hm,← mul_sub] at hh
  exact hh.trans (add_le_add_left hcomp _)

/-- The complete-family comparison supplies the required hinge test at any
larger threshold. In particular it permits mass-sensitive pruning before the
next coordinate step. -/
theorem completeConvexBound_stopLoss {n : ℕ} {κ : Type*}
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (t : ℕ) (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x) (ν : ℕ →₀ ℚ)
    (hcomp : CompleteConvexBound κ A E c q t μ ν)
    (M : ℕ) (K : Finset κ) (e : κ → Fin n → ℕ) (X : κ → ∀ i,Finset (A i))
    (he : ∀ k∈K,PrefixPattern E t (e k))
    (hX : ∀ k∈K,∀ i∈expSupport (e k),c i*fraction (X k i) ≤ q i (e k i-1))
    (hM : CompletePatterns E t K e M) (m u v : ℚ) (hm : (∑ x,μ x)=m) (huv : u ≤ v) :
    (∑ x,μ x*max 0 ((∑ k∈K,boxIndicator A (expSupport (e k)) (X k) x)-(M:ℚ)*u)) ≤
      expect ν (fun k => max 0 ((M:ℚ)*k-(M:ℚ)*v))+(M:ℚ)*(v-u)*m := by
  apply stopLoss_compare_at_larger_threshold μ hμ _ ν M m u v (Nat.cast_nonneg M) huv hm
  have hh := hcomp M K e X he hX hM (fun z => max 0 (z-(M:ℚ)*v))
    (by simpa only [one_mul,sub_eq_add_neg] using hinge_convex 1 (-((M:ℚ)*v)))
    (by intro x y hxy; exact max_le_max le_rfl (sub_le_sub_right hxy _))
  exact hh

#print axioms completeConvexBound_stopLoss
end Erdos7KilledSieve



/-! Positive upper-tail laws obtained by a mass-sensitive stop-loss refinement. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7BinarySieve (expect expect_congr expect_add expect_mul)
set_option maxHeartbeats 4000000

noncomputable def tailLaw (ν : ℕ →₀ ℚ) (b : ℕ) : ℕ →₀ ℚ := ν.filter (fun k => b < k)
noncomputable def tailMass (ν : ℕ →₀ ℚ) (b : ℕ) : ℚ := expect (tailLaw ν b) (fun _ => 1)
noncomputable def upperLaw (ν : ℕ →₀ ℚ) (b : ℕ) (m : ℚ) : ℕ →₀ ℚ :=
  tailLaw ν b + Finsupp.single b (m-tailMass ν b)

lemma expect_tailLaw (ν : ℕ →₀ ℚ) (b : ℕ) (f : ℕ → ℚ) :
    expect (tailLaw ν b) f=expect ν (fun k => if b < k then f k else 0) := by
  unfold tailLaw expect
  rw [Finsupp.sum_filter_index,Finsupp.support_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs with h <;> simp [h]

lemma expect_upperLaw (ν : ℕ →₀ ℚ) (b : ℕ) (m : ℚ) (f : ℕ → ℚ) :
    expect (upperLaw ν b m) f=expect (tailLaw ν b) f+(m-tailMass ν b)*f b := by
  rw [upperLaw,Erdos7ExponentLaw.expect_add_law]
  simp only [expect,Finsupp.sum_single_index,zero_mul]

lemma upperLaw_mass (ν : ℕ →₀ ℚ) (b : ℕ) (m : ℚ) :
    expect (upperLaw ν b m) (fun _ => 1)=m := by
  rw [expect_upperLaw,mul_one]
  change tailMass ν b+(m-tailMass ν b)=m
  ring

lemma upperLaw_nonneg (ν : ℕ →₀ ℚ) (hν : ∀ k,0 ≤ ν k) (b : ℕ) (m : ℚ)
    (hm : tailMass ν b ≤ m) (k : ℕ) : 0 ≤ upperLaw ν b m k := by
  simp only [upperLaw,Finsupp.add_apply,tailLaw,Finsupp.filter_apply,Finsupp.single_apply]
  apply add_nonneg
  · split_ifs <;> [exact hν k; exact le_rfl]
  · split_ifs <;> [exact sub_nonneg.mpr hm; exact le_rfl]

lemma tailLaw_hinge_above (ν : ℕ →₀ ℚ) (b : ℕ) (u : ℚ) (hu : (b:ℚ) ≤ u) :
    expect (tailLaw ν b) (fun k => max 0 ((k:ℚ)-u))=expect ν (fun k => max 0 ((k:ℚ)-u)) := by
  rw [expect_tailLaw]
  apply expect_congr
  intro k
  split_ifs with h
  · rfl
  · have hk : k ≤ b := Nat.le_of_not_gt h
    have hkQ : (k:ℚ) ≤ b := by exact_mod_cast hk
    rw [max_eq_left (by linarith)]

lemma upperLaw_hinge_above (ν : ℕ →₀ ℚ) (b : ℕ) (m u : ℚ) (hu : (b:ℚ) ≤ u) :
    expect (upperLaw ν b m) (fun k => max 0 ((k:ℚ)-u))=expect ν (fun k => max 0 ((k:ℚ)-u)) := by
  rw [expect_upperLaw,tailLaw_hinge_above ν b u hu,max_eq_left (sub_nonpos.mpr hu),mul_zero,add_zero]

lemma upperLaw_hinge_below (ν : ℕ →₀ ℚ) (b : ℕ) (m u : ℚ) (hu : u ≤ (b:ℚ)) :
    expect (upperLaw ν b m) (fun k => max 0 ((k:ℚ)-u))=
      expect ν (fun k => max 0 ((k:ℚ)-b))+((b:ℚ)-u)*m := by
  have hp (k : ℕ) : (if b < k then max 0 ((k:ℚ)-u) else 0)=
      (if b < k then max 0 ((k:ℚ)-b) else 0)+((b:ℚ)-u)*(if b < k then 1 else 0) := by
    split_ifs with hk
    · have hkQ : (b:ℚ) < k := by exact_mod_cast hk
      rw [max_eq_right (by linarith),max_eq_right (by linarith)]
      ring
    · ring
  have hh := expect_congr ν _ _ hp
  rw [expect_add,expect_mul,← expect_tailLaw,← expect_tailLaw,← expect_tailLaw] at hh
  rw [expect_upperLaw,hh,tailLaw_hinge_above ν b b le_rfl,max_eq_right (sub_nonneg.mpr hu)]
  change expect ν (fun k => max 0 ((k:ℚ)-b)) + ((b:ℚ)-u)*tailMass ν b +
    (m-tailMass ν b)*((b:ℚ)-u) = _
  ring

/-- A measure of prescribed mass dominated in every stop-loss test is still
dominated after pruning the comparison law below any chosen cutoff and placing
the remaining mass at that cutoff. If `m>=tailMass`, this new law is positive. -/
theorem upperLaw_dominates {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℚ) (hμ : ∀ x,0 ≤ μ x) (f : Ω → ℚ) (m : ℚ) (hm : (∑ x,μ x)=m)
    (ν : ℕ →₀ ℚ) (hH : ∀ u : ℚ, (∑ x,μ x*max 0 (f x-u)) ≤ expect ν (fun k => max 0 ((k:ℚ)-u)))
    (b : ℕ) (u : ℚ) :
    (∑ x,μ x*max 0 (f x-u)) ≤ expect (upperLaw ν b m) (fun k => max 0 ((k:ℚ)-u)) := by
  by_cases hu : (b:ℚ) ≤ u
  · rw [upperLaw_hinge_above ν b m u hu]
    exact hH u
  · have hub : u ≤ (b:ℚ) := (lt_of_not_ge hu).le
    rw [upperLaw_hinge_below ν b m u hub]
    have hh := stopLoss_mass_bound μ hμ f u b hub
    rw [hm] at hh
    exact hh.trans (add_le_add_left (hH b) _)

#print axioms upperLaw_dominates
end Erdos7KilledSieve



/-! Convex-test preservation under positive upper-tail pruning. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
open Erdos7BinarySieve (expect expect_congr expect_sub expect_const)
set_option maxHeartbeats 4000000

/-- A positive-part transform of a convex test is still convex. -/
lemma positivePart_convex (φ : ℚ → ℚ) (hφ : ConvexOn ℚ Set.univ φ) (a : ℚ) :
    ConvexOn ℚ Set.univ (fun x => max 0 (φ x-a)) := by
  have hh := hφ.add (convexOn_const (-a) convex_univ)
  simpa only [sub_eq_add_neg] using (convexOn_const 0 convex_univ).sup hh

/-- The upper-tail law has a positive-part formula for every monotone test.
No positivity assumption on the raw law is needed for this identity. -/
lemma upperLaw_convex_formula (ν : ℕ →₀ ℚ) (b : ℕ) (m M : ℚ) (hM : 0 ≤ M)
    (φ : ℚ → ℚ) (hmono : Monotone φ) :
    expect (upperLaw ν b m) (fun k => φ (M*k)) =
      expect ν (fun k => max 0 (φ (M*k)-φ (M*b)))+m*φ (M*b) := by
  have hh : expect (tailLaw ν b) (fun k => φ (M*k)-φ (M*b)) =
      expect ν (fun k => max 0 (φ (M*k)-φ (M*b))) := by
    rw [expect_tailLaw]
    apply expect_congr
    intro k
    by_cases hbk : b < k
    · rw [if_pos hbk,max_eq_right]
      apply sub_nonneg.mpr
      apply hmono
      apply mul_le_mul_of_nonneg_left _ hM
      exact_mod_cast hbk.le
    · rw [if_neg hbk,max_eq_left]
      apply sub_nonpos.mpr
      apply hmono
      apply mul_le_mul_of_nonneg_left _ hM
      exact_mod_cast Nat.le_of_not_gt hbk
  rw [expect_sub,expect_const] at hh
  rw [expect_upperLaw]
  change expect (tailLaw ν b) (fun k => φ (M*k))+(m-tailMass ν b)*φ (M*b)=_
  change expect (tailLaw ν b) (fun k => φ (M*k))-φ (M*b)*tailMass ν b=_ at hh
  rw [← hh]
  ring

/-- Nonnegative convex-test domination, together with exact actual mass,
implies full convex-test domination by the pruned law. -/
theorem upperLaw_convex_dominates {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℚ) (hμ : ∀ x,0 ≤ μ x) (f : Ω → ℚ) (m M : ℚ) (hM : 0 ≤ M)
    (hm : (∑ x,μ x)=m) (ν : ℕ →₀ ℚ)
    (hraw : ∀ ψ : ℚ → ℚ, ConvexOn ℚ Set.univ ψ → Monotone ψ → (∀ z,0 ≤ ψ z) →
      (∑ x,μ x*ψ (f x)) ≤ expect ν (fun k => ψ (M*k)))
    (b : ℕ) (φ : ℚ → ℚ) (hφ : ConvexOn ℚ Set.univ φ) (hmono : Monotone φ) :
    (∑ x,μ x*φ (f x)) ≤ expect (upperLaw ν b m) (fun k => φ (M*k)) := by
  let ψ (z : ℚ) := max 0 (φ z-φ (M*b))
  have hψ : ConvexOn ℚ Set.univ ψ := positivePart_convex φ hφ _
  have hψmono : Monotone ψ := by
    intro x y hxy
    exact max_le_max le_rfl (sub_le_sub_right (hmono hxy) _)
  have hh := hraw ψ hψ hψmono (fun z => le_max_left _ _)
  have hp (x : Ω) : φ (f x) ≤ ψ (f x)+φ (M*b) := by
    have hh := le_max_right 0 (φ (f x)-φ (M*b))
    dsimp only [ψ]
    linarith
  calc
    _ ≤ ∑ x,μ x*(ψ (f x)+φ (M*b)) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hp x) (hμ x))
    _ = (∑ x,μ x*ψ (f x))+m*φ (M*b) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib,← Finset.sum_mul,hm]
    _ ≤ expect ν (fun k => ψ (M*k))+m*φ (M*b) := add_le_add_left hh _
    _ = _ := (upperLaw_convex_formula ν b m M hM φ hmono).symm

/-- Positive-law version of one complete-pattern killed-coordinate step. -/
theorem completeConvexBound_topTrim {n : ℕ} (κ : Type*)
    (A : Fin n → Type*) [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]
    (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ) (t : ℕ) (ht : t < n)
    (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x) (ν : ℕ →₀ ℚ)
    (hcomp : CompleteConvexBound κ A E c q t μ ν)
    (B : Finset (∀ i,A i)) (hc : 1 ≤ c ⟨t,ht⟩) (hq1 : q ⟨t,ht⟩ 0 ≤ 1)
    (hqdec : ∀ g,g < E ⟨t,ht⟩ → q ⟨t,ht⟩ (g+1) ≤ q ⟨t,ht⟩ g)
    (hqE : q ⟨t,ht⟩ (E ⟨t,ht⟩)=0) (L : ℚ) (hLm : L ≤ ∑ x,μ x)
    (hL : (∑ x,μ x*residual (c ⟨t,ht⟩) (coordinateFraction A ⟨t,ht⟩ B x)) ≤ L)
    (b : ℕ) :
    CompleteConvexBound κ A E c q (t+1) (killedResample A ⟨t,ht⟩ μ B (c ⟨t,ht⟩) L)
      (upperLaw (Erdos7ExponentLaw.step (E ⟨t,ht⟩) (q ⟨t,ht⟩) ν) b ((∑ x,μ x)-L)) := by
  intro M K e X he hX hM φ hφ hmono
  apply upperLaw_convex_dominates _
    (killedResample_nonneg A ⟨t,ht⟩ μ hμ B (c ⟨t,ht⟩) L hc hLm) _ _ M (Nat.cast_nonneg _)
    (killedResample_total A ⟨t,ht⟩ μ B (c ⟨t,ht⟩) L hc hLm hL) _ _ b φ hφ hmono
  intro ψ hψ hψmono hψ0
  have hkill := killedResample_test A ⟨t,ht⟩ μ hμ B (c ⟨t,ht⟩) L hc hLm hL
    (fun x => ψ (∑ k∈K,boxIndicator A (expSupport (e k)) (X k) x)) 0 (fun x => hψ0 _)
  rw [mul_zero,sub_zero] at hkill
  exact hkill.trans (completeConvexBound_resample κ A E c q t ht μ hμ ν hcomp B hc hq1 hqdec hqE
    M K e X he hX hM ψ hψ hψmono)

#print axioms completeConvexBound_topTrim
end Erdos7KilledSieve



/-! Positive comparison-law towers with exact-mass upper-tail pruning. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
open Erdos7BinarySieve (expect)
set_option maxHeartbeats 4000000

noncomputable def prunedStep (E : ℕ) (q : ℕ → ℚ) (ν : ℕ →₀ ℚ) (L : ℚ) (b : ℕ) : ℕ →₀ ℚ :=
  upperLaw (Erdos7ExponentLaw.step E q ν) b (expect ν (fun _ => 1)-L)

lemma prunedStep_mass (E : ℕ) (q : ℕ → ℚ) (ν : ℕ →₀ ℚ) (L : ℚ) (b : ℕ) :
    expect (prunedStep E q ν L b) (fun _ => 1)=expect ν (fun _ => 1)-L := upperLaw_mass _ _ _

noncomputable def prunedTower {n : ℕ} (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ)
    (loss : Fin n → (ℕ →₀ ℚ) → ℚ) (cut : Fin n → (ℕ →₀ ℚ) → ℕ) : ℕ → (ℕ →₀ ℚ)
  | 0 => Erdos7ExponentLaw.initial
  | t+1 => if h : t < n then
      prunedStep (E ⟨t,h⟩) (q ⟨t,h⟩) (prunedTower E q loss cut t)
        (loss ⟨t,h⟩ (prunedTower E q loss cut t)) (cut ⟨t,h⟩ (prunedTower E q loss cut t))
    else prunedTower E q loss cut t

section Tower
variable {n : ℕ} {κ : Type*} (A : Fin n → Type*)
variable [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]

noncomputable def prunedWeights (B : Fin n → Finset (∀ i,A i)) (c : Fin n → ℚ)
    (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ) (loss : Fin n → (ℕ →₀ ℚ) → ℚ)
    (cut : Fin n → (ℕ →₀ ℚ) → ℕ) : ℕ → (∀ i,A i) → ℚ
  | 0 => towerWeights A B c 0
  | t+1 => if h : t < n then
      killedResample A ⟨t,h⟩ (prunedWeights B c E q loss cut t) (B ⟨t,h⟩) (c ⟨t,h⟩)
        (loss ⟨t,h⟩ (prunedTower E q loss cut t))
    else prunedWeights B c E q loss cut t

/-- Both the actual weights and the comparison law stay nonnegative. -/
theorem prunedTower_invariants (B : Fin n → Finset (∀ i,A i)) (c : Fin n → ℚ)
    (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ) (loss : Fin n → (ℕ →₀ ℚ) → ℚ)
    (cut : Fin n → (ℕ →₀ ℚ) → ℕ)
    (hc : ∀ i,1 ≤ c i) (hq1 : ∀ i,q i 0 ≤ 1)
    (hqdec : ∀ i g,g < E i → q i (g+1) ≤ q i g) (hqE : ∀ i,q i (E i)=0)
    (hB : ∀ i j : Fin n,j < i → ∀ x v,Function.update x i v∈B j ↔ x∈B j)
    (horacle : ∀ (i : Fin n) (μ : (∀ j,A j) → ℚ) (ν : ℕ →₀ ℚ),
      (∀ x,0 ≤ μ x) → CompleteConvexBound κ A E c q i.val μ ν →
      (∑ x,μ x*residual (c i) (coordinateFraction A i (B i) x)) ≤ loss i ν)
    (hcut : ∀ i : Fin n,
      let ν := prunedTower E q loss cut i.val
      tailMass (Erdos7ExponentLaw.step (E i) (q i) ν) (cut i ν) ≤ expect ν (fun _ => 1)-loss i ν)
    (t : ℕ) (ht : t ≤ n) :
    (∀ x,0 ≤ prunedWeights A B c E q loss cut t x) ∧
    (∀ k,0 ≤ prunedTower E q loss cut t k) ∧
    (∑ x,prunedWeights A B c E q loss cut t x)=expect (prunedTower E q loss cut t) (fun _ => 1) ∧
    CompleteConvexBound κ A E c q t (prunedWeights A B c E q loss cut t) (prunedTower E q loss cut t) ∧
    (∀ j : Fin n,j.val < t → ∀ x∈B j,prunedWeights A B c E q loss cut t x=0) := by
  induction t with
  | zero =>
    refine ⟨towerWeights_nonneg A B c hc 0,?_,?_,?_,?_⟩
    · intro k
      simp only [prunedTower,Erdos7ExponentLaw.initial,Finsupp.single_apply]
      split_ifs <;> norm_num
    · simp only [prunedWeights,prunedTower,Erdos7ExponentLaw.expect_initial,towerWeights_total A B c hc]
    · exact completeConvexBound_initial κ A E c q _ (towerWeights_total A B c hc 0)
    · intro j hj; omega
  | succ t ih =>
    have ht' : t ≤ n := by omega
    obtain ⟨hμ,hν,hμtot,hcomp,hzero⟩ := ih ht'
    have htn : t < n := by omega
    let i : Fin n := ⟨t,htn⟩
    let μ := prunedWeights A B c E q loss cut t
    let ν := prunedTower E q loss cut t
    let L := loss i ν
    let b := cut i ν
    have hνsucc : prunedTower E q loss cut (t+1)=prunedStep (E i) (q i) ν L b := by
      simp only [prunedTower,dif_pos htn,ν,L,b,i]
    have hμsucc : prunedWeights A B c E q loss cut (t+1)=killedResample A i μ (B i) (c i) L := by
      simp only [prunedWeights,dif_pos htn,μ,ν,L,i]
    have hraw : ∀ k,0 ≤ Erdos7ExponentLaw.step (E i) (q i) ν k :=
      Erdos7ExponentLaw.step_nonneg (E i) (q i) (hq1 i) (hqdec i) ν hν
    have htail : 0 ≤ tailMass (Erdos7ExponentLaw.step (E i) (q i) ν) b := by
      apply Erdos7BinarySieve.expect_nonneg
      · intro k
        simp only [tailLaw,Finsupp.filter_apply]
        split_ifs <;> [exact hraw k; exact le_rfl]
      · intro k; norm_num
    have hLm : L ≤ ∑ x,μ x := by
      have hh := htail.trans (hcut i)
      rw [hμtot]
      exact sub_nonneg.mp hh
    have hL := horacle i μ ν hμ hcomp
    rw [hμsucc,hνsucc]
    refine ⟨killedResample_nonneg A i μ hμ (B i) (c i) L (hc i) hLm,
      upperLaw_nonneg _ hraw b _ (hcut i),?_,?_,?_⟩
    · rw [killedResample_total A i μ (B i) (c i) L (hc i) hLm hL,prunedStep_mass]
      exact congrArg (fun z => z-L) hμtot
    · have hh := completeConvexBound_topTrim κ A E c q t htn μ hμ ν hcomp (B i) (hc i)
        (hq1 i) (hqdec i) (hqE i) L hLm hL b
      dsimp only [prunedStep]
      rwa [hμtot] at hh
    · intro j hj x hx
      by_cases hji : j=i
      · subst j
        exact killedResample_zero A i μ (B i) (c i) L x hx
      · have hjt : j.val < t := by
          have hjne : j.val≠t := by intro heq; exact hji (Fin.ext heq)
          omega
        exact killedResample_preserves_zero A i μ (B i) (B j) (c i) L
          (hB i j hjt) (hzero j hjt) x hx

/-- A positive final pruned-law mass certifies avoidance of all layered bad sets. -/
theorem pruned_tower_avoids (B : Fin n → Finset (∀ i,A i)) (c : Fin n → ℚ)
    (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ) (loss : Fin n → (ℕ →₀ ℚ) → ℚ)
    (cut : Fin n → (ℕ →₀ ℚ) → ℕ)
    (hc : ∀ i,1 ≤ c i) (hq1 : ∀ i,q i 0 ≤ 1)
    (hqdec : ∀ i g,g < E i → q i (g+1) ≤ q i g) (hqE : ∀ i,q i (E i)=0)
    (hB : ∀ i j : Fin n,j < i → ∀ x v,Function.update x i v∈B j ↔ x∈B j)
    (horacle : ∀ (i : Fin n) (μ : (∀ j,A j) → ℚ) (ν : ℕ →₀ ℚ),
      (∀ x,0 ≤ μ x) → CompleteConvexBound κ A E c q i.val μ ν →
      (∑ x,μ x*residual (c i) (coordinateFraction A i (B i) x)) ≤ loss i ν)
    (hcut : ∀ i : Fin n,
      let ν := prunedTower E q loss cut i.val
      tailMass (Erdos7ExponentLaw.step (E i) (q i) ν) (cut i ν) ≤ expect ν (fun _ => 1)-loss i ν)
    (hpos : 0 < expect (prunedTower E q loss cut n) (fun _ => 1)) :
    ∃ x : ∀ i,A i,∀ i,x∉B i := by
  obtain ⟨hμ,hν,hμtot,hcomp,hzero⟩ := prunedTower_invariants A B c E q loss cut hc hq1 hqdec hqE hB horacle hcut n le_rfl
  have hp : 0 < ∑ x,prunedWeights A B c E q loss cut n x := by rwa [hμtot]
  have hex : ∃ x,0 < prunedWeights A B c E q loss cut n x := by
    by_contra hh
    push_neg at hh
    exact (not_le_of_gt hp) (Finset.sum_nonpos (fun x _ => hh x))
  obtain ⟨x,hpx⟩ := hex
  refine ⟨x,fun i hi => ?_⟩
  have hz := hzero i i.isLt x hi
  rw [hz] at hpx
  exact lt_irrefl _ hpx

end Tower
#print axioms pruned_tower_avoids
end Erdos7KilledSieve



/-! The signed killed-law criterion for complete nonzero exponent rectangles. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
open Erdos7BinarySieve (expect)
set_option maxHeartbeats 4000000

/-- A positive pruned-law residual budget rules out a covering by a complete
nonzero exponent rectangle. All finite exponents and arbitrary residues are
permitted. The cutoff condition ensures that both the actual measure and the comparison
law retain nonnegative mass throughout. -/
theorem complete_box_pruned_avoidance {n : ℕ} {κ : Type*} [Fintype κ]
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (E : Fin n → ℕ) (hE : ∀ i, 0 < E i) (c s : Fin n → ℚ) (r q : Fin n → ℕ → ℚ)
    (hc : ∀ i, 1 ≤ c i) (hs : ∀ i, 0 < s i)
    (hr : ∀ i g, g < E i → 0 ≤ r i (g+1))
    (hrs : ∀ i, (∑ g∈Finset.range (E i),r i (g+1)) ≤ s i)
    (hq1 : ∀ i, q i 0 ≤ 1) (hqdec : ∀ i g, g < E i → q i (g+1) ≤ q i g)
    (hqE : ∀ i, q i (E i)=0) (hqr : ∀ i g, g < E i → c i*r i (g+1) ≤ q i g)
    (e : κ → Fin n → ℕ) (heinj : Function.Injective e)
    (he : ∀ k i, e k i ≤ E i) (hne : ∀ k, (expSupport (e k)).Nonempty)
    (hfull : ∀ f : Fin n → ℕ, (∀ i, f i ≤ E i) → (∃ i, f i≠0) → ∃ k, e k=f)
    (X : κ → ∀ i, Finset (A i))
    (hX : ∀ k i, e k i≠0 → fraction (X k i) ≤ r i (e k i))
    (cut : Fin n → (ℕ →₀ ℚ) → ℕ)
    (hcut : ∀ i : Fin n,
      let ν := prunedTower E q (fun i ν => expect ν (fun k => residual (c i) (s i*k))) cut i.val
      tailMass (Erdos7ExponentLaw.step (E i) (q i) ν) (cut i ν) ≤
        expect ν (fun _ => 1)-expect ν (fun k => residual (c i) (s i*k)))
    (hpos : 0 < expect (prunedTower E q
      (fun i ν => expect ν (fun k => residual (c i) (s i*k))) cut n) (fun _ => 1)) :
    ∃ x : ∀ i, A i, ∀ k, ¬ (∀ i∈expSupport (e k), x i∈X k i) := by
  classical
  let S (k : κ) := expSupport (e k)
  let σ (k : κ) := (S k).max' (hne k)
  have hσ (k : κ) : σ k∈S k := Finset.max'_mem _ _
  have hS (k : κ) (j : Fin n) (hj : j∈S k) : j ≤ σ k := Finset.le_max' _ _ hj
  let B := layeredBad A S X σ
  have hB : ∀ i j : Fin n, j < i → ∀ x v, Function.update x i v∈B j ↔ x∈B j := by
    intro i j hji x v
    exact layeredBad_invariant A S X σ hS i j hji x v
  have hc0 : ∀ i, 0 ≤ c i := fun i => (by norm_num : (0:ℚ) ≤ 1).trans (hc i)
  have horacle (i : Fin n) (μ : (∀ j, A j) → ℚ) (ν : ℕ →₀ ℚ)
      (hμ : ∀ x, 0 ≤ μ x) (hcomp : CompleteConvexBound κ A E c q i.val μ ν) :
      (∑ x, μ x*residual (c i) (coordinateFraction A i (B i) x)) ≤
        expect ν (fun k => residual (c i) (s i*k)) := by
    let K := layerFamily σ i
    let Kg (g : ℕ) := K.filter (fun k => e k i=g+1)
    let e' (k : κ) := Function.update (e k) i 0
    let W (k : κ) (x : ∀ j, A j) := boxIndicator A (expSupport (e' k)) (X k) x
    let N (g : ℕ) (x : ∀ j, A j) := ∑ k∈Kg g, W k x
    have hki (k : κ) (hk : k∈K) : i∈S k := by
      simpa only [(Finset.mem_filter.mp hk).2] using hσ k
    have he' (k : κ) (hk : k∈K) : PrefixPattern E i.val (e' k) := by
      constructor
      · intro j
        by_cases hj : j=i
        · subst j; simp [e']
        · simpa only [e',Function.update_of_ne hj] using he k j
      · intro j hj
        by_cases hji : j=i
        · subst j; simp [e']
        · have hz : e k j=0 := by
            by_contra h
            have hle := hS k j ((mem_expSupport _ _).mpr h)
            rw [(Finset.mem_filter.mp hk).2] at hle
            have hlt : i < j := lt_of_le_of_ne hj (Ne.symm hji)
            exact (not_le_of_gt hlt) hle
          simpa only [e',Function.update_of_ne hji] using hz
    have hX' (k : κ) (j : Fin n) (hj : j∈expSupport (e' k)) :
        c j*fraction (X k j) ≤ q j (e' k j-1) := by
      rw [expSupport_update_zero] at hj
      have hjne := (Finset.mem_erase.mp hj).1
      have hpos := (mem_expSupport _ _).mp (Finset.mem_erase.mp hj).2
      have hEj : e k j-1 < E j := by have := he k j; omega
      have hq := hqr j (e k j-1) hEj
      have heq : e k j-1+1=e k j := by omega
      rw [heq] at hq
      simpa only [e',Function.update_of_ne hjne] using
        (mul_le_mul_of_nonneg_left (hX k j hpos) (hc0 j)).trans hq
    have hmult (g : ℕ) (hg : g < E i) : CompletePatterns E i.val (Kg g) e' 1 := by
      intro f hf
      let v := Function.update f i (g+1)
      have hvE (j : Fin n) : v j ≤ E j := by
        by_cases hj : j=i
        · subst j; simpa only [v,Function.update_self] using (show g+1 ≤ E i by omega)
        · simpa only [v,Function.update_of_ne hj] using hf.1 j
      obtain ⟨k,hkv⟩ := hfull v hvE ⟨i,by simp [v]⟩
      have hki' : e k i=g+1 := by simp only [hkv,v,Function.update_self]
      have hσi : σ k=i := by
        apply le_antisymm
        · apply Finset.max'_le
          intro j hj
          by_contra h
          have hij : i < j := lt_of_not_ge h
          have hji : j≠i := ne_of_gt hij
          have hz := hf.2 j hij.le
          have hh := (mem_expSupport _ _).mp hj
          simp only [hkv,v,Function.update_of_ne hji,hz] at hh
          exact hh rfl
        · exact hS k i ((mem_expSupport _ _).mpr (by omega))
      have hkKg : k∈Kg g := by simp [Kg,K,layerFamily,hσi,hki']
      have hkf : e' k=f := by
        funext j
        by_cases hj : j=i
        · subst j
          simp only [e',Function.update_self,hf.2 i le_rfl]
        · simp only [e',Function.update_of_ne hj,hkv,v]
      have hle : ((Kg g).filter (fun k => e' k=f)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro u hu w hw
        obtain ⟨hu,huf⟩ := Finset.mem_filter.mp hu
        obtain ⟨hw,hwf⟩ := Finset.mem_filter.mp hw
        have hug := (Finset.mem_filter.mp hu).2
        have hwg := (Finset.mem_filter.mp hw).2
        apply heinj
        funext j
        by_cases hj : j=i
        · subst j; exact hug.trans hwg.symm
        · have hh := congrFun (huf.trans hwf.symm) j
          simpa only [e',Function.update_of_ne hj] using hh
      exact le_antisymm hle (Finset.card_pos.mpr ⟨k,Finset.mem_filter.mpr ⟨hkKg,hkf⟩⟩)
    have hpoint (x : ∀ j, A j) : coordinateFraction A i (B i) x ≤
        ∑ g∈Finset.range (E i), r i (g+1)*N g x := by
      have hzero : K.filter (fun k => e k i=0)=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro k hk
        obtain ⟨hk,hz⟩ := Finset.mem_filter.mp hk
        exact (mem_expSupport _ _).mp (hki k hk) hz
      have hfullK : K.filter (fun k => e k i ≤ E i)=K := Finset.filter_true_of_mem (fun k _ => he k i)
      have hsum := sum_filter_nat_le K (fun k => e k i) (E i) (fun k => r i (e k i)*W k x)
      rw [hzero,hfullK,Finset.sum_empty,zero_add] at hsum
      calc
        _ ≤ ∑ k∈K, fraction (X k i)*boxIndicator A ((S k).erase i) (X k) x :=
          layered_fraction_bound A S X σ hσ i x
        _ ≤ ∑ k∈K, r i (e k i)*W k x := by
          apply Finset.sum_le_sum
          intro k hk
          have hi := (mem_expSupport _ _).mp (hki k hk)
          simpa only [W,e',expSupport_update_zero,S] using
            mul_le_mul_of_nonneg_right (hX k i hi) (boxIndicator_nonneg A ((S k).erase i) (X k) x)
        _ = ∑ g∈Finset.range (E i), r i (g+1)*N g x := by
          rw [hsum]
          apply Finset.sum_congr rfl
          intro g hg
          rw [show r i (g+1)*N g x=∑ k∈Kg g, r i (g+1)*W k x from Finset.mul_sum _ _ _]
          apply Finset.sum_congr rfl
          intro k hk
          rw [(Finset.mem_filter.mp hk).2]
    exact complete_layer_loss_bound A E c q i.val μ hμ ν hcomp (c i) (s i) (hc i) (hs i)
      (E i) (hE i) (fun g => r i (g+1)) (hr i) (hrs i) Kg (fun _ => e') (fun _ => X)
      (fun g hg k hk => he' k (Finset.mem_filter.mp hk).1)
      (fun g hg k hk => hX' k) hmult (coordinateFraction A i (B i)) hpoint
  obtain ⟨x,hx⟩ := pruned_tower_avoids A B c E q
    (fun i ν => expect ν (fun k => residual (c i) (s i*k))) cut hc hq1 hqdec hqE hB horacle hcut hpos
  refine ⟨x,fun k hk => hx (σ k) ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,k,by simp [layerFamily],hk⟩

#print axioms complete_box_pruned_avoidance
end Erdos7KilledSieve



/-! Complete a distinct box family by inserting missing exponent patterns. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
open Erdos7BinarySieve (expect)
set_option maxHeartbeats 4000000

/-- The complete-rectangle criterion applies to arbitrary distinct nonzero
exponent families: missing patterns can be filled by empty boxes. -/
theorem distinct_box_pruned_avoidance {n : ℕ} {κ : Type*} [Fintype κ]
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (E : Fin n → ℕ) (hE : ∀ i, 0 < E i) (c s : Fin n → ℚ) (r q : Fin n → ℕ → ℚ)
    (hc : ∀ i, 1 ≤ c i) (hs : ∀ i, 0 < s i)
    (hr : ∀ i g, g < E i → 0 ≤ r i (g+1))
    (hrs : ∀ i, (∑ g∈Finset.range (E i),r i (g+1)) ≤ s i)
    (hq1 : ∀ i, q i 0 ≤ 1) (hqdec : ∀ i g, g < E i → q i (g+1) ≤ q i g)
    (hqE : ∀ i, q i (E i)=0) (hqr : ∀ i g, g < E i → c i*r i (g+1) ≤ q i g)
    (e : κ → Fin n → ℕ) (heinj : Function.Injective e)
    (he : ∀ k i, e k i ≤ E i) (hne : ∀ k, (expSupport (e k)).Nonempty)
    (X : κ → ∀ i, Finset (A i))
    (hX : ∀ k i, e k i≠0 → fraction (X k i) ≤ r i (e k i))
    (cut : Fin n → (ℕ →₀ ℚ) → ℕ)
    (hcut : ∀ i : Fin n,
      let ν := prunedTower E q (fun i ν => expect ν (fun k => residual (c i) (s i*k))) cut i.val
      tailMass (Erdos7ExponentLaw.step (E i) (q i) ν) (cut i ν) ≤
        expect ν (fun _ => 1)-expect ν (fun k => residual (c i) (s i*k)))
    (hpos : 0 < expect (prunedTower E q
      (fun i ν => expect ν (fun k => residual (c i) (s i*k))) cut n) (fun _ => 1)) :
    ∃ x : ∀ i, A i, ∀ k, ¬ (∀ i∈expSupport (e k), x i∈X k i) := by
  classical
  let V := ∀ i : Fin n, Fin (E i+1)
  let ρ := {v : V // ∃ i, (v i:ℕ)≠0}
  let e' (k : ρ) (i : Fin n) : ℕ := k.val i
  have he' (k : ρ) (i : Fin n) : e' k i ≤ E i := Nat.le_of_lt_succ (k.val i).isLt
  have hne' (k : ρ) : (expSupport (e' k)).Nonempty := by
    obtain ⟨i,hi⟩ := k.property
    exact ⟨i,(mem_expSupport _ _).mpr hi⟩
  have hinj' : Function.Injective e' := by
    intro k l hkl
    apply Subtype.ext
    funext i
    exact Fin.ext (congrFun hkl i)
  have hfull' (f : Fin n → ℕ) (hf : ∀ i, f i ≤ E i) (hfn : ∃ i, f i≠0) : ∃ k : ρ, e' k=f := by
    exact ⟨⟨fun i => ⟨f i,by have := hf i; omega⟩,hfn⟩,rfl⟩
  let X' (k : ρ) (i : Fin n) : Finset (A i) :=
    if h : ∃ l, e l=e' k then X h.choose i else ∅
  have hX' (k : ρ) (i : Fin n) (hi : e' k i≠0) : fraction (X' k i) ≤ r i (e' k i) := by
    dsimp only [X']
    split_ifs with h
    · have heq := congrFun h.choose_spec i
      simpa only [heq] using hX h.choose i (by simpa only [heq] using hi)
    · have hg : e' k i-1 < E i := by have := he' k i; omega
      have hh := hr i (e' k i-1) hg
      have heq : e' k i-1+1=e' k i := by omega
      simpa only [fraction,Finset.card_empty,Nat.cast_zero,zero_div,heq] using hh
  obtain ⟨x,hx⟩ := complete_box_pruned_avoidance A E hE c s r q hc hs hr hrs hq1 hqdec hqE hqr
    e' hinj' he' hne' hfull' X' hX' cut hcut hpos
  refine ⟨x,fun k hk => ?_⟩
  obtain ⟨l,hl⟩ := hfull' (e k) (he k) (by
    obtain ⟨i,hi⟩ := hne k
    exact ⟨i,(mem_expSupport _ _).mp hi⟩)
  have hex : ∃ j, e j=e' l := ⟨k,hl.symm⟩
  have hchoice : hex.choose=k := heinj (hex.choose_spec.trans hl)
  apply hx l
  intro i hi
  have hi' : i∈expSupport (e k) := by simpa only [hl] using hi
  have hXi : X' l i=X k i := by simp only [X',dif_pos hex,hchoice]
  rw [hXi]
  exact hk i hi'

#print axioms distinct_box_pruned_avoidance
end Erdos7KilledSieve



/-! Arithmetic specialization of the signed complete-pattern killed sieve. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve Erdos7StarSieve
open Erdos7BinarySieve (expect)
set_option maxHeartbeats 4000000

/-- Positive final pruned-law mass, with admissible cutoffs throughout, precludes
an arithmetic cover by distinct finite exponent patterns. -/
theorem arithmetic_pruned_not_cover {n : ℕ} {κ : Type*} [Fintype κ]
    (p E : Fin n → ℕ) (hp : ∀ i, 1 < p i) (hE : ∀ i, 0 < E i)
    (hcop : Pairwise (Function.onFun Nat.Coprime p))
    (e : κ → Fin n → ℕ) (he : Function.Injective e) (he0 : ∀ k, ∃ i, e k i≠0)
    (heE : ∀ k i, e k i≤E i) (a : κ → ℤ)
    (c s : Fin n → ℚ) (hc : ∀ i, 1≤c i) (hcp : ∀ i, c i≤p i)
    (hs : ∀ i, 0<s i)
    (hsum : ∀ i, (∑ g∈Finset.range (E i), ((p i:ℚ)⁻¹)^(g+1))≤s i)
    (cut : Fin n → (ℕ →₀ ℚ) → ℕ)
    (hcut : ∀ i : Fin n,
      let q := fun i => powerTail (p i) (c i) (E i)
      let ν := prunedTower E q (fun i ν => expect ν (fun k => residual (c i) (s i*k))) cut i.val
      tailMass (Erdos7ExponentLaw.step (E i) (q i) ν) (cut i ν) ≤
        expect ν (fun _ => 1)-expect ν (fun k => residual (c i) (s i*k)))
    (hpos : 0 < expect (prunedTower E (fun i => powerTail (p i) (c i) (E i))
      (fun i ν => expect ν (fun k => residual (c i) (s i*k))) cut n) (fun _ => 1)) :
    ¬ (∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k) := by
  intro hcover
  classical
  letI (i : Fin n) : NeZero (p i) := ⟨by have := hp i; omega⟩
  let A (i : Fin n) := ZMod (p i ^ E i)
  let f (k : κ) (i : Fin n) := ZMod.castHom (pow_dvd_pow (p i) (heE k i)) (ZMod (p i ^ e k i))
  let B (k : κ) (i : Fin n) := Finset.univ.filter (fun x : A i => f k i x = (a k : ZMod (p i ^ e k i)))
  have hBcard (k : κ) (i : Fin n) : ((B k i).card : ℚ) ≤
      (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(e k i) := by
    have hh := surjective_fiber_card_rat (f k i).toAddMonoidHom
      (ZMod.castHom_surjective (pow_dvd_pow (p i) (heE k i))) (a k)
    change ((B k i).card : ℚ) = _ at hh
    rw [hh]
    simp only [A, ZMod.card, Nat.cast_pow, div_eq_mul_inv, inv_pow]
    exact le_rfl
  have hbox : ∀ x : ∀ i, A i, ∃ k, ∀ i, x i ∈ B k i := by
    intro x
    let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) (fun i => p i ^ E i) Finset.univ
      (fun i _ => pow_ne_zero _ (NeZero.ne _))
      (fun i _ j _ hij => (hcop hij).pow _ _)
    have hz (i : Fin n) : (z.val : A i) = x i := by
      rw [← ZMod.natCast_zmod_val (x i)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
    obtain ⟨k, hk⟩ := hcover (z.val : ℤ)
    refine ⟨k, ?_⟩
    intro i
    have hpi : p i ^ e k i ∣ ∏ j, p j ^ e k j :=
      Finset.dvd_prod_of_mem (fun j => p j ^ e k j) (Finset.mem_univ i)
    have hpi' : ((p i ^ e k i : ℕ) : ℤ) ∣ ((∏ j, p j ^ e k j : ℕ) : ℤ) := by exact_mod_cast hpi
    have hqi := hpi'.trans hk
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hz i, map_natCast]
    symm
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (a k) (z.val : ℤ) (p i ^ e k i)).mpr hqi
  have hc0 : ∀ i, 0≤c i := fun i => (by norm_num : (0:ℚ)≤1).trans (hc i)
  have hfrac (k : κ) (i : Fin n) : fraction (B k i)≤((p i:ℚ)⁻¹)^(e k i) := by
    apply (div_le_iff₀ card_pos_rat).mpr
    simpa only [mul_comm] using hBcard k i
  obtain ⟨x,hx⟩ := distinct_box_pruned_avoidance A E hE c s (fun i g => ((p i:ℚ)⁻¹)^g)
    (fun i => powerTail (p i) (c i) (E i)) hc hs (fun _ _ _ => by positivity) hsum
    (fun i => powerTail_zero_le_one (p i) (hp i) (c i) (hcp i) (E i))
    (fun i g _ => powerTail_decreasing (p i) (hp i) (c i) (hc0 i) (E i) g)
    (fun i => powerTail_terminal (p i) (c i) (E i))
    (fun i g hg => by simp only [powerTail,if_pos hg,le_refl]) e he heE (by
      intro k
      obtain ⟨i,hi⟩ := he0 k
      exact ⟨i,(mem_expSupport _ _).mpr hi⟩) B (fun k i _ => hfrac k i) cut hcut hpos
  obtain ⟨k,hk⟩ := hbox x
  exact hx k (fun i _ => hk i)

#print axioms arithmetic_pruned_not_cover
end Erdos7KilledSieve



/-! Cubic residual and geometric-moment bounds for the finite distortion sieve. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
open Erdos7BinarySieve (expect)
set_option maxHeartbeats 4000000

lemma hinge_le_cubic (x y : ℚ) (hx : 0 ≤ x) (hy : 0 < y) :
    max 0 (x-y) ≤ 4*x^3/(27*y^2) := by
  apply max_le (by positivity)
  apply (le_div_iff₀ (by positivity : (0:ℚ) < 27*y^2)).mpr
  have hh : 0 ≤ (2*x-3*y)^2*(x+3*y) := mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith only [hh]

lemma residual_le_cubic {c α : ℚ} (hc : 1 < c) (hα : 0 ≤ α) :
    residual c α ≤ (4*c^3/(27*(c-1)^2))*α^3 := by
  have hh := hinge_le_cubic (c*α) (c-1) (mul_nonneg (by linarith) hα) (by linarith)
  apply hh.trans_eq
  ring

/-- Tail potential for the quadratic coefficients in a cubic geometric moment. -/
def cubicGeomTail (r : ℚ) (E : ℕ) : ℚ :=
  r^E*((3*(E:ℚ)^2+3*E+1)/(1-r)+(6*E+3)*r/(1-r)^2+3*r*(1+r)/(1-r)^3)

lemma cubicGeomTail_step (r : ℚ) (hr : r < 1) (E : ℕ) :
    cubicGeomTail r E=(3*(E:ℚ)^2+3*E+1)*r^E+cubicGeomTail r (E+1) := by
  have hn : 1-r≠0 := by linarith
  unfold cubicGeomTail
  push_cast
  rw [pow_succ]
  field_simp
  <;> ring

lemma cubicGeomTail_nonneg (r : ℚ) (hr0 : 0 ≤ r) (hr : r < 1) (E : ℕ) :
    0 ≤ cubicGeomTail r E := by
  have hd : 0 < 1-r := by linarith
  unfold cubicGeomTail
  positivity

lemma cubicGeomTail_sum (r : ℚ) (hr : r < 1) (E : ℕ) :
    (∑ a∈Finset.range E,(3*(a:ℚ)^2+3*a+1)*r^a)+cubicGeomTail r E=cubicGeomTail r 0 := by
  induction E with
  | zero => simp
  | succ E ih =>
    rw [Finset.sum_range_succ]
    have hh := cubicGeomTail_step r hr E
    linarith

lemma cubic_positive_geometric_bound (r : ℚ) (hr0 : 0 ≤ r) (hr : r < 1) (E : ℕ) :
    (∑ g∈Finset.range E,(3*((g+1:ℕ):ℚ)^2+3*(g+1)+1)*r^(g+1)) ≤
      r*(7-2*r+r^2)/(1-r)^3 := by
  have hh := cubicGeomTail_sum r hr (E+1)
  rw [Finset.sum_range_succ'] at hh
  have hn := cubicGeomTail_nonneg r hr0 hr (E+1)
  have hid : cubicGeomTail r 0-1=r*(7-2*r+r^2)/(1-r)^3 := by
    have hne : 1-r≠0 := by linarith
    unfold cubicGeomTail
    simp only [Nat.cast_zero,pow_zero,mul_zero,add_zero,zero_add,one_mul,zero_pow (by omega : 2≠0)]
    field_simp
    <;> ring
  rw [← hid]
  norm_num only [Nat.cast_zero,pow_zero,mul_zero,add_zero,zero_add,one_mul,zero_pow (by omega : 2≠0)] at hh
  simp only [Nat.cast_add,Nat.cast_one] at hh ⊢
  linarith

lemma prime_cubic_geometric_bound (p E : ℕ) (hp : 1 < p) :
    (∑ g∈Finset.range E,(3*((g+1:ℕ):ℚ)^2+3*(g+1)+1)*((p:ℚ)⁻¹)^(g+1)) ≤
      (7*(p:ℚ)^2-2*p+1)/(p-1)^3 := by
  have hpQ : (1:ℚ) < p := by exact_mod_cast hp
  have h0 : 0 < (p:ℚ) := lt_trans (by norm_num) hpQ
  have hi : (p:ℚ)⁻¹ < 1 := (inv_lt_one₀ h0).mpr hpQ
  apply (cubic_positive_geometric_bound (p:ℚ)⁻¹ (by positivity) hi E).trans_eq
  have hn : (p:ℚ)-1≠0 := by linarith
  field_simp
  <;> ring

#print axioms residual_le_cubic
#print axioms prime_cubic_geometric_bound
end Erdos7KilledSieve



/-! A uniform finite cubic budget bound using the wheel 2310. -/
namespace Erdos7CubicSieve
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

noncomputable def multiplier (p : ℕ) : ℚ :=
  1+(5/4:ℚ)*(7*(p:ℚ)^2-2*p+1)/(p-1)^3
noncomputable def charge (p : ℕ) : ℚ := (125/27:ℚ)/(p-1)^3

lemma multiplier_increment (p : ℕ) (hp : 5 ≤ p) :
    multiplier p-1=(35/4:ℚ)/(p-1)+15/(p-1)^2+(15/2:ℚ)/(p-1)^3 := by
  have hpQ : (5:ℚ) ≤ p := by exact_mod_cast hp
  have hn : (p:ℚ)-1≠0 := by linarith
  dsimp [multiplier]
  field_simp
  <;> ring

lemma multiplier_one_le (p : ℕ) (hp : 5 ≤ p) : 1 ≤ multiplier p := by
  have hpQ : (5:ℚ) ≤ p := by exact_mod_cast hp
  have hn : (0:ℚ) < p-1 := by linarith
  have hh := multiplier_increment p hp
  have hpos : 0 ≤ (35/4:ℚ)/(p-1)+15/(p-1)^2+(15/2:ℚ)/(p-1)^3 := by positivity
  linarith

lemma multiplier_nonneg (p : ℕ) (hp : 5 ≤ p) : 0 ≤ multiplier p :=
  le_trans (by norm_num) (multiplier_one_le p hp)
lemma charge_nonneg (p : ℕ) (hp : 5 ≤ p) : 0 ≤ charge p := by
  have hpQ : (5:ℚ) ≤ p := by exact_mod_cast hp
  have hh : (0:ℚ) < p-1 := by linarith
  dsimp [charge]
  positivity

/-- Wheel 2310 leaves at most 480 possible prime residues per block. -/
theorem prime_block_card_le (N : ℕ) (hN : 2310 < N) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ N ≤ p ∧ p < N+2310) : P.card ≤ 480 := by
  have hsub : P ⊆ (Finset.Ico N (N+2310)).filter (fun p => Nat.Coprime 2310 p) := by
    intro p hp
    obtain ⟨hprime,hlo,hhi⟩ := hP p hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hlo,hhi⟩, ?_⟩
    exact (Nat.coprime_of_lt_prime (by norm_num : 2310 ≠ 0) (hN.trans_le hlo) hprime).symm
  have hh := Finset.card_le_card hsub
  rw [Nat.filter_coprime_Ico_eq_totient] at hh
  norm_num [Nat.totient] at hh
  exact hh

lemma scalar_increment_bound (n : ℚ) (hn : 1000000 ≤ n) :
    (35/4:ℚ)/(n-1)+15/(n-1)^2+(15/2:ℚ)/(n-1)^3 ≤ (219/25:ℚ)/n := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n-1 := by linarith
  have hden : 0 < 100*n*(n-1)^3 := by positivity
  apply (mul_le_mul_iff_of_pos_right hden).mp
  field_simp
  have hx : 0 ≤ n-1000000 := by linarith
  nlinarith [mul_nonneg hx (sq_nonneg n),sq_nonneg (n-1)]

lemma scalar_charge_bound (n : ℚ) (hn : 1000000 ≤ n) :
    (125/27:ℚ)/(n-1)^3 ≤ (116/25:ℚ)/n^3 := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n-1 := by linarith
  have hden : 0 < 675*n^3*(n-1)^3 := by positivity
  apply (mul_le_mul_iff_of_pos_right hden).mp
  field_simp
  have hx : 0 ≤ n-1000000 := by linarith
  nlinarith [mul_nonneg hx (sq_nonneg n),sq_nonneg (n-1)]

lemma block_potential_drop (n : ℚ) (hn : 1000000 ≤ n) :
    ((11136/5:ℚ)/n^3+6/(n+2310)^2)/(1-(21024/5:ℚ)/n) ≤ 6/n^2 := by
  have hn0 : 0 < n := by linarith
  have hN : 0 < n+2310 := by linarith
  have hD : 0 < 5*n-21024 := by linarith
  have hd : 0 < 1-(21024/5:ℚ)/n := by
    apply sub_pos.mpr
    exact (div_lt_one hn0).mpr (by linarith)
  apply (div_le_iff₀ hd).mpr
  have hden : 0 < 5*n^3*(n+2310)^2 := by positivity
  apply (mul_le_mul_iff_of_pos_right hden).mp
  field_simp
  have hx : 0 ≤ n-1000000 := by linarith
  nlinarith [mul_nonneg hx (by linarith : 0 ≤ n)]

noncomputable def budgetProduct (S : Finset ℕ) : ℚ := ∏ p ∈ S, multiplier p
noncomputable def budgetCost (S : Finset ℕ) : ℚ :=
  ∑ p ∈ S, charge p * budgetProduct (S.filter (· < p))

lemma budgetProduct_nonneg (S : Finset ℕ) (hS : ∀ p ∈ S, 5 ≤ p) :
    0 ≤ budgetProduct S :=
  Finset.prod_nonneg (fun p hp => multiplier_nonneg p (hS p hp))

lemma budgetProduct_one_le (S : Finset ℕ) (hS : ∀ p ∈ S, 5 ≤ p) :
    1 ≤ budgetProduct S :=
  by
    have hh := Finset.prod_le_prod (s := S) (f := fun _ => (1 : ℚ))
      (by intros; norm_num) (fun p hp => multiplier_one_le p (hS p hp))
    simpa only [Finset.prod_const_one] using hh

lemma budgetProduct_mono {S T : Finset ℕ} (hST : S ⊆ T)
    (hT : ∀ p ∈ T, 5 ≤ p) : budgetProduct S ≤ budgetProduct T := by
  have heq : budgetProduct (T \ S) * budgetProduct S = budgetProduct T :=
    Finset.prod_sdiff hST
  have h1 := budgetProduct_one_le (T \ S) (fun p hp => hT p (Finset.mem_sdiff.mp hp).1)
  have h0 := budgetProduct_nonneg S (fun p hp => hT p (hST hp))
  nlinarith

lemma budgetCost_nonneg (S : Finset ℕ) (hS : ∀ p ∈ S, 5 ≤ p) :
    0 ≤ budgetCost S := by
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (charge_nonneg p (hS p hp))
    (budgetProduct_nonneg _ (fun q hq => hS q (Finset.mem_filter.mp hq).1))

lemma budgetCost_mono {S T : Finset ℕ} (hST : S ⊆ T)
    (hT : ∀ p ∈ T, 5 ≤ p) : budgetCost S ≤ budgetCost T := by
  apply (Finset.sum_le_sum (fun p (hp : p ∈ S) =>
    mul_le_mul_of_nonneg_left
      (budgetProduct_mono (Finset.filter_subset_filter _ hST)
        (fun q hq => hT q (Finset.mem_filter.mp hq).1)) (charge_nonneg p (hT p (hST hp))))).trans
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun p hp _ =>
    mul_nonneg (charge_nonneg p (hT p hp))
      (budgetProduct_nonneg _ (fun q hq => hT q (Finset.mem_filter.mp hq).1)))

lemma budgetProduct_union {A B : Finset ℕ} (h : Disjoint A B) :
    budgetProduct (A ∪ B) = budgetProduct A * budgetProduct B :=
  Finset.prod_union h

lemma budgetCost_union {A B : Finset ℕ}
    (h : ∀ a ∈ A, ∀ b ∈ B, a < b) :
    budgetCost (A ∪ B) = budgetCost A + budgetProduct A * budgetCost B := by
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (lt_irrefl a) (h a ha a hb)
  have hA (a : ℕ) (ha : a ∈ A) :
      (A ∪ B).filter (· < a) = A.filter (· < a) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hp | hp, hpa⟩
      · exact ⟨hp, hpa⟩
      · exact False.elim ((not_lt_of_gt (h a ha p hp)) hpa)
    · rintro ⟨hp,hpa⟩; exact ⟨Or.inl hp,hpa⟩
  have hB (b : ℕ) (hb : b ∈ B) :
      (A ∪ B).filter (· < b) = A ∪ B.filter (· < b) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hp | hp,hpb⟩
      · exact Or.inl hp
      · exact Or.inr ⟨hp,hpb⟩
    · rintro (hp | ⟨hp,hpb⟩)
      · exact ⟨Or.inl hp,h p hp b hb⟩
      · exact ⟨Or.inr hp,hpb⟩
  unfold budgetCost
  rw [Finset.sum_union hd, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro a ha; rw [hA a ha]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [hB b hb, budgetProduct_union (hd.mono_right (Finset.filter_subset _ _))]
    ring

lemma budgetProduct_empty : budgetProduct ∅ = 1 := by simp [budgetProduct]
lemma budgetCost_empty : budgetCost ∅ = 0 := by simp [budgetCost]
lemma budgetProduct_singleton (p : ℕ) : budgetProduct {p} = multiplier p := by
  simp [budgetProduct]
lemma budgetCost_singleton (p : ℕ) : budgetCost {p} = charge p := by
  have hf : ({p} : Finset ℕ).filter (· < p) = ∅ := by ext; simp; omega
  simp [budgetCost, hf, budgetProduct_empty]



lemma multiplier_increment_le {n p : ℕ} (hn : 1000000 ≤ n) (hp : n ≤ p) :
    multiplier p-1 ≤ (219/25:ℚ)/n := by
  have hnQ : (1000000:ℚ) ≤ n := by exact_mod_cast hn
  have hpQ : (n:ℚ) ≤ p := by exact_mod_cast hp
  have hn1 : (0:ℚ) < n-1 := by linarith
  rw [multiplier_increment p (by omega)]
  apply le_trans _ (scalar_increment_bound n hnQ)
  gcongr

lemma charge_le {n p : ℕ} (hn : 1000000 ≤ n) (hp : n ≤ p) :
    charge p ≤ (116/25:ℚ)/n^3 := by
  have hnQ : (1000000:ℚ) ≤ n := by exact_mod_cast hn
  have hpQ : (n:ℚ) ≤ p := by exact_mod_cast hp
  have hn1 : (0:ℚ) < n-1 := by linarith
  apply le_trans _ (scalar_charge_bound n hnQ)
  dsimp [charge]
  gcongr

lemma block_den_pos (n : ℕ) (hn : 1000000 ≤ n) :
    (0:ℚ) < 1-(21024/5:ℚ)/n := by
  have hnQ : (1000000:ℚ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℚ) < n := by linarith
  apply sub_pos.mpr
  exact (div_lt_one hn0).mpr (by linarith)

lemma block_product_bound (n : ℕ) (hn : 1000000 ≤ n) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ n ≤ p ∧ p < n+2310) :
    budgetProduct S ≤ 1/(1-(21024/5:ℚ)/n) := by
  have hnQ : (1000000:ℚ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℚ) < n := by linarith
  have hcardQ : (S.card:ℚ) ≤ 480 := by
    exact_mod_cast prime_block_card_le n (by omega) S hS
  have hsum : (∑ p∈S, (multiplier p-1)) ≤ (21024/5:ℚ)/n := by
    have hb := Finset.sum_le_card_nsmul S (fun p => multiplier p-1) ((219/25:ℚ)/n)
      (fun p hp => multiplier_increment_le hn (hS p hp).2.1)
    simp only [nsmul_eq_mul] at hb
    have hm := mul_le_mul_of_nonneg_right hcardQ (by positivity : 0 ≤ (219/25:ℚ)/n)
    exact hb.trans (hm.trans_eq (by ring))
  have hsmall : (21024/5:ℚ)/n < 1 := by have := block_den_pos n hn; linarith
  have hh := Erdos7No23Sieve.product_le_inverse_sum S (fun p => multiplier p-1)
    (fun p hp => sub_nonneg.mpr (multiplier_one_le p (by have := (hS p hp).2.1; omega)))
    (hsum.trans_lt hsmall)
  simp only [add_sub_cancel] at hh
  apply hh.trans
  exact div_le_div_of_nonneg_left (by norm_num) (block_den_pos n hn) (by linarith)

lemma block_cost_bound (n : ℕ) (hn : 1000000 ≤ n) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ n ≤ p ∧ p < n+2310) :
    budgetCost S ≤ ((11136/5:ℚ)/n^3)/(1-(21024/5:ℚ)/n) := by
  have hnQ : (1000000:ℚ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℚ) < n := by linarith
  have hden := block_den_pos n hn
  have hS5 : ∀ p∈S, 5 ≤ p := by intro p hp; have := (hS p hp).2.1; omega
  have hP := block_product_bound n hn S hS
  have hcard : (S.card:ℚ) ≤ 480 := by
    exact_mod_cast prime_block_card_le n (by omega) S hS
  have hh := Finset.sum_le_card_nsmul S
    (fun p => charge p*budgetProduct (S.filter (· < p)))
    (((116/25:ℚ)/n^3)/(1-(21024/5:ℚ)/n)) (by
      intro p hp
      rw [div_eq_mul_inv _ (1-(21024/5:ℚ)/n)]
      exact mul_le_mul (charge_le hn (hS p hp).2.1)
        ((budgetProduct_mono (Finset.filter_subset _ _) hS5).trans (by simpa using hP))
        (budgetProduct_nonneg _ (fun q hq => hS5 q (Finset.mem_filter.mp hq).1))
        (by positivity))
  simp only [nsmul_eq_mul] at hh
  have hm := mul_le_mul_of_nonneg_right hcard
    (by positivity : 0 ≤ ((116/25:ℚ)/n^3)/(1-(21024/5:ℚ)/n))
  exact hh.trans (hm.trans_eq (by ring))

lemma block_budget_bound (n : ℕ) (hn : 1000000 ≤ n) (S : Finset ℕ)
    (hS : ∀ p∈S, p.Prime ∧ n ≤ p ∧ p < n+2310) :
    budgetCost S+6*budgetProduct S/(n+2310)^2 ≤ 6/(n:ℚ)^2 := by
  have hnQ : (1000000:ℚ) ≤ n := by exact_mod_cast hn
  have hC := block_cost_bound n hn S hS
  have hP := block_product_bound n hn S hS
  apply (add_le_add hC (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hP (by norm_num)) (by positivity))).trans
  convert block_potential_drop n hnQ using 1 <;> ring

lemma bounded_tail_cost (k n : ℕ) (hn : 1000000 ≤ n) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ n ≤ p ∧ p < n + 2310*k) :
    budgetCost S ≤ (6:ℚ)/(n:ℚ)^2 := by
  induction k generalizing n S with
  | zero =>
    have hSE : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have := hS p hp
      omega
    rw [hSE, budgetCost_empty]
    positivity
  | succ k ih =>
    let A := S.filter (· < n+2310)
    let B := S.filter (fun p => ¬p < n+2310)
    have hSAB : S = A ∪ B := (Finset.filter_union_filter_not_eq _ _).symm
    have hA (p : ℕ) (hp : p ∈ A) : p.Prime ∧ n ≤ p ∧ p < n+2310 := by
      obtain ⟨hp,hlo⟩ := Finset.mem_filter.mp hp
      exact ⟨(hS p hp).1, (hS p hp).2.1, hlo⟩
    have hB (p : ℕ) (hp : p ∈ B) : p.Prime ∧ n+2310 ≤ p ∧ p < (n+2310)+2310*k := by
      obtain ⟨hp,hhi⟩ := Finset.mem_filter.mp hp
      obtain ⟨hprime,hlo,hbound⟩ := hS p hp
      refine ⟨hprime,by omega,by omega⟩
    have hAB : ∀ a ∈ A, ∀ b ∈ B, a < b := by
      intro a ha b hb
      exact (hA a ha).2.2.trans_le (hB b hb).2.1
    have hPA : 0 ≤ budgetProduct A := budgetProduct_nonneg A (by
      intro p hp; have := (hA p hp).2.1; omega)
    have hb := ih (n+2310) (by omega) B hB
    rw [hSAB, budgetCost_union hAB]
    apply (add_le_add_right (mul_le_mul_of_nonneg_left hb hPA) _).trans
    have hh := block_budget_bound n hn A hA
    simp only [Nat.cast_add, Nat.cast_ofNat] at *
    convert hh using 1 <;> ring

/-- The tail bound is uniform over all finite sets and all finite exponent caps. -/
theorem tail_cost_bound (n : ℕ) (hn : 1000000 ≤ n) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ n ≤ p) :
    budgetCost S ≤ (6:ℚ)/(n:ℚ)^2 := by
  apply bounded_tail_cost (S.sup id + 1) n hn S
  intro p hp
  have hpmax : p ≤ S.sup id := Finset.le_sup (f := id) hp
  exact ⟨(hS p hp).1, (hS p hp).2, by omega⟩


#print axioms tail_cost_bound
end Erdos7CubicSieve



/-! Complete-family estimates without a finitely supported comparison law. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
set_option maxHeartbeats 4000000

section Test
variable {n : ℕ} (κ : Type*) (A : Fin n → Type*)
variable [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]

/-- A bound for one test and one complete-family multiplicity. -/
def CompleteTestBound (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (t : ℕ) (μ : (∀ i,A i) → ℚ) (M : ℕ) (φ : ℚ → ℚ) (G : ℚ) : Prop :=
  ∀ (K : Finset κ) (e : κ → Fin n → ℕ) (X : κ → ∀ i,Finset (A i)),
    (∀ k∈K,PrefixPattern E t (e k)) →
    (∀ k∈K,∀ i∈expSupport (e k),c i*fraction (X k i) ≤ q i (e k i-1)) →
    CompletePatterns E t K e M →
    (∑ x,μ x*φ (∑ k∈K,boxIndicator A (expSupport (e k)) (X k) x)) ≤ G

lemma completeTestBound_initial (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (μ : (∀ i,A i) → ℚ) (hμ : (∑ x,μ x)=1)
    (M : ℕ) (φ : ℚ → ℚ) : CompleteTestBound κ A E c q 0 μ M φ (φ M) := by
  intro K e X he hX hM
  have hz (k : κ) (hk : k∈K) : e k=fun _ => 0 := funext (fun i => (he k hk).2 i (Nat.zero_le _))
  have hcard : K.card=M := by
    have hh := hM _ (prefixPattern_zero E 0)
    have heq : K.filter (fun k => e k=fun _ => 0)=K := Finset.filter_true_of_mem hz
    rwa [heq] at hh
  have hval (x : ∀ i, A i) : (∑ k∈K, boxIndicator A (expSupport (e k)) (X k) x)=(M:ℚ) := by
    calc
      _ = ∑ _k∈K, (1:ℚ) := Finset.sum_congr rfl (fun k hk => by simp [hz k hk,expSupport,boxIndicator_empty])
      _ = _ := by simp [hcard]
  simp_rw [hval]
  rw [← Finset.sum_mul,hμ,one_mul]

/-- Finite positive-mixture compression for a single convex test. -/
theorem completeTestBound_resample (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (ht : t < n)
    (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (M : ℕ) (φ : ℚ → ℚ) (hφ : ConvexOn ℚ Set.univ φ) (hmono : Monotone φ)
    (G : ℕ → ℚ)
    (hcomp : ∀ a,a ≤ E ⟨t,ht⟩ → CompleteTestBound κ A E c q t μ ((a+1)*M) φ (G a))
    (B : Finset (∀ i,A i)) (hc : 1 ≤ c ⟨t,ht⟩) (hq1 : q ⟨t,ht⟩ 0 ≤ 1)
    (hqdec : ∀ g,g < E ⟨t,ht⟩ → q ⟨t,ht⟩ (g+1) ≤ q ⟨t,ht⟩ g)
    (hqE : q ⟨t,ht⟩ (E ⟨t,ht⟩)=0) :
    CompleteTestBound κ A E c q (t+1) (resample A ⟨t,ht⟩ μ B (c ⟨t,ht⟩)) M φ
      ((1-q ⟨t,ht⟩ 0)*G 0+∑ g∈Finset.range (E ⟨t,ht⟩),(q ⟨t,ht⟩ g-q ⟨t,ht⟩ (g+1))*G (g+1)) := by
  intro K e X he hX hM
  let i : Fin n := ⟨t,ht⟩
  let e' (k : κ) := Function.update (e k) i 0
  let K' (a : ℕ) := K.filter (fun k => e k i ≤ a)
  have he' (k : κ) (hk : k∈K) : PrefixPattern E t (e' k) := by
    constructor
    · intro j
      by_cases hj : j=i
      · subst j; simp [e']
      · simpa only [e',Function.update_of_ne hj] using (he k hk).1 j
    · intro j hj
      by_cases hji : j=i
      · subst j; simp [e']
      · have hjt : j.val≠t := by intro heq; exact hji (Fin.ext heq)
        have hh := (he k hk).2 j (by omega)
        simpa only [e',Function.update_of_ne hji] using hh
  have hX' (k : κ) (hk : k∈K) (j : Fin n) (hj : j∈expSupport (e' k)) :
      c j*fraction (X k j) ≤ q j (e' k j-1) := by
    rw [expSupport_update_zero] at hj
    have hjne := (Finset.mem_erase.mp hj).1
    simpa only [e',Function.update_of_ne hjne] using hX k hk j (Finset.mem_erase.mp hj).2
  have hbound (a : ℕ) (ha : a ≤ E i) :
      (∑ x, μ x*φ (∑ k∈K' a, boxIndicator A (expSupport (e' k)) (X k) x))  ≤ 
        G a :=
    hcomp a ha (K' a) e' X
      (fun k hk => he' k (Finset.mem_filter.mp hk).1)
      (fun k hk => hX' k (Finset.mem_filter.mp hk).1)
      (completePatterns_erase E t ht K e M hM a ha)
  have hstep := resample_exponent_compression A i μ hμ B (c i) hc φ hφ hmono K e X (E i) (q i)
    (fun k hk => (he k hk).1 i)
    (fun k hk hi => hX k hk i ((mem_expSupport _ _).mpr hi)) hqE
  apply hstep.trans
  have h0 := mul_le_mul_of_nonneg_left (hbound 0 (Nat.zero_le _)) (sub_nonneg.mpr hq1)
  have hsum := Finset.sum_le_sum (fun g (hg : g∈Finset.range (E i)) =>
    mul_le_mul_of_nonneg_left (hbound (g+1) (by have := Finset.mem_range.mp hg; omega))
      (sub_nonneg.mpr (hqdec g (Finset.mem_range.mp hg))))
  exact add_le_add h0 hsum

lemma completeTestBound_mono (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (t : ℕ) (μ : (∀ i,A i) → ℚ) (M : ℕ) (φ : ℚ → ℚ) {G H : ℚ}
    (hh : CompleteTestBound κ A E c q t μ M φ G) (hGH : G ≤ H) :
    CompleteTestBound κ A E c q t μ M φ H := by
  intro K e X he hX hM
  exact (hh K e X he hX hM).trans hGH

lemma completeTestBound_kill (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (t : ℕ) (i : Fin n) (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (B : Finset (∀ i,A i)) (hc : 1 ≤ c i) (L : ℚ) (hLm : L ≤ ∑ x,μ x)
    (hL : (∑ x,μ x*residual (c i) (coordinateFraction A i B x)) ≤ L)
    (M : ℕ) (φ : ℚ → ℚ) (hφ : ∀ z,0 ≤ φ z) (G : ℚ)
    (hh : CompleteTestBound κ A E c q t (resample A i μ B (c i)) M φ G) :
    CompleteTestBound κ A E c q t (killedResample A i μ B (c i) L) M φ G := by
  intro K e X he hX hM
  have hk := killedResample_test A i μ hμ B (c i) L hc hLm hL
    (fun x => φ (∑ k∈K,boxIndicator A (expSupport (e k)) (X k) x)) 0 (fun x => hφ _)
  rw [mul_zero,sub_zero] at hk
  exact hk.trans (hh K e X he hX hM)

end Test
#print axioms completeTestBound_resample
end Erdos7KilledSieve



/-! Scaled stop-loss profiles for complete exponent families. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
set_option maxHeartbeats 4000000

/-- The finite-coordinate operator on a stop-loss profile. -/
def profileStep (E : ℕ) (q : ℕ → ℚ) (H : ℚ → ℚ) (u : ℚ) : ℚ :=
  (1-q 0)*H u+∑ g∈Finset.range E,(q g-q (g+1))*(g+2)*H (u/(g+2))

section Profile
variable {n : ℕ} (κ : Type*) (A : Fin n → Type*)
variable [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]

/-- Only nonnegative thresholds at most `T` are needed in the finite prefix. -/
def CompleteProfileBound (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (t : ℕ) (μ : (∀ i,A i) → ℚ) (T : ℚ) (H : ℚ → ℚ) : Prop :=
  ∀ (M : ℕ) (u : ℚ),0 ≤ u → u ≤ T →
    CompleteTestBound κ A E c q t μ M (fun z => max 0 (z-(M:ℚ)*u)) ((M:ℚ)*H u)

lemma completeProfileBound_initial (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (μ : (∀ i,A i) → ℚ) (hμ : (∑ x,μ x)=1) (T : ℚ) :
    CompleteProfileBound κ A E c q 0 μ T (fun u => max 0 (1-u)) := by
  intro M u hu huT
  have hh := completeTestBound_initial κ A E c q μ hμ M (fun z => max 0 (z-(M:ℚ)*u))
  convert hh using 1
  rw [mul_max_of_nonneg _ _ (Nat.cast_nonneg M)]
  ring_nf

lemma completeProfileBound_resample (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (ht : t < n)
    (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x) (T : ℚ) (H : ℚ → ℚ)
    (hcomp : CompleteProfileBound κ A E c q t μ T H)
    (B : Finset (∀ i,A i)) (hc : 1 ≤ c ⟨t,ht⟩) (hq1 : q ⟨t,ht⟩ 0 ≤ 1)
    (hqdec : ∀ g,g < E ⟨t,ht⟩ → q ⟨t,ht⟩ (g+1) ≤ q ⟨t,ht⟩ g)
    (hqE : q ⟨t,ht⟩ (E ⟨t,ht⟩)=0) :
    CompleteProfileBound κ A E c q (t+1) (resample A ⟨t,ht⟩ μ B (c ⟨t,ht⟩)) T
      (profileStep (E ⟨t,ht⟩) (q ⟨t,ht⟩) H) := by
  intro M u hu huT
  let G (a : ℕ) : ℚ := (((a+1)*M:ℕ):ℚ)*H (u/(a+1))
  have hbound (a : ℕ) (ha : a ≤ E ⟨t,ht⟩) :
      CompleteTestBound κ A E c q t μ ((a+1)*M) (fun z => max 0 (z-(M:ℚ)*u)) (G a) := by
    have ha0 : (0:ℚ) < a+1 := by positivity
    have hau : u/(a+1) ≤ u := (div_le_self hu (by norm_num)).trans le_rfl
    have hh := hcomp ((a+1)*M) (u/(a+1)) (div_nonneg hu ha0.le) (hau.trans huT)
    have hid : (((a+1)*M:ℕ):ℚ)*(u/(a+1))=(M:ℚ)*u := by
      push_cast
      field_simp
      <;> ring
    simpa only [hid,G] using hh
  have hh := completeTestBound_resample κ A E c q t ht μ hμ M
    (fun z => max 0 (z-(M:ℚ)*u))
    (by simpa only [one_mul,sub_eq_add_neg] using hinge_convex 1 (-((M:ℚ)*u)))
    (by intro x y hxy; exact max_le_max le_rfl (sub_le_sub_right hxy _)) G hbound B hc hq1 hqdec hqE
  convert hh using 1
  simp only [G,profileStep,Nat.zero_add,Nat.one_mul,Nat.cast_zero,zero_add,div_one,
    Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.add_assoc]
  rw [mul_add,Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro g hg
    ring_nf

lemma completeProfileBound_kill (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (t : ℕ) (i : Fin n) (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (B : Finset (∀ i,A i)) (hc : 1 ≤ c i) (L : ℚ) (hLm : L ≤ ∑ x,μ x)
    (hL : (∑ x,μ x*residual (c i) (coordinateFraction A i B x)) ≤ L)
    (T : ℚ) (H : ℚ → ℚ)
    (hh : CompleteProfileBound κ A E c q t (resample A i μ B (c i)) T H) :
    CompleteProfileBound κ A E c q t (killedResample A i μ B (c i) L) T H := by
  intro M u hu huT
  exact completeTestBound_kill κ A E c q t i μ hμ B hc L hLm hL M _
    (fun z => le_max_left _ _) _ (hh M u hu huT)

/-- Arbitrary cutoffs give valid mass-based refinements; they do not require
positivity of a comparison law or convexity of the stored upper profile. -/
lemma completeProfileBound_prune (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (t : ℕ) (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (T : ℚ) (H : ℚ → ℚ) (hcomp : CompleteProfileBound κ A E c q t μ T H)
    (m : ℚ) (hm : (∑ x,μ x)=m) (b : ℚ) (hb : 0 ≤ b) (hbT : b ≤ T) :
    CompleteProfileBound κ A E c q t μ T
      (fun u => if u ≤ b then min (H u) (H b+(b-u)*m) else H u) := by
  intro M u hu huT K e X he hX hM
  have hh := hcomp M u hu huT K e X he hX hM
  dsimp only
  by_cases hub : u ≤ b
  · rw [if_pos hub,mul_min_of_nonneg _ _ (Nat.cast_nonneg M)]
    refine le_min hh ?_
    have hp := stopLoss_mass_bound μ hμ
      (fun x => ∑ k∈K,boxIndicator A (expSupport (e k)) (X k) x)
      ((M:ℚ)*u) ((M:ℚ)*b) (mul_le_mul_of_nonneg_left hub (Nat.cast_nonneg _))
    have hv := hcomp M b hb hbT K e X he hX hM
    rw [hm] at hp
    calc
      _ ≤ (M:ℚ)*H b+((M:ℚ)*b-(M:ℚ)*u)*m := hp.trans (add_le_add_left hv _)
      _ = _ := by ring
  · simpa only [if_neg hub] using hh

lemma completeProfileBound_mono (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (t : ℕ) (μ : (∀ i,A i) → ℚ) (T : ℚ) (H J : ℚ → ℚ)
    (hh : CompleteProfileBound κ A E c q t μ T H) (hHJ : ∀ u,0 ≤ u → u ≤ T → H u ≤ J u) :
    CompleteProfileBound κ A E c q t μ T J := by
  intro M u hu huT
  exact completeTestBound_mono κ A E c q t μ M _ (hh M u hu huT)
    (mul_le_mul_of_nonneg_left (hHJ u hu huT) (Nat.cast_nonneg _))

end Profile
#print axioms completeProfileBound_resample
#print axioms completeProfileBound_prune
end Erdos7KilledSieve



/-! Independent moment bounds alongside finite stop-loss profiles. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
set_option maxHeartbeats 4000000

/-- Nonnegative power test, globally monotone and convex. -/
def positivePower (r : ℕ) (x : ℚ) : ℚ := (max 0 x)^r

lemma positivePower_convex (r : ℕ) : ConvexOn ℚ Set.univ (positivePower r) := by
  have hh : ConvexOn ℚ Set.univ (fun x : ℚ => max 0 x) := by
    simpa only [one_mul,add_zero] using hinge_convex 1 0
  exact hh.pow (fun x hx => le_max_left _ _) r

lemma positivePower_monotone (r : ℕ) : Monotone (positivePower r) := by
  intro x y hxy
  dsimp [positivePower]
  gcongr

/-- Exact finite-coordinate moment factor. -/
def momentFactor (E : ℕ) (q : ℕ → ℚ) (r : ℕ) : ℚ :=
  1+∑ g∈Finset.range E,q g*(((g+2:ℕ):ℚ)^r-((g+1:ℕ):ℚ)^r)

lemma momentFactor_eq_mixture (E : ℕ) (q : ℕ → ℚ) (hqE : q E=0) (r : ℕ) :
    momentFactor E q r=(1-q 0)+∑ g∈Finset.range E,(q g-q (g+1))*((g+2:ℕ):ℚ)^r := by
  have hh := chain_summation_by_parts (fun g => ((g+1:ℕ):ℚ)^r) q E
  simpa only [momentFactor,Nat.zero_add,Nat.cast_one,one_pow,mul_one,hqE,zero_mul,add_zero,Nat.add_assoc] using hh

lemma geometric_cubic_factor (p E : ℕ) (hp : 1 < p) (c : ℚ) (hc : 0 ≤ c) :
    momentFactor E (powerTail p c E) 3 ≤ 1+c*(7*(p:ℚ)^2-2*p+1)/(p-1)^3 := by
  have hEq : momentFactor E (powerTail p c E) 3 =
      1+c*∑ g∈Finset.range E,(3*((g+1:ℕ):ℚ)^2+3*(g+1)+1)*((p:ℚ)⁻¹)^(g+1) := by
    unfold momentFactor
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro g hg
    rw [powerTail,if_pos (Finset.mem_range.mp hg)]
    push_cast
    ring
  rw [hEq]
  simpa only [mul_div_assoc] using add_le_add_right
    (mul_le_mul_of_nonneg_left (prime_cubic_geometric_bound p E hp) hc) 1

section Moment
variable {n : ℕ} (κ : Type*) (A : Fin n → Type*)
variable [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]

/-- A uniform homogeneous moment bound for every complete prefix family. -/
def CompleteMomentBound (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (t : ℕ) (μ : (∀ i,A i) → ℚ) (r : ℕ) (C : ℚ) : Prop :=
  ∀ M : ℕ,CompleteTestBound κ A E c q t μ M (positivePower r) ((M:ℚ)^r*C)

lemma completeMomentBound_initial (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (μ : (∀ i,A i) → ℚ) (hμ : (∑ x,μ x)=1) (r : ℕ) :
    CompleteMomentBound κ A E c q 0 μ r 1 := by
  intro M
  simpa only [positivePower,max_eq_right (Nat.cast_nonneg M),mul_one] using
    completeTestBound_initial κ A E c q μ hμ M (positivePower r)

lemma completeMomentBound_resample (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (ht : t < n)
    (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x) (r : ℕ) (C : ℚ)
    (hcomp : CompleteMomentBound κ A E c q t μ r C)
    (B : Finset (∀ i,A i)) (hc : 1 ≤ c ⟨t,ht⟩) (hq1 : q ⟨t,ht⟩ 0 ≤ 1)
    (hqdec : ∀ g,g < E ⟨t,ht⟩ → q ⟨t,ht⟩ (g+1) ≤ q ⟨t,ht⟩ g)
    (hqE : q ⟨t,ht⟩ (E ⟨t,ht⟩)=0) :
    CompleteMomentBound κ A E c q (t+1) (resample A ⟨t,ht⟩ μ B (c ⟨t,ht⟩)) r
      (momentFactor (E ⟨t,ht⟩) (q ⟨t,ht⟩) r*C) := by
  intro M
  have hh := completeTestBound_resample κ A E c q t ht μ hμ M (positivePower r)
    (positivePower_convex r) (positivePower_monotone r)
    (fun a => (((a+1)*M:ℕ):ℚ)^r*C) (fun a ha => hcomp ((a+1)*M)) B hc hq1 hqdec hqE
  convert hh using 1
  rw [momentFactor_eq_mixture _ _ hqE]
  simp only [Nat.zero_add,Nat.one_mul,Nat.add_assoc,Nat.cast_mul,mul_pow]
  rw [add_mul,mul_add,Finset.sum_mul,Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro g hg
    ring

lemma completeMomentBound_kill (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (t : ℕ) (i : Fin n) (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (B : Finset (∀ i,A i)) (hc : 1 ≤ c i) (L : ℚ) (hLm : L ≤ ∑ x,μ x)
    (hL : (∑ x,μ x*residual (c i) (coordinateFraction A i B x)) ≤ L)
    (r : ℕ) (C : ℚ)
    (hh : CompleteMomentBound κ A E c q t (resample A i μ B (c i)) r C) :
    CompleteMomentBound κ A E c q t (killedResample A i μ B (c i) L) r C := by
  intro M
  exact completeTestBound_kill κ A E c q t i μ hμ B hc L hLm hL M _
    (fun z => pow_nonneg (le_max_left _ _) _) _ (hh M)

lemma completeMomentBound_mono (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (t : ℕ) (μ : (∀ i,A i) → ℚ) (r : ℕ) {C D : ℚ}
    (hh : CompleteMomentBound κ A E c q t μ r C) (hCD : C ≤ D) :
    CompleteMomentBound κ A E c q t μ r D := by
  intro M
  exact completeTestBound_mono κ A E c q t μ M _ (hh M)
    (mul_le_mul_of_nonneg_left hCD (pow_nonneg (Nat.cast_nonneg _) _))

end Moment
#print axioms geometric_cubic_factor
#print axioms completeMomentBound_resample
end Erdos7KilledSieve



/-! Finite-uniform truncation of the geometric stop-loss operator. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
set_option maxHeartbeats 4000000

lemma geometric_sum_zero_le (r : ℚ) (hr0 : 0 ≤ r) (hr : r < 1) (N : ℕ) :
    (∑ g∈Finset.range N,r^g) ≤ 1/(1-r) := by
  apply (le_div_iff₀ (sub_pos.mpr hr)).mpr
  have hh := geom_sum_mul r N
  have hp := pow_nonneg hr0 N
  nlinarith only [hh,hp]

lemma weighted_tail_telescope (E a : ℕ) (ha : a ≤ E) (q : ℕ → ℚ) (hqE : q E=0) :
    (∑ g∈Finset.Ico a E,(q g-q (g+1))*(g+2)) =
      (a+1)*q a+∑ g∈Finset.Ico a E,q g := by
  have hid (g : ℕ) : (q g-q (g+1))*(g+2)=q g-((g+2)*q (g+1)-(g+1)*q g) := by ring
  simp_rw [hid]
  rw [Finset.sum_sub_distrib]
  have hh := Finset.sum_Ico_sub (fun g => (g+1:ℚ)*q g) ha
  simp only [Nat.cast_add,Nat.cast_one] at hh
  have hsum : (∑ g∈Finset.Ico a E,((g+2:ℚ)*q (g+1)-(g+1)*q g)) =
      (E+1)*q E-(a+1)*q a := by
    convert hh using 1 <;> ring_nf
  rw [hsum,hqE,mul_zero]
  ring

lemma powerTail_sum_Ico_le (p E a : ℕ) (hp : 1 < p) (c : ℚ) (hc : 0 ≤ c) :
    (∑ g∈Finset.Ico a E,powerTail p c E g) ≤ c*((p:ℚ)⁻¹)^(a+1)/(1-(p:ℚ)⁻¹) := by
  have hpQ : (1:ℚ) < p := by exact_mod_cast hp
  have hp0 : (0:ℚ) < p := by linarith
  have hr : (p:ℚ)⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hpQ
  have heq : (∑ g∈Finset.Ico a E,powerTail p c E g) =
      c*((p:ℚ)⁻¹)^(a+1)*(∑ g∈Finset.range (E-a),((p:ℚ)⁻¹)^g) := by
    have hh : (∑ g∈Finset.Ico a E,powerTail p c E g)=
        ∑ g∈Finset.Ico a E,c*((p:ℚ)⁻¹)^(g+1) := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [powerTail,if_pos (Finset.mem_Ico.mp hg).2]
    rw [hh,Finset.sum_Ico_eq_sum_range,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g hg
    rw [show a+g+1=(a+1)+g by omega,pow_add]
    ring
  rw [heq]
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
    (geometric_sum_zero_le (p:ℚ)⁻¹ (by positivity) hr (E-a))
    (by positivity : 0 ≤ c*((p:ℚ)⁻¹)^(a+1))

lemma powerTail_weighted_tail_le (p E a : ℕ) (hp : 1 < p) (ha : a ≤ E)
    (c : ℚ) (hc : 0 ≤ c) :
    (∑ g∈Finset.Ico a E,(powerTail p c E g-powerTail p c E (g+1))*(g+2)) ≤
      c*((p:ℚ)⁻¹)^(a+1)*((a+2)+1/(p-1)) := by
  rw [weighted_tail_telescope E a ha _ (powerTail_terminal p c E)]
  have hqa : powerTail p c E a ≤ c*((p:ℚ)⁻¹)^(a+1) := by
    unfold powerTail
    split_ifs <;> [exact le_rfl; positivity]
  apply (add_le_add (mul_le_mul_of_nonneg_left hqa (by positivity))
    (powerTail_sum_Ico_le p E a hp c hc)).trans_eq
  have hpQ : (1:ℚ) < p := by exact_mod_cast hp
  have hp0 : (p:ℚ)≠0 := by linarith
  have hp1 : (p:ℚ)-1≠0 := by linarith
  field_simp
  <;> ring

lemma powerTail_difference (p E g : ℕ) (hp : 1 < p) (hg : g+1 < E) (c : ℚ) :
    powerTail p c E g-powerTail p c E (g+1)=c*(p-1)*((p:ℚ)⁻¹)^(g+2) := by
  have hpQ : (1:ℚ) < p := by exact_mod_cast hp
  have hp0 : (p:ℚ)≠0 := by linarith
  rw [powerTail,powerTail,if_pos (by omega : g < E),if_pos hg]
  simp only [pow_succ]
  field_simp
  <;> ring

/-- All omitted exponent factors are bounded using only the old first moment.
The formula is uniform in every finite exponent cap `E>a`. -/
theorem geometricMixture_truncate (p E a : ℕ) (hp : 1 < p) (ha : a < E)
    (c : ℚ) (hc : 0 ≤ c) (F : ℕ → ℚ) (H0 : ℚ) (hH0 : 0 ≤ H0)
    (hH : ∀ g,g∈Finset.Ico a E → F (g+2) ≤ H0) :
    ((1-powerTail p c E 0)*F 1+
      ∑ g∈Finset.range E,(powerTail p c E g-powerTail p c E (g+1))*(g+2)*F (g+2)) ≤
      (1-c/(p:ℚ))*F 1+
      (∑ g∈Finset.range a,c*(p-1)*((p:ℚ)⁻¹)^(g+2)*(g+2)*F (g+2))+
      c*((p:ℚ)⁻¹)^(a+1)*((a+2)+1/(p-1))*H0 := by
  have hq0 : powerTail p c E 0=c/(p:ℚ) := by
    rw [powerTail,if_pos (by omega : 0 < E)]
    simp only [zero_add,pow_one,div_eq_mul_inv]
  rw [hq0,← Finset.sum_range_add_sum_Ico _ ha.le]
  have hlow : (∑ g∈Finset.range a,(powerTail p c E g-powerTail p c E (g+1))*(g+2)*F (g+2)) =
      ∑ g∈Finset.range a,c*(p-1)*((p:ℚ)⁻¹)^(g+2)*(g+2)*F (g+2) := by
    apply Finset.sum_congr rfl
    intro g hg
    rw [powerTail_difference p E g hp (by have := Finset.mem_range.mp hg; omega)]
  rw [hlow]
  have ht : (∑ g∈Finset.Ico a E,(powerTail p c E g-powerTail p c E (g+1))*(g+2)*F (g+2)) ≤
      c*((p:ℚ)⁻¹)^(a+1)*((a+2)+1/(p-1))*H0 := by
    calc
      _ ≤ ∑ g∈Finset.Ico a E,(powerTail p c E g-powerTail p c E (g+1))*(g+2)*H0 := by
        apply Finset.sum_le_sum
        intro g hg
        apply mul_le_mul_of_nonneg_left (hH g hg)
        exact mul_nonneg (sub_nonneg.mpr (powerTail_decreasing p hp c hc E g)) (by positivity)
      _ = (∑ g∈Finset.Ico a E,(powerTail p c E g-powerTail p c E (g+1))*(g+2))*H0 := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (powerTail_weighted_tail_le p E a hp ha.le c hc) hH0
  linarith

/-- All omitted exponent factors are bounded using only the old first moment.
The formula is uniform in every finite exponent cap `E>a`. -/
theorem profileStep_geometric_truncate (p E a : ℕ) (hp : 1 < p) (ha : a < E)
    (c : ℚ) (hc : 0 ≤ c) (H : ℚ → ℚ) (u H0 : ℚ) (hH0 : 0 ≤ H0)
    (hH : ∀ g,g∈Finset.Ico a E → H (u/(g+2)) ≤ H0) :
    profileStep E (powerTail p c E) H u ≤
      (1-c/(p:ℚ))*H u+
      (∑ g∈Finset.range a,c*(p-1)*((p:ℚ)⁻¹)^(g+2)*(g+2)*H (u/(g+2)))+
      c*((p:ℚ)⁻¹)^(a+1)*((a+2)+1/(p-1))*H0 := by
  have hq0 : powerTail p c E 0=c/(p:ℚ) := by
    rw [powerTail,if_pos (by omega : 0 < E)]
    simp only [zero_add,pow_one,div_eq_mul_inv]
  unfold profileStep
  rw [hq0,← Finset.sum_range_add_sum_Ico _ ha.le]
  have hlow : (∑ g∈Finset.range a,(powerTail p c E g-powerTail p c E (g+1))*(g+2)*H (u/(g+2))) =
      ∑ g∈Finset.range a,c*(p-1)*((p:ℚ)⁻¹)^(g+2)*(g+2)*H (u/(g+2)) := by
    apply Finset.sum_congr rfl
    intro g hg
    rw [powerTail_difference p E g hp (by have := Finset.mem_range.mp hg; omega)]
  rw [hlow]
  have ht : (∑ g∈Finset.Ico a E,(powerTail p c E g-powerTail p c E (g+1))*(g+2)*H (u/(g+2))) ≤
      c*((p:ℚ)⁻¹)^(a+1)*((a+2)+1/(p-1))*H0 := by
    calc
      _ ≤ ∑ g∈Finset.Ico a E,(powerTail p c E g-powerTail p c E (g+1))*(g+2)*H0 := by
        apply Finset.sum_le_sum
        intro g hg
        apply mul_le_mul_of_nonneg_left (hH g hg)
        exact mul_nonneg (sub_nonneg.mpr (powerTail_decreasing p hp c hc E g)) (by positivity)
      _ = (∑ g∈Finset.Ico a E,(powerTail p c E g-powerTail p c E (g+1))*(g+2))*H0 := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (powerTail_weighted_tail_le p E a hp ha.le c hc) hH0
  linarith

#print axioms profileStep_geometric_truncate
end Erdos7KilledSieve



/-! Loss bounds supplied either by a stop-loss profile or by a cubic moment. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
set_option maxHeartbeats 4000000

theorem completeTestBound_layer_loss {n : ℕ} {κ : Type*}
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (t : ℕ) (μ : (∀ i, A i) → ℚ) (hμ : ∀ x, 0 ≤ μ x)
    (d s : ℚ) (G : ℚ)
    (hcomp : CompleteTestBound κ A E c q t μ 1 (fun z => residual d (s*z)) G)
    (hd : 1 ≤ d) (hs : 0 < s) (R : ℕ) (hR : 0 < R)
    (r : ℕ → ℚ) (hr : ∀ a, a < R → 0 ≤ r a) (hrs : (∑ a∈Finset.range R,r a) ≤ s)
    (K : ℕ → Finset κ) (e : ℕ → κ → Fin n → ℕ) (X : ℕ → κ → ∀ i, Finset (A i))
    (he : ∀ a, a < R → ∀ k∈K a, PrefixPattern E t (e a k))
    (hX : ∀ a, a < R → ∀ k∈K a, ∀ i∈expSupport (e a k), c i*fraction (X a k i) ≤ q i (e a k i-1))
    (hM : ∀ a, a < R → CompletePatterns E t (K a) (e a) 1)
    (α : (∀ i, A i) → ℚ)
    (hα : ∀ x, α x ≤ ∑ a∈Finset.range R, r a*∑ k∈K a, boxIndicator A (expSupport (e a k)) (X a k) x) :
    (∑ x, μ x*residual d (α x)) ≤ G := by
  let N (a : ℕ) (x : ∀ i, A i) := ∑ k∈K a, boxIndicator A (expSupport (e a k)) (X a k) x
  let φ (x : ℚ) := residual d (s*x)
  have hd0 : 0 ≤ d := (by norm_num : (0:ℚ) ≤ 1).trans hd
  have hcmp (a : ℕ) (ha : a < R) : (∑ x, μ x*φ (N a x)) ≤ G := by
    exact hcomp (K a) (e a) (X a) (he a ha) (hX a ha) (hM a ha)
  have hG : 0 ≤ G :=
    (Finset.sum_nonneg (fun x _ => mul_nonneg (hμ x) (le_max_left _ _))).trans (hcmp 0 hR)
  have hres (x : ∀ i, A i) : residual d (α x) ≤
      ∑ a∈Finset.range R, (r a/s)*φ (N a x) := by
    apply (max_le_max le_rfl (sub_le_sub_right (mul_le_mul_of_nonneg_left (hα x) hd0) _)).trans
    exact weighted_residual_bound (Finset.range R) d s hd hs r (fun a => N a x)
      (fun a ha => hr a (Finset.mem_range.mp ha)) hrs
  calc
    _ ≤ ∑ x, μ x*(∑ a∈Finset.range R, (r a/s)*φ (N a x)) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hres x) (hμ x))
    _ = ∑ a∈Finset.range R, (r a/s)*(∑ x, μ x*φ (N a x)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ ≤ ∑ a∈Finset.range R, (r a/s)*G :=
      Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hcmp a (Finset.mem_range.mp ha))
        (div_nonneg (hr a (Finset.mem_range.mp ha)) hs.le))
    _ ≤ G := by
      rw [← Finset.sum_mul,← Finset.sum_div]
      have hh := mul_le_mul_of_nonneg_right ((div_le_one hs).mpr hrs) hG
      simpa only [one_mul] using hh



lemma residual_hinge_formula (c s u : ℚ) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hu : c*s*u=c-1) (x : ℚ) : residual c (s*x)=c*s*max 0 (x-u) := by
  rw [mul_max_of_nonneg _ _ (mul_nonneg hc hs)]
  dsimp [Erdos7Distortion.residual]
  rw [mul_zero]
  congr 1
  nlinarith only [hu]

lemma residual_le_positiveCubic (c s : ℚ) (hc : 1 < c) (hs : 0 ≤ s) (x : ℚ) :
    residual c (s*x) ≤ (4*c^3/(27*(c-1)^2))*s^3*positivePower 3 x := by
  have hmono := residual_scaled_monotone c s (by linarith) hs
  apply (hmono (le_max_right 0 x)).trans
  apply (residual_le_cubic hc (mul_nonneg hs (le_max_left _ _))).trans_eq
  dsimp [positivePower]
  ring

section Residual
variable {n : ℕ} (κ : Type*) (A : Fin n → Type*)
variable [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]

lemma completeProfileBound_residual (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (μ : (∀ i,A i) → ℚ)
    (T : ℚ) (H : ℚ → ℚ) (hcomp : CompleteProfileBound κ A E c q t μ T H)
    (d s u : ℚ) (hd : 0 ≤ d) (hs : 0 ≤ s) (hu : d*s*u=d-1)
    (hu0 : 0 ≤ u) (huT : u ≤ T) :
    CompleteTestBound κ A E c q t μ 1 (fun z => residual d (s*z)) (d*s*H u) := by
  intro K e X he hX hM
  have hh := hcomp 1 u hu0 huT K e X he hX hM
  simp only [Nat.cast_one,one_mul] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg hd hs)
  rw [Finset.mul_sum] at hh'
  simp_rw [residual_hinge_formula d s u hd hs hu]
  convert hh' using 1
  apply Finset.sum_congr rfl
  intro x hx
  ring

lemma completeMomentBound_residual (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (C : ℚ) (hcomp : CompleteMomentBound κ A E c q t μ 3 C)
    (d s : ℚ) (hd : 1 < d) (hs : 0 ≤ s) :
    CompleteTestBound κ A E c q t μ 1 (fun z => residual d (s*z))
      ((4*d^3/(27*(d-1)^2))*s^3*C) := by
  intro K e X he hX hM
  have hh := hcomp 1 K e X he hX hM
  simp only [Nat.cast_one,one_pow,one_mul] at hh
  have hcoef : 0 ≤ (4*d^3/(27*(d-1)^2))*s^3 := by
    have : 0 < d := by linarith
    positivity
  have hh' := mul_le_mul_of_nonneg_left hh hcoef
  rw [Finset.mul_sum] at hh'
  apply le_trans _ hh'
  apply Finset.sum_le_sum
  intro x hx
  have hpoint := mul_le_mul_of_nonneg_left
    (residual_le_positiveCubic d s hd hs (∑ k∈K,boxIndicator A (expSupport (e k)) (X k) x)) (hμ x)
  convert hpoint using 1 <;> ring

/-- At the fixed tail cap 5/4, the cubic loss coefficient is exactly the
charge used in the wheel-2310 tail budget. -/
lemma completeMomentBound_tail_residual (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (C : ℚ) (hcomp : CompleteMomentBound κ A E c q t μ 3 C) (p : ℕ) (hp : 1 < p) :
    CompleteTestBound κ A E c q t μ 1 (fun z => residual (5/4) ((1/(p-1:ℚ))*z))
      (Erdos7CubicSieve.charge p*C) := by
  have hpQ : (1:ℚ) < p := by exact_mod_cast hp
  have hs : (0:ℚ) < p-1 := by linarith
  have hh := completeMomentBound_residual κ A E c q t μ hμ C hcomp (5/4) (1/(p-1))
    (by norm_num) (by positivity)
  convert hh using 1
  dsimp [Erdos7CubicSieve.charge]
  field_simp
  <;> ring

end Residual
#print axioms completeTestBound_layer_loss
#print axioms completeProfileBound_residual
#print axioms completeMomentBound_tail_residual
end Erdos7KilledSieve



/-! Exact-loss killed towers with an arbitrary verified invariant. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
set_option maxHeartbeats 4000000

section Tower
variable {n : ℕ} (A : Fin n → Type*)
variable [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]

/-- Losses are supplied by a certificate, rather than computed from a law. -/
def certifiedWeights (B : Fin n → Finset (∀ i,A i)) (c L : Fin n → ℚ) : ℕ → (∀ i,A i) → ℚ
  | 0 => towerWeights A B c 0
  | t+1 => if h : t < n then
      killedResample A ⟨t,h⟩ (certifiedWeights B c L t) (B ⟨t,h⟩) (c ⟨t,h⟩) (L ⟨t,h⟩)
    else certifiedWeights B c L t

theorem certifiedWeights_invariants (B : Fin n → Finset (∀ i,A i)) (c L : Fin n → ℚ)
    (hc : ∀ i,1 ≤ c i) (m : ℕ → ℚ) (hm0 : m 0=1)
    (hmsucc : ∀ i : Fin n,m (i.val+1)=m i.val-L i)
    (hmpos : ∀ t,t ≤ n → 0 ≤ m t)
    (hB : ∀ i j : Fin n,j < i → ∀ x v,Function.update x i v∈B j ↔ x∈B j)
    (I : ℕ → ((∀ i,A i) → ℚ) → Prop) (hI0 : I 0 (towerWeights A B c 0))
    (hloss : ∀ (i : Fin n) (μ : (∀ i,A i) → ℚ),
      (∀ x,0 ≤ μ x) → (∑ x,μ x)=m i.val → I i.val μ →
      (∑ x,μ x*residual (c i) (coordinateFraction A i (B i) x)) ≤ L i)
    (hstep : ∀ (i : Fin n) (μ : (∀ i,A i) → ℚ),
      (∀ x,0 ≤ μ x) → (∑ x,μ x)=m i.val → I i.val μ →
      I (i.val+1) (killedResample A i μ (B i) (c i) (L i)))
    (t : ℕ) (ht : t ≤ n) :
    (∀ x,0 ≤ certifiedWeights A B c L t x) ∧
    (∑ x,certifiedWeights A B c L t x)=m t ∧
    I t (certifiedWeights A B c L t) ∧
    (∀ j : Fin n,j.val < t → ∀ x∈B j,certifiedWeights A B c L t x=0) := by
  induction t with
  | zero =>
    refine ⟨towerWeights_nonneg A B c hc 0,?_,hI0,?_⟩
    · rw [certifiedWeights,towerWeights_total A B c hc,hm0]
    · intro j hj; omega
  | succ t ih =>
    obtain ⟨hμ,hμtot,hI,hzero⟩ := ih (by omega)
    have htn : t < n := by omega
    let i : Fin n := ⟨t,htn⟩
    let μ := certifiedWeights A B c L t
    have hsucc : certifiedWeights A B c L (t+1)=killedResample A i μ (B i) (c i) (L i) := by
      simp only [certifiedWeights,dif_pos htn,μ,i]
    have hLm : L i ≤ ∑ x,μ x := by
      have hh := hmpos (t+1) ht
      have hs := hmsucc i
      change m (t+1)=m t-L i at hs
      rw [hs] at hh
      rw [hμtot]
      linarith
    have hL := hloss i μ hμ hμtot hI
    rw [hsucc]
    refine ⟨killedResample_nonneg A i μ hμ (B i) (c i) (L i) (hc i) hLm,?_,
      hstep i μ hμ hμtot hI,?_⟩
    · rw [killedResample_total A i μ (B i) (c i) (L i) (hc i) hLm hL,hμtot]
      exact (hmsucc i).symm
    · intro j hj x hx
      by_cases hji : j=i
      · subst j
        exact killedResample_zero A i μ (B i) (c i) (L i) x hx
      · have hjt : j.val < t := by
          have hjne : j.val≠t := by intro heq; exact hji (Fin.ext heq)
          omega
        exact killedResample_preserves_zero A i μ (B i) (B j) (c i) (L i)
          (hB i j hjt) (hzero j hjt) x hx

theorem certified_tower_avoids (B : Fin n → Finset (∀ i,A i)) (c L : Fin n → ℚ)
    (hc : ∀ i,1 ≤ c i) (m : ℕ → ℚ) (hm0 : m 0=1)
    (hmsucc : ∀ i : Fin n,m (i.val+1)=m i.val-L i)
    (hmpos : ∀ t,t ≤ n → 0 ≤ m t) (hmfinal : 0 < m n)
    (hB : ∀ i j : Fin n,j < i → ∀ x v,Function.update x i v∈B j ↔ x∈B j)
    (I : ℕ → ((∀ i,A i) → ℚ) → Prop) (hI0 : I 0 (towerWeights A B c 0))
    (hloss : ∀ (i : Fin n) (μ : (∀ i,A i) → ℚ),
      (∀ x,0 ≤ μ x) → (∑ x,μ x)=m i.val → I i.val μ →
      (∑ x,μ x*residual (c i) (coordinateFraction A i (B i) x)) ≤ L i)
    (hstep : ∀ (i : Fin n) (μ : (∀ i,A i) → ℚ),
      (∀ x,0 ≤ μ x) → (∑ x,μ x)=m i.val → I i.val μ →
      I (i.val+1) (killedResample A i μ (B i) (c i) (L i))) :
    ∃ x : ∀ i,A i,∀ i,x∉B i := by
  obtain ⟨hμ,hμtot,hI,hzero⟩ := certifiedWeights_invariants A B c L hc m hm0 hmsucc hmpos hB I hI0 hloss hstep n le_rfl
  have hp : 0 < ∑ x,certifiedWeights A B c L n x := by rwa [hμtot]
  have hex : ∃ x,0 < certifiedWeights A B c L n x := by
    by_contra hh
    push_neg at hh
    exact (not_le_of_gt hp) (Finset.sum_nonpos (fun x _ => hh x))
  obtain ⟨x,hpx⟩ := hex
  refine ⟨x,fun i hi => ?_⟩
  have hz := hzero i i.isLt x hi
  rw [hz] at hpx
  exact lt_irrefl _ hpx

end Tower
#print axioms certified_tower_avoids
end Erdos7KilledSieve



/-! Chord interpolation is applied to the actual convex stop-loss function,
not to a possibly nonconvex stored upper profile. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
set_option maxHeartbeats 4000000

lemma hinge_chord_bound (x M l u v : ℚ) (hlv : l < v) (hlu : l ≤ u) (huv : u ≤ v) :
    max 0 (x-M*u) ≤ ((v-u)*max 0 (x-M*l)+(u-l)*max 0 (x-M*v))/(v-l) := by
  apply (le_div_iff₀ (sub_pos.mpr hlv)).mpr
  rw [max_mul_of_nonneg _ _ (sub_nonneg.mpr hlv.le),zero_mul]
  apply max_le
  · exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr huv) (le_max_left _ _))
      (mul_nonneg (sub_nonneg.mpr hlu) (le_max_left _ _))
  · have h1 := mul_le_mul_of_nonneg_left (le_max_right 0 (x-M*l)) (sub_nonneg.mpr huv)
    have h2 := mul_le_mul_of_nonneg_left (le_max_right 0 (x-M*v)) (sub_nonneg.mpr hlu)
    nlinarith only [h1,h2]

section Interpolate
variable {n : ℕ} (κ : Type*) (A : Fin n → Type*)
variable [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]

lemma completeTestBound_interpolate (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (M : ℕ) (l u v Hl Hv : ℚ) (hlv : l < v) (hlu : l ≤ u) (huv : u ≤ v)
    (hlo : CompleteTestBound κ A E c q t μ M (fun z => max 0 (z-(M:ℚ)*l)) ((M:ℚ)*Hl))
    (hhi : CompleteTestBound κ A E c q t μ M (fun z => max 0 (z-(M:ℚ)*v)) ((M:ℚ)*Hv)) :
    CompleteTestBound κ A E c q t μ M (fun z => max 0 (z-(M:ℚ)*u))
      ((M:ℚ)*((v-u)*Hl+(u-l)*Hv)/(v-l)) := by
  intro K e X he hX hM
  let f (x : ∀ i,A i) := ∑ k∈K,boxIndicator A (expSupport (e k)) (X k) x
  have hpoint := Finset.sum_le_sum (fun x (_ : x∈(Finset.univ:Finset (∀ i,A i))) =>
    mul_le_mul_of_nonneg_left (hinge_chord_bound (f x) M l u v hlv hlu huv) (hμ x))
  have hid : (∑ x,μ x*(((v-u)*max 0 (f x-(M:ℚ)*l)+(u-l)*max 0 (f x-(M:ℚ)*v))/(v-l))) =
      ((v-u)*(∑ x,μ x*max 0 (f x-(M:ℚ)*l))+(u-l)*(∑ x,μ x*max 0 (f x-(M:ℚ)*v)))/(v-l) := by
    simp only [← mul_div_assoc,mul_add,← Finset.sum_div,Finset.sum_add_distrib]
    rw [Finset.mul_sum,Finset.mul_sum]
    congr 2 <;> apply Finset.sum_congr rfl <;> intros <;> ring
  rw [hid] at hpoint
  apply hpoint.trans
  apply (div_le_div_of_nonneg_right (add_le_add
    (mul_le_mul_of_nonneg_left (hlo K e X he hX hM) (sub_nonneg.mpr huv))
    (mul_le_mul_of_nonneg_left (hhi K e X he hX hM) (sub_nonneg.mpr hlu)))
    (sub_nonneg.mpr hlv.le)).trans_eq
  ring

end Interpolate
#print axioms completeTestBound_interpolate
end Erdos7KilledSieve



/-! Node-wise stop-loss certificates and a finitely truncated resampling rule. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
set_option maxHeartbeats 4000000

section Grid
variable {n : ℕ} (κ : Type*) (A : Fin n → Type*)
variable [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]

def CompleteHingeBound (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (t : ℕ) (μ : (∀ i,A i) → ℚ) (u H : ℚ) : Prop :=
  ∀ M : ℕ,CompleteTestBound κ A E c q t μ M (fun z => max 0 (z-(M:ℚ)*u)) ((M:ℚ)*H)

lemma completeHingeBound_interpolate (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (l u v Hl Hv : ℚ) (hlv : l < v) (hlu : l ≤ u) (huv : u ≤ v)
    (hlo : CompleteHingeBound κ A E c q t μ l Hl)
    (hhi : CompleteHingeBound κ A E c q t μ v Hv) :
    CompleteHingeBound κ A E c q t μ u (((v-u)*Hl+(u-l)*Hv)/(v-l)) := by
  intro M
  have hh := completeTestBound_interpolate κ A E c q t μ hμ M l u v Hl Hv hlv hlu huv (hlo M) (hhi M)
  simpa only [mul_div_assoc] using hh

lemma completeHingeBound_shift (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (u v Hv m : ℚ) (hm : (∑ x,μ x)=m) (huv : u ≤ v)
    (hhi : CompleteHingeBound κ A E c q t μ v Hv) :
    CompleteHingeBound κ A E c q t μ u (Hv+(v-u)*m) := by
  intro M K e X he hX hM
  have hh := stopLoss_mass_bound μ hμ
    (fun x => ∑ k∈K,boxIndicator A (expSupport (e k)) (X k) x)
    ((M:ℚ)*u) ((M:ℚ)*v) (mul_le_mul_of_nonneg_left huv (Nat.cast_nonneg _))
  rw [hm] at hh
  apply (hh.trans (add_le_add_left (hhi M K e X he hX hM) _)).trans_eq
  ring

lemma completeHingeBound_increase_threshold (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (u v H : ℚ) (huv : u ≤ v) (hlo : CompleteHingeBound κ A E c q t μ u H) :
    CompleteHingeBound κ A E c q t μ v H := by
  intro M K e X he hX hM
  apply le_trans _ (hlo M K e X he hX hM)
  apply Finset.sum_le_sum
  intro x hx
  apply mul_le_mul_of_nonneg_left _ (hμ x)
  apply max_le_max le_rfl
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left huv (Nat.cast_nonneg _)) _

lemma completeHingeBound_mono (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (t : ℕ) (μ : (∀ i,A i) → ℚ) (u : ℚ) {H J : ℚ}
    (hh : CompleteHingeBound κ A E c q t μ u H) (hHJ : H ≤ J) :
    CompleteHingeBound κ A E c q t μ u J := by
  intro M
  exact completeTestBound_mono κ A E c q t μ M _ (hh M)
    (mul_le_mul_of_nonneg_left hHJ (Nat.cast_nonneg _))

lemma completeHingeBound_min (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (t : ℕ) (μ : (∀ i,A i) → ℚ) (u H J : ℚ)
    (hh : CompleteHingeBound κ A E c q t μ u H) (hj : CompleteHingeBound κ A E c q t μ u J) :
    CompleteHingeBound κ A E c q t μ u (min H J) := by
  intro M K e X he hX hM
  rw [mul_min_of_nonneg _ _ (Nat.cast_nonneg M)]
  exact le_min (hh M K e X he hX hM) (hj M K e X he hX hM)

lemma completeHingeBound_kill (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (t : ℕ) (i : Fin n) (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (B : Finset (∀ i,A i)) (hc : 1 ≤ c i) (L : ℚ) (hLm : L ≤ ∑ x,μ x)
    (hL : (∑ x,μ x*residual (c i) (coordinateFraction A i B x)) ≤ L)
    (u H : ℚ) (hh : CompleteHingeBound κ A E c q t (resample A i μ B (c i)) u H) :
    CompleteHingeBound κ A E c q t (killedResample A i μ B (c i) L) u H := by
  intro M
  exact completeTestBound_kill κ A E c q t i μ hμ B hc L hLm hL M _
    (fun z => le_max_left _ _) _ (hh M)

/-- Only the finitely many thresholds `u/d`, `1≤d≤R`, are requested.
All larger exponent factors use the first-moment node at zero. -/
theorem completeHingeBound_geometric_resample (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (ht : t < n)
    (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (p R : ℕ) (hp : 1 < p) (hR : 0 < R) (hRE : R ≤ E ⟨t,ht⟩)
    (hqi : q ⟨t,ht⟩=powerTail p (c ⟨t,ht⟩) (E ⟨t,ht⟩))
    (hc : 1 ≤ c ⟨t,ht⟩) (hcp : c ⟨t,ht⟩ ≤ p)
    (u H0 : ℚ) (hu : 0 ≤ u) (hH0 : 0 ≤ H0) (F : ℕ → ℚ)
    (hlocal : ∀ d,1 ≤ d → d ≤ R → CompleteHingeBound κ A E c q t μ (u/d) (F d))
    (hmean : CompleteHingeBound κ A E c q t μ 0 H0)
    (B : Finset (∀ i,A i)) :
    CompleteHingeBound κ A E c q (t+1) (resample A ⟨t,ht⟩ μ B (c ⟨t,ht⟩)) u
      ((1-c ⟨t,ht⟩/(p:ℚ))*F 1+
        (∑ g∈Finset.range (R-1),c ⟨t,ht⟩*(p-1)*((p:ℚ)⁻¹)^(g+2)*(g+2)*F (g+2))+
        c ⟨t,ht⟩*((p:ℚ)⁻¹)^R*((R+1)+1/(p-1))*H0) := by
  let i : Fin n := ⟨t,ht⟩
  change R ≤ E i at hRE
  have hc0 : 0 ≤ c i := (by norm_num : (0:ℚ) ≤ 1).trans hc
  let f (d : ℕ) : ℚ := if d ≤ R then F d else H0
  intro M
  let G (a : ℕ) : ℚ := (((a+1)*M:ℕ):ℚ)*f (a+1)
  have hbound (a : ℕ) (ha : a ≤ E i) :
      CompleteTestBound κ A E c q t μ ((a+1)*M) (fun z => max 0 (z-(M:ℚ)*u)) (G a) := by
    have ha0 : (0:ℚ) < a+1 := by positivity
    have hscalar : (((a+1)*M:ℕ):ℚ)*(u/(a+1))=(M:ℚ)*u := by
      push_cast
      field_simp
      <;> ring
    by_cases har : a+1 ≤ R
    · have hh := hlocal (a+1) (by omega) har ((a+1)*M)
      simpa only [Nat.cast_add,Nat.cast_one,hscalar,G,f,if_pos har] using hh
    · have hh := completeHingeBound_increase_threshold κ A E c q t μ hμ 0 (u/(a+1)) H0
        (div_nonneg hu ha0.le) hmean ((a+1)*M)
      simpa only [hscalar,G,f,if_neg har] using hh
  have hh := completeTestBound_resample κ A E c q t ht μ hμ M
    (fun z => max 0 (z-(M:ℚ)*u))
    (by simpa only [one_mul,sub_eq_add_neg] using hinge_convex 1 (-((M:ℚ)*u)))
    (by intro x y hxy; exact max_le_max le_rfl (sub_le_sub_right hxy _)) G hbound B hc
    (by rw [hqi]; exact powerTail_zero_le_one p hp (c i) hcp (E i))
    (by intro g hg; rw [hqi]; exact powerTail_decreasing p hp (c i) hc0 (E i) g)
    (by rw [hqi]; exact powerTail_terminal p (c i) (E i))
  apply completeTestBound_mono κ A E c q (t+1) _ M _ hh
  have hid : (1-q i 0)*G 0+(∑ g∈Finset.range (E i),(q i g-q i (g+1))*G (g+1)) =
      (M:ℚ)*((1-q i 0)*f 1+∑ g∈Finset.range (E i),(q i g-q i (g+1))*(g+2)*f (g+2)) := by
    simp only [G,Nat.zero_add,Nat.one_mul,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.add_assoc]
    rw [mul_add,Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro g hg
      ring_nf
  rw [hid,hqi]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg M)
  have htail := geometricMixture_truncate p (E i) (R-1) hp (by omega) (c i) hc0 f H0 hH0 (by
    intro g hg
    have hgr : ¬g+2 ≤ R := by have := (Finset.mem_Ico.mp hg).1; omega
    simp only [f,if_neg hgr,le_refl])
  apply htail.trans_eq
  have hR1 : R-1+1=R := by omega
  have hR2 : (R-1:ℕ)+2=R+1 := by omega
  simp only [hR1,f,if_pos (by omega : 1 ≤ R)]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro g hg
    rw [if_pos (by have := Finset.mem_range.mp hg; omega : g+2 ≤ R)]
  · have heq : ((R-1:ℕ):ℚ)+2=(R:ℚ)+1 := by exact_mod_cast hR2
    rw [heq]

end Grid
#print axioms completeHingeBound_geometric_resample
end Erdos7KilledSieve



/-! Positive-operator binomial truncation bounds for grouped sieve steps. -/
namespace Erdos7KilledSieve
open scoped BigOperators
set_option maxHeartbeats 4000000

lemma geometric_sum_Ico_le (r : ℚ) (hr0 : 0 ≤ r) (hr : r < 1) (a b : ℕ) :
    (∑ j∈Finset.Ico a b,r^j) ≤ r^a/(1-r) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp_rw [pow_add]
  rw [← Finset.mul_sum]
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
    (geometric_sum_zero_le r hr0 hr (b-a)) (pow_nonneg hr0 a)

lemma choose_term_le_geometric (k j : ℕ) (α β H0 F : ℚ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ : 0 ≤ β) (hH0 : 0 ≤ H0)
    (hF : F ≤ β^j*H0) :
    (k.choose j:ℚ)*α^(k-j)*F ≤ ((k:ℚ)*β)^j*H0 := by
  have hcoef : 0 ≤ (k.choose j:ℚ)*α^(k-j) := by positivity
  apply (mul_le_mul_of_nonneg_left hF hcoef).trans
  have hc : (k.choose j:ℚ) ≤ (k:ℚ)^j := by exact_mod_cast Nat.choose_le_pow k j
  have ha := pow_le_one₀ hα0 hα1 (n := k-j)
  have hprod := mul_le_mul hc ha (pow_nonneg hα0 _) (pow_nonneg (Nat.cast_nonneg _) _)
  have hh := mul_le_mul_of_nonneg_right hprod (mul_nonneg (pow_nonneg hβ j) hH0)
  convert hh using 1 <;> simp only [mul_pow] <;> ring

/-- The finite binomial expansion can be truncated at any degree, with a
uniform geometric bound for all remaining terms. -/
theorem binomial_truncation_bound (k r : ℕ) (α β H0 : ℚ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ : 0 ≤ β) (hH0 : 0 ≤ H0)
    (hsmall : (k:ℚ)*β < 1) (F : ℕ → ℚ)
    (hF : ∀ j,F j ≤ β^j*H0) :
    (∑ j∈Finset.range (k+1),(k.choose j:ℚ)*α^(k-j)*F j) ≤
      (∑ j∈Finset.range r,(k.choose j:ℚ)*α^(k-j)*F j)+
      (((k:ℚ)*β)^r/(1-(k:ℚ)*β))*H0 := by
  by_cases hkr : r ≤ k+1
  · rw [← Finset.sum_range_add_sum_Ico _ hkr]
    apply add_le_add_right
    calc
      _ ≤ ∑ j∈Finset.Ico r (k+1),((k:ℚ)*β)^j*H0 :=
        Finset.sum_le_sum (fun j hj => choose_term_le_geometric k j α β H0 (F j) hα0 hα1 hβ hH0 (hF j))
      _ = (∑ j∈Finset.Ico r (k+1),((k:ℚ)*β)^j)*H0 := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (geometric_sum_Ico_le ((k:ℚ)*β) (mul_nonneg (Nat.cast_nonneg _) hβ) hsmall r (k+1)) hH0
  · have hk : k+1 ≤ r := by omega
    have heq : (∑ j∈Finset.range r,(k.choose j:ℚ)*α^(k-j)*F j)=
        ∑ j∈Finset.range (k+1),(k.choose j:ℚ)*α^(k-j)*F j := by
      rw [← Finset.sum_range_add_sum_Ico _ hk]
      have hz : (∑ j∈Finset.Ico (k+1) r,(k.choose j:ℚ)*α^(k-j)*F j)=0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hkj : k < j := (Finset.mem_Ico.mp hj).1
        rw [Nat.choose_eq_zero_of_lt hkj,Nat.cast_zero,zero_mul,zero_mul]
      rw [hz,add_zero]
    rw [heq]
    have hd : (0:ℚ) < 1-(k:ℚ)*β := sub_pos.mpr hsmall
    exact le_add_of_nonneg_right (by positivity)

lemma binomial_truncation_small (k r : ℕ) (hkr : k < r) (α : ℚ) (F : ℕ → ℚ) :
    (∑ j∈Finset.range (k+1),(k.choose j:ℚ)*α^(k-j)*F j)=
      ∑ j∈Finset.range r,(k.choose j:ℚ)*α^(k-j)*F j := by
  rw [← Finset.sum_range_add_sum_Ico _ hkr]
  have hz : (∑ j∈Finset.Ico (k+1) r,(k.choose j:ℚ)*α^(k-j)*F j)=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hkj : k < j := (Finset.mem_Ico.mp hj).1
    rw [Nat.choose_eq_zero_of_lt hkj,Nat.cast_zero,zero_mul,zero_mul]
  rw [hz,add_zero]

section Operator
variable {ι : Type*}

lemma positive_operator_pow_bound (T : Module.End ℚ (ι → ℚ))
    (hT : Monotone T) (β : ℚ) (hβ : 0 ≤ β)
    (hone : T (fun _ => 1) ≤ fun _ => β)
    (H : ι → ℚ) (H0 : ℚ) (hH0 : 0 ≤ H0) (hH : H ≤ fun _ => H0) (j : ℕ) :
    (T^j) H ≤ fun _ => β^j*H0 := by
  induction j with
  | zero => simpa using hH
  | succ j ih =>
    rw [pow_succ',Module.End.mul_apply]
    apply (hT ih).trans
    have hid : (fun _ : ι => β^j*H0)=(β^j*H0) • (fun _ : ι => (1:ℚ)) := by ext; simp
    rw [hid,map_smul]
    intro i
    have hh := mul_le_mul_of_nonneg_left (hone i) (mul_nonneg (pow_nonneg hβ j) hH0)
    simpa only [Pi.smul_apply,smul_eq_mul,pow_succ,mul_assoc,mul_comm,mul_left_comm] using hh

/-- Exact binomial formula for a scalar identity plus an arbitrary linear
operator. No norm or positivity assumption is needed for this identity. -/
lemma scalar_add_operator_pow (T : Module.End ℚ (ι → ℚ)) (α : ℚ)
    (H : ι → ℚ) (k : ℕ) (i : ι) :
    ((α • (1:Module.End ℚ (ι → ℚ))+T)^k) H i =
      ∑ j∈Finset.range (k+1),(k.choose j:ℚ)*α^(k-j)*((T^j) H i) := by
  have hc : Commute T (α • (1:Module.End ℚ (ι → ℚ))) := (Commute.one_right T).smul_right α
  rw [add_comm, hc.add_pow,LinearMap.sum_apply,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Module.End.mul_apply,Module.End.natCast_apply,Module.End.mul_apply,smul_pow,one_pow,
    LinearMap.smul_apply,Module.End.one_apply,map_smul,map_nsmul]
  simp only [Pi.smul_apply,smul_eq_mul]
  simp only [nsmul_eq_mul]
  ring

theorem positive_operator_truncation (T : Module.End ℚ (ι → ℚ))
    (hT : Monotone T) (α β H0 : ℚ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hβ : 0 ≤ β) (hH0 : 0 ≤ H0) (hone : T (fun _ => 1) ≤ fun _ => β)
    (H : ι → ℚ) (hH : H ≤ fun _ => H0) (k r : ℕ) (hsmall : (k:ℚ)*β < 1) (i : ι) :
    ((α • (1:Module.End ℚ (ι → ℚ))+T)^k) H i ≤
      (∑ j∈Finset.range r,(k.choose j:ℚ)*α^(k-j)*((T^j) H i))+
      (((k:ℚ)*β)^r/(1-(k:ℚ)*β))*H0 := by
  rw [scalar_add_operator_pow]
  apply binomial_truncation_bound k r α β H0 hα0 hα1 hβ hH0 hsmall
  intro j
  exact positive_operator_pow_bound T hT β hβ hone H H0 hH0 hH j i

end Operator
#print axioms binomial_truncation_bound
#print axioms positive_operator_truncation
end Erdos7KilledSieve



/-! Monotone prime coefficients and the exact norm of a truncated operator. -/
namespace Erdos7KilledSieve
open scoped BigOperators
set_option maxHeartbeats 4000000

lemma quadratic_fraction_antitone (n p : ℚ) (hn : 2 ≤ n) (hnp : n ≤ p) :
    (p-1)/p^2 ≤ (n-1)/n^2 := by
  have hn0 : 0 < n := by linarith
  have hp0 : 0 < p := by linarith
  apply (div_le_div_iff₀ (sq_pos_of_pos hp0) (sq_pos_of_pos hn0)).mpr
  have h1 : 0 ≤ n*p-p-n := by nlinarith [mul_nonneg (by linarith : 0 ≤ n-2) (by linarith : 0 ≤ p-2)]
  have h2 := mul_nonneg (sub_nonneg.mpr hnp) h1
  nlinarith only [h2]

lemma geometric_coefficient_antitone (n p g : ℕ) (hn : 2 ≤ n) (hnp : n ≤ p) :
    ((p:ℚ)-1)*((p:ℚ)⁻¹)^(g+2) ≤ ((n:ℚ)-1)*((n:ℚ)⁻¹)^(g+2) := by
  have hnQ : (2:ℚ) ≤ n := by exact_mod_cast hn
  have hnpQ : (n:ℚ) ≤ p := by exact_mod_cast hnp
  have hn0 : (0:ℚ) < n := by linarith
  have hp0 : (0:ℚ) < p := by linarith
  have hp1 : (0:ℚ) < p-1 := by linarith
  have hn1 : (0:ℚ) < n-1 := by linarith
  have hsmall : ((p:ℚ)-1)/(p:ℚ)^2 ≤ ((n:ℚ)-1)/(n:ℚ)^2 :=
    quadratic_fraction_antitone n p hnQ hnpQ
  have hpow : ((p:ℚ)⁻¹)^g ≤ ((n:ℚ)⁻¹)^g := by gcongr
  have hh := mul_le_mul hsmall hpow (by positivity)
    (by positivity : 0 ≤ ((n:ℚ)-1)/(n:ℚ)^2)
  convert hh using 1 <;> simp only [pow_add,div_eq_mul_inv,inv_pow] <;> ring

lemma geometric_tail_mean_antitone (n p R : ℕ) (hn : 2 ≤ n) (hnp : n ≤ p) (c : ℚ) (hc : 0 ≤ c) :
    c*((p:ℚ)⁻¹)^R*((R+1)+1/(p-1)) ≤ c*((n:ℚ)⁻¹)^R*((R+1)+1/(n-1)) := by
  have hnQ : (2:ℚ) ≤ n := by exact_mod_cast hn
  have hnpQ : (n:ℚ) ≤ p := by exact_mod_cast hnp
  have hn0 : (0:ℚ) < n := by linarith
  have hn1 : (0:ℚ) < n-1 := by linarith
  have hp0 : (0:ℚ) < p := by linarith
  have hp1 : (0:ℚ) < p-1 := by linarith
  gcongr

lemma cubic_fraction_partial (p : ℚ) (hp : 1 < p) :
    (7*p^2-2*p+1)/(p-1)^3=7/(p-1)+12/(p-1)^2+6/(p-1)^3 := by
  have hne : p-1≠0 := by linarith
  field_simp
  <;> ring

lemma cubic_fraction_antitone (n p : ℚ) (hn : 1 < n) (hnp : n ≤ p) :
    (7*p^2-2*p+1)/(p-1)^3 ≤ (7*n^2-2*n+1)/(n-1)^3 := by
  rw [cubic_fraction_partial p (hn.trans_le hnp),cubic_fraction_partial n hn]
  have hn1 : 0 < n-1 := by linarith
  gcongr

/-- The total first-moment mass of all factors at least two. -/
def geometricMeanNorm (p : ℕ) (c : ℚ) : ℚ := c*(2*(p:ℚ)-1)/((p:ℚ)*(p-1))

lemma geometricMeanTail_step (p a : ℕ) (hp : 1 < p) (c : ℚ) :
    c*((p:ℚ)⁻¹)^(a+1)*((a+2)+1/(p-1)) =
      c*(p-1)*((p:ℚ)⁻¹)^(a+2)*(a+2)+c*((p:ℚ)⁻¹)^(a+2)*((a+3)+1/(p-1)) := by
  have hpQ : (1:ℚ) < p := by exact_mod_cast hp
  have hp0 : (p:ℚ)≠0 := by linarith
  have hp1 : (p:ℚ)-1≠0 := by linarith
  simp only [pow_succ]
  field_simp
  <;> ring

lemma geometric_truncated_mean (p a : ℕ) (hp : 1 < p) (c : ℚ) :
    (∑ g∈Finset.range a,c*(p-1)*((p:ℚ)⁻¹)^(g+2)*(g+2))+
      c*((p:ℚ)⁻¹)^(a+1)*((a+2)+1/(p-1))=geometricMeanNorm p c := by
  induction a with
  | zero =>
    have hpQ : (1:ℚ) < p := by exact_mod_cast hp
    have hp0 : (p:ℚ)≠0 := by linarith
    have hp1 : (p:ℚ)-1≠0 := by linarith
    simp only [Finset.sum_range_zero,zero_add,pow_one,Nat.cast_zero]
    dsimp [geometricMeanNorm]
    field_simp
    <;> ring
  | succ a ih =>
    rw [Finset.sum_range_succ]
    have hh := geometricMeanTail_step p a hp c
    simp only [Nat.cast_add,Nat.cast_one] at *
    convert ih using 1
    linarith only [hh]

#print axioms geometric_coefficient_antitone
#print axioms geometric_truncated_mean
end Erdos7KilledSieve



/-! Positive interpolation operators on a finite grid. -/
namespace Erdos7KilledSieve
open scoped BigOperators
set_option maxHeartbeats 4000000

section Geometry
variable {m : ℕ}

def gridChord (G : Fin m → ℚ) (l r : Fin m) (u : ℚ) (H : Fin m → ℚ) : ℚ :=
  ((G r-u)*H l+(u-G l)*H r)/(G r-G l)

lemma gridChord_nonneg (G : Fin m → ℚ) (l r : Fin m) (u : ℚ) (H : Fin m → ℚ)
    (hlr : G l < G r) (hlu : G l ≤ u) (hur : u ≤ G r) (hH : ∀ j,0 ≤ H j) :
    0 ≤ gridChord G l r u H := by
  exact div_nonneg (add_nonneg
    (mul_nonneg (sub_nonneg.mpr hur) (hH l))
    (mul_nonneg (sub_nonneg.mpr hlu) (hH r))) (sub_nonneg.mpr hlr.le)

lemma gridChord_mono (G : Fin m → ℚ) (l r : Fin m) (u : ℚ)
    (hlr : G l < G r) (hlu : G l ≤ u) (hur : u ≤ G r) :
    Monotone (gridChord G l r u) := by
  intro H J hHJ
  exact div_le_div_of_nonneg_right (add_le_add
    (mul_le_mul_of_nonneg_left (hHJ l) (sub_nonneg.mpr hur))
    (mul_le_mul_of_nonneg_left (hHJ r) (sub_nonneg.mpr hlu))) (sub_nonneg.mpr hlr.le)

lemma gridChord_one (G : Fin m → ℚ) (l r : Fin m) (u : ℚ) (hlr : G l < G r) :
    gridChord G l r u (fun _ => 1)=1 := by
  unfold gridChord
  have hd : G r-G l≠0 := sub_ne_zero.mpr (ne_of_gt hlr)
  field_simp
  <;> ring

lemma gridChord_add (G : Fin m → ℚ) (l r : Fin m) (u : ℚ) (H J : Fin m → ℚ) :
    gridChord G l r u (H+J)=gridChord G l r u H+gridChord G l r u J := by
  dsimp [gridChord]
  ring

lemma gridChord_smul (G : Fin m → ℚ) (l r : Fin m) (u d : ℚ) (H : Fin m → ℚ) :
    gridChord G l r u (d • H)=d*gridChord G l r u H := by
  dsimp [gridChord]
  ring

/-- Positive off-diagonal part of a finite geometric grid update.
`a+1` is the largest explicitly retained multiplicative factor. -/
noncomputable def geometricGridOperator (G : Fin m → ℚ) (z : Fin m)
    (lo hi : ℕ → Fin m → Fin m) (p a : ℕ) (c : ℚ) : Module.End ℚ (Fin m → ℚ) where
  toFun H j := (∑ g∈Finset.range a,c*(p-1)*((p:ℚ)⁻¹)^(g+2)*(g+2)*
    gridChord G (lo g j) (hi g j) (G j/(g+2)) H)+
    c*((p:ℚ)⁻¹)^(a+1)*((a+2)+1/(p-1))*H z
  map_add' H J := by
    ext j
    simp only [gridChord_add,Pi.add_apply,mul_add,Finset.sum_add_distrib]
    ring
  map_smul' r H := by
    ext j
    simp only [gridChord_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp only [mul_add,Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro g hg
      ring
    · ring

lemma geometricGridOperator_monotone (G : Fin m → ℚ) (z : Fin m)
    (lo hi : ℕ → Fin m → Fin m) (p a : ℕ) (hp : 1 < p) (c : ℚ) (hc : 0 ≤ c)
    (hgeometry : ∀ g,g < a → ∀ j,G (lo g j) < G (hi g j) ∧
      G (lo g j) ≤ G j/(g+2) ∧ G j/(g+2) ≤ G (hi g j)) :
    Monotone (geometricGridOperator G z lo hi p a c) := by
  intro H J hHJ j
  have hpQ : (1:ℚ) < p := by exact_mod_cast hp
  have hp1 : (0:ℚ) < p-1 := by linarith
  apply add_le_add
  · apply Finset.sum_le_sum
    intro g hg
    obtain ⟨hlr,hlu,hur⟩ := hgeometry g (Finset.mem_range.mp hg) j
    exact mul_le_mul_of_nonneg_left (gridChord_mono G _ _ _ hlr hlu hur hHJ) (by positivity)
  · exact mul_le_mul_of_nonneg_left (hHJ z) (by positivity)

lemma geometricGridOperator_one (G : Fin m → ℚ) (z : Fin m)
    (lo hi : ℕ → Fin m → Fin m) (p a : ℕ) (hp : 1 < p) (c : ℚ)
    (hgeometry : ∀ g,g < a → ∀ j,G (lo g j) < G (hi g j)) :
    geometricGridOperator G z lo hi p a c (fun _ => 1)=fun _ => geometricMeanNorm p c := by
  ext j
  change (∑ g∈Finset.range a,c*(p-1)*((p:ℚ)⁻¹)^(g+2)*(g+2)*
      gridChord G (lo g j) (hi g j) (G j/(g+2)) (fun _ => 1))+
      c*((p:ℚ)⁻¹)^(a+1)*((a+2)+1/(p-1))*1=geometricMeanNorm p c
  have heq : (∑ g∈Finset.range a,c*(p-1)*((p:ℚ)⁻¹)^(g+2)*(g+2)*
      gridChord G (lo g j) (hi g j) (G j/(g+2)) (fun _ => 1))=
      ∑ g∈Finset.range a,c*(p-1)*((p:ℚ)⁻¹)^(g+2)*(g+2) := by
    apply Finset.sum_congr rfl
    intro g hg
    rw [gridChord_one _ _ _ _ (hgeometry g (Finset.mem_range.mp hg) j),mul_one]
  rw [heq,mul_one]
  exact geometric_truncated_mean p a hp c

end Geometry
#print axioms geometricGridOperator_monotone
#print axioms geometricGridOperator_one
end Erdos7KilledSieve



/-! Uniform block majorants for actual complete-family resampling. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
set_option maxHeartbeats 4000000

section Grid
variable {n m : ℕ} (κ : Type*) (A : Fin n → Type*)
variable [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]

def CompleteGridBound (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (t : ℕ) (μ : (∀ i,A i) → ℚ) (G H : Fin m → ℚ) : Prop :=
  ∀ j,CompleteHingeBound κ A E c q t μ (G j) (H j)

lemma completeGridBound_chord (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (t : ℕ) (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x) (G H : Fin m → ℚ)
    (hh : CompleteGridBound κ A E c q t μ G H)
    (l r : Fin m) (u : ℚ) (hlr : G l < G r) (hlu : G l ≤ u) (hur : u ≤ G r) :
    CompleteHingeBound κ A E c q t μ u (gridChord G l r u H) :=
  completeHingeBound_interpolate κ A E c q t μ hμ (G l) u (G r) (H l) (H r)
    hlr hlu hur (hh l) (hh r)

lemma completeGridBound_mono (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (t : ℕ) (μ : (∀ i,A i) → ℚ) (G H J : Fin m → ℚ)
    (hh : CompleteGridBound κ A E c q t μ G H) (hHJ : H ≤ J) :
    CompleteGridBound κ A E c q t μ G J := by
  intro j
  exact completeHingeBound_mono κ A E c q t μ (G j) (hh j) (hHJ j)

lemma completeGridBound_kill (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (t : ℕ) (i : Fin n) (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (B : Finset (∀ i,A i)) (hc : 1 ≤ c i) (L : ℚ) (hLm : L ≤ ∑ x,μ x)
    (hL : (∑ x,μ x*residual (c i) (coordinateFraction A i B x)) ≤ L)
    (G H : Fin m → ℚ) (hh : CompleteGridBound κ A E c q t (resample A i μ B (c i)) G H) :
    CompleteGridBound κ A E c q t (killedResample A i μ B (c i) L) G H := by
  intro j
  exact completeHingeBound_kill κ A E c q t i μ hμ B hc L hLm hL (G j) (H j) (hh j)

lemma completeGridBound_prune (E : Fin n → ℕ) (c : Fin n → ℚ) (q : Fin n → ℕ → ℚ)
    (t : ℕ) (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (G H : Fin m → ℚ) (hh : CompleteGridBound κ A E c q t μ G H)
    (mass : ℚ) (hm : (∑ x,μ x)=mass) (b : Fin m) :
    CompleteGridBound κ A E c q t μ G
      (fun j => if G j ≤ G b then min (H j) (H b+(G b-G j)*mass) else H j) := by
  intro j
  dsimp only
  by_cases hj : G j ≤ G b
  · rw [if_pos hj]
    exact completeHingeBound_min κ A E c q t μ (G j) (H j) _ (hh j)
      (completeHingeBound_shift κ A E c q t μ hμ (G j) (G b) (H b) mass hm hj (hh b))
  · simpa only [if_neg hj] using hh j

lemma completeHingeBound_residual (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (μ : (∀ i,A i) → ℚ) (u H : ℚ)
    (hh : CompleteHingeBound κ A E c q t μ u H)
    (d s : ℚ) (hd : 0 ≤ d) (hs : 0 ≤ s) (hu : d*s*u=d-1) :
    CompleteTestBound κ A E c q t μ 1 (fun z => residual d (s*z)) (d*s*H) := by
  intro K e X he hX hM
  have htest := hh 1 K e X he hX hM
  simp only [Nat.cast_one,one_mul] at htest
  have hbound := mul_le_mul_of_nonneg_left htest (mul_nonneg hd hs)
  rw [Finset.mul_sum] at hbound
  simp_rw [residual_hinge_formula d s u hd hs hu]
  convert hbound using 1
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- A single actual prime may be replaced by the same positive operator
throughout a prime block. The scalar `alpha` controls its diagonal term. -/
theorem completeGridBound_resample_majorant (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (ht : t < n)
    (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (G H : Fin m → ℚ) (hG : ∀ j,0 ≤ G j) (hH : ∀ j,0 ≤ H j)
    (hcomp : CompleteGridBound κ A E c q t μ G H)
    (z : Fin m) (hz : G z=0) (lo hi : ℕ → Fin m → Fin m)
    (pmin p a : ℕ) (hn : 2 ≤ pmin) (hnp : pmin ≤ p) (haE : a+1 ≤ E ⟨t,ht⟩)
    (hgeometry : ∀ g,g < a → ∀ j,G (lo g j) < G (hi g j) ∧
      G (lo g j) ≤ G j/(g+2) ∧ G j/(g+2) ≤ G (hi g j))
    (hqi : q ⟨t,ht⟩=powerTail p (c ⟨t,ht⟩) (E ⟨t,ht⟩))
    (hc : 1 ≤ c ⟨t,ht⟩) (hcp : c ⟨t,ht⟩ ≤ p)
    (alpha : ℚ) (halpha : 1-c ⟨t,ht⟩/(p:ℚ) ≤ alpha)
    (B : Finset (∀ i,A i)) :
    CompleteGridBound κ A E c q (t+1) (resample A ⟨t,ht⟩ μ B (c ⟨t,ht⟩)) G
      (fun j => alpha*H j+geometricGridOperator G z lo hi pmin a (c ⟨t,ht⟩) H j) := by
  let i : Fin n := ⟨t,ht⟩
  have hp : 1 < p := by omega
  have hc0 : 0 ≤ c i := (by norm_num : (0:ℚ) ≤ 1).trans hc
  have hmean : CompleteHingeBound κ A E c q t μ 0 (H z) := by simpa only [hz] using hcomp z
  intro j
  let F (d : ℕ) : ℚ := if d=1 then H j else
    gridChord G (lo (d-2) j) (hi (d-2) j) (G j/d) H
  have hlocal (d : ℕ) (hd1 : 1 ≤ d) (hda : d ≤ a+1) :
      CompleteHingeBound κ A E c q t μ (G j/d) (F d) := by
    by_cases hd : d=1
    · subst d
      simpa only [F,if_pos rfl,Nat.cast_one,div_one] using hcomp j
    · have hd2 : d-2+2=d := by omega
      have hg : d-2 < a := by omega
      obtain ⟨hlr,hlu,hur⟩ := hgeometry (d-2) hg j
      have hcast : ((d-2:ℕ):ℚ)+2=(d:ℚ) := by exact_mod_cast hd2
      rw [hcast] at hlu hur
      simpa only [F,if_neg hd] using
        completeGridBound_chord κ A E c q t μ hμ G H hcomp (lo (d-2) j) (hi (d-2) j) (G j/d) hlr hlu hur
  have hh := completeHingeBound_geometric_resample κ A E c q t ht μ hμ p (a+1) hp (by omega) haE
    hqi hc hcp (G j) (H z) (hG j) (hH z) F hlocal hmean B
  apply completeHingeBound_mono κ A E c q (t+1) _ (G j) hh
  have hF1 : F 1=H j := by simp only [F,if_pos rfl]
  have hFg (g : ℕ) : F (g+2)=gridChord G (lo g j) (hi g j) (G j/(g+2)) H := by
    simp only [F,if_neg (by omega : g+2≠1),Nat.add_sub_cancel,Nat.cast_add,Nat.cast_ofNat]
  simp only [Nat.add_sub_cancel,hF1,hFg,Nat.cast_add,Nat.cast_one]
  change ((1-c i/(p:ℚ))*H j+
    (∑ g∈Finset.range a,c i*(p-1)*((p:ℚ)⁻¹)^(g+2)*(g+2)*
      gridChord G (lo g j) (hi g j) (G j/(g+2)) H))+
      c i*((p:ℚ)⁻¹)^(a+1)*(((a:ℚ)+1+1)+1/(p-1))*H z ≤
    alpha*H j+((∑ g∈Finset.range a,c i*(pmin-1)*((pmin:ℚ)⁻¹)^(g+2)*(g+2)*
      gridChord G (lo g j) (hi g j) (G j/(g+2)) H)+
      c i*((pmin:ℚ)⁻¹)^(a+1)*((a+2)+1/(pmin-1))*H z)
  have h0 := mul_le_mul_of_nonneg_right halpha (hH j)
  have hsum : (∑ g∈Finset.range a,c i*(p-1)*((p:ℚ)⁻¹)^(g+2)*(g+2)*
      gridChord G (lo g j) (hi g j) (G j/(g+2)) H) ≤
    ∑ g∈Finset.range a,c i*(pmin-1)*((pmin:ℚ)⁻¹)^(g+2)*(g+2)*
      gridChord G (lo g j) (hi g j) (G j/(g+2)) H := by
    apply Finset.sum_le_sum
    intro g hg
    obtain ⟨hlr,hlu,hur⟩ := hgeometry g (Finset.mem_range.mp hg) j
    have hF := gridChord_nonneg G _ _ _ H hlr hlu hur hH
    have hc' := mul_le_mul_of_nonneg_left (geometric_coefficient_antitone pmin p g hn hnp) hc0
    have hd' := mul_le_mul_of_nonneg_right hc' (by positivity : (0:ℚ) ≤ g+2)
    have hv := mul_le_mul_of_nonneg_right hd' hF
    simpa only [mul_assoc] using hv
  have htail := mul_le_mul_of_nonneg_right
    (geometric_tail_mean_antitone pmin p (a+1) hn hnp (c i) hc0) (hH z)
  simp only [Nat.cast_add,Nat.cast_one] at htail
  linarith only [h0,hsum,htail]

end Grid
#print axioms completeGridBound_resample_majorant
end Erdos7KilledSieve



/-! Complete-pattern avoidance with a certified arbitrary invariant. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
open Erdos7BinarySieve (expect)
set_option maxHeartbeats 4000000

/-- Any verified test-bound invariant with an exact positive mass schedule
rules out a complete nonzero exponent-pattern cover. -/
theorem complete_box_certified_avoidance {n : ℕ} {κ : Type*} [Fintype κ]
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (E : Fin n → ℕ) (hE : ∀ i, 0 < E i) (c s : Fin n → ℚ) (r q : Fin n → ℕ → ℚ)
    (hc : ∀ i, 1 ≤ c i) (hs : ∀ i, 0 < s i)
    (hr : ∀ i g, g < E i → 0 ≤ r i (g+1))
    (hrs : ∀ i, (∑ g∈Finset.range (E i),r i (g+1)) ≤ s i)
    (hq1 : ∀ i, q i 0 ≤ 1) (hqdec : ∀ i g, g < E i → q i (g+1) ≤ q i g)
    (hqE : ∀ i, q i (E i)=0) (hqr : ∀ i g, g < E i → c i*r i (g+1) ≤ q i g)
    (e : κ → Fin n → ℕ) (heinj : Function.Injective e)
    (he : ∀ k i, e k i ≤ E i) (hne : ∀ k, (expSupport (e k)).Nonempty)
    (hfull : ∀ f : Fin n → ℕ, (∀ i, f i ≤ E i) → (∃ i, f i≠0) → ∃ k, e k=f)
    (X : κ → ∀ i, Finset (A i))
    (hX : ∀ k i, e k i≠0 → fraction (X k i) ≤ r i (e k i))
    (L : Fin n → ℚ) (m : ℕ → ℚ) (hm0 : m 0=1)
    (hmsucc : ∀ i : Fin n,m (i.val+1)=m i.val-L i)
    (hmpos : ∀ t,t ≤ n → 0 ≤ m t) (hmfinal : 0 < m n)
    (I : ℕ → ((∀ i,A i) → ℚ) → Prop)
    (hI0 : ∀ B : Fin n → Finset (∀ i,A i),I 0 (towerWeights A B c 0))
    (htest : ∀ (i : Fin n) (μ : (∀ i,A i) → ℚ),
      (∀ x,0 ≤ μ x) → (∑ x,μ x)=m i.val → I i.val μ →
      CompleteTestBound κ A E c q i.val μ 1 (fun z => residual (c i) (s i*z)) (L i))
    (hstep : ∀ (i : Fin n) (μ : (∀ i,A i) → ℚ) (B : Finset (∀ i,A i)),
      (∀ x,0 ≤ μ x) → (∑ x,μ x)=m i.val → I i.val μ →
      (∑ x,μ x*residual (c i) (coordinateFraction A i B x)) ≤ L i →
      I (i.val+1) (killedResample A i μ B (c i) (L i))) :
    ∃ x : ∀ i, A i, ∀ k, ¬ (∀ i∈expSupport (e k), x i∈X k i) := by
  classical
  let S (k : κ) := expSupport (e k)
  let σ (k : κ) := (S k).max' (hne k)
  have hσ (k : κ) : σ k∈S k := Finset.max'_mem _ _
  have hS (k : κ) (j : Fin n) (hj : j∈S k) : j ≤ σ k := Finset.le_max' _ _ hj
  let B := layeredBad A S X σ
  have hB : ∀ i j : Fin n, j < i → ∀ x v, Function.update x i v∈B j ↔ x∈B j := by
    intro i j hji x v
    exact layeredBad_invariant A S X σ hS i j hji x v
  have hc0 : ∀ i, 0 ≤ c i := fun i => (by norm_num : (0:ℚ) ≤ 1).trans (hc i)
  have horacle (i : Fin n) (μ : (∀ j,A j) → ℚ)
      (hμ : ∀ x,0 ≤ μ x) (hμtot : (∑ x,μ x)=m i.val) (hI : I i.val μ) :
      (∑ x,μ x*residual (c i) (coordinateFraction A i (B i) x)) ≤ L i := by
    have hcomp := htest i μ hμ hμtot hI
    let K := layerFamily σ i
    let Kg (g : ℕ) := K.filter (fun k => e k i=g+1)
    let e' (k : κ) := Function.update (e k) i 0
    let W (k : κ) (x : ∀ j, A j) := boxIndicator A (expSupport (e' k)) (X k) x
    let N (g : ℕ) (x : ∀ j, A j) := ∑ k∈Kg g, W k x
    have hki (k : κ) (hk : k∈K) : i∈S k := by
      simpa only [(Finset.mem_filter.mp hk).2] using hσ k
    have he' (k : κ) (hk : k∈K) : PrefixPattern E i.val (e' k) := by
      constructor
      · intro j
        by_cases hj : j=i
        · subst j; simp [e']
        · simpa only [e',Function.update_of_ne hj] using he k j
      · intro j hj
        by_cases hji : j=i
        · subst j; simp [e']
        · have hz : e k j=0 := by
            by_contra h
            have hle := hS k j ((mem_expSupport _ _).mpr h)
            rw [(Finset.mem_filter.mp hk).2] at hle
            have hlt : i < j := lt_of_le_of_ne hj (Ne.symm hji)
            exact (not_le_of_gt hlt) hle
          simpa only [e',Function.update_of_ne hji] using hz
    have hX' (k : κ) (j : Fin n) (hj : j∈expSupport (e' k)) :
        c j*fraction (X k j) ≤ q j (e' k j-1) := by
      rw [expSupport_update_zero] at hj
      have hjne := (Finset.mem_erase.mp hj).1
      have hpos := (mem_expSupport _ _).mp (Finset.mem_erase.mp hj).2
      have hEj : e k j-1 < E j := by have := he k j; omega
      have hq := hqr j (e k j-1) hEj
      have heq : e k j-1+1=e k j := by omega
      rw [heq] at hq
      simpa only [e',Function.update_of_ne hjne] using
        (mul_le_mul_of_nonneg_left (hX k j hpos) (hc0 j)).trans hq
    have hmult (g : ℕ) (hg : g < E i) : CompletePatterns E i.val (Kg g) e' 1 := by
      intro f hf
      let v := Function.update f i (g+1)
      have hvE (j : Fin n) : v j ≤ E j := by
        by_cases hj : j=i
        · subst j; simpa only [v,Function.update_self] using (show g+1 ≤ E i by omega)
        · simpa only [v,Function.update_of_ne hj] using hf.1 j
      obtain ⟨k,hkv⟩ := hfull v hvE ⟨i,by simp [v]⟩
      have hki' : e k i=g+1 := by simp only [hkv,v,Function.update_self]
      have hσi : σ k=i := by
        apply le_antisymm
        · apply Finset.max'_le
          intro j hj
          by_contra h
          have hij : i < j := lt_of_not_ge h
          have hji : j≠i := ne_of_gt hij
          have hz := hf.2 j hij.le
          have hh := (mem_expSupport _ _).mp hj
          simp only [hkv,v,Function.update_of_ne hji,hz] at hh
          exact hh rfl
        · exact hS k i ((mem_expSupport _ _).mpr (by omega))
      have hkKg : k∈Kg g := by simp [Kg,K,layerFamily,hσi,hki']
      have hkf : e' k=f := by
        funext j
        by_cases hj : j=i
        · subst j
          simp only [e',Function.update_self,hf.2 i le_rfl]
        · simp only [e',Function.update_of_ne hj,hkv,v]
      have hle : ((Kg g).filter (fun k => e' k=f)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro u hu w hw
        obtain ⟨hu,huf⟩ := Finset.mem_filter.mp hu
        obtain ⟨hw,hwf⟩ := Finset.mem_filter.mp hw
        have hug := (Finset.mem_filter.mp hu).2
        have hwg := (Finset.mem_filter.mp hw).2
        apply heinj
        funext j
        by_cases hj : j=i
        · subst j; exact hug.trans hwg.symm
        · have hh := congrFun (huf.trans hwf.symm) j
          simpa only [e',Function.update_of_ne hj] using hh
      exact le_antisymm hle (Finset.card_pos.mpr ⟨k,Finset.mem_filter.mpr ⟨hkKg,hkf⟩⟩)
    have hpoint (x : ∀ j, A j) : coordinateFraction A i (B i) x ≤
        ∑ g∈Finset.range (E i), r i (g+1)*N g x := by
      have hzero : K.filter (fun k => e k i=0)=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro k hk
        obtain ⟨hk,hz⟩ := Finset.mem_filter.mp hk
        exact (mem_expSupport _ _).mp (hki k hk) hz
      have hfullK : K.filter (fun k => e k i ≤ E i)=K := Finset.filter_true_of_mem (fun k _ => he k i)
      have hsum := sum_filter_nat_le K (fun k => e k i) (E i) (fun k => r i (e k i)*W k x)
      rw [hzero,hfullK,Finset.sum_empty,zero_add] at hsum
      calc
        _ ≤ ∑ k∈K, fraction (X k i)*boxIndicator A ((S k).erase i) (X k) x :=
          layered_fraction_bound A S X σ hσ i x
        _ ≤ ∑ k∈K, r i (e k i)*W k x := by
          apply Finset.sum_le_sum
          intro k hk
          have hi := (mem_expSupport _ _).mp (hki k hk)
          simpa only [W,e',expSupport_update_zero,S] using
            mul_le_mul_of_nonneg_right (hX k i hi) (boxIndicator_nonneg A ((S k).erase i) (X k) x)
        _ = ∑ g∈Finset.range (E i), r i (g+1)*N g x := by
          rw [hsum]
          apply Finset.sum_congr rfl
          intro g hg
          rw [show r i (g+1)*N g x=∑ k∈Kg g, r i (g+1)*W k x from Finset.mul_sum _ _ _]
          apply Finset.sum_congr rfl
          intro k hk
          rw [(Finset.mem_filter.mp hk).2]
    exact completeTestBound_layer_loss A E c q i.val μ hμ (c i) (s i) (L i) hcomp (hc i) (hs i)
      (E i) (hE i) (fun g => r i (g+1)) (hr i) (hrs i) Kg (fun _ => e') (fun _ => X)
      (fun g hg k hk => he' k (Finset.mem_filter.mp hk).1)
      (fun g hg k hk => hX' k) hmult (coordinateFraction A i (B i)) hpoint
  obtain ⟨x,hx⟩ := certified_tower_avoids A B c L hc m hm0 hmsucc hmpos hmfinal hB I (hI0 B)
    horacle (fun i μ hμ hμtot hI => hstep i μ (B i) hμ hμtot hI (horacle i μ hμ hμtot hI))
  refine ⟨x,fun k hk => hx (σ k) ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,k,by simp [layerFamily],hk⟩

#print axioms complete_box_certified_avoidance
end Erdos7KilledSieve



/-! A numeric-certificate interface independent of the actual residue boxes. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
set_option maxHeartbeats 4000000

/-- A certificate must supply its invariant uniformly for every finite
coordinate alphabet and every type of pattern labels. -/
def SieveInvariantCertificate {n : ℕ} (E : Fin n → ℕ) (c s : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (L : Fin n → ℚ) (m : ℕ → ℚ) : Prop :=
  ∀ (κ : Type) (A : Fin n → Type) [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)],
    ∃ I : ℕ → ((∀ i,A i) → ℚ) → Prop,
      (∀ B : Fin n → Finset (∀ i,A i),I 0 (towerWeights A B c 0)) ∧
      (∀ (i : Fin n) (μ : (∀ i,A i) → ℚ),
        (∀ x,0 ≤ μ x) → (∑ x,μ x)=m i.val → I i.val μ →
        CompleteTestBound κ A E c q i.val μ 1 (fun z => residual (c i) (s i*z)) (L i)) ∧
      (∀ (i : Fin n) (μ : (∀ i,A i) → ℚ) (B : Finset (∀ i,A i)),
        (∀ x,0 ≤ μ x) → (∑ x,μ x)=m i.val → I i.val μ →
        (∑ x,μ x*residual (c i) (coordinateFraction A i B x)) ≤ L i →
        I (i.val+1) (killedResample A i μ B (c i) (L i)))

end Erdos7KilledSieve



/-! Complete a distinct box family by inserting missing exponent patterns. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
open Erdos7BinarySieve (expect)
set_option maxHeartbeats 4000000

/-- The complete-rectangle criterion applies to arbitrary distinct nonzero
exponent families: missing patterns can be filled by empty boxes. -/
theorem distinct_box_certified_avoidance {n : ℕ} {κ : Type*} [Fintype κ]
    (A : Fin n → Type) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (E : Fin n → ℕ) (hE : ∀ i, 0 < E i) (c s : Fin n → ℚ) (r q : Fin n → ℕ → ℚ)
    (hc : ∀ i, 1 ≤ c i) (hs : ∀ i, 0 < s i)
    (hr : ∀ i g, g < E i → 0 ≤ r i (g+1))
    (hrs : ∀ i, (∑ g∈Finset.range (E i),r i (g+1)) ≤ s i)
    (hq1 : ∀ i, q i 0 ≤ 1) (hqdec : ∀ i g, g < E i → q i (g+1) ≤ q i g)
    (hqE : ∀ i, q i (E i)=0) (hqr : ∀ i g, g < E i → c i*r i (g+1) ≤ q i g)
    (e : κ → Fin n → ℕ) (heinj : Function.Injective e)
    (he : ∀ k i, e k i ≤ E i) (hne : ∀ k, (expSupport (e k)).Nonempty)
    (X : κ → ∀ i, Finset (A i))
    (hX : ∀ k i, e k i≠0 → fraction (X k i) ≤ r i (e k i))
    (L : Fin n → ℚ) (m : ℕ → ℚ) (hm0 : m 0=1)
    (hmsucc : ∀ i : Fin n,m (i.val+1)=m i.val-L i)
    (hmpos : ∀ t,t ≤ n → 0 ≤ m t) (hmfinal : 0 < m n)
    (hcert : SieveInvariantCertificate E c s q L m) :
    ∃ x : ∀ i, A i, ∀ k, ¬ (∀ i∈expSupport (e k), x i∈X k i) := by
  classical
  let V := ∀ i : Fin n, Fin (E i+1)
  let ρ := {v : V // ∃ i, (v i:ℕ)≠0}
  let e' (k : ρ) (i : Fin n) : ℕ := k.val i
  have he' (k : ρ) (i : Fin n) : e' k i ≤ E i := Nat.le_of_lt_succ (k.val i).isLt
  have hne' (k : ρ) : (expSupport (e' k)).Nonempty := by
    obtain ⟨i,hi⟩ := k.property
    exact ⟨i,(mem_expSupport _ _).mpr hi⟩
  have hinj' : Function.Injective e' := by
    intro k l hkl
    apply Subtype.ext
    funext i
    exact Fin.ext (congrFun hkl i)
  have hfull' (f : Fin n → ℕ) (hf : ∀ i, f i ≤ E i) (hfn : ∃ i, f i≠0) : ∃ k : ρ, e' k=f := by
    exact ⟨⟨fun i => ⟨f i,by have := hf i; omega⟩,hfn⟩,rfl⟩
  let X' (k : ρ) (i : Fin n) : Finset (A i) :=
    if h : ∃ l, e l=e' k then X h.choose i else ∅
  have hX' (k : ρ) (i : Fin n) (hi : e' k i≠0) : fraction (X' k i) ≤ r i (e' k i) := by
    dsimp only [X']
    split_ifs with h
    · have heq := congrFun h.choose_spec i
      simpa only [heq] using hX h.choose i (by simpa only [heq] using hi)
    · have hg : e' k i-1 < E i := by have := he' k i; omega
      have hh := hr i (e' k i-1) hg
      have heq : e' k i-1+1=e' k i := by omega
      simpa only [fraction,Finset.card_empty,Nat.cast_zero,zero_div,heq] using hh
  obtain ⟨I,hI0,htest,hstep⟩ := hcert ρ A
  obtain ⟨x,hx⟩ := complete_box_certified_avoidance A E hE c s r q hc hs hr hrs hq1 hqdec hqE hqr
    e' hinj' he' hne' hfull' X' hX' L m hm0 hmsucc hmpos hmfinal I hI0 htest hstep
  refine ⟨x,fun k hk => ?_⟩
  obtain ⟨l,hl⟩ := hfull' (e k) (he k) (by
    obtain ⟨i,hi⟩ := hne k
    exact ⟨i,(mem_expSupport _ _).mp hi⟩)
  have hex : ∃ j, e j=e' l := ⟨k,hl.symm⟩
  have hchoice : hex.choose=k := heinj (hex.choose_spec.trans hl)
  apply hx l
  intro i hi
  have hi' : i∈expSupport (e k) := by simpa only [hl] using hi
  have hXi : X' l i=X k i := by simp only [X',dif_pos hex,hchoice]
  rw [hXi]
  exact hk i hi'

#print axioms distinct_box_certified_avoidance
end Erdos7KilledSieve



/-! Arithmetic specialization of an invariant-based finite sieve certificate. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve Erdos7StarSieve
open Erdos7BinarySieve (expect)
set_option maxHeartbeats 4000000

/-- An invariant certificate with a positive exact final mass precludes a
covering by distinct finite prime-power exponent patterns. -/
theorem arithmetic_certified_not_cover {n : ℕ} {κ : Type*} [Fintype κ]
    (p E : Fin n → ℕ) (hp : ∀ i, 1 < p i) (hE : ∀ i, 0 < E i)
    (hcop : Pairwise (Function.onFun Nat.Coprime p))
    (e : κ → Fin n → ℕ) (he : Function.Injective e) (he0 : ∀ k, ∃ i, e k i≠0)
    (heE : ∀ k i, e k i≤E i) (a : κ → ℤ)
    (c s : Fin n → ℚ) (hc : ∀ i, 1≤c i) (hcp : ∀ i, c i≤p i)
    (hs : ∀ i, 0<s i)
    (hsum : ∀ i, (∑ g∈Finset.range (E i), ((p i:ℚ)⁻¹)^(g+1))≤s i)
    (L : Fin n → ℚ) (m : ℕ → ℚ) (hm0 : m 0=1)
    (hmsucc : ∀ i : Fin n,m (i.val+1)=m i.val-L i)
    (hmpos : ∀ t,t ≤ n → 0 ≤ m t) (hmfinal : 0 < m n)
    (hcert : SieveInvariantCertificate E c s (fun i => powerTail (p i) (c i) (E i)) L m) :
    ¬ (∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k) := by
  intro hcover
  classical
  letI (i : Fin n) : NeZero (p i) := ⟨by have := hp i; omega⟩
  let A (i : Fin n) := ZMod (p i ^ E i)
  let f (k : κ) (i : Fin n) := ZMod.castHom (pow_dvd_pow (p i) (heE k i)) (ZMod (p i ^ e k i))
  let B (k : κ) (i : Fin n) := Finset.univ.filter (fun x : A i => f k i x = (a k : ZMod (p i ^ e k i)))
  have hBcard (k : κ) (i : Fin n) : ((B k i).card : ℚ) ≤
      (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(e k i) := by
    have hh := surjective_fiber_card_rat (f k i).toAddMonoidHom
      (ZMod.castHom_surjective (pow_dvd_pow (p i) (heE k i))) (a k)
    change ((B k i).card : ℚ) = _ at hh
    rw [hh]
    simp only [A, ZMod.card, Nat.cast_pow, div_eq_mul_inv, inv_pow]
    exact le_rfl
  have hbox : ∀ x : ∀ i, A i, ∃ k, ∀ i, x i ∈ B k i := by
    intro x
    let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) (fun i => p i ^ E i) Finset.univ
      (fun i _ => pow_ne_zero _ (NeZero.ne _))
      (fun i _ j _ hij => (hcop hij).pow _ _)
    have hz (i : Fin n) : (z.val : A i) = x i := by
      rw [← ZMod.natCast_zmod_val (x i)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
    obtain ⟨k, hk⟩ := hcover (z.val : ℤ)
    refine ⟨k, ?_⟩
    intro i
    have hpi : p i ^ e k i ∣ ∏ j, p j ^ e k j :=
      Finset.dvd_prod_of_mem (fun j => p j ^ e k j) (Finset.mem_univ i)
    have hpi' : ((p i ^ e k i : ℕ) : ℤ) ∣ ((∏ j, p j ^ e k j : ℕ) : ℤ) := by exact_mod_cast hpi
    have hqi := hpi'.trans hk
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hz i, map_natCast]
    symm
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (a k) (z.val : ℤ) (p i ^ e k i)).mpr hqi
  have hc0 : ∀ i, 0≤c i := fun i => (by norm_num : (0:ℚ)≤1).trans (hc i)
  have hfrac (k : κ) (i : Fin n) : fraction (B k i)≤((p i:ℚ)⁻¹)^(e k i) := by
    apply (div_le_iff₀ card_pos_rat).mpr
    simpa only [mul_comm] using hBcard k i
  obtain ⟨x,hx⟩ := distinct_box_certified_avoidance A E hE c s (fun i g => ((p i:ℚ)⁻¹)^g)
    (fun i => powerTail (p i) (c i) (E i)) hc hs (fun _ _ _ => by positivity) hsum
    (fun i => powerTail_zero_le_one (p i) (hp i) (c i) (hcp i) (E i))
    (fun i g _ => powerTail_decreasing (p i) (hp i) (c i) (hc0 i) (E i) g)
    (fun i => powerTail_terminal (p i) (c i) (E i))
    (fun i g hg => by simp only [powerTail,if_pos hg,le_refl]) e he heE (by
      intro k
      obtain ⟨i,hi⟩ := he0 k
      exact ⟨i,(mem_expSupport _ _).mpr hi⟩) B (fun k i _ => hfrac k i) L m hm0 hmsucc hmpos hmfinal hcert
  obtain ⟨k,hk⟩ := hbox x
  exact hx k (fun i _ => hk i)

#print axioms arithmetic_certified_not_cover
end Erdos7KilledSieve
