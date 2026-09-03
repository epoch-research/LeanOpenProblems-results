import Submission.HypergraphLinearization
import Submission.IntegerSumCapacity
import Submission.SquareSumRepresentations
import Submission.FractionalSquareSidon
import Submission.APFreeExtraction

/-! Simultaneous bounded sum and difference multiplicity for actual squares.
The capacity-one exponent is still two thirds; this is not Erdos 773. -/
namespace Erdos773.JointSquareMultiplicity
open Finset Filter
open IntegerDifferenceCapacity (support)
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option Elab.async false

section Generic
variable {ι : Type*}

def bad (I : Finset ι) (R : ι → Finset (ℕ × ℕ)) (g : ℕ) : Finset (Finset ℕ) :=
  I.biUnion (fun i => ((R i).powersetCard (g+1)).image support)

lemma bad_subset {I : Finset ι} {R : ι → Finset (ℕ × ℕ)} {A : Finset ℕ} {g : ℕ}
    (hR : ∀ i ∈ I, R i ⊆ A ×ˢ A) : ∀ e ∈ bad I R g, e ⊆ A := by
  intro e he
  obtain ⟨i,hi,he⟩ := mem_biUnion.mp he
  obtain ⟨E,hE,rfl⟩ := mem_image.mp he
  have hE := (mem_powersetCard.mp hE).1
  intro x hx
  rcases mem_union.mp hx with hx | hx
  · obtain ⟨ab,hab,rfl⟩ := mem_image.mp hx
    exact (mem_product.mp (hR i hi (hE hab))).1
  · obtain ⟨ab,hab,rfl⟩ := mem_image.mp hx
    exact (mem_product.mp (hR i hi (hE hab))).2

lemma bad_size {I : Finset ι} {R : ι → Finset (ℕ × ℕ)} {g : ℕ}
    (hs : ∀ i ∈ I, ∀ E ⊆ R i, (support E).card = 2*E.card) :
    ∀ e ∈ bad I R g, e.card = 2*g+2 := by
  intro e he
  obtain ⟨i,hi,he⟩ := mem_biUnion.mp he
  obtain ⟨E,hE,rfl⟩ := mem_image.mp he
  obtain ⟨hE,hc⟩ := mem_powersetCard.mp hE
  rw [hs i hi E hE,hc]
  omega

lemma bad_card (I : Finset ι) (R : ι → Finset (ℕ × ℕ)) (g : ℕ) (K : ℝ)
    (hK : ∀ i ∈ I, ((R i).card : ℝ) ≤ K) :
    ((bad I R g).card : ℝ) ≤ I.card*K^(g+1) := by
  have hc : (bad I R g).card ≤ ∑ i ∈ I, (R i).card^(g+1) := by
    apply card_biUnion_le.trans
    apply sum_le_sum
    intro i hi
    apply card_image_le.trans
    rw [card_powersetCard]
    exact Nat.choose_le_pow _ _
  calc
    _ ≤ ∑ i ∈ I, ((R i).card : ℝ)^(g+1) := by exact_mod_cast hc
    _ ≤ ∑ _i ∈ I, K^(g+1) :=
      sum_le_sum (fun i hi => pow_le_pow_left₀ (Nat.cast_nonneg _) (hK i hi) _)
    _ = _ := by simp

lemma capacity_of_avoid {I : Finset ι} {R : ι → Finset (ℕ × ℕ)} {g : ℕ}
    {B : Finset ℕ} (hB : ∀ e ∈ bad I R g, ¬ e ⊆ B) :
    ∀ i ∈ I, ((R i).filter (fun ab => ab.1 ∈ B ∧ ab.2 ∈ B)).card ≤ g := by
  intro i hi
  by_contra! hh
  obtain ⟨E,hE,hc⟩ := exists_subset_card_eq (show g+1 ≤
    ((R i).filter (fun ab => ab.1 ∈ B ∧ ab.2 ∈ B)).card by omega)
  apply hB (support E)
  · exact mem_biUnion.mpr ⟨i,hi,mem_image.mpr
      ⟨E,mem_powersetCard.mpr ⟨hE.trans (filter_subset _ _),hc⟩,rfl⟩⟩
  · intro x hx
    rcases mem_union.mp hx with hx | hx
    · obtain ⟨ab,hab,rfl⟩ := mem_image.mp hx
      exact (mem_filter.mp (hE hab)).2.1
    · obtain ⟨ab,hab,rfl⟩ := mem_image.mp hx
      exact (mem_filter.mp (hE hab)).2.2

/-- A uniform alteration certificate for several families of disjoint pairs. -/
theorem indexed_selection (A : Finset ℕ) (I : Finset ι) (R : ι → Finset (ℕ × ℕ))
    (hR : ∀ i ∈ I, R i ⊆ A ×ˢ A)
    (hs : ∀ i ∈ I, ∀ E ⊆ R i, (support E).card=2*E.card)
    (g : ℕ) (K p : ℝ) (hK : ∀ i ∈ I, ((R i).card : ℝ) ≤ K)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ B ⊆ A,
      p*A.card - I.card*K^(g+1)*p^(2*g+2) ≤ (B.card : ℝ) ∧
      ∀ i ∈ I, ((R i).filter (fun ab => ab.1 ∈ B ∧ ab.2 ∈ B)).card ≤ g := by
  have hn : ∀ e ∈ bad I R g, e.Nonempty := by
    intro e he
    apply card_pos.mp
    have hh := bad_size hs e he
    omega
  obtain ⟨B,hB,havoid,hcard⟩ := HypergraphLinearization.ambient_alteration
    A (bad I R g) (bad_subset hR) hn p hp hp1
  refine ⟨B,hB,?_,capacity_of_avoid havoid⟩
  have hcost : (∑ e ∈ bad I R g, p^e.card) ≤ I.card*K^(g+1)*p^(2*g+2) := by
    calc
      _ = ∑ _e ∈ bad I R g, p^(2*g+2) := by
        apply sum_congr rfl
        intro e he
        rw [bad_size hs e he]
      _ = ((bad I R g).card : ℝ)*p^(2*g+2) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (bad_card I R g K hK) (pow_nonneg hp _)
  linarith only [hcard,hcost]
end Generic

abbrev squares (N : ℕ) : Finset ℕ := (Icc 1 N).image (fun n : ℕ => n^2)

def indices (N : ℕ) : Finset (Bool × ℕ) :=
  ({false} ×ˢ Icc 1 (N^2)) ∪ ({true} ×ˢ Icc 1 (2*N^2))

def families (A : Finset ℕ) (i : Bool × ℕ) : Finset (ℕ × ℕ) :=
  if i.1 then IntegerSumCapacity.sumReps A i.2 else IntegerDifferenceCapacity.reps A i.2

lemma indices_card (N : ℕ) : (indices N).card = 3*N^2 := by
  rw [indices,card_union_of_disjoint]
  · simp
    omega
  · apply disjoint_left.mpr
    intro i hi hj
    have hf := mem_singleton.mp (mem_product.mp hi).1
    have ht := mem_singleton.mp (mem_product.mp hj).1
    exact Bool.false_ne_true (hf.symm.trans ht)

lemma square_bounds {N x : ℕ} (hx : x ∈ squares N) : 1 ≤ x ∧ x ≤ N^2 := by
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
  obtain ⟨ha,hN⟩ := mem_Icc.mp ha
  exact ⟨by nlinarith, Nat.pow_le_pow_left hN 2⟩

lemma sqrt_mem {N x : ℕ} (hx : x ∈ squares N) :
    Nat.sqrt x ∈ Icc 1 N ∧ (Nat.sqrt x)^2=x := by
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
  simpa only [Nat.sqrt_eq'] using (⟨ha,rfl⟩ : a ∈ Icc 1 N ∧ a^2=a^2)

lemma sqrt_pair_inj {N : ℕ} {A : Finset ℕ} (hA : A ⊆ squares N) :
    Set.InjOn (fun ab : ℕ × ℕ => (Nat.sqrt ab.1,Nat.sqrt ab.2)) (A ×ˢ A : Finset _) := by
  intro ab hab cd hcd he
  have ha := (sqrt_mem (hA (mem_product.mp hab).1)).2
  have hb := (sqrt_mem (hA (mem_product.mp hab).2)).2
  have hc := (sqrt_mem (hA (mem_product.mp hcd).1)).2
  have hd := (sqrt_mem (hA (mem_product.mp hcd).2)).2
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  dsimp only at he1 he2
  exact Prod.ext (by rw [← ha,← hc,he1]) (by rw [← hb,← hd,he2])

lemma difference_card_le {N : ℕ} {A : Finset ℕ} (hA : A ⊆ squares N) (D : ℕ) :
    (IntegerDifferenceCapacity.reps A D).card ≤ (squareDifferenceReps N D).card := by
  apply card_le_card_of_injOn (fun ab : ℕ × ℕ => (Nat.sqrt ab.1,Nat.sqrt ab.2))
  · intro ab hab
    obtain ⟨hab,habD⟩ := mem_filter.mp hab
    have ha := sqrt_mem (hA (mem_product.mp hab).1)
    have hb := sqrt_mem (hA (mem_product.mp hab).2)
    exact mem_filter.mpr ⟨mem_product.mpr ⟨ha.1,hb.1⟩,
      by nlinarith [ha.2,hb.2], by simpa only [ha.2,hb.2] using habD.2⟩
  · intro ab hab cd hcd he
    exact sqrt_pair_inj hA (mem_filter.mp hab).1 (mem_filter.mp hcd).1 he

lemma sum_card_le {N : ℕ} {A : Finset ℕ} (hA : A ⊆ squares N) (S : ℕ) :
    (IntegerSumCapacity.sumReps A S).card ≤ (SquareSumRepresentations.reps N S).card := by
  apply card_le_card_of_injOn (fun ab : ℕ × ℕ => (Nat.sqrt ab.1,Nat.sqrt ab.2))
  · intro ab hab
    obtain ⟨hab,habS⟩ := mem_filter.mp hab
    have ha := sqrt_mem (hA (mem_product.mp hab).1)
    have hb := sqrt_mem (hA (mem_product.mp hab).2)
    exact mem_filter.mpr ⟨mem_product.mpr ⟨ha.1,hb.1⟩,
      by simpa only [ha.2,hb.2] using habS.2⟩
  · intro ab hab cd hcd he
    exact sqrt_pair_inj hA (mem_filter.mp hab).1 (mem_filter.mp hcd).1 he

lemma pair_filter_restrict {A B : Finset ℕ} (hB : B ⊆ A) (P : ℕ × ℕ → Prop)
    [DecidablePred P] :
    ((A ×ˢ A).filter P).filter (fun ab => ab.1 ∈ B ∧ ab.2 ∈ B) = (B ×ˢ B).filter P := by
  ext ab
  simp only [mem_filter,mem_product]
  constructor
  · rintro ⟨⟨_,hp⟩,hb⟩
    exact ⟨hb,hp⟩
  · rintro ⟨⟨ha,hb⟩,hp⟩
    exact ⟨⟨⟨hB ha,hB hb⟩,hp⟩,ha,hb⟩

lemma diff_empty {N D : ℕ} {A : Finset ℕ} (hA : A ⊆ squares N) (hD : N^2 < D) :
    IntegerDifferenceCapacity.reps A D = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro ab hab
  obtain ⟨hab,hd⟩ := mem_filter.mp hab
  have hb := square_bounds (hA (mem_product.mp hab).2)
  omega

lemma sum_empty {N S : ℕ} {A : Finset ℕ} (hA : A ⊆ squares N)
    (hS : S=0 ∨ 2*N^2 < S) : IntegerSumCapacity.sumReps A S = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro ab hab
  obtain ⟨hab,hs⟩ := mem_filter.mp hab
  have ha := square_bounds (hA (mem_product.mp hab).1)
  have hb := square_bounds (hA (mem_product.mp hab).2)
  omega

/-- Both capacities are controlled by one deletion. The sum convention includes
possible diagonal representations. The AP-free hypothesis is inherited. -/
theorem finite_selection {N : ℕ} {A : Finset ℕ} (hA : A ⊆ squares N)
    (hAP : ThreeAPFree (A : Set ℕ)) (g : ℕ) (hg : 1 ≤ g) (K p : ℝ)
    (hD : ∀ D ∈ Icc 1 (N^2), ((squareDifferenceReps N D).card : ℝ) ≤ K)
    (hS : ∀ S ∈ Icc 1 (2*N^2), ((SquareSumRepresentations.reps N S).card : ℝ) ≤ K)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ C ⊆ A, ThreeAPFree (C : Set ℕ) ∧
      p*A.card - 3*(N : ℝ)^2*K^(g+1)*p^(2*g+2) ≤ (C.card : ℝ) ∧
      (∀ D, 0 < D → (IntegerDifferenceCapacity.reps C D).card ≤ g) ∧
      (∀ S, (IntegerSumCapacity.unorderedSumReps C S).card ≤ g) := by
  have hR : ∀ i ∈ indices N, families A i ⊆ A ×ˢ A := by
    intro i hi
    unfold families
    split <;> exact filter_subset _ _
  have hs : ∀ i ∈ indices N, ∀ E ⊆ families A i, (support E).card=2*E.card := by
    intro i hi E hE
    cases hb : i.1
    · exact IntegerDifferenceCapacity.support_card hAP (by simpa [families,hb] using hE)
    · exact IntegerSumCapacity.support_card (by simpa [families,hb] using hE)
  have hK : ∀ i ∈ indices N, ((families A i).card : ℝ) ≤ K := by
    intro i hi
    rcases mem_union.mp hi with hi | hi
    · obtain ⟨hi,hmem⟩ := mem_product.mp hi
      have hi := mem_singleton.mp hi
      have hc : ((IntegerDifferenceCapacity.reps A i.2).card : ℝ) ≤
          (squareDifferenceReps N i.2).card := by exact_mod_cast difference_card_le hA i.2
      simpa [families,hi] using hc.trans (hD i.2 hmem)
    · obtain ⟨hi,hmem⟩ := mem_product.mp hi
      have hi := mem_singleton.mp hi
      have hc : ((IntegerSumCapacity.sumReps A i.2).card : ℝ) ≤
          (SquareSumRepresentations.reps N i.2).card := by exact_mod_cast sum_card_le hA i.2
      simpa [families,hi] using hc.trans (hS i.2 hmem)
  obtain ⟨C,hC,hcard,hcap⟩ := indexed_selection A (indices N) (families A) hR hs g K p hK hp hp1
  have hCAP : ThreeAPFree (C : Set ℕ) := hAP.mono (by exact_mod_cast hC)
  refine ⟨C,hC,hCAP,?_,?_,?_⟩
  · simpa [indices_card] using hcard
  · intro D hD0
    by_cases hDN : D ≤ N^2
    · have hi : (false,D) ∈ indices N := mem_union_left _
        (mem_product.mpr ⟨mem_singleton_self _,mem_Icc.mpr ⟨hD0,hDN⟩⟩)
      have hh := hcap (false,D) hi
      simpa only [families, Bool.false_eq_true, ↓reduceIte,
        IntegerDifferenceCapacity.reps, pair_filter_restrict hC] using hh
    · rw [diff_empty (hC.trans hA) (by omega)]
      simp
  · apply IntegerSumCapacity.unordered_capacity hg hCAP
    intro S
    by_cases hSN : S ∈ Icc 1 (2*N^2)
    · have hi : (true,S) ∈ indices N := mem_union_right _
        (mem_product.mpr ⟨mem_singleton_self _,hSN⟩)
      have hh := hcap (true,S) hi
      simpa only [families, ↓reduceIte, IntegerSumCapacity.sumReps,
        pair_filter_restrict hC] using hh
    · rw [sum_empty (hC.trans hA) (by simp only [mem_Icc,not_and_or,not_le] at hSN; omega)]
      simp

lemma eventually_sum_bound (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ S ∈ Icc 1 (2*N^2),
      ((SquareSumRepresentations.reps N S).card : ℝ) ≤ (N : ℝ)^δ := by
  obtain ⟨C,hC,hbound⟩ := SquareSumRepresentations.reps_height_subpower (δ/2) (by positivity)
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^(δ/2)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < δ/2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop C,eventually_ge_atTop 1] with N hlarge hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  intro S hS
  calc
    _ ≤ C*(N : ℝ)^(δ/2) := hbound N S (mem_Icc.mp hS).1 (mem_Icc.mp hS).2
    _ ≤ (N : ℝ)^(δ/2)*(N : ℝ)^(δ/2) :=
      mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hN0.le _)
    _ = _ := by rw [← Real.rpow_add hN0]; congr 1; ring

/-- For every fixed positive capacity, both kinds of representation can be
bounded simultaneously. This is a relaxed statement when g is greater than one. -/
theorem fixed_joint_multiplicity (g : ℕ) (hg : 1 ≤ g) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ C ⊆ squares N, ThreeAPFree (C : Set ℕ) ∧
      (N : ℝ)^(1-1/(2*(g : ℝ)+1)-ε) ≤ (C.card : ℝ) ∧
      (∀ D, 0 < D → (IntegerDifferenceCapacity.reps C D).card ≤ g) ∧
      (∀ S, (IntegerSumCapacity.unorderedSumReps C S).card ≤ g) := by
  let q : ℝ := 1/(2*g+1)
  let ρ : ℝ := 3*g*ε/4
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hqmul : q*(2*g+1)=1 := by dsimp [q]; field_simp
  have ht (r : ℝ) (hr : 0 < r) :
      Tendsto (fun N : ℕ => (N : ℝ)^(-r)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hr).comp tendsto_natCast_atTop_atTop
  have hsmall := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1/6) (ht ρ hρ)
  have hslack := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1/2)
    (ht (ε/4) (by positivity))
  filter_upwards [APFreeExtraction.square_ap_free_near_linear (ε/4) (by positivity),
    Fractional.eventually_representation_bound (ε/8) (by positivity),
    eventually_sum_bound (ε/4) (by positivity),hsmall,hslack,eventually_ge_atTop 1]
    with N hAP hD hS hsmall hslack hN
  obtain ⟨A,hA,hAP,hAc⟩ := hAP
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith only [hN1]
  let p : ℝ := (N : ℝ)^(-q-ε/2)
  let K : ℝ := (N : ℝ)^(ε/4)
  let T : ℝ := (N : ℝ)^(1-q-3*ε/4)
  have hp : 0 ≤ p := Real.rpow_nonneg hN0.le _
  have hp1 : p ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hT : 0 ≤ T := Real.rpow_nonneg hN0.le _
  have hD' : ∀ D ∈ Icc 1 (N^2), ((squareDifferenceReps N D).card : ℝ) ≤ K := by
    intro D hDmem
    simpa only [K,show 2*(ε/8)=ε/4 by ring] using hD D (mem_Icc.mp hDmem).1
  obtain ⟨C,hC,hCAP,hcard,hCD,hCS⟩ := finite_selection hA hAP g hg K p hD' hS hp hp1
  have hlead : T ≤ p*A.card := by
    calc
      _ = p*(N : ℝ)^(1-ε/4) := by
        dsimp [p,T]
        rw [← Real.rpow_add hN0]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hAc hp
  have hcost : (N : ℝ)^2*K^(g+1)*p^(2*g+2) = T*(N : ℝ)^(-ρ) := by
    dsimp [K,p,T,ρ]
    rw [← Real.rpow_mul_natCast hN0.le, ← Real.rpow_mul_natCast hN0.le,
      ← Real.rpow_natCast (N : ℝ) 2]
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
    congr 1
    push_cast
    nlinarith only [hqmul]
  have htarget : (N : ℝ)^(1-1/(2*(g : ℝ)+1)-ε) = T*(N : ℝ)^(-(ε/4)) := by
    dsimp [T,q]
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  have herr := mul_le_mul_of_nonneg_left hsmall hT
  have htar := mul_le_mul_of_nonneg_left hslack hT
  have hcost3 : 3*(N : ℝ)^2*K^(g+1)*p^(2*g+2) = 3*(T*(N : ℝ)^(-ρ)) := by
    rw [← hcost]
    ring
  rw [hcost3] at hcard
  refine ⟨C,hC.trans hA,hCAP,?_,hCD,hCS⟩
  rw [htarget]
  nlinarith only [hcard,hlead,herr,htar]

/-- Near-linear actual square sets with a fixed, epsilon-dependent joint capacity.
The capacity is not asserted to be one. -/
theorem near_linear_joint_capacity (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℕ, 1 ≤ g ∧ ∀ᶠ N : ℕ in atTop,
      ∃ C ⊆ squares N, ThreeAPFree (C : Set ℕ) ∧
        (N : ℝ)^(1-ε) ≤ (C.card : ℝ) ∧
        (∀ D, 0 < D → (IntegerDifferenceCapacity.reps C D).card ≤ g) ∧
        (∀ S, (IntegerSumCapacity.unorderedSumReps C S).card ≤ g) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (2/ε)
  let g := n+1
  have hg : 1 ≤ g := by dsimp [g]; omega
  have hn' : 2 < (n : ℝ)*ε := (div_lt_iff₀ hε).mp hn
  have hg0 : (0 : ℝ) < 2*(g : ℝ)+1 := by positivity
  have hi : 1/(2*(g : ℝ)+1) ≤ ε/2 := by
    apply (div_le_iff₀ hg0).mpr
    dsimp [g]
    push_cast
    nlinarith only [hn',hε]
  refine ⟨g,hg,?_⟩
  filter_upwards [fixed_joint_multiplicity g hg (ε/2) (by positivity),eventually_ge_atTop 1]
    with N hN hN1
  obtain ⟨C,hC,hAP,hcard,hD,hS⟩ := hN
  refine ⟨C,hC,hAP,?_,hD,hS⟩
  apply le_trans _ hcard
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1)
  linarith only [hi]

end Erdos773.JointSquareMultiplicity

#print axioms Erdos773.JointSquareMultiplicity.indexed_selection
#print axioms Erdos773.JointSquareMultiplicity.finite_selection
#print axioms Erdos773.JointSquareMultiplicity.fixed_joint_multiplicity
#print axioms Erdos773.JointSquareMultiplicity.near_linear_joint_capacity
