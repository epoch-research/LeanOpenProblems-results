import Submission.NaturalSidonExtractionExplore
import Submission.WindowPerturbationExplore

/-! A count-preserving reflection patch. It is used to test the strength
of bounded-prefix-discrepancy rounding, not to assert the original limit. -/
namespace Erdos66ReflectionRoundingPatch
open AdditiveCombinatorics Erdos66NaturalSidonExtraction Erdos66NatPairAlgebra
  Erdos66WindowPerturbation Erdos66Counting Erdos66Generating Erdos66Rounding
open scoped Classical
set_option maxHeartbeats 1500000

noncomputable def intervalPart (B : Set ℕ) (a b : ℕ) : Finset ℕ :=
  (Finset.Ico a b).filter (fun x ↦ x∈B)

lemma intervalPart_card (B : Set ℕ) (a w : ℕ) :
    (intervalPart B a (a+w)).card=localCount B a w := rfl

lemma local_count_error (B : Set ℕ) (p : ℕ→ℝ) (D : ℝ)
    (hB : ∀N, |(count B N : ℝ)-cumulative p N|≤D) (a b : ℕ) (hab : a≤b) :
    |((intervalPart B a b).card : ℝ)-(∑i∈Finset.Ico a b,p i)|≤2*D := by
  have hc : ((intervalPart B a b).card : ℝ)=
      (count B b : ℝ)-(count B a : ℝ) := by
    have hsum (N : ℕ) : (count B N : ℝ)=∑i∈Finset.range N,indicator B i := by
      simp [count,cutoff,indicator,Finset.sum_ite]
    rw [hsum,hsum,←Finset.sum_Ico_eq_sub _ hab]
    simp [intervalPart,indicator,Finset.sum_ite]
  rw [hc,Finset.sum_Ico_eq_sub _ hab]
  have hh : |((count B b : ℝ)-cumulative p b)-((count B a : ℝ)-cumulative p a)|≤2*D :=
    (abs_sub _ _).trans (by linarith [hB a,hB b])
  convert hh using 1 <;> dsimp [cumulative] <;> congr 1 <;> ring

/-- Choose a set of the requested size by trimming or extending F. Every
restricted count changes by at most the necessary cardinality difference. -/
lemma match_card (U F : Finset ℕ) (hFU : F⊆U) (m : ℕ) (hm : m≤U.card) :
    ∃ G : Finset ℕ, G⊆U ∧ G.card=m ∧
      (∀T : Finset ℕ, |(((G∩T).card : ℝ)-((F∩T).card : ℝ))|≤|(m : ℝ)-F.card|) ∧
      min F.card m≤(F∩G).card := by
  by_cases hFm : m≤F.card
  · obtain ⟨G,hGF,hGcard⟩ := Finset.exists_subset_card_eq hFm
    refine ⟨G,hGF.trans hFU,hGcard,?_,?_⟩
    · intro T
      have hsub : G∩T⊆F∩T := Finset.inter_subset_inter_right hGF
      have hdiff : (F∩T)\(G∩T)⊆F\G := by
        intro a ha
        simp only [Finset.mem_sdiff,Finset.mem_inter] at ha ⊢
        tauto
      have hcc := Finset.card_le_card hdiff
      have he := Finset.card_sdiff_add_card_eq_card hsub
      have he' := Finset.card_sdiff_add_card_eq_card hGF
      have hle : ((G∩T).card : ℝ)≤(F∩T).card := by exact_mod_cast Finset.card_le_card hsub
      have hle' : (m : ℝ)≤F.card := by exact_mod_cast hFm
      rw [abs_of_nonpos (sub_nonpos.mpr hle),abs_of_nonpos (sub_nonpos.mpr hle')]
      have hh : (F∩T).card+m≤F.card+(G∩T).card := by omega
      have hh' : ((F∩T).card : ℝ)+m≤F.card+(G∩T).card := by exact_mod_cast hh
      linarith
    · rw [Finset.inter_eq_right.mpr hGF,hGcard,min_eq_right hFm]
  · have hFm' : F.card≤ m := by omega
    have hroom : m-F.card≤(U\F).card := by
      have hh := Finset.card_sdiff_add_card_eq_card hFU
      omega
    obtain ⟨E,hE,hEc⟩ := Finset.exists_subset_card_eq hroom
    let G := F∪E
    have hdis : Disjoint F E := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.mem_sdiff.mp (hE hb)).2 ha
    have hFG : F⊆G := Finset.subset_union_left
    have hGU : G⊆U := Finset.union_subset hFU (hE.trans Finset.sdiff_subset)
    have hGc : G.card=m := by
      rw [Finset.card_union_of_disjoint hdis,hEc]
      omega
    refine ⟨G,hGU,hGc,?_,?_⟩
    · intro T
      have hsub : F∩T⊆G∩T := Finset.inter_subset_inter_right hFG
      have hdiff : (G∩T)\(F∩T)⊆G\F := by
        intro a ha
        simp only [Finset.mem_sdiff,Finset.mem_inter] at ha ⊢
        tauto
      have hcc := Finset.card_le_card hdiff
      have he := Finset.card_sdiff_add_card_eq_card hsub
      have he' := Finset.card_sdiff_add_card_eq_card hFG
      have hle : ((F∩T).card : ℝ)≤(G∩T).card := by exact_mod_cast Finset.card_le_card hsub
      have hle' : (F.card : ℝ)≤ m := by exact_mod_cast hFm'
      rw [abs_of_nonneg (sub_nonneg.mpr hle),abs_of_nonneg (sub_nonneg.mpr hle')]
      have hh : (G∩T).card+F.card≤ m+(F∩T).card := by omega
      have hh' : ((G∩T).card : ℝ)+F.card≤ m+(F∩T).card := by exact_mod_cast hh
      linarith
    · rw [Finset.inter_eq_left.mpr hFG,min_eq_left hFm']

lemma reflected_prefix_count (B : Set ℕ) (L W j : ℕ) (hj : j≤W) (hW : 0<W) :
    ((natReflect (2*L+2*W-1) (intervalPart B L (L+W)))∩Finset.range (L+W+j)).card =
      (intervalPart B (L+W-j) (L+W)).card := by
  let t := 2*L+2*W-1
  have he : natReflect t (intervalPart B L (L+W))∩Finset.range (L+W+j)=
      (intervalPart B (L+W-j) (L+W)).image (fun a ↦ t-a) := by
    ext x
    simp only [Finset.mem_inter,Finset.mem_range,natReflect,Finset.mem_image,
      intervalPart,Finset.mem_filter,Finset.mem_Ico]
    constructor
    · rintro ⟨⟨a,⟨⟨haL,haU⟩,haB⟩,rfl⟩,hx⟩
      exact ⟨a,⟨⟨by dsimp [t] at hx; omega,haU⟩,haB⟩,rfl⟩
    · rintro ⟨a,⟨⟨haL,haU⟩,haB⟩,rfl⟩
      exact ⟨⟨a,⟨⟨by omega,haU⟩,haB⟩,rfl⟩,by dsimp [t]; omega⟩
  rw [he]
  apply Finset.card_image_of_injOn
  intro a ha b hb heq
  change a∈intervalPart B (L+W-j) (L+W) at ha
  change b∈intervalPart B (L+W-j) (L+W) at hb
  have ha' := (Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1).2
  have hb' := (Finset.mem_Ico.mp (Finset.mem_filter.mp hb).1).2
  dsimp [t] at heq
  omega

lemma reflected_interval_bounds (B : Set ℕ) (L W : ℕ) (hW : 0<W) :
    natReflect (2*L+2*W-1) (intervalPart B L (L+W))⊆Finset.Ico (L+W) (L+2*W) := by
  intro x hx
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
  have ha' := Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1
  apply Finset.mem_Ico.mpr
  constructor <;> omega

lemma mem_natReflect_iff (F : Finset ℕ) (t b : ℕ) (ht : ∀a∈F, a≤t) :
    b∈natReflect t F ↔ b≤t ∧ t-b∈F := by
  constructor
  · intro hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    have hh := ht a ha
    exact ⟨Nat.sub_le _ _,by simpa only [Nat.sub_sub_self hh] using ha⟩
  · rintro ⟨hb,hF⟩
    exact Finset.mem_image.mpr ⟨t-b,hF,Nat.sub_sub_self hb⟩

lemma reflected_pairs_card (F G : Finset ℕ) (t : ℕ) (ht : ∀a∈F, a≤t) :
    pairs F G t=(natReflect t F∩G).card := by
  rw [pairs_comm,pairs_eq_filter]
  congr 1
  ext b
  simp only [Finset.mem_filter,Finset.mem_inter,mem_natReflect_iff F t b ht]
  tauto

lemma equal_length_counts_close (B : Set ℕ) (p : ℕ→ℝ) (D : ℝ)
    (hB : ∀N, |(count B N : ℝ)-cumulative p N|≤D) (hp : Antitone p)
    (L R a b j : ℕ) (ha : L≤a) (hb : L≤b) (haR : a+j≤R) (hbR : b+j≤R)
    (hosc : (R-L : ℕ)*(p L-p R)≤1) :
    |((intervalPart B a (a+j)).card : ℝ)-(intervalPart B b (b+j)).card|≤4*D+1 := by
  have hmass (t : ℕ) (ht : L≤t) (htR : t+j≤R) :
      (j : ℝ)*p R≤∑i∈Finset.Ico t (t+j),p i ∧
      (∑i∈Finset.Ico t (t+j),p i)≤(j : ℝ)*p L := by
    have h₁ := Finset.sum_le_sum (s := Finset.Ico t (t+j)) (f := fun _ ↦ p R)
      (g := p) (by intro i hi; have hh := Finset.mem_Ico.mp hi; exact hp (by omega))
    have h₂ := Finset.sum_le_sum (s := Finset.Ico t (t+j)) (f := p)
      (g := fun _ ↦ p L) (by intro i hi; have hh := Finset.mem_Ico.mp hi; exact hp (by omega))
    simpa only [Finset.sum_const,nsmul_eq_mul,Nat.card_Ico,Nat.add_sub_cancel_left] using And.intro h₁ h₂
  have h₁ := hmass a ha haR
  have h₂ := hmass b hb hbR
  have he₁ := abs_le.mp (local_count_error B p D hB a (a+j) (by omega))
  have he₂ := abs_le.mp (local_count_error B p D hB b (b+j) (by omega))
  have hnon : 0≤p L-p R := sub_nonneg.mpr (hp (by omega))
  have hj : (j : ℝ)≤(R-L : ℕ) := by exact_mod_cast (show j≤R-L by omega)
  have hm := mul_le_mul_of_nonneg_right hj hnon
  rw [abs_le]
  constructor <;> nlinarith

lemma reflected_card (B : Set ℕ) (L W : ℕ) (hW : 0<W) :
    (natReflect (2*L+2*W-1) (intervalPart B L (L+W))).card=(intervalPart B L (L+W)).card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb he
  change a∈intervalPart B L (L+W) at ha
  change b∈intervalPart B L (L+W) at hb
  have ha' := Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1
  have hb' := Finset.mem_Ico.mp (Finset.mem_filter.mp hb).1
  change 2*L+2*W-1-a=2*L+2*W-1-b at he
  omega

/-- On a nearly constant-density window, the right half can be replaced
without changing its total count. All prefix counts change by a fixed
constant, and almost all of the smaller half-count becomes a peak. -/
theorem exists_reflection_patch (B : Set ℕ) (p : ℕ→ℝ) (D : ℝ) (hD : 0≤D)
    (hB : ∀N, |(count B N : ℝ)-cumulative p N|≤D) (hp : Antitone p)
    (L W : ℕ) (hW : 0<W) (hosc : (2*W : ℕ)*(p L-p (L+2*W))≤1) :
    ∃ G : Finset ℕ, G⊆Finset.Ico (L+W) (L+2*W) ∧
      G.card=(intervalPart B (L+W) (L+2*W)).card ∧
      (∀N : ℕ, |((G∩Finset.range N).card : ℝ)-
        ((intervalPart B (L+W) (L+2*W)∩Finset.range N).card : ℝ)|≤8*D+2) ∧
      2*min (intervalPart B L (L+W)).card (intervalPart B (L+W) (L+2*W)).card≤
        sumRep ((intervalPart B L (L+W)∪G : Finset ℕ) : Set ℕ) (2*L+2*W-1) := by
  let F := intervalPart B L (L+W)
  let R := intervalPart B (L+W) (L+2*W)
  let t := 2*L+2*W-1
  let Q := natReflect t F
  have hQsub : Q⊆Finset.Ico (L+W) (L+2*W) := reflected_interval_bounds B L W hW
  have hQc : Q.card=F.card := reflected_card B L W hW
  have hRsub : R⊆Finset.Ico (L+W) (L+2*W) := Finset.filter_subset _ _
  obtain ⟨G,hGsub,hGc,hclose,hinter⟩ := match_card (Finset.Ico (L+W) (L+2*W)) Q hQsub R.card
    (Finset.card_le_card hRsub)
  have hcountdiff : |(R.card : ℝ)-Q.card|≤4*D+1 := by
    rw [hQc]
    have hh := equal_length_counts_close B p D hB hp L (L+2*W) (L+W) L W
      (by omega) le_rfl (by omega) (by omega) (by simpa using hosc)
    simpa only [F,R,show L+W+W=L+2*W by omega] using hh
  refine ⟨G,hGsub,hGc,?_,?_⟩
  · intro N
    by_cases hnlo : N≤L+W
    · have hg : G∩Finset.range N=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        obtain ⟨haG,haN⟩ := Finset.mem_inter.mp ha
        have hh := Finset.mem_Ico.mp (hGsub haG)
        have hn := Finset.mem_range.mp haN
        omega
      have hr : R∩Finset.range N=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        obtain ⟨haR,haN⟩ := Finset.mem_inter.mp ha
        have hh := Finset.mem_Ico.mp (hRsub haR)
        have hn := Finset.mem_range.mp haN
        omega
      change |((G∩Finset.range N).card : ℝ)-((R∩Finset.range N).card : ℝ)|≤_
      rw [hg,hr]
      simp only [Finset.card_empty,Nat.cast_zero,sub_self,abs_zero]
      positivity
    by_cases hnhi : L+2*W≤N
    · have hg : G∩Finset.range N=G := Finset.inter_eq_left.mpr (fun a ha ↦ by
        have hh := Finset.mem_Ico.mp (hGsub ha); exact Finset.mem_range.mpr (by omega))
      have hr : R∩Finset.range N=R := Finset.inter_eq_left.mpr (fun a ha ↦ by
        have hh := Finset.mem_Ico.mp (hRsub ha); exact Finset.mem_range.mpr (by omega))
      change |((G∩Finset.range N).card : ℝ)-((R∩Finset.range N).card : ℝ)|≤_
      rw [hg,hr,hGc,sub_self,abs_zero]
      positivity
    let j := N-(L+W)
    have hj : j≤W := by dsimp [j]; omega
    have hN : N=L+W+j := by dsimp [j]; omega
    have hQpref : (Q∩Finset.range N).card=(intervalPart B (L+W-j) (L+W)).card := by
      rw [hN]
      exact reflected_prefix_count B L W j hj hW
    have hRpref : R∩Finset.range N=intervalPart B (L+W) (L+W+j) := by
      have he : R∩Finset.range N=intervalPart B (L+W) N := by
        ext a
        simp only [R,intervalPart,Finset.mem_inter,Finset.mem_filter,Finset.mem_Ico,Finset.mem_range]
        constructor
        · tauto
        · rintro ⟨⟨haL,haN⟩,haB⟩
          exact ⟨⟨⟨haL,by omega⟩,haB⟩,haN⟩
      exact he.trans (by rw [hN])
    have hcomp : |((Q∩Finset.range N).card : ℝ)-((R∩Finset.range N).card : ℝ)|≤4*D+1 := by
      rw [hQpref,hRpref]
      have hh := equal_length_counts_close B p D hB hp L (L+2*W) (L+W-j) (L+W) j
        (by omega) (by omega) (by omega) (by omega) (by simpa using hosc)
      simpa only [show L+W-j+j=L+W by omega] using hh
    have hh := (hclose (Finset.range N)).trans hcountdiff
    exact (abs_sub_le ((G∩Finset.range N).card : ℝ) ((Q∩Finset.range N).card : ℝ)
      ((R∩Finset.range N).card : ℝ)).trans (by linarith)
  · have hdis : Disjoint F G := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      have ha' := Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1
      have hb' := Finset.mem_Ico.mp (hGsub hb)
      omega
    have hFt : ∀a∈F, a≤t := by
      intro a ha
      have ha' := Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1
      dsimp [t]
      omega
    rw [sumRep_union_self F G t hdis,reflected_pairs_card F G t hFt]
    change 2*min F.card R.card≤sumRep (F : Set ℕ) t+2*(Q∩G).card+sumRep (G : Set ℕ) t
    rw [hQc] at hinter
    omega

end Erdos66ReflectionRoundingPatch
