import Submission.LocalizedRepairExplore
import Submission.TemplatePacketExplore

/-! Coarse projections and mixed counts for a finite packet. -/
namespace Erdos66CoarseCounting
open AdditiveCombinatorics Erdos66Counting Erdos66Compactness
  Erdos66NatPairAlgebra Erdos66TemplatePacket
open scoped Classical
set_option maxHeartbeats 1500000

noncomputable def mixed (A : Set ℕ) (F : Finset ℕ) (n : ℕ) : ℕ :=
  (F.filter (fun d ↦ d ≤ n ∧ n-d ∈ A)).card

lemma mixed_eq_pairs (A : Set ℕ) (F : Finset ℕ) (n : ℕ) :
    mixed A F n = pairs F (cutoff A (n+1)) n := by
  rw [mixed, pairs_eq_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, mem_cutoff]
  constructor
  · rintro ⟨ha,han,hA⟩
    exact ⟨ha,han,by omega,hA⟩
  · rintro ⟨ha,han,_,hA⟩
    exact ⟨ha,han,hA⟩

lemma cutoff_rep (A : Set ℕ) (n : ℕ) :
    sumRep (cutoff A (n+1) : Set ℕ) n = sumRep A n := by
  apply sumRep_congr_below
  intro a ha
  simp only [Finset.mem_coe, mem_cutoff]
  exact and_iff_right (by omega)

lemma union_rep (A : Set ℕ) (F : Finset ℕ) (n : ℕ)
    (hd : Disjoint A (F : Set ℕ)) :
    sumRep (A ∪ (F : Set ℕ)) n = sumRep A n + 2*mixed A F n + sumRep (F : Set ℕ) n := by
  have hdis : Disjoint F (cutoff A (n+1)) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact Set.disjoint_left.mp hd (mem_cutoff.mp hb).2 ha
  have he : sumRep ((F ∪ cutoff A (n+1) : Finset ℕ) : Set ℕ) n =
      sumRep (A ∪ (F : Set ℕ)) n := by
    apply sumRep_congr_below
    intro a ha
    simp only [Finset.mem_coe, Finset.mem_union, mem_cutoff, Set.mem_union]
    have hh : a < n+1 := by omega
    tauto
  have hh := sumRep_union_self F (cutoff A (n+1)) n hdis
  rw [he, cutoff_rep, ←mixed_eq_pairs] at hh
  omega

lemma finite_rep_le_card (F : Finset ℕ) (n : ℕ) :
    sumRep (F : Set ℕ) n ≤ F.card := by
  rw [←pairs_self, pairs_eq_filter]
  exact Finset.card_le_card (Finset.filter_subset _ _)

def coarse (A : Set ℕ) (M : ℕ) : Set ℕ :=
  {q | ∃ a ∈ A, a/M = q}

noncomputable def rep (A : Set ℕ) (M q : ℕ) : ℕ :=
  if h : q ∈ coarse A M then Classical.choose h else 0

lemma rep_spec {A : Set ℕ} {M q : ℕ} (hq : q ∈ coarse A M) :
    rep A M q ∈ A ∧ rep A M q / M = q := by
  simp only [rep, dif_pos hq]
  exact Classical.choose_spec hq

lemma rep_bounds {A : Set ℕ} {M q : ℕ} (hM : 0 < M) (hq : q ∈ coarse A M) :
    q*M ≤ rep A M q ∧ rep A M q < (q+1)*M := by
  have hh := (rep_spec hq).2
  have h₁ := Nat.div_add_mod' (rep A M q) M
  have h₂ := Nat.mod_lt (rep A M q) hM
  rw [hh] at h₁
  constructor
  · omega
  · simp only [Nat.add_mul, Nat.one_mul]
    omega

/-- Each coarse representation can be injected into original representations
in an interval of length twice the block width. -/
theorem coarse_rep_le (A : Set ℕ) (M : ℕ) (hM : 0 < M) (q : ℕ) :
    sumRep (coarse A M) q ≤
      ∑ z ∈ Finset.Ico (q*M) ((q+2)*M), sumRep A z := by
  let N := (q+2)*M
  let B := cutoff A N
  have hrhs : (∑ z ∈ Finset.Ico (q*M) N, sumRep A z) =
      ((B.product B).filter (fun p ↦ p.1+p.2 ∈ Finset.Ico (q*M) N)).card := by
    calc
      _ = ∑ z ∈ Finset.Ico (q*M) N, pairs B B z := by
        apply Finset.sum_congr rfl
        intro z hz
        exact sumRep_eq_fiber_card A N z (Finset.mem_Ico.mp hz).2
      _ = _ := pairs_sum _ _ _
  rw [show (q+2)*M = N from rfl, hrhs, sumRep_def]
  apply Finset.card_le_card_of_injOn (fun p ↦ (rep A M p.1, rep A M p.2))
  · intro p hp
    obtain ⟨hp, ha, hb⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
    have hp' := Finset.mem_antidiagonal.mp hp
    have ha' := rep_spec ha
    have hb' := rep_spec hb
    have haB := rep_bounds hM ha
    have hbB := rep_bounds hM hb
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨mem_cutoff.mpr ⟨?_,ha'.1⟩,
      mem_cutoff.mpr ⟨?_,hb'.1⟩⟩, Finset.mem_Ico.mpr ⟨?_,?_⟩⟩ <;>
      dsimp [N] <;> nlinarith
  · intro p hp s hs he
    obtain ⟨_,hp₁,hp₂⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
    obtain ⟨_,hs₁,hs₂⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hs)
    have h₁ := congrArg (fun v : ℕ × ℕ ↦ v.1 / M) he
    have h₂ := congrArg (fun v : ℕ × ℕ ↦ v.2 / M) he
    dsimp at h₁ h₂
    rw [(rep_spec hp₁).2, (rep_spec hs₁).2] at h₁
    rw [(rep_spec hp₂).2, (rep_spec hs₂).2] at h₂
    exact Prod.ext h₁ h₂

/-- Coarsening by a fixed width preserves a logarithmic upper envelope. -/
theorem coarse_log_bound (A : Set ℕ) (M : ℕ) (hM : 0 < M) (K C : ℝ)
    (hC : 0 ≤ C)
    (hA : ∀ z, (sumRep A z : ℝ) ≤ K+C*Real.log ((z : ℝ)+2)) (q : ℕ) :
    (sumRep (coarse A M) q : ℝ) ≤
      (2*M : ℕ)*(K+C*Real.log (2*(M : ℝ))) +
        ((2*M : ℕ)*C)*Real.log ((q : ℝ)+2) := by
  have hl (z : ℕ) (hz : z ∈ Finset.Ico (q*M) ((q+2)*M)) :
      (sumRep A z : ℝ) ≤ K+C*(Real.log (2*(M : ℝ))+Real.log ((q : ℝ)+2)) := by
    have hzn := (Finset.mem_Ico.mp hz).2
    have hz' : z+2 ≤ 2*M*(q+2) := by nlinarith
    have hzp : (0 : ℝ) < (z : ℝ)+2 := by positivity
    have hbound : (z : ℝ)+2 ≤ 2*(M : ℝ)*((q : ℝ)+2) := by exact_mod_cast hz'
    have hlog := Real.log_le_log hzp hbound
    rw [Real.log_mul (by positivity) (by positivity)] at hlog
    exact (hA z).trans (by gcongr)
  have hc : (Finset.Ico (q*M) ((q+2)*M)).card = 2*M := by
    rw [Nat.card_Ico]
    have hh : q*M ≤ (q+2)*M := Nat.mul_le_mul_right M (by omega)
    simp only [Nat.add_mul, Nat.add_sub_cancel_left]
  calc
    (sumRep (coarse A M) q : ℝ) ≤
        ∑ z ∈ Finset.Ico (q*M) ((q+2)*M), (sumRep A z : ℝ) := by
      exact_mod_cast coarse_rep_le A M hM q
    _ ≤ ∑ _z ∈ Finset.Ico (q*M) ((q+2)*M),
        (K+C*(Real.log (2*(M : ℝ))+Real.log ((q : ℝ)+2))) := Finset.sum_le_sum hl
    _ = _ := by rw [Finset.sum_const, hc]; push_cast; ring

lemma tensor_digits (M : ℕ) (hM : 0 < M) (P S : Finset ℕ)
    (hS : ∀ s∈S, s < M) {d : ℕ} (hd : d ∈ tensor M P S) :
    d/M ∈ P ∧ d%M ∈ S := by
  obtain ⟨ps,hps,rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨hp,hs⟩ := Finset.mem_product.mp hps
  have hdiv : (ps.1*M+ps.2)/M=ps.1 := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt (hS _ hs)]
    omega
  have hmod : (ps.1*M+ps.2)%M=ps.2 := by
    simp only [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_eq_of_lt (hS _ hs)]
  rw [hdiv,hmod]
  exact ⟨hp,hs⟩

lemma tensor_disjoint (A : Set ℕ) (M : ℕ) (hM : 0 < M) (P S : Finset ℕ)
    (hS : ∀ s∈S, s < M) (hd : Disjoint (coarse A M) (P : Set ℕ)) :
    Disjoint A (tensor M P S : Set ℕ) := by
  apply Set.disjoint_left.mpr
  intro d hdA hdF
  exact Set.disjoint_left.mp hd ⟨d,hdA,rfl⟩ (tensor_digits M hM P S hS hdF).1

/-- The only two possible coarse sums of a fine mixed representation are the
fine quotient and its predecessor. Keeping the predecessor even at zero is
harmless for this upper bound. -/
theorem tensor_mixed_le (A : Set ℕ) (M : ℕ) (hM : 0 < M) (P S : Finset ℕ)
    (hS : ∀ s∈S, s < M) (n : ℕ) :
    mixed A (tensor M P S) n ≤
      (mixed (coarse A M) P (n/M) + mixed (coarse A M) P (n/M-1))*S.card := by
  let T (k : ℕ) := P.filter (fun p ↦ p ≤ k ∧ k-p ∈ coarse A M)
  have hh : mixed A (tensor M P S) n ≤ ((T (n/M) ∪ T (n/M-1)).product S).card := by
    apply Finset.card_le_card_of_injOn (fun d ↦ (d/M,d%M))
    · intro d hd
      obtain ⟨hdF,hdn,hdA⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hd)
      have hdPS := tensor_digits M hM P S hS hdF
      apply Finset.mem_product.mpr
      refine ⟨?_,hdPS.2⟩
      change d/M ∈ T (n/M) ∪ T (n/M-1)
      have he : n/M=d/M+(n-d)/M+(if M ≤ d%M+(n-d)%M then 1 else 0) := by
        conv_lhs => rw [←Nat.add_sub_of_le hdn]
        exact Nat.add_div hM
      have hnon := Nat.zero_le ((n-d)/M)
      have hbase : (n-d)/M ∈ coarse A M := ⟨n-d,hdA,rfl⟩
      by_cases hc : M ≤ d%M+(n-d)%M
      · rw [if_pos hc] at he
        apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        refine ⟨hdPS.1,by omega,?_⟩
        convert hbase using 1 <;> omega
      · rw [if_neg hc] at he
        apply Finset.mem_union_left
        apply Finset.mem_filter.mpr
        refine ⟨hdPS.1,by omega,?_⟩
        convert hbase using 1 <;> omega
    · intro d hd e he hde
      have hq := congrArg Prod.fst hde
      have hr := congrArg Prod.snd hde
      dsimp at hq hr
      have hd' := Nat.div_add_mod' d M
      have he' := Nat.div_add_mod' e M
      rw [hq,hr] at hd'
      omega
  calc
    _ ≤ ((T (n/M) ∪ T (n/M-1)).product S).card := hh
    _ = (T (n/M) ∪ T (n/M-1)).card*S.card := Finset.card_product _ _
    _ ≤ ((T (n/M)).card+(T (n/M-1)).card)*S.card :=
      Nat.mul_le_mul_right _ (Finset.card_union_le _ _)
    _ = _ := rfl

end Erdos66CoarseCounting
