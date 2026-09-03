import Submission.TransitionLinearExplore
import Submission.SummedBernoulliBoundsExplore
import Submission.MixedThinningExplore

/-! A variance-sensitive finite extension criterion with the old prefix held
fixed. This supplies a conditional first-window extension, not a sequence
of extensions satisfying the logarithmic conjecture. -/
namespace Erdos66LinearPrefixExtension
open AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66TransitionLinear
  Erdos66FiniteBernoulli Erdos66SummedBernoulliBounds Erdos66MixedThinning
open scoped Classical
set_option maxHeartbeats 1800000

noncomputable def newPoints (N L : ℕ) (ω : Fin L → Bool) : Finset ℕ :=
  (Finset.univ.filter (fun i ↦ ω i=true)).image (fun i ↦ N+i.val)

lemma newPoint_embedding (N L : ℕ) : Function.Injective (fun i : Fin L ↦ N+i.val) := by
  intro i j hij
  exact Fin.ext (Nat.add_left_cancel hij)

lemma newPoints_bounds (N L : ℕ) (ω : Fin L → Bool) {x : ℕ}
    (hx : x∈newPoints N L ω) : N ≤ x ∧ x<N+L := by
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
  have hi := i.isLt
  omega

noncomputable def coefficient (N : ℕ) (B : Finset ℕ) (n : ℕ) {L : ℕ} (i : Fin L) : ℝ :=
  if N+i.val ≤ n ∧ n-(N+i.val)∈B then 2 else 0

lemma coefficient_bounds (N : ℕ) (B : Finset ℕ) (n : ℕ) {L : ℕ} (i : Fin L) :
    0 ≤ coefficient N B n i ∧ coefficient N B n i ≤ 2 := by
  unfold coefficient
  split_ifs <;> norm_num

noncomputable def mixedMean (N : ℕ) (B : Finset ℕ) (n : ℕ) {L : ℕ} (p : Fin L → ℝ) : ℝ :=
  ∑ i, coefficient N B n i*p i

lemma mixed_increment_bits (N L : ℕ) (B : Finset ℕ) (ω : Fin L → Bool) (n : ℕ) :
    2*(pairs B (newPoints N L ω) n:ℝ)=∑ i, coefficient N B n i*bit (ω i) := by
  rw [pairs_comm,pairs_eq_filter]
  unfold newPoints
  rw [Finset.filter_image,Finset.card_image_of_injective _ (newPoint_embedding N L),
    Finset.filter_filter,Finset.card_filter]
  simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [coefficient,bit]
  by_cases hh : N+i.val ≤ n ∧ n-(N+i.val)∈B <;> cases hω : ω i <;> simp [hh,hω]

/-- Exact first-window formula for a Boolean choice of new points. -/
lemma extension_count_bits (N L : ℕ) (B : Finset ℕ)
    (hB : ∀ b∈B, b<N) (ω : Fin L → Bool) (n : ℕ) (hn : n<2*N) :
    (sumRep ((B∪newPoints N L ω : Finset ℕ):Set ℕ) n:ℝ)=
      sumRep (B:Set ℕ) n+∑ i, coefficient N B n i*bit (ω i) := by
  rw [transition_exact B _ N n hB (fun b hb ↦ (newPoints_bounds N L ω hb).1) hn]
  push_cast
  rw [mixed_increment_bits]

/-- The scale in the concentration criterion is the NEW mixed mean. The
already fixed old/old contribution is not charged as random variance. -/
theorem exists_linear_prefix_extension (N L : ℕ) (B : Finset ℕ)
    (hB : ∀ b∈B, b<N) (p : Fin L → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset ℕ) (hS : ∀ n∈S, n<2*N) (V : ℕ → ℝ) (ε : ℝ)
    (hε : 0<ε) (hε1 : ε ≤ 1) (hm : ∀ n∈S, mixedMean N B n p ≤ V n)
    (hbudget : (∑ n∈S, 2*Real.exp (-ε^2*V n/8))<1) :
    ∃ F : Finset ℕ, F ⊆ Finset.Ico N (N+L) ∧ Disjoint B F ∧
      (∀ a<N, a∈B∪F ↔ a∈B) ∧
      (∀ n<N, sumRep ((B∪F:Finset ℕ):Set ℕ) n=sumRep (B:Set ℕ) n) ∧
      ∀ n∈S, |(sumRep ((B∪F:Finset ℕ):Set ℕ) n:ℝ)-
        ((sumRep (B:Set ℕ) n:ℝ)+mixedMean N B n p)|<ε*V n := by
  obtain ⟨ω,hw,hω⟩ := exists_summed_bound p hp S
    (fun n ω ↦ ∑ i, coefficient N B n i*bit (ω i)) (fun n ↦ mixedMean N B n p)
    V ε hε hε1 hm (fun n hn t ht ↦ by
      exact linear_centered_mgf p hp (coefficient N B n)
        (coefficient_bounds N B n) t ht) hbudget
  refine ⟨newPoints N L ω,?_,cutoff_disjoint B _ N hB
    (fun b hb ↦ (newPoints_bounds N L ω hb).1),?_,?_,?_⟩
  · intro a ha
    exact Finset.mem_Ico.mpr (newPoints_bounds N L ω ha)
  · intro a ha
    have hnot : a∉newPoints N L ω := by intro hh; have := (newPoints_bounds N L ω hh).1; omega
    simp [hnot]
  · intro n hn
    exact unchanged_below_cutoff B _ N n hB (fun b hb ↦ (newPoints_bounds N L ω hb).1) hn
  · intro n hn
    rw [extension_count_bits N L B hB ω n (hS n hn)]
    have he : (sumRep (B:Set ℕ) n:ℝ)+(∑ i, coefficient N B n i*bit (ω i))-
        ((sumRep (B:Set ℕ) n:ℝ)+mixedMean N B n p)=
      (∑ i, coefficient N B n i*bit (ω i))-mixedMean N B n p := by ring
    rw [he]
    exact hω n hn


/-- Local mean bound: only old points below n-N can participate in a new
mixed pair at n. There is no charge for the rest of the old prefix. -/
lemma mixedMean_local_bound (N L : ℕ) (B : Finset ℕ) (n : ℕ)
    (p : Fin L → ℝ) (v : ℝ) (hv : 0 ≤ v) (hp : ∀ i, p i ≤ v) :
    mixedMean N B n p ≤ 2*v*((B.filter (fun a ↦ a ≤ n-N)).card:ℝ) := by
  let E : Finset (Fin L) := Finset.univ.filter (fun i ↦ N+i.val ≤ n ∧ n-(N+i.val)∈B)
  have hE (i : Fin L) : i∈E ↔ N+i.val ≤ n ∧ n-(N+i.val)∈B := by simp [E]
  have hcard : E.card ≤ (B.filter (fun a ↦ a ≤ n-N)).card := by
    apply Finset.card_le_card_of_injOn (fun i : Fin L ↦ n-(N+i.val))
    · intro i hi
      obtain ⟨hni,hiB⟩ := (hE i).mp hi
      exact Finset.mem_filter.mpr ⟨hiB,by change n-(N+i.val) ≤ n-N; omega⟩
    · intro i hi j hj he
      have hni := ((hE i).mp hi).1
      have hnj := ((hE j).mp hj).1
      apply Fin.ext
      dsimp only at he
      omega
  have he : mixedMean N B n p=2*(∑ i∈E, p i) := by
    unfold mixedMean
    rw [Finset.mul_sum]
    dsimp only [E]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    unfold coefficient
    split_ifs <;> ring
  rw [he]
  have hs : (∑ i∈E, p i) ≤ E.card*v := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum (fun i hi ↦ hp i)
  have hc : (E.card:ℝ) ≤ (B.filter (fun a ↦ a ≤ n-N)).card := by exact_mod_cast hcard
  nlinarith only [hs,mul_le_mul_of_nonneg_right hc hv]

/-- A necessary deterministic capacity bound for every extension, not just
for a random selection. The old point must be at most n-N. -/
lemma first_window_capacity (N n : ℕ) (B F : Finset ℕ)
    (hB : ∀ b∈B, b<N) (hF : ∀ f∈F, N ≤ f) (hn : n<2*N) :
    sumRep ((B∪F:Finset ℕ):Set ℕ) n ≤ sumRep (B:Set ℕ) n+
      2*(B.filter (fun a ↦ a ≤ n-N)).card := by
  rw [transition_exact B F N n hB hF hn]
  have hh : pairs B F n ≤ (B.filter (fun a ↦ a ≤ n-N)).card := by
    rw [pairs_eq_filter]
    apply Finset.card_le_card
    intro a ha
    obtain ⟨ha,han,hna⟩ := Finset.mem_filter.mp ha
    have hnew := hF (n-a) hna
    exact Finset.mem_filter.mpr ⟨ha,by omega⟩
  omega

/-- At the cutoff itself, adding an arbitrary tail can supply at most two
ordered representations. A substantial deficit there is already irreversible. -/
lemma cutoff_capacity (N : ℕ) (hN : 0<N) (B F : Finset ℕ)
    (hB : ∀ b∈B, b<N) (hF : ∀ f∈F, N ≤ f) :
    sumRep ((B∪F:Finset ℕ):Set ℕ) N ≤ sumRep (B:Set ℕ) N+2 := by
  have hh := first_window_capacity N N B F hB hF (by omega)
  have hc : (B.filter (fun a ↦ a ≤ N-N)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ha := (Finset.mem_filter.mp ha).2
    have hb := (Finset.mem_filter.mp hb).2
    omega
  omega

/-- The conditional mean must itself fit the desired profile. This theorem
keeps that hypothesis explicit rather than inferring it from past accuracy. -/
theorem exists_profile_prefix_extension (N L : ℕ) (B : Finset ℕ)
    (hB : ∀ b∈B, b<N) (p : Fin L → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset ℕ) (hS : ∀ n∈S, n<2*N) (V q E : ℕ → ℝ) (ε : ℝ)
    (hε : 0<ε) (hε1 : ε ≤ 1) (hm : ∀ n∈S, mixedMean N B n p ≤ V n)
    (hbias : ∀ n∈S, |((sumRep (B:Set ℕ) n:ℝ)+mixedMean N B n p)-q n| ≤ E n)
    (hbudget : (∑ n∈S, 2*Real.exp (-ε^2*V n/8))<1) :
    ∃ F : Finset ℕ, F ⊆ Finset.Ico N (N+L) ∧ Disjoint B F ∧
      (∀ a<N, a∈B∪F ↔ a∈B) ∧
      (∀ n<N, sumRep ((B∪F:Finset ℕ):Set ℕ) n=sumRep (B:Set ℕ) n) ∧
      ∀ n∈S, |(sumRep ((B∪F:Finset ℕ):Set ℕ) n:ℝ)-q n|<E n+ε*V n := by
  obtain ⟨F,hF,hd,hmem,hpast,hgood⟩ := exists_linear_prefix_extension N L B hB p hp S hS V ε
    hε hε1 hm hbudget
  refine ⟨F,hF,hd,hmem,hpast,fun n hn ↦ ?_⟩
  have hh := abs_sub_le (sumRep ((B∪F:Finset ℕ):Set ℕ) n:ℝ)
    ((sumRep (B:Set ℕ) n:ℝ)+mixedMean N B n p) (q n)
  linarith [hgood n hn,hbias n hn]

end Erdos66LinearPrefixExtension

