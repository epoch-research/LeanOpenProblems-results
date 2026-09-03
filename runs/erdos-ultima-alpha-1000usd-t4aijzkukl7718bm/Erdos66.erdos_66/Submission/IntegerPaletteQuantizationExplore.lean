import Submission.IntegerPaletteAssemblyExplore

/-! Quantizing a finite step profile with a complete cyclic palette, followed
by actual integer assembly. This does not construct compatible infinite scales. -/
namespace Erdos66IntegerPaletteQuantization
open AdditiveCombinatorics Erdos66IntegerPaletteAssembly Erdos66IntegerPaletteSlices
  Erdos66OuterMixedPrefix Erdos66SaturatingCyclicFamily
open scoped Classical
set_option maxHeartbeats 3000000

variable (M : ℕ) [NeZero M]

noncomputable def overlap (a b c d n : ℕ) : ℝ :=
  ((cutHi b c n:ℝ)-cutLo a b c d n)/M

lemma overlap_bounds (a b c d n : ℕ) (hb : b ≤ M) :
    0 ≤ overlap M a b c d n ∧ overlap M a b c d n ≤ 1 := by
  have hM : (0:ℝ)<M := by exact_mod_cast NeZero.pos M
  have hlo : (cutLo a b c d n:ℝ) ≤ cutHi b c n := by exact_mod_cast cutLo_le_cutHi a b c d n
  have hhi : (cutHi b c n:ℝ) ≤ M := by exact_mod_cast (cutHi_le b c n).trans hb
  have hl0 : (0:ℝ) ≤ cutLo a b c d n := by positivity
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlo) hM.le
  · apply (div_le_iff₀ hM).mpr
    linarith

noncomputable def weightedProfile {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (a b : ι → ℕ) (n : ℕ) : ℝ :=
  ∑ i∈s, ∑ j∈s, overlap M (a i) (b i) (a j) (b j) n*(w i*w j)

lemma weightedProfile_bounds {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (a b : ι → ℕ) (hw : ∀ i∈s, 0 ≤ w i) (hb : ∀ i∈s, b i ≤ M) (n : ℕ) :
    0 ≤ weightedProfile M s w a b n ∧ weightedProfile M s w a b n ≤ (∑ i∈s, w i)^2 := by
  constructor
  · exact Finset.sum_nonneg (fun i hi ↦ Finset.sum_nonneg (fun j hj ↦
      mul_nonneg (overlap_bounds M _ _ _ _ _ (hb i hi)).1 (mul_nonneg (hw i hi) (hw j hj))))
  · rw [weightedProfile,pow_two,Finset.sum_mul_sum]
    exact Finset.sum_le_sum (fun i hi ↦ Finset.sum_le_sum (fun j hj ↦
      mul_le_of_le_one_left (mul_nonneg (hw i hi) (hw j hj)) (overlap_bounds M _ _ _ _ _ (hb i hi)).2))

lemma quantized_mean_bracket (B C D : Finset (ZMod M)) (u v R : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hR : 0 ≤ R)
    (hC : u*(B.card:ℝ) ≤ C.card ∧ (C.card:ℝ) ≤ R*u*B.card)
    (hD : v*(B.card:ℝ) ≤ D.card ∧ (D.card:ℝ) ≤ R*v*B.card) :
    actualMean M B B*(u*v) ≤ actualMean M C D ∧
      actualMean M C D ≤ R^2*actualMean M B B*(u*v) := by
  have hq : (0:ℝ) ≤ B.card := by positivity
  have hl := div_le_div_of_nonneg_right
    (mul_le_mul hC.1 hD.1 (mul_nonneg hv hq) (Nat.cast_nonneg C.card)) (Nat.cast_nonneg M)
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul hC.2 hD.2 (Nat.cast_nonneg D.card) (by positivity)) (Nat.cast_nonneg M)
  constructor
  · convert hl using 1 <;> dsimp [actualMean] <;> ring
  · convert hh using 1 <;> dsimp [actualMean] <;> ring

lemma quantized_profile_bracket {ι : Type*} (s : Finset ι)
    (B : Finset (ZMod M)) (C : ι → Finset (ZMod M)) (w : ι → ℝ) (a b : ι → ℕ)
    (R : ℝ) (hR : 0 ≤ R) (hw : ∀ i∈s, 0 ≤ w i) (hb : ∀ i∈s, b i ≤ M)
    (hcard : ∀ i∈s, w i*(B.card:ℝ) ≤ (C i).card ∧ ((C i).card:ℝ) ≤ R*w i*B.card) (n : ℕ) :
    actualMean M B B*weightedProfile M s w a b n ≤ profile M s C a b n ∧
      profile M s C a b n ≤ R^2*actualMean M B B*weightedProfile M s w a b n := by
  have hp i hi j hj := quantized_mean_bracket M B (C i) (C j) (w i) (w j) R
    (hw i hi) (hw j hj) hR (hcard i hi) (hcard j hj)
  constructor
  · simp only [weightedProfile,profile,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have hh := mul_le_mul_of_nonneg_left (hp i hi j hj).1 (overlap_bounds M (a i) (b i) (a j) (b j) n (hb i hi)).1
    dsimp [overlap] at hh ⊢
    nlinarith only [hh]
  · simp only [weightedProfile,profile,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have hh := mul_le_mul_of_nonneg_left (hp i hi j hj).2 (overlap_bounds M (a i) (b i) (a j) (b j) n (hb i hi)).1
    dsimp [overlap] at hh ⊢
    nlinarith only [hh]

/-- Error for actual integer sets after spatial and cardinality quantization. -/
theorem quantized_assembly_error {ι : Type*} (s : Finset ι)
    (B : Finset (ZMod M)) (C : ι → Finset (ZMod M)) (w : ι → ℝ) (a b : ι → ℕ)
    (hdisj : ∀ i∈s, ∀ j∈s, i ≠ j → b i ≤ a j ∨ b j ≤ a i)
    (hb : ∀ i∈s, b i ≤ M) (hw : ∀ i∈s, 0 ≤ w i)
    (R η : ℝ) (hR : 1 ≤ R) (hη : 0 ≤ η)
    (hcard : ∀ i∈s, w i*(B.card:ℝ) ≤ (C i).card ∧ ((C i).card:ℝ) ≤ R*w i*B.card)
    (hprefix : ∀ i∈s, ∀ j∈s, ∀ z u, u ≤ M →
      |(prefixCount M (C i) (C j) z u:ℝ)-(u:ℝ)/M*actualMean M (C i) (C j)| ≤
        η*actualMean M (C i) (C j)) (n : ℕ) :
    |(sumRep (assembled M s C a b : Set ℕ) n:ℝ)-actualMean M B B*weightedProfile M s w a b n| ≤
      ((1+2*η)*R^2-1)*actualMean M B B*(∑ i∈s, w i)^2 := by
  have hR0 : 0 ≤ R := by linarith
  have hq : (0:ℝ) ≤ B.card := by positivity
  have hW : 0 ≤ ∑ i∈s, w i := Finset.sum_nonneg hw
  have hμ : 0 ≤ actualMean M B B := actualMean_nonneg M B B
  have hcards : (∑ i∈s, ((C i).card:ℝ)) ≤ R*(B.card:ℝ)*(∑ i∈s, w i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    nlinarith only [(hcard i hi).2]
  have hsq := pow_le_pow_left₀ (Finset.sum_nonneg (fun i hi ↦ Nat.cast_nonneg _)) hcards 2
  have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 2*η/(M:ℝ) by positivity)
  have he : (2*η/M)*(R*(B.card:ℝ)*(∑ i∈s, w i))^2 =
      2*η*R^2*actualMean M B B*(∑ i∈s, w i)^2 := by dsimp [actualMean]; ring
  rw [he] at hmul
  have hround := (assembled_profile_error M s C a b hdisj hb η hprefix n).trans hmul
  obtain ⟨hl,hu⟩ := quantized_profile_bracket M s B C w a b R hR0 hw hb hcard n
  obtain ⟨hF0,hF⟩ := weightedProfile_bounds M s w a b hw hb n
  have hR2 : 0 ≤ R^2-1 := by nlinarith
  have hquant : |profile M s C a b n-actualMean M B B*weightedProfile M s w a b n| ≤
      (R^2-1)*actualMean M B B*(∑ i∈s, w i)^2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hl)]
    have hh := mul_le_mul_of_nonneg_left hF (mul_nonneg hR2 hμ)
    nlinarith only [hu,hh]
  have htri := abs_sub_le (sumRep (assembled M s C a b : Set ℕ) n:ℝ)
    (profile M s C a b n) (actualMean M B B*weightedProfile M s w a b n)
  nlinarith only [htri,hround,hquant]

/-- Palette coverage selects all the required levels in ONE palette. -/
theorem exists_quantized_assembly {ι : Type*} (s : Finset ι)
    (B : Finset (ZMod M)) (P : Finset (Finset (ZMod M)))
    (w : ι → ℝ) (a b : ι → ℕ)
    (hw : ∀ i∈s, 1 ≤ w i) (hfit : ∀ i∈s, w i*(B.card:ℝ) ≤ M)
    (hdisj : ∀ i∈s, ∀ j∈s, i ≠ j → b i ≤ a j ∨ b j ≤ a i)
    (hb : ∀ i∈s, b i ≤ M) (ε η : ℝ) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hcover : ∀ x : ℝ, (B.card:ℝ) ≤ x → x ≤ M →
      ∃ C∈P, x ≤ (C.card:ℝ) ∧ (C.card:ℝ) ≤ (1+ε)*x)
    (hprefix : ∀ C∈P, ∀ D∈P, ∀ z u, u ≤ M →
      |(prefixCount M C D z u:ℝ)-(u:ℝ)/M*actualMean M C D| ≤ η*actualMean M C D) :
    ∃ A : Finset ℕ, A ⊆ Finset.range M ∧ ∀ n : ℕ,
      |(sumRep (A:Set ℕ) n:ℝ)-actualMean M B B*weightedProfile M s w a b n| ≤
        ((1+2*η)*(1+ε)^2-1)*actualMean M B B*(∑ i∈s, w i)^2 := by
  have hchoose : ∀ i, ∃ C : Finset (ZMod M), i∈s → C∈P ∧
      w i*(B.card:ℝ) ≤ C.card ∧ (C.card:ℝ) ≤ (1+ε)*w i*B.card := by
    intro i
    by_cases hi : i∈s
    · have hlow : (B.card:ℝ) ≤ w i*B.card := le_mul_of_one_le_left (by positivity) (hw i hi)
      obtain ⟨C,hCP,hl,hu⟩ := hcover (w i*B.card) hlow (hfit i hi)
      exact ⟨C,fun _ ↦ ⟨hCP,hl,by nlinarith only [hu]⟩⟩
    · exact ⟨B,fun hh ↦ False.elim (hi hh)⟩
  choose C hC using hchoose
  refine ⟨assembled M s C a b,?_,fun n ↦ ?_⟩
  · intro x hx
    obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_range.mpr ((mem_slice M (C i) (a i) (b i) x).mp hx).1
  · exact quantized_assembly_error M s B C w a b hdisj hb
      (fun i hi ↦ by linarith [hw i hi]) (1+ε) η (by linarith) hη
      (fun i hi ↦ (hC i hi).2) (fun i hi j hj ↦ hprefix _ (hC i hi).1 _ (hC j hj).1) n

end Erdos66IntegerPaletteQuantization
