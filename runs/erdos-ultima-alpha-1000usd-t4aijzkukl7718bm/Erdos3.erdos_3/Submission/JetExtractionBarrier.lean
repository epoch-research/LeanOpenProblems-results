import Submission.DigitPolynomialCase
import Submission.WeightedIntersectionCheck

/-! A barrier to extracting the finite binary-jet invariant special case from an arbitrary
reciprocal-divergent set. This is not a disproof of Erdős Problem 3. -/
namespace Erdos3JetExtractionBarrier
open Polynomial Erdos3DigitPolynomialCase Erdos3FiniteKernelCase
  Erdos3BinarySymmetryCase Erdos3WeightedIntersectionCheck
open scoped Classical
set_option maxHeartbeats 2000000

lemma count_digits_ofDigits {q a : ℕ} (hq : 1 < q) (ha : a ≠ 0)
    (w : List ℕ) (hw : ∀ b ∈ w, b < q) :
    (Nat.digits q (Nat.ofDigits q w)).count a = w.count a := by
  have he := congrArg (List.count a)
    ((Nat.setInvOn_digitsAppend_ofDigits hq w.length).1 ⟨rfl,hw⟩)
  simpa [Nat.digitsAppend, List.count_replicate, ha, Ne.symm ha] using he

def blockColor (q a n : ℕ) : Fin 2 :=
  ⟨(Nat.digits q n).count a % 2, Nat.mod_lt _ (by norm_num)⟩

/-- Replacing a nonzero base-q digit a by a different digit flips its count parity. -/
lemma blockColor_ne {q a b : ℕ} (hq : 1 < q) (ha : 0 < a)
    (haq : a < q) (hbq : b < q) (hab : a ≠ b)
    (j s t : ℕ) (hs : s < q^j) :
    blockColor q a (q^j*(q*t+a)+s) ≠ blockColor q a (q^j*(q*t+b)+s) := by
  let lo := Nat.digitsAppend q j s
  let hi := Nat.digits q t
  have hlo : lo.length = j := Nat.length_digitsAppend hq j hs
  have hlo' : ∀ c ∈ lo, c < q := Nat.lt_of_mem_digitsAppend hq j
  have hhi : ∀ c ∈ hi, c < q := fun c hc ↦ Nat.digits_lt_base hq hc
  have hw (c : ℕ) (hc : c < q) : ∀ d ∈ lo ++ [c] ++ hi, d < q := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · rcases List.mem_append.mp hd with hd | hd
      · exact hlo' d hd
      · simpa using (List.mem_singleton.mp hd) ▸ hc
    · exact hhi d hd
  have hv (c : ℕ) : Nat.ofDigits q (lo ++ [c] ++ hi) = q^j*(q*t+c)+s := by
    simp only [Nat.ofDigits_append, Nat.ofDigits_cons, Nat.ofDigits_nil,
      List.length_append, List.length_singleton, hlo]
    have hlov : Nat.ofDigits q lo = s := by simp [lo, Nat.digitsAppend, Nat.ofDigits_digits]
    have hhiv : Nat.ofDigits q hi = t := Nat.ofDigits_digits q t
    rw [hlov, hhiv, pow_succ]
    ring
  have hca := count_digits_ofDigits hq ha.ne' _ (hw a haq)
  have hcb := count_digits_ofDigits hq ha.ne' _ (hw b hbq)
  rw [hv] at hca hcb
  simp only [List.count_append, List.count_cons, List.count_nil] at hca hcb
  simp only [beq_self_eq_true, ↓reduceIte, Nat.zero_add, beq_iff_eq,
    hab, Ne.symm hab, ↓reduceIte] at hca hcb
  intro he
  have he' := congrArg Fin.val he
  change (Nat.digits q (q^j*(q*t+a)+s)).count a % 2 =
    (Nat.digits q (q^j*(q*t+b)+s)).count a % 2 at he'
  rw [hca, hcb] at he'
  omega

/-- Monochromaticity and closure under a fixed digit replacement force summability. -/
theorem monochromatic_replacement_summable {A : Set ℕ} {q a b : ℕ}
    (hq : 1 < q) (ha : 0 < a) (haq : a < q) (hbq : b < q) (hab : a ≠ b)
    (hclosed : ∀ j s t, s < q^j →
      q^j*(q*t+a)+s ∈ A → q^j*(q*t+b)+s ∈ A)
    (hmono : ∀ x ∈ A, ∀ y ∈ A, blockColor q a x = blockColor q a y) :
    Summable (fun n : A ↦ 1 / (n : ℝ)) := by
  let K : Set (Set ℕ) := {B | ∃ j s, s < q^j ∧ B = sectionSet A (q^j) s}
  have hself : A ∈ K := by
    refine ⟨0,0,by simp,?_⟩
    ext n
    simp [sectionSet]
  have hKclosed : ∀ B ∈ K, ∀ c < q, sectionSet B q c ∈ K := by
    rintro B ⟨j,s,hs,rfl⟩ c hc
    refine ⟨j+1,q^j*c+s,?_,?_⟩
    · rw [pow_succ]
      have hmul := Nat.mul_le_mul_left (q^j) (Nat.succ_le_of_lt hc)
      nlinarith
    · rw [section_section, pow_succ]
  have hholes : ∀ B ∈ K, ∃ c < q, sectionSet B q c = ∅ := by
    rintro B ⟨j,s,hs,rfl⟩
    refine ⟨a,haq,Set.eq_empty_iff_forall_notMem.mpr ?_⟩
    intro t ht
    change q^j*(q*t+a)+s ∈ A at ht
    exact blockColor_ne hq ha haq hbq hab j s t hs
      (hmono _ ht _ (hclosed j s t hs ht))
  apply summable_of_count_pow_bound hq
  intro j
  exact count_pow_le_of_holes K q hKclosed hholes j A hself

lemma jet_block_replacement {A : Set ℕ} {r L a b : ℕ}
    (hA : JetInvariant A r) (u v : List ℕ)
    (hu : ∀ c ∈ u, c < 2) (hv : ∀ c ∈ v, c < 2)
    (hul : u.length = L) (hvl : v.length = L)
    (hua : Nat.ofDigits 2 u = a) (hvb : Nat.ofDigits 2 v = b)
    (hjet : (X-1 : ℤ[X])^r ∣ wordPoly v-wordPoly u)
    (j s t : ℕ) (hs : s < (2^L)^j)
    (hn : (2^L)^j*(2^L*t+a)+s ∈ A) :
    (2^L)^j*(2^L*t+b)+s ∈ A := by
  let lo := Nat.digitsAppend 2 (L*j) s
  let hi := Nat.digits 2 t
  have hlo : lo.length = L*j :=
    Nat.length_digitsAppend (by norm_num : 1 < 2) (L*j) (by simpa [pow_mul] using hs)
  have hlo' : ∀ c ∈ lo, c < 2 := Nat.lt_of_mem_digitsAppend (by norm_num : 1 < 2) (L*j)
  have hhi : ∀ c ∈ hi, c < 2 := fun c hc ↦ Nat.digits_lt_base (by norm_num) hc
  have hw (w : List ℕ) (hw : ∀ c ∈ w, c < 2) : ∀ c ∈ lo ++ w ++ hi, c < 2 := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact (List.mem_append.mp hc).elim (hlo' c) (hw c)
    · exact hhi c hc
  have he (w : List ℕ) (hl : w.length = L) : Nat.ofDigits 2 (lo ++ w ++ hi) =
      (2^L)^j*(2^L*t+Nat.ofDigits 2 w)+s := by
    simp only [Nat.ofDigits_append, List.length_append, hlo, hl]
    rw [show Nat.ofDigits 2 lo = s from padded_value (L*j) s,
      show Nat.ofDigits 2 hi = t from Nat.ofDigits_digits 2 t, pow_add, pow_mul]
    ring
  have hj : (X-1 : ℤ[X])^r ∣ wordPoly (lo ++ v ++ hi)-wordPoly (lo ++ u ++ hi) := by
    rw [wordPoly_sandwich _ _ _ _ (hvl.trans hul.symm)]
    exact dvd_mul_of_dvd_right hjet _
  have hn' : Nat.ofDigits 2 (lo ++ u ++ hi) ∈ A := by simpa only [he u hul, hua] using hn
  have hres := hA _ _ (hw u hu) (hw v hv) (by simp only [List.length_append, hul, hvl]) hj hn'
  simpa only [he v hvl, hvb] using hres

/-- A binary coloring prevents any eventually monochromatic finite-jet invariant set
from having divergent reciprocal sum. -/
theorem exists_jet_separator (r : ℕ) :
    ∃ color : ℕ → Fin 2, ∀ A : Set ℕ, JetInvariant A r →
      (∃ F : Finset ℕ, ∀ x ∈ A, ∀ y ∈ A, x ∉ F → y ∉ F → color x = color y) →
      Summable (fun a : A ↦ 1 / (a : ℝ)) := by
  obtain ⟨L,a,d,hL,hd,w,hlen,hbin,hval,hjet⟩ := binary_jet_progression r 3
  let u := w ⟨1,by norm_num⟩
  let v := w ⟨2,by norm_num⟩
  have hu : Nat.ofDigits 2 u = a+d := by simpa [u] using hval ⟨1,by norm_num⟩
  have hv : Nat.ofDigits 2 v = a+2*d := by simpa [v] using hval ⟨2,by norm_num⟩
  have hq : 1 < 2^L := one_lt_pow₀ one_lt_two hL.ne'
  have haq : a+d < 2^L := by
    have h := Nat.ofDigits_lt_base_pow_length (by norm_num : 1 < 2) (hbin ⟨1,by norm_num⟩)
    simpa only [← hu, u, hlen] using h
  have hbq : a+2*d < 2^L := by
    have h := Nat.ofDigits_lt_base_pow_length (by norm_num : 1 < 2) (hbin ⟨2,by norm_num⟩)
    simpa only [← hv, v, hlen] using h
  refine ⟨blockColor (2^L) (a+d),?_⟩
  rintro A hA ⟨F,hF⟩
  by_contra hs
  let M := F.sup id
  let B := A ∩ Set.Ioi M
  have hB : ¬ Summable (fun b : B ↦ 1 / (b : ℝ)) := nonsummable_tail hs M
  apply hB
  apply monochromatic_replacement_summable hq (by omega : 0 < a+d) haq hbq (by omega : a+d ≠ a+2*d)
  · intro j s t hs hn
    have hn' := jet_block_replacement hA u v (hbin _) (hbin _) (hlen _) (hlen _)
      hu hv (hjet _ _) j s t hs hn.1
    refine ⟨hn',?_⟩
    have hm := hn.2
    change M < (2^L)^j*(2^L*t+(a+2*d))+s
    apply hm.trans_le
    gcongr
    omega
  · intro x hx y hy
    apply hF x hx.1 y hy.1
    · intro hxF
      have hle : x ≤ M := Finset.le_sup (f := id) hxF
      exact (not_lt_of_ge hle) hx.2
    · intro hyF
      have hle : y ≤ M := Finset.le_sup (f := id) hyF
      exact (not_lt_of_ge hle) hy.2

/-- Every divergent set has a divergent subset containing no divergent finite-jet
invariant subset, even when the jet order may be chosen after the subset. -/
theorem divergent_subset_without_jet_invariant_subsets {A : Set ℕ}
    (hA : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) :
    ∃ B ⊆ A, (¬ Summable (fun b : B ↦ 1 / (b : ℝ))) ∧
      ∀ C ⊆ B, ∀ r : ℕ, JetInvariant C r → Summable (fun c : C ↦ 1 / (c : ℝ)) := by
  choose color hcolor using exists_jet_separator
  obtain ⟨B,hBA,hB,hmono⟩ := Erdos3ThinningCheck.nonsummable_eventually_monochromatic color hA
  refine ⟨B,hBA,hB,?_⟩
  intro C hCB r hC
  obtain ⟨F,hF⟩ := hmono r
  exact hcolor r C hC ⟨F,fun x hx y hy ↦ hF x (hCB hx) y (hCB hy)⟩

/-- This negates only a proposed auxiliary extraction principle, not Erdős Problem 3. -/
theorem no_divergent_jet_invariant_extraction :
    ¬ (∀ A : Set ℕ, (¬ Summable (fun a : A ↦ 1 / (a : ℝ))) →
      ∃ B ⊆ A, (¬ Summable (fun b : B ↦ 1 / (b : ℝ))) ∧ ∃ r, JetInvariant B r) := by
  intro h
  obtain ⟨A,hA,_⟩ := Erdos3ThinningCheck.exists_divergent_affine_thin
  obtain ⟨B,hBA,hB,hbarrier⟩ := divergent_subset_without_jet_invariant_subsets hA
  obtain ⟨C,hCB,hC,r,hr⟩ := h B hB
  exact hC (hbarrier C hCB r hr)

#print axioms blockColor_ne
#print axioms exists_jet_separator
#print axioms divergent_subset_without_jet_invariant_subsets
#print axioms no_divergent_jet_invariant_extraction
end Erdos3JetExtractionBarrier
