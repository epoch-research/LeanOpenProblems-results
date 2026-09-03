import Submission.BinarySupportedSubspaceExplore
import Submission.DigitLoopPeakExplore
import Submission.Explore

/-! Natural sum-representation peaks in arbitrary binary linear codes.
No Cartesian product decomposition of the code is required. -/
namespace Erdos66BinaryLinearCodePeak
open Module Erdos66BinaryZeroSpan Erdos66BinarySupportedSubspace
  Erdos66DigitLoopPeak AdditiveCombinatorics
open scoped Classical Topology
set_option maxHeartbeats 1800000

noncomputable def encode {n : ℕ} (x : Fin n → F) : ℕ :=
  Nat.ofDigits 2 (List.ofFn (fun i ↦ (x i).val))

lemma encode_injective {n : ℕ} : Function.Injective (@encode n) := by
  intro x y h
  have he := Nat.ofDigits_inj_of_len_eq (by norm_num : 1<2)
    (by simp : (List.ofFn (fun i ↦ (x i).val)).length=(List.ofFn (fun i ↦ (y i).val)).length)
    (by intro a ha; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha; exact (x i).val_lt)
    (by intro a ha; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha; exact (y i).val_lt) h
  have hf := List.ofFn_injective he
  funext i
  exact ZMod.val_injective 2 (congrFun hf i)

lemma encode_lt {n : ℕ} (x : Fin n → F) : encode x<2^n := by
  have he := Nat.ofDigits_lt_base_pow_length (by norm_num : 1<2)
    (l := List.ofFn (fun i ↦ (x i).val))
    (by intro a ha; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha; exact (x i).val_lt)
  simpa only [List.length_ofFn] using he

lemma encode_sum_of_digits {n : ℕ} (x y z : Fin n → F)
    (h : ∀ i, (x i).val+(y i).val=(z i).val) : encode x+encode y=encode z := by
  unfold encode
  rw [Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq (by simp)]
  congr 1
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_zipWith,List.getElem_ofFn]
  exact h _

lemma encode_complement {n : ℕ} (c x : Fin n → F)
    (h : ∀ i, c i=0 → x i=0) : encode x+encode (c+x)=encode c := by
  apply encode_sum_of_digits
  intro i
  change (x i).val+(c i+x i).val=(c i).val
  rcases bit_cases (c i) with hc | hc
  · have hx := h i hc
    simp [hc,hx]
  · rcases bit_cases (x i) with hx | hx <;>
      simp [hc,hx,show (1:F)+1=0 by decide]

noncomputable def codeSet {n : ℕ} (C : Submodule F (Fin n → F)) : Set ℕ :=
  Set.range (fun x : C ↦ encode x.val)

/-- The supporting subspace is injected into ordered natural representations.
The coordinatewise sum is carry-free; no modular count is substituted. -/
lemma supported_subspace_peak {n : ℕ} (C : Submodule F (Fin n → F))
    (c : C) (W : Submodule F C)
    (hs : ∀ x∈W, ∀ i, c.val i=0 → x.val i=0) :
    2^finrank F W≤sumRep (codeSet C) (encode c.val) := by
  letI : Fintype C := Fintype.ofFinite C
  letI : Fintype W := Fintype.ofFinite W
  have hsum (x : W) : encode x.val.val+encode (c+x.val).val=encode c.val :=
    encode_complement c.val x.val.val (hs x.val x.property)
  rw [sumRep_def]
  have hi := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset W))
    (t := (Finset.antidiagonal (encode c.val)).filter
      (fun p ↦ p.1∈codeSet C ∧ p.2∈codeSet C))
    (fun x ↦ (encode x.val.val,encode (c+x.val).val))
    (by
      intro x hx
      change (encode x.val.val,encode (c+x.val).val)∈
        (Finset.antidiagonal (encode c.val)).filter
          (fun p : ℕ × ℕ ↦ p.1∈codeSet C ∧ p.2∈codeSet C)
      simp only [Finset.mem_filter,Finset.mem_antidiagonal]
      exact ⟨hsum x,⟨x.val,rfl⟩,⟨c+x.val,rfl⟩⟩)
    (by
      intro x hx y hy he
      apply Subtype.ext
      apply Subtype.ext
      exact encode_injective (congrArg Prod.fst he))
  rw [Finset.card_univ,Module.card_eq_pow_finrank (K := F) (V := W),ZMod.card] at hi
  exact hi

/-- A length-n, dimension-k binary linear code has a natural representation
peak at least 2^(k-floor(n/3)), at a target strictly below 2^n. -/
theorem exists_linear_code_peak {n : ℕ} (C : Submodule F (Fin n → F)) :
    ∃ t : ℕ, t<2^n ∧ 2^(finrank F C-n/3)≤sumRep (codeSet C) t := by
  obtain ⟨c,W,hd,hc,hs⟩ := code_supported_subspace C
  refine ⟨encode c.val,encode_lt c.val,?_⟩
  exact (Nat.pow_le_pow_right (by norm_num : 1≤2) hd).trans
    (supported_subspace_peak C c W hs)

/-- Full binary linear codes of rate at least one half, at arbitrarily many
specified lengths, cannot be contained in a logarithmic-limit witness. -/
theorem no_log_limit_of_linear_code_family (A : Set ℕ)
    (hA : ∀ k : ℕ, ∃ C : Submodule F (Fin (6*k) → F),
      3*k≤finrank F C ∧ codeSet C⊆A) :
    ∀ c : ℝ, ¬Filter.Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) Filter.atTop (𝓝 c) := by
  apply no_log_limit_of_exponential_peaks A 64 1 (by norm_num)
  intro k
  obtain ⟨C,hC,hCA⟩ := hA k
  obtain ⟨t,ht,hrep⟩ := exists_linear_code_peak C
  have hd : k≤finrank F C-(6*k)/3 := by omega
  refine ⟨t,?_,(Nat.pow_le_pow_right (by norm_num : 1≤2) hd).trans
    (hrep.trans (Erdos66Explore.sumRep_mono hCA t))⟩
  have he : 2^(6*k)=64^k := by rw [pow_mul]; norm_num
  simpa only [one_mul,he] using ht.le

lemma encode_add_congr_digits {n : ℕ} (a b c d : Fin n → F)
    (h : ∀ i, (a i).val+(b i).val=(c i).val+(d i).val) :
    encode a+encode b=encode c+encode d := by
  unfold encode
  rw [Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq (by simp),
    Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq (by simp)]
  congr 1
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_zipWith,List.getElem_ofFn]
  exact h _

/-- An affine bit translation changes the target but does not remove the
supporting-subspace multiplicity. Fixed digit sums equal to two are allowed;
their ordinary carries are the same for every represented pair. -/
lemma encode_affine_complement {n : ℕ} (b c x : Fin n → F)
    (h : ∀ i, c i=0 → x i=0) :
    encode (b+x)+encode (b+c+x)=encode b+encode (b+c) := by
  apply encode_add_congr_digits
  intro i
  simp only [Pi.add_apply]
  rcases bit_cases (c i) with hc | hc
  · have hx := h i hc
    simp [hc,hx]
  · rcases bit_cases (x i) with hx | hx <;> rcases bit_cases (b i) with hb | hb <;>
      simp [hc,hx,hb,show (1:F)+1=0 by decide]

noncomputable def affineCodeSet {n : ℕ} (b : Fin n → F)
    (C : Submodule F (Fin n → F)) : Set ℕ :=
  Set.range (fun x : C ↦ encode (b+x.val))

lemma affine_supported_subspace_peak {n : ℕ} (b : Fin n → F)
    (C : Submodule F (Fin n → F)) (c : C) (W : Submodule F C)
    (hs : ∀ x∈W, ∀ i, c.val i=0 → x.val i=0) :
    2^finrank F W≤sumRep (affineCodeSet b C) (encode b+encode (b+c.val)) := by
  letI : Fintype C := Fintype.ofFinite C
  letI : Fintype W := Fintype.ofFinite W
  let t := encode b+encode (b+c.val)
  have hsum (x : W) : encode (b+x.val.val)+encode (b+(c+x.val).val)=t := by
    simpa only [t,Submodule.coe_add,add_assoc] using
      encode_affine_complement b c.val x.val.val (hs x.val x.property)
  rw [sumRep_def]
  have hi := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset W))
    (t := (Finset.antidiagonal t).filter
      (fun p ↦ p.1∈affineCodeSet b C ∧ p.2∈affineCodeSet b C))
    (fun x ↦ (encode (b+x.val.val),encode (b+(c+x.val).val)))
    (by
      intro x hx
      change (encode (b+x.val.val),encode (b+(c+x.val).val))∈
        (Finset.antidiagonal t).filter
          (fun p : ℕ × ℕ ↦ p.1∈affineCodeSet b C ∧ p.2∈affineCodeSet b C)
      simp only [Finset.mem_filter,Finset.mem_antidiagonal]
      exact ⟨hsum x,⟨x.val,rfl⟩,⟨c+x.val,rfl⟩⟩)
    (by
      intro x hx y hy he
      apply Subtype.ext
      apply Subtype.ext
      exact add_left_cancel (encode_injective (congrArg Prod.fst he)))
  rw [Finset.card_univ,Module.card_eq_pow_finrank (K := F) (V := W),ZMod.card] at hi
  exact hi

theorem exists_affine_code_peak {n : ℕ} (b : Fin n → F)
    (C : Submodule F (Fin n → F)) :
    ∃ t : ℕ, t<2^(n+1) ∧ 2^(finrank F C-n/3)≤sumRep (affineCodeSet b C) t := by
  obtain ⟨c,W,hd,hc,hs⟩ := code_supported_subspace C
  refine ⟨encode b+encode (b+c.val),?_,?_⟩
  · have hb := encode_lt b
    have hc := encode_lt (b+c.val)
    rw [pow_succ]
    omega
  · exact (Nat.pow_le_pow_right (by norm_num : 1≤2) hd).trans
      (affine_supported_subspace_peak b C c W hs)

theorem no_log_limit_of_affine_code_family (A : Set ℕ)
    (hA : ∀ k : ℕ, ∃ b : Fin (6*k) → F, ∃ C : Submodule F (Fin (6*k) → F),
      3*k≤finrank F C ∧ affineCodeSet b C⊆A) :
    ∀ c : ℝ, ¬Filter.Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) Filter.atTop (𝓝 c) := by
  apply no_log_limit_of_exponential_peaks A 64 2 (by norm_num)
  intro k
  obtain ⟨b,C,hC,hCA⟩ := hA k
  obtain ⟨t,ht,hrep⟩ := exists_affine_code_peak b C
  have hd : k≤finrank F C-(6*k)/3 := by omega
  refine ⟨t,?_,(Nat.pow_le_pow_right (by norm_num : 1≤2) hd).trans
    (hrep.trans (Erdos66Explore.sumRep_mono hCA t))⟩
  have he : 2^(6*k+1)=2*64^k := by rw [pow_succ,pow_mul]; norm_num; ring
  simpa only [he] using ht.le

end Erdos66BinaryLinearCodePeak
