import Submission.RepeatedBlockProfileExplore
import Submission.CarryExplore

/-! A repeated finite cyclic template can be padded to a slightly larger
cyclic modulus. This is a finite transference statement, not an infinite
construction for the logarithmic representation conjecture. -/
namespace Erdos66CyclicPadding
open AdditiveCombinatorics Erdos66RepeatedBlockProfile Erdos66CarryAveraging
  Erdos66BinaryBlockTransfer Erdos66Carry
open scoped Classical

lemma triangle_padding_bound (K q s : ℕ) (hq : q ≤ K)
    (hs : s=q+K ∨ s=q+K+1) :
    |triangle K q+triangle K s-(K : ℤ)| ≤ 1 := by
  unfold triangle
  rcases hs with rfl | rfl <;> push_cast <;> rw [abs_le] <;> constructor <;> omega

lemma padding_quotients (M K d n : ℕ) (hM : 0 < M) (hd : d < M)
    (hn : n < M*K+d) : n/M ≤ K ∧
    (n+(M*K+d))/M=n/M+K ∨ n/M ≤ K ∧
    (n+(M*K+d))/M=n/M+K+1 := by
  have hq : n/M ≤ K := by
    have hh : n < (K+1)*M := by nlinarith
    have hh' := (Nat.div_lt_iff_lt_mul hM).mpr hh
    omega
  have he : (n+(M*K+d))/M = n/M+K+(n%M+d)/M := by
    have hdecomp := Nat.div_add_mod n M
    calc
      _ = (M*(n/M+K)+(n%M+d))/M := by congr 1; nlinarith
      _ = n/M+K+(n%M+d)/M := by rw [Nat.mul_add_div hM]
  have ht : (n%M+d)/M < (2 : ℕ) :=
    (Nat.div_lt_iff_lt_mul hM).mpr (by have := Nat.mod_lt n hM; omega)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ ht) with hh | hh
  · left
    exact ⟨hq,by rw [he,hh,Nat.add_zero]⟩
  · right
    exact ⟨hq,by rw [he,hh]⟩

lemma triangle_two_lifts_bound (M K d n : ℕ) (hM : 0 < M) (hd : d < M)
    (hn : n < M*K+d) :
    |triangle K (n/M : ℕ)+triangle K ((n+(M*K+d))/M : ℕ)-(K : ℤ)| ≤ 1 := by
  obtain (⟨hq,hs⟩ | ⟨hq,hs⟩) := padding_quotients M K d n hM hd hn
  · exact triangle_padding_bound K _ _ hq (Or.inl hs)
  · exact triangle_padding_bound K _ _ hq (Or.inr hs)

variable (M : ℕ) [NeZero M]

noncomputable def repeatedFinset (B : Finset (ZMod M)) (K : ℕ) : Finset ℕ :=
  (Finset.range (M*K)).filter (fun n ↦ (n : ZMod M) ∈ B)

lemma repeatedFinset_coe (B : Finset (ZMod M)) (K : ℕ) :
    (repeatedFinset M B K : Set ℕ)=repeatedBlock M B K := by
  ext n
  simp only [repeatedFinset,Finset.mem_coe,Finset.mem_filter,Finset.mem_range,
    repeatedBlock,binaryBlocks]
  have he : n/M < K ↔ n < M*K := by
    rw [Nat.div_lt_iff_lt_mul (NeZero.pos M),Nat.mul_comm K M]
  change (n < M*K ∧ (n : ZMod M) ∈ B) ↔ _
  by_cases hn : n < M*K <;> simp [Erdos66IntegerBlock.blockSet,he,hn]

variable (N : ℕ) [NeZero N]

noncomputable def padded (B : Finset (ZMod M)) (K : ℕ) : Finset (ZMod N) :=
  (repeatedFinset M B K).image (fun n : ℕ ↦ (n : ZMod N))

lemma padded_val_image (B : Finset (ZMod M)) (K : ℕ) (hMN : M*K ≤ N) :
    (padded M N B K).image ZMod.val=repeatedFinset M B K := by
  rw [padded,Finset.image_image]
  calc
    _ = (repeatedFinset M B K).image (fun n ↦ n) := by
      apply Finset.image_congr
      intro n hn
      have hnM : n < M*K := (Finset.mem_range.mp (Finset.mem_filter.mp hn).1)
      exact ZMod.val_natCast_of_lt (hnM.trans_le hMN)
    _ = _ := Finset.image_id

lemma padded_periodization (B : Finset (ZMod M)) (K n : ℕ)
    (hMN : M*K ≤ N) (hn : n < N) :
    ((padded M N B K).filter (fun a ↦ (n : ZMod N)-a∈padded M N B K)).card =
      sumRep (repeatedBlock M B K) n+sumRep (repeatedBlock M B K) (n+N) := by
  rw [cyclic_periodization N _ n hn,padded_val_image M N B K hMN,
    repeatedFinset_coe]

/-- Padding by fewer than one small period adds only a bounded carry error.
The new modulus need not be a multiple of the old modulus. -/
theorem padded_cyclic_error (B : Finset (ZMod M)) (K d : ℕ) (hN : N=M*K+d)
    (hd : d < M) (μ E : ℝ) (hμ : 0 ≤ μ) (hE : 0 ≤ E)
    (hB : ∀ z : ZMod M, |(((B.filter (fun a ↦ z-a∈B)).card : ℝ)-μ)| ≤ E)
    (z : ZMod N) :
    |(((padded M N B K).filter (fun a ↦ z-a∈padded M N B K)).card : ℝ)-K*μ| ≤
      2*K*E+3*μ+2*E := by
  have hn := ZMod.val_lt z
  have hMN : M*K ≤ N := by omega
  have hformula := padded_periodization M N B K z.val hMN hn
  rw [ZMod.natCast_zmod_val] at hformula
  have hformula' : (((padded M N B K).filter
      (fun a ↦ z-a∈padded M N B K)).card : ℝ) =
      (sumRep (repeatedBlock M B K) z.val : ℝ)+sumRep (repeatedBlock M B K) (z.val+N) := by
    exact_mod_cast hformula
  have h₁ := repeated_block_uniform_error M B K μ E hE hB z.val
  have h₂ := repeated_block_uniform_error M B K μ E hE hB (z.val+N)
  have htri : |(triangle K (z.val/M : ℕ) : ℝ)+(triangle K ((z.val+N)/M : ℕ) : ℝ)-(K : ℝ)| ≤ 1 := by
    have hh := triangle_two_lifts_bound M K d z.val (NeZero.pos M) hd (by omega)
    rw [← hN] at hh
    exact_mod_cast hh
  rw [hformula']
  have he : (sumRep (repeatedBlock M B K) z.val : ℝ)+sumRep (repeatedBlock M B K) (z.val+N)-K*μ =
      ((sumRep (repeatedBlock M B K) z.val : ℝ)-μ*(triangle K (z.val/M : ℕ) : ℝ))+
      ((sumRep (repeatedBlock M B K) (z.val+N) : ℝ)-μ*(triangle K ((z.val+N)/M : ℕ) : ℝ))+
      μ*((triangle K (z.val/M : ℕ) : ℝ)+(triangle K ((z.val+N)/M : ℕ) : ℝ)-K) := by ring
  rw [he]
  calc
    _ ≤ |(sumRep (repeatedBlock M B K) z.val : ℝ)-μ*(triangle K (z.val/M : ℕ) : ℝ)|+
        |(sumRep (repeatedBlock M B K) (z.val+N) : ℝ)-μ*(triangle K ((z.val+N)/M : ℕ) : ℝ)|+
        |μ*((triangle K (z.val/M : ℕ) : ℝ)+(triangle K ((z.val+N)/M : ℕ) : ℝ)-K)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ((K : ℝ)*E+μ+E)+((K : ℝ)*E+μ+E)+μ := by
      rw [abs_mul,abs_of_nonneg hμ]
      exact add_le_add (add_le_add h₁ h₂)
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left htri hμ)
    _ = _ := by ring

/-- Choose the number of complete repetitions by division to obtain a bound
at any positive destination modulus. -/
theorem padding_to_any_modulus (B : Finset (ZMod M)) (μ E : ℝ)
    (hμ : 0 ≤ μ) (hE : 0 ≤ E)
    (hB : ∀ z : ZMod M, |(((B.filter (fun a ↦ z-a∈B)).card : ℝ)-μ)| ≤ E) :
    ∃ D : Finset (ZMod N), ∀ z : ZMod N,
      |(((D.filter (fun a ↦ z-a∈D)).card : ℝ)-(N/M : ℕ)*μ)| ≤
        2*(N/M : ℕ)*E+3*μ+2*E := by
  refine ⟨padded M N B (N/M),fun z ↦ ?_⟩
  exact padded_cyclic_error M N B (N/M) (N%M) (Nat.div_add_mod N M).symm
    (Nat.mod_lt N (NeZero.pos M)) μ E hμ hE hB z

end Erdos66CyclicPadding
