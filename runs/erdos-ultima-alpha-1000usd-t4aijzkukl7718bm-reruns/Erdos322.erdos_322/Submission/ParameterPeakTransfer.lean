import FormalConjecturesUtil

/-! An exact parameter-count criterion for power peaks. Both the number of
target values and the number of repeated outputs must be accounted for. -/
namespace Erdos322Research.ParameterPeakTransfer
noncomputable section
open Finset
open scoped Classical
set_option Elab.async false
set_option maxHeartbeats 0

/-- A finite pigeonhole estimate retaining the full integer surplus. -/
theorem large_fiber {α : Type*} (S : Finset α) (T : Finset ℕ)
    (N : α → ℕ) (r : ℕ → ℕ) (B m e f : ℕ) (hB : 0<B) (hgap : e + f < m)
    (hS : B^m≤S.card) (hT : T.card≤B^e)
    (hN : ∀ a∈S, N a∈T)
    (hF : ∀ n∈T, (S.filter (fun a ↦ N a=n)).card≤B^f*r n) :
    ∃ n∈T, B^(m-e-f)≤r n := by
  by_contra hn
  push_neg at hn
  let δ := m-e-f
  have hδ : 0<δ := by dsimp [δ]; omega
  have hm : m=e+f+δ := by dsimp [δ]; omega
  have hp : 0<B^δ := pow_pos hB _
  have hbound : S.card≤(B^f*(B^δ-1))*T.card := by
    apply card_le_mul_card_image_of_maps_to hN
    intro n hnT
    exact (hF n hnT).trans (Nat.mul_le_mul_left _ (by have hh : r n<B^δ := hn n hnT; omega))
  have hlt : (B^f*(B^δ-1))*T.card<B^m := by
    calc
      (B^f*(B^δ-1))*T.card ≤ (B^f*(B^δ-1))*B^e := Nat.mul_le_mul_left _ hT
      _ < (B^f*B^δ)*B^e := Nat.mul_lt_mul_of_pos_right
        (Nat.mul_lt_mul_of_pos_left (by omega : B^δ-1<B^δ) (pow_pos hB _)) (pow_pos hB _)
      _ = B^m := by rw [hm,pow_add,pow_add]; ring
  exact (not_lt_of_ge hS) (hbound.trans_lt hlt)

/-- A height-controlled count lower bound at arbitrarily large parameter
scales yields one fixed positive real exponent, not just unbounded counts. -/
theorem peaks_of_height_witnesses (r : ℕ → ℕ) (d δ : ℕ) (hd : 0<d) (hδ : 0<δ)
    (h : ∀ M : ℕ, ∃ B n : ℕ, M<B ∧ n≤B^d ∧ B^δ≤r n) :
    {n : ℕ | (n : ℝ)^((δ : ℝ)/(2*d)) < (r n : ℝ)}.Infinite := by
  let c : ℝ := (δ : ℝ)/(2*d)
  have hc : 0<c := by dsimp [c]; positivity
  by_contra hfinite
  have hf : {n : ℕ | (n : ℝ)^c < (r n : ℝ)}.Finite := Set.not_infinite.mp hfinite
  let M := ∑ n∈hf.toFinset, r n
  obtain ⟨B,n,hBM,hn,hcount⟩ := h (M+2)
  have hB : 1<B := by omega
  have hBr : (1 : ℝ)<B := by exact_mod_cast hB
  have hdR : (d : ℝ)≠0 := by positivity
  have hδR : (0 : ℝ)<δ := by exact_mod_cast hδ
  have hexp : (d : ℝ)*c=(δ : ℝ)/2 := by dsimp [c]; field_simp
  have hpeak : (n : ℝ)^c < (r n : ℝ) := by
    calc
      (n : ℝ)^c ≤ (((B^d : ℕ) : ℝ))^c :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hn) hc.le
      _ = (B : ℝ)^((δ : ℝ)/2) := by rw [Nat.cast_pow,← Real.rpow_natCast_mul (Nat.cast_nonneg B),hexp]
      _ < (B : ℝ)^(δ : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hBr (by linarith)
      _ = ((B^δ : ℕ) : ℝ) := by rw [Real.rpow_natCast,Nat.cast_pow]
      _ ≤ (r n : ℝ) := by exact_mod_cast hcount
  have hnmem : n∈hf.toFinset := hf.mem_toFinset.mpr hpeak
  have hnr : r n≤M := single_le_sum (fun _ _ ↦ Nat.zero_le _) hnmem
  have hBB : B≤B^δ := Nat.le_pow (by omega)
  omega

/-- Parameter count minus target-value count minus repeated-output count is
the relevant surplus. A positive integer surplus gives explicit power peaks. -/
theorem peaks_of_parameter_counts {α : ℕ → Type*}
    (S : ∀ B, Finset (α B)) (T : ℕ → Finset ℕ) (N : ∀ B, α B → ℕ)
    (r : ℕ → ℕ) (m e f d B₀ : ℕ) (hd : 0<d) (hgap : e + f < m)
    (hS : ∀ B, B₀≤B → B^m≤(S B).card)
    (hT : ∀ B, B₀≤B → (T B).card≤B^e)
    (hN : ∀ B, B₀≤B → ∀ a∈S B, N B a∈T B)
    (hF : ∀ B, B₀≤B → ∀ n∈T B,
      ((S B).filter (fun a ↦ N B a=n)).card≤B^f*r n)
    (hheight : ∀ B, B₀≤B → ∀ n∈T B, n≤B^d) :
    {n : ℕ | (n : ℝ)^(((m-e-f : ℕ) : ℝ)/(2*d)) < (r n : ℝ)}.Infinite := by
  apply peaks_of_height_witnesses r d (m-e-f) hd (by omega)
  intro M
  let B := max (M+1) B₀+1
  have hBM : M<B := by dsimp [B]; omega
  have hB₀ : B₀≤B := by dsimp [B]; omega
  obtain ⟨n,hnT,hn⟩ := large_fiber (S B) (T B) (N B) r B m e f
    (by omega) hgap (hS B hB₀) (hT B hB₀) (hN B hB₀) (hF B hB₀)
  exact ⟨B,n,hBM,hheight B hB₀ n hnT,hn⟩

/-- How to justify the repeated-output factor: parameters first map to actual
finite representation sets, with a separate bound on each output's preimages. -/
theorem fiber_bound_of_output_multiplicity {α β : Type*}
    (S : Finset α) (N : α → ℕ) (F : α → β) (R : ℕ → Finset β) (K n : ℕ)
    (hmap : ∀ a∈S, F a∈R (N a))
    (hmult : ∀ b∈R n,
      ((S.filter (fun a ↦ N a=n)).filter (fun a ↦ F a=b)).card≤K) :
    (S.filter (fun a ↦ N a=n)).card≤K*(R n).card := by
  apply card_le_mul_card_image_of_maps_to (f := F) (t := R n) ?_ K hmult
  intro a ha
  obtain ⟨ha,han⟩ := mem_filter.mp ha
  simpa only [han] using hmap a ha

end
end Erdos322Research.ParameterPeakTransfer
