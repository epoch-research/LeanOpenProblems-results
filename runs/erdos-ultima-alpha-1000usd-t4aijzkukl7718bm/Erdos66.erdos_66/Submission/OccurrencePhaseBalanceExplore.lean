import Submission.TranslatedPrefixPaletteExplore

/-! A deterministic cyclic phase schedule balances the aggregate membership
counts of an arbitrary sequence of finite templates. -/
namespace Erdos66OccurrencePhaseBalance
open Erdos66TranslatedPrefixPalette
open scoped Classical
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

variable {α : Type*} [DecidableEq α]

noncomputable def occurrences (f : ℕ → α) (t : α) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun k ↦ f k=t)).card

@[simp] lemma occurrences_zero (f : ℕ → α) (t : α) : occurrences f t 0=0 := by
  simp [occurrences]

lemma occurrences_succ (f : ℕ → α) (t : α) (N : ℕ) :
    occurrences f t (N+1)=occurrences f t N + if f N=t then 1 else 0 := by
  simp only [occurrences,Finset.range_add_one,Finset.filter_insert]
  split_ifs <;> simp_all

lemma sum_occurrences (f : ℕ → α) (t : α) (g : ℕ → ℝ) (N : ℕ) :
    (∑ k∈Finset.range N, if f k=t then g (occurrences f t k) else 0)=
      ∑ j∈Finset.range (occurrences f t N), g j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,occurrences_succ]
    split_ifs with h
    · exact (Finset.sum_range_succ _ _).symm
    · simp

variable (M : ℕ) [NeZero M]

noncomputable def phase (f : ℕ → α) (n : ℕ) : ZMod M := occurrences f (f n) n

noncomputable def hit (C : Finset (ZMod M)) (z : ZMod M) (j : ℕ) : ℝ :=
  if z-(j : ZMod M) ∈ C then 1 else 0

lemma hit_nonneg (C : Finset (ZMod M)) (z : ZMod M) (j : ℕ) : 0 ≤ hit M C z j := by
  unfold hit
  split_ifs <;> norm_num

lemma hit_le_one (C : Finset (ZMod M)) (z : ZMod M) (j : ℕ) : hit M C z j ≤ 1 := by
  unfold hit
  split_ifs <;> norm_num

lemma hit_period (C : Finset (ZMod M)) (z : ZMod M) (j : ℕ) :
    hit M C z (j+M)=hit M C z j := by
  simp [hit]

lemma hit_full_sum (C : Finset (ZMod M)) (z : ZMod M) :
    (∑ j∈Finset.range M, hit M C z j)=(C.card : ℝ) := by
  have he : (∑ j∈Finset.range M, hit M C z j)=
      ∑ a : ZMod M, if z-a∈C then (1:ℝ) else 0 := by
    apply Finset.sum_bij (fun (j : ℕ) _ ↦ (j : ZMod M))
    · intro j hj; simp
    · intro i hi j hj he
      have hh := congrArg ZMod.val he
      simpa only [ZMod.val_natCast_of_lt (Finset.mem_range.mp hi),
        ZMod.val_natCast_of_lt (Finset.mem_range.mp hj)] using hh
    · intro a ha
      exact ⟨a.val, Finset.mem_range.mpr (ZMod.val_lt a), ZMod.natCast_zmod_val a⟩
    · intro j hj; rfl
  rw [he]
  have hh := Equiv.sum_comp (Equiv.subLeft z) (fun a : ZMod M ↦ if a∈C then (1:ℝ) else 0)
  simpa using hh

lemma hit_sum_blocks (C : Finset (ZMod M)) (z : ZMod M) (q : ℕ) :
    (∑ j∈Finset.range (q*M), hit M C z j)=(q:ℝ)*C.card := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul,Finset.sum_range_add,ih]
    have hh : (∑ j∈Finset.range M, hit M C z (q*M+j))=(C.card:ℝ) := by
      simpa only [hit,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,mul_zero,zero_add] using
        hit_full_sum M C z
    rw [hh]
    push_cast
    ring

/-- Every incomplete phase cycle contributes at most M absolute error. -/
lemma hit_sum_error (C : Finset (ZMod M)) (z : ZMod M) (R : ℕ) :
    |(∑ j∈Finset.range R, hit M C z j)-(R:ℝ)*C.card/M| ≤ M := by
  have hM : (0:ℝ)<M := by exact_mod_cast NeZero.pos M
  have hC : (C.card:ℝ)≤M := by exact_mod_cast (show C.card ≤ M by simpa using Finset.card_le_univ C)
  have hR : R=R/M*M+R%M := by simpa [Nat.mul_comm] using (Nat.div_add_mod R M).symm
  have hformula : (∑ j∈Finset.range R, hit M C z j)=
      (R/M:ℕ)* (C.card:ℝ) + ∑ j∈Finset.range (R%M), hit M C z j := by
    conv_lhs => rw [hR,Finset.sum_range_add,hit_sum_blocks]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp [hit]
  have hlow : 0≤∑ j∈Finset.range (R%M), hit M C z j :=
    Finset.sum_nonneg (fun j _ ↦ hit_nonneg M C z j)
  have hupp : (∑ j∈Finset.range (R%M), hit M C z j)≤(R%M:ℕ) := by
    simpa using Finset.sum_le_sum (s := Finset.range (R%M))
      (g := fun _ ↦ (1:ℝ)) (fun j _ ↦ hit_le_one M C z j)
  have hmod : (R%M:ℕ)<(M:ℝ) := by exact Nat.cast_lt.mpr (Nat.mod_lt R (NeZero.pos M))
  have hr : (R:ℝ)=(R/M:ℕ)*(M:ℝ)+(R%M:ℕ) := by
    simpa only [Nat.cast_add,Nat.cast_mul] using congrArg (fun n : ℕ ↦ (n:ℝ)) hR
  have hfrac : 0≤(R%M:ℕ)*(C.card:ℝ)/M :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hM.le
  have hfrac' : (R%M:ℕ)*(C.card:ℝ)/M ≤ (R%M:ℕ) := by
    apply (div_le_iff₀ hM).mpr
    exact mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg _)
  rw [hformula,hr]
  have he : (R/M:ℕ)*(C.card:ℝ)+(∑ j∈Finset.range (R%M), hit M C z j)-
      ((R/M:ℕ)*(M:ℝ)+(R%M:ℕ))*C.card/M =
      (∑ j∈Finset.range (R%M), hit M C z j)-(R%M:ℕ)*(C.card:ℝ)/M := by
    field_simp
    <;> ring
  rw [he,abs_le]
  constructor <;> linarith

variable [Fintype α]

lemma sum_by_type (f : ℕ → α) (g : α → ℝ) (N : ℕ) :
    (∑ k∈Finset.range N, g (f k))=∑ t, (occurrences f t N:ℝ)*g t := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    simp_rw [occurrences_succ,Nat.cast_add,add_mul]
    rw [Finset.sum_add_distrib]
    congr 1
    simp [eq_comm]

/-- Cycling the phase separately for each template type gives a bounded
    aggregate discrepancy at every residue, for every prefix. -/
theorem phase_balance (f : ℕ → α) (C : α → Finset (ZMod M))
    (N : ℕ) (z : ZMod M) :
    |(∑ k∈Finset.range N,
        if z∈shift M (C (f k)) (phase M f k) then (1:ℝ) else 0)-
      (∑ k∈Finset.range N, ((C (f k)).card:ℝ))/M| ≤ (Fintype.card α:ℝ)*M := by
  have hc : (∑ k∈Finset.range N,
        if z∈shift M (C (f k)) (phase M f k) then (1:ℝ) else 0)=
      ∑ t, ∑ j∈Finset.range (occurrences f t N), hit M (C t) z j := by
    simp_rw [←sum_occurrences f]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    simp [phase,hit,eq_comm]
  have hm : (∑ k∈Finset.range N, ((C (f k)).card:ℝ))/M=
      ∑ t, (occurrences f t N:ℝ)*(C t).card/M := by
    rw [sum_by_type f (fun t ↦ ((C t).card:ℝ)) N,Finset.sum_div]
  rw [hc,hm,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ t, |(∑ j∈Finset.range (occurrences f t N), hit M (C t) z j)-
        (occurrences f t N:ℝ)*(C t).card/M| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : α, (M:ℝ) :=
      Finset.sum_le_sum (fun t _ ↦ hit_sum_error M (C t) z (occurrences f t N))
    _ = _ := by simp

end Erdos66OccurrencePhaseBalance
