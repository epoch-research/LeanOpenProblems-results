import Submission.MultiplicativeNaturalRowsExplore

/-! A natural, two-carry obstruction for reflected multiplicative rows.
This only restricts the row construction; it does not disprove Erdős 66. -/
namespace Erdos66MultiplicativeReflection
open Erdos66MultiplicativeRows Erdos66MultiplicativeNaturalRows
  Erdos66IntegerBlock Erdos66OriginRepair AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 1800000

lemma reflected_solution {F : Type*} [Field F] (a y u : F) (hy : y+1≠0) :
    linearSolution a y (-y-2) (-2*a) u=u := by
  dsimp [linearSolution,linearTarget]
  field_simp
  <;> ring

lemma reflected_row_pairCount {F : Type*} [Field F]
    (U V : Finset F) (a y : F) (hy : y+1≠0) :
    pairCount (row U a y) (row V a (-y-2)) (-2*a)=(U∩V).card := by
  have hz : -y-2+1≠0 := by
    intro he
    apply hy
    linear_combination -he
  rw [row_pairCount U V a y (-y-2) (-2*a) hy hz]
  simp_rw [reflected_solution a y _ hy]
  congr 1

variable {p : ℕ} [Fact p.Prime]

lemma reflected_height (k : ℕ) (hk : k<p-1) :
    ((p-2-k:ℕ):ZMod p)=-(k:ZMod p)-2 := by
  have he : (p-2-k)+k+2=p := by omega
  have hh := congrArg (fun n : ℕ ↦ (n:ZMod p)) he
  simp only [Nat.cast_add,Nat.cast_ofNat,ZMod.natCast_self] at hh
  linear_combination hh

noncomputable def overlapSum (U : ℕ → Finset (ZMod p)) : ℕ :=
  ∑ k∈Finset.range (p-1), (U k∩U (p-2-k)).card

/-- Every old parameter common to a pair of reflected rows contributes to
one of two ordinary natural targets. Their contributions cannot cancel. -/
theorem overlap_le_two_targets (U : ℕ → Finset (ZMod p)) (a : ZMod p) :
    overlapSum U≤sumRep (naturalSet U a) ((p-2)*p+(-2*a).val)+
      sumRep (naturalSet U a) ((p-1)*p+(-2*a).val) := by
  have hp : 2≤p := (Fact.out : p.Prime).two_le
  let C : ℕ → Finset (ZMod p) := fun k ↦ row (U k) a (k:ZMod p)
  let t : ℕ := (-2*a).val
  have ht : t<p := ZMod.val_lt _
  have hrow (k : ℕ) (hk : k∈Finset.range (p-1)) :
      lower p (C k) (C (p-2-k)) t+upper p (C k) (C (p-2-k)) t=
        (U k∩U (p-2-k)).card := by
    have hkp : k<p-1 := Finset.mem_range.mp hk
    rw [lower_add_upper]
    have hh := reflected_row_pairCount (U k) (U (p-2-k)) a (k:ZMod p)
      (small_row_nonsingular k (by omega))
    dsimp only [C,t]
    rw [reflected_height k hkp,ZMod.natCast_zmod_val]
    simp only [pairCount] at hh
    convert hh using 1 <;> congr 1 <;> ext u <;> simp only [Finset.mem_filter,Finset.mem_inter]
  have hsum : overlapSum U=
      (∑ k∈Finset.range (p-1), lower p (C k) (C (p-2-k)) t)+
        ∑ k∈Finset.range (p-1), upper p (C k) (C (p-2-k)) t := by
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k hk ↦ (hrow k hk).symm)
  have h₀ := block_formula p C (p-2) t ht
  have h₁ := block_formula p C (p-1) t ht
  have he : p-2+1=p-1 := by omega
  have he' (k : ℕ) : p-1-k-1=p-2-k := by omega
  rw [he] at h₀
  simp_rw [he'] at h₁
  change overlapSum U≤sumRep (blockSet p C) ((p-2)*p+t)+
    sumRep (blockSet p C) ((p-1)*p+t)
  rw [hsum,h₀,h₁]
  omega

/-- The peak lies below p², not merely at an unspecified modular target. -/
theorem exists_overlap_peak (U : ℕ → Finset (ZMod p)) (a : ZMod p) :
    ∃ n : ℕ, n<p^2 ∧ overlapSum U≤2*sumRep (naturalSet U a) n := by
  have hp : 2≤p := (Fact.out : p.Prime).two_le
  have hs := ZMod.val_lt (-2*a)
  have h₀ : (p-2)*p+(-2*a).val<p^2 := by nlinarith [Nat.sub_add_cancel hp]
  have h₁ : (p-1)*p+(-2*a).val<p^2 := by nlinarith [Nat.sub_add_cancel (by omega : 1≤p)]
  have h := overlap_le_two_targets U a
  by_cases he : overlapSum U≤2*sumRep (naturalSet U a) ((p-2)*p+(-2*a).val)
  · exact ⟨_,h₀,he⟩
  · exact ⟨_,h₁,by omega⟩

/-- More than half a full field of retained rows forces a peak from any
common old parameter set, even when that set has only one point. -/
theorem common_parameter_mass_le_overlap (U : ℕ → Finset (ZMod p))
    (V : Finset (ZMod p)) (N : ℕ) (hN : N≤p-1)
    (hV : ∀ k<N, V⊆U k) :
    (2*N-(p-1))*V.card≤overlapSum U := by
  let S : Finset ℕ := Finset.Ico (p-1-N) N
  have hS : S⊆Finset.range (p-1) := by
    intro k hk
    have hh := Finset.mem_Ico.mp hk
    exact Finset.mem_range.mpr (lt_of_lt_of_le hh.2 hN)
  have hc : S.card=2*N-(p-1) := by
    rw [Nat.card_Ico]
    omega
  calc
    _ = ∑ _k∈S, V.card := by simp [hc]
    _ ≤ ∑ k∈S, (U k∩U (p-2-k)).card := by
      apply Finset.sum_le_sum
      intro k hk
      have hh := Finset.mem_Ico.mp hk
      apply Finset.card_le_card
      intro u hu
      exact Finset.mem_inter.mpr ⟨hV k hh.2 hu,hV (p-2-k) (by omega) hu⟩
    _ ≤ overlapSum U := Finset.sum_le_sum_of_subset hS

/-- A simple global cap already limits how far a nested taper can continue. -/
theorem common_parameter_cap (U : ℕ → Finset (ZMod p)) (a : ZMod p)
    (V : Finset (ZMod p)) (N B : ℕ) (hN : N≤p-1)
    (hV : ∀ k<N, V⊆U k)
    (hcap : ∀ n<p^2, sumRep (naturalSet U a) n≤B) :
    (2*N-(p-1))*V.card≤2*B := by
  obtain ⟨n,hn,hpeak⟩ := exists_overlap_peak U a
  exact (common_parameter_mass_le_overlap U V N hN hV).trans
    (hpeak.trans (Nat.mul_le_mul_left 2 (hcap n hn)))

end Erdos66MultiplicativeReflection
