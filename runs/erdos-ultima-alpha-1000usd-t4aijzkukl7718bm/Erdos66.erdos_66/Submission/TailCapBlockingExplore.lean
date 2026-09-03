import Submission.PointwiseCapBlockingExplore

/-! A distant blocking certificate can be supported entirely in the new
part of a capped extension. This is a tool for testing finite exchanges,
not a disproof of the original existential conjecture. -/
namespace Erdos66TailCapBlocking
open Filter AdditiveCombinatorics Erdos66NaturalSymmetricPacket
  Erdos66NaturalSidonExtraction Erdos66NatPairAlgebra Erdos66LocalMoves
  Erdos66Generating Erdos66Explore Erdos66Compactness Erdos66PointwiseCapBlocking
open scoped Classical Topology
set_option maxHeartbeats 1800000

/-- In addition to the old extension properties, a blocking certificate is
contained entirely above the old cutoff L. -/
theorem exists_tail_blocking_extension (q : ℕ → ℕ)
    (hqtop : Tendsto q atTop atTop) (hqsmall : ∀ᶠ n in atTop, (q n)^4 < n/12)
    (C : Finset ℕ) (L x : ℕ) (hC : ∀ a∈C, a<L)
    (hcap : Capped q (C : Set ℕ)) (hx : x∉C) :
    ∃ (B : Finset ℕ) (N : ℕ),
      8*(L+x+1)<N ∧ C⊆B ∧
      (∀ a∈B, a≤N) ∧ (∀ a<L, a∈B ↔ a∈C) ∧
      Capped q (B : Set ℕ) ∧ Blocked q B x ∧
      sumRep (B : Set ℕ) (2*L)=0 ∧
      sumRep (B : Set ℕ) N+1 ≥ q N ∧
      ∃ F : Finset ℕ, F⊆B ∧ (∀ a∈F, L≤a) ∧ Blocked q F x := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hqtop.eventually_ge_atTop (2*C.card+8))
  obtain ⟨N,hNsmall,hN⟩ := (hqsmall.and
    (eventually_ge_atTop (max 48 (12*(T+L+x+1))))).exists
  have hN48 : 48 ≤ N := (le_max_left _ _).trans hN
  have hNbig : 12*(T+L+x+1) ≤ N := (le_max_right _ _).trans hN
  have hNx : x < N/4 := by omega
  have hNL : 2*L < N/4 := by omega
  have hTquarter : T ≤ N/4 := by omega
  let m := q N/2
  have hm : m^4 < N/12 :=
    lt_of_le_of_lt (Nat.pow_le_pow_left (Nat.div_le_self (q N) 2) 4) hNsmall
  let I := Finset.Ico (N/3) (N/3+N/12)
  obtain ⟨E,hEI,hEm,hEs⟩ := exists_natSidon_subset I m (by simpa [I] using hm)
  have hE (a : ℕ) (ha : a∈E) : N/3 ≤ a ∧ a<N/3+N/12 := Finset.mem_Ico.mp (hEI ha)
  have hhalf (a : ℕ) (ha : a∈E) : 2*a<N := by have := hE a ha; omega
  have hEn (a : ℕ) (ha : a∈E) : a≤N := by have := hhalf a ha; omega
  let P := natPacket N E
  have hP (a : ℕ) (ha : a∈P) : N/4 ≤ a ∧ a≤N ∧ 3*a ≤ 2*N+3 := by
    rcases Finset.mem_union.mp ha with ha | ha
    · have hh := hE a ha
      omega
    · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
      have hh := hE b hb
      omega
  have hPcenter : sumRep (P : Set ℕ) N=2*m := by
    rw [natPacket_center N E hEn,natPacket_card N E hhalf,hEm]
  have hPoff (z : ℕ) (hz : z≠N) : sumRep (P : Set ℕ) z≤6 :=
    natPacket_off_center E hEs N hhalf z hz
  have hdis : Disjoint C P := by
    apply Finset.disjoint_left.mpr
    intro a ha hp
    have hh := hC a ha
    have hh' := (hP a hp).1
    omega
  have hbasecenter : sumRep ((C∪P : Finset ℕ) : Set ℕ) N=2*m := by
    rw [sumRep_union_self C P N hdis,rep_zero_of_upper C L N hC (by omega),
      pairs_comm C P,natPacket_mixed_center_zero C E N hEn hdis,hPcenter]
    omega
  have hxbase : x∉C∪P := by
    intro hx'
    rcases Finset.mem_union.mp hx' with hx' | hx'
    · exact hx hx'
    · have hh := (hP x hx').1; omega
  let a := N-x
  have haN : a≤N := Nat.sub_le _ _
  have haquarter : N/4 ≤ a := by dsimp [a]; omega
  have habase : a∉C∪P := by
    intro ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have hh := hC a ha; dsimp [a] at hh; omega
    · have hh := (hP a ha).2.2; dsimp [a] at hh; omega
  let B := insert a (C∪P)
  have hBcenter : sumRep (B : Set ℕ) N=2*m := by
    have he := sumRep_insert_exact (A := ((C∪P : Finset ℕ) : Set ℕ)) habase N
    have hs : shiftedIndicator ((C∪P : Finset ℕ) : Set ℕ) a N=0 := by
      simp only [shiftedIndicator,if_pos haN,indicator]
      have hx' : N-a=x := by dsimp [a]; omega
      simp only [hx',Finset.mem_coe,if_neg hxbase]
    have hd : pointMass (2*a) N=0 := by
      apply if_neg
      dsimp [a]
      omega
    rw [hs,hd,hbasecenter] at he
    norm_num only [mul_zero,add_zero] at he
    have he' : sumRep (insert a ((C∪P : Finset ℕ) : Set ℕ)) N=2*m := by exact_mod_cast he
    simpa only [B,Finset.coe_insert] using he' 
  have hBsmall (z : ℕ) (hz : z<N/4) : sumRep (B : Set ℕ) z=sumRep (C : Set ℕ) z := by
    apply sumRep_congr_below
    intro i hi
    have hia : i≠a := by omega
    have hiP : i∉P := by intro hh; have := (hP i hh).1; omega
    simp [B,hia,hiP]
  have hBcap : Capped q (B : Set ℕ) := by
    intro z
    by_cases hzN : z=N
    · subst z
      rw [hBcenter]
      dsimp [m]
      omega
    by_cases hz : z<N/4
    · rw [hBsmall z hz]
      exact hcap z
    have hU : sumRep ((C∪P : Finset ℕ) : Set ℕ) z ≤ sumRep (P : Set ℕ) z+2*C.card := by
      have hh := Erdos66NaturalRepairBridge.sumRep_union_finset_le (P : Set ℕ) C z
      simpa only [Finset.coe_union,Set.union_comm] using hh
    have hi := sumRep_insert_le (((C∪P : Finset ℕ) : Set ℕ)) a z
    have hqz := hT z (by omega)
    have hpz := hPoff z hzN
    have hi' : sumRep (B : Set ℕ) z ≤ sumRep ((C∪P : Finset ℕ) : Set ℕ) z+2 := by
      simpa only [B,Finset.coe_insert] using hi
    omega
  have hxB : x∉B := by
    simp only [B,Finset.mem_insert]
    intro hh
    rcases hh with hh | hh
    · dsimp [a] at hh; omega
    · exact hxbase hh
  have hblock : Blocked q B x := by
    refine ⟨N,?_⟩
    have he := sumRep_insert_exact (A := (B : Set ℕ)) hxB N
    have hs : shiftedIndicator (B : Set ℕ) x N=1 := by
      simp only [shiftedIndicator,if_pos (show x≤N by omega),indicator]
      exact if_pos (Finset.mem_insert_self a (C∪P))
    have hd : pointMass (2*x) N=0 := by apply if_neg; omega
    rw [hs,hd,hBcenter] at he
    have he' : sumRep (insert x (B : Set ℕ)) N=2*m+2 := by exact_mod_cast he
    rw [he']
    dsimp [m]
    omega
  let F := insert a P
  have hFB : F⊆B := by
    apply Finset.insert_subset_insert
    exact Finset.subset_union_right
  have hxF : x∉F := fun hh ↦ hxB (hFB hh)
  have hFcenter : sumRep (F : Set ℕ) N=2*m := by
    have haP : a∉P := fun hh ↦ habase (Finset.mem_union_right C hh)
    have hxP : x∉P := fun hh ↦ hxbase (Finset.mem_union_right C hh)
    have he := sumRep_insert_exact (A := (P : Set ℕ)) haP N
    have hs : shiftedIndicator (P : Set ℕ) a N=0 := by
      have hx' : N-a=x := by dsimp [a]; omega
      simp only [shiftedIndicator,if_pos haN,indicator,hx',Finset.mem_coe,if_neg hxP]
    have hd : pointMass (2*a) N=0 := by
      apply if_neg
      dsimp [a]
      omega
    rw [hs,hd,hPcenter] at he
    norm_num only [mul_zero,add_zero] at he
    have he' : sumRep (insert a (P : Set ℕ)) N=2*m := by exact_mod_cast he
    simpa only [F,Finset.coe_insert] using he'
  have hFblock : Blocked q F x := by
    refine ⟨N,?_⟩
    have he := sumRep_insert_exact (A := (F : Set ℕ)) hxF N
    have hs : shiftedIndicator (F : Set ℕ) x N=1 := by
      simp only [shiftedIndicator,if_pos (show x≤N by omega),indicator]
      exact if_pos (Finset.mem_insert_self a P)
    have hd : pointMass (2*x) N=0 := by apply if_neg; omega
    rw [hs,hd,hFcenter] at he
    have he' : sumRep (insert x (F : Set ℕ)) N=2*m+2 := by exact_mod_cast he
    rw [he']
    dsimp [m]
    omega
  have hFlow : ∀ b∈F, L≤b := by
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · omega
    · have hh := (hP b hb).1; omega
  refine ⟨B,N,by omega,?_,?_,?_,hBcap,hblock,?_,?_,⟨F,hFB,hFlow,hFblock⟩⟩
  · exact Finset.subset_union_left.trans (Finset.subset_insert _ _)
  · intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact haN
    · rcases Finset.mem_union.mp hb with hb | hb
      · have := hC b hb; omega
      · exact (hP b hb).2.1
  · intro b hb
    have hba : b≠a := by omega
    have hbP : b∉P := by intro hh; have := (hP b hh).1; omega
    simp [B,hba,hbP]
  · rw [hBsmall (2*L) hNL,rep_zero_of_upper C L (2*L) hC (le_refl _)]
  · rw [hBcenter]
    dsimp [m]
    omega


end Erdos66TailCapBlocking
