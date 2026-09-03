import Submission.ShortSeparationPrimeCollisions

/-! Removal of all sublinear-separation collisions from the dyadic signed
critical-energy criterion. The remaining macroscopic collisions are unproved. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

noncomputable def dyadicNearLoserPairs (D N : ℕ) : Finset (ℕ × ℕ) :=
  ((Ico N (2*N)).offDiag).filter fun nm =>
    primeLoser nm.1=primeLoser nm.2 ∧ Nat.dist nm.1 nm.2≤D

noncomputable def criticalLoserPairWeight (nm : ℕ × ℕ) : ℝ :=
  (primeLoser nm.1 : ℝ)/((nm.1 : ℝ)*(nm.2 : ℝ))

noncomputable def dyadicNearLoserMass (D N : ℕ) : ℝ :=
  ∑ nm ∈ dyadicNearLoserPairs D N, criticalLoserPairWeight nm

lemma criticalLoserPairWeight_nonneg (nm : ℕ × ℕ) : 0≤criticalLoserPairWeight nm := by
  unfold criticalLoserPairWeight
  positivity

lemma dyadicNearLoserPairs_mem (D N n m : ℕ) :
    (n,m)∈dyadicNearLoserPairs D N ↔
      n∈Ico N (2*N) ∧ m∈Ico N (2*N) ∧ n≠m ∧
        primeLoser n=primeLoser m ∧ Nat.dist n m≤D := by
  simp only [dyadicNearLoserPairs,mem_filter,mem_offDiag]
  tauto

lemma dyadicNearLoserPairs_swap (D N n m : ℕ)
    (h : (n,m)∈dyadicNearLoserPairs D N) : (m,n)∈dyadicNearLoserPairs D N := by
  rw [dyadicNearLoserPairs_mem] at h ⊢
  exact ⟨h.2.1,h.1,Ne.symm h.2.2.1,h.2.2.2.1.symm,by simpa only [Nat.dist_comm] using h.2.2.2.2⟩

lemma dyadicNearLoserMass_eq_twice_forward (D N : ℕ) :
    dyadicNearLoserMass D N =
      2*∑ nm ∈ (dyadicNearLoserPairs D N).filter (fun nm => nm.1<nm.2),
        criticalLoserPairWeight nm := by
  let T := dyadicNearLoserPairs D N
  have he : (∑ nm ∈ T.filter (fun nm => ¬nm.1<nm.2), criticalLoserPairWeight nm)=
      ∑ nm ∈ T.filter (fun nm => nm.1<nm.2), criticalLoserPairWeight nm := by
    apply sum_bij (fun nm _ => (nm.2,nm.1))
    · intro nm hnm
      obtain ⟨hnm,hnot⟩ := mem_filter.mp hnm
      have hd := (dyadicNearLoserPairs_mem D N nm.1 nm.2).mp hnm
      exact mem_filter.mpr ⟨dyadicNearLoserPairs_swap D N _ _ hnm,by omega⟩
    · intro nm hnm kl hkl he
      exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
    · intro nm hnm
      obtain ⟨hnm,hlt⟩ := mem_filter.mp hnm
      exact ⟨(nm.2,nm.1),mem_filter.mpr ⟨dyadicNearLoserPairs_swap D N _ _ hnm,by omega⟩,rfl⟩
    · intro nm hnm
      have hd := (dyadicNearLoserPairs_mem D N nm.1 nm.2).mp (mem_filter.mp hnm).1
      unfold criticalLoserPairWeight
      dsimp only
      rw [hd.2.2.2.1,mul_comm]
  have hs := sum_filter_add_sum_filter_not T (fun nm => nm.1<nm.2) criticalLoserPairWeight
  rw [he] at hs
  change (∑ nm ∈ T, criticalLoserPairWeight nm)=_
  linarith

lemma dyadicNearLoser_forward_offset_sum (D N : ℕ) :
    (∑ nm ∈ (dyadicNearLoserPairs D N).filter (fun nm => nm.1<nm.2), criticalLoserPairWeight nm) =
      ∑ n ∈ Ico N (2*N),
        ∑ d ∈ (Icc 1 D).filter (fun d => n+d<2*N ∧ primeLoser (n+d)=primeLoser n),
          (primeLoser n : ℝ)/((n : ℝ)*(n+d : ℕ)) := by
  rw [sum_sigma']
  apply sum_bij (fun nm _ => ⟨nm.1,nm.2-nm.1⟩)
  · intro nm hnm
    obtain ⟨hnm,hlt⟩ := mem_filter.mp hnm
    obtain ⟨hn,hm,hne,hp,hd⟩ := (dyadicNearLoserPairs_mem D N nm.1 nm.2).mp hnm
    rw [Nat.dist_eq_sub_of_le hlt.le] at hd
    apply mem_sigma.mpr
    dsimp only
    refine ⟨hn,mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hd⟩,?_,?_⟩⟩
    · have := (mem_Ico.mp hm).2
      omega
    · simpa only [Nat.add_sub_of_le hlt.le] using hp.symm
  · intro nm hnm kl hkl he
    have h1 := congrArg Sigma.fst he
    have h2 := congrArg (fun x : Σ _ : ℕ, ℕ => x.2) he
    have hn := (mem_filter.mp hnm).2
    have hk := (mem_filter.mp hkl).2
    apply Prod.ext <;> dsimp only at * <;> omega
  · intro nd hnd
    obtain ⟨hn,hd⟩ := mem_sigma.mp hnd
    obtain ⟨hd,hU,hp⟩ := mem_filter.mp hd
    obtain ⟨hd1,hdD⟩ := mem_Icc.mp hd
    refine ⟨(nd.1,nd.1+nd.2),mem_filter.mpr ⟨?_,by dsimp; omega⟩,?_⟩
    · apply (dyadicNearLoserPairs_mem D N _ _).mpr
      refine ⟨hn,mem_Ico.mpr ⟨?_,hU⟩,by omega,hp.symm,?_⟩
      · have := (mem_Ico.mp hn).1
        omega
      · rw [Nat.dist_eq_sub_of_le (by omega)]
        simpa only [Nat.add_sub_cancel_left] using hdD
    · simp only [Nat.add_sub_cancel_left]
  · intro nm hnm
    have hlt := (mem_filter.mp hnm).2
    simp only [criticalLoserPairWeight,Nat.add_sub_of_le hlt.le]

/-- The full ordered near-diagonal mass is bounded, including both
orientations and the separately controlled adjacent pairs. -/
theorem dyadicNearLoserMass_bound (D N : ℕ) (hN : 0<N) :
    dyadicNearLoserMass D N ≤ 2*dyadicLoserWindowDiagonal N+6*(D+1 : ℝ)/N := by
  have hforward : (∑ n ∈ Ico N (2*N),
      ∑ d ∈ (Icc 1 D).filter (fun d => n+d<2*N ∧ primeLoser (n+d)=primeLoser n),
        (primeLoser n : ℝ)/((n : ℝ)*(n+d : ℕ))) ≤
      dyadicLoserWindowDiagonal N+dyadicForwardNearLoserMass D N := by
    rw [dyadicLoserWindowDiagonal,dyadicForwardNearLoserMass,← sum_add_distrib]
    apply sum_le_sum
    intro n hn
    let S := (Icc 1 D).filter (fun d => n+d<2*N ∧ primeLoser (n+d)=primeLoser n)
    have hsub : S⊆insert 1 (nearLoserOffsets D (2*N) n) := by
      intro d hd
      obtain ⟨hd,hU,hp⟩ := mem_filter.mp hd
      by_cases h1 : d=1
      · exact mem_insert.mpr (Or.inl h1)
      · exact mem_insert_of_mem (mem_filter.mpr
          ⟨mem_Icc.mpr ⟨by have := mem_Icc.mp hd; omega,(mem_Icc.mp hd).2⟩,hU,hp⟩)
    have hs := sum_le_sum_of_subset_of_nonneg (f := fun d =>
      (primeLoser n : ℝ)/((n : ℝ)*(n+d : ℕ))) hsub (by intros; positivity)
    rw [sum_insert (by simp [nearLoserOffsets] : 1∉nearLoserOffsets D (2*N) n)] at hs
    have ha := critical_pair_weight_le_diagonal (primeLoser n) n 1
      (hN.trans_le (mem_Ico.mp hn).1)
    exact hs.trans (add_le_add ha le_rfl)
  rw [dyadicNearLoserMass_eq_twice_forward,dyadicNearLoser_forward_offset_sum]
  have hh := dyadicForwardNearLoserMass_bound D N hN
  have he : 6*(D+1 : ℝ)/N=2*(3*(D+1 : ℝ)/N) := by ring
  rw [he]
  linarith

theorem dyadicNearLoserMass_zero (D : ℕ → ℕ)
    (hD : Tendsto (fun N => (D N : ℝ)/N) atTop (𝓝 0)) :
    Tendsto (fun N => dyadicNearLoserMass (D N) N) atTop (𝓝 0) := by
  have ht := (dyadicLoserWindowDiagonal_zero.const_mul 2).add
    ((hD.add tendsto_one_div_atTop_nhds_zero_nat).const_mul 6)
  simp only [add_zero,mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun N => by
    unfold dyadicNearLoserMass
    exact sum_nonneg (fun nm _ => criticalLoserPairWeight_nonneg nm))) _ ht
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  simpa only [add_div,mul_add,mul_div_assoc] using dyadicNearLoserMass_bound (D N) N hN

noncomputable def dyadicSignedLoserPairTerm (nm : ℕ × ℕ) : ℝ :=
  (primeLoser nm.1 : ℝ)*(factorSign nm.1/nm.1)*(factorSign nm.2/nm.2)

lemma dyadicSignedLoserPairTerm_norm (nm : ℕ × ℕ) :
    ‖dyadicSignedLoserPairTerm nm‖=criticalLoserPairWeight nm := by
  simp only [dyadicSignedLoserPairTerm,norm_mul,norm_div,factorSign_norm,
    Real.norm_natCast,criticalLoserPairWeight]
  ring

noncomputable def dyadicFarLoserSignedCollisions (D N : ℕ) : ℝ :=
  ∑ nm ∈ (((Ico N (2*N)).offDiag).filter
      (fun nm => primeLoser nm.1=primeLoser nm.2)).filter
      (fun nm => D<Nat.dist nm.1 nm.2), dyadicSignedLoserPairTerm nm

lemma dyadicSignedCollisions_near_far_split (D N : ℕ) :
    dyadicLoserWindowSignedCollisions N =
      (∑ nm ∈ dyadicNearLoserPairs D N, dyadicSignedLoserPairTerm nm)+
        dyadicFarLoserSignedCollisions D N := by
  have hs := sum_filter_add_sum_filter_not
    (((Ico N (2*N)).offDiag).filter (fun nm => primeLoser nm.1=primeLoser nm.2))
    (fun nm => Nat.dist nm.1 nm.2≤D) dyadicSignedLoserPairTerm
  simpa only [filter_filter,not_le,dyadicLoserWindowSignedCollisions,
    dyadicNearLoserPairs,dyadicFarLoserSignedCollisions,dyadicSignedLoserPairTerm] using hs.symm

lemma dyadicSignedCollisions_near_error_bound (D N : ℕ) :
    ‖dyadicLoserWindowSignedCollisions N-dyadicFarLoserSignedCollisions D N‖ ≤
      dyadicNearLoserMass D N := by
  rw [dyadicSignedCollisions_near_far_split,add_sub_cancel_right]
  simpa only [dyadicNearLoserMass,dyadicSignedLoserPairTerm_norm] using
    norm_sum_le (dyadicNearLoserPairs D N) dyadicSignedLoserPairTerm

/-- Removing ALL collisions at any sublinear separation changes the signed
critical-energy sum by o(1), without using cancellation in the removed part. -/
theorem dyadicSignedCollisions_sub_far_zero (D : ℕ → ℕ)
    (hD : Tendsto (fun N => (D N : ℝ)/N) atTop (𝓝 0)) :
    Tendsto (fun N => dyadicLoserWindowSignedCollisions N-
      dyadicFarLoserSignedCollisions (D N) N) atTop (𝓝 0) :=
  squeeze_zero_norm (fun N => dyadicSignedCollisions_near_error_bound (D N) N)
    (dyadicNearLoserMass_zero D hD)

/-- The long-separation condition is still unproved. Short-separation
removal is not by itself a proof of either limit. -/
theorem dyadicSignedCollisions_zero_iff_far (D : ℕ → ℕ)
    (hD : Tendsto (fun N => (D N : ℝ)/N) atTop (𝓝 0)) :
    Tendsto dyadicLoserWindowSignedCollisions atTop (𝓝 0) ↔
      Tendsto (fun N => dyadicFarLoserSignedCollisions (D N) N) atTop (𝓝 0) := by
  constructor
  · intro h
    simpa only [sub_sub_cancel,sub_zero] using h.sub (dyadicSignedCollisions_sub_far_zero D hD)
  · intro h
    simpa only [sub_add_cancel,add_zero] using (dyadicSignedCollisions_sub_far_zero D hD).add h

#print axioms dyadicSignedCollisions_sub_far_zero
#print axioms dyadicSignedCollisions_zero_iff_far
#print axioms dyadicNearLoserMass_bound
#print axioms dyadicNearLoserMass_zero
end Erdos371
