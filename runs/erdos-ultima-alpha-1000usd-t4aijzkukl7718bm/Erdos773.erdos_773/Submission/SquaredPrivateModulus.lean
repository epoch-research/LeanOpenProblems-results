import Submission.PrivateModulusPacking

/-!
A square-modulus private-fiber selector: divisibility of roots by p yields
constant square values modulo p^2. Its cardinality cost still leaves only an
O(N^(2/3)) tail outside one largest fiber. This is not a bound on arbitrary
Sidon subsets of the squares.
-/
namespace Erdos773.SquaredPrivateModulus
open Finset PartialResidueFibers MatchedResidueLifting PrivateModulusPacking
set_option maxHeartbeats 1500000

/-- Root divisibility gives a stronger value modulus without demanding that
    the roots themselves all have the same residue modulo p^2. -/
theorem separate_fibers (q r s p c : ℕ) (A B : Finset ℕ)
    (hA : ∀ k ∈ A, k ≡ c [MOD p]) (hdiv : p ∣ q*c+r)
    (hB : Set.InjOn (fun k : ℕ => ((q*k+s)^2)%(p^2)) (B : Set ℕ)) :
    Disjoint (positiveDiffs (fiberValues q r A)) (positiveDiffs (fiberValues q s B)) := by
  apply separate_by_modulus (p^2) 0
  · intro a ha
    obtain ⟨k,hk,rfl⟩ := mem_image.mp ha
    have hmod : q*k+r ≡ q*c+r [MOD p] :=
      Nat.ModEq.add_right r (Nat.ModEq.mul_left q (hA k hk))
    have hd : p ∣ q*k+r := (hmod.dvd_iff (dvd_refl p)).mpr hdiv
    exact Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow_of_dvd hd 2)
  · intro a ha b hb he
    obtain ⟨k,hk,rfl⟩ := mem_image.mp ha
    obtain ⟨l,hl,rfl⟩ := mem_image.mp hb
    have h := hB hk hl he
    simp [h]

/-- A valid Sidon-union construction under the squared private-modulus rule. -/
theorem sidon_union (q : ℕ) (R : Finset ℕ) (B : ℕ → Finset ℕ) (P C : ℕ → ℕ)
    (hM : PairMatching q R)
    (hSidon : ∀ r ∈ R, IsSidon (fiberValues q r (B r) : Set ℕ))
    (hclass : ∀ r ∈ R, ∀ k ∈ B r, k ≡ C r [MOD P r])
    (hdiv : ∀ r ∈ R, P r ∣ q*C r+r)
    (hinj : ∀ r ∈ R, ∀ s ∈ R, r ≠ s →
      Set.InjOn (fun k : ℕ => ((q*k+s)^2)%((P r)^2)) (B s : Set ℕ)) :
    IsSidon ((R.biUnion (fun r => fiberValues q r (B r)) : Finset ℕ) : Set ℕ) := by
  apply (partial_square_iff q R B hM).mpr
  refine ⟨hSidon,?_⟩
  intro r hr s hs hrs
  exact separate_fibers q r s (P r) (C r) (B r) (B s)
    (hclass r hr) (hdiv r hr) (hinj r hr s hs hrs)

/-- The first fiber pays for a root residue modulo p, while the other fiber
    has injective square residues modulo p^2. These are different costs. -/
theorem pair_card_cost (q s p c H : ℕ) (A B : Finset ℕ) (hp : 0 < p)
    (hA : A ⊆ Icc 0 H) (hclass : ∀ a ∈ A, a ≡ c [MOD p])
    (hinj : Set.InjOn (fun b : ℕ => ((q*b+s)^2)%(p^2)) (B : Set ℕ)) :
    (A.card-1)^2*B.card ≤ H^2 := by
  have ha := residue_class_card p c H A hA hclass
  have hb := injective_square_residue_card q s (p^2) B (pow_pos hp 2) hinj
  have hquot : A.card-1 ≤ H/p := by
    simpa only [Nat.add_sub_cancel] using Nat.sub_le_sub_right ha 1
  have hmul : (A.card-1)*p ≤ H :=
    (Nat.mul_le_mul_right p hquot).trans (Nat.div_mul_le_self H p)
  calc
    _ ≤ (A.card-1)^2*p^2 := Nat.mul_le_mul_left _ hb
    _ = ((A.card-1)*p)^2 := (mul_pow _ _ _).symm
    _ ≤ H^2 := Nat.pow_le_pow_left hmul 2

private lemma cubic_cost {m H : ℕ} (h : (m-1)^2*m ≤ H^2) : m^3 ≤ 4*H^2+1 := by
  by_cases hm : m ≤ 1
  · interval_cases m <;> simp
  · have hh : m ≤ 2*(m-1) := by omega
    have hp := Nat.mul_le_mul_right m (Nat.pow_le_pow_left hh 2)
    nlinarith only [hp,h]

/-- Abstract tail bound for these squared private-modulus costs. It applies
    to partial fibers, not just to full index intervals. -/
theorem capacity_tail_sixth (q H : ℕ) (R : Finset ℕ) (m : ℕ → ℕ)
    (hq : 0 < q) (hR : R.Nonempty) (hM : PairMatching q R)
    (hcost : ∀ r ∈ R, ∀ s ∈ R, r ≠ s →
      (m r-1)^2*m s ≤ H^2 ∨ (m s-1)^2*m r ≤ H^2) :
    ∃ r₀ ∈ R, (∀ s ∈ R, m s ≤ m r₀) ∧
      (∑ s ∈ R.erase r₀, m s)^6 ≤ 200*(q*(H+1))^4 := by
  obtain ⟨r₀,hr₀,hmax⟩ := exists_max_image R m hR
  refine ⟨r₀,hr₀,hmax,?_⟩
  have hsmall : ∀ s ∈ R.erase r₀, (m s)^3 ≤ 5*(H+1)^2 := by
    intro s hs
    obtain ⟨hsne,hsR⟩ := mem_erase.mp hs
    have hm := hmax s hsR
    have hc : (m s-1)^2*m s ≤ H^2 := by
      rcases hcost r₀ hr₀ s hsR hsne.symm with h | h
      · exact (Nat.mul_le_mul_right _
          (Nat.pow_le_pow_left (Nat.sub_le_sub_right hm 1) 2)).trans h
      · exact (Nat.mul_le_mul_left _ hm).trans h
    have hh := cubic_cost hc
    nlinarith only [hh,Nat.zero_le H]
  by_cases hT : (R.erase r₀).Nonempty
  · obtain ⟨s,hs,hmaxs⟩ := exists_max_image (R.erase r₀) m hT
    have hsum : (∑ t ∈ R.erase r₀, m t) ≤ R.card*m s := by
      calc
        _ ≤ ∑ _t ∈ R.erase r₀, m s := sum_le_sum hmaxs
        _ = (R.erase r₀).card*m s := by simp
        _ ≤ R.card*m s := Nat.mul_le_mul_right _ (card_le_card (erase_subset r₀ R))
    have hk := Nat.pow_le_pow_left (pairMatching_card q R hq hM) 3
    have hm := Nat.pow_le_pow_left (hsmall s hs) 2
    have hk' : R.card^6 ≤ 8*q^3 := by simpa only [mul_pow,← pow_mul] using hk
    have hm' : (m s)^6 ≤ 25*(H+1)^4 := by simpa only [mul_pow,← pow_mul] using hm
    calc
      _ ≤ (R.card*m s)^6 := Nat.pow_le_pow_left hsum 6
      _ = R.card^6*(m s)^6 := mul_pow _ _ _
      _ ≤ (8*q^3)*(25*(H+1)^4) := Nat.mul_le_mul hk' hm'
      _ = 200*q^3*(H+1)^4 := by ring
      _ ≤ 200*q^4*(H+1)^4 := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by omega : 1 ≤ q) (by omega : 3 ≤ 4)))
      _ = _ := by ring
  · have he : R.erase r₀ = ∅ := not_nonempty_iff_eq_empty.mp hT
    simp [he]

/-- The selected union has an O((q(H+1))^(2/3)) tail outside one largest
    fiber. The parameter q(H+1) bounds root height when labels are canonical;
    canonical labels are not needed for this cardinality inequality itself.
    No bound on the largest fiber or on arbitrary compatible fibers is asserted. -/
theorem private_union_bound (q H : ℕ) (R : Finset ℕ)
    (B : ℕ → Finset ℕ) (P C : ℕ → ℕ) (hq : 0 < q) (hR : R.Nonempty)
    (hM : PairMatching q R) (hP : ∀ r ∈ R, 0 < P r)
    (hB : ∀ r ∈ R, B r ⊆ Icc 0 H)
    (hclass : ∀ r ∈ R, ∀ k ∈ B r, k ≡ C r [MOD P r])
    (hinj : ∀ r ∈ R, ∀ s ∈ R, r ≠ s →
      Set.InjOn (fun k : ℕ => ((q*k+s)^2)%((P r)^2)) (B s : Set ℕ)) :
    ∃ r₀ ∈ R, (∀ s ∈ R, (B s).card ≤ (B r₀).card) ∧
      ((R.biUnion (fun r => fiberValues q r (B r))).card:ℝ) ≤
        (B r₀).card+3*((q*(H+1):ℕ):ℝ)^(2/3:ℝ) := by
  have hcost : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → ((B r).card-1)^2*(B s).card ≤ H^2 := by
    intro r hr s hs hrs
    exact pair_card_cost q s (P r) (C r) H (B r) (B s) (hP r hr)
      (hB r hr) (hclass r hr) (hinj r hr s hs hrs)
  obtain ⟨r₀,hr₀,hmax,hbound⟩ := capacity_tail_sixth q H R (fun r => (B r).card) hq hR hM
    (fun r hr s hs hrs => Or.inl (hcost r hr s hs hrs))
  refine ⟨r₀,hr₀,hmax,?_⟩
  have hb : ((∑ s ∈ R.erase r₀, (B s).card:ℕ):ℝ)^6 ≤ 200*((q*(H+1):ℕ):ℝ)^4 := by
    exact_mod_cast hbound
  have htail : ((∑ s ∈ R.erase r₀, (B s).card:ℕ):ℝ) ≤
      3*((q*(H+1):ℕ):ℝ)^(2/3:ℝ) := by
    apply le_of_pow_le_pow_left₀ (by decide : (6:ℕ) ≠ 0) (by positivity)
    have he : (3*((q*(H+1):ℕ):ℝ)^(2/3:ℝ))^6 = 729*((q*(H+1):ℕ):ℝ)^4 := by
      rw [mul_pow,← Real.rpow_mul_natCast (Nat.cast_nonneg (q*(H+1)))]
      norm_num
    rw [he]
    nlinarith only [hb,pow_nonneg (Nat.cast_nonneg (α := ℝ) (q*(H+1))) 4]
  rw [partial_card q R B hq hM,← sum_erase_add R (fun r => (B r).card) hr₀]
  push_cast at htail ⊢
  linarith only [htail]

/-- A concrete gain over testing the same private modulus only to the first
    power. This demonstrates one-way separation, not all-fibers private data,
    and is not an asymptotic construction. -/
theorem squared_modulus_example :
    Disjoint (positiveDiffs (fiberValues 11 3 {0,3}))
      (positiveDiffs (fiberValues 11 1 {0,1,2})) ∧
    IsSidon ((fiberValues 11 3 {0,3} ∪ fiberValues 11 1 {0,1,2} : Finset ℕ) : Set ℕ) ∧
    Set.InjOn (fun k : ℕ => ((11*k+1)^2)%9) ({0,1,2} : Finset ℕ) ∧
    ¬ Set.InjOn (fun k : ℕ => ((11*k+1)^2)%3) ({0,1,2} : Finset ℕ) := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_⟩
  · intro a ha b hb he
    simp only [Finset.mem_coe,mem_insert,mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> norm_num at *
  · intro h
    have hh := h (show (0:ℕ) ∈ ({0,1,2} : Finset ℕ) by simp)
      (show (2:ℕ) ∈ ({0,1,2} : Finset ℕ) by simp)
      (by norm_num : ((11*0+1:ℕ)^2)%3=((11*2+1:ℕ)^2)%3)
    norm_num at hh

#print axioms squared_modulus_example
#print axioms separate_fibers
#print axioms sidon_union
#print axioms pair_card_cost
#print axioms capacity_tail_sixth
#print axioms private_union_bound
end Erdos773.SquaredPrivateModulus
