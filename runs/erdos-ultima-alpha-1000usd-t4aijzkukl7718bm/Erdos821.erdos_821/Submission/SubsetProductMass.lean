import FormalConjecturesUtil

/-!
# A lower bound for weighted squarefree subset products

If each individual weight is small compared with the total mass, the
mass of r-element subsets has the expected factorial lower bound.
-/
open Finset
open scoped Classical BigOperators
namespace Erdos821
set_option maxHeartbeats 3000000

noncomputable def elementaryMass (P : Finset ℕ) (w : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ S ∈ P.powersetCard r, ∏ p ∈ S, w p

lemma elementaryMass_nonneg (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (r : ℕ) : 0 ≤ elementaryMass P w r := by
  exact sum_nonneg (fun S hS => prod_nonneg (fun p hp => hw p ((mem_powersetCard.mp hS).1 hp)))

lemma elementaryMass_zero (P : Finset ℕ) (w : ℕ → ℝ) : elementaryMass P w 0 = 1 := by
  simp [elementaryMass]

lemma elementaryMass_succ_identity (P : Finset ℕ) (w : ℕ → ℝ) (r : ℕ) :
    ((r+1 : ℕ) : ℝ)*elementaryMass P w (r+1) =
      ∑ S ∈ P.powersetCard r, (∏ p ∈ S, w p)*(∑ p ∈ P \ S, w p) := by
  let A := (P.powersetCard r ×ˢ P).filter (fun z => z.2 ∉ z.1)
  let B := (P.powersetCard (r+1) ×ˢ P).filter (fun z => z.2 ∈ z.1)
  have hbij : (∑ z ∈ A, (∏ p ∈ z.1, w p)*w z.2) =
      ∑ z ∈ B, ∏ p ∈ z.1, w p := by
    apply sum_bij (fun z _ => (insert z.2 z.1,z.2))
    · intro z hz
      obtain ⟨hz,hnot⟩ := mem_filter.mp hz
      obtain ⟨hS,hp⟩ := mem_product.mp hz
      obtain ⟨hSP,hcard⟩ := mem_powersetCard.mp hS
      exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_powersetCard.mpr
        ⟨insert_subset hp hSP,by rw [card_insert_of_notMem hnot,hcard]⟩,hp⟩,
        mem_insert_self _ _⟩
    · intro z hz y hy he
      have hzy := congrArg (fun a : Finset ℕ × ℕ => a.2) he
      have hS := congrArg (fun a : Finset ℕ × ℕ => a.1) he
      dsimp only at hzy hS
      have hznot := (mem_filter.mp hz).2
      have hynot := (mem_filter.mp hy).2
      have h := congrArg (fun S : Finset ℕ => S.erase z.2) hS
      rw [hzy] at h hznot
      simp only [erase_insert hznot,erase_insert hynot] at h
      exact Prod.ext h hzy
    · intro z hz
      obtain ⟨hz,hpS⟩ := mem_filter.mp hz
      obtain ⟨hS,hpP⟩ := mem_product.mp hz
      obtain ⟨hSP,hcard⟩ := mem_powersetCard.mp hS
      refine ⟨(z.1.erase z.2,z.2),mem_filter.mpr ⟨mem_product.mpr ⟨?_,hpP⟩,notMem_erase _ _⟩,?_⟩
      · exact mem_powersetCard.mpr ⟨(erase_subset _ _).trans hSP,by rw [card_erase_of_mem hpS,hcard]; omega⟩
      · simp only [insert_erase hpS]
    · intro z hz
      have hnot := (mem_filter.mp hz).2
      simp only [prod_insert hnot,mul_comm]
  have hleft : (∑ z ∈ A, (∏ p ∈ z.1, w p)*w z.2) =
      ∑ S ∈ P.powersetCard r, (∏ p ∈ S, w p)*(∑ p ∈ P \ S, w p) := by
    simp only [A,sum_filter,sum_product,mul_sum]
    apply sum_congr rfl
    intro S hS
    rw [← sum_filter]
    congr 1
    ext p
    simp only [mem_filter,mem_sdiff]
  have hright : (∑ z ∈ B, ∏ p ∈ z.1, w p) =
      ((r+1 : ℕ) : ℝ)*elementaryMass P w (r+1) := by
    simp only [B,sum_filter,sum_product,elementaryMass,mul_sum]
    apply sum_congr rfl
    intro S hS
    have hfilter : P.filter (fun p => p ∈ S) = S := by
      ext p
      simp only [mem_filter]
      exact ⟨fun h => h.2,fun hp => ⟨(mem_powersetCard.mp hS).1 hp,hp⟩⟩
    rw [← sum_filter,hfilter,sum_const,nsmul_eq_mul,(mem_powersetCard.mp hS).2]
  exact hright.symm.trans (hbij.symm.trans hleft)

lemma elementaryMass_succ_lower (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (b : ℝ) (hb : ∀ p ∈ P, w p ≤ b) (r : ℕ) :
    elementaryMass P w r * ((∑ p ∈ P, w p)-(r : ℝ)*b) ≤
      ((r+1 : ℕ) : ℝ)*elementaryMass P w (r+1) := by
  rw [elementaryMass_succ_identity,elementaryMass,sum_mul]
  apply sum_le_sum
  intro S hS
  have hSP := (mem_powersetCard.mp hS).1
  have hsmall : (∑ p ∈ S, w p) ≤ (r : ℝ)*b := by
    calc
      _ ≤ ∑ _p ∈ S, b := sum_le_sum (fun p hp => hb p (hSP hp))
      _ = _ := by rw [sum_const,nsmul_eq_mul,(mem_powersetCard.mp hS).2]
  have hsplit := sum_sdiff hSP (f := w)
  apply mul_le_mul_of_nonneg_left _ (prod_nonneg (fun p hp => hw p (hSP hp)))
  linarith

/-- The estimate is uniform in r; r need not be fixed as the pool changes. -/
theorem elementaryMass_factorial_lower (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (b μ : ℝ) (hb : 0 ≤ b) (hμ : 0 ≤ μ)
    (hwb : ∀ p ∈ P, w p ≤ b) (r : ℕ)
    (hmass : μ+(r : ℝ)*b ≤ ∑ p ∈ P, w p) :
    μ^r/(r.factorial : ℝ) ≤ elementaryMass P w r := by
  induction r with
  | zero => simp [elementaryMass_zero]
  | succ r ih =>
    have hmass' : μ+(r : ℝ)*b ≤ ∑ p ∈ P, w p := by
      push_cast at hmass
      linarith
    have hi := ih hmass'
    have hlo : μ ≤ (∑ p ∈ P, w p)-(r : ℝ)*b := by linarith
    have hs := elementaryMass_succ_lower P w hw b hwb r
    have hm := mul_le_mul_of_nonneg_right hi hμ
    have hn := mul_le_mul_of_nonneg_left hlo (elementaryMass_nonneg P w hw r)
    have hpos : (0 : ℝ) < r+1 := by positivity
    apply (le_of_mul_le_mul_left ?_ hpos)
    calc
      ((r : ℝ)+1)*(μ^(r+1)/((r+1).factorial : ℝ)) = (μ^r/(r.factorial : ℝ))*μ := by
        rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
        field_simp
      _ ≤ elementaryMass P w r*μ := hm
      _ ≤ elementaryMass P w r*((∑ p ∈ P, w p)-(r : ℝ)*b) := hn
      _ ≤ ((r : ℝ)+1)*elementaryMass P w (r+1) := by simpa only [Nat.cast_add,Nat.cast_one] using hs

end Erdos821
