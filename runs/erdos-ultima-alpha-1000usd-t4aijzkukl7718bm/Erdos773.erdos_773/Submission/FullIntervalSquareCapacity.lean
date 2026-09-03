import Submission.ShiftedFiberOverlap
import Submission.PartialResidueFibers

/-! Packing full intervals of square roots by their short-gap weighted centers.
This capacity theorem does not apply to arbitrary sparse selections. -/
namespace Erdos773.FullIntervalSquareCapacity
open Finset
set_option maxHeartbeats 2000000

variable {ι : Type*} [DecidableEq ι]

def block (H : ℕ) (start : ι → ℕ) (i : ι) : Finset ℕ :=
  Icc (start i) (start i+H)

def roots (H : ℕ) (I : Finset ι) (start : ι → ℕ) : Finset ℕ :=
  I.biUnion (block H start)

def key (T : ℕ) (start : ι → ℕ) (z : ι × ℕ) : ℕ :=
  z.2*(start z.1+5*T)/T^2

omit [DecidableEq ι] in
lemma key_collision {T : ℕ} {start : ι → ℕ} {i j : ι} {u v : ℕ}
    (hT : 0 < T) (hu : u ∈ Icc T (2*T)) (hv : v ∈ Icc T (2*T))
    (he : key T start (i,u) = key T start (j,v)) :
    ∃ a c : ℕ, start i ≤ a ∧ a+2*u ≤ start i+10*T ∧
      start j ≤ c ∧ c+2*v ≤ start j+10*T ∧
      (a+2*u)^2+c^2=a^2+(c+2*v)^2 := by
  have hc := ShiftedFiberOverlap.same_bin_close (by positivity : 0<T^2) he
  have hh := ShiftedFiberOverlap.close_center_collision
    (q := 1) (r := 0) (s := 0) (A := start i) (B := start j)
    (by decide) hT hu hv (by simp) (by decide) (by decide) (by simp [Nat.ModEq])
    (by simpa [ShiftedFiberOverlap.center] using hc.1)
    (by simpa [ShiftedFiberOverlap.center] using hc.2)
  simpa only [one_mul, add_zero] using hh

lemma key_injective {H T : ℕ} {I : Finset ι} {start : ι → ℕ}
    (hT : 0<T) (hTH : 10*T≤H)
    (hdis : ∀ i∈I, ∀ j∈I, i≠j → Disjoint (block H start i) (block H start j))
    (hS : IsSidon (((roots H I start).image (fun n => n^2)) : Set ℕ)) :
    Set.InjOn (key T start) ((I ×ˢ Icc T (2*T) : Finset (ι × ℕ)) : Set (ι × ℕ)) := by
  rintro ⟨i,u⟩ hiu ⟨j,v⟩ hjv he
  obtain ⟨hi,hu⟩ := mem_product.mp hiu
  obtain ⟨hj,hv⟩ := mem_product.mp hjv
  obtain ⟨a,c,ha,haH,hc,hcH,hcol⟩ := key_collision hT hu hv he
  dsimp only at ha haH hc hcH hcol
  have hu0 : 0<u := hT.trans_le (mem_Icc.mp hu).1
  have hv0 : 0<v := hT.trans_le (mem_Icc.mp hv).1
  have haB : a ∈ block H start i := mem_Icc.mpr ⟨ha,by omega⟩
  have haE : a+2*u ∈ block H start i := mem_Icc.mpr ⟨by omega,by omega⟩
  have hcB : c ∈ block H start j := mem_Icc.mpr ⟨hc,by omega⟩
  have hcE : c+2*v ∈ block H start j := mem_Icc.mpr ⟨by omega,by omega⟩
  have hmem {i : ι} (hi : i∈I) {n : ℕ} (hn : n∈block H start i) :
      n^2 ∈ (roots H I start).image (fun n => n^2) :=
    mem_image.mpr ⟨n,mem_biUnion.mpr ⟨i,hi,hn⟩,rfl⟩
  have hal : a^2 < (a+2*u)^2 :=
    Nat.pow_lt_pow_left (by omega) (by decide : (2 : ℕ)≠0)
  have hcl : c^2 < (c+2*v)^2 :=
    Nat.pow_lt_pow_left (by omega) (by decide : (2 : ℕ)≠0)
  obtain ⟨hlo,hhi⟩ := PartialResidueFibers.endpoints_unique hS
    (hmem hi haB) (hmem hi haE) (hmem hj hcB) (hmem hj hcE)
    hal hcl (by omega)
  have hac : a=c := Nat.pow_left_injective (by decide : (2 : ℕ)≠0) hlo
  have heq : a+2*u=c+2*v := Nat.pow_left_injective (by decide : (2 : ℕ)≠0) hhi
  have hij : i=j := by
    by_contra h
    exact disjoint_left.mp (hdis i hi j hj h) haB (hac ▸ hcB)
  exact Prod.ext hij (by omega)

/-- One-dimensional bins suffice when no residue labels need to be retained. -/
theorem gap_capacity {N H T : ℕ} {I : Finset ι} {start : ι → ℕ}
    (hT : 0<T) (hTH : 10*T≤H)
    (hheight : ∀ i∈I, start i+H≤N)
    (hdis : ∀ i∈I, ∀ j∈I, i≠j → Disjoint (block H start i) (block H start j))
    (hS : IsSidon (((roots H I start).image (fun n => n^2)) : Set ℕ)) :
    I.card*(T+1)*T ≤ 2*N+T := by
  have hc := card_le_card_of_injOn (s := I ×ˢ Icc T (2*T))
    (t := range (2*T*N/T^2+1)) (key T start) (by
      rintro ⟨i,u⟩ hiu
      obtain ⟨hi,hu⟩ := mem_product.mp hiu
      have hu2 := (mem_Icc.mp hu).2
      have hcenter : start i+5*T≤N := by have := hheight i hi; omega
      have hp : u*(start i+5*T)≤2*T*N := Nat.mul_le_mul hu2 hcenter
      have hd := Nat.div_le_div_right (c := T^2) hp
      exact mem_range.mpr (by dsimp [key]; omega))
    (key_injective hT hTH hdis hS)
  have hcc : (Icc T (2*T)).card=T+1 := by simp only [Nat.card_Icc]; omega
  rw [card_product,hcc,card_range] at hc
  have hd := Nat.mul_div_le (2*T*N) (T^2)
  have hh : T*(T*(2*T*N/T^2))≤T*(2*N) := by nlinarith only [hd]
  have hd' : T*(2*T*N/T^2)≤2*N := Nat.le_of_mul_le_mul_left hh hT
  have hm := Nat.mul_le_mul_right T hc
  nlinarith only [hm,hd']

/-- Full disjoint intervals of a common positive width have bounded total
squared width. No modular pair matching is assumed. -/
theorem squared_width_capacity {N H : ℕ} {I : Finset ι} {start : ι → ℕ}
    (hH : 10≤H) (hheight : ∀ i∈I, start i+H≤N)
    (hdis : ∀ i∈I, ∀ j∈I, i≠j → Disjoint (block H start i) (block H start j))
    (hS : IsSidon (((roots H I start).image (fun n => n^2)) : Set ℕ)) :
    I.card*H^2≤1200*N := by
  by_cases hne : I.Nonempty
  · obtain ⟨i,hi⟩ := hne
    let T := H/10
    have hT : 0<T := by dsimp [T]; omega
    have hTH : 10*T≤H := Nat.mul_div_le H 10
    have hHT : H≤20*T := by dsimp [T]; omega
    have hTN : T≤N := by have := hheight i hi; omega
    have hc := gap_capacity hT hTH hheight hdis hS
    have hcap : I.card*T^2≤3*N := by nlinarith only [hc,hTN]
    have hs := Nat.mul_le_mul_left I.card (Nat.pow_le_pow_left hHT 2)
    nlinarith only [hs,hcap]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

end Erdos773.FullIntervalSquareCapacity

#print axioms Erdos773.FullIntervalSquareCapacity.key_collision
#print axioms Erdos773.FullIntervalSquareCapacity.key_injective
#print axioms Erdos773.FullIntervalSquareCapacity.gap_capacity
#print axioms Erdos773.FullIntervalSquareCapacity.squared_width_capacity
