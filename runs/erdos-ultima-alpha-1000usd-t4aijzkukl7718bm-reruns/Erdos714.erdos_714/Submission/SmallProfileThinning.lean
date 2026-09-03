import Submission.ProfileThinning

/-! Arbitrary edge thinnings with small set-valued neighborhood profiles.
This is a restricted-model bound, not a resolution of Erdős 714. -/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 2000000
namespace Erdos714SmallProfiles
variable {C X T P : Type*} [Fintype C] [Fintype X] [Fintype T] [Fintype P]

def neighbors (g : X → C → P) (Z : X → P → Finset T) (c : C) : Finset (X × T) :=
  univ.filter (fun p => p.2 ∈ Z p.1 (g p.1 c))

def graph (g : X → C → P) (Z : X → P → Finset T) : SimpleGraph (C ⊕ (X × T)) :=
  Erdos714Packing.incidence (neighbors g Z)

/-- Profile fibers are chunked, so no bound on their individual sizes is
needed. The set represented by each profile has at most2q points. -/
theorem fourth_power (g : X → C → P) (Z : X → P → Finset T)
    (q : ℕ) (hq : 0<q) (hZ : ∀ x p, (Z x p).card ≤ 2*q)
    (H : SimpleGraph (C ⊕ (X × T))) (hH : H ≤ graph g Z)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 1327104*
      (∑ x : X, Fintype.card (Erdos714ProfileChunks.Index (g x) q))^4*q^7 := by
  let J := Σ x : X, Erdos714ProfileChunks.Index (g x) q
  let L (j : J) : Finset (C ⊕ (X × T)) :=
    (Erdos714ProfileChunks.block (g j.1) q j.2).map Function.Embedding.inl
  let R (j : J) : Finset (C ⊕ (X × T)) :=
    (Z j.1 j.2.1).map ⟨fun t => Sum.inr (j.1,t),by
      intro t u h; exact congrArg Prod.snd (Sum.inr.inj h)⟩
  have hsize (j : J) : (L j ∪ R j).card ≤ 2*(2*q) := by
    have hl : (L j).card ≤ q := by
      simpa only [L,card_map] using Erdos714ProfileChunks.block_size (g j.1) q hq j.2
    have hr : (R j).card ≤ 2*q := by simpa only [R,card_map] using hZ j.1 j.2.1
    have h := card_union_le (L j) (R j)
    omega
  have hforward (c : C) (x : X) (t : T) (ht : t ∈ Z x (g x c)) :
      ∃ j : J, Sum.inl c ∈ L j ∪ R j ∧ Sum.inr (x,t) ∈ L j ∪ R j := by
    obtain ⟨k,hk⟩ := Erdos714ProfileChunks.block_cover (g x) q c
    have hp := Erdos714ProfileChunks.block_profile (g x) q k hk
    refine ⟨⟨x,k⟩,mem_union_left _ (mem_map.mpr ⟨c,hk,rfl⟩),?_⟩
    apply mem_union_right
    apply mem_map.mpr
    exact ⟨t,by simpa only [hp] using ht,rfl⟩
  have hcover : ∀ v w, H.Adj v w → ∃ j : J, v ∈ L j ∪ R j ∧ w ∈ L j ∪ R j := by
    intro v w hvw
    have h := hH hvw
    cases v with
    | inl c =>
      cases w with
      | inl d => exact False.elim h
      | inr p => exact hforward c p.1 p.2 ((mem_filter.mp h).2)
    | inr p =>
      cases w with
      | inr u => exact False.elim h
      | inl c =>
        obtain ⟨j,hc,hp⟩ := hforward c p.1 p.2 ((mem_filter.mp h).2)
        exact ⟨j,hp,hc⟩
  have hb := Erdos714BlockThinning.fourth_power_of_block_cover H hf
    (fun j : J => L j ∪ R j) (2*q) hsize hcover
  simp only [J,Fintype.card_sigma] at hb
  convert hb using 1
  ring

/-- q^2 slices, q^4 columns, and at most4q^3 profiles imply a subcritical
q^(27/4) edge bound, even after arbitrary edge deletions. -/
theorem critical_bound (g : X → C → P) (Z : X → P → Finset T)
    (q : ℕ) (hq : 0<q) (hZ : ∀ x p, (Z x p).card ≤ 2*q)
    (hX : Fintype.card X ≤ q^2) (hC : Fintype.card C ≤ q^4)
    (hP : Fintype.card P ≤ 4*q^3)
    (H : SimpleGraph (C ⊕ (X × T))) (hH : H ≤ graph g Z)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 829440000*q^27 := by
  have hi (x : X) : Fintype.card (Erdos714ProfileChunks.Index (g x) q) ≤ 5*q^3 := by
    have h := Erdos714ProfileChunks.cardinality_budget (g x) q
    have hb : q*Fintype.card (Erdos714ProfileChunks.Index (g x) q) ≤ q*(5*q^3) := by
      calc
        _ ≤ Fintype.card C+q*Fintype.card P := h
        _ ≤ q^4+q*(4*q^3) := Nat.add_le_add hC (Nat.mul_le_mul_left _ hP)
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left hb hq
  have hs : (∑ x : X, Fintype.card (Erdos714ProfileChunks.Index (g x) q)) ≤ 5*q^5 := by
    calc
      _ ≤ ∑ _x : X, 5*q^3 := sum_le_sum (fun x _ => hi x)
      _ = Fintype.card X*(5*q^3) := by simp
      _ ≤ q^2*(5*q^3) := Nat.mul_le_mul_right _ hX
      _ = _ := by ring
  calc
    _ ≤ 1327104*(∑ x : X, Fintype.card (Erdos714ProfileChunks.Index (g x) q))^4*q^7 :=
      fourth_power g Z q hq hZ H hH hf
    _ ≤ 1327104*(5*q^5)^4*q^7 := by gcongr
    _ = _ := by ring

#print axioms fourth_power
#print axioms critical_bound
end Erdos714SmallProfiles
