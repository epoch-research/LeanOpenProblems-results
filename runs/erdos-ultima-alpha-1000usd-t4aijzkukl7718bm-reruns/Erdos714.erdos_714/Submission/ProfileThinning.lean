import Submission.ColoredTensorThinning
import Submission.Coding

/-!
Arbitrary edge thinnings of locally low-profile code graphs. Splitting each
profile fiber into small blocks makes the Kővári–Sós–Turán block bound apply
without any upper bound on individual profile-fiber sizes.
This does not resolve Erdős 714.
-/

noncomputable section
open Finset SimpleGraph Classical
set_option maxHeartbeats 2000000

namespace Erdos714ProfileChunks

variable {C P : Type*} [Fintype C] [Fintype P]

/-- One extra, possibly empty, chunk avoids exceptional zero-fiber cases. -/
def Index (g : C → P) (q : ℕ) :=
  Σ p : P, Fin (Fintype.card {c // g c = p} / q + 1)

instance (g : C → P) (q : ℕ) : Fintype (Index g q) := by
  unfold Index
  infer_instance

/-- Enumerate one fiber and retain one interval of at most `q` ranks. -/
def block (g : C → P) (q : ℕ) (j : Index g q) : Finset C :=
  (univ.filter (fun c : {c // g c = j.1} =>
    ((Fintype.equivFin {c // g c = j.1}) c).val / q = j.2.val)).map
      ⟨Subtype.val, Subtype.val_injective⟩

omit [Fintype P] in
lemma block_profile (g : C → P) (q : ℕ) (j : Index g q) {c : C}
    (hc : c ∈ block g q j) : g c = j.1 := by
  obtain ⟨d, _, rfl⟩ := mem_map.mp hc
  exact d.property

omit [Fintype P] in
lemma block_size (g : C → P) (q : ℕ) (hq : 0 < q) (j : Index g q) :
    (block g q j).card ≤ q := by
  unfold block
  rw [card_map]
  let rank := Fintype.equivFin {c // g c = j.1}
  apply le_trans (card_le_card_of_injOn
    (s := univ.filter (fun c : {c // g c = j.1} => (rank c).val / q = j.2.val))
    (t := range q) (fun c => (rank c).val % q) ?_ ?_) (by simp)
  · intro c _
    exact mem_range.mpr (Nat.mod_lt _ hq)
  · intro c hc d hd h
    apply rank.injective
    apply Fin.ext
    have hc' := (mem_filter.mp hc).2
    have hd' := (mem_filter.mp hd).2
    dsimp only at h
    have hec := Nat.mod_add_div (rank c).val q
    have hed := Nat.mod_add_div (rank d).val q
    rw [hc', h] at hec
    rw [hd'] at hed
    omega

omit [Fintype P] in
lemma block_cover (g : C → P) (q : ℕ) (c : C) :
    ∃ j : Index g q, c ∈ block g q j := by
  let d : {a // g a = g c} := ⟨c,rfl⟩
  let rank := Fintype.equivFin {a // g a = g c}
  let k : Fin (Fintype.card {a // g a = g c} / q + 1) :=
    ⟨(rank d).val / q, Nat.lt_succ_of_le (Nat.div_le_div_right (rank d).isLt.le)⟩
  refine ⟨⟨g c,k⟩, mem_map.mpr ⟨d, ?_, rfl⟩⟩
  exact mem_filter.mpr ⟨mem_univ _, rfl⟩

/-- The total chunk budget, rather than the largest fiber, controls the cover. -/
theorem cardinality_budget (g : C → P) (q : ℕ) :
    q * Fintype.card (Index g q) ≤ Fintype.card C + q * Fintype.card P := by
  have hf : (∑ p : P, Fintype.card {c // g c = p}) = Fintype.card C := by
    simpa only [Fintype.card_sigma] using Fintype.card_congr (Equiv.sigmaFiberEquiv g)
  change q * Fintype.card (Σ p : P, Fin (Fintype.card {c // g c = p} / q + 1)) ≤ _
  simp only [Fintype.card_sigma, Fintype.card_fin, mul_sum]
  calc
    _ ≤ ∑ p : P, (Fintype.card {c // g c = p} + q) := by
      apply sum_le_sum
      intro p _
      have h := Nat.mul_div_le (Fintype.card {c // g c = p}) q
      nlinarith
    _ = _ := by rw [sum_add_distrib, hf]; simp [mul_comm]

end Erdos714ProfileChunks

namespace Erdos714ProfileThinning

variable {C X T A P : Type*}
  [Fintype C] [Fintype X] [Fintype T] [Fintype A] [Fintype P]

/-- A code with a separate profile for each coordinate block `x`. -/
def code (g : X → C → P) (eval : X → P → T → A) (c : C) (i : X × T) : A :=
  eval i.1 (g i.1 c) i.2

/-- The exact fourth-power bound from the profile-dependent chunk cover. -/
theorem fourth_power_bound (g : X → C → P) (eval : X → P → T → A)
    (H : SimpleGraph (C ⊕ ((X × T) × A)))
    (hH : H ≤ Erdos714Coding.graph (code g eval))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (q : ℕ) (hq : 0 < q) (hT : Fintype.card T ≤ q) :
    H.edgeFinset.card ^ 4 ≤
      10368 * (∑ x : X, Fintype.card (Erdos714ProfileChunks.Index (g x) q))^4 * q^7 := by
  let J := Σ x : X, Erdos714ProfileChunks.Index (g x) q
  let L (j : J) : Finset (C ⊕ ((X × T) × A)) :=
    (Erdos714ProfileChunks.block (g j.1) q j.2).map Function.Embedding.inl
  let R (j : J) : Finset (C ⊕ ((X × T) × A)) :=
    univ.map ⟨fun t : T => Sum.inr ((j.1,t),eval j.1 j.2.1 t), by
      intro t u h
      exact congrArg (fun p : (X × T) × A => p.1.2) (Sum.inr.inj h)⟩
  have hsize (j : J) : (L j ∪ R j).card ≤ 2*q := by
    have hl : (L j).card ≤ q := by
      simpa only [L, card_map] using Erdos714ProfileChunks.block_size (g j.1) q hq j.2
    have hr : (R j).card ≤ q := by simpa only [R, card_map, card_univ] using hT
    have h := card_union_le (L j) (R j)
    omega
  have hforward (c : C) (i : X × T) (a : A)
      (h : (Erdos714Coding.graph (code g eval)).Adj (.inl c) (.inr (i,a))) :
      ∃ j : J, Sum.inl c ∈ L j ∪ R j ∧ Sum.inr (i,a) ∈ L j ∪ R j := by
    have he : eval i.1 (g i.1 c) i.2 = a := by
      simpa only [Erdos714Coding.graph, Erdos714Packing.incidence,
        Erdos714Coding.mem_symbols, code] using h
    obtain ⟨k,hk⟩ := Erdos714ProfileChunks.block_cover (g i.1) q c
    have hp := Erdos714ProfileChunks.block_profile (g i.1) q k hk
    refine ⟨⟨i.1,k⟩, mem_union_left _ (mem_map.mpr ⟨c,hk,rfl⟩), ?_⟩
    apply mem_union_right
    apply mem_map.mpr
    refine ⟨i.2,mem_univ _,?_⟩
    change Sum.inr ((i.1,i.2),eval i.1 k.1 i.2) = Sum.inr (i,a)
    rw [← hp, he]
  have hcover : ∀ v w, H.Adj v w → ∃ j : J, v ∈ L j ∪ R j ∧ w ∈ L j ∪ R j := by
    intro v w hvw
    have h := hH hvw
    cases v with
    | inl c =>
      cases w with
      | inl d => exact False.elim h
      | inr y => exact hforward c y.1 y.2 h
    | inr y =>
      cases w with
      | inr z => exact False.elim h
      | inl c =>
        obtain ⟨j,hc,hy⟩ := hforward c y.1 y.2 h.symm
        exact ⟨j,hy,hc⟩
  have hb := Erdos714BlockThinning.fourth_power_of_block_cover H hfree
    (fun j : J => L j ∪ R j) q hsize hcover
  simpa only [J, Fintype.card_sigma] using hb

/-- At the balanced fourth-case scale, every free edge thinning loses a power
of q: the fourth power of its edge count is O(q^27), not Omega(q^28). -/
theorem critical_scale_bound (g : X → C → P) (eval : X → P → T → A)
    (H : SimpleGraph (C ⊕ ((X × T) × A)))
    (hH : H ≤ Erdos714Coding.graph (code g eval))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (q : ℕ) (hq : 0 < q) (hT : Fintype.card T ≤ q)
    (hX : Fintype.card X ≤ q^2) (hC : Fintype.card C ≤ q^4)
    (hP : Fintype.card P ≤ q^3) :
    H.edgeFinset.card ^ 4 ≤ 165888 * q^27 := by
  have hi (x : X) : Fintype.card (Erdos714ProfileChunks.Index (g x) q) ≤ 2*q^3 := by
    have h := Erdos714ProfileChunks.cardinality_budget (g x) q
    have h' : q * Fintype.card (Erdos714ProfileChunks.Index (g x) q) ≤ q*(2*q^3) := by
      calc
        _ ≤ Fintype.card C + q * Fintype.card P := h
        _ ≤ q^4 + q*q^3 := Nat.add_le_add hC (Nat.mul_le_mul_left q hP)
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left h' hq
  have hs : (∑ x : X, Fintype.card (Erdos714ProfileChunks.Index (g x) q)) ≤ 2*q^5 := by
    calc
      _ ≤ ∑ _x : X, 2*q^3 := sum_le_sum (fun x _ => hi x)
      _ = Fintype.card X * (2*q^3) := by simp
      _ ≤ q^2*(2*q^3) := Nat.mul_le_mul_right _ hX
      _ = _ := by ring
  calc
    _ ≤ 10368 * (∑ x : X, Fintype.card (Erdos714ProfileChunks.Index (g x) q))^4 * q^7 :=
      fourth_power_bound g eval H hH hfree q hq hT
    _ ≤ 10368 * (2*q^5)^4 * q^7 := by gcongr
    _ = 165888 * q^27 := by ring

/-- A fixed critical-scale edge constant is possible only at bounded q. -/
theorem critical_size_budget (g : X → C → P) (eval : X → P → T → A)
    (H : SimpleGraph (C ⊕ ((X × T) × A)))
    (hH : H ≤ Erdos714Coding.graph (code g eval))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (q K : ℕ) (hq : 0 < q) (hT : Fintype.card T ≤ q)
    (hX : Fintype.card X ≤ q^2) (hC : Fintype.card C ≤ q^4)
    (hP : Fintype.card P ≤ q^3) (hdense : q^7 ≤ K*H.edgeFinset.card) :
    q ≤ 165888*K^4 := by
  have he := critical_scale_bound g eval H hH hfree q hq hT hX hC hP
  have h : q^27*q ≤ q^27*(165888*K^4) := by
    calc
      q^27*q = (q^7)^4 := by ring
      _ ≤ (K*H.edgeFinset.card)^4 := Nat.pow_le_pow_left hdense 4
      _ = K^4*H.edgeFinset.card^4 := mul_pow _ _ _
      _ ≤ K^4*(165888*q^27) := Nat.mul_le_mul_left _ he
      _ = q^27*(165888*K^4) := by ring
  exact Nat.le_of_mul_le_mul_left h (pow_pos hq 27)

end Erdos714ProfileThinning

#print axioms Erdos714ProfileChunks.block_size
#print axioms Erdos714ProfileChunks.cardinality_budget
#print axioms Erdos714ProfileThinning.fourth_power_bound
#print axioms Erdos714ProfileThinning.critical_scale_bound
#print axioms Erdos714ProfileThinning.critical_size_budget
