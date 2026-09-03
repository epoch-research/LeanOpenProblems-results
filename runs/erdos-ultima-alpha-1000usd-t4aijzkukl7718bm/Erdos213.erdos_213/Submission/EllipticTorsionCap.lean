import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! A finite incidence obstruction for one torsion-based construction.
It is not a bound on arbitrary integral-distance configurations. -/
set_option maxHeartbeats 5000000
set_option synthInstance.maxSize 100000
set_option maxRecDepth 100000
set_option Elab.async false

namespace Erdos213.EllipticTorsionCap

abbrev G := ZMod 2 × ZMod 8

def NoThreeSum (S : Finset G) : Prop :=
  ∀ T ∈ S.powersetCard 3, (∑ a ∈ T, a) ≠ 0

def OppositePairs (S : Finset G) : Prop :=
  ∃ p ∈ S, ∃ q ∈ S,
    -p ∈ S ∧ -q ∈ S ∧ p ≠ -p ∧ q ≠ -q ∧ p ≠ q ∧ p ≠ -q

private def lines : Finset (Finset G) :=
  {{(0,1),(0,2),(0,5)},
   {(0,1),(0,3),(0,4)},
   {(0,1),(1,0),(1,7)},
   {(0,1),(1,1),(1,6)},
   {(0,1),(1,2),(1,5)},
   {(0,1),(1,3),(1,4)},
   {(0,2),(1,0),(1,6)},
   {(0,2),(1,1),(1,5)},
   {(0,2),(1,2),(1,4)},
   {(0,3),(0,6),(0,7)},
   {(0,3),(1,0),(1,5)},
   {(0,3),(1,1),(1,4)},
   {(0,3),(1,2),(1,3)},
   {(0,3),(1,6),(1,7)},
   {(0,4),(0,5),(0,7)},
   {(0,4),(1,0),(1,4)},
   {(0,4),(1,1),(1,3)},
   {(0,4),(1,5),(1,7)},
   {(0,5),(1,0),(1,3)},
   {(0,5),(1,1),(1,2)},
   {(0,5),(1,4),(1,7)},
   {(0,5),(1,5),(1,6)},
   {(0,6),(1,0),(1,2)},
   {(0,6),(1,3),(1,7)},
   {(0,6),(1,4),(1,6)},
   {(0,7),(1,0),(1,1)},
   {(0,7),(1,2),(1,7)},
   {(0,7),(1,3),(1,6)},
   {(0,7),(1,4),(1,5)}}

private def quartets : Finset (Finset G) :=
  {{(0,1),(0,7),(0,2),(0,6)},
   {(0,1),(0,7),(0,3),(0,5)},
   {(0,1),(0,7),(1,1),(1,7)},
   {(0,1),(0,7),(1,2),(1,6)},
   {(0,1),(0,7),(1,3),(1,5)},
   {(0,2),(0,6),(0,3),(0,5)},
   {(0,2),(0,6),(1,1),(1,7)},
   {(0,2),(0,6),(1,2),(1,6)},
   {(0,2),(0,6),(1,3),(1,5)},
   {(0,3),(0,5),(1,1),(1,7)},
   {(0,3),(0,5),(1,2),(1,6)},
   {(0,3),(0,5),(1,3),(1,5)},
   {(1,1),(1,7),(1,2),(1,6)},
   {(1,1),(1,7),(1,3),(1,5)},
   {(1,2),(1,6),(1,3),(1,5)}}

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
private lemma lines_correct : ∀ T ∈ lines, T.card = 3 ∧ (∑ a ∈ T, a) = 0 := by
  decide +kernel

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype in
private lemma quartets_correct : ∀ T ∈ quartets, OppositePairs T := by
  unfold OppositePairs
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private lemma bool_certificate (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : Bool) :
    (if b0 then (1 : ℕ) else 0) + (if b1 then (1 : ℕ) else 0) + (if b2 then (1 : ℕ) else 0) + (if b3 then (1 : ℕ) else 0) + (if b4 then (1 : ℕ) else 0) + (if b5 then (1 : ℕ) else 0) + (if b6 then (1 : ℕ) else 0) + (if b7 then (1 : ℕ) else 0) + (if b8 then (1 : ℕ) else 0) + (if b9 then (1 : ℕ) else 0) + (if b10 then (1 : ℕ) else 0) + (if b11 then (1 : ℕ) else 0) + (if b12 then (1 : ℕ) else 0) + (if b13 then (1 : ℕ) else 0) + (if b14 then (1 : ℕ) else 0) = 8 →
      (b0 = true ∧ b1 = true ∧ b4 = true) ∨
      (b0 = true ∧ b2 = true ∧ b3 = true) ∨
      (b0 = true ∧ b7 = true ∧ b14 = true) ∨
      (b0 = true ∧ b8 = true ∧ b13 = true) ∨
      (b0 = true ∧ b9 = true ∧ b12 = true) ∨
      (b0 = true ∧ b10 = true ∧ b11 = true) ∨
      (b1 = true ∧ b7 = true ∧ b13 = true) ∨
      (b1 = true ∧ b8 = true ∧ b12 = true) ∨
      (b1 = true ∧ b9 = true ∧ b11 = true) ∨
      (b2 = true ∧ b5 = true ∧ b6 = true) ∨
      (b2 = true ∧ b7 = true ∧ b12 = true) ∨
      (b2 = true ∧ b8 = true ∧ b11 = true) ∨
      (b2 = true ∧ b9 = true ∧ b10 = true) ∨
      (b2 = true ∧ b13 = true ∧ b14 = true) ∨
      (b3 = true ∧ b4 = true ∧ b6 = true) ∨
      (b3 = true ∧ b7 = true ∧ b11 = true) ∨
      (b3 = true ∧ b8 = true ∧ b10 = true) ∨
      (b3 = true ∧ b12 = true ∧ b14 = true) ∨
      (b4 = true ∧ b7 = true ∧ b10 = true) ∨
      (b4 = true ∧ b8 = true ∧ b9 = true) ∨
      (b4 = true ∧ b11 = true ∧ b14 = true) ∨
      (b4 = true ∧ b12 = true ∧ b13 = true) ∨
      (b5 = true ∧ b7 = true ∧ b9 = true) ∨
      (b5 = true ∧ b10 = true ∧ b14 = true) ∨
      (b5 = true ∧ b11 = true ∧ b13 = true) ∨
      (b6 = true ∧ b7 = true ∧ b8 = true) ∨
      (b6 = true ∧ b9 = true ∧ b14 = true) ∨
      (b6 = true ∧ b10 = true ∧ b13 = true) ∨
      (b6 = true ∧ b11 = true ∧ b12 = true) ∨
      (b0 = true ∧ b6 = true ∧ b1 = true ∧ b5 = true) ∨
      (b0 = true ∧ b6 = true ∧ b2 = true ∧ b4 = true) ∨
      (b0 = true ∧ b6 = true ∧ b8 = true ∧ b14 = true) ∨
      (b0 = true ∧ b6 = true ∧ b9 = true ∧ b13 = true) ∨
      (b0 = true ∧ b6 = true ∧ b10 = true ∧ b12 = true) ∨
      (b1 = true ∧ b5 = true ∧ b2 = true ∧ b4 = true) ∨
      (b1 = true ∧ b5 = true ∧ b8 = true ∧ b14 = true) ∨
      (b1 = true ∧ b5 = true ∧ b9 = true ∧ b13 = true) ∨
      (b1 = true ∧ b5 = true ∧ b10 = true ∧ b12 = true) ∨
      (b2 = true ∧ b4 = true ∧ b8 = true ∧ b14 = true) ∨
      (b2 = true ∧ b4 = true ∧ b9 = true ∧ b13 = true) ∨
      (b2 = true ∧ b4 = true ∧ b10 = true ∧ b12 = true) ∨
      (b8 = true ∧ b14 = true ∧ b9 = true ∧ b13 = true) ∨
      (b8 = true ∧ b14 = true ∧ b10 = true ∧ b12 = true) ∨
      (b9 = true ∧ b13 = true ∧ b10 = true ∧ b12 = true) := by
  revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  decide +kernel

private lemma finite_cover (S : Finset G) (hc : S.card = 8) (h0 : (0 : G) ∉ S) :
    ∃ T ∈ lines ∪ quartets, T ⊆ S := by
  have hs : (∑ i : G, if i ∈ S then (1 : ℕ) else 0) = 8 := by
    rw [Finset.sum_boole]
    simpa using hc
  rw [Fintype.sum_prod_type] at hs
  change (∑ a : Fin 2, ∑ b : Fin 8, if ((a,b) : G) ∈ S then (1 : ℕ) else 0) = 8 at hs
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hs
  have hz : ((0,0) : G) ∉ S := h0
  have hb := bool_certificate (decide (((0,1) : G) ∈ S)) (decide (((0,2) : G) ∈ S)) (decide (((0,3) : G) ∈ S)) (decide (((0,4) : G) ∈ S)) (decide (((0,5) : G) ∈ S)) (decide (((0,6) : G) ∈ S)) (decide (((0,7) : G) ∈ S)) (decide (((1,0) : G) ∈ S)) (decide (((1,1) : G) ∈ S)) (decide (((1,2) : G) ∈ S)) (decide (((1,3) : G) ∈ S)) (decide (((1,4) : G) ∈ S)) (decide (((1,5) : G) ∈ S)) (decide (((1,6) : G) ∈ S)) (decide (((1,7) : G) ∈ S))
  simp only [decide_eq_true_eq] at hb
  have hh := hb (by simpa only [hz,ite_false,zero_add,add_assoc] using hs)
  rcases hh with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43
  · refine ⟨{(0,1),(0,2),(0,5)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h0
  · refine ⟨{(0,1),(0,3),(0,4)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h1
  · refine ⟨{(0,1),(1,0),(1,7)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h2
  · refine ⟨{(0,1),(1,1),(1,6)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h3
  · refine ⟨{(0,1),(1,2),(1,5)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h4
  · refine ⟨{(0,1),(1,3),(1,4)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h5
  · refine ⟨{(0,2),(1,0),(1,6)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h6
  · refine ⟨{(0,2),(1,1),(1,5)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h7
  · refine ⟨{(0,2),(1,2),(1,4)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h8
  · refine ⟨{(0,3),(0,6),(0,7)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h9
  · refine ⟨{(0,3),(1,0),(1,5)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h10
  · refine ⟨{(0,3),(1,1),(1,4)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h11
  · refine ⟨{(0,3),(1,2),(1,3)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h12
  · refine ⟨{(0,3),(1,6),(1,7)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h13
  · refine ⟨{(0,4),(0,5),(0,7)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h14
  · refine ⟨{(0,4),(1,0),(1,4)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h15
  · refine ⟨{(0,4),(1,1),(1,3)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h16
  · refine ⟨{(0,4),(1,5),(1,7)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h17
  · refine ⟨{(0,5),(1,0),(1,3)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h18
  · refine ⟨{(0,5),(1,1),(1,2)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h19
  · refine ⟨{(0,5),(1,4),(1,7)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h20
  · refine ⟨{(0,5),(1,5),(1,6)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h21
  · refine ⟨{(0,6),(1,0),(1,2)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h22
  · refine ⟨{(0,6),(1,3),(1,7)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h23
  · refine ⟨{(0,6),(1,4),(1,6)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h24
  · refine ⟨{(0,7),(1,0),(1,1)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h25
  · refine ⟨{(0,7),(1,2),(1,7)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h26
  · refine ⟨{(0,7),(1,3),(1,6)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h27
  · refine ⟨{(0,7),(1,4),(1,5)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h28
  · refine ⟨{(0,1),(0,7),(0,2),(0,6)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h29
  · refine ⟨{(0,1),(0,7),(0,3),(0,5)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h30
  · refine ⟨{(0,1),(0,7),(1,1),(1,7)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h31
  · refine ⟨{(0,1),(0,7),(1,2),(1,6)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h32
  · refine ⟨{(0,1),(0,7),(1,3),(1,5)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h33
  · refine ⟨{(0,2),(0,6),(0,3),(0,5)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h34
  · refine ⟨{(0,2),(0,6),(1,1),(1,7)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h35
  · refine ⟨{(0,2),(0,6),(1,2),(1,6)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h36
  · refine ⟨{(0,2),(0,6),(1,3),(1,5)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h37
  · refine ⟨{(0,3),(0,5),(1,1),(1,7)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h38
  · refine ⟨{(0,3),(0,5),(1,2),(1,6)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h39
  · refine ⟨{(0,3),(0,5),(1,3),(1,5)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h40
  · refine ⟨{(1,1),(1,7),(1,2),(1,6)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h41
  · refine ⟨{(1,1),(1,7),(1,3),(1,5)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h42
  · refine ⟨{(1,2),(1,6),(1,3),(1,5)}, by decide, ?_⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using h43

private lemma finite_certificate :
    ∀ S ∈ (Finset.univ : Finset G).powersetCard 8,
      (0 : G) ∉ S → NoThreeSum S → OppositePairs S := by
  intro S hS h0 ht
  obtain ⟨T,hT,hTS⟩ := finite_cover S (Finset.mem_powersetCard.mp hS).2 h0
  rcases Finset.mem_union.mp hT with hT | hT
  · obtain ⟨hc,hz⟩ := lines_correct T hT
    exact False.elim (ht T (Finset.mem_powersetCard.mpr ⟨hTS,hc⟩) hz)
  · obtain ⟨a,ha,b,hb,hna,hnb,h⟩ := quartets_correct T hT
    exact ⟨a,hTS ha,b,hTS hb,hTS hna,hTS hnb,h⟩

lemma eight_has_opposite_pairs (S : Finset G) (hc : S.card = 8)
    (h0 : (0 : G) ∉ S) (ht : NoThreeSum S) : OppositePairs S :=
  finite_certificate S (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S,hc⟩) h0 ht

lemma noThreeSum_of_triples (S : Finset G)
    (h : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
      a ≠ b → a ≠ c → b ≠ c → a+b+c ≠ 0) : NoThreeSum S := by
  intro T hT
  obtain ⟨hTS,hcard⟩ := Finset.mem_powersetCard.mp hT
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp hcard
  have ha : a ∈ S := hTS (by simp)
  have hb : b ∈ S := hTS (by simp)
  have hc : c ∈ S := hTS (by simp)
  simpa [hab,hac,hbc,add_assoc] using h a ha b hb c hc hab hac hbc

#print axioms eight_has_opposite_pairs
#print axioms noThreeSum_of_triples
end Erdos213.EllipticTorsionCap
