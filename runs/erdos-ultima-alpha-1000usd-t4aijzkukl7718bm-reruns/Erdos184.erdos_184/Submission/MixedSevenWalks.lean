import Submission.MixedCriticalNonforest
import Submission.MixedSevenData
/-! Walk realization of the finite packing certificate. -/
open SimpleGraph
namespace Erdos184.MixedSevenWalks
open MixedCriticalNonforest MixedSevenFinite
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def edge : E → Sym2 V := ![s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(0,6),s(1,2),s(1,3),s(1,4),s(1,5),s(1,6),s(2,3),s(2,4),s(2,5),s(2,6)]
lemma edge_injective : Function.Injective edge := by decide
lemma edge_mem_G : ∀ e, edge e ∈ G.edgeSet := by decide
lemma edge_surjective : ∀ u v, G.Adj u v → ∃ e, edge e = s(u,v) := by decide

def w0 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 0) <|
  .nil
lemma w0_cycle : w0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w0],by decide⟩

def w1 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 3) <|
  .cons (by decide : G.Adj 3 0) <|
  .nil
lemma w1_cycle : w1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w1],by decide⟩

def w2 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 1) <|
  .cons (by decide : G.Adj 1 3) <|
  .cons (by decide : G.Adj 3 0) <|
  .nil
lemma w2_cycle : w2.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w2],by decide⟩

def w3 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 4) <|
  .cons (by decide : G.Adj 4 0) <|
  .nil
lemma w3_cycle : w3.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w3],by decide⟩

def w4 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 1) <|
  .cons (by decide : G.Adj 1 4) <|
  .cons (by decide : G.Adj 4 0) <|
  .nil
lemma w4_cycle : w4.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w4],by decide⟩

def w5 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 1) <|
  .cons (by decide : G.Adj 1 4) <|
  .cons (by decide : G.Adj 4 0) <|
  .nil
lemma w5_cycle : w5.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w5],by decide⟩

def w6 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w6_cycle : w6.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w6],by decide⟩

def w7 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w7_cycle : w7.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w7],by decide⟩

def w8 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w8_cycle : w8.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w8],by decide⟩

def w9 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 4) <|
  .cons (by decide : G.Adj 4 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w9_cycle : w9.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w9],by decide⟩

def w10 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w10_cycle : w10.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w10],by decide⟩

def w11 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w11_cycle : w11.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w11],by decide⟩

def w12 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w12_cycle : w12.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w12],by decide⟩

def w13 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 4) <|
  .cons (by decide : G.Adj 4 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w13_cycle : w13.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w13],by decide⟩

def w14 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 5) <|
  .cons (by decide : G.Adj 5 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w14_cycle : w14.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w14],by decide⟩

def w15 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 0) <|
  .nil
lemma w15_cycle : w15.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w15],by decide⟩

def w16 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 0) <|
  .nil
lemma w16_cycle : w16.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w16],by decide⟩

def w17 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 0) <|
  .nil
lemma w17_cycle : w17.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w17],by decide⟩

def w18 : G.Walk 1 1 :=
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 1) <|
  .nil
lemma w18_cycle : w18.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w18],by decide⟩

def w19 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 1) <|
  .cons (by decide : G.Adj 1 4) <|
  .cons (by decide : G.Adj 4 0) <|
  .nil
lemma w19_cycle : w19.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w19],by decide⟩

def w20 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 1) <|
  .cons (by decide : G.Adj 1 4) <|
  .cons (by decide : G.Adj 4 0) <|
  .nil
lemma w20_cycle : w20.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w20],by decide⟩

def w21 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w21_cycle : w21.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w21],by decide⟩

def w22 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w22_cycle : w22.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w22],by decide⟩

def w23 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w23_cycle : w23.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w23],by decide⟩

def w24 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w24_cycle : w24.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w24],by decide⟩

def w25 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 4) <|
  .cons (by decide : G.Adj 4 0) <|
  .nil
lemma w25_cycle : w25.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w25],by decide⟩

def w26 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 4) <|
  .cons (by decide : G.Adj 4 0) <|
  .nil
lemma w26_cycle : w26.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w26],by decide⟩

def w27 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 1) <|
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 4) <|
  .cons (by decide : G.Adj 4 0) <|
  .nil
lemma w27_cycle : w27.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w27],by decide⟩

def w28 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 0) <|
  .nil
lemma w28_cycle : w28.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w28],by decide⟩

def w29 : G.Walk 1 1 :=
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 4) <|
  .cons (by decide : G.Adj 4 1) <|
  .nil
lemma w29_cycle : w29.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w29],by decide⟩

def w30 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 4) <|
  .cons (by decide : G.Adj 4 1) <|
  .cons (by decide : G.Adj 1 3) <|
  .cons (by decide : G.Adj 3 0) <|
  .nil
lemma w30_cycle : w30.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w30],by decide⟩

def w31 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w31_cycle : w31.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w31],by decide⟩

def w32 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 4) <|
  .cons (by decide : G.Adj 4 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w32_cycle : w32.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w32],by decide⟩

def w33 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w33_cycle : w33.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w33],by decide⟩

def w34 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 4) <|
  .cons (by decide : G.Adj 4 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w34_cycle : w34.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w34],by decide⟩

def w35 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 4) <|
  .cons (by decide : G.Adj 4 0) <|
  .nil
lemma w35_cycle : w35.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w35],by decide⟩

def w36 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 4) <|
  .cons (by decide : G.Adj 4 0) <|
  .nil
lemma w36_cycle : w36.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w36],by decide⟩

def w37 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 0) <|
  .nil
lemma w37_cycle : w37.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w37],by decide⟩

def w38 : G.Walk 1 1 :=
  .cons (by decide : G.Adj 1 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 4) <|
  .cons (by decide : G.Adj 4 1) <|
  .nil
lemma w38_cycle : w38.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w38],by decide⟩

def w39 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w39_cycle : w39.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w39],by decide⟩

def w40 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 4) <|
  .cons (by decide : G.Adj 4 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w40_cycle : w40.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w40],by decide⟩

def w41 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w41_cycle : w41.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w41],by decide⟩

def w42 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 4) <|
  .cons (by decide : G.Adj 4 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w42_cycle : w42.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w42],by decide⟩

def w43 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w43_cycle : w43.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w43],by decide⟩

def w44 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w44_cycle : w44.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w44],by decide⟩

def w45 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 1) <|
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w45_cycle : w45.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w45],by decide⟩

def w46 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 4) <|
  .cons (by decide : G.Adj 4 1) <|
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w46_cycle : w46.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w46],by decide⟩

def w47 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 2) <|
  .cons (by decide : G.Adj 2 0) <|
  .nil
lemma w47_cycle : w47.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w47],by decide⟩

def w48 : G.Walk 1 1 :=
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 5) <|
  .cons (by decide : G.Adj 5 1) <|
  .nil
lemma w48_cycle : w48.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w48],by decide⟩

def w49 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 5) <|
  .cons (by decide : G.Adj 5 1) <|
  .cons (by decide : G.Adj 1 3) <|
  .cons (by decide : G.Adj 3 0) <|
  .nil
lemma w49_cycle : w49.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w49],by decide⟩

def w50 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 5) <|
  .cons (by decide : G.Adj 5 1) <|
  .cons (by decide : G.Adj 1 4) <|
  .cons (by decide : G.Adj 4 0) <|
  .nil
lemma w50_cycle : w50.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w50],by decide⟩

def w51 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 5) <|
  .cons (by decide : G.Adj 5 2) <|
  .cons (by decide : G.Adj 2 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w51_cycle : w51.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w51],by decide⟩

def w52 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 5) <|
  .cons (by decide : G.Adj 5 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w52_cycle : w52.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w52],by decide⟩

def w53 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w53_cycle : w53.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w53],by decide⟩

def w54 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w54_cycle : w54.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w54],by decide⟩

def w55 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 4) <|
  .cons (by decide : G.Adj 4 1) <|
  .cons (by decide : G.Adj 1 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w55_cycle : w55.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w55],by decide⟩

def w56 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 0) <|
  .nil
lemma w56_cycle : w56.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w56],by decide⟩

def w57 : G.Walk 1 1 :=
  .cons (by decide : G.Adj 1 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 5) <|
  .cons (by decide : G.Adj 5 1) <|
  .nil
lemma w57_cycle : w57.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w57],by decide⟩

def w58 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 5) <|
  .cons (by decide : G.Adj 5 1) <|
  .cons (by decide : G.Adj 1 4) <|
  .cons (by decide : G.Adj 4 0) <|
  .nil
lemma w58_cycle : w58.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w58],by decide⟩

def w59 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 5) <|
  .cons (by decide : G.Adj 5 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w59_cycle : w59.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w59],by decide⟩

def w60 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 5) <|
  .cons (by decide : G.Adj 5 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w60_cycle : w60.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w60],by decide⟩

def w61 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w61_cycle : w61.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w61],by decide⟩

def w62 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w62_cycle : w62.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w62],by decide⟩

def w63 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 1) <|
  .cons (by decide : G.Adj 1 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w63_cycle : w63.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w63],by decide⟩

def w64 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 2) <|
  .cons (by decide : G.Adj 2 4) <|
  .cons (by decide : G.Adj 4 0) <|
  .nil
lemma w64_cycle : w64.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w64],by decide⟩

def w65 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 2) <|
  .cons (by decide : G.Adj 2 4) <|
  .cons (by decide : G.Adj 4 0) <|
  .nil
lemma w65_cycle : w65.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w65],by decide⟩

def w66 : G.Walk 1 1 :=
  .cons (by decide : G.Adj 1 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 5) <|
  .cons (by decide : G.Adj 5 1) <|
  .nil
lemma w66_cycle : w66.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w66],by decide⟩

def w67 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 5) <|
  .cons (by decide : G.Adj 5 2) <|
  .cons (by decide : G.Adj 2 4) <|
  .cons (by decide : G.Adj 4 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w67_cycle : w67.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w67],by decide⟩

def w68 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 5) <|
  .cons (by decide : G.Adj 5 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w68_cycle : w68.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w68],by decide⟩

def w69 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w69_cycle : w69.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w69],by decide⟩

def w70 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w70_cycle : w70.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w70],by decide⟩

def w71 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 1) <|
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w71_cycle : w71.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w71],by decide⟩

def w72 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 4) <|
  .cons (by decide : G.Adj 4 1) <|
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w72_cycle : w72.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w72],by decide⟩

def w73 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 5) <|
  .cons (by decide : G.Adj 5 1) <|
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w73_cycle : w73.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w73],by decide⟩

def w74 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 2) <|
  .cons (by decide : G.Adj 2 0) <|
  .nil
lemma w74_cycle : w74.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w74],by decide⟩

def w75 : G.Walk 1 1 :=
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 1) <|
  .nil
lemma w75_cycle : w75.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w75],by decide⟩

def w76 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 1) <|
  .cons (by decide : G.Adj 1 3) <|
  .cons (by decide : G.Adj 3 0) <|
  .nil
lemma w76_cycle : w76.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w76],by decide⟩

def w77 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 1) <|
  .cons (by decide : G.Adj 1 4) <|
  .cons (by decide : G.Adj 4 0) <|
  .nil
lemma w77_cycle : w77.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w77],by decide⟩

def w78 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w78_cycle : w78.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w78],by decide⟩

def w79 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w79_cycle : w79.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w79],by decide⟩

def w80 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w80_cycle : w80.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w80],by decide⟩

def w81 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 4) <|
  .cons (by decide : G.Adj 4 1) <|
  .cons (by decide : G.Adj 1 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w81_cycle : w81.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w81],by decide⟩

def w82 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 5) <|
  .cons (by decide : G.Adj 5 1) <|
  .cons (by decide : G.Adj 1 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w82_cycle : w82.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w82],by decide⟩

def w83 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 0) <|
  .nil
lemma w83_cycle : w83.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w83],by decide⟩

def w84 : G.Walk 1 1 :=
  .cons (by decide : G.Adj 1 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 1) <|
  .nil
lemma w84_cycle : w84.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w84],by decide⟩

def w85 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 1) <|
  .cons (by decide : G.Adj 1 4) <|
  .cons (by decide : G.Adj 4 0) <|
  .nil
lemma w85_cycle : w85.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w85],by decide⟩

def w86 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w86_cycle : w86.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w86],by decide⟩

def w87 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w87_cycle : w87.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w87],by decide⟩

def w88 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w88_cycle : w88.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w88],by decide⟩

def w89 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 1) <|
  .cons (by decide : G.Adj 1 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w89_cycle : w89.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w89],by decide⟩

def w90 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 5) <|
  .cons (by decide : G.Adj 5 1) <|
  .cons (by decide : G.Adj 1 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w90_cycle : w90.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w90],by decide⟩

def w91 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 2) <|
  .cons (by decide : G.Adj 2 4) <|
  .cons (by decide : G.Adj 4 0) <|
  .nil
lemma w91_cycle : w91.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w91],by decide⟩

def w92 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 2) <|
  .cons (by decide : G.Adj 2 4) <|
  .cons (by decide : G.Adj 4 0) <|
  .nil
lemma w92_cycle : w92.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w92],by decide⟩

def w93 : G.Walk 1 1 :=
  .cons (by decide : G.Adj 1 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 1) <|
  .nil
lemma w93_cycle : w93.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w93],by decide⟩

def w94 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w94_cycle : w94.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w94],by decide⟩

def w95 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 5) <|
  .cons (by decide : G.Adj 5 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w95_cycle : w95.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w95],by decide⟩

def w96 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w96_cycle : w96.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w96],by decide⟩

def w97 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w97_cycle : w97.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w97],by decide⟩

def w98 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 4) <|
  .cons (by decide : G.Adj 4 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 0) <|
  .nil
lemma w98_cycle : w98.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w98],by decide⟩

def w99 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 2) <|
  .cons (by decide : G.Adj 2 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w99_cycle : w99.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w99],by decide⟩

def w100 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 3) <|
  .cons (by decide : G.Adj 3 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 2) <|
  .cons (by decide : G.Adj 2 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w100_cycle : w100.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w100],by decide⟩

def w101 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 4) <|
  .cons (by decide : G.Adj 4 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 2) <|
  .cons (by decide : G.Adj 2 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma w101_cycle : w101.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w101],by decide⟩

def w102 : G.Walk 1 1 :=
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 2) <|
  .cons (by decide : G.Adj 2 6) <|
  .cons (by decide : G.Adj 6 1) <|
  .nil
lemma w102_cycle : w102.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w102],by decide⟩

def walk : I → Σ v, G.Walk v v := ![
  ⟨0,w0⟩,
  ⟨0,w1⟩,
  ⟨0,w2⟩,
  ⟨0,w3⟩,
  ⟨0,w4⟩,
  ⟨0,w5⟩,
  ⟨0,w6⟩,
  ⟨0,w7⟩,
  ⟨0,w8⟩,
  ⟨0,w9⟩,
  ⟨0,w10⟩,
  ⟨0,w11⟩,
  ⟨0,w12⟩,
  ⟨0,w13⟩,
  ⟨0,w14⟩,
  ⟨0,w15⟩,
  ⟨0,w16⟩,
  ⟨0,w17⟩,
  ⟨1,w18⟩,
  ⟨0,w19⟩,
  ⟨0,w20⟩,
  ⟨0,w21⟩,
  ⟨0,w22⟩,
  ⟨0,w23⟩,
  ⟨0,w24⟩,
  ⟨0,w25⟩,
  ⟨0,w26⟩,
  ⟨0,w27⟩,
  ⟨0,w28⟩,
  ⟨1,w29⟩,
  ⟨0,w30⟩,
  ⟨0,w31⟩,
  ⟨0,w32⟩,
  ⟨0,w33⟩,
  ⟨0,w34⟩,
  ⟨0,w35⟩,
  ⟨0,w36⟩,
  ⟨0,w37⟩,
  ⟨1,w38⟩,
  ⟨0,w39⟩,
  ⟨0,w40⟩,
  ⟨0,w41⟩,
  ⟨0,w42⟩,
  ⟨0,w43⟩,
  ⟨0,w44⟩,
  ⟨0,w45⟩,
  ⟨0,w46⟩,
  ⟨0,w47⟩,
  ⟨1,w48⟩,
  ⟨0,w49⟩,
  ⟨0,w50⟩,
  ⟨0,w51⟩,
  ⟨0,w52⟩,
  ⟨0,w53⟩,
  ⟨0,w54⟩,
  ⟨0,w55⟩,
  ⟨0,w56⟩,
  ⟨1,w57⟩,
  ⟨0,w58⟩,
  ⟨0,w59⟩,
  ⟨0,w60⟩,
  ⟨0,w61⟩,
  ⟨0,w62⟩,
  ⟨0,w63⟩,
  ⟨0,w64⟩,
  ⟨0,w65⟩,
  ⟨1,w66⟩,
  ⟨0,w67⟩,
  ⟨0,w68⟩,
  ⟨0,w69⟩,
  ⟨0,w70⟩,
  ⟨0,w71⟩,
  ⟨0,w72⟩,
  ⟨0,w73⟩,
  ⟨0,w74⟩,
  ⟨1,w75⟩,
  ⟨0,w76⟩,
  ⟨0,w77⟩,
  ⟨0,w78⟩,
  ⟨0,w79⟩,
  ⟨0,w80⟩,
  ⟨0,w81⟩,
  ⟨0,w82⟩,
  ⟨0,w83⟩,
  ⟨1,w84⟩,
  ⟨0,w85⟩,
  ⟨0,w86⟩,
  ⟨0,w87⟩,
  ⟨0,w88⟩,
  ⟨0,w89⟩,
  ⟨0,w90⟩,
  ⟨0,w91⟩,
  ⟨0,w92⟩,
  ⟨1,w93⟩,
  ⟨0,w94⟩,
  ⟨0,w95⟩,
  ⟨0,w96⟩,
  ⟨0,w97⟩,
  ⟨0,w98⟩,
  ⟨0,w99⟩,
  ⟨0,w100⟩,
  ⟨0,w101⟩,
  ⟨1,w102⟩]

lemma walk_cycle (i : I) : (walk i).2.IsCycle := by
  fin_cases i
  · exact w0_cycle
  · exact w1_cycle
  · exact w2_cycle
  · exact w3_cycle
  · exact w4_cycle
  · exact w5_cycle
  · exact w6_cycle
  · exact w7_cycle
  · exact w8_cycle
  · exact w9_cycle
  · exact w10_cycle
  · exact w11_cycle
  · exact w12_cycle
  · exact w13_cycle
  · exact w14_cycle
  · exact w15_cycle
  · exact w16_cycle
  · exact w17_cycle
  · exact w18_cycle
  · exact w19_cycle
  · exact w20_cycle
  · exact w21_cycle
  · exact w22_cycle
  · exact w23_cycle
  · exact w24_cycle
  · exact w25_cycle
  · exact w26_cycle
  · exact w27_cycle
  · exact w28_cycle
  · exact w29_cycle
  · exact w30_cycle
  · exact w31_cycle
  · exact w32_cycle
  · exact w33_cycle
  · exact w34_cycle
  · exact w35_cycle
  · exact w36_cycle
  · exact w37_cycle
  · exact w38_cycle
  · exact w39_cycle
  · exact w40_cycle
  · exact w41_cycle
  · exact w42_cycle
  · exact w43_cycle
  · exact w44_cycle
  · exact w45_cycle
  · exact w46_cycle
  · exact w47_cycle
  · exact w48_cycle
  · exact w49_cycle
  · exact w50_cycle
  · exact w51_cycle
  · exact w52_cycle
  · exact w53_cycle
  · exact w54_cycle
  · exact w55_cycle
  · exact w56_cycle
  · exact w57_cycle
  · exact w58_cycle
  · exact w59_cycle
  · exact w60_cycle
  · exact w61_cycle
  · exact w62_cycle
  · exact w63_cycle
  · exact w64_cycle
  · exact w65_cycle
  · exact w66_cycle
  · exact w67_cycle
  · exact w68_cycle
  · exact w69_cycle
  · exact w70_cycle
  · exact w71_cycle
  · exact w72_cycle
  · exact w73_cycle
  · exact w74_cycle
  · exact w75_cycle
  · exact w76_cycle
  · exact w77_cycle
  · exact w78_cycle
  · exact w79_cycle
  · exact w80_cycle
  · exact w81_cycle
  · exact w82_cycle
  · exact w83_cycle
  · exact w84_cycle
  · exact w85_cycle
  · exact w86_cycle
  · exact w87_cycle
  · exact w88_cycle
  · exact w89_cycle
  · exact w90_cycle
  · exact w91_cycle
  · exact w92_cycle
  · exact w93_cycle
  · exact w94_cycle
  · exact w95_cycle
  · exact w96_cycle
  · exact w97_cycle
  · exact w98_cycle
  · exact w99_cycle
  · exact w100_cycle
  · exact w101_cycle
  · exact w102_cycle

lemma walk_edges : ∀ i e, edge e ∈ (walk i).2.edges ↔ e ∈ cyc i := by decide

def piece (i : I) : G.Subgraph := (walk i).2.toSubgraph

open scoped Classical
lemma piece_cycle (i : I) : (piece i).coe.Connected ∧ (piece i).coe.IsRegularOfDegree 2 := by
  have hh := cycle_subgraph_regular G (walk_cycle i)
  refine ⟨hh.1,?_⟩
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hh.2 v

lemma piece_edgeSet (i : I) : (piece i).edgeSet = ((cyc i).image edge : Set (Sym2 V)) := by
  ext e
  constructor
  · intro he
    have heG := (piece i).edgeSet_subset he
    induction e using Sym2.ind with
    | h u v =>
      obtain ⟨a,ha⟩ := edge_surjective u v heG
      refine Finset.mem_image.mpr ⟨a,?_,ha⟩
      apply (walk_edges i a).mp
      rw [ha]
      exact (walk i).2.mem_edges_toSubgraph.mp he
  · intro he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    exact (walk i).2.mem_edges_toSubgraph.mpr ((walk_edges i a).mpr ha)

end Erdos184.MixedSevenWalks
