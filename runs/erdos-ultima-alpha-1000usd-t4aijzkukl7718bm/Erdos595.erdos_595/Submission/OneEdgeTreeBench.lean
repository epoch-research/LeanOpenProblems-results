import Submission.ArcAdjoint

/-! A kernel-checked local obstruction for degree-three marked neighborhoods.
This is auxiliary work on a candidate family, not a settlement of Erdős 595.
The SAT certificate is reconstructed by Mathlib's propositional LRAT checker,
not by native_decide or bv_decide. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.unusedVariables false
open SimpleGraph Set
namespace Erdos595OneEdgeLocal
open Erdos595ArcAdjoint

def coords (i : Fin 60) : Fin 4 × Fin 4 × Fin 4 × Fin 4 :=
  match i.val with
  | 0 => (0,1,1,0)
  | 1 => (0,1,1,2)
  | 2 => (0,1,1,3)
  | 3 => (0,1,2,0)
  | 4 => (0,1,3,0)
  | 5 => (0,2,1,0)
  | 6 => (0,2,2,0)
  | 7 => (0,2,2,1)
  | 8 => (0,2,2,3)
  | 9 => (0,2,3,0)
  | 10 => (0,3,1,0)
  | 11 => (0,3,2,0)
  | 12 => (0,3,3,0)
  | 13 => (0,3,3,1)
  | 14 => (0,3,3,2)
  | 15 => (1,0,0,1)
  | 16 => (1,0,0,2)
  | 17 => (1,0,0,3)
  | 18 => (1,0,2,1)
  | 19 => (1,0,3,1)
  | 20 => (1,2,0,1)
  | 21 => (1,2,2,0)
  | 22 => (1,2,2,1)
  | 23 => (1,2,2,3)
  | 24 => (1,2,3,1)
  | 25 => (1,3,0,1)
  | 26 => (1,3,2,1)
  | 27 => (1,3,3,0)
  | 28 => (1,3,3,1)
  | 29 => (1,3,3,2)
  | 30 => (2,0,0,1)
  | 31 => (2,0,0,2)
  | 32 => (2,0,0,3)
  | 33 => (2,0,1,2)
  | 34 => (2,0,3,2)
  | 35 => (2,1,0,2)
  | 36 => (2,1,1,0)
  | 37 => (2,1,1,2)
  | 38 => (2,1,1,3)
  | 39 => (2,1,3,2)
  | 40 => (2,3,0,2)
  | 41 => (2,3,1,2)
  | 42 => (2,3,3,0)
  | 43 => (2,3,3,1)
  | 44 => (2,3,3,2)
  | 45 => (3,0,0,1)
  | 46 => (3,0,0,2)
  | 47 => (3,0,0,3)
  | 48 => (3,0,1,3)
  | 49 => (3,0,2,3)
  | 50 => (3,1,0,3)
  | 51 => (3,1,1,0)
  | 52 => (3,1,1,2)
  | 53 => (3,1,1,3)
  | 54 => (3,1,2,3)
  | 55 => (3,2,0,3)
  | 56 => (3,2,1,3)
  | 57 => (3,2,2,0)
  | 58 => (3,2,2,1)
  | _ => (3,2,2,3)

private theorem coords_valid : ∀ i : Fin 60,
    (coords i).1 ≠ (coords i).2.1 ∧
    (coords i).2.2.1 ≠ (coords i).2.2.2 ∧
    ((coords i).2.1 = (coords i).2.2.1 ∨ (coords i).2.2.2 = (coords i).1) := by
  decide +kernel

def sourceVertex (i : Fin 60) : Arc (arcGraph (⊤ : SimpleGraph (Fin 4))) :=
  ⟨(⟨((coords i).1,(coords i).2.1),(coords_valid i).1⟩,
    ⟨((coords i).2.2.1,(coords i).2.2.2),(coords_valid i).2.1⟩),
    (coords_valid i).2.2⟩

def sourceAdj (i j : Fin 60) : Prop :=
  ((coords i).2.2.1 = (coords j).1 ∧ (coords i).2.2.2 = (coords j).2.1) ∨
  ((coords j).2.2.1 = (coords i).1 ∧ (coords j).2.2.2 = (coords i).2.1)
instance : DecidableRel sourceAdj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

lemma sourceVertex_adj {i j : Fin 60} (h : sourceAdj i j) :
    (arcGraph (arcGraph (⊤ : SimpleGraph (Fin 4)))).Adj (sourceVertex i) (sourceVertex j) := by
  rcases h with h | h
  · exact Or.inl (Subtype.ext (Prod.ext h.1 h.2))
  · exact Or.inr (Subtype.ext (Prod.ext h.1 h.2))

private lemma sat_one {v : Sat.Valuation} {c : Sat.Clause}
    (h : v.satisfies c) : v.satisfies_fmla (Sat.Fmla.one c) :=
  ⟨by intro d hd; have he : d = c := List.mem_singleton.mp hd; subst d; exact h⟩
private lemma sat_and {v : Sat.Valuation} {a b : Sat.Fmla}
    (ha : v.satisfies_fmla a) (hb : v.satisfies_fmla b) :
    v.satisfies_fmla (Sat.Fmla.and a b) :=
  ⟨fun c hc => (List.mem_append.mp hc).elim (ha.prop c) (hb.prop c)⟩

variable {V : Type*} (H : SimpleGraph V) (m : V → Prop)

structure LocalConditions : Prop where
  independent : ∀ a b, m a → m b → ¬H.Adj a b
  hit : ∀ a b c, H.Adj a b → H.Adj a c → H.Adj b c → m a ∨ m b ∨ m c
  degree : ∀ a, m a → ∀ b c d e, H.Adj a b → H.Adj a c → H.Adj a d → H.Adj a e →
    b = c ∨ b = d ∨ b = e ∨ c = d ∨ c = e ∨ d = e
  matching : ∀ a, m a → ∀ b c d, H.Adj a b → H.Adj a c → H.Adj a d →
    H.Adj b c → H.Adj b d → c = d

variable (h : LocalConditions H m) (z : Fin 60 → V)
    (hz : ∀ i j, sourceAdj i j → H.Adj (z i) (z j))

def valuation : Sat.Valuation := fun n =>
  if n < 60 then m (z (Fin.ofNat 60 n))
  else if n < 3660 then
    z (Fin.ofNat 60 ((n-60)/60)) = z (Fin.ofNat 60 ((n-60)%60))
  else H.Adj (z (Fin.ofNat 60 ((n-3660)/60))) (z (Fin.ofNat 60 ((n-3660)%60)))

private def node0 : Sat.Fmla := Sat.Fmla.one [.pos 3675]
private def node1 : Sat.Fmla := Sat.Fmla.one [.neg 0, .neg 16, .neg 3676]
private def node2 : Sat.Fmla := Sat.Fmla.and node0 node1
private def node3 : Sat.Fmla := Sat.Fmla.one [.pos 3676]
private def node4 : Sat.Fmla := Sat.Fmla.one [.neg 0, .neg 17, .neg 3677]
private def node5 : Sat.Fmla := Sat.Fmla.one [.pos 3677]
private def node6 : Sat.Fmla := Sat.Fmla.and node4 node5
private def node7 : Sat.Fmla := Sat.Fmla.and node3 node6
private def node8 : Sat.Fmla := Sat.Fmla.and node2 node7
private def node9 : Sat.Fmla := Sat.Fmla.one [.neg 0, .neg 18, .neg 3678]
private def node10 : Sat.Fmla := Sat.Fmla.one [.pos 3678]
private def node11 : Sat.Fmla := Sat.Fmla.one [.pos 3679]
private def node12 : Sat.Fmla := Sat.Fmla.and node10 node11
private def node13 : Sat.Fmla := Sat.Fmla.and node9 node12
private def node14 : Sat.Fmla := Sat.Fmla.one [.neg 0, .neg 20, .neg 3680]
private def node15 : Sat.Fmla := Sat.Fmla.one [.pos 3680]
private def node16 : Sat.Fmla := Sat.Fmla.one [.neg 0, .neg 25, .neg 3685]
private def node17 : Sat.Fmla := Sat.Fmla.and node15 node16
private def node18 : Sat.Fmla := Sat.Fmla.and node14 node17
private def node19 : Sat.Fmla := Sat.Fmla.and node13 node18
private def node20 : Sat.Fmla := Sat.Fmla.and node8 node19
private def node21 : Sat.Fmla := Sat.Fmla.one [.pos 3685]
private def node22 : Sat.Fmla := Sat.Fmla.one [.neg 0, .neg 30, .neg 3690]
private def node23 : Sat.Fmla := Sat.Fmla.one [.pos 3690]
private def node24 : Sat.Fmla := Sat.Fmla.and node22 node23
private def node25 : Sat.Fmla := Sat.Fmla.and node21 node24
private def node26 : Sat.Fmla := Sat.Fmla.one [.pos 3705]
private def node27 : Sat.Fmla := Sat.Fmla.one [.neg 123, .neg 1, .pos 3]
private def node28 : Sat.Fmla := Sat.Fmla.one [.neg 123, .pos 1, .neg 3]
private def node29 : Sat.Fmla := Sat.Fmla.and node27 node28
private def node30 : Sat.Fmla := Sat.Fmla.and node26 node29
private def node31 : Sat.Fmla := Sat.Fmla.and node25 node30
private def node32 : Sat.Fmla := Sat.Fmla.one [.neg 1, .neg 3, .neg 3723]
private def node33 : Sat.Fmla := Sat.Fmla.one [.neg 1, .neg 15, .neg 3735]
private def node34 : Sat.Fmla := Sat.Fmla.one [.pos 3735]
private def node35 : Sat.Fmla := Sat.Fmla.and node33 node34
private def node36 : Sat.Fmla := Sat.Fmla.and node32 node35
private def node37 : Sat.Fmla := Sat.Fmla.one [.neg 1, .neg 20, .neg 3740]
private def node38 : Sat.Fmla := Sat.Fmla.one [.pos 3740]
private def node39 : Sat.Fmla := Sat.Fmla.one [.neg 141, .neg 3741]
private def node40 : Sat.Fmla := Sat.Fmla.and node38 node39
private def node41 : Sat.Fmla := Sat.Fmla.and node37 node40
private def node42 : Sat.Fmla := Sat.Fmla.and node36 node41
private def node43 : Sat.Fmla := Sat.Fmla.and node31 node42
private def node44 : Sat.Fmla := Sat.Fmla.and node20 node43
private def node45 : Sat.Fmla := Sat.Fmla.one [.neg 1, .neg 21, .neg 3741]
private def node46 : Sat.Fmla := Sat.Fmla.one [.pos 3741]
private def node47 : Sat.Fmla := Sat.Fmla.and node45 node46
private def node48 : Sat.Fmla := Sat.Fmla.one [.neg 1, .neg 22, .neg 3742]
private def node49 : Sat.Fmla := Sat.Fmla.one [.pos 3742]
private def node50 : Sat.Fmla := Sat.Fmla.one [.neg 1, .neg 23, .neg 3743]
private def node51 : Sat.Fmla := Sat.Fmla.and node49 node50
private def node52 : Sat.Fmla := Sat.Fmla.and node48 node51
private def node53 : Sat.Fmla := Sat.Fmla.and node47 node52
private def node54 : Sat.Fmla := Sat.Fmla.one [.pos 3743]
private def node55 : Sat.Fmla := Sat.Fmla.one [.neg 1, .neg 24, .neg 3744]
private def node56 : Sat.Fmla := Sat.Fmla.one [.pos 3744]
private def node57 : Sat.Fmla := Sat.Fmla.and node55 node56
private def node58 : Sat.Fmla := Sat.Fmla.and node54 node57
private def node59 : Sat.Fmla := Sat.Fmla.one [.neg 145, .neg 3745]
private def node60 : Sat.Fmla := Sat.Fmla.one [.neg 1, .neg 25, .neg 3745]
private def node61 : Sat.Fmla := Sat.Fmla.one [.pos 3745]
private def node62 : Sat.Fmla := Sat.Fmla.and node60 node61
private def node63 : Sat.Fmla := Sat.Fmla.and node59 node62
private def node64 : Sat.Fmla := Sat.Fmla.and node58 node63
private def node65 : Sat.Fmla := Sat.Fmla.and node53 node64
private def node66 : Sat.Fmla := Sat.Fmla.one [.neg 150, .neg 3750]
private def node67 : Sat.Fmla := Sat.Fmla.one [.neg 1, .neg 30, .neg 3750]
private def node68 : Sat.Fmla := Sat.Fmla.one [.pos 3750]
private def node69 : Sat.Fmla := Sat.Fmla.and node67 node68
private def node70 : Sat.Fmla := Sat.Fmla.and node66 node69
private def node71 : Sat.Fmla := Sat.Fmla.one [.neg 158, .neg 1, .pos 38]
private def node72 : Sat.Fmla := Sat.Fmla.one [.neg 1, .neg 45, .neg 3765]
private def node73 : Sat.Fmla := Sat.Fmla.one [.pos 3765]
private def node74 : Sat.Fmla := Sat.Fmla.and node72 node73
private def node75 : Sat.Fmla := Sat.Fmla.and node71 node74
private def node76 : Sat.Fmla := Sat.Fmla.and node70 node75
private def node77 : Sat.Fmla := Sat.Fmla.one [.neg 168, .pos 1, .neg 48]
private def node78 : Sat.Fmla := Sat.Fmla.one [.neg 2, .neg 15, .neg 3795]
private def node79 : Sat.Fmla := Sat.Fmla.one [.pos 3795]
private def node80 : Sat.Fmla := Sat.Fmla.and node78 node79
private def node81 : Sat.Fmla := Sat.Fmla.and node77 node80
private def node82 : Sat.Fmla := Sat.Fmla.one [.neg 2, .neg 20, .neg 3800]
private def node83 : Sat.Fmla := Sat.Fmla.one [.pos 3800]
private def node84 : Sat.Fmla := Sat.Fmla.one [.neg 2, .neg 25, .neg 3805]
private def node85 : Sat.Fmla := Sat.Fmla.and node83 node84
private def node86 : Sat.Fmla := Sat.Fmla.and node82 node85
private def node87 : Sat.Fmla := Sat.Fmla.and node81 node86
private def node88 : Sat.Fmla := Sat.Fmla.and node76 node87
private def node89 : Sat.Fmla := Sat.Fmla.and node65 node88
private def node90 : Sat.Fmla := Sat.Fmla.and node44 node89
private def node91 : Sat.Fmla := Sat.Fmla.one [.pos 3805]
private def node92 : Sat.Fmla := Sat.Fmla.one [.neg 2, .neg 26, .neg 3806]
private def node93 : Sat.Fmla := Sat.Fmla.and node91 node92
private def node94 : Sat.Fmla := Sat.Fmla.one [.pos 3806]
private def node95 : Sat.Fmla := Sat.Fmla.one [.neg 207, .neg 3807]
private def node96 : Sat.Fmla := Sat.Fmla.one [.neg 2, .neg 27, .neg 3807]
private def node97 : Sat.Fmla := Sat.Fmla.and node95 node96
private def node98 : Sat.Fmla := Sat.Fmla.and node94 node97
private def node99 : Sat.Fmla := Sat.Fmla.and node93 node98
private def node100 : Sat.Fmla := Sat.Fmla.one [.pos 3807]
private def node101 : Sat.Fmla := Sat.Fmla.one [.neg 2, .neg 28, .neg 3808]
private def node102 : Sat.Fmla := Sat.Fmla.one [.pos 3808]
private def node103 : Sat.Fmla := Sat.Fmla.and node101 node102
private def node104 : Sat.Fmla := Sat.Fmla.and node100 node103
private def node105 : Sat.Fmla := Sat.Fmla.one [.neg 2, .neg 29, .neg 3809]
private def node106 : Sat.Fmla := Sat.Fmla.one [.pos 3809]
private def node107 : Sat.Fmla := Sat.Fmla.one [.neg 2, .neg 30, .neg 3810]
private def node108 : Sat.Fmla := Sat.Fmla.and node106 node107
private def node109 : Sat.Fmla := Sat.Fmla.and node105 node108
private def node110 : Sat.Fmla := Sat.Fmla.and node104 node109
private def node111 : Sat.Fmla := Sat.Fmla.and node99 node110
private def node112 : Sat.Fmla := Sat.Fmla.one [.pos 3810]
private def node113 : Sat.Fmla := Sat.Fmla.one [.neg 225, .neg 3825]
private def node114 : Sat.Fmla := Sat.Fmla.one [.neg 2, .neg 45, .neg 3825]
private def node115 : Sat.Fmla := Sat.Fmla.and node113 node114
private def node116 : Sat.Fmla := Sat.Fmla.and node112 node115
private def node117 : Sat.Fmla := Sat.Fmla.one [.pos 3825]
private def node118 : Sat.Fmla := Sat.Fmla.one [.neg 252, .neg 3852]
private def node119 : Sat.Fmla := Sat.Fmla.one [.neg 3, .neg 15, .neg 3855]
private def node120 : Sat.Fmla := Sat.Fmla.and node118 node119
private def node121 : Sat.Fmla := Sat.Fmla.and node117 node120
private def node122 : Sat.Fmla := Sat.Fmla.and node116 node121
private def node123 : Sat.Fmla := Sat.Fmla.one [.pos 3855]
private def node124 : Sat.Fmla := Sat.Fmla.one [.neg 260, .neg 3860]
private def node125 : Sat.Fmla := Sat.Fmla.one [.neg 3, .neg 20, .neg 3860]
private def node126 : Sat.Fmla := Sat.Fmla.and node124 node125
private def node127 : Sat.Fmla := Sat.Fmla.and node123 node126
private def node128 : Sat.Fmla := Sat.Fmla.one [.pos 3860]
private def node129 : Sat.Fmla := Sat.Fmla.one [.neg 3, .neg 25, .neg 3865]
private def node130 : Sat.Fmla := Sat.Fmla.one [.pos 3865]
private def node131 : Sat.Fmla := Sat.Fmla.and node129 node130
private def node132 : Sat.Fmla := Sat.Fmla.and node128 node131
private def node133 : Sat.Fmla := Sat.Fmla.and node127 node132
private def node134 : Sat.Fmla := Sat.Fmla.and node122 node133
private def node135 : Sat.Fmla := Sat.Fmla.and node111 node134
private def node136 : Sat.Fmla := Sat.Fmla.one [.neg 3, .neg 30, .neg 3870]
private def node137 : Sat.Fmla := Sat.Fmla.one [.pos 3870]
private def node138 : Sat.Fmla := Sat.Fmla.one [.pos 3871]
private def node139 : Sat.Fmla := Sat.Fmla.and node137 node138
private def node140 : Sat.Fmla := Sat.Fmla.and node136 node139
private def node141 : Sat.Fmla := Sat.Fmla.one [.neg 3, .neg 32, .neg 3872]
private def node142 : Sat.Fmla := Sat.Fmla.one [.pos 3872]
private def node143 : Sat.Fmla := Sat.Fmla.one [.neg 273, .neg 3873]
private def node144 : Sat.Fmla := Sat.Fmla.and node142 node143
private def node145 : Sat.Fmla := Sat.Fmla.and node141 node144
private def node146 : Sat.Fmla := Sat.Fmla.and node140 node145
private def node147 : Sat.Fmla := Sat.Fmla.one [.neg 3, .neg 33, .neg 3873]
private def node148 : Sat.Fmla := Sat.Fmla.one [.pos 3873]
private def node149 : Sat.Fmla := Sat.Fmla.one [.neg 3, .neg 34, .neg 3874]
private def node150 : Sat.Fmla := Sat.Fmla.and node148 node149
private def node151 : Sat.Fmla := Sat.Fmla.and node147 node150
private def node152 : Sat.Fmla := Sat.Fmla.one [.pos 3874]
private def node153 : Sat.Fmla := Sat.Fmla.one [.neg 3, .neg 45, .neg 3885]
private def node154 : Sat.Fmla := Sat.Fmla.one [.pos 3885]
private def node155 : Sat.Fmla := Sat.Fmla.and node153 node154
private def node156 : Sat.Fmla := Sat.Fmla.and node152 node155
private def node157 : Sat.Fmla := Sat.Fmla.and node151 node156
private def node158 : Sat.Fmla := Sat.Fmla.and node146 node157
private def node159 : Sat.Fmla := Sat.Fmla.one [.neg 295, .neg 3895]
private def node160 : Sat.Fmla := Sat.Fmla.one [.neg 297, .neg 3, .pos 57]
private def node161 : Sat.Fmla := Sat.Fmla.one [.pos 3915]
private def node162 : Sat.Fmla := Sat.Fmla.and node160 node161
private def node163 : Sat.Fmla := Sat.Fmla.and node159 node162
private def node164 : Sat.Fmla := Sat.Fmla.one [.neg 320, .neg 3920]
private def node165 : Sat.Fmla := Sat.Fmla.one [.neg 4, .neg 20, .neg 3920]
private def node166 : Sat.Fmla := Sat.Fmla.one [.pos 3920]
private def node167 : Sat.Fmla := Sat.Fmla.and node165 node166
private def node168 : Sat.Fmla := Sat.Fmla.and node164 node167
private def node169 : Sat.Fmla := Sat.Fmla.and node163 node168
private def node170 : Sat.Fmla := Sat.Fmla.one [.neg 325, .neg 3925]
private def node171 : Sat.Fmla := Sat.Fmla.one [.neg 4, .neg 25, .neg 3925]
private def node172 : Sat.Fmla := Sat.Fmla.one [.pos 3925]
private def node173 : Sat.Fmla := Sat.Fmla.and node171 node172
private def node174 : Sat.Fmla := Sat.Fmla.and node170 node173
private def node175 : Sat.Fmla := Sat.Fmla.one [.neg 4, .neg 30, .neg 3930]
private def node176 : Sat.Fmla := Sat.Fmla.one [.pos 3930]
private def node177 : Sat.Fmla := Sat.Fmla.one [.neg 4, .neg 45, .neg 3945]
private def node178 : Sat.Fmla := Sat.Fmla.and node176 node177
private def node179 : Sat.Fmla := Sat.Fmla.and node175 node178
private def node180 : Sat.Fmla := Sat.Fmla.and node174 node179
private def node181 : Sat.Fmla := Sat.Fmla.and node169 node180
private def node182 : Sat.Fmla := Sat.Fmla.and node158 node181
private def node183 : Sat.Fmla := Sat.Fmla.and node135 node182
private def node184 : Sat.Fmla := Sat.Fmla.and node90 node183
private def node185 : Sat.Fmla := Sat.Fmla.one [.pos 3945]
private def node186 : Sat.Fmla := Sat.Fmla.one [.neg 4, .neg 46, .neg 3946]
private def node187 : Sat.Fmla := Sat.Fmla.and node185 node186
private def node188 : Sat.Fmla := Sat.Fmla.one [.pos 3946]
private def node189 : Sat.Fmla := Sat.Fmla.one [.neg 4, .neg 47, .neg 3947]
private def node190 : Sat.Fmla := Sat.Fmla.one [.pos 3947]
private def node191 : Sat.Fmla := Sat.Fmla.and node189 node190
private def node192 : Sat.Fmla := Sat.Fmla.and node188 node191
private def node193 : Sat.Fmla := Sat.Fmla.and node187 node192
private def node194 : Sat.Fmla := Sat.Fmla.one [.neg 348, .neg 3948]
private def node195 : Sat.Fmla := Sat.Fmla.one [.neg 4, .neg 48, .neg 3948]
private def node196 : Sat.Fmla := Sat.Fmla.one [.pos 3948]
private def node197 : Sat.Fmla := Sat.Fmla.and node195 node196
private def node198 : Sat.Fmla := Sat.Fmla.and node194 node197
private def node199 : Sat.Fmla := Sat.Fmla.one [.neg 4, .neg 49, .neg 3949]
private def node200 : Sat.Fmla := Sat.Fmla.one [.pos 3949]
private def node201 : Sat.Fmla := Sat.Fmla.one [.pos 3975]
private def node202 : Sat.Fmla := Sat.Fmla.and node200 node201
private def node203 : Sat.Fmla := Sat.Fmla.and node199 node202
private def node204 : Sat.Fmla := Sat.Fmla.and node198 node203
private def node205 : Sat.Fmla := Sat.Fmla.and node193 node204
private def node206 : Sat.Fmla := Sat.Fmla.one [.neg 5, .neg 16, .neg 3976]
private def node207 : Sat.Fmla := Sat.Fmla.one [.pos 3976]
private def node208 : Sat.Fmla := Sat.Fmla.one [.neg 5, .neg 17, .neg 3977]
private def node209 : Sat.Fmla := Sat.Fmla.and node207 node208
private def node210 : Sat.Fmla := Sat.Fmla.and node206 node209
private def node211 : Sat.Fmla := Sat.Fmla.one [.pos 3977]
private def node212 : Sat.Fmla := Sat.Fmla.one [.neg 5, .neg 18, .neg 3978]
private def node213 : Sat.Fmla := Sat.Fmla.one [.pos 3978]
private def node214 : Sat.Fmla := Sat.Fmla.and node212 node213
private def node215 : Sat.Fmla := Sat.Fmla.and node211 node214
private def node216 : Sat.Fmla := Sat.Fmla.and node210 node215
private def node217 : Sat.Fmla := Sat.Fmla.one [.neg 5, .neg 19, .neg 3979]
private def node218 : Sat.Fmla := Sat.Fmla.one [.pos 3979]
private def node219 : Sat.Fmla := Sat.Fmla.one [.neg 5, .neg 31, .neg 3991]
private def node220 : Sat.Fmla := Sat.Fmla.and node218 node219
private def node221 : Sat.Fmla := Sat.Fmla.and node217 node220
private def node222 : Sat.Fmla := Sat.Fmla.one [.pos 3991]
private def node223 : Sat.Fmla := Sat.Fmla.one [.neg 395, .neg 3995]
private def node224 : Sat.Fmla := Sat.Fmla.one [.pos 3995]
private def node225 : Sat.Fmla := Sat.Fmla.and node223 node224
private def node226 : Sat.Fmla := Sat.Fmla.and node222 node225
private def node227 : Sat.Fmla := Sat.Fmla.and node221 node226
private def node228 : Sat.Fmla := Sat.Fmla.and node216 node227
private def node229 : Sat.Fmla := Sat.Fmla.and node205 node228
private def node230 : Sat.Fmla := Sat.Fmla.one [.neg 5, .neg 40, .neg 4000]
private def node231 : Sat.Fmla := Sat.Fmla.one [.pos 4000]
private def node232 : Sat.Fmla := Sat.Fmla.one [.neg 5, .neg 46, .neg 4006]
private def node233 : Sat.Fmla := Sat.Fmla.and node231 node232
private def node234 : Sat.Fmla := Sat.Fmla.and node230 node233
private def node235 : Sat.Fmla := Sat.Fmla.one [.pos 4006]
private def node236 : Sat.Fmla := Sat.Fmla.one [.neg 6, .neg 16, .neg 4036]
private def node237 : Sat.Fmla := Sat.Fmla.one [.pos 4036]
private def node238 : Sat.Fmla := Sat.Fmla.and node236 node237
private def node239 : Sat.Fmla := Sat.Fmla.and node235 node238
private def node240 : Sat.Fmla := Sat.Fmla.and node234 node239
private def node241 : Sat.Fmla := Sat.Fmla.one [.neg 6, .neg 30, .neg 4050]
private def node242 : Sat.Fmla := Sat.Fmla.one [.pos 4050]
private def node243 : Sat.Fmla := Sat.Fmla.one [.neg 6, .neg 32, .neg 4052]
private def node244 : Sat.Fmla := Sat.Fmla.and node242 node243
private def node245 : Sat.Fmla := Sat.Fmla.and node241 node244
private def node246 : Sat.Fmla := Sat.Fmla.one [.pos 4052]
private def node247 : Sat.Fmla := Sat.Fmla.one [.neg 6, .neg 33, .neg 4053]
private def node248 : Sat.Fmla := Sat.Fmla.one [.pos 4053]
private def node249 : Sat.Fmla := Sat.Fmla.and node247 node248
private def node250 : Sat.Fmla := Sat.Fmla.and node246 node249
private def node251 : Sat.Fmla := Sat.Fmla.and node245 node250
private def node252 : Sat.Fmla := Sat.Fmla.and node240 node251
private def node253 : Sat.Fmla := Sat.Fmla.one [.neg 454, .neg 4054]
private def node254 : Sat.Fmla := Sat.Fmla.one [.neg 6, .neg 34, .neg 4054]
private def node255 : Sat.Fmla := Sat.Fmla.one [.pos 4054]
private def node256 : Sat.Fmla := Sat.Fmla.and node254 node255
private def node257 : Sat.Fmla := Sat.Fmla.and node253 node256
private def node258 : Sat.Fmla := Sat.Fmla.one [.neg 6, .neg 35, .neg 4055]
private def node259 : Sat.Fmla := Sat.Fmla.one [.pos 4055]
private def node260 : Sat.Fmla := Sat.Fmla.one [.pos 4060]
private def node261 : Sat.Fmla := Sat.Fmla.and node259 node260
private def node262 : Sat.Fmla := Sat.Fmla.and node258 node261
private def node263 : Sat.Fmla := Sat.Fmla.and node257 node262
private def node264 : Sat.Fmla := Sat.Fmla.one [.neg 6, .neg 46, .neg 4066]
private def node265 : Sat.Fmla := Sat.Fmla.one [.pos 4066]
private def node266 : Sat.Fmla := Sat.Fmla.one [.neg 496, .neg 4096]
private def node267 : Sat.Fmla := Sat.Fmla.and node265 node266
private def node268 : Sat.Fmla := Sat.Fmla.and node264 node267
private def node269 : Sat.Fmla := Sat.Fmla.one [.neg 7, .neg 16, .neg 4096]
private def node270 : Sat.Fmla := Sat.Fmla.one [.pos 4096]
private def node271 : Sat.Fmla := Sat.Fmla.one [.pos 4111]
private def node272 : Sat.Fmla := Sat.Fmla.and node270 node271
private def node273 : Sat.Fmla := Sat.Fmla.and node269 node272
private def node274 : Sat.Fmla := Sat.Fmla.and node268 node273
private def node275 : Sat.Fmla := Sat.Fmla.and node263 node274
private def node276 : Sat.Fmla := Sat.Fmla.and node252 node275
private def node277 : Sat.Fmla := Sat.Fmla.and node229 node276
private def node278 : Sat.Fmla := Sat.Fmla.one [.neg 516, .neg 4116]
private def node279 : Sat.Fmla := Sat.Fmla.one [.pos 4116]
private def node280 : Sat.Fmla := Sat.Fmla.and node278 node279
private def node281 : Sat.Fmla := Sat.Fmla.one [.pos 4117]
private def node282 : Sat.Fmla := Sat.Fmla.one [.neg 7, .neg 38, .neg 4118]
private def node283 : Sat.Fmla := Sat.Fmla.one [.pos 4118]
private def node284 : Sat.Fmla := Sat.Fmla.and node282 node283
private def node285 : Sat.Fmla := Sat.Fmla.and node281 node284
private def node286 : Sat.Fmla := Sat.Fmla.and node280 node285
private def node287 : Sat.Fmla := Sat.Fmla.one [.neg 7, .neg 39, .neg 4119]
private def node288 : Sat.Fmla := Sat.Fmla.one [.pos 4119]
private def node289 : Sat.Fmla := Sat.Fmla.one [.neg 7, .neg 40, .neg 4120]
private def node290 : Sat.Fmla := Sat.Fmla.and node288 node289
private def node291 : Sat.Fmla := Sat.Fmla.and node287 node290
private def node292 : Sat.Fmla := Sat.Fmla.one [.pos 4120]
private def node293 : Sat.Fmla := Sat.Fmla.one [.neg 7, .neg 46, .neg 4126]
private def node294 : Sat.Fmla := Sat.Fmla.one [.pos 4126]
private def node295 : Sat.Fmla := Sat.Fmla.and node293 node294
private def node296 : Sat.Fmla := Sat.Fmla.and node292 node295
private def node297 : Sat.Fmla := Sat.Fmla.and node291 node296
private def node298 : Sat.Fmla := Sat.Fmla.and node286 node297
private def node299 : Sat.Fmla := Sat.Fmla.one [.neg 8, .neg 16, .neg 4156]
private def node300 : Sat.Fmla := Sat.Fmla.one [.pos 4156]
private def node301 : Sat.Fmla := Sat.Fmla.one [.neg 8, .neg 31, .neg 4171]
private def node302 : Sat.Fmla := Sat.Fmla.and node300 node301
private def node303 : Sat.Fmla := Sat.Fmla.and node299 node302
private def node304 : Sat.Fmla := Sat.Fmla.one [.pos 4171]
private def node305 : Sat.Fmla := Sat.Fmla.one [.neg 8, .neg 35, .neg 4175]
private def node306 : Sat.Fmla := Sat.Fmla.one [.pos 4175]
private def node307 : Sat.Fmla := Sat.Fmla.and node305 node306
private def node308 : Sat.Fmla := Sat.Fmla.and node304 node307
private def node309 : Sat.Fmla := Sat.Fmla.and node303 node308
private def node310 : Sat.Fmla := Sat.Fmla.one [.neg 8, .neg 40, .neg 4180]
private def node311 : Sat.Fmla := Sat.Fmla.one [.pos 4180]
private def node312 : Sat.Fmla := Sat.Fmla.one [.neg 8, .neg 41, .neg 4181]
private def node313 : Sat.Fmla := Sat.Fmla.and node311 node312
private def node314 : Sat.Fmla := Sat.Fmla.and node310 node313
private def node315 : Sat.Fmla := Sat.Fmla.one [.pos 4181]
private def node316 : Sat.Fmla := Sat.Fmla.one [.neg 8, .neg 42, .neg 4182]
private def node317 : Sat.Fmla := Sat.Fmla.one [.pos 4182]
private def node318 : Sat.Fmla := Sat.Fmla.and node316 node317
private def node319 : Sat.Fmla := Sat.Fmla.and node315 node318
private def node320 : Sat.Fmla := Sat.Fmla.and node314 node319
private def node321 : Sat.Fmla := Sat.Fmla.and node309 node320
private def node322 : Sat.Fmla := Sat.Fmla.and node298 node321
private def node323 : Sat.Fmla := Sat.Fmla.one [.neg 8, .neg 43, .neg 4183]
private def node324 : Sat.Fmla := Sat.Fmla.one [.pos 4183]
private def node325 : Sat.Fmla := Sat.Fmla.one [.neg 8, .neg 44, .neg 4184]
private def node326 : Sat.Fmla := Sat.Fmla.and node324 node325
private def node327 : Sat.Fmla := Sat.Fmla.and node323 node326
private def node328 : Sat.Fmla := Sat.Fmla.one [.pos 4184]
private def node329 : Sat.Fmla := Sat.Fmla.one [.neg 586, .neg 4186]
private def node330 : Sat.Fmla := Sat.Fmla.one [.pos 4186]
private def node331 : Sat.Fmla := Sat.Fmla.and node329 node330
private def node332 : Sat.Fmla := Sat.Fmla.and node328 node331
private def node333 : Sat.Fmla := Sat.Fmla.and node327 node332
private def node334 : Sat.Fmla := Sat.Fmla.one [.neg 9, .neg 16, .neg 4216]
private def node335 : Sat.Fmla := Sat.Fmla.one [.pos 4216]
private def node336 : Sat.Fmla := Sat.Fmla.one [.neg 9, .neg 31, .neg 4231]
private def node337 : Sat.Fmla := Sat.Fmla.and node335 node336
private def node338 : Sat.Fmla := Sat.Fmla.and node334 node337
private def node339 : Sat.Fmla := Sat.Fmla.one [.pos 4231]
private def node340 : Sat.Fmla := Sat.Fmla.one [.pos 4235]
private def node341 : Sat.Fmla := Sat.Fmla.one [.neg 640, .neg 4240]
private def node342 : Sat.Fmla := Sat.Fmla.and node340 node341
private def node343 : Sat.Fmla := Sat.Fmla.and node339 node342
private def node344 : Sat.Fmla := Sat.Fmla.and node338 node343
private def node345 : Sat.Fmla := Sat.Fmla.and node333 node344
private def node346 : Sat.Fmla := Sat.Fmla.one [.neg 9, .neg 40, .neg 4240]
private def node347 : Sat.Fmla := Sat.Fmla.one [.pos 4240]
private def node348 : Sat.Fmla := Sat.Fmla.one [.neg 9, .neg 45, .neg 4245]
private def node349 : Sat.Fmla := Sat.Fmla.and node347 node348
private def node350 : Sat.Fmla := Sat.Fmla.and node346 node349
private def node351 : Sat.Fmla := Sat.Fmla.one [.pos 4245]
private def node352 : Sat.Fmla := Sat.Fmla.one [.neg 9, .neg 46, .neg 4246]
private def node353 : Sat.Fmla := Sat.Fmla.one [.pos 4246]
private def node354 : Sat.Fmla := Sat.Fmla.and node352 node353
private def node355 : Sat.Fmla := Sat.Fmla.and node351 node354
private def node356 : Sat.Fmla := Sat.Fmla.and node350 node355
private def node357 : Sat.Fmla := Sat.Fmla.one [.neg 9, .neg 47, .neg 4247]
private def node358 : Sat.Fmla := Sat.Fmla.one [.pos 4247]
private def node359 : Sat.Fmla := Sat.Fmla.one [.neg 9, .neg 48, .neg 4248]
private def node360 : Sat.Fmla := Sat.Fmla.and node358 node359
private def node361 : Sat.Fmla := Sat.Fmla.and node357 node360
private def node362 : Sat.Fmla := Sat.Fmla.one [.pos 4248]
private def node363 : Sat.Fmla := Sat.Fmla.one [.pos 4249]
private def node364 : Sat.Fmla := Sat.Fmla.one [.neg 10, .neg 15, .neg 4275]
private def node365 : Sat.Fmla := Sat.Fmla.and node363 node364
private def node366 : Sat.Fmla := Sat.Fmla.and node362 node365
private def node367 : Sat.Fmla := Sat.Fmla.and node361 node366
private def node368 : Sat.Fmla := Sat.Fmla.and node356 node367
private def node369 : Sat.Fmla := Sat.Fmla.and node345 node368
private def node370 : Sat.Fmla := Sat.Fmla.and node322 node369
private def node371 : Sat.Fmla := Sat.Fmla.and node277 node370
private def node372 : Sat.Fmla := Sat.Fmla.and node184 node371
include h hz in
example : (valuation H m z).satisfies_fmla node372 := by
  apply sat_and (a := node184) (b := node371)
  ·
    apply sat_and (a := node90) (b := node183)
    ·
      apply sat_and (a := node44) (b := node89)
      ·
        apply sat_and (a := node20) (b := node43)
        ·
          apply sat_and (a := node8) (b := node19)
          ·
            apply sat_and (a := node2) (b := node7)
            ·
              apply sat_and (a := node0) (b := node1)
              ·
                apply sat_one (c := [.pos 3675])
                change (¬ (H.Adj (z 0) (z 15))) → False
                intro h1
                exact h1 (hz 0 15 (by decide +kernel))
              ·
                apply sat_one (c := [.neg 0, .neg 16, .neg 3676])
                change (m (z 0)) → (m (z 16)) → (H.Adj (z 0) (z 16)) → False
                intro h1 h2 h3
                exact h.independent (z 0) (z 16) h1 h2 h3
            ·
              apply sat_and (a := node3) (b := node6)
              ·
                apply sat_one (c := [.pos 3676])
                change (¬ (H.Adj (z 0) (z 16))) → False
                intro h1
                exact h1 (hz 0 16 (by decide +kernel))
              ·
                apply sat_and (a := node4) (b := node5)
                ·
                  apply sat_one (c := [.neg 0, .neg 17, .neg 3677])
                  change (m (z 0)) → (m (z 17)) → (H.Adj (z 0) (z 17)) → False
                  intro h1 h2 h3
                  exact h.independent (z 0) (z 17) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 3677])
                  change (¬ (H.Adj (z 0) (z 17))) → False
                  intro h1
                  exact h1 (hz 0 17 (by decide +kernel))
          ·
            apply sat_and (a := node13) (b := node18)
            ·
              apply sat_and (a := node9) (b := node12)
              ·
                apply sat_one (c := [.neg 0, .neg 18, .neg 3678])
                change (m (z 0)) → (m (z 18)) → (H.Adj (z 0) (z 18)) → False
                intro h1 h2 h3
                exact h.independent (z 0) (z 18) h1 h2 h3
              ·
                apply sat_and (a := node10) (b := node11)
                ·
                  apply sat_one (c := [.pos 3678])
                  change (¬ (H.Adj (z 0) (z 18))) → False
                  intro h1
                  exact h1 (hz 0 18 (by decide +kernel))
                ·
                  apply sat_one (c := [.pos 3679])
                  change (¬ (H.Adj (z 0) (z 19))) → False
                  intro h1
                  exact h1 (hz 0 19 (by decide +kernel))
            ·
              apply sat_and (a := node14) (b := node17)
              ·
                apply sat_one (c := [.neg 0, .neg 20, .neg 3680])
                change (m (z 0)) → (m (z 20)) → (H.Adj (z 0) (z 20)) → False
                intro h1 h2 h3
                exact h.independent (z 0) (z 20) h1 h2 h3
              ·
                apply sat_and (a := node15) (b := node16)
                ·
                  apply sat_one (c := [.pos 3680])
                  change (¬ (H.Adj (z 0) (z 20))) → False
                  intro h1
                  exact h1 (hz 0 20 (by decide +kernel))
                ·
                  apply sat_one (c := [.neg 0, .neg 25, .neg 3685])
                  change (m (z 0)) → (m (z 25)) → (H.Adj (z 0) (z 25)) → False
                  intro h1 h2 h3
                  exact h.independent (z 0) (z 25) h1 h2 h3
        ·
          apply sat_and (a := node31) (b := node42)
          ·
            apply sat_and (a := node25) (b := node30)
            ·
              apply sat_and (a := node21) (b := node24)
              ·
                apply sat_one (c := [.pos 3685])
                change (¬ (H.Adj (z 0) (z 25))) → False
                intro h1
                exact h1 (hz 0 25 (by decide +kernel))
              ·
                apply sat_and (a := node22) (b := node23)
                ·
                  apply sat_one (c := [.neg 0, .neg 30, .neg 3690])
                  change (m (z 0)) → (m (z 30)) → (H.Adj (z 0) (z 30)) → False
                  intro h1 h2 h3
                  exact h.independent (z 0) (z 30) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 3690])
                  change (¬ (H.Adj (z 0) (z 30))) → False
                  intro h1
                  exact h1 (hz 0 30 (by decide +kernel))
            ·
              apply sat_and (a := node26) (b := node29)
              ·
                apply sat_one (c := [.pos 3705])
                change (¬ (H.Adj (z 0) (z 45))) → False
                intro h1
                exact h1 (hz 0 45 (by decide +kernel))
              ·
                apply sat_and (a := node27) (b := node28)
                ·
                  apply sat_one (c := [.neg 123, .neg 1, .pos 3])
                  change (z 1 = z 3) → (m (z 1)) → (¬ (m (z 3))) → False
                  intro h1 h2 h3
                  exact h3 (h1 ▸ h2)
                ·
                  apply sat_one (c := [.neg 123, .pos 1, .neg 3])
                  change (z 1 = z 3) → (¬ (m (z 1))) → (m (z 3)) → False
                  intro h1 h2 h3
                  exact h2 (h1.symm ▸ h3)
          ·
            apply sat_and (a := node36) (b := node41)
            ·
              apply sat_and (a := node32) (b := node35)
              ·
                apply sat_one (c := [.neg 1, .neg 3, .neg 3723])
                change (m (z 1)) → (m (z 3)) → (H.Adj (z 1) (z 3)) → False
                intro h1 h2 h3
                exact h.independent (z 1) (z 3) h1 h2 h3
              ·
                apply sat_and (a := node33) (b := node34)
                ·
                  apply sat_one (c := [.neg 1, .neg 15, .neg 3735])
                  change (m (z 1)) → (m (z 15)) → (H.Adj (z 1) (z 15)) → False
                  intro h1 h2 h3
                  exact h.independent (z 1) (z 15) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 3735])
                  change (¬ (H.Adj (z 1) (z 15))) → False
                  intro h1
                  exact h1 (hz 1 15 (by decide +kernel))
            ·
              apply sat_and (a := node37) (b := node40)
              ·
                apply sat_one (c := [.neg 1, .neg 20, .neg 3740])
                change (m (z 1)) → (m (z 20)) → (H.Adj (z 1) (z 20)) → False
                intro h1 h2 h3
                exact h.independent (z 1) (z 20) h1 h2 h3
              ·
                apply sat_and (a := node38) (b := node39)
                ·
                  apply sat_one (c := [.pos 3740])
                  change (¬ (H.Adj (z 1) (z 20))) → False
                  intro h1
                  exact h1 (hz 1 20 (by decide +kernel))
                ·
                  apply sat_one (c := [.neg 141, .neg 3741])
                  change (z 1 = z 21) → (H.Adj (z 1) (z 21)) → False
                  intro h1 h2
                  exact h2.ne h1
      ·
        apply sat_and (a := node65) (b := node88)
        ·
          apply sat_and (a := node53) (b := node64)
          ·
            apply sat_and (a := node47) (b := node52)
            ·
              apply sat_and (a := node45) (b := node46)
              ·
                apply sat_one (c := [.neg 1, .neg 21, .neg 3741])
                change (m (z 1)) → (m (z 21)) → (H.Adj (z 1) (z 21)) → False
                intro h1 h2 h3
                exact h.independent (z 1) (z 21) h1 h2 h3
              ·
                apply sat_one (c := [.pos 3741])
                change (¬ (H.Adj (z 1) (z 21))) → False
                intro h1
                exact h1 (hz 1 21 (by decide +kernel))
            ·
              apply sat_and (a := node48) (b := node51)
              ·
                apply sat_one (c := [.neg 1, .neg 22, .neg 3742])
                change (m (z 1)) → (m (z 22)) → (H.Adj (z 1) (z 22)) → False
                intro h1 h2 h3
                exact h.independent (z 1) (z 22) h1 h2 h3
              ·
                apply sat_and (a := node49) (b := node50)
                ·
                  apply sat_one (c := [.pos 3742])
                  change (¬ (H.Adj (z 1) (z 22))) → False
                  intro h1
                  exact h1 (hz 1 22 (by decide +kernel))
                ·
                  apply sat_one (c := [.neg 1, .neg 23, .neg 3743])
                  change (m (z 1)) → (m (z 23)) → (H.Adj (z 1) (z 23)) → False
                  intro h1 h2 h3
                  exact h.independent (z 1) (z 23) h1 h2 h3
          ·
            apply sat_and (a := node58) (b := node63)
            ·
              apply sat_and (a := node54) (b := node57)
              ·
                apply sat_one (c := [.pos 3743])
                change (¬ (H.Adj (z 1) (z 23))) → False
                intro h1
                exact h1 (hz 1 23 (by decide +kernel))
              ·
                apply sat_and (a := node55) (b := node56)
                ·
                  apply sat_one (c := [.neg 1, .neg 24, .neg 3744])
                  change (m (z 1)) → (m (z 24)) → (H.Adj (z 1) (z 24)) → False
                  intro h1 h2 h3
                  exact h.independent (z 1) (z 24) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 3744])
                  change (¬ (H.Adj (z 1) (z 24))) → False
                  intro h1
                  exact h1 (hz 1 24 (by decide +kernel))
            ·
              apply sat_and (a := node59) (b := node62)
              ·
                apply sat_one (c := [.neg 145, .neg 3745])
                change (z 1 = z 25) → (H.Adj (z 1) (z 25)) → False
                intro h1 h2
                exact h2.ne h1
              ·
                apply sat_and (a := node60) (b := node61)
                ·
                  apply sat_one (c := [.neg 1, .neg 25, .neg 3745])
                  change (m (z 1)) → (m (z 25)) → (H.Adj (z 1) (z 25)) → False
                  intro h1 h2 h3
                  exact h.independent (z 1) (z 25) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 3745])
                  change (¬ (H.Adj (z 1) (z 25))) → False
                  intro h1
                  exact h1 (hz 1 25 (by decide +kernel))
        ·
          apply sat_and (a := node76) (b := node87)
          ·
            apply sat_and (a := node70) (b := node75)
            ·
              apply sat_and (a := node66) (b := node69)
              ·
                apply sat_one (c := [.neg 150, .neg 3750])
                change (z 1 = z 30) → (H.Adj (z 1) (z 30)) → False
                intro h1 h2
                exact h2.ne h1
              ·
                apply sat_and (a := node67) (b := node68)
                ·
                  apply sat_one (c := [.neg 1, .neg 30, .neg 3750])
                  change (m (z 1)) → (m (z 30)) → (H.Adj (z 1) (z 30)) → False
                  intro h1 h2 h3
                  exact h.independent (z 1) (z 30) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 3750])
                  change (¬ (H.Adj (z 1) (z 30))) → False
                  intro h1
                  exact h1 (hz 1 30 (by decide +kernel))
            ·
              apply sat_and (a := node71) (b := node74)
              ·
                apply sat_one (c := [.neg 158, .neg 1, .pos 38])
                change (z 1 = z 38) → (m (z 1)) → (¬ (m (z 38))) → False
                intro h1 h2 h3
                exact h3 (h1 ▸ h2)
              ·
                apply sat_and (a := node72) (b := node73)
                ·
                  apply sat_one (c := [.neg 1, .neg 45, .neg 3765])
                  change (m (z 1)) → (m (z 45)) → (H.Adj (z 1) (z 45)) → False
                  intro h1 h2 h3
                  exact h.independent (z 1) (z 45) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 3765])
                  change (¬ (H.Adj (z 1) (z 45))) → False
                  intro h1
                  exact h1 (hz 1 45 (by decide +kernel))
          ·
            apply sat_and (a := node81) (b := node86)
            ·
              apply sat_and (a := node77) (b := node80)
              ·
                apply sat_one (c := [.neg 168, .pos 1, .neg 48])
                change (z 1 = z 48) → (¬ (m (z 1))) → (m (z 48)) → False
                intro h1 h2 h3
                exact h2 (h1.symm ▸ h3)
              ·
                apply sat_and (a := node78) (b := node79)
                ·
                  apply sat_one (c := [.neg 2, .neg 15, .neg 3795])
                  change (m (z 2)) → (m (z 15)) → (H.Adj (z 2) (z 15)) → False
                  intro h1 h2 h3
                  exact h.independent (z 2) (z 15) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 3795])
                  change (¬ (H.Adj (z 2) (z 15))) → False
                  intro h1
                  exact h1 (hz 2 15 (by decide +kernel))
            ·
              apply sat_and (a := node82) (b := node85)
              ·
                apply sat_one (c := [.neg 2, .neg 20, .neg 3800])
                change (m (z 2)) → (m (z 20)) → (H.Adj (z 2) (z 20)) → False
                intro h1 h2 h3
                exact h.independent (z 2) (z 20) h1 h2 h3
              ·
                apply sat_and (a := node83) (b := node84)
                ·
                  apply sat_one (c := [.pos 3800])
                  change (¬ (H.Adj (z 2) (z 20))) → False
                  intro h1
                  exact h1 (hz 2 20 (by decide +kernel))
                ·
                  apply sat_one (c := [.neg 2, .neg 25, .neg 3805])
                  change (m (z 2)) → (m (z 25)) → (H.Adj (z 2) (z 25)) → False
                  intro h1 h2 h3
                  exact h.independent (z 2) (z 25) h1 h2 h3
    ·
      apply sat_and (a := node135) (b := node182)
      ·
        apply sat_and (a := node111) (b := node134)
        ·
          apply sat_and (a := node99) (b := node110)
          ·
            apply sat_and (a := node93) (b := node98)
            ·
              apply sat_and (a := node91) (b := node92)
              ·
                apply sat_one (c := [.pos 3805])
                change (¬ (H.Adj (z 2) (z 25))) → False
                intro h1
                exact h1 (hz 2 25 (by decide +kernel))
              ·
                apply sat_one (c := [.neg 2, .neg 26, .neg 3806])
                change (m (z 2)) → (m (z 26)) → (H.Adj (z 2) (z 26)) → False
                intro h1 h2 h3
                exact h.independent (z 2) (z 26) h1 h2 h3
            ·
              apply sat_and (a := node94) (b := node97)
              ·
                apply sat_one (c := [.pos 3806])
                change (¬ (H.Adj (z 2) (z 26))) → False
                intro h1
                exact h1 (hz 2 26 (by decide +kernel))
              ·
                apply sat_and (a := node95) (b := node96)
                ·
                  apply sat_one (c := [.neg 207, .neg 3807])
                  change (z 2 = z 27) → (H.Adj (z 2) (z 27)) → False
                  intro h1 h2
                  exact h2.ne h1
                ·
                  apply sat_one (c := [.neg 2, .neg 27, .neg 3807])
                  change (m (z 2)) → (m (z 27)) → (H.Adj (z 2) (z 27)) → False
                  intro h1 h2 h3
                  exact h.independent (z 2) (z 27) h1 h2 h3
          ·
            apply sat_and (a := node104) (b := node109)
            ·
              apply sat_and (a := node100) (b := node103)
              ·
                apply sat_one (c := [.pos 3807])
                change (¬ (H.Adj (z 2) (z 27))) → False
                intro h1
                exact h1 (hz 2 27 (by decide +kernel))
              ·
                apply sat_and (a := node101) (b := node102)
                ·
                  apply sat_one (c := [.neg 2, .neg 28, .neg 3808])
                  change (m (z 2)) → (m (z 28)) → (H.Adj (z 2) (z 28)) → False
                  intro h1 h2 h3
                  exact h.independent (z 2) (z 28) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 3808])
                  change (¬ (H.Adj (z 2) (z 28))) → False
                  intro h1
                  exact h1 (hz 2 28 (by decide +kernel))
            ·
              apply sat_and (a := node105) (b := node108)
              ·
                apply sat_one (c := [.neg 2, .neg 29, .neg 3809])
                change (m (z 2)) → (m (z 29)) → (H.Adj (z 2) (z 29)) → False
                intro h1 h2 h3
                exact h.independent (z 2) (z 29) h1 h2 h3
              ·
                apply sat_and (a := node106) (b := node107)
                ·
                  apply sat_one (c := [.pos 3809])
                  change (¬ (H.Adj (z 2) (z 29))) → False
                  intro h1
                  exact h1 (hz 2 29 (by decide +kernel))
                ·
                  apply sat_one (c := [.neg 2, .neg 30, .neg 3810])
                  change (m (z 2)) → (m (z 30)) → (H.Adj (z 2) (z 30)) → False
                  intro h1 h2 h3
                  exact h.independent (z 2) (z 30) h1 h2 h3
        ·
          apply sat_and (a := node122) (b := node133)
          ·
            apply sat_and (a := node116) (b := node121)
            ·
              apply sat_and (a := node112) (b := node115)
              ·
                apply sat_one (c := [.pos 3810])
                change (¬ (H.Adj (z 2) (z 30))) → False
                intro h1
                exact h1 (hz 2 30 (by decide +kernel))
              ·
                apply sat_and (a := node113) (b := node114)
                ·
                  apply sat_one (c := [.neg 225, .neg 3825])
                  change (z 2 = z 45) → (H.Adj (z 2) (z 45)) → False
                  intro h1 h2
                  exact h2.ne h1
                ·
                  apply sat_one (c := [.neg 2, .neg 45, .neg 3825])
                  change (m (z 2)) → (m (z 45)) → (H.Adj (z 2) (z 45)) → False
                  intro h1 h2 h3
                  exact h.independent (z 2) (z 45) h1 h2 h3
            ·
              apply sat_and (a := node117) (b := node120)
              ·
                apply sat_one (c := [.pos 3825])
                change (¬ (H.Adj (z 2) (z 45))) → False
                intro h1
                exact h1 (hz 2 45 (by decide +kernel))
              ·
                apply sat_and (a := node118) (b := node119)
                ·
                  apply sat_one (c := [.neg 252, .neg 3852])
                  change (z 3 = z 12) → (H.Adj (z 3) (z 12)) → False
                  intro h1 h2
                  exact h2.ne h1
                ·
                  apply sat_one (c := [.neg 3, .neg 15, .neg 3855])
                  change (m (z 3)) → (m (z 15)) → (H.Adj (z 3) (z 15)) → False
                  intro h1 h2 h3
                  exact h.independent (z 3) (z 15) h1 h2 h3
          ·
            apply sat_and (a := node127) (b := node132)
            ·
              apply sat_and (a := node123) (b := node126)
              ·
                apply sat_one (c := [.pos 3855])
                change (¬ (H.Adj (z 3) (z 15))) → False
                intro h1
                exact h1 (hz 3 15 (by decide +kernel))
              ·
                apply sat_and (a := node124) (b := node125)
                ·
                  apply sat_one (c := [.neg 260, .neg 3860])
                  change (z 3 = z 20) → (H.Adj (z 3) (z 20)) → False
                  intro h1 h2
                  exact h2.ne h1
                ·
                  apply sat_one (c := [.neg 3, .neg 20, .neg 3860])
                  change (m (z 3)) → (m (z 20)) → (H.Adj (z 3) (z 20)) → False
                  intro h1 h2 h3
                  exact h.independent (z 3) (z 20) h1 h2 h3
            ·
              apply sat_and (a := node128) (b := node131)
              ·
                apply sat_one (c := [.pos 3860])
                change (¬ (H.Adj (z 3) (z 20))) → False
                intro h1
                exact h1 (hz 3 20 (by decide +kernel))
              ·
                apply sat_and (a := node129) (b := node130)
                ·
                  apply sat_one (c := [.neg 3, .neg 25, .neg 3865])
                  change (m (z 3)) → (m (z 25)) → (H.Adj (z 3) (z 25)) → False
                  intro h1 h2 h3
                  exact h.independent (z 3) (z 25) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 3865])
                  change (¬ (H.Adj (z 3) (z 25))) → False
                  intro h1
                  exact h1 (hz 3 25 (by decide +kernel))
      ·
        apply sat_and (a := node158) (b := node181)
        ·
          apply sat_and (a := node146) (b := node157)
          ·
            apply sat_and (a := node140) (b := node145)
            ·
              apply sat_and (a := node136) (b := node139)
              ·
                apply sat_one (c := [.neg 3, .neg 30, .neg 3870])
                change (m (z 3)) → (m (z 30)) → (H.Adj (z 3) (z 30)) → False
                intro h1 h2 h3
                exact h.independent (z 3) (z 30) h1 h2 h3
              ·
                apply sat_and (a := node137) (b := node138)
                ·
                  apply sat_one (c := [.pos 3870])
                  change (¬ (H.Adj (z 3) (z 30))) → False
                  intro h1
                  exact h1 (hz 3 30 (by decide +kernel))
                ·
                  apply sat_one (c := [.pos 3871])
                  change (¬ (H.Adj (z 3) (z 31))) → False
                  intro h1
                  exact h1 (hz 3 31 (by decide +kernel))
            ·
              apply sat_and (a := node141) (b := node144)
              ·
                apply sat_one (c := [.neg 3, .neg 32, .neg 3872])
                change (m (z 3)) → (m (z 32)) → (H.Adj (z 3) (z 32)) → False
                intro h1 h2 h3
                exact h.independent (z 3) (z 32) h1 h2 h3
              ·
                apply sat_and (a := node142) (b := node143)
                ·
                  apply sat_one (c := [.pos 3872])
                  change (¬ (H.Adj (z 3) (z 32))) → False
                  intro h1
                  exact h1 (hz 3 32 (by decide +kernel))
                ·
                  apply sat_one (c := [.neg 273, .neg 3873])
                  change (z 3 = z 33) → (H.Adj (z 3) (z 33)) → False
                  intro h1 h2
                  exact h2.ne h1
          ·
            apply sat_and (a := node151) (b := node156)
            ·
              apply sat_and (a := node147) (b := node150)
              ·
                apply sat_one (c := [.neg 3, .neg 33, .neg 3873])
                change (m (z 3)) → (m (z 33)) → (H.Adj (z 3) (z 33)) → False
                intro h1 h2 h3
                exact h.independent (z 3) (z 33) h1 h2 h3
              ·
                apply sat_and (a := node148) (b := node149)
                ·
                  apply sat_one (c := [.pos 3873])
                  change (¬ (H.Adj (z 3) (z 33))) → False
                  intro h1
                  exact h1 (hz 3 33 (by decide +kernel))
                ·
                  apply sat_one (c := [.neg 3, .neg 34, .neg 3874])
                  change (m (z 3)) → (m (z 34)) → (H.Adj (z 3) (z 34)) → False
                  intro h1 h2 h3
                  exact h.independent (z 3) (z 34) h1 h2 h3
            ·
              apply sat_and (a := node152) (b := node155)
              ·
                apply sat_one (c := [.pos 3874])
                change (¬ (H.Adj (z 3) (z 34))) → False
                intro h1
                exact h1 (hz 3 34 (by decide +kernel))
              ·
                apply sat_and (a := node153) (b := node154)
                ·
                  apply sat_one (c := [.neg 3, .neg 45, .neg 3885])
                  change (m (z 3)) → (m (z 45)) → (H.Adj (z 3) (z 45)) → False
                  intro h1 h2 h3
                  exact h.independent (z 3) (z 45) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 3885])
                  change (¬ (H.Adj (z 3) (z 45))) → False
                  intro h1
                  exact h1 (hz 3 45 (by decide +kernel))
        ·
          apply sat_and (a := node169) (b := node180)
          ·
            apply sat_and (a := node163) (b := node168)
            ·
              apply sat_and (a := node159) (b := node162)
              ·
                apply sat_one (c := [.neg 295, .neg 3895])
                change (z 3 = z 55) → (H.Adj (z 3) (z 55)) → False
                intro h1 h2
                exact h2.ne h1
              ·
                apply sat_and (a := node160) (b := node161)
                ·
                  apply sat_one (c := [.neg 297, .neg 3, .pos 57])
                  change (z 3 = z 57) → (m (z 3)) → (¬ (m (z 57))) → False
                  intro h1 h2 h3
                  exact h3 (h1 ▸ h2)
                ·
                  apply sat_one (c := [.pos 3915])
                  change (¬ (H.Adj (z 4) (z 15))) → False
                  intro h1
                  exact h1 (hz 4 15 (by decide +kernel))
            ·
              apply sat_and (a := node164) (b := node167)
              ·
                apply sat_one (c := [.neg 320, .neg 3920])
                change (z 4 = z 20) → (H.Adj (z 4) (z 20)) → False
                intro h1 h2
                exact h2.ne h1
              ·
                apply sat_and (a := node165) (b := node166)
                ·
                  apply sat_one (c := [.neg 4, .neg 20, .neg 3920])
                  change (m (z 4)) → (m (z 20)) → (H.Adj (z 4) (z 20)) → False
                  intro h1 h2 h3
                  exact h.independent (z 4) (z 20) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 3920])
                  change (¬ (H.Adj (z 4) (z 20))) → False
                  intro h1
                  exact h1 (hz 4 20 (by decide +kernel))
          ·
            apply sat_and (a := node174) (b := node179)
            ·
              apply sat_and (a := node170) (b := node173)
              ·
                apply sat_one (c := [.neg 325, .neg 3925])
                change (z 4 = z 25) → (H.Adj (z 4) (z 25)) → False
                intro h1 h2
                exact h2.ne h1
              ·
                apply sat_and (a := node171) (b := node172)
                ·
                  apply sat_one (c := [.neg 4, .neg 25, .neg 3925])
                  change (m (z 4)) → (m (z 25)) → (H.Adj (z 4) (z 25)) → False
                  intro h1 h2 h3
                  exact h.independent (z 4) (z 25) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 3925])
                  change (¬ (H.Adj (z 4) (z 25))) → False
                  intro h1
                  exact h1 (hz 4 25 (by decide +kernel))
            ·
              apply sat_and (a := node175) (b := node178)
              ·
                apply sat_one (c := [.neg 4, .neg 30, .neg 3930])
                change (m (z 4)) → (m (z 30)) → (H.Adj (z 4) (z 30)) → False
                intro h1 h2 h3
                exact h.independent (z 4) (z 30) h1 h2 h3
              ·
                apply sat_and (a := node176) (b := node177)
                ·
                  apply sat_one (c := [.pos 3930])
                  change (¬ (H.Adj (z 4) (z 30))) → False
                  intro h1
                  exact h1 (hz 4 30 (by decide +kernel))
                ·
                  apply sat_one (c := [.neg 4, .neg 45, .neg 3945])
                  change (m (z 4)) → (m (z 45)) → (H.Adj (z 4) (z 45)) → False
                  intro h1 h2 h3
                  exact h.independent (z 4) (z 45) h1 h2 h3
  ·
    apply sat_and (a := node277) (b := node370)
    ·
      apply sat_and (a := node229) (b := node276)
      ·
        apply sat_and (a := node205) (b := node228)
        ·
          apply sat_and (a := node193) (b := node204)
          ·
            apply sat_and (a := node187) (b := node192)
            ·
              apply sat_and (a := node185) (b := node186)
              ·
                apply sat_one (c := [.pos 3945])
                change (¬ (H.Adj (z 4) (z 45))) → False
                intro h1
                exact h1 (hz 4 45 (by decide +kernel))
              ·
                apply sat_one (c := [.neg 4, .neg 46, .neg 3946])
                change (m (z 4)) → (m (z 46)) → (H.Adj (z 4) (z 46)) → False
                intro h1 h2 h3
                exact h.independent (z 4) (z 46) h1 h2 h3
            ·
              apply sat_and (a := node188) (b := node191)
              ·
                apply sat_one (c := [.pos 3946])
                change (¬ (H.Adj (z 4) (z 46))) → False
                intro h1
                exact h1 (hz 4 46 (by decide +kernel))
              ·
                apply sat_and (a := node189) (b := node190)
                ·
                  apply sat_one (c := [.neg 4, .neg 47, .neg 3947])
                  change (m (z 4)) → (m (z 47)) → (H.Adj (z 4) (z 47)) → False
                  intro h1 h2 h3
                  exact h.independent (z 4) (z 47) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 3947])
                  change (¬ (H.Adj (z 4) (z 47))) → False
                  intro h1
                  exact h1 (hz 4 47 (by decide +kernel))
          ·
            apply sat_and (a := node198) (b := node203)
            ·
              apply sat_and (a := node194) (b := node197)
              ·
                apply sat_one (c := [.neg 348, .neg 3948])
                change (z 4 = z 48) → (H.Adj (z 4) (z 48)) → False
                intro h1 h2
                exact h2.ne h1
              ·
                apply sat_and (a := node195) (b := node196)
                ·
                  apply sat_one (c := [.neg 4, .neg 48, .neg 3948])
                  change (m (z 4)) → (m (z 48)) → (H.Adj (z 4) (z 48)) → False
                  intro h1 h2 h3
                  exact h.independent (z 4) (z 48) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 3948])
                  change (¬ (H.Adj (z 4) (z 48))) → False
                  intro h1
                  exact h1 (hz 4 48 (by decide +kernel))
            ·
              apply sat_and (a := node199) (b := node202)
              ·
                apply sat_one (c := [.neg 4, .neg 49, .neg 3949])
                change (m (z 4)) → (m (z 49)) → (H.Adj (z 4) (z 49)) → False
                intro h1 h2 h3
                exact h.independent (z 4) (z 49) h1 h2 h3
              ·
                apply sat_and (a := node200) (b := node201)
                ·
                  apply sat_one (c := [.pos 3949])
                  change (¬ (H.Adj (z 4) (z 49))) → False
                  intro h1
                  exact h1 (hz 4 49 (by decide +kernel))
                ·
                  apply sat_one (c := [.pos 3975])
                  change (¬ (H.Adj (z 5) (z 15))) → False
                  intro h1
                  exact h1 (hz 5 15 (by decide +kernel))
        ·
          apply sat_and (a := node216) (b := node227)
          ·
            apply sat_and (a := node210) (b := node215)
            ·
              apply sat_and (a := node206) (b := node209)
              ·
                apply sat_one (c := [.neg 5, .neg 16, .neg 3976])
                change (m (z 5)) → (m (z 16)) → (H.Adj (z 5) (z 16)) → False
                intro h1 h2 h3
                exact h.independent (z 5) (z 16) h1 h2 h3
              ·
                apply sat_and (a := node207) (b := node208)
                ·
                  apply sat_one (c := [.pos 3976])
                  change (¬ (H.Adj (z 5) (z 16))) → False
                  intro h1
                  exact h1 (hz 5 16 (by decide +kernel))
                ·
                  apply sat_one (c := [.neg 5, .neg 17, .neg 3977])
                  change (m (z 5)) → (m (z 17)) → (H.Adj (z 5) (z 17)) → False
                  intro h1 h2 h3
                  exact h.independent (z 5) (z 17) h1 h2 h3
            ·
              apply sat_and (a := node211) (b := node214)
              ·
                apply sat_one (c := [.pos 3977])
                change (¬ (H.Adj (z 5) (z 17))) → False
                intro h1
                exact h1 (hz 5 17 (by decide +kernel))
              ·
                apply sat_and (a := node212) (b := node213)
                ·
                  apply sat_one (c := [.neg 5, .neg 18, .neg 3978])
                  change (m (z 5)) → (m (z 18)) → (H.Adj (z 5) (z 18)) → False
                  intro h1 h2 h3
                  exact h.independent (z 5) (z 18) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 3978])
                  change (¬ (H.Adj (z 5) (z 18))) → False
                  intro h1
                  exact h1 (hz 5 18 (by decide +kernel))
          ·
            apply sat_and (a := node221) (b := node226)
            ·
              apply sat_and (a := node217) (b := node220)
              ·
                apply sat_one (c := [.neg 5, .neg 19, .neg 3979])
                change (m (z 5)) → (m (z 19)) → (H.Adj (z 5) (z 19)) → False
                intro h1 h2 h3
                exact h.independent (z 5) (z 19) h1 h2 h3
              ·
                apply sat_and (a := node218) (b := node219)
                ·
                  apply sat_one (c := [.pos 3979])
                  change (¬ (H.Adj (z 5) (z 19))) → False
                  intro h1
                  exact h1 (hz 5 19 (by decide +kernel))
                ·
                  apply sat_one (c := [.neg 5, .neg 31, .neg 3991])
                  change (m (z 5)) → (m (z 31)) → (H.Adj (z 5) (z 31)) → False
                  intro h1 h2 h3
                  exact h.independent (z 5) (z 31) h1 h2 h3
            ·
              apply sat_and (a := node222) (b := node225)
              ·
                apply sat_one (c := [.pos 3991])
                change (¬ (H.Adj (z 5) (z 31))) → False
                intro h1
                exact h1 (hz 5 31 (by decide +kernel))
              ·
                apply sat_and (a := node223) (b := node224)
                ·
                  apply sat_one (c := [.neg 395, .neg 3995])
                  change (z 5 = z 35) → (H.Adj (z 5) (z 35)) → False
                  intro h1 h2
                  exact h2.ne h1
                ·
                  apply sat_one (c := [.pos 3995])
                  change (¬ (H.Adj (z 5) (z 35))) → False
                  intro h1
                  exact h1 (hz 5 35 (by decide +kernel))
      ·
        apply sat_and (a := node252) (b := node275)
        ·
          apply sat_and (a := node240) (b := node251)
          ·
            apply sat_and (a := node234) (b := node239)
            ·
              apply sat_and (a := node230) (b := node233)
              ·
                apply sat_one (c := [.neg 5, .neg 40, .neg 4000])
                change (m (z 5)) → (m (z 40)) → (H.Adj (z 5) (z 40)) → False
                intro h1 h2 h3
                exact h.independent (z 5) (z 40) h1 h2 h3
              ·
                apply sat_and (a := node231) (b := node232)
                ·
                  apply sat_one (c := [.pos 4000])
                  change (¬ (H.Adj (z 5) (z 40))) → False
                  intro h1
                  exact h1 (hz 5 40 (by decide +kernel))
                ·
                  apply sat_one (c := [.neg 5, .neg 46, .neg 4006])
                  change (m (z 5)) → (m (z 46)) → (H.Adj (z 5) (z 46)) → False
                  intro h1 h2 h3
                  exact h.independent (z 5) (z 46) h1 h2 h3
            ·
              apply sat_and (a := node235) (b := node238)
              ·
                apply sat_one (c := [.pos 4006])
                change (¬ (H.Adj (z 5) (z 46))) → False
                intro h1
                exact h1 (hz 5 46 (by decide +kernel))
              ·
                apply sat_and (a := node236) (b := node237)
                ·
                  apply sat_one (c := [.neg 6, .neg 16, .neg 4036])
                  change (m (z 6)) → (m (z 16)) → (H.Adj (z 6) (z 16)) → False
                  intro h1 h2 h3
                  exact h.independent (z 6) (z 16) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 4036])
                  change (¬ (H.Adj (z 6) (z 16))) → False
                  intro h1
                  exact h1 (hz 6 16 (by decide +kernel))
          ·
            apply sat_and (a := node245) (b := node250)
            ·
              apply sat_and (a := node241) (b := node244)
              ·
                apply sat_one (c := [.neg 6, .neg 30, .neg 4050])
                change (m (z 6)) → (m (z 30)) → (H.Adj (z 6) (z 30)) → False
                intro h1 h2 h3
                exact h.independent (z 6) (z 30) h1 h2 h3
              ·
                apply sat_and (a := node242) (b := node243)
                ·
                  apply sat_one (c := [.pos 4050])
                  change (¬ (H.Adj (z 6) (z 30))) → False
                  intro h1
                  exact h1 (hz 6 30 (by decide +kernel))
                ·
                  apply sat_one (c := [.neg 6, .neg 32, .neg 4052])
                  change (m (z 6)) → (m (z 32)) → (H.Adj (z 6) (z 32)) → False
                  intro h1 h2 h3
                  exact h.independent (z 6) (z 32) h1 h2 h3
            ·
              apply sat_and (a := node246) (b := node249)
              ·
                apply sat_one (c := [.pos 4052])
                change (¬ (H.Adj (z 6) (z 32))) → False
                intro h1
                exact h1 (hz 6 32 (by decide +kernel))
              ·
                apply sat_and (a := node247) (b := node248)
                ·
                  apply sat_one (c := [.neg 6, .neg 33, .neg 4053])
                  change (m (z 6)) → (m (z 33)) → (H.Adj (z 6) (z 33)) → False
                  intro h1 h2 h3
                  exact h.independent (z 6) (z 33) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 4053])
                  change (¬ (H.Adj (z 6) (z 33))) → False
                  intro h1
                  exact h1 (hz 6 33 (by decide +kernel))
        ·
          apply sat_and (a := node263) (b := node274)
          ·
            apply sat_and (a := node257) (b := node262)
            ·
              apply sat_and (a := node253) (b := node256)
              ·
                apply sat_one (c := [.neg 454, .neg 4054])
                change (z 6 = z 34) → (H.Adj (z 6) (z 34)) → False
                intro h1 h2
                exact h2.ne h1
              ·
                apply sat_and (a := node254) (b := node255)
                ·
                  apply sat_one (c := [.neg 6, .neg 34, .neg 4054])
                  change (m (z 6)) → (m (z 34)) → (H.Adj (z 6) (z 34)) → False
                  intro h1 h2 h3
                  exact h.independent (z 6) (z 34) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 4054])
                  change (¬ (H.Adj (z 6) (z 34))) → False
                  intro h1
                  exact h1 (hz 6 34 (by decide +kernel))
            ·
              apply sat_and (a := node258) (b := node261)
              ·
                apply sat_one (c := [.neg 6, .neg 35, .neg 4055])
                change (m (z 6)) → (m (z 35)) → (H.Adj (z 6) (z 35)) → False
                intro h1 h2 h3
                exact h.independent (z 6) (z 35) h1 h2 h3
              ·
                apply sat_and (a := node259) (b := node260)
                ·
                  apply sat_one (c := [.pos 4055])
                  change (¬ (H.Adj (z 6) (z 35))) → False
                  intro h1
                  exact h1 (hz 6 35 (by decide +kernel))
                ·
                  apply sat_one (c := [.pos 4060])
                  change (¬ (H.Adj (z 6) (z 40))) → False
                  intro h1
                  exact h1 (hz 6 40 (by decide +kernel))
          ·
            apply sat_and (a := node268) (b := node273)
            ·
              apply sat_and (a := node264) (b := node267)
              ·
                apply sat_one (c := [.neg 6, .neg 46, .neg 4066])
                change (m (z 6)) → (m (z 46)) → (H.Adj (z 6) (z 46)) → False
                intro h1 h2 h3
                exact h.independent (z 6) (z 46) h1 h2 h3
              ·
                apply sat_and (a := node265) (b := node266)
                ·
                  apply sat_one (c := [.pos 4066])
                  change (¬ (H.Adj (z 6) (z 46))) → False
                  intro h1
                  exact h1 (hz 6 46 (by decide +kernel))
                ·
                  apply sat_one (c := [.neg 496, .neg 4096])
                  change (z 7 = z 16) → (H.Adj (z 7) (z 16)) → False
                  intro h1 h2
                  exact h2.ne h1
            ·
              apply sat_and (a := node269) (b := node272)
              ·
                apply sat_one (c := [.neg 7, .neg 16, .neg 4096])
                change (m (z 7)) → (m (z 16)) → (H.Adj (z 7) (z 16)) → False
                intro h1 h2 h3
                exact h.independent (z 7) (z 16) h1 h2 h3
              ·
                apply sat_and (a := node270) (b := node271)
                ·
                  apply sat_one (c := [.pos 4096])
                  change (¬ (H.Adj (z 7) (z 16))) → False
                  intro h1
                  exact h1 (hz 7 16 (by decide +kernel))
                ·
                  apply sat_one (c := [.pos 4111])
                  change (¬ (H.Adj (z 7) (z 31))) → False
                  intro h1
                  exact h1 (hz 7 31 (by decide +kernel))
    ·
      apply sat_and (a := node322) (b := node369)
      ·
        apply sat_and (a := node298) (b := node321)
        ·
          apply sat_and (a := node286) (b := node297)
          ·
            apply sat_and (a := node280) (b := node285)
            ·
              apply sat_and (a := node278) (b := node279)
              ·
                apply sat_one (c := [.neg 516, .neg 4116])
                change (z 7 = z 36) → (H.Adj (z 7) (z 36)) → False
                intro h1 h2
                exact h2.ne h1
              ·
                apply sat_one (c := [.pos 4116])
                change (¬ (H.Adj (z 7) (z 36))) → False
                intro h1
                exact h1 (hz 7 36 (by decide +kernel))
            ·
              apply sat_and (a := node281) (b := node284)
              ·
                apply sat_one (c := [.pos 4117])
                change (¬ (H.Adj (z 7) (z 37))) → False
                intro h1
                exact h1 (hz 7 37 (by decide +kernel))
              ·
                apply sat_and (a := node282) (b := node283)
                ·
                  apply sat_one (c := [.neg 7, .neg 38, .neg 4118])
                  change (m (z 7)) → (m (z 38)) → (H.Adj (z 7) (z 38)) → False
                  intro h1 h2 h3
                  exact h.independent (z 7) (z 38) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 4118])
                  change (¬ (H.Adj (z 7) (z 38))) → False
                  intro h1
                  exact h1 (hz 7 38 (by decide +kernel))
          ·
            apply sat_and (a := node291) (b := node296)
            ·
              apply sat_and (a := node287) (b := node290)
              ·
                apply sat_one (c := [.neg 7, .neg 39, .neg 4119])
                change (m (z 7)) → (m (z 39)) → (H.Adj (z 7) (z 39)) → False
                intro h1 h2 h3
                exact h.independent (z 7) (z 39) h1 h2 h3
              ·
                apply sat_and (a := node288) (b := node289)
                ·
                  apply sat_one (c := [.pos 4119])
                  change (¬ (H.Adj (z 7) (z 39))) → False
                  intro h1
                  exact h1 (hz 7 39 (by decide +kernel))
                ·
                  apply sat_one (c := [.neg 7, .neg 40, .neg 4120])
                  change (m (z 7)) → (m (z 40)) → (H.Adj (z 7) (z 40)) → False
                  intro h1 h2 h3
                  exact h.independent (z 7) (z 40) h1 h2 h3
            ·
              apply sat_and (a := node292) (b := node295)
              ·
                apply sat_one (c := [.pos 4120])
                change (¬ (H.Adj (z 7) (z 40))) → False
                intro h1
                exact h1 (hz 7 40 (by decide +kernel))
              ·
                apply sat_and (a := node293) (b := node294)
                ·
                  apply sat_one (c := [.neg 7, .neg 46, .neg 4126])
                  change (m (z 7)) → (m (z 46)) → (H.Adj (z 7) (z 46)) → False
                  intro h1 h2 h3
                  exact h.independent (z 7) (z 46) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 4126])
                  change (¬ (H.Adj (z 7) (z 46))) → False
                  intro h1
                  exact h1 (hz 7 46 (by decide +kernel))
        ·
          apply sat_and (a := node309) (b := node320)
          ·
            apply sat_and (a := node303) (b := node308)
            ·
              apply sat_and (a := node299) (b := node302)
              ·
                apply sat_one (c := [.neg 8, .neg 16, .neg 4156])
                change (m (z 8)) → (m (z 16)) → (H.Adj (z 8) (z 16)) → False
                intro h1 h2 h3
                exact h.independent (z 8) (z 16) h1 h2 h3
              ·
                apply sat_and (a := node300) (b := node301)
                ·
                  apply sat_one (c := [.pos 4156])
                  change (¬ (H.Adj (z 8) (z 16))) → False
                  intro h1
                  exact h1 (hz 8 16 (by decide +kernel))
                ·
                  apply sat_one (c := [.neg 8, .neg 31, .neg 4171])
                  change (m (z 8)) → (m (z 31)) → (H.Adj (z 8) (z 31)) → False
                  intro h1 h2 h3
                  exact h.independent (z 8) (z 31) h1 h2 h3
            ·
              apply sat_and (a := node304) (b := node307)
              ·
                apply sat_one (c := [.pos 4171])
                change (¬ (H.Adj (z 8) (z 31))) → False
                intro h1
                exact h1 (hz 8 31 (by decide +kernel))
              ·
                apply sat_and (a := node305) (b := node306)
                ·
                  apply sat_one (c := [.neg 8, .neg 35, .neg 4175])
                  change (m (z 8)) → (m (z 35)) → (H.Adj (z 8) (z 35)) → False
                  intro h1 h2 h3
                  exact h.independent (z 8) (z 35) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 4175])
                  change (¬ (H.Adj (z 8) (z 35))) → False
                  intro h1
                  exact h1 (hz 8 35 (by decide +kernel))
          ·
            apply sat_and (a := node314) (b := node319)
            ·
              apply sat_and (a := node310) (b := node313)
              ·
                apply sat_one (c := [.neg 8, .neg 40, .neg 4180])
                change (m (z 8)) → (m (z 40)) → (H.Adj (z 8) (z 40)) → False
                intro h1 h2 h3
                exact h.independent (z 8) (z 40) h1 h2 h3
              ·
                apply sat_and (a := node311) (b := node312)
                ·
                  apply sat_one (c := [.pos 4180])
                  change (¬ (H.Adj (z 8) (z 40))) → False
                  intro h1
                  exact h1 (hz 8 40 (by decide +kernel))
                ·
                  apply sat_one (c := [.neg 8, .neg 41, .neg 4181])
                  change (m (z 8)) → (m (z 41)) → (H.Adj (z 8) (z 41)) → False
                  intro h1 h2 h3
                  exact h.independent (z 8) (z 41) h1 h2 h3
            ·
              apply sat_and (a := node315) (b := node318)
              ·
                apply sat_one (c := [.pos 4181])
                change (¬ (H.Adj (z 8) (z 41))) → False
                intro h1
                exact h1 (hz 8 41 (by decide +kernel))
              ·
                apply sat_and (a := node316) (b := node317)
                ·
                  apply sat_one (c := [.neg 8, .neg 42, .neg 4182])
                  change (m (z 8)) → (m (z 42)) → (H.Adj (z 8) (z 42)) → False
                  intro h1 h2 h3
                  exact h.independent (z 8) (z 42) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 4182])
                  change (¬ (H.Adj (z 8) (z 42))) → False
                  intro h1
                  exact h1 (hz 8 42 (by decide +kernel))
      ·
        apply sat_and (a := node345) (b := node368)
        ·
          apply sat_and (a := node333) (b := node344)
          ·
            apply sat_and (a := node327) (b := node332)
            ·
              apply sat_and (a := node323) (b := node326)
              ·
                apply sat_one (c := [.neg 8, .neg 43, .neg 4183])
                change (m (z 8)) → (m (z 43)) → (H.Adj (z 8) (z 43)) → False
                intro h1 h2 h3
                exact h.independent (z 8) (z 43) h1 h2 h3
              ·
                apply sat_and (a := node324) (b := node325)
                ·
                  apply sat_one (c := [.pos 4183])
                  change (¬ (H.Adj (z 8) (z 43))) → False
                  intro h1
                  exact h1 (hz 8 43 (by decide +kernel))
                ·
                  apply sat_one (c := [.neg 8, .neg 44, .neg 4184])
                  change (m (z 8)) → (m (z 44)) → (H.Adj (z 8) (z 44)) → False
                  intro h1 h2 h3
                  exact h.independent (z 8) (z 44) h1 h2 h3
            ·
              apply sat_and (a := node328) (b := node331)
              ·
                apply sat_one (c := [.pos 4184])
                change (¬ (H.Adj (z 8) (z 44))) → False
                intro h1
                exact h1 (hz 8 44 (by decide +kernel))
              ·
                apply sat_and (a := node329) (b := node330)
                ·
                  apply sat_one (c := [.neg 586, .neg 4186])
                  change (z 8 = z 46) → (H.Adj (z 8) (z 46)) → False
                  intro h1 h2
                  exact h2.ne h1
                ·
                  apply sat_one (c := [.pos 4186])
                  change (¬ (H.Adj (z 8) (z 46))) → False
                  intro h1
                  exact h1 (hz 8 46 (by decide +kernel))
          ·
            apply sat_and (a := node338) (b := node343)
            ·
              apply sat_and (a := node334) (b := node337)
              ·
                apply sat_one (c := [.neg 9, .neg 16, .neg 4216])
                change (m (z 9)) → (m (z 16)) → (H.Adj (z 9) (z 16)) → False
                intro h1 h2 h3
                exact h.independent (z 9) (z 16) h1 h2 h3
              ·
                apply sat_and (a := node335) (b := node336)
                ·
                  apply sat_one (c := [.pos 4216])
                  change (¬ (H.Adj (z 9) (z 16))) → False
                  intro h1
                  exact h1 (hz 9 16 (by decide +kernel))
                ·
                  apply sat_one (c := [.neg 9, .neg 31, .neg 4231])
                  change (m (z 9)) → (m (z 31)) → (H.Adj (z 9) (z 31)) → False
                  intro h1 h2 h3
                  exact h.independent (z 9) (z 31) h1 h2 h3
            ·
              apply sat_and (a := node339) (b := node342)
              ·
                apply sat_one (c := [.pos 4231])
                change (¬ (H.Adj (z 9) (z 31))) → False
                intro h1
                exact h1 (hz 9 31 (by decide +kernel))
              ·
                apply sat_and (a := node340) (b := node341)
                ·
                  apply sat_one (c := [.pos 4235])
                  change (¬ (H.Adj (z 9) (z 35))) → False
                  intro h1
                  exact h1 (hz 9 35 (by decide +kernel))
                ·
                  apply sat_one (c := [.neg 640, .neg 4240])
                  change (z 9 = z 40) → (H.Adj (z 9) (z 40)) → False
                  intro h1 h2
                  exact h2.ne h1
        ·
          apply sat_and (a := node356) (b := node367)
          ·
            apply sat_and (a := node350) (b := node355)
            ·
              apply sat_and (a := node346) (b := node349)
              ·
                apply sat_one (c := [.neg 9, .neg 40, .neg 4240])
                change (m (z 9)) → (m (z 40)) → (H.Adj (z 9) (z 40)) → False
                intro h1 h2 h3
                exact h.independent (z 9) (z 40) h1 h2 h3
              ·
                apply sat_and (a := node347) (b := node348)
                ·
                  apply sat_one (c := [.pos 4240])
                  change (¬ (H.Adj (z 9) (z 40))) → False
                  intro h1
                  exact h1 (hz 9 40 (by decide +kernel))
                ·
                  apply sat_one (c := [.neg 9, .neg 45, .neg 4245])
                  change (m (z 9)) → (m (z 45)) → (H.Adj (z 9) (z 45)) → False
                  intro h1 h2 h3
                  exact h.independent (z 9) (z 45) h1 h2 h3
            ·
              apply sat_and (a := node351) (b := node354)
              ·
                apply sat_one (c := [.pos 4245])
                change (¬ (H.Adj (z 9) (z 45))) → False
                intro h1
                exact h1 (hz 9 45 (by decide +kernel))
              ·
                apply sat_and (a := node352) (b := node353)
                ·
                  apply sat_one (c := [.neg 9, .neg 46, .neg 4246])
                  change (m (z 9)) → (m (z 46)) → (H.Adj (z 9) (z 46)) → False
                  intro h1 h2 h3
                  exact h.independent (z 9) (z 46) h1 h2 h3
                ·
                  apply sat_one (c := [.pos 4246])
                  change (¬ (H.Adj (z 9) (z 46))) → False
                  intro h1
                  exact h1 (hz 9 46 (by decide +kernel))
          ·
            apply sat_and (a := node361) (b := node366)
            ·
              apply sat_and (a := node357) (b := node360)
              ·
                apply sat_one (c := [.neg 9, .neg 47, .neg 4247])
                change (m (z 9)) → (m (z 47)) → (H.Adj (z 9) (z 47)) → False
                intro h1 h2 h3
                exact h.independent (z 9) (z 47) h1 h2 h3
              ·
                apply sat_and (a := node358) (b := node359)
                ·
                  apply sat_one (c := [.pos 4247])
                  change (¬ (H.Adj (z 9) (z 47))) → False
                  intro h1
                  exact h1 (hz 9 47 (by decide +kernel))
                ·
                  apply sat_one (c := [.neg 9, .neg 48, .neg 4248])
                  change (m (z 9)) → (m (z 48)) → (H.Adj (z 9) (z 48)) → False
                  intro h1 h2 h3
                  exact h.independent (z 9) (z 48) h1 h2 h3
            ·
              apply sat_and (a := node362) (b := node365)
              ·
                apply sat_one (c := [.pos 4248])
                change (¬ (H.Adj (z 9) (z 48))) → False
                intro h1
                exact h1 (hz 9 48 (by decide +kernel))
              ·
                apply sat_and (a := node363) (b := node364)
                ·
                  apply sat_one (c := [.pos 4249])
                  change (¬ (H.Adj (z 9) (z 49))) → False
                  intro h1
                  exact h1 (hz 9 49 (by decide +kernel))
                ·
                  apply sat_one (c := [.neg 10, .neg 15, .neg 4275])
                  change (m (z 10)) → (m (z 15)) → (H.Adj (z 10) (z 15)) → False
                  intro h1 h2 h3
                  exact h.independent (z 10) (z 15) h1 h2 h3
end Erdos595OneEdgeLocal
