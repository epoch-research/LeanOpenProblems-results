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

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.pos 3675]) := by
  apply sat_one
  change (¬ (H.Adj (z 0) (z 15))) → False
  intro h1
  exact h1 (hz 0 15 (by decide +kernel))

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 0, .neg 16, .neg 3676]) := by
  apply sat_one
  change (m (z 0)) → (m (z 16)) → (H.Adj (z 0) (z 16)) → False
  intro h1 h2 h3
  exact h.independent (z 0) (z 16) h1 h2 h3

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.pos 3676]) := by
  apply sat_one
  change (¬ (H.Adj (z 0) (z 16))) → False
  intro h1
  exact h1 (hz 0 16 (by decide +kernel))

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 0, .neg 17, .neg 3677]) := by
  apply sat_one
  change (m (z 0)) → (m (z 17)) → (H.Adj (z 0) (z 17)) → False
  intro h1 h2 h3
  exact h.independent (z 0) (z 17) h1 h2 h3

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.pos 3677]) := by
  apply sat_one
  change (¬ (H.Adj (z 0) (z 17))) → False
  intro h1
  exact h1 (hz 0 17 (by decide +kernel))

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 0, .neg 18, .neg 3678]) := by
  apply sat_one
  change (m (z 0)) → (m (z 18)) → (H.Adj (z 0) (z 18)) → False
  intro h1 h2 h3
  exact h.independent (z 0) (z 18) h1 h2 h3

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.pos 3678]) := by
  apply sat_one
  change (¬ (H.Adj (z 0) (z 18))) → False
  intro h1
  exact h1 (hz 0 18 (by decide +kernel))

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.pos 3679]) := by
  apply sat_one
  change (¬ (H.Adj (z 0) (z 19))) → False
  intro h1
  exact h1 (hz 0 19 (by decide +kernel))

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 0, .neg 20, .neg 3680]) := by
  apply sat_one
  change (m (z 0)) → (m (z 20)) → (H.Adj (z 0) (z 20)) → False
  intro h1 h2 h3
  exact h.independent (z 0) (z 20) h1 h2 h3

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 0, .neg 25, .neg 3685]) := by
  apply sat_one
  change (m (z 0)) → (m (z 25)) → (H.Adj (z 0) (z 25)) → False
  intro h1 h2 h3
  exact h.independent (z 0) (z 25) h1 h2 h3

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 123, .neg 1, .pos 3]) := by
  apply sat_one
  change (z 1 = z 3) → (m (z 1)) → (¬ (m (z 3))) → False
  intro h1 h2 h3
  exact h3 (h1 ▸ h2)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 123, .pos 1, .neg 3]) := by
  apply sat_one
  change (z 1 = z 3) → (¬ (m (z 1))) → (m (z 3)) → False
  intro h1 h2 h3
  exact h2 (h1.symm ▸ h3)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 141, .neg 3741]) := by
  apply sat_one
  change (z 1 = z 21) → (H.Adj (z 1) (z 21)) → False
  intro h1 h2
  exact h2.ne h1

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 145, .neg 3745]) := by
  apply sat_one
  change (z 1 = z 25) → (H.Adj (z 1) (z 25)) → False
  intro h1 h2
  exact h2.ne h1

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 150, .neg 3750]) := by
  apply sat_one
  change (z 1 = z 30) → (H.Adj (z 1) (z 30)) → False
  intro h1 h2
  exact h2.ne h1

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 158, .neg 1, .pos 38]) := by
  apply sat_one
  change (z 1 = z 38) → (m (z 1)) → (¬ (m (z 38))) → False
  intro h1 h2 h3
  exact h3 (h1 ▸ h2)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 168, .pos 1, .neg 48]) := by
  apply sat_one
  change (z 1 = z 48) → (¬ (m (z 1))) → (m (z 48)) → False
  intro h1 h2 h3
  exact h2 (h1.symm ▸ h3)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 207, .neg 3807]) := by
  apply sat_one
  change (z 2 = z 27) → (H.Adj (z 2) (z 27)) → False
  intro h1 h2
  exact h2.ne h1

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 225, .neg 3825]) := by
  apply sat_one
  change (z 2 = z 45) → (H.Adj (z 2) (z 45)) → False
  intro h1 h2
  exact h2.ne h1

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 297, .neg 3, .pos 57]) := by
  apply sat_one
  change (z 3 = z 57) → (m (z 3)) → (¬ (m (z 57))) → False
  intro h1 h2 h3
  exact h3 (h1 ▸ h2)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 1281, .pos 20, .neg 21]) := by
  apply sat_one
  change (z 20 = z 21) → (¬ (m (z 20))) → (m (z 21)) → False
  intro h1 h2 h3
  exact h2 (h1.symm ▸ h3)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 1589, .pos 25, .neg 29]) := by
  apply sat_one
  change (z 25 = z 29) → (¬ (m (z 25))) → (m (z 29)) → False
  intro h1 h2 h3
  exact h2 (h1.symm ▸ h3)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 1594, .neg 25, .pos 34]) := by
  apply sat_one
  change (z 25 = z 34) → (m (z 25)) → (¬ (m (z 34))) → False
  intro h1 h2 h3
  exact h3 (h1 ▸ h2)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 2030, .neg 32, .pos 50]) := by
  apply sat_one
  change (z 32 = z 50) → (m (z 32)) → (¬ (m (z 50))) → False
  intro h1 h2 h3
  exact h3 (h1 ▸ h2)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 2032, .pos 32, .neg 52]) := by
  apply sat_one
  change (z 32 = z 52) → (¬ (m (z 32))) → (m (z 52)) → False
  intro h1 h2 h3
  exact h2 (h1.symm ▸ h3)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 70, .neg 3730, .pos 3661]) := by
  apply sat_one
  change (z 0 = z 10) → (H.Adj (z 1) (z 10)) → (¬ (H.Adj (z 0) (z 1))) → False
  intro h1 h2 h3
  exact h3 ((h1).symm ▸ (h2).symm)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 61, .pos 3671, .neg 3731]) := by
  apply sat_one
  change (z 0 = z 1) → (¬ (H.Adj (z 0) (z 11))) → (H.Adj (z 1) (z 11)) → False
  intro h1 h2 h3
  exact h2 ((h1).symm ▸ h3)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 3661, .neg 3690, .neg 3750, .pos 0, .pos 1, .pos 30]) := by
  apply sat_one
  change (H.Adj (z 0) (z 1)) → (H.Adj (z 0) (z 30)) → (H.Adj (z 1) (z 30)) → (¬ (m (z 0))) → (¬ (m (z 1))) → (¬ (m (z 30))) → False
  intro h1 h2 h3 h4 h5 h6
  exact (h.hit (z 0) (z 1) (z 30) h1 h2 h3).elim h4 (fun hh => hh.elim h5 h6)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 61, .neg 3694, .pos 3754]) := by
  apply sat_one
  change (z 0 = z 1) → (H.Adj (z 0) (z 34)) → (¬ (H.Adj (z 1) (z 34))) → False
  intro h1 h2 h3
  exact h3 (h1 ▸ h2)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 171, .neg 111, .pos 61]) := by
  apply sat_one
  change (z 1 = z 51) → (z 0 = z 51) → (¬ (z 0 = z 1)) → False
  intro h1 h2 h3
  exact h3 (((h1).trans (h2).symm).symm)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 65, .neg 3785, .pos 3662]) := by
  apply sat_one
  change (z 0 = z 5) → (H.Adj (z 2) (z 5)) → (¬ (H.Adj (z 0) (z 2))) → False
  intro h1 h2 h3
  exact h3 ((h1).symm ▸ (h2).symm)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 3662, .neg 3685, .neg 3805, .pos 0, .pos 2, .pos 25]) := by
  apply sat_one
  change (H.Adj (z 0) (z 2)) → (H.Adj (z 0) (z 25)) → (H.Adj (z 2) (z 25)) → (¬ (m (z 0))) → (¬ (m (z 2))) → (¬ (m (z 25))) → False
  intro h1 h2 h3 h4 h5 h6
  exact (h.hit (z 0) (z 2) (z 25) h1 h2 h3).elim h4 (fun hh => hh.elim h5 h6)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 89, .neg 3809, .pos 3662]) := by
  apply sat_one
  change (z 0 = z 29) → (H.Adj (z 2) (z 29)) → (¬ (H.Adj (z 0) (z 2))) → False
  intro h1 h2 h3
  exact h3 ((h1).symm ▸ (h2).symm)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 3662, .neg 3690, .neg 3810, .pos 0, .pos 2, .pos 30]) := by
  apply sat_one
  change (H.Adj (z 0) (z 2)) → (H.Adj (z 0) (z 30)) → (H.Adj (z 2) (z 30)) → (¬ (m (z 0))) → (¬ (m (z 2))) → (¬ (m (z 30))) → False
  intro h1 h2 h3 h4 h5 h6
  exact (h.hit (z 0) (z 2) (z 30) h1 h2 h3).elim h4 (fun hh => hh.elim h5 h6)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 236, .pos 3662, .neg 3716]) := by
  apply sat_one
  change (z 2 = z 56) → (¬ (H.Adj (z 0) (z 2))) → (H.Adj (z 0) (z 56)) → False
  intro h1 h2 h3
  exact h2 (((h1).symm ▸ (h3).symm)).symm

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 246, .pos 3663, .neg 3666]) := by
  apply sat_one
  change (z 3 = z 6) → (¬ (H.Adj (z 0) (z 3))) → (H.Adj (z 0) (z 6)) → False
  intro h1 h2 h3
  exact h2 (((h1).symm ▸ (h3).symm)).symm

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 70, .neg 63, .pos 250]) := by
  apply sat_one
  change (z 0 = z 10) → (z 0 = z 3) → (¬ (z 3 = z 10)) → False
  intro h1 h2 h3
  exact h3 ((((h1).symm).trans h2).symm)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 63, .neg 3677, .pos 3857]) := by
  apply sat_one
  change (z 0 = z 3) → (H.Adj (z 0) (z 17)) → (¬ (H.Adj (z 3) (z 17))) → False
  intro h1 h2 h3
  exact h3 (h1 ▸ h2)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 63, .pos 3693, .neg 3873]) := by
  apply sat_one
  change (z 0 = z 3) → (¬ (H.Adj (z 0) (z 33))) → (H.Adj (z 3) (z 33)) → False
  intro h1 h2 h3
  exact h2 ((h1).symm ▸ h3)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 63, .pos 3694, .neg 3874]) := by
  apply sat_one
  change (z 0 = z 3) → (¬ (H.Adj (z 0) (z 34))) → (H.Adj (z 3) (z 34)) → False
  intro h1 h2 h3
  exact h2 ((h1).symm ▸ h3)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 68, .neg 64, .pos 308]) := by
  apply sat_one
  change (z 0 = z 8) → (z 0 = z 4) → (¬ (z 4 = z 8)) → False
  intro h1 h2 h3
  exact h3 ((((h1).symm).trans h2).symm)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 3664, .neg 3685, .neg 3925, .pos 0, .pos 4, .pos 25]) := by
  apply sat_one
  change (H.Adj (z 0) (z 4)) → (H.Adj (z 0) (z 25)) → (H.Adj (z 4) (z 25)) → (¬ (m (z 0))) → (¬ (m (z 4))) → (¬ (m (z 25))) → False
  intro h1 h2 h3 h4 h5 h6
  exact (h.hit (z 0) (z 4) (z 25) h1 h2 h3).elim h4 (fun hh => hh.elim h5 h6)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 3664, .neg 3690, .neg 3930, .pos 0, .pos 4, .pos 30]) := by
  apply sat_one
  change (H.Adj (z 0) (z 4)) → (H.Adj (z 0) (z 30)) → (H.Adj (z 4) (z 30)) → (¬ (m (z 0))) → (¬ (m (z 4))) → (¬ (m (z 30))) → False
  intro h1 h2 h3 h4 h5 h6
  exact (h.hit (z 0) (z 4) (z 30) h1 h2 h3).elim h4 (fun hh => hh.elim h5 h6)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 65, .neg 368, .pos 68]) := by
  apply sat_one
  change (z 0 = z 5) → (z 5 = z 8) → (¬ (z 0 = z 8)) → False
  intro h1 h2 h3
  exact h3 ((h1).trans h2)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 96, .neg 65, .pos 396]) := by
  apply sat_one
  change (z 0 = z 36) → (z 0 = z 5) → (¬ (z 5 = z 36)) → False
  intro h1 h2 h3
  exact h3 ((((h1).symm).trans h2).symm)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 0, .pos 1038, .pos 1039, .pos 1050, .pos 1159, .pos 1170, .pos 1230]) := by
  apply sat_one
  change (m (z 0)) → (¬ (z 16 = z 18)) → (¬ (z 16 = z 19)) → (¬ (z 16 = z 30)) → (¬ (z 18 = z 19)) → (¬ (z 18 = z 30)) → (¬ (z 19 = z 30)) → False
  intro h1 h2 h3 h4 h5 h6 h7
  rcases h.degree (z 0) h1 (z 16) (z 18) (z 19) (z 30) (hz 0 16 (by decide +kernel)) (hz 0 18 (by decide +kernel)) (hz 0 19 (by decide +kernel)) (hz 0 30 (by decide +kernel)) with he | he | he | he | he | he
  · exact h2 he
  · exact h3 he
  · exact h4 he
  · exact h5 he
  · exact h6 he
  · exact h7 he

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 0, .pos 1099, .pos 1105, .pos 1125, .pos 1225, .pos 1245, .pos 1605]) := by
  apply sat_one
  change (m (z 0)) → (¬ (z 17 = z 19)) → (¬ (z 17 = z 25)) → (¬ (z 17 = z 45)) → (¬ (z 19 = z 25)) → (¬ (z 19 = z 45)) → (¬ (z 25 = z 45)) → False
  intro h1 h2 h3 h4 h5 h6 h7
  rcases h.degree (z 0) h1 (z 17) (z 19) (z 25) (z 45) (hz 0 17 (by decide +kernel)) (hz 0 19 (by decide +kernel)) (hz 0 25 (by decide +kernel)) (hz 0 45 (by decide +kernel)) with he | he | he | he | he | he
  · exact h2 he
  · exact h3 he
  · exact h4 he
  · exact h5 he
  · exact h6 he
  · exact h7 he

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 1, .pos 1281, .pos 1282, .pos 1290, .pos 1342, .pos 1350, .pos 1410]) := by
  apply sat_one
  change (m (z 1)) → (¬ (z 20 = z 21)) → (¬ (z 20 = z 22)) → (¬ (z 20 = z 30)) → (¬ (z 21 = z 22)) → (¬ (z 21 = z 30)) → (¬ (z 22 = z 30)) → False
  intro h1 h2 h3 h4 h5 h6 h7
  rcases h.degree (z 1) h1 (z 20) (z 21) (z 22) (z 30) (hz 1 20 (by decide +kernel)) (hz 1 21 (by decide +kernel)) (hz 1 22 (by decide +kernel)) (hz 1 30 (by decide +kernel)) with he | he | he | he | he | he
  · exact h2 he
  · exact h3 he
  · exact h4 he
  · exact h5 he
  · exact h6 he
  · exact h7 he

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 1, .pos 1281, .pos 1283, .pos 1285, .pos 1343, .pos 1345, .pos 1465]) := by
  apply sat_one
  change (m (z 1)) → (¬ (z 20 = z 21)) → (¬ (z 20 = z 23)) → (¬ (z 20 = z 25)) → (¬ (z 21 = z 23)) → (¬ (z 21 = z 25)) → (¬ (z 23 = z 25)) → False
  intro h1 h2 h3 h4 h5 h6 h7
  rcases h.degree (z 1) h1 (z 20) (z 21) (z 23) (z 25) (hz 1 20 (by decide +kernel)) (hz 1 21 (by decide +kernel)) (hz 1 23 (by decide +kernel)) (hz 1 25 (by decide +kernel)) with he | he | he | he | he | he
  · exact h2 he
  · exact h3 he
  · exact h4 he
  · exact h5 he
  · exact h6 he
  · exact h7 he

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 1, .pos 1281, .pos 1283, .pos 1290, .pos 1343, .pos 1350, .pos 1470]) := by
  apply sat_one
  change (m (z 1)) → (¬ (z 20 = z 21)) → (¬ (z 20 = z 23)) → (¬ (z 20 = z 30)) → (¬ (z 21 = z 23)) → (¬ (z 21 = z 30)) → (¬ (z 23 = z 30)) → False
  intro h1 h2 h3 h4 h5 h6 h7
  rcases h.degree (z 1) h1 (z 20) (z 21) (z 23) (z 30) (hz 1 20 (by decide +kernel)) (hz 1 21 (by decide +kernel)) (hz 1 23 (by decide +kernel)) (hz 1 30 (by decide +kernel)) with he | he | he | he | he | he
  · exact h2 he
  · exact h3 he
  · exact h4 he
  · exact h5 he
  · exact h6 he
  · exact h7 he

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 1, .neg 4945, .neg 4881, .pos 1285]) := by
  apply sat_one
  change (m (z 1)) → (H.Adj (z 21) (z 25)) → (H.Adj (z 20) (z 21)) → (¬ (z 20 = z 25)) → False
  intro h1 h2 h3 h4
  exact h4 ((h.matching (z 1) h1 (z 21) (z 25) (z 20) (hz 1 21 (by decide +kernel)) (hz 1 25 (by decide +kernel)) (hz 1 20 (by decide +kernel)) h2 (h3).symm).symm)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 1, .neg 4885, .neg 4945, .pos 1281]) := by
  apply sat_one
  change (m (z 1)) → (H.Adj (z 20) (z 25)) → (H.Adj (z 21) (z 25)) → (¬ (z 20 = z 21)) → False
  intro h1 h2 h3 h4
  exact h4 (h.matching (z 1) h1 (z 25) (z 20) (z 21) (hz 1 25 (by decide +kernel)) (hz 1 20 (by decide +kernel)) (hz 1 21 (by decide +kernel)) (h2).symm (h3).symm)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 1, .neg 4950, .neg 4881, .pos 1290]) := by
  apply sat_one
  change (m (z 1)) → (H.Adj (z 21) (z 30)) → (H.Adj (z 20) (z 21)) → (¬ (z 20 = z 30)) → False
  intro h1 h2 h3 h4
  exact h4 ((h.matching (z 1) h1 (z 21) (z 30) (z 20) (hz 1 21 (by decide +kernel)) (hz 1 30 (by decide +kernel)) (hz 1 20 (by decide +kernel)) h2 (h3).symm).symm)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 1, .neg 4890, .neg 4950, .pos 1281]) := by
  apply sat_one
  change (m (z 1)) → (H.Adj (z 20) (z 30)) → (H.Adj (z 21) (z 30)) → (¬ (z 20 = z 21)) → False
  intro h1 h2 h3 h4
  exact h4 (h.matching (z 1) h1 (z 30) (z 20) (z 21) (hz 1 30 (by decide +kernel)) (hz 1 20 (by decide +kernel)) (hz 1 21 (by decide +kernel)) (h2).symm (h3).symm)

include h hz in
example : (valuation H m z).satisfies_fmla (Sat.Fmla.one [.neg 1, .neg 4890, .neg 5130, .pos 1284]) := by
  apply sat_one
  change (m (z 1)) → (H.Adj (z 20) (z 30)) → (H.Adj (z 24) (z 30)) → (¬ (z 20 = z 24)) → False
  intro h1 h2 h3 h4
  exact h4 (h.matching (z 1) h1 (z 30) (z 20) (z 24) (hz 1 30 (by decide +kernel)) (hz 1 20 (by decide +kernel)) (hz 1 24 (by decide +kernel)) (h2).symm (h3).symm)

end Erdos595OneEdgeLocal
