import Mathlib
import Submission.Basic
import Submission.Net
import Submission.Cap1
import Submission.Cap2
import Submission.Cap3

open SimpleGraph

namespace E74

universe u

variable {V : Type u}

section cap

variable {Q : SimpleGraph V} {F : Finset (Sym2 V)} {P : V → Bool} {C : Finset V} {R : ℕ}

theorem prof_cap [Fintype V] (T : ℕ → ℕ) (hT : Monotone T) (hd : CapData Q F P C R) {B' : ℕ}
    (hFB : F.card ≤ B') (hTR : T B' < R) (hQ : Prof T Q) :
    Prof T (capGraph Q (Iset Q F C R) (Nset Q F C R)) := by
  classical
  intro S' k hk
  have h1 : k ≤ F.card := le_trans (hk (chi Q F C)) (claim2 hd S')
  have hkB : k ≤ B' := h1.trans hFB
  by_cases hbig : T B' ≤ S'.card
  · exact (hT hkB).trans hbig
  · push_neg at hbig
    let A : Finset V := (Finset.univ : Finset V).filter
      (fun v => v ∈ Iset Q F C R ∧ some v ∈ S')
    have hAS : A.card ≤ S'.card := by
      apply Finset.card_le_card_of_injOn some
      · intro v hv
        simp only [A, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
        exact hv.2
      · exact (Option.some_injective V).injOn
    have hAI : ∀ v ∈ A, v ∈ Iset Q F C R := by
      intro v hv
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      exact hv.1
    have hAR : A.card < R := by omega
    have hk' : ∀ c : V → Bool, k ≤ (mono Q A c).ncard := by
      intro c
      obtain ⟨c', hc'⟩ := claim3 hd A hAI hAR c
      refine le_trans (hk c') (hc' S' ?_)
      intro v hvI hvS
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hvI, hvS⟩
    exact (hQ A k hk').trans hAS

end cap

/-- scale bound -/
def Lsc (t B : ℕ) : ℕ := 4 * (t + 1) * 5 ^ ((4 * B) * (4 * B)) + 1

/-- the fast growing function. -/
def Tseq : ℕ → ℕ
  | 0 => 0
  | (B + 1) => sz (Lsc (Tseq B) (B + 1)) (B + 1) + Tseq B + 1

lemma Tseq_succ (B : ℕ) :
    Tseq (B + 1) = sz (Lsc (Tseq B) (B + 1)) (B + 1) + Tseq B + 1 := rfl

lemma Tseq_gt_sz (B : ℕ) : sz (Lsc (Tseq B) (B + 1)) (B + 1) < Tseq (B + 1) := by
  rw [Tseq_succ]; omega

lemma Tseq_lt_succ (B : ℕ) : Tseq B < Tseq (B + 1) := by
  rw [Tseq_succ]; omega

lemma Tseq_mono : Monotone Tseq := monotone_nat_of_le_succ (fun n => (Tseq_lt_succ n).le)

lemma Tseq_zero : Tseq 0 = 0 := rfl

/-- the vertices of a `Sym2` element -/
def vs [Fintype V] [DecidableEq V] (e : Sym2 V) : Finset V := Finset.univ.filter (· ∈ e)

lemma vs_card_le [Fintype V] [DecidableEq V] (e : Sym2 V) : (vs e).card ≤ 2 := by
  induction e using Sym2.ind with
  | _ a b =>
    have : vs s(a, b) ⊆ {a, b} := by
      intro x hx
      simp only [vs, Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff] at hx
      simpa using hx
    exact (Finset.card_le_card this).trans (Finset.card_le_two)

theorem main_thm : ∀ (B : ℕ) (V : Type u) [Fintype V] (Q : SimpleGraph V),
    (∃ P : V → Bool, (mono Q Finset.univ P).ncard ≤ B) → Prof Tseq Q → Col3 Q := by
  classical
  intro B
  induction B using Nat.strong_induction_on with
  | _ B ih =>
  intro V _ Q hPex hProf
  obtain ⟨P, hP⟩ := hPex
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · -- bipartite
    have h0 : mono Q Finset.univ P = ∅ :=
      (Set.ncard_eq_zero (Set.toFinite _)).1 (Nat.le_zero.1 hP)
    refine ⟨fun v => if P v then 1 else 0, ?_⟩
    intro u v huv hcol
    have hPuv : P u = P v := by
      cases hPu : P u <;> cases hPv : P v <;> simp_all
    have hmem : s(u, v) ∈ mono Q Finset.univ P :=
      ⟨u, v, rfl, Finset.mem_univ _, Finset.mem_univ _, huv, hPuv⟩
    rw [h0] at hmem
    exact hmem
  · obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
    -- Step 1: find F
    have hF : ∃ F : Finset (Sym2 V), F.card < B' + 1 ∧
        ¬ OddShort (Tg Q F) (Lsc (Tseq B') (B' + 1)) := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨S, hS1, hS2⟩ := tree_lemma (Lsc (Tseq B') (B' + 1)) (B' + 1) Q
        (fun F hF => hcon F hF)
      have h1 := hProf S (B' + 1) hS2
      have h3 := Tseq_gt_sz B'
      omega
    obtain ⟨F, hFcard, hFodd⟩ := hF
    -- Step 2: the set W
    let Dset : Finset (Sym2 V) := (Set.toFinite (mono Q Finset.univ P)).toFinset
    let W : Finset V := F.biUnion vs ∪ Dset.biUnion vs
    have hWcard : W.card ≤ 4 * (B' + 1) := by
      have h1 : (F.biUnion vs).card ≤ F.card * 2 :=
        Finset.card_biUnion_le_card_mul _ _ _ (fun e _ => vs_card_le e)
      have h2 : (Dset.biUnion vs).card ≤ Dset.card * 2 :=
        Finset.card_biUnion_le_card_mul _ _ _ (fun e _ => vs_card_le e)
      have h3 : Dset.card = (mono Q Finset.univ P).ncard :=
        (Set.ncard_eq_toFinset_card _ (Set.toFinite _)).symm
      have h4 : W.card ≤ (F.biUnion vs).card + (Dset.biUnion vs).card :=
        Finset.card_union_le (F.biUnion vs) (Dset.biUnion vs)
      omega
    have hWmem : ∀ v : V, ((∃ e ∈ F, v ∈ e) ∨ ∃ u, Q.Adj v u ∧ P v = P u) → v ∈ W := by
      intro v hv
      rcases hv with ⟨e, he, hve⟩ | ⟨u, hadj, hPu⟩
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨e, he, by simp [vs, hve]⟩)
      · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨s(v, u), ?_, by simp [vs]⟩)
        simp only [Dset, Set.Finite.mem_toFinset]
        exact ⟨v, u, rfl, Finset.mem_univ _, Finset.mem_univ _, hadj, hPu⟩
    -- Step 3: scale and net
    obtain ⟨i, hi, hgap⟩ := exists_gap_scale W (Tg Q F).edist (Tseq B' + 1) (4 * (B' + 1)) hWcard
    obtain ⟨C, hCW, hCnear, hCsep⟩ := exists_net W (Tg Q F).edist
      (fun x y => edist_comm) (fun x => edist_self) ((Tseq B' + 1) * 5 ^ i) hgap
    have hR1 : 1 ≤ (Tseq B' + 1) * 5 ^ i := Nat.mul_pos (by omega) (by positivity)
    have hRle : (Tseq B' + 1) * 5 ^ i ≤ (Tseq B' + 1) * 5 ^ ((4 * (B' + 1)) * (4 * (B' + 1))) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hi)
    have hd : CapData Q F P C ((Tseq B' + 1) * 5 ^ i) := by
      refine ⟨hR1, ?_, ?_, ?_⟩
      · intro c hc c' hc' hne
        refine lt_of_le_of_lt ?_ (hCsep c hc c' hc' hne)
        exact_mod_cast (by omega : 4 * ((Tseq B' + 1) * 5 ^ i) + 1 ≤ 5 * ((Tseq B' + 1) * 5 ^ i))
      · intro u w hodd
        by_contra hle
        push_neg at hle
        refine hFodd ⟨u, w, hodd, ?_⟩
        unfold Lsc
        have : 4 * ((Tseq B' + 1) * 5 ^ i) ≤ 4 * ((Tseq B' + 1) * 5 ^ ((4 * (B' + 1)) * (4 * (B' + 1)))) :=
          Nat.mul_le_mul_left _ hRle
        nlinarith
      · intro v hv
        exact hCnear v (hWmem v hv)
    have hFB : F.card ≤ B' := by omega
    have hTR : Tseq B' < (Tseq B' + 1) * 5 ^ i := by
      have : (Tseq B' + 1) ≤ (Tseq B' + 1) * 5 ^ i := Nat.le_mul_of_pos_right _ (by positivity)
      omega
    have hProf' := prof_cap Tseq Tseq_mono hd hFB hTR hProf
    have hcol' := ih F.card (by omega) (Option V)
      (capGraph Q (Iset Q F C ((Tseq B' + 1) * 5 ^ i)) (Nset Q F C ((Tseq B' + 1) * 5 ^ i)))
      ⟨chi Q F C, claim2 hd Finset.univ⟩ hProf'
    exact claim1 hd hcol'

end E74
