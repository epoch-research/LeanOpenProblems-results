import Submission.BinaryMinplusCertificates

/-! Binary min-plus certificates with accepting endpoints. A minimum is taken
only over accepting runs; totality and strict rate are explicit hypotheses.
No sufficient instance for Erdős406 is asserted. -/
namespace Erdos406BinaryAcceptingMinplus
open Erdos406GroupedCertificate
open Erdos406Tropical (Automaton Run)
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

noncomputable def scores (D : Automaton σ) (s : σ) : List ℕ → Finset (σ × ℝ)
  | [] => {(s,0)}
  | d::L => by
    classical
    exact (D.next s d).biUnion (fun t =>
      (scores D t L).image (fun p => (p.1,D.weight s d t+p.2)))

lemma mem_scores {D : Automaton σ} {s t L v} :
    (t,v) ∈ scores D s L ↔ Run D s L t v := by
  classical
  induction L generalizing s t v with
  | nil =>
    simp only [scores,Finset.mem_singleton,Prod.mk.injEq]
    constructor
    · rintro ⟨rfl,rfl⟩; exact Run.nil _
    · intro h; cases h; exact ⟨rfl,rfl⟩
  | cons d L ih =>
    simp only [scores,Finset.mem_biUnion,Finset.mem_image]
    constructor
    · rintro ⟨u,hu,⟨t',w⟩,hp,he⟩
      simp only [Prod.mk.injEq] at he
      rcases he with ⟨rfl,rfl⟩
      exact Run.cons hu (ih.mp hp)
    · intro h
      cases h with
      | @cons _ u _ _ _ w hu hw =>
        exact ⟨u,hu,(t,w),ih.mpr hw,rfl⟩

noncomputable def acceptedScores (D : Automaton σ) (F : σ → Prop)
    (s : σ) (L : List ℕ) : Finset (σ × ℝ) := by
  classical
  exact (scores D s L).filter (fun p => F p.1)

lemma mem_acceptedScores {D : Automaton σ} {F : σ → Prop} {s t L v} :
    (t,v) ∈ acceptedScores D F s L ↔ Run D s L t v ∧ F t := by
  classical
  simp only [acceptedScores,Finset.mem_filter,mem_scores]

def Total (D : Automaton σ) (F : σ → Prop) : Prop :=
  ∀ n : ℕ, ∃ t v, Run D D.start (Nat.digits 2 n).reverse t v ∧ F t

/-- An always-accepting strategy is one sufficient way to prove totality.
The main framework does not require totality to be established this way. -/
lemma total_of_closed_accepting {D : Automaton σ} {F : σ → Prop}
    (hstart : F D.start)
    (hstep : ∀ s d, d < 2 → F s → ∃ t, t ∈ D.next s d ∧ F t) : Total D F := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · subst n
      exact ⟨D.start,0,by simpa using Run.nil D.start,hstart⟩
    have hp : 0 < n := Nat.pos_of_ne_zero hz
    obtain ⟨s,v,hv,hs⟩ := ih (n/2) (Nat.div_lt_self hp (by decide))
    obtain ⟨t,ht,hF⟩ := hstep s (n%2) (Nat.mod_lt _ (by decide)) hs
    refine ⟨t,v+D.weight s (n%2) t,?_,hF⟩
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 2) hp,List.reverse_cons]
    exact hv.snoc ht

lemma accepted_nonempty {D : Automaton σ} {F : σ → Prop}
    (h : Total D F) (n : ℕ) :
    (acceptedScores D F D.start (Nat.digits 2 n).reverse).Nonempty := by
  obtain ⟨t,v,hv,ht⟩ := h n
  exact ⟨(t,v),mem_acceptedScores.mpr ⟨hv,ht⟩⟩

noncomputable def value (D : Automaton σ) (F : σ → Prop) (h : Total D F) (n : ℕ) : ℝ :=
  (acceptedScores D F D.start (Nat.digits 2 n).reverse).inf' (accepted_nonempty h n) Prod.snd

lemma value_le_run {D : Automaton σ} {F : σ → Prop} (h : Total D F)
    {n t v} (hr : Run D D.start (Nat.digits 2 n).reverse t v) (ht : F t) :
    value D F h n ≤ v :=
  Finset.inf'_le Prod.snd (mem_acceptedScores.mpr ⟨hr,ht⟩)

lemma exists_min_run {D : Automaton σ} {F : σ → Prop} (h : Total D F) (n : ℕ) :
    ∃ t, Run D D.start (Nat.digits 2 n).reverse t (value D F h n) ∧ F t := by
  obtain ⟨⟨t,v⟩,hp,he⟩ := Finset.exists_mem_eq_inf' (accepted_nonempty h n) Prod.snd
  have hh := mem_acceptedScores.mp hp
  change value D F h n = v at he
  exact ⟨t,he.symm ▸ hh.1,hh.2⟩

structure Construction (D : Automaton σ) (F : σ → Prop) where
  R : σ → σ → ℕ → Prop
  H : σ → σ → ℕ → ℝ
  seed : ∀ c, c < 3 → ∃ t v, Run D D.start (Nat.digits 2 c).reverse t v ∧
    R D.start t c ∧ v ≤ H D.start t c
  step : ∀ s t c d e cp, c < 3 → d < 2 → e < 2 → cp < 3 →
    3*d+cp = 2*c+e → R s t c → ∀ sp, sp ∈ D.next s d →
    ∃ tp, tp ∈ D.next t e ∧ R sp tp cp ∧
      H s t c + D.weight t e tp-D.weight s d sp ≤ H sp tp cp
  finish : ∀ s t c, c < 2 → R s t c → F s → F t ∧ H s t c ≤ 1

namespace Construction
variable {D : Automaton σ} {F : σ → Prop} (C : Construction D F)
include C

lemma simulate (n c : ℕ) (hc : c < 3) {s v}
    (hin : Run D D.start (Nat.digits 2 n).reverse s v) :
    ∃ t u, Run D D.start (Nat.digits 2 (3*n+c)).reverse t u ∧
      C.R s t c ∧ u-v ≤ C.H s t c := by
  induction n using Nat.strong_induction_on generalizing c s v with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp only [Nat.digits_zero,List.reverse_nil] at hin
      cases hin
      obtain ⟨t,u,hu,hr,hh⟩ := C.seed c hc
      exact ⟨t,u,by simpa using hu,hr,by simpa using hh⟩
    · have hp : 0 < n := Nat.pos_of_ne_zero hn
      let d := n%2
      let cp := (3*d+c)/2
      let e := (3*d+c)%2
      have hd : d < 2 := Nat.mod_lt _ (by decide)
      have he : e < 2 := Nat.mod_lt _ (by decide)
      have hcp : cp < 3 := by dsimp [cp]; omega
      have hid : 3*d+c = 2*cp+e := by dsimp [cp,e]; omega
      rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 2) hp,List.reverse_cons] at hin
      obtain ⟨p,a,hp',hs,hv⟩ := hin.split_last
      obtain ⟨q,b,hq,hr,hh⟩ := ih (n/2) (Nat.div_lt_self hp (by decide)) cp hcp hp'
      obtain ⟨t,ht,hr',hh'⟩ := C.step p q cp d e c hcp hd he hc hid hr s hs
      have hout : 0 < 3*n+c := by omega
      obtain ⟨heq,hmod⟩ := affine_div_mod 2 3 n c (by decide)
      refine ⟨t,b+D.weight q e t,?_,hr',?_⟩
      · rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 2) hout,List.reverse_cons,heq,hmod]
        exact hq.snoc ht
      · dsimp only [d] at hh'
        linarith

lemma construction_bound (h : Total D F) (n d : ℕ) (hd : d < 2) :
    value D F h (3*n+d) ≤ value D F h n+1 := by
  obtain ⟨s,hs,hF⟩ := exists_min_run h n
  obtain ⟨t,u,hu,hr,hh⟩ := C.simulate n d (by omega) hs
  have hf := C.finish s t d hd hr hF
  have hb := value_le_run h hu hf.1
  linarith [hf.2]
end Construction

structure PowerBound (D : Automaton σ) (F : σ → Prop) where
  a : ℝ
  B : ℝ
  G : σ → Prop
  Z : σ → Prop
  J : σ → ℝ
  start : ∀ s, s ∈ D.next D.start 1 → G s
  forward : ∀ s t, G s → t ∈ D.next s 0 → G t
  accepting : ∀ t, F t → Z t
  backward : ∀ s t, Z t → t ∈ D.next s 0 → Z s
  lower_step : ∀ s t, G s → Z t → t ∈ D.next s 0 →
    a+J t-J s ≤ D.weight s 0 t
  lower_end : ∀ s t, s ∈ D.next D.start 1 → G t → F t → Z s →
    -B ≤ D.weight D.start 1 s + J t-J s

namespace PowerBound
variable {D : Automaton σ} {F : σ → Prop} (P : PowerBound D F)

lemma zero_run_lower (k : ℕ) {s t v} (h : Run D s (List.replicate k 0) t v)
    (hs : P.G s) (ht : P.Z t) :
    P.G t ∧ P.Z s ∧ P.a*k+P.J t-P.J s ≤ v := by
  induction k generalizing s v with
  | zero =>
    simp only [List.replicate_zero] at h
    cases h
    exact ⟨hs,ht,by simp⟩
  | succ k ih =>
    rw [List.replicate_succ] at h
    cases h with
    | @cons _ u _ _ _ w hu hw =>
      obtain ⟨hgt,hzu,hb⟩ := ih hw (P.forward s u hs hu)
      have hzs := P.backward s u hzu hu
      have he := P.lower_step s u hs hzu hu
      refine ⟨hgt,hzs,?_⟩
      push_cast
      linarith

lemma power_run_lower (k : ℕ) {t v}
    (h : Run D D.start (1::List.replicate k 0) t v) (hF : F t) : P.a*k-P.B ≤ v := by
  cases h with
  | @cons _ s _ _ _ w hs hw =>
    obtain ⟨hgt,hzs,hb⟩ := P.zero_run_lower k hw (P.start s hs) (P.accepting t hF)
    have he := P.lower_end s t hs hgt hF hzs
    linarith

lemma power_lower (h : Total D F) (k : ℕ) : P.a*k-P.B ≤ value D F h (2^k) := by
  have hword : (Nat.digits 2 (2^k)).reverse = 1::List.replicate k 0 := by
    have hh := Nat.digits_base_pow_mul (b:=2) (k:=k) (m:=1) (by decide) (by decide)
    simpa using congrArg List.reverse hh
  obtain ⟨t,ht,hF⟩ := exists_min_run h (2^k)
  exact P.power_run_lower k (hword ▸ ht) hF
end PowerBound

/-- A complete accepting-run instance at a strict rate would settle the
original proposition. No such instance is supplied by this theorem. -/
theorem accepting_minplus_criterion (D : Automaton σ) (F : σ → Prop) (h : Total D F)
    (C : Construction D F) (P : PowerBound D F)
    (hcrit : Real.log 2 < P.a*Real.log 3) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite :=
  Erdos406BinaryWeighted.construction_potential_criterion (value D F h) P.a P.B
    (C.construction_bound h) (P.power_lower h) hcrit

#print axioms mem_scores
#print axioms exists_min_run
#print axioms Construction.construction_bound
#print axioms PowerBound.power_lower
#print axioms accepting_minplus_criterion
end Erdos406BinaryAcceptingMinplus
