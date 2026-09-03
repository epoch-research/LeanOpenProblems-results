import Submission.SuffixInvariantNecessity

/-! Permutation digit automata cannot supply a safe affine invariant. This
 rules out a certificate family, not the original finiteness conjecture. -/
namespace Erdos406Permutation
open Erdos406MSDCertificate

lemma finite_closed_iff {α : Type*} [Finite α] (f : α → α)
    (hf : Function.Injective f) (P : α → Prop) (hp : ∀ x, P x → P (f x)) (x : α) :
    P (f x) ↔ P x := by
  constructor
  · intro hx
    let g : {x // P x} → {x // P x} := fun y => ⟨f y.val, hp y.val y.property⟩
    have hg : Function.Injective g := by
      intro a b hab
      apply Subtype.ext
      exact hf (congrArg Subtype.val hab)
    obtain ⟨y, hy⟩ := (Finite.surjective_of_injective hg) ⟨f x, hx⟩
    have he : y.val = x := hf (congrArg Subtype.val hy)
    exact he ▸ y.property
  · exact hp x

lemma predicate_transport_iff {α : Type*} [Fintype α] (f : α → α)
    (hf : Function.Injective f) (P Q : α → Prop)
    (hp : ∀ x, P x → Q (f x))
    (hcard : Nat.card {x // P x} = Nat.card {x // Q x}) (x : α) :
    Q (f x) ↔ P x := by
  classical
  let g : {x // P x} → {x // Q x} := fun y => ⟨f y.val, hp y.val y.property⟩
  have hg : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    exact hf (congrArg Subtype.val hab)
  have hs : Function.Surjective g := by
    by_contra hh
    have hl := Fintype.card_lt_of_injective_not_surjective g hg hh
    simp only [Nat.card_eq_fintype_card] at hcard
    omega
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hs ⟨f x, hx⟩
    have he : y.val = x := hf (congrArg Subtype.val hy)
    exact he ▸ y.property
  · exact hp x

variable {σ : Type*} [Fintype σ]

def pairStep (D : DFA ℕ σ) (d e : ℕ) (p : σ × σ) : σ × σ :=
  (D.step p.1 d, D.step p.2 e)

lemma pairStep_injective (D : DFA ℕ σ) (d e : ℕ)
    (hd : Function.Injective (fun s => D.step s d))
    (he : Function.Injective (fun s => D.step s e)) : Function.Injective (pairStep D d e) := by
  intro a b hab
  apply Prod.ext
  · exact hd (congrArg Prod.fst hab)
  · exact he (congrArg Prod.snd hab)

abbrev Slice (R : σ → σ → ℕ → Prop) (c : ℕ) := {p : σ × σ // R p.1 p.2 c}

structure Carry (D : DFA ℕ σ) where
  R : σ → σ → ℕ → Prop
  initial : R D.start D.start 0
  step : ∀ s t c d e cp, c < 4 → d < 3 → e < 3 → cp < 4 →
    4 * d + cp = 3 * c + e → R s t c → R (D.step s d) (D.step t e) cp
  finish : ∀ s t, R s t 1 → s ∈ D.accept → t ∈ D.accept

namespace Carry
variable {D : DFA ℕ σ} (C : Carry D)
variable (hinj : ∀ d, d < 3 → Function.Injective (fun s => D.step s d))
include hinj

lemma slice_card_le (c d e cp : ℕ) (hc : c < 4) (hd : d < 3) (he : e < 3)
    (hcp : cp < 4) (har : 4 * d + cp = 3 * c + e) :
    Nat.card (Slice C.R c) ≤ Nat.card (Slice C.R cp) := by
  classical
  let f : Slice C.R c → Slice C.R cp := fun p =>
    ⟨pairStep D d e p.val, C.step _ _ c d e cp hc hd he hcp har p.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact pairStep_injective D d e (hinj d hd) (hinj e he) (congrArg Subtype.val hab)
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective f hf

lemma slice_cards_equal (c cp : ℕ) (hc : c < 4) (hcp : cp < 4) :
    Nat.card (Slice C.R c) = Nat.card (Slice C.R cp) := by
  have h01 := C.slice_card_le hinj 0 0 1 1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h13 := C.slice_card_le hinj 1 0 0 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h32 := C.slice_card_le hinj 3 2 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h20 := C.slice_card_le hinj 2 2 2 0 (by decide) (by decide) (by decide) (by decide) (by decide)
  interval_cases c <;> interval_cases cp <;> omega


lemma step_iff (s t : σ) (c d e cp : ℕ) (hc : c < 4) (hd : d < 3) (he : e < 3)
    (hcp : cp < 4) (har : 4 * d + cp = 3 * c + e) :
    C.R (D.step s d) (D.step t e) cp ↔ C.R s t c := by
  exact predicate_transport_iff (pairStep D d e)
    (pairStep_injective D d e (hinj d hd) (hinj e he))
    (fun p => C.R p.1 p.2 c) (fun p => C.R p.1 p.2 cp)
    (fun p hp => C.step _ _ c d e cp hc hd he hcp har hp)
    (C.slice_cards_equal hinj c cp hc hcp) (s,t)

variable (G : σ → Prop) (hGstep : ∀ s d, d < 2 → G s → G (D.step s d))
include hGstep

def touches (c : ℕ) (s : σ) : Prop := ∃ t, G t ∧ C.R s t c

lemma touches_transport (s : σ) (c d e cp : ℕ) (hc : c < 4) (hd : d < 3)
    (he : e < 2) (hcp : cp < 4) (har : 4 * d + cp = 3 * c + e) :
    C.touches G cp (D.step s d) ↔ C.touches G c s := by
  constructor
  · rintro ⟨t, ht, hr⟩
    obtain ⟨u, rfl⟩ := (Finite.surjective_of_injective (hinj e (by omega))) t
    have hu : G u := (finite_closed_iff (fun s => D.step s e) (hinj e (by omega)) G
      (fun s hs => hGstep s e he hs) u).mp ht
    exact ⟨u, hu, (C.step_iff hinj s u c d e cp hc hd (by omega) hcp har).mp hr⟩
  · rintro ⟨t, ht, hr⟩
    exact ⟨D.step t e, hGstep t e he ht, C.step _ _ c d e cp hc hd (by omega) hcp har hr⟩

lemma touches_one_iff_zero (s : σ) : C.touches G 1 s ↔ C.touches G 0 s := by
  obtain ⟨u, rfl⟩ := (Finite.surjective_of_injective (hinj 0 (by decide))) s
  have h00 := C.touches_transport hinj G hGstep u 0 0 0 0
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have h01 := C.touches_transport hinj G hGstep u 0 0 1 1
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact h01.trans h00.symm

lemma touches_three_iff_zero (s : σ) : C.touches G 3 s ↔ C.touches G 0 s := by
  obtain ⟨u, rfl⟩ := (Finite.surjective_of_injective (hinj 0 (by decide))) s
  have h13 := C.touches_transport hinj G hGstep u 1 0 0 3
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have h00 := C.touches_transport hinj G hGstep u 0 0 0 0
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact h13.trans ((C.touches_one_iff_zero hinj G hGstep u).trans h00.symm)

lemma touches_step_one (s : σ) : C.touches G 0 (D.step s 1) ↔ C.touches G 0 s := by
  have h10 := C.touches_transport hinj G hGstep s 1 1 1 0
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact h10.trans (C.touches_one_iff_zero hinj G hGstep s)

lemma touches_two_iff_zero (s : σ) : C.touches G 2 s ↔ C.touches G 0 s := by
  have h23 := C.touches_transport hinj G hGstep s 2 1 1 3
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact h23.symm.trans ((C.touches_three_iff_zero hinj G hGstep _).trans
    (C.touches_step_one hinj G hGstep s))

lemma touches_step_two (s : σ) : C.touches G 0 (D.step s 2) ↔ C.touches G 0 s := by
  have h31 := C.touches_transport hinj G hGstep s 3 2 0 1
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact (C.touches_one_iff_zero hinj G hGstep _).symm.trans
    (h31.trans (C.touches_three_iff_zero hinj G hGstep s))

lemma touches_step (s : σ) (d : ℕ) (hd : d < 3) (hs : C.touches G 0 s) :
    C.touches G 0 (D.step s d) := by
  interval_cases d
  · exact (C.touches_transport hinj G hGstep s 0 0 0 0
      (by decide) (by decide) (by decide) (by decide) (by decide)).mpr hs
  · exact (C.touches_step_one hinj G hGstep s).mpr hs
  · exact (C.touches_step_two hinj G hGstep s).mpr hs

include C

/-- Every accepted word is impossible under a safe good-state predicate.
 The actual powers of two are not needed for this abstract obstruction. -/
theorem no_accepted_word (hGstart : G D.start) (hGsafe : ∀ s, G s → s ∉ D.accept)
    (w : List ℕ) (hw : ∀ d ∈ w, d < 3) : D.eval w ∉ D.accept := by
  have ht : C.touches G 0 (D.eval w) := by
    apply Erdos406GroupedCertificate.reachable_word D (fun d => d < 3)
      (C.touches G 0) (fun s d hd hs => C.touches_step hinj G hGstep s d hd hs)
      w hw D.start
    exact ⟨D.start, hGstart, C.initial⟩
  obtain ⟨t, hGt, hR⟩ := (C.touches_one_iff_zero hinj G hGstep _).mpr ht
  intro ha
  exact hGsafe t hGt (C.finish _ _ hR ha)

#print axioms no_accepted_word

end Carry
lemma evalNat_three_mul_add (D : DFA ℕ σ) (hpad : D.step D.start 0 = D.start)
    (n d : ℕ) (hd : d < 3) : evalNat D (3 * n + d) = D.step (evalNat D n) d := by
  by_cases hz : 3 * n + d = 0
  · have hn : n = 0 := by omega
    have hdz : d = 0 := by omega
    simp [hn, hdz, evalNat_zero, hpad]
  · rw [evalNat_pos D (by omega : 0 < 3 * n + d)]
    have hdiv : (3 * n + d) / 3 = n := by omega
    have hmod : (3 * n + d) % 3 = d := by omega
    rw [hdiv, hmod]

/-- Any finite permutation digit DFA whose accepted integers are forward
 invariant under x↦4x+1 and avoid all ternary-good integers accepts no integer
 at all. Thus this entire certificate family is impossible, at every size. -/
theorem permutation_affine_invariant_empty (D : DFA ℕ σ)
    (hinj : ∀ d, d < 3 → Function.Injective (fun s => D.step s d))
    (hpad : D.step D.start 0 = D.start)
    (hclosed : ∀ n, evalNat D n ∈ D.accept → evalNat D (4 * n + 1) ∈ D.accept)
    (hsafe : ∀ n, Nat.digits 3 n ⊆ [0, 1] → evalNat D n ∉ D.accept) (n : ℕ) :
    evalNat D n ∉ D.accept := by
  let R : σ → σ → ℕ → Prop := fun s t c => ∃ n, s = evalNat D n ∧ t = evalNat D (4 * n + c)
  have hinit : R D.start D.start 0 := by
    exact ⟨0, by simp [evalNat_zero], by simp [evalNat_zero]⟩
  have hstep : ∀ s t c d e cp, c < 4 → d < 3 → e < 3 → cp < 4 →
      4 * d + cp = 3 * c + e → R s t c → R (D.step s d) (D.step t e) cp := by
    rintro s t c d e cp hc hd he hcp har ⟨m, rfl, rfl⟩
    refine ⟨3 * m + d, (evalNat_three_mul_add D hpad m d hd).symm, ?_⟩
    have hid : 4 * (3 * m + d) + cp = 3 * (4 * m + c) + e := by omega
    rw [hid, evalNat_three_mul_add D hpad (4 * m + c) e he]
  have hfinish : ∀ s t, R s t 1 → s ∈ D.accept → t ∈ D.accept := by
    rintro s t ⟨m, rfl, rfl⟩ hm
    exact hclosed m hm
  let C : Carry D := ⟨R, hinit, hstep, hfinish⟩
  let G : σ → Prop := fun s => ∃ m, Nat.digits 3 m ⊆ [0, 1] ∧ s = evalNat D m
  have hGstart : G D.start := by exact ⟨0, by simp, by simp [evalNat_zero]⟩
  have hGstep : ∀ s d, d < 2 → G s → G (D.step s d) := by
    rintro s d hd ⟨m, hm, rfl⟩
    refine ⟨3 * m + d, Erdos406AffineCertificate.good_three_mul_add hm ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    · exact (evalNat_three_mul_add D hpad m d (by omega)).symm
  have hGsafe : ∀ s, G s → s ∉ D.accept := by
    rintro s ⟨m, hm, rfl⟩
    exact hsafe m hm
  apply C.no_accepted_word hinj G hGstep hGstart hGsafe
    (Nat.digits 3 n).reverse
  intro d hd
  exact Nat.digits_lt_base (by decide) (List.mem_reverse.mp hd)

#print axioms permutation_affine_invariant_empty

end Erdos406Permutation
