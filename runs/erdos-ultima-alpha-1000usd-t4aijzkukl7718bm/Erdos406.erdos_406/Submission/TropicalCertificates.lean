import Submission.AffinePotentialCertificates

/-! Soundness of max-plus nondeterministic automaton certificates.
No subcritical witness is supplied, and this file does not settle Erdős406. -/

namespace Erdos406Tropical
open Erdos406AffineCertificate Erdos406GroupedCertificate Erdos406AffinePotential

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

structure Automaton (σ : Type*) [Fintype σ] [DecidableEq σ] where
  next : σ → ℕ → Finset σ
  nonempty : ∀ s d, (next s d).Nonempty
  weight : σ → ℕ → σ → ℝ
  start : σ

inductive Run (D : Automaton σ) : σ → List ℕ → σ → ℝ → Prop
  | nil (s) : Run D s [] s 0
  | cons {s t u d L v} (ht : t ∈ D.next s d) (h : Run D t L u v) :
      Run D s (d :: L) u (D.weight s d t + v)

noncomputable def valueFrom (D : Automaton σ) (s : σ) : List ℕ → ℝ
  | [] => 0
  | d :: L => (D.next s d).sup' (D.nonempty s d)
      (fun t => D.weight s d t + valueFrom D t L)

noncomputable def value (D : Automaton σ) (n : ℕ) : ℝ :=
  valueFrom D D.start (Nat.digits 3 n).reverse

lemma Run.le_valueFrom {D : Automaton σ} {s t L v} (h : Run D s L t v) :
    v ≤ valueFrom D s L := by
  induction h with
  | nil => exact le_rfl
  | @cons s t u d L v ht h ih =>
    have hs := Finset.le_sup' (fun t => D.weight s d t + valueFrom D t L) ht
    change D.weight s d t + v ≤ (D.next s d).sup' _ _
    linarith

lemma exists_max_run (D : Automaton σ) (s : σ) (L : List ℕ) :
    ∃ t, Run D s L t (valueFrom D s L) := by
  induction L generalizing s with
  | nil => exact ⟨s, Run.nil s⟩
  | cons d L ih =>
    obtain ⟨t, ht, he⟩ := Finset.exists_mem_eq_sup' (D.nonempty s d)
      (fun t => D.weight s d t + valueFrom D t L)
    obtain ⟨u, hu⟩ := ih t
    refine ⟨u, ?_⟩
    change Run D s (d :: L) u ((D.next s d).sup' _ _)
    rw [he]
    exact Run.cons ht hu

lemma Run.snoc {D : Automaton σ} {s t u L v d} (h : Run D s L t v)
    (hu : u ∈ D.next t d) :
    Run D s (L ++ [d]) u (v + D.weight t d u) := by
  induction h with
  | nil => simpa using Run.cons hu (Run.nil u)
  | cons ht h ih => simpa only [List.cons_append, add_assoc] using Run.cons ht (ih hu)

lemma Run.split_last {D : Automaton σ} {s u L v d}
    (h : Run D s (L ++ [d]) u v) :
    ∃ t a, Run D s L t a ∧ u ∈ D.next t d ∧ v = a + D.weight t d u := by
  induction L generalizing s v with
  | nil =>
    cases h with
    | cons ht h =>
      cases h
      exact ⟨s, 0, Run.nil s, ht, by simp⟩
  | cons e L ih =>
    cases h with
    | @cons _ t _ _ _ b ht h =>
      obtain ⟨p, a, hp, hu, he⟩ := ih h
      exact ⟨p, D.weight s e t + a, Run.cons ht hp, hu, by rw [he]; ring⟩

structure Simulation (D : Automaton σ) where
  R : σ → σ → ℕ → Prop
  H : σ → σ → ℕ → ℝ
  seed : ∀ c, c < 4 → ∃ t v, Run D D.start (Nat.digits 3 c).reverse t v ∧
    R D.start t c ∧ H D.start t c ≤ v
  step : ∀ s t c d e c', c < 4 → d < 3 → e < 3 → c' < 4 →
    4*d+c' = 3*c+e → R s t c → ∀ s', s' ∈ D.next s d →
    ∃ t', t' ∈ D.next t e ∧ R s' t' c' ∧
      H s' t' c' ≤ H s t c + D.weight t e t' - D.weight s d s'
  finish : ∀ s t, R s t 1 → 1 ≤ H s t 1

namespace Simulation
variable {D : Automaton σ} (S : Simulation D)
include S

lemma simulate (n c : ℕ) (hc : c < 4) {s v}
    (hin : Run D D.start (Nat.digits 3 n).reverse s v) :
    ∃ t u, Run D D.start (Nat.digits 3 (4*n+c)).reverse t u ∧
      S.R s t c ∧ S.H s t c ≤ u-v := by
  induction n using Nat.strong_induction_on generalizing c s v with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp only [Nat.digits_zero, List.reverse_nil] at hin
      cases hin
      obtain ⟨t, u, hu, hr, hh⟩ := S.seed c hc
      exact ⟨t, u, by simpa using hu, hr, by simpa using hh⟩
    · have hnpos := Nat.pos_of_ne_zero hn
      let d := n % 3
      let cp := (4*d+c)/3
      let e := (4*d+c)%3
      have hd : d < 3 := Nat.mod_lt _ (by decide)
      have he : e < 3 := Nat.mod_lt _ (by decide)
      have hcp : cp < 4 := by dsimp [cp]; omega
      have hid : 4*d+c = 3*cp+e := by dsimp [cp,e]; omega
      rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hnpos,
        List.reverse_cons] at hin
      obtain ⟨p, a, hp, hs, hv⟩ := hin.split_last
      obtain ⟨q, b, hq, hr, hh⟩ := ih (n/3)
        (Nat.div_lt_self hnpos (by decide)) cp hcp hp
      obtain ⟨t, ht, hr', hh'⟩ := S.step p q cp d e c hcp hd he hc hid hr s hs
      have hout : 0 < 4*n+c := by omega
      obtain ⟨heq, hmod⟩ := affine_div_mod 3 4 n c (by decide)
      refine ⟨t, b + D.weight q e t, ?_, hr', ?_⟩
      · rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hout,
          List.reverse_cons, heq, hmod]
        exact hq.snoc ht
      · dsimp only [d] at hh'
        linarith

lemma grows (n : ℕ) : value D n + 1 ≤ value D (4*n+1) := by
  obtain ⟨s, hs⟩ := exists_max_run D D.start (Nat.digits 3 n).reverse
  obtain ⟨t, v, hv, hr, hh⟩ := S.simulate n 1 (by decide) hs
  have hf := S.finish s t hr
  have hb := hv.le_valueFrom
  change v ≤ value D (4*n+1) at hb
  change S.H s t 1 ≤ v - value D n at hh
  linarith
end Simulation

structure GoodBound (D : Automaton σ) where
  c : ℝ
  B : ℝ
  J : σ → ℝ
  c_nonneg : 0 ≤ c
  step : ∀ s d t, d < 2 → t ∈ D.next s d →
    D.weight s d t ≤ c + J t - J s
  bound : ∀ t, J t - J D.start ≤ B

namespace GoodBound
variable {D : Automaton σ} (G : GoodBound D)

lemma run_bound {s t L v} (h : Run D s L t v) (hL : ∀ d ∈ L, d < 2) :
    v ≤ G.c * (L.length : ℝ) + G.J t - G.J s := by
  induction h with
  | nil => simp
  | @cons s t u d L v ht h ih =>
    have hb := ih (fun a ha => hL a (List.mem_cons_of_mem _ ha))
    have hw := G.step s d t (hL d (List.mem_cons_self ..)) ht
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

lemma good_bound (n : ℕ) (hn : Good n) :
    value D n ≤ G.c * (Nat.digits 3 n).length + G.B := by
  obtain ⟨t, ht⟩ := exists_max_run D D.start (Nat.digits 3 n).reverse
  have hL : ∀ d ∈ (Nat.digits 3 n).reverse, d < 2 := by
    intro d hd
    have hh := hn (List.mem_reverse.mp hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    omega
  have hh := G.run_bound ht hL
  have hb := G.bound t
  simp only [List.length_reverse] at hh
  change value D n ≤ _ at hh
  linarith
end GoodBound

/-- This proves finiteness only if a witness satisfying the strict slope
inequality is supplied. No such witness is constructed here. -/
theorem tropical_affine_criterion (D : Automaton σ) (S : Simulation D)
    (G : GoodBound D) (hcrit : G.c * Real.log 4 < Real.log 3) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite :=
  affine_potential_criterion (value D) G.c G.B G.c_nonneg hcrit S.grows G.good_bound

#print axioms Simulation.grows
#print axioms tropical_affine_criterion
end Erdos406Tropical
