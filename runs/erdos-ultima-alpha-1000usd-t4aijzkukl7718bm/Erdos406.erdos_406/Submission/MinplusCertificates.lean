import Submission.TropicalCertificates

/-! Soundness of minimum-path automaton certificates.
No subcritical witness is supplied. This does not settle Erdős406. -/

namespace Erdos406Minplus
open Erdos406AffineCertificate Erdos406GroupedCertificate Erdos406AffinePotential
open Erdos406Tropical (Automaton Run)

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

noncomputable def valueFrom (D : Automaton σ) (s : σ) : List ℕ → ℝ
  | [] => 0
  | d :: L => (D.next s d).inf' (D.nonempty s d)
      (fun t => D.weight s d t + valueFrom D t L)

noncomputable def value (D : Automaton σ) (n : ℕ) : ℝ :=
  valueFrom D D.start (Nat.digits 3 n).reverse

lemma valueFrom_le_run {D : Automaton σ} {s t L v} (h : Run D s L t v) :
    valueFrom D s L ≤ v := by
  induction h with
  | nil => exact le_rfl
  | @cons s t u d L v ht h ih =>
    have hs := Finset.inf'_le (fun t => D.weight s d t + valueFrom D t L) ht
    change (D.next s d).inf' _ _ ≤ D.weight s d t + v
    linarith

lemma exists_min_run (D : Automaton σ) (s : σ) (L : List ℕ) :
    ∃ t, Run D s L t (valueFrom D s L) := by
  induction L generalizing s with
  | nil => exact ⟨s, Run.nil s⟩
  | cons d L ih =>
    obtain ⟨t, ht, he⟩ := Finset.exists_mem_eq_inf' (D.nonempty s d)
      (fun t => D.weight s d t + valueFrom D t L)
    obtain ⟨u, hu⟩ := ih t
    refine ⟨u, ?_⟩
    change Run D s (d :: L) u ((D.next s d).inf' _ _)
    rw [he]
    exact Run.cons ht hu

/-- Unlike max-plus simulation, every output transition must have a match. -/
structure Simulation (D : Automaton σ) where
  R : σ → σ → ℕ → Prop
  H : σ → σ → ℕ → ℝ
  seed : ∀ c, c < 4 → ∀ t v, Run D D.start (Nat.digits 3 c).reverse t v →
    R D.start t c ∧ H D.start t c ≤ v
  step : ∀ s t c d e c', c < 4 → d < 3 → e < 3 → c' < 4 →
    4*d+c' = 3*c+e → R s t c → ∀ t', t' ∈ D.next t e →
    ∃ s', s' ∈ D.next s d ∧ R s' t' c' ∧
      H s' t' c' ≤ H s t c + D.weight t e t' - D.weight s d s'
  finish : ∀ s t, R s t 1 → 1 ≤ H s t 1

namespace Simulation
variable {D : Automaton σ} (S : Simulation D)
include S

lemma simulate (n c : ℕ) (hc : c < 4) {t u}
    (hout : Run D D.start (Nat.digits 3 (4*n+c)).reverse t u) :
    ∃ s v, Run D D.start (Nat.digits 3 n).reverse s v ∧
      S.R s t c ∧ S.H s t c ≤ u-v := by
  induction n using Nat.strong_induction_on generalizing c t u with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp only [mul_zero, zero_add] at hout
      have hs := S.seed c hc t u hout
      refine ⟨D.start, 0, ?_, hs.1, by simpa using hs.2⟩
      simpa using Run.nil (D := D) D.start
    · have hnpos := Nat.pos_of_ne_zero hn
      let d := n % 3
      let cp := (4*d+c)/3
      let e := (4*d+c)%3
      have hd : d < 3 := Nat.mod_lt _ (by decide)
      have he : e < 3 := Nat.mod_lt _ (by decide)
      have hcp : cp < 4 := by dsimp [cp]; omega
      have hid : 4*d+c = 3*cp+e := by dsimp [cp,e]; omega
      have hpos : 0 < 4*n+c := by omega
      obtain ⟨heq, hmod⟩ := affine_div_mod 3 4 n c (by decide)
      rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hpos,
        List.reverse_cons, heq, hmod] at hout
      obtain ⟨q, b, hq, ht, hu⟩ := hout.split_last
      obtain ⟨p, a, hp, hr, hh⟩ := ih (n/3)
        (Nat.div_lt_self hnpos (by decide)) cp hcp hq
      obtain ⟨s, hs, hr', hh'⟩ := S.step p q cp d e c hcp hd he hc hid hr t ht
      refine ⟨s, a + D.weight p d s, ?_, hr', ?_⟩
      · rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hnpos,
          List.reverse_cons]
        exact hp.snoc hs
      · dsimp only [e] at hh'
        linarith

lemma grows (n : ℕ) : value D n + 1 ≤ value D (4*n+1) := by
  obtain ⟨t, ht⟩ := exists_min_run D D.start (Nat.digits 3 (4*n+1)).reverse
  obtain ⟨s, v, hv, hr, hh⟩ := S.simulate n 1 (by decide) ht
  have hf := S.finish s t hr
  have hb := valueFrom_le_run hv
  change value D n ≤ v at hb
  change S.H s t 1 ≤ value D (4*n+1) - v at hh
  linarith
end Simulation

/-- A cheap path is enough for a minimum-path upper bound. -/
structure GoodBound (D : Automaton σ) where
  c : ℝ
  B : ℝ
  J : σ → ℝ
  c_nonneg : 0 ≤ c
  step : ∀ s d, d < 2 → ∃ t, t ∈ D.next s d ∧
    D.weight s d t ≤ c + J t - J s
  bound : ∀ t, J t - J D.start ≤ B

namespace GoodBound
variable {D : Automaton σ} (G : GoodBound D)

lemma cheap_run (L : List ℕ) (hL : ∀ d ∈ L, d < 2) (s : σ) :
    ∃ t v, Run D s L t v ∧ v ≤ G.c * (L.length : ℝ) + G.J t - G.J s := by
  induction L generalizing s with
  | nil => exact ⟨s, 0, Run.nil s, by simp⟩
  | cons d L ih =>
    obtain ⟨t, ht, hw⟩ := G.step s d (hL d (List.mem_cons_self ..))
    obtain ⟨u, v, hu, hv⟩ := ih (fun a ha => hL a (List.mem_cons_of_mem _ ha)) t
    refine ⟨u, D.weight s d t + v, Run.cons ht hu, ?_⟩
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

lemma good_bound (n : ℕ) (hn : Good n) :
    value D n ≤ G.c * (Nat.digits 3 n).length + G.B := by
  have hL : ∀ d ∈ (Nat.digits 3 n).reverse, d < 2 := by
    intro d hd
    have hh := hn (List.mem_reverse.mp hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    omega
  obtain ⟨t, v, hv, hh⟩ := G.cheap_run _ hL D.start
  have hb := G.bound t
  have hm := valueFrom_le_run hv
  simp only [List.length_reverse] at hh
  change value D n ≤ v at hm
  linarith
end GoodBound

/-- The strict slope condition is essential. No subcritical witness is known here. -/
theorem minplus_affine_criterion (D : Automaton σ) (S : Simulation D)
    (G : GoodBound D) (hcrit : G.c * Real.log 4 < Real.log 3) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite :=
  affine_potential_criterion (value D) G.c G.B G.c_nonneg hcrit S.grows G.good_bound

#print axioms Simulation.grows
#print axioms minplus_affine_criterion
end Erdos406Minplus
