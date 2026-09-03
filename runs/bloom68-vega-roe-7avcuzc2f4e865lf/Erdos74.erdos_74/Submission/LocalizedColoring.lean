import FormalConjecturesUtil
import Submission.CertificateDefs
import Submission.Gluing
import OwnSubmission.Levels
import OwnSubmission.WalkCover
import Submission.RadiusCertificate
import Submission.BallCertificate

/-!
# Local repair of Boolean colorings and finite edge certificates

The induction either repairs a Boolean coloring, using a third color only in a
bounded neighborhood of its bad edges, or produces a bounded edge certificate.
- a smaller-error coloring of a ball is repaired recursively and glued through
  a clean four-level annulus;
- if the ball retains every error, bounded-radius branching gives a certificate.
-/

namespace Erdos74.Certificates

/-- The radius needed to repair `t` bad edges, unless a certificate is found. -/
def repairRadius : ℕ → ℕ
  | 0 => 0
  | t + 1 => (2 * (t + 1) - 1) * (2 * repairRadius t + 4)

@[simp] theorem repairRadius_zero : repairRadius 0 = 0 := rfl

@[simp] theorem repairRadius_succ (t : ℕ) :
    repairRadius (t + 1) = (2 * (t + 1) - 1) * (2 * repairRadius t + 4) := rfl

theorem repairRadius_le_succ (t : ℕ) : repairRadius t ≤ repairRadius (t + 1) := by
  rw [repairRadius_succ]
  have hfac : 1 ≤ 2 * (t + 1) - 1 := by omega
  calc
    repairRadius t ≤ 2 * repairRadius t + 4 := by omega
    _ = 1 * (2 * repairRadius t + 4) := by simp
    _ ≤ (2 * (t + 1) - 1) * (2 * repairRadius t + 4) :=
      Nat.mul_le_mul_right _ hfac

theorem repairRadius_monotone : Monotone repairRadius :=
  monotone_nat_of_le_succ repairRadius_le_succ

theorem repairRadius_pred {t : ℕ} (ht : 0 < t) :
    repairRadius t = (2 * t - 1) * (2 * repairRadius (t - 1) + 4) := by
  cases t with
  | zero => omega
  | succ t => simp

/-- Edge-count threshold for a certificate at level `t`. -/
def certificateBound (t : ℕ) : ℕ := radiusCertificateBound t (repairRadius t)

universe u
variable {V : Type u}

/-- The induced ball used in the repair induction. -/
def colorBall (G : SimpleGraph V) [Finite V] (c : V → Bool) (R : ℕ) : Set V :=
  {v | level G (endVerts (badEdges G c)) (R + 1) v ≤ R}

/-- A recursively repaired coloring of a ball extends through an annulus which
contains no new bad-edge endpoints. -/
theorem extend_repaired_ball [Finite V]
    (G : SimpleGraph V) (c : V → Bool) {t r R : ℕ}
    (ht : 0 < t) (hR : R = (2 * t - 1) * (2 * r + 4))
    (c₁ : colorBall G c R → Bool)
    (herr : (badEdges (G.induce (colorBall G c R)) c₁).card < t)
    (γ : (G.induce (colorBall G c R)).Coloring (Fin 3))
    (hloc : ∀ v, ¬ Near (G.induce (colorBall G c R))
      (endVerts (badEdges (G.induce (colorBall G c R)) c₁)) r v →
      γ v = AnnulusGluing.boolColor (c₁ v)) :
    ∃ C : G.Coloring (Fin 3), ∀ v,
      ¬ Near G (endVerts (badEdges G c)) R v →
      C v = AnnulusGluing.boolColor (c v) := by
  classical
  let ℓ : V → ℕ := level G (endVerts (badEdges G c)) (R + 1)
  let T : Set V := colorBall G c R
  let H : SimpleGraph T := G.induce T
  let Z : Finset T := endVerts (badEdges H c₁)
  have hZ : Z.card ≤ 2 * t - 2 := by
    have hz := card_endVerts_le (badEdges H c₁)
    change (badEdges H c₁).card < t at herr
    change Z.card ≤ 2 * (badEdges H c₁).card at hz
    omega
  obtain ⟨a, ha, habound, hsep⟩ :=
    exists_separated_annulus Z (fun v : T => ℓ v) (r := r) ht hZ
  have hab : a + 3 ≤ R := by simpa only [hR] using habound
  have hlevel : ∀ {u v : V}, G.Adj u v → ℓ u ≤ ℓ v + 1 :=
    fun h => level_adj_le h
  have hlevelH : ∀ {u v : T}, H.Adj u v → ℓ u ≤ ℓ v + 1 :=
    fun h => hlevel h
  have havoid (v : T) (hvlo : a ≤ ℓ v) (hvhi : ℓ v ≤ a + 3) :
      ¬ Near H Z r v := by
    rintro ⟨z, hz, p, hp⟩
    have hvz := walk_level_ineq hlevelH p
    have hzv := walk_level_ineq hlevelH p.reverse
    simp only [SimpleGraph.Walk.length_reverse] at hzv
    rcases hsep z hz (ℓ v) hvlo hvhi with h | h <;> omega
  let γ₀ (v : V) : Fin 3 :=
    if h : ℓ v ≤ R then γ ⟨v, h⟩ else AnnulusGluing.boolColor (c v)
  let c₀ (v : V) : Bool := if h : ℓ v ≤ R then c₁ ⟨v, h⟩ else c v
  have hγ : ∀ {u v : V}, G.Adj u v → ℓ u ≤ a → ℓ v ≤ a → γ₀ u ≠ γ₀ v := by
    intro u v huv hu hv
    have huR : ℓ u ≤ R := by omega
    have hvR : ℓ v ≤ R := by omega
    dsimp only [γ₀]
    rw [dif_pos huR, dif_pos hvR]
    exact γ.valid (show H.Adj ⟨u, huR⟩ ⟨v, hvR⟩ from huv)
  have hc : ∀ {u v : V}, G.Adj u v → a ≤ ℓ u → a ≤ ℓ v → c u ≠ c v := by
    intro u v huv hu _
    apply proper_off_badEdges huv
    intro hus
    have hzero : ℓ u = 0 := level_zero_of_mem hus
    omega
  have hc₀ : ∀ {u v : V}, G.Adj u v →
      a ≤ ℓ u → ℓ u ≤ a + 3 → a ≤ ℓ v → ℓ v ≤ a + 3 → c₀ u ≠ c₀ v := by
    intro u v huv hulo huhi hvlo hvhi
    have huR : ℓ u ≤ R := by omega
    have hvR : ℓ v ≤ R := by omega
    dsimp only [c₀]
    rw [dif_pos huR, dif_pos hvR]
    apply proper_off_badEdges (G := H) (c := c₁)
      (show H.Adj ⟨u, huR⟩ ⟨v, hvR⟩ from huv)
    intro huZ
    exact havoid ⟨u, huR⟩ hulo huhi (near_of_mem huZ)
  have hmatch : ∀ v, ℓ v = a → γ₀ v = AnnulusGluing.boolColor (c₀ v) := by
    intro v hv
    have hvR : ℓ v ≤ R := by omega
    dsimp only [γ₀, c₀]
    rw [dif_pos hvR, dif_pos hvR]
    apply hloc
    exact havoid ⟨v, hvR⟩ (show a ≤ ℓ v by omega) (show ℓ v ≤ a + 3 by omega)
  obtain ⟨C, _, houter⟩ := AnnulusGluing.exists_coloring hlevel hγ hc hc₀ hmatch
  refine ⟨C, ?_⟩
  intro v hv
  apply houter
  have hcap : ℓ v = R + 1 := level_eq_cap_of_not_near hv
  omega

/-- Strong local repair alternative. The certificate need not itself be
non-three-colorable; its lower bound is retained unchanged by the induction. -/
theorem localized_coloring_or_certificate (t : ℕ) :
    ∀ (V : Type u) [Finite V] (G : SimpleGraph V) (c : V → Bool),
      (badEdges G c).card = t →
      (∃ C : G.Coloring (Fin 3), ∀ v,
        ¬ Near G (endVerts (badEdges G c)) (repairRadius t) v →
        C v = AnnulusGluing.boolColor (c v)) ∨
      ∃ k > 0, ∃ Q : Finset (Sym2 V),
        (Q : Set (Sym2 V)) ⊆ G.edgeSet ∧ Q.card ≤ certificateBound k ∧
          ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card := by
  classical
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro V _ G c hcount
    by_cases ht : t = 0
    · have hFempty : badEdges G c = ∅ := Finset.card_eq_zero.mp (hcount.trans ht)
      have hc : ∀ {v w : V}, G.Adj v w → c v ≠ c w := by
        intro v w hvw heq
        have hmem := (mem_badEdges G c v w).mpr ⟨hvw, heq⟩
        simp only [hFempty, Finset.notMem_empty] at hmem
      let C : G.Coloring (Fin 3) := SimpleGraph.Coloring.mk
        (fun v => AnnulusGluing.boolColor (c v))
        (fun h => AnnulusGluing.boolColor_injective.ne (hc h))
      exact Or.inl ⟨C, fun _ _ => rfl⟩
    have htpos : 0 < t := Nat.pos_of_ne_zero ht
    let T : Set V := colorBall G c (repairRadius t)
    let H : SimpleGraph T := G.induce T
    by_cases hall : ∀ d : T → Bool, t ≤ (badEdges H d).card
    · obtain ⟨Q, hQ, hcard, hmono⟩ :=
        exists_ball_certificate_of_badEdges G c (R := repairRadius t) hcount hall
      exact Or.inr ⟨t, htpos, Q, hQ, hcard, hmono⟩
    push_neg at hall
    obtain ⟨c₁, hs⟩ := hall
    let s := (badEdges H c₁).card
    have hslt : s < t := hs
    rcases ih s hslt T H c₁ rfl with hgood | hcert
    · obtain ⟨γ, hγ⟩ := hgood
      have hrad : repairRadius s ≤ repairRadius (t - 1) :=
        repairRadius_monotone (by omega)
      apply Or.inl
      apply extend_repaired_ball G c htpos (repairRadius_pred htpos) c₁ hs γ
      intro v hv
      apply hγ
      intro hvnear
      exact hv (near_mono hrad hvnear)
    · obtain ⟨k, hk, Q, hQ, hcard, hmono⟩ := hcert
      let φ : H →g G := (SimpleGraph.Embedding.induce T).toHom
      have hφ : Function.Injective φ := Subtype.val_injective
      obtain ⟨hQ', hcard', hmono'⟩ := image_certificate φ hφ hQ hcard hmono
      exact Or.inr ⟨k, hk, Q.image (Sym2.map φ), hQ', hcard', hmono'⟩

/-- Every finite graph which is not three-colorable has a uniformly bounded
finite edge certificate. -/
theorem finite_non_three_colorable_certificate
    (V : Type u) [Finite V] (G : SimpleGraph V) (hG : ¬ G.Colorable 3) :
    ∃ k > 0, ∃ Q : Finset (Sym2 V),
      (Q : Set (Sym2 V)) ⊆ G.edgeSet ∧ Q.card ≤ certificateBound k ∧
        ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card := by
  rcases localized_coloring_or_certificate (badEdges G (fun _ => false)).card
      V G (fun _ => false) rfl with h | h
  · obtain ⟨C, _⟩ := h
    exact (hG ⟨C⟩).elim
  · exact h

end Erdos74.Certificates
