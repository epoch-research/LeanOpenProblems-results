import FormalConjecturesUtil
import Submission.CertificateDefs
import OwnSubmission.Levels
import OwnSubmission.WalkCover
import Submission.RadiusCertificate

/-!
# Certificates from a ball around the bad-edge endpoints

The radius-`R` ball around the endpoints of the bad edges of a Boolean coloring
has a properly colored spanning subgraph with a radius-`R` walk cover by at most
`2 * t` roots. If every Boolean coloring of the induced ball has at least `t`
bad edges, the radius certificate therefore gives an ambient edge certificate.

The ball is expanded in the public hypothesis; no auxiliary vertex-set
definition or positivity assumption on `t` or `R` is required.
-/

namespace Erdos74.Certificates

universe u
variable {V : Type u}

/-- If the radius-`R` ball around the endpoints of the `t` bad edges of `c`
still has at least `t` bad edges under every Boolean coloring, then `G` has an
ambient certificate of size at most `radiusCertificateBound t R` forcing at
least `t` monochromatic edges under every Boolean coloring. The cap `R + 1`
ensures that the ball consists exactly of vertices with a walk of length at
most `R` to a bad-edge endpoint. -/
theorem exists_ball_certificate_of_badEdges [Finite V]
    (G : SimpleGraph V) (c : V → Bool) {t R : ℕ}
    (hcard : (badEdges G c).card = t)
    (hfar : ∀ d : {v : V // level G (endVerts (badEdges G c)) (R + 1) v ≤ R} → Bool,
      t ≤ (badEdges
        (G.induce {v : V | level G (endVerts (badEdges G c)) (R + 1) v ≤ R}) d).card) :
    ∃ Q : Finset (Sym2 V), (Q : Set (Sym2 V)) ⊆ G.edgeSet ∧
      Q.card ≤ radiusCertificateBound t R ∧
      ∀ d : V → Bool, t ≤ (Q.filter (mono d)).card := by
  classical
  let F := badEdges G c
  let S := endVerts F
  let ℓ := level G S (R + 1)
  let T : Set V := {v | ℓ v ≤ R}
  let H := G.induce T
  let B := (G.deleteEdges (F : Set (Sym2 V))).induce T
  have hBH : B ≤ H := fun _ _ h => (SimpleGraph.deleteEdges_adj.mp h).1
  let c0 : T → Bool := fun v => c v
  have hc : ∀ ⦃v w : T⦄, B.Adj v w → c0 v ≠ c0 w :=
    fun _ _ h => proper_delete_badEdges G c h
  let f : S → T := fun s => ⟨s.val, by
    change level G S (R + 1) s.val ≤ R
    rw [level_zero_of_mem s.property]
    exact Nat.zero_le R⟩
  let S_H : Finset T := S.attach.image f
  have hScard : S_H.card ≤ 2 * t := by
    calc
      S_H.card ≤ S.attach.card := Finset.card_image_le
      _ = S.card := Finset.card_attach
      _ ≤ 2 * F.card := card_endVerts_le F
      _ = 2 * t := by rw [show F.card = t from hcard]
  have hℓ : ∀ {x y : V}, (G.deleteEdges (F : Set (Sym2 V))).Adj x y →
      ℓ x ≤ ℓ y + 1 :=
    fun h => level_adj_le (SimpleGraph.deleteEdges_adj.mp h).1
  have hcover : ∀ v : T, ∃ s ∈ S_H, ∃ p : B.Walk v s, p.length ≤ R := by
    intro v
    have hv : level G S (R + 1) (v : V) ≤ R := v.property
    obtain ⟨s, hs, p, hp⟩ := (level_le_iff_near (Nat.lt_succ_self R)).mp hv
    obtain ⟨r, hr, q, hq⟩ := walk_to_endVerts_after_deletion F hs p
    let r' : T := f ⟨r, hr⟩
    have hroot : ℓ (r' : V) = 0 := level_zero_of_mem hr
    obtain ⟨q', hq'⟩ := exists_induced_walk_of_level_zero hℓ
      (v := v) (root := r') hroot q (hq.trans hp)
    refine ⟨r', ?_, q', hq'.le.trans (hq.trans hp)⟩
    exact Finset.mem_image.mpr ⟨⟨r, hr⟩, Finset.mem_attach S _, rfl⟩
  obtain ⟨Q_H, hQH, hQcard, hQmono⟩ :=
    exists_radius_certificate_of_badEdges hBH c0 hc S_H hScard hcover hfar
  let incl : H →g G := (SimpleGraph.Embedding.induce T).toHom
  exact ⟨Q_H.image (Sym2.map incl),
    image_certificate incl Subtype.val_injective hQH hQcard hQmono⟩

end Erdos74.Certificates
