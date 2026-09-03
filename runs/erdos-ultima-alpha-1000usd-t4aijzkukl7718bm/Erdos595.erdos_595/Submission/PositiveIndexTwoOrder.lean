import Submission.MycielskiFiveOrderObstruction

/-!
A normalized positive-index-two orthogonality representation has no increasing
three-edge shortcut, ordered by its second positive coordinate. The negative
part may be any positive semidefinite symmetric bilinear space over any ordered
field. This is a representation obstruction, not a solution of Erdos 595.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open SimpleGraph Set
namespace Erdos595PositiveIndexTwoOrder

variable {K E V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup E] [Module K E]
  (Q : LinearMap.BilinForm K E)
  (hs : ∀ x y, Q x y = Q y x) (hp : ∀ x, 0 ≤ Q x x)

include hs hp in
lemma energy_pair (u v : E) {a b : K} (ha : 0 < a) (hb : 0 < b) :
    Q (u+v) (u+v) / (a+b) ≤ Q u u / a + Q v v / b := by
  have h := hp (b • u - a • v)
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul] at h
  rw [← hs u v] at h
  rw [div_add_div _ _ (ne_of_gt ha) (ne_of_gt hb)]
  apply (div_le_div_iff₀ (add_pos ha hb) (mul_pos ha hb)).mpr
  simp only [map_add, LinearMap.add_apply]
  rw [← hs u v]
  nlinarith

include hs hp in
lemma energy_three (u v w : E) {a b c : K} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Q (u+v+w) (u+v+w) / (a+b+c) ≤ Q u u / a + Q v v / b + Q w w / c := by
  exact (energy_pair Q hs hp (u+v) w (add_pos ha hb) hc).trans
    (add_le_add (energy_pair Q hs hp u v ha hb) le_rfl)

variable (t : V → K) (q : V → E)

def radius (v : V) : K := 1 + t v * t v - Q (q v) (q v)

include hs in
lemma diff_formula {a b : V}
    (he : 1 + t a * t b - Q (q a) (q b) = 0) :
    Q (q b - q a) (q b - q a) =
      (t b - t a)^2 - radius Q t q a - radius Q t q b := by
  simp only [map_sub, LinearMap.sub_apply, radius]
  rw [← hs (q a) (q b)]
  nlinarith

include hs hp in
lemma edge_separates (hr : ∀ v, 0 < radius Q t q v) {a b : V}
    (he : 1 + t a * t b - Q (q a) (q b) = 0) : t a ≠ t b := by
  intro ht
  have h := hp (q b - q a)
  rw [diff_formula Q hs t q he,ht,sub_self,zero_pow (by decide : 2 ≠ 0)] at h
  have ha := hr a
  have hb := hr b
  linarith

include hs hp in
/-- The endpoint edge cannot coexist with an increasing three-edge path. -/
theorem no_shortcut (hr : ∀ v, 0 < radius Q t q v) (a b c d : V)
    (hab : 1 + t a * t b - Q (q a) (q b) = 0)
    (hbc : 1 + t b * t c - Q (q b) (q c) = 0)
    (hcd : 1 + t c * t d - Q (q c) (q d) = 0)
    (had : 1 + t a * t d - Q (q a) (q d) = 0)
    (ht : t a < t b ∧ t b < t c ∧ t c < t d) : False := by
  let x := t b - t a
  let y := t c - t b
  let z := t d - t c
  let w := t d - t a
  have hx : 0 < x := sub_pos.mpr ht.1
  have hy : 0 < y := sub_pos.mpr ht.2.1
  have hz : 0 < z := sub_pos.mpr ht.2.2
  have hw : 0 < w := sub_pos.mpr ((ht.1.trans ht.2.1).trans ht.2.2)
  have hw_eq : w = x+y+z := by dsimp [w,x,y,z]; ring
  have hE := energy_three Q hs hp (q b-q a) (q c-q b) (q d-q c) hx hy hz
  have htel : q b-q a+(q c-q b)+(q d-q c) = q d-q a := by abel
  rw [htel, ← hw_eq] at hE
  rw [diff_formula Q hs t q had,diff_formula Q hs t q hab,
    diff_formula Q hs t q hbc,diff_formula Q hs t q hcd] at hE
  change (w^2-radius Q t q a-radius Q t q d)/w ≤
    (x^2-radius Q t q a-radius Q t q b)/x +
    (y^2-radius Q t q b-radius Q t q c)/y +
    (z^2-radius Q t q c-radius Q t q d)/z at hE
  have hf (k r s : K) (hk : k ≠ 0) : (k^2-r-s)/k = k-(r+s)/k := by
    field_simp
    ring
  rw [hf _ _ _ (ne_of_gt hw),hf _ _ _ (ne_of_gt hx),
    hf _ _ _ (ne_of_gt hy),hf _ _ _ (ne_of_gt hz)] at hE
  have hax : radius Q t q a / w < (radius Q t q a + radius Q t q b)/x := by
    calc
      _ ≤ radius Q t q a / x := div_le_div_of_nonneg_left (le_of_lt (hr a)) hx
        (by rw [hw_eq]; linarith)
      _ < _ := (div_lt_div_iff_of_pos_right hx).mpr (by have := hr b; linarith)
  have hdz : radius Q t q d / w < (radius Q t q c + radius Q t q d)/z := by
    calc
      _ ≤ radius Q t q d / z := div_le_div_of_nonneg_left (le_of_lt (hr d)) hz
        (by rw [hw_eq]; linarith)
      _ < _ := (div_lt_div_iff_of_pos_right hz).mpr (by have := hr c; linarith)
  have hmid : 0 < (radius Q t q b + radius Q t q c)/y := div_pos (add_pos (hr b) (hr c)) hy
  rw [add_div] at hE
  linarith

include hs hp in
/-- The finite triangle-free Mycielski obstruction cannot have this normalized
representation, regardless of the dimension of the negative space. -/
theorem no_mycielski_normalized (t : Erdos595MycielskiFiveOrder.Vertex → K)
    (q : Erdos595MycielskiFiveOrder.Vertex → E)
    (hr : ∀ v, 0 < radius Q t q v)
    (he : ∀ a b, Erdos595MycielskiFiveOrder.graph.Adj a b →
      1 + t a * t b - Q (q a) (q b) = 0) : False := by
  obtain ⟨a,b,c,d,hab,hbc,hcd,hda,ht⟩ := Erdos595MycielskiFiveOrder.increasing_shortcut t
    (fun a b hab => edge_separates Q hs hp t q hr (he a b hab))
  exact no_shortcut Q hs hp t q hr a b c d (he a b hab) (he b c hbc)
    (he c d hcd) (he a d hda.symm) ht

#print axioms energy_pair
#print axioms no_shortcut
#print axioms no_mycielski_normalized
end Erdos595PositiveIndexTwoOrder
