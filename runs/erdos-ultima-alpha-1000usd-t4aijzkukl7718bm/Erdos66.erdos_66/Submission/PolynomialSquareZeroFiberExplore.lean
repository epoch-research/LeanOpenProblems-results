import FormalConjecturesUtil

/-! Polynomial graphs modulo q^2 are affine on every input residue class
modulo q. Their within-class group sums have at most q possible values. -/
namespace Erdos66PolynomialSquareZeroFiber
open scoped Classical
set_option maxHeartbeats 1800000

variable (q : ℕ) [NeZero q]

noncomputable def residue (x : ZMod (q^2)) : Fin q :=
  ⟨x.val % q, Nat.mod_lt _ (NeZero.pos q)⟩

noncomputable def fiber (B : Finset (ZMod (q^2))) (r : Fin q) : Finset (ZMod (q^2)) :=
  B.filter (fun x ↦ residue q x = r)

lemma residue_val (x : ZMod (q^2)) : (residue q x).val = x.val % q := rfl

lemma offset_square_zero (x : ZMod (q^2)) (r : Fin q) (hx : residue q x = r) :
    (x-(r.val : ZMod (q^2)))^2 = 0 := by
  have hr : x.val % q = r.val := congrArg Fin.val hx
  have he := Nat.mod_add_div x.val q
  rw [hr] at he
  have he' : (r.val : ZMod (q^2))+(q : ZMod (q^2))*(x.val/q : ℕ) = x := by
    simpa only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val] using
      congrArg (fun n : ℕ ↦ (n : ZMod (q^2))) he
  have hsq : (q : ZMod (q^2))^2 = 0 := by rw [← Nat.cast_pow,ZMod.natCast_self]
  rw [← he',add_sub_cancel_left,mul_pow,hsq,zero_mul]

lemma eval_affine_on_fiber (P : Polynomial (ZMod (q^2))) (x : ZMod (q^2))
    (r : Fin q) (hx : residue q x = r) :
    P.eval x = P.eval (r.val : ZMod (q^2))+
      P.derivative.eval (r.val : ZMod (q^2))*(x-(r.val : ZMod (q^2))) := by
  have hh := Polynomial.eval_add_of_sq_eq_zero P (r.val : ZMod (q^2))
    (x-(r.val : ZMod (q^2))) (offset_square_zero q x r hx)
  rw [show (r.val : ZMod (q^2))+(x-(r.val : ZMod (q^2)))=x by ring] at hh
  exact hh

noncomputable def graph (P : Polynomial (ZMod (q^2))) (x : ZMod (q^2)) : ZMod (q^2) × ZMod (q^2) :=
  (x,P.eval x)

noncomputable def tangentSum (P : Polynomial (ZMod (q^2))) (r : Fin q)
    (s : ZMod (q^2)) : ZMod (q^2) × ZMod (q^2) :=
  (s,2*P.eval (r.val : ZMod (q^2))+
    P.derivative.eval (r.val : ZMod (q^2))*(s-2*(r.val : ZMod (q^2))))

lemma same_fiber_graph_sum (P : Polynomial (ZMod (q^2))) (r : Fin q)
    (x y : ZMod (q^2)) (hx : residue q x = r) (hy : residue q y = r) :
    graph q P x+graph q P y = tangentSum q P r (x+y) := by
  apply Prod.ext
  · rfl
  · change P.eval x+P.eval y = _
    rw [eval_affine_on_fiber q P x r hx,eval_affine_on_fiber q P y r hy]
    dsimp [tangentSum]
    ring

noncomputable def sumValue (r i : Fin q) : ZMod (q^2) :=
  (((2*r.val)%q+q*i.val : ℕ) : ZMod (q^2))

lemma sumValue_exists (r : Fin q) (x y : ZMod (q^2))
    (hx : residue q x = r) (hy : residue q y = r) :
    ∃ i : Fin q, x+y = sumValue q r i := by
  have hx' : x.val%q = r.val := congrArg Fin.val hx
  have hy' : y.val%q = r.val := congrArg Fin.val hy
  have hq : q ∣ q^2 := by simpa only [pow_two] using Nat.dvd_mul_right q q
  have hmod : (x+y).val%q = (2*r.val)%q := by
    rw [ZMod.val_add,Nat.mod_mod_of_dvd _ hq,Nat.add_mod,hx',hy']
    congr 1
    omega
  have hval := ZMod.val_lt (x+y)
  have hdiv : (x+y).val/q < q := (Nat.div_lt_iff_lt_mul (NeZero.pos q)).mpr (by nlinarith)
  refine ⟨⟨(x+y).val/q,hdiv⟩,?_⟩
  have he := Nat.mod_add_div (x+y).val q
  rw [hmod] at he
  change x+y = (((2*r.val)%q+q*((x+y).val/q) : ℕ) : ZMod (q^2))
  rw [he,ZMod.natCast_zmod_val]

lemma within_fiber_sum_values (P : Polynomial (ZMod (q^2))) (r : Fin q)
    (x y : ZMod (q^2)) (hx : residue q x = r) (hy : residue q y = r) :
    ∃ i : Fin q, graph q P x+graph q P y = tangentSum q P r (sumValue q r i) := by
  obtain ⟨i,hi⟩ := sumValue_exists q r x y hx hy
  exact ⟨i,by rw [same_fiber_graph_sum q P r x y hx hy,hi]⟩

end Erdos66PolynomialSquareZeroFiber
