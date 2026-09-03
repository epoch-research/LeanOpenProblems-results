import Submission.TetrahedralArithmetic
import Mathlib.Tactic

/-! Arithmetic needed to diagnose a restricted elliptic-division construction.
No existence or nonexistence of perfect cuboids is assumed. -/
namespace Erdos213.CommonFaceClass
open TetrahedralArithmetic
set_option maxHeartbeats 1000000

lemma integer_primitive_scale (a b c : ℤ) (h : a^2+b^2 ≠ 0) :
    ∃ t A B C : ℤ, t ≠ 0 ∧ a=t*A ∧ b=t*B ∧ c=t*C ∧ Primitive A B C := by
  let g : ℤ := Int.gcd a b
  let t : ℤ := Int.gcd g c
  have hta : t ∣ a := (Int.gcd_dvd_left g c).trans (Int.gcd_dvd_left a b)
  have htb : t ∣ b := (Int.gcd_dvd_left g c).trans (Int.gcd_dvd_right a b)
  have htc : t ∣ c := Int.gcd_dvd_right g c
  have ht : t ≠ 0 := by
    intro hz
    rw [hz,zero_dvd_iff] at hta htb
    exact h (by simp [hta,htb])
  obtain ⟨A,hA⟩ := hta
  obtain ⟨B,hB⟩ := htb
  obtain ⟨C,hC⟩ := htc
  refine ⟨t,A,B,C,ht,hA,hB,hC,?_⟩
  refine ⟨Int.gcdA a b*Int.gcdA g c,Int.gcdB a b*Int.gcdA g c,Int.gcdB g c,?_⟩
  apply mul_left_cancel₀ ht
  have hg : g=a*Int.gcdA a b+b*Int.gcdB a b := Int.gcd_eq_gcd_ab a b
  have htt : t=g*Int.gcdA g c+c*Int.gcdB g c := Int.gcd_eq_gcd_ab g c
  calc
    t*((Int.gcdA a b*Int.gcdA g c)*A+(Int.gcdB a b*Int.gcdA g c)*B+
        Int.gcdB g c*C) = (a*Int.gcdA a b+b*Int.gcdB a b)*Int.gcdA g c+
          c*Int.gcdB g c := by rw [hA,hB,hC]; ring
    _ = t*1 := by rw [← hg,← htt,mul_one]

lemma rational_primitive_scale (a b c : ℚ) (h : 0<a^2+b^2) :
    ∃ t : ℚ, ∃ A B C : ℤ, t ≠ 0 ∧ a=t*A ∧ b=t*B ∧ c=t*C ∧ Primitive A B C := by
  let L : ℕ := a.den*b.den*c.den
  let A₀ : ℤ := a.num*b.den*c.den
  let B₀ : ℤ := b.num*a.den*c.den
  let C₀ : ℤ := c.num*a.den*b.den
  have hL : (L : ℚ) ≠ 0 := by
    dsimp [L]; exact_mod_cast mul_ne_zero (mul_ne_zero a.den_ne_zero b.den_ne_zero) c.den_ne_zero
  have ha : (A₀ : ℚ)=(L : ℚ)*a := by
    dsimp [A₀,L]; push_cast
    linear_combination -(b.den : ℚ)*c.den*(Rat.den_mul_eq_num a)
  have hb : (B₀ : ℚ)=(L : ℚ)*b := by
    dsimp [B₀,L]; push_cast
    linear_combination -(a.den : ℚ)*c.den*(Rat.den_mul_eq_num b)
  have hc : (C₀ : ℚ)=(L : ℚ)*c := by
    dsimp [C₀,L]; push_cast
    linear_combination -(a.den : ℚ)*b.den*(Rat.den_mul_eq_num c)
  have h₀ : A₀^2+B₀^2 ≠ 0 := by
    intro hz
    have hzQ : (A₀ : ℚ)^2+(B₀ : ℚ)^2=0 := by exact_mod_cast hz
    rw [ha,hb] at hzQ
    have he : (L : ℚ)^2*(a^2+b^2)=0 := by nlinarith only [hzQ]
    exact (mul_ne_zero (pow_ne_zero _ hL) (ne_of_gt h)) he
  obtain ⟨m,A,B,C,hm,hA,hB,hC,hp⟩ := integer_primitive_scale A₀ B₀ C₀ h₀
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  refine ⟨(m : ℚ)/L,A,B,C,div_ne_zero hmQ hL,?_,?_,?_,hp⟩
  · have he : (A₀ : ℚ)=(m : ℚ)*A := by exact_mod_cast hA
    field_simp
    nlinarith only [ha,he]
  · have he : (B₀ : ℚ)=(m : ℚ)*B := by exact_mod_cast hB
    field_simp
    nlinarith only [hb,he]
  · have he : (C₀ : ℚ)=(m : ℚ)*C := by exact_mod_cast hC
    field_simp
    nlinarith only [hc,he]

lemma squarefree_class_integral {D : ℕ} (hD : Squarefree D) (hD0 : D ≠ 0)
    (N : ℤ) (hs : IsSquare ((N : ℚ)/(D : ℚ))) :
    ∃ t : ℤ, N=(D : ℤ)*t^2 := by
  have hDi : (D : ℤ) ≠ 0 := by exact_mod_cast hD0
  have hDQ : (D : ℚ) ≠ 0 := by exact_mod_cast hD0
  have hh : IsSquare (((D : ℤ)*N : ℤ) : ℚ) := by
    convert (IsSquare.sq (D : ℚ)).mul hs using 1
    push_cast
    field_simp
  obtain ⟨z,hz⟩ := Rat.isSquare_intCast_iff.mp hh
  have hd : (D : ℤ) ∣ z^2 := by rw [pow_two,← hz]; exact dvd_mul_right _ _
  have hzD : (D : ℤ) ∣ z :=
    ((Int.squarefree_natCast.mpr hD).dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)).mp hd
  obtain ⟨t,ht⟩ := hzD
  refine ⟨t,?_⟩
  apply mul_left_cancel₀ hDi
  rw [hz,ht]
  ring

set_option synthInstance.maxSize 10000 in
private lemma mod_four_faces_body : ∀ a b c : ZMod 4,
    (∃ u, a^2+b^2=2*u^2) → (∃ v, a^2+c^2=2*v^2) → (∃ w, b^2+c^2=2*w^2) →
    IsSquare (a^2+b^2+c^2) → a.val%2=0 ∧ b.val%2=0 ∧ c.val%2=0 := by
  decide

lemma primitive_two_class_no_square_body (a b c : ℤ) (hp : Primitive a b c)
    (hab : ∃ u : ℤ, a^2+b^2=2*u^2) (hac : ∃ v : ℤ, a^2+c^2=2*v^2)
    (hbc : ∃ w : ℤ, b^2+c^2=2*w^2) : ¬ IsSquare (a^2+b^2+c^2) := by
  intro hs
  obtain ⟨u,hu⟩ := hab
  obtain ⟨v,hv⟩ := hac
  obtain ⟨w,hw⟩ := hbc
  have h1 : (a : ZMod 4)^2+(b : ZMod 4)^2=2*(u : ZMod 4)^2 := by simpa using congrArg ((↑) : ℤ → ZMod 4) hu
  have h2 : (a : ZMod 4)^2+(c : ZMod 4)^2=2*(v : ZMod 4)^2 := by simpa using congrArg ((↑) : ℤ → ZMod 4) hv
  have h3 : (b : ZMod 4)^2+(c : ZMod 4)^2=2*(w : ZMod 4)^2 := by simpa using congrArg ((↑) : ℤ → ZMod 4) hw
  have h4 : IsSquare ((a : ZMod 4)^2+(b : ZMod 4)^2+(c : ZMod 4)^2) := by
    simpa using hs.map (Int.castRingHom (ZMod 4))
  obtain ⟨ha,hb,hc⟩ := mod_four_faces_body _ _ _ ⟨u,h1⟩ ⟨v,h2⟩ ⟨w,h3⟩ h4
  have even (z : ℤ) (hz : (z : ZMod 4).val%2=0) : (2 : ℤ) ∣ z := by
    have hh : (((z : ZMod 4).val : ℤ)%2)=0 := by exact_mod_cast hz
    rw [ZMod.val_intCast] at hh
    norm_num only [Nat.cast_ofNat] at hh
    rw [Int.emod_emod_of_dvd _ (by norm_num : (2 : ℤ) ∣ 4)] at hh
    exact Int.dvd_of_emod_eq_zero hh
  obtain ⟨r,s,t,hp⟩ := hp
  have hd : (2 : ℤ) ∣ 1 := by
    rw [← hp]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_right (even a ha) r)
      (dvd_mul_of_dvd_right (even b hb) s)) (dvd_mul_of_dvd_right (even c hc) t)
  norm_num at hd

lemma primitive_common_faces (a b c : ℤ) (hp : Primitive a b c) (hN : 0<a^2+b^2)
    (hac : IsSquare (((a : ℚ)^2+c^2)/((a : ℚ)^2+b^2)))
    (hbc : IsSquare (((b : ℚ)^2+c^2)/((a : ℚ)^2+b^2)))
    (hbody : IsSquare (a^2+b^2+c^2)) : IsSquare (a^2+b^2) := by
  have hn : 0 < (a^2+b^2).natAbs := Int.natAbs_pos.mpr (ne_of_gt hN)
  obtain ⟨D,u,hD0,hu0,hde,hD⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hdeZ : (a^2+b^2)=(u : ℤ)^2*D := by
    have hh := congrArg (fun x : ℕ => (x : ℤ)) hde
    simpa only [Nat.cast_mul,Nat.cast_pow,Int.natAbs_of_nonneg (le_of_lt hN)] using hh.symm
  have hdeQ : (a : ℚ)^2+b^2=(u : ℚ)^2*D := by exact_mod_cast hdeZ
  have hDQ : (D : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hD0
  have hNQ : (a : ℚ)^2+b^2 ≠ 0 := by exact_mod_cast ne_of_gt hN
  have hbase : IsSquare (((a : ℚ)^2+b^2)/(D : ℚ)) := by
    rw [hdeQ,mul_div_cancel_right₀ _ hDQ]
    exact IsSquare.sq _
  have hAC : IsSquare (((a^2+c^2 : ℤ) : ℚ)/(D : ℚ)) := by
    convert hac.mul hbase using 1
    push_cast
    field_simp
  have hBC : IsSquare (((b^2+c^2 : ℤ) : ℚ)/(D : ℚ)) := by
    convert hbc.mul hbase using 1
    push_cast
    field_simp
  obtain ⟨v,hv⟩ := squarefree_class_integral hD (ne_of_gt hD0) (a^2+c^2) hAC
  obtain ⟨w,hw⟩ := squarefree_class_integral hD (ne_of_gt hD0) (b^2+c^2) hBC
  have hd : D ∣ 2 := common_face_squareclass_dvd_two hD hp
    ⟨(u : ℤ)^2,by rw [hdeZ]; ring⟩ ⟨v^2,hv⟩ ⟨w^2,hw⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · subst D
    exact ⟨u,by simpa [pow_two] using hdeZ⟩
  · subst D
    exact False.elim (primitive_two_class_no_square_body a b c hp
      ⟨u,by simpa [mul_comm] using hdeZ⟩ ⟨v,by simpa using hv⟩ ⟨w,by simpa using hw⟩ hbody)

/-- With a rational space diagonal, a common square class for the three face
diagonals must actually be the rational-square class. -/
theorem common_faces_square (a b c : ℚ) (hN : 0<a^2+b^2)
    (hac : IsSquare ((a^2+c^2)/(a^2+b^2))) (hbc : IsSquare ((b^2+c^2)/(a^2+b^2)))
    (hbody : IsSquare (a^2+b^2+c^2)) : IsSquare (a^2+b^2) := by
  obtain ⟨t,A,B,C,ht,ha,hb,hc,hp⟩ := rational_primitive_scale a b c hN
  have hT : t^2 ≠ 0 := pow_ne_zero _ ht
  have he : a^2+b^2=t^2*((A : ℚ)^2+B^2) := by rw [ha,hb]; ring
  have hAC : (a^2+c^2)/(a^2+b^2)=((A : ℚ)^2+C^2)/((A : ℚ)^2+B^2) := by
    rw [ha,hb,hc]
    field_simp
  have hBC : (b^2+c^2)/(a^2+b^2)=((B : ℚ)^2+C^2)/((A : ℚ)^2+B^2) := by
    rw [ha,hb,hc]
    field_simp
  have hN' : 0<A^2+B^2 := by
    have hq : 0<(A : ℚ)^2+B^2 := by nlinarith [sq_nonneg t]
    exact_mod_cast hq
  have hbody' : IsSquare (A^2+B^2+C^2) := by
    apply Rat.isSquare_intCast_iff.mp
    convert hbody.div (IsSquare.sq t) using 1
    push_cast
    rw [ha,hb,hc]
    field_simp
  have hh := (primitive_common_faces A B C hp hN' (hAC ▸ hac) (hBC ▸ hbc) hbody').map (Int.castRingHom ℚ)
  rw [he]
  exact (IsSquare.sq t).mul (by simpa using hh)

#print axioms primitive_two_class_no_square_body
#print axioms common_faces_square
end Erdos213.CommonFaceClass
