import FormalConjecturesUtil

/-! Four exact cross-ratio obstructions in the nine x-coordinates of an
explicit full Z/3 x Z/6 torsion model. The theorem is over all complex
parameters and even allows arbitrary positive real endpoint weights.
It is a restricted construction obstruction, not a settlement of Erdos 213. -/
namespace Erdos213.TorsionThreeSixX
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

def rr : ℂ := (Real.sqrt 3 : ℂ)*Complex.I

lemma rr_sq : rr^2=-3 := by
  rw [rr,mul_pow,Complex.I_sq,← Complex.ofReal_pow]
  norm_num [Real.sq_sqrt]

lemma rr_cube : rr^3=-3*rr := by rw [pow_succ,rr_sq]

lemma constant_norms : Complex.normSq (3+rr)=12 ∧ Complex.normSq (3-rr)=12 := by
  norm_num [Complex.normSq_apply,rr,Real.mul_self_sqrt (by norm_num : (0 : ℝ)≤3)]

/-- Rational lengths after arbitrary positive real endpoint factors. -/
def Weighted {ι : Type*} (p : ι → ℂ) : Prop :=
  ∃ l : ι → ℝ, (∀ i, 0<l i) ∧ ∀ i j, i≠j →
    l i*l j*dist (p i) (p j)∈Set.range ((↑) : ℚ → ℝ)

lemma Weighted.comp {ι κ : Type*} {p : ι → ℂ} (h : Weighted p)
    (f : κ → ι) (hf : Function.Injective f) : Weighted (p ∘ f) := by
  obtain ⟨l,hl,he⟩ := h
  exact ⟨l ∘ f,fun i => hl (f i),fun i j hij => he (f i) (f j) (hf.ne hij)⟩

lemma norm_three_of_cross {a b c d : ℂ}
    (h : 2*(a-b)*(c-d)=(3+rr)*(b-c)*(d-a) ∨
      2*(a-b)*(c-d)=(3-rr)*(b-c)*(d-a)) :
    Complex.normSq (a-b)*Complex.normSq (c-d) =
      3*(Complex.normSq (b-c)*Complex.normSq (d-a)) := by
  have hn2 : Complex.normSq (2 : ℂ)=4 := by norm_num [Complex.normSq_apply]
  rcases h with h | h
  · have he := congrArg Complex.normSq h
    simp only [map_mul,hn2,constant_norms.1] at he
    nlinarith only [he]
  · have he := congrArg Complex.normSq h
    simp only [map_mul,hn2,constant_norms.2] at he
    nlinarith only [he]

/-- A cross-ratio of squared norm three is an obstruction even when the
original squared distances need not be rational. -/
lemma four_not_weighted (p : Fin 4 → ℂ) (hp : Function.Injective p)
    (hN : Complex.normSq (p 0-p 1)*Complex.normSq (p 2-p 3) =
      3*(Complex.normSq (p 1-p 2)*Complex.normSq (p 3-p 0))) : ¬Weighted p := by
  rintro ⟨l,hl,he⟩
  obtain ⟨u,hu⟩ := he 0 1 (by decide)
  obtain ⟨v,hv⟩ := he 1 2 (by decide)
  obtain ⟨w,hw⟩ := he 2 3 (by decide)
  obtain ⟨z,hz⟩ := he 3 0 (by decide)
  have hs {i j : Fin 4} {q : ℚ} (h : (q : ℝ)=l i*l j*dist (p i) (p j)) :
      (q : ℝ)^2=(l i)^2*(l j)^2*Complex.normSq (p i-p j) := by
    rw [h,mul_pow,mul_pow,dist_eq_norm,Complex.normSq_eq_norm_sq]
  have hidR : (u : ℝ)^2*(w : ℝ)^2=3*((v : ℝ)^2*(z : ℝ)^2) := by
    rw [hs hu,hs hv,hs hw,hs hz]
    linear_combination (l 0)^2*(l 1)^2*(l 2)^2*(l 3)^2*hN
  have hid : u^2*w^2=3*(v^2*z^2) := by exact_mod_cast hidR
  have hv0 : v≠0 := by
    have hd : 0<dist (p 1) (p 2) := dist_pos.mpr (hp.ne (by decide))
    have hh : 0<(v : ℝ) := by rw [hv]; exact mul_pos (mul_pos (hl 1) (hl 2)) hd
    exact_mod_cast (ne_of_gt hh)
  have hz0 : z≠0 := by
    have hd : 0<dist (p 3) (p 0) := dist_pos.mpr (hp.ne (by decide))
    have hh : 0<(z : ℝ) := by rw [hz]; exact mul_pos (mul_pos (hl 3) (hl 0)) hd
    exact_mod_cast (ne_of_gt hh)
  have hsq : (u*w/(v*z))^2=3 := by
    field_simp
    nlinarith only [hid]
  have hn : ¬IsSquare (3 : ℚ) := by norm_num
  exact hn ⟨u*w/(v*z),by nlinarith only [hsq]⟩

/-- The common degree-six term of the torsion coordinates was translated away
and all coordinates were scaled by nine. These changes preserve cross-ratios. -/
def points (s : ℂ) : Fin 9 → ℂ :=
  ![24*s^3+12,
    4*s^6+16*s^3+16,
    (6*rr+6)*s^4+(-18*rr+18)*s^2+(12*rr+12)*s,
    (-6*rr+6)*s^4+(18*rr+18)*s^2+(-12*rr+12)*s,
    -12*s^4-36*s^2-24*s,
    -12*s^3+48,
    (6*rr-6)*s^5+(12*rr+12)*s^4+36*s^3+(-6*rr+6)*s^2+(-12*rr-12)*s,
    (-6*rr-6)*s^5+(-12*rr+12)*s^4+36*s^3+(6*rr+6)*s^2+(12*rr-12)*s,
    12*s^5-24*s^4+36*s^3-12*s^2+24*s]

lemma cycleA (s : ℂ) :
    2*(points s 1-points s 2)*(points s 7-points s 8) =
      (3-rr)*(points s 2-points s 7)*(points s 8-points s 1) := by
  dsimp [points]
  ring_nf
  all_goals try simp only [rr_sq,rr_cube]
  all_goals ring

lemma cycleB (s : ℂ) :
    2*(points s 2-points s 3)*(points s 5-points s 8) =
      (3-rr)*(points s 3-points s 5)*(points s 8-points s 2) := by
  dsimp [points]
  ring_nf
  all_goals try simp only [rr_sq,rr_cube]
  all_goals ring

lemma cycleC (s : ℂ) :
    2*(points s 1-points s 3)*(points s 6-points s 8) =
      (3+rr)*(points s 3-points s 6)*(points s 8-points s 1) := by
  dsimp [points]
  ring_nf
  all_goals try simp only [rr_sq,rr_cube]
  all_goals ring

lemma cycleD (s : ℂ) :
    2*(points s 1-points s 4)*(points s 6-points s 7) =
      (3-rr)*(points s 4-points s 6)*(points s 7-points s 1) := by
  dsimp [points]
  ring_nf
  all_goals try simp only [rr_sq,rr_cube]
  all_goals ring

/-- Each row avoids its index. The four displayed cycles cover every deletion
of one of the nine points. -/
def cycle (k : Fin 9) : Fin 4 → Fin 9 :=
  (![![1,2,7,8],![2,3,5,8],![1,3,6,8],![1,2,7,8],![1,2,7,8],
      ![1,2,7,8],![1,2,7,8],![1,3,6,8],![1,4,6,7]]) k

lemma cycle_avoids : ∀ k : Fin 9, ∀ i : Fin 4, cycle k i≠k := by decide
lemma cycle_injective : ∀ k : Fin 9, Function.Injective (cycle k) := by decide

def selected (k : Fin 9) (i : Fin 4) : {j : Fin 9 // j≠k} :=
  ⟨cycle k i,cycle_avoids k i⟩

lemma selected_injective (k : Fin 9) : Function.Injective (selected k) := by
  intro i j h
  exact cycle_injective k (congrArg Subtype.val h)

lemma cycle_norms (s : ℂ) (k : Fin 9) :
    Complex.normSq (points s (cycle k 0)-points s (cycle k 1))*
      Complex.normSq (points s (cycle k 2)-points s (cycle k 3)) =
    3*(Complex.normSq (points s (cycle k 1)-points s (cycle k 2))*
      Complex.normSq (points s (cycle k 3)-points s (cycle k 0))) := by
  apply norm_three_of_cross
  fin_cases k <;> simp only [cycle,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_succ]
  · exact Or.inr (cycleA s)
  · exact Or.inr (cycleB s)
  · exact Or.inl (cycleC s)
  · exact Or.inr (cycleA s)
  · exact Or.inr (cycleA s)
  · exact Or.inr (cycleA s)
  · exact Or.inr (cycleA s)
  · exact Or.inl (cycleC s)
  · exact Or.inr (cycleD s)

/-- No eight distinct points from this nine-point model can have rational
weighted lengths. This excludes arbitrary complex parameters, not merely
parameters in a quadratic number field. -/
theorem eight_not_weighted (s : ℂ) (k : Fin 9)
    (hp : Function.Injective (fun i : {j : Fin 9 // j≠k} => points s i)) :
    ¬Weighted (fun i : {j : Fin 9 // j≠k} => points s i) := by
  intro h
  have hh := h.comp (selected k) (selected_injective k)
  exact four_not_weighted _ (hp.comp (selected_injective k)) (cycle_norms s k) hh

/-- Finset version: all eight-element selections are covered, even when a
ninth coordinate collides with one of the selected values. -/
theorem finset_eight_not_weighted (s : ℂ) (S : Finset (Fin 9)) (hS : S.card=8)
    (hp : Function.Injective (fun i : S => points s i)) :
    ¬Weighted (fun i : S => points s i) := by
  have hc : Sᶜ.card=1 := by rw [Finset.card_compl,hS]; norm_num
  obtain ⟨k,hk⟩ := Finset.card_eq_one.mp hc
  have hm (i : Fin 9) (hi : i≠k) : i∈S := by
    by_contra h
    have hh : i∈Sᶜ := Finset.mem_compl.mpr h
    rw [hk,Finset.mem_singleton] at hh
    exact hi hh
  let f : {i : Fin 9 // i≠k} → S := fun i => ⟨i,hm i i.property⟩
  have hf : Function.Injective f := by
    intro i j h
    apply Subtype.ext
    exact congrArg (fun x : S => (x : Fin 9)) h
  intro h
  exact eight_not_weighted s k (hp.comp hf) (h.comp f hf)

/-- Inverting about an arbitrary center and then applying any positive real
scale cannot evade the four-cycle obstruction. -/
theorem eight_not_inverted (s : ℂ) (k : Fin 9)
    (hp : Function.Injective (fun i : {j : Fin 9 // j≠k} => points s i))
    (o : ℂ) (ho : ∀ i : {j : Fin 9 // j≠k}, points s i≠o)
    (A : ℝ) (hA : 0<A) :
    ¬(∀ i j : {j : Fin 9 // j≠k}, i≠j →
      A*dist (EuclideanGeometry.inversion o 1 (points s i))
        (EuclideanGeometry.inversion o 1 (points s j))∈Set.range ((↑) : ℚ → ℝ)) := by
  intro h
  apply eight_not_weighted s k hp
  let l := fun i : {j : Fin 9 // j≠k} => Real.sqrt A/dist (points s i) o
  have hd (i : {j : Fin 9 // j≠k}) : 0<dist (points s i) o := dist_pos.mpr (ho i)
  refine ⟨l,fun i => div_pos (Real.sqrt_pos.mpr hA) (hd i),?_⟩
  intro i j hij
  have he : l i*l j*dist (points s i) (points s j) =
      A*dist (EuclideanGeometry.inversion o 1 (points s i))
        (EuclideanGeometry.inversion o 1 (points s j)) := by
    rw [EuclideanGeometry.dist_inversion_inversion (ho i) (ho j)]
    dsimp [l]
    rw [one_pow]
    have hi := ne_of_gt (hd i)
    have hj := ne_of_gt (hd j)
    field_simp
    linear_combination dist (points s i) (points s j)*(Real.sq_sqrt hA.le)
  rw [he]
  exact h i j hij

#print axioms finset_eight_not_weighted
#print axioms eight_not_inverted
#print axioms four_not_weighted
#print axioms cycleA
#print axioms cycleB
#print axioms cycleC
#print axioms cycleD
#print axioms eight_not_weighted
end
end Erdos213.TorsionThreeSixX
