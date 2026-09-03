import FormalConjecturesUtil

/-! Index-two star assignments avoid the involutive product relation.
They can be realized as voltage ratios when cubing is surjective.
This shows a genuine limitation of the odd-order counting route; it is
not a C8-free construction and not a disproof of the main conjecture. -/
namespace Erdos713InvolutiveEvenStar
variable {J I W Q : Type*} [CommGroup W] [Group Q]
set_option maxHeartbeats 1000000

def flip (p : J × Bool) : J × Bool := (p.1,!p.2)

def star (g : J → W) (b : W) (p : J × Bool) : W := if p.2 then b else g p.1

lemma flip_involutive : Function.Involutive (flip (J := J)) := by
  rintro ⟨j,e⟩
  simp [flip]

lemma flip_ne (p : J × Bool) : flip p ≠ p := by
  rcases p with ⟨j,e⟩
  cases e <;> simp [flip]

lemma fst_ne_of_exclusions {c r : J × Bool} (h : c ≠ r) (h' : c ≠ flip r) : c.1 ≠ r.1 := by
  rcases c with ⟨c,e⟩
  rcases r with ⟨r,f⟩
  intro he
  dsimp at he
  subst r
  cases e <;> cases f <;> simp_all [flip]

lemma star_pair (g : J → W) (b : W) (c : J × Bool) :
    star g b c * star g b (flip c) = g c.1*b := by
  rcases c with ⟨j,e⟩
  cases e <;> simp [star,flip,mul_comm]

/-- An injective list in the kernel, paired with one constant outside it,
avoids every nondegenerate involutive product relation. -/
theorem star_avoid (g : J → W) (hg : Function.Injective g) (b : W) (χ : W →* Q)
    (hker : ∀ j, χ (g j)=1) (hb : χ b ≠ 1) (hb2 : (χ b)^2=1)
    (c r d : J × Bool) (hcr : c ≠ r) (hcr' : c ≠ flip r)
    (hcd : c ≠ d) (hcd' : c ≠ flip d) :
    star g b c*star g b (flip c) ≠ star g b r*star g b d := by
  have hr := fst_ne_of_exclusions hcr hcr'
  have hd := fst_ne_of_exclusions hcd hcd'
  rw [star_pair]
  intro he
  rcases r with ⟨r,e⟩
  rcases d with ⟨d,f⟩
  cases e <;> cases f
  · have hh := congrArg χ he
    simp only [star,Bool.false_eq_true,if_false,map_mul,hker,one_mul,mul_one] at hh
    exact hb hh
  · have hh : g c.1*b=g r*b := he
    exact hr (hg (mul_right_cancel hh))
  · have hh : g c.1*b=g d*b := he.trans (mul_comm _ _)
    exact hd (hg (mul_right_cancel hh))
  · have hh := congrArg χ he
    simp only [star,if_true,map_mul,hker,one_mul] at hh
    exact hb (hh.trans (by rw [← pow_two,hb2]))

/-- Cubing being surjective is enough to realize every proposed ratio
B(i)=f(i)^2/f(tau(i)); no homomorphism condition on B is needed. -/
theorem realize_ratio (τ : I → I) (hτ : Function.Involutive τ) (B : I → W)
    (hpow : Function.Surjective (fun w : W => w^3)) :
    ∃ f : I → W, ∀ i, f i^2*(f (τ i))⁻¹=B i := by
  classical
  choose u hu using (fun i => hpow (B i))
  refine ⟨fun i => u i^2*u (τ i),?_⟩
  intro i
  dsimp only
  rw [hτ i]
  calc
    (u i^2*u (τ i))^2*(u (τ i)^2*u i)⁻¹ =
        (u i*(u i)⁻¹)*(u (τ i)*(u (τ i))⁻¹)*(u (τ i)*(u (τ i))⁻¹)*u i^3 := by
      simp only [pow_succ,pow_zero,mul_inv_rev,one_mul]
      ac_rfl
    _ = u i^3 := by simp
    _ = _ := hu i

/-- The cyclic even-order example, before realizing its ratios. -/
theorem cyclic_star (n : ℕ) :
    ∃ B : (Fin n × Bool) → Multiplicative (ZMod (2*n)),
      ∀ c r d, c ≠ r → c ≠ flip r → c ≠ d → c ≠ flip d →
        B c*B (flip c) ≠ B r*B d := by
  let g : Fin n → Multiplicative (ZMod (2*n)) := fun j =>
    Multiplicative.ofAdd ((2*j.val : ℕ) : ZMod (2*n))
  let b : Multiplicative (ZMod (2*n)) := Multiplicative.ofAdd 1
  let χ : Multiplicative (ZMod (2*n)) →* Multiplicative (ZMod 2) :=
    AddMonoidHom.toMultiplicative (ZMod.castHom (show 2 ∣ 2*n by omega) (ZMod 2)).toAddMonoidHom
  have hg : Function.Injective g := by
    intro i j he
    have hh : ((2*i.val : ℕ) : ZMod (2*n)) = ((2*j.val : ℕ) : ZMod (2*n)) :=
      congrArg Multiplicative.toAdd he
    have hv := congrArg ZMod.val hh
    rw [ZMod.val_natCast_of_lt (by omega),ZMod.val_natCast_of_lt (by omega)] at hv
    exact Fin.ext (by omega)
  have hker (j : Fin n) : χ (g j)=1 := by
    change (ZMod.castHom (show 2 ∣ 2*n by omega) (ZMod 2))
      (((2*j.val : ℕ) : ZMod (2*n))) = 0
    rw [map_natCast,Nat.cast_mul,show ((2 : ℕ) : ZMod 2)=0 by decide,zero_mul]
  have hb : χ b ≠ 1 := by
    change (ZMod.castHom (show 2 ∣ 2*n by omega) (ZMod 2)) (1 : ZMod (2*n)) ≠ 0
    simp
  have hb2 : (χ b)^2=1 := by
    rw [pow_two]
    change Multiplicative.ofAdd
      ((ZMod.castHom (show 2 ∣ 2*n by omega) (ZMod 2)) (1 : ZMod (2*n)) +
       (ZMod.castHom (show 2 ∣ 2*n by omega) (ZMod 2)) (1 : ZMod (2*n))) =
      Multiplicative.ofAdd (0 : ZMod 2)
    simp only [map_one]
    exact congrArg Multiplicative.ofAdd (by decide : (1 : ZMod 2)+1=0)
  exact ⟨star g b,star_avoid g hg b χ hker hb hb2⟩

/-- At every power-of-two order the cyclic star data are genuine voltage
ratios. The conclusion only avoids the displayed word family; it does
not assert that the corresponding Cayley graph is C8-free. -/
theorem cyclic_power_two_voltage (e : ℕ) :
    ∃ f : (Fin (2^e) × Bool) → Multiplicative (ZMod (2*2^e)),
      let B := fun i => f i^2*(f (flip i))⁻¹
      ∀ c r d, c ≠ r → c ≠ flip r → c ≠ d → c ≠ flip d →
        B c*B (flip c) ≠ B r*B d := by
  letI : NeZero (2*2^e) := ⟨by positivity⟩
  obtain ⟨B,hB⟩ := cyclic_star (2^e)
  have hcoprime : (Nat.card (Multiplicative (ZMod (2*2^e)))).Coprime 3 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card]
    simpa only [pow_succ,Nat.mul_comm] using
      (show Nat.Coprime 2 3 by decide).pow_left (e+1)
  obtain ⟨f,hf⟩ := realize_ratio flip flip_involutive B hcoprime.pow_left_bijective.surjective
  refine ⟨f,?_⟩
  dsimp only
  simpa only [hf] using hB

#print axioms star_avoid
#print axioms realize_ratio
#print axioms cyclic_star
#print axioms cyclic_power_two_voltage
end Erdos713InvolutiveEvenStar
