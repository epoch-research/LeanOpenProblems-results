import Submission.AdditiveCoding

/-!
Additive-energy bounds for arbitrary dense selections of additive codes.
These are construction obstructions, not a resolution of Erdős 714.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

noncomputable section
open Finset SimpleGraph
open scoped Pointwise
open Classical

namespace Erdos714SelectedAdditive

variable {V I A : Type*} [AddCommGroup V] [AddCommGroup A]
  [Fintype V] [Fintype I] [Fintype A]

/-- Direction pairs of parallelograms that occur inside the selected message set. -/
def directions (S : Finset V) : Finset (V × V) :=
  univ.filter (fun p => ∃ x ∈ S, x+p.1 ∈ S ∧ x+p.2 ∈ S ∧ x+p.1+p.2 ∈ S)

/-- Only directions vanishing under this coordinate homomorphism are counted. -/
def kernelDirections (l : V →+ A) (S : Finset V) : Finset (V × V) :=
  (directions S).filter (fun p => l p.1 = 0 ∧ l p.2 = 0)

/-- A dense selected set has a correspondingly dense intersection with some translate. -/
lemma dense_translate (S K : Finset V) (D : ℕ)
    (hS : Fintype.card V ≤ D*S.card) :
    ∃ x : V, K.card ≤ D*(K.filter (fun u => x+u ∈ S)).card := by
  have hc (u : V) : (univ.filter (fun x : V => x+u ∈ S)).card = S.card := by
    have he : univ.filter (fun x : V => x+u ∈ S) =
        S.map (Equiv.subRight u).toEmbedding := by
      ext x
      simp
    rw [he, card_map]
  have hsum : ∑ x : V, (K.filter (fun u => x+u ∈ S)).card = K.card*S.card := by
    simp only [card_filter]
    rw [sum_comm]
    simp_rw [← card_filter, hc]
    simp
  have hb : (∑ _x : V, K.card) ≤ ∑ x : V, D*(K.filter (fun u => x+u ∈ S)).card := by
    rw [← mul_sum, hsum]
    simp only [sum_const, card_univ, smul_eq_mul]
    nlinarith [Nat.mul_le_mul_right K.card hS]
  obtain ⟨x, _, hx⟩ := exists_le_of_sum_le (univ_nonempty : (univ : Finset V).Nonempty) hb
  exact ⟨x, hx⟩

omit [Fintype A] in
/-- Energy quadruples inject into a starting point and a kernel-direction pair. -/
lemma energy_upper (l : V →+ A) (S T : Finset V) (x : V)
    (hT : ∀ t ∈ T, l t = 0) (hTS : ∀ t ∈ T, x+t ∈ S) :
    T.addEnergy T ≤ T.card*(kernelDirections l S).card := by
  rw [← card_product]
  unfold Finset.addEnergy
  apply card_le_card_of_injOn
    (fun p : (V × V) × (V × V) => (p.1.1, (p.1.2-p.1.1, p.2.2-p.1.1)))
  · rintro ⟨⟨a,b⟩,c,d⟩ hp
    simp only [mem_coe, mem_filter, mem_product] at hp
    obtain ⟨⟨⟨ha,hb⟩,hc,hd⟩,he⟩ := hp
    apply mem_product.mpr
    refine ⟨ha, mem_filter.mpr ⟨?_, ?_⟩⟩
    · apply mem_filter.mpr
      refine ⟨mem_univ _, x+a, hTS a ha, ?_, ?_, ?_⟩
      · convert hTS b hb using 1; simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      · convert hTS d hd using 1; simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      · have hbd : b+d-a = c := by rw [← he]; abel_nf
        convert hTS c hc using 1
        rw [← hbd]
        simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    · simp [map_sub, hT a ha, hT b hb, hT d hd]
  · rintro ⟨⟨a,b⟩,c,d⟩ hp ⟨⟨a',b'⟩,c',d'⟩ hq hh
    have hp' := (mem_filter.mp hp).2
    have hq' := (mem_filter.mp hq).2
    have ha : a = a' := congrArg Prod.fst hh
    subst a'
    have hb : b = b' := sub_left_injective (congrArg (fun z : V × (V × V) => z.2.1) hh)
    have hd : d = d' := sub_left_injective (congrArg (fun z : V × (V × V) => z.2.2) hh)
    subst b'
    subst d'
    have hc : c = c' := add_left_cancel (hp'.trans hq'.symm)
    subst c'
    rfl

omit [Fintype A] in
/-- A dense selection supplies quadratically many usable directions in every kernel. -/
lemma kernel_square_le_directions (l : V →+ A) (S : Finset V) (D : ℕ)
    (hS : Fintype.card V ≤ D*S.card) :
    (univ.filter (fun v => l v = 0)).card ^ 2 ≤ D^3*(kernelDirections l S).card := by
  let K := univ.filter (fun v => l v = 0)
  obtain ⟨x,hx⟩ := dense_translate S K D hS
  let T := K.filter (fun u => x+u ∈ S)
  have hT (t : V) (ht : t ∈ T) : l t = 0 :=
    (mem_filter.mp (mem_filter.mp ht).1).2
  have hTS (t : V) (ht : t ∈ T) : x+t ∈ S := (mem_filter.mp ht).2
  have hsum : (T+T).card ≤ K.card := by
    apply card_le_card
    intro t ht
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp ht
    simp only [K, mem_filter, mem_univ, true_and]
    simp [map_add, hT a ha, hT b hb]
  have he : T.card^4 ≤ K.card*(T.addEnergy T) := by
    have hh := (le_card_add_mul_addEnergy T T).trans
      (Nat.mul_le_mul_right (T.addEnergy T) hsum)
    nlinarith
  have he' := Nat.mul_le_mul_left K.card (energy_upper l S T x hT hTS)
  have hk : 0 < K.card := card_pos.mpr ⟨0, by simp [K]⟩
  have ht : 0 < T.card := by
    change K.card ≤ D*T.card at hx
    by_contra! h
    have ht0 : T.card = 0 := Nat.eq_zero_of_le_zero h
    rw [ht0, mul_zero] at hx
    omega
  have hcube : T.card^3 ≤ K.card*(kernelDirections l S).card := by
    apply Nat.le_of_mul_le_mul_left (c := T.card) _ ht
    nlinarith [he.trans he']
  change K.card ≤ D*T.card at hx
  have hc := Nat.pow_le_pow_left hx 3
  have hh := Nat.mul_le_mul_left (D^3) hcube
  change K.card^2 ≤ _
  apply Nat.le_of_mul_le_mul_left (c := K.card) _ hk
  nlinarith

/-- Every nondegenerate selected parallelogram forces a common-zero bound. -/
lemma selected_common_zeros (f : V →+ (I → A)) (S : Finset V)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (fun v : S => f v.1)))
    {u v : V} (hp : (u,v) ∈ directions S)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) (hs : u+v ≠ 0) :
    (univ.filter (fun i => f u i = 0 ∧ f v i = 0)).card ≤ 3 := by
  obtain ⟨x,hx,hxu,hxv,hxuv⟩ := (mem_filter.mp hp).2
  let e : Fin 4 ↪ V := ⟨![0,u,v,u+v], by
    intro i j h
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact False.elim (hu h)
      | exact False.elim (hu h.symm)
      | exact False.elim (hv h)
      | exact False.elim (hv h.symm)
      | exact False.elim (huv h)
      | exact False.elim (huv h.symm)
      | exact False.elim (hs h)
      | exact False.elim (hs h.symm)
      | exact False.elim (hu (by simpa using h))
      | exact False.elim (hu (by simpa using h.symm))
      | exact False.elim (hv (by simpa using h))⟩
  have hm (i : Fin 4) : x+e i ∈ S := by
    fin_cases i
    · simpa [e] using hx
    · simpa [e] using hxu
    · simpa [e] using hxv
    · simpa [e, add_assoc] using hxuv
  let g : Fin 4 ↪ S := ⟨fun i => ⟨x+e i, hm i⟩, by
    intro i j h
    exact e.injective (add_left_cancel (congrArg Subtype.val h))⟩
  have hg := (Erdos714Coding.free_iff_agreement (fun v : S => f v.1) (by decide)).mp hfree g
  have hle : (univ.filter (fun i => f u i = 0 ∧ f v i = 0)).card ≤
      (Erdos714Coding.agreement (fun v : S => f v.1) (by decide : 0 < 4) g).card := by
    apply card_le_card
    intro i hi
    obtain ⟨hfu,hfv⟩ := (mem_filter.mp hi).2
    simp only [Erdos714Coding.agreement, mem_filter, mem_univ, true_and]
    intro j
    fin_cases j <;> simp [g, e, hfu, hfv]
  omega

/-- A selected code bounds the total number of usable kernel directions. -/
lemma directions_sum_bound (f : V →+ (I → A)) (S : Finset V)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (fun v : S => f v.1))) :
    ∑ i : I, (kernelDirections ((Pi.evalAddMonoidHom (fun _ : I => A) i).comp f) S).card ≤
      3*(Fintype.card V)^2 + 4*Fintype.card I*Fintype.card V := by
  let c (p : V × V) := if p ∈ directions S then
    (univ.filter (fun i => f p.1 i = 0 ∧ f p.2 i = 0)).card else 0
  have hc (p : V × V) : c p ≤ 3 +
      if p ∈ Erdos714AdditiveCoding.degeneratePairs then Fintype.card I else 0 := by
    by_cases hd : p ∈ directions S
    · dsimp only [c]
      rw [if_pos hd]
      by_cases hb : p ∈ Erdos714AdditiveCoding.degeneratePairs
      · have he : (univ.filter (fun i => f p.1 i = 0 ∧ f p.2 i = 0)).card ≤
            Fintype.card I := card_le_univ _
        simp only [if_pos hb]
        omega
      · have hgood : p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 ≠ p.2 ∧ p.1+p.2 ≠ 0 := by
          simpa only [Erdos714AdditiveCoding.degeneratePairs, mem_filter,
            mem_univ, true_and, not_or] using hb
        simpa only [if_neg hb, add_zero] using selected_common_zeros f S hfree hd
          hgood.1 hgood.2.1 hgood.2.2.1 hgood.2.2.2
    · simp only [c, if_neg hd]
      omega
  have he : (∑ i : I, (kernelDirections
      ((Pi.evalAddMonoidHom (fun _ : I => A) i).comp f) S).card) = ∑ p : V × V, c p := by
    calc
      _ = ∑ p ∈ directions S, (univ.filter (fun i => f p.1 i = 0 ∧ f p.2 i = 0)).card := by
        simp only [kernelDirections, card_filter]
        rw [sum_comm]
        rfl
      _ = _ := by
        dsimp only [c]
        rw [← sum_filter]
        simp
  have hb : (∑ p : V × V, if p ∈ Erdos714AdditiveCoding.degeneratePairs then
      Fintype.card I else 0) =
      (Erdos714AdditiveCoding.degeneratePairs : Finset (V × V)).card * Fintype.card I := by
    rw [← sum_filter]
    simp
  rw [he]
  calc
    ∑ p : V × V, c p ≤ ∑ p : V × V, (3 +
        if p ∈ Erdos714AdditiveCoding.degeneratePairs then Fintype.card I else 0) :=
      sum_le_sum (fun p _ => hc p)
    _ = 3*(Fintype.card V)^2 +
        (Erdos714AdditiveCoding.degeneratePairs : Finset (V × V)).card * Fintype.card I := by
      rw [sum_add_distrib, hb]
      simp [pow_two, mul_comm]
    _ ≤ _ := by
      have hh := Nat.mul_le_mul_right (Fintype.card I)
        (Erdos714AdditiveCoding.degeneratePairs_card (V := V))
      nlinarith

/-- A positive-density message selection only changes the kernel bound by D^3. -/
theorem selected_kernel_second_moment (f : V →+ (I → A)) (S : Finset V) (D : ℕ)
    (hS : Fintype.card V ≤ D*S.card)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (fun v : S => f v.1))) :
    ∑ i : I, (univ.filter (fun v => f v i = 0)).card ^ 2 ≤
      D^3*(3*(Fintype.card V)^2 + 4*Fintype.card I*Fintype.card V) := by
  have h := sum_le_sum (s := (univ : Finset I)) (fun i _ =>
    kernel_square_le_directions ((Pi.evalAddMonoidHom (fun _ : I => A) i).comp f) S D hS)
  simp only [← mul_sum] at h
  exact h.trans (Nat.mul_le_mul_left _ (directions_sum_bound f S hfree))

/-- Dense arbitrary message selections still force additive-code length O_D(q^2). -/
theorem selected_length_bound (f : V →+ (I → A)) (S : Finset V) (D : ℕ)
    (hS : Fintype.card V ≤ D*S.card)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (fun v : S => f v.1)))
    (hsize : 8*D^3*(Fintype.card A)^2 ≤ Fintype.card V) :
    Fintype.card I ≤ 6*D^3*(Fintype.card A)^2 := by
  have hk (i : I) : Fintype.card V ≤
      Fintype.card A * (univ.filter (fun v => f v i = 0)).card :=
    Erdos714AdditiveCoding.card_le_alphabet_mul_kernel
      ((Pi.evalAddMonoidHom (fun _ : I => A) i).comp f)
  have hsq (i : I) : (Fintype.card V)^2 ≤ (Fintype.card A)^2 *
      (univ.filter (fun v => f v i = 0)).card ^ 2 := by
    have h := Nat.mul_le_mul (hk i) (hk i)
    nlinarith
  have hsum : Fintype.card I * (Fintype.card V)^2 ≤
      (Fintype.card A)^2 * ∑ i : I, (univ.filter (fun v => f v i = 0)).card ^ 2 := by
    have h := sum_le_sum (s := (univ : Finset I)) (fun i _ => hsq i)
    simpa only [sum_const, card_univ, smul_eq_mul, ← mul_sum] using h
  have hm := Nat.mul_le_mul_left ((Fintype.card A)^2)
    (selected_kernel_second_moment f S D hS hfree)
  have ht := hsum.trans hm
  have hv : 0 < Fintype.card V := Fintype.card_pos
  have hc : Fintype.card I * Fintype.card V ≤
      3*D^3*(Fintype.card A)^2 * Fintype.card V +
        4*D^3*(Fintype.card A)^2 * Fintype.card I := by
    apply Nat.le_of_mul_le_mul_right (c := Fintype.card V) _ hv
    nlinarith
  have hh := Nat.mul_le_mul_right (Fintype.card I) hsize
  apply Nat.le_of_mul_le_mul_right (c := Fintype.card V) _ hv
  nlinarith

/-- Dense selected additive codes cannot reach the fourth-case critical parameters. -/
theorem selected_quartic_not_free (f : V →+ (I → A)) (S : Finset V) (D : ℕ)
    (hS : Fintype.card V ≤ D*S.card) (hq : 8*D^3 < Fintype.card A)
    (hV : Fintype.card V = (Fintype.card A)^4)
    (hI : Fintype.card I = (Fintype.card A)^3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (fun v : S => f v.1)) := by
  intro hfree
  have hsize : 8*D^3*(Fintype.card A)^2 ≤ Fintype.card V := by
    rw [hV, show (Fintype.card A)^4 = (Fintype.card A)^2 * (Fintype.card A)^2 by ring]
    apply Nat.mul_le_mul_right
    have hq0 : 0 < Fintype.card A := Fintype.card_pos
    nlinarith
  have hlen := selected_length_bound f S D hS hfree hsize
  rw [hI] at hlen
  have hp : 0 < (Fintype.card A)^2 := pow_pos Fintype.card_pos 2
  have hle : Fintype.card A ≤ 6*D^3 := by
    apply Nat.le_of_mul_le_mul_right (c := (Fintype.card A)^2) _ hp
    nlinarith
  omega

#print axioms dense_translate
#print axioms energy_upper
#print axioms kernel_square_le_directions
#print axioms selected_common_zeros
#print axioms selected_kernel_second_moment
#print axioms selected_length_bound
#print axioms selected_quartic_not_free

end Erdos714SelectedAdditive
