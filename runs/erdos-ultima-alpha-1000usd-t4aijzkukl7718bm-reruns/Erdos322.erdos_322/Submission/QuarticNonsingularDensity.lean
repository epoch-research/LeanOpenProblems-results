import Submission.LocalAPDensity

/-! A nonsingular quartic local-density gain at primes congruent to one modulo
eight. All bounds here concern finite-field roots, not exact integer counts. -/
namespace Erdos322Research.QuarticNonsingularDensity
noncomputable section
open Finset LocalPeakCounting LocalSeedDensity
open scoped Classical
set_option Elab.async false
set_option maxHeartbeats 0

abbrev Pairs (p : ℕ) := Fin 2 → ZMod p
abbrev pairSum {p : ℕ} (x : Pairs p) := ∑ i, x i^4
abbrev PairFiber (p : ℕ) (b : ZMod p) := {x : Pairs p // pairSum x=b}

lemma pair_zero_lower (p : ℕ) [Fact p.Prime] (hd : 8 ∣ p-1) :
    1+4*(p-1) ≤ Fintype.card (PairFiber p 0) := by
  obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have hg' : orderOf g = p-1 := by
    simpa only [Nat.card_eq_fintype_card,ZMod.card_units] using hg
  let u : (ZMod p)ˣ := g^(orderOf g/8)
  have hu : orderOf u=8 := orderOf_pow_orderOf_div
    (by rw [hg']; have := (Fact.out : p.Prime).two_le; omega)
    (by simpa only [hg'] using hd)
  have hprim : IsPrimitiveRoot (u : ZMod p) 8 :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hu)
  have hu4 : (u : ZMod p)^4 = -1 := by
    have hs : ((u : ZMod p)^4)^2=1 := by simpa only [← pow_mul] using hprim.pow_eq_one
    exact (sq_eq_one_iff.mp hs).resolve_left (hprim.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  let r : Fin 4 → ZMod p := fun i ↦ (u : ZMod p)^(2*(i : ℕ)+1)
  have hr (i : Fin 4) : r i^4 = -1 := by
    dsimp only [r]
    rw [← pow_mul, mul_comm (2*(i : ℕ)+1) 4, pow_mul, hu4]
    rw [pow_add,pow_mul]
    norm_num
  have hinj : Function.Injective r := by
    intro i j h
    have hh := hprim.pow_inj (show 2*(i : ℕ)+1 < 8 by omega)
      (show 2*(j : ℕ)+1 < 8 by omega) h
    apply Fin.ext
    omega
  let f : Option (Fin 4 × (ZMod p)ˣ) → PairFiber p 0 := fun z ↦ match z with
    | none => ⟨0,by simp [pairSum]⟩
    | some (i,y) => ⟨![r i*y,y],by
        simp only [pairSum,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
          mul_pow,hr,neg_one_mul,neg_add_cancel]⟩
  have hf : Function.Injective f := by
    intro x y h
    have h0 := congrArg (fun z : PairFiber p 0 ↦ z.val 0) h
    have h1 := congrArg (fun z : PairFiber p 0 ↦ z.val 1) h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y =>
        simp only [f,Pi.zero_apply,Matrix.cons_val_one] at h1
        exact False.elim (y.2.ne_zero h1.symm)
    | some x =>
      cases y with
      | none => simp [f] at h1
      | some y =>
        have he : x.2=y.2 := Units.ext (by simpa [f] using h1)
        have hi : x.1=y.1 := hinj (mul_right_cancel₀ x.2.ne_zero (by simpa [f,he] using h0))
        exact congrArg some (Prod.ext hi he)
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_option,Fintype.card_prod,Fintype.card_fin,ZMod.card_units,add_comm] using hh

lemma pair_energy_le_roots (p : ℕ) [Fact p.Prime] (a : ZMod p) (ha : a^4 = -1) :
    (∑ b : ZMod p, (Fintype.card (PairFiber p b))^2) ≤ rootCount 4 p := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  let E := Σ b : ZMod p, PairFiber p b × PairFiber p b
  let f : E → RingRoots 4 (ZMod p) := fun x ↦
    ⟨Fin.append x.2.1.val (fun i ↦ a*x.2.2.val i),by
      rw [Fin.sum_univ_add (a := 2) (b := 2)]
      simp only [Fin.append_left,Fin.append_right,mul_pow,← Finset.mul_sum]
      change pairSum x.2.1.val+a^4*pairSum x.2.2.val=0
      rw [x.2.1.property,x.2.2.property,ha]
      ring⟩
  have hf : Function.Injective f := by
    rintro ⟨b,x,y⟩ ⟨c,v,w⟩ h
    have hx : x.val=v.val := by
      funext i
      have hh := congrArg (fun z : RingRoots 4 (ZMod p) ↦ z.val (Fin.castAdd 2 i)) h
      simpa only [f,Fin.append_left] using hh
    have hy : y.val=w.val := by
      funext i
      have hh := congrArg (fun z : RingRoots 4 (ZMod p) ↦ z.val (Fin.natAdd 2 i)) h
      simp only [f,Fin.append_right] at hh
      exact mul_left_cancel₀ ha0 hh
    have hbc : b=c := x.property.symm.trans ((congrArg pairSum hx).trans v.property)
    subst c
    congr 1
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
  have hh := Fintype.card_le_of_injective f hf
  have heq := Fintype.card_congr (rootsEquiv 4 p)
  simpa only [E,Fintype.card_sigma,Fintype.card_prod,← pow_two,rootCount,heq] using hh

/-- The pair zero-fiber creates a secondary term of size nine p squared. -/
theorem quartic_root_gain (p : ℕ) [Fact p.Prime] (hd : 8 ∣ p-1) :
    (p : ℝ)^3+9*p^2-9*p ≤ rootCount 4 p := by
  let r : ZMod p → ℝ := fun b ↦ Fintype.card (PairFiber p b)
  let T := (univ : Finset (ZMod p)).erase 0
  have htotal : ∑ b : ZMod p, r b=(p : ℝ)^2 := by
    have he := Fintype.card_congr (Equiv.sigmaFiberEquiv (pairSum (p := p)))
    simp only [Fintype.card_sigma,Fintype.card_fun,Fintype.card_fin,ZMod.card] at he
    dsimp only [r]
    exact_mod_cast he
  have htot : r 0+∑ b ∈ T, r b=(p : ℝ)^2 := by
    rw [add_comm,Finset.sum_erase_add _ _ (mem_univ 0)]
    exact htotal
  have hcard : (T.card : ℝ)=(p : ℝ)-1 := by
    have h := Finset.card_erase_of_mem (mem_univ (0 : ZMod p))
    simp only [Finset.card_univ,ZMod.card] at h
    dsimp only [T]
    rw [h,Nat.cast_sub (by have := (Fact.out : p.Prime).two_le; omega),Nat.cast_one]
  have hcs : (∑ b ∈ T, r b)^2 ≤ ((p : ℝ)-1)*(∑ b ∈ T, r b^2) := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq T (fun _ ↦ (1 : ℝ)) r
    simpa only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,hcard] using hh
  obtain ⟨a,ha⟩ := LocalAPDensity.exists_power_neg_one p 4 (by decide) hd
  have he := pair_energy_le_roots p a (by linear_combination ha)
  have henergy : r 0^2+∑ b ∈ T, r b^2 ≤ (rootCount 4 p : ℝ) := by
    rw [add_comm,Finset.sum_erase_add _ _ (mem_univ 0)]
    dsimp only [r]
    exact_mod_cast he
  have hp : (1 : ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hzero : 4*(p : ℝ)-3 ≤ r 0 := by
    have hh := pair_zero_lower p hd
    have hc : ((p-1 : ℕ) : ℝ)=(p : ℝ)-1 := by rw [Nat.cast_sub (by have := (Fact.out : p.Prime).two_le; omega),Nat.cast_one]
    have hh' : (1 : ℝ)+4*((p-1 : ℕ) : ℝ) ≤ r 0 := by
      dsimp only [r]
      exact_mod_cast hh
    rw [hc] at hh'
    linarith
  have hs : 9*((p : ℝ)-1)^2 ≤ (r 0-p)^2 := by
    nlinarith [sq_nonneg (r 0-(4*p-3))]
  have hm := mul_le_mul_of_nonneg_left henergy (by linarith : (0 : ℝ)≤p-1)
  have hcs' : ((p : ℝ)^2-r 0)^2 ≤ ((p : ℝ)-1)*(∑ b ∈ T, r b^2) := by
    rw [show (p : ℝ)^2-r 0=∑ b ∈ T, r b by linarith]
    exact hcs
  have hs' := mul_le_mul_of_nonneg_left hs (by linarith : (0 : ℝ)≤p)
  have hfinal : ((p : ℝ)-1)*((p : ℝ)^3+9*p^2-9*p) ≤
      ((p : ℝ)-1)*(rootCount 4 p : ℝ) := by nlinarith
  exact (mul_le_mul_iff_right₀ (by linarith : (0 : ℝ)<p-1)).mp hfinal

abbrev NonzeroRoots (k p : ℕ) := {x : RingRoots k (ZMod p) // x.val ≠ 0}

lemma roots_le_nonzero_add_one (p : ℕ) [Fact p.Prime] :
    rootCount 4 p ≤ Fintype.card (NonzeroRoots 4 p)+1 := by
  let f : Option (NonzeroRoots 4 p) → RingRoots 4 (ZMod p) := fun x ↦ match x with
    | none => ⟨0,by simp⟩
    | some x => x.val
  have hf : Function.Surjective f := by
    intro x
    by_cases hx : x.val=0
    · exact ⟨none,Subtype.ext hx.symm⟩
    · exact ⟨some ⟨x,hx⟩,rfl⟩
  have hh := Fintype.card_le_of_surjective f hf
  have he := Fintype.card_congr (rootsEquiv 4 p)
  simpa only [rootCount,he,Fintype.card_option] using hh

/-- Nonsingular local density exceeds one by at least eight divided by p. -/
theorem quartic_nonsingular_gain (p : ℕ) [Fact p.Prime]
    (hd : 8 ∣ p-1) (hp : 10 ≤ p) :
    (p : ℝ)^3*(1+8/p) ≤ Fintype.card (NonzeroRoots 4 p) := by
  have h := quartic_root_gain p hd
  have h' : (rootCount 4 p : ℝ) ≤ Fintype.card (NonzeroRoots 4 p)+1 := by
    exact_mod_cast roots_le_nonzero_add_one p
  have hp' : (10 : ℝ)≤p := by exact_mod_cast hp
  have hp0 : (p : ℝ)≠0 := by positivity
  have he : (p : ℝ)^3*(1+8/p)=(p : ℝ)^3+8*p^2 := by field_simp
  rw [he]
  nlinarith

end
end Erdos322Research.QuarticNonsingularDensity
