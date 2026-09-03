import Submission.UnitOrbitPhaseDescent

/-! A second-factorial-moment obstruction on prime-length multiplicative orbits.
A cover with no unit-period class needs every phase, so one conflicting pair
is not the right failure threshold. No universal arithmetic upper bound is
proved by this module. -/
namespace Erdos7PrimeOrbitMoment
open Erdos7UnitOrbitDescent Erdos7UnitOrbitPhaseDescent
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

variable {G I : Type} [Group G] [Fintype G] [Fintype I]
variable (H : I → Type) [∀ i, Group (H i)]
variable (π : (i : I) → G →* H i) (a : (i : I) → H i)

/-- Ordered conflicting labels. Same-phase duplicates are not included. -/
def Conflict (u v : G) (i j : I) : Prop :=
  Active H π a u v i ∧ Active H π a u v j ∧
    orderOf (π i u) = orderOf (π j u) ∧ orderOf (π i u) ≠ 1 ∧
      ¬ CoActive H π a u v i j

lemma active_prime_order {p : ℕ} (hp : p.Prime) (u v : G) (hu : orderOf u = p)
    (hn : ∀ i, Active H π a u v i → orderOf (π i u) ≠ 1)
    (i : I) (hi : Active H π a u v i) : orderOf (π i u) = p := by
  have hd : orderOf (π i u) ∣ p := hu ▸ orderOf_map_dvd (π i) u
  exact (hp.eq_one_or_self_of_dvd _ hd).resolve_left (hn i hi)

lemma phase_unique {p : ℕ} (u v : G) (i : I) (hi : orderOf (π i u) = p)
    (s t : Fin p) (hs : π i (v*u^(s.val : ℤ)) = a i)
    (ht : π i (v*u^(t.val : ℤ)) = a i) : s = t := by
  have hh := hs.trans ht.symm
  simp only [map_mul, map_zpow] at hh
  have hmod := zpow_eq_zpow_iff_modEq.mp (mul_left_cancel hh)
  rw [hi] at hmod
  exact Fin.ext ((Int.natCast_modEq_iff.mp hmod).eq_of_lt_of_lt s.isLt t.isLt)

lemma different_phases_not_coActive {p : ℕ} (u v : G) (i j : I)
    (hi : orderOf (π i u) = p) (hj : orderOf (π j u) = p)
    (s t : Fin p) (hne : s ≠ t)
    (hs : π i (v*u^(s.val : ℤ)) = a i) (ht : π j (v*u^(t.val : ℤ)) = a j) :
    ¬ CoActive H π a u v i j := by
  rintro ⟨n,hni,hnj⟩
  have hsi := hit_difference H π a u v i hs hni
  have htj := hit_difference H π a u v j ht hnj
  rw [hi] at hsi
  rw [hj] at htj
  have hst : (p : ℤ) ∣ (t.val : ℤ) - s.val := by
    convert dvd_sub hsi htj using 1 <;> ring
  have hmod : (s.val : ℤ) ≡ t.val [ZMOD (p : ℤ)] := Int.modEq_iff_dvd.mpr hst
  exact hne (Fin.ext ((Int.natCast_modEq_iff.mp hmod).eq_of_lt_of_lt s.isLt t.isLt))

/-- Each of the p phases needs a different label. Every ordered pair of
these labels is a genuine phase conflict, yielding p*(p-1) conflicts. -/
theorem prime_orbit_conflicts {p : ℕ} (hp : p.Prime)
    (hc : ∀ x : G, ∃ i, π i x = a i) (u v : G) (hu : orderOf u = p)
    (hn : ∀ i, Active H π a u v i → orderOf (π i u) ≠ 1) :
    p*(p-1) ≤ ((Finset.univ : Finset (I × I)).filter (fun ij =>
      Conflict H π a u v ij.1 ij.2)).card := by
  have hphase (t : Fin p) : ∃ i, π i (v*u^(t.val : ℤ)) = a i := hc _
  let f (t : Fin p) : I := Classical.choose (hphase t)
  have hf (t : Fin p) : π (f t) (v*u^(t.val : ℤ)) = a (f t) :=
    Classical.choose_spec (hphase t)
  have hfa (t : Fin p) : Active H π a u v (f t) := ⟨t.val, hf t⟩
  have hfo (t : Fin p) : orderOf (π (f t) u) = p :=
    active_prime_order H π a hp u v hu hn _ (hfa t)
  have hfi : Function.Injective f := by
    intro s t he
    apply phase_unique H π a u v (f s) (hfo s) s t (hf s)
    rw [he]
    exact hf t
  let S := (Finset.univ : Finset (Fin p)).offDiag
  have hsub : S.image (Prod.map f f) ⊆
      (Finset.univ : Finset (I × I)).filter (fun ij => Conflict H π a u v ij.1 ij.2) := by
    intro ij hij
    obtain ⟨st,hst,rfl⟩ := Finset.mem_image.mp hij
    have hne := (Finset.mem_offDiag.mp hst).2.2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfa st.1, hfa st.2,
      (hfo st.1).trans (hfo st.2).symm, hn _ (hfa st.1), ?_⟩
    exact different_phases_not_coActive H π a u v _ _ (hfo st.1) (hfo st.2)
      st.1 st.2 hne (hf st.1) (hf st.2)
  calc
    p*(p-1) = S.card := by simp [S, Finset.offDiag_card, Nat.mul_sub_left_distrib]
    _ = (S.image (Prod.map f f)).card :=
      (Finset.card_image_of_injective S (hfi.prodMap hfi)).symm
    _ ≤ _ := Finset.card_le_card hsub

lemma incidence_count {Ω J : Type} [Fintype Ω] [Fintype J] (P : Ω → J → Prop) :
    (∑ x : Ω, ((Finset.univ : Finset J).filter (P x)).card) =
      ∑ j : J, ((Finset.univ : Finset Ω).filter (fun x => P x j)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- Integer form of the prime-orbit second-moment necessary inequality.
No minimal-counterexample assumption is required. The pair sum is ordered. -/
theorem prime_orbit_moment_bound {p : ℕ} (hp : p.Prime)
    (hc : ∀ x : G, ∃ i, π i x = a i) (u : G) (hu : orderOf u = p) :
    p*(p-1) * Fintype.card G ≤
      p*(p-1) * (∑ i : I, ((Finset.univ : Finset G).filter (fun v =>
        Active H π a u v i ∧ orderOf (π i u) = 1)).card) +
      ∑ ij : I × I, ((Finset.univ : Finset G).filter (fun v =>
        Conflict H π a u v ij.1 ij.2)).card := by
  let U (v : G) : Finset I := Finset.univ.filter (fun i =>
    Active H π a u v i ∧ orderOf (π i u) = 1)
  let C (v : G) : Finset (I × I) := Finset.univ.filter (fun ij =>
    Conflict H π a u v ij.1 ij.2)
  have hpoint (v : G) : p*(p-1) ≤ p*(p-1)*(U v).card + (C v).card := by
    by_cases hh : (U v).Nonempty
    · have hpos := Finset.card_pos.mpr hh
      calc
        p*(p-1) = p*(p-1)*1 := (mul_one _).symm
        _ ≤ p*(p-1)*(U v).card := Nat.mul_le_mul_left _ hpos
        _ ≤ _ := Nat.le_add_right _ _
    · have hn : ∀ i, Active H π a u v i → orderOf (π i u) ≠ 1 := by
        intro i hai he
        exact hh ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hai,he⟩⟩
      exact (prime_orbit_conflicts H π a hp hc u v hu hn).trans (Nat.le_add_left _ _)
  have hh := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset G)) => hpoint v)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum] at hh
  rw [mul_comm (Fintype.card G)] at hh
  have hU : (∑ v : G, (U v).card) = ∑ i : I,
      ((Finset.univ : Finset G).filter (fun v =>
        Active H π a u v i ∧ orderOf (π i u) = 1)).card := by
    convert incidence_count (fun (v : G) (i : I) =>
      Active H π a u v i ∧ orderOf (π i u) = 1) using 1
    all_goals
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      ext i
      simp [U]
  have hC : (∑ v : G, (C v).card) = ∑ ij : I × I,
      ((Finset.univ : Finset G).filter (fun v => Conflict H π a u v ij.1 ij.2)).card := by
    convert incidence_count (fun (v : G) (ij : I × I) =>
      Conflict H π a u v ij.1 ij.2) using 1
  rw [hU,hC] at hh
  exact hh

#print axioms prime_orbit_conflicts
#print axioms prime_orbit_moment_bound
end
end Erdos7PrimeOrbitMoment
