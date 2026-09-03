import Submission.GenericUltrafilterUniversality

/-!
A countable target with only finitely many infinite-degree vertices can
absorb mutual ultrafilter extensions, if one vertex is adjacent to all
exceptional vertices. The target need NOT be K4-free.
-/

open SimpleGraph Set Filter
open Erdos595Work Erdos595GenericUltrafilterUniversality
namespace Erdos595FiniteExceptionUltrafilterTarget

noncomputable def collapse {A : Type*} (d : A) (p : Ultrafilter A) : A := by
  classical
  exact if h : ∃ a, p = pure a then h.choose else d

lemma collapse_pure {A : Type*} (d a : A) : collapse d (pure a) = a := by
  classical
  have h : ∃ b : A, (pure a : Ultrafilter A) = pure b := ⟨a,rfl⟩
  rw [collapse,dif_pos h]
  exact Ultrafilter.pure_injective h.choose_spec.symm

lemma collapse_nonprincipal {A : Type*} (d : A) (p : Ultrafilter A)
    (hp : ¬∃ a, p = pure a) : collapse d p = d := by
  classical
  exact dif_neg hp

lemma collapse_adj {A : Type*} (T : SimpleGraph A) (E : Set A) (hE : E.Finite)
    (hfinite : ∀ a ∉ E, (T.neighborSet a).Finite) (d : A) (hd : ∀ a ∈ E, T.Adj d a)
    (p q : Ultrafilter A) (hpq : fubiniAdj T p q) (hqp : fubiniAdj T q p) :
    T.Adj (collapse d p) (collapse d q) := by
  classical
  have hanchor : ∀ (a : A) (u : Ultrafilter A), (¬∃ b, u = pure b) →
      T.neighborSet a ∈ u → a ∈ E := by
    intro a u hu hm
    by_contra ha
    obtain ⟨b,_,hb⟩ := u.eq_pure_of_finite_mem (hfinite a ha) hm
    exact hu ⟨b,hb⟩
  by_cases hp : ∃ a, p = pure a
  · obtain ⟨a,rfl⟩ := hp
    rw [collapse_pure]
    by_cases hq : ∃ b, q = pure b
    · obtain ⟨b,rfl⟩ := hq
      rw [collapse_pure]
      exact hpq
    · rw [collapse_nonprincipal d q hq]
      exact (hd a (hanchor a q hq hpq)).symm
  · rw [collapse_nonprincipal d p hp]
    by_cases hq : ∃ b, q = pure b
    · obtain ⟨b,rfl⟩ := hq
      rw [collapse_pure]
      exact hd b (hanchor b p hp hqp)
    · have he : E ∈ p := Filter.mem_of_superset hpq (fun a ha => hanchor a q hq ha)
      obtain ⟨a,_,ha⟩ := p.eq_pure_of_finite_mem hE he
      exact (hp ⟨a,ha⟩).elim

noncomputable def liftHom {A B : Type*} (T : SimpleGraph A) (E : Set A) (hE : E.Finite)
    (hfinite : ∀ a ∉ E, (T.neighborSet a).Finite) (d : A) (hd : ∀ a ∈ E, T.Adj d a)
    {H : SimpleGraph B} (hH : H.CliqueFree 4) (f : H →g T) : ultrafilterGraph H hH →g T where
  toFun p := collapse d (Ultrafilter.map f p)
  map_rel' h := collapse_adj T E hE hfinite d hd _ _
    (fubiniAdj_map_hom f h.1) (fubiniAdj_map_hom f h.2)

noncomputable def towerHom {A B : Type*} (T : SimpleGraph A) (E : Set A) (hE : E.Finite)
    (hfinite : ∀ a ∉ E, (T.neighborSet a).Finite) (d : A) (hd : ∀ a ∈ E, T.Adj d a)
    {H : SimpleGraph B} (hH : H.CliqueFree 4) (f : H →g T) :
    (n : ℕ) → (tower H hH n).val →g T
  | 0 => f
  | n+1 => liftHom T E hE hfinite d hd (tower H hH n).property
    (towerHom T E hE hfinite d hd hH f n)

/-- Every finite tower stays countably coverable under this explicit target criterion. -/
theorem tower_cover {A B : Type} [Countable A] (T : SimpleGraph A) (E : Set A) (hE : E.Finite)
    (hfinite : ∀ a ∉ E, (T.neighborSet a).Finite) (d : A) (hd : ∀ a ∈ E, T.Adj d a)
    {H : SimpleGraph B} (hH : H.CliqueFree 4) (f : H →g T) (n : ℕ) :
    IsCountableUnionOfTriangleFree (tower H hH n).val := by
  classical
  obtain ⟨enc,henc⟩ := exists_injective_nat A
  let code : A → ℕ → Fin 2 := fun a m => if enc a = m then 1 else 0
  have hcode : Function.Injective code := by
    intro a b he
    apply henc
    have hh := congrFun he (enc a)
    by_contra hab
    simp [code,Ne.symm hab] at hh
  exact countable_union_of_hom (towerHom T E hE hfinite d hd hH f n)
    (countable_union_of_binary_encoding T code hcode)

#print axioms collapse_adj
#print axioms tower_cover
end Erdos595FiniteExceptionUltrafilterTarget
