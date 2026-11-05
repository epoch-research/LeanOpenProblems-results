import Mathlib
import Submission.Basic
import Submission.Cap1
import Submission.Cap2

open SimpleGraph

namespace E74

universe u

variable {V : Type u}

/-- parity bit -/
def pb (n : ℕ) : Bool := decide (n % 2 = 0)

lemma pb_ne_succ (n : ℕ) : pb (n + 1) ≠ pb n := by
  unfold pb
  by_cases h : n % 2 = 0
  · have : (n + 1) % 2 ≠ 0 := by omega
    simp [h, this]
  · have : (n + 1) % 2 = 0 := by omega
    simp [h, this]

lemma pb_of_odd {n : ℕ} (h : n % 2 = 1) : pb n = false := by
  unfold pb
  simp [h]

section cap

variable {Q : SimpleGraph V} {F : Finset (Sym2 V)} {P : V → Bool} {C : Finset V} {R : ℕ}

/-- the integer-valued layer -/
noncomputable def par (Q : SimpleGraph V) (F : Finset (Sym2 V)) (C : Finset V) (v : V) : ℕ :=
  (delta (Tg Q F) C v).toNat

lemma delta_eq_par {v : V} (hv : v ∈ Iset Q F C R) :
    delta (Tg Q F) C v = (par Q F C v : ℕ∞) := by
  have hne : delta (Tg Q F) C v ≠ ⊤ := ne_top_of_lt hv
  simp [par, ENat.coe_toNat hne]

lemma par_lt {v : V} (hv : v ∈ Iset Q F C R) : par Q F C v < 2 * R := by
  have h : (par Q F C v : ℕ∞) < ((2 * R : ℕ) : ℕ∞) := by
    rw [← delta_eq_par hv]; exact hv
  exact_mod_cast h

lemma par_adj (hd : CapData Q F P C R) {u v : V} (huv : (Tg Q F).Adj u v)
    (hu : u ∈ Iset Q F C R) (hv : v ∈ Iset Q F C R) :
    par Q F C v = par Q F C u + 1 ∨ par Q F C u = par Q F C v + 1 := by
  have h1 := delta_step (C := C) huv
  have h2 := delta_step (C := C) huv.symm
  have h3 := delta_layer hd huv (le_of_lt hu)
  rw [delta_eq_par hu, delta_eq_par hv] at h1 h2 h3
  have h1' : par Q F C v ≤ par Q F C u + 1 := by exact_mod_cast h1
  have h2' : par Q F C u ≤ par Q F C v + 1 := by exact_mod_cast h2
  have h3' : par Q F C u ≠ par Q F C v := by
    intro h; exact h3 (by rw [h])
  omega

lemma par_N (hd : CapData Q F P C R) {u : V} (hu : u ∈ Nset Q F C R) :
    par Q F C u + 1 = 2 * R := by
  obtain ⟨huI, v, huv, hvS⟩ := hu
  have h1 := delta_step (C := C) huv
  rw [hvS, delta_eq_par huI] at h1
  have h1' : 2 * R ≤ par Q F C u + 1 := by exact_mod_cast h1
  have := par_lt huI
  omega

lemma N_subset_I {u : V} (hu : u ∈ Nset Q F C R) : u ∈ Iset Q F C R := hu.1

/-- the parity colouring of the capped graph. -/
noncomputable def chi (Q : SimpleGraph V) (F : Finset (Sym2 V)) (C : Finset V) :
    Option V → Bool
  | none => true
  | some v => pb (par Q F C v)

lemma chi_N (hd : CapData Q F P C R) {u : V} (hu : u ∈ Nset Q F C R) :
    chi Q F C (some u) = false := by
  have h := par_N hd hu
  have h1 := hd.hR
  exact pb_of_odd (by omega)

lemma chi_adj (hd : CapData Q F P C R) {u v : V} (huv : (Tg Q F).Adj u v)
    (hu : u ∈ Iset Q F C R) (hv : v ∈ Iset Q F C R) :
    chi Q F C (some u) ≠ chi Q F C (some v) := by
  show pb (par Q F C u) ≠ pb (par Q F C v)
  rcases par_adj hd huv hu hv with h | h
  · rw [h]; exact (pb_ne_succ _).symm
  · rw [h]; exact pb_ne_succ _

theorem claim2 [Finite V] (hd : CapData Q F P C R) (S' : Finset (Option V)) :
    (mono (capGraph Q (Iset Q F C R) (Nset Q F C R)) S' (chi Q F C)).ncard ≤ F.card := by
  have hsub : mono (capGraph Q (Iset Q F C R) (Nset Q F C R)) S' (chi Q F C) ⊆
      (Sym2.map some) '' (F : Set (Sym2 V)) := by
    rintro e ⟨a, b, rfl, _, _, hadj, hchi⟩
    cases a with
    | none =>
      cases b with
      | none => exact absurd hadj (capGraph_adj_none_none _ _ _)
      | some v =>
        have hv : v ∈ Nset Q F C R := hadj
        rw [chi_N hd hv] at hchi
        simp [chi] at hchi
    | some u =>
      cases b with
      | none =>
        have hu : u ∈ Nset Q F C R := hadj
        rw [chi_N hd hu] at hchi
        simp [chi] at hchi
      | some v =>
        obtain ⟨hu, hv, hQ⟩ := hadj
        rcases adj_of_Q (F := F) hQ with hT | hFe
        · exact absurd hchi (chi_adj hd hT hu hv)
        · exact ⟨s(u, v), hFe, by simp⟩
  calc (mono (capGraph Q (Iset Q F C R) (Nset Q F C R)) S' (chi Q F C)).ncard
      ≤ ((Sym2.map some) '' (F : Set (Sym2 V))).ncard :=
        Set.ncard_le_ncard hsub ((F.finite_toSet).image _)
    _ ≤ (F : Set (Sym2 V)).ncard := Set.ncard_image_le F.finite_toSet
    _ = F.card := Set.ncard_coe_finset F


/-- the set `Z` of vertices of `A` reachable from `N ∩ A` inside `T[A]`. -/
def Zset (Q : SimpleGraph V) (F : Finset (Sym2 V)) (C : Finset V) (R : ℕ) (A : Finset V) :
    Set V :=
  {z | z ∈ A ∧ ∃ u, u ∈ A ∧ u ∈ Nset Q F C R ∧
    Relation.ReflTransGen (fun a b => a ∈ A ∧ b ∈ A ∧ (Tg Q F).Adj a b) u z}

lemma Z_not_F (hd : CapData Q F P C R) (A : Finset V)
    (hAI : ∀ v ∈ A, v ∈ Iset Q F C R) (hA : A.card < R) :
    ∀ z ∈ Zset Q F C R A, ∀ e ∈ F, z ∉ e := by
  classical
  intro z hz e he hze
  obtain ⟨hzA, u, huA, huN, hr⟩ := hz
  -- layer of z is small
  have hzW : par Q F C z ≤ R := by
    obtain ⟨c, hc, hcz⟩ := hd.hW z (Or.inl ⟨e, he, hze⟩)
    have h1 : delta (Tg Q F) C z ≤ (R : ℕ∞) := le_trans (delta_le hc) hcz
    rw [delta_eq_par (hAI z hzA)] at h1
    exact_mod_cast h1
  have hpu := par_N hd huN
  -- all intermediate layers are attained
  have key : ∀ y, Relation.ReflTransGen (fun a b => a ∈ A ∧ b ∈ A ∧ (Tg Q F).Adj a b) u y →
      ∀ j, par Q F C y ≤ j → j ≤ par Q F C u → ∃ x ∈ A, par Q F C x = j := by
    intro y hy
    induction hy with
    | refl =>
      intro j hj1 hj2
      exact ⟨u, huA, by omega⟩
    | tail hab hbc ih =>
      rename_i b c
      intro j hj1 hj2
      obtain ⟨hbA, hcA, hbc'⟩ := hbc
      have hpa := par_adj hd hbc' (hAI b hbA) (hAI c hcA)
      by_cases hbj : par Q F C b ≤ j
      · exact ih j hbj hj2
      · refine ⟨c, hcA, ?_⟩
        omega
  have hsub : Finset.Icc R (2 * R - 1) ⊆ A.image (par Q F C) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    obtain ⟨x, hxA, hx⟩ := key z hr j (by omega) (by omega)
    exact Finset.mem_image.2 ⟨x, hxA, hx⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_image_le (s := A) (f := par Q F C)
  rw [Nat.card_Icc] at h1
  have := hd.hR
  omega

theorem claim3 [Finite V] (hd : CapData Q F P C R) (A : Finset V)
    (hAI : ∀ v ∈ A, v ∈ Iset Q F C R) (hA : A.card < R) (c : V → Bool) :
    ∃ c' : Option V → Bool, ∀ S' : Finset (Option V),
      (∀ v, v ∈ Iset Q F C R → some v ∈ S' → v ∈ A) →
      (mono (capGraph Q (Iset Q F C R) (Nset Q F C R)) S' c').ncard ≤ (mono Q A c).ncard := by
  classical
  set Z := Zset Q F C R A with hZ
  have hZF : ∀ z ∈ Z, ∀ e ∈ F, z ∉ e := Z_not_F hd A hAI hA
  have hZclosed : ∀ z, z ∈ Z → ∀ v, v ∈ A → (Tg Q F).Adj z v → v ∈ Z := by
    intro z hz v hvA hadj
    obtain ⟨hzA, u, huA, huN, hr⟩ := hz
    exact ⟨hvA, u, huA, huN, hr.tail ⟨hzA, hvA, hadj⟩⟩
  have hZadj : ∀ z ∈ Z, ∀ v, Q.Adj z v → (Tg Q F).Adj z v := by
    intro z hz v hQ
    rcases adj_of_Q (F := F) hQ with h | h
    · exact h
    · exact absurd (Sym2.mem_mk_left z v) (hZF z hz _ h)
  let c'' : V → Bool := fun v => if v ∈ Z then pb (par Q F C v) else c v
  refine ⟨fun a => match a with | none => true | some v => c'' v, ?_⟩
  intro S' hS'
  have hsub : mono (capGraph Q (Iset Q F C R) (Nset Q F C R)) S'
      (fun a => match a with | none => true | some v => c'' v) ⊆
      (Sym2.map some) '' (mono Q A c) := by
    rintro e ⟨a, b, rfl, ha, hb, hadj, hcc⟩
    cases a with
    | none =>
      cases b with
      | none => exact absurd hadj (capGraph_adj_none_none _ _ _)
      | some v =>
        have hvN : v ∈ Nset Q F C R := hadj
        have hvA : v ∈ A := hS' v hvN.1 hb
        have hvZ : v ∈ Z := ⟨hvA, v, hvA, hvN, Relation.ReflTransGen.refl⟩
        have h1 : pb (par Q F C v) = false := chi_N hd hvN
        simp only [c'', if_pos hvZ, h1] at hcc
        simp at hcc
    | some u =>
      cases b with
      | none =>
        have huN : u ∈ Nset Q F C R := hadj
        have huA : u ∈ A := hS' u huN.1 ha
        have huZ : u ∈ Z := ⟨huA, u, huA, huN, Relation.ReflTransGen.refl⟩
        have h1 : pb (par Q F C u) = false := chi_N hd huN
        simp only [c'', if_pos huZ, h1] at hcc
        simp at hcc
      | some v =>
        obtain ⟨huI, hvI, hQ⟩ := hadj
        have huA : u ∈ A := hS' u huI ha
        have hvA : v ∈ A := hS' v hvI hb
        have hcc' : c'' u = c'' v := hcc
        refine ⟨s(u, v), ⟨u, v, rfl, huA, hvA, hQ, ?_⟩, by simp⟩
        by_cases huZ : u ∈ Z
        · exfalso
          have hT := hZadj u huZ v hQ
          have hvZ := hZclosed u huZ v hvA hT
          simp only [c'', if_pos huZ, if_pos hvZ] at hcc'
          exact chi_adj hd hT huI hvI hcc'
        · by_cases hvZ : v ∈ Z
          · exfalso
            have hT := hZadj v hvZ u hQ.symm
            exact huZ (hZclosed v hvZ u huA hT)
          · simp only [c'', if_neg huZ, if_neg hvZ] at hcc'
            exact hcc'
  calc (mono (capGraph Q (Iset Q F C R) (Nset Q F C R)) S'
        (fun a => match a with | none => true | some v => c'' v)).ncard
      ≤ ((Sym2.map some) '' (mono Q A c)).ncard :=
        Set.ncard_le_ncard hsub ((Set.toFinite _).image _)
    _ ≤ (mono Q A c).ncard := Set.ncard_image_le (Set.toFinite _)

end cap

end E74
