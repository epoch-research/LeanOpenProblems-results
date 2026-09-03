import FormalConjecturesUtil
import Submission.ThetaPositiveCompletion
import Submission.ThetaHeavyMatching

/-! In a rigid theta-free family, all local zero-pair witnesses for arbitrarily
many large heavy books can lie in the same five-element set. This does not
refute a global zero-pair charge or the theta density gap. -/
open Finset
open scoped Classical
namespace Erdos713ThetaForcedDiamond
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
set_option maxHeartbeats 2000000

abbrev Rows (N : ℕ) := Fin 3 × Fin N
abbrev Cols (N : ℕ) := Fin 4 ⊕ (Fin N × Fin 2)

def side (h : Fin 4) : Fin 3 := ![0,0,1,2] h

def Inc (N : ℕ) (a : Rows N) : Cols N → Prop
  | .inl h => a.1 = side h
  | .inr p => a.2 = p.1

def hub {N : ℕ} (h : Fin 4) : Cols N := .inl h
def anchor {N : ℕ} (i : Fin N) (t : Fin 2) : Cols N := .inr (i,t)

lemma hub_injective (N : ℕ) : Function.Injective (@hub N) := Sum.inl_injective
lemma anchor_injective {N : ℕ} (i : Fin N) : Function.Injective (@anchor N i) := by
  intro j k he
  exact congrArg Prod.snd (Sum.inr.inj he)

lemma side_fiber_le (s : Fin 3) : (univ.filter (fun h : Fin 4 => side h = s)).card ≤ 2 := by
  fin_cases s <;> decide

lemma common_subset {N : ℕ} {a b : Rows N} (hab : a ≠ b) :
    (row (Inc N) a ∩ row (Inc N) b ⊆ univ.image (@hub N)) ∨
    row (Inc N) a ∩ row (Inc N) b ⊆ univ.image (@anchor N a.2) := by
  by_cases hi : a.2 = b.2
  · right
    have hs : a.1 ≠ b.1 := fun he => hab (Prod.ext he hi)
    intro x hx
    have hx' : Inc N a x ∧ Inc N b x := by simpa only [mem_inter,mem_row] using hx
    rcases x with h | ⟨i,t⟩
    · exact (hs (hx'.1.trans hx'.2.symm)).elim
    · exact mem_image.mpr ⟨t,mem_univ _,congrArg (fun i => anchor i t) hx'.1⟩
  · left
    intro x hx
    have hx' : Inc N a x ∧ Inc N b x := by simpa only [mem_inter,mem_row] using hx
    rcases x with h | p
    · exact mem_image.mpr ⟨h,mem_univ _,rfl⟩
    · exact (hi (hx'.1.trans hx'.2.symm)).elim

lemma rigid (N : ℕ) (a b : Rows N) (hab : a ≠ b) :
    (row (Inc N) a ∩ row (Inc N) b).card ≤ 2 := by
  rcases common_subset hab with hh | ha
  · have hsub : row (Inc N) a ∩ row (Inc N) b ⊆
        (univ.filter (fun h : Fin 4 => side h = a.1)).image (@hub N) := by
      intro x hx
      obtain ⟨h,_,rfl⟩ := mem_image.mp (hh hx)
      have hax : a.1 = side h := (mem_row (Inc N) a (hub h)).mp (mem_inter.mp hx).1
      exact mem_image.mpr ⟨h,mem_filter.mpr ⟨mem_univ _,hax.symm⟩,rfl⟩
    exact (card_le_card hsub).trans ((card_image_le).trans (side_fiber_le a.1))
  · exact (card_le_card ha).trans (by rw [card_image_of_injective _ (anchor_injective _)]; simp)

/-- Private columns on opposite sides of two intersecting rows cannot meet. -/
lemma private_cross {N : ℕ} {a b c : Rows N} {z x y : Cols N}
    (haz : Inc N a z) (hbz : Inc N b z)
    (hax : Inc N a x) (hbx : ¬ Inc N b x)
    (hby : Inc N b y) (hay : ¬ Inc N a y)
    (hcx : Inc N c x) (hcy : Inc N c y) : False := by
  rcases z with h | ⟨i,t⟩
  · have hs : a.1 = b.1 := haz.trans hbz.symm
    rcases x with u | ⟨j,v⟩
    · exact hbx (hs.symm.trans hax)
    rcases y with u | ⟨k,w⟩
    · exact hay (hs.trans hby)
    exact hbx (hby.trans (hcy.symm.trans hcx))
  · have hi : a.2 = b.2 := haz.trans hbz.symm
    rcases x with u | ⟨j,v⟩
    · rcases y with w | ⟨k,v⟩
      · exact hbx ((hcy.trans hby.symm).symm.trans hcx)
      · exact hay (hi.trans hby)
    · exact hbx (hi.symm.trans hax)

lemma no_theta (N : ℕ) : ¬ HasTheta (Inc N) := by
  rintro ⟨a,b,ha,hb,h00,h10,h01,h11,h02,h22,h13,h23⟩
  have hab : a 0 ≠ a 1 := fun he => (by decide : (0 : Fin 3) ≠ 1) (ha he)
  have hn (i j : Fin 4) (hij : i ≠ j) : b i ≠ b j := fun he => hij (hb he)
  have hx : ¬ Inc N (a 1) (b 2) := by
    intro hh
    exact hab (Erdos713ThetaPositiveCompletion.eq_of_three (fun a b hab => by
      convert rigid N a b hab using 1
      congr 1
      ext x
      simp)
      (hn 0 1 (by decide)) (hn 0 2 (by decide)) (hn 1 2 (by decide))
      h00 h01 h02 h10 h11 hh)
  have hy : ¬ Inc N (a 0) (b 3) := by
    intro hh
    exact hab (Erdos713ThetaPositiveCompletion.eq_of_three (fun a b hab => by
      convert rigid N a b hab using 1
      congr 1
      ext x
      simp)
      (hn 0 1 (by decide)) (hn 0 3 (by decide)) (hn 1 3 (by decide))
      h00 h01 hh h10 h11 h13)
  exact private_cross h00 h10 h02 hx h13 hy h22 h23

lemma anchor_codegree {N : ℕ} (i : Fin N) :
    codegree (Inc N) (anchor i 0) (anchor i 1) = 3 := by
  let e : {a : Rows N // Inc N a (anchor i 0) ∧ Inc N a (anchor i 1)} ≃ Fin 3 := {
    toFun := fun a => a.val.1
    invFun := fun s => ⟨(s,i),rfl,rfl⟩
    left_inv := fun a => Subtype.ext (Prod.ext rfl a.property.1.symm)
    right_inv := fun _ => rfl }
  change Nat.card _ = 3
  rw [Nat.card_congr e]
  simp

lemma large_row {N : ℕ} (i : Fin N) : (row (Inc N) (0,i)).card = 4 := by
  have he : row (Inc N) (0,i) = {hub 0,hub 1,anchor i 0,anchor i 1} := by
    ext x
    rcases x with h | ⟨j,t⟩
    · fin_cases h <;> simp [mem_row,Inc,hub,anchor,side]
    · fin_cases t <;> simp [mem_row,Inc,hub,anchor,eq_comm]
  rw [he]
  simp [hub,anchor]

lemma no_exact_pair {N : ℕ} (i : Fin N) (a : Rows N) :
    row (Inc N) a ≠ {anchor i 0,anchor i 1} := by
  intro he
  have hs : ∀ s : Fin 3, ∃ h : Fin 4, s = side h := by
    intro s
    fin_cases s
    · exact ⟨0,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
  obtain ⟨h,hh⟩ := hs a.1
  have hm : hub h ∈ row (Inc N) a := (mem_row _ _ _).mpr hh
  rw [he] at hm
  simp [hub,anchor] at hm

/-- Every non-anchor column in any row of this anchor book is a hub.
There are no additional private columns available for a different choice. -/
lemma book_petal_is_hub {N : ℕ} (i : Fin N) {a : Rows N} {x : Cols N}
    (ha : Inc N a (anchor i 0)) (hx : Inc N a x)
    (hx0 : x ≠ anchor i 0) (hx1 : x ≠ anchor i 1) :
    ∃ h : Fin 4, x = hub h := by
  rcases x with h | ⟨j,t⟩
  · exact ⟨h,rfl⟩
  · have hij : j = i := hx.symm.trans ha
    subst j
    fin_cases t
    · exact (hx0 rfl).elim
    · exact (hx1 rfl).elim

lemma hub_zero_iff {N : ℕ} (i : Fin N) (h k : Fin 4) :
    codegree (Inc N) (hub h) (hub k) = 0 ↔ side h ≠ side k := by
  constructor
  · intro hz he
    haveI : Nonempty {a : Rows N // Inc N a (hub h) ∧ Inc N a (hub k)} :=
      ⟨⟨(side h,i),rfl,he⟩⟩
    have hp : 0 < codegree (Inc N) (hub h) (hub k) := Nat.card_pos
    omega
  · intro hn
    letI : IsEmpty {a : Rows N // Inc N a (hub h) ∧ Inc N a (hub k)} :=
      ⟨fun a => hn (a.property.1.symm.trans a.property.2)⟩
    exact Nat.card_of_isEmpty

noncomputable def zeroHubPairs (N : ℕ) : Finset (Finset (Cols N)) :=
  {{hub 0,hub 2},{hub 0,hub 3},{hub 1,hub 2},{hub 1,hub 3},{hub 2,hub 3}}

lemma zeroHubPairs_card (N : ℕ) : (zeroHubPairs N).card = 5 := by
  let S : Finset (Finset (Fin 4)) := {{0,2},{0,3},{1,2},{1,3},{2,3}}
  have he : zeroHubPairs N = S.image (Finset.image (@hub N)) := by
    simp [S,zeroHubPairs]
  rw [he,card_image_of_injective _ (Finset.image_injective (hub_injective N))]
  decide

lemma zero_hubs_mem {N : ℕ} (i : Fin N) {h k : Fin 4}
    (hz : codegree (Inc N) (hub h) (hub k) = 0) :
    ({hub h,hub k} : Finset (Cols N)) ∈ zeroHubPairs N := by
  have hn := (hub_zero_iff i h k).mp hz
  fin_cases h <;> fin_cases k <;> simp_all [side,zeroHubPairs,Finset.pair_comm]

/-- Any choice of a local zero pair in a distinguished book is one of the
same five pairs, independently of the book's index. -/
theorem local_zero_mem {N : ℕ} (i : Fin N) {a b : Rows N} {x y : Cols N}
    (ha : Inc N a (anchor i 0)) (hb : Inc N b (anchor i 0))
    (hx : Inc N a x) (hy : Inc N b y)
    (hx0 : x ≠ anchor i 0) (hx1 : x ≠ anchor i 1)
    (hy0 : y ≠ anchor i 0) (hy1 : y ≠ anchor i 1)
    (hz : codegree (Inc N) x y = 0) : {x,y} ∈ zeroHubPairs N := by
  obtain ⟨h,rfl⟩ := book_petal_is_hub i ha hx hx0 hx1
  obtain ⟨k,rfl⟩ := book_petal_is_hub i hb hy hy0 hy1
  exact zero_hubs_mem i hz

theorem no_local_injection {N : ℕ} (hN : 5 < N)
    (f : Fin N → Finset (Cols N)) (hf : ∀ i, f i ∈ zeroHubPairs N) :
    ¬ Function.Injective f := by
  intro hi
  have hh : N ≤ (zeroHubPairs N).card := by
    simpa using Finset.card_le_card_of_injOn f (fun i _ => hf i)
      (fun i _ j _ he => hi he : Set.InjOn f (univ : Finset (Fin N)))
  rw [zeroHubPairs_card] at hh
  omega

#print axioms rigid
#print axioms no_theta

/-- A zero pair chosen from non-anchor columns in rows of the given book. -/
def LocalZero {N : ℕ} (i : Fin N) (p : Finset (Cols N)) : Prop :=
  ∃ a b : Rows N, ∃ x y : Cols N,
    Inc N a (anchor i 0) ∧ Inc N b (anchor i 0) ∧
    Inc N a x ∧ Inc N b y ∧
    x ≠ anchor i 0 ∧ x ≠ anchor i 1 ∧
    y ≠ anchor i 0 ∧ y ≠ anchor i 1 ∧
    codegree (Inc N) x y = 0 ∧ p = {x,y}

lemma localZero_nonempty {N : ℕ} (i : Fin N) : ∃ p, LocalZero i p := by
  refine ⟨{hub 0,hub 2},(0,i),(1,i),hub 0,hub 2,
    rfl,rfl,rfl,rfl,?_,?_,?_,?_,?_,rfl⟩
  · simp [hub,anchor]
  · simp [hub,anchor]
  · simp [hub,anchor]
  · simp [hub,anchor]
  · exact (hub_zero_iff i 0 2).mpr (by decide)

theorem forced_local_failure {N : ℕ} (hN : 5 < N) :
    ¬ ∃ f : Fin N → Finset (Cols N), Function.Injective f ∧ ∀ i, LocalZero i (f i) := by
  rintro ⟨f,hi,hf⟩
  apply no_local_injection hN f ?_ hi
  intro i
  obtain ⟨a,b,x,y,ha,hb,hx,hy,hx0,hx1,hy0,hy1,hz,he⟩ := hf i
  rw [he]
  exact local_zero_mem i ha hb hx hy hx0 hx1 hy0 hy1 hz

lemma anchor_pairs_injective (N : ℕ) :
    Function.Injective (fun i : Fin N => ({anchor i 0,anchor i 1} : Finset (Cols N))) := by
  intro i j he
  have hh := (Finset.ext_iff.mp he) (anchor i 0)
  simp only [mem_insert,mem_singleton] at hh
  have hm := hh.mp (Or.inl trivial)
  rcases hm with hm | hm <;> exact congrArg Prod.fst (Sum.inr.inj hm)

/-- The hypotheses concern the same relation and the same distinguished books.
Every book has a local witness, but no injective local selection exists. -/
theorem forced_example {N : ℕ} (hN : 5 < N) :
    ¬ HasTheta (Inc N) ∧
    (∀ a b, a ≠ b → (row (Inc N) a ∩ row (Inc N) b).card ≤ 2) ∧
    Function.Injective (fun i : Fin N => ({anchor i 0,anchor i 1} : Finset (Cols N))) ∧
    (∀ i : Fin N, codegree (Inc N) (anchor i 0) (anchor i 1) = 3 ∧
      (row (Inc N) (0,i)).card = 4 ∧
      (∀ a, row (Inc N) a ≠ {anchor i 0,anchor i 1}) ∧ ∃ p, LocalZero i p) ∧
    ¬ ∃ f : Fin N → Finset (Cols N), Function.Injective f ∧ ∀ i, LocalZero i (f i) := by
  exact ⟨no_theta N,rigid N,anchor_pairs_injective N,
    fun i => ⟨anchor_codegree i,large_row i,no_exact_pair i,localZero_nonempty i⟩,
    forced_local_failure hN⟩

#print axioms forced_local_failure
#print axioms forced_example

#print axioms anchor_codegree
#print axioms large_row
#print axioms no_exact_pair
#print axioms local_zero_mem
#print axioms no_local_injection
end Erdos713ThetaForcedDiamond
