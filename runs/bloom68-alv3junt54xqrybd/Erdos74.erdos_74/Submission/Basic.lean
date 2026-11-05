import FormalConjecturesUtil

/-! Finite cut costs and graph balls used in the disproof of Erdős 74. -/

namespace E74

open SimpleGraph

universe u v
variable {V : Type u}

/-- Whether the endpoints of an unordered pair have the same binary color. -/
def Mono (b : V → Bool) : Sym2 V → Prop :=
  Sym2.lift ⟨fun x y => b x = b y, fun x y => propext eq_comm⟩

@[simp] theorem mono_mk (b : V → Bool) (x y : V) :
    Mono b s(x,y) ↔ b x = b y := Iff.rfl

/-- The monochromatic edges of a binary cut. -/
noncomputable def defects [Finite V] (G : SimpleGraph V) (b : V → Bool) :
    Finset (Sym2 V) :=
  (Set.toFinite {e | e ∈ G.edgeSet ∧ Mono b e}).toFinset

@[simp] theorem mem_defects [Finite V] (G : SimpleGraph V) (b : V → Bool)
    (e : Sym2 V) : e ∈ defects G b ↔ e ∈ G.edgeSet ∧ Mono b e := by
  classical
  simp [defects]

@[simp] theorem mk_mem_defects [Finite V] (G : SimpleGraph V) (b : V → Bool)
    (x y : V) : s(x,y) ∈ defects G b ↔ G.Adj x y ∧ b x = b y := by
  simp

noncomputable def cost [Finite V] (G : SimpleGraph V) (b : V → Bool) : ℕ :=
  (defects G b).card

/-- Finite edge frustration, in its binary-cut formulation. -/
noncomputable def tau [Finite V] (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ b : V → Bool, cost G b = k}

theorem cost_set_nonempty [Finite V] (G : SimpleGraph V) :
    ({k | ∃ b : V → Bool, cost G b = k} : Set ℕ).Nonempty :=
  ⟨_, (fun _ => false), rfl⟩

theorem tau_le_cost [Finite V] (G : SimpleGraph V) (b : V → Bool) :
    tau G ≤ cost G b := Nat.sInf_le ⟨b, rfl⟩

theorem tau_attained [Finite V] (G : SimpleGraph V) :
    ∃ b : V → Bool, cost G b = tau G :=
  Nat.sInf_mem (cost_set_nonempty G)

/-- Endpoints of a finite set of unordered edges. -/
noncomputable def ends (F : Finset (Sym2 V)) : Finset V := by
  classical
  exact F.biUnion Sym2.toFinset

/-- Binary colors viewed as the first two of three colors. -/
def base (b : Bool) : Fin 3 := if b then 1 else 0

@[simp] theorem base_false : base false = 0 := rfl
@[simp] theorem base_true : base true = 1 := rfl

theorem base_injective : Function.Injective base := by
  intro a b h
  cases a <;> cases b <;> simp_all [base]

/-- Extended graph-metric balls: unreachable vertices are not included. -/
def ball (G : SimpleGraph V) (z : V) (r : ℕ) : Set V :=
  {x | G.edist z x ≤ (r : ℕ∞)}

/-- A named center whose eccentricity is bounded by a natural number. -/
def HasRadius (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∃ z : V, ∀ x : V, G.edist z x ≤ (r : ℕ∞)

/-- A deliberately generous radius budget for recursive binary phase repair. -/
def rho : ℕ → ℕ
  | 0 => 0
  | n + 1 => (100 * (n + 1) + 100) * (rho n + 1)

/-- Padding sufficient for two binary phases and all lower-budget repair supports. -/
def padding (m : ℕ) : ℕ := 4 * m * rho (m - 1) + 20 * m + 10

/-- A subgraph at its own frustration level, with a controlled intrinsic radius. -/
def Pressure [Finite V] (G : SimpleGraph V) : Prop :=
  ∃ (S : Set V) (k : ℕ), 2 ≤ k ∧ tau (G.induce S) = k ∧
    HasRadius (G.induce S) (rho k)

/-- A localized three-color repair of a given binary cut. -/
def Repair [Finite V] (G : SimpleGraph V) (b : V → Bool) : Prop :=
  ∃ c : G.Coloring (Fin 3), ∀ x : V, c x ≠ base (b x) →
    ∃ z ∈ ends (defects G b), G.edist z x ≤ (rho (cost G b) : ℕ∞)

end E74
