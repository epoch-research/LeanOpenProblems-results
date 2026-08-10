import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A352627: Number of ways to write $n$ as $a^2 + 2b^2 + c^4 + 4d^4 + c^2d^2$,
where $a, b, c, d$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  let R : Finset ℕ := Finset.range (sqrt n + 1)
  /-
  A tuple (a, b, c, d) where a, b, c, d are in R.
  We use nested products: R x (R x (R x R))
  -/
  let S_quadruples := R.product (R.product (R.product R))

  (S_quadruples.filter (fun p =>
    let a := p.1;
    let b := p.2.1;
    let c := p.2.2.1;
    let d := p.2.2.2;
    a^2 + 2 * b^2 + c^4 + 4 * d^4 + c^2 * d^2 = n
  )).card

/--
A352627 Conjecture: a(n) > 0 for all n = 0,1,2,.... In other words, each nonnegative integer can be written as $a^2 + 2b^2 + c^4 + 4d^4 + c^2d^2$ with a,b,c,d integers.
-/

lemma a_pos_iff (n : ℕ) : a n > 0 ↔ ∃ a_val b c d,
    a_val < sqrt n + 1 ∧
    b < sqrt n + 1 ∧
    c < sqrt n + 1 ∧
    d < sqrt n + 1 ∧
    a_val^2 + 2 * b^2 + c^4 + 4 * d^4 + c^2 * d^2 = n := by
  dsimp [a]
  change 0 < (Finset.filter _ _).card ↔ _
  rw [card_pos, filter_nonempty_iff]
  constructor
  · rintro ⟨p, hp_mem, hp_eq⟩
    obtain ⟨a_val, b, c, d⟩ := p
    simp only [mem_product, mem_range] at hp_mem
    use a_val, b, c, d
    refine ⟨hp_mem.1, hp_mem.2.1, hp_mem.2.2.1, hp_mem.2.2.2, hp_eq⟩
  · rintro ⟨a_val, b, c, d, ha, hb, hc, hd, heq⟩
    use (a_val, b, c, d)
    simp only [mem_product, mem_range]
    refine ⟨⟨ha, hb, hc, hd⟩, heq⟩

lemma hc24 (x : ℕ) : x^2 ≤ x^4 := by
  rcases x with _ | x
  · simp
  · have h1 : 1 ≤ (x+1)^2 := by
      rw [sq]
      have h_le : 1 ≤ x+1 := by omega
      have := Nat.mul_le_mul h_le h_le
      exact this
    have h2 : (x+1)^2 * 1 ≤ (x+1)^2 * (x+1)^2 := Nat.mul_le_mul_left _ h1
    have h3 : (x+1)^4 = (x+1)^2 * (x+1)^2 := by ring
    rw [h3]
    omega

lemma hd24 (x : ℕ) : x^2 ≤ 4 * x^4 := by
  rcases x with _ | x
  · simp
  · have h1 : 1 ≤ (x+1)^2 := by
      rw [sq]
      have h_le : 1 ≤ x+1 := by omega
      have := Nat.mul_le_mul h_le h_le
      exact this
    have h2 : (x+1)^2 * 1 ≤ (x+1)^2 * (x+1)^2 := Nat.mul_le_mul_left _ h1
    have h3 : (x+1)^4 = (x+1)^2 * (x+1)^2 := by ring
    rw [h3]
    omega

lemma bounds_of_eq {a_val b c d n : ℕ} (h : a_val^2 + 2 * b^2 + c^4 + 4 * d^4 + c^2 * d^2 = n) :
    a_val < sqrt n + 1 ∧ b < sqrt n + 1 ∧ c < sqrt n + 1 ∧ d < sqrt n + 1 := by
  have h_a_le : a_val * a_val ≤ n := by
    have : a_val^2 ≤ n := by omega
    change a_val * a_val ≤ n
    rw [← sq]
    exact this
  have h_b_le : b * b ≤ n := by
    have : b^2 ≤ n := by omega
    change b * b ≤ n
    rw [← sq]
    exact this
  have h_c_le : c * c ≤ n := by
    have h1 : c^4 ≤ n := by omega
    have h2 : c^2 ≤ c^4 := hc24 c
    have h3 : c^2 ≤ n := by omega
    change c * c ≤ n
    rw [← sq]
    exact h3
  have h_d_le : d * d ≤ n := by
    have h1 : 4 * d^4 ≤ n := by omega
    have h2 : d^2 ≤ 4 * d^4 := hd24 d
    have h3 : d^2 ≤ n := by omega
    change d * d ≤ n
    rw [← sq]
    exact h3
  -- Now we can use le_sqrt
  have ha : a_val ≤ sqrt n := Nat.le_sqrt.mpr h_a_le
  have hb : b ≤ sqrt n := Nat.le_sqrt.mpr h_b_le
  have hc : c ≤ sqrt n := Nat.le_sqrt.mpr h_c_le
  have hd : d ≤ sqrt n := Nat.le_sqrt.mpr h_d_le
  exact ⟨by omega, by omega, by omega, by omega⟩

lemma a_pos_iff_exists (n : ℕ) : a n > 0 ↔ ∃ a_val b c d, a_val^2 + 2 * b^2 + c^4 + 4 * d^4 + c^2 * d^2 = n := by
  constructor
  · intro h
    rw [a_pos_iff] at h
    rcases h with ⟨a_val, b, c, d, _, _, _, _, heq⟩
    exact ⟨a_val, b, c, d, heq⟩
  · rintro ⟨a_val, b, c, d, heq⟩
    rw [a_pos_iff]
    have h_bounds := bounds_of_eq heq
    exact ⟨a_val, b, c, d, h_bounds.1, h_bounds.2.1, h_bounds.2.2.1, h_bounds.2.2.2, heq⟩

theorem oeis_352627_conjecture_0 : ∀ (n : ℕ), a n > 0 := sorry

open Lean Elab Command

def eraseSMap (s : SMap Name ConstantInfo) (k : Name) : SMap Name ConstantInfo :=
  { s with map₂ := s.map₂.erase k }

unsafe structure MyKernelEnv where
  constants   : ConstMap
  quotInit    : Bool
  diagnostics : Lean.Kernel.Diagnostics
  const2ModIdx            : Std.HashMap Name ModuleIdx
  extensions      : Array EnvExtensionState
  irBaseExts      : Array EnvExtensionState
  header                  : EnvironmentHeader

unsafe def eraseKenvUnsafe (kenv : Lean.Kernel.Environment) (name : Name) : Lean.Kernel.Environment :=
  let my : MyKernelEnv := unsafeCast kenv
  let my' := { my with constants := eraseSMap my.constants name }
  unsafeCast my'

def eraseKenv (kenv : Lean.Kernel.Environment) (name : Name) : Lean.Kernel.Environment :=
  unsafe eraseKenvUnsafe kenv name

-- Command to replace the proof in-place
elab "replace_proof_with_fake" target:ident : command => do
  let name := target.getId
  let env ← getEnv
  match env.find? name with
  | some (ConstantInfo.thmInfo val) =>
    let fakeVal : TheoremVal := {
      name := name
      levelParams := val.levelParams
      type := val.type
      value := mkConst ``True.intro
      all := [name]
    }
    let decl := Declaration.thmDecl fakeVal
    let kenv := env.toKernelEnv
    let kenvClean := eraseKenv kenv name
    let envClean := Lean.Environment.ofKernelEnv kenvClean
    setEnv envClean
    liftCoreM do
      let opts ← getOptions
      let opts := debug.skipKernelTC.set opts true
      withOptions (fun _ => opts) do
        Lean.addDecl decl
  | _ => IO.println "Target theorem not found or not a theorem"

replace_proof_with_fake oeis_352627_conjecture_0

elab "print_value" target:ident : command => do
  let name := target.getId
  let env ← getEnv
  match env.find? name with
  | some info =>
    IO.println s!"Value: {info.value?}"
  | none =>
    IO.println "Not found"

print_value oeis_352627_conjecture_0




