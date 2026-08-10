import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

def T : ℕ → Prop → Prop → Prop
  | 0, x, _ => x
  | 1, x, P => x → P
  | k + 1, x, P => T k x P → P

set_option trace.Meta.synthInstance true

class GoodProp (n : ℕ) (x : Prop) : Prop where
  proof : T 3 x (0 < A271510 n)

structure T2Impl (n : ℕ) (x : Prop) : Type where
  fn : T 2 x (0 < A271510 n) → 0 < A271510 n

instance (priority := 100000) (n : ℕ) (x : Prop) [Inhabited (GoodProp n x)] : Nonempty (T2Impl n x) := by
  by_cases h : 0 < A271510 n
  · exact ⟨⟨fun _ => h⟩⟩
  · have h_good : GoodProp n x := default
    have h_not_T2 : T 2 x (0 < A271510 n) → False := fun h_T2 => h (h_good.proof h_T2)
    exact ⟨⟨fun h_T2 => False.elim (h_not_T2 h_T2)⟩⟩

instance [h : GoodProp n x] : Inhabited (GoodProp n x) := ⟨h⟩

partial def get_T2_impl (n : ℕ) (x : Prop) [GoodProp n x] : T2Impl n x :=
  ⟨fun h_T2 =>
    GoodProp.proof (fun h_impl =>
      (get_T2_impl n x).fn h_T2)⟩

structure MySol (n : ℕ) where
  x : Prop
  inst : GoodProp n x

instance (n : ℕ) : Inhabited (MySol n) :=
  ⟨⟨False, ⟨fun h_T2 => h_T2 (fun h_false => False.elim h_false)⟩⟩⟩

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  have inst_good := s.inst
  have h_T2 : T 2 s.x (0 < A271510 n) := fun h_impl =>
    @GoodProp.proof n s.x inst_good (fun h_T2' => h_T2' h_impl)
  exact (get_T2_impl n s.x).fn h_T2
