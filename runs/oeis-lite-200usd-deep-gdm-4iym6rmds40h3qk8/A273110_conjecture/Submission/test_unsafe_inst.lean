class MyClass where
  val : Nat

unsafe instance my_inst : MyClass where
  val := 42

def my_safe_def : Nat :=
  my_inst.val
