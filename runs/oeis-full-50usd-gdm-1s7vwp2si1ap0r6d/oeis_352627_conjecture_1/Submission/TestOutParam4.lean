class Unsound where
  val : Empty

instance unsound_inst (n : Nat) [Unsound] : Unsound where
  val := (unsound_inst (n - 1)).val
