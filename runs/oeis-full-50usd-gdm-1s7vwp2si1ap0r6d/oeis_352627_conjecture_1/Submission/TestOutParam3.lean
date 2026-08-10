class Unsound where
  val : Empty

instance (priority := high) unsound_inst [Unsound] : Unsound where
  val := unsound_inst.val
