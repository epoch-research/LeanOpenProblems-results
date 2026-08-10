inductive Index : Type 0
| base : Index
| next : Index → Index

inductive Unsound : Prop
| mk : (Type 0 → Unsound) → Unsound

def g : Index → Unsound
| Index.base => Unsound.mk (fun X => g Index.base)
| Index.next i => Unsound.mk (fun X => g i)
