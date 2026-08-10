inductive True' : Prop where
  | intro : True'

def loop : True' → False
  | .intro => loop .intro
