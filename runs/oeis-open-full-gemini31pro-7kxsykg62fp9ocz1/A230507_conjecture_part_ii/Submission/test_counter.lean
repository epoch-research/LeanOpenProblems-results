import Submission.Spec
open OeisA230507

#eval (List.range 100).filter (fun n =>
  if n > 8 then
    ! (List.range n).any (fun x =>
      (List.range n).any (fun y =>
        (List.range n).any (fun z =>
          if x + y + z == n then
            -- Can't easily eval Nat.Prime in Bool
            true
          else false)))
  else false)
