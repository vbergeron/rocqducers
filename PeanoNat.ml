
module Nat =
 struct
  (** val leb : int -> int -> bool **)

  let rec leb n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun m' -> leb n' m')
        m)
      n
 end
