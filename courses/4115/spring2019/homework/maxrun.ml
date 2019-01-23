let maxrun l =
  let rec runs n = function
    [] -> []
  | h :: (s :: _ as t) when h = s -> runs (n+1) t
  | h :: t -> (n+1) :: runs 0 t
  in List.fold_left max 0 (runs 0 l)

let maxrun2 l =
  let rec runs m r = function
      [] -> m
    | h :: (s :: _ as t) when h = s -> runs m (r+1) t
    | h :: t -> runs (max m (r+1)) 0 t
  in runs 0 0 l
