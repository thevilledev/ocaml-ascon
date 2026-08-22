type t = {
  mutable x0 : int64;
  mutable x1 : int64;
  mutable x2 : int64;
  mutable x3 : int64;
  mutable x4 : int64;
}

let create x0 x1 x2 x3 x4 = { x0; x1; x2; x3; x4 }
let copy s = { x0 = s.x0; x1 = s.x1; x2 = s.x2; x3 = s.x3; x4 = s.x4 }
