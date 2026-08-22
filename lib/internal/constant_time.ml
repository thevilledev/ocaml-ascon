let equal a b =
  let len = Bytes.length a in
  if len <> Bytes.length b then false
  else
    let difference = ref 0 in
    for i = 0 to len - 1 do
      difference :=
        !difference
        lor (Char.code (Bytes.unsafe_get a i) lxor Char.code (Bytes.unsafe_get b i))
    done;
    !difference = 0
