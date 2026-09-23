import Ascon.Spec.Basic

/-! Hexadecimal encoding shared by the KAT runner and the differential driver. -/

namespace Tools
open Ascon.Spec

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def parseHex (s : String) : Except String (List Byte) :=
  let rec go : List Char → Except String (List Byte)
    | [] => .ok []
    | [_] => .error s!"odd-length hex: {s}"
    | a :: b :: rest =>
      match hexDigit a, hexDigit b with
      | some x, some y => do return BitVec.ofNat 8 (16 * x + y) :: (← go rest)
      | _, _ => .error s!"invalid hex: {s}"
  go s.toList

def toHex (bs : List Byte) : String :=
  String.join (bs.map fun b =>
    let n := b.toNat
    let d (k : Nat) : Char := if k < 10 then Char.ofNat (48 + k) else Char.ofNat (87 + k)
    String.ofList [d (n / 16), d (n % 16)])

end Tools
