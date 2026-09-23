import Ascon.Spec.Aead
import Ascon.Spec.Hash
import Tools.Hex

/-!
# Validation of the specification against the official KAT files

`lake exe kat <vector directory>` evaluates the *specification* (not the
implementation model) on every vector in the four `ascon-c` KAT files vendored
under `test/vectors/`. This ties the Lean transcription of SP 800-232 to the
reference implementation.
-/

open Ascon.Spec
open Tools

abbrev Record := List (String × String)

def parseRecords (text : String) : List Record :=
  let lines := text.splitOn "\n" |>.map String.trimAscii |>.map (·.toString)
  let step (acc : List Record × Record) (line : String) : List Record × Record :=
    if line.isEmpty then
      if acc.2.isEmpty then acc else (acc.2.reverse :: acc.1, [])
    else
      match line.splitOn "=" with
      | [k, v] => (acc.1, ((k.trimAscii.toString, v.trimAscii.toString) :: acc.2))
      | _ => acc
  let (records, pending) := lines.foldl step ([], [])
  (if pending.isEmpty then records else pending.reverse :: records).reverse

def field (r : Record) (name : String) : Except String (List Byte) :=
  match r.lookup name with
  | some v => parseHex v
  | none => .error s!"missing field {name}"

def checkFile (path : System.FilePath) (expectedCount : Nat)
    (check : Record → Except String Bool) : IO Bool := do
  let records := parseRecords (← IO.FS.readFile path)
  let mut failures := 0
  for r in records do
    match check r with
    | .ok true => pure ()
    | .ok false =>
      failures := failures + 1
      IO.eprintln s!"{path}: mismatch at Count = {r.lookup "Count" |>.getD "?"}"
    | .error e =>
      failures := failures + 1
      IO.eprintln s!"{path}: {e}"
  let ok := failures == 0 && records.length == expectedCount
  IO.println s!"{path.fileName.getD ""}: {records.length - failures}/{records.length} vectors match the specification{if records.length == expectedCount then "" else s!" (expected {expectedCount} records)"}"
  return ok

def decryptResultIs (r : Except Aead.DecryptError (List Byte))
    (expected : Except Aead.DecryptError (List Byte)) : Bool :=
  match r, expected with
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

def aeadCheck (r : Record) : Except String Bool := do
  let K ← field r "Key"
  let N ← field r "Nonce"
  let P ← field r "PT"
  let A ← field r "AD"
  let CT ← field r "CT"
  let (C, T) := Aead.encrypt K N A P
  let encOk := C ++ T == CT
  let decOk := decryptResultIs (Aead.decrypt K N A (CT.take P.length) (CT.drop P.length)) (.ok P)
  -- Single-bit changes at both ends of each tag word must be rejected.
  let tagBitsOk := [0, 63, 64, 127].all fun bit =>
    let T' := T.set (bit / 8) (T.getD (bit / 8) 0 ^^^ BitVec.ofNat 8 (1 <<< (bit % 8)))
    decryptResultIs (Aead.decrypt K N A C T') (.error .authenticationFailure)
  return encOk && decOk && tagBitsOk

def hashCheck (r : Record) : Except String Bool := do
  return Hash.hash256 (← field r "Msg") == (← field r "MD")

def xofCheck (r : Record) : Except String Bool := do
  let md ← field r "MD"
  return Hash.xof128 (← field r "Msg") md.length == md

def cxofCheck (r : Record) : Except String Bool := do
  let md ← field r "MD"
  return Hash.cxof128 (← field r "Msg") md.length (← field r "Z") == md

/-- Official `ascon-c` permutation outputs and SP 800-232 Appendix B
initialization states (the same values as `test/test_ascon.ml`). -/
def permutationChecks : List (String × Bool) :=
  let zero : State := ⟨0, 0, 0, 0, 0⟩
  [("p[8](0)", asconP 8 zero ==
      ⟨0x1418f8af721aa830, 0xa5425f1f8cb31388, 0xa01ef761bf8e1652,
       0xf01fdabf8c8a82b4, 0x0168260badf76a06⟩),
   ("p[12](0)", asconP 12 zero ==
      ⟨0x78ea7ae5cfebb108, 0x9b9bfb8513b560f7, 0x6937f83e03d11a50,
       0x3fe53f36f2c1178c, 0x045d648e4def12c9⟩),
   ("Hash256 IV state", Hash.initial Hash.hashIV ==
      ⟨0x9b1e5494e934d681, 0x4bc3a01e333751d2, 0xae65396c6b34b81a,
       0x3c7fd4a4d56a4db3, 0x1a5c464906c5976d⟩),
   ("XOF128 IV state", Hash.initial Hash.xofIV ==
      ⟨0xda82ce768d9447eb, 0xcc7ce6c75f1ef969, 0xe7508fd780085631,
       0x0ee0ea53416b58cc, 0xe0547524db6f0bde⟩),
   ("CXOF128 IV state", Hash.initial Hash.cxofIV ==
      ⟨0x675527c2a0e8de03, 0x43d12d7dc0377bbc, 0xe9901dec426e81b5,
       0x2ab14907720780b6, 0x8f3f1d02d432bc46⟩)]

def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath := args.headD "../../test/vectors"
  let mut ok := true
  for (name, result) in permutationChecks do
    IO.println s!"{name}: {if result then "matches" else "MISMATCH"}"
    ok := ok && result
  ok := (← checkFile (dir / "LWC_HASH_KAT_128_256.txt") 1025 hashCheck) && ok
  ok := (← checkFile (dir / "LWC_XOF_KAT_128_512.txt") 1025 xofCheck) && ok
  ok := (← checkFile (dir / "LWC_CXOF_KAT_128_512.txt") 1089 cxofCheck) && ok
  ok := (← checkFile (dir / "LWC_AEAD_KAT_128_128.txt") 1089 aeadCheck) && ok
  IO.println (if ok then "All KAT vectors match the specification." else "KAT FAILURES")
  return if ok then 0 else 1
