import Ascon.Spec.Aead
import Ascon.Spec.Hash
import Tools.Hex

/-!
# Differential driver for the specification

Reads one command per line on standard input and prints one line per command
with the specification's result in hexadecimal. The commands match
`tools/differential/ocaml_driver.ml`:

* `aead KEY NONCE AD PLAINTEXT`: `C ‖ T`
* `hash MESSAGE`
* `xof MESSAGE LENGTH`
* `cxof CUSTOMIZATION MESSAGE LENGTH`

An empty hexadecimal argument is written as `-`.
-/

open Ascon.Spec
open Tools

def arg (s : String) : Except String (List Byte) := if s == "-" then .ok [] else parseHex s

def run (line : String) : Except String String := do
  match line.splitOn " " |>.filter (· ≠ "") with
  | ["aead", k, n, a, p] =>
    let (C, T) := Aead.encrypt (← arg k) (← arg n) (← arg a) (← arg p)
    return toHex (C ++ T)
  | ["hash", m] => return toHex (Hash.hash256 (← arg m))
  | ["xof", m, l] =>
    match l.toNat? with
    | some l => return toHex (Hash.xof128 (← arg m) l)
    | none => .error "invalid length"
  | ["cxof", z, m, l] =>
    match l.toNat? with
    | some l => return toHex (Hash.cxof128 (← arg m) l (← arg z))
    | none => .error "invalid length"
  | _ => .error s!"invalid command: {line}"

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut status : UInt32 := 0
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    match run line.trimAscii.toString with
    | .ok out => stdout.putStrLn out
    | .error e =>
      stdout.putStrLn s!"error: {e}"
      status := 1
    stdout.flush
  return status
