import Scc.Lower.Raw
import Scc.Lower.SpecX64
import Scc.Frontend
import Scc.Cert.Elf
import Scc.Test.ElfTest
import Scc.Test.Src

/-!
# `hello1.w` on x86-64, `--host raw`, linked (uncertified)

`Scc/Test/elf/hello1rawx64/hello1.s` is `scc --host raw -S` of `hello1.w`
(checked below against the raw pipeline, `Lower.lowerIRHost` with
`host := .raw`, then `Lower.X64.emitAll` and its listing), assembled by GNU
`as` and linked by GNU `ld -static` with `Scc/Test/elf/raw.ld`
(`Scc/Test/elf.sh`): the text at address 0, `.rodata` and the data each from
the next 64 KiB granule, entry `scc_rt_main`. It is not a certificate's text
and no placement check runs on it.

The layout reader (`Scc.Cert.Elf.elfParts`) refuses the file: its entry is
`scc_rt_main`, after the kernel routine trampolines, not the start of
`.text` (the reader's `_start` rule). The refusal is pinned below and is
expected to change when the reader learns raw units. The file is read here
with the reader's parts (`header`, `sections`, `symTable`) instead, and
pinned by its SHA-256. `Scc/Test/elf.sh --raw-check` compares it with the Linux
`hello1x64/hello1` (`Scc/Test/rawcheck.py`).
-/

namespace Spike.Test.Hello1RawLinkedX64

open Scc.Cert.Elf

/-- The path of the linked executable. -/
def path : String := "Scc/Test/elf/hello1rawx64/hello1"

/-- `hello1.w`'s raw listing on x86-64, as `scc --host raw -S` prints it. -/
def rawText : Except String String := do
  let c ← match Scc.Frontend.run (w_src% "Scc/Test/hello1.w") with
    | .ok c => pure c
    | .error _ => throw "frontend error"
  let l ← Scc.Lower.lowerIRHost { arch := .x64, host := .raw } c.prog
  let e ← Scc.Lower.X64.emitAll l
  return (← e.listing).text

-- The text linked is the raw listing, verbatim (evaluation).
/-- info: true -/
#guard_msgs in
#eval do IO.println (some (← IO.FS.readFile "Scc/Test/elf/hello1rawx64/hello1.s") == rawText.toOption)

-- The file read is the executable linked (evaluation, not a proof).
/-- info: 04271835b4aa0a38b7ba3b9497215022e7e9bb95779cb1d6ff9393b10a5d3cf7 -/
#guard_msgs in
#eval do IO.println (Scc.Cert.Sha256.ofBytes (← IO.FS.readBinFile path))

/-- The entry, the `.text` section's address and size, and the address of
each named symbol (`none` when missing), read with the reader's parts. -/
def facts (b : ByteArray) (names : List String) :
    Except String (Nat × Nat × Nat × List (Option Nat)) := do
  let h ← header b
  let secs ← sections b h
  let some t := secs.find? (·.name == ".text") | throw "no .text"
  let syms ← symTable b secs
  return (h.entry, t.addr, t.size, names.map fun n => (syms.find? (·.name == n)).map (·.value))

-- The entry is `scc_rt_main`; `.text` and `scc_text_start` at 0; the
-- trampolines, from `scc_kabi_start`, end at `scc_kabi_end` before `wc_main`.
/-- info: ok -/
#guard_msgs in
#eval do
  let b ← IO.FS.readBinFile path
  match facts b ["scc_rt_main", "scc_text_start", "scc_kabi_start", "scc_kabi_end", "wc_main"] with
  | .ok (e, t, _, [some m, some ts, some ks, some ke, some w]) =>
    IO.println (if e == m && t == 0 && ts == 0 && ks == 0 && ks < ke && ke ≤ w then "ok"
      else s!"entry {e}, text {t}, symbols {[m, ts, ks, ke, w]}")
  | .ok r => IO.println s!"missing symbol: {repr r.2.2.2}"
  | .error m => IO.println m

-- The layout reader refuses the file (its `_start` rule), as documented above;
-- expected to change when the reader learns raw units.
/-- info: the entry point 181 is not the start of .text (0) -/
#guard_msgs in
#eval Scc.Test.Elf.verdict path pure

end Spike.Test.Hello1RawLinkedX64
