/-
The FEAT_LSE2 reading of an `LDP`/`STP` (Armv8.4): a 16-byte-aligned pair of
two `X` registers to Normal memory is single-copy atomic. Kraken's
single-threaded semantics (`Operation.interp`) performs an `LDP`/`STP` as two
accesses in address order and is unchanged; this file gives the alternative
reading as a function of the cell, shared by the weak-memory adapter
(`Kraken.Promising.AArch64.isaLSE2`, the machine) and the environment logic
(`Kraken.AArch64.EnvLSE2`, the judgment), so that the two read a cell the same
way by definition.

`Directive.interpLSE2?` is `some` exactly for a 16-byte-aligned `LDP`/`STP` of
two `X` registers: the pair as one `MachineData.loadPairK`/`storePairK`
(`.plain`, not exclusive), whose effect, when both halves are outside `dmem`,
is the non-exclusive `sync_load_pair`/`sync_store_pair` (which the adapter
performs as one 16-byte access on a declared 16-byte location,
`Kraken.Promising.AArch64.toEv`). `Directive.interpLSE2` is the cell's
interpreter under FEAT_LSE2: that reading where it applies, `Directive.interp`
otherwise.
-/
import Kraken.AArch64.Semantics

/-- The FEAT_LSE2 reading of the cell `d` run in `s` over the range `p`, if
`d` is an `LDP`/`STP` of two `X` registers whose address is a multiple of 16:
the base writeback of the addressing form, the `SP` alignment check, then one
plain pair access, continuing with `next`. `none` for every other cell. -/
def Directive.interpLSE2? [Labels] (d : Directive) (s : MachineData) (p : Std.Rco Int64)
    (next : MachineData → Effects) : Option Effects :=
  match d with
  | .instr ⟨.W64, .LDP dst1 dst2 src⟩ =>
    let (addr, s') := src.eval s p
    if addr % 16 != 0 then none else
    some <| src.checkSPAlignment s fun _ =>
      s'.loadPairK .plain false addr .W64 fun v1 v2 s'' =>
        s''.setRegOrZr dst1 v1 fun s3 => s3.setRegOrZr dst2 v2 next
  | .instr ⟨.W64, .STP src1 src2 dst⟩ =>
    let v1 := s.regs.getRegOrZr src1
    let v2 := s.regs.getRegOrZr src2
    let (addr, s') := dst.eval s p
    if addr % 16 != 0 then none else
    some <| dst.checkSPAlignment s fun _ =>
      s'.storePairK .plain false addr (w := .W64) v1 v2 fun _ s'' => next s''
  | _ => none

/-- The interpreter of the cell `d` under FEAT_LSE2: `interpLSE2?` where it
applies, `Directive.interp` otherwise. -/
def Directive.interpLSE2 [Labels] (d : Directive) (s : MachineData) (p : Std.Rco Int64)
    (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  (d.interpLSE2? s p next).getD (d.interp s p next jmp)

/-- A cell other than a 64-bit `LDP`/`STP` or a `CASP` of two `X` registers has
no FEAT_LSE2 reading. The `LDP`/`STP` reading is `interpLSE2?`; a `CASP` of `X`
registers keeps its effects, which the weak-memory adapter performs as one
16-byte `rmw` on a declared 16-byte location
(`Kraken.Promising.AArch64.toEvCASP`). -/
def Directive.LSE2Free : Directive → Prop
  | .instr ⟨.W64, .LDP ..⟩ => False
  | .instr ⟨.W64, .STP ..⟩ => False
  | .instr ⟨.W64, .CASP ..⟩ => False
  | _ => True

theorem Directive.interpLSE2?_none_of_free [Labels] {d : Directive} (hd : d.LSE2Free)
    (s : MachineData) (p : Std.Rco Int64) (next : MachineData → Effects) :
    d.interpLSE2? s p next = none := by
  unfold Directive.interpLSE2?
  split
  · exact hd.elim
  · exact hd.elim
  · rfl

theorem Directive.interpLSE2_of_none [Labels] {d : Directive} {s : MachineData} {p : Std.Rco Int64}
    {next : MachineData → Effects} (jmp : Int64 → MachineData → Effects)
    (h : d.interpLSE2? s p next = none) : d.interpLSE2 s p next jmp = d.interp s p next jmp := by
  simp only [Directive.interpLSE2, h, Option.getD_none]
