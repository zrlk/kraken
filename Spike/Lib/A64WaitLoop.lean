/-
**Main's spin-wait on AArch64** (main's half;
`s1_threads.md` §2.2 option B, proposal 2): `wc_waitLoop` of `hello.w`'s
listing as one segment with the load-or-stutter row (`SegL`,
`Spike/Lib/SegLd.lean`), composed from its blocks over its control-flow
graph (`Spike/Lib/A64CfgL.lean`).

    wc_waitLoop(c = x0):
      stack check: if sp - 32 < limit (thread pointer + 8) goto grow
      prologue (frame of 32 bytes, x29/x30 saved at 16/24, c at 0)
      d = ldar [c]                                -- the acquire load of the flag
      if d = 1 then return 0
      park (bl scc_rt_park); tail call wc_waitLoop(c)
      grow: save x0–x7, x29, x30 in a frame of 80; bl scc_rt_morestack; restore; goto stack check

The source is `let d = load acq c in e` (its control `c0`). **The source
never parks**: it stutters at its load until the target's `ldar` reads `1`,
and only then takes the load (`ldarSt_nd`: a value read that is not `1`
lands with the source at `c0`; `1` lands with `d` bound to a word the
relation lets the source read that represents `1`). The target's park
(`scc_rt_park`) and its tail call back into the stack check are stutters
as well. So on the way back to the entry (`.e`) the source is at `c0`, and
the return exit (`.ret`) has the source past its load.

*Why the source does not park with the target* (proposal 2, condition 2).
A source park would move the source thread's view to at least the source
size it then reads `c` at, `kc` (the worker's `store rel c 1`), while the
target's read view `vrNew` stays below `Tc`, the target worker's store. The
relation then breaks: target main's `swpal` on its permit word can fulfil
main's own earlier promise `pT := 0` at `t2` while reading at `t1 < Tc`,
so after it the target's next `ldar` of `c` may still read the pre-spawn
`T0 = 0`, but the source, whose view is at least `kc`, can only read `1`.
With the source stuttering at its load, the source view is unchanged until
the target reads `1` at `Tc` (`Spike.Lib.Inv2Read.stepOne_load_c`: a read
of `c` gets a pre-spawn `0` or `Tc`'s `1`), and then the source reads `kc`
(`stepLoad_kc`).

The region is `[-80, 0)` from the `sp` at entry: the frame (`[-32, 0)`),
and the stack grow path's 80 bytes. Ghost parameters: the source control
`c0` with its load's binder `x`, continuation `e` and the type `ty` of
its address, the address `A` of `c` (in `x0` at entry), the caller's `x29`
and the return address `ra`, the thread pointer `tp` (`TPIDR_EL0`, kept
everywhere: `scc_rt_park` needs it), and the words the source may read as `1`
(`Rd`, instantiated with `ms.rd` and `ValRep _ 1`). Entry (`.e`): `sp` at
offset 0, `x0 = A`, `x29`, `x30 = ra`, the source at `c0`; the tail call
comes back to it. Return (exit `.ret`): pc at `ra`, `sp` at offset 0,
`x29`, `x30` restored, `x0 = 0`, the source at `e` with `x` bound to a
word of `Rd`.

Given nodes (hypotheses): the thread-pointer load of the stack limit
(`htls`, a `SegW` inside `TlsW`: off the abort exits and the transfer
sites, no load at the flag's `A`, the source at `c0`; it lands at `.n1`
with the limit in `x10` at most the new `sp` in `x9`) and the call to
`scc_rt_park` (`hpark`, from its entry with the return address in `x30`
back to `.sp3`). The stack check never fails (`.n1`'s `x10 ≤ x9`), so the
stack grow path (`.grow`, `.ms`, `.spc`) is dead: its nodes' invariants are
`False`. The park call may move the frame: the region, the frame condition
`F` and the caller's `x29` are a ghost (`fn_seg_gL`). `A` is not private
memory under any frame condition (`hdm`). The code, the prologue's
fall-through into `.0_entry` and the stack-check label at the function's
address are hypotheses.

`seg_parkCall` discharges `hpark` with `Spike.Lib.A64.Flow.Park.seg_park`
(`Spike/Lib/A64Park.lean`) through `call_nd_F` (the park's frame `[-64, 0)`
below the loop's, so the region reaches down to `-96`), and
`seg_waitLoopP` is `seg_waitLoop` with it.

**The label prefix** `pfx` (a parameter of `N`, `Code` and the proofs): the
function's local labels are `pfx ++ ".0_entry"` etc., `pfx` being
`.L<n>_wc_waitLoop` with `n` the compiler's per-program function number
(`.L20_wc_waitLoop` in wake.w's certificate, `.L24_` in hello's old
listing). The blocks that branch to a local label are taken at `pfx`
(`Spike/Lib/A64Relabel.lean`). The runtime's labels
(`.L10_scc_rt_park.0_entry` in `hpentry`, `scc_rt_park`,
`scc_rt_morestack`) are still fixed.
-/
import Spike.Lib.A64CfgL
import Spike.Lib.A64Park
import Spike.Lib.A64Relabel
import Spike.Lib.A64AbOffLDef
import Kraken.AArch64.Parser

namespace Spike.Lib.A64.WaitLoop

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow
open Scc.Sem (ValRep)

/-! ## The blocks (generated) -/

def b0 : List Directive := parseAArch64("sub x9, sp, #32
mrs x10, tpidr_el0")
def b1T : List Directive := parseAArch64("subs xzr, x9, x10
b.lo pfx.stack_grow")
def b2 : List Directive := parseAArch64("add sp, x9, #0
str x29, [sp, #16]
str x30, [sp, #24]
add x29, sp, #16
str x0, [sp]")
def b3 : List Directive := parseAArch64("ldr x10, [sp]")
def b4T : List Directive := parseAArch64("str x9, [sp, #8]
ldr x9, [sp, #8]
movz x10, #1
subs xzr, x9, x10
b.eq pfx.1_then1")
def b5T : List Directive := parseAArch64("b pfx.2_else2")
def b6 : List Directive := parseAArch64("movz x0, #0
ldr x29, [sp, #16]
ldr x30, [sp, #24]
add sp, sp, #32
ret")
def b7 : List Directive := parseAArch64("bl scc_rt_park")
def b8 : List Directive := parseAArch64("ldr x0, [sp]
ldr x29, [sp, #16]
ldr x30, [sp, #24]
add sp, sp, #32
b wc_waitLoop")
def b9 : List Directive := parseAArch64("sub sp, sp, #80
str x0, [sp]
str x1, [sp, #8]
str x2, [sp, #16]
str x3, [sp, #24]
str x4, [sp, #32]
str x5, [sp, #40]
str x6, [sp, #48]
str x7, [sp, #56]
str x29, [sp, #64]
str x30, [sp, #72]
add x29, sp, #64
movz x0, #32
bl scc_rt_morestack")
def b10T : List Directive := parseAArch64("ldr x0, [sp]
ldr x1, [sp, #8]
ldr x2, [sp, #16]
ldr x3, [sp, #24]
ldr x4, [sp, #32]
ldr x5, [sp, #40]
ldr x6, [sp, #48]
ldr x7, [sp, #56]
ldr x29, [sp, #64]
ldr x30, [sp, #72]
add sp, sp, #80
b pfx.stack_check")

/-- The acquire load between `b3` and `b4`. -/
theorem ldar_parse : parseAArch64("ldar x9, [x10]") = [ldarDir .X9 .X10] := by decide

/-- The offsets inside the frame. -/
abbrev oI : SO := ⟨-32, []⟩
/-- The offsets at entry. -/
abbrev oE : SO := ⟨0, []⟩
/-- The offsets during the stack check (`x9` the new `sp`). -/
abbrev oX : SO := ⟨0, [(.X9, -32)]⟩
/-- The offsets in the stack grow path. -/
abbrev oG : SO := ⟨-80, []⟩

block_spec b0 (-80) 0 oE b0
block_spec b1T (-80) 0 oX b1T
block_spec b2 (-80) 0 oX b2
block_spec b3 (-80) 0 oI b3
block_spec b4T (-80) 0 oI b4T
block_spec b5T (-80) 0 oI b5T
block_spec b6 (-80) 0 oI b6
block_spec b7 (-80) 0 oI b7
block_spec b8 (-80) 0 oI b8
block_spec b9 (-80) 0 oE b9
block_spec b10T (-80) 0 oG b10T

/-! ## The blocks at the function's label prefix

The four blocks that end in a branch to a local label (`b1`, `b4`, `b5`,
`b10`) are taken at the function's label prefix `pfx` (`.L<n>_wc_waitLoop`,
numbered by the compiler per program): each is its template (`b1T` …, at
the placeholder prefix `pfx`) with the branch's label replaced, its `okBlk`
is the template's (`okBlk_snoc`) and its abstract run is the template's
under the relabelling `rl` (`arun_snoc`, `dstep_bc`, `dstep_b`). -/

/-- `b1T` without its branch. -/
def b1p : List Directive := parseAArch64("subs xzr, x9, x10")
/-- `b4T` without its branch. -/
def b4p : List Directive := parseAArch64("str x9, [sp, #8]
ldr x9, [sp, #8]
movz x10, #1
subs xzr, x9, x10")
/-- `b10T` without its branch. -/
def b10p : List Directive := parseAArch64("ldr x0, [sp]
ldr x1, [sp, #8]
ldr x2, [sp, #16]
ldr x3, [sp, #24]
ldr x4, [sp, #32]
ldr x5, [sp, #40]
ldr x6, [sp, #48]
ldr x7, [sp, #56]
ldr x29, [sp, #64]
ldr x30, [sp, #72]
add sp, sp, #80")

theorem b1T_eq : b1T = b1p ++ [bcD .CC "pfx.stack_grow"] := by decide
theorem b4T_eq : b4T = b4p ++ [bcD .EQ "pfx.1_then1"] := by decide
theorem b5T_eq : b5T = [] ++ [bD "pfx.2_else2"] := by decide
theorem b10T_eq : b10T = b10p ++ [bD "pfx.stack_check"] := by decide

/-- `b1` at prefix `pfx`. -/
def b1 (pfx : String) : List Directive := b1p ++ [bcD .CC (pfx ++ ".stack_grow")]
/-- `b4` at prefix `pfx`. -/
def b4 (pfx : String) : List Directive := b4p ++ [bcD .EQ (pfx ++ ".1_then1")]
/-- `b5` at prefix `pfx`. -/
def b5 (pfx : String) : List Directive := [] ++ [bD (pfx ++ ".2_else2")]
/-- `b10` at prefix `pfx`. -/
def b10 (pfx : String) : List Directive := b10p ++ [bD (pfx ++ ".stack_check")]

theorem b1_ok {pfx : String} : Flow.okBlk (-80) 0 oX (b1 pfx) = true := by
  rw [b1, okBlk_snoc (t := bcD .CC (pfx ++ ".stack_grow")) (t' := bcD .CC "pfx.stack_grow") (fun _ => rfl), ← b1T_eq]
  exact b1T_ok
theorem b4_ok {pfx : String} : Flow.okBlk (-80) 0 oI (b4 pfx) = true := by
  rw [b4, okBlk_snoc (t := bcD .EQ (pfx ++ ".1_then1")) (t' := bcD .EQ "pfx.1_then1") (fun _ => rfl), ← b4T_eq]
  exact b4T_ok
theorem b5_ok {pfx : String} : Flow.okBlk (-80) 0 oI (b5 pfx) = true := by
  rw [b5, okBlk_snoc (t := bD (pfx ++ ".2_else2")) (t' := bD "pfx.2_else2") (fun _ => rfl), ← b5T_eq]
  exact b5T_ok
theorem b10_ok {pfx : String} : Flow.okBlk (-80) 0 oG (b10 pfx) = true := by
  rw [b10, okBlk_snoc (t := bD (pfx ++ ".stack_check")) (t' := bD "pfx.stack_check") (fun _ => rfl), ← b10T_eq]
  exact b10T_ok

theorem b1_run {pfx : String} (lab : Label → Int64) (am : AM) :
    Flow.arun lab (b1 pfx) am = Flow.arun (rl lab "pfx.stack_grow" (pfx ++ ".stack_grow")) b1T am := by
  rw [b1T_eq]; exact arun_snoc (by decide) (dstep_bc _ _ _ _) am
theorem b4_run {pfx : String} (lab : Label → Int64) (am : AM) :
    Flow.arun lab (b4 pfx) am = Flow.arun (rl lab "pfx.1_then1" (pfx ++ ".1_then1")) b4T am := by
  rw [b4T_eq]; exact arun_snoc (by decide) (dstep_bc _ _ _ _) am
theorem b5_run {pfx : String} (lab : Label → Int64) (am : AM) :
    Flow.arun lab (b5 pfx) am = Flow.arun (rl lab "pfx.2_else2" (pfx ++ ".2_else2")) b5T am := by
  rw [b5T_eq]; exact arun_snoc (by decide) (dstep_b _ _ _) am
theorem b10_run {pfx : String} (lab : Label → Int64) (am : AM) :
    Flow.arun lab (b10 pfx) am = Flow.arun (rl lab "pfx.stack_check" (pfx ++ ".stack_check")) b10T am := by
  rw [b10T_eq]; exact arun_snoc (by decide) (dstep_b _ _ _) am

/-! ## The graph -/

/-- The internal nodes: one per block, the acquire load, and the given
nodes. -/
inductive PN where
  | e | tls | n1 | n2 | entry | ld | n4 | n5 | then1 | else2 | park | sp3 | grow | ms | spc

/-- The exits. -/
inductive PX where
  | ret

section Spec

variable (lab : Label → Int64) (pfx : String) (c0 : Ctl) (x : String) (e : Expr) (ty : Ty) (Rd : TermRun.Word → Prop)
  (A x29 ra tp : BitVec 64)

/-- The source past its load: `x` bound to a word of `Rd`. -/
def Past (c : Ctl) : Prop := ∃ w', Rd w' ∧ c = ⟨e, (x, loadTy ty, [w']) :: c0.env, none⟩

/-- Outside the frame: the source at its load, `x0` the flag's address,
`x29` and `x30` the caller's, the thread pointer `tp`. -/
def JE (σ : Flow.AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.regs.X0.toBitVec = A ∧ σ.regs.X29.toBitVec = x29 ∧ σ.regs.X30.toBitVec = ra ∧
    σ.regs.TPIDR_EL0.toBitVec = tp

/-- Inside the frame: the caller's `x29`, the return address and the flag's
address in their cells. -/
def JF (σ : Flow.AS) : Prop := σ.slot (-16) = x29 ∧ σ.slot (-8) = ra ∧ σ.slot (-32) = A

/-- Inside the frame, the source at its load, the thread pointer `tp`. -/
def JI (σ : Flow.AS) (c : Ctl) : Prop := c = c0 ∧ JF A x29 ra σ ∧ σ.regs.TPIDR_EL0.toBitVec = tp

/-- In the stack grow path: the caller's `x29`, the return address and the
flag's address (`x0`) saved, the thread pointer `tp`. -/
def JG (σ : Flow.AS) (c : Ctl) : Prop := c = c0 ∧ σ.slot (-16) = x29 ∧ σ.slot (-8) = ra ∧ σ.slot (-80) = A ∧
  σ.regs.TPIDR_EL0.toBitVec = tp

/-- **The nodes.** -/
def N : PN → ND
  | .e => ⟨lab "wc_waitLoop", oE, JE c0 A x29 ra tp⟩
  | .tls => ⟨lab "wc_waitLoop" + 4 + 4, oX, fun σ c => JE c0 A x29 ra tp σ c ∧ σ.regs.X10.toBitVec = tp⟩
  | .n1 => ⟨lab "wc_waitLoop" + 4 + 4 + 4, oX, fun σ c => JE c0 A x29 ra tp σ c ∧
      σ.regs.X10.toBitVec.toNat ≤ σ.regs.X9.toBitVec.toNat⟩
  | .n2 => ⟨lab "wc_waitLoop" + 4 + 4 + 4 + 4 + 4, oX, JE c0 A x29 ra tp⟩
  | .entry => ⟨lab (pfx ++ ".0_entry"), oI, JI c0 A x29 ra tp⟩
  | .ld => ⟨lab (pfx ++ ".0_entry") + 4, oI, fun σ c => JI c0 A x29 ra tp σ c ∧ σ.regs.X10.toBitVec = A⟩
  | .n4 => ⟨lab (pfx ++ ".0_entry") + 4 + 4, oI, fun σ c => JF A x29 ra σ ∧ σ.regs.TPIDR_EL0.toBitVec = tp ∧
      ((σ.regs.X9.toBitVec = 1#64 ∧ Past c0 x e ty Rd c) ∨ (σ.regs.X9.toBitVec ≠ 1#64 ∧ c = c0))⟩
  | .n5 => ⟨lab (pfx ++ ".0_entry") + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, JI c0 A x29 ra tp⟩
  | .then1 => ⟨lab (pfx ++ ".1_then1"), oI, fun σ c => JF A x29 ra σ ∧ σ.regs.TPIDR_EL0.toBitVec = tp ∧
      Past c0 x e ty Rd c ∧ σ.regs.X9.toBitVec = 1#64⟩
  | .else2 => ⟨lab (pfx ++ ".2_else2"), oI, JI c0 A x29 ra tp⟩
  | .park => ⟨lab "scc_rt_park", oI, fun σ c => JI c0 A x29 ra tp σ c ∧
      σ.regs.X30.toBitVec =
        BitVec.ofInt 64 (((lab (pfx ++ ".2_else2")).toInt + 4).bmod 18446744073709551616)⟩
  | .sp3 => ⟨lab (pfx ++ ".sp3"), oI, JI c0 A x29 ra tp⟩
  | .grow => ⟨lab (pfx ++ ".stack_grow"), oE, fun _ _ => False⟩
  | .ms => ⟨lab "scc_rt_morestack", oG, fun _ _ => False⟩
  | .spc => ⟨lab (pfx ++ ".sp_check"), oG, fun _ _ => False⟩

/-- **The exit**: back at the caller, the source past its load, `x0 = 0`,
the thread pointer kept; the flag's address still in the (popped) frame's
cell and the loaded `1` in `x9` (where the source's environment is placed
until main's exit). -/
def E : PX → ND
  | .ret => ⟨Int64.ofBitVec ra, oE, fun σ c => Past c0 x e ty Rd c ∧ σ.regs.X0.toBitVec = 0#64 ∧
      σ.regs.X29.toBitVec = x29 ∧ σ.regs.X30.toBitVec = ra ∧ σ.regs.TPIDR_EL0.toBitVec = tp ∧
      σ.slot (-32) = A ∧ σ.regs.X9.toBitVec = 1#64⟩

/-- **The code**: every block at its node's pc. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  top : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .e).pc b0
  n1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .n1).pc (b1 pfx)
  n2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .n2).pc b2
  entry : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .entry).pc b3
  ld : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .ld).pc [ldarDir .X9 .X10]
  n4 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .n4).pc (b4 pfx)
  n5 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .n5).pc (b5 pfx)
  then1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .then1).pc b6
  else2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .else2).pc b7
  sp3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .sp3).pc b8
  grow : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .grow).pc b9
  spc : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .spc).pc (b10 pfx)

end Spec

/-! ## The proof -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {pfx : String} {c0 : Ctl} {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty}
  {w : TermRun.Word} {A ra tp : BitVec 64} {γ : Sort _} {Rg : γ → Region}
  {Fg : γ → MachineData → Prop} {fp : γ → BitVec 64}

/-- The register an `ldar` into `Xt` writes. -/
theorem ldStep_X9 (v : BitVec 64) (σ : Flow.AS) : (ldStep .X9 v σ).regs.X9.toBitVec = v := by
  simp [ldStep, Reg64s.setRegOrZr, Reg64s.setRegOrZr64]

/-- The other registers and the cells. -/
theorem ldStep_slot (v : BitVec 64) (σ : Flow.AS) : (ldStep .X9 v σ).slot = σ.slot := rfl

/-- The thread pointer. -/
theorem ldStep_tp (v : BitVec 64) (σ : Flow.AS) : (ldStep .X9 v σ).regs.TPIDR_EL0 = σ.regs.TPIDR_EL0 :=
  KeepTP.setRegOrZr_tp _ _ _

/-- `scc_rt_park`'s code does not depend on its ghosts (its nodes' pcs do
not). -/
theorem _root_.Spike.Lib.A64.Flow.Park.Code.ghost {exe : _root_.Executable} {endPc : Int64} {c0 c0' : Ctl}
    {x29 ra tp x29' ra' tp' : BitVec 64} (h : Park.Code c0 x29 ra tp exe endPc) :
    Park.Code c0' x29' ra' tp' exe endPc :=
  ⟨h.e, h.n1, h.swp1, h.n2, h.n3, h.wait, h.svc, h.n5, h.swp2, h.n6, h.done⟩

/-- **A dead node** (its invariant `False`): a segment to anything. -/
theorem _root_.Spike.Lib.SegL.ofDead {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {n : ND} {Q : Frag isaLSE2} (h : ∀ σ c, n.J σ c → False) :
    SegL p lbl ms (At exe endPc R F n) Q :=
  ⟨fun _ _ => False, fun _ _ ⟨_, _, _, _, σ, _, _, hJ⟩ => h σ _ hJ, fun _ _ h => h.elim⟩

set_option hygiene false in
/-- A block node: the block, its `okBlk`, its code; the edge is left. -/
macro "node " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine seg_fixL g (seg_nd (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (fun s he hn => hcode.$f s he hn) fun σ c hJ => ⟨c, .refl c, ?_⟩).toL)

/-- Hitting node `j`. -/
macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> simp_all [N, JE, JI, JF, JG, Spike.Lib.upd_apply, Reg64s.getSysReg,
    KeepTP.setRegOrZr_tp, KeepTP.setXReg_tp, KeepTP.setRegOrSp_tp]))

/-- **`wc_waitLoop` is one segment with the load-or-stutter row** from its
entry to its return. The source stutters at its acquire load `c0` until the
`ldar` reads `1`, and then takes it (`Past`); it never parks. The frame may
move (the park and the stack grow are calls): the region, the frame
condition and the caller's `x29` are a ghost `g` (`fn_seg_gL`). -/
theorem seg_waitLoop (hF : ∀ g, FStable (Rg g) (Fg g)) (hR : ∀ g, (Rg g).OK)
    (hal : ∀ g, (Rg g).base.toNat % 16 = 0) (hlo : ∀ g, (Rg g).lo ≤ -80) (hhi : ∀ g, 0 ≤ (Rg g).hi)
    (hterm : c0.term = .let_ x (.load true a) e) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hval : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hdm : ∀ g m, Fg g m → Mem.loadInt m.dmem A 8 = none)
    (hcode : ∀ g, Code pfx c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp exe endPc)
    (hentry : (_root_.Executable.labels exe).label (pfx ++ ".0_entry") =
      (_root_.Executable.labels exe).label "wc_waitLoop" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4)
    (htls : ∀ g,
      SegW (Spike.Lib.A64AbOffL.TlsW (_root_.Executable.labels exe).label A c0) (fun _ _ => False) p lbl ms
        (At exe endPc (Rg g) (Fg g)
          (N (_root_.Executable.labels exe).label pfx c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .tls))
        (At exe endPc (Rg g) (Fg g)
          (N (_root_.Executable.labels exe).label pfx c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .n1)))
    (hpark : ∀ g,
      Seg p lbl ms (At exe endPc (Rg g) (Fg g)
          (N (_root_.Executable.labels exe).label pfx c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .park))
        (fun s c => ∃ g', At exe endPc (Rg g') (Fg g')
          (N (_root_.Executable.labels exe).label pfx c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g') ra tp .sp3) s c))
    (g0 : γ) :
    SegL p lbl ms (At exe endPc (Rg g0) (Fg g0)
        (N (_root_.Executable.labels exe).label pfx c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g0) ra tp .e))
      (fun s c => ∃ g x', At exe endPc (Rg g) (Fg g)
        (E c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp x') s c) := by
  refine fn_seg_gL (Rg := Rg) (Fg := Fg)
    (N := fun g => N _ pfx c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp)
    (E := fun g => E c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp) (fun g i => ?_) g0 PN.e
  have hF := hF g; have hR := hR g; have hal := hal g; have hlo := hlo g; have hhi := hhi g
  have hcode := hcode g
  cases i
  case e => node b0 b0_ok top; rw [N, b0_run]; hit PN.tls
  case tls => exact seg_fixL g (seg_given PN.n1 (htls g).toSeg).toL
  case n1 =>
    node b1 b1_ok n1; rw [N, b1_run, b1T_run, rl_self]
    obtain ⟨hJ, hle⟩ := hJ
    rw [ite_eq_right (by rw [Spike.Lib.A64.Alloc.subs_c]; simpa using hle)]
    hit PN.n2
  case n2 => node b2 b2_ok n2; rw [N, b2_run]; hit PN.entry
  case entry => node b3 b3_ok entry; rw [N, b3_run]; hit PN.ld
  case ld =>
    refine seg_fixL g (ldarSt_nd (V := 1) hF (fun s he hn => hcode.ld s he hn) (hdm g) ?_)
    rintro m σ c - - ⟨⟨rfl, hJ, htp⟩, h10⟩
    refine ⟨h10, x, a, e, ty, w, hterm, hev, hval, htag, fun v hv => ?_, fun v w' hv hr hr' => ?_⟩
    · refine .inl ⟨PN.n4, rfl, (by decide : SO.le oI (oI.kill .X9) = true), hJ, by rw [ldStep_tp, htp], .inr ⟨?_, rfl⟩⟩
      rw [ldStep_X9]; intro h; exact hv (by rw [h]; rfl)
    · refine .inl ⟨PN.n4, rfl, (by decide : SO.le oI (oI.kill .X9) = true), hJ, by rw [ldStep_tp, htp],
        .inl ⟨?_, w', ⟨hr, hr'⟩, rfl⟩⟩
      rw [ldStep_X9]; exact BitVec.eq_of_toNat_eq (by rw [hv]; rfl)
  case n4 =>
    node b4 b4_ok n4; rw [N, b4_run, b4T_run, rl_self]
    obtain ⟨hJ, htp, h | h⟩ := hJ
    · rw [ite_eq_left (by rw [Spike.Lib.A64.Alloc.subs_z]; simp [h.1])]
      refine .inl ⟨PN.then1, rfl, rfl, ?_, ?_, h.2, ?_⟩ <;>
        simp_all [JF, Spike.Lib.upd_apply]
    · rw [ite_eq_right (by rw [Spike.Lib.A64.Alloc.subs_z]; simp [h.1])]
      refine .inl ⟨PN.n5, rfl, rfl, h.2, ?_, ?_⟩ <;>
        simp_all [JF, Spike.Lib.upd_apply]
  case n5 => node b5 b5_ok n5; rw [N, b5_run, b5T_run, rl_self]; hit PN.else2
  case then1 =>
    node b6 b6_ok then1; rw [N, b6_run]
    refine .inr ⟨PX.ret, ?_, rfl, ?_⟩ <;>
      simp_all [N, E, JF, Past]
  case else2 => node b7 b7_ok else2; rw [N, b7_run]; hit PN.park
  case park => exact seg_movedL PN.sp3 (hpark g).toL
  case sp3 => node b8 b8_ok sp3; rw [N, b8_run]; hit PN.e
  case grow => exact SegL.ofDead fun _ _ h => h
  case ms => exact SegL.ofDead fun _ _ h => h
  case spc => exact SegL.ofDead fun _ _ h => h

/-! ## The park call -/

/-- **The call of `scc_rt_park`** (`call_nd_F` with `Park.seg_park`, frame
`[-64, 0)` from the call's `sp`, which is at offset `-32`): from `.park` back
to `.sp3`, the frame unmoved. The ghosts of `seg_park` are the source
control, `x29` and `x30` at the call and the thread pointer `tp` (in `JI`).
The facts it needs are hypotheses: the kernel model (`hK`), the permit
word's (`hS`, `htp4`), the park routine's code (`hpcode`, for any of its
ghosts: `Park.Code.ghost`) and its prologue's fall-through (`hpentry`); and
the return address: `.sp3` is the instruction after the `bl` (`hsp3`). -/
theorem seg_parkCall {R : Region} {F : MachineData → Prop} {Rd : TermRun.Word → Prop} {x29 : BitVec 64}
    {c0' : Ctl} {x29' ra' tp' : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -96) (hhi : 0 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.A64.abi) (hS : Ret0.StOk ms F exe endPc (tp + 16#64) 0#64)
    (htp4 : (tp + 16#64).toNat % 4 = 0) (hpcode : Park.Code c0' x29' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".L10_scc_rt_park.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_park" + 4 + 4 + 4 + 4)
    (hsp3 : (_root_.Executable.labels exe).label (pfx ++ ".sp3") =
      (_root_.Executable.labels exe).label (pfx ++ ".2_else2") + 4) :
    Seg p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .park))
      (At exe endPc R F (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .sp3)) := by
  refine Ret0.seg_one (call_nd_F (lo' := -64) (hi' := 0)
    (N := fun _ : Unit => N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .sp3)
    (E := fun e : Empty => e.elim)
    (Ne := fun g : Ctl × BitVec 64 × BitVec 64 => Park.N (_root_.Executable.labels exe).label g.1 g.2.1 g.2.2 tp .e)
    (Ex := fun g y => Park.E g.1 g.2.1 g.2.2 tp y)
    hR hal hF (by show R.lo ≤ -32 + -64; omega) (by decide) (by show (-32 : Int) < R.hi; omega) (by decide)
    (by show (-32 : Int) % 16 = 0; decide) (by decide) (by decide)
    (fun R' F' hR' hal' hlo' hhi' hF' hFF g =>
      Park.seg_park hF' hR' hal' hlo' hhi' hK (hS.mono hFF) htp4 hpcode.ghost hpentry)
    (fun _ => rfl) ?_ ?_)
  · rintro σC c ⟨⟨rfl, -, htp⟩, -⟩
    exact ⟨(c, σC.regs.X29.toBitVec, σC.regs.X30.toBitVec), rfl, rfl, rfl, rfl, htp⟩
  · rintro ⟨c1, x29', ra'⟩ ⟨⟩ σC c σx c' σR ⟨⟨rfl, hJF, -⟩, h30⟩ ⟨hc, -, hra, -⟩ ⟨hc', -, -, htp'⟩ hreg - hslot
    have hout : ∀ k : Int, -32 ≤ k → k % 8 = 0 → k + 8 ≤ 0 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
      hslot k ⟨h2, by omega, by omega⟩ fun ⟨_, _, h⟩ => by
        simp only [Region.callee, N] at h; omega
    refine .inl ⟨(), ?_, rfl, hc'.trans hc.symm, ⟨?_, ?_, ?_⟩, ?_⟩
    · subst hra
      show (_root_.Executable.labels exe).label (pfx ++ ".sp3") = Int64.ofBitVec σC.regs.X30.toBitVec
      rw [h30, hsp3, Ret0.ofInt_bmod, BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt]; rfl
    · rw [hout (-16) (by decide) (by decide) (by decide)]; exact hJF.1
    · rw [hout (-8) (by decide) (by decide) (by decide)]; exact hJF.2.1
    · rw [hout (-32) (by decide) (by decide) (by decide)]; exact hJF.2.2
    · show σR.regs.TPIDR_EL0.toBitVec = tp
      rw [hreg]; exact htp'

/-- **`wc_waitLoop` with its park call discharged** (`seg_waitLoop` with
`hpark` from `seg_parkCall`): the region must hold the park routine's frame
below the loop's (`hlo`, `-32 - 64`); the permit word's facts under every
frame condition (`hS`), the kernel model, the park routine's code and its
prologue's fall-through, and the return label `.sp3` after the `bl` are
hypotheses. -/
theorem seg_waitLoopP (hF : ∀ g, FStable (Rg g) (Fg g)) (hR : ∀ g, (Rg g).OK)
    (hal : ∀ g, (Rg g).base.toNat % 16 = 0) (hlo : ∀ g, (Rg g).lo ≤ -96) (hhi : ∀ g, 0 ≤ (Rg g).hi)
    (hterm : c0.term = .let_ x (.load true a) e) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hval : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hdm : ∀ g m, Fg g m → Mem.loadInt m.dmem A 8 = none)
    (hcode : ∀ g, Code pfx c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp exe endPc)
    (hentry : (_root_.Executable.labels exe).label (pfx ++ ".0_entry") =
      (_root_.Executable.labels exe).label "wc_waitLoop" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4)
    (hK : ms.K = some Scc.Sem.A64.abi) (hS : ∀ g, Ret0.StOk ms (Fg g) exe endPc (tp + 16#64) 0#64)
    (htp4 : (tp + 16#64).toNat % 4 = 0) {c0' : Ctl} {x29' ra' tp' : BitVec 64}
    (hpcode : Park.Code c0' x29' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".L10_scc_rt_park.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_park" + 4 + 4 + 4 + 4)
    (hsp3 : (_root_.Executable.labels exe).label (pfx ++ ".sp3") =
      (_root_.Executable.labels exe).label (pfx ++ ".2_else2") + 4)
    (htls : ∀ g,
      SegW (Spike.Lib.A64AbOffL.TlsW (_root_.Executable.labels exe).label A c0) (fun _ _ => False) p lbl ms
        (At exe endPc (Rg g) (Fg g)
          (N (_root_.Executable.labels exe).label pfx c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .tls))
        (At exe endPc (Rg g) (Fg g)
          (N (_root_.Executable.labels exe).label pfx c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .n1)))
    (g0 : γ) :
    SegL p lbl ms (At exe endPc (Rg g0) (Fg g0)
        (N (_root_.Executable.labels exe).label pfx c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g0) ra tp .e))
      (fun s c => ∃ g x', At exe endPc (Rg g) (Fg g)
        (E c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp x') s c) :=
  seg_waitLoop hF hR hal (fun g => Int.le_trans (hlo g) (by decide)) hhi hterm hev hval htag hdm hcode hentry
    htls (fun g => (seg_parkCall (hF g) (hR g) (hal g) (hlo g) (hhi g) hK (hS g) htp4 hpcode hpentry hsp3).mono_post
      fun _ _ h => ⟨g, h⟩) g0

end Proof

end Spike.Lib.A64.WaitLoop
