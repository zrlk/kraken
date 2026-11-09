import Scc.IR.Core

/-!
# Reserved TCB words (specification constant only)

The platform-owned TCB words (the kernel routine-table word `kabi` among them) are
**dedicated slots** past the runtime's fields, not a reuse of the unused word `Tcb.depth` (64).
They are `Scc.IR.Tcb.allocBlk` (72), `rseqDesc` (80), `ckpt` (88) and `kabi` (96), and a spawned
thread's argument words start after them, at `Tcb.size` (104), on both hosts, so that Linux and
raw share one TCB layout.

* `allocBlk`: the address of the two-word allocation block the inline restartable sequence uses
  (Linux: the thread's own buffer; raw: the current core's block, refreshed by the scheduler).
  Nothing reads or writes it yet.
* `rseqDesc`: the armed restart descriptor (`Scc.Cert.Maps.Rseq`), 0 when none is armed.
  Nothing reads or writes it yet.
* `ckpt`: the checkpoint state (the thread's expected mark state and a pending flag). Nothing
  reads or writes it yet.
* `kabi`: `--host raw`, the address of the kernel routine table, which the kernel writes before
  the thread's first instruction; 0 and never read under `--host linux`.

The thread never stores to these words; the platform does.

**x64 only: the FPU/vector save area** (`fpuSave`), the TCB's last field, so that its size can
vary: an `FXSAVE` record (`fpuSaveMin` = 512 bytes, 16-byte aligned) or an `XSAVE`-family record
(size from `CPUID`, 64-byte aligned). It starts at the first 64-aligned offset at or after
`sizeNext`, and a TCB with an `XSAVE` record of `n` bytes takes `sizeNextFpu n` bytes. The offsets
are relative to the TCB's base, so the area is 64-aligned only if the base is: today a TCB base is
only 8-aligned (the pinned allocator, `Runtime.allocF` with `counter := false`, bumps by multiples
of 8 bytes from the 16-aligned `scc_rt_pinned`, and the first TCB is at `scc_rt_pinned + 8`), so a
64-aligned TCB base is a runtime change of a later round. AArch64 does not use the
area. Nothing reserves it yet: the argument words follow `sizeNext` today.
-/
namespace Scc.Cert.Maps.TcbReserved

open Scc.IR

/-- The allocation block pointer. -/
def allocBlk : Nat := Tcb.allocBlk
/-- The armed restart descriptor (0: none). -/
def rseqDesc : Nat := Tcb.rseqDesc
/-- The checkpoint state. -/
def ckpt : Nat := Tcb.ckpt
/-- The kernel routine table (`--host raw`). -/
def kabi : Nat := Tcb.kabi
/-- The reserved words, in order. -/
def words : List Nat := [allocBlk, rseqDesc, ckpt, kabi]
/-- The end of the reserved words: where a spawned thread's argument words start (`Tcb.size`). -/
def sizeNext : Nat := Tcb.size

/-- Today's TCB fields (`Scc.IR.Tcb`). -/
def current : List Nat :=
  [Tcb.self, Tcb.stackLimit, Tcb.permit, Tcb.exited, Tcb.stackBase, Tcb.stackTop, Tcb.badMask,
    Tcb.index, Tcb.depth]

/-- `n` rounded up to a multiple of 64. -/
def roundUp64 (n : Nat) : Nat := (n + 63) / 64 * 64

/-- x64: the offset of the FPU/vector save area, the TCB's last field: the first 64-aligned
offset at or after `sizeNext`. -/
def fpuSave : Nat := roundUp64 sizeNext
/-- x64: the smallest save area, an `FXSAVE` record. -/
def fpuSaveMin : Nat := 512
/-- x64: the TCB size with a save area of `xsaveSize` bytes (rounded up to 64). -/
def sizeNextFpu (xsaveSize : Nat) : Nat := fpuSave + roundUp64 xsaveSize

/-- **The reservation is well formed**: the reserved words are 8-aligned, pairwise distinct,
disjoint from every current field (in particular not word 64, `Tcb.depth`), past every current
field, contiguous up to `sizeNext` (`Tcb.size`, where the argument words start), and `sizeNext`
keeps 8-byte alignment; the x64 save area is 64-aligned,
starts at or after `sizeNext` (so after every reserved word and current field), and with the
minimum (`FXSAVE`) record ends 64-aligned. -/
theorem reserved_ok :
    words.all (· % 8 = 0) ∧ words.Nodup ∧ words.all (fun w => !current.contains w) ∧
    words.all (fun w => current.all (· + 8 ≤ w) ∧ w + 8 ≤ sizeNext) ∧ Tcb.depth ∉ words ∧
    8 * words.length + Tcb.allocBlk = sizeNext ∧ sizeNext % 8 = 0 ∧
    fpuSave % 64 = 0 ∧ sizeNext ≤ fpuSave ∧ words.all (fun w => w + 8 ≤ fpuSave) ∧
    current.all (fun w => w + 8 ≤ fpuSave) ∧
    fpuSave + fpuSaveMin ≤ sizeNextFpu fpuSaveMin ∧ sizeNextFpu fpuSaveMin % 64 = 0 := by
  decide

/-- **Any save area size fits**: the TCB with an `xsaveSize`-byte record holds the record from
`fpuSave` and ends 64-aligned. -/
theorem sizeNextFpu_ok (xsaveSize : Nat) :
    fpuSave + xsaveSize ≤ sizeNextFpu xsaveSize ∧ sizeNextFpu xsaveSize % 64 = 0 := by
  have h : fpuSave = 128 := by decide
  simp only [sizeNextFpu, roundUp64, h]
  omega

/-- info: (72, 80, 88, 96, 104, 128, 640) -/
#guard_msgs in
#eval (allocBlk, rseqDesc, ckpt, kabi, sizeNext, fpuSave, sizeNextFpu fpuSaveMin)

/-- info: 'Scc.Cert.Maps.TcbReserved.reserved_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reserved_ok

/-- info: 'Scc.Cert.Maps.TcbReserved.sizeNextFpu_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sizeNextFpu_ok

end Scc.Cert.Maps.TcbReserved
