/-
**hello.w on x86-64: the byte step at `print`'s loop** (the twin of
`Spike.Lib.HelloEmitEx`, live part). The memory side `helloMsW` puts
`bo := ByteOutP helloSrc lbl`. The byte step of an `Out.emit` row is a
theorem at `print`'s published loop, not a premise.

- `byteOutP_printCP`: from the loop invariant `PrintCP … k` below `printN n
  m`, byte `b + k` of the buffer placed at `b` is a `ByteOutP` step into
  `PrintCP … (k + 1)` (`printCP_load`, `ByteOutP.load`, `ByteOutP.closed`,
  `printCP_next`).

**Where this differs from AArch64** (forced by the x86-64 shape):
- The program is `X64HelloSrc.helloSrc`, and the loop's lemmas are
  `X64HelloPrintSrcPub`'s. The statement and proof are otherwise AArch64's.
- Only `byteOutP_printCP` is twinned. AArch64's `EmitLand`, `hbyteH`,
  `emitRowH`, `hsvc_emitH`, `printCP_ex`, `printN_hello`, `bufW_byte` and
  `loadCP_byte_hello` are dead in the hello proof (the non-vacuity example).
  `loadCP_byte_hello`'s source lemma `loadCP_byte_i` is not twinned on x86-64
  either (see `X64HelloPrintSrcPub`).
-/
import Spike.Lib.X64HelloByteOutP

namespace Spike.Lib.X64HelloEmitEx

open CoreLang CoreTerm TermRun
open Kraken.Promising
open Scc.Sem Scc.Sem.SrcSem Scc.Sem.SrcOutProto
open Spike.Lib
open Spike.Lib.PrintSrc (printN)
open Spike.Lib.X64HelloPrintSrcPub (PrintCP elemW printCP_load printCP_next printLPD_find)
open Spike.Lib.X64HelloByteOutP (ByteOutP)

/-! ## The byte step at `print`'s loop -/

/-- **The byte step from the loop invariant**: below `printN n m`, from
`PrintCP … k`, byte `b + k` of the buffer at `b` is a `ByteOutP` step into
`PrintCP … (k + 1)`. -/
theorem byteOutP_printCP {I : ISA} {lbl : WeakMem.AllocLabel → Option Nat} {s : I.State} {pw wn : Word}
    {l : WeakMem.AllocLabel} {b n m k : Nat} {c1 : Ctl} (hpw : pw.val = .loc ⟨l, 0⟩ 0) (hl : lbl l = some b)
    (hwn : wn.val = .num n) (hk : k < printN n m) (h : PrintCP pw wn n m k c1) :
    ByteOutP X64HelloSrc.helloSrc lbl s (b + k) c1 (PrintCP pw wn n m (k + 1)) := by
  refine ByteOutP.closed (printCP_load printLPD_find h hk).toLocalRun (ByteOutP.load hpw hl) ?_
  rintro _ ⟨mw, v, rfl⟩
  obtain ⟨c2, r, h2⟩ := printCP_next (lw := elemW pw l (k / 8)) (mw := mw) (b := v) printLPD_find hwn hk
  exact ⟨c2, r.toLocalRun, h2⟩

end Spike.Lib.X64HelloEmitEx

/-- info: 'Spike.Lib.X64HelloEmitEx.byteOutP_printCP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloEmitEx.byteOutP_printCP
