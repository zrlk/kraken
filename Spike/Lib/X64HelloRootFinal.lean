/-
**hello.w on x86-64: the root's obligations at a linked layout** (the twin of `Spike/Lib/A64HelloRootFinal.lean`):
`RootLit.hello_root_litM` at the linked executable's facts `RootBaseInh.LayoutEX Λ0`. Every premise below the
loader's trust boundary is discharged; what remains is exactly the boundary:

- `F : LayoutEX Λ0`: the linked layout's facts (`PlaceWX`, `.text` at `X64.HelloPh.lo`, no static words,
  `scc_rt_nthreads` at `0`, A13's data part, the first TCB in the pinned region, the second limit word's initial
  value, the child's stack in the pool), decided at the executable's layout `Λe`
  (`Spike/Test/HelloLinkedX64Le.lean`, `layoutEX_e`);
- `hparse`: the listing's parse (`#guard`-checked in `X64HelloCode`);
- `hB`: the budget's cells; `hE`: the entry admissible at the placed layout.

The table is the root's (`i0 := X64.HelloImms.i0M Λ0`, `iRdM Λ0 = immsH Λ0 (i0M Λ0)`), the worker side the
DH := helloDRF switch's (`X64HelloWorkerDHF`); the relation is `RootLit.QRoot` there.

- `hello_root_final`: the root's `WakeObligationsR` at every admissible entry `E` (`hE`).
- `hello_correct`: `CorrectE 2 (helloS arch)` at the placed layout (`X64WakeA64.hello_correctE_RQ`); the statement
  `Spike/Test/HelloLinkedX64Root.lean` instantiates at `Λe`.

**Where this differs from AArch64** (forced by the x86-64 shape):
- The layout facts are `LayoutEX` (`PlaceWX`, all of `placeOK2At`'s components, with `hpin2` and `hsub1` as
  fields), not `LayoutE` (`PlaceW`, A1/A2/A4/A6/A8); the layout is `RuntimeLayout.ofPlaceWX`.
- The parse is `Scc.Cert.Link.X64.parsesTo helloAsm helloCells helloSecs` (an `Asm` and code cells).
- `ImmsKid` at the root's layout is the pair `⟨kid_root F.hp, wcall_root F.hp⟩` (`X64HelloImmsKid`; AArch64:
  `ImmsMe.immsKid_root`).
- The immediates are `X64.HelloImms`'s `iRdM`/`i0M` (AArch64: `ImmsMe`'s).
-/
import Spike.Lib.X64HelloRootLit
import Spike.Lib.X64HelloLayoutE
import Spike.Lib.X64HelloCorrectEQ

namespace Spike.Lib.X64.HelloPh.RootFinal

open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.HelloPh.RootBaseInh (LayoutEX)
open Spike.Lib.X64.HelloImms (iRdM i0M)
open Spike.Lib.X64WakeA64 (WakeObligationsR)
open Scc.Cert.Link.X64 (parsesTo)
open Spike.Lib.X64WakePreTi (TiPre)
open Spike.Lib.X64HelloOAb (AbH AcH)
open Spike.Lib.X64HelloPostAb (TwH)
open Spike.Lib.X64HelloSrc (helloSrc helloS)

/-- **The root's obligations at a linked layout** (module doc): `hello_root_litM` at `F`'s facts; the premises are
the boundary `F`, `hparse`, `hB`, `hE`. -/
theorem hello_root_final {Λ0 : Scc.Sem.Layout} (F : LayoutEX Λ0) {arch : WeakMem.Arch} {B : Scc.Sem.Budget}
    {E : Scc.Sem.Entry} {ls : Spike.Lib.X64Consumer.Lsize}
    (hparse : parsesTo SccCode.helloAsm SccCode.helloCells SccCode.helloSecs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells) (hE : E.Ok (RuntimeLayout.ofPlaceWX F.hp (iRdM Λ0)).Λ) :
    WakeObligationsR arch (RuntimeLayout.ofPlaceWX F.hp (iRdM Λ0)).Λ B SccCode.helloAsm
      (RootLit.QRoot (arch := arch) (E := E) (ls := ls) F.hp (i0M Λ0) hparse F.hlo
        ⟨Spike.Lib.X64.HelloImms.kid_root F.hp, Spike.Lib.X64.HelloImms.wcall_root F.hp⟩) E
      (fun t tr => TiPre (AbH F.hp (iRdM Λ0)) (AcH F.hp (iRdM Λ0)) t tr ∧
        TwH (RuntimeLayout.ofPlaceWX F.hp (iRdM Λ0)).Λ E (AbH F.hp (iRdM Λ0)) t tr)
      helloSrc :=
  RootLit.hello_root_litM F.hp hparse F.hlo F.hstat F.hnz hB hE F.hA13 F.hinit2

/-- **hello.w is correct at a linked layout** (`CorrectE 2` at `helloS`): `hello_root_final` at every admissible
entry (`X64WakeA64.hello_correctE_RQ`). The premises are the boundary: the linked layout's facts `F`, the
listing's parse `hparse` and the budget's `hB`. -/
theorem hello_correct {Λ0 : Scc.Sem.Layout} (F : LayoutEX Λ0) {arch : WeakMem.Arch} {B : Scc.Sem.Budget}
    (hparse : parsesTo SccCode.helloAsm SccCode.helloCells SccCode.helloSecs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells) :
    Scc.Sem.X64.CorrectE 2 (helloS arch) (RuntimeLayout.ofPlaceWX F.hp (iRdM Λ0)).Λ B SccCode.helloAsm :=
  -- the conclusion is independent of level 0's label sizes `ls`; any choice serves
  Spike.Lib.X64WakeA64.hello_correctE_RQ _ _ fun _ hE => hello_root_final F (ls := fun _ => 0) hparse hB hE

end Spike.Lib.X64.HelloPh.RootFinal

/-- info: 'Spike.Lib.X64.HelloPh.RootFinal.hello_root_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootFinal.hello_root_final

/-- info: 'Spike.Lib.X64.HelloPh.RootFinal.hello_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootFinal.hello_correct
