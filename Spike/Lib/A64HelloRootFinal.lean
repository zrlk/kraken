/-
**hello.w on AArch64: the root's obligations at a linked layout** (row hello-root-final): `RootLit.hello_root_litM`
at the linked executable's facts `RootBaseInh.LayoutE Λ0`. Every premise below the loader's trust boundary is
discharged; what remains is exactly the boundary:

- `F : LayoutE Λ0`: the linked layout's facts (`PlaceW`, `.text` at `lo`, no static words, `scc_rt_nthreads` at `0`,
  A13's data part, the second limit word's initial value), decided at the executable's layout `Λe` (row hello-elf);
- `hparse`: the listing's parse (`#guard`-checked in `A64HelloCode`);
- `hB`: the budget's cells; `hE`: the entry admissible at the placed layout.

The table is the certificate's (`i0 := ImmsMe.i0M Λ0`), the worker side the DH := helloDRF switch's
(`HelloWorkerDHF`); the relation is `RootLit.QRoot` there.

- `hello_root_final`: the root's `WakeObligationsR` at every admissible entry `E` (`hE`).
- `hello_correct`: `CorrectE 2 (helloS arch)` at the placed layout (`HelloCorrectEQ.hello_correctE_RQ`); the
  statement the hello cut instantiates at `Λe`.
-/
import Spike.Lib.A64HelloRootBaseInh
import Spike.Lib.HelloCorrectEQ

namespace Spike.Lib.A64.HelloPh.RootFinal

open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.HelloPh.RootBaseInh (LayoutE)
open Spike.Lib.A64.HelloPh.ImmsMe (iRdM i0M)
open Spike.Lib.WakePreTi (TiPre)
open Spike.Lib.WakeA64 (WakeObligationsR)
open Spike.Lib.HelloOAb (AbH AcH)
open Spike.Lib.HelloPostAb (TwH)
open Spike.Lib.HelloSrc (helloSrc helloS)
open Scc.Cert.Link.A64 (parsesTo)

/-- **The root's obligations at a linked layout** (module doc): `hello_root_litM` at `F`'s facts; the premises are
the boundary `F`, `hparse`, `hB`, `hE`. -/
theorem hello_root_final {Λ0 : Scc.Sem.Layout} (F : LayoutE Λ0) {arch : WeakMem.Arch} {B : Scc.Sem.Budget}
    {E : Scc.Sem.Entry} {ls : Spike.Lib.A64Consumer.Lsize}
    (hparse : parsesTo SccCode.helloAsm SccCode.helloProg SccCode.helloSecs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells) (hE : E.Ok (RuntimeLayout.ofPlaceW F.hp (iRdM Λ0)).Λ) :
    WakeObligationsR arch (RuntimeLayout.ofPlaceW F.hp (iRdM Λ0)).Λ B SccCode.helloAsm
      (RootLit.QRoot (arch := arch) (E := E) (ls := ls) F.hp (i0M Λ0) hparse F.hlo (ImmsMe.immsKid_root F.hp)) E
      (fun t tr => TiPre (AbH F.hp (iRdM Λ0)) (AcH F.hp (iRdM Λ0)) t tr ∧
        TwH (RuntimeLayout.ofPlaceW F.hp (iRdM Λ0)).Λ E (AbH F.hp (iRdM Λ0)) t tr)
      helloSrc :=
  RootLit.hello_root_litM F.hp hparse F.hlo F.hstat F.hnz hB hE F.hA13 F.hinit2

/-- **hello.w is correct at a linked layout** (`CorrectE 2` at `helloS`): `hello_root_final` at every admissible
entry (`HelloCorrectEQ.hello_correctE_RQ`). The premises are the boundary: the linked layout's facts `F`, the
listing's parse `hparse` and the budget's `hB`. -/
theorem hello_correct {Λ0 : Scc.Sem.Layout} (F : LayoutE Λ0) {arch : WeakMem.Arch} {B : Scc.Sem.Budget}
    (hparse : parsesTo SccCode.helloAsm SccCode.helloProg SccCode.helloSecs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells) :
    Scc.Sem.A64.CorrectE 2 (helloS arch) (RuntimeLayout.ofPlaceW F.hp (iRdM Λ0)).Λ B SccCode.helloAsm :=
  -- the conclusion is independent of level 0's label sizes `ls`; any choice serves
  Spike.Lib.WakeA64.hello_correctE_RQ _ _ fun _ hE => hello_root_final F (ls := fun _ => 0) hparse hB hE

end Spike.Lib.A64.HelloPh.RootFinal

/-- info: 'Spike.Lib.A64.HelloPh.RootFinal.hello_root_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootFinal.hello_root_final

/-- info: 'Spike.Lib.A64.HelloPh.RootFinal.hello_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootFinal.hello_correct
