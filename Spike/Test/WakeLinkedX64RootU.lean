import Spike.Test.WakeLinkedX64Br
import Spike.Lib.X64WakeFinalCAO
import Spike.Lib.X64WakeRootO
import Spike.Lib.X64WakeC0

/-!
# `wake.w` on x86-64 at `Λe`: the root's assembly

`wake_linkedXU` is the body of `WakeLinkedXGoal ie` (`CorrectE 2` of the
neutral source semantics `wakeSX` at `{ Λe with imms := ie }`), from
`X64WakeRootO.wake_finalX_LUO` at `hp := placeWX_e`, `i := ie`
(`= X64.WakeImms.iW Λe`, `ie_eq`), `c0 := X64.WakeC0.c0W`. Its instance facts
are discharged at `Λe`:

- `hstat`, `hA13_e`, `hpin2` (`WakeLinkedX64Le`), `hinit2_W`, `hsub1_W`,
  `hnz_W` (`WakeLinkedX64Br`, the local forms by `rfl`);
- `hc` by `X64WakeFinalCAO.ctrZ_cert`;
- the goal's layout and source by `Le_Λ`, `wakeS_eq`.

Still premises: `hlo : Λe.code.lo = WakePh.lo` (both the linked `.text` base
`0x401000`, so `WakeLinkedX64.hlo` closes it; kept here so the assembly is
independent of the decision) and the three per-entry rows `hland`, `hland1`,
`hst` at `c0W`.

Unlike AArch64 (`Spike/Test/WakeLinkedA64Root.lean`, `wake_linkedU`), the
statement is at the certificate's `prog_src` and `Scc.Sem.SrcSem.srcPo`
(`wakeSX`) rather than the root's local `wakeSrc`/`srcPo`, and its layout is
written `{ Λe with imms := ie }` rather than `Le.Λ`; both are bridged by `rfl`
(`WakeLinkedX64Br`).
-/

namespace Spike.Test.WakeLinkedX64RootU

open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib
open Spike.Test.WakeLinkedX64 Spike.Test.WakeLinkedX64Br
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib.X64WakeParse (certAsm)
open Spike.Lib.X64WakeFinal (inv0G)
open Spike.Lib.X64.WakePh.RootUL (CtxRU HLandU HLand1U)
open Spike.Lib.X64.WakeH1Inv (inv1W)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64.WakeC0 (c0W)
open SccCertificate (asm sizes labelOffs outLit)

local notation "cTR" => fun _ : Entry => Spike.Lib.X64WakeHG.cTW placeWX_e ie

/-- **wake.w's x86-64 statement at `Λe`**, from the loader check `hP`, the
budget `hB`, the code base `hlo` and the three per-entry rows (see the module
doc). -/
theorem wake_linkedXU {arch : WeakMem.Arch} {B : Budget} (ls0 : Entry → Lsize) (frM : Entry → TermRun.Frame)
    /- the loader's check (the trust boundary; `#guard`-checked in `WakeLinkedX64`) -/
    (hP : Scc.Cert.Link.X64.parsesTo ⟨asm, sizes, labelOffs⟩ outLit.prog outLit.secs = true)
    /- the budget: the caller's choice -/
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    /- the code base (`WakeLinkedX64.hlo`, decided) -/
    (hlo : Λe.code.lo = Spike.Lib.X64.WakePh.lo)
    /- OPEN: the counter add's tail, per entry -/
    (hland : ∀ E : Entry, E.Ok Le.Λ →
      HLandU placeWX_e ie c0W ls0 (inv0G placeWX_e ie cTR ls0 (CtxRU placeWX_e ie c0W ls0) frM E) E)
    /- OPEN: the box store's landing, per entry -/
    (hland1 : ∀ E : Entry, E.Ok Le.Λ →
      HLand1U placeWX_e ie c0W ls0 (inv0G placeWX_e ie cTR ls0 (CtxRU placeWX_e ie c0W ls0) frM E)
        (inv1W certAsm placeWX_e ie E (Spike.Lib.X64WakeHG.cTW placeWX_e ie) DtW
          (CtxRU placeWX_e ie c0W ls0 E) (ls0 E)) E)
    /- OPEN: the start in `inv0G`, per entry -/
    (hst : ∀ E : Entry, E.Ok Le.Λ →
      inv0G placeWX_e ie cTR ls0 (CtxRU placeWX_e ie c0W ls0) frM E
        (threadAt E Le.Λ.code.lo outLit.prog (loadSyms Le.Λ outLit.secs.rodata))
        ⟨Spike.Lib.X64WakePreAsm.wakeTh0.term, Spike.Lib.X64WakePreAsm.wakeTh0.env, none⟩
        Spike.Lib.X64WakePreAsm.wakeTh0.stack) :
    Scc.Sem.X64.CorrectE 2 (wakeSX arch) { Λe with imms := ie } B ⟨asm, sizes, labelOffs⟩ := by
  rw [← wakeS_eq, ← Le_Λ]
  exact Spike.Lib.X64WakeRootO.wake_finalX_LUO placeWX_e ie ls0 frM c0W hP hB hlo hstat hA13_e hpin2 hinit2_W
    hsub1_W X64WakeFinalCAO.ctrZ_cert hnz_W hland hland1 hst

end Spike.Test.WakeLinkedX64RootU

/-- info: 'Spike.Test.WakeLinkedX64RootU.wake_linkedXU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.WakeLinkedX64RootU.wake_linkedXU
