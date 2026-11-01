/-
**hello's root base at a linked layout** (AArch64; row RootBase-inhabit): the scaffolding that, given the linked
executable's layout facts, builds the root's bundles `HelloRootBase` and `HelloRootPrem` with exactly the choices
`RootInv.hello_root_inv` makes, and the root's table facts. The instance at the executable's layout `Λe` (row
hello-elf: `Spike/Test/HelloLinkedA64*.lean`) is one line per bundle: `LayoutE` from the decided facts, then
`baseE`/`premE`.

The table is the certificate's, `i0 := ImmsMe.i0M Λ0` (so the root's immediates are `ImmsMe.iRdM Λ0`, row
root-imms), and the output and configuration are the listing's `RootLit.oH`, `pcfgH`.

- `LayoutE Λ0`: the linked executable's facts, the ones the root's bundles need: `PlaceW pcfgH Λ0 oH`, `hlo`
  (`.text` at `WakePh.lo`), `hstat`, `hnz`, A13's data part at the placed layout, and `hinit2` (the second TCB's limit
  word starts at `0`).
- `LayoutE.hpin2`: the first TCB in the pinned region (`ChildRoot.hpin2_H` at `RootLit.hz_H`).
- `LayoutE.hm`, `hRdI`, `hme`, `hzI`: the root's table facts (`ImmsMe.hm_iRdM`, `rdImms_iRdM`, `hmeC_iRdM`,
  `HabCtlA.hz_i0M`).
- `LayoutE.restE`, `baseE`, `premE`: `RootPlug.RootRest` at `hello_root_inv`'s choices (`Dt := DtW`,
  `Ctx := LandRU.CtxRdU`, `frM := frH c0S.env`, `F0 := RootInv.F0H`, `msB := RootOkb.msBH`), the base
  `RootRest.toBase` from it, and the premises `HelloRootBase.toPrem`, from the listing's parse `hparse` alone.
- The final `example`: `RootLit.hello_root_lit` at `LayoutE`, with every layout and table premise discharged;
  what remains are the per-entry premises and the root's open rows.
-/
import Spike.Lib.A64HelloRootLit
import Spike.Lib.A64HelloHabCtlA

namespace Spike.Lib.A64.HelloPh.RootBaseInh

open Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib (PlaceW)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.HelloPh.RootLit (pcfgH oH)
open Spike.Lib.A64.HelloPh.ImmsMe (i0M iRdM)
open Spike.Lib.WakeLoadT (L0T)
open Scc.Cert.Link.A64 (parsesTo parsed_of_parsesTo)

/-- **The linked executable's facts** at the layout `Λ0`, the ones the root's bundles need (row hello-elf decides
each at `Λe`). -/
structure LayoutE (Λ0 : Scc.Sem.Layout) : Prop where
  /-- `PlaceW` (A1, A2, A4, A6, A8). -/
  hp : PlaceW pcfgH Λ0 oH
  /-- `.text` at hello's phase base. -/
  hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo
  /-- No static words. -/
  hstat : Λ0.static = fun _ => none
  /-- `scc_rt_nthreads` starts at `0`. -/
  hnz : Spike.Lib.WakeOInit.NtZ Λ0 oH = true
  /-- A13's data part at the placed layout. -/
  hA13 : Scc.Cert.Spawn.A64.a13data (RuntimeLayout.ofPlaceW hp (iRdM Λ0)).Λ oH.prog oH.secs = true
  /-- The second TCB's limit word starts at `0` (`HelloRootCP.hCP_root`'s `hinit2`; not a `PlaceW` fact: A8's
  `rtInitOk` covers the first TCB's words only, and the load's image is the layout's). -/
  hinit2 : (Spike.Lib.A64.PhRec.m0Of (RuntimeLayout.ofPlaceW hp (iRdM Λ0)).Λ oH.prog oH.secs).initVal
    ⟨Spike.Lib.HelloGOf2H.lim2AH (RuntimeLayout.ofPlaceW hp (iRdM Λ0)), 8⟩ = 0

namespace LayoutE

variable {Λ0 : Scc.Sem.Layout} (F : LayoutE Λ0)

set_option hygiene false in
/-- The placed layout at the root's table. -/
local notation "Ly" => RuntimeLayout.ofPlaceW F.hp (iRdM Λ0)

set_option hygiene false in
local notation "AW" => Spike.Lib.WakeOD.arW F.hp (iRdM Λ0)

set_option hygiene false in
local notation "MS2" => Spike.Lib.A64.HelloPh.H2Rt.ms2H (asm := SccCode.helloAsm) F.hp (iRdM Λ0) E

/-- **The first TCB in the pinned region** (`hpin2`): `ChildRoot.hpin2_H` at the listing's `.zero`. -/
theorem hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size :=
  Spike.Lib.A64.HelloPh.ChildRoot.hpin2_H F.hp (iRdM Λ0) RootLit.hz_H (by decide)

/-- **`hm`** at the root's table. -/
theorem hm : (Ly).Λ.imms Spike.Lib.HelloRodataSrc.eB "m" 0 = some 2 :=
  ImmsMe.hm_iRdM F.hp

/-- **`hRdI`** at the root's table. -/
theorem hRdI : Spike.Lib.A64.HelloPh.RdPlS.RdImms (Ly).Λ :=
  have h := ImmsMe.rdImms_iRdM F.hp
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- **`hme`** at the root's table. -/
theorem hme : (Ly).Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some (Spike.Lib.WakeLoadT.tcb0 (Ly).Λ) :=
  ImmsMe.hmeC_iRdM F.hp

/-- **`hzI`** at the root's table. -/
theorem hzI : i0M Λ0 Spike.Lib.HelloMainPreSrc.newTerm "z" 0 = some 0 :=
  HabCtlA.hz_i0M Λ0

/-- **The base's rest at `hello_root_inv`'s choices** (its `let R`). -/
noncomputable def restE (E : Scc.Sem.Entry) (ls : Spike.Lib.A64Consumer.Lsize) :
    RootPlug.RootRest (Ly) (L0T (Ly).Λ) (AW) (MS2) where
  W1 := fun _ _ _ => True
  Dt := Spike.Lib.A64.WakeWf.DtW
  Ctx := Spike.Lib.A64.HelloPh.LandRU.CtxRdU (asm := SccCode.helloAsm) F.hp (i0M Λ0) E (fun _ => True) ls
  ls := ls
  frM := Spike.Lib.HelloRdCf.frH Spike.Lib.A64.HelloPh.C0S.c0S.env
  msB := RootOkb.msBH (asm := SccCode.helloAsm) F.hp (i0M Λ0) E ls
  F0 := RootInv.F0H F.hp (i0M Λ0)
  hokb := RootOkb.hokb_H (asm := SccCode.helloAsm) F.hp (i0M Λ0) E ls RootLit.hc_H
  hg := RootOkb.hg_H (asm := SccCode.helloAsm) F.hp (i0M Λ0) E ls

/-- **The root's base** at the linked layout, from the listing's parse (`RootRest.toBase` of `restE`). -/
noncomputable def baseE (hparse : parsesTo SccCode.helloAsm SccCode.helloProg SccCode.helloSecs = true)
    (E : Scc.Sem.Entry) (ls : Spike.Lib.A64Consumer.Lsize) :
    HelloRootBase (Ly) (L0T (Ly).Λ) (AW) (MS2) :=
  (F.restE E ls).toBase F.hp (i0M Λ0) E (parsed_of_parsesTo hparse).1 (parsed_of_parsesTo hparse).1 F.hlo F.hA13
    RootLit.hc_H

/-- **The root's premises** at the linked layout (`HelloRootBase.toPrem` of `baseE`). -/
noncomputable def premE (hparse : parsesTo SccCode.helloAsm SccCode.helloProg SccCode.helloSecs = true)
    (E : Scc.Sem.Entry) (ls : Spike.Lib.A64Consumer.Lsize) : HelloRootPrem (Ly) (L0T (Ly).Λ) :=
  (F.baseE hparse E ls).toPrem F.hp (i0M Λ0) E F.hA13 F.hpin2 F.hstat

/-- `premE`'s third level is the root's `W2I` at `DtW` and `CtxRdU` (by `rfl`). -/
example (hparse : parsesTo SccCode.helloAsm SccCode.helloProg SccCode.helloSecs = true)
    (E : Scc.Sem.Entry) (ls : Spike.Lib.A64Consumer.Lsize) :
    (F.premE hparse E ls).W2 = Spike.Lib.A64.HelloPh.W2I (Ly) (AW) Spike.Lib.A64.WakeWf.DtW
      (Spike.Lib.A64.HelloPh.LandRU.CtxRdU (asm := SccCode.helloAsm) F.hp (i0M Λ0) E (fun _ => True) ls)
      (L0T (Ly).Λ) (Spike.Lib.WakeLoadT.ls0T ls) := rfl

/-- **`hello_root_lit` at the linked layout**: the layout facts (`hlo`, `hstat`, `hnz`, `hA13`) and the table's
(`hm`, `hRdI`, `hme`, `hzI`) discharged; the rest are the per-entry premises (`hB`, `hE`) and the root's open
rows. -/
example {arch : WeakMem.Arch} {B : Scc.Sem.Budget} {E : Scc.Sem.Entry} {ls : Spike.Lib.A64Consumer.Lsize}
    (hparse : parsesTo SccCode.helloAsm SccCode.helloProg SccCode.helloSecs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells) (hE : E.Ok (Ly).Λ) :=
  RootLit.hello_root_lit (arch := arch) (ls := ls) F.hp (i0M Λ0) hparse F.hlo F.hstat F.hnz hB hE F.hA13 F.hm
    (hRdI := F.hRdI) (hme := F.hme) (hzI := hzI (Λ0 := Λ0))

end LayoutE

end Spike.Lib.A64.HelloPh.RootBaseInh

/-- info: 'Spike.Lib.A64.HelloPh.RootBaseInh.LayoutE.hpin2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootBaseInh.LayoutE.hpin2

/-- info: 'Spike.Lib.A64.HelloPh.RootBaseInh.LayoutE.hRdI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootBaseInh.LayoutE.hRdI

/-- info: 'Spike.Lib.A64.HelloPh.RootBaseInh.LayoutE.premE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootBaseInh.LayoutE.premE
