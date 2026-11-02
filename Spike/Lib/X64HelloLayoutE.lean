/-
**hello's linked-layout facts on x86-64** (the twin of `A64.HelloPh.RootBaseInh.LayoutE`): the facts of a
linked executable's layout `Λ0` that hello's x86-64 root reads, bundled so that the root is stated once at
any `Λ0` and instantiated at a concrete layout by deciding each field (`Spike/Test/HelloLinkedX64L1.lean` at
`Λ1`; `Spike/Test/HelloLinkedX64Le.lean`'s `layoutEX_e` at the checked-in executable's layout `Λe`, `hlo` included).

The placed layout is `ofPlaceWX hp (X64.HelloImms.iRdM Λ0)`, the root's table (`Spike/Lib/X64HelloImms.lean`),
and the output and configuration are the listing's `RootLit.oH`, `pcfgH`.

Unlike AArch64:
- `hp` is `PlaceWX` (every component of `placeOK2At`), not AArch64's `PlaceW` subset (A1, A2, A4, A6, A8);
- `hpin2` and `hsub1` are fields, decided at the concrete layout as x86-64 wake does
  (`WakeLinkedX64Le.hpin2`, `hsub1`); AArch64 derives `hpin2` from the listing's `.zero` and has no `hsub1`;
- `hnz` is x86-64's `X64WakeOInit.NtZ` and `hinit2` reads `X64HelloGOf2H.lim2AH` (`pinA + 120`, hello's second
  TCB's limit word, as `HelloRootCP.hCP_root` asks; wake's is `pinA + 112`).

- `LayoutEX Λ0`: the facts.
- `LayoutEX.hwide`: the executable is in the wide fragment (from `hp`'s A4).
- `LayoutEX.hme`, `hmeC`, `hm`, `hRd`: the root's table facts (`X64.HelloImms.hme_iRdM`, `hmeC_iRdM`,
  `hm_iRdM`, `rdImms_iRdM`).
-/
import Spike.Lib.X64HelloImms
import Spike.Lib.X64HelloOut
import Spike.Lib.X64HelloPh
import Spike.Lib.X64WakeOInit
import Spike.Lib.X64HelloGOf2H
import Spike.Lib.Rt.X64RtPreChild

namespace Spike.Lib.X64.HelloPh.RootBaseInh

open Spike.Lib (PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.HelloPh.RootLit (pcfgH oH)
open Spike.Lib.X64.HelloImms (iRdM)
open Spike.Lib.X64HelloRodataSrc (eB eW0 eO0 eW1 eO1 eS eN eRet)
open Spike.Lib.Hello1RodataSrc (rdK1 rdK2)

/-- **The linked executable's facts** at the layout `Λ0`, the ones hello's x86-64 root reads (each decided at
a concrete layout). -/
structure LayoutEX (Λ0 : Scc.Sem.Layout) : Prop where
  /-- `PlaceWX` (every component of `placeOK2At`). -/
  hp : PlaceWX pcfgH Λ0 oH
  /-- `.text` at hello's phase base. -/
  hlo : Λ0.code.lo = Spike.Lib.X64.HelloPh.lo
  /-- No static words. -/
  hstat : Λ0.static = fun _ => none
  /-- `scc_rt_nthreads` starts at `0`. -/
  hnz : Spike.Lib.X64WakeOInit.NtZ Λ0 oH = true
  /-- A13's data part at the placed layout. -/
  hA13 : Scc.Cert.Spawn.X64.a13data (RuntimeLayout.ofPlaceWX hp (iRdM Λ0)).Λ oH.prog oH.secs = true
  /-- The first TCB's 168 bytes fit the pinned region. -/
  hpin2 : (RuntimeLayout.ofPlaceWX hp (iRdM Λ0)).pinA.toNat + 168 ≤
    (RuntimeLayout.ofPlaceWX hp (iRdM Λ0)).Λ.pinned.lo + (RuntimeLayout.ofPlaceWX hp (iRdM Λ0)).Λ.pinned.size
  /-- The second TCB's limit word starts at `0` (not a `PlaceWX` fact: A8's `rtInitOk` covers the first TCB's
  words only). -/
  hinit2 : (Spike.Lib.X64.PhRec.m0Of (RuntimeLayout.ofPlaceWX hp (iRdM Λ0)).Λ oH.prog oH.secs).initVal
    ⟨Spike.Lib.X64HelloGOf2H.lim2AH (RuntimeLayout.ofPlaceWX hp (iRdM Λ0)), 8⟩ = 0
  /-- The child's stack range lies in the stack pool. -/
  hsub1 : (Spike.Lib.X64.Rt.PreChild.r1Of (RuntimeLayout.ofPlaceWX hp (iRdM Λ0)).lab).Sub
    (RuntimeLayout.ofPlaceWX hp (iRdM Λ0)).Λ.stackPool

namespace LayoutEX

variable {Λ0 : Scc.Sem.Layout} (F : LayoutEX Λ0)

set_option hygiene false in
/-- The placed layout at the root's table. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX F.hp (iRdM Λ0)

/-- **The executable is in the wide fragment** (A4, `wideSt_threadAt`). -/
theorem hwide : Scc.Cert.WideX64.ExeWide (Ly).exe :=
  (Scc.Cert.WideX64.wideSt_threadAt (PlaceWX.wideIn_of_placeWX F.hp) Scc.Sem.Entry.linux _ _).2

/-- **`me` at `tcb0` at the setup start** at the root's table. -/
theorem hme : (Ly).Λ.imms Scc.Sem.SrcSem.setupTerm "me" 0 = some (Spike.Lib.X64WakeLoadT.tcb0 (Ly).Λ) :=
  Spike.Lib.X64.HelloImms.hme_iRdM F.hp

/-- **`me` at `tcb0` at the setup continuation** at the root's table. -/
theorem hmeC : (Ly).Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some (Spike.Lib.X64WakeLoadT.tcb0 (Ly).Λ) :=
  Spike.Lib.X64.HelloImms.hmeC_iRdM F.hp

/-- **rodata's `m` at `eB`** at the root's table. -/
theorem hm : (Ly).Λ.imms eB "m" 0 = some 2 :=
  Spike.Lib.X64.HelloImms.hm_iRdM F.hp

/-- **rodata's immediates** at the root's table (`m`, `w0`, `w1`, `sl1`, `sl2`). -/
theorem hRd :
    (∀ e ∈ [eW0, eO0, eW1, eO1, eS, eN], (Ly).Λ.imms e "m" 0 = some 2) ∧
      (Ly).Λ.imms eO0 "w0" 0 = some rdK1 ∧ (Ly).Λ.imms eO1 "w1" 0 = some rdK2 ∧
      (Ly).Λ.imms eRet "sl" 1 = some 2 ∧ (Ly).Λ.imms eRet "sl" 2 = some 13 :=
  Spike.Lib.X64.HelloImms.rdImms_iRdM F.hp

end LayoutEX

end Spike.Lib.X64.HelloPh.RootBaseInh

/--
info: 'Spike.Lib.X64.HelloPh.RootBaseInh.LayoutEX.hwide' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootBaseInh.LayoutEX.hwide

/-- info: 'Spike.Lib.X64.HelloPh.RootBaseInh.LayoutEX.hRd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootBaseInh.LayoutEX.hRd
