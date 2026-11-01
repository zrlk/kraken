/-
**From `_start` to `wc_main`'s heap abort, at hello** (AArch64; the second half of
`A64HelloMainGlue`): `hello_start_rd_segW`'s segment to `wc_rodata`'s allocator's
return, the allocator's fresh-label landing at `wc_rodata`'s `.sp0`
(`HelloM.hello_main_hxa_of_post`), `wc_rodata` from `.sp0`, `bl wc_main` and
`wc_main` from its entry to its first allocation's heap abort
(`HelloM.hello_main_post_segW` with `HelloWc.hello_wc_entry_segJr` as its `hWc`).

- `MainWcP`: the premises past the layout's of that second part, for a caller's state
  `m0`, `σC` at `wc_rodata`'s call: `hello_main_post_segW`'s (`hW`, `hra` … `hedge`)
  and `hello_wc_entry_segJr`'s (`htp` … `hxa`), the allocator's words aside.
- `main_wc_segW`: from `.sp0` (`pN .s0`) to `wc_main`'s abort exit (`wXH .abort`, with
  `TP t`), in any valid layout of `helloProg`, at any level `W`.
- `hello_start_wc_segW`: the composed segment at the start's level `WSH`, from `_start`
  at `F ∧ P` to `wc_main`'s abort exit or `wc_rodata`'s heap abort. The allocators' words
  come from `WordsNone` (`Alloc.hmem_of_wordsNone`, `StartGlue.hmemB_of_wordsNone`).
-/
import Spike.Lib.A64HelloMainGlue
import Spike.Lib.A64HelloWcEntry

namespace Spike.Lib.A64.HelloPh.MainGlueW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Rt.A64 (Lays endOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout mainE0 swFSL)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.WakeWf (RunWf)
open Spike.Lib.A64.WakePh (WSep)
open Spike.Lib.A64.HelloPh.WcW (freeNH)
open Spike.Lib.A64.HelloPh.StartWf (WSH)
open Spike.Lib.A64.Flow (swR FStable NoMsrW rAddr tcbA enter leave Abs CKept)
open Spike.Lib.A64.Flow.Ret0 (pinA stacksA limA LimOk StOk entryN MainG)
open Spike.Lib.A64.WakePh.MainGlue (gS FS JS)
open Spike.Lib.A64.Flow.Hello1 (AG mR mF mRdJ0 mNC rpK1 rpK2 aR mWC)
open Spike.Lib.A64.Flow.HelloRd (rN rX pN)
open Spike.Lib.A64.Flow.HelloM (MainPostW wcR wcF wcJ0)
open Spike.Lib.A64.Flow.HelloWc (wXH bXH WcPreWH WcSp0WH)
open Spike.Lib.A64.Flow.WakeWc (AGB BoxW tpG)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.A64.Alloc (Call Ea)
open Spike.Lib.DmemPriv (WordsNone WordsNoneP WordIn)
/-- `Flow`'s abstract state (`AS` alone is ambiguous here). -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

open Spike.Lib (Arena FragS Frag MemSide Region SegW LocalRun XchgSite FenceRun)

/-! ## From `wc_rodata`'s `.sp0` to `wc_main`'s heap abort -/

/-- **`hello_main_post_segW`'s and `hello_wc_entry_segJr`'s premises** past the layout's, for a caller's state
`m0`, `σC` at `wc_rodata`'s call and `wc_main`'s region `D` deep at its call: the states inside `W` (`hW`, and
`hWp`, `hWs` at every caller's state `m1`, `σ1` at `wc_main`'s call), `wc_rodata`'s source and frame facts from
`.sp0` (`hra` … `hedge`, of exit invariant `Jr`), and `wc_main`'s entry's (`htp` … `hxa`, `Jr1` after the entry
block's local run). The allocator's words (`hmem0`) are left to the caller.

VACUOUS: `hedge` hands `Jr` states of any thread pointer and
`htp` pins it, so no `J5` state exists (witness `mainWcPS_J5_empty` for the old framed `MainWcPS`,
since deleted). Not used by the live hello root; the fixed form is
`MainGlueS.MainWcPS` at `HelloM.JrT` (`A64HelloMainPostT`). -/
structure MainWcP (W : Frag isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Region) (D : Int)
    (F : MachineData → Prop) (m0 : MachineData) (σC : FAS) (Jp Jp' J1 J2 J2' J3 J4 J5 Jr Jr1 : FAS → Ctl → Prop)
    (t : UInt64) : Prop where
  hW : MainPostW W K exe endPc R F m0 σC Jp Jp' J1 J2 J2' J3 J4 J5 Jr
  hra : ∀ σ0 c, Jp σ0 c → (_root_.Executable.labels exe).label ".L1_scc_rt_main.sp0" = Int64.ofBitVec (σ0.slot (-8))
  hmem : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
    ∀ m, mF R F m0 σC m → Mem.loadInt m.dmem (rAddr σ0.regs .X0 i) 8 = none
  hr0 : ∀ σ0 c, Jp σ0 c → ∃ c', LocalRun p c c' ∧ Jp' σ0 c'
  h1 : ∀ σ0 c, Jp' σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
    XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧ c.hold = none ∧
    ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
      J1 σ0 { c with hold := some ((rAddr σ0.regs .X0 0).toNat, w') }
  h2 : ∀ σ0 c, J1 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
    (wv wold : TermRun.Word),
    XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧
    c.hold = some ((rAddr σ0.regs .X0 0).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
    Scc.Sem.ValRep lbl wv.val (rpK1.setWidth 128).toNat ∧ J2 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩
  hr2 : ∀ σ0 c, J2 σ0 c → ∃ c', LocalRun p c c' ∧ J2' σ0 c'
  h3 : ∀ σ0 c, J2' σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
    XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧ c.hold = none ∧
    ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
      J3 σ0 { c with hold := some ((rAddr σ0.regs .X0 8).toNat, w') }
  h4 : ∀ σ0 c, J3 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
    (wv wold : TermRun.Word),
    XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧
    c.hold = some ((rAddr σ0.regs .X0 8).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
    Scc.Sem.ValRep lbl wv.val (rpK2.setWidth 128).toNat ∧ J4 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩
  hfen : ∀ σ0 c, J4 σ0 c → ∃ c', FenceRun p ms.pub .st c c' ∧ J5 σ0 c'
  hedge : ∀ σ0 c, J5 σ0 c → ∀ σ' : FAS, σ'.regs.X0.toBitVec = σ0.regs.X0.toBitVec →
    σ'.regs.X1.toBitVec = 0#64 → σ'.regs.X2.toBitVec = 2#64 → σ'.regs.X3.toBitVec = 13#64 →
    σ'.regs.X29.toBitVec = σ0.slot (-16) → σ'.regs.X30.toBitVec = σ0.slot (-8) →
    ∃ c', LocalRun p c c' ∧ Jr σ' c'
  htp : ∀ σ c, Jr σ c → σ.regs.TPIDR_EL0 = t
  hWp : ∀ m1 σ1, WcPreWH (NoMsrW (tpG t W) K) K exe endPc (wcR R D) (wcF R D F m1 σ1) (tpXa ms t)
    (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr).J σ1)
    (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1)
  hWs : ∀ m1 σ1, WcSp0WH (NoMsrW (tpG t W) K) K exe endPc (wcR R D) (wcF R D F m1 σ1) (tpXa ms t)
    (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1)
  hlim : ∀ σ c, Jr σ c → LimOk ms F exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (144 : Int64).toBitVec)
  hloc : ∀ σ c, Jr σ c → ∃ c', LocalRun p c c' ∧ Jr1 σ c'
  hq : ∀ σ c, Jr1 σ c → ∃ q : Call, q.OKB ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
    q.h = 256#64 ∧ q.k = 1#64 ∧ q.u ms = 2#64
  hbox : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, Jr1 σ q.1.c0) → BoxW lbl q.1
  hcell0 : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, Jr1 σ q.1.c0) → ∀ o : Nat, ms.lo o →
    o + ms.units 1 q.1.τ ≤ ms.cells →
    ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
    ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none
  hxa : ∀ m1 σ1, ∀ l A s c, lbl l = none → Spike.Lib.A64.Flow.At exe endPc (wcR R D) (wcF R D F m1 σ1)
    (bXH ms (_root_.Executable.labels exe).label (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1)
      l A) s c →
    TP t s → ms.xa l A 1 s c

/-- **`scc_rt_main` from `wc_rodata`'s `.sp0` to `wc_main`'s first allocation's heap abort is one segment inside
`W`** in any valid layout of `helloProg`: `hello_main_post_segW` into `wc_main`'s region `D` deep at its call,
then at every caller's state `m1`, `σ1` there `hello_wc_entry_segJr`, its allocator's words from `F`'s
(`hmem0`).

Superseded: frameless, so vacuous at the real run (`rodata` called under a frame); use
`MainGlueS.main_wc_segWS` (`Spike/Lib/A64HelloMainGlueS.lean`). -/
theorem main_wc_segW {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {W : Frag isaLSE2} {K : State → State → Prop}
    (hK : ms.K = some abi) {kp : Nat} (hp : Lays exe SccCode.helloProg kp)
    (hend : endPc = endOf exe SccCode.helloProg kp) {D : Int} (hD : 304 ≤ D) (hD16 : D % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hloD : R.lo ≤ -80 - D)
    (hhi : 0 ≤ R.hi) {m0 : MachineData} {σC : FAS} {Jp Jp' J1 J2 J2' J3 J4 J5 Jr Jr1 : FAS → Ctl → Prop}
    {t : UInt64} (hP : MainWcP W K p lbl ms exe endPc R D F m0 σC Jp Jp' J1 J2 J2' J3 J4 J5 Jr Jr1 t)
    (hmem0 : ∀ q : Call, q.OKB ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    SegW W K p lbl ms
      (Spike.Lib.A64.Flow.At exe endPc (mR R) (mF R F m0 σC)
        (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 J5 .s0))
      (fun s c => ∃ m1 σ1, Spike.Lib.A64.Flow.At exe endPc (wcR R D) (wcF R D F m1 σ1)
        (wXH ms (_root_.Executable.labels exe).label (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1)
          .abort) s c ∧ TP t s) :=
  Spike.Lib.A64.Flow.HelloM.hello_main_post_segW hp hend (by omega) hD16 hF hR hal hlo hloD hhi hP.hW hP.hra
    hP.hmem hP.hr0 hP.h1 hP.h2 hP.hr2 hP.h3 hP.h4 hP.hfen hP.hedge
    (Q := fun m1 σ1 s c => Spike.Lib.A64.Flow.At exe endPc (wcR R D) (wcF R D F m1 σ1)
      (wXH ms (_root_.Executable.labels exe).label (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1)
        .abort) s c ∧ TP t s)
    fun m1 σ1 hR' hal' hF' =>
      Spike.Lib.A64.Flow.HelloWc.hello_wc_entry_segJr hK hp hend hF' hR' hal' (show -D ≤ -304 by omega)
        (show (0 : Int) ≤ 0 by decide) hP.htp (hP.hWp m1 σ1) (hP.hWs m1 σ1) hP.hlim hP.hloc hP.hq hmem0 hP.hbox
        hP.hcell0 (hP.hxa m1 σ1)

/-! ## From `_start` to `wc_main`'s heap abort at the start's level -/

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Scc.Sem.Range} {Tk : State → Prop} {lbl' : Lbl}
  {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s, Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hX0 : ∀ s, freeNH (pcOf s) = true → X0 s)

include hp hlo hlab hsite hcl hc0 hpl0 hX0

/-- **From `_start` to `wc_main`'s first allocation's heap abort inside the start's level**: the start up to the
switch (`startEW_W0SH`), at each base `v` of the new stack of depth `Lsw` `scc_rt_main` up to `bl wc_rodata`
(`mainPreWH_W0SH`), `wc_rodata` up to its allocator's return (`hello_main_pre_segW`), whose fresh-label landings
are at `.sp0` (`hello_main_hxa_of_post`: `hJp`, `hpost`), and from `.sp0` (its states by `hret`) to `wc_main`'s
abort exit (`main_wc_segW` at `wc_main`'s region `D` deep, `hP`). The other exit is `wc_rodata`'s heap abort.

Superseded: frameless, so vacuous at the real run (`rodata` called under a frame); use
`StartWcS.hello_start_wc_segWS` (`Spike/Lib/A64HelloStartWcS.lean`); also `hpost` unsatisfiable (`b`, `w`
unconstrained vs `AllocLand`), see `StartWcS`'s Ea-level `hxa`. -/
theorem hello_start_wc_segW (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hs : WSep L a) (hro : L.Λ.rodata.Disjoint L.Λ.stackPool) {k0 : BitVec 64}
    {Lsw : Int} {ms : Spike.Lib.MemSide isaLSE2} {pS : Prog} {lblS : Lbl}
    (hK : ms.K = some abi) (hwf : L.Λ.WF) (hC0 : Spike.Lib.A64Consumer.CFacts L.Λ lbl' c0)
    (hF : FStable R F) {P : MachineData → Prop} (hP : FStable R P) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hRlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF L m)
    (hFw : ∀ m, F m → WordsNoneP L.Λ m.dmem)
    (hrS : rS = ⟨(stacksA L.lab + k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hSM : FStable R (Spike.Lib.A64.Flow.Ret0.StackM rS))
    (hSMi : FStable (R.callee Spike.Lib.A64.Abort.oI.sp (-256) 0) (Spike.Lib.A64.Flow.Ret0.StackM rS))
    (hSMt : FStable ((R.callee Spike.Lib.A64.Abort.oI.sp (-256) 0).callee
      Spike.Lib.A64.Flow.Ret0.ThreadInit.oI.sp (-208) 0) (Spike.Lib.A64.Flow.Ret0.StackM rS))
    (hLsw : 288 ≤ Lsw) (hL8 : Lsw % 8 = 0)
    (hk : k0.toNat + 16384 ≤ 536870912) (h16 : (stacksA L.lab + k0 + 16384#64).toNat % 16 = 0)
    (hok : (swR (stacksA L.lab + k0 + 16384#64) (-Lsw) 0).OK)
    (hsubS : ∀ k, (swR (stacksA L.lab + k0 + 16384#64) (-Lsw) 0).Off k →
      ((swR (stacksA L.lab + k0 + 16384#64) (-Lsw) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA L.lab + k0 + 16384#64) (-Lsw) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA L.lab + k0 + 16384#64) (-Lsw) 0).addr k).toNat + 7))
    (hfitL : (limA (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (houtL : ((limA (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64))).toNat : Int) + 8 ≤
        (stacksA L.lab + k0 + 16384#64).toNat + -Lsw ∨
      ((stacksA L.lab + k0 + 16384#64).toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64))).toNat)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (Spike.Lib.A64.Flow.Ret0.takeMem pm rS m))
    (hoffP : ¬ (L.Λ.stackPool.lo < (R.addr (-48)).toNat ∧
      (R.addr (-48)).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size))
    (htcbW : ∀ g, g.ra = (L.lab ".L0_scc_rt_start.sp2").toBitVec → ∀ i,
      Spike.Lib.A64.Flow.Ret0.TcbW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe
        L.endPc (R.callee Spike.Lib.A64.Abort.oI.sp (-192) 0) F ⟨g, 0#64, c0⟩ i)
    (htiW : ∀ g, g.ra = (L.lab Spike.Lib.A64.Flow.Ret0.sp3L).toBitVec → ∀ i,
      Spike.Lib.A64.Flow.Ret0.TiW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe
        L.endPc (R.callee Spike.Lib.A64.Abort.oI.sp (-256) 0) F (Spike.Lib.A64.Flow.Ret0.StackM rS)
        ⟨g, pinA L.lab + 0#64 + 8#64, k0, c0⟩ i P)
    (hhdr : StOk ms F L.exe L.endPc (pinA L.lab + 0#64) (Spike.Lib.A64.Flow.Ret0.AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcbO : ∀ g, Spike.Lib.A64.Rt.TcbOkA ms F L.exe L.endPc (R.callee Spike.Lib.A64.Abort.oI.sp (-192) 0) F
      ⟨g, 0#64, c0⟩)
    (hfld : ∀ e ∈ Spike.Lib.A64.Flow.Ret0.ThreadInit.fields (pinA L.lab + 0#64 + 8#64) (stacksA L.lab + k0),
      StOk ms F L.exe L.endPc (pinA L.lab + 0#64 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : ∀ g, Spike.Lib.A64.Rt.TakeOkA ms F L.exe L.endPc ((R.callee Spike.Lib.A64.Abort.oI.sp (-256) 0).callee
      Spike.Lib.A64.Flow.Ret0.ThreadInit.oI.sp (-208) 0) F ⟨g, k0, c0⟩)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64))) 8 = none)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) false
      ⟨limA (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64)), 8⟩ = true)
    (hlim80 : LimOk ms F L.exe L.endPc (limA (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64)))
      (stacksA L.lab + k0 + 16384#64 - (80 : Int64).toBitVec))
    (hlim128 : LimOk ms F L.exe L.endPc (limA (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64)))
      (stacksA L.lab + k0 + 16384#64 - (80 : Int64).toBitVec - (48 : Int64).toBitVec))
    (hH : L.Λ.heap.lo ≤ ms.heap) (hHi : ms.heap + 16 * ms.cells ≤ L.Λ.heap.lo + L.Λ.heap.size)
    (hctr : WordIn L.Λ.heap ms.ctr ∨ WordIn L.Λ.data ms.ctr)
    (hoff : ∀ q : Call, q.OK ms L.lab → ms.off q.n q.τ ≤ 16 * ms.units q.n q.τ)
    (hoffB : ∀ q : Call, q.OKB ms L.lab → ms.off q.n q.τ ≤ 16 * ms.units q.n q.τ)
    {J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.A64.Flow.AS → Ctl → Prop}
    (hWrd : ∀ v m0 σC, Spike.Lib.A64.Flow.HelloRd.RdPreW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0)
      (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc (mR (swR v (-Lsw) 0)) (mF (swR v (-Lsw) 0) (FS L rS Lsw k0 v) m0 σC)
      ms (mRdJ0 (mNC L.lab (JS L k0 c0)).J σC) (J1 σC))
    (hloc : ∀ σC σ c, mRdJ0 (mNC L.lab (JS L k0 c0)).J σC σ c → ∃ c', Spike.Lib.LocalRun pS c c' ∧ J1 σC σ c')
    (hq : ∀ σC σ c, J1 σC σ c → ∃ q : Call, q.OK ms L.lab ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ms = 3#64)
    {D : Int} (hD : 304 ≤ D) (hD16 : D % 16 = 0) (hLD : 80 + D ≤ Lsw) {t : UInt64}
    {Jp Jp' Jx1 J2 J2' J3 J4 J5 Jr Jr1 : BitVec 64 → MachineData → FAS → FAS → Ctl → Prop}
    (hJp : ∀ v m0 σC (q : AG ms L.lab) l b w σx σ c0 c, (Ea ms q.1 l b w).J σx c →
      (rN L.lab (mRdJ0 (mNC L.lab (JS L k0 c0)).J σC) (J1 σC) .call).J σ c0 →
      (Spike.Lib.A64.Alloc.N L.lab ms q.1 .e).J (enter (-48) σ) c0 →
      Jp v m0 σC (leave (aR (mR (swR v (-Lsw) 0))) (-48) σ σx) c)
    (hpost : ∀ v l b w s c, lblS l = none → (∃ m0 σC, Spike.Lib.A64.Flow.At L.exe L.endPc (mR (swR v (-Lsw) 0))
      (mF (swR v (-Lsw) 0) (FS L rS Lsw k0 v) m0 σC)
      (pN L.lab (Jp v m0 σC) (Jp' v m0 σC) (Jx1 v m0 σC) (J2 v m0 σC) (J2' v m0 σC) (J3 v m0 σC) (J4 v m0 σC)
        (J5 v m0 σC) .s0) s c) →
      ms.xa l b w s c)
    (hret : ∀ v m0 σC σ c, (rX ms L.lab lblS (J1 σC) .sp0).J σ c → Jp v m0 σC σ c)
    (hPw : ∀ v m0 σC, MainWcP (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) pS lblS ms
      L.exe L.endPc (swR v (-Lsw) 0) D (FS L rS Lsw k0 v) m0 σC (Jp v m0 σC) (Jp' v m0 σC) (Jx1 v m0 σC)
      (J2 v m0 σC) (J2' v m0 σC) (J3 v m0 σC) (J4 v m0 σC) (J5 v m0 σC) (Jr v m0 σC) (Jr1 v m0 σC) t) :
    SegW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) pS lblS ms
      (Spike.Lib.A64.Flow.At L.exe L.endPc R (fun m => F m ∧ P m) (entryN L.lab c0))
      (fun s c => (∃ v m0 σC m1 σ1,
          Spike.Lib.A64.Flow.At L.exe L.endPc (wcR (swR v (-Lsw) 0) D) (wcF (swR v (-Lsw) 0) D (FS L rS Lsw k0 v) m1 σ1)
            (wXH ms L.lab (wcJ0 (mWC L.lab σC (Jr1 v m0 σC)).J σ1) .abort) s c ∧ TP t s) ∨
        ∃ v m0 σC,
          Spike.Lib.A64.Flow.At L.exe L.endPc (mR (swR v (-Lsw) 0)) (mF (swR v (-Lsw) 0) (FS L rS Lsw k0 v) m0 σC)
            (rX ms L.lab lblS (J1 σC) .abort) s c) := by
  have hpS : Lays L.exe SccCode.helloProg L.pfx := hp ▸ L.lays
  have hendS : L.endPc = endOf L.exe SccCode.helloProg L.pfx := by show endOf L.exe L.prog L.pfx = _; rw [hp]
  have hFwS := fun v => Spike.Lib.A64.Rt.wordsNoneP_swFSL_fstable (v := v) hwf hsub hok (by omega) hL8 hsubS
    hfitL houtL hfit
  refine (Spike.Lib.A64.Rt.startEF_segWA (Fw := WordsNoneP L.Λ) hpS hendS hello_rtCodeIn0 hK hF hR hal hRlo hhi
    0#64 k0 c0 (by decide) hhdr htcbO hk hfld htk h16 hok hsubS hun hFw hFwS hRS hfit houtS hFt hP
    (Spike.Lib.A64.WakePh.StartGlue.StartEW.toF (StartWf.startEW_W0SH hp hlo hlab hsite hcl hc0 hpl0 hX0 hΛ hs hro
      hC0 hR hal hRlo hhi hFr rfl hrS hsub hSM hSMi hSMt hfit h16 hok hL8 hoffP htcbW htiW))).seq ?_
  refine (SegW.exists_pre (P := fun g : {v : BitVec 64 // v.toNat % 16 = 0 ∧ (swR v (-Lsw) 0).OK} =>
      Spike.Lib.A64.Flow.At L.exe L.endPc (swR g.1 (-Lsw) 0) (FS L rS Lsw k0 g.1) (mainE0 L.lab (gS L k0 c0)))
    fun g => ?_).mono_pre fun _ _ ⟨v, h1, h2, hA⟩ => ⟨⟨v, h1, h2⟩, hA⟩
  obtain ⟨v, hv, hR'⟩ := g
  have hpre := MainWf.mainPreWH_W0SH (R := swR v (-Lsw) 0) (F := FS L rS Lsw k0 v) (ms := ms)
    (J := JS L k0 c0) (tp := UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64)) (a := a) (ar := ar) (Dt := Dt) (Ctx := Ctx)
    (lsize := lsize) (frM := frM)
    hp hlo hlab hsite hcl hc0 hpl0 hX0 hΛ (fun _ _ h => ⟨h.1.1, h.1.2.2⟩) hC0
    hR' hv (show -Lsw ≤ -80 by omega) (Int.le_refl 0) (show (-Lsw) % 8 = 0 by omega)
    (show (0 : Int) % 8 = 0 by decide) hsub hfit (fun _ h => h.2.2) hmr (fun _ h => h.2.1.2)
  have hS : SegW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) pS lblS ms
      (fun s c => ∃ m0 σC, Spike.Lib.A64.Flow.At L.exe L.endPc (mR (swR v (-Lsw) 0))
        (mF (swR v (-Lsw) 0) (FS L rS Lsw k0 v) m0 σC)
        (pN L.lab (Jp v m0 σC) (Jp' v m0 σC) (Jx1 v m0 σC) (J2 v m0 σC) (J2' v m0 σC) (J3 v m0 σC) (J4 v m0 σC)
          (J5 v m0 σC) .s0) s c)
      (fun s c => ∃ m0 σC, ∃ m1 σ1, Spike.Lib.A64.Flow.At L.exe L.endPc (wcR (swR v (-Lsw) 0) D)
        (wcF (swR v (-Lsw) 0) D (FS L rS Lsw k0 v) m1 σ1)
        (wXH ms L.lab (wcJ0 (mWC L.lab σC (Jr1 v m0 σC)).J σ1) .abort) s c ∧ TP t s) :=
    SegW.exists_pre fun m0 => SegW.exists_pre fun σC => SegW.mono_post (
    main_wc_segW (W := WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (K := Spike.Lib.A64.PhRec.K L rS) (p := pS)
      (lbl := lblS) (F := FS L rS Lsw k0 v) (Jp := Jp v m0 σC) (Jp' := Jp' v m0 σC) (J1 := Jx1 v m0 σC)
      (J2 := J2 v m0 σC) (J2' := J2' v m0 σC) (J3 := J3 v m0 σC) (J4 := J4 v m0 σC) (J5 := J5 v m0 σC)
      (Jr := Jr v m0 σC) (Jr1 := Jr1 v m0 σC) (t := t) hK hpS hendS hD hD16 (hFwS v) hR' hv
      (show -Lsw ≤ -288 by omega) (show -Lsw ≤ -80 - D by omega) (Int.le_refl 0) (hPw v m0 σC)
      (Spike.Lib.A64.WakePh.StartGlue.hmemB_of_wordsNone hwf (fun _ h => h.1.wn) hH hHi hctr hoffB))
      fun _ _ h => ⟨m0, σC, h⟩
  refine ((SegW.seq_left (E := fun s c => ∃ m0 σC, Spike.Lib.A64.Flow.At L.exe L.endPc (mR (swR v (-Lsw) 0))
      (mF (swR v (-Lsw) 0) (FS L rS Lsw k0 v) m0 σC) (rX ms L.lab lblS (J1 σC) .abort) s c)
    ((Spike.Lib.A64.Flow.HelloM.hello_main_pre_segW hpS hendS (hFwS v) hR' hv
    (show -Lsw ≤ -288 by omega) (Int.le_refl 0) ⟨hpre.1, hpre.2, hWrd v⟩
    (Spike.Lib.A64.WakePh.MainWf.limOk_mainE0 ⟨hlim80.rt, hlim80.mp, fun _ h => h.2.1.2, hlim80.room⟩)
    ?hlimR hloc hq
    (Spike.Lib.A64.Alloc.hmem_of_wordsNone hwf (fun _ h => h.1.wn) hH hHi hctr hoff)
    (Spike.Lib.A64.Flow.HelloM.hello_main_hxa_of_post (hJp v) (hpost v))).mono_post ?conv) hS).mono_post ?pack)
  case hlimR =>
    rintro σ c ⟨⟨-, hsp, htp⟩, -⟩
    rw [Spike.Lib.A64.Flow.Ret0.tcbA_limA htp, hsp]
    exact ⟨hlim128.rt, hlim128.mp, fun _ h => h.2.1.2, hlim128.room⟩
  case conv =>
    rintro s c ⟨m0, σC, y, h⟩
    cases y
    · obtain ⟨he, hn, hdc, hpc, σ, hA, hD', hJ⟩ := h
      exact .inl ⟨m0, σC, he, hn, hdc, hpc, σ, hA, hD', hret v m0 σC σ c hJ⟩
    · exact .inr ⟨m0, σC, h⟩
  case pack =>
    rintro s c (⟨m0, σC, m1, σ1, h⟩ | ⟨m0, σC, h⟩)
    · exact .inl ⟨v, m0, σC, m1, σ1, h⟩
    · exact .inr ⟨v, m0, σC, h⟩

end Gen

end Spike.Lib.A64.HelloPh.MainGlueW

/-- info: 'Spike.Lib.A64.HelloPh.MainGlueW.main_wc_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainGlueW.main_wc_segW

/--
info: 'Spike.Lib.A64.HelloPh.MainGlueW.hello_start_wc_segW' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainGlueW.hello_start_wc_segW
