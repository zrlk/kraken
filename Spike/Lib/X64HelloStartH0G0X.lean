/-
**hello.w from `_start` to `wc_rodata`'s heap abort at hello's start choices, level 0, at `ownGHXW`** (x86-64; the
`ownGHXW` instance of `Spike/Lib/X64HelloStartH0G0.lean`): `StartPlaceX.hello_rd_placeXT` at hello's start choices
(`c0S`, `helloSrc`, `L0T`/`ls0T ls`, `cTW`, the take site, `frH c0S.env`, `J' v := rdJH lab (RS helloLsw v) JW`,
`helloLsw`), with the root's memory side owning `ownGHXW Ly ntA` and the start's level `WSHFg (ownGHXW Ly ntA)`.
The leaf premises are discharged as in `StartH0G0.hello_start_rd_h0G0`; the thread init inside `WSHX` is
`hello_rd_placeXT`'s.

Left as premises: the loader's facts (`hpa`, `hhp`, `hlo0`, `hstat`, `hA13`, `hctr2`, `hc`), the immediate `hme`,
and the source/frame premises (`hWe`, `hrd`, `hloc`, `hq`, `hxa`) at the new memory side and level.

- `hello_start_rd_h0G0X`: the statement; its exit and `hxa` carry `TP (tpOf (tcbS Ly))`.

## Differences from the AArch64 version

AArch64's root memory side owns `ownGH` (`A64HelloStartH0G0`); x86-64's main also holds its own and the worker's
TCB words, so the memory side owns `ownGHXW` and the level is `WSHFg (ownGHXW …)` (`hello_rd_placeXT`). The rest
is `StartH0G0`'s differences: `scc_rt_main` in `MainGlue.RS helloLsw v` with `J'` indexed by `v` (`hloc` only at
`topS Ly 0`), `helloLsw = 488`,
the loader's facts as `cellsOf asm = some …`, the start's controls `HelloRdCf.start_ctl c0S.env`, the thread
pointer `tpOf (tcbS Ly)`.
-/
import Spike.Lib.X64HelloStartPlaceXT
import Spike.Lib.X64HelloC0S
import Spike.Lib.X64WakeOSide
import Spike.Lib.X64WakeHG

namespace Spike.Lib.X64.HelloPh.StartH0G0X

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout entryR rtF)
open Spike.Lib.X64Consumer (Lbl Lsize Pz)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64.HelloPh.StartWcS (WS rdJH)
open Spike.Lib.X64 (At enter)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS topS tcbS)
open Spike.Lib.X64.Flow.Hello1 (AG mR mF mRdJ0 mNC aR)
open Spike.Lib.X64.Flow.HelloRd (rN rX RdPreW)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.Alloc (Call Ea)
open Spike.Lib.X64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.X64.DmemPriv (WordsNoneP)
open Spike.Lib (FragS Frag SegWS LocalRun PlaceWX)
open Spike.Lib.X64WakeLoadT (L0T ls0T tcb0)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64HelloSrc (helloSrc)

/-- The abstract state (`AS` alone is ambiguous here). -/
local notation "FAS" => Spike.Lib.X64.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw i

set_option hygiene false in
local notation "NT" => Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
local notation "FWN" => fun m : MachineData => WordsNoneP (Ly).Λ m.dmem ∧ rtF (Ly) m

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
/-- The start's labels. -/
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- The take site. -/
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
/-- The root's memory sides at the frames `fs`, owning `ownGHXW`. -/
local notation "MSF" => fun fs : List TermRun.Frame => Spike.Lib.X64ConsumerA.msOfA (Ly).Λ μ rd
  (Spike.Lib.X64HelloGOf2H.gWH hpw i (Spike.Lib.X64WakeHG.cTW hpw i))
  (fun s _ => Spike.Lib.X64.HelloPh.ownGHXW (Ly) NT s) (AR) I (LB) (ls0T ls) fs

set_option hygiene false in
/-- The start's level at hello's choices, at `ownGHXW`, with frames. -/
local notation "WP" => fun s c fs => Spike.Lib.X64.HelloWf.WSHFg (Spike.Lib.X64.HelloPh.ownGHXW (Ly) NT) (Ly) (AR)
  helloSrc Dt (Spike.Lib.X64.HelloPh.ClH (Ly)) Ctx (LB) lsize frM (X0WH (Ly) (AX)) fs s c

set_option hygiene false in
local notation "KR" => Spike.Lib.X64.PhRec.K (Ly) RS0

set_option hygiene false in
/-- `scc_rt_main`'s entry invariant at `c0S`. -/
local notation "JW" => JS (Ly) 0#64 c0S

set_option hygiene false in
/-- The source after the setup's call of `rodata`, at the switch base `v`. -/
local notation "J'" => fun v : BitVec 64 => rdJH (Ly).lab (RS helloLsw v) (JW)

set_option hygiene false in
/-- `wc_rodata`'s frame: the setup's call of `rodata` from `c0S`. -/
local notation "FR" => Spike.Lib.X64HelloRdCf.frH c0S.env

/-- **From `_start` to `wc_rodata`'s heap abort at hello's start choices, level 0, at `ownGHXW`**:
`StartPlaceX.hello_rd_placeXT` at hello's start choices (`c0S`, `helloSrc`, `L0T`/`ls0T ls`, `cTW`, the take site, `frH c0S.env`, `rdJH` at
`RS helloLsw v`, `helloLsw`), its leaf premises discharged from the loader's facts. -/
theorem hello_start_rd_h0G0X {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    {Dt : State → Prop} {Ctx : FragS isa} {lsize : Lsize} {frM : TermRun.Frame}
    {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {I : Spike.Lib.X64ConsumerS.InvS} {ls : Lsize} {lblS : Lbl}
    (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells)
    (hlo0 : Λ0.code.lo = lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hctr2 : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ Spike.Lib.X64HelloGOf2H.lim2AH (Ly))
    (hc : Spike.Lib.X64.Rt.CtrZ o)
    /- the root's immediates (`HelloImms.immsH_start` at `i := HelloImms.immsH Λ0 i0`) -/
    (hme : i Scc.Sem.SrcSem.setupTerm "me" 0 = some (tcb0 Λ0))
    {J1 : FAS → FAS → Ctl → Prop}
    (hWe : ∀ v s c, At (Ly).exe (Ly).endPc (RS helloLsw v) (FS (Ly) RS0 helloLsw 0#64 v)
      (mNC (Ly).lab (RS helloLsw v) (JW)) s c → WP s c [])
    (hrd : ∀ v m0 σC, RdPreW (Spike.Lib.X64.WakeTP.tpG (tpOf (tcbS (Ly))) fun s c => WP s c [FR]) KR
      (Ly).exe (Ly).endPc (mR (RS helloLsw v)) (mF (RS helloLsw v) (FS (Ly) RS0 helloLsw 0#64 v) m0 σC)
      ((MSF) [FR]) (mRdJ0 ((J') v) σC) (J1 σC))
    (hloc : ∀ σC σ c, mRdJ0 ((J') (topS (Ly) 0#64)) σC σ c → ∃ c', LocalRun helloSrc c c' ∧ J1 σC σ c')
    (hq : ∀ σC σ c, J1 σC σ c → ∃ q : Call, q.OK ((MSF) [FR]) (Ly).lab ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ((MSF) [FR]) = 3#64)
    (hxa : ∀ v m0 σC, ∀ q : AG ((MSF) [FR]) (Ly).lab, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF (RS helloLsw v) (FS (Ly) RS0 helloLsw 0#64 v) m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Spike.Lib.X64.Abs (mR (RS helloLsw v)) ⟨-48, []⟩ mC σ ∧
        (rN (Ly).lab (mR (RS helloLsw v)) (mRdJ0 ((J') v) σC) (J1 σC) .call).J σ c ∧
        (Spike.Lib.X64.Alloc.N (Ly).lab ((MSF) [FR]) q.1 .e).J (enter (-48) σ) c ∧
        Spike.Lib.X64.CKept (mR (RS helloLsw v)) (-48) (-160) 8 mC m) →
      ∀ l b w s c, lblS l = none →
        At (Ly).exe (Ly).endPc (aR (mR (RS helloLsw v))) F' (Ea ((MSF) [FR]) q.1 l b w) s c →
        TP (tpOf (tcbS (Ly))) s → ((MSF) [FR]).xa l b w s c) :
    SegWS (WP) KR helloSrc lblS (MSF)
      ((At (Ly).exe (Ly).endPc (entryR E) (fun m => FWN m ∧ Pz RS0 m)
        (Spike.Lib.X64.Rt.entryN0 (Ly).lab c0S)).at [])
      (Frag.at (fun s c => ∃ v m0 σC,
          At (Ly).exe (Ly).endPc (mR (RS helloLsw v)) (mF (RS helloLsw v) (FS (Ly) RS0 helloLsw 0#64 v) m0 σC)
            (rX ((MSF) [FR]) (Ly).lab lblS (mR (RS helloLsw v)) (J1 σC) .abort) s c ∧
          TP (tpOf (tcbS (Ly))) s) [FR]) := by
  have hp : o.prog = SccCode.helloCells := Option.some.inj (hpa.symm.trans hhp)
  have hme' : (Ly).Λ.imms Scc.Sem.SrcSem.setupTerm "me" 0 = some (tcb0 (Ly).Λ) := hme
  exact Spike.Lib.X64.HelloPh.StartPlaceX.hello_rd_placeXT hpw i hE hp hlo0
    (Spike.Lib.X64HelloRdCf.start_ctl c0S.env) (Spike.Lib.X64.HelloPh.C0S.placedSE_c0S hme') rfl hA13
    (Spike.Lib.X64WakeOSide.hro_W hpw i) (Spike.Lib.X64.HelloPh.C0S.cfacts_c0S hme')
    (Spike.Lib.X64.WakePh.StartPlaceLy.hfree_W hpw i hstat ls)
    hctr2
    (Spike.Lib.X64.WakePh.StartPlaceLy.hcT_W hpw i) hc
    (by decide) (by decide) (by decide)
    hWe (fun _ => Spike.Lib.X64.HelloPh.StartWcS.rdJH_run (fun _ _ h => h.1.1) Spike.Lib.X64.HelloPh.C0S.c0S_u)
    (fun _ => Spike.Lib.X64.HelloPh.StartWcS.rdJH_back) hrd hloc hq hxa

end Spike.Lib.X64.HelloPh.StartH0G0X


/-- info: 'Spike.Lib.X64.HelloPh.StartH0G0X.hello_start_rd_h0G0X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartH0G0X.hello_start_rd_h0G0X
