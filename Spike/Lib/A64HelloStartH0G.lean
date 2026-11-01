/-
**`hello_start_wc_place` at hello's start choices** (AArch64; the twin of
`A64WakeStartH0G`): the start control `C0S.c0S` (the setup start, `setupStartT 2`'s thread), the program
`helloSrc` (both the start's and the source run's), the labels `L0T`/`ls0T ls`, the dummy heap word
`WakeHG.cTW`, the take site `ax := lab scc_rt_take_site`, `wc_rodata`'s frame `fr := HelloRdCf.frH c0S.env`
(the setup's call of `rodata`), `J' := StartWcS.rdJH`, and hello's depths **`helloD = 400`,
`helloLsw = 480`** (named once here; consumers reference the names): `wc_main`'s region `400` below
`wc_rodata`'s call and `scc_rt_main`'s frame `80` above it, inside the new stack of `16384` bytes. `400` is
`wc_main`'s frame `144` plus `scc_rt_thread_init`'s callee region `256` (the call at `.L22_wc_main.sp3`,
`R.callee (-144) (-256) 0`; the hat chain's and `HelloHMid.BoxPureH`'s `R.lo ≤ -400`). It covers the deepest
consumer below the box's allocation too: the allocator's `160` (the heap abort's `wXH .abort` at `-304`) plus
the abort dispatcher's and heap stub's `48` below it (`seg_jabort2RW`'s `R.lo ≤ -304 - 48`, the stub's
`R.lo ≤ -352`). Every consumer reads a lower bound (`R.lo ≤ -k`), none an exact depth. The bounds, all by
`decide` (`helloD_bounds`): `hD`: `304 ≤ 400`, `hD16`: `400 % 16 = 0`, `hLD`: `80 + 400 ≤ 480`, `hL8`:
`480 % 8 = 0`, `hLmax`: `480 ≤ 12288`; `StartWcS`'s `288 ≤ 480`; `wc_rodata`'s own depth `80 + 48 + 208 = 336 ≤
480`, and its heap abort's `80 + 208 + 48 = 336 ≤ 480`. No other bound reads `Lsw` (the prologue checks read the
stack limit word, not the depth).

Discharged here (beyond `hello_start_wc_place`'s):
- `hp` from the loader's two parses (`hpa`, `hhp`), `hlo` from the input layout's (`hlo0`);
- `hc0` by `C0S.c0S_ctl`, `hpl0` by `C0S.placedSE_c0S`, `hC0` by `C0S.cfacts_c0S` (at `hme`: the layout's
  immediates put `me` at `tcb0` at `setupTerm`; `C0S.immsH_start` at `i := C0S.immsH Λ0 i0`);
- `hax` by `rfl`; `hro` by `WakeOSide.hro_W`; `hfree` by `StartPlaceLy.hfree_W`; `hctr2` a premise (the counters
  off the second limit word; at the instance `HelloCtr2.hctr2_H` from `hA13`); `hcT` by `StartPlaceLy.hcT_W`;
  `hfr` by `rfl`;
- `hrun`, `hJ'` by `StartWcS.rdJH_run`, `rdJH_back` (the source's call of `rodata` from `c0S`).

Left as premises: the loader's facts (`hpa`, `hhp`, `hlo0`, `hstat`, `hA13`, `hctr2`, `hc`), the
immediate `hme`, and the source/frame/`wc_main` premises at these choices (as split in
`hello_start_wc_segWS`: `hWe`, `hrd`, `hloc`, `hq`, `hret`, `hPw`; `hxa`, the allocator's
fresh-label landing in `ms [FR]`'s allocation fragment).

- `helloD`, `helloLsw`, `helloD_bounds`: the depths and their bounds.
- `hello_start_wc_h0G`: the statement.
-/
import Spike.Lib.A64HelloStartPlace
import Spike.Lib.A64HelloC0S
import Spike.Lib.A64WakeStartPlaceLy
import Spike.Lib.HelloGOf2H

namespace Spike.Lib.A64.HelloPh.StartH0G

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (textProgram)
open Spike.Lib.A64.Rt (RuntimeLayout entryR rtF)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.HelloPh.StartGlue (X0WH)
open Spike.Lib.A64.HelloPh.StartWcS (WS rdJH)
open Spike.Lib.A64.Flow (swR At enter leave)
open Spike.Lib.A64.Flow.Ret0 (entryN)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.Flow.Hello1 (AG mR mF mRdJ0 mNC aR mWC)
open Spike.Lib.A64.Flow.HelloRd (rN rX pN RdPreW)
open Spike.Lib.A64.Flow.HelloM (wcR wcF wcJ0)
open Spike.Lib.A64.Flow.HelloWc (wXH)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.Alloc (Call Ea)
open Spike.Lib.A64.HelloPh.MainGlueS (MainWcPS)
open Spike.Lib.DmemPriv (WordsNoneP)
open Spike.Lib (FragS Frag SegWS LocalRun)
open Spike.Lib.WakeLoadT (L0T ls0T tcb0)
open Spike.Lib.A64.HelloPh.C0S (c0S)
open Spike.Lib.HelloSrc (helloSrc)

/-- **hello's `wc_main` region depth** below `wc_rodata`'s call (`wc_main`'s frame, the allocator's, and the heap
abort's dispatcher and stub). -/
abbrev helloD : Int := 400

/-- **hello's new-stack region depth** (`scc_rt_main`'s frame `80` above `helloD`). -/
abbrev helloLsw : Int := 480

/-- **The depths' bounds** (`hello_start_wc_place`'s and `StartWcS`'s, `wc_rodata`'s and its heap abort's). -/
theorem helloD_bounds : 304 ≤ helloD ∧ helloD % 16 = 0 ∧ 80 + helloD ≤ helloLsw ∧ helloLsw % 8 = 0 ∧
    helloLsw ≤ 12288 ∧ 288 ≤ helloLsw ∧ 80 + 48 + 208 ≤ helloLsw ∧ helloLsw - 80 - 208 ≥ 48 ∧
    -helloD ≤ -304 - 48 := by
  decide

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw i

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw i

set_option hygiene false in
local notation "NT" => Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
local notation "FWN" => fun m : MachineData => WordsNoneP (Ly).Λ m.dmem ∧ rtF (Ly) m

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
/-- The start's labels. -/
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- The take site. -/
local notation "AX" => (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
/-- The root's memory sides at the frames `fs`. -/
local notation "MSF" => fun fs : List TermRun.Frame => Spike.Lib.A64ConsumerA.msOfA (Ly).Λ μ rd
  (Spike.Lib.HelloGOf2H.gWH hpw i (Spike.Lib.WakeHG.cTW hpw i)) (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) NT s)
  (AR) I (LB) (ls0T ls) fs

set_option hygiene false in
/-- The start's level at hello's choices. -/
local notation "WP" => WS (Ly) NT (AR) helloSrc Dt (Spike.Lib.A64.HelloPh.ClH (Ly)) Ctx (LB) lsize frM
  (X0WH (Ly) (AX))

set_option hygiene false in
local notation "KR" => Spike.Lib.A64.PhRec.K (Ly) RS

set_option hygiene false in
/-- `scc_rt_main`'s entry invariant at `c0S`. -/
local notation "JW" => JS (Ly) 0#64 c0S

set_option hygiene false in
/-- The source after the setup's call of `rodata`. -/
local notation "J'" => rdJH (Ly).lab (JW)

set_option hygiene false in
/-- `wc_rodata`'s frame: the setup's call of `rodata` from `c0S`. -/
local notation "FR" => Spike.Lib.HelloRdCf.frH c0S.env

/-- **From `_start` to `wc_main`'s heap abort at hello's start choices**: `StartPlace.hello_start_wc_place` at
`c0S`, `helloSrc`, `L0T`/`ls0T ls`, `cTW`, the take site, `frH c0S.env`, `rdJH`, `helloD`, `helloLsw`, its
leaf premises discharged from the loader's facts (see the module doc). -/
theorem hello_start_wc_h0G {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    {Dt : State → Prop} {Ctx : FragS isaLSE2} {lsize : Lsize} {frM : TermRun.Frame}
    {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {I : Spike.Lib.A64ConsumerS.InvS} {ls : Lsize} {lblS : Lbl}
    (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg)
    (hlo0 : Λ0.code.lo = lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hctr2 : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ Spike.Lib.HelloGOf2H.lim2AH (Ly))
    (hc : Spike.Lib.A64.Rt.CtrZ o)
    /- the root's immediates (`C0S.immsH_start` at `i := C0S.immsH Λ0 i0`) -/
    (hme : i Scc.Sem.SrcSem.setupTerm "me" 0 = some (tcb0 Λ0))
    {J1 : FAS → FAS → Ctl → Prop}
    (hWe : ∀ v s c, At (Ly).exe (Ly).endPc (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v) (mNC (Ly).lab (JW))
      s c → WP s c [])
    (hrd : ∀ v m0 σC, RdPreW (fun s c => WP s c [FR]) KR (Ly).exe (Ly).endPc (mR (swR v (-helloLsw) 0))
      (mF (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v) m0 σC) ((MSF) [FR]) (mRdJ0 (J') σC) (J1 σC))
    (hloc : ∀ σC σ c, mRdJ0 (J') σC σ c → ∃ c', LocalRun helloSrc c c' ∧ J1 σC σ c')
    (hq : ∀ σC σ c, J1 σC σ c → ∃ q : Call, q.OK ((MSF) [FR]) (Ly).lab ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ((MSF) [FR]) = 3#64)
    {t : UInt64} {Jp Jp' Jx1 J2 J2' J3 J4 J5 Jr Jr1 : BitVec 64 → MachineData → FAS → FAS → Ctl → Prop}
    (hxa : ∀ v m0 σC, ∀ q : AG ((MSF) [FR]) (Ly).lab, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v) m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Spike.Lib.A64.Flow.Abs (mR (swR v (-helloLsw) 0)) ⟨-48, []⟩ mC σ ∧
        (rN (Ly).lab (mRdJ0 (J') σC) (J1 σC) .call).J σ c ∧
        (Spike.Lib.A64.Alloc.N (Ly).lab ((MSF) [FR]) q.1 .e).J (enter (-48) σ) c ∧
        Spike.Lib.A64.Flow.CKept (mR (swR v (-helloLsw) 0)) (-48) (-160) 0 mC m) →
      ∀ l b w s c, lblS l = none →
        At (Ly).exe (Ly).endPc (aR (mR (swR v (-helloLsw) 0))) F' (Ea ((MSF) [FR]) q.1 l b w) s c →
        ((MSF) [FR]).xa l b w s c)
    (hret : ∀ v m0 σC σ c, (rX ((MSF) [FR]) (Ly).lab lblS (J1 σC) .sp0).J σ c → Jp v m0 σC σ c)
    (hPw : ∀ v m0 σC, MainWcPS (WP) KR helloSrc lblS (MSF) (Ly).exe (Ly).endPc (swR v (-helloLsw) 0) helloD
      (FS (Ly) RS helloLsw 0#64 v) (FR) m0 σC (Jp v m0 σC) (Jp' v m0 σC) (Jx1 v m0 σC) (J2 v m0 σC) (J2' v m0 σC)
      (J3 v m0 σC) (J4 v m0 σC) (J5 v m0 σC) (Jr v m0 σC) (Jr1 v m0 σC) t) :
    SegWS (WP) KR helloSrc lblS (MSF)
      ((At (Ly).exe (Ly).endPc (entryR E) (fun m => FWN m ∧ Spike.Lib.A64Consumer.Pz RS m)
        (entryN (Ly).lab c0S)).at [])
      (fun s c fs => Frag.at (fun s c => ∃ v m0 σC m1 σ1,
          At (Ly).exe (Ly).endPc (wcR (swR v (-helloLsw) 0) helloD)
            (wcF (swR v (-helloLsw) 0) helloD (FS (Ly) RS helloLsw 0#64 v) m1 σ1)
            (wXH ((MSF) []) (Ly).lab (wcJ0 (mWC (Ly).lab σC (Jr1 v m0 σC)).J σ1) .abort) s c ∧ TP t s) [] s c fs ∨
        Frag.at (fun s c => ∃ v m0 σC,
          At (Ly).exe (Ly).endPc (mR (swR v (-helloLsw) 0))
            (mF (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v) m0 σC)
            (rX ((MSF) [FR]) (Ly).lab lblS (J1 σC) .abort) s c) [FR] s c fs) := by
  have hp : o.prog = SccCode.helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have hme' : (Ly).Λ.imms Scc.Sem.SrcSem.setupTerm "me" 0 = some (tcb0 (Ly).Λ) := hme
  exact Spike.Lib.A64.HelloPh.StartPlace.hello_start_wc_place hpw i hE hp hlo0
    Spike.Lib.A64.HelloPh.C0S.c0S_ctl (Spike.Lib.A64.HelloPh.C0S.placedSE_c0S hme') rfl hA13
    (Spike.Lib.WakeOSide.hro_W hpw i) (Spike.Lib.A64.HelloPh.C0S.cfacts_c0S hme')
    (Spike.Lib.A64.WakePh.StartPlaceLy.hfree_W hpw i hstat ls)
    hctr2
    (Spike.Lib.A64.WakePh.StartPlaceLy.hcT_W hpw i) hc rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hWe (Spike.Lib.A64.HelloPh.StartWcS.rdJH_run (fun _ _ h => h.1.1) Spike.Lib.A64.HelloPh.C0S.c0S_u)
    Spike.Lib.A64.HelloPh.StartWcS.rdJH_back hrd hloc hq hxa hret hPw

end Spike.Lib.A64.HelloPh.StartH0G

/--
info: 'Spike.Lib.A64.HelloPh.StartH0G.hello_start_wc_h0G' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartH0G.hello_start_wc_h0G

/-- info: 'Spike.Lib.A64.HelloPh.StartH0G.helloD_bounds' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartH0G.helloD_bounds
