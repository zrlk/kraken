/-
**`StartPlace0.hello_rd_place0` at hello's start choices, level 0** (AArch64, the twin of `A64HelloStartH0G`):
`StartH0G.hello_start_wc_h0G`'s choices and discharges (`c0S`, `helloSrc`,
`L0T`/`ls0T ls`, `cTW`, the take site, `frH c0S.env`, `rdJH`, `helloLsw`), up to rodata's landing only: the
segment's only exit is `wc_rodata`'s heap abort at `[FR]`. `helloLsw`'s bounds here: `288 ≤ 480`, `480 % 8 = 0`,
`480 ≤ 12288` (`decide`).

Left as premises: the loader's facts (`hpa`, `hhp`, `hlo0`, `hstat`, `hA13`, `hctr2`, `hc`), the
immediate `hme`, and the source/frame premises (`hWe`, `hrd`, `hloc`, `hq`; `hxa`, the allocator's
fresh-label landing in `ms [FR]`'s allocation fragment). No `hret`, `hPw` (level 1's).

- `hello_start_rd_h0G0`: the statement; its exit and `hxa` carry `TP (pinA + 8)` (L1-TP).
-/
import Spike.Lib.A64HelloStartPlace0
import Spike.Lib.A64HelloStartH0G
import Spike.Lib.A64HelloC0S
import Spike.Lib.A64WakeStartPlaceLy
import Spike.Lib.HelloGOf2H

namespace Spike.Lib.A64.HelloPh.StartH0G0

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
open Spike.Lib.A64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.DmemPriv (WordsNoneP)
open Spike.Lib (FragS Frag SegWS LocalRun)
open Spike.Lib.WakeLoadT (L0T ls0T tcb0)
open Spike.Lib.A64.HelloPh.C0S (c0S)
open Spike.Lib.HelloSrc (helloSrc)

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

/-- **From `_start` to `wc_rodata`'s heap abort at hello's start choices, level 0**: `StartPlace0.hello_rd_place0`
at `StartH0G.hello_start_wc_h0G`'s choices (`c0S`, `helloSrc`, `L0T`/`ls0T ls`, `cTW`, the take site,
`frH c0S.env`, `rdJH`, `helloLsw`), its leaf premises discharged from the loader's facts as there. -/
theorem hello_start_rd_h0G0 {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
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
    (hrd : ∀ v m0 σC, RdPreW (Spike.Lib.A64.Flow.WakeWc.tpG
        (UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)) fun s c => WP s c [FR]) KR (Ly).exe
      (Ly).endPc (mR (swR v (-helloLsw) 0))
      (mF (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v) m0 σC) ((MSF) [FR]) (mRdJ0 (J') σC) (J1 σC))
    (hloc : ∀ σC σ c, mRdJ0 (J') σC σ c → ∃ c', LocalRun helloSrc c c' ∧ J1 σC σ c')
    (hq : ∀ σC σ c, J1 σC σ c → ∃ q : Call, q.OK ((MSF) [FR]) (Ly).lab ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ((MSF) [FR]) = 3#64)
    (hxa : ∀ v m0 σC, ∀ q : AG ((MSF) [FR]) (Ly).lab, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v) m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Spike.Lib.A64.Flow.Abs (mR (swR v (-helloLsw) 0)) ⟨-48, []⟩ mC σ ∧
        (rN (Ly).lab (mRdJ0 (J') σC) (J1 σC) .call).J σ c ∧
        (Spike.Lib.A64.Alloc.N (Ly).lab ((MSF) [FR]) q.1 .e).J (enter (-48) σ) c ∧
        Spike.Lib.A64.Flow.CKept (mR (swR v (-helloLsw) 0)) (-48) (-160) 0 mC m) →
      ∀ l b w s c, lblS l = none →
        At (Ly).exe (Ly).endPc (aR (mR (swR v (-helloLsw) 0))) F' (Ea ((MSF) [FR]) q.1 l b w) s c →
        TP (UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)) s → ((MSF) [FR]).xa l b w s c) :
    SegWS (WP) KR helloSrc lblS (MSF)
      ((At (Ly).exe (Ly).endPc (entryR E) (fun m => FWN m ∧ Spike.Lib.A64Consumer.Pz RS m)
        (entryN (Ly).lab c0S)).at [])
      (Frag.at (fun s c => ∃ v m0 σC,
          At (Ly).exe (Ly).endPc (mR (swR v (-helloLsw) 0))
            (mF (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v) m0 σC)
            (rX ((MSF) [FR]) (Ly).lab lblS (J1 σC) .abort) s c ∧
          TP (UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)) s) [FR]) := by
  have hp : o.prog = SccCode.helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have hme' : (Ly).Λ.imms Scc.Sem.SrcSem.setupTerm "me" 0 = some (tcb0 (Ly).Λ) := hme
  exact Spike.Lib.A64.HelloPh.StartPlace0.hello_rd_place0 hpw i hE hp hlo0
    Spike.Lib.A64.HelloPh.C0S.c0S_ctl (Spike.Lib.A64.HelloPh.C0S.placedSE_c0S hme') rfl hA13
    (Spike.Lib.WakeOSide.hro_W hpw i) (Spike.Lib.A64.HelloPh.C0S.cfacts_c0S hme')
    (Spike.Lib.A64.WakePh.StartPlaceLy.hfree_W hpw i hstat ls)
    hctr2
    (Spike.Lib.A64.WakePh.StartPlaceLy.hcT_W hpw i) hc
    (by decide) (by decide) (by decide)
    hWe (Spike.Lib.A64.HelloPh.StartWcS.rdJH_run (fun _ _ h => h.1.1) Spike.Lib.A64.HelloPh.C0S.c0S_u)
    Spike.Lib.A64.HelloPh.StartWcS.rdJH_back hrd hloc hq hxa

end Spike.Lib.A64.HelloPh.StartH0G0

/--
info: 'Spike.Lib.A64.HelloPh.StartH0G0.hello_start_rd_h0G0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartH0G0.hello_start_rd_h0G0
