import WeakCore.TermPredHold
import WeakCore.TermPtrRtsDefs
import WeakCore.TermPlantIdxDefs
import WeakCore.TermUndefLowDefs
import WeakCore.TermOverCrDefs
import WeakCore.TermPoolDefs
import WeakCore.TermZwIni
import WeakCore.TermStepper
import WeakCore.TermOnce
import WeakCore.TermUndefZ
import WeakCore.TermOwnCohZ
import WeakCore.TermBoxZ

/-!
# TermMainDefs: the vocabulary of the headline-1 skeleton

`SysInvN`, the step contexts (`TCtx`, `EnvAt`, `TOut`, `EgT`, `PCtx`, `EgP`, …) that
`TermInterf` (S8c) and `TermMain` (`Obligations`, wiring, headline) share.
-/

namespace TermMain

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## The net key bound and the carried invariant -/

/-- The keys the types make exclusive: region tokens, region words, own
handles. -/
def ExclKey : Key → Prop
  | .rg _ => True
  | .wd _ => True
  | .own _ => True
  | _ => False

/-- **K-net**: per key, frames, private holdings and outstanding promise
credits of all threads plus the shared holding are at most one plus the
outstanding promise debits. -/
def KeyNet (c : Cfg) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res) (k : Key) : Prop :=
  ((List.range c.ths.size).map (fun i => (Tot i + HP i + pSumAt c i (cr i)) k)).sum + HS k ≤
    1 + ((List.range c.ths.size).map (fun i => pSumAt c i (db i) k)).sum

/-- (S10, rid freshness, net form) **Every held region id is used, up to
outstanding debits**, under the per-thread counters `rc` (`TermOnce.RidUsed`): at
`rg n`/`wd n` of an unused id `n`, frames, private holdings, credits and the shared
holding are at most the outstanding promise debits (`TermBal.KeyLoad ≤ TermBal.KeyDebt`;
`KeyNet` at bound `0`).  A planted or promised holding of a not-yet-minted id (P1's
`IexTok` pt3) is paid by its debit; preservation is `TermBal.ridT_N` / `ridP_N`. -/
def RidOK (c : Cfg) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res) (rc : Nat → Nat) : Prop :=
  ∀ n, ¬ TermOnce.RidUsed rc n → ∀ key : Key, (key = .rg n ∨ key = .wd n) →
    ((List.range c.ths.size).map (fun i => (Tot i + HP i + pSumAt c i (cr i)) key)).sum + HS key ≤
      ((List.range c.ths.size).map (fun i => pSumAt c i (db i) key)).sum

/-- (B4 PromTyOK (a0)) Every outstanding promise at a shared cell lies
at an initialised offset. -/
def PromIniOK (Eg : GEnv) (c : Cfg) : Prop :=
  ∀ (j : Nat) (th : TTh) (t : Ts) (m : Msg), c.ths[j]? = some th → t ∈ th.promises → c.mem[t]? = some m →
    ∀ cl, Eg.sto m.loc.label = some cl → Eg.Shared m.loc.label → InitR (PubE Eg) cl m.loc.label m.loc.offset

/-- (B4 PromTyOK (a)) Every outstanding promise at a shared cell is a
typed word of the cell in `PubE`. -/
def PromTyAOK (Eg : GEnv) (c : Cfg) : Prop :=
  ∀ (j : Nat) (th : TTh) (t : Ts) (m : Msg), c.ths[j]? = some th → t ∈ th.promises → c.mem[t]? = some m →
    ∀ cl, Eg.sto m.loc.label = some cl → Eg.Shared m.loc.label → WordOK (PubE Eg) cl.ty m.loc.offset (mw m)

/-- (H1 of `TermStoreNI.SeenHid`; the `HolderUniq`) **No outstanding promise is
`undef`**: every outstanding promise of every thread is a non-`undef` message
(kept by `TermPromNU.promNU_thread` / `promNU_prom`, certification). -/
def PromNotUndef (c : Cfg) : Prop :=
  ∀ (q : Nat) (thq : TTh) (t : Ts) (m : Msg), c.ths[q]? = some thq → t ∈ thq.promises → c.mem[t]? = some m →
    m.val ≠ .undef

/-- (B4 PromTyOK (c) at every cell; B5) **No outstanding promise lies on a word
of a two-word unit of its cell** (kept by `TermB5.promNoTwoOK_thread` /
`promNoTwoOK_promise`, certification). -/
def PromNoTwoOK (Eg : GEnv) (c : Cfg) : Prop :=
  ∀ (j : Nat) (th : TTh) (t : Ts) (m : Msg) (cl : Cell), c.ths[j]? = some th → t ∈ th.promises →
    c.mem[t]? = some m → Eg.sto m.loc.label = some cl → ∀ o, TwoAtT cl.ty o →
      m.loc.offset ≠ o ∧ m.loc.offset ≠ o + 1

/-- (S10, T20b2) **No own-handle key of a not-yet-allocated fresh label is held**: at every thread
`q`'s fresh label `freshLabel lbase n q j` with `q.nalloc ≤ j`, the own key has zero load in frames,
holdings and credits (kept by `TermOwnFresh.ownFresh_thread` / `ownFresh_prom`; what
`TermOwnFresh.mintRoomF_at` needs). -/
def OwnFreshZ (c : Cfg) (Tot HP : Nat → Res) (HS : Res) (cr : Nat → Ts → Res) : Prop :=
  ∀ (q : Nat) (thq : TTh) (j : Nat), c.ths[q]? = some thq → thq.nalloc ≤ j →
    (∀ n, n < c.ths.size → (Tot n + HP n + pSumAt c n (cr n)) (.own (freshLabel c.lbase c.n q j)) = 0) ∧
      HS (.own (freshLabel c.lbase c.n q j)) = 0

/-- (replaces the `ObligationsF` field `plantClos`) **Promise closure**: an outstanding promise
of `j` at a cell of `j`'s cut (`GEnv.InCut`) whose type holds no `own` or region reference
(`noOwnIn`, `rgnFree`), whose value names one of `j`'s cells, names a cell with a frontier (the
plant of `TermPlantF.plantOf` fired at the promise; kept by `TermPromClos.promClos_thread` /
`promClos_prom`). -/
def PromClosG (Eg : GEnv) (c : Cfg) : Prop :=
  ∀ (j : Nat) (th : TTh) (t : Ts) (m : Msg), c.ths[j]? = some th → t ∈ th.promises → c.mem[t]? = some m →
    ∀ (a' : Address) (g : Nat), m.val = .loc a' g → ∀ cl, Eg.sto a'.label = some cl → cl.owner = some j →
      ∀ cm, Eg.sto m.loc.label = some cm → (cm.owner = some j ∨ Eg.Shared m.loc.label) →
        Ty.noOwnIn [] cm.ty = true → rgnFree cm.ty = true → ∃ f, Eg.pfr a'.label = some f

/-- What an outstanding promise of `i` may name (the conclusion of `FgnPromClosG`): a cell
with a frontier, a cell of `i`, a box, or one of `i`'s labels holding no cell yet. -/
def TgtOK (Eg : GEnv) (c : Cfg) (i : Nat) (l : AllocLabel) : Prop :=
  (∃ f, Eg.pfr l = some f) ∨ (∃ cl, Eg.sto l = some cl ∧ cl.owner = some i) ∨ (∃ B, Eg.box l = some B) ∨
    ∃ n, l = freshLabel c.lbase c.n i n ∧ Eg.sto l = none

/-- **Foreign promise closure**: an outstanding promise of `i` at a cell of a `noOwnIn`/`rgnFree`
type whose value is a pointer names a target `TgtOK` (`TermFgnClos.fgnClos_thread` /
`fgnClos_prom` keep it; `fgnClos_use` is the consumer form). -/
def FgnPromClosG (Eg : GEnv) (c : Cfg) : Prop :=
  ∀ (i : Nat) (th : TTh) (t : Ts) (m : Msg), c.ths[i]? = some th → t ∈ th.promises → c.mem[t]? = some m →
    ∀ (a' : Address) (g : Nat), m.val = .loc a' g → ∀ cm, Eg.sto m.loc.label = some cm →
      Ty.noOwnIn [] cm.ty = true → rgnFree cm.ty = true → TgtOK Eg c i a'.label

/-- (K1a, D-B) **Foreign promise closure at counted slots**: an outstanding promise of `i` at a
single-word counted slot of a cell of Σ whose value is a pointer names a target `TgtOK`
(`TermFgnCnt.fgnCnt_thread` / `fgnCnt_prom` keep it; read by `TermMemRtsProm.noCnt_unpl`). -/
def FgnPromCntG (Eg : GEnv) (c : Cfg) : Prop :=
  ∀ (i : Nat) (th : TTh) (t : Ts) (m : Msg), c.ths[i]? = some th → t ∈ th.promises → c.mem[t]? = some m →
    ∀ (a' : Address) (g : Nat), m.val = .loc a' g → ∀ cm, Eg.sto m.loc.label = some cm →
      TermPtrRts.NotSnd cm.ty m.loc.offset → TermPtrRts.CntOK cm.ty m.loc.offset (mw m) → TgtOK Eg c i a'.label

/-- **Cells holding a message, and shared cells, have a live owner or are shared**
(`TermCellOwn.cellOwn_thread` / `cellOwn_prom` keep it; `cellOwn_use` is the consumer form). -/
def CellOwnerLiveM (Eg : GEnv) (c : Cfg) : Prop :=
  ∀ l cl, Eg.sto l = some cl → ((∃ (t : Nat) (m : Msg), c.mem[t]? = some m ∧ m.loc.label = l) ∨ Eg.Shared l) →
    (∀ i, cl.owner = some i → i < c.ths.size) ∧ (cl.owner = none → Eg.Shared l)

/-- (B2, ownPub) **Own-handle keys sit with the owner**: a thread's frame carries `own l` only for a
label outside Σ or a cell it owns (holdings: `TermOwnKey.MemHeldOn_ownL`, by typing). -/
def OwnKeyOwnG (c : Cfg) (Eg : GEnv) (Tot : Nat → Res) : Prop :=
  ∀ (j : Nat) (th : TTh) (l : AllocLabel), c.ths[j]? = some th → Tot j (.own l) ≠ 0 →
    Eg.sto l = none ∨ ∃ cl, Eg.sto l = some cl ∧ cl.owner = some j

/-- (B2, ownPub) **No own key of a published cell**: a label `GEnv.pubd` marks has a frontier, and,
in Σ, no frame, private holding or shared holding carries its own key. -/
def OwnPubG (c : Cfg) (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) : Prop :=
  ∀ l : AllocLabel, Eg.pubd l → Eg.pfr l ≠ none ∧ (Eg.sto l ≠ none →
    (∀ (j : Nat) (th : TTh), c.ths[j]? = some th → (Tot j + HP j) (.own l) = 0) ∧ HS (.own l) = 0)

/-- (StoNI) **Every cell type is `∀`-free at value positions** (`noIallV`): cells are created
only by `new`/`newBuf`, whose types the program's scope check keeps `∀`-free. -/
def StoNI (Eg : GEnv) : Prop := ∀ l cl, Eg.sto l = some cl → TermTv.noIallV cl.ty = true

/-- (msgWords) **Every message's offset lies within its cell's words** (`InWords`). -/
def MsgWordsG (Eg : GEnv) (c : Cfg) : Prop :=
  ∀ (t : Nat) (m : Msg) (cl : Cell), c.mem[t]? = some m → Eg.sto m.loc.label = some cl →
    TermStep.InWords cl.ty m.loc.offset

/-- (E2) A thread's box, once it has one, is a published zero-word cell. -/
def TidBox (Eg : GEnv) (th : TTh) : Prop :=
  ∀ l, th.tidLbl = some l → Eg.sto l = some ⟨.unit, none⟩ ∧ Eg.pfr l = some 0

/-- **`SysInvW` with net key bounds** (the invariant carried along runs). -/
structure SysInvN (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : Res) (MintOK : Res → Prop)
    (c : Cfg) (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res) : Prop where
  thr : ∀ i th, c.ths[i]? = some th →
    ThSys p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i)
  held : MemHeldG Eg c HS
  clo : GStoClo Eg
  cmg : GStoMg Eg
  shty : SharedTyOK Eg
  proms : PromsOK Eg c
  fpok : ∀ i th (S : AllocLabel → Prop), c.ths[i]? = some th → FpOK (Cut Eg i S) (stOf c.mem c.pairs th)
  fresh : ∀ i th, c.ths[i]? = some th → ∀ j, th.nalloc ≤ j →
    GFreshL Eg c th (freshLabel c.lbase c.n i j)
  bal : ∃ M, MintOK M ∧
    thSum c.ths.size (fun i => Tot i + pSumAt c i (cr i) + HP i) + HS ≤
      Init + M + thSum c.ths.size (fun i => pSumAt c i (db i))
  knet : ∀ key, ExclKey key → KeyNet c Tot HP HS cr db key
  bf : c.boxFence = true
  boxtop : BoxTopG Eg c
  disj : PromsDisj c
  fpfree : FpOwnFree Eg c
  plt : AllPromLt c
  vwr : VWrLe c
  frle : FrontierLe Eg c.mem.size
  rle : ∀ l, Eg.rini l ≤ Eg.ini l
  /-- (ZwIni) at an unpublished frontier buffer of inhabited zero-width elements, `ini` covers
  every slot (`TermZwIni.ZwIniG`; BH1's zero-width case, `TermPlantWin.bh1_of`). -/
  zwIni : TermZwIni.ZwIniG Eg
  /-- (PredHolder; BH2′ of `bufInitHeld`) at a predicted unit of an unpublished own cell the first
  write is an outstanding own promise (`TermPredHold.PredHoldG`; `TermPredHoldP` keeps it). -/
  predHold : TermPredHold.PredHoldG Eg c
  bnamed : GBoxNamed Eg
  /-- (S10) every held region id is used (rid freshness, `RidOK`). -/
  rid : ∃ rc, RidOK c Tot HP HS cr db rc
  /-- (B4 PromTyOK (a0), B3) every outstanding promise at a shared cell lies at an initialised offset. -/
  promIni : PromIniOK Eg c
  /-- (B4 PromTyOK (a), B3) every outstanding promise at a shared cell is a typed word of its cell. -/
  promTy : PromTyAOK Eg c
  /-- (H1) no outstanding promise is `undef` (`PromNotUndef`). -/
  promNU : PromNotUndef c
  /-- (S10, T20b2) no own key of a not-yet-allocated fresh label is held (`OwnFreshZ`). -/
  ownF : OwnFreshZ c Tot HP HS cr
  /-- (B4 PromTyOK (c), B5) no outstanding promise lies on a word of a two-word unit (`PromNoTwoOK`). -/
  promNoTwo : PromNoTwoOK Eg c
  /-- (T3c, replaces `FrontW` of `seenFacts`) every protocol-word unit of every cell has an `undef`
  message, its allocation placeholder (`TermUndefZ.UndefAtG`; `TermUndefInv` keeps it). -/
  undefAt : TermUndefZ.UndefAtG Eg c.mem
  /-- (B2) own-handle keys sit with the owner (`OwnKeyOwnG`). -/
  ownKeyOwn : OwnKeyOwnG c Eg Tot
  /-- (B2) no own key of a published cell (`OwnPubG`). -/
  ownPub : OwnPubG c Eg Tot HP HS
  /-- (box L1) a box payload reference's view is below its box's frontier (`TermBoxZ.BoxPV`;
  thread steps: `TermBoxPV.boxPV_thread`). -/
  boxPV : TermBoxZ.BoxPV Eg
  /-- (box L2) a box's frontier is at most its owner's `vWr` (`TermBoxOwn.boxFrOwnT_of`). -/
  boxFrOwn : TermBoxZ.BoxFrOwn Eg c
  /-- (box Ln) every box's frontier is at most the memory size (`TermBoxOwn.boxFrLeT_of`). -/
  boxFrLe : TermBoxZ.BoxFrLe Eg c.mem.size
  /-- (T.pay) every thread's `vWr` is at most the last timestamp (`TermVwrLt.VWrLtT_of`). -/
  vwrLt : ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → th.vs.vWr ≤ c.mem.size - 1
  /-- (T.pay `hLn`) every box's frontier is at most the last timestamp (`TermVwrLt.boxFrLtT_of`). -/
  boxFrLt : TermBoxZ.BoxFrLe Eg (c.mem.size - 1)
  /-- (frlt, (2′) L437) every frontier of a cell is at most the last timestamp (strict `frle`;
  thread steps: `FrontierLt_post`). -/
  frlt : FrontierLe Eg (c.mem.size - 1)
  /-- (box L3) a box payload reference to an unpublished cell names a cell of the box's owner
  (`TermBoxOwn.payOwnT_of`). -/
  payOwn : TermBoxZ.PayOwn Eg
  /-- Box labels hold no cell (`TermBoxOwn.boxStoT_of`). -/
  boxSto : TermBoxZ.BoxSto Eg
  /-- (N16, formerly the `ObligationsF` field `ownCohInv`) at every own private cell of every
  thread, its coherence is at most its `vWr` (`TermOwnCohZ.OwnCohZ` = `TermCohLe.OwnCohInv`;
  `TermOwnCoh` keeps it). -/
  ownCoh : ∀ i th (S : AllocLabel → Prop), c.ths[i]? = some th →
    TermOwnCohZ.OwnCohZ (Cut Eg i S) (stOf c.mem c.pairs th)
  /-- ((i′) seed) past the real count, every non-promise message at or below an own buffer's
  frontier is the allocation placeholder (`TermTyped.RiniCoh`; `TermRiniCoh` keeps it). -/
  riniCoh : ∀ i th (S : AllocLabel → Prop), c.ths[i]? = some th →
    TermTyped.RiniCoh (Cut Eg i S) (stOf c.mem c.pairs th)
  /-- every outstanding promise of a thread at a cell of Σ lies in its cut: its own cell or a
  shared one (`TermPtrStab.PromInCut`; `promInCut_threadT` / `promInCut_prom` keep it). -/
  promInCut : TermPtrStab.PromInCut Eg c
  /-- (formerly the `ObligationsF` field `plantClos`) promise closure (`PromClosG`). -/
  promClos : PromClosG Eg c
  /-- (StoNI) every cell type is `∀`-free at value positions (`StoNI`). -/
  stoNI : StoNI Eg
  /-- at a single-word unit of a cell, a defined message is never followed by an `undef` one
  (`TermUndefLow.UndefLowG`; kept by `undefLow_thread` (typing, layout, `PromAllocF`) and
  `undefLow_prom` (`promNU`)). -/
  undefLow : TermUndefLow.UndefLowG Eg c.mem
  /-- every thread's outstanding promises lie above its coherence (`PromAboveG`; kept by
  certification of the stepper, `TermPromAboveG.promAboveG_step`). -/
  promAbove : TermOverCr.PromAboveG c
  /-- (msgWords) every message lies within its cell's words (`MsgWordsG`). -/
  msgWords : MsgWordsG Eg c
  /-- foreign promise closure (`FgnPromClosG`; `TermFgnClos.fgnClos_thread` (`PromAllocF`) /
  `fgnClos_prom` (`CertRunP`) keep it). -/
  fgnClos : FgnPromClosG Eg c
  /-- cells holding a message, and shared cells, have a live owner or are shared
  (`CellOwnerLiveM`; `TermCellOwn.cellOwn_thread` / `cellOwn_prom` keep it). -/
  cellOwn : CellOwnerLiveM Eg c
  /-- (D-B, v3c) the rts package: (M)+(R) at gated cells, `LblSto`, `GateTmin`, counted-slot (M)
  (`TermPtrStab.ptrRtsGL_prom` / `TermPtrRtsK.ptrRtsGL_thread` keep it). -/
  ptrGL : k.storeDepRts = true → TermPtrRts.PtrRtsGL Eg Tot HP c
  /-- (D-B, v3c) granules are written whole (`GranuleW`), at every configuration with a thread
  (`TermPtrRtsK.granuleW_prom` / `TermGranStep.granuleW_stepNF` keep it). -/
  granW : k.storeDepRts = true → c.ths.size = 0 ∨ TermPtrRts.GranuleW Eg.sto c.mem c.pairs
  /-- (D-B) every cell type is laid out (`LayT`; `TermPtrRtsK.stoLay_thread` / `stoLay_egP`). -/
  stoLay : k.storeDepRts = true → ∀ l cl, Eg.sto l = some cl → LayT cl.ty
  /-- (D-B) box payloads naming a gated cell are below its frontier or carried at indices
  `≥ tmin` (`TermPtrRtsK.boxPlantSep_prom` / `boxPlantSep_thread` keep it). -/
  boxPlantSep : k.storeDepRts = true → TermPtrRts.BoxPlantSep Eg Tot HP c
  /-- (D-B, K1a) foreign promises at counted slots name `TgtOK` targets (`FgnPromCntG`). -/
  fgnCnt : k.storeDepRts = true → FgnPromCntG Eg c
  /-- (pool) **Pool credits** `pl`: tagged (`PoolTag`), with the own-frontier cover, balance, net keys and
  rid freshness at credits plus pool `crPl cr pl` (the body of `TermPoolStaging.PoolInv`). -/
  pool : ∃ pl : Nat → Ts → Res, TermPool.PoolTag Eg c pl ∧ TermOverCr.OverCrG Eg c (TermPool.crPl cr pl) ∧
    (∃ M, MintOK M ∧ thSum c.ths.size (fun i => Tot i + pSumAt c i (TermPool.crPl cr pl i) + HP i) + HS ≤
      Init + M + thSum c.ths.size (fun i => pSumAt c i (db i))) ∧
    (∀ key, ExclKey key → KeyNet c Tot HP HS (TermPool.crPl cr pl) db key) ∧
    (∃ rc, RidOK c Tot HP HS (TermPool.crPl cr pl) db rc)
  /-- (under `storeDepRts`) the plant-index clause: at an own frontier cell whose own key the
  owner still holds (`KeyG`), the least outstanding plant-edge promise (`tminG`) lies at or above
  `vWr`, below the footprint, with only own promises or `≤ coh` messages below it
  (`TermPlantAtT.PlantIdxG`; kept by `TermPlantAtJ.plantIdx_thread` / `plantIdx_prom`). -/
  plantIdx : k.storeDepRts = true → TermPlantAtT.PlantIdxG TermPtrRts.tminG Eg Tot HP c
  /-- every thread's coherence views name messages at their addresses (`TermLiveProps.CfgCoh`;
  kept by `threadSteps_coh` / `promise_coh`). -/
  cfgCoh : TermLiveProps.CfgCoh c
  /-- (A1 stoW) every cell type is `wrapTop` (`EFoot`: a new cell's type, by
  `CkW_newCell` / `CkW_newBufCell`; `InitOK` at the start). -/
  stoW : ∀ l cl, Eg.sto l = some cl → TermA4.wrapTop cl.ty = true
  /-- (2b, freshU) unborn stripes are fresh and unowned (`TermFreshU`); vacuous when `n ≤ ths.size`. -/
  freshU : FreshU c.n Eg c Tot HP HS cr
  /-- (E2) every thread's `ThreadId` box, once allocated, is a published zero-word cell (`TidBox`). -/
  tidBox : ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → TidBox Eg th

def SysInvNx (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : Res) (MintOK : Res → Prop) (c : Cfg) : Prop :=
  ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
    SysInvN p k arch Init MintOK c Eg Tot HP HS cr db

/-- No thread has an outstanding promise. -/
def AllNoProm (c : Cfg) : Prop := ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → th.promises = []

theorem pSumAt_zero {c : Cfg} (h : AllNoProm c) (i : Nat) (f : Ts → Res) (key : Key) :
    pSumAt c i f key = 0 := by
  unfold pSumAt
  cases e : c.ths[i]? with
  | none => rfl
  | some th =>
    show Res.sum ((stOf c.mem c.pairs th).promises.map f) key = 0
    have : (stOf c.mem c.pairs th).promises = [] := h i th e
    rw [this]
    rfl

theorem sum_map_congr {f g : Nat → Nat} : ∀ (l : List Nat), (∀ i, f i = g i) → (l.map f).sum = (l.map g).sum
  | [], _ => rfl
  | a :: l, h => by simp only [List.map_cons, List.sum_cons, h a, sum_map_congr l h]

theorem sum_map_zero : ∀ (l : List Nat), (l.map fun _ => (0 : Nat)).sum = 0
  | [] => rfl
  | _ :: l => by simp only [List.map_cons, List.sum_cons, sum_map_zero l]

/-- Without outstanding promises the net bound is the gross one (`KeySum`). -/
theorem keyNet_gross {c : Cfg} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {key : Key}
    (hn : AllNoProm c) (h : KeyNet c Tot HP HS cr db key) :
    KeySum c.ths.size (fun i => Tot i + HP i) HS key := by
  unfold KeyNet at h
  unfold KeySum
  rw [sum_map_congr _ (fun i => by rw [Res.add_apply, pSumAt_zero hn i (cr i) key, Nat.add_zero]),
    sum_map_congr _ (fun i => pSumAt_zero hn i (db i) key), sum_map_zero] at h
  exact h

/-- And conversely. -/
theorem gross_keyNet {c : Cfg} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {key : Key}
    (hn : AllNoProm c) (h : KeySum c.ths.size (fun i => Tot i + HP i) HS key) :
    KeyNet c Tot HP HS cr db key := by
  unfold KeyNet
  unfold KeySum at h
  rw [sum_map_congr _ (fun i => by rw [Res.add_apply, pSumAt_zero hn i (cr i) key, Nat.add_zero]),
    sum_map_congr _ (fun i => pSumAt_zero hn i (db i) key), sum_map_zero]
  omega

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
  {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}

/-- **At a promise-free configuration `SysInvN` is `SysInvW`** (gross key
bounds, so `tokUniq`/`wdUniq`/`ownUniq`). -/
theorem SysInvN.toW (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hn : AllNoProm c) :
    SysInvW p k arch Init MintOK c Eg Tot HP HS cr db :=
  ⟨h.thr, h.held, h.clo, h.cmg, h.shty, h.proms, h.fpok, h.fresh, h.bal,
    fun n => keyNet_gross hn (h.knet (.rg n) trivial), fun n => keyNet_gross hn (h.knet (.wd n) trivial),
    fun l => keyNet_gross hn (h.knet (.own l) trivial), h.bf, h.boxtop, h.disj, h.fpfree, h.plt, h.vwr,
    h.frle, h.rle, h.bnamed, h.freshU⟩

theorem SysInvW.toN (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) (hn : AllNoProm c)
    (hr : ∃ rc, RidOK c Tot HP HS cr db rc) (hof : OwnFreshZ c Tot HP HS cr) (hu : TermUndefZ.UndefAtG Eg c.mem)
    (hoc : ∀ i th (S : AllocLabel → Prop), c.ths[i]? = some th → TermOwnCohZ.OwnCohZ (Cut Eg i S) (stOf c.mem c.pairs th))
    (hbx : ∀ l, Eg.box l = none) (hkw : OwnKeyOwnG c Eg Tot) (hop : OwnPubG c Eg Tot HP HS)
    (hni : StoNI Eg) (hul : TermUndefLow.UndefLowG Eg c.mem) (hzw : TermZwIni.ZwIniG Eg) (hph : TermPredHold.PredHoldG Eg c)
    (hvl : ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → th.vs.vWr ≤ c.mem.size - 1)
    (hmw : MsgWordsG Eg c) (hmem0 : c.mem = #[]) (hpf0 : ∀ l, Eg.pfr l = none)
    (hlb : TermPtrRts.LblSto Eg c) (hly : ∀ l cl, Eg.sto l = some cl → LayT cl.ty)
    (hcc : TermLiveProps.CfgCoh c) (hsw : (∀ l cl, Eg.sto l = some cl → TermA4.wrapTop cl.ty = true))
    (htb : ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → TidBox Eg th) :
    SysInvN p k arch Init MintOK c Eg Tot HP HS cr db where
  tidBox := htb
  thr := h.thr
  held := h.held
  clo := h.clo
  cmg := h.cmg
  shty := h.shty
  proms := h.proms
  fpok := h.fpok
  fresh := h.fresh
  bal := h.bal
  knet := fun key hk => by
    cases key with
    | rg n => exact gross_keyNet hn (h.tok n)
    | wd n => exact gross_keyNet hn (h.wd n)
    | own l => exact gross_keyNet hn (h.own l)
    | _ => exact hk.elim
  bf := h.bf
  boxtop := h.boxtop
  disj := h.disj
  fpfree := h.fpfree
  plt := h.plt
  vwr := h.vwr
  frle := h.frle
  rle := h.rle
  zwIni := hzw
  predHold := hph
  bnamed := h.bnamed
  rid := hr
  promIni := fun j th t m hj ht => by rw [hn j th hj] at ht; cases ht
  promTy := fun j th t m hj ht => by rw [hn j th hj] at ht; cases ht
  promNU := fun j th t m hj ht => by rw [hn j th hj] at ht; cases ht
  ownF := hof
  promNoTwo := fun j th t m cl hj ht => by rw [hn j th hj] at ht; cases ht
  undefAt := hu
  ownKeyOwn := hkw
  ownPub := hop
  boxPV := TermBoxZ.boxPV_none hbx
  boxFrOwn := TermBoxZ.boxFrOwn_none hbx
  boxFrLe := TermBoxZ.boxFrLe_none hbx
  vwrLt := hvl
  boxFrLt := TermBoxZ.boxFrLe_none hbx
  frlt := fun l _ f _ hf => by rw [hpf0 l] at hf; cases hf
  payOwn := TermBoxZ.payOwn_none hbx
  boxSto := TermBoxZ.boxSto_none hbx
  ownCoh := hoc
  riniCoh := fun _ _ _ _ _ _ _ _ _ _ f _ _ _ _ hpf => by
    change Eg.pfr _ = some f at hpf; rw [hpf0] at hpf; cases hpf
  promClos := fun j th t m hj ht => by rw [hn j th hj] at ht; cases ht
  promInCut := fun j th t m hj ht => by rw [hn j th hj] at ht; cases ht
  stoNI := hni
  msgWords := hmw
  fgnClos := fun i th t m hi ht => by rw [hn i th hi] at ht; cases ht
  cellOwn := fun l cl _ hg => by
    rcases hg with ⟨t, m, hm, _⟩ | ⟨f, hf⟩
    · rw [hmem0] at hm
      cases hm
    · rw [hpf0 l] at hf
      cases hf
  undefLow := hul
  promAbove := fun j th hj t ht => by
    have ht' : t ∈ th.promises := ht
    rw [hn j th hj] at ht'
    cases ht'
  ptrGL := fun _ => ⟨fun _ _ a _ _ _ _ _ hf => absurd hf (by rw [hpf0 a]; exact fun h => by cases h), hlb,
    fun _ a _ _ _ _ hf => absurd hf (by rw [hpf0 a]; exact fun h => by cases h),
    fun _ _ a _ _ _ _ _ hf => absurd hf (by rw [hpf0 a]; exact fun h => by cases h)⟩
  granW := fun _ => by
    cases hth : c.ths[0]? with
    | none => exact Or.inl (Nat.le_zero.1 (Array.getElem?_eq_none_iff.1 hth))
    | some th =>
      obtain ⟨S, -, -, hm, -⟩ := h.thr 0 th hth
      have hq : ∀ q, q ∈ c.pairs → False := fun q hq => by
        have h1 : q + 1 < c.mem.size := hm.1.2.2 q hq
        rw [hmem0] at h1
        exact Nat.not_lt_zero _ h1
      refine Or.inr ⟨fun q h1 => (hq q h1).elim, fun q h1 => (hq q h1).elim, fun q h1 => (hq q h1).elim,
        fun v mv _ _ hv => ?_⟩
      rw [hmem0] at hv
      simp at hv
  stoLay := fun _ => hly
  boxPlantSep := fun _ l B hB => by rw [hbx l] at hB; cases hB
  fgnCnt := fun _ i th t m hi ht => by rw [hn i th hi] at ht; cases ht
  pool := ⟨fun _ _ => .zero, TermPool.poolTag_zero _ _ hn, fun _ _ _ _ _ _ _ _ hpf => absurd (hpf0 _) hpf,
    by rw [TermPool.crPl_zero]; exact h.bal,
    by
      rw [TermPool.crPl_zero]
      intro key hk
      cases key with
      | rg n => exact gross_keyNet hn (h.tok n)
      | wd n => exact gross_keyNet hn (h.wd n)
      | own l => exact gross_keyNet hn (h.own l)
      | _ => exact hk.elim,
    by rw [TermPool.crPl_zero]; exact hr⟩
  plantIdx := fun _ => TermPlantAtT.plantIdx_none hpf0
  cfgCoh := hcc
  stoW := hsw
  freshU := h.freshU

/-- The stepper's fresh labels are blank (`SysInvW.gfresh` for `SysInvN`). -/
theorem SysInvN.gfresh (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat} {th : TTh}
    (hth : c.ths[i]? = some th) (n' : Nat) : GFreshE (gOf p k arch c i) Eg th.nalloc n' := by
  rintro l ⟨j, hj, -, rfl⟩
  obtain ⟨h1, h2, -, h4, -⟩ := h.fresh i th hth j hj
  exact ⟨h1, h2, h4⟩

end

/-! ## Step contexts -/

/-- Pointwise update of a per-thread family. -/
def upd {α : Type} (f : Nat → α) (i : Nat) (x : α) : Nat → α := fun j => if j = i then x else f j

theorem upd_self {α : Type} (f : Nat → α) (i : Nat) (x : α) : upd f i x i = x := by simp [upd]
theorem upd_other {α : Type} (f : Nat → α) {i j : Nat} (x : α) (h : j ≠ i) : upd f i x j = f j := by
  simp [upd, h]

/-- (D1) The credits after a thread step of `i`: `i`'s new credits `cr'`, and the
transfer `δ` added to every other thread's. -/
def updD (cr : Nat → Ts → Res) (i : Nat) (cr' δ : Ts → Res) : Nat → Ts → Res :=
  fun j => if j = i then cr' else fun t => cr j t + δ t

theorem updD_self (cr : Nat → Ts → Res) (i : Nat) (cr' δ : Ts → Res) : updD cr i cr' δ i = cr' := by
  simp [updD]

theorem updD_other (cr : Nat → Ts → Res) {i j : Nat} (cr' δ : Ts → Res) (h : j ≠ i) :
    updD cr i cr' δ j = fun t => cr j t + δ t := by
  simp [updD, h]

theorem updD_zero (cr : Nat → Ts → Res) (i : Nat) (cr' : Ts → Res) :
    updD cr i cr' (fun _ => .zero) = upd cr i cr' := by
  funext j t
  by_cases h : j = i
  · simp [updD, upd, h]
  · simp only [updD, upd, h, ite_false, Res.add_zero]

/-- **A thread step of thread `i` from a reachable configuration**: `c` is
reached from `c0`, satisfies `SysInvN` with the given witnesses, and steps by
`tstep` result `r` of `i` to `c'`, after which `i` is certified. -/
structure TCtx (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : Res) (MintOK : Res → Prop) (c0 c c' : Cfg)
    (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res) (i : Nat) (th : TTh)
    (r : Memory × List Ts × TTh) : Prop where
  run : TermStep.Steps p k arch c0 c
  inv : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db
  hth : c.ths[i]? = some th
  hr : r ∈ tstep (gOf p k arch c i) c.mem c.pairs th
  hc' : c' ∈ threadSteps p k arch c i
  e1 : c'.mem = r.1
  e2 : c'.pairs = r.2.1
  e3 : c'.ths[i]? = some r.2.2
  ho : ∀ j, j ≠ i → c'.ths[j]? = c.ths[j]?
  cert : Certified p k arch c' i

/-- (spawn) **`TCtx` over runs with an extra relation `Sp`** (`Sp := Spawn …` for runs with spawns,
`Sp := ⊥` for the old finals): identical except `run`. -/
structure TCtxX (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 c c' : Cfg)
    (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res) (i : Nat) (th : TTh)
    (r : Memory × List Ts × TTh) : Prop where
  run : TermSpawnStep.StepsG p k arch Sp c0 c
  inv : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db
  hth : c.ths[i]? = some th
  hr : r ∈ tstep (gOf p k arch c i) c.mem c.pairs th
  hc' : c' ∈ threadSteps p k arch c i
  e1 : c'.mem = r.1
  e2 : c'.pairs = r.2.1
  e3 : c'.ths[i]? = some r.2.2
  ho : ∀ j, j ≠ i → c'.ths[j]? = c.ths[j]?
  cert : Certified p k arch c' i

/-- The bridge: a context over a spawn-free run is one over a run with any `Sp`. -/
theorem TCtx.toX {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop} {Init : Res}
    {MintOK : Res → Prop} {c0 c c' : Cfg}
    {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh}
    {r : Memory × List Ts × TTh} (X : TCtx p k arch Init MintOK c0 c c' Eg Tot HP HS cr db i th r) :
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r :=
  ⟨TermSpawnStep.StepsG.ofSteps X.run, X.inv, X.hth, X.hr, X.hc', X.e1, X.e2, X.e3, X.ho, X.cert⟩

/-- At `Sp := ⊥` a context is an old one. -/
theorem TCtxX.toBot {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 c c' : Cfg}
    {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh}
    {r : Memory × List Ts × TTh} (X : TCtxX p k arch (fun _ _ => False) Init MintOK c0 c c' Eg Tot HP HS cr db i th r) :
    TCtx p k arch Init MintOK c0 c c' Eg Tot HP HS cr db i th r :=
  ⟨TermSpawnStep.StepsG.toSteps_bot X.run, X.inv, X.hth, X.hr, X.hc', X.e1, X.e2, X.e3, X.ho, X.cert⟩

#print axioms TCtx.toX
#print axioms TCtxX.toBot

/-- The stepping thread's typing at its cut (what `SysInvW.env` exposes). -/
def EnvAt (p : Prog) (Eg : GEnv) (i : Nat) (th : TTh) (Tot : Res) (S : AllocLabel → Prop) (ρ : Nat → Nat)
    (η : TEnv) (cx : Cx) (Rf Rs : Res) : Prop :=
  CE η = Cut Eg i S ∧ η.tid = i ∧ EnvOK p η ∧ TypedK p η cx th.term ∧ TvOK cx ∧
    FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧ Rf + Rs = Tot

/-- (D1) **What the cross-thread credit transfer `δ` of a thread step may do**:
it pays only foreign promises (the step's footprint `η.fp`), never one of the
stepping thread's own.  (adds the per-idle-thread planted-piece clause.) -/
def CrShift (η : TEnv) (s : St) (δ : Ts → Res) : Prop :=
  (∀ t, δ t ≠ .zero → t ∈ η.fp) ∧ ∀ t, δ t ≠ .zero → t ∉ s.promises

theorem CrShift_zero (η : TEnv) (s : St) : CrShift η s (fun _ => .zero) :=
  ⟨fun _ h => absurd rfl h, fun _ h => absurd rfl h⟩

/-- **The plant-credit transfer at a thread step of `i`** from `c` to `c'`
(post-step global environment `Eg'`): every nonzero `δ t` goes to a promise
`t` of an idle thread `j ≠ i`, and together with `t`'s old credit `cr j t` is a
key-free plant credit of `t` at every cut of `j` after the step (H8). -/
def CrShiftP (c c' : Cfg) (Eg' : GEnv) (cr : Nat → Ts → Res) (i : Nat) (δ : Ts → Res) : Prop :=
  ∀ t, δ t ≠ .zero → ∃ j thj m, j ≠ i ∧ c.ths[j]? = some thj ∧ t ∈ thj.promises ∧
    c'.mem[t]? = some m ∧ ∀ (Sj : AllocLabel → Prop) thj', c'.ths[j]? = some thj' →
      PlantCr (Cut Eg' j Sj) (stOf c'.mem c'.pairs thj') m t (cr j t + δ t) ∧
        TermPlant.CrKeys (cr j t + δ t)

theorem CrShiftP_zero (c c' : Cfg) (Eg' : GEnv) (cr : Nat → Ts → Res) (i : Nat) :
    CrShiftP c c' Eg' cr i (fun _ => .zero) := fun _ h => absurd rfl h

theorem Res.sum_map_zero' {α : Type} : ∀ (L : List α), Res.sum (L.map (fun _ => Res.zero)) = .zero
  | [] => rfl
  | _ :: L => by simp only [List.map_cons, Res.sum_cons, Res.sum_map_zero' L, Res.zero_add]

/-- **What `tstepMCF_step` returns** for result `r`, with the new holding split
into its private and shared parts at the S6 witness `E'`.  (D1) The last two
conjuncts: the transfer `δ` to idle threads' credits (`CrShift`), paid out of
the step's inequality (`Res.sum (Fd.map δ)` on its left, for a list `Fd`
covering `δ`'s support, e.g. a duplicate-free copy of `η.fp`). -/
def TOut (p : Prog) (g : G) (η : TEnv) (s : St) (r : Memory × List Ts × TTh) (E' : TEnv)
    (Tot' HP' HS' C F : Res) (cr' db' : Ts → Res) (Rf Rs H : Res) (cr db : Ts → Res) (δ : Ts → Res) : Prop :=
  EFoot g (CE η) E' s (stOf r.1 r.2.1 r.2.2) ∧ ThInvRE p E' r.2.2 Tot' ∧ MemInv g E' (stOf r.1 r.2.1 r.2.2) ∧
    MemHeldP E' (stOf r.1 r.2.1 r.2.2) HP' ∧ MemHeldS E' (stOf r.1 r.2.1 r.2.2) HS' ∧
    TermPlant.PromCrK E' (stOf r.1 r.2.1 r.2.2) cr' db' ∧ MintStep g η s (stOf r.1 r.2.1 r.2.2) C F ∧
    Tot' + (HP' + HS') + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum s db + C ≤
      Rf + Rs + H + pSum s cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F ∧
    BoxNewV (CE η) E' s r.2.2 ∧
    CrShift η s δ ∧ ∃ Fd : List Ts, (∀ t, δ t ≠ .zero → t ∈ Fd) ∧
    Tot' + (HP' + HS') + pSum (stOf r.1 r.2.1 r.2.2) cr' + Res.sum (Fd.map δ) + pSum s db + C ≤
      Rf + Rs + H + pSum s cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F ∧
    IniFixZ { g with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l } (CE η) E' s (stOf r.1 r.2.1 r.2.2) ∧
    (∀ E0, TermTyped.WrLocA2 E0 g (CE η) E' s (stOf r.1 r.2.1 r.2.2))

/-- (R4 resplit, (A)) **The credit-free part of `TOut`**: `TOut` with its two inequalities dropped
(replaced by `True`, so conjunct positions are kept).  It does not read `Rf Rs H cr db`; consumers that
never read the step's inequality take it, so a stepper output at the stepper's credits `crS` (`TOut … crS`)
serves them at the thread's credits `cr i` (`TOut.toC`). -/
def TOutC (p : Prog) (g : G) (η : TEnv) (s : St) (r : Memory × List Ts × TTh) (E' : TEnv)
    (Tot' HP' HS' C F : Res) (cr' db' : Ts → Res) (_Rf _Rs _H : Res) (_cr _db : Ts → Res) (δ : Ts → Res) :
    Prop :=
  EFoot g (CE η) E' s (stOf r.1 r.2.1 r.2.2) ∧ ThInvRE p E' r.2.2 Tot' ∧ MemInv g E' (stOf r.1 r.2.1 r.2.2) ∧
    MemHeldP E' (stOf r.1 r.2.1 r.2.2) HP' ∧ MemHeldS E' (stOf r.1 r.2.1 r.2.2) HS' ∧
    TermPlant.PromCrK E' (stOf r.1 r.2.1 r.2.2) cr' db' ∧ MintStep g η s (stOf r.1 r.2.1 r.2.2) C F ∧
    True ∧ BoxNewV (CE η) E' s r.2.2 ∧
    CrShift η s δ ∧ ∃ Fd : List Ts, (∀ t, δ t ≠ .zero → t ∈ Fd) ∧ True ∧
    IniFixZ { g with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l } (CE η) E' s (stOf r.1 r.2.1 r.2.2) ∧
    (∀ E0, TermTyped.WrLocA2 E0 g (CE η) E' s (stOf r.1 r.2.1 r.2.2))

/-- A `TOut` gives its credit-free part, at any `Rf Rs H cr db`. -/
theorem TOut.toC {p : Prog} {g : G} {η : TEnv} {s : St} {r : Memory × List Ts × TTh} {E' : TEnv}
    {Tot' HP' HS' C F : Res} {cr' db' : Ts → Res} {Rf Rs H : Res} {cr db δ : Ts → Res}
    (h : TOut p g η s r E' Tot' HP' HS' C F cr' db' Rf Rs H cr db δ) (Rf2 Rs2 H2 : Res) (cr2 db2 : Ts → Res) :
    TOutC p g η s r E' Tot' HP' HS' C F cr' db' Rf2 Rs2 H2 cr2 db2 δ :=
  let ⟨a1, a2, a3, a4, a5, a6, a7, _, a9, a10, Fd, hFd, _, a12⟩ := h
  ⟨a1, a2, a3, a4, a5, a6, a7, trivial, a9, a10, Fd, hFd, trivial, a12⟩

/-- (D1) A `TOut` without transfer: `δ = 0`. -/
theorem TOut_zero {p : Prog} {g : G} {η : TEnv} {s : St} {r : Memory × List Ts × TTh} {E' : TEnv}
    {Tot' HP' HS' C F : Res} {cr' db' : Ts → Res} {Rf Rs H : Res} {cr db : Ts → Res}
    (h1 : EFoot g (CE η) E' s (stOf r.1 r.2.1 r.2.2)) (h2 : ThInvRE p E' r.2.2 Tot')
    (h3 : MemInv g E' (stOf r.1 r.2.1 r.2.2)) (h4 : MemHeldP E' (stOf r.1 r.2.1 r.2.2) HP')
    (h5 : MemHeldS E' (stOf r.1 r.2.1 r.2.2) HS') (h6 : TermPlant.PromCrK E' (stOf r.1 r.2.1 r.2.2) cr' db')
    (h7 : MintStep g η s (stOf r.1 r.2.1 r.2.2) C F)
    (h8 : Tot' + (HP' + HS') + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum s db + C ≤
      Rf + Rs + H + pSum s cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F)
    (h9 : BoxNewV (CE η) E' s r.2.2)
    (h10 : IniFixZ { g with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l } (CE η) E' s (stOf r.1 r.2.1 r.2.2))
    (h11 : ∀ E0, TermTyped.WrLocA2 E0 g (CE η) E' s (stOf r.1 r.2.1 r.2.2)) :
    TOut p g η s r E' Tot' HP' HS' C F cr' db' Rf Rs H cr db (fun _ => .zero) := by
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, CrShift_zero η s, [], fun _ h => absurd rfl h, ?_, h10, h11⟩
  rw [List.map_nil, Res.sum_nil, Res.add_zero]
  exact h8

/-- **`E_g` after a thread step** with S6 witness `E'` (`GEnv.post`, foreign
promises synchronised, `fpSync`). -/
noncomputable def EgT (Eg : GEnv) (g : G) (n n' : Nat) (E' : TEnv) (c' : Cfg) : GEnv :=
  (Eg.post g n n' E').withFp (fpSync Eg c')

/-- A promise step of thread `j` from a reachable configuration. -/
structure PCtx (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : Res) (MintOK : Res → Prop) (c0 c : Cfg)
    (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res) (j : Nat) (th : TTh)
    (a : Address) (v : WeakMem.Val) (w : Ts) : Prop where
  run : TermStep.Steps p k arch c0 c
  inv : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db
  hth : c.ths[j]? = some th
  hw : w < c.mem.size
  cert : Certified p k arch (promise c j a v w) j

/-- (spawn) **`PCtx` over runs with an extra relation `Sp`**: identical except `run`. -/
structure PCtxX (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 c : Cfg)
    (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res) (j : Nat) (th : TTh)
    (a : Address) (v : WeakMem.Val) (w : Ts) : Prop where
  run : TermSpawnStep.StepsG p k arch Sp c0 c
  inv : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db
  hth : c.ths[j]? = some th
  hw : w < c.mem.size
  cert : Certified p k arch (promise c j a v w) j

/-- The bridge for promise steps. -/
theorem PCtx.toX {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop} {Init : Res}
    {MintOK : Res → Prop} {c0 c : Cfg}
    {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtx p k arch Init MintOK c0 c Eg Tot HP HS cr db j th a v w) :
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w :=
  ⟨TermSpawnStep.StepsG.ofSteps X.run, X.inv, X.hth, X.hw, X.cert⟩

/-- At `Sp := ⊥` a promise context is an old one. -/
theorem PCtxX.toBot {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 c : Cfg}
    {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch (fun _ _ => False) Init MintOK c0 c Eg Tot HP HS cr db j th a v w) :
    PCtx p k arch Init MintOK c0 c Eg Tot HP HS cr db j th a v w :=
  ⟨TermSpawnStep.StepsG.toSteps_bot X.run, X.inv, X.hth, X.hw, X.cert⟩

#print axioms PCtx.toX
#print axioms PCtxX.toBot

/-- (S7d, A′; B1) **The ghost plant**: frontiers set at the labels `P` chooses, and (F2′) their
reader-visible counts raised to `N` (`ini := max ini N`). -/
def plantG (Eg : GEnv) (P : AllocLabel → Option Ts) (N : AllocLabel → Nat) : GEnv :=
  { Eg with pfr := fun l => match P l with | some f => some f | none => Eg.pfr l
            ini := fun l => match P l with | some _ => max (Eg.ini l) (N l) | none => Eg.ini l }

theorem plantG_none {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} (h : ∀ l, P l = none) :
    plantG Eg P N = Eg := by
  cases Eg
  simp [plantG, h]

/-- (B1) The plant raises `ini` only at planted labels, and only upwards. -/
theorem plantG_ini_le (Eg : GEnv) (P : AllocLabel → Option Ts) (N : AllocLabel → Nat) (l : AllocLabel) :
    Eg.ini l ≤ (plantG Eg P N).ini l := by
  simp only [plantG]; split <;> omega

theorem plantG_ini_none {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {l : AllocLabel}
    (h : P l = none) : (plantG Eg P N).ini l = Eg.ini l := by
  simp only [plantG, h]

/-- What a plant may do (s7_design §1): from no frontier, at a cell of the
promiser, to a frontier within memory, of a `noOR` cell type. -/
def PlantSpec (Eg : GEnv) (P : AllocLabel → Option Ts) (j : Nat) (n : Nat) : Prop :=
  ∀ l f, P l = some f → Eg.pfr l = none ∧ Eg.OwnAt j l ∧ f ≤ n ∧ ∀ cl, Eg.sto l = some cl → noOR cl.ty = true

/-- **`E_g` after a promise step** of `j` at timestamp `n` with plant `P`. -/
def EgP (Eg : GEnv) (P : AllocLabel → Option Ts) (N : AllocLabel → Nat) (j n : Nat) : GEnv :=
  (plantG Eg P N).withFp (fpProm Eg j n)

/-- The promised state of `j`. -/
def thP (th : TTh) (n : Nat) : TTh := { th with promises := th.promises ++ [n] }

/-- The side condition `hwu` of `tstepMC_prom`/`tstepMC_promE`, (B5) at the
promiser's environment `E` (its cut, `tstepMC_promEc`). -/
def HWU (p : Prog) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (Tot : Res) (a : Address)
    (v : WeakMem.Val) (w : Ts) (E : TEnv) : Prop :=
  ∀ η : TEnv, CE η = E → ThInvRE p (CE η) th Tot → MemInv g (CE η) (stOf mem pairs th) → VisU (CE η) a →
    ∃ c n P, η.sto a.label = some c ∧ AtOff c.ty a.offset (.word (.lit n) P) ∧
      P.ghost = false ∧ IniAt η.ini c a (.word (.lit n) P) ∧
      ∃ Rn, VRR (fun _ => 0) (CE (CE η).unsee) (.word (.lit n) P) (shp (.word (.lit n) P)) [mw ⟨a, v, w⟩] Rn

/-- (U3) The side condition `hfw` of `tstepMC_prom`/`tstepMC_promE`: at a
predicted unit there is a first write, (B5) at the
promiser's environment `E`. -/
def HFW (p : Prog) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (Tot : Res) (a : Address)
    (E : TEnv) : Prop :=
  ∀ η : TEnv, CE η = E → ThInvRE p (CE η) th Tot → MemInv g (CE η) (stOf mem pairs th) → PredU (CE η) a →
    ∃ h, FirstW mem a h

/-- (B5) **`tstepMC_promE` with its side conditions at the promiser's
environment `E`** only (where `tstepMC_promE` uses them). -/
theorem tstepMC_promEc {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Tot H : Res}
    {cr db : Ts → Res} {a : Address} {v : WeakMem.Val} {w : Ts} {E : TEnv}
    (hT : ThInvRE p E th Tot) (hm : MemInv g E (stOf mem pairs th)) (hH : MemHeld E (stOf mem pairs th) H)
    (hC : PromCr E (stOf mem pairs th) cr db)
    (hwu : HWU p g mem pairs th Tot a v w E) (hfw : HFW p g mem pairs th Tot a E) :
    ∃ H' cr' db', (∀ t, t < mem.size → cr' t = cr t ∧ db' t = db t) ∧
      ThInvRE p E { th with promises := th.promises ++ [mem.size] } Tot ∧
      MemInv g E (stOf (mem.push ⟨a, v, w⟩) pairs { th with promises := th.promises ++ [mem.size] }) ∧
      MemHeld E (stOf (mem.push ⟨a, v, w⟩) pairs { th with promises := th.promises ++ [mem.size] }) H' ∧
      PromCr E (stOf (mem.push ⟨a, v, w⟩) pairs { th with promises := th.promises ++ [mem.size] }) cr' db' ∧
      H' + pSum (promSt (stOf mem pairs th) a v w) cr' + pSum (stOf mem pairs th) db =
        H + pSum (stOf mem pairs th) cr + pSum (promSt (stOf mem pairs th) a v w) db' := by
  obtain ⟨ρ, η, cx, Rf, Rs, hE, hrest⟩ := hT
  subst hE
  have hT : ThInvRE p (CE η) th Tot := ⟨ρ, η, cx, Rf, Rs, rfl, hrest⟩
  obtain ⟨H', cr', db', hag, hH', hC', heq⟩ :=
    promise_acct hH hC (MemInv_promLt hm) (hwu η rfl hT hm) (hfw η rfl hT hm)
  refine ⟨H', cr', db', hag, ⟨ρ, η, cx, Rf, Rs, rfl, hrest⟩, ?_, ?_, ?_, heq⟩
  · rw [stOf_promise]; exact MemInv_promSt hm
  · rw [stOf_promise]; exact hH'
  · rw [stOf_promise]; exact hC'

/-- The promise step's accounting equality (`tstepMC_prom`). -/
def PAcct (s : St) (a : Address) (v : WeakMem.Val) (w : Ts) (H H' : Res) (cr db cr' db' : Ts → Res) : Prop :=
  H' + pSum (promSt s a v w) cr' + pSum s db = H + pSum s cr + pSum (promSt s a v w) db'

/-- `ThSys` at a given `seen` set (`ThSys` is `∃ S, ThSysAt … S`). -/
def ThSysAt (p : Prog) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (Eg : GEnv)
    (Tot HP HS : Res) (cr db : Ts → Res) (S : AllocLabel → Prop) : Prop :=
  ThInvRE p (Cut Eg g.i S) th Tot ∧ ThInvE p (Cut Eg g.i S) th ∧
    MemInv g (Cut Eg g.i S) (stOf mem pairs th) ∧
    MemHeldP (Cut Eg g.i S) (stOf mem pairs th) HP ∧ MemHeldS (Cut Eg g.i S) (stOf mem pairs th) HS ∧
    TermPlant.PromCrK (Cut Eg g.i S) (stOf mem pairs th) cr db

/-- `ThSys.env` at a given `seen` set: the typing of `ThSysAt … S` at the cut `Cut Eg g.i S` itself. -/
theorem ThSysAt.env {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Eg : GEnv} {Tot HP HS : Res}
    {cr db : Ts → Res} {S : AllocLabel → Prop} (hclo : GStoClo Eg)
    (h : ThSysAt p g mem pairs th Eg Tot HP HS cr db S) :
    ∃ ρ η cx Rf Rs, CE η = Cut Eg g.i S ∧ η.tid = g.i ∧ EnvOK p η ∧ TypedK p η cx th.term ∧ TvOK cx ∧
      FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧ Rf + Rs = Tot ∧ TermTyped.StoClo (CE η) ∧
      MemInv g (CE η) (stOf mem pairs th) ∧ MemHeld (CE η) (stOf mem pairs th) (HP + HS) ∧
      TermPlant.PromCrK (CE η) (stOf mem pairs th) cr db ∧ RetPw th.σs th.stack cx.ret := by
  obtain ⟨⟨ρ, η, cx, Rf, Rs, hCE, hE, hT, htv, hi, hsum, hRP⟩, -, hm, hP, hS, hC⟩ := h
  have hH := MemHeld_join (fun _ _ hc hp => Cut_cov hc hp) hP hS
  have htid : (CE η).tid = (Cut Eg g.i S).tid := congrArg TEnv.tid hCE
  refine ⟨ρ, η, cx, Rf, Rs, hCE, htid, hE, hT, htv, hi, hsum, ?_, ?_, ?_, ?_, hRP⟩
  · rw [hCE]; exact StoClo_Cut hclo g.i S
  · rw [hCE]; exact hm
  · rw [hCE]; exact hH
  · rw [hCE]; exact hC

/-! ## (D1) The transfer is paid for -/

theorem Res.sum_apply' : ∀ (L : List Res) (key : Key), Res.sum L key = (L.map (fun R => R key)).sum
  | [], _ => rfl
  | R :: L, key => by simp only [Res.sum_cons, Res.add_apply, List.map_cons, List.sum_cons, Res.sum_apply' L key]

theorem nsumPerm {f : Ts → Nat} {L₁ L₂ : List Ts} (h : L₁.Perm L₂) : (L₁.map f).sum = (L₂.map f).sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.map_cons, List.sum_cons, ih]
  | swap x y L => simp only [List.map_cons, List.sum_cons]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- A sum over a nodup list, supported in `F`, is at most the sum over `F`. -/
theorem nsum_le_of_nodup {f : Ts → Nat} : ∀ {L : List Ts} (F : List Ts), L.Nodup → (∀ x ∈ L, f x ≠ 0 → x ∈ F) →
    (L.map f).sum ≤ (F.map f).sum
  | [], _, _, _ => Nat.zero_le _
  | x :: L, F, hnd, hs => by
      obtain ⟨hx, hnd'⟩ := List.nodup_cons.1 hnd
      simp only [List.map_cons, List.sum_cons]
      by_cases h0 : f x = 0
      · rw [h0, Nat.zero_add]; exact nsum_le_of_nodup F hnd' (fun y hy => hs y (List.mem_cons_of_mem _ hy))
      · have hxF := hs x (List.mem_cons_self ..) h0
        have e : (F.map f).sum = f x + ((F.erase x).map f).sum := by
          rw [nsumPerm (List.perm_cons_erase hxF)]; simp
        rw [e]
        have := nsum_le_of_nodup (F.erase x) hnd' (fun y hy hy0 => by
          have hne : y ≠ x := fun e => hx (e ▸ hy)
          exact (List.mem_erase_of_ne hne).2 (hs y (List.mem_cons_of_mem _ hy) hy0))
        omega

/-- Thread `n`'s promises in `c` (none past the threads). -/
def promsOf (c : Cfg) (n : Nat) : List Ts :=
  match c.ths[n]? with
  | some th => th.promises
  | none => []

theorem pSumAt_key (c : Cfg) (n : Nat) (f : Ts → Res) (key : Key) :
    pSumAt c n f key = ((promsOf c n).map (fun t => f t key)).sum := by
  unfold pSumAt promsOf
  cases c.ths[n]? with
  | none => rfl
  | some th => simp only [pSum, Res.sum_apply', List.map_map]; rfl

theorem promsOf_nodup {c : Cfg} (hd : PromsDisj c) (hnd : ∀ (k : Nat) (th : TTh), c.ths[k]? = some th → th.promises.Nodup) :
    ∀ (ns : List Nat), ns.Nodup → (ns.flatMap (promsOf c)).Nodup
  | [], _ => List.nodup_nil
  | n :: ns, hns => by
      obtain ⟨hn, hns'⟩ := List.nodup_cons.1 hns
      rw [List.flatMap_cons, List.nodup_append]
      refine ⟨?_, promsOf_nodup hd hnd ns hns', fun a ha b hb e => ?_⟩
      · unfold promsOf
        cases h : c.ths[n]? with
        | none => exact List.nodup_nil
        | some th => exact hnd n th h
      · subst e
        obtain ⟨m, hm, ha'⟩ := List.mem_flatMap.1 hb
        have hmn : n ≠ m := fun e => hn (e ▸ hm)
        unfold promsOf at ha ha'
        cases h1 : c.ths[n]? with
        | none => rw [h1] at ha; simp at ha
        | some thn =>
        cases h2 : c.ths[m]? with
        | none => rw [h2] at ha'; simp at ha'
        | some thm =>
        rw [h1] at ha; rw [h2] at ha'
        exact hd n m thn thm a hmn h1 h2 ha ha'

theorem sum_promsOf (c : Cfg) (g : Ts → Nat) :
    ∀ (ns : List Nat), (ns.map (fun n => ((promsOf c n).map g).sum)).sum = ((ns.flatMap (promsOf c)).map g).sum
  | [] => rfl
  | n :: ns => by
      rw [List.map_cons, List.sum_cons, sum_promsOf c g ns, List.flatMap_cons, List.map_append, List.sum_append]

/-- (D1) **`CrShift_sum`**: what any nodup set of threads receives by a transfer
supported in `F` is at most `Σ_F δ` (promises are thread-disjoint and nodup). -/
theorem CrShift_sum {c : Cfg} {δ : Ts → Res} {F : List Ts} (hδ : ∀ t, δ t ≠ .zero → t ∈ F)
    (hd : PromsDisj c) (hnd : ∀ (k : Nat) (th : TTh), c.ths[k]? = some th → th.promises.Nodup) (key : Key)
    (ns : List Nat) (hns : ns.Nodup) :
    (ns.map (fun n => pSumAt c n δ key)).sum ≤ Res.sum (F.map δ) key := by
  have e : (ns.map (fun n => pSumAt c n δ key)).sum =
      (ns.map (fun n => ((promsOf c n).map (fun t => δ t key)).sum)).sum := by
    congr 1; exact List.map_congr_left (fun n _ => pSumAt_key c n δ key)
  rw [e, sum_promsOf, Res.sum_apply', List.map_map]
  exact nsum_le_of_nodup F (promsOf_nodup hd hnd ns hns) (fun t _ h0 =>
    hδ t (fun hz => h0 (by rw [hz]; rfl)))

theorem pSumAt_add (c : Cfg) (n : Nat) (f g : Ts → Res) (key : Key) :
    pSumAt c n (fun t => f t + g t) key = pSumAt c n f key + pSumAt c n g key := by
  simp only [pSumAt_key, Res.add_apply]
  induction promsOf c n with
  | nil => rfl
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-- (D1) The credit sums after `updD`, against `upd`: at most `Σ_F δ` more. -/
theorem sum_updD_le {c : Cfg} {cr : Nat → Ts → Res} {i : Nat} {cr' δ : Ts → Res} {F : List Ts}
    (hδ : ∀ t, δ t ≠ .zero → t ∈ F) (hd : PromsDisj c) (hnd : ∀ (k : Nat) (th : TTh), c.ths[k]? = some th → th.promises.Nodup)
    (key : Key) (ns : List Nat) (hns : ns.Nodup) :
    (ns.map (fun n => pSumAt c n (updD cr i cr' δ n) key)).sum ≤
      (ns.map (fun n => pSumAt c n (upd cr i cr' n) key)).sum + Res.sum (F.map δ) key := by
  have hle : ∀ (ms : List Nat), (ms.map (fun n => pSumAt c n (updD cr i cr' δ n) key)).sum ≤
      (ms.map (fun n => pSumAt c n (upd cr i cr' n) key)).sum + (ms.map (fun n => pSumAt c n δ key)).sum := by
    intro ms
    induction ms with
    | nil => exact Nat.le_refl _
    | cons n ms ih =>
        simp only [List.map_cons, List.sum_cons]
        have : pSumAt c n (updD cr i cr' δ n) key ≤ pSumAt c n (upd cr i cr' n) key + pSumAt c n δ key := by
          by_cases h : n = i
          · subst h; rw [updD_self, upd_self]; omega
          · rw [updD_other _ _ _ h, upd_other _ _ h, pSumAt_add]; exact Nat.le_refl _
        omega
  have := CrShift_sum hδ hd hnd key ns hns
  have := hle ns
  omega

end TermMain

#print axioms TermMain.CrShift_zero
#print axioms TermMain.Res.sum_map_zero'
#print axioms TermMain.TOut_zero
#print axioms TermMain.CrShiftP_zero
#print axioms TermMain.updD_self
#print axioms TermMain.updD_other
#print axioms TermMain.updD_zero
#print axioms TermMain.Res.sum_apply'
#print axioms TermMain.nsumPerm
#print axioms TermMain.nsum_le_of_nodup
#print axioms TermMain.pSumAt_key
#print axioms TermMain.promsOf_nodup
#print axioms TermMain.sum_promsOf
#print axioms TermMain.CrShift_sum
#print axioms TermMain.pSumAt_add
#print axioms TermMain.sum_updD_le
