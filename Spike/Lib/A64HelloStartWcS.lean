/-
**`hello.w` from `_start` to `wc_main`'s heap abort at depth** (AArch64, Option A,
step 4b): `MainGlueW.hello_start_wc_segW` over segments with frames (`SegWS`, `Spike/Lib/SegS.lean`) at the
start's level at the frames `fs` (`HelloWf.WSHF`), `wc_rodata` under the frame `fr` its source call pushed (at
the real run `HelloRdCf.frH env`).

`MainGlueW.hello_start_wc_segW` runs `scc_rt_main` as one frameless segment, so at the real run (the setup start,
`rodata` called) its `rodata` premises hold vacuously. Here the start is at `[]` (`Rt.startEF_segWA` lifted by
`SegWS.liftS`), and from `scc_rt_main`'s entry `MainGlueS.hello_main_wc_segWS` (`wc_rodata` at `[fr]`).

- `WS`: `WSHF` as a level with frames (`WS … s c [] = WSH … s c` by `rfl`).
- `hxa_of_post`: `HelloM.hello_main_hxa_of_post` at any `wc_rodata` entry invariant `J0` (here the source after
  the call of `rodata`, not `mNC`'s). Superseded: its `hpost` premise is unsatisfiable at a reachable `.sp0` (`b`,
  `w` unconstrained); `hello_start_wc_segWS` takes the allocator's landing `hxa` directly.
- `rdJH`, `rdJH_run`, `rdJH_back`: the source at `rodata`'s first allocation after the setup's call, its entry
  state kept (`hello_start_wc_segWS`'s `hrun`, `hJ'` at hello's source, `HelloRdCf.setup_call_run`).
- `hello_start_wc_segWS`: from `_start` at `F ∧ P` to `wc_main`'s abort exit at `[]` or `wc_rodata`'s heap
  abort at `[fr]`.
-/
import Spike.Lib.A64HelloMainGlueS
import Spike.Lib.A64HelloMainGlueW
import Spike.Lib.A64HelloAllocWSF

namespace Spike.Lib.A64.HelloPh.StartWcS

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
open Spike.Lib.A64.HelloWf (WSHF)
open Spike.Lib.A64.Flow (swR FStable At enter leave CKept)
open Spike.Lib.A64.Flow.Ret0 (pinA stacksA limA LimOk StOk entryN)
open Spike.Lib.A64.WakePh.MainGlue (gS FS JS)
open Spike.Lib.A64.Flow.Hello1 (AG mR mF mRdJ0 mNC aR mWC)
open Spike.Lib.A64.Flow.HelloRd (rN rX pN RdPreW)
open Spike.Lib.A64.Flow.HelloM (wcR wcF wcJ0)
open Spike.Lib.A64.Flow.HelloWc (wXH)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.Alloc (Call Ea)
open Spike.Lib.A64.HelloPh.MainGlueS (MainWcPS)
open Spike.Lib.DmemPriv (WordsNoneP WordIn)
open Spike.Lib (Arena FragS Frag MemSide SegWS LocalRun FrameRun)
/-- `Flow`'s abstract state (`AS` alone is ambiguous here). -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

/-- **The start's level as a level with frames**: `WSHF … fs` at the frames `fs`. -/
abbrev WS (L : RuntimeLayout) (a : BitVec 64) (ar : Arena) (p : Prog) (Dt Cl : State → Prop)
    (Ctx : FragS isaLSE2) (lbl : Lbl) (lsize : Lsize) (frM : TermRun.Frame) (X0 : State → Prop) : FragS isaLSE2 :=
  fun s c fs => WSHF L a ar p Dt Cl Ctx lbl lsize frM X0 fs s c

/-! ## The allocator's fresh-label landing at any `wc_rodata` entry invariant -/

section Bridge

variable {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **The allocator's fresh-label landing is at `wc_rodata`'s `.sp0`** (`HelloM.hello_main_xa_post` at any entry
invariant `J0` of `wc_rodata`, per caller's state `σC`).

Superseded: its consumer `hxa_of_post`'s `hpost` premise is unsatisfiable at a reachable `.sp0` (`b`, `w`
unconstrained); see `hello_start_wc_segWS`'s `hxa`. -/
theorem xa_post {J0 : FAS → FAS → Ctl → Prop} {Jp Jp' J1' J2 J2' J3 J4 J5 : FAS → Ctl → Prop}
    {J1 : FAS → FAS → Ctl → Prop}
    {m0 : MachineData} {σC : FAS} {q : AG ms (_root_.Executable.labels exe).label} {F' : MachineData → Prop}
    {l : WeakMem.AllocLabel} {b w : Nat}
    (hFF : ∀ m, F' m → mF R F m0 σC m)
    (hkeep : ∀ m, F' m → ∃ mC σ c, Spike.Lib.A64.Flow.Abs (mR R) ⟨-48, []⟩ mC σ ∧
      (rN (_root_.Executable.labels exe).label (J0 σC) (J1 σC) .call).J σ c ∧
      (Spike.Lib.A64.Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c ∧
      CKept (mR R) (-48) (-160) 0 mC m)
    (hJp : ∀ σx σ c0 c, (Ea ms q.1 l b w).J σx c →
      (rN (_root_.Executable.labels exe).label (J0 σC) (J1 σC) .call).J σ c0 →
      (Spike.Lib.A64.Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c0 →
      Jp (leave (aR (mR R)) (-48) σ σx) c)
    {s : State} {c : Ctl} (h : At exe endPc (aR (mR R)) F' (Ea ms q.1 l b w) s c) :
    At exe endPc (mR R) (mF R F m0 σC) (pN (_root_.Executable.labels exe).label Jp Jp' J1' J2 J2' J3 J4 J5 .s0)
      s c := by
  have h' := Spike.Lib.A64.Flow.at_leave (R := mR R) (kc := -48) (lo' := -160) (hi' := 0)
    (P := fun σ => ∃ c0, (rN (_root_.Executable.labels exe).label (J0 σC) (J1 σC) .call).J σ c0 ∧
      (Spike.Lib.A64.Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c0)
    rfl (fun m hm => by
      obtain ⟨mC, σ, c0, hA, h1, h2, hK⟩ := hkeep m hm
      exact ⟨hFF m hm, mC, σ, _, hK, hA, c0, h1, h2⟩) h
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, σx, σ', hJx, ⟨c0, h1, h2⟩, rfl⟩ := h'
  refine ⟨he, hn, hdc, ?_, _, hA, hD, hJp σx σ' c0 c hJx h1 h2⟩
  rw [hpc]
  show Int64.ofBitVec q.1.ra = (_root_.Executable.labels exe).label ".L19_wc_rodata.sp0"
  rw [← h2.2.2.1]
  show Int64.ofBitVec σ'.regs.X30.toBitVec = _
  rw [h1.2.2.2.2, Spike.Lib.int64_ofBitVec_toBitVec]

/-- **`hello_main_wc_segWS`'s `hxa` from the landing at `.sp0`** (`HelloM.hello_main_hxa_of_post` at any entry
invariant `J0` of `wc_rodata`): if every state at `wc_rodata`'s `.sp0` for some caller's state `m0`, `σC` (of an
invariant `Jp m0 σC` the landings imply, `hJp`) is one a fresh label's allocation continues in (`hpost`), the
allocator's landings are (`xa_post`).

Superseded: its `hpost` premise is unsatisfiable at a reachable `.sp0` (`b`, `w` unconstrained: `msOfA`'s `xa`
asks `AllocLand heap cells b w`, false at `b = 0`); see `hello_start_wc_segWS`'s `hxa`. -/
theorem hxa_of_post {J0 : FAS → FAS → Ctl → Prop} {J1 : FAS → FAS → Ctl → Prop}
    {Jp Jp' J1' J2 J2' J3 J4 J5 : MachineData → FAS → FAS → Ctl → Prop}
    (hJp : ∀ m0 σC (q : AG ms (_root_.Executable.labels exe).label) l b w σx σ c0 c, (Ea ms q.1 l b w).J σx c →
      (rN (_root_.Executable.labels exe).label (J0 σC) (J1 σC) .call).J σ c0 →
      (Spike.Lib.A64.Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c0 →
      Jp m0 σC (leave (aR (mR R)) (-48) σ σx) c)
    (hpost : ∀ l b w s c, lbl l = none → (∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
      (pN (_root_.Executable.labels exe).label (Jp m0 σC) (Jp' m0 σC) (J1' m0 σC) (J2 m0 σC) (J2' m0 σC)
        (J3 m0 σC) (J4 m0 σC) (J5 m0 σC) .s0) s c) →
      ms.xa l b w s c) :
    ∀ m0 σC, ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF R F m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Spike.Lib.A64.Flow.Abs (mR R) ⟨-48, []⟩ mC σ ∧
        (rN (_root_.Executable.labels exe).label (J0 σC) (J1 σC) .call).J σ c ∧
        (Spike.Lib.A64.Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c ∧
        CKept (mR R) (-48) (-160) 0 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR (mR R)) F' (Ea ms q.1 l b w) s c → ms.xa l b w s c :=
  fun m0 σC q _ hFF hkeep l b w _ _ hl h =>
    hpost l b w _ _ hl ⟨m0, σC, xa_post hFF hkeep (hJp m0 σC q l b w) h⟩

end Bridge

/-! ## The source after the setup's call of `rodata` -/

/-- **The source at `rodata`'s first allocation after the setup's call**, `scc_rt_main`'s state at the call kept
(`mNC`'s invariant at some control). -/
def rdJH (lab : Label → Int64) (J : FAS → Ctl → Prop) (σ : FAS) (c : Ctl) : Prop :=
  c = Spike.Lib.HelloRodataSrc.rdCN ∧ ∃ c', (mNC lab J).J σ c'

/-- **The setup's call of `rodata` and its first steps** from `mNC`'s invariant, whose controls are the setup
start in `env` (`hJ`, `hu`): `rdJH` under `HelloRdCf.frH env` (`HelloRdCf.setup_call_run`). -/
theorem rdJH_run {lab : Label → Int64} {J : FAS → Ctl → Prop} {env : TermRun.Env}
    (hJ : ∀ σ c, J σ c → c = ⟨Scc.Sem.SrcSem.setupTerm, env, none⟩)
    (hu : TermRun.evalAt env (.var "u") = some (.unit, [])) :
    ∀ σ c, (mNC lab J).J σ c → ∃ c', FrameRun Spike.Lib.HelloSrc.helloSrc (c, [])
      (c', [Spike.Lib.HelloRdCf.frH env]) ∧ rdJH lab J σ c' := by
  intro σ c h
  obtain ⟨⟨σe, hJe, -⟩, -⟩ := id h
  refine ⟨_, ?_, rfl, c, h⟩
  rw [hJ σe c hJe]
  exact Spike.Lib.HelloRdCf.setup_call_run hu

/-- **`rdJH`'s states are `mNC`'s** at some control. -/
theorem rdJH_back {lab : Label → Int64} {J : FAS → Ctl → Prop} :
    ∀ σ c', rdJH lab J σ c' → ∃ c, (mNC lab J).J σ c :=
  fun _ _ h => h.2

/-! ## From `_start` to `wc_main`'s heap abort at the start's level with frames -/

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Scc.Sem.Range} {lbl' : Lbl}
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

/-- **From `_start` to `wc_main`'s first allocation's heap abort inside the start's level with frames**
(`MainGlueW.hello_start_wc_segW` with `wc_rodata` under its frame `fr`): the start up to the switch at `[]`
(`startEW_W0SH`, `Rt.startEF_segWA` lifted), then at each base `v` of the new stack of depth `Lsw`
`MainGlueS.hello_main_wc_segWS` at `WS` from `scc_rt_main`'s entry (`mainPreWH_W0SH`; `hWe` at `bl wc_rodata`'s
target), the source's call of `rodata` pushing `fr` into `J'` (`hrun`, `hJ'`; at hello `rdJH`), `wc_rodata` at
`[fr]` (`hrd`), its fresh-label landings in `ms [fr]`'s allocation fragment (`hxa`, at the allocator's landing
`Ea`), and from `.sp0` (its states by `hret`) to `wc_main`'s abort exit at `[]` (`hP`). The other exit is
`wc_rodata`'s heap abort at `[fr]`. -/
theorem hello_start_wc_segWS (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hs : WSep L a) (hro : L.Λ.rodata.Disjoint L.Λ.stackPool) {k0 : BitVec 64}
    {Lsw : Int} {ms : List TermRun.Frame → MemSide isaLSE2} {pS : Prog} {lblS : Lbl} {fr : TermRun.Frame}
    (hK : (ms []).K = some abi) (hK' : (ms [fr]).K = some abi) (hfr : fr.σs = []) (hwf : L.Λ.WF)
    (hC0 : Spike.Lib.A64Consumer.CFacts L.Λ lbl' c0)
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
    (hhdr : StOk (ms []) F L.exe L.endPc (pinA L.lab + 0#64)
      (Spike.Lib.A64.Flow.Ret0.AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcbO : ∀ g, Spike.Lib.A64.Rt.TcbOkA (ms []) F L.exe L.endPc (R.callee Spike.Lib.A64.Abort.oI.sp (-192) 0) F
      ⟨g, 0#64, c0⟩)
    (hfld : ∀ e ∈ Spike.Lib.A64.Flow.Ret0.ThreadInit.fields (pinA L.lab + 0#64 + 8#64) (stacksA L.lab + k0),
      StOk (ms []) F L.exe L.endPc (pinA L.lab + 0#64 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : ∀ g, Spike.Lib.A64.Rt.TakeOkA (ms []) F L.exe L.endPc
      ((R.callee Spike.Lib.A64.Abort.oI.sp (-256) 0).callee Spike.Lib.A64.Flow.Ret0.ThreadInit.oI.sp (-208) 0) F
      ⟨g, k0, c0⟩)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64))) 8 = none)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) false
      ⟨limA (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64)), 8⟩ = true)
    (hlim80 : LimOk (ms []) F L.exe L.endPc (limA (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64)))
      (stacksA L.lab + k0 + 16384#64 - (80 : Int64).toBitVec))
    (hlim128 : LimOk (ms [fr]) F L.exe L.endPc (limA (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64)))
      (stacksA L.lab + k0 + 16384#64 - (80 : Int64).toBitVec - (48 : Int64).toBitVec))
    (hH : ∀ fs, L.Λ.heap.lo ≤ (ms fs).heap)
    (hHi : ∀ fs, (ms fs).heap + 16 * (ms fs).cells ≤ L.Λ.heap.lo + L.Λ.heap.size)
    (hctr : ∀ fs, WordIn L.Λ.heap (ms fs).ctr ∨ WordIn L.Λ.data (ms fs).ctr)
    (hoff : ∀ q : Call, q.OK (ms [fr]) L.lab → (ms [fr]).off q.n q.τ ≤ 16 * (ms [fr]).units q.n q.τ)
    (hoffB : ∀ q : Call, q.OKB (ms []) L.lab → (ms []).off q.n q.τ ≤ 16 * (ms []).units q.n q.τ)
    {J' : FAS → Ctl → Prop} {J1 : FAS → FAS → Ctl → Prop}
    (hWe : ∀ v s c, At L.exe L.endPc (swR v (-Lsw) 0) (FS L rS Lsw k0 v) (mNC L.lab (JS L k0 c0)) s c →
      WS L a ar p Dt Cl Ctx lbl lsize frM X0 s c [])
    (hrun : ∀ σ c, (mNC L.lab (JS L k0 c0)).J σ c → ∃ c', FrameRun pS (c, []) (c', [fr]) ∧ J' σ c')
    (hJ' : ∀ σ c', J' σ c' → ∃ c, (mNC L.lab (JS L k0 c0)).J σ c)
    (hrd : ∀ v m0 σC, RdPreW (fun s c => WS L a ar p Dt Cl Ctx lbl lsize frM X0 s c [fr])
      (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc (mR (swR v (-Lsw) 0)) (mF (swR v (-Lsw) 0) (FS L rS Lsw k0 v) m0 σC)
      (ms [fr]) (mRdJ0 J' σC) (J1 σC))
    (hloc : ∀ σC σ c, mRdJ0 J' σC σ c → ∃ c', LocalRun pS c c' ∧ J1 σC σ c')
    (hq : ∀ σC σ c, J1 σC σ c → ∃ q : Call, q.OK (ms [fr]) L.lab ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u (ms [fr]) = 3#64)
    {D : Int} (hD : 304 ≤ D) (hD16 : D % 16 = 0) (hLD : 80 + D ≤ Lsw) {t : UInt64}
    {Jp Jp' Jx1 J2 J2' J3 J4 J5 Jr Jr1 : BitVec 64 → MachineData → FAS → FAS → Ctl → Prop}
    (hxa : ∀ v m0 σC, ∀ q : AG (ms [fr]) L.lab, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF (swR v (-Lsw) 0) (FS L rS Lsw k0 v) m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Spike.Lib.A64.Flow.Abs (mR (swR v (-Lsw) 0)) ⟨-48, []⟩ mC σ ∧
        (rN L.lab (mRdJ0 J' σC) (J1 σC) .call).J σ c ∧
        (Spike.Lib.A64.Alloc.N L.lab (ms [fr]) q.1 .e).J (enter (-48) σ) c ∧
        CKept (mR (swR v (-Lsw) 0)) (-48) (-160) 0 mC m) →
      ∀ l b w s c, lblS l = none → At L.exe L.endPc (aR (mR (swR v (-Lsw) 0))) F' (Ea (ms [fr]) q.1 l b w) s c →
        (ms [fr]).xa l b w s c)
    (hret : ∀ v m0 σC σ c, (rX (ms [fr]) L.lab lblS (J1 σC) .sp0).J σ c → Jp v m0 σC σ c)
    (hPw : ∀ v m0 σC, MainWcPS (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) pS lblS ms
      L.exe L.endPc (swR v (-Lsw) 0) D (FS L rS Lsw k0 v) fr m0 σC (Jp v m0 σC) (Jp' v m0 σC) (Jx1 v m0 σC)
      (J2 v m0 σC) (J2' v m0 σC) (J3 v m0 σC) (J4 v m0 σC) (J5 v m0 σC) (Jr v m0 σC) (Jr1 v m0 σC) t) :
    SegWS (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) pS lblS ms
      ((At L.exe L.endPc R (fun m => F m ∧ P m) (entryN L.lab c0)).at [])
      (fun s c fs => Frag.at (fun s c => ∃ v m0 σC m1 σ1,
          At L.exe L.endPc (wcR (swR v (-Lsw) 0) D) (wcF (swR v (-Lsw) 0) D (FS L rS Lsw k0 v) m1 σ1)
            (wXH (ms []) L.lab (wcJ0 (mWC L.lab σC (Jr1 v m0 σC)).J σ1) .abort) s c ∧ TP t s) [] s c fs ∨
        Frag.at (fun s c => ∃ v m0 σC,
          At L.exe L.endPc (mR (swR v (-Lsw) 0)) (mF (swR v (-Lsw) 0) (FS L rS Lsw k0 v) m0 σC)
            (rX (ms [fr]) L.lab lblS (J1 σC) .abort) s c) [fr] s c fs) := by
  have hpS : Lays L.exe SccCode.helloProg L.pfx := hp ▸ L.lays
  have hendS : L.endPc = endOf L.exe SccCode.helloProg L.pfx := by show endOf L.exe L.prog L.pfx = _; rw [hp]
  have hFwS := fun v => Spike.Lib.A64.Rt.wordsNoneP_swFSL_fstable (v := v) hwf hsub hok (by omega) hL8 hsubS
    hfitL houtL hfit
  have hA := Spike.Lib.A64.Rt.startEF_segWA (Fw := WordsNoneP L.Λ) (p := pS) (lbl := lblS) hpS hendS
    hello_rtCodeIn0 hK hF hR hal hRlo hhi 0#64 k0 c0 (by decide) hhdr htcbO hk hfld htk h16 hok hsubS hun hFw hFwS
    hRS hfit houtS hFt hP
    (Spike.Lib.A64.WakePh.StartGlue.StartEW.toF (StartWf.startEW_W0SH hp hlo hlab hsite hcl hc0 hpl0 hX0 hΛ hs hro
      hC0 hR hal hRlo hhi hFr rfl hrS hsub hSM hSMi hSMt hfit h16 hok hL8 hoffP htcbW htiW))
  refine (SegWS.liftS (W := WS L a ar p Dt Cl Ctx lbl lsize frM X0) [] hA fun _ _ h => h).seq ?_
  refine (SegWS.exists_pre (P := fun g : {v : BitVec 64 // v.toNat % 16 = 0 ∧ (swR v (-Lsw) 0).OK} =>
      (At L.exe L.endPc (swR g.1 (-Lsw) 0) (FS L rS Lsw k0 g.1) (mainE0 L.lab (gS L k0 c0))).at [])
    fun g => ?_).mono_pre ?_
  · obtain ⟨v, hv, hR'⟩ := g
    have hpre := MainWf.mainPreWH_W0SH (R := swR v (-Lsw) 0) (F := FS L rS Lsw k0 v) (ms := ms [])
      (J := JS L k0 c0) (tp := UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64)) (a := a) (ar := ar) (Dt := Dt)
      (Ctx := Ctx) (lsize := lsize) (frM := frM)
      hp hlo hlab hsite hcl hc0 hpl0 hX0 hΛ (fun _ _ h => ⟨h.1.1, h.1.2.2⟩) hC0
      hR' hv (show -Lsw ≤ -80 by omega) (Int.le_refl 0) (show (-Lsw) % 8 = 0 by omega)
      (show (0 : Int) % 8 = 0 by decide) hsub hfit (fun _ h => h.2.2) hmr (fun _ h => h.2.1.2)
    refine (MainGlueS.hello_main_wc_segWS (W := WS L a ar p Dt Cl Ctx lbl lsize frM X0)
      (K := Spike.Lib.A64.PhRec.K L rS) (p := pS) (lbl := lblS) (ms := ms) (fr := fr) (J1 := J1)
      (Jp := Jp v) (Jp' := Jp' v) (Jx1 := Jx1 v) (J2 := J2 v) (J2' := J2' v) (J3 := J3 v) (J4 := J4 v)
      (J5 := J5 v) (Jr := Jr v) (Jr1 := Jr1 v) (t := t) hK hK' hpS hendS hD hD16 (hFwS v) hR' hv
      (show -Lsw ≤ -288 by omega) (show -Lsw ≤ -80 - D by omega) (Int.le_refl 0) hfr hpre.1 hpre.2 (hWe v)
      hrun hJ' (hrd v)
      (Spike.Lib.A64.WakePh.MainWf.limOk_mainE0 ⟨hlim80.rt, hlim80.mp, fun _ h => h.2.1.2, hlim80.room⟩)
      ?_ hloc hq
      (Spike.Lib.A64.Alloc.hmem_of_wordsNone hwf (fun _ h => h.1.wn) (hH _) (hHi _) (hctr _) hoff)
      (hxa v) (hret v) (hPw v)
      (Spike.Lib.A64.WakePh.StartGlue.hmemB_of_wordsNone hwf (fun _ h => h.1.wn) (hH _) (hHi _) (hctr _)
        hoffB)).mono_post ?_
    · rintro σ c ⟨⟨-, hsp, htp⟩, -⟩
      rw [Spike.Lib.A64.Flow.Ret0.tcbA_limA htp, hsp]
      exact ⟨hlim128.rt, hlim128.mp, fun _ h => h.2.1.2, hlim128.room⟩
    · rintro s c fs (⟨⟨m0, σC, m1, σ1, h⟩, rfl⟩ | ⟨⟨m0, σC, h⟩, rfl⟩)
      · exact .inl ⟨⟨v, m0, σC, m1, σ1, h⟩, rfl⟩
      · exact .inr ⟨⟨v, m0, σC, h⟩, rfl⟩
  · rintro s c fs ⟨⟨v, h16, hok, h⟩, rfl⟩
    exact ⟨⟨v, h16, hok⟩, h, rfl⟩

end Gen

end Spike.Lib.A64.HelloPh.StartWcS

/-- info: 'Spike.Lib.A64.HelloPh.StartWcS.hxa_of_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartWcS.hxa_of_post

/-- info: 'Spike.Lib.A64.HelloPh.StartWcS.rdJH_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartWcS.rdJH_run

/--
info: 'Spike.Lib.A64.HelloPh.StartWcS.hello_start_wc_segWS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartWcS.hello_start_wc_segWS
