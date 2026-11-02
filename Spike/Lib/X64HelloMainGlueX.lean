/-
**hello.w on x86-64 from `_start` to `wc_rodata`'s heap abort at depth, level 0, at `ownGHXW`** (the `ownGHXW`
instance of `Spike/Lib/X64HelloStartWcS0.lean`, the hello counterpart of `Spike/Lib/X64WakeMainGlueX.lean`):
`StartWcS0.hello_start_rd_segWS0` with the start's level `StartWf.WSH` (at `ownGH`) replaced, at every frame list,
by `AllocWSF.WSHFg` at `ownGHXW` (main's and the worker's TCB words appended; `WSHX` at `[]`): the start up to the
switch by `OwnSt.startEXPH` (from `StartWf.startEWP_W0SH` inside `WSH`, the callees' states inside `WSHX`),
`scc_rt_main` up to `call wc_rodata` by `MainPreX.mainPreWHX` (from `MainWf.mainPreWH_W0SH`), then
`HelloM.hello_main_pre_segWSTF` (generic in the level) through `wc_rodata` at `[fr]` to its heap abort.

- `bandRS80`: `scc_rt_main`'s region band `[-80, 8]` at the new stack's top lies on the pool (`mainPreWHX`'s `hb`).
- `hello_start_rd_segWS0X`: the composed segment inside `WSHFg (ownGHXW L a)`.

## Differences from the AArch64 version

AArch64's start owns `ownGH` throughout (`A64HelloStartWcS0`). x86-64's main also holds its own TCB word from
`scc_rt_start`'s `.x1` on (`ownSH`) and the worker's while it starts it (`ownSWH`), so the segment is stated inside
`WSHFg (ownGHXW L a)`. `startEXPH` lifts `startEWP_W0SH`'s `StartEWFP` inside `WSH`, so the callees' states are
needed inside both levels (`htcb`, `hti` inside `WSH`; `htcbX`, `htiX` inside `WSHX`); `ownGHXW`'s separation
(`hsep`, `ha`, `hW`) is carried; `hWe` and `hrd` are at the new level. Against x86-64 wake's `MainGlueX`: hello's
glue goes through `wc_rodata` at `[fr]` and ends at its heap abort (wake: on to `wc_main`'s), and `scc_rt_main`'s
band is `[-80, 8]` (`bandRS80`, `88 ≤ Lsw`; wake `bandRS`, `[-48, 8]`). The rest is `hello_start_rd_segWS0`'s.
-/
import Spike.Lib.X64HelloStartWcS0
import Spike.Lib.X64HelloOwnStartEP
import Spike.Lib.X64HelloMainPreX
import Spike.Lib.X64HelloAllocWSF

namespace Spike.Lib.X64.HelloPh.StartWcS0


open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (Lays endOf)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout mainE0)
open Spike.Lib.X64Consumer (Lbl Lsize CFacts)
open Spike.Lib.X64.WakeWf (RunWf)
open Spike.Lib.X64.WakePh (WSep tcbM BandOnP)
open Spike.Lib.X64.HelloPh.WcW (freeNH)
open Spike.Lib.X64.HelloPh.StartWf (WSH)
open Spike.Lib.X64 (swR FStable At CKept Abs enter)
open Spike.Lib.X64.Flow.Ret0 (pinA stacksA limA tpOf LimOk StOk)
open Spike.Lib.X64.WakePh.MainGlue (topS tcbS gS RS FS JS stackOff_RS)
open Spike.Lib.X64.Flow.Hello1 (AG mR mF mRdJ0 mNC aR)
open Spike.Lib.X64.Flow.HelloRd (rN rX RdPreW)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.WakeTP (tpG)
open Spike.Lib.X64.Alloc (Call Ea)
open Spike.Lib.DmemPriv (WordIn)
open Spike.Lib.X64.DmemPriv (WordsNoneP)
open Spike.Lib (Arena FragS Frag MemSide SegWS LocalRun FrameRun Region)
/-- The abstract state (`AS` alone is ambiguous here). -/
local notation "FAS" => Spike.Lib.X64.AS


open Spike.Lib.X64HelloOwnLift (tcbWH)
open Spike.Lib.X64.HelloWf (WSHFg)

/-- **`scc_rt_main`'s region band `[-80, 8]` lies on the pool**: its addresses are the new stack's top less `88` up
to the top, inside the stack `rS` (`hrS`), which lies in the pool (`hsub`). -/
theorem bandRS80 {L : RuntimeLayout} {rS : Range} {k0 : BitVec 64} {Lsw : Int}
    (hrS : rS = ⟨(stacksA L.lab + k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hLsw : 88 ≤ Lsw) (hok : (swR (topS L k0) (-Lsw) 0).OK) :
    BandOnP L (RS Lsw (topS L k0)) (-80) 8 := by
  intro k h1 h2
  have hR' : (⟨topS L k0, -Lsw, 1⟩ : Region).OK := ⟨hok.lo, by
    show ((topS L k0).toNat : Int) + 1 ≤ 2 ^ 64; have := (topS L k0).isLt; omega⟩
  have ha := Region.addr_toNat_of hR' (k := -8 - 0 + k) (by show -Lsw ≤ _; omega) (by show _ < (1 : Int); omega)
  have e : (RS Lsw (topS L k0)).addr k = Region.addr ⟨topS L k0, -Lsw, 1⟩ (-8 - 0 + k) := by
    rw [Region.callee_addr]; rfl
  have hf := L.pool_fit
  subst hrS
  obtain ⟨hs1, hs2⟩ := hsub
  simp only at hs1 hs2
  have ht : (topS L k0).toNat = (stacksA L.lab + k0).toNat + 16384 := by
    show (stacksA L.lab + k0 + 16384#64).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  change (((Region.addr ⟨topS L k0, -Lsw, 1⟩ (-8 - 0 + k)).toNat : Nat) : Int) = (topS L k0).toNat + (-8 - 0 + k) at ha
  rw [e]
  omega

section GenX

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Range} {lbl' : Lbl}
  {R : Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hX0 : ∀ s, freeNH (pcOf s) = true → X0 s)

  (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])

include hp hlo hlab hsite hcl hc0 hpl0 hX0 hsep ha hW


set_option hygiene false in
/-- The start's level at `ownGHXW`, with frames. -/
local notation "WSXL" => fun s c fs =>
  WSHFg (Spike.Lib.X64.HelloPh.ownGHXW L a) L ar p Dt Cl Ctx lbl lsize frM X0 fs s c

set_option maxHeartbeats 1600000 in
/-- **From `_start` to `wc_rodata`'s heap abort inside the start's level with frames, level 0**: the start up to
`scc_rt_main`'s entry at `[]` (`startEWP_W0SH`, `Rt.startEF_segWA` lifted), then at the new stack's top `topS L k0`
`HelloM.hello_main_pre_segWSTF` at `WS` from `scc_rt_main`'s entry in `RS Lsw (topS L k0)` (`mainPreWH_W0SH`;
`hWe` at `call wc_rodata`'s target), the source's call of `rodata` pushing `fr` into `J' v` (`hrun`, `hJ'`),
`wc_rodata` at `[fr]` (`hrd`), and its fresh-label landings in `ms [fr]`'s allocation fragment (`hxa`). Level 0
ends at rodata's landing, so the only exit is `wc_rodata`'s heap abort at `[fr]`. -/
theorem hello_start_rd_segWS0X (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hs : WSep L a) (hro : L.Λ.rodata.Disjoint L.Λ.stackPool) {k0 : BitVec 64}
    {Lsw : Int} {ms : List TermRun.Frame → MemSide isa} {pS : Prog} {lblS : Lbl} {fr : TermRun.Frame}
    (hK : (ms []).K = some abi) (hK' : (ms [fr]).K = some abi) (hwf : L.Λ.WF)
    (hC0 : CFacts L.Λ lbl' c0)
    (hF : FStable R F) {P : MachineData → Prop} (hP : FStable R P) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hRlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m)
    (hFw : ∀ m, F m → WordsNoneP L.Λ m.dmem)
    (hrS : rS = ⟨(stacksA L.lab + k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hLsw : 296 ≤ Lsw) (hL8 : Lsw % 8 = 0)
    (hk : k0.toNat + 16384 ≤ 536870912) (h8 : (topS L k0).toNat % 8 = 0)
    (hok : (swR (topS L k0) (-Lsw) 0).OK)
    (hsubS : ∀ k, (swR (topS L k0) (-Lsw) 0).Off k →
      ((swR (topS L k0) (-Lsw) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (topS L k0) (-Lsw) 0).addr k).toNat ∧
      rS.contains (((swR (topS L k0) (-Lsw) 0).addr k).toNat + 7))
    (hfitL : (limA (tpOf (tcbS L))).toNat + 8 ≤ 2 ^ 64)
    (houtL : ((limA (tpOf (tcbS L))).toNat : Int) + 8 ≤ (topS L k0).toNat + -Lsw ∨
      ((topS L k0).toNat : Int) + 0 ≤ (limA (tpOf (tcbS L))).toNat)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (Spike.Lib.X64.Flow.Ret0.takeMem pm rS m))
    (hoffP : ¬ (L.Λ.stackPool.lo < ((R.callee (-8) (-296) 8).addr (-48)).toNat ∧
      ((R.callee (-8) (-296) 8).addr (-48)).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size))
    (htcb : ∀ F' : MachineData → Prop, FStable (R.callee (-8) (-296) 8) F' →
      Spike.Lib.X64.KStable (Spike.Lib.X64.PhRec.K L rS) F' → (∀ m, F' m → F m) →
      ∀ g, g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x0L).toBitVec → ∀ i,
      Spike.Lib.X64.Flow.Ret0.TcbW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
        L.endPc ((R.callee (-8) (-296) 8).callee (-48 - 0) (-184) 8) F' ⟨g, 0#64, c0⟩ i)
    (hti : ∀ F' : MachineData → Prop, FStable (R.callee (-8) (-296) 8) F' →
      Spike.Lib.X64.KStable (Spike.Lib.X64.PhRec.K L rS) F' → (∀ m, F' m → F m) →
      ∀ g, g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x1L).toBitVec → ∀ i,
      Spike.Lib.X64.Rt.TiWAtP (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
        L.endPc ((R.callee (-8) (-296) 8).callee (-48 - 0) (-248) 8) F' (Spike.Lib.X64.Flow.Ret0.StackM rS)
        ⟨g, tcbS L, k0, c0⟩ Spike.Lib.X64.Rt.x8L P i)
    (htcbX : ∀ F' : MachineData → Prop, FStable (R.callee (-8) (-296) 8) F' →
      Spike.Lib.X64.KStable (Spike.Lib.X64.PhRec.K L rS) F' → (∀ m, F' m → F m) →
      ∀ g, g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x0L).toBitVec → ∀ i,
      Spike.Lib.X64.Flow.Ret0.TcbW (WSHX L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
        L.endPc ((R.callee (-8) (-296) 8).callee (-48 - 0) (-184) 8) F' ⟨g, 0#64, c0⟩ i)
    (htiX : ∀ F' : MachineData → Prop, FStable (R.callee (-8) (-296) 8) F' →
      Spike.Lib.X64.KStable (Spike.Lib.X64.PhRec.K L rS) F' → (∀ m, F' m → F m) →
      ∀ g, g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x1L).toBitVec → ∀ i,
      Spike.Lib.X64.Rt.TiWAtP (WSHX L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
        L.endPc ((R.callee (-8) (-296) 8).callee (-48 - 0) (-248) 8) F' (Spike.Lib.X64.Flow.Ret0.StackM rS)
        ⟨g, tcbS L, k0, c0⟩ Spike.Lib.X64.Rt.x8L P i)
    (hhdr : StOk (ms []) F (pinA L.lab + 0#64) (Spike.Lib.X64.Flow.Ret0.AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcbO : ∀ g, Spike.Lib.X64.Rt.TcbOkA (ms []) F L.exe L.endPc
      ((R.callee (-8) (-296) 8).callee (-48 - 0) (-184) 8) F ⟨g, 0#64, c0⟩)
    (hfld : ∀ e ∈ Spike.Lib.X64.Flow.Ret0.ThreadInit.fields (tcbS L) (stacksA L.lab + k0),
      StOk (ms []) F (tcbS L + BitVec.ofNat 64 e.1) e.2)
    (htk : ∀ g, Spike.Lib.X64.Rt.TakeOkA (ms []) F L.exe L.endPc
      (((R.callee (-8) (-296) 8).callee (-48 - 0) (-248) 8).callee (-48 - 0) (-200) 8) F ⟨g, k0, c0⟩)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA (tpOf (tcbS L))) 8 = none)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) false ⟨limA (tpOf (tcbS L)), 8⟩ = true)
    (hlimM : LimOk (ms []) F (limA (tpOf (tcbS L))) (topS L k0 - 8#64 - 8#64 - (64 : Int64).toBitVec))
    (hlimR : LimOk (ms [fr]) F (limA (tpOf (tcbS L)))
      (topS L k0 - 8#64 - 8#64 - 64#64 - 8#64 - 8#64 - (32 : Int64).toBitVec))
    (hH : ∀ fs, L.Λ.heap.lo ≤ (ms fs).heap)
    (hHi : ∀ fs, (ms fs).heap + 16 * (ms fs).cells ≤ L.Λ.heap.lo + L.Λ.heap.size)
    (hctr : ∀ fs, WordIn L.Λ.heap (ms fs).ctr ∨ WordIn L.Λ.data (ms fs).ctr)
    (hoff : ∀ q : Call, q.OK (ms [fr]) L.lab → (ms [fr]).off q.n q.τ ≤ 16 * (ms [fr]).units q.n q.τ)
    {J' : BitVec 64 → FAS → Ctl → Prop} {J1 : FAS → FAS → Ctl → Prop}
    (hWe : ∀ v s c, At L.exe L.endPc (RS Lsw v) (FS L rS Lsw k0 v) (mNC L.lab (RS Lsw v) (JS L k0 c0)) s c →
      WSXL s c [])
    (hrun : ∀ v σ c, (mNC L.lab (RS Lsw v) (JS L k0 c0)).J σ c → ∃ c', FrameRun pS (c, []) (c', [fr]) ∧ J' v σ c')
    (hJ' : ∀ v σ c', J' v σ c' → ∃ c, (mNC L.lab (RS Lsw v) (JS L k0 c0)).J σ c)
    (hrd : ∀ v m0 σC, RdPreW (tpG (tpOf (tcbS L)) fun s c => WSXL s c [fr])
      (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc (mR (RS Lsw v)) (mF (RS Lsw v) (FS L rS Lsw k0 v) m0 σC)
      (ms [fr]) (mRdJ0 (J' v) σC) (J1 σC))
    (hloc : ∀ σC σ c, mRdJ0 (J' (topS L k0)) σC σ c → ∃ c', LocalRun pS c c' ∧ J1 σC σ c')
    (hq : ∀ σC σ c, J1 σC σ c → ∃ q : Call, q.OK (ms [fr]) L.lab ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u (ms [fr]) = 3#64)
    (hxa : ∀ v m0 σC, ∀ q : AG (ms [fr]) L.lab, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF (RS Lsw v) (FS L rS Lsw k0 v) m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Abs (mR (RS Lsw v)) ⟨-48, []⟩ mC σ ∧
        (rN L.lab (mR (RS Lsw v)) (mRdJ0 (J' v) σC) (J1 σC) .call).J σ c ∧
        (Spike.Lib.X64.Alloc.N L.lab (ms [fr]) q.1 .e).J (enter (-48) σ) c ∧
        CKept (mR (RS Lsw v)) (-48) (-160) 8 mC m) →
      ∀ l b w s c, lblS l = none → At L.exe L.endPc (aR (mR (RS Lsw v))) F' (Ea (ms [fr]) q.1 l b w) s c →
        TP (tpOf (tcbS L)) s → (ms [fr]).xa l b w s c) :
    SegWS (WSXL) (Spike.Lib.X64.PhRec.K L rS) pS lblS ms
      ((At L.exe L.endPc R (fun m => F m ∧ P m) (Spike.Lib.X64.Rt.entryN0 L.lab c0)).at [])
      (Frag.at (fun s c => ∃ v m0 σC,
          At L.exe L.endPc (mR (RS Lsw v)) (mF (RS Lsw v) (FS L rS Lsw k0 v) m0 σC)
            (rX (ms [fr]) L.lab lblS (mR (RS Lsw v)) (J1 σC) .abort) s c ∧
          TP (tpOf (tcbS L)) s) [fr]) := by
  have hpS : Lays L.exe helloCells L.pfx := hp ▸ L.lays
  have hendS : L.endPc = endOf L.exe helloCells L.pfx := by show endOf L.exe L.prog L.pfx = _; rw [hp]
  have hL : 8 ≤ Lsw := by omega
  have hFwS := fun v => Spike.Lib.X64.Rt.wordsNoneP_swFSL_fstable (v := v) hwf hsub hok hL hL8 hsubS
    hfitL houtL hfit
  have hA := Spike.Lib.X64.Rt.startEF_segWA (Fw := WordsNoneP L.Λ) (p := pS) (lbl := lblS) (ms := ms []) hpS hendS
    hello_rtCodeInTi hL hK hF hR hal hRlo hhi 0#64 k0 c0 (by decide) hhdr htcbO hk hfld htk
    hok hsubS hun hFw hFwS hRS hfit houtS hFt hP
    (OwnSt.startEXPH hp hlab hsite hsep ha hW hlo hR hRlo hhi hL hok hoffP hrS hsub
      (StartWf.startEWP_W0SH hp hlo hlab hsite hcl hc0 hpl0 hX0 hΛ hs hro hC0 hR hRlo hhi
        hFr rfl hrS hsub houtS h8 hok hL hL8 hoffP htcb hti) htcbX htiX)
  refine (SegWS.liftS (W := WSXL) [] hA fun _ _ h => h).seq ?_
  refine (SegWS.exists_pre (P := fun v : BitVec 64 => Frag.at (fun s c => (swR v (-Lsw) 0).OK ∧
      At L.exe L.endPc (RS Lsw v) (FS L rS Lsw k0 v) (mainE0 L.lab (gS L k0 c0)) s c) [])
    fun v => ?_).mono_pre fun _ _ _ ⟨⟨v, h⟩, e⟩ => ⟨v, h, e⟩
  by_cases hv : v = topS L k0
  case neg =>
    exact SegWS.empty fun _ _ _ ⟨⟨_, _, _, _, _, _, _, hFS, _⟩, _⟩ => hv hFS.1.2.1.1
  subst hv
  refine (SegWS.exists_pre (P := fun _ : (swR (topS L k0) (-Lsw) 0).OK =>
      (At L.exe L.endPc (RS Lsw (topS L k0)) (FS L rS Lsw k0 (topS L k0)) (mainE0 L.lab (gS L k0 c0))).at [])
    fun hv => ?_).mono_pre fun _ _ _ ⟨⟨h1, h2⟩, e⟩ => ⟨h1, h2, e⟩
  have hR2 := Spike.Lib.X64.Rt.mainEF_ok (tcb := tcbS L) hL hL8 hv (hFwS (topS L k0))
  have hb := Region.callee_base (kc := -8 - 0) (lo' := 8 - Lsw) (hi' := 8) hv
    (by show -Lsw ≤ -8 - 0 + (8 - Lsw); omega) (by omega) (by show (-8 : Int) - 0 < 0; decide)
  have hR8 : (RS Lsw (topS L k0)).base.toNat % 8 = 0 := by
    change ((RS Lsw (topS L k0)).base.toNat : Int) = (topS L k0).toNat + (-8 - 0) at hb
    omega
  have hpre := MainWf.mainPreWH_W0SH (R := RS Lsw (topS L k0)) (F := FS L rS Lsw k0 (topS L k0)) (ms := ms [])
    (J := JS L k0 c0) (tp := tpOf (tcbS L)) (a := a) (ar := ar) (Dt := Dt) (Ctx := Ctx) (lsize := lsize)
    (frM := frM)
    hp hlo hlab hsite hcl hc0 hpl0 hX0 hΛ (fun _ _ h => ⟨h.1.1, h.1.2.2⟩) hC0 hR2.1 hR8
    (show 8 - Lsw ≤ -288 by omega) (show (8 : Int) ≤ 8 by decide) (show (8 - Lsw) % 8 = 0 by omega)
    (show (8 : Int) % 8 = 0 by decide) hsub hfit (fun _ h => stackOff_RS hv hL h.1.2.2) hmr (fun _ h => h.1.2.1.2)
  have hpreX := MainPreX.mainPreWHX hp hlab hsite hsep ha hW (bandRS80 hrS hsub (by omega) hv) hR2.1
    (show 8 - Lsw ≤ -288 by omega) (show (8 : Int) ≤ 8 by decide) (fun _ _ h => h.1.2.2) (fun _ h => h.1.2.1.2) hpre
  refine (Spike.Lib.X64.Flow.HelloM.hello_main_pre_segWSTF (W := WSXL)
    (K := Spike.Lib.X64.PhRec.K L rS) (p := pS) (lbl := lblS) (ms := ms) (fs1 := [fr]) (J1 := J1) hpS hendS hK'
    hR2.2 hR2.1 (show 8 - Lsw ≤ -288 by omega) (show (8 : Int) ≤ 8 by decide) hpreX.1 hpreX.2 (hWe (topS L k0))
    (by rintro σ c ⟨σe, hJe, -, -, -, -, hfs, -, -⟩; exact hfs.trans hJe.1.2.2) (hrun (topS L k0))
    (hJ' (topS L k0)) (hrd (topS L k0))
    (Spike.Lib.X64.WakePh.MainWf.limOk_mainE0 (f := fun x => x - 8#64 - (64 : Int64).toBitVec)
      ⟨hlimM.rt, hlimM.mp, fun _ h => h.1.2.1.2, hlimM.room⟩)
    (Spike.Lib.X64.WakePh.MainWf.limOk_mainE0
      (f := fun x => x - 8#64 - 64#64 - 8#64 - 8#64 - (32 : Int64).toBitVec)
      ⟨hlimR.rt, hlimR.mp, fun _ h => h.1.2.1.2, hlimR.room⟩)
    hloc hq
    (Spike.Lib.X64.Alloc.hmem_of_wordsNone hwf (fun _ h => h.1.1.wn) (hH _) (hHi _) (hctr _) hoff)
    (hxa (topS L k0))).mono_post ?_
  rintro s c fs ⟨⟨m0, σC, h, ht⟩, rfl⟩
  exact ⟨⟨topS L k0, m0, σC, h, ht⟩, rfl⟩

end GenX

end Spike.Lib.X64.HelloPh.StartWcS0

/-- info: 'Spike.Lib.X64.HelloPh.StartWcS0.bandRS80' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartWcS0.bandRS80

/-- info: 'Spike.Lib.X64.HelloPh.StartWcS0.hello_start_rd_segWS0X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartWcS0.hello_start_rd_segWS0X
