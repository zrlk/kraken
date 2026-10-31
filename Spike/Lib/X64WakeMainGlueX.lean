/-
**From `_start` to `wc_main`'s heap abort inside the start's level at
`ownGXW`** (x86-64): `MainGlue.wake_start_wc_segW` with the start's level
`StartWf.WS` (at `ownG`) replaced by `OwnImp.WSX` (at `ownGXW`, main's and
the worker's TCB words appended): the start up to the switch by
`OwnSt.startEXP` (from `StartWf.startEWP_W0S` inside `WS`, the callees'
states inside `WSX`), `scc_rt_main` up to `call wc_main` by
`MainPreX.mainPreWWX` (from `MainWf.mainPreWW_W0S`), and `wc_main` from its
entry to its heap abort by `WakeWc.wake_wc_entry_segJm` (generic in the
level).

- `bandRS`: `scc_rt_main`'s region band `[-48, 8]` at the new stack's top
  lies on the pool (`mainPreWWX`'s `hb`).
- `wake_start_wc_segWX`: the composed segment inside `WSX`.

Where x86-64 differs from AArch64: AArch64's start owns `ownG` throughout
(`A64WakeMainGlue`). x86-64's main also holds its own TCB word from
`scc_rt_start`'s `.x1` on (`ownS`) and the worker's while it starts it
(`ownSW`), so the segment is stated inside `WSX`. `startEXP` lifts
`startEWP_W0S`'s `StartEWFP` inside `WS`, so the callees' states are needed
inside both levels (`htcb`, `hti` inside `WS`; `htcbX`, `htiX` inside
`WSX`); `ownGXW`'s separation (`hsep`, `ha`, `hW`) is carried; `hWp`, `hWs`
are inside `WSX`. The rest is `wake_start_wc_segW`'s.
-/
import Spike.Lib.X64WakeMainGlue
import Spike.Lib.X64WakeOwnStartEP
import Spike.Lib.X64WakeMainPreX

namespace Spike.Lib.X64.WakePh.MainGlue

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (Lays endOf)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout mainE0 swFSL)
open Spike.Lib.X64Consumer (Lbl Lsize CFacts)
open Spike.Lib.X64.WakeWf (RunWf)
open Spike.Lib.X64.WakePh.WcW (freeN)
open Spike.Lib.X64.WakePh.StartWf (WS)
open Spike.Lib.X64 (swR FStable At)
open Spike.Lib.X64.Flow.Ret0 (pinA stacksA limA tpOf LimOk StOk StackOff MainG CallerCells)
open Spike.Lib.X64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.X64.Flow.WakeWc (WcPreW WcSp0W AGB BoxW bX wX)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Spike.Lib.X64.WakeTP (tpG)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.DmemPriv (WordsNone WordIn)
open Spike.Lib.X64.DmemPriv (WordsNoneP)
open Spike.Lib (Arena FragS SegW Region)

/-- **`scc_rt_main`'s region band `[-48, 8]` lies on the pool**: its
addresses are the new stack's top less `56` up to the top, inside the stack
`rS` (`hrS`), which lies in the pool (`hsub`). -/
theorem bandRS {L : RuntimeLayout} {rS : Range} {k0 : BitVec 64} {Lsw : Int}
    (hrS : rS = ⟨(stacksA L.lab + k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hLsw : 56 ≤ Lsw) (hok : (swR (topS L k0) (-Lsw) 0).OK) :
    BandOnP L (RS Lsw (topS L k0)) (-48) 8 := by
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

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Range} {lbl' : Lbl}
  {R : Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hX0 : ∀ s, freeN (pcOf s) = true → X0 s)

include hp hlo hlab hsite hcl hc0 hpl0 hX0

set_option maxHeartbeats 1600000 in
/-- **From `_start` to `wc_main`'s heap abort inside `WSX`, the take
site's frame also `P`**: the start up to the switch (`startEXP` of
`startEWP_W0S`), at the new stack's top `scc_rt_main` up to `call wc_main`
(`mainPreWWX` of `mainPreWW_W0S`) and `wc_main` into a region `D` deep
(`wake_wc_entry_segJm`). -/
theorem wake_start_wc_segWX (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hs : Spike.Lib.X64.WakePh.WSep L a)
    (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool) {k0 : BitVec 64}
    {Lsw D : Int} {ms : Spike.Lib.MemSide isa} {pS : Prog} {lblS : Lbl}
    (hK : ms.K = some abi) (hwf : L.Λ.WF) (hC0 : CFacts L.Λ lbl' c0)
    (hF : FStable R F) {P : MachineData → Prop} (hP : FStable R P) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hRlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m)
    (hFw : ∀ m, F m → WordsNoneP L.Λ m.dmem)
    (hrS : rS = ⟨(stacksA L.lab + k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hD8 : D % 8 = 0) (hD : 240 ≤ D) (hLsw : 56 + D ≤ Lsw) (hL8 : Lsw % 8 = 0)
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
      Spike.Lib.X64.Flow.Ret0.TcbW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
        L.endPc ((R.callee (-8) (-296) 8).callee (-48 - 0) (-184) 8) F' ⟨g, 0#64, c0⟩ i)
    (hti : ∀ F' : MachineData → Prop, FStable (R.callee (-8) (-296) 8) F' →
      Spike.Lib.X64.KStable (Spike.Lib.X64.PhRec.K L rS) F' → (∀ m, F' m → F m) →
      ∀ g, g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x1L).toBitVec → ∀ i,
      Spike.Lib.X64.Rt.TiWAtP (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
        L.endPc ((R.callee (-8) (-296) 8).callee (-48 - 0) (-248) 8) F' (Spike.Lib.X64.Flow.Ret0.StackM rS)
        ⟨g, tcbS L, k0, c0⟩ Spike.Lib.X64.Rt.Code.Ti.x7L P i)
    (htcbX : ∀ F' : MachineData → Prop, FStable (R.callee (-8) (-296) 8) F' →
      Spike.Lib.X64.KStable (Spike.Lib.X64.PhRec.K L rS) F' → (∀ m, F' m → F m) →
      ∀ g, g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x0L).toBitVec → ∀ i,
      Spike.Lib.X64.Flow.Ret0.TcbW (WSX L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
        L.endPc ((R.callee (-8) (-296) 8).callee (-48 - 0) (-184) 8) F' ⟨g, 0#64, c0⟩ i)
    (htiX : ∀ F' : MachineData → Prop, FStable (R.callee (-8) (-296) 8) F' →
      Spike.Lib.X64.KStable (Spike.Lib.X64.PhRec.K L rS) F' → (∀ m, F' m → F m) →
      ∀ g, g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x1L).toBitVec → ∀ i,
      Spike.Lib.X64.Rt.TiWAtP (WSX L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
        L.endPc ((R.callee (-8) (-296) 8).callee (-48 - 0) (-248) 8) F' (Spike.Lib.X64.Flow.Ret0.StackM rS)
        ⟨g, tcbS L, k0, c0⟩ Spike.Lib.X64.Rt.Code.Ti.x7L P i)
    (hhdr : StOk ms F (pinA L.lab + 0#64) (Spike.Lib.X64.Flow.Ret0.AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcbO : ∀ g, Spike.Lib.X64.Rt.TcbOkA ms F L.exe L.endPc
      ((R.callee (-8) (-296) 8).callee (-48 - 0) (-184) 8) F ⟨g, 0#64, c0⟩)
    (hfld : ∀ e ∈ Spike.Lib.X64.Flow.Ret0.ThreadInit.fields (tcbS L) (stacksA L.lab + k0),
      StOk ms F (tcbS L + BitVec.ofNat 64 e.1) e.2)
    (htk : ∀ g, Spike.Lib.X64.Rt.TakeOkA ms F L.exe L.endPc
      (((R.callee (-8) (-296) 8).callee (-48 - 0) (-248) 8).callee (-48 - 0) (-200) 8) F ⟨g, k0, c0⟩)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA (tpOf (tcbS L))) 8 = none)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) false ⟨limA (tpOf (tcbS L)), 8⟩ = true)
    (hlim48 : LimOk ms F (limA (tpOf (tcbS L))) (topS L k0 - 8#64 - 8#64 - (32 : Int64).toBitVec))
    (hlim120 : LimOk ms F (limA (tpOf (tcbS L))) (topS L k0 - 8#64 - 120#64))
    (hq0 : ∃ q : Call, q.OKB ms L.lab ∧ q.c0 = c0 ∧ q.h = 256#64 ∧ q.k = 1#64 ∧ q.u ms = 2#64)
    (hH : L.Λ.heap.lo ≤ ms.heap) (hHi : ms.heap + 16 * ms.cells ≤ L.Λ.heap.lo + L.Λ.heap.size)
    (hroom : ms.heap + 16 * ms.cells ≤ 2 ^ 64)
    (hctr : WordIn L.Λ.heap ms.ctr ∨ WordIn L.Λ.data ms.ctr)
    (hoff : ∀ q : Call, q.OKB ms L.lab → ms.off q.n q.τ ≤ 16 * ms.units q.n q.τ)
    (hoB : ∀ q : AGB ms L.lab, q.1.c0 = c0 → ms.off 1 q.1.τ + 16 ≤ 16 * ms.units 1 q.1.τ)
    (hmp : ∀ q : AGB ms L.lab, q.1.c0 = c0 → ∀ o : Nat, ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true)
    (hbox : ∀ q : AGB ms L.lab, q.1.c0 = c0 → BoxW lblS q.1)
    (hWp : ∀ v m0 σC, WcPreW (Spike.Lib.X64.NoSetFsW (tpG (tpOf (tcbS L)) (WSX L a ar p Dt Cl Ctx lbl lsize frM X0))
        (Spike.Lib.X64.PhRec.K L rS))
      (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc (wR (RS Lsw v) D) (wF (RS Lsw v) D (FS L rS Lsw k0 v) m0 σC)
      (tpXa ms (tpOf (tcbS L))) (wJ0 (wNC L.lab (JS L k0 c0)).J σC) (wJ0 (wNC L.lab (JS L k0 c0)).J σC))
    (hWs : ∀ v m0 σC, WcSp0W (Spike.Lib.X64.NoSetFsW (tpG (tpOf (tcbS L)) (WSX L a ar p Dt Cl Ctx lbl lsize frM X0))
        (Spike.Lib.X64.PhRec.K L rS))
      (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc (wR (RS Lsw v) D) (wF (RS Lsw v) D (FS L rS Lsw k0 v) m0 σC)
      (tpXa ms (tpOf (tcbS L))) (wJ0 (wNC L.lab (JS L k0 c0)).J σC))
    (hxa : ∀ v m0 σC l A s c, lblS l = none →
      At L.exe L.endPc ((wR (RS Lsw v) D).fp (-8)) (wF (RS Lsw v) D (FS L rS Lsw k0 v) m0 σC)
        (bX ms L.lab (wJ0 (wNC L.lab (JS L k0 c0)).J σC) l A) s c →
      TP (tpOf (tcbS L)) s → ms.xa l A 1 s c) :
    SegW (WSX L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) pS lblS ms
      (At L.exe L.endPc R (fun m => F m ∧ P m) (Spike.Lib.X64.Rt.entryN0 L.lab c0))
      (fun s c => ∃ v m0 σC,
        At L.exe L.endPc (wR (RS Lsw v) D) (wF (RS Lsw v) D (FS L rS Lsw k0 v) m0 σC)
          (wX ms L.lab (wR (RS Lsw v) D) (wJ0 (wNC L.lab (JS L k0 c0)).J σC) .abort) s c ∧
        TP (tpOf (tcbS L)) s) := by
  have hpS : Lays L.exe wakeCells L.pfx := hp ▸ L.lays
  have hendS : L.endPc = endOf L.exe wakeCells L.pfx := by show endOf L.exe L.prog L.pfx = _; rw [hp]
  have hL : 8 ≤ Lsw := by omega
  have hFwS := fun v => Spike.Lib.X64.Rt.wordsNoneP_swFSL_fstable (v := v) hwf hsub hok hL hL8 hsubS
    hfitL houtL hfit
  refine (Spike.Lib.X64.Rt.startEF_segWA (Fw := WordsNoneP L.Λ) hpS hendS
    Spike.Lib.X64.WakePh.wake_rtCodeInTi hL hK hF hR hal hRlo hhi 0#64 k0 c0 (by decide) hhdr htcbO hk hfld htk
    hok hsubS hun hFw hFwS hRS hfit houtS hFt hP
    (Spike.Lib.X64.WakePh.OwnSt.startEXP hp hlab hsite hsep ha hW hlo hR hRlo hhi hL hok hoffP hrS hsub
      (Spike.Lib.X64.WakePh.StartWf.startEWP_W0S hp hlo hlab hsite hcl hc0 hpl0 hX0 hΛ hs hro hC0 hR hRlo hhi
        hFr rfl hrS hsub houtS h8 hok hL hL8 hoffP htcb hti) htcbX htiX)).seq ?_
  refine SegW.exists_pre fun v => ?_
  by_cases hv : v = topS L k0
  case neg =>
    exact SegW.empty fun _ _ ⟨_, _, _, _, _, _, _, hFS, _⟩ => hv hFS.1.2.1.1
  subst hv
  refine (SegW.exists_pre (P := fun _ : (swR (topS L k0) (-Lsw) 0).OK =>
      At L.exe L.endPc (RS Lsw (topS L k0)) (FS L rS Lsw k0 (topS L k0)) (mainE0 L.lab (gS L k0 c0)))
    fun hv => ?_).mono_pre fun _ _ ⟨h1, h2⟩ => ⟨h1, h2⟩
  have hR2 := Spike.Lib.X64.Rt.mainEF_ok (tcb := tcbS L) hL hL8 hv (hFwS (topS L k0))
  have hb := Region.callee_base (kc := -8 - 0) (lo' := 8 - Lsw) (hi' := 8) hv
    (by show -Lsw ≤ -8 - 0 + (8 - Lsw); omega) (by omega) (by show (-8 : Int) - 0 < 0; decide)
  have hR8 : (RS Lsw (topS L k0)).base.toNat % 8 = 0 := by
    change ((RS Lsw (topS L k0)).base.toNat : Int) = (topS L k0).toNat + (-8 - 0) at hb
    omega
  refine (Spike.Lib.X64.Flow.WakeM.wake_main_pre_segW hpS hendS (by omega) hD8 hR2.2 hR2.1
    (show 8 - Lsw ≤ -48 - D by omega) (show (0 : Int) ≤ 8 by decide)
    (Spike.Lib.X64.WakePh.MainPreX.mainPreWWX hp hlab hsite hsep ha hW (bandRS hrS hsub (by omega) hv) hR2.1
      (show 8 - Lsw ≤ -48 by omega) (show (0 : Int) ≤ 8 by decide) (fun _ _ h => h.1.2.2) (fun _ h => h.1.2.1.2)
      (Spike.Lib.X64.WakePh.MainWf.mainPreWW_W0S hp hlo hlab hsite hcl hc0 hpl0 hX0 hΛ
        (fun _ _ h => ⟨h.1.1, h.1.2.2⟩) hC0 hR2.1 hR8
        (show 8 - Lsw ≤ -48 by omega) (show (0 : Int) ≤ 8 by decide) (show (8 - Lsw) % 8 = 0 by omega)
        (show (8 : Int) % 8 = 0 by decide) hsub hfit
        (fun _ h => stackOff_RS hv hL h.1.2.2) hmr (fun _ h => h.1.2.1.2)))
    (Spike.Lib.X64.WakePh.MainWf.limOk_mainE0 (f := fun x => x - 8#64 - (32 : Int64).toBitVec)
      ⟨hlim48.rt, hlim48.mp, fun _ h => h.1.2.1.2, hlim48.room⟩)
    fun m0 σC hok' hFS' => Spike.Lib.X64.Flow.WakeWc.wake_wc_entry_segJm hK hpS hendS hFS' hok'
      (show -D ≤ -240 by omega) (show (8 : Int) ≤ 8 by decide)
      (fun _ _ h => Spike.Lib.X64.Flow.WakeHtp.mainJ_tp h)
      (hWp (topS L k0) m0 σC) (hWs (topS L k0) m0 σC)
      (Spike.Lib.X64.WakePh.MainWf.limOk_mainE0 (f := fun x => x - 120#64)
        ⟨hlim120.rt, hlim120.mp, fun _ h => h.1.2.1.2, hlim120.room⟩)
      (Spike.Lib.X64.WakePh.MainWf.ctl_mainE0 (P := fun c => ∃ q : Call, q.OKB ms L.lab ∧ q.c0 = c ∧
        q.h = 256#64 ∧ q.k = 1#64 ∧ q.u ms = 2#64) hq0)
      (Spike.Lib.X64.WakePh.StartGlue.hmemB_of_wordsNone hwf (fun _ h => h.1.1.wn) hH hHi hctr hoff)
      (fun q ⟨σ, h⟩ => hbox q (Spike.Lib.X64.WakePh.MainWf.ctl_mainE0 (P := fun c => c = c0) rfl σ _ h))
      (fun q ⟨σ, h⟩ => Spike.Lib.X64.WakePh.StartGlue.hcellB_of_wordsNone (P := fun q => q.c0 = c0)
        (fun _ h => h.1.1.wn) hH hHi hroom hoB hmp
        q (Spike.Lib.X64.WakePh.MainWf.ctl_mainE0 (P := fun c => c = c0) rfl σ _ h))
      (hxa (topS L k0) m0 σC)).mono_post
    fun _ _ ⟨m0, σC, h⟩ => ⟨topS L k0, m0, σC, h⟩

end Gen

end Spike.Lib.X64.WakePh.MainGlue

/-- info: 'Spike.Lib.X64.WakePh.MainGlue.bandRS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.MainGlue.bandRS

/-- info: 'Spike.Lib.X64.WakePh.MainGlue.wake_start_wc_segWX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.MainGlue.wake_start_wc_segWX
