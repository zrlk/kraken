/-
**hello.w on x86-64 from `_start` to `wc_rodata`'s heap abort at depth, level 0** (the twin of
`Spike/Lib/A64HelloStartWcS0.lean`): the start up to `scc_rt_main`'s entry at `[]` (`Rt.startEF_segWA` of
`StartWf.startEWP_W0SH`, lifted by `SegWS.liftS`), then at the new stack's top `HelloM.hello_main_pre_segWSTF`
from `scc_rt_main`'s entry (`MainWf.mainPreWH_W0SH`; `wc_rodata` at `[fr]`, its allocator's return being its
allocation, landing in `ms [fr]`'s `xa`). What follows the landing is level 1's.

- `hello_start_rd_segWS0`: from `_start` at `F ∧ P` to `wc_rodata`'s heap abort at `[fr]`, the thread pointer
  `tpOf (pinA + 8)` kept (via `HelloM.hello_main_pre_segWSTF`; `hxa` may assume it; needs `hK'`).

**Where this differs from AArch64** (forced by the x86-64 shape):
- `scc_rt_main` runs in `call scc_rt_main`'s callee region `RS Lsw v` (`Rt.MainEF`; AArch64: `swR v (-Lsw) 0`)
  under `FS`, which carries the caller's cells (`CallerCells`); its entry ghosts are `gS` (top less the return
  address). `MainEF` pins `v` to the new stack's top (`swF`), so only `v = topS L k0` is reached; the other
  bases are empty (`SegWS.empty`).
- The start's callees run in `R.callee (-8) (-296) 8`'s callee regions (`hoffP`, `htcb`, `hti`, `htcbO`, `htk`;
  AArch64: `R.callee oI.sp …`). `htcb` and `hti` are `startEWP_W0SH`'s (any `F'` stable in the start's region,
  `scc_rt_thread_init` returning to `x8L` with `P`; AArch64: `htcbW`, `htiW` at `F`), so `hSM`, `hSMi`, `hSMt`
  are not asked.
- The new top is `8`-aligned (`h8`; AArch64: `16`, `h16`), and the depth is `296 ≤ Lsw` so that `RS`'s low end
  `8 - Lsw` is at most `-288` (AArch64: `288 ≤ Lsw`).
- The limit words are at `tpOf (pinA + 8)`'s `limA`, with bounds `top - 8 - 8 - 64` (`hlimM`) and
  `top - 8 - 8 - 64 - 8 - 8 - 32` (`hlimR`), `scc_rt_main`'s `%rsp` at entry being `top - 8` (AArch64: `hlim80`,
  `hlim128` at `top - 80`, `top - 80 - 48`).
- `hxa`'s kept cells are `CKept (mR (RS Lsw v)) (-48) (-160) 8` (AArch64: `0`), and `mNC` takes the region.
- `rodata`'s call invariant `J'` is indexed by the switch base (`J' v`, AArch64: one `J'`): `mNC` at `RS Lsw v`
  pins `%rbp` to `(RS Lsw v).addr (-8)`, so a `v`-independent `J'` meeting `hJ'` at every `v` would be empty. The
  callers' `J' v := StartWcS.rdJH lab (RS Lsw v) J` (the `example` after the theorem).
-/
import Spike.Lib.X64HelloStartWcS
import Spike.Lib.X64HelloMainPreTF
import Spike.Lib.X64HelloStartWfP
import Spike.Lib.X64HelloMainWf
import Spike.Lib.X64WakeMainGlue
import Spike.Lib.X64WordsNone
import Spike.Lib.X64HelloFrameD

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
open Spike.Lib.X64.WakePh (WSep)
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
open Spike.Lib.X64.HelloPh.StartWcS (WS)
open Spike.Lib.DmemPriv (WordIn)
open Spike.Lib.X64.DmemPriv (WordsNoneP)
open Spike.Lib (Arena FragS Frag MemSide SegWS LocalRun FrameRun Region)
/-- The abstract state (`AS` alone is ambiguous here). -/
local notation "FAS" => Spike.Lib.X64.AS

section Gen

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

include hp hlo hlab hsite hcl hc0 hpl0 hX0

set_option maxHeartbeats 1600000 in
/-- **From `_start` to `wc_rodata`'s heap abort inside the start's level with frames, level 0**: the start up to
`scc_rt_main`'s entry at `[]` (`startEWP_W0SH`, `Rt.startEF_segWA` lifted), then at the new stack's top `topS L k0`
`HelloM.hello_main_pre_segWSTF` at `WS` from `scc_rt_main`'s entry in `RS Lsw (topS L k0)` (`mainPreWH_W0SH`;
`hWe` at `call wc_rodata`'s target), the source's call of `rodata` pushing `fr` into `J' v` (`hrun`, `hJ'`),
`wc_rodata` at `[fr]` (`hrd`), and its fresh-label landings in `ms [fr]`'s allocation fragment (`hxa`). Level 0
ends at rodata's landing, so the only exit is `wc_rodata`'s heap abort at `[fr]`. -/
theorem hello_start_rd_segWS0 (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
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
      WS L a ar p Dt Cl Ctx lbl lsize frM X0 s c [])
    (hrun : ∀ v σ c, (mNC L.lab (RS Lsw v) (JS L k0 c0)).J σ c → ∃ c', FrameRun pS (c, []) (c', [fr]) ∧ J' v σ c')
    (hJ' : ∀ v σ c', J' v σ c' → ∃ c, (mNC L.lab (RS Lsw v) (JS L k0 c0)).J σ c)
    (hrd : ∀ v m0 σC, RdPreW (tpG (tpOf (tcbS L)) fun s c => WS L a ar p Dt Cl Ctx lbl lsize frM X0 s c [fr])
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
    SegWS (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) pS lblS ms
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
    (StartWf.startEWP_W0SH hp hlo hlab hsite hcl hc0 hpl0 hX0 hΛ hs hro hC0 hR hRlo hhi
      hFr rfl hrS hsub houtS h8 hok hL hL8 hoffP htcb hti)
  refine (SegWS.liftS (W := WS L a ar p Dt Cl Ctx lbl lsize frM X0) [] hA fun _ _ h => h).seq ?_
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
  refine (Spike.Lib.X64.Flow.HelloM.hello_main_pre_segWSTF (W := WS L a ar p Dt Cl Ctx lbl lsize frM X0)
    (K := Spike.Lib.X64.PhRec.K L rS) (p := pS) (lbl := lblS) (ms := ms) (fs1 := [fr]) (J1 := J1) hpS hendS hK'
    hR2.2 hR2.1 (show 8 - Lsw ≤ -288 by omega) (show (8 : Int) ≤ 8 by decide) hpre.1 hpre.2 (hWe (topS L k0))
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

end Gen

/-- `hello_start_rd_segWS0`'s `J'` is indexed by the switch base: at the callers' shape
`J' v := StartWcS.rdJH lab (RS helloLsw v) J` (main's `mNC` at `v`, whose `%rbp` is `(RS helloLsw v).addr (-8)`),
`hJ'` is `rdJH`'s second conjunct and `hrun` is `StartWcS.rdJH_run` at each `v` (non-vacuity of the indexing). -/
example {lab : Label → Int64} {J : FAS → Ctl → Prop} {env : TermRun.Env}
    (hJ : ∀ σ c, J σ c → c = ⟨Scc.Sem.SrcSem.setupTerm, env, none⟩)
    (hu : TermRun.evalAt env (.var "u") = some (.unit, [])) :
    (∀ v σ c', Spike.Lib.X64.HelloPh.StartWcS.rdJH lab (RS Spike.Lib.X64.HelloPh.StartH0G.helloLsw v) J σ c' →
      ∃ c, (mNC lab (RS Spike.Lib.X64.HelloPh.StartH0G.helloLsw v) J).J σ c) ∧
    (∀ v σ c, (mNC lab (RS Spike.Lib.X64.HelloPh.StartH0G.helloLsw v) J).J σ c →
      ∃ c', FrameRun Spike.Lib.X64HelloSrc.helloSrc (c, []) (c', [Spike.Lib.X64HelloRdCf.frH env]) ∧
        Spike.Lib.X64.HelloPh.StartWcS.rdJH lab (RS Spike.Lib.X64.HelloPh.StartH0G.helloLsw v) J σ c') :=
  ⟨fun _ _ _ h => h.2, fun _ => Spike.Lib.X64.HelloPh.StartWcS.rdJH_run hJ hu⟩

end Spike.Lib.X64.HelloPh.StartWcS0

/-! ## Axioms -/

/--
info: 'Spike.Lib.X64.HelloPh.StartWcS0.hello_start_rd_segWS0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartWcS0.hello_start_rd_segWS0
