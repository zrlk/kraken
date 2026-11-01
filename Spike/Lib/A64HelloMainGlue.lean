/-
**From `_start` to `wc_rodata`'s allocator's return inside `W0`, at hello**
(AArch64; hello twin of the first half of `A64WakeMainGlue`): `Rt.startEF_segWA` at
the start's level `HelloPh.StartWf.WSH` (its blocks by `StartWf.startEW_W0SH`, the
frame after the switch strengthened by `DmemPriv.WordsNone`), then, at each base of
the new stack, `HelloM.hello_main_pre_segW`: `scc_rt_main`'s prologue and
`bl wc_rodata` (`MainWf.mainPreWH_W0SH`) and **`wc_rodata`'s segment** up to its
allocator's return (hello's `scc_rt_main` calls `wc_rodata` before `wc_main`; wake's
glue goes straight into `wc_main`).

- `hello_start_rd_segW`: the composed segment, from `_start` at the frame `F ∧ P` to
  `wc_rodata`'s exits (`HelloRd.rX`: its `.sp0` after the allocator or its heap
  abort) in its region at the call. Left as premises, as in wake: the memory side's
  facts, the two callees' states (`htcbW`, `htiW`), the region facts, and
  `wc_rodata`'s own states inside `W` (`hWrd`, `HelloM.MainPreW.rd` at `WSH`: no
  `ownGH` twin of rodata's nodes yet), its source run (`hloc`, `hq`) and fresh-label
  landing (`hxa`). The allocator's words come from `WordsNone`
  (`Alloc.hmem_of_wordsNone`).

The rest (`wc_rodata` from `.sp0`, `bl wc_main`, `wc_main` to its clone/heap abort:
`HelloM.hello_main_post_segW`) has no `W0` glue here yet.
-/
import Spike.Lib.A64HelloStartGlue
import Spike.Lib.A64WakeMainGlue

namespace Spike.Lib.A64.HelloPh.MainGlue

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
open Spike.Lib.A64.Flow (swR FStable NoMsrW)
open Spike.Lib.A64.Flow.Ret0 (pinA stacksA limA LimOk StOk entryN MainG)
open Spike.Lib.A64.WakePh.MainGlue (gS FS JS)
open Spike.Lib.A64.Flow.Hello1 (AG mR mF mRdJ0 mNC)
open Spike.Lib.A64.Flow.HelloRd (rN rX)
open Spike.Lib.A64.Alloc (Call Ea)
open Spike.Lib.DmemPriv (WordsNone WordsNoneP WordIn)
open Spike.Lib (Arena FragS SegW)

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

/-- **From `_start` to `wc_rodata`'s allocator's return inside the start's level**:
the start up to the switch (`startEW_W0SH`), at each base `v` of the new stack of
depth `Lsw` `scc_rt_main` up to `bl wc_rodata` (`mainPreWH_W0SH`) and `wc_rodata`
up to its allocator's return (`hello_main_pre_segW`).

Superseded: frameless, so vacuous at the real run (`rodata` called under a frame); use
`StartWcS.hello_start_wc_segWS` (`Spike/Lib/A64HelloStartWcS.lean`). -/
theorem hello_start_rd_segW (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
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
    {J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.A64.Flow.AS → Ctl → Prop}
    (hWrd : ∀ v m0 σC, Spike.Lib.A64.Flow.HelloRd.RdPreW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0)
      (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc (mR (swR v (-Lsw) 0)) (mF (swR v (-Lsw) 0) (FS L rS Lsw k0 v) m0 σC)
      ms (mRdJ0 (mNC L.lab (JS L k0 c0)).J σC) (J1 σC))
    (hloc : ∀ σC σ c, mRdJ0 (mNC L.lab (JS L k0 c0)).J σC σ c → ∃ c', Spike.Lib.LocalRun pS c c' ∧ J1 σC σ c')
    (hq : ∀ σC σ c, J1 σC σ c → ∃ q : Call, q.OK ms L.lab ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ms = 3#64)
    (hxa : ∀ v m0 σC, ∀ q : AG ms L.lab, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF (swR v (-Lsw) 0) (FS L rS Lsw k0 v) m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Spike.Lib.A64.Flow.Abs (mR (swR v (-Lsw) 0)) ⟨-48, []⟩ mC σ ∧
        (rN L.lab (mRdJ0 (mNC L.lab (JS L k0 c0)).J σC) (J1 σC) .call).J σ c ∧
        (Spike.Lib.A64.Alloc.N L.lab ms q.1 .e).J (Spike.Lib.A64.Flow.enter (-48) σ) c ∧
        Spike.Lib.A64.Flow.CKept (mR (swR v (-Lsw) 0)) (-48) (-160) 0 mC m) →
      ∀ l b w s c, lblS l = none →
        Spike.Lib.A64.Flow.At L.exe L.endPc (Spike.Lib.A64.Flow.Hello1.aR (mR (swR v (-Lsw) 0))) F'
          (Ea ms q.1 l b w) s c → ms.xa l b w s c) :
    SegW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) pS lblS ms
      (Spike.Lib.A64.Flow.At L.exe L.endPc R (fun m => F m ∧ P m) (entryN L.lab c0))
      (fun s c => ∃ v m0 σC y,
        Spike.Lib.A64.Flow.At L.exe L.endPc (mR (swR v (-Lsw) 0)) (mF (swR v (-Lsw) 0) (FS L rS Lsw k0 v) m0 σC)
          (rX ms L.lab lblS (J1 σC) y) s c) := by
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
  refine (Spike.Lib.A64.Flow.HelloM.hello_main_pre_segW hpS hendS (hFwS v) hR' hv
    (show -Lsw ≤ -288 by omega) (Int.le_refl 0) ⟨hpre.1, hpre.2, hWrd v⟩
    (Spike.Lib.A64.WakePh.MainWf.limOk_mainE0 ⟨hlim80.rt, hlim80.mp, fun _ h => h.2.1.2, hlim80.room⟩)
    ?_ hloc hq
    (Spike.Lib.A64.Alloc.hmem_of_wordsNone hwf (fun _ h => h.1.wn) hH hHi hctr hoff) (hxa v)).mono_post
    fun _ _ ⟨m0, σC, y, h⟩ => ⟨v, m0, σC, y, h⟩
  rintro σ c ⟨⟨-, hsp, htp⟩, -⟩
  rw [Spike.Lib.A64.Flow.Ret0.tcbA_limA htp, hsp]
  exact ⟨hlim128.rt, hlim128.mp, fun _ h => h.2.1.2, hlim128.room⟩

end Gen

end Spike.Lib.A64.HelloPh.MainGlue

/-- info: 'Spike.Lib.A64.HelloPh.MainGlue.hello_start_rd_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainGlue.hello_start_rd_segW
