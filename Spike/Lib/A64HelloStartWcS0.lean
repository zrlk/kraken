/-
**`hello.w` from `_start` to `wc_rodata`'s heap abort at depth, level 0** (AArch64): `StartWcS.hello_start_wc_segWS`'s
twin that ends at rodata's landing. The start at `[]`
(`Rt.startEF_segWA` lifted by `SegWS.liftS`), then from `scc_rt_main`'s entry `HelloM.hello_main_pre_segWSF`
(`wc_rodata` at `[fr]`, its allocator's return being its allocation, landing in `ms [fr]`'s `xa`). What follows the
landing (`wc_rodata`'s rest, `scc_rt_main`'s `.sp0`, `wc_main`) is level 1's.

- `hello_start_rd_segWS0`: from `_start` at `F ∧ P` to `wc_rodata`'s heap abort at `[fr]`, the thread pointer
  `pinA + 8` kept (L1-TP, via `HelloM.hello_main_pre_segWSTF`; `hxa` may assume it; needs `hK'`).
-/
import Spike.Lib.A64HelloStartWcS
import Spike.Lib.A64HelloMainPreF
import Spike.Lib.A64HelloMainPreTF

namespace Spike.Lib.A64.HelloPh.StartWcS0

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
open Spike.Lib.A64.HelloPh.StartWcS (WS)
open Spike.Lib.DmemPriv (WordsNoneP WordIn)
open Spike.Lib (Arena FragS Frag MemSide SegWS LocalRun FrameRun)
/-- `Flow`'s abstract state (`AS` alone is ambiguous here). -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

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

/-- **From `_start` to `wc_rodata`'s heap abort inside the start's level with frames, level 0**
(`hello_start_wc_segWS`'s twin): the start up to the switch at `[]` (`startEW_W0SH`,
`Rt.startEF_segWA` lifted), then at each base `v` of the new stack of depth `Lsw`
`HelloM.hello_main_pre_segWSF` at `WS` from `scc_rt_main`'s entry (`mainPreWH_W0SH`; `hWe` at `bl wc_rodata`'s
target), the source's call of `rodata` pushing `fr` into `J'` (`hrun`, `hJ'`), `wc_rodata` at `[fr]` (`hrd`), and
its fresh-label landings in `ms [fr]`'s allocation fragment (`hxa`). Level 0 ends at rodata's landing: the
allocator's return is its allocation, so the only exit is `wc_rodata`'s heap abort at `[fr]`; no `hret`, `hPw`
(`MainWcPS`) or `wc_main` facts are asked for. -/
theorem hello_start_rd_segWS0 (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hs : WSep L a) (hro : L.Λ.rodata.Disjoint L.Λ.stackPool) {k0 : BitVec 64}
    {Lsw : Int} {ms : List TermRun.Frame → MemSide isaLSE2} {pS : Prog} {lblS : Lbl} {fr : TermRun.Frame}
    (hK : (ms []).K = some abi) (hK' : (ms [fr]).K = some abi) (hwf : L.Λ.WF)
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
    {J' : FAS → Ctl → Prop} {J1 : FAS → FAS → Ctl → Prop}
    (hWe : ∀ v s c, At L.exe L.endPc (swR v (-Lsw) 0) (FS L rS Lsw k0 v) (mNC L.lab (JS L k0 c0)) s c →
      WS L a ar p Dt Cl Ctx lbl lsize frM X0 s c [])
    (hrun : ∀ σ c, (mNC L.lab (JS L k0 c0)).J σ c → ∃ c', FrameRun pS (c, []) (c', [fr]) ∧ J' σ c')
    (hJ' : ∀ σ c', J' σ c' → ∃ c, (mNC L.lab (JS L k0 c0)).J σ c)
    (hrd : ∀ v m0 σC, RdPreW (Spike.Lib.A64.Flow.WakeWc.tpG (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64))
        fun s c => WS L a ar p Dt Cl Ctx lbl lsize frM X0 s c [fr])
      (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc (mR (swR v (-Lsw) 0)) (mF (swR v (-Lsw) 0) (FS L rS Lsw k0 v) m0 σC)
      (ms [fr]) (mRdJ0 J' σC) (J1 σC))
    (hloc : ∀ σC σ c, mRdJ0 J' σC σ c → ∃ c', LocalRun pS c c' ∧ J1 σC σ c')
    (hq : ∀ σC σ c, J1 σC σ c → ∃ q : Call, q.OK (ms [fr]) L.lab ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u (ms [fr]) = 3#64)
    (hxa : ∀ v m0 σC, ∀ q : AG (ms [fr]) L.lab, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF (swR v (-Lsw) 0) (FS L rS Lsw k0 v) m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Spike.Lib.A64.Flow.Abs (mR (swR v (-Lsw) 0)) ⟨-48, []⟩ mC σ ∧
        (rN L.lab (mRdJ0 J' σC) (J1 σC) .call).J σ c ∧
        (Spike.Lib.A64.Alloc.N L.lab (ms [fr]) q.1 .e).J (enter (-48) σ) c ∧
        CKept (mR (swR v (-Lsw) 0)) (-48) (-160) 0 mC m) →
      ∀ l b w s c, lblS l = none → At L.exe L.endPc (aR (mR (swR v (-Lsw) 0))) F' (Ea (ms [fr]) q.1 l b w) s c →
        TP (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64)) s → (ms [fr]).xa l b w s c) :
    SegWS (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) pS lblS ms
      ((At L.exe L.endPc R (fun m => F m ∧ P m) (entryN L.lab c0)).at [])
      (Frag.at (fun s c => ∃ v m0 σC,
          At L.exe L.endPc (mR (swR v (-Lsw) 0)) (mF (swR v (-Lsw) 0) (FS L rS Lsw k0 v) m0 σC)
            (rX (ms [fr]) L.lab lblS (J1 σC) .abort) s c ∧
          TP (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64)) s) [fr]) := by
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
    refine (Spike.Lib.A64.Flow.HelloM.hello_main_pre_segWSTF (W := WS L a ar p Dt Cl Ctx lbl lsize frM X0)
      (K := Spike.Lib.A64.PhRec.K L rS) (p := pS) (lbl := lblS) (ms := ms) (fs1 := [fr]) (J1 := J1) hpS hendS hK'
      (hFwS v) hR' hv (show -Lsw ≤ -288 by omega) (Int.le_refl 0) hpre.1 hpre.2 (hWe v)
      (by rintro σ c ⟨⟨σe, ⟨⟨-, -, htp⟩, -⟩, -, -, -, -, ht⟩, -⟩; exact ht.trans htp) hrun hJ' (hrd v)
      (Spike.Lib.A64.WakePh.MainWf.limOk_mainE0 ⟨hlim80.rt, hlim80.mp, fun _ h => h.2.1.2, hlim80.room⟩)
      ?_ hloc hq
      (Spike.Lib.A64.Alloc.hmem_of_wordsNone hwf (fun _ h => h.1.wn) (hH _) (hHi _) (hctr _) hoff)
      (hxa v)).mono_post ?_
    · rintro σ c ⟨⟨-, hsp, htp⟩, -⟩
      rw [Spike.Lib.A64.Flow.Ret0.tcbA_limA htp, hsp]
      exact ⟨hlim128.rt, hlim128.mp, fun _ h => h.2.1.2, hlim128.room⟩
    · rintro s c fs ⟨⟨m0, σC, h, ht⟩, rfl⟩
      exact ⟨⟨v, m0, σC, h, ht⟩, rfl⟩
  · rintro s c fs ⟨⟨v, h16, hok, h⟩, rfl⟩
    exact ⟨⟨v, h16, hok⟩, h, rfl⟩

end Gen

end Spike.Lib.A64.HelloPh.StartWcS0

/--
info: 'Spike.Lib.A64.HelloPh.StartWcS0.hello_start_rd_segWS0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartWcS0.hello_start_rd_segWS0
