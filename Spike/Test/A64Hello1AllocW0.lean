/-
**`scc_rt_alloc`'s states inside `W0` at `hello1.w`'s instance** (AArch64):
the allocator's node obligations (`AllocW`, `Spike/Lib/A64Alloc.lean`) in
`wc_rodata`'s call context (`RdPreW.alloc`'s frame condition at
`MainPreW.rd`'s, the source at `rdJ'`'s) inside `W0` under `rodata`'s
frame `setupFrame e env`, from the components: the state's facts
(`allocSt`), the write abort's phase (`allocAb`), the arena's writes
(`allocArena`), the frames placed (`allocPlaced`), the counter's write in
its context (`allocCtr`), the abort sites (`allocAbortW`), the source's
runs (`allocRun`).

- `q0_of_rdCtx`: the call context's call is at `rdCN`.
- `allocRun`: the source's runs from every node's control (`runOk_hello1o`).
- `allocW0`: every node of `scc_rt_alloc` inside `W0`.
- `ctxA_of_at`: the counter add's states in `CtxA`.
- `allocW0A`: `allocW0` in the context `CtxA` at `scc_rt_main`'s switched region.
-/
import Spike.Test.A64Hello1PlacedS
import Spike.Test.A64Hello1AllocCtr
import Spike.Test.A64Hello1Ctr

namespace Spike.Test.A64Hello1W0

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region MemSide Ctl Frag FragS)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow (NodeW BlkW ND AS At holdCtr swR)
open Spike.Lib.A64.Flow.Hello1 (setupFrame rdJ' mF mR mNC mRdJ0 aR RdCtx)
open Spike.Lib.A64.Flow.Ret0 (MainG CallerCells StackOff limA)
open Spike.Lib.A64.Rt (swFSL)
open Spike.Lib.A64ConsumerS (PlacedS)
open Spike.Lib.A64ConsumerA (msOfA)
open Spike.Lib.A64ConsumerA (WrAt)
open Spike.Lib.A64.Flow.Hello1.SFactsN (RunOk runOk_hello1o)
open Spike.Lib.Hello1RodataSrc (rdCN eB envN)
open Spike.Lib.Hello1oRuns (hello1oTerms)
open Spike.Test.A64ArenaHello1 (ar)
open Spike.Lib.A64.Flow.Hello1.Inst
open SccCode (hello1Λ)

section Alloc

open Spike.Lib.A64.Alloc (Call AllocW N)
open Spike.Lib.A64.Flow.Hello1.Mem (hello1Exe hello1End)

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2}
  {q : Call} {g : MainG} {m0 : MachineData} {σC : AS}

/-- **The call context's call is at `rodata`'s allocation**: the call node's
source is `rdJ'`'s (`rdCN`), the allocator's entry at the call's. -/
theorem q0_of_rdCtx {lab : Label → Int64} {R' : Region} {m : MachineData}
    (h : RdCtx ms lab R' (mRdJ0 (mNC lab (rdJ' g)).J σC) q m) : q.c0 = rdCN := by
  obtain ⟨mC, σC', c1, -, ⟨⟨σe, ⟨-, hmc⟩, -, -⟩, -⟩, he, -⟩ := h
  obtain ⟨⟨σ0, ⟨hc1, -, -, -⟩, -, -, -, -, -⟩, -⟩ := hmc
  exact he.1.symm.trans hc1

/-- **The source's runs from every node's control** of `scc_rt_alloc` in
the call context, `rodata`'s frame's body a term of `hello1o`'s runs. -/
theorem allocRun {e : Expr} {env : TermRun.Env} (he : e ∈ hello1oTerms) :
    AllocW ms q (fun _ c => RunOk Spike.Test.Hello1MainSrc.hello1o c [setupFrame e env]) (fun _ _ => False) exe
      endPc (aR (mR R))
      (fun m => mF R F m0 σC m ∧ CallerCells (mR R) (-48) (-160) 0 m ∧
        RdCtx ms (_root_.Executable.labels exe).label (mR R)
          (mRdJ0 (mNC (_root_.Executable.labels exe).label (rdJ' g)).J σC) q m) := by
  refine allocW_of_ctl fun mA hFA _ c _ hc => runOk_hello1o ?_ ?_
  · have hq0 := q0_of_rdCtx hFA.2.2
    have ht : c.term = eB := by rcases hc with rfl | ⟨o, rfl⟩ <;> rw [hq0] <;> rfl
    rw [ht]
    simp [hello1oTerms, Spike.Lib.Hello1oRuns.sufs, Spike.Test.Hello1MainSrc.hello1o,
      Spike.Lib.Hello1Src.hello1Src, eB, Spike.Lib.Hello1RodataSrc.eW0, Spike.Lib.Hello1RodataSrc.eO0,
      Spike.Lib.Hello1RodataSrc.eW1, Spike.Lib.Hello1RodataSrc.eO1, Spike.Lib.Hello1RodataSrc.eN,
      Spike.Lib.Hello1RodataSrc.eSm, Spike.Lib.Hello1RodataSrc.eSl0, Spike.Lib.Hello1RodataSrc.ePack,
      Spike.Lib.Hello1RodataSrc.eRet]
  · intro f hf
    rw [List.mem_singleton.mp hf]
    exact he

/-- **Every node of `scc_rt_alloc` inside `W0`** under `rodata`'s frame
`setupFrame e env`, none moved but by the take (`Kr rS`), for `wc_rodata`'s
call `q` with its premises (`hok`) returning to `.sp0` (`hra`) in the
region at the call of `main`'s region `R` (aligned, its frame `R.lo ≤ -288`)
whose frame condition at `wc_rodata`'s gives the stack range off `wc_rodata`'s
region (`hFO`), the memory side the arena's (`hctr`, `hheap`, `hoff`) with
its writable words mapped (`hmp`), the counter and every header the code may
store unmapped in private memory and owned at no phase (`hmem`, `hno`), the
counter add's states in `Ctx` (`hctx`), `e` a term of `hello1o`'s runs
(`he`) reading only `me` besides `r`, bound to `w` holding the thread
pointer (`hfv`, `hme`, `hw`). -/
theorem allocW0 {rS : Range} {Dt : State → Prop} {Ctx : FragS isaLSE2} {e : Expr} {env : TermRun.Env}
    {w : TermRun.Word} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hhi : 0 ≤ R.hi)
    (hsub : rS.Sub hello1Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, mF R F m0 σC m → StackOff rS (mR R) m)
    (hok : q.OK ms (_root_.Executable.labels hello1Exe).label)
    (hra : q.ra = (labT ".L18_wc_rodata.sp0").toBitVec)
    (hmp : ∀ L, ms.mp L true → Kernel.mapped (K0 hello1Λ) true L = true)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j)
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hctx : ∀ s c, At hello1Exe hello1End (aR (mR R))
      (fun m => mF R F m0 σC m ∧ CallerCells (mR R) (-48) (-160) 0 m ∧
        RdCtx ms (_root_.Executable.labels hello1Exe).label (mR R)
          (mRdJ0 (mNC (_root_.Executable.labels hello1Exe).label (rdJ' g)).J σC) q m)
      (N (_root_.Executable.labels hello1Exe).label ms q .rmw) s c → Ctx s c [setupFrame e env])
    (he : e ∈ hello1oTerms) (hfv : ∀ y ∈ (exprFv e).filter (· != "r"), y = "me")
    (hme : ∀ ty ws, TermRun.lookupE env "me" = some (ty, ws) → ws = [w])
    (hw : w.val = .num g.tp.toBitVec.toNat) :
    AllocW ms q (fun s c => W0 Spike.Test.Hello1MainSrc.hello1o rS Dt Ctx s c [setupFrame e env]) (Kr rS)
      hello1Exe hello1End (aR (mR R))
      (fun m => mF R F m0 σC m ∧ CallerCells (mR R) (-48) (-160) 0 m ∧
        RdCtx ms (_root_.Executable.labels hello1Exe).label (mR R)
          (mRdJ0 (mNC (_root_.Executable.labels hello1Exe).label (rdJ' g)).J σC) q m) := by
  have hm1 : (mR R).OK := Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)
  have hb1 : (((mR R).base.toNat : Int)) = R.base.toNat + -80 :=
    Region.callee_base hR (by omega) (by decide) (by omega)
  have hal1 : (mR R).base.toNat % 16 = 0 := by omega
  have ha : (aR (mR R)).OK :=
    Region.callee_ok hm1 (by simp [Region.callee]) (by decide) (by simp [Region.callee])
      (by simp [Region.callee])
  have hala := Spike.Test.A64Hello1Ctr.aR_al hm1 hal1 (by simp [Region.callee]) (by simp [Region.callee])
  have hlo' : (aR (mR R)).lo ≤ -160 := by simp [Region.callee]
  have hhi' : 0 ≤ (aR (mR R)).hi := by simp [Region.callee]
  have hq : ∀ m, (fun m => mF R F m0 σC m ∧ CallerCells (mR R) (-48) (-160) 0 m ∧
      RdCtx ms (_root_.Executable.labels hello1Exe).label (mR R)
        (mRdJ0 (mNC (_root_.Executable.labels hello1Exe).label (rdJ' g)).J σC) q m) m →
      q.OK ms (_root_.Executable.labels hello1Exe).label := fun _ _ => hok
  have hFO' : ∀ m, (fun m => mF R F m0 σC m ∧ CallerCells (mR R) (-48) (-160) 0 m ∧
      RdCtx ms (_root_.Executable.labels hello1Exe).label (mR R)
        (mRdJ0 (mNC (_root_.Executable.labels hello1Exe).label (rdJ' g)).J σC) q m) m →
      StackOff rS (aR (mR R)) m := fun m hm =>
    Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hm1 (by omega) (by simp [Region.callee])
      (by simp [Region.callee]) (by simp [Region.callee]) (by decide) (by simp [Region.callee]) (by decide)
      (hFO m hm.1) hm.2.1
  have hSt := allocSt ha hala hlo' hhi' (by simp [Region.callee]) (by simp [Region.callee]) hsub hfit hFO' hq
    hra hmp (fun a h m hm => hmem a h m hm.1.1) hno
  have hAb := allocAb ha hala hlo' hhi' hq hra (fun a h m hm => hmem a h m hm.1.1)
  have hAr := allocArena (p := Spike.Test.Hello1MainSrc.hello1o) ha hala hlo' hhi' hq
    (fun a h m hm => hmem a h m hm.1.1) hctr hheap hoff
  have hPl := allocPlaced (ms := ms) (q := q) (lbl := hello1Λ.static) (exe := hello1Exe) (endPc := hello1End)
    (F := F) (m0 := m0) (σC := σC) (e := e) (env := env) hR hlo hhi hfv hme hw
  have hCt := allocCtr (Ctx := fun s c => Ctx s c [setupFrame e env]) ha hala hlo' hhi' hq
    (fun a h m hm => hmem a (.inr h) m hm.1.1) hheap hctx
  have hRn := allocRun (ms := ms) (q := q) (exe := hello1Exe) (endPc := hello1End) (R := R) (F := F)
    (g := g) (m0 := m0) (σC := σC) (env := env) he
  have hAo := allocAbortW (ms := ms) (q := q) (R := aR (mR R)) (F := fun m => mF R F m0 σC m ∧
    CallerCells (mR R) (-48) (-160) 0 m ∧ RdCtx ms (_root_.Executable.labels hello1Exe).label (mR R)
      (mRdJ0 (mNC (_root_.Executable.labels hello1Exe).label (rdJ' g)).J σC) q m)
  refine AllocW.imp (AllocW.imp (AllocW.imp (AllocW.imp (AllocW.imp (AllocW.imp hSt hAb (fun _ _ => And.intro))
    hAr (fun _ _ => And.intro)) hPl (fun _ _ => And.intro)) hCt (fun _ _ => And.intro))
    hRn (fun _ _ => And.intro)) hAo ?_
  intro s c h h7
  obtain ⟨h, h6⟩ := h
  obtain ⟨h, h5⟩ := h
  obtain ⟨h, h4⟩ := h
  obtain ⟨h, h3⟩ := h
  obtain ⟨h1, h2⟩ := h
  exact w0_of_stA h1 (fun h => absurd h (List.cons_ne_nil _ _)) h4 h2 h6 (h3 _) h5 (h7 _)

/-- **The counter add's states are in `CtxA`** at `scc_rt_main`'s region
`swR v (-L) 0` (aligned, a region), for `wc_rodata`'s call `q` returning to
`.sp0`, under the memory side of any allocation fragment `I`: neither the
node nor the frame condition reads the fragment (`allocW0`'s `hctx`). -/
theorem ctxA_of_at {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : Spike.Lib.A64ConsumerS.OwnS}
    {I : Spike.Lib.A64ConsumerS.InvS} {lsize : Lsize} {exe : _root_.Executable} {endPc : Int64}
    {rT : Scc.Sem.Range} {tcb top : BitVec 64} {c0 : Spike.Lib.Ctl} {L : Int} {e : Expr} {env : TermRun.Env}
    {v : BitVec 64} (h16 : v.toNat % 16 = 0) (hok : (swR v (-L) 0).OK)
    (hra : q.ra = ((_root_.Executable.labels exe).label ".L18_wc_rodata.sp0").toBitVec) {s : State}
    {c : Spike.Lib.Ctl}
    (hAt : At exe endPc (aR (mR (swR v (-L) 0)))
      (Spike.Test.A64Hello1Ctr.FaA (msOfA hello1Λ μ rd G own ar I hello1Λ.static lsize [setupFrame e env]) exe
        rT tcb top c0 L v m0 σC q)
      (N (_root_.Executable.labels exe).label
        (msOfA hello1Λ μ rd G own ar I hello1Λ.static lsize [setupFrame e env]) q .rmw) s c) :
    Spike.Test.A64Hello1Ctr.CtxA μ rd G own lsize exe endPc rT tcb top c0 L e env s c [setupFrame e env] :=
  ⟨rfl, v, h16, hok, m0, σC, q, hra, hAt⟩

/-- **`allocW0` in the context `CtxA`** at `scc_rt_main`'s region
`swR v (-L) 0` and frame condition `swFSL`, under the memory side of any
allocation fragment `I`: the arena's facts and the mapped words hold by
definition, the counter add's states are in `CtxA` (`ctxA_of_at`). -/
theorem allocW0A {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : Spike.Lib.A64ConsumerS.OwnS}
    {I : Spike.Lib.A64ConsumerS.InvS} {lsize : Lsize} {rT rS : Scc.Sem.Range} {tcb top : BitVec 64}
    {c0 : Spike.Lib.Ctl} {L : Int} {e : Expr} {env : TermRun.Env} {w : TermRun.Word} {Dt : State → Prop}
    {v : BitVec 64} (h16 : v.toNat % 16 = 0) (hok : (swR v (-L) 0).OK) (hL : 288 ≤ L)
    (hsub : rS.Sub hello1Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, mF (swR v (-L) 0) (swFSL L rT top (limA (UInt64.ofBitVec tcb)) v) m0 σC m →
      StackOff rS (mR (swR v (-L) 0)) m)
    (hq : q.OK (msOfA hello1Λ μ rd G own ar I hello1Λ.static lsize [setupFrame e env])
      (_root_.Executable.labels hello1Exe).label)
    (hra : q.ra = (labT ".L18_wc_rodata.sp0").toBitVec)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (msOfA hello1Λ μ rd G own ar I hello1Λ.static lsize [setupFrame e env]) o) →
      ∀ m, swFSL L rT top (limA (UInt64.ofBitVec tcb)) v m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ar.ctr ∨ ∃ o, o + ar.units q.n q.τ ≤ ar.cells ∧
        a.toNat = q.hdrAt (msOfA hello1Λ μ rd G own ar I hello1Λ.static lsize [setupFrame e env]) o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j)
    (he : e ∈ hello1oTerms) (hfv : ∀ y ∈ (exprFv e).filter (· != "r"), y = "me")
    (hme : ∀ ty ws, TermRun.lookupE env "me" = some (ty, ws) → ws = [w])
    (hw : w.val = .num (UInt64.ofBitVec tcb).toBitVec.toNat) :
    AllocW (msOfA hello1Λ μ rd G own ar I hello1Λ.static lsize [setupFrame e env]) q
      (fun s c => W0 Spike.Test.Hello1MainSrc.hello1o rS Dt
        (Spike.Test.A64Hello1Ctr.CtxA μ rd G own lsize hello1Exe hello1End rT tcb top c0 L e env) s c
        [setupFrame e env]) (Kr rS) hello1Exe hello1End (aR (mR (swR v (-L) 0)))
      (Spike.Test.A64Hello1Ctr.FaA (msOfA hello1Λ μ rd G own ar I hello1Λ.static lsize [setupFrame e env])
        hello1Exe rT tcb top c0 L v m0 σC q) :=
  allocW0 (g := ⟨top, UInt64.ofBitVec tcb, c0⟩) hok h16 (by simp only [swR]; omega) (by simp [swR]) hsub hfit
    hFO hq hra (fun _ h => h.1) hmem hno rfl rfl (fun _ _ => rfl)
    (fun _ _ hA => ctxA_of_at h16 hok (by rw [hello1_labT]; exact hra) hA) he hfv hme hw

end Alloc

/-- info: 'Spike.Test.A64Hello1W0.q0_of_rdCtx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms q0_of_rdCtx

/-- info: 'Spike.Test.A64Hello1W0.allocRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocRun

/-- info: 'Spike.Test.A64Hello1W0.allocW0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocW0

/-- info: 'Spike.Test.A64Hello1W0.ctxA_of_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ctxA_of_at

/-- info: 'Spike.Test.A64Hello1W0.allocW0A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocW0A

end Spike.Test.A64Hello1W0
