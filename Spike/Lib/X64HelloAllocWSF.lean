/-
**`scc_rt_alloc` inside the start's level at any frames** (x86-64; the twin of
`Spike/Lib/A64HelloAllocWSF.lean`): `allocW_WSH_tp`'s body (`X64HelloAllocWSTp`) at the frames `fs`, one of `[]`
and `[frM]` (`hfs`). rodata runs under the setup block's frame (`X64HelloRdCf.frH`): its buffer allocation's
states are at `[frH env]`, not at `[]`, so the level `StartWf.WSH` (fixed at `[]`) does not hold there; `WSHF … fs`
is `W0 … fs` (and `StartWf.WSH` at `fs = []`). Each component is `allocW_WSH_tp`'s at `fs`:
`AllocG.allocArenaS` is already at every frame list, the counter's context, the frames placed, `X0` and the
control's facts at `fs` (`hctx`, `hpl`, `hX0`, `hcf`: no `ret` of `main` only at no frame).

- `WSHFg`: the level at the frames `fs` at any owned words `own`; `WSHF`: at `ownGH`.
- `allocW_WSHFg`: the allocator inside `WSHFg own`, from its `SFactsSt2` at `own` (`hS`).
- `allocW_WSHF`: the statement, `allocW_WSHFg` at `WcW.allocW_wcGH`.
- `allocW_WSHFX`: `allocW_WSHFg` at `ownGHXW` (both self words appended), from `OwnAlloc.allocW_wcGHX`.

**Where this differs from AArch64** (forced by the x86-64 shape): the premises are `allocW_WSH_tp`'s x86-64 ones
(the cells `helloCells`, labels by `codeLabel`, the region `[-160, 8)` with an 8-aligned base, `hR8`,
`8 ≤ R.hi`; A64's 16-aligned `hal`, `0 ≤ R.hi`). A64's `wshF_nil` and `allocW_WSHF_tp` are dead in the hello proof
and are not twinned. The level is generic in the owned words (`WSHFg`; AArch64's `WSHF` is at `ownGH` only), so
that `ownGHXW`, which carries main's and the worker's TCB words, shares the statement (`allocW_WSHFX`, x86-64
only: its extra premises are `OwnAlloc.allocW_wcGHX`'s).
-/
import Spike.Lib.X64HelloAllocWSTp

namespace Spike.Lib.X64.HelloWf

open Spike.Lib.X64.WakeWf (W0 Wf RunWf abortWf_of_off)

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (pcOf abi codeLabel)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (WrAt)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Alloc (Call AllocW N)
open Spike.Lib (Arena FragS)

/-- **The start's level at the frames `fs` at any owned words `own`**: `W0` at `own`, the write and threads
aborts' phases. -/
abbrev WSHFg (own : Spike.Lib.X64Consumer.Own) (L : RuntimeLayout) (ar : Arena) (p : Prog) (Dt Cl : State → Prop)
    (Ctx : FragS isa) (lbl : Lbl) (lsize : Lsize) (frM : TermRun.Frame) (X0 : State → Prop)
    (fs : List TermRun.Frame) : Spike.Lib.Frag isa := fun s c =>
  W0 L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
    (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab Spike.Lib.X64.HelloPh.StartWf.pfxM) Ctx lbl lsize frM X0 s c fs

/-- **The start's level at the frames `fs`**: `WSHFg` at `ownGH` (`StartWf.WSH` at `fs`). -/
abbrev WSHF (L : RuntimeLayout) (a : BitVec 64) (ar : Arena) (p : Prog) (Dt Cl : State → Prop)
    (Ctx : FragS isa) (lbl : Lbl) (lsize : Lsize) (frM : TermRun.Frame) (X0 : State → Prop)
    (fs : List TermRun.Frame) : Spike.Lib.Frag isa :=
  WSHFg (Spike.Lib.X64.HelloPh.ownGH L a) L ar p Dt Cl Ctx lbl lsize frM X0 fs

variable {L : RuntimeLayout} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {fs : List TermRun.Frame}

set_option maxHeartbeats 800000 in
/-- **`scc_rt_alloc` inside `WSHFg own … fs`**, moved only by the take, from the allocator's `SFactsSt2` at `own`
(`hS`, e.g. `WcW.allocW_wcGH` at `ownGH`, `OwnAlloc.allocW_wcGHX` at `ownGHXW`): both abort phases
(`allocAbAcH`), the arena, the counter's context (`hctx`) and the pcs, at the frames `fs` (`hfs`), the frames
placed (`hpl`), `X0` (`hX0`), the control's facts (`hcf`). -/
theorem allocW_WSHFg {own : Spike.Lib.X64Consumer.Own} (hp : L.prog = helloCells)
    (hlo : L.Λ.code.lo = Spike.Lib.X64.HelloPh.lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    {ms : Spike.Lib.MemSide isa} {q : Call}
    (hR : R.OK) (hlo' : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hfs : fs = [] ∨ fs = [frM])
    {rl : Label} (hrl : Spike.Lib.X64.HelloPh.WcW.AllocRetH rl)
    (hra : q.ra = (L.lab rl).toBitVec) (hq : ∀ m, F m → q.OKS ms L.lab)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hS : AllocW ms q (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s)
      (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hpl : AllocW ms q (fun s c => Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c fs) (fun _ _ => False)
      L.exe L.endPc R F)
    (hX0 : AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc R F)
    (hcf : AllocW ms q (fun _ c => (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs) (fun _ _ => False)
      L.exe L.endPc R F)
    (hctx : ∀ s c, At L.exe L.endPc R F (N L.lab ms q .rmw) s c → Ctx s c fs)
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    AllocW ms q (WSHFg own L ar p Dt Cl Ctx lbl lsize frM X0 fs) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F := by
  have hI := Spike.Lib.X64.HelloPh.instOkH hp hlo 0#64 (fun _ => False) hsite (rS := rS)
  have hA : Spike.Lib.X64.Alloc.allocIn L.prog = true := by
    rw [hp]; exact Spike.Lib.X64.Flow.HelloRd.hello_alloc
  have hph := Spike.Lib.X64.HelloPh.WcW.allocPhH (Λ := L.Λ) hΛ hlab
  have hPh := allocAbAcH (Cl := Cl) hI hA hph hlab hR hlo' hhi hq hrl hra hmem
  have hAr := Spike.Lib.X64.AllocG.allocArenaS (lbl := lbl) (p := p) hI hA hR hlo' hhi hq hmem hctr hheap
    hoff hnew
  have hCx := Spike.Lib.X64.AllocG.allocCtrS (Ctx := fun s c => Ctx s c fs) hI hA hR hlo' hhi hq
    (fun a h => hmem a (.inr h)) hheap hlt h64 hctx
  have hPc := Spike.Lib.X64.AllocG.allocPc (R := R) (F := F) (ms := ms) (q := q) hI hph
  have g1 := Spike.Lib.X64.AllocG.AllocW.imp hX0 hcf (fun _ _ => And.intro)
  have g2 := Spike.Lib.X64.AllocG.AllocW.imp hpl g1 (fun _ _ => And.intro)
  have g3 := Spike.Lib.X64.AllocG.AllocW.imp hPc g2 (fun _ _ => And.intro)
  have g4 := Spike.Lib.X64.AllocG.AllocW.imp hCx g3 (fun _ _ => And.intro)
  have g5 := Spike.Lib.X64.AllocG.AllocW.imp hAr g4 (fun _ _ => And.intro)
  have h2 := Spike.Lib.X64.AllocG.AllocW.imp hPh g5 (fun _ _ => And.intro)
  refine Spike.Lib.X64.AllocG.AllocW.imp hS h2 ?_
  rintro s c hst ⟨⟨hab, hac⟩, har, hcx, hpc, hpl', hx, hnr, hr⟩
  exact ⟨hfs, hx, Wf.intro (Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt hst fun h => h.elim) hab hac hcl
    hnr hpl' (fun c' fs' hrun L0 hW hne => .inl (har fs c' fs' hrun L0 hW hne lsize)) hcx hr
    (abortWf_of_off (hI.off s hpc).1.noAbort)⟩

set_option maxHeartbeats 800000 in
/-- **`scc_rt_alloc` inside `WSHF … fs`** (owned word `a`), moved only by the take: `allocW_WSH_tp`'s premises
at the frames `fs` (`hfs`: `[]` or `[frM]`), the frames placed (`hpl`), `X0` (`hX0`), the control's facts (`hcf`)
and the counter's context (`hctx`) at `fs`, with no thread-pointer guard. -/
theorem allocW_WSHF (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = Spike.Lib.X64.HelloPh.lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (a : BitVec 64) {ms : Spike.Lib.MemSide isa} {q : Call}
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo' : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64)
    (hfs : fs = [] ∨ fs = [frM])
    {rl : Label} (hrl : Spike.Lib.X64.HelloPh.WcW.AllocRetH rl)
    (hra : q.ra = (L.lab rl).toBitVec) (hq : ∀ m, F m → q.OKS ms L.lab)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) true l = true)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ Spike.Lib.X64.HelloPh.ownH L a j)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hpl : AllocW ms q (fun s c => Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c fs) (fun _ _ => False)
      L.exe L.endPc R F)
    (hX0 : AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc R F)
    (hcf : AllocW ms q (fun _ c => (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs) (fun _ _ => False)
      L.exe L.endPc R F)
    (hctx : ∀ s c, At L.exe L.endPc R F (N L.lab ms q .rmw) s c → Ctx s c fs)
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    AllocW ms q (WSHF L a ar p Dt Cl Ctx lbl lsize frM X0 fs) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F :=
  allocW_WSHFg hp hlo hΛ hlab hsite hR hlo' hhi hfs hrl hra hq hmem
    (Spike.Lib.X64.HelloPh.WcW.allocW_wcGH (rS := rS) (Λ := L.Λ) hp hlo hΛ hlab hsite a hR hR8 hlo' hhi hl hh hpool
      hrl hra hq hmp hmem hno)
    hcl hpl hX0 hcf hctx hctr hheap hoff hnew hlt h64

set_option maxHeartbeats 800000 in
/-- **`allocW_WSHF` at `ownGHXW`**: `allocW_WSHFg` at `OwnAlloc.allocW_wcGHX` (`ownGHXW`'s separation `hsep`, `ha`,
`hW`, the allocator's frame's band on the pool `hb`, the counter and the headers off `tcbM` `hnoM`). -/
theorem allocW_WSHFX (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = Spike.Lib.X64.HelloPh.lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (a : BitVec 64) {ms : Spike.Lib.MemSide isa} {q : Call}
    (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : Spike.Lib.X64.WakePh.tcbM L ≠ a)
    (hW : Spike.Lib.X64HelloOwnLift.tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hb : Spike.Lib.X64.WakePh.BandOnP L R (-160) 8)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo' : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64)
    (hfs : fs = [] ∨ fs = [frM])
    {rl : Label} (hrl : Spike.Lib.X64.HelloPh.WcW.AllocRetH rl)
    (hra : q.ra = (L.lab rl).toBitVec) (hq : ∀ m, F m → q.OKS ms L.lab)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) true l = true)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ Spike.Lib.X64.HelloPh.ownH L a j)
    (hnoM : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      w ≠ Spike.Lib.X64.WakePh.tcbM L)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hpl : AllocW ms q (fun s c => Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c fs) (fun _ _ => False)
      L.exe L.endPc R F)
    (hX0 : AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc R F)
    (hcf : AllocW ms q (fun _ c => (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs) (fun _ _ => False)
      L.exe L.endPc R F)
    (hctx : ∀ s c, At L.exe L.endPc R F (N L.lab ms q .rmw) s c → Ctx s c fs)
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    AllocW ms q (WSHFg (Spike.Lib.X64.HelloPh.ownGHXW L a) L ar p Dt Cl Ctx lbl lsize frM X0 fs)
      (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F :=
  allocW_WSHFg hp hlo hΛ hlab hsite hR hlo' hhi hfs hrl hra hq hmem
    (Spike.Lib.X64.HelloPh.OwnAlloc.allocW_wcGHX (rS := rS) (Λ := L.Λ) hp hlab hsite hsep ha hW hb hlo hΛ hR hR8
      hlo' hhi hl hh hpool hrl hra hq hmp hmem hno hnoM)
    hcl hpl hX0 hcf hctx hctr hheap hoff hnew hlt h64

end Spike.Lib.X64.HelloWf

/-- info: 'Spike.Lib.X64.HelloWf.allocW_WSHFg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloWf.allocW_WSHFg

/-- info: 'Spike.Lib.X64.HelloWf.allocW_WSHF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloWf.allocW_WSHF

/-- info: 'Spike.Lib.X64.HelloWf.allocW_WSHFX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloWf.allocW_WSHFX
