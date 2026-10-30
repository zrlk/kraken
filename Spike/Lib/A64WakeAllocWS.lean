/-
**`scc_rt_alloc` inside the start's level `WS`** (AArch64): the box's
allocation in `WcPreW.alloc` at `W0 … []` (`StartWf.WS`), moved only by the
take (`PhRec.K L rS`). Per component of `Wf`:

- the state's facts: `WcW.allocW_wcG` (`SFactsSt2` at `ownG`), its write
  tail anything (`mono_dt`, no `write` at the allocator);
- both abort phases: `allocAbAcW`;
- the arena's writes: `AllocG.allocArenaS` (`ArenaWr0`, at any `lsize`),
  the counter's write only at the add (`AllocG.allocCtrS`, the context
  there from `hctx`);
- the abort sites: off them (`AllocG.allocPc`, `abortWf_of_off`);
- the frames placed (`hpl`), `X0` (`hX0`) and the control's facts (no `ret`
  of `main`, its runs well formed, `hcf`): the caller's, per node.
-/
import Spike.Lib.A64WakeAllocPh
import Spike.Lib.A64WakeWcAllocWI
import Spike.Lib.A64WakeStartWf

namespace Spike.Lib.A64.WakeWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (WrAt)
open Spike.Lib.A64.Flow (At)
open Spike.Lib.A64.Alloc (Call AllocW N)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib (Arena FragS)

variable {L : RuntimeLayout} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop}

set_option maxHeartbeats 800000 in
/-- **`scc_rt_alloc` inside `WS`** (owned word `a`), moved only by the
take: `allocW_wcG`'s premises (`hR` … `hno`), the clone states' facts
(`hcl`), per node the frames placed (`hpl`), `X0` (`hX0`) and the control's
facts (`hcf`), the context at the counter's add (`hctx`), the memory side's
arena the arena's (`hctr`, `hheap`, `hoff`, boxes `hnew`), the counter below
the heap (`hlt`, `h64`). -/
theorem allocW_WS (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = Spike.Lib.A64.WakePh.lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf Spike.Lib.A64.WakePh.lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (a : BitVec 64) {ms : Spike.Lib.MemSide isaLSE2} {q : Call}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64)
    (hra : q.ra = (L.lab ".L21_wc_main.sp0").toBitVec) (hq : ∀ m, F m → q.OKS ms L.lab)
    (hmp : ∀ l, ms.mp l true → Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true l = true)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ w : BitVec 64,
      (w = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ w.toNat = q.hdrAt ms o) →
      ∀ j v, (⟨w, 8⟩, v) ∉ Spike.Lib.A64.WakePh.ownW L a j)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hpl : AllocW ms q (fun s c => Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c []) (fun _ _ => False)
      L.exe L.endPc R F)
    (hX0 : AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc R F)
    (hcf : AllocW ms q (fun _ c => (∀ a, c.term ≠ .ret a) ∧ RunWf p c []) (fun _ _ => False)
      L.exe L.endPc R F)
    (hctx : ∀ s c, At L.exe L.endPc R F (N L.lab ms q .rmw) s c → Ctx s c [])
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    AllocW ms q (Spike.Lib.A64.WakePh.StartWf.WS L a ar p Dt Cl Ctx lbl lsize frM X0)
      (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F := by
  have hI := Spike.Lib.A64.WakePh.instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hA : Spike.Lib.A64.Flow.allocIn L.prog = true := by
    rw [hp]; exact Spike.Lib.A64.Flow.WakeWc.wake_alloc
  have hph := Spike.Lib.A64.WakePh.WcW.allocPhW hΛ hlab
  have hS := Spike.Lib.A64.WakePh.WcW.allocW_wcG (rS := rS) hp hlo hΛ hlab hsite a hR hal hlo' hhi hl hh hpool
    hra hq hmp hmem hno
  have hPh := allocAbAcW (Cl := Cl) hI hA hph hlab hR hal hlo' hhi hq hra hmem
  have hAr := Spike.Lib.A64.AllocG.allocArenaS (lbl := lbl) (p := p) hI hA hR hal hlo' hhi hq hmem hctr hheap
    hoff hnew
  have hCx := Spike.Lib.A64.AllocG.allocCtrS (Ctx := fun s c => Ctx s c []) hI hA hR hal hlo' hhi hq
    (fun a h => hmem a (.inr h)) hheap hlt h64 hctx
  have hPc := Spike.Lib.A64.AllocG.allocPc (R := R) (F := F) (ms := ms) (q := q) hI hph
  have g1 := Spike.Lib.A64.AllocG.AllocW.imp hX0 hcf (fun _ _ => And.intro)
  have g2 := Spike.Lib.A64.AllocG.AllocW.imp hpl g1 (fun _ _ => And.intro)
  have g3 := Spike.Lib.A64.AllocG.AllocW.imp hPc g2 (fun _ _ => And.intro)
  have g4 := Spike.Lib.A64.AllocG.AllocW.imp hCx g3 (fun _ _ => And.intro)
  have g5 := Spike.Lib.A64.AllocG.AllocW.imp hAr g4 (fun _ _ => And.intro)
  have h2 := Spike.Lib.A64.AllocG.AllocW.imp hPh g5 (fun _ _ => And.intro)
  refine Spike.Lib.A64.AllocG.AllocW.imp hS h2 ?_
  rintro s c hst ⟨⟨hab, hac⟩, har, hcx, hpc, hpl', hx, hnr, hr⟩
  exact W0.intro0 hx (Wf.intro (Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt hst fun h => h.elim) hab hac hcl (fun _ => hnr) hpl'
    (fun c' fs' hrun L0 hW hne => .inl (har [] c' fs' hrun L0 hW hne lsize)) hcx hr
    (abortWf_of_off (hI.off s hpc).1.noAbort))

end Spike.Lib.A64.WakeWf

/-- info: 'Spike.Lib.A64.WakeWf.allocW_WS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.allocW_WS
