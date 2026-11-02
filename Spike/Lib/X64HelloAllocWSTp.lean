/-
**`scc_rt_alloc` inside `WSH` guarded by the thread pointer** (x86-64; hello twin of
`Spike/Lib/X64WakeAllocWSTp.lean`, the twin of `Spike/Lib/A64HelloAllocWSTp.lean`):
`scc_rt_alloc` inside hello start's level `WSH` with the counter's context (`hctx`)
owed only at states with thread pointer `t` (`fsBase`), the conclusion `tpG t WSH`.
The counter's write is in `fun s c => TP t s → Ctx s c []` (`AllocG.allocCtrS` at
that context); the level's other conjuncts come from `allocW_wcGH` (`SFactsSt2` at
`ownGH`), `allocAbAcH` (both abort phases) and `AllocG.allocArenaS`.

- `allocW_WSH_tp`: the statement.
- `allocW_WSHX_tp`: the same at `ownGHXW` (`HelloPh.WSHX`: both self words appended), its `SFactsSt2` from
  `OwnAlloc.allocW_wcGHX`.

**Where this differs from AArch64** (forced by the x86-64 shape): the cells are
`helloCells` (labels by `codeLabel`), the region is `[-160, 8)` with an 8-aligned
base (`hR8`, `8 ≤ R.hi`; A64's 16-aligned `hal`, `0 ≤ R.hi`); the two return points
are `.Lwc_rodata.x15` and `.Lwc_main.x22` (`AllocRetH`); the thread pointer is
`fsBase` (`KeepTP.TP`, `WakeTP.tpG`; A64's `TPIDR_EL0`, `WakeWc.tpG`). There is no
separate `allocW_WSH` module: its body is folded into this proof, as on AArch64
only the thread-pointer form is used. `allocW_WSHX_tp` is x86-64 only (main owns its TCB's self word; AArch64
owns none): `allocW_wcGHX`'s premises `hsep`, `ha`, `hW`, `hb`, `hnoM` are added.
-/
import Spike.Lib.X64HelloAllocPh
import Spike.Lib.X64HelloStartWfL
import Spike.Lib.X64WakeAllocWSTp
import Spike.Lib.X64HelloOwnAllocX

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
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib (Arena FragS)

variable {L : RuntimeLayout} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop}

set_option maxHeartbeats 800000 in
/-- **`scc_rt_alloc` inside `tpG t WSH`**: the hello start's `scc_rt_alloc` with the context at
the counter's add owed only under the thread pointer `t` (`hctx`). -/
theorem allocW_WSH_tp (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = Spike.Lib.X64.HelloPh.lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (a : BitVec 64) {ms : Spike.Lib.MemSide isa} {q : Call} {t : UInt64}
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo' : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64)
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
    (hpl : AllocW ms q (fun s c => Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c []) (fun _ _ => False)
      L.exe L.endPc R F)
    (hX0 : AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc R F)
    (hcf : AllocW ms q (fun _ c => (∀ a, c.term ≠ .ret a) ∧ RunWf p c []) (fun _ _ => False)
      L.exe L.endPc R F)
    (hctx : ∀ s c, At L.exe L.endPc R F (N L.lab ms q .rmw) s c → TP t s → Ctx s c [])
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    AllocW ms q (Spike.Lib.X64.WakeTP.tpG t
        (Spike.Lib.X64.HelloPh.StartWf.WSH L a ar p Dt Cl Ctx lbl lsize frM X0))
      (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F := by
  have hI := Spike.Lib.X64.HelloPh.instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hA : Spike.Lib.X64.Alloc.allocIn L.prog = true := by
    rw [hp]; exact Spike.Lib.X64.Flow.HelloRd.hello_alloc
  have hph := Spike.Lib.X64.HelloPh.WcW.allocPhH (Λ := L.Λ) hΛ hlab
  have hS := Spike.Lib.X64.HelloPh.WcW.allocW_wcGH (rS := rS) (Λ := L.Λ) hp hlo hΛ hlab hsite a hR hR8 hlo' hhi
    hl hh hpool hrl hra hq hmp hmem hno
  have hPh := allocAbAcH (Cl := Cl) hI hA hph hlab hR hlo' hhi hq hrl hra hmem
  have hAr := Spike.Lib.X64.AllocG.allocArenaS (lbl := lbl) (p := p) hI hA hR hlo' hhi hq hmem hctr hheap
    hoff hnew
  have hCx := Spike.Lib.X64.AllocG.allocCtrS (Ctx := fun s c => TP t s → Ctx s c []) hI hA hR hlo' hhi hq
    (fun a h => hmem a (.inr h)) hheap hlt h64 hctx
  have hPc := Spike.Lib.X64.AllocG.allocPc (R := R) (F := F) (ms := ms) (q := q) hI hph
  have g1 := Spike.Lib.X64.AllocG.AllocW.imp hX0 hcf (fun _ _ => And.intro)
  have g2 := Spike.Lib.X64.AllocG.AllocW.imp hpl g1 (fun _ _ => And.intro)
  have g3 := Spike.Lib.X64.AllocG.AllocW.imp hPc g2 (fun _ _ => And.intro)
  have g4 := Spike.Lib.X64.AllocG.AllocW.imp hCx g3 (fun _ _ => And.intro)
  have g5 := Spike.Lib.X64.AllocG.AllocW.imp hAr g4 (fun _ _ => And.intro)
  have h2 := Spike.Lib.X64.AllocG.AllocW.imp hPh g5 (fun _ _ => And.intro)
  refine Spike.Lib.X64.AllocG.AllocW.imp hS h2 ?_
  rintro s c hst ⟨⟨hab, hac⟩, har, hcx, hpc, hpl', hx, hnr, hr⟩ htp
  exact W0.intro0 hx (Wf.intro (Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt hst fun h => h.elim) hab hac hcl
    (fun _ => hnr) hpl' (fun c' fs' hrun L0 hW hne => .inl (har [] c' fs' hrun L0 hW hne lsize))
    (fun hW => hcx hW htp) hr
    (abortWf_of_off (hI.off s hpc).1.noAbort))

set_option maxHeartbeats 800000 in
/-- **`allocW_WSH_tp` at `ownGHXW`**: `tpG t (HelloPh.WSHX …)`, from `OwnAlloc.allocW_wcGHX` (`ownGHXW`'s separation
`hsep`, `ha`, `hW`, the frame's band on the pool `hb`, the counter and the headers off `tcbM` `hnoM`). -/
theorem allocW_WSHX_tp (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = Spike.Lib.X64.HelloPh.lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (a : BitVec 64) {ms : Spike.Lib.MemSide isa} {q : Call} {t : UInt64}
    (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : Spike.Lib.X64.WakePh.tcbM L ≠ a)
    (hW : Spike.Lib.X64HelloOwnLift.tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hb : Spike.Lib.X64.WakePh.BandOnP L R (-160) 8)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo' : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hpool : L.Λ.stackPool.lo ≤ 2 ^ 64)
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
    (hpl : AllocW ms q (fun s c => Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c []) (fun _ _ => False)
      L.exe L.endPc R F)
    (hX0 : AllocW ms q (fun s _ => X0 s) (fun _ _ => False) L.exe L.endPc R F)
    (hcf : AllocW ms q (fun _ c => (∀ a, c.term ≠ .ret a) ∧ RunWf p c []) (fun _ _ => False)
      L.exe L.endPc R F)
    (hctx : ∀ s c, At L.exe L.endPc R F (N L.lab ms q .rmw) s c → TP t s → Ctx s c [])
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ)
    (hnew : ms.newOk → ar.newOk) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64) :
    AllocW ms q (Spike.Lib.X64.WakeTP.tpG t
        (Spike.Lib.X64.HelloPh.WSHX L a ar p Dt Cl Ctx lbl lsize frM X0))
      (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F := by
  have hI := Spike.Lib.X64.HelloPh.instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hA : Spike.Lib.X64.Alloc.allocIn L.prog = true := by
    rw [hp]; exact Spike.Lib.X64.Flow.HelloRd.hello_alloc
  have hph := Spike.Lib.X64.HelloPh.WcW.allocPhH (Λ := L.Λ) hΛ hlab
  have hS := Spike.Lib.X64.HelloPh.OwnAlloc.allocW_wcGHX (rS := rS) (Λ := L.Λ) hp hlab hsite hsep ha hW hb hlo hΛ
    hR hR8 hlo' hhi hl hh hpool hrl hra hq hmp hmem hno hnoM
  have hPh := allocAbAcH (Cl := Cl) hI hA hph hlab hR hlo' hhi hq hrl hra hmem
  have hAr := Spike.Lib.X64.AllocG.allocArenaS (lbl := lbl) (p := p) hI hA hR hlo' hhi hq hmem hctr hheap
    hoff hnew
  have hCx := Spike.Lib.X64.AllocG.allocCtrS (Ctx := fun s c => TP t s → Ctx s c []) hI hA hR hlo' hhi hq
    (fun a h => hmem a (.inr h)) hheap hlt h64 hctx
  have hPc := Spike.Lib.X64.AllocG.allocPc (R := R) (F := F) (ms := ms) (q := q) hI hph
  have g1 := Spike.Lib.X64.AllocG.AllocW.imp hX0 hcf (fun _ _ => And.intro)
  have g2 := Spike.Lib.X64.AllocG.AllocW.imp hpl g1 (fun _ _ => And.intro)
  have g3 := Spike.Lib.X64.AllocG.AllocW.imp hPc g2 (fun _ _ => And.intro)
  have g4 := Spike.Lib.X64.AllocG.AllocW.imp hCx g3 (fun _ _ => And.intro)
  have g5 := Spike.Lib.X64.AllocG.AllocW.imp hAr g4 (fun _ _ => And.intro)
  have h2 := Spike.Lib.X64.AllocG.AllocW.imp hPh g5 (fun _ _ => And.intro)
  refine Spike.Lib.X64.AllocG.AllocW.imp hS h2 ?_
  rintro s c hst ⟨⟨hab, hac⟩, har, hcx, hpc, hpl', hx, hnr, hr⟩ htp
  exact W0.intro0 hx (Wf.intro (Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt hst fun h => h.elim) hab hac hcl
    (fun _ => hnr) hpl' (fun c' fs' hrun L0 hW hne => .inl (har [] c' fs' hrun L0 hW hne lsize))
    (fun hW => hcx hW htp) hr
    (abortWf_of_off (hI.off s hpc).1.noAbort))

end Spike.Lib.X64.HelloWf

/-- info: 'Spike.Lib.X64.HelloWf.allocW_WSH_tp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloWf.allocW_WSH_tp

/-- info: 'Spike.Lib.X64.HelloWf.allocW_WSHX_tp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloWf.allocW_WSHX_tp
