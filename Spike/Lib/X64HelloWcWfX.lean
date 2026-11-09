/-
**hello.w's `wc_main` node and block obligations inside `Wf` at any owned words** (x86-64; twin of
`Spike/Lib/A64HelloWcWf.lean`'s node and block lemmas): AArch64 `WcWf.blkW_wfCH`, `nodeW_wfCH`, `nodeW_wfC_siH` with the
owned-words map a parameter `own` (in the nodes' `SFactsSt2`, `hst`, and in `Wf`), so the same lemmas serve hello's
levels at `ownGH` and at `ownGHXW` (`ownGH ++ ownSH ++ ownSWH`). `StartWf.blkW_wfQH` and `WakeWf.nodeW_wf` are generic
in the owned words, and the code instance (`instOkH`) is used only for the code facts (its owned words are any, here
those at `0`).

- `blkW_wfCX`: a covered `ret`-free block inside `Wf` at `own`.
- `nodeW_wfCX`: a single instruction without an event stepping to `pc + z` inside `Wf` at `own`, its writes'
  obligations given (`hwr`, `NoWrC`).
- `nodeW_wfC_siX`: a silent single instruction inside `Wf` at `own`.

## Differences from the AArch64 version

AArch64's are at `ownGH` only (main owns no TCB word there); here the owned words are a parameter (as x86-64
wake's generic `WcWfS`/`CalWf` lemmas).
- As `X64WakeWcWf` against `A64WakeWcWf`: a block sits at a byte offset `k` of a label (`blockAtB helloCells
  l k blk`, `lab l + k`), its instructions at `cellOff blk j`; a single instruction has a size `z`
  (`[(si.toDir, z)]`, steps to `pc + z`, its phase check `siOffW pfxM l k z`), and its cell is not a
  `syscall` (AArch64: not an `SVC`); no `hal` (no 16-alignment of the region's base).
- `pfxM` is `HelloPh.StartWf.pfxM` (`.Lwc_main`; AArch64 takes it from `Hello.Child`), and the quiet-block
  lemma is `HelloPh.StartWf.blkW_wfQH` (AArch64's `HelloWf.blkW_wfQH`). `nodeW_wfCX` goes through
  `HelloWf.nodeW_phSt` (AArch64's `nodeW_phStH`).
-/
import Spike.Lib.X64HelloWcWf

namespace Spike.Lib.X64.HelloPh.WcWfX

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (blockAtB okPcOf)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout InstOk)
open Spike.Lib.X64Consumer (Lbl Lsize noRetBlk)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64 (ND BlkW NodeW At cellOff okBlk SI)
open Spike.Lib.X64.WakeWf (Wf RunWf NoWrC)
open Spike.Lib.X64.HelloPh (lo instOkH)
open Spike.Lib.X64.HelloPh.StartWf (pfxM)
open Spike.Lib (Arena FragS)
open Kraken.Promising.Lower.X64 (CellAt)

section Gen

variable {L : RuntimeLayout} {own : Spike.Lib.X64Consumer.Own} {K : State → State → Prop} {R : Spike.Lib.Region}
  {F : MachineData → Prop} {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl}
  {lsize : Lsize} {fs : List TermRun.Frame}
  (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)

include hp hlo hlab hsite

/-- **A covered `ret`-free block inside `Wf`** at the frames `fs`, at any owned words `own`: its `SFactsSt2` at
`Dt = False` (`hst`, moved by `K`), its pcs off the sites (`hokpc`), its abort phases' check (`hph`), its
controls not `main`'s `ret` at no frame with their runs well formed (`hJ`), its frames placed (`hpl`). -/
theorem blkW_wfCX {n : ND} {blk : List (Directive × Nat)} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAtB helloCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK)
    (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n blk)
    (hokpc : ∀ j < blk.length,
      okPcOf lo helloCells L.Λ (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true)
    (hph : Spike.Lib.X64.HelloWf.phOffW pfxM l k l blk = true)
    (hnr : noRetBlk blk = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW (fun s c => Wf L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F n blk := by
  have hI := instOkH hp hlo 0#64 (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hst' : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s Dt) K L.exe L.endPc R F n blk :=
    fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 =>
      let r := hst s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9
      ⟨Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt r.1 (fun h => h.elim), r.2⟩
  exact Spike.Lib.X64.HelloPh.StartWf.blkW_wfQH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := fs) hI (hp ▸ hb) he hok hR hlo' hhi hst'
    (fun j hj s h1 h2 h3 => (hI.off s (by unfold pcOf; rw [h3]; exact hokpc j hj)).1)
    (Spike.Lib.X64.HelloWf.phOffW_sound hlab hph)
    (fun _ _ _ j hj r => (Spike.Lib.X64Consumer.noRet_false hnr j hj r).elim) hcl hJ hpl

omit hsite in
/-- **A single instruction without an event inside `Wf`** at the frames `fs`, at any owned words `own`: its `SFactsSt2`
at `Dt = False` (`hst`, moved by `K`), its pc off the take site (`htk`, e.g. `htk_of_freeNH`) and `okPcOf`
(`hokpc`), its next pc off both abort phases' pcs (`hph`), its step to `pc + z` (`hstep`, e.g.
`WakeWf.si_step`), its controls' facts (`hJ`), its frames placed (`hpl`), its writes' obligations (`hwr`). -/
theorem nodeW_wfCX {n : ND} {l : Label} {k z : Nat} (he : L.lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n)
    (htk : ∀ x, (Spike.Lib.X64.PhRec.μ L).site .take = some x → n.pc.toBitVec.toNat ≠ x)
    (hokpc : okPcOf lo helloCells L.Λ n.pc.toBitVec.toNat = true)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l k z = true)
    (hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, CellAt s d z ∧
      (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧ isa.exec s = some tree ∧
      ∀ s' : State, Scc.Sem.TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n)
    (hwr : NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW (fun s c => Wf L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F n := by
  have hP := Spike.Lib.X64.HelloWf.nodeW_phSt (Cl := Cl) (R := R) (F := F) (μ := Spike.Lib.X64.PhRec.μ L)
    (exe := L.exe) (endPc := L.endPc) (pfx := pfxM) he (Spike.Lib.X64.HelloWf.siOffW_sound hlab hph) htk hstep
  have hst' : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s Dt) K L.exe L.endPc R F n :=
    fun s c hA => ⟨Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt (hst s c hA).1 (fun h => h.elim), (hst s c hA).2⟩
  exact Spike.Lib.X64.WakeWf.nodeW_wf hst' (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩)
    (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩) hcl
    (fun s c hA => ⟨⟨(Spike.Lib.X64.WakeWf.nodeW_ofJ hJ s c hA).1.1, (hpl s c hA).1,
      (Spike.Lib.X64.WakeWf.nodeW_ofJ hJ s c hA).1.2⟩, fun _ h => h⟩) hwr
    (Spike.Lib.X64.WakeWf.nodeW_abortWf_off (Spike.Lib.X64.HelloPh.WcWf.habt_of_okPcOfH hp hlo hokpc))

/-- **A silent single instruction inside `Wf`** at the frames `fs`, at any owned words `own` (`nodeW_wfCX` at
`WakeWf.si_step`, writing nothing). -/
theorem nodeW_wfC_siX {n : ND} {si : SI} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(si.toDir, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n)
    (htk : ∀ x, (Spike.Lib.X64.PhRec.μ L).site .take = some x → n.pc.toBitVec.toNat ≠ x)
    (hokpc : okPcOf lo helloCells L.Λ n.pc.toBitVec.toNat = true)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l k z = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW (fun s c => Wf L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F n := by
  have hI := instOkH hp hlo 0#64 (fun _ => False) hsite (rS := ⟨0, 0⟩)
  exact nodeW_wfCX hp hlo hlab he hst htk hokpc hph
    (Spike.Lib.X64.WakeWf.si_step (R := R) (F := F) hI (hp ▸ hb) he) hcl hJ hpl
    (Spike.Lib.X64.WakeWf.nodeW_noWrC (Spike.Lib.X64.AllocG.nodeW_noWr_si hI (hp ▸ hb) he rfl))

end Gen

end Spike.Lib.X64.HelloPh.WcWfX

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.WcWfX.blkW_wfCX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWfX.blkW_wfCX

/-- info: 'Spike.Lib.X64.HelloPh.WcWfX.nodeW_wfCX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWfX.nodeW_wfCX

/-- info: 'Spike.Lib.X64.HelloPh.WcWfX.nodeW_wfC_siX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWfX.nodeW_wfC_siX
