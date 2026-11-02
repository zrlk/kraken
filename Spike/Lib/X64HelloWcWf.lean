/-
**hello.w's `wc_main` before the spawn inside `Wf`** (x86-64; twin of `Spike/Lib/A64HelloWcWf.lean`, the hello
twin of `Spike/Lib/X64WakeWcWf.lean` at `helloCells`): the generic node and block obligations inside
`WakeWf.Wf` at any frame list `fs`, at hello.w's global owned-words map `ownGH` and threads abort phase
`Hello.ThreadsAb.AcH`, from a node's `SFactsSt2` at `ownGH` (`Dt` free), its pcs off the sites, its abort
phases' decided checks (`HelloWf.phOffW`, `siOffW`) and its controls' facts. Generic in the layout `L`, the
counter `a`, the move `K`, the arena, the source, the clone path and the level.

Wake's `frameRun_hold`, `RunWf.hold`, `PlacedSE.hold` (`X64WakeWcWf`) are program independent and reused as is.

- `blkW_wfCH`: a covered `ret`-free block inside `Wf` (`HelloPh.StartWf.blkW_wfQH` at `instOkH`).
- `nodeW_wfCH`: a single instruction without an event stepping to `pc + z` inside `Wf`, its writes'
  obligations given (`hwr`, `NoWrC`).
- `nodeW_wfC_siH`: a silent single instruction inside `Wf` (`WakeWf.si_step` at `instOkH`, writing nothing).
- `htk_of_freeNH`, `habt_of_okPcOfH`: a free pc is off the take site, a pc `okPcOf` is off the abort sites.

## Differences from the AArch64 version

- As `X64WakeWcWf` against `A64WakeWcWf`: a block sits at a byte offset `k` of a label (`blockAtB helloCells
  l k blk`, `lab l + k`), its instructions at `cellOff blk j`; a single instruction has a size `z`
  (`[(si.toDir, z)]`, steps to `pc + z`, its phase check `siOffW pfxM l k z`), and its cell is not a
  `syscall` (AArch64: not an `SVC`); no `hal` (no 16-alignment of the region's base).
- `pfxM` is `HelloPh.StartWf.pfxM` (`.Lwc_main`; AArch64 takes it from `Hello.Child`), and the quiet-block
  lemma is `HelloPh.StartWf.blkW_wfQH` (AArch64's `HelloWf.blkW_wfQH`). `nodeW_wfCH` goes through
  `HelloWf.nodeW_phSt` (AArch64's `nodeW_phStH`).
- Not twinned (unreachable from the AArch64 root, so twins only live constants): none.
-/
import Spike.Lib.X64HelloStartWf
import Spike.Lib.X64WakeWcWf

namespace Spike.Lib.X64.HelloPh.WcWf

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
open Spike.Lib.X64.HelloPh.WcW (freeNH site_ne_of_freeNH)
open Spike.Lib.X64.HelloPh.StartWf (pfxM)
open Spike.Lib (Arena FragS)
open Kraken.Promising.Lower.X64 (CellAt)

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {K : State → State → Prop} {R : Spike.Lib.Region}
  {F : MachineData → Prop} {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl}
  {lsize : Lsize} {fs : List TermRun.Frame}
  (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)

include hsite hlab in
/-- **A free pc is off the take site.** -/
theorem htk_of_freeNH {pc : Int64} (hf : freeNH pc.toBitVec.toNat = true) :
    ∀ x, (Spike.Lib.X64.PhRec.μ L).site .take = some x → pc.toBitVec.toNat ≠ x := fun x hx => by
  rw [hsite] at hx; cases hx; exact site_ne_of_freeNH hlab hf

include hp hlo in
/-- **A pc `okPcOf` is off the abort sites.** -/
theorem habt_of_okPcOfH {pc : Int64} (hok : okPcOf lo helloCells L.Λ pc.toBitVec.toNat = true) :
    ∀ k x, (Spike.Lib.X64.PhRec.μ L).abortAt k = some x → pc.toBitVec.toNat ≠ x := fun j _ hx =>
  Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hok) (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx

include hp hlo hlab hsite

/-- **A covered `ret`-free block inside `Wf`** at the frames `fs`, at `ownGH`: its `SFactsSt2` at
`Dt = False` (`hst`, moved by `K`), its pcs off the sites (`hokpc`), its abort phases' check (`hph`), its
controls not `main`'s `ret` at no frame with their runs well formed (`hJ`), its frames placed (`hpl`). -/
theorem blkW_wfCH {n : ND} {blk : List (Directive × Nat)} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAtB helloCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK)
    (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) K L.exe L.endPc R F n blk)
    (hokpc : ∀ j < blk.length,
      okPcOf lo helloCells L.Λ (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true)
    (hph : Spike.Lib.X64.HelloWf.phOffW pfxM l k l blk = true)
    (hnr : noRetBlk blk = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW (fun s c => Wf L.Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F n blk := by
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hst' : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s Dt) K L.exe L.endPc R F n blk :=
    fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 =>
      let r := hst s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9
      ⟨Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt r.1 (fun h => h.elim), r.2⟩
  exact Spike.Lib.X64.HelloPh.StartWf.blkW_wfQH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := fs) hI (hp ▸ hb) he hok hR hlo' hhi hst'
    (fun j hj s h1 h2 h3 => (hI.off s (by unfold pcOf; rw [h3]; exact hokpc j hj)).1)
    (Spike.Lib.X64.HelloWf.phOffW_sound hlab hph)
    (fun _ _ _ j hj r => (Spike.Lib.X64Consumer.noRet_false hnr j hj r).elim) hcl hJ hpl

omit hsite in
/-- **A single instruction without an event inside `Wf`** at the frames `fs`, at `ownGH`: its `SFactsSt2`
at `Dt = False` (`hst`, moved by `K`), its pc off the take site (`htk`, e.g. `htk_of_freeNH`) and `okPcOf`
(`hokpc`), its next pc off both abort phases' pcs (`hph`), its step to `pc + z` (`hstep`, e.g.
`WakeWf.si_step`), its controls' facts (`hJ`), its frames placed (`hpl`), its writes' obligations (`hwr`). -/
theorem nodeW_wfCH {n : ND} {l : Label} {k z : Nat} (he : L.lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) K L.exe L.endPc R F n)
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
    NodeW (fun s c => Wf L.Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F n := by
  have hP := Spike.Lib.X64.HelloWf.nodeW_phSt (Cl := Cl) (R := R) (F := F) (μ := Spike.Lib.X64.PhRec.μ L)
    (exe := L.exe) (endPc := L.endPc) (pfx := pfxM) he (Spike.Lib.X64.HelloWf.siOffW_sound hlab hph) htk hstep
  have hst' : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s Dt) K L.exe L.endPc R F n :=
    fun s c hA => ⟨Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt (hst s c hA).1 (fun h => h.elim), (hst s c hA).2⟩
  exact Spike.Lib.X64.WakeWf.nodeW_wf hst' (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩)
    (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩) hcl
    (fun s c hA => ⟨⟨(Spike.Lib.X64.WakeWf.nodeW_ofJ hJ s c hA).1.1, (hpl s c hA).1,
      (Spike.Lib.X64.WakeWf.nodeW_ofJ hJ s c hA).1.2⟩, fun _ h => h⟩) hwr
    (Spike.Lib.X64.WakeWf.nodeW_abortWf_off (habt_of_okPcOfH hp hlo hokpc))

/-- **A silent single instruction inside `Wf`** at the frames `fs`, at `ownGH` (`nodeW_wfCH` at
`WakeWf.si_step`, writing nothing). -/
theorem nodeW_wfC_siH {n : ND} {si : SI} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(si.toDir, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) K L.exe L.endPc R F n)
    (htk : ∀ x, (Spike.Lib.X64.PhRec.μ L).site .take = some x → n.pc.toBitVec.toNat ≠ x)
    (hokpc : okPcOf lo helloCells L.Λ n.pc.toBitVec.toNat = true)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l k z = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW (fun s c => Wf L.Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F n := by
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
  exact nodeW_wfCH hp hlo hlab he hst htk hokpc hph
    (Spike.Lib.X64.WakeWf.si_step (R := R) (F := F) hI (hp ▸ hb) he) hcl hJ hpl
    (Spike.Lib.X64.WakeWf.nodeW_noWrC (Spike.Lib.X64.AllocG.nodeW_noWr_si hI (hp ▸ hb) he rfl))

end Gen

end Spike.Lib.X64.HelloPh.WcWf

/-! ## Axioms -/

/--
info: 'Spike.Lib.X64.HelloPh.WcWf.htk_of_freeNH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWf.htk_of_freeNH

/--
info: 'Spike.Lib.X64.HelloPh.WcWf.blkW_wfCH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWf.blkW_wfCH

/--
info: 'Spike.Lib.X64.HelloPh.WcWf.nodeW_wfCH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWf.nodeW_wfCH

/--
info: 'Spike.Lib.X64.HelloPh.WcWf.nodeW_wfC_siH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWf.nodeW_wfC_siH
