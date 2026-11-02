/-
**The box's landing into `h2`'s invariant, on x86-64** (the twin of `Spike/Lib/A64HelloH2Box.lean`; the
generic core of `Spike/Lib/X64WakeBoxW.lean`'s `cloneSeg`/`hB_box`/`h1Stmt_box` at hello's `inv2H`):
`Box ⊆ inv2H` from three segments inside the level and its facts `W2 ∧ X2H`, under the take or a `clone`
refusal (`TakeCKS a Cl`):

1. `hmid`: from the box's landing (at no frames) to main's `clone` call `CP`;
2. the refusal: at the `clone`'s `syscall` the segment does not step itself, `CP`'s states are `Cl`'s, the
   refusal (`CloneErrK`) moves them, and the return continues into `Ref` (`cloneSegH`);
3. `hseg`: from `Ref` the threads abort never leaves.

- `cloneSegH`: the refusal's segment (wake's `cloneSeg`), generic in the take pc `a` and `Cl`.
- `hB2_of`: `Box ⊆ inv2H` from `hmid`, the refusal and `hseg` (wake's `hB_box`), `CP`'s states in `W2 ∧ X2H`
  (`hCP`).
- `h2Stmt_box`: `H2StmtH` at `inv2H` (wake's `h1Stmt_box`).

**Where this differs from AArch64**: nothing in the statements; the system call is x86-64's `syscall`
(AArch64: `svc`), and the module is over `isa`, `X64ConsumerA` (`TakeCKS`, `upd`, `updN`), `X64HelloPreA`,
`X64HelloSrc`, `X64HelloH2Inv` and `X64.WakeBoxW.SegWS.kmove`.
-/
import Spike.Lib.X64HelloH2Inv
import Spike.Lib.X64WakeBoxW

namespace Spike.Lib.X64HelloH2Box

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Arena FragS SegWS MemSide FrameRun)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (TakeCKS)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64HelloPreA (H2StmtH)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloH2Inv (X2H inv2H)

/-- **The `clone` refusal's segment** (wake's `cloneSeg`): states of `P` inside `W`, at a refusal `Cl`, off the
take pc `a`, step only by the refusal (`CloneErrK`), whose return continues into `Ref` (`hret`). -/
theorem cloneSegH {a : Int64} {Cl : State → Prop} {W P Ref : FragS isa} {lbl : Lbl}
    {ms : List TermRun.Frame → MemSide isa}
    (hW : ∀ s c fs, P s c fs → W s c fs) (hcl : ∀ s c fs, P s c fs → Cl s)
    (hna : ∀ s c fs, P s c fs → s.st.2 ≠ a)
    (hret : ∀ s c fs, P s c fs → ∀ r, (r = Kernel.neg Kernel.eagain ∨ r = Kernel.neg Kernel.enomem) →
      ∃ c' fs', FrameRun helloSrc (c, fs) (c', fs') ∧ Ref (abi.ret s r) c' fs') :
    SegWS W (TakeCKS a Cl) helloSrc lbl ms P Ref := by
  refine Spike.Lib.X64.WakeBoxW.SegWS.kmove hW (fun s c fs h => ⟨_, .inr ⟨hcl s c fs h, _, .inl rfl, rfl⟩⟩) ?_
  rintro s c fs h s' (⟨hpc, -⟩ | ⟨-, r, hr, rfl⟩)
  · exact (hna s c fs h hpc).elim
  · exact hret s c fs h r hr

section Box

variable {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
  {L : RuntimeLayout} {a endPc : Int64} {L0 : Lbl} {ls0 : Lsize} {Cl : State → Prop}
  {Box : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → State → Spike.Lib.Ctl → Prop}
  {CP Ref : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}

set_option hygiene false in
/-- The level's placement. -/
local notation "L2" => fun (l : WeakMem.AllocLabel) (b : Nat) (l' : WeakMem.AllocLabel) (b' : Nat) =>
  Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64ConsumerA.upd L0 l b) l' b'

set_option hygiene false in
/-- The level's sizes. -/
local notation "S2" => fun (l : WeakMem.AllocLabel) (n : Nat) (l' : WeakMem.AllocLabel) (n' : Nat) =>
  Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64ConsumerA.updN ls0 l n) l' n'

set_option hygiene false in
/-- The level and its facts. -/
local notation "WX" => fun (l : WeakMem.AllocLabel) (b n : Nat) (l' : WeakMem.AllocLabel) (b' n' : Nat) =>
  fun s c fs => W2 l b n l' b' n' s c fs ∧ X2H L a endPc ((L2) l b l' b') ((S2) l n l' n') s c fs

/-- **`Box ⊆ inv2H`** (`HelloH2Inv.h2Stmt_of`'s `hB`; wake's `hB_box`): the box's states run inside `W2 ∧ X2H`
to `CP` (`hmid`), the refusal (`cloneSegH`, `CP`'s states inside `W2 ∧ X2H` at `Cl` off the take pc, `hCP`) to
`Ref` (`hret`), and the threads abort from there never leaves (`hseg`). -/
theorem hB2_of {l : WeakMem.AllocLabel} {b n : Nat} {l' : WeakMem.AllocLabel} {b' n' : Nat}
    (hmid : SegWS ((WX) l b n l' b' n') (TakeCKS a Cl) helloSrc ((L2) l b l' b') (ms2 l b n l' b' n')
      (fun s c fs => Box l b n l' b' n' s c ∧ fs = []) (CP l b n l' b' n'))
    (hCP : ∀ s c fs, CP l b n l' b' n' s c fs → (WX) l b n l' b' n' s c fs ∧ Cl s ∧ s.st.2 ≠ a)
    (hret : ∀ s c fs, CP l b n l' b' n' s c fs → ∀ r, (r = Kernel.neg Kernel.eagain ∨ r = Kernel.neg Kernel.enomem) →
      ∃ c' fs', FrameRun helloSrc (c, fs) (c', fs') ∧ Ref l b n l' b' n' (abi.ret s r) c' fs')
    (hseg : SegWS ((WX) l b n l' b' n') (TakeCKS a Cl) helloSrc ((L2) l b l' b') (ms2 l b n l' b' n')
      (Ref l b n l' b' n') (fun _ _ _ => False)) :
    ∀ s c, Box l b n l' b' n' s c → inv2H W2 (TakeCKS a Cl) ms2 L a endPc L0 ls0 l b n l' b' n' s c [] :=
  fun s c hB => Spike.Lib.X64HelloH2Inv.inv2H_of_segWS (hmid.seq ((cloneSegH (fun s c fs h => (hCP s c fs h).1)
    (fun s c fs h => (hCP s c fs h).2.1) (fun s c fs h => (hCP s c fs h).2.2) hret).seq hseg)) s c [] ⟨hB, rfl⟩

/-- **`H2StmtH` at `inv2H`** from the box's three segments at every index (`hB2_of`; wake's `h1Stmt_box`). -/
theorem h2Stmt_box (ar : Arena)
    (hmid : ∀ l b n l' b' n', L0 l = none → AllocLand ar.heap ar.cells b n →
      Spike.Lib.X64ConsumerA.upd L0 l b l' = none → AllocLand ar.heap ar.cells b' n' →
      SegWS ((WX) l b n l' b' n') (TakeCKS a Cl) helloSrc ((L2) l b l' b') (ms2 l b n l' b' n')
        (fun s c fs => Box l b n l' b' n' s c ∧ fs = []) (CP l b n l' b' n'))
    (hCP : ∀ l b n l' b' n', L0 l = none → AllocLand ar.heap ar.cells b n →
      Spike.Lib.X64ConsumerA.upd L0 l b l' = none → AllocLand ar.heap ar.cells b' n' →
      ∀ s c fs, CP l b n l' b' n' s c fs → (WX) l b n l' b' n' s c fs ∧ Cl s ∧ s.st.2 ≠ a)
    (hret : ∀ l b n l' b' n', L0 l = none → AllocLand ar.heap ar.cells b n →
      Spike.Lib.X64ConsumerA.upd L0 l b l' = none → AllocLand ar.heap ar.cells b' n' →
      ∀ s c fs, CP l b n l' b' n' s c fs → ∀ r, (r = Kernel.neg Kernel.eagain ∨ r = Kernel.neg Kernel.enomem) →
        ∃ c' fs', FrameRun helloSrc (c, fs) (c', fs') ∧ Ref l b n l' b' n' (abi.ret s r) c' fs')
    (hseg : ∀ l b n l' b' n', L0 l = none → AllocLand ar.heap ar.cells b n →
      Spike.Lib.X64ConsumerA.upd L0 l b l' = none → AllocLand ar.heap ar.cells b' n' →
      SegWS ((WX) l b n l' b' n') (TakeCKS a Cl) helloSrc ((L2) l b l' b') (ms2 l b n l' b' n')
        (Ref l b n l' b' n') (fun _ _ _ => False)) :
    H2StmtH W2 (TakeCKS a Cl) ar L0 ms2 L endPc Box (inv2H W2 (TakeCKS a Cl) ms2 L a endPc L0 ls0) :=
  Spike.Lib.X64HelloH2Inv.h2Stmt_of W2 (TakeCKS a Cl) ms2 L a endPc L0 ls0 ar Box
    fun l b n l' b' n' hl hb hl' hb' => hB2_of (hmid l b n l' b' n' hl hb hl' hb')
      (hCP l b n l' b' n' hl hb hl' hb') (hret l b n l' b' n' hl hb hl' hb') (hseg l b n l' b' n' hl hb hl' hb')

end Box

end Spike.Lib.X64HelloH2Box

/-- info: 'Spike.Lib.X64HelloH2Box.cloneSegH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloH2Box.cloneSegH

/-- info: 'Spike.Lib.X64HelloH2Box.hB2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloH2Box.hB2_of

/-- info: 'Spike.Lib.X64HelloH2Box.h2Stmt_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloH2Box.h2Stmt_box
