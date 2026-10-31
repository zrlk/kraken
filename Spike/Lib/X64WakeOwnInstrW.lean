/-
**wake.w's worker keeps its TCB self word, x86-64** (`WCompat.ownInstr`,
X64-OwnInstrW). Off a system call, every instruction of the worker leaves
its owned words `X64WakeOwnX.wakeOwnXW T W`'s thread-1 list
`[(⟨W, 8⟩, W)]` in place, and writes nothing at `⟨W, 8⟩`. This is
`X64WakeAssembly.wCompat_of`'s hypothesis `ownInstr`, discharged for any
worker side whose invariant lies inside `OwnW W` (`Spike/Lib/X64OwnWNodes.lean`).
That holds in particular for a side inside `NNZ exe endPc (wakeZX Λ lbl cS W
exe kp)` (`Spike/Lib/X64WakeZX.lean`), the fragment the worker's segments
keep (`ZX.childThrZA_X`, `cZA_X`).

- `ownInstr_of`: from `OwnW W` at every invariant state;
- `ownInstr_ofX`: from `NNZ … (wakeZX …)` at every invariant state.

**Unlike AArch64** (forced by the x64 shape): on AArch64 the worker owns no
word, and `ownInstr` is `OwnTree.nil`. On x86-64 the worker owns its TCB
self word, which it reads through `%fs:0`.
-/
import Spike.Lib.X64WakeAssembly
import Spike.Lib.X64WakeZX

namespace Spike.Lib.X64WakeW1.OwnInstrW

open Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64WakeA64
open Spike.Lib.X64.Flow.Worker (NNZ)
open Spike.Lib.X64.Flow.Worker.Wake.OwnW (OwnW)
open Spike.Lib.X64.Flow.Worker.Wake.ZX (wakeZX)

variable {Q : WakeRel} {D : WSide Q.ι} {T W : BitVec 64}

/-- **`WCompat.ownInstr`** for a worker side whose invariant lies inside
`OwnW W`, at the owned words `wakeOwnXW T W`. -/
theorem ownInstr_of (hown : Q.own = X64WakeOwnX.wakeOwnXW T W) (hD : ∀ w s c, D.Wi w s c → OwnW W s c) :
    ∀ w s c tree, D.Wi w s c → Scc.Sem.X64.abi.atSys s = false → isa.exec s = some tree →
      Consumer1.OwnTree (fun s => Q.own w 1 s []) (Q.own w 1 s []) tree := by
  intro w s c tree hW hns he
  rw [hown]
  exact .inl ⟨(Consumer1.allInv_true tree).mono fun _ _ => rfl,
    Consumer1.writeTree_mono (fun l _ hl v hm => by
      simp only [X64WakeOwnX.wakeOwnXW_one, List.mem_singleton, Prod.mk.injEq] at hm
      exact hl hm.1) (hD w s c hW hns tree he)⟩

/-- **`WCompat.ownInstr`** for a worker side whose invariant lies inside
`NNZ exe endPc (wakeZX Λ lbl cS W exe kp)`. -/
theorem ownInstr_ofX {exe : _root_.Executable} {endPc : Int64} {kp : Nat} {Λ : Scc.Sem.Layout}
    {lbl : WeakMem.AllocLabel → Option Nat} {cS : WeakMem.Address}
    (hown : Q.own = X64WakeOwnX.wakeOwnXW T W)
    (hD : ∀ w s c, D.Wi w s c → NNZ exe endPc (wakeZX Λ lbl cS W exe kp) s c) :
    ∀ w s c tree, D.Wi w s c → Scc.Sem.X64.abi.atSys s = false → isa.exec s = some tree →
      Consumer1.OwnTree (fun s => Q.own w 1 s []) (Q.own w 1 s []) tree :=
  ownInstr_of hown fun w s c h => Spike.Lib.X64.Flow.Worker.Wake.ZX.ownW (hD w s c h).2

end Spike.Lib.X64WakeW1.OwnInstrW

/-- info: 'Spike.Lib.X64WakeW1.OwnInstrW.ownInstr_ofX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeW1.OwnInstrW.ownInstr_ofX
