/-
**`scc_rt_alloc_tcb`'s and `scc_rt_stack_take`'s own-word accesses under `ownGHXW`** (x86-64; the hello twin of
`Spike/Lib/X64WakeStartOwnAX.lean`): `StartOwnA.tcbOkA_ownGH` / `takeOkA_ownGH` with main's memory side owning
`ownGHXW` (`ownGH`'s words, main's TCB word, the worker's TCB word) instead of `ownGH`. Every word the two callees
access is one of `ownGH`'s at the access's state, and `ownGH` is a prefix of `ownGHXW`.

- `tcbOkA_ownGHXW`: `TcbOkA` at `n0 = 0` under `ms.own = ownGHXW L a`;
- `takeOkA_ownGHXW`: `TakeOkA` at `k0 = 0` under `ms.own = ownGHXW L a`.

## Differences from the AArch64 version

AArch64's start level owns `ownGH` throughout, so `A64HelloStartOwnA` needs no such lift; x86-64's main also holds
its own and the worker's TCB words (`ownSH`, `ownSWH`), so the start's memory side owns `ownGHXW`. Against x86-64
wake's: the code is helloCells and the base lemmas are `StartOwnA`'s (`tcbOkA_ownGH`, `takeOkA_ownGH`).
-/
import Spike.Lib.X64HelloStartOwnA
import Spike.Lib.X64HelloOwnSX

namespace Spike.Lib.X64.HelloPh.StartOwnA

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout TcbOkA TakeOkA)
open Spike.Lib.X64.Flow.Ret0 (pnA lockA freeNA nextA StOk LdOk)
open Spike.Lib (Region)

variable {L : RuntimeLayout} {a : BitVec 64} {ms : Spike.Lib.MemSide isa} {F0 F : MachineData → Prop}
  {R : Region}

/-- A word owned under `ownGH` is owned under `ownGHXW`. -/
private theorem mem_ownGHXW {s : State} {x : Loc × Val} (h : x ∈ Spike.Lib.X64.HelloPh.ownGH L a s) : x ∈ Spike.Lib.X64.HelloPh.ownGHXW L a s :=
  List.mem_append_left _ (List.mem_append_left _ h)

/-- `StOk` does not read the owned words. -/
private theorem stOk' {o : State → List (Loc × Val)} {a v : BitVec 64} (h : StOk ms F0 a v) :
    StOk { ms with own := o } F0 a v :=
  ⟨h.rt, h.mp, h.G, h.unmapped⟩

/-- `LdOk` does not read the owned words. -/
private theorem ldOk' {o : State → List (Loc × Val)} {a : BitVec 64} (h : LdOk ms F0 a) :
    LdOk { ms with own := o } F0 a :=
  ⟨h.rt, h.mp, h.unmapped⟩

/-- **`scc_rt_alloc_tcb`'s counter at `n0 = 0`, owned at the `lock xadd`
node's states** under `ownGHXW`, its frame (`R`'s `-184`) off the pool. -/
theorem tcbOkA_ownGHXW
    (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hown : ∀ s, ms.own s = Spike.Lib.X64.HelloPh.ownGHXW L a s)
    {g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G} {c0 : Ctl}
    (hnext : StOk ms F0 (pnA L.lab) (0#64 + Spike.Lib.X64.Flow.Ret0.AllocTcb.tcbLen))
    (hoff : ¬ (L.Λ.stackPool.lo < (R.addr (-184)).toNat ∧
      (R.addr (-184)).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size)) :
    TcbOkA ms F0 L.exe L.endPc R F ⟨g, 0#64, c0⟩ := by
  have h := tcbOkA_ownGH (ms := { ms with own := Spike.Lib.X64.HelloPh.ownGH L a }) (F0 := F0) (F := F) (g := g) (c0 := c0) hlab
    (fun _ => rfl) (stOk' hnext) hoff
  exact ⟨hnext, fun s c hA => by rw [hown]; exact mem_ownGHXW (h.own s c hA)⟩

/-- **`scc_rt_stack_take`'s three own-word accesses at `k0 = 0`, owned at
their nodes' states** under `ownGHXW`, its frame (`R`'s `-200`) off the
pool. -/
theorem takeOkA_ownGHXW
    (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hown : ∀ s, ms.own s = Spike.Lib.X64.HelloPh.ownGHXW L a s)
    {g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G} {c0 : Ctl}
    (hlock1 : StOk ms F0 (lockA L.lab) 1#64) (hfreeN : LdOk ms F0 (freeNA L.lab))
    (hlock0 : StOk ms F0 (lockA L.lab) 0#64)
    (hnext : StOk ms F0 (nextA L.lab) (0#64 + Spike.Lib.X64.Flow.Ret0.StackTake.size0))
    (hoff : ¬ (L.Λ.stackPool.lo < (R.addr (-200)).toNat ∧
      (R.addr (-200)).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size)) :
    TakeOkA ms F0 L.exe L.endPc R F ⟨g, 0#64, c0⟩ := by
  have h := takeOkA_ownGH (ms := { ms with own := Spike.Lib.X64.HelloPh.ownGH L a }) (F0 := F0) (F := F) (g := g) (c0 := c0) hlab
    (fun _ => rfl) (stOk' hlock1) (ldOk' hfreeN) (stOk' hlock0) (stOk' hnext) hoff
  exact ⟨hlock1, hfreeN, hlock0, hnext,
    fun b s c hA => by rw [hown]; exact mem_ownGHXW (h.ownLock b s c hA),
    fun b s c hA => by rw [hown]; exact mem_ownGHXW (h.ownFreeN b s c hA),
    fun b s c hA => by rw [hown]; exact mem_ownGHXW (h.ownNext b s c hA)⟩

end Spike.Lib.X64.HelloPh.StartOwnA

/-- info: 'Spike.Lib.X64.HelloPh.StartOwnA.tcbOkA_ownGHXW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartOwnA.tcbOkA_ownGHXW

/-- info: 'Spike.Lib.X64.HelloPh.StartOwnA.takeOkA_ownGHXW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartOwnA.takeOkA_ownGHXW
