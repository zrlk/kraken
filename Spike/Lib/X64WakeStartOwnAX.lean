/-
**`scc_rt_alloc_tcb`'s and `scc_rt_stack_take`'s own-word accesses under
`ownGXW`** (x86-64): `tcbOkA_ownG` / `takeOkA_ownG` with main's memory side
owning `ownGXW` (`ownG`'s words, main's TCB word, the worker's TCB word)
instead of `ownG`. Every word the two callees access is one of `ownG`'s at
the access's state, and `ownG` is a prefix of `ownGXW`.

- `tcbOkA_ownGXW`: `TcbOkA` at `n0 = 0` under `ms.own = ownGXW L a`;
- `takeOkA_ownGXW`: `TakeOkA` at `k0 = 0` under `ms.own = ownGXW L a`.

Where x86-64 differs from AArch64: AArch64's start level owns `ownG`
throughout, so `A64WakeStartOwnA` needs no such lift; x86-64's main also
holds its own and the worker's TCB words (`ownS`, `ownSW`), so the start's
memory side owns `ownGXW`.
-/
import Spike.Lib.X64WakeStartOwnA
import Spike.Lib.X64WakeOwnT2

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout TcbOkA TakeOkA)
open Spike.Lib.X64.Flow.Ret0 (pnA lockA freeNA nextA StOk LdOk)
open Spike.Lib (Region)

variable {L : RuntimeLayout} {a : BitVec 64} {ms : Spike.Lib.MemSide isa} {F0 F : MachineData → Prop}
  {R : Region}

/-- A word owned under `ownG` is owned under `ownGXW`. -/
private theorem mem_ownGXW {s : State} {x : Loc × Val} (h : x ∈ ownG L a s) : x ∈ ownGXW L a s :=
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
node's states** under `ownGXW`, its frame (`R`'s `-184`) off the pool. -/
theorem tcbOkA_ownGXW
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hown : ∀ s, ms.own s = ownGXW L a s)
    {g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G} {c0 : Ctl}
    (hnext : StOk ms F0 (pnA L.lab) (0#64 + Spike.Lib.X64.Flow.Ret0.AllocTcb.tcbLen))
    (hoff : ¬ (L.Λ.stackPool.lo < (R.addr (-184)).toNat ∧
      (R.addr (-184)).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size)) :
    TcbOkA ms F0 L.exe L.endPc R F ⟨g, 0#64, c0⟩ := by
  have h := tcbOkA_ownG (ms := { ms with own := ownG L a }) (F0 := F0) (F := F) (g := g) (c0 := c0) hlab
    (fun _ => rfl) (stOk' hnext) hoff
  exact ⟨hnext, fun s c hA => by rw [hown]; exact mem_ownGXW (h.own s c hA)⟩

/-- **`scc_rt_stack_take`'s three own-word accesses at `k0 = 0`, owned at
their nodes' states** under `ownGXW`, its frame (`R`'s `-200`) off the
pool. -/
theorem takeOkA_ownGXW
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hown : ∀ s, ms.own s = ownGXW L a s)
    {g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G} {c0 : Ctl}
    (hlock1 : StOk ms F0 (lockA L.lab) 1#64) (hfreeN : LdOk ms F0 (freeNA L.lab))
    (hlock0 : StOk ms F0 (lockA L.lab) 0#64)
    (hnext : StOk ms F0 (nextA L.lab) (0#64 + Spike.Lib.X64.Flow.Ret0.StackTake.size0))
    (hoff : ¬ (L.Λ.stackPool.lo < (R.addr (-200)).toNat ∧
      (R.addr (-200)).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size)) :
    TakeOkA ms F0 L.exe L.endPc R F ⟨g, 0#64, c0⟩ := by
  have h := takeOkA_ownG (ms := { ms with own := ownG L a }) (F0 := F0) (F := F) (g := g) (c0 := c0) hlab
    (fun _ => rfl) (stOk' hlock1) (ldOk' hfreeN) (stOk' hlock0) (stOk' hnext) hoff
  exact ⟨hlock1, hfreeN, hlock0, hnext,
    fun b s c hA => by rw [hown]; exact mem_ownGXW (h.ownLock b s c hA),
    fun b s c hA => by rw [hown]; exact mem_ownGXW (h.ownFreeN b s c hA),
    fun b s c hA => by rw [hown]; exact mem_ownGXW (h.ownNext b s c hA)⟩

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.tcbOkA_ownGXW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.tcbOkA_ownGXW

/-- info: 'Spike.Lib.X64.WakePh.takeOkA_ownGXW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.takeOkA_ownGXW
