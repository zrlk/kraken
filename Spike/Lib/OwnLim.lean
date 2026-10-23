/-
**The stack limit as an owned word** (G6 D2): the thread control block's
`stackLimit` word (`Scc.IR.Tcb.stackLimit`) as a runtime word the thread
owns (`MemSide.own`), so a runtime load of it reads the limit `L` and a
stack check's branch to the grow path is never taken.

`scc_rt_thread_init` takes the thread's stack range `rS` and stores
`L = rS.lo + Tcb.headroom` (`lim rS`) to `[tcb + stackLimit]` (`limLoc tcb`,
`tcb` the thread control block's address); no later runtime store writes
that word. The owned words of a thread state `s` are then
`ownLim tcb rS Lim s`: the one entry `(limLoc tcb, limVal rS)` once past
that store (the phase `Lim`), none before. The word is keyed on the TCB's
address, a ghost of the thread like `rS`, not on the thread pointer: the
runtime sets the thread pointer to `tcb` only after `scc_rt_thread_init`
returns (`msr tpidr_el0` / `arch_prctl`), so a stack check's load of
`[tp + stackLimit]` hits the owned word where the node invariant has
`tp = tcb`. Generic over the ISA's kernel interface `A`
(`Scc.Sem.Kernel.Abi`): the stack pointer is `A.sp`.

- **The phase** (`LimPath`, over the paired states `P`): at the store
  (`atLim`) the instruction is the store of `limVal rS` to `limLoc tcb` and
  every leaf is in the phase; off it no instruction, system call or take
  enters or leaves the phase; in the phase no instruction writes the word
  (`NoWrite`).
- **The owned words change only at the store** (`LimPath.keep`,
  `LimPath.store`, `LimPath.noWrite_own`): off the store every leaf owns
  what `s` owns; at it `s` owns nothing and every leaf owns exactly the
  store's location and value; and in the phase no instruction writes an
  owned word. These are what the consumer's frame condition over the
  execution tree (`Nodes.ownFrame`) asks of `own`.
- **The node clause** (`SpOk`): the stack pointer is at least the limit
  plus the node's stack need (`Scc.Lower.stackNeed`, checked per program by
  `Scc.Cert.NeedA64.needOk` / `Scc.Cert.NeedX64.needOk`).
-/
import Scc.Sem.Kernel
import Scc.IR.Core
import Kraken.Promising.InvLink
import Spike.Lib.Consumer1

namespace Spike.Lib.OwnLim

open Kraken.Promising
open Scc.Sem (Range)

variable {I : ISA} (A : Scc.Sem.Kernel.Abi I)

/-! ## The owned word -/

/-- **The stack limit** of the range `rS`: its base plus the headroom. -/
def lim (rS : Range) : Nat := rS.lo + Scc.IR.Tcb.headroom

/-- The limit as the value of the word: a 64-bit store's value. -/
def limVal (rS : Range) : Val := (BitVec.ofNat 64 (lim rS)).setWidth 128

/-- **The limit's word**: the `stackLimit` field of the TCB at `tcb`. -/
def limLoc (tcb : BitVec 64) : Loc := ⟨tcb + BitVec.ofNat 64 Scc.IR.Tcb.stackLimit, 8⟩

open Classical in
/-- **The owned words**: the limit's word holding `lim rS` in the phase
`Lim`, nothing before it. -/
noncomputable def ownLim (tcb : BitVec 64) (rS : Range) (Lim : I.State → Prop) (s : I.State) :
    List (Loc × Val) :=
  if Lim s then [(limLoc tcb, limVal rS)] else []

/-- **The node clause**: the stack pointer is at least the limit plus the
node's stack need `need`. -/
def SpOk (rS : Range) (need : Nat) (s : I.State) : Prop := lim rS + need ≤ A.sp s

variable {A} {tcb : BitVec 64} {rS : Range} {Lim : I.State → Prop}

theorem mem_ownLim {s : I.State} {L : Loc} {w : Val} :
    (L, w) ∈ ownLim tcb rS Lim s ↔ Lim s ∧ L = limLoc tcb ∧ w = limVal rS := by
  unfold ownLim
  split <;> simp_all

theorem ownLim_of_not {s : I.State} (h : ¬ Lim s) : ownLim tcb rS Lim s = [] := by
  simp [ownLim, h]

theorem ownLim_of {s : I.State} (h : Lim s) : ownLim tcb rS Lim s = [(limLoc tcb, limVal rS)] := by
  simp [ownLim, h]

/-- The owned words are the same in a state in the same phase. -/
theorem ownLim_eq {s s' : I.State} (hL : Lim s' ↔ Lim s) : ownLim tcb rS Lim s' = ownLim tcb rS Lim s := by
  unfold ownLim
  rw [propext hL]

/-! ## No write of a word -/

/-- **No store or read-modify-write of `L`** in an execution tree. -/
def NoWrite {σ : Type} (L : Loc) : EvTree σ → Prop
  | .done _ => True
  | .fault _ => True
  | .choose _ k => ∀ i, NoWrite L (k i)
  | .load _ _ _ ret => ∀ v, NoWrite L (ret v)
  | .store _ _ l _ ret => l ≠ L ∧ ∀ b, NoWrite L (ret b)
  | .rmw _ _ l _ ret => l ≠ L ∧ ∀ v, NoWrite L (ret v)
  | .fence _ ret => ∀ u, NoWrite L (ret u)

/-- **No write of `L` is a `WriteTree`** of the locations other than `L`. -/
theorem NoWrite.writeTree {σ : Type} {L : Loc} :
    ∀ {t : EvTree σ}, NoWrite L t → Scc.Sem.WriteTree (fun l _ => l ≠ L) t
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ _, h => fun i => NoWrite.writeTree (h i)
  | .load _ _ _ _, h => fun v => NoWrite.writeTree (h v)
  | .store _ _ _ _ _, h => ⟨h.1, fun b => NoWrite.writeTree (h.2 b)⟩
  | .rmw _ _ _ _ _, h => ⟨fun _ _ _ => h.1, fun v => NoWrite.writeTree (h.2 v)⟩
  | .fence _ _, h => fun u => NoWrite.writeTree (h u)

/-! ## The phase -/

variable (A) in
/-- **The phase past the limit's store** (paired states `P`, the store's
states `atLim`, the take site's states `atTake`, the TCB's address `tcb`,
the stack range `rS`, the phase `Lim`):

- `site`: a paired state at the store is before the phase, off a system
  call, and its instruction is a store of `limVal rS` to `limLoc tcb`
  followed by nothing but a state in the phase (`Consumer1.OwnTree`'s
  store case);
- `instr`: off the store and off a system call, every leaf of the
  instruction is in the phase iff the state is;
- `sys`: likewise for every state a system call may resume the thread in;
- `take`: likewise for the take (`skip ∘ setDmem`);
- `noWrite`: in the phase, off a system call, no instruction writes the
  limit's word. -/
structure LimPath (P : I.State → Prop) (atLim atTake : I.State → Prop) (tcb : BitVec 64) (rS : Range)
    (Lim : I.State → Prop) : Prop where
  site : ∀ s, P s → atLim s → ¬ Lim s ∧ A.atSys s = false ∧
    ∃ kr s', I.exec s = some (.store kr false (limLoc tcb) (limVal rS) fun _ => .done s') ∧ Lim s'
  instr : ∀ s, P s → ¬ atLim s → A.atSys s = false → ∀ tree, I.exec s = some tree →
    tree.AllInv (fun _ _ => True) (fun s' => Lim s' ↔ Lim s)
  sys : ∀ s, P s → A.atSys s = true → ∀ call, ∀ s' ∈ Scc.Sem.Kernel.certSuccs A s call, Lim s' ↔ Lim s
  take : ∀ s, P s → atTake s → ∀ m, Lim (A.skip (A.setDmem s m)) ↔ Lim s
  noWrite : ∀ s, P s → Lim s → A.atSys s = false → ∀ tree, I.exec s = some tree → NoWrite (limLoc tcb) tree

namespace LimPath

variable {P atLim atTake : I.State → Prop} (h : LimPath A P atLim atTake tcb rS Lim)
include h

/-- **Off the store, the owned words are kept**: every leaf of the
instruction owns what the state owns. -/
theorem keep {s : I.State} (hP : P s) (ha : ¬ atLim s) (hs : A.atSys s = false) {tree : EvTree I.State}
    (he : I.exec s = some tree) :
    tree.AllInv (fun _ _ => True) (fun s' => ownLim tcb rS Lim s' = ownLim tcb rS Lim s) :=
  (h.instr s hP ha hs tree he).mono fun _ hL => ownLim_eq hL

/-- **At the store**, the state owns nothing, and its instruction is the
store of `limVal rS` to `limLoc` into a state that owns exactly that
location and value. -/
theorem store {s : I.State} (hP : P s) (ha : atLim s) :
    ownLim tcb rS Lim s = [] ∧ A.atSys s = false ∧
      ∃ kr s', I.exec s = some (.store kr false (limLoc tcb) (limVal rS) fun _ => .done s') ∧
        ownLim tcb rS Lim s' = [(limLoc tcb, limVal rS)] := by
  obtain ⟨hn, hs, kr, s', he, hL⟩ := h.site s hP ha
  exact ⟨ownLim_of_not hn, hs, kr, s', he, ownLim_of hL⟩

/-- **A system call keeps the owned words.** -/
theorem sys_keep {s : I.State} (hP : P s) (hs : A.atSys s = true) {call : Scc.Sem.Kernel.Call}
    {s' : I.State} (hs' : s' ∈ Scc.Sem.Kernel.certSuccs A s call) :
    ownLim tcb rS Lim s' = ownLim tcb rS Lim s :=
  ownLim_eq (h.sys s hP hs call s' hs')

/-- **The take keeps the owned words.** -/
theorem take_keep {s : I.State} (hP : P s) (ha : atTake s) (m : _root_.Mem 64) :
    ownLim tcb rS Lim (A.skip (A.setDmem s m)) = ownLim tcb rS Lim s :=
  ownLim_eq (h.take s hP ha m)

/-- **No instruction writes an owned word**, off a system call. -/
theorem noWrite_own {s : I.State} (hP : P s) (hs : A.atSys s = false) {tree : EvTree I.State}
    (he : I.exec s = some tree) {L : Loc} {w : Val} (hm : (L, w) ∈ ownLim tcb rS Lim s) : NoWrite L tree := by
  obtain ⟨hL, rfl, -⟩ := mem_ownLim.mp hm
  exact h.noWrite s hP hL hs tree he

/-- **One instruction off a system call is `Consumer1.OwnTree`** for the
owned words `ownLim tcb rS Lim` (`Nodes.ownInstr`): at the store, its
second case; elsewhere, its first (`keep`, and `noWrite` in the phase). -/
theorem ownTree {s : I.State} (hP : P s) (hs : A.atSys s = false) {tree : EvTree I.State}
    (he : I.exec s = some tree) :
    Spike.Lib.Consumer1.OwnTree (ownLim tcb rS Lim) (ownLim tcb rS Lim s) tree := by
  by_cases ha : atLim s
  · obtain ⟨h0, -, kr, s', he', h1⟩ := h.store hP ha
    rw [he] at he'
    cases he'
    exact .inr (.inl ⟨h0, kr, limLoc tcb, limVal rS, s', rfl, rfl, h1⟩)
  · refine .inl ⟨h.keep hP ha hs he, ?_⟩
    by_cases hL : Lim s
    · rw [ownLim_of hL]
      exact Spike.Lib.Consumer1.writeTree_mono (fun l _ hl w hm => hl (Prod.mk.inj (List.mem_singleton.mp hm)).1)
        (NoWrite.writeTree (h.noWrite s hP hL hs tree he))
    · rw [ownLim_of_not hL]
      exact Spike.Lib.Consumer1.writeTree_mono (fun _ _ _ _ hm => by simp at hm)
        (Spike.Lib.Consumer1.writeTree_true tree)

/-- **A system call keeps the owned words** (`Nodes.ownSys`, any call the
kernel decodes). -/
theorem ownSys {s : I.State} (hP : P s) (hs : A.atSys s = true) (call : Scc.Sem.Kernel.Call) :
    ∀ s' ∈ Scc.Sem.Kernel.certSuccs A s call, ownLim tcb rS Lim s' = ownLim tcb rS Lim s :=
  fun _ hs' => h.sys_keep hP hs hs'

end LimPath

end Spike.Lib.OwnLim
