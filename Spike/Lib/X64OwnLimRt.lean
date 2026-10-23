/-
**The stack limit as an owned word, for any program on x64** (G6 D2, the
runtime side of `Spike.Lib.OwnLim`): the x64 twin of
`Spike/Lib/A64OwnLimRt.lean`. The phase `Lim` past the limit's store in
`scc_rt_thread_init`, the store's states `atLim`, and `limPath`, the
`LimPath` of the composition's states from a per-state predicate `LimW`;
and the layout check `layoutOk` on a program's cells from which the layout
facts follow. Generic in the executable and the cells: it reads only the
runtime's labels (`preLabels`), which every program's runtime has, and
imports no generated data. Per program (`Spike/Lib/X64Ret0Own.lean`,
`Spike/Lib/X64Hello1Own.lean`): the
check by `decide +kernel` at the link's code address, the layout facts and
the ownership at load.

- **The phase is pc-based** (`preStore`): a state is before the limit's
  store iff its pc is in one of the four ranges of code that runs before it,
  `[_start, .Lscc_rt_start.x1)` (`_start` calls `scc_rt_start`, which
  follows it after `ud2`), `[scc_rt_alloc_tcb, scc_rt_thread_reserve)`,
  `[scc_rt_thread_init, limPc + 4)` (the store, four bytes, included)
  and `[scc_rt_stack_take, scc_rt_stack_release)` (with
  `scc_rt_take_site`). `Lim` is the complement. The word is keyed on the
  TCB's address (the thread pointer is set by `arch_prctl` only after
  `.Lscc_rt_start.x1`, after the store).
- **The state predicate** (`LimW`): the composition's invariant adds it to
  its node clauses, so `limPath` never looks inside the invariant. At
  the store: the cell `movq %rax, 8(%rcx)`, `%rcx = tcb`, `%rax = lim rS`,
  the word unmapped in `dmem` and the declarations agreeing there.
  Elsewhere: every leaf of an instruction, every system call's resumption
  and the take keep `preStore` of the pc (so the abort branches of
  `scc_rt_alloc_tcb` and `scc_rt_stack_take`, and the grow path, are the
  invariant's to exclude), and past the store no instruction writes the
  word.
- **The layout** (`hpre`, `hpost`): the store's pc is before the phase, the
  pc after it is in the phase; from the kernel-decided check `layoutOk` on
  the cells (`pre_post_of_layoutOk`, by the labels' addresses `labIn`).
-/
import Spike.Lib.OwnLim
import Spike.Lib.X64RtNodes
import Scc.Sem.SysX64
import Scc.Cert.Rt.LaysX64

namespace Spike.Lib.X64.OwnLimRt

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib.OwnLim
open Spike.Lib.X64 (stDir)
open Scc.Sem (Range)
open Scc.Sem.X64 (abi pcOf atSyscall_false_of_cellAt)

/-! ## The phase -/

/-- The executable's labels. -/
abbrev labOf (exe : _root_.Executable) : Label → Int64 := (_root_.Executable.labels exe).label

/-- The pc `pc` is in `[a, b)`. -/
def inR (a b : Int64) (pc : Nat) : Bool := a.toBitVec.toNat ≤ pc && pc < b.toBitVec.toNat

/-- **The pc of the limit's store** (`movq %rax, 8(%rcx)`, field 1 of the
TCB in `scc_rt_thread_init`): 83 bytes after the function's label (the
24-byte stack check to its internal label, then 59). The internal label's
number depends on the program (`.Lscc_rt_thread_init.x7` in `ret0`, `.x8`
in `hello1`), the function's code does not, so the pc is keyed on the
function's label. It is `storePc lab 1` of
`Spike.Lib.X64.Flow.Ret0.ThreadInit` in `ret0`'s layout (checked there by
`decide +kernel`); this module does not import it: it reads no program's
data. -/
abbrev limPc (lab : Label → Int64) : Int64 :=
  lab "scc_rt_thread_init" + Int64.ofNat 83

/-- **The code before the limit's store**, by pc: `_start` and
`scc_rt_start` up to the return of `scc_rt_thread_init`,
`scc_rt_alloc_tcb`, `scc_rt_thread_init` up to and with the store, and
`scc_rt_stack_take`. -/
def preStore (lab : Label → Int64) (pc : Nat) : Bool :=
  inR (lab "_start") (lab ".Lscc_rt_start.x1") pc ||
  inR (lab "scc_rt_alloc_tcb") (lab "scc_rt_thread_reserve") pc ||
  inR (lab "scc_rt_thread_init") (limPc lab + 4) pc ||
  inR (lab "scc_rt_stack_take") (lab "scc_rt_stack_release") pc

/-- **The limit's store**: the thread at the store of field 1 of
`scc_rt_thread_init` (`movq %rax, 8(%rcx)`). -/
def atLim (exe : _root_.Executable) (s : State) : Prop := s.st.2 = limPc (labOf exe)

/-- **The phase past the limit's store**: the pc outside `preStore`. -/
def Lim (exe : _root_.Executable) (s : State) : Prop := preStore (labOf exe) (pcOf s) = false

/-! ## The state predicate -/

/-- **What the invariant gives at a state `s`** (the executable `exe`, the
take site's states `atTake`, the TCB's address `tcb`, the stack range `rS`):

- `store`: at the limit's store, the cell `movq %rax, 8(%rcx)` (four
  bytes), `%rcx = tcb`, `%rax = lim rS`, the word unmapped in `dmem`, the
  declarations agreeing (TODO: the instance supplies `s.decls = {}` from `P`,
  `agrees_of_decls`; the conjunct goes when `LimW` is instantiated);
- `instr`: off the store and off a system call, every leaf of the
  instruction keeps `preStore` of the pc;
- `sys`: every state a system call resumes in keeps it;
- `take`: the take keeps it;
- `noWrite`: past the store, off a system call, the instruction does not
  write the limit's word. -/
structure LimW (exe : _root_.Executable) (atTake : State → Prop) (tcb : BitVec 64) (rS : Range)
    (s : State) : Prop where
  store : atLim exe s →
    CellAt s (stDir .rcx 8 .rax) 4 ∧ s.st.1.regs.get64 .rcx = tcb ∧
    s.st.1.regs.get64 .rax = BitVec.ofNat 64 (lim rS) ∧
    Mem.loadInt s.st.1.dmem (limLoc tcb).addr 8 = none ∧ s.decls.AgreesAt (limLoc tcb).addr 8
  instr : ¬ atLim exe s → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
    tree.AllInv (fun _ _ => True) (fun s' => preStore (labOf exe) (pcOf s') = preStore (labOf exe) (pcOf s))
  sys : abi.atSys s = true → ∀ call, ∀ s' ∈ Scc.Sem.Kernel.certSuccs abi s call,
    preStore (labOf exe) (pcOf s') = preStore (labOf exe) (pcOf s)
  take : atTake s → ∀ m, preStore (labOf exe) (pcOf (abi.skip (abi.setDmem s m))) = preStore (labOf exe) (pcOf s)
  noWrite : Lim exe s → abi.atSys s = false → ∀ tree, isa.exec s = some tree → NoWrite (limLoc tcb) tree

/-! ## The phase's path -/

theorem lim_iff {exe : _root_.Executable} {s s' : State}
    (h : preStore (labOf exe) (pcOf s') = preStore (labOf exe) (pcOf s)) : Lim exe s' ↔ Lim exe s := by
  unfold Lim; rw [h]

/-- **The phase past the limit's store** is a `LimPath` of any paired
states `P` whose every state satisfies `LimW`, given the layout: the
store's pc before the phase, the next pc in it. -/
theorem limPath {exe : _root_.Executable} {atTake : State → Prop} {tcb : BitVec 64} {rS : Range}
    {P : State → Prop} (hW : ∀ s, P s → LimW exe atTake tcb rS s)
    (hpre : preStore (labOf exe) (limPc (labOf exe)).toBitVec.toNat = true)
    (hpost : preStore (labOf exe) (limPc (labOf exe) + Int64.ofNat 4).toBitVec.toNat = false) :
    LimPath abi P (atLim exe) atTake tcb rS (Lim exe) where
  site s hP ha := by
    obtain ⟨hc, hcx, hax, hdm, hag⟩ := (hW s hP).store ha
    have hea : eaddr s 4 (mB .rcx 8) = (limLoc tcb).addr := (eaddr_mB s 4 .rcx 8).trans (by rw [hcx]; rfl)
    have hex := exec_store_agrees hc hea hdm hag
    rw [Reg64s.get_low64] at hex
    refine ⟨?_, atSyscall_false_of_cellAt hc (by intro w w' h; cases h), .plain, after s 4 s.st.1, ?_, ?_⟩
    · intro h; unfold Lim pcOf at h; rw [ha, hpre] at h; cases h
    · rw [hex, hax]; rfl
    · unfold Lim pcOf; dsimp only; rw [ha]; exact hpost
  instr s hP ha hs tree he := ((hW s hP).instr ha hs tree he).mono fun _ h => lim_iff h
  sys s hP hs call s' hs' := lim_iff ((hW s hP).sys hs call s' hs')
  take s hP ht m := lim_iff ((hW s hP).take ht m)
  noWrite s hP hL hs tree he := (hW s hP).noWrite hL hs tree he

/-! ## The layout -/

section Layout

open Scc.Cert.Rt.X64 (Lays labelIdx labelIdx_spec)

/-- **A label's address in a layout of `cells` at `base`**, computed from
the cells: `base` plus the sizes of the cells before its first
occurrence. -/
def labIn (base : Nat) (cells : List (Directive × Nat)) (l : Label) : Int64 :=
  match labelIdx cells l with
  | some n => Int64.ofNat base + Int64.ofNat ((cells.take n).map (·.2)).sum
  | none => -1

/-- The labels `preStore` and `limPc` read. -/
def preLabels : List Label :=
  ["_start", ".Lscc_rt_start.x1", "scc_rt_alloc_tcb", "scc_rt_thread_reserve", "scc_rt_thread_init",
    "scc_rt_stack_take", "scc_rt_stack_release"]

/-- **The layout's check** for `cells` at `base`: the labels in the cells,
the limit's store before the phase and the instruction after it in it. -/
def layoutOk (base : Nat) (cells : List (Directive × Nat)) : Bool :=
  preLabels.all (fun l => (labelIdx cells l).isSome) &&
  preStore (labIn base cells) (limPc (labIn base cells)).toBitVec.toNat &&
  !preStore (labIn base cells) (limPc (labIn base cells) + Int64.ofNat 4).toBitVec.toNat

/-- **A label's address in a layout of `cells`** is `labIn`'s. -/
theorem label_labIn {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)}
    (hp : Lays exe cells) {base : Nat} (hb : exe.1 = Int64.ofNat base) {l : Label}
    (hl : (labelIdx cells l).isSome = true) :
    labOf exe l = labIn base cells l := by
  obtain ⟨ext, he⟩ := hp
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hl
  unfold labIn
  rw [hn]
  obtain ⟨⟨z, hz⟩, hfirst⟩ := labelIdx_spec hn
  have hnl : n < cells.length := by
    rcases Nat.lt_or_ge n cells.length with hc | hc
    · exact hc
    · rw [List.getElem?_eq_none hc] at hz; cases hz
  have hz' : exe.2[n]? = some (.label l, z) := by rw [he, List.getElem?_append_left hnl, hz]
  have hz0 := Kraken.Executable.ValidLayout.label_size n l z hz'
  subst hz0
  have htake : exe.2.take n = cells.take n := by
    rw [he, List.take_append_of_le_length (Nat.le_of_lt hnl)]
  rw [labOf, Kraken.Executable.label_addrOf exe l n hz' (by rw [htake]; exact hfirst),
    Kraken.Executable.addrOf, Kraken.Executable.sizeBefore, hb, htake]

/-- **The layout facts of `limPath`** from the check: in a layout of
`cells` at `base` with `layoutOk`, the limit's store is before the phase
and the instruction after it is in it. -/
theorem pre_post_of_layoutOk {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
    {cells : List (Directive × Nat)} (hp : Lays exe cells) {base : Nat} (hb : exe.1 = Int64.ofNat base)
    (h : layoutOk base cells = true) :
    preStore (labOf exe) (limPc (labOf exe)).toBitVec.toNat = true ∧
      preStore (labOf exe) (limPc (labOf exe) + Int64.ofNat 4).toBitVec.toNat = false := by
  simp only [layoutOk, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hl, hpre⟩, hpost⟩ := h
  have e : ∀ l ∈ preLabels, labOf exe l = labIn base cells l := fun l hm =>
    label_labIn hp hb (List.all_eq_true.mp hl l hm)
  simp only [preLabels, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := e
  simp only [preStore, limPc] at hpre hpost ⊢
  rw [e1, e2, e3, e4, e5, e6, e7]
  exact ⟨hpre, hpost⟩

/-- **The thread starts before the phase**: in a layout of `cells` at
`base` with `layoutOk`, the pc `base` (the loaded thread's) is before the
limit's store when `preStore` of `labIn` says so. -/
theorem not_lim_of_layoutOk {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)}
    (hp : Lays exe cells) {base : Nat} (hb : exe.1 = Int64.ofNat base) (h : layoutOk base cells = true)
    (h0 : preStore (labIn base cells) (Int64.ofNat base).toBitVec.toNat = true) {s : State} (hs : s.exe = exe)
    (hpc : s.st.2 = Int64.ofNat base) : ¬ Lim s.exe s := by
  simp only [layoutOk, Bool.and_eq_true] at h
  have e : ∀ l ∈ preLabels, labOf exe l = labIn base cells l := fun l hm =>
    label_labIn hp hb (List.all_eq_true.mp h.1.1 l hm)
  simp only [preLabels, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := e
  intro hL
  unfold Lim pcOf at hL
  rw [hs, hpc] at hL
  simp only [preStore, limPc] at hL h0
  rw [e1, e2, e3, e4, e5, e6, e7, h0] at hL
  cases hL

end Layout

/-! ## The store's text -/

open Kraken.X64.Parser in
/-- `stDir .rcx 8 .rax` is what Kraken's parser makes of the limit's store. -/
example : parse("movq %rax, 8(%rcx)") = [stDir .rcx 8 .rax] := by decide

end Spike.Lib.X64.OwnLimRt
