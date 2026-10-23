/-
**The stack limit as an owned word, for any program on AArch64** (G6 D2,
the runtime side of `Spike.Lib.OwnLim`): the phase `Lim` past the limit's
store in `scc_rt_thread_init`, the store's states `atLim`, and `limPath`,
the `LimPath` of the composition's states from a per-state predicate `LimW`;
and the layout check `layoutOk` on a program from which the layout facts
follow. Generic in the executable and the program: it reads only the
runtime's labels (`preLabels`), which every program's runtime has, and
imports no generated data. Per program (`Spike/Lib/A64Ret0Own.lean`,
`Spike/Lib/A64Hello1Own.lean`): the check by `decide +kernel` at the link's
code address, the layout facts and the ownership at load.

- **The phase is pc-based** (`preStore`): a state is before the limit's
  store iff its pc is in one of the four ranges of code that runs before it,
  `[_start, .L0_scc_rt_start.sp3)` (`_start` falls into `scc_rt_start`),
  `[scc_rt_alloc_tcb, scc_rt_thread_reserve)`,
  `[scc_rt_thread_init, limPc + 4)` (the store included) and
  `[scc_rt_stack_take, scc_rt_stack_release)` (with `scc_rt_take_site`).
  `Lim` is the complement. The word is keyed on the TCB's address (the
  thread pointer is set only at `.L0_scc_rt_start.sp3`, after the store).
- **The state predicate** (`LimW`): the composition's invariant adds it to
  its node clauses, so `limPath` never looks inside the invariant. At
  the store: the cell `str x9, [x10, #8]`, `x10 = tcb`, `x9 = lim rS`, the
  word unmapped in `dmem` and the declarations agreeing there. Elsewhere:
  every leaf of an instruction, every system call's resumption and the take
  keep `preStore` of the pc (so the abort branches of `scc_rt_alloc_tcb`
  and `scc_rt_stack_take`, and the grow path, are the invariant's to
  exclude), and past the store no instruction writes the word.
- **The layout** (`hpre`, `hpost`): the store's pc is before the phase, the
  pc after it is in the phase; from the kernel-decided check `layoutOk` on
  the program (`pre_post_of_layoutOk`, by the labels' addresses `labIn`).
-/
import Spike.Lib.OwnLim
import Spike.Lib.A64Alloc
import Scc.Sem.SysA64
import Scc.Cert.Rt.LayoutA64

namespace Spike.Lib.A64.OwnLimRt

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.OwnLim
open Spike.Lib.A64.Flow (strDir)
open Scc.Sem (Range)
open Scc.Sem.A64 (abi pcOf atSvc atSvc_false_of_cellAt)

/-! ## The phase -/

/-- The executable's labels. -/
abbrev labOf (exe : _root_.Executable) : Label → Int64 := (_root_.Executable.labels exe).label

/-- The pc `pc` is in `[a, b)`. -/
def inR (a b : Int64) (pc : Nat) : Bool := a.toBitVec.toNat ≤ pc && pc < b.toBitVec.toNat

/-- **The pc of the limit's store** (`str x9, [x10, #8]`, field 1 of the
TCB in `scc_rt_thread_init`): instruction 14 (from 0) after its label
`.L5_scc_rt_thread_init.sp0`. It is `storePc lab 1` of
`Spike.Lib.A64.Flow.Ret0.ThreadInit` (by `rfl`), which this module does not
import: it reads no program's data. -/
abbrev limPc (lab : Label → Int64) : Int64 :=
  lab ".L5_scc_rt_thread_init.sp0" + Int64.ofNat (4 * (11 + 3 * 1))

/-- **The code before the limit's store**, by pc: `scc_rt_start` up to the
return of `scc_rt_thread_init` (from `_start`), `scc_rt_alloc_tcb`,
`scc_rt_thread_init` up to and with the store, and `scc_rt_stack_take`. -/
def preStore (lab : Label → Int64) (pc : Nat) : Bool :=
  inR (lab "_start") (lab ".L0_scc_rt_start.sp3") pc ||
  inR (lab "scc_rt_alloc_tcb") (lab "scc_rt_thread_reserve") pc ||
  inR (lab "scc_rt_thread_init") (limPc lab + 4) pc ||
  inR (lab "scc_rt_stack_take") (lab "scc_rt_stack_release") pc

/-- **The limit's store**: the thread at the store of field 1 of
`scc_rt_thread_init` (`str x9, [x10, #8]`). -/
def atLim (exe : _root_.Executable) (s : State) : Prop := s.st.2 = limPc (labOf exe)

/-- **The phase past the limit's store**: the pc outside `preStore`. -/
def Lim (exe : _root_.Executable) (s : State) : Prop := preStore (labOf exe) (pcOf s) = false

/-! ## The state predicate -/

/-- **What the invariant gives at a state `s`** (the executable `exe`, the
take site's states `atTake`, the TCB's address `tcb`, the stack range `rS`):

- `store`: at the limit's store, the cell `str x9, [x10, #8]`, `x10 = tcb`,
  `x9 = lim rS`, the word unmapped in `dmem`, the declarations agreeing;
- `instr`: off the store and off a system call, every leaf of the
  instruction keeps `preStore` of the pc;
- `sys`: every state a system call resumes in keeps it;
- `take`: the take keeps it;
- `noWrite`: past the store, off a system call, the instruction does not
  write the limit's word. -/
structure LimW (exe : _root_.Executable) (atTake : State → Prop) (tcb : BitVec 64) (rS : Range)
    (s : State) : Prop where
  store : atLim exe s →
    CellAt s (strDir .X9 .X10 8) 4 ∧ (s.st.1.regs.getXReg .X10).toBitVec = tcb ∧
    (s.st.1.regs.getXReg .X9).toBitVec = BitVec.ofNat 64 (lim rS) ∧
    Mem.loadInt s.st.1.dmem (limLoc tcb).addr 8 = none ∧ s.decls.AgreesAt (limLoc tcb).addr 8
  instr : ¬ atLim exe s → abi.atSys s = false → ∀ tree, isaLSE2.exec s = some tree →
    tree.AllInv (fun _ _ => True) (fun s' => preStore (labOf exe) (pcOf s') = preStore (labOf exe) (pcOf s))
  sys : abi.atSys s = true → ∀ call, ∀ s' ∈ Scc.Sem.Kernel.certSuccs abi s call,
    preStore (labOf exe) (pcOf s') = preStore (labOf exe) (pcOf s)
  take : atTake s → ∀ m, preStore (labOf exe) (pcOf (abi.skip (abi.setDmem s m))) = preStore (labOf exe) (pcOf s)
  noWrite : Lim exe s → abi.atSys s = false → ∀ tree, isaLSE2.exec s = some tree → NoWrite (limLoc tcb) tree

/-! ## The phase's path -/

/-- `[x10, #8]` is the limit's word of the TCB at `x10`. -/
theorem addr_lim (t : BitVec 64) :
    BitVec.ofInt 64 (t.toInt + (8 : Int64).toInt) = (limLoc t).addr := by
  apply BitVec.eq_of_toInt_eq
  simp only [limLoc, Scc.IR.Tcb.stackLimit, BitVec.toInt_ofInt, BitVec.toInt_add]
  rfl

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
    obtain ⟨hc, h10, h9, hdm, hag⟩ := (hW s hP).store ha
    have hex := exec_str_agrees hc (addr_lim _ ▸ congrArg (fun t => BitVec.ofInt 64 (t.toInt + (8 : Int64).toInt)) h10) hdm hag
    refine ⟨?_, atSvc_false_of_cellAt hc (by intro imm h; cases h), .plain, after s 4 s.st.1, ?_, ?_⟩
    · intro h; unfold Lim pcOf at h; rw [ha, hpre] at h; cases h
    · rw [hex]; simp only [limLoc, Spike.Lib.A64.Alloc.getRegOrZr_x, h9, limVal]
    · unfold Lim pcOf; dsimp only; rw [ha]; exact hpost
  instr s hP ha hs tree he := ((hW s hP).instr ha hs tree he).mono fun _ h => lim_iff h
  sys s hP hs call s' hs' := lim_iff ((hW s hP).sys hs call s' hs')
  take s hP ht m := lim_iff ((hW s hP).take ht m)
  noWrite s hP hL hs tree he := (hW s hP).noWrite hL hs tree he

/-! ## The layout -/

section Layout

open Scc.Cert.Rt.A64 (Lays isIns labelIdx labelIdx_spec getElem?_fst)

/-- An instruction or a label (no data). -/
def insOrLabel (d : Directive) : Bool := isIns d || d.isLabel

/-- The number of instructions among the first `n` directives. -/
def insBefore (prog : List Directive) (n : Nat) : Nat := ((prog.take n).filter isIns).length

/-- **A label's address in a layout of `prog` at `base`**, computed from the
program: `base` plus four bytes per instruction before its first
occurrence. -/
def labIn (base : Nat) (prog : List Directive) (l : Label) : Int64 :=
  match labelIdx prog l with
  | some n => Int64.ofNat base + Int64.ofNat (4 * insBefore prog n)
  | none => -1

/-- `l` is in `prog`, after instructions and labels only. -/
def labOk (prog : List Directive) (l : Label) : Bool :=
  match labelIdx prog l with
  | some n => (prog.take n).all insOrLabel
  | none => false

/-- The labels `preStore` and `limPc` read. -/
def preLabels : List Label :=
  ["_start", ".L0_scc_rt_start.sp3", "scc_rt_alloc_tcb", "scc_rt_thread_reserve", "scc_rt_thread_init",
    "scc_rt_stack_take", "scc_rt_stack_release", ".L5_scc_rt_thread_init.sp0"]

/-- **The layout's check** for `prog` at `base`: the labels in the program,
the limit's store before the phase and the instruction after it in it. -/
def layoutOk (base : Nat) (prog : List Directive) : Bool :=
  preLabels.all (labOk prog) &&
  preStore (labIn base prog) (limPc (labIn base prog)).toBitVec.toNat &&
  !preStore (labIn base prog) (limPc (labIn base prog) + Int64.ofNat 4).toBitVec.toNat

/-- The cells' sizes: four per instruction, none per label. -/
theorem sum_sizes : ∀ (L : List (Directive × Nat)), (∀ c ∈ L, insOrLabel c.1 = true) →
    (∀ c ∈ L, isIns c.1 = true → c.2 = 4) → (∀ c ∈ L, c.1.isLabel = true → c.2 = 0) →
    (L.map (·.2)).sum = 4 * ((L.map (·.1)).filter isIns).length
  | [], _, _, _ => rfl
  | c :: L, hk, h4, h0 => by
    have ih := sum_sizes L (fun c h => hk c (.tail _ h)) (fun c h => h4 c (.tail _ h)) (fun c h => h0 c (.tail _ h))
    simp only [List.map_cons, List.sum_cons, List.filter_cons, ih]
    cases hi : isIns c.1
    · have hl : c.1.isLabel = true := by
        have := hk c (.head _); simp only [insOrLabel, hi, Bool.false_or] at this; exact this
      simp [h0 c (.head _) hl]
    · simp only [ite_true, List.length_cons, h4 c (.head _) hi]; omega

/-- **A label's address in a layout of `prog`** is `labIn`'s. -/
theorem label_labIn {exe : _root_.Executable} [hv : Kraken.Executable.ValidLayout exe] {prog : List Directive}
    (hp : Lays exe prog) {base : Nat} (hb : exe.1 = Int64.ofNat base) {l : Label} (hl : labOk prog l = true) :
    labOf exe l = labIn base prog l := by
  unfold labOk at hl
  unfold labIn
  split at hl
  next n hn =>
    obtain ⟨hpn, hfirst⟩ := labelIdx_spec hn
    obtain ⟨z, hz⟩ := getElem?_fst hp hpn
    have hz0 := hv.label_size n l z hz
    subst hz0
    have hnl : n ≤ prog.length := by
      rcases Nat.lt_or_ge n prog.length with hc | hc
      · exact Nat.le_of_lt hc
      · rw [List.getElem?_eq_none hc] at hpn; cases hpn
    have htake := hp.take_fst hnl
    have hfirst' : ∀ dz ∈ exe.2.take n, dz.1 ≠ Directive.label l := by
      intro dz hdz
      apply hfirst
      rw [← htake]
      exact List.mem_map_of_mem hdz
    rw [labOf, Kraken.Executable.label_addrOf exe l n hz hfirst', Kraken.Executable.addrOf,
      Kraken.Executable.sizeBefore, hb]
    have hmem : ∀ c ∈ exe.2.take n, ∃ i : Nat, exe.2[i]? = some c := by
      intro c hc
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hc
      rw [List.getElem?_take] at hi
      split at hi
      · exact ⟨i, hi⟩
      · cases hi
    rw [sum_sizes _ ?k ?i4 ?l0, htake]
    · rfl
    case k =>
      intro c hc
      have : c.1 ∈ prog.take n := by rw [← htake]; exact List.mem_map_of_mem hc
      exact List.all_eq_true.mp hl _ this
    case i4 =>
      intro c hc hi
      obtain ⟨i, hi'⟩ := hmem c hc
      obtain ⟨d, z⟩ := c
      cases d with
      | instr ins => exact hv.instr_size _ ins z hi'
      | _ => simp [isIns] at hi
    case l0 =>
      intro c hc hi
      obtain ⟨i, hi'⟩ := hmem c hc
      obtain ⟨d, z⟩ := c
      cases d with
      | label l' => exact hv.label_size _ l' z hi'
      | _ => simp [Directive.isLabel] at hi
  · cases hl

/-- **The layout facts of `limPath`** from the check: in a layout of
`prog` at `base` with `layoutOk`, the limit's store is before the phase and
the instruction after it is in it. -/
theorem pre_post_of_layoutOk {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive}
    (hp : Lays exe prog) {base : Nat} (hb : exe.1 = Int64.ofNat base) (h : layoutOk base prog = true) :
    preStore (labOf exe) (limPc (labOf exe)).toBitVec.toNat = true ∧
      preStore (labOf exe) (limPc (labOf exe) + Int64.ofNat 4).toBitVec.toNat = false := by
  simp only [layoutOk, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hl, hpre⟩, hpost⟩ := h
  have e : ∀ l ∈ preLabels, labOf exe l = labIn base prog l := fun l hm =>
    label_labIn hp hb (List.all_eq_true.mp hl l hm)
  simp only [preLabels, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := e
  simp only [preStore, limPc] at hpre hpost ⊢
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  exact ⟨hpre, hpost⟩

/-- **The thread starts before the phase**: in a layout of `prog` at
`base` with `layoutOk`, the pc `base` (the loaded thread's) is before the
limit's store when `preStore` of `labIn` says so. -/
theorem not_lim_of_layoutOk {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive}
    (hp : Lays exe prog) {base : Nat} (hb : exe.1 = Int64.ofNat base) (h : layoutOk base prog = true)
    (h0 : preStore (labIn base prog) (Int64.ofNat base).toBitVec.toNat = true) {s : State} (hs : s.exe = exe)
    (hpc : s.st.2 = Int64.ofNat base) : ¬ Lim s.exe s := by
  simp only [layoutOk, Bool.and_eq_true] at h
  have e : ∀ l ∈ preLabels, labOf exe l = labIn base prog l := fun l hm =>
    label_labIn hp hb (List.all_eq_true.mp h.1.1 l hm)
  simp only [preLabels, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := e
  intro hL
  unfold Lim pcOf at hL
  rw [hs, hpc] at hL
  simp only [preStore, limPc] at hL h0
  rw [e1, e2, e3, e4, e5, e6, e7, e8, h0] at hL
  cases hL

end Layout

/-! ## The store's text -/

open Kraken.AArch64.Parser in
/-- `strDir .X9 .X10 8` is what Kraken's parser makes of the limit's store. -/
example : parseAArch64("str x9, [x10, #8]") = [strDir .X9 .X10 8] := by decide

end Spike.Lib.A64.OwnLimRt
