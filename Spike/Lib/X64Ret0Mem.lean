/-
**`ret0.w` on x64: the layout's memory-side facts**, the premises of
`start_seg` (`Spike/Lib/X64Ret0.lean`) that its layout `ret0Λ` decides, in
the canonical loader's thread (`ret0Exe`) at own words `n0 = k0 = 0`.

- **The runtime's words** (`symAt`, `ret0_pinA` …): the six data symbols'
  labels in the loaded thread, decided on its cells. The loader places the
  symbols with `List.mergeSort`, which the kernel does not evaluate;
  `mergeSort_symSort` (`Spike/Lib/SegCommon.lean`) replaces it by an
  insertion sort (`placeSyms_eq`, `ret0Cells'`). Each decided fact is a
  small Boolean check (`symAt`, `clearOf`, `mappedB`).
- **The words `start_seg` touches** (`ret0Words`): the four counters, the
  TCB's header, its six fields (the limit word among them). The entry frame
  condition `ret0F` has each of them unmapped in `dmem`; they lie outside the
  entry stack (`ret0Words_entry`) and the stack pool (`ret0Words_pool`), the
  disjointness the frame condition's stability needs.
- **The memory side** is `msOf ret0Λ μ rd G own ret0Λ.static lsize`
  (`Spike/Lib/X64Consumer.lean`): `ret0` has no static labels, so every
  address is the runtime's (`rt_static`); each word is mapped in the loaded
  kernel state and shared (`ret0Words_mapped`). The builders (`stOk_ret0`,
  `ldOk_ret0`, `limOk_ret0`) take what is not layout: the value invariant
  `G` at the word and, for the limit, its room.
- **`start_seg`'s premises at `0`**: the arithmetic ones (`ret0_hn`,
  `ret0_hk`, `ret0_hok`, `ret0_hfit`, `ret0_hout`) and the memory-side ones
  (`ret0_hhdr`, `ret0_hfld`, `ret0_tcbOk`, `ret0_takeOk`, `ret0_limOk`),
  the last given `G` at each word, the own words' values (`OwnAt`) and the
  limit's room.
-/
import Spike.Lib.X64Ret0
import Spike.Lib.X64Consumer

namespace Spike.Lib.X64.Flow.Ret0.Mem

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.X64.Parser Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays endOf labelIdx labelIdx_spec)
open Spike.Lib.X64Consumer (msOf K0 Own)
open Spike.Lib.Consumer1 (LocIn)
open SccCode (ret0Λ ret0Cells ret0Secs)

/-! ## The loaded thread's labels -/

/-- The executable's labels. -/
abbrev labOf (exe : _root_.Executable) : Label → Int64 := (_root_.Executable.labels exe).label

/-- **`ret0`'s loaded executable**: the canonical loader's thread at the
Linux entry state. -/
abbrev ret0Exe : _root_.Executable :=
  (Scc.Sem.X64.threadAt Scc.Sem.Entry.linux ret0Λ.code.lo ret0Cells (Scc.Sem.loadSyms ret0Λ ret0Secs.rodata)).exe

/-- Its end address. -/
abbrev ret0End : Int64 := endOf ret0Exe ret0Cells

/-- `ret0`'s symbols all lie at or above its code (by `decide +kernel`):
static-link-only, at `ret0`'s link `SccCode.ret0Λ`, for the instance's lemmas
that take no prefix (a layout with data symbols below the code goes through
`RuntimeLayout.ofPlaceOK`, `pfx := belowLen`). -/
theorem ret0_above :
    ∀ p ∈ Scc.Sem.loadSyms SccCode.ret0Λ SccCode.ret0Secs.rodata, SccCode.ret0Λ.code.lo ≤ p.2 := by
  decide +kernel

instance : Kraken.Executable.ValidLayout ret0Exe :=
  Scc.Cert.Link.X64.validLayout_of_loadOk SccCode.ret0Λ_load _

theorem ret0_lays : Lays ret0Exe ret0Cells := Scc.Cert.Link.X64.lays_threadAt _ _ _ _ ret0_above

/-- **A label's address from its first cell** in a valid layout. -/
theorem label_idx {e : _root_.Executable} [hv : Kraken.Executable.ValidLayout e] {l : Label} {n : Nat}
    (h : labelIdx e.2 l = some n) : labOf e l = e.1 + Int64.ofNat ((e.2.take n).map (·.2)).sum := by
  obtain ⟨⟨z, hz⟩, hfirst⟩ := labelIdx_spec h
  have hz0 := hv.label_size n l z hz
  subst hz0
  rw [labOf, Kraken.Executable.label_addrOf e l n hz hfirst]
  rfl

/-- The loader's data symbols in address order, by insertion sort. -/
def ret0Syms : List (String × Nat) := symSort (Scc.Sem.loadSyms ret0Λ ret0Secs.rodata)

theorem ret0Syms_perm : ret0Syms.Perm (Scc.Sem.loadSyms ret0Λ ret0Secs.rodata) := by decide +kernel

theorem ret0Syms_sorted : ret0Syms.Pairwise (fun a b => a.2 < b.2) := by decide +kernel

/-- **The loaded thread's cells**, with the data symbols placed in
`ret0Syms`' order (`Scc.Sem.placeSyms` without its `mergeSort`). -/
def ret0Cells' : List (Directive × Nat) :=
  ret0Cells ++ placeL (Directive.byteArray (.mk #[])) Directive.label (Scc.Sem.X64.codeEnd ret0Λ.code.lo ret0Cells)
    ret0Syms

theorem ret0Exe_cells : ret0Exe.2 = ret0Cells' := by
  unfold ret0Cells'
  rw [← placeSyms_eq _ _ _ ret0Syms_perm ret0Syms_sorted]
  show (Scc.Sem.X64.threadAt _ _ _ _).exe.2 = _
  rw [Scc.Cert.Link.X64.threadAt_exe_of_above ret0_above]

/-- **The label `l` is at `a`** in the loaded thread (decided on
`ret0Cells'`). -/
def symAt (l : Label) (a : BitVec 64) : Bool :=
  match labelIdx ret0Cells' l with
  | some n => decide (BitVec.ofNat 64 ret0Λ.code.lo + BitVec.ofNat 64 ((ret0Cells'.take n).map (·.2)).sum = a)
  | none => false

theorem lab_of_symAt {l : Label} {a : BitVec 64} (h : symAt l a = true) : (labOf ret0Exe l).toBitVec = a := by
  unfold symAt at h
  split at h
  next n hn =>
    rw [← ret0Exe_cells] at hn
    rw [label_idx hn, ret0Exe_cells]
    exact of_decide_eq_true h
  · cases h

/-- The runtime's data symbols `start_seg` reads, at their addresses. -/
def rtSyms : List (Label × BitVec 64) :=
  [("scc_rt_pinned", 134217728#64), ("scc_rt_pinned_next", 6291472#64), ("scc_rt_stacks", 268435456#64),
    ("scc_rt_stack_next", 6291488#64), ("scc_rt_stack_lock", 6291496#64), ("scc_rt_stack_free_n", 6291504#64)]

theorem rtSyms_ok : rtSyms.all (fun p => symAt p.1 p.2) = true := by decide +kernel

private theorem rtSym {l : Label} {a : BitVec 64} (h : (l, a) ∈ rtSyms) : (labOf ret0Exe l).toBitVec = a :=
  lab_of_symAt (List.all_eq_true.mp rtSyms_ok _ h)

theorem ret0_pinA : pinA (labOf ret0Exe) = 134217728#64 := rtSym (by decide)
theorem ret0_pnA : pnA (labOf ret0Exe) = 6291472#64 := rtSym (by decide)
theorem ret0_stacksA : stacksA (labOf ret0Exe) = 268435456#64 := rtSym (by decide)
theorem ret0_nextA : nextA (labOf ret0Exe) = 6291488#64 := rtSym (by decide)
theorem ret0_lockA : lockA (labOf ret0Exe) = 6291496#64 := rtSym (by decide)
theorem ret0_freeNA : freeNA (labOf ret0Exe) = 6291504#64 := rtSym (by decide)

/-! ## The words and the entry frame condition -/

/-- **The runtime words `start_seg` touches** at `n0 = k0 = 0`: the
counters `scc_rt_pinned_next`, `scc_rt_stack_next`, `scc_rt_stack_lock`,
`scc_rt_stack_free_n`; the TCB's header at `scc_rt_pinned`; its six fields
from `scc_rt_pinned + 8` (the limit word `limA` the second). -/
def ret0Words : List (BitVec 64) :=
  [6291472#64, 6291488#64, 6291496#64, 6291504#64, 134217728#64,
    134217736#64, 134217744#64, 134217752#64, 134217760#64, 134217768#64, 134217776#64]

/-- **The entry frame condition**: every word of `ret0Words` unmapped in
the thread's private memory. -/
def ret0F (m : MachineData) : Prop := ∀ a ∈ ret0Words, Mem.loadInt m.dmem a 8 = none

/-- The word `a` is clear of the range `r`. -/
def clearOf (r : Scc.Sem.Range) (a : BitVec 64) : Bool :=
  decide (a.toNat + 8 ≤ r.lo) || decide (r.lo + r.size ≤ a.toNat)

theorem clearOf_iff {r : Scc.Sem.Range} {a : BitVec 64} :
    clearOf r a = true ↔ a.toNat + 8 ≤ r.lo ∨ r.lo + r.size ≤ a.toNat := by
  simp [clearOf]

theorem ret0Words_entry_ok : ret0Words.all (clearOf Scc.Sem.Entry.linux.stack) = true := by decide +kernel

theorem ret0Words_pool_ok : ret0Words.all (clearOf ret0Λ.stackPool) = true := by decide +kernel

/-- **The words are clear of the entry stack** (`Entry.linux.stack`). -/
theorem ret0Words_entry : ∀ a ∈ ret0Words,
    a.toNat + 8 ≤ Scc.Sem.Entry.linux.stack.lo ∨
      Scc.Sem.Entry.linux.stack.lo + Scc.Sem.Entry.linux.stack.size ≤ a.toNat :=
  fun a ha => clearOf_iff.mp (List.all_eq_true.mp ret0Words_entry_ok a ha)

/-- **The words are clear of the stack pool** (`ret0Λ.stackPool`). -/
theorem ret0Words_pool : ∀ a ∈ ret0Words,
    a.toNat + 8 ≤ ret0Λ.stackPool.lo ∨ ret0Λ.stackPool.lo + ret0Λ.stackPool.size ≤ a.toNat :=
  fun a ha => clearOf_iff.mp (List.all_eq_true.mp ret0Words_pool_ok a ha)

/-- The word `a` is mapped in the loaded kernel state for reading and
writing, its bytes in `data` or `pinned`. -/
def mappedB (a : BitVec 64) : Bool :=
  Scc.Sem.Kernel.mapped (K0 ret0Λ) true ⟨a, 8⟩ && Scc.Sem.Kernel.mapped (K0 ret0Λ) false ⟨a, 8⟩ &&
    (List.range 8).all fun i =>
      decide (ret0Λ.data.contains (a.toNat + i)) || decide (ret0Λ.pinned.contains (a.toNat + i))

theorem ret0Words_mappedB : ret0Words.all mappedB = true := by decide +kernel

/-- **The words are mapped** in the loaded kernel state, for reading and
writing, and shared (in `data` or `pinned`). -/
theorem ret0Words_mapped {a : BitVec 64} (ha : a ∈ ret0Words) :
    Scc.Sem.Kernel.mapped (K0 ret0Λ) true ⟨a, 8⟩ = true ∧ Scc.Sem.Kernel.mapped (K0 ret0Λ) false ⟨a, 8⟩ = true ∧
      ∀ i < 8, ret0Λ.data.contains (a.toNat + i) ∨ ret0Λ.pinned.contains (a.toNat + i) := by
  have h := List.all_eq_true.mp ret0Words_mappedB a ha
  simp only [mappedB, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-! ## The memory side -/

variable {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : Own}
  {lsize : WeakMem.AllocLabel → Nat}

/-- **`ret0`'s memory side**: no static labels. -/
abbrev msR (μ : Scc.Sem.Marks) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop) (own : Own)
    (lsize : WeakMem.AllocLabel → Nat) : MemSide isa :=
  msOf ret0Λ μ rd G own ret0Λ.static lsize

/-- Every address is the runtime's: `ret0` places no label. -/
theorem rt_static (a : Nat) : (msR μ rd G own lsize).rt a := by
  rintro ⟨l, b, h, -⟩
  exact absurd h (by rw [show ret0Λ.static l = none from rfl]; exact nofun)

theorem mp_ret0 {a : BitVec 64} (ha : a ∈ ret0Words) (w : Bool) : (msR μ rd G own lsize).mp ⟨a, 8⟩ w := by
  obtain ⟨h1, h2, h3⟩ := ret0Words_mapped ha
  refine ⟨by cases w <;> assumption, fun _ i hi => ?_⟩
  rcases h3 i (by simpa [Scc.Sem.Kernel.locBytes] using hi) with h | h
  · exact .inl h
  · exact .inr (.inr h)

/-- **A runtime store's facts** at a word of `ret0Words`, given the value
invariant there. -/
theorem stOk_ret0 {a v : BitVec 64} (ha : a ∈ ret0Words) (hG : G ⟨a, 8⟩ (v.setWidth 128)) :
    StOk (msR μ rd G own lsize) ret0F a v :=
  ⟨rt_static _, mp_ret0 ha true, hG, fun _ hm => hm a ha⟩

/-- **A runtime load's facts** at a word of `ret0Words`. -/
theorem ldOk_ret0 {a : BitVec 64} (ha : a ∈ ret0Words) : LdOk (msR μ rd G own lsize) ret0F a :=
  ⟨rt_static _, mp_ret0 ha false, fun _ hm => hm a ha⟩

/-- **A limit load's facts** at a word of `ret0Words`, given its room. -/
theorem limOk_ret0 {a Z : BitVec 64} (ha : a ∈ ret0Words)
    (hroom : ∀ v : Val, G ⟨a, 8⟩ v → (v.setWidth 64).toNat ≤ Z.toNat) : LimOk (msR μ rd G own lsize) ret0F a Z :=
  ⟨rt_static _, mp_ret0 ha false, fun _ hm => hm a ha, hroom⟩

/-! ## `start_seg`'s premises at `n0 = k0 = 0` -/

/-- The TCB's address. -/
abbrev tcb0 : BitVec 64 := pinA (labOf ret0Exe) + 0#64 + 8#64

/-- The new stack's top. -/
abbrev top0 : BitVec 64 := stacksA (labOf ret0Exe) + 0#64 + 16384#64

theorem ret0_hn : (0#64).toNat + 80 ≤ 131072 := by decide
theorem ret0_hk : (0#64).toNat + 16384 ≤ 536870912 := by decide

theorem ret0_hok : (swR top0 (-80) 0).OK := by
  rw [top0, ret0_stacksA]; exact ⟨by decide, by decide⟩

theorem ret0_hfit : (limA (tpOf tcb0)).toNat + 8 ≤ 2 ^ 64 := by
  rw [tcb0, ret0_pinA]; decide

theorem ret0_hout : ((limA (tpOf tcb0)).toNat : Int) + 8 ≤ top0.toNat + -80 ∨
    (top0.toNat : Int) + 0 ≤ (limA (tpOf tcb0)).toNat := by
  rw [tcb0, top0, ret0_pinA, ret0_stacksA]; decide

theorem ret0_hhdr (hG : G ⟨pinA (labOf ret0Exe) + 0#64, 8⟩ ((AllocTcb.hdr0 ||| 1#64 <<< 36).setWidth 128)) :
    StOk (msR μ rd G own lsize) ret0F (pinA (labOf ret0Exe) + 0#64) (AllocTcb.hdr0 ||| 1#64 <<< 36) :=
  stOk_ret0 (by rw [ret0_pinA]; decide) hG

theorem ret0_hfld
    (hG : ∀ e ∈ ThreadInit.fields tcb0 (stacksA (labOf ret0Exe) + 0#64),
      G ⟨tcb0 + BitVec.ofNat 64 e.1, 8⟩ (e.2.setWidth 128)) :
    ∀ e ∈ ThreadInit.fields tcb0 (stacksA (labOf ret0Exe) + 0#64),
      StOk (msR μ rd G own lsize) ret0F (tcb0 + BitVec.ofNat 64 e.1) e.2 := by
  intro e he
  refine stOk_ret0 ?_ (hG e he)
  have : e.1 ∈ [0, 8, 16, 24, 32, 40] := by
    simp only [ThreadInit.fields, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [tcb0, ret0_pinA]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with h | h | h | h | h | h <;> rw [h] <;> decide

theorem ret0_tcbOk
    (hG : G ⟨pnA (labOf ret0Exe), 8⟩ ((0#64 + AllocTcb.tcbLen).setWidth 128))
    (hown : OwnAt (msR μ rd G own lsize) ret0Exe ret0End (AllocTcb.rmwPc (labOf ret0Exe)) (pnA (labOf ret0Exe)) 0#64) :
    TcbOk (msR μ rd G own lsize) ret0F ret0Exe ret0End 0#64 :=
  ⟨stOk_ret0 (by rw [ret0_pnA]; decide) hG, hown⟩

theorem ret0_takeOk
    (hG1 : G ⟨lockA (labOf ret0Exe), 8⟩ ((1#64).setWidth 128))
    (hG0 : G ⟨lockA (labOf ret0Exe), 8⟩ ((0#64).setWidth 128))
    (hGn : G ⟨nextA (labOf ret0Exe), 8⟩ ((0#64 + StackTake.size0).setWidth 128))
    (hownL : OwnAt (msR μ rd G own lsize) ret0Exe ret0End (StackTake.swpPc (labOf ret0Exe)) (lockA (labOf ret0Exe))
      0#64)
    (hownF : OwnAt (msR μ rd G own lsize) ret0Exe ret0End (StackTake.freeNPc (labOf ret0Exe))
      (freeNA (labOf ret0Exe)) 0#64)
    (hownN : OwnAt (msR μ rd G own lsize) ret0Exe ret0End (StackTake.nextPc (labOf ret0Exe)) (nextA (labOf ret0Exe))
      0#64) :
    TakeOk (msR μ rd G own lsize) ret0F ret0Exe ret0End 0#64 :=
  ⟨stOk_ret0 (by rw [ret0_lockA]; decide) hG1, ldOk_ret0 (by rw [ret0_freeNA]; decide),
    stOk_ret0 (by rw [ret0_lockA]; decide) hG0, stOk_ret0 (by rw [ret0_nextA]; decide) hGn, hownL, hownF, hownN⟩

/-- **The limit word's facts** (`hlimM`, `hlimW`) for any bound `Z`,
given its room. -/
theorem ret0_limOk {Z : BitVec 64}
    (hroom : ∀ v : Val, G ⟨limA (tpOf tcb0), 8⟩ v → (v.setWidth 64).toNat ≤ Z.toNat) :
    LimOk (msR μ rd G own lsize) ret0F (limA (tpOf tcb0)) Z :=
  limOk_ret0 (by rw [tcb0, ret0_pinA]; decide) hroom

end Spike.Lib.X64.Flow.Ret0.Mem
