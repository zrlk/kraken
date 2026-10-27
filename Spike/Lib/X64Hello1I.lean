/-
**`hello1.w` on x64: the per-state facts of the main path** (`SFacts`,
`Spike/Lib/X64SegInst.lean`) at the loaded thread, the instance side of
`inst_of_segW`: the twin of `Spike/Lib/X64Ret0I.lean` and the x64 twin of
`Spike/Lib/A64Hello1I.lean`.

- **The labels** (`hello1Tab`, `labT`, `hello1_labT`): the code labels of
  the main path at their addresses in the loaded thread, a table the kernel
  reads (`labIn` decided on the cells, `label_labIn`), so a block's checks
  are decided. The runtime up to `.Lscc_rt_main.x2` is at `ret0`'s
  addresses; `scc_rt_main` is 41 bytes longer, so the runtime past it is 41
  bytes higher.
- **The phase index** (`ph`): four bits of the pc, as `ret0`'s, the runtime
  past `scc_rt_main` at its addresses here. `scc_rt_print`, `wc_rodata` and
  `wc_main` are past the take, in no counter's phase.
- **The owned words** (`own`): the four counters `scc_rt_pinned_next`,
  `scc_rt_stack_lock`, `scc_rt_stack_free_n`, `scc_rt_stack_next` with their
  values by phase; **the take's phase** (`Tk`): past the take site.
- **The marks** (`μ0`, `hello1_marks`): the transfer and abort sites, from
  the loader's parse of the text (the trust boundary `hpa`); `okPc`, a pc
  off all of them, gives `PcOff` (`pcOff_of_okPc`).
- **A block's and an instruction's states** before the take (`blkW_pre`,
  `nodeW_pre`, `nodeW_si_pre`, `nodeW_fi_pre`, `nodeW_st_pre`,
  `nodeW_xadd_pre`), as `ret0`'s at this program, and
  **`scc_rt_alloc_tcb`'s** (`tcbW`).
- **`scc_rt_main`'s source facts** (`Hello1Src`, `Hello1PostSrc`): the
  premises of `hello1_main_segW` of classes (a) and (d), stated for the
  instance to discharge; `hello1_main_segW_src` is `hello1_main_segW` from
  them.
-/
import Spike.Lib.X64Ret0I
import Spike.Lib.X64Hello1Mem
import Spike.Lib.X64Hello1Main

namespace Spike.Lib.X64.Flow.Hello1.Inst

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (pcOf)
open Spike.Lib.X64Consumer
open Spike.Lib.X64
open Spike.Lib.X64.Flow.Hello1.Mem (hello1Exe hello1End hello1_lays)
open Spike.Lib.X64.OwnLimRt (labIn label_labIn)
open Scc.Cert.Rt.X64 (labelIdx blockAtB code_field)
open SccCode (hello1Λ hello1Cells hello1Asm)
open Spike.Lib.X64.Flow.Ret0 (TakeK TakeK.pc)
open Spike.Lib.X64.Flow.Ret0.Inst (inN lookup_mem)

/-! ## The labels -/

/-- **The main path's code labels** at their addresses in the loaded
thread. -/
def hello1Tab : List (Label × Nat) :=
  [("_start", 4194304), ("scc_rt_start", 4194317), (".Lscc_rt_start.entry", 4194325), (".Lscc_rt_start.x0", 4194391),
    (".Lscc_rt_start.x1", 4194404), ("scc_rt_main", 4194444), (".Lscc_rt_main.chk", 4194448),
    (".Lscc_rt_main.entry", 4194475), (".Lscc_rt_main.x2", 4194480), (".Lscc_rt_main.x3", 4194521),
    (".Lscc_rt_main.stk", 4194542), (".Lscc_rt_main.x4", 4194560), ("scc_rt_alloc", 4194570),
    (".Lscc_rt_alloc.entry", 4194593), (".Lscc_rt_alloc.cnt", 4194611), (".Lscc_rt_alloc.slow", 4194672),
    (".Lscc_rt_alloc.spin", 4194690), (".Lscc_rt_alloc.full", 4194692), (".Lscc_rt_alloc.x5", 4194704),
    (".Lscc_rt_alloc.ok", 4194706), ("scc_rt_alloc_tcb", 4194933), (".Lscc_rt_alloc_tcb.entry", 4194952),
    (".Lscc_rt_alloc_tcb.len", 4194974), (".Lscc_rt_alloc_tcb.full", 4195174), (".Lscc_rt_alloc_tcb.x6", 4195186),
    (".Lscc_rt_alloc_tcb.ok", 4195188), ("scc_rt_thread_reserve", 4195388), (".Lscc_rt_thread_reserve.entry", 4195396),
    (".Lscc_rt_thread_reserve.full", 4195463), (".Lscc_rt_thread_reserve.x7", 4195475),
    (".Lscc_rt_thread_reserve.ok", 4195477), ("scc_rt_thread_init", 4195486), (".Lscc_rt_thread_init.entry", 4195498),
    (".Lscc_rt_thread_init.x8", 4195510), ("scc_rt_stack_take", 4195636), (".Lscc_rt_stack_take.entry", 4195651),
    (".Lscc_rt_stack_take.cls5", 4195697), (".Lscc_rt_stack_take.clsnext6", 4195712),
    (".Lscc_rt_stack_take.clsdone7", 4195801), (".Lscc_rt_stack_take.spin14", 4195866),
    (".Lscc_rt_stack_take.locked15", 4195902), (".Lscc_rt_stack_take.pop", 4195931),
    (".Lscc_rt_stack_take.bump", 4196043), (".Lscc_rt_stack_take.full", 4196153), (".Lscc_rt_stack_take.x9", 4196165),
    (".Lscc_rt_stack_take.ok", 4196167), (".Lscc_rt_stack_take.taken", 4196207), ("scc_rt_take_site", 4196218),
    ("scc_rt_stack_release", 4196231), ("scc_rt_print", 4197934), (".Lscc_rt_print.entry", 4197950),
    (".Lscc_rt_print.loop", 4197952), (".Lscc_rt_print.write", 4197974), (".Lscc_rt_print.chk2", 4198018),
    (".Lscc_rt_print.chk3", 4198036), (".Lscc_rt_print.adv", 4198054), (".Lscc_rt_print.fail", 4198089),
    (".Lscc_rt_print.x12", 4198101), (".Lscc_rt_print.done", 4198103), ("wc_rodata", 4198876),
    (".Lwc_rodata.chk", 4198880), (".Lwc_rodata.entry", 4198903), (".Lwc_rodata.x13", 4198929),
    (".Lwc_rodata.stk", 4199021), (".Lwc_rodata.x14", 4199039), ("wc_main", 4199052), (".Lwc_main.chk", 4199056),
    (".Lwc_main.entry", 4199099), (".Lwc_main.x15", 4199186), (".Lwc_main.stk", 4199198), (".Lwc_main.x16", 4199216)]

/-- Each is a label of the cells at its `labIn` address. -/
theorem hello1Tab_ok : hello1Tab.all (fun p => (labelIdx hello1Cells p.1).isSome &&
    labIn hello1Λ.code.lo hello1Cells p.1 == Int64.ofNat p.2) = true := by decide +kernel

/-- **The loaded thread's labels**, the table's first. -/
noncomputable def labT (l : Label) : Int64 :=
  match hello1Tab.lookup l with
  | some n => Int64.ofNat n
  | none => (_root_.Executable.labels hello1Exe).label l

/-- **The loaded thread's labels are `labT`'s.** -/
theorem hello1_labT : (_root_.Executable.labels hello1Exe).label = labT := by
  funext l
  unfold labT
  split
  · rename_i n hn
    have h := List.all_eq_true.mp hello1Tab_ok _ (lookup_mem hn)
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [← h.2]
    exact label_labIn hello1_lays rfl h.1
  · rfl

/-! ## The phases -/

/-- **`scc_rt_pinned_next` is still `0`**: `_start` and `scc_rt_start` up
to the call of `scc_rt_alloc_tcb`, and that function up to and including
its counter's `lock xadd`. -/
def bP (pc : Nat) : Bool := inN 4194304 4194391 pc || inN 4194933 4195137 pc

/-- **The stack lock is held**: past the `xchg` of `scc_rt_stack_take` up
to and including the store releasing it on its bump path. -/
def bL (pc : Nat) : Bool := inN 4195880 4196074 pc

/-- **`scc_rt_stack_next` is still `0`**: `scc_rt_start` up to the return
of its call of `scc_rt_thread_init`, `scc_rt_alloc_tcb`,
`scc_rt_thread_init` up to the return of its call, and `scc_rt_stack_take`
up to and including the `lock xadd`. -/
def bN (pc : Nat) : Bool :=
  inN 4194304 4194404 pc || inN 4194933 4195388 pc || inN 4195486 4195510 pc || inN 4195636 4196104 pc

/-- **The stack is not taken yet**: as `bN`, and `scc_rt_stack_take` up to
and including the take site. -/
def bT (pc : Nat) : Bool :=
  inN 4194304 4194404 pc || inN 4194933 4195388 pc || inN 4195486 4195510 pc || inN 4195636 4196219 pc

/-- **The phase index of a pc**: its four bits. -/
def ph (pc : Nat) : Nat := (bP pc).toNat + 2 * (bL pc).toNat + 4 * (bN pc).toNat + 8 * (bT pc).toNat

/-- **The owned words at a phase index**: the four counters and their
values. -/
def ownOf (i : Nat) : List (Loc × Val) :=
  [(⟨6291472#64, 8⟩, (if i % 2 = 1 then 0#64 else Ret0.AllocTcb.tcbLen).setWidth 128),
    (⟨6291496#64, 8⟩, (if i / 2 % 2 = 1 then 1#64 else 0#64).setWidth 128),
    (⟨6291504#64, 8⟩, (0#64).setWidth 128),
    (⟨6291488#64, 8⟩, (if i / 4 % 2 = 1 then 0#64 else Ret0.StackTake.size0).setWidth 128)]

/-- **The words a state owns**, by its pc's phase. -/
def own (s : State) : List (Loc × Val) := ownOf (ph (pcOf s))

/-- **The take's phase**: past the take site. -/
def Tk (s : State) : Prop := ph (pcOf s) / 8 % 2 = 0

/-- The owned words and the phase factor through `ph` of the pc. -/
theorem ph_same : ∀ s s' : State, ph (pcOf s') = ph (pcOf s) → own s' = own s ∧ (Tk s' ↔ Tk s) := by
  intro s s' h
  unfold own Tk
  rw [h]
  exact ⟨rfl, Iff.rfl⟩

/-! ## The marks -/

/-- **The loaded program's marks**: the take and release sites, the five
abort sites. -/
def μ0 : Marks where
  site
    | .take => some 4196218
    | .release => some 4196258
  abortAt
    | .overflow => some 4198596
    | .heap => some 4198664
    | .stack => some 4198732
    | .writeErr => some 4198800
    | .threads => some 4198868

/-- **The canonical target's marks of `hello1`** are `μ0`, given the
loader's parse of the text (`hpa`, the trust boundary). -/
theorem hello1_marks (hpa : Scc.Sem.X64.cellsOf hello1Asm = some hello1Cells) : T.marks hello1Asm hello1Λ = μ0 := by
  have hr := Scc.Sem.X64.resolve_of_parsed (Scc.Sem.X64.kernel 1) Scc.Sem.Entry.linux hello1Λ hpa
  unfold Scc.Sem.Target.marks
  congr 1
  · funext k; cases k <;> exact (hr _).trans (by decide +kernel)
  · funext k; cases k <;> exact (hr _).trans (by decide +kernel)

/-- **The pcs off the marks' sites.** -/
def okPc (pc : Nat) : Bool := !([4196218, 4196258, 4198596, 4198664, 4198732, 4198800, 4198868].contains pc)

/-- A pc off the sites is off `μ0`'s, with no take there. -/
theorem pcOff_of_okPc {rS : Range} : ∀ s : State, okPc (pcOf s) = true →
    PcOff μ0 s ∧ ∀ s', ¬ TakeK (labT Ret0.StackTake.siteL) rS s s' := by
  intro s h
  have hne : ∀ a ∈ [4196218, 4196258, 4198596, 4198664, 4198732, 4198800, 4198868], pcOf s ≠ a := by
    intro a ha he
    subst he
    simp only [okPc, Bool.not_eq_true', List.contains_eq_any_beq, List.any_eq_false, beq_iff_eq] at h
    exact h _ ha rfl
  refine ⟨⟨fun a ha => ?_, fun a ha => ?_, fun k a ha => ?_⟩, fun s' hk => ?_⟩
  · cases ha; exact hne _ (by simp)
  · cases ha; exact hne _ (by simp)
  · cases k <;> cases ha <;> exact hne _ (by simp)
  · have := congrArg (fun x : Int64 => x.toBitVec.toNat) (TakeK.pc hk)
    exact hne 4196218 (by simp) (by unfold pcOf; rw [this]; decide +kernel)

/-! ## A block's states -/

section Blk

open Spike.Lib.X64.Flow.Ret0
variable {rS : Range}

/-- **The per-state facts of `hello1`**: `SFacts` at the loaded program's
marks and owned words, no label placed. -/
abbrev Wr (rS : Range) : Frag isa := fun s c => SFacts hello1Λ μ0 own rS Tk hello1Λ.static s c

/-- **The outside move**: the take at the take site. -/
abbrev Kr (rS : Range) : State → State → Prop := TakeK (labT StackTake.siteL) rS

/-- A state not in the take's phase, at a pc whose phase says so. -/
theorem not_tk {s : State} (h : bT (pcOf s) = true) : ¬ Tk s := by
  unfold Tk ph
  rw [h]
  cases bP (pcOf s) <;> cases bL (pcOf s) <;> cases bN (pcOf s) <;> decide

/-- A block of the cells at its label, in the loaded thread. -/
theorem codeT {l : Label} {off : Nat} {b : List (Directive × Nat)} (hb : blockAtB hello1Cells l off b = true)
    {s : State} (hs : s.exe = hello1Exe) (hn : s.endPc = hello1End) : CodeAt s (labT l + Int64.ofNat off) b :=
  code_field hello1_lays rfl hb (by rw [hello1_labT]) s hs hn

/-- **A covered block of the main path before the take** is inside `Wr`:
its code (`hb`), its cover (`hok`), the region's facts, the source
control's facts at the node (`hC`), the phase check (`hph`) and its dead
targets never reached (`hdead`), every `ret` returning to `ra` (`hret`),
and the entry not in the take's phase (`hT`). -/
theorem blkW_pre {R : Region} {F : MachineData → Prop} {n : ND} {blk : List (Directive × Nat)} {lo hi : Int}
    {dead : Nat → Bool} {ra : Int64} {l : Label} {off : Nat}
    (hb : blockAtB hello1Cells l off blk = true) (he : labT l + Int64.ofNat off = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts hello1Λ hello1Λ.static c)
    (hph : blkPh okPc ph dead labT (labT l + Int64.ofNat off) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun labT (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun labT (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra)
    (hdead : ∀ σ c, n.J σ c → dead (arun labT blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hT : bT (labT l + Int64.ofNat off).toBitVec.toNat = true) :
    BlkW (Wr rS) (Kr rS) hello1Exe hello1End R F n blk := by
  rw [he] at hph hT
  have hcode : ∀ s : State, s.exe = hello1Exe → s.endPc = hello1End → CodeAt s n.pc blk := fun s hs hn =>
    he ▸ codeT hb hs hn
  rw [← hello1_labT] at hph hret hdead
  obtain ⟨hpc, hph', hsm⟩ := blkPh_sound (μ := μ0) (endPc := hello1End) ph_same pcOff_of_okPc hok hph hret hdead
  refine blkW_sfacts hcode hok hR hlo hhi hC hpc hph' fun s m _ _ _ k hk s' _ hpc' htk => ?_
  have := (hsm k hk { s' with st := (s'.st.1, n.pc) } s' rfl hpc').2.mp htk
  exact absurd this (not_tk (by unfold pcOf; exact hT))

end Blk

/-! ## A single instruction's states -/

section Node

open Spike.Lib.X64.Flow.Ret0
open Kraken.Promising.Lower.X64 (CellAt after exec_store_agrees exec_load_agrees exec_xaddG_agrees
  exec_xchgG_agrees eaddr exec_movfs_load_agrees fsAddr)
open Spike.Lib.X64.Flow.Hello1.Mem (hello1Words hello1F hello1Words_mapped)

variable {rS : Range} {R : Region} {F : MachineData → Prop}

/-- An instruction of the cells at its label, in the loaded thread. -/
theorem cellT {l : Label} {off z : Nat} {d : Directive} {p : Int64} (hb : blockAtB hello1Cells l off [(d, z)] = true)
    (he : labT l + Int64.ofNat off = p) {s : State} (hs : s.exe = hello1Exe) (hn : s.endPc = hello1End)
    (hpc : s.st.2 = p) : CellAt s d z :=
  (codeT hb hs hn).cell0 rfl rfl (hpc.trans he.symm)

/-- Past an instruction of `z` bytes at `p` whose next pc has its phase, a
state owns what it owns and is in the take's phase iff it is. -/
theorem next_same {s : State} {p : Int64} {z : Nat} (hpc : s.st.2 = p)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat) :
    ∀ m, own (after s z m) = own s ∧ (Tk (after s z m) ↔ Tk s) :=
  fun _ => ph_same _ _ (by
    show ph (s.st.2 + Int64.ofNat z).toBitVec.toNat = ph s.st.2.toBitVec.toNat; rw [hpc]; exact hph)

theorem own_at {s : State} {p : Int64} (hpc : s.st.2 = p) : own s = ownOf (ph p.toBitVec.toNat) := by
  unfold own pcOf; rw [hpc]

theorem ph_bT (pc : Nat) : ph pc / 8 % 2 = (bT pc).toNat := by
  unfold ph
  cases bP pc <;> cases bL pc <;> cases bN pc <;> cases bT pc <;> decide

/-- Past an instruction of `z` bytes at `p` whose next pc is in the take's
phase iff `p` is, a state is in it iff it is. -/
theorem next_tk {s : State} {p : Int64} {z : Nat} (hpc : s.st.2 = p)
    (h : bT (p + Int64.ofNat z).toBitVec.toNat = bT p.toBitVec.toNat) : ∀ m, Tk (after s z m) ↔ Tk s := by
  intro m
  show ph (s.st.2 + Int64.ofNat z).toBitVec.toNat / 8 % 2 = 0 ↔ ph s.st.2.toBitVec.toNat / 8 % 2 = 0
  rw [hpc, ph_bT, ph_bT, h]

/-- A word other than the four counters is owned at no phase. -/
theorem not_own {a : BitVec 64} (h : a ∉ [6291472#64, 6291496#64, 6291504#64, 6291488#64]) :
    ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j := by
  intro j w hm
  apply h
  simp only [ownOf, List.mem_cons, Prod.mk.injEq, Loc.mk.injEq, and_true, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

/-- **A write's update of the owned words, decided**: for each owned value
`v` of `L`, `ow'` is `ow` with `L` at `f v`, or a word of `ow` other than
`L`. -/
def ownUpdB (ow ow' : List (Loc × Val)) (L : Loc) (f : Val → Val) : Bool :=
  ow.all fun q => decide (q.1 ≠ L) || ow'.all fun r => decide ((r.1 = L ∧ r.2 = f q.2) ∨ (r.1 ≠ L ∧ r ∈ ow))

theorem ownUpd_of {ow ow' : List (Loc × Val)} {L : Loc} {f : Val → Val} (h : ownUpdB ow ow' L f = true) :
    ∀ v, (L, v) ∈ ow → Spike.Lib.Consumer1.OwnUpd ow ow' L (f v) := by
  intro v hv L' w hm
  have := List.all_eq_true.mp h _ hv
  simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_or, List.all_eq_true, decide_eq_true_eq] at this
  exact this _ hm

/-- **A node of the main path before the take**, at `p` off the sites:
its states are inside `Wr` given `SFacts` with `PcOff` and the range owned
in the take's phase (which they are not in). -/
theorem nodeW_pre {n : ND} {p : Int64} (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true)
    (h : ∀ s c σ, s.exe = hello1Exe → s.endPc = hello1End → s.decls = {} → s.st.2 = p → Abs R n.o s.st.1 σ →
      F s.st.1 → n.J σ c → PcOff μ0 s → (Tk s → Owned hello1Λ rS s) → Wr rS s c) :
    NodeW (Wr rS) (Kr rS) hello1Exe hello1End R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hP := pcOff_of_okPc (rS := rS) s (by unfold pcOf; rw [hpc]; exact hok)
  exact ⟨h s c σ hs hn hdc hpc hA hD hJ hP.1 fun h' => absurd h' (not_tk (by unfold pcOf; rw [hpc]; exact hT)), hP.2⟩

/-- **A node at a single instruction without an event** (`SI`) before the
take, its next pc in its phase. -/
theorem nodeW_si_pre {n : ND} {si : SI} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB hello1Cells l off [(si.toDir, z)] = true) (he : labT l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts hello1Λ hello1Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat) :
    NodeW (Wr rS) (Kr rS) hello1Exe hello1End R F n :=
  nodeW_pre hp hok hT fun _s c σ hs hn _ hpc _ _ hJ hP hO =>
    sfacts_si (hC σ c hJ) hP (cellT hb he hs hn hpc) (next_same hpc hph) hO

/-- **A node at an instruction with undefined flags** (`FI`) before the
take, its next pc in its phase. -/
theorem nodeW_fi_pre {n : ND} {fi : FI} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB hello1Cells l off [(fi.toDir, z)] = true) (he : labT l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts hello1Λ hello1Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat) :
    NodeW (Wr rS) (Kr rS) hello1Exe hello1End R F n :=
  nodeW_pre hp hok hT fun _s c σ hs hn _ hpc _ _ hJ hP hO =>
    sfacts_fi (hC σ c hJ) hP (cellT hb he hs hn hpc) (next_same hpc hph) hO

/-- **A node at a runtime store** `movq %r, k(%b)` to a word `a` of
`hello1Words` no phase owns, before the take, its next pc in its phase. -/
theorem nodeW_st_pre {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    {a : BitVec 64} (hb : blockAtB hello1Cells l off [(stDir b k r, z)] = true) (he : labT l + Int64.ofNat off = p)
    (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts hello1Λ hello1Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (ha : ∀ σ c, n.J σ c → bAddr σ.regs b k = a) (hw : a ∈ hello1Words) (hFr : ∀ m, F m → hello1F m)
    (hno : ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j) :
    NodeW (Wr rS) (Kr rS) hello1Exe hello1End R F n :=
  nodeW_pre hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellT hb he hs hn hpc
    have ha' : eaddr s z (mB b k) = a := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha σ c hJ)
    have hex := exec_store_agrees hc ha' (hFr _ hD a hw) (agrees_of_decls hdc _ _)
    obtain ⟨hT', hown, htk⟩ := store_facts (Λ := hello1Λ) (own := own) (Tk := Tk) (k := .plain) (s := s)
      (m := s.st.1) (V := (s.st.1.regs.get (.low r .W64)).setWidth 128) (hello1Words_mapped hw).1
      (next_same hpc hph _).2 (.inl ⟨(next_same hpc hph _).1, fun w h => by rw [own_at hpc] at h; exact hno _ w h⟩)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hT' hown htk hO

/-- **A node at an owned counter's `lock xaddq %r, k(%b)`** before the
take, its next pc before it too: the counter's word `a` (`ha`), owned at
`p` (`hin`), updated to the sum at the next pc (`hupd`). -/
theorem nodeW_xadd_pre {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    {a : BitVec 64} (hb : blockAtB hello1Cells l off [(xaddDir b k r, z)] = true)
    (he : labT l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts hello1Λ hello1Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hT' : bT (p + Int64.ofNat z).toBitVec.toNat = true)
    (ha : ∀ σ c, n.J σ c → bAddr σ.regs b k = a) (hw : a ∈ hello1Words) (hFr : ∀ m, F m → hello1F m)
    (hin : ∃ v, (⟨a, 8⟩, v) ∈ ownOf (ph p.toBitVec.toNat))
    (hupd : ∀ σ c, n.J σ c → ownUpdB (ownOf (ph p.toBitVec.toNat)) (ownOf (ph (p + Int64.ofNat z).toBitVec.toNat))
      ⟨a, 8⟩ (fun old => (old.setWidth 64 + σ.regs.get64 r).setWidth 128) = true) :
    NodeW (Wr rS) (Kr rS) hello1Exe hello1End R F n :=
  nodeW_pre hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellT hb he hs hn hpc
    have ha' : eaddr s z (mB b k) = a := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha σ c hJ)
    have hex := exec_xaddG_agrees (w := .W64) hc ha' (hFr _ hD a hw) (agrees_of_decls hdc _ _)
    have hpc4 : ∀ m, (after s z m).st.2 = p + Int64.ofNat z := fun _ => by rw [← hpc]
    obtain ⟨hT'', hown, htk⟩ := rmw_facts (Λ := hello1Λ) (own := own) (Tk := Tk) (s := s) (k := .acqRel)
      (nr := false) (z := z)
      (op := fun old => some ((old.setWidth 64 + s.st.1.regs.get (.low r .W64)).setWidth 128))
      (m := fun v => { s.st.1 with
        regs := s.st.1.regs.set (.low r .W64) (v.setWidth 64)
        status := LockBinOp.add.status (v.setWidth 64) (s.st.1.regs.get (.low r .W64))
          (v.setWidth 64 + s.st.1.regs.get (.low r .W64)) false })
      (hello1Words_mapped hw).1 (fun _ => next_tk hpc (by rw [hT, hT']) _) (by rw [own_at hpc]; exact hin)
      (fun v hv => by
        rw [own_at hpc, own_at (hpc4 _), Option.getD_some, Reg64s.get_low64, hA.regs]
        rw [own_at hpc] at hv
        exact ownUpd_of (hupd σ c hJ) v hv)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hT'' hown htk hO

end Node

/-! ## `scc_rt_alloc_tcb` -/

section Tcb

open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Hello1.Mem (hello1F)

variable {rS : Range} {c0 : Ctl} {F : MachineData → Prop}

theorem labT_pnA : pnA labT = 6291472#64 := by rw [← hello1_labT]; exact Hello1.Mem.hello1_pnA
theorem labT_pinA : pinA labT = 134217728#64 := by rw [← hello1_labT]; exact Hello1.Mem.hello1_pinA
theorem labT_lockA : lockA labT = 6291496#64 := by rw [← hello1_labT]; exact Hello1.Mem.hello1_lockA
theorem labT_freeNA : freeNA labT = 6291504#64 := by rw [← hello1_labT]; exact Hello1.Mem.hello1_freeNA
theorem labT_nextA : nextA labT = 6291488#64 := by rw [← hello1_labT]; exact Hello1.Mem.hello1_nextA

set_option hygiene false in
/-- A block of `scc_rt_alloc_tcb` before the take, no `ret`, no dead target. -/
local macro "tblk " l:term:max k:term:max ok:term:max : tactic =>
  `(tactic| exact blkW_pre (l := $l) (off := $k) (dead := fun _ => false) (ra := 0) (by decide +kernel)
    (by first | rfl | exact ofNat_zero' _) $ok hR (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0)
    (by decide +kernel) (fun _ _ _ k hk hr => (noRet_false (by decide +kernel) k hk hr).elim)
    (fun _ _ _ => rfl) (by decide +kernel))

set_option hygiene false in
/-- A `leaq L(%rip)` of `scc_rt_alloc_tcb`. -/
local macro "tsi " si:term:max z:term:max l:term:max k:term:max : tactic =>
  `(tactic| exact nodeW_si_pre (si := $si) (z := $z) (l := $l) (off := $k) (p := labT $l + Int64.ofNat $k)
    (by decide +kernel) rfl (by first | rfl | exact (ofNat_zero' _).symm)
    (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option hygiene false in
/-- An instruction with undefined flags of `scc_rt_alloc_tcb`. -/
local macro "tfi " fi:term:max z:term:max l:term:max k:term:max : tactic =>
  `(tactic| exact nodeW_fi_pre (fi := $fi) (z := $z) (l := $l) (off := $k) (p := labT $l + Int64.ofNat $k)
    (by decide +kernel) rfl rfl
    (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel) (by decide +kernel) (by decide +kernel))

/-- **`scc_rt_alloc_tcb`'s states are inside `Wr`**, in any region holding
its frame, at `n0 = 0`, returning to `.x0`, with the source control `c0`
(`hC0`, its facts) and the frame condition implying `hello1F`. -/
theorem tcbW (hC0 : CFacts hello1Λ hello1Λ.static c0) {R : Region} (hR : R.OK) (hlo : R.lo ≤ -184) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → hello1F m) (q : TcbG) (hq : q.c0 = c0) (hn0 : q.n0 = 0#64)
    (hra : q.g.ra = (labT ".Lscc_rt_start.x0").toBitVec) :
    ∀ i, TcbW (Wr rS) (Kr rS) hello1Exe hello1End R F q i := by
  intro i
  cases i
  case e => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.fnL 0 AllocTcb.atPro_ok
  case entry =>
    show BlkW _ _ _ _ _ _ _ _
    rw [hello1_labT]
    exact blkW_pre (l := AllocTcb.entryL) (off := 0) (dead := fun t => t == 4195174) (ra := 0)
      (by decide +kernel) (ofNat_zero' _) AllocTcb.atChk_ok hR (by omega) (by omega)
      (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk hr => (noRet_false (by decide +kernel) k hk hr).elim)
      (fun _ _ hJ => by dsimp only [tcbN] at hJ ⊢; rw [(AllocTcb.atChk_walk labT _ hJ.2).1]; decide +kernel)
      (by decide +kernel)
  case j1 => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.entryL 20 AllocTcb.atJ1_ok
  case len => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.lenL 0 AllocTcb.atL0_ok
  case shr1 => show NodeW _ _ _ _ _ _ _; rw [hello1_labT]; tfi (.shr_cl .rax) 3 AllocTcb.lenL 11
  case l1 => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.lenL 14 AllocTcb.atL1_ok
  case and1 => show NodeW _ _ _ _ _ _ _; rw [hello1_labT]; tfi (.and_rr .rax .rcx) 3 AllocTcb.lenL 29
  case l2 => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.lenL 32 AllocTcb.atL2_ok
  case shr2 => show NodeW _ _ _ _ _ _ _; rw [hello1_labT]; tfi (.shr_cl .rax) 3 AllocTcb.lenL 47
  case l3 => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.lenL 50 AllocTcb.atL3_ok
  case and2 => show NodeW _ _ _ _ _ _ _; rw [hello1_labT]; tfi (.and_rr .rax .rcx) 3 AllocTcb.lenL 65
  case l4 => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.lenL 68 AllocTcb.atL4_ok
  case imul1 => show NodeW _ _ _ _ _ _ _; rw [hello1_labT]; tfi (.imul_rr .rax .rcx) 4 AllocTcb.lenL 95
  case l5 => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.lenL 99 AllocTcb.atL5_ok
  case shl1 => show NodeW _ _ _ _ _ _ _; rw [hello1_labT]; tfi (.shl_cl .rax) 3 AllocTcb.lenL 132
  case l6 => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.lenL 135 AllocTcb.atL6_ok
  case lea1 =>
    show NodeW _ _ _ _ _ _ _; rw [hello1_labT]; tsi (.leaRip .rax "scc_rt_pinned_next") 7 AllocTcb.lenL 139
  case arg => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.lenL 146 AllocTcb.atArg_ok
  case rmw =>
    show NodeW _ _ _ _ _ _ _
    rw [hello1_labT]
    refine nodeW_xadd_pre (b := .rcx) (k := 0) (r := .rax) (z := 5) (l := AllocTcb.lenL) (off := 158)
      (a := 6291472#64) (by decide +kernel) rfl rfl (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (fun σ _ hJ => ?_) (by decide) hFr ⟨_, .head _⟩ fun σ _ hJ => ?_
    · obtain ⟨-, -, -, hc⟩ := hJ
      rw [← labT_pnA, ← hc]
      simp [bAddr, Reg64s.get64]
    · obtain ⟨-, -, ha, -⟩ := hJ
      have h : σ.regs.get64 .rax = AllocTcb.tcbLen := by rw [← ha]; rfl
      rw [h]
      decide +kernel
  case bnd => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.lenL 163 AllocTcb.atBnd_ok
  case j2 => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.lenL 198 AllocTcb.atJ2_ok
  case ok => show NodeW _ _ _ _ _ _ _; rw [hello1_labT]; tsi (.leaRip .rax "scc_rt_pinned") 7 AllocTcb.okL 0
  case o1 => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.okL 7 AllocTcb.atO1_ok
  case imul2 => show NodeW _ _ _ _ _ _ _; rw [hello1_labT]; tfi (.imul_rr .rax .rcx) 4 AllocTcb.okL 34
  case o2 => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.okL 38 AllocTcb.atO2_ok
  case shl2 => show NodeW _ _ _ _ _ _ _; rw [hello1_labT]; tfi (.shl_cl .rax) 3 AllocTcb.okL 53
  case o3 => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.okL 56 AllocTcb.atO3_ok
  case shl3 => show NodeW _ _ _ _ _ _ _; rw [hello1_labT]; tfi (.shl_cl .rax) 3 AllocTcb.okL 74
  case o4 => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.okL 77 AllocTcb.atO4_ok
  case or1 => show NodeW _ _ _ _ _ _ _; rw [hello1_labT]; tfi (.or_rr .rax .rcx) 3 AllocTcb.okL 95
  case o5 => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.okL 98 AllocTcb.atO5_ok
  case hdr =>
    show NodeW _ _ _ _ _ _ _
    rw [hello1_labT]
    refine nodeW_st_pre (b := .rcx) (k := 0) (r := .rax) (z := 3) (l := AllocTcb.okL) (off := 140)
      (a := 134217728#64) (by decide +kernel) rfl rfl (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (fun σ _ hJ => ?_) (by decide) hFr (not_own (by decide))
    obtain ⟨-, -, -, hc⟩ := hJ
    rw [hn0, labT_pinA] at hc
    have h : σ.regs.rcx.toBitVec = 134217728#64 := by rw [hc]; rfl
    simp [bAddr, Reg64s.get64, h]
  case ret =>
    show BlkW _ _ _ _ _ _ _ _
    rw [hello1_labT]
    exact blkW_pre (l := AllocTcb.okL) (off := 143) (dead := fun _ => false) (ra := labT ".Lscc_rt_start.x0")
      (by decide +kernel) rfl AllocTcb.atRet_ok hR (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0)
      (by decide +kernel)
      (hret_of_run AllocTcb.atRet_ok fun _ _ hJ => by
        dsimp only [tcbN] at hJ ⊢
        rw [(AllocTcb.atRet_walk labT _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ _ _ => rfl) (by decide +kernel)

end Tcb

/-! ## `scc_rt_main`'s source facts -/

section Src

open Spike.Lib Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Hello1
open Kraken.X64.Parser Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib.X64.Flow.Ret0 (CallerCells LimOk)
open Spike.Lib.X64.Alloc (Call Ea)
open Scc.Cert.Rt.X64 (Lays endOf)

/-- **`hello1_main_post_segW`'s source and frame facts** for a caller's
state `m0`, `σC` at `wc_rodata`'s call: `MainPostP` but its states inside
`W` (`hW`, the instance's node obligations).
VACUOUS at .x13 at `rodata`'s source: see X64Hello1RodataSetupG (`hand_x13_empty`). -/
structure Hello1PostSrc (W : Frag isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : MemSide isa) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (m0 : MachineData) (σC : AS) (Jp J1 J2 J3 J4 Jr Jw : AS → Ctl → Prop) : Prop where
  hbp : ∀ σ0 c, Jp σ0 c → σ0.regs.get64 .rbp = (mR R).addr (-8)
  hra : ∀ σ0 c, Jp σ0 c → (_root_.Executable.labels exe).label ".Lscc_rt_main.x2" = Int64.ofBitVec (σ0.slot 0)
  hmem : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
      ∀ m, mF R F m0 σC m → Mem.loadInt m.dmem (bAddr σ0.regs .rax i) 8 = none
  h1 : ∀ σ0 c, Jp σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 0).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J1 σ0 { c with hold := some ((bAddr σ0.regs .rax 0).toNat, w') }
  h2 : ∀ σ0 c, J1 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 0).toNat ∧
      c.hold = some ((bAddr σ0.regs .rax 0).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK1.setWidth 128).toNat ∧ J2 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩
  h3 : ∀ σ0 c, J2 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 8).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J3 σ0 { c with hold := some ((bAddr σ0.regs .rax 8).toNat, w') }
  h4 : ∀ σ0 c, J3 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 8).toNat ∧
      c.hold = some ((bAddr σ0.regs .rax 8).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK2.setWidth 128).toNat ∧ J4 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩
  hedge : ∀ σ0 c, J4 σ0 c → ∀ σ' : AS, σ'.regs.rax.toBitVec = σ0.regs.rax.toBitVec →
      σ'.regs.rdx.toBitVec = 0#64 → σ'.regs.rcx.toBitVec = 2#64 → σ'.regs.rsi.toBitVec = 13#64 →
      σ'.regs.rbp.toBitVec = σ0.slot (-8) → σ'.regs.rsp.toBitVec = σ0.regs.rbp.toBitVec + 8#64 + 8#64 →
      ∃ c', LocalRun p c c' ∧ Jr σ' c'
  hbpr : ∀ σx c, Jr σx c → σx.regs.get64 .rbp = R.addr (-8)
  hlimW : ∀ σx c, Jr σx c → LimOk ms F (σx.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σx.regs.rsp.toBitVec - 8#64 - 8#64 - (80 : Int64).toBitVec)
  hsvc : ∀ F' : MachineData → Prop, FStable (pR (wR R)) F' →
      (∀ m, F' m → ((F m ∧ CallerCells R (-80) (-144) 8 m) ∧ CallerCells (wR R) (-96 - 8) (-40) 16 m) ∧
        Spike.Lib.X64.Rt.WcRa (wR R) ((_root_.Executable.labels exe).label ".Lscc_rt_main.x3") m ∧
        Spike.Lib.X64.Rt.WcFp (wR R) (R.addr (-8)) m) →
      ∀ g' : PG, g'.2.2 = ((_root_.Executable.labels exe).label ".Lwc_main.x15").toBitVec →
      g'.2.1 = (wR R).addr (-8) →
      SegW W K p lbl ms
        (At exe endPc (pR (wR R)) F' (Print.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .sys))
        (At exe endPc (pR (wR R)) F' (Print.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .n5))
  hedgeW : ∀ g : AS × Ctl, ∀ σ c, wcJ (wJ0 (_root_.Executable.labels exe).label σC Jr g) σ c →
      σ.regs.get64 .rbp = (wR R).addr (-8) → ∀ σ' : AS,
      (∀ k, -88 ≤ k → k < 8 → k % 8 = 0 → σ'.slot k = wcSl (_root_.Executable.labels exe).label σ k) →
      σ'.regs.rax.toBitVec = 0#64 → σ'.regs.rbp.toBitVec = σ.slot (-8) →
      σ'.regs.rsp.toBitVec = σ.regs.rbp.toBitVec + 8#64 + 8#64 →
      ∃ c', LocalRun p c c' ∧ Jw σ' c'
  hbpw : ∀ σx c, Jw σx c → σx.regs.get64 .rbp = R.addr (-8)
  hok : ∀ s c σx, Jw σx c →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label ".Lscc_rt_main.x3" + Int64.ofNat 4 + Int64.ofNat 4 +
        Int64.ofNat 5, mO, fun _ _ => True⟩ s c → SysOk p ms s c (.exitGroup σx.regs.rax.toNat)

/-- **`hello1_main_segW`'s source and frame facts**, the instance's to
discharge: the premises of classes (a) (from the source program: the
allocator's call `hq`, the bridge `hret`, and per caller's state the
exchanges `h1`–`h4`, the local runs `hedge`, `hedgeW`, the exit `hok`, the
saved return `hra` and the saved `%rbp`s `hbp`, `hbpr`, `hbpw`) and (d)
(the limit loads' room `hlimM`, `hlimR`, `hlimW`, the fresh cells unmapped
`hmem`, the allocation's continuation `hpost` through `hJp`, and `print`'s
system call `hsvc`), at the main path's invariants `J` and, indexed by the
caller's state, `Jp`, `J1`–`J4`, `Jr`, `Jw`. The layout's premises (class
(b)) and the states inside `W` stay `hello1_main_segW_src`'s. -/
structure Hello1Src (W : Frag isa) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide isa) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (J : AS → Ctl → Prop)
    (Jp J1 J2 J3 J4 Jr Jw : MachineData → AS → AS → Ctl → Prop) : Prop where
  hlimM : ∀ σ c, J σ c → LimOk ms F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - (64 : Int64).toBitVec)
  hlimR : ∀ σ c, J σ c → LimOk ms F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - 64#64 - 8#64 - 8#64 - (32 : Int64).toBitVec)
  hq : ∀ σ c, J σ c → ∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ms = 3#64
  hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none
  hJp : ∀ m0 σC (q : AG ms (_root_.Executable.labels exe).label) l b w σx σ c0 c, (Ea ms q.1 l b w).J σx c →
      (rN (_root_.Executable.labels exe).label (mR R)
        (mRdJ0 (mNC (_root_.Executable.labels exe).label R J).J σC) .call).J σ c0 →
      (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c0 →
      Jp m0 σC (leave (aR (mR R)) (-48) σ σx) c
  hpost : ∀ l b w s c, lbl l = none → (∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
      (rdX13 (_root_.Executable.labels exe).label (Jp m0 σC)) s c) → ms.xa l b w s c
  hret : ∀ m0 σC σ c,
      (rX ms (_root_.Executable.labels exe).label lbl (mR R)
        (mRdJ0 (mNC (_root_.Executable.labels exe).label R J).J σC) .x13).J σ c →
      Jp m0 σC σ c
  post : ∀ m0 σC, Hello1PostSrc W K p lbl ms exe endPc R F m0 σC (Jp m0 σC) (J1 m0 σC) (J2 m0 σC) (J3 m0 σC)
    (J4 m0 σC) (Jr m0 σC) (Jw m0 σC)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`hello1_main_segW` from the source facts**: the layout's premises,
the states inside `W` before (`hW`) and after (`hWp`) `wc_rodata`'s
allocation, and `Hello1Src`.
VACUOUS at .x13 at `rodata`'s source: see X64Hello1RodataSetupG (`hand_x13_empty`). -/
theorem hello1_main_segW_src {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi)
    {J : AS → Ctl → Prop} {Jp J1 J2 J3 J4 Jr Jw : MachineData → AS → AS → Ctl → Prop}
    (hW : MainPreW W K exe endPc R F ms J)
    (hWp : ∀ m0 σC, MainPostW W K exe endPc R F ms m0 σC (Jp m0 σC) (J1 m0 σC) (J2 m0 σC) (J3 m0 σC) (J4 m0 σC)
      (Jr m0 σC) (Jw m0 σC))
    (hS : Hello1Src W K p lbl ms exe endPc R F J Jp J1 J2 J3 J4 Jr Jw) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_main", ⟨0, []⟩, J⟩)
      (fun s c => At exe endPc R F (mAb (_root_.Executable.labels exe).label) s c ∨
        ∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
          (rX ms (_root_.Executable.labels exe).label lbl (mR R)
            (mRdJ0 (mNC (_root_.Executable.labels exe).label R J).J σC) .abort) s c) ∧
    SegW W K p lbl ms
      (fun s c => ∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
        (rdX13 (_root_.Executable.labels exe).label (Jp m0 σC)) s c)
      (At exe endPc R F (mAb (_root_.Executable.labels exe).label)) :=
  hello1_main_segW hp hend hF hR hlo hhi hK hW hS.hlimM hS.hlimR hS.hq hS.hmem hS.hJp hS.hpost hS.hret
    fun m0 σC => let h := hS.post m0 σC
      ⟨hWp m0 σC, h.hbp, h.hra, h.hmem, h.h1, h.h2, h.h3, h.h4, h.hedge, h.hbpr, h.hlimW, h.hsvc, h.hedgeW, h.hbpw,
        h.hok⟩

end Src

end Spike.Lib.X64.Flow.Hello1.Inst
