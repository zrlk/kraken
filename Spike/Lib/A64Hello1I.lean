/-
**`hello1.w` on AArch64: the per-state facts of the main path** (`SFacts`,
`Spike/Lib/A64SegInst.lean`) at the loaded thread, the instance side of
`inst_of_segW`, the twin of `Spike/Lib/A64Ret0I.lean`.

- **The labels** (`hello1Tab`, `labT`, `hello1_labT`): the code labels of
  the main path at their addresses in the loaded thread, a table the kernel
  reads (`labIn` decided on the program, `label_labIn`), so a block's checks
  are decided. The runtime up to `.L1_scc_rt_main.sp0` is at `ret0`'s
  addresses; `scc_rt_main` is ten instructions longer, so the runtime past
  it is 40 bytes higher.
- **The phase index** (`ph`): four bits of the pc, as `ret0`'s, the runtime
  past `scc_rt_main` at its addresses here. `scc_rt_print`, `wc_rodata` and
  `wc_main` are past the take, in no counter's phase.
- **The owned words** (`own`): the four counters `scc_rt_pinned_next`,
  `scc_rt_stack_lock`, `scc_rt_stack_free_n`, `scc_rt_stack_next` with their
  values by phase; **the take's phase** (`Tk`): past the take site.
- **The marks** (`μ0`, `hello1_marks`): the transfer and abort sites, from
  the loader's parse of the listing (the trust boundary `hpa`); `okPc`, a pc
  off all of them, gives `PcOff` (`pcOff_of_okPc`).
- **A block's and a node's states** before the take (`blkW_pre`,
  `nodeW_pre`, `nodeW_si_pre`, `nodeW_st_pre`, `nodeW_ldop_pre`), as
  `ret0`'s at this program, and **`scc_rt_alloc_tcb`'s** (`tcbW`).
- **`scc_rt_main`'s source facts** (`Hello1Src`, `Hello1PostSrc`): the
  premises of `hello1_main_segW` of classes (a) and (d), stated for the
  instance to discharge; `hello1_main_segW_src` is `hello1_main_segW` from
  them.
-/
import Spike.Lib.A64Ret0I
import Spike.Lib.A64Hello1Mem
import Spike.Lib.A64Hello1Main

namespace Spike.Lib.A64.Flow.Hello1.Inst

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow.Hello1.Mem (hello1Exe hello1End hello1_lays)
open Spike.Lib.A64.OwnLimRt (labIn labOk label_labIn)
open Spike.Lib.A64.Flow.Ret0.Inst (inN lookup_mem labsAt edgesAt)
open Spike.Lib.A64.Flow.Ret0 (TakeK)
open SccCode (hello1Λ hello1Prog hello1Asm)

/-! ## The labels -/

/-- **The main path's code labels** at their addresses in the loaded
thread: the runtime up to `scc_rt_stack_release`, `scc_rt_print`,
`wc_rodata` and `wc_main`. -/
def hello1Tab : List (Label × Nat) :=
  [("_start", 4194304), ("scc_rt_start", 4194308), (".L0_scc_rt_start.0_entry", 4194324),
    (".L0_scc_rt_start.sp2", 4194376), (".L0_scc_rt_start.sp3", 4194388), (".L0_scc_rt_start.halt4", 4194420),
    ("scc_rt_main", 4194424), (".L1_scc_rt_main.stack_check", 4194424), (".L1_scc_rt_main.0_entry", 4194464),
    (".L1_scc_rt_main.sp0", 4194468), (".L1_scc_rt_main.sp1", 4194508), (".L1_scc_rt_main.halt3", 4194528),
    (".L1_scc_rt_main.stack_grow", 4194532), (".L1_scc_rt_main.sp_check", 4194588), ("scc_rt_alloc", 4194636),
    (".L2_scc_rt_alloc.0_entry", 4194664), (".L2_scc_rt_alloc.1_cnt", 4194684), (".L2_scc_rt_alloc.2_slow", 4194748),
    (".L2_scc_rt_alloc.3_spin", 4194768), (".L2_scc_rt_alloc.4_full", 4194772), (".L2_scc_rt_alloc.sp7", 4194780),
    (".L2_scc_rt_alloc.halt8", 4194780), (".L2_scc_rt_alloc.5_ok", 4194784), ("scc_rt_alloc_tcb", 4195004),
    (".L3_scc_rt_alloc_tcb.0_entry", 4195028), (".L3_scc_rt_alloc_tcb.1_len", 4195048),
    (".L3_scc_rt_alloc_tcb.2_full", 4195240), (".L3_scc_rt_alloc_tcb.sp13", 4195248),
    (".L3_scc_rt_alloc_tcb.halt14", 4195248), (".L3_scc_rt_alloc_tcb.3_ok", 4195252),
    ("scc_rt_thread_reserve", 4195424), (".L4_scc_rt_thread_reserve.0_entry", 4195440),
    (".L4_scc_rt_thread_reserve.1_full", 4195504), (".L4_scc_rt_thread_reserve.sp4", 4195512),
    (".L4_scc_rt_thread_reserve.halt5", 4195512), (".L4_scc_rt_thread_reserve.2_ok", 4195516),
    ("scc_rt_thread_init", 4195536), (".L5_scc_rt_thread_init.0_entry", 4195556),
    (".L5_scc_rt_thread_init.sp0", 4195564), ("scc_rt_stack_take", 4195692),
    (".L6_scc_rt_stack_take.0_entry", 4195712), (".L6_scc_rt_stack_take.1_cls5", 4195748),
    (".L6_scc_rt_stack_take.2_clsnext6", 4195768), (".L6_scc_rt_stack_take.3_clsdone7", 4195852),
    (".L6_scc_rt_stack_take.4_spin14", 4195924), (".L6_scc_rt_stack_take.5_locked15", 4195960),
    (".L6_scc_rt_stack_take.6_pop", 4195992), (".L6_scc_rt_stack_take.7_bump", 4196092),
    (".L6_scc_rt_stack_take.8_full", 4196180), (".L6_scc_rt_stack_take.sp36", 4196188),
    (".L6_scc_rt_stack_take.halt37", 4196188), (".L6_scc_rt_stack_take.9_ok", 4196192),
    (".L6_scc_rt_stack_take.10_taken", 4196224), ("scc_rt_take_site", 4196232), ("scc_rt_stack_release", 4196256),
    ("scc_rt_print", 4197752), (".L9_scc_rt_print.0_entry", 4197776), (".L9_scc_rt_print.1_loop", 4197780),
    (".L9_scc_rt_print.2_write", 4197800), (".L9_scc_rt_print.3_chk2", 4197856), (".L9_scc_rt_print.4_chk3", 4197888),
    (".L9_scc_rt_print.5_adv", 4197908), (".L9_scc_rt_print.6_fail", 4197944), (".L9_scc_rt_print.sp9", 4197952),
    (".L9_scc_rt_print.halt10", 4197952), (".L9_scc_rt_print.7_done", 4197956), ("wc_rodata", 4198848),
    (".L18_wc_rodata.stack_check", 4198848), (".L18_wc_rodata.0_entry", 4198884), (".L18_wc_rodata.sp0", 4198900),
    (".L18_wc_rodata.stack_grow", 4199004), (".L18_wc_rodata.sp_check", 4199060), ("wc_main", 4199108),
    (".L19_wc_main.stack_check", 4199108), (".L19_wc_main.0_entry", 4199164), (".L19_wc_main.sp4", 4199248),
    (".L19_wc_main.stack_grow", 4199268), (".L19_wc_main.sp_check", 4199324)]

/-- Each is a label of the program at its `labIn` address. -/
theorem hello1Tab_ok :
    hello1Tab.all (fun p => labOk hello1Prog p.1 && labIn hello1Λ.code.lo hello1Prog p.1 == Int64.ofNat p.2)
    = true := by decide +kernel

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
its counter's add. -/
def bP (pc : Nat) : Bool := inN 4194304 4194376 pc || inN 4195004 4195200 pc

/-- **The stack lock is held**: past the `swpal` of `scc_rt_stack_take` up
to and including the `stlr` of its bump path. -/
def bL (pc : Nat) : Bool := inN 4195936 4196116 pc

/-- **`scc_rt_stack_next` is still `0`**: up to `.sp3` of `scc_rt_start`,
`scc_rt_alloc_tcb` (and `scc_rt_thread_reserve`), `scc_rt_thread_init` up
to the return of its call, and `scc_rt_stack_take` up to and including the
add. -/
def bN (pc : Nat) : Bool :=
  inN 4194304 4194388 pc || inN 4195004 4195424 pc || inN 4195536 4195564 pc || inN 4195692 4196140 pc

/-- **The stack is not taken yet**: as `bN`, and `scc_rt_stack_take` up to
and including the take site. -/
def bT (pc : Nat) : Bool :=
  inN 4194304 4194388 pc || inN 4195004 4195424 pc || inN 4195536 4195564 pc || inN 4195692 4196236 pc

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

/-! ## The phase's crossings

As `ret0`'s (`Ret0.Inst.tkCross`): the program's control edges whose ends
differ in `bT`, decided. The same four, at this program's addresses: the
two calls of `scc_rt_abort` off the `.2_full` and `.8_full` paths (dead on
the main path), the take site's fall-through (the take itself), and
`scc_rt_grow`'s call of `scc_rt_stack_take` (dead on the main path). -/

/-- **The edges crossing the take's phase** in the loaded program. -/
def tkCross : List (Nat × Nat) :=
  (edgesAt (labsAt 4194304 hello1Prog) 4194304 hello1Prog).filter fun e => bT e.1 != bT e.2

/-- **The only crossings.** -/
theorem tkCross_eq :
    tkCross = [(4195244, 4198284), (4196184, 4198284), (4196232, 4196236), (4196880, 4195692)] := by
  decide +kernel

/-- The take site's fall-through owns what the site owns. -/
theorem ownOf_site : ownOf (ph 4196236) = ownOf (ph 4196232) := by decide

/-! ## The marks -/

/-- **The loaded program's marks**: the take and release sites, the five
abort sites. -/
def μ0 : Marks where
  site
    | .take => some 4196232
    | .release => some 4196288
  abortAt
    | .overflow => some 4198548
    | .heap => some 4198620
    | .stack => some 4198692
    | .writeErr => some 4198764
    | .threads => some 4198836

/-- **The canonical target's marks of `hello1`** are `μ0`, given the
loader's parse of the listing (`hpa`, the trust boundary). -/
theorem hello1_marks (hpa : Scc.Sem.A64.textProgram hello1Asm = .ok hello1Prog) :
    T.marks hello1Asm hello1Λ = μ0 := by
  have hr := Scc.Sem.A64.resolve_of_parsed (Scc.Sem.A64.kernel 1) Scc.Sem.Entry.linux hello1Λ hpa
  unfold Scc.Sem.Target.marks
  congr 1
  · funext k; cases k <;> exact (hr _).trans (by decide +kernel)
  · funext k; cases k <;> exact (hr _).trans (by decide +kernel)

/-- **The pcs off the marks' sites.** -/
def okPc (pc : Nat) : Bool := !([4196232, 4196288, 4198548, 4198620, 4198692, 4198764, 4198836].contains pc)

/-- A pc off the sites is off `μ0`'s, with no take there. -/
theorem pcOff_of_okPc {rS : Range} : ∀ s : State, okPc (pcOf s) = true →
    PcOff μ0 s ∧ ∀ s', ¬ TakeK (labT Ret0.StackTake.siteL) rS s s' := by
  intro s h
  have hne : ∀ a ∈ [4196232, 4196288, 4198548, 4198620, 4198692, 4198764, 4198836], pcOf s ≠ a := by
    intro a ha he
    subst he
    simp only [okPc, Bool.not_eq_true', List.contains_eq_any_beq, List.any_eq_false, beq_iff_eq] at h
    exact h _ ha rfl
  refine ⟨⟨fun a ha => ?_, fun a ha => ?_, fun k a ha => ?_⟩, fun s' hk => ?_⟩
  · cases ha; exact hne _ (by simp)
  · cases ha; exact hne _ (by simp)
  · cases k <;> cases ha <;> exact hne _ (by simp)
  · have := congrArg (fun x : Int64 => x.toBitVec.toNat) (TakeK.pc hk)
    exact hne 4196232 (by simp) (by unfold pcOf; rw [this]; decide +kernel)

/-! ## The per-state facts -/

/-- **The per-state facts of `hello1`**: `SFacts` at the loaded program's
marks and owned words, no label placed. -/
abbrev Wr (rS : Range) : Frag isaLSE2 := fun s c => SFacts hello1Λ μ0 own rS Tk hello1Λ.static s c

/-- **The outside move**: the take at the take site. -/
abbrev Kr (rS : Range) : State → State → Prop := TakeK (labT Ret0.StackTake.siteL) rS

/-- A state not in the take's phase, at a pc whose phase says so. -/
theorem not_tk {s : State} (h : bT (pcOf s) = true) : ¬ Tk s := by
  unfold Tk ph
  rw [h]
  cases bP (pcOf s) <;> cases bL (pcOf s) <;> cases bN (pcOf s) <;> decide

/-- **The loaded thread is not in the take's phase**: its pc, the code's
start, is before the take (`htk0`). -/
theorem not_tk_threadAt {syms : List (String × Nat)} :
    ¬ Tk (Scc.Sem.A64.threadAt Scc.Sem.Entry.linux hello1Λ.code.lo hello1Prog syms) :=
  not_tk (by simp only [Scc.Sem.A64.pcOf, Scc.Sem.A64.threadAt]; decide +kernel)

/-! ## A block's and a node's states -/

section Node

open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Scc.Cert.Rt.A64 (blockAt)
open Kraken.Promising.Lower.A64 (CellAt after exec_str_agrees exec_ldop access_agrees)
open Spike.Lib.A64.Flow.Hello1.Mem (hello1Words hello1F hello1Words_mapped)

variable {rS : Range} {R : Region} {F : MachineData → Prop} {c0 : Ctl}

/-- **A covered block of the main path before the take** is inside `Wr`:
its code (`hb`), its cover (`hok`), the region's facts, the source control
`c0` with its facts at the node (`hC`), the phase check (`hph`) and its
dead targets never reached (`hdead`), every `ret` returning to `ra`
(`hret`), and the entry not in the take's phase (`hT`). -/
theorem blkW_pre {R : Region} {F : MachineData → Prop} {n : ND} {blk : List Directive} {lo hi : Int}
    {dead : Nat → Bool} {ra : Int64} {l : Label} {k : Nat}
    (hb : blockAt hello1Prog l k blk = true) (he : labT l + Int64.ofNat (4 * k) = n.pc)
    (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts hello1Λ hello1Λ.static c)
    (hph : blkPh okPc ph dead labT (labT l + Int64.ofNat (4 * k)) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, classify blk[k] = some (.ret r) →
      Int64.ofInt ((arun labT (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra)
    (hdead : ∀ σ c, n.J σ c → dead (arun labT blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hT : bT (labT l + Int64.ofNat (4 * k)).toBitVec.toNat = true) :
    BlkW (Wr rS) (Kr rS) hello1Exe hello1End R F n blk := by
  rw [he] at hph hT
  have hcode := code_of (exe := hello1Exe) hello1_lays rfl hb (q := n.pc) (by rw [hello1_labT]; exact he)
  rw [← hello1_labT] at hph hret hdead
  obtain ⟨hpc, hph', hsm⟩ := blkPh_sound (μ := μ0) (endPc := hello1End) ph_same pcOff_of_okPc hok hph hret hdead
  refine blkW_sfacts hcode hok hR hal hlo hhi hC hpc hph' fun s m _ _ _ k hk s' _ hpc' htk => ?_
  have := (hsm k hk { s' with st := (s'.st.1, n.pc) } s' rfl hpc').2.mp htk
  exact absurd this (not_tk (by unfold pcOf; exact hT))

/-- A block of the program at its label, in the loaded thread. -/
theorem codeT {l : Label} {k : Nat} {b : List Directive} (hb : blockAt hello1Prog l k b = true) {s : State}
    (hs : s.exe = hello1Exe) (hn : s.endPc = hello1End) : CodeAt s (labT l + Int64.ofNat (4 * k)) b :=
  code_of (exe := hello1Exe) hello1_lays rfl hb (by rw [hello1_labT]) s hs hn

/-- An instruction of the program at its label, in the loaded thread. -/
theorem cellT {l : Label} {k : Nat} {d : Directive} {p : Int64} (hb : blockAt hello1Prog l k [d] = true)
    (he : labT l + Int64.ofNat (4 * k) = p) {s : State} (hs : s.exe = hello1Exe) (hn : s.endPc = hello1End)
    (hpc : s.st.2 = p) : CellAt s d 4 :=
  (codeT hb hs hn).cell (j := 0) rfl rfl rfl (by rw [hpc, ← he]; simp)

/-- Past an instruction at `p` whose next pc has its phase, a state owns
what it owns and is in the take's phase iff it is. -/
theorem next_same {s : State} {p : Int64} (hpc : s.st.2 = p)
    (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat) :
    ∀ m, own (after s 4 m) = own s ∧ (Tk (after s 4 m) ↔ Tk s) :=
  fun _ => ph_same _ _ (by
    show ph (s.st.2 + Int64.ofNat 4).toBitVec.toNat = ph s.st.2.toBitVec.toNat; rw [hpc]; exact hph)

theorem own_at {s : State} {p : Int64} (hpc : s.st.2 = p) : own s = ownOf (ph p.toBitVec.toNat) := by
  unfold own pcOf; rw [hpc]

theorem ph_bT (pc : Nat) : ph pc / 8 % 2 = (bT pc).toNat := by
  unfold ph
  cases bP pc <;> cases bL pc <;> cases bN pc <;> cases bT pc <;> decide

/-- Past an instruction at `p` whose next pc is in the take's phase iff `p`
is, a state is in it iff it is. -/
theorem next_tk {s : State} {p : Int64} (hpc : s.st.2 = p)
    (h : bT (p + Int64.ofNat 4).toBitVec.toNat = bT p.toBitVec.toNat) : ∀ m, Tk (after s 4 m) ↔ Tk s := by
  intro m
  show ph (s.st.2 + Int64.ofNat 4).toBitVec.toNat / 8 % 2 = 0 ↔ ph s.st.2.toBitVec.toNat / 8 % 2 = 0
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
theorem nodeW_si_pre {n : ND} {si : SI} {l : Label} {k : Nat} {p : Int64}
    (hb : blockAt hello1Prog l k [si.toDir] = true) (he : labT l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts hello1Λ hello1Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat) :
    NodeW (Wr rS) (Kr rS) hello1Exe hello1End R F n :=
  nodeW_pre hp hok hT fun _s c σ hs hn _ hpc _ _ hJ hP hO =>
    sfacts_si (hC σ c hJ) hP (cellT hb he hs hn hpc) (next_same hpc hph) hO

/-- **A node at a runtime store** `str Xt, [Xn, #i]` to a word of
`hello1Words` no phase owns, before the take, its next pc in its phase. -/
theorem nodeW_st_pre {n : ND} {t b : XReg} {i : Int64} {l : Label} {k : Nat} {p : Int64} {a : BitVec 64}
    (hb : blockAt hello1Prog l k [strDir t b i] = true) (he : labT l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts hello1Λ hello1Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat)
    (ha : ∀ σ c, n.J σ c → rAddr σ.regs b i = a) (hw : a ∈ hello1Words) (hFr : ∀ m, F m → hello1F m)
    (hno : ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j) :
    NodeW (Wr rS) (Kr rS) hello1Exe hello1End R F n :=
  nodeW_pre hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellT hb he hs hn hpc
    have ha' : rAddr s.st.1.regs b i = a := by rw [hA.regs]; exact ha σ c hJ
    have hex := exec_str_agrees hc ha' (hFr _ hD a hw) (agrees_of_decls hdc _ _)
    obtain ⟨hT', hown, htk⟩ := store_facts (Λ := hello1Λ) (own := own) (Tk := Tk) (k := .plain) (s := s)
      (m := s.st.1) (V := (s.st.1.regs.getRegOrZr (.low (.reg t) .W64)).setWidth 128) (hello1Words_mapped hw).1
      (next_same hpc hph _).2 (.inl ⟨(next_same hpc hph _).1, fun w h => by rw [own_at hpc] at h; exact hno _ w h⟩)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro imm h; cases h) hex hT' hown htk hO

/-- **A node at an owned counter's `ld<op><k> Xs, Xt, [Xn]`** before the
take, its next pc before it too: the counter's word `a` (`ha`), owned at
`p` (`hin`), updated to the operation's result at the next pc (`hupd`). -/
theorem nodeW_ldop_pre {n : ND} {op : AtomicOp} {kk : RmwKind} {rs rt b : XReg} {l : Label} {k : Nat} {p : Int64}
    {a : BitVec 64} (hb : blockAt hello1Prog l k [ldopDir op kk rs rt b] = true)
    (he : labT l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts hello1Λ hello1Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hT4 : bT (p + Int64.ofNat 4).toBitVec.toNat = true)
    (ha : ∀ σ c, n.J σ c → (σ.regs.getXReg b).toBitVec = a) (hw : a ∈ hello1Words) (hFr : ∀ m, F m → hello1F m)
    (hin : ∃ v, (⟨a, 8⟩, v) ∈ ownOf (ph p.toBitVec.toNat))
    (hupd : ∀ σ c, n.J σ c → ownUpdB (ownOf (ph p.toBitVec.toNat)) (ownOf (ph (p + Int64.ofNat 4).toBitVec.toNat))
      ⟨a, 8⟩ (fun old => (op.apply (old.setWidth 64) (σ.regs.getRegOrZr (.low (.reg rs) .W64))).setWidth 128)
      = true) :
    NodeW (Wr rS) (Kr rS) hello1Exe hello1End R F n :=
  nodeW_pre hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellT hb he hs hn hpc
    have ha' : (s.st.1.regs.getXReg b).toBitVec = a := by rw [hA.regs]; exact ha σ c hJ
    have hex := exec_ldop hc (by rw [ha']; exact hFr _ hD a hw)
    rw [ha', access_agrees (agrees_of_decls hdc _ _)] at hex
    have hpc4 : ∀ m, (after s 4 m).st.2 = p + Int64.ofNat 4 := fun _ => by rw [← hpc]
    obtain ⟨hT', hown, htk⟩ := rmw_facts (Λ := hello1Λ) (own := own) (Tk := Tk) (s := s) (k := kk)
      (nr := (RegOrZr.low (.reg rt) .W64 : RegOrZr .W64).isZr)
      (op := fun old => some ((op.apply (old.setWidth 64) (s.st.1.regs.getRegOrZr (.low (.reg rs) .W64))).setWidth 128))
      (m := fun v => { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg rt) .W64) (v.setWidth 64) })
      (hello1Words_mapped hw).1 (fun _ => next_tk hpc (by rw [hT, hT4]) _) (by rw [own_at hpc]; exact hin)
      (fun v hv => by
        rw [own_at hpc, own_at (hpc4 _), Option.getD_some, hA.regs]
        rw [own_at hpc] at hv
        exact ownUpd_of (hupd σ c hJ) v hv)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro imm h; cases h) hex hT' hown htk hO

end Node

/-! ## `scc_rt_alloc_tcb` -/

section Tcb

open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Flow.Hello1.Mem (hello1F)

variable {rS : Range} {c0 : Ctl} {F : MachineData → Prop}

theorem labT_pnA : pnA labT = 6291472#64 := by rw [← hello1_labT]; exact Hello1.Mem.hello1_pnA
theorem labT_pinA : pinA labT = 134217728#64 := by rw [← hello1_labT]; exact Hello1.Mem.hello1_pinA
theorem labT_lockA : lockA labT = 6291496#64 := by rw [← hello1_labT]; exact Hello1.Mem.hello1_lockA
theorem labT_freeNA : freeNA labT = 6291504#64 := by rw [← hello1_labT]; exact Hello1.Mem.hello1_freeNA
theorem labT_nextA : nextA labT = 6291488#64 := by rw [← hello1_labT]; exact Hello1.Mem.hello1_nextA

set_option hygiene false in
/-- A block of `scc_rt_alloc_tcb` before the take, no `ret`, no dead target. -/
local macro "tblk " l:term:max k:term:max ok:term:max : tactic =>
  `(tactic| exact blkW_pre (l := $l) (k := $k) (dead := fun _ => false) (ra := 0) (by decide +kernel) rfl $ok
    hR hal (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel)
    (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim) (fun _ _ _ => rfl) (by decide +kernel))

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc_tcb` without an event. -/
local macro "tsi " si:term:max l:term:max k:term:max : tactic =>
  `(tactic| exact nodeW_si_pre (si := $si) (l := $l) (k := $k) (p := labT $l + Int64.ofNat (4 * $k))
    (by decide +kernel) rfl (by first | rfl | exact (Spike.Lib.A64.Flow.ofNat4_zero _).symm)
    (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel))

/-- **`scc_rt_alloc_tcb`'s states are inside `Wr`**, in any region holding
its frame, at `n0 = 0`, returning to `.sp2`, with the source control `c0`
(`hC0`, its facts) and the frame condition implying `hello1F`. -/
theorem tcbW (hC0 : CFacts hello1Λ hello1Λ.static c0) {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → hello1F m) (q : TcbG)
    (hq : q.c0 = c0) (hn0 : q.n0 = 0#64) (hra : q.g.ra = (labT ".L0_scc_rt_start.sp2").toBitVec) :
    ∀ i, TcbW (Wr rS) (Kr rS) hello1Exe hello1End R F q i := by
  intro i
  cases i
  case e => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.fnL 0 AllocTcb.atPro_ok
  case entry =>
    show BlkW _ _ _ _ _ _ _ _
    rw [hello1_labT]
    exact blkW_pre (l := AllocTcb.entryL) (k := 0) (dead := fun t => t == 4195240) (ra := 0) (by decide +kernel)
      rfl AllocTcb.atChk_ok hR hal (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim)
      (fun _ _ hJ => by dsimp only [tcbN] at hJ ⊢; rw [(AllocTcb.atChk_walk labT _ hJ.2).1]; decide +kernel)
      (by decide +kernel)
  case j1 => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.entryL 4 AllocTcb.atJ1_ok
  case len => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.lenL 0 AllocTcb.atLen_ok
  case adrp => show NodeW _ _ _ _ _ _ _; rw [hello1_labT]; tsi (SI.adrp .X9 "scc_rt_pinned_next") AllocTcb.lenL 32
  case add => show NodeW _ _ _ _ _ _ _; rw [hello1_labT]; tsi (SI.addLo12 .X9 .X9 "scc_rt_pinned_next") AllocTcb.lenL 33
  case arg => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.lenL 34 AllocTcb.atArg_ok
  case rmw =>
    show NodeW _ _ _ _ _ _ _
    rw [hello1_labT]
    refine nodeW_ldop_pre (op := .ADD) (kk := .acqRel) (rs := .X9) (rt := .X11) (b := .X10) (l := AllocTcb.lenL)
      (k := 37) (by decide +kernel) rfl rfl
      (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fun σ _ hJ => by show σ.regs.X10.toBitVec = _; exact hJ.2.2.2.trans labT_pnA) (by decide) hFr
      ⟨_, .head _⟩ fun σ _ hJ => ?_
    rw [Spike.Lib.A64.Alloc.getRegOrZr_x]
    simp only [Reg64s.getXReg]
    rw [hJ.2.2.1]
    decide +kernel
  case bnd => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.lenL 38 AllocTcb.atBnd_ok
  case j2 => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.lenL 47 AllocTcb.atJ2_ok
  case ok => show NodeW _ _ _ _ _ _ _; rw [hello1_labT]; tsi (SI.adrp .X9 "scc_rt_pinned") AllocTcb.okL 0
  case ok1 => show NodeW _ _ _ _ _ _ _; rw [hello1_labT]; tsi (SI.addLo12 .X9 .X9 "scc_rt_pinned") AllocTcb.okL 1
  case ok2 => show BlkW _ _ _ _ _ _ _ _; rw [hello1_labT]; tblk AllocTcb.okL 2 AllocTcb.atOk_ok
  case hdr =>
    show NodeW _ _ _ _ _ _ _
    rw [hello1_labT]
    refine nodeW_st_pre (t := .X9) (b := .X10) (i := 0) (l := AllocTcb.okL) (k := 29) (a := 134217728#64)
      (by decide +kernel) rfl rfl
      (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fun σ _ hJ => ?_) (by decide) hFr (not_own (by decide))
    obtain ⟨-, -, -, h10⟩ := hJ
    rw [hn0, labT_pinA] at h10
    have h10' : σ.regs.X10.toBitVec = 134217728#64 := by rw [h10]; rfl
    simp only [rAddr, Reg64s.getXReg, h10']
    decide
  case ret =>
    show BlkW _ _ _ _ _ _ _ _
    rw [hello1_labT]
    exact blkW_pre (l := AllocTcb.okL) (k := 30) (dead := fun _ => false) (ra := labT ".L0_scc_rt_start.sp2")
      (by decide +kernel) rfl AllocTcb.atRet_ok hR hal (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0)
      (by decide +kernel)
      (hret_of_run AllocTcb.atRet_ok fun _ _ hJ => by
        dsimp only [tcbN] at hJ ⊢
        rw [(AllocTcb.atRet_walk labT _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ _ _ => rfl) (by decide +kernel)

end Tcb

/-! ## `scc_rt_main`'s source facts -/

section Src

open Spike.Lib Spike.Lib.A64.Flow
open Kraken.AArch64.Parser Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow.Ret0 (CallerCells LimOk)
open Spike.Lib.A64.Alloc (Call Ea)
open Scc.Cert.Rt.A64 (Lays endOf)

/-- **`hello1_main_post_segW`'s source and frame facts** for a caller's
state `m0`, `σC` at `wc_rodata`'s call: `MainPostP` but its states inside
`W` (`hW`, the instance's node obligations). -/
structure Hello1PostSrc (W : Frag isaLSE2) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (m0 : MachineData) (σC : AS) (Jp J1 J2 J3 J4 Jr Jw : AS → Ctl → Prop) :
    Prop where
  hra : ∀ σ0 c, Jp σ0 c → (_root_.Executable.labels exe).label ".L1_scc_rt_main.sp0" = Int64.ofBitVec (σ0.slot (-8))
  hmem : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
      ∀ m, mF R F m0 σC m → Mem.loadInt m.dmem (rAddr σ0.regs .X0 i) 8 = none
  h1 : ∀ σ0 c, Jp σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J1 σ0 { c with hold := some ((rAddr σ0.regs .X0 0).toNat, w') }
  h2 : ∀ σ0 c, J1 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧
      c.hold = some ((rAddr σ0.regs .X0 0).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK1.setWidth 128).toNat ∧ J2 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩
  h3 : ∀ σ0 c, J2 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧ c.hold = none ∧
      ∀ (r : Val) (w' : TermRun.Word), ms.rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
        J3 σ0 { c with hold := some ((rAddr σ0.regs .X0 8).toNat, w') }
  h4 : ∀ σ0 c, J3 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
      (wv wold : TermRun.Word),
      XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧
      c.hold = some ((rAddr σ0.regs .X0 8).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
      Scc.Sem.ValRep lbl wv.val (rpK2.setWidth 128).toNat ∧ J4 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩
  hedge : ∀ σ0 c, J4 σ0 c → ∀ σ' : AS, σ'.regs.X0.toBitVec = σ0.regs.X0.toBitVec →
      σ'.regs.X1.toBitVec = 0#64 → σ'.regs.X2.toBitVec = 2#64 → σ'.regs.X3.toBitVec = 13#64 →
      σ'.regs.X29.toBitVec = σ0.slot (-16) → σ'.regs.X30.toBitVec = σ0.slot (-8) →
      ∃ c', LocalRun p c c' ∧ Jr σ' c'
  hlimW : ∀ σx c, Jr σx c → LimOk ms F exe endPc (tcbA σx.regs 8) (σx.regs.SP.toBitVec - (96 : Int64).toBitVec)
  hsvc : ∀ F' : MachineData → Prop, FStable (pR (wR R)) F' →
      (∀ m, F' m → (F m ∧ CallerCells R (-80) (-144) 0 m) ∧ CallerCells (wR R) (-96) (-48) 0 m) →
      ∀ g' : PG, g'.2.2 = ((_root_.Executable.labels exe).label ".L19_wc_main.sp4").toBitVec →
      SegW W K p lbl ms
        (At exe endPc (pR (wR R)) F' (Print.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .svc))
        (At exe endPc (pR (wR R)) F' (Print.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .n5))
  hedgeW : ∀ g : AS × Ctl, ∀ σ c, wcJ (wJ0 (_root_.Executable.labels exe).label σC Jr g) σ c →
      ∀ σ' : AS, (∀ k, -96 ≤ k → k < 0 → k % 8 = 0 → σ'.slot k = wcSl σ k) →
      σ'.regs.X0.toBitVec = 0#64 → σ'.regs.X29.toBitVec = σ.slot (-16) → σ'.regs.X30.toBitVec = σ.slot (-8) →
      ∃ c', LocalRun p c c' ∧ Jw σ' c'
  hok : ∀ s c σx, Jw σx c →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label ".L1_scc_rt_main.sp1" + 4 + 4 + 4, ⟨-80, []⟩,
        fun _ _ => True⟩ s c → SysOk p ms s c (.exitGroup σx.regs.X0.toNat)

/-- **`hello1_main_segW`'s source and frame facts**, the instance's to
discharge: the premises of classes (a) (from the source program: the
allocator's call `hq`, the bridge `hret`, and per caller's state the
exchanges `h1`–`h4`, the local runs `hedge`, `hedgeW`, the exit `hok`, the
saved return `hra`) and (d) (the limit loads' room `hlimM`, `hlimR`,
`hlimW`, the fresh cells unmapped `hmem`, the allocation's continuation
`hpost` through `hJp`, and `print`'s write `hsvc`), at the main path's
invariants `J` and, indexed by the caller's state, `Jp`, `J1`–`J4`, `Jr`,
`Jw`. The layout's premises (class (b)) and the states inside `W` stay
`hello1_main_segW_src`'s. -/
structure Hello1Src (W : Frag isaLSE2) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (J : AS → Ctl → Prop)
    (Jp J1 J2 J3 J4 Jr Jw : MachineData → AS → AS → Ctl → Prop) : Prop where
  hlimM : ∀ σ c, J σ c → LimOk ms F exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (80 : Int64).toBitVec)
  hlimR : ∀ σ c, J σ c → LimOk ms F exe endPc (tcbA σ.regs 8)
      (σ.regs.SP.toBitVec - (80 : Int64).toBitVec - (48 : Int64).toBitVec)
  hq : ∀ σ c, J σ c → ∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ms = 3#64
  hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none
  hJp : ∀ m0 σC (q : AG ms (_root_.Executable.labels exe).label) l b w σx σ c0 c, (Ea ms q.1 l b w).J σx c →
      (rN (_root_.Executable.labels exe).label (mRdJ0 (mNC (_root_.Executable.labels exe).label J).J σC) .call).J σ c0 →
      (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c0 →
      Jp m0 σC (leave (aR (mR R)) (-48) σ σx) c
  hpost : ∀ l b w s c, lbl l = none → (∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
      (pN (_root_.Executable.labels exe).label (Jp m0 σC) (J1 m0 σC) (J2 m0 σC) (J3 m0 σC) (J4 m0 σC) .s0) s c) →
      ms.xa l b w s c
  hret : ∀ m0 σC σ c,
      (rX ms (_root_.Executable.labels exe).label lbl
        (mRdJ0 (mNC (_root_.Executable.labels exe).label J).J σC) .sp0).J σ c →
      Jp m0 σC σ c
  post : ∀ m0 σC, Hello1PostSrc W K p lbl ms exe endPc R F m0 σC (Jp m0 σC) (J1 m0 σC) (J2 m0 σC) (J3 m0 σC)
    (J4 m0 σC) (Jr m0 σC) (Jw m0 σC)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`hello1_main_segW` from the source facts**: the layout's premises,
the states inside `W` before (`hW`) and after (`hWp`) `wc_rodata`'s
allocation, and `Hello1Src`. -/
theorem hello1_main_segW_src {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hhi : 0 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.A64.abi)
    {J : AS → Ctl → Prop} {Jp J1 J2 J3 J4 Jr Jw : MachineData → AS → AS → Ctl → Prop}
    (hW : MainPreW W K exe endPc R F ms J)
    (hWp : ∀ m0 σC, MainPostW W K exe endPc R F ms m0 σC (Jp m0 σC) (J1 m0 σC) (J2 m0 σC) (J3 m0 σC) (J4 m0 σC)
      (Jr m0 σC) (Jw m0 σC))
    (hS : Hello1Src W K p lbl ms exe endPc R F J Jp J1 J2 J3 J4 Jr Jw) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_main", ⟨0, []⟩, J⟩)
      (fun s c => At exe endPc R F (mAb (_root_.Executable.labels exe).label) s c ∨
        ∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
          (rX ms (_root_.Executable.labels exe).label lbl
            (mRdJ0 (mNC (_root_.Executable.labels exe).label J).J σC) .abort) s c) ∧
    SegW W K p lbl ms
      (fun s c => ∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
        (pN (_root_.Executable.labels exe).label (Jp m0 σC) (J1 m0 σC) (J2 m0 σC) (J3 m0 σC) (J4 m0 σC) .s0) s c)
      (At exe endPc R F (mAb (_root_.Executable.labels exe).label)) :=
  hello1_main_segW hp hend hF hR hal hlo hhi hK hW hS.hlimM hS.hlimR hS.hq hS.hmem hS.hJp hS.hpost hS.hret
    fun m0 σC => let h := hS.post m0 σC
      ⟨hWp m0 σC, h.hra, h.hmem, h.h1, h.h2, h.h3, h.h4, h.hedge, h.hlimW, h.hsvc, h.hedgeW, h.hok⟩

end Src

end Spike.Lib.A64.Flow.Hello1.Inst
