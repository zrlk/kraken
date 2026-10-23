/-
**`ret0.w` on AArch64: the per-state facts of the main path** (`SFacts`,
`Spike/Lib/A64SegInst.lean`) at the loaded thread, the instance side of
`inst_of_segW`.

- **The labels** (`ret0Tab`, `labT`, `ret0_labT`): the code labels of the
  main path at their addresses in the loaded thread, a table the kernel
  reads (`labIn` decided on the program, `label_labIn`), so a block's checks
  are decided.
- **The phase index** (`ph`): four bits of the pc. The main path visits each
  of its pcs in one phase, every function on it running once: whether
  `scc_rt_pinned_next` is still `0` (up to the counter's add in
  `scc_rt_alloc_tcb`), whether the stack lock is held (past the `swpal`, up
  to the `stlr`), whether `scc_rt_stack_next` is still `0` (up to its add)
  and whether the stack is not yet taken (up to the take site). A pc off the
  main path has whatever phase its range gives.
- **The owned words** (`own`): the four counters `scc_rt_pinned_next`,
  `scc_rt_stack_lock`, `scc_rt_stack_free_n`, `scc_rt_stack_next` with their
  values by phase; **the take's phase** (`Tk`): past the take site.
- **The marks** (`μ0`, `ret0_marks`): the transfer and abort sites, from
  the loader's parse of the listing (the trust boundary `hpa`); `okPc`, a pc
  off all of them, gives `PcOff` (`pcOff_of_okPc`).
-/
import Spike.Lib.A64SegInst
import Spike.Lib.A64Ret0Mem
import Spike.Lib.A64Ret0Own

namespace Spike.Lib.A64.Flow.Ret0.Inst

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow.Ret0.Mem (ret0Exe ret0End ret0_lays)
open Spike.Lib.A64.OwnLimRt (labIn labOk label_labIn)
open SccCode (ret0Λ ret0Prog ret0Asm)

/-! ## The labels -/

/-- **The main path's code labels** at their addresses in the loaded
thread. -/
def ret0Tab : List (Label × Nat) :=
  [("_start", 4194304), ("scc_rt_start", 4194308), (".L0_scc_rt_start.0_entry", 4194324),
    (".L0_scc_rt_start.sp2", 4194376), (".L0_scc_rt_start.sp3", 4194388), (".L0_scc_rt_start.halt4", 4194420),
    ("scc_rt_main", 4194424), (".L1_scc_rt_main.stack_check", 4194424), (".L1_scc_rt_main.0_entry", 4194464),
    (".L1_scc_rt_main.sp0", 4194468), (".L1_scc_rt_main.halt2", 4194488), (".L1_scc_rt_main.stack_grow", 4194492),
    (".L1_scc_rt_main.sp_check", 4194548), ("scc_rt_alloc", 4194596), (".L2_scc_rt_alloc.0_entry", 4194624),
    (".L2_scc_rt_alloc.1_cnt", 4194644), (".L2_scc_rt_alloc.2_slow", 4194708),
    (".L2_scc_rt_alloc.3_spin", 4194728), (".L2_scc_rt_alloc.4_full", 4194732), (".L2_scc_rt_alloc.sp7", 4194740),
    (".L2_scc_rt_alloc.halt8", 4194740), (".L2_scc_rt_alloc.5_ok", 4194744), ("scc_rt_alloc_tcb", 4194964),
    (".L3_scc_rt_alloc_tcb.0_entry", 4194988), (".L3_scc_rt_alloc_tcb.1_len", 4195008),
    (".L3_scc_rt_alloc_tcb.2_full", 4195200), (".L3_scc_rt_alloc_tcb.sp13", 4195208),
    (".L3_scc_rt_alloc_tcb.halt14", 4195208), (".L3_scc_rt_alloc_tcb.3_ok", 4195212),
    ("scc_rt_thread_reserve", 4195384), (".L4_scc_rt_thread_reserve.0_entry", 4195400),
    (".L4_scc_rt_thread_reserve.1_full", 4195464), (".L4_scc_rt_thread_reserve.sp4", 4195472),
    (".L4_scc_rt_thread_reserve.halt5", 4195472), (".L4_scc_rt_thread_reserve.2_ok", 4195476),
    ("scc_rt_thread_init", 4195496), (".L5_scc_rt_thread_init.0_entry", 4195516),
    (".L5_scc_rt_thread_init.sp0", 4195524), ("scc_rt_stack_take", 4195652),
    (".L6_scc_rt_stack_take.0_entry", 4195672), (".L6_scc_rt_stack_take.1_cls5", 4195708),
    (".L6_scc_rt_stack_take.2_clsnext6", 4195728), (".L6_scc_rt_stack_take.3_clsdone7", 4195812),
    (".L6_scc_rt_stack_take.4_spin14", 4195884), (".L6_scc_rt_stack_take.5_locked15", 4195920),
    (".L6_scc_rt_stack_take.6_pop", 4195952), (".L6_scc_rt_stack_take.7_bump", 4196052),
    (".L6_scc_rt_stack_take.8_full", 4196140), (".L6_scc_rt_stack_take.sp36", 4196148),
    (".L6_scc_rt_stack_take.halt37", 4196148), (".L6_scc_rt_stack_take.9_ok", 4196152),
    (".L6_scc_rt_stack_take.10_taken", 4196184), ("scc_rt_take_site", 4196192), ("scc_rt_stack_release", 4196216),
    ("wc_main", 4198808), (".L18_wc_main.stack_check", 4198808), (".L18_wc_main.0_entry", 4198844),
    (".L18_wc_main.stack_grow", 4198884), (".L18_wc_main.sp_check", 4198940),
    (".L18_wc_main.abort_overflow", 4198988), (".L18_wc_main.abort_overflow_halt", 4198996)]

/-- Each is a label of the program at its `labIn` address. -/
theorem ret0Tab_ok : ret0Tab.all (fun p => labOk ret0Prog p.1 && labIn ret0Λ.code.lo ret0Prog p.1 == Int64.ofNat p.2)
    = true := by decide +kernel

/-- **The loaded thread's labels**, the table's first. -/
def labT (l : Label) : Int64 :=
  match ret0Tab.lookup l with
  | some n => Int64.ofNat n
  | none => (_root_.Executable.labels ret0Exe).label l

theorem lookup_mem {l : Label} {n : Nat} : ∀ {L : List (Label × Nat)}, L.lookup l = some n → (l, n) ∈ L
  | [], h => by cases h
  | (l', n') :: L, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i he
      cases h
      rw [beq_iff_eq] at he
      subst he
      exact .head _
    · exact .tail _ (lookup_mem h)

/-- **The loaded thread's labels are `labT`'s.** -/
theorem ret0_labT : (_root_.Executable.labels ret0Exe).label = labT := by
  funext l
  unfold labT
  split
  · rename_i n hn
    have h := List.all_eq_true.mp ret0Tab_ok _ (lookup_mem hn)
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [← h.2]
    exact label_labIn ret0_lays rfl h.1
  · rfl

/-! ## The phases -/

/-- The pc `pc` is in `[a, b)`. -/
def inN (a b pc : Nat) : Bool := a ≤ pc && pc < b

/-- **`scc_rt_pinned_next` is still `0`**: `_start` and `scc_rt_start` up
to the call of `scc_rt_alloc_tcb`, and that function up to and including
its counter's add. -/
def bP (pc : Nat) : Bool := inN 4194304 4194376 pc || inN 4194964 4195160 pc

/-- **The stack lock is held**: past the `swpal` of `scc_rt_stack_take` up
to and including the `stlr` of its bump path. -/
def bL (pc : Nat) : Bool := inN 4195896 4196076 pc

/-- **`scc_rt_stack_next` is still `0`**: up to `.sp3` of `scc_rt_start`,
`scc_rt_alloc_tcb` (and `scc_rt_thread_reserve`), `scc_rt_thread_init` up
to the return of its call, and `scc_rt_stack_take` up to and including the
add. -/
def bN (pc : Nat) : Bool :=
  inN 4194304 4194388 pc || inN 4194964 4195384 pc || inN 4195496 4195524 pc || inN 4195652 4196100 pc

/-- **The stack is not taken yet**: as `bN`, and `scc_rt_stack_take` up to
and including the take site. -/
def bT (pc : Nat) : Bool :=
  inN 4194304 4194388 pc || inN 4194964 4195384 pc || inN 4195496 4195524 pc || inN 4195652 4196196 pc

/-- **The phase index of a pc**: its four bits. -/
def ph (pc : Nat) : Nat := (bP pc).toNat + 2 * (bL pc).toNat + 4 * (bN pc).toNat + 8 * (bT pc).toNat

/-- **The owned words at a phase index**: the four counters and their
values. -/
def ownOf (i : Nat) : List (Loc × Val) :=
  [(⟨6291472#64, 8⟩, (if i % 2 = 1 then 0#64 else AllocTcb.tcbLen).setWidth 128),
    (⟨6291496#64, 8⟩, (if i / 2 % 2 = 1 then 1#64 else 0#64).setWidth 128),
    (⟨6291504#64, 8⟩, (0#64).setWidth 128),
    (⟨6291488#64, 8⟩, (if i / 4 % 2 = 1 then 0#64 else StackTake.size0).setWidth 128)]

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

The take's phase is a function of the pc (`Tk`), so it is sound only if no
pc is reached both before and after the take. `tkCross` lists the program's
control edges whose ends differ in `bT`, decided (`tkCross_eq`): the two
calls of `scc_rt_abort` off the `.2_full` and `.8_full` paths (dead on the
main path), the take site's fall-through (the take itself), and
`scc_rt_grow`'s call of `scc_rt_stack_take` (after the take into before it:
dead on the main path, and a second take the one-take consumer does not
model). A new crossing, such as a runtime helper called in both phases,
changes the list and fails here. -/

/-- The code labels of a program laid out from `pc`, with their addresses. -/
def labsAt : Nat → List Directive → List (Label × Nat)
  | _, [] => []
  | pc, .label l :: ds => (l, pc) :: labsAt pc ds
  | pc, _ :: ds => labsAt (pc + 4) ds

/-- **The control edges** of a program laid out from `pc`, its labels at
`L`: a branch's target, a conditional's both, every other instruction's
fall-through; a `ret`'s none (its target is the caller's, a call's
fall-through). -/
def edgesAt (L : List (Label × Nat)) : Nat → List Directive → List (Nat × Nat)
  | _, [] => []
  | pc, .label _ :: ds => edgesAt L pc ds
  | pc, d :: ds =>
    let lab := fun l => (L.lookup l).getD 0
    (match Spike.Lib.A64.Flow.classify d with
      | some (.b l) | some (.bl l) => [(pc, lab l)]
      | some (.bcond _ l) | some (.cbz _ l) | some (.cbnz _ l) => [(pc, lab l), (pc, pc + 4)]
      | some (.ret _) => []
      | _ => [(pc, pc + 4)]) ++ edgesAt L (pc + 4) ds

/-- **The edges crossing the take's phase** in the loaded program. -/
def tkCross : List (Nat × Nat) :=
  (edgesAt (labsAt ret0Λ.code.lo ret0Prog) ret0Λ.code.lo ret0Prog).filter fun e => bT e.1 != bT e.2

/-- **The only crossings**: `scc_rt_alloc_tcb`'s and `scc_rt_stack_take`'s
calls of `scc_rt_abort`, the take site's fall-through, `scc_rt_grow`'s call
of `scc_rt_stack_take`. -/
theorem tkCross_eq :
    tkCross = [(4195204, 4198244), (4196144, 4198244), (4196192, 4196196), (4196840, 4195652)] := by
  decide +kernel

/-- The take site's fall-through owns what the site owns. -/
theorem ownOf_site : ownOf (ph 4196196) = ownOf (ph 4196192) := by decide

/-! ## The marks -/

/-- **The loaded program's marks**: the take and release sites, the five
abort sites. -/
def μ0 : Marks where
  site
    | .take => some 4196192
    | .release => some 4196248
  abortAt
    | .overflow => some 4198508
    | .heap => some 4198580
    | .stack => some 4198652
    | .writeErr => some 4198724
    | .threads => some 4198796

/-- **The canonical target's marks of `ret0`** are `μ0`, given the
loader's parse of the listing (`hpa`, the trust boundary). -/
theorem ret0_marks (hpa : Scc.Sem.A64.textProgram ret0Asm = .ok ret0Prog) : T.marks ret0Asm ret0Λ = μ0 := by
  have hr := Scc.Sem.A64.resolve_of_parsed (Scc.Sem.A64.kernel 1) Scc.Sem.Entry.linux ret0Λ hpa
  unfold Scc.Sem.Target.marks
  congr 1
  · funext k; cases k <;> exact (hr _).trans (by decide +kernel)
  · funext k; cases k <;> exact (hr _).trans (by decide +kernel)

/-- **The pcs off the marks' sites.** -/
def okPc (pc : Nat) : Bool := !([4196192, 4196248, 4198508, 4198580, 4198652, 4198724, 4198796].contains pc)

/-- A pc off the sites is off `μ0`'s, with no take there. -/
theorem pcOff_of_okPc {rS : Range} : ∀ s : State, okPc (pcOf s) = true →
    PcOff μ0 s ∧ ∀ s', ¬ TakeK (labT StackTake.siteL) rS s s' := by
  intro s h
  have hne : ∀ a ∈ [4196192, 4196248, 4198508, 4198580, 4198652, 4198724, 4198796], pcOf s ≠ a := by
    intro a ha he
    subst he
    simp only [okPc, Bool.not_eq_true', List.contains_eq_any_beq, List.any_eq_false, beq_iff_eq] at h
    exact h _ ha rfl
  refine ⟨⟨fun a ha => ?_, fun a ha => ?_, fun k a ha => ?_⟩, fun s' hk => ?_⟩
  · cases ha; exact hne _ (by simp)
  · cases ha; exact hne _ (by simp)
  · cases k <;> cases ha <;> exact hne _ (by simp)
  · have := congrArg (fun x : Int64 => x.toBitVec.toNat) (TakeK.pc hk)
    exact hne 4196192 (by simp) (by unfold pcOf; rw [this]; decide +kernel)

/-! ## A block's states -/

section Blk

open Spike.Lib.A64.Flow
open Scc.Cert.Rt.A64 (blockAt)
open Spike.Lib.A64.Flow.Ret0.Mem (ret0Exe ret0End)

variable {rS : Range} {c0 : Ctl}

/-- **The per-state facts of `ret0`**: `SFacts` at the loaded program's
marks and owned words, no label placed. -/
abbrev Wr (rS : Range) : Frag isaLSE2 := fun s c => SFacts ret0Λ μ0 own rS Tk ret0Λ.static s c

/-- **The outside move**: the take at the take site. -/
abbrev Kr (rS : Range) : State → State → Prop := TakeK (labT StackTake.siteL) rS

/-- A state not in the take's phase, at a pc whose phase says so. -/
theorem not_tk {s : State} (h : bT (pcOf s) = true) : ¬ Tk s := by
  unfold Tk ph
  rw [h]
  cases bP (pcOf s) <;> cases bL (pcOf s) <;> cases bN (pcOf s) <;> decide

/-- **The loaded thread is not in the take's phase**: its pc, the code's
start, is before the take (`htk0`). -/
theorem not_tk_threadAt {syms : List (String × Nat)} :
    ¬ Tk (Scc.Sem.A64.threadAt Scc.Sem.Entry.linux ret0Λ.code.lo ret0Prog syms) :=
  not_tk (by simp only [Scc.Sem.A64.pcOf, Scc.Sem.A64.threadAt]; decide +kernel)

/-- **A covered block of the main path before the take** is inside `Wr`:
its code (`hb`), its cover (`hok`), the region's facts, the source control
`c0` with its facts at the node (`hC`), the phase check (`hph`) and its
dead targets never reached (`hdead`), every `ret` returning to `ra`
(`hret`), and the entry not in the take's phase (`hT`). -/
theorem blkW_pre {R : Region} {F : MachineData → Prop} {n : ND} {blk : List Directive} {lo hi : Int}
    {dead : Nat → Bool} {ra : Int64} {l : Label} {k : Nat}
    (hb : blockAt ret0Prog l k blk = true) (he : labT l + Int64.ofNat (4 * k) = n.pc)
    (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c)
    (hph : blkPh okPc ph dead labT (labT l + Int64.ofNat (4 * k)) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, classify blk[k] = some (.ret r) →
      Int64.ofInt ((arun labT (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra)
    (hdead : ∀ σ c, n.J σ c → dead (arun labT blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hT : bT (labT l + Int64.ofNat (4 * k)).toBitVec.toNat = true) :
    BlkW (Wr rS) (Kr rS) ret0Exe ret0End R F n blk := by
  rw [he] at hph hT
  have hcode := code_of (exe := ret0Exe) ret0_lays rfl hb (q := n.pc) (by rw [ret0_labT]; exact he)
  rw [← ret0_labT] at hph hret hdead
  obtain ⟨hpc, hph', hsm⟩ := blkPh_sound (μ := μ0) (endPc := ret0End) ph_same pcOff_of_okPc hok hph hret hdead
  refine blkW_sfacts hcode hok hR hal hlo hhi hC hpc hph' fun s m _ _ _ k hk s' _ hpc' htk => ?_
  have := (hsm k hk { s' with st := (s'.st.1, n.pc) } s' rfl hpc').2.mp htk
  exact absurd this (not_tk (by unfold pcOf; exact hT))

/-- **A covered block of the main path after the take** is inside `Wr`: as
`blkW_pre` without the phase's entry check, its frame condition also
`StackM rS` (kept by the region's writes, `hSM`) and `rS` in the pool
(`hsub`), so its states own the range. -/
theorem blkW_post {R : Region} {F : MachineData → Prop} {n : ND} {blk : List Directive} {lo hi : Int}
    {dead : Nat → Bool} {ra : Int64} {l : Label} {k : Nat}
    (hb : blockAt ret0Prog l k blk = true) (he : labT l + Int64.ofNat (4 * k) = n.pc)
    (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c)
    (hph : blkPh okPc ph dead labT (labT l + Int64.ofNat (4 * k)) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, classify blk[k] = some (.ret r) →
      Int64.ofInt ((arun labT (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra)
    (hdead : ∀ σ c, n.J σ c → dead (arun labT blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hsub : rS.Sub ret0Λ.stackPool) (hSM : FStable R (StackM rS)) :
    BlkW (Wr rS) (Kr rS) ret0Exe ret0End R (fun m => F m ∧ StackM rS m) n blk := by
  rw [he] at hph
  have hcode := code_of (exe := ret0Exe) ret0_lays rfl hb (q := n.pc) (by rw [ret0_labT]; exact he)
  rw [← ret0_labT] at hph hret hdead
  obtain ⟨hpc, hph', -⟩ := blkPh_sound (μ := μ0) (endPc := ret0End) ph_same pcOff_of_okPc hok hph hret hdead
  refine blkW_sfacts hcode hok hR hal hlo hhi hC hpc hph' fun s m hF hD _ k hk s' hm _ _ => ?_
  refine ⟨hsub, fun a h8 ha ha7 => ?_⟩
  unfold Scc.Sem.A64.privLoad
  rw [Option.isSome_map, hm]
  exact hSM _ _ hF.2 hD a h8 ha ha7

/-- **The range owned from a region's cells and the words off it**: every
aligned word of `rS` either lies off the 8-aligned region `R` (`hoff`) or is
one of its cells (`hc`). -/
theorem owned_off {R : Region} (hR : R.OK) (hb : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub ret0Λ.stackPool) {s : State} (hoff : StackOff rS R s.st.1)
    (hc : ∀ k, R.Off k → (Mem.loadInt s.st.1.dmem (R.addr k) 8).isSome) : Owned ret0Λ rS s := by
  refine ⟨hsub, fun a h8 ha ha7 => ?_⟩
  unfold Scc.Sem.A64.privLoad
  rw [Option.isSome_map]
  by_cases hout : (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a
  · exact hoff a h8 ha ha7 hout
  · have h1 := hR.lo
    have h2 := hR.hi
    have hk : R.Off ((a : Int) - R.base.toNat) := ⟨by omega, by omega, by omega⟩
    have he : R.addr ((a : Int) - R.base.toNat) = BitVec.ofNat 64 a := by
      apply BitVec.eq_of_toNat_eq
      have := Region.addr_toNat hR hk
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [← he]
    exact hc _ hk

/-- **The words of `rS` off a callee's region**: off the caller's region
(`StackOff`) or a caller's cell outside the callee's (`CallerCells`). -/
theorem stackOff_callee {R : Region} (hR : R.OK) (hb : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) {kc lo' : Int} (hlo : R.lo ≤ kc + lo') (hlo0 : lo' ≤ 0) (hkc : kc < R.hi)
    (hk8 : kc % 8 = 0) {m : MachineData} (hoff : StackOff rS R m) (hcc : CallerCells R kc lo' 0 m) :
    StackOff rS (R.callee kc lo' 0) m := by
  intro a h8 ha ha7 hout'
  have hcb := Region.callee_base (hi' := 0) hR hlo hlo0 hkc
  by_cases hout : (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a
  · exact hoff a h8 ha ha7 hout
  · have h1 := hR.lo
    have h2 := hR.hi
    have hk : R.Off ((a : Int) - R.base.toNat) := ⟨by omega, by omega, by omega⟩
    have hn : ¬ (R.callee kc lo' 0).Off ((a : Int) - R.base.toNat - kc) := by
      rintro ⟨-, h3, h4⟩
      simp only [Region.callee] at hcb h3 h4 hout'
      omega
    have he : R.addr ((a : Int) - R.base.toNat) = BitVec.ofNat 64 a := by
      apply BitVec.eq_of_toNat_eq
      have := Region.addr_toNat hR hk
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [← he]
    exact hcc _ hk hn

/-- **A covered block of the main path after the take**, in a region whose
frame condition gives the words of `rS` off it (`hFO`): as `blkW_post`. -/
theorem blkW_postO {R : Region} {F : MachineData → Prop} {n : ND} {blk : List Directive} {lo hi : Int}
    {dead : Nat → Bool} {ra : Int64} {l : Label} {k : Nat}
    (hb : blockAt ret0Prog l k blk = true) (he : labT l + Int64.ofNat (4 * k) = n.pc)
    (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c)
    (hph : blkPh okPc ph dead labT (labT l + Int64.ofNat (4 * k)) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, classify blk[k] = some (.ret r) →
      Int64.ofInt ((arun labT (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra)
    (hdead : ∀ σ c, n.J σ c → dead (arun labT blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hsub : rS.Sub ret0Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    BlkW (Wr rS) (Kr rS) ret0Exe ret0End R F n blk := by
  rw [he] at hph
  have hcode := code_of (exe := ret0Exe) ret0_lays rfl hb (q := n.pc) (by rw [ret0_labT]; exact he)
  rw [← ret0_labT] at hph hret hdead
  obtain ⟨hpc, hph', -⟩ := blkPh_sound (μ := μ0) (endPc := ret0End) ph_same pcOff_of_okPc hok hph hret hdead
  refine blkW_sfacts hcode hok hR hal hlo hhi hC hpc hph' fun s m hF hD hc k hk s' hm _ _ => ?_
  subst hm
  exact owned_off hR (by omega) hl hh hsub (stackOff_stable hfit _ _ (hFO _ hF) hD) hc

end Blk

/-! ## A single instruction's states -/

section Node

open Spike.Lib.A64.Flow
open Scc.Cert.Rt.A64 (blockAt)
open Kraken.Promising.Lower.A64 (CellAt after exec_str_agrees exec_stlr_agrees exec_ldr_agrees exec_ldop exec_swp
  access_agrees)
open Spike.Lib.A64.Flow.Ret0.Mem (ret0Exe ret0End ret0Words ret0F ret0Words_mapped)

variable {rS : Range} {R : Region} {F : MachineData → Prop}

/-- A block of the program at its label, in the loaded thread. -/
theorem codeT {l : Label} {k : Nat} {b : List Directive} (hb : blockAt ret0Prog l k b = true) {s : State}
    (hs : s.exe = ret0Exe) (hn : s.endPc = ret0End) : CodeAt s (labT l + Int64.ofNat (4 * k)) b :=
  code_of (exe := ret0Exe) ret0_lays rfl hb (by rw [ret0_labT]) s hs hn

/-- An instruction of the program at its label, in the loaded thread. -/
theorem cellT {l : Label} {k : Nat} {d : Directive} {p : Int64} (hb : blockAt ret0Prog l k [d] = true)
    (he : labT l + Int64.ofNat (4 * k) = p) {s : State} (hs : s.exe = ret0Exe) (hn : s.endPc = ret0End)
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
    (h : ∀ s c σ, s.exe = ret0Exe → s.endPc = ret0End → s.decls = {} → s.st.2 = p → Abs R n.o s.st.1 σ →
      F s.st.1 → n.J σ c → PcOff μ0 s → (Tk s → Owned ret0Λ rS s) → Wr rS s c) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hP := pcOff_of_okPc (rS := rS) s (by unfold pcOf; rw [hpc]; exact hok)
  exact ⟨h s c σ hs hn hdc hpc hA hD hJ hP.1 fun h' => absurd h' (not_tk (by unfold pcOf; rw [hpc]; exact hT)), hP.2⟩

/-- **A node at a single instruction without an event** (`SI`) before the
take, its next pc in its phase. -/
theorem nodeW_si_pre {n : ND} {si : SI} {l : Label} {k : Nat} {p : Int64}
    (hb : blockAt ret0Prog l k [si.toDir] = true) (he : labT l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  nodeW_pre hp hok hT fun _s c σ hs hn _ hpc _ _ hJ hP hO =>
    sfacts_si (hC σ c hJ) hP (cellT hb he hs hn hpc) (next_same hpc hph) hO

/-- **A node at a runtime store** `str Xt, [Xn, #i]` to a word of
`ret0Words` no phase owns, before the take, its next pc in its phase. -/
theorem nodeW_st_pre {n : ND} {t b : XReg} {i : Int64} {l : Label} {k : Nat} {p : Int64} {a : BitVec 64}
    (hb : blockAt ret0Prog l k [strDir t b i] = true) (he : labT l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat)
    (ha : ∀ σ c, n.J σ c → rAddr σ.regs b i = a) (hw : a ∈ ret0Words) (hFr : ∀ m, F m → ret0F m)
    (hno : ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  nodeW_pre hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellT hb he hs hn hpc
    have ha' : rAddr s.st.1.regs b i = a := by rw [hA.regs]; exact ha σ c hJ
    have hex := exec_str_agrees hc ha' (hFr _ hD a hw) (agrees_of_decls hdc _ _)
    obtain ⟨hT', hown, htk⟩ := store_facts (Λ := ret0Λ) (own := own) (Tk := Tk) (k := .plain) (s := s)
      (m := s.st.1) (V := (s.st.1.regs.getRegOrZr (.low (.reg t) .W64)).setWidth 128) (ret0Words_mapped hw).1
      (next_same hpc hph _).2 (.inl ⟨(next_same hpc hph _).1, fun w h => by rw [own_at hpc] at h; exact hno _ w h⟩)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro imm h; cases h) hex hT' hown htk hO

/-- **A node at an owned counter's `ld<op><k> Xs, Xt, [Xn]`** before the
take, its next pc before it too: the counter's word `a` (`ha`), owned at
`p` (`hin`), updated to the operation's result at the next pc (`hupd`). -/
theorem nodeW_ldop_pre {n : ND} {op : AtomicOp} {kk : RmwKind} {rs rt b : XReg} {l : Label} {k : Nat} {p : Int64}
    {a : BitVec 64} (hb : blockAt ret0Prog l k [ldopDir op kk rs rt b] = true)
    (he : labT l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hT4 : bT (p + Int64.ofNat 4).toBitVec.toNat = true)
    (ha : ∀ σ c, n.J σ c → (σ.regs.getXReg b).toBitVec = a) (hw : a ∈ ret0Words) (hFr : ∀ m, F m → ret0F m)
    (hin : ∃ v, (⟨a, 8⟩, v) ∈ ownOf (ph p.toBitVec.toNat))
    (hupd : ∀ σ c, n.J σ c → ownUpdB (ownOf (ph p.toBitVec.toNat)) (ownOf (ph (p + Int64.ofNat 4).toBitVec.toNat))
      ⟨a, 8⟩ (fun old => (op.apply (old.setWidth 64) (σ.regs.getRegOrZr (.low (.reg rs) .W64))).setWidth 128)
      = true) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  nodeW_pre hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellT hb he hs hn hpc
    have ha' : (s.st.1.regs.getXReg b).toBitVec = a := by rw [hA.regs]; exact ha σ c hJ
    have hex := exec_ldop hc (by rw [ha']; exact hFr _ hD a hw)
    rw [ha', access_agrees (agrees_of_decls hdc _ _)] at hex
    have hpc4 : ∀ m, (after s 4 m).st.2 = p + Int64.ofNat 4 := fun _ => by rw [← hpc]
    obtain ⟨hT', hown, htk⟩ := rmw_facts (Λ := ret0Λ) (own := own) (Tk := Tk) (s := s) (k := kk)
      (nr := (RegOrZr.low (.reg rt) .W64 : RegOrZr .W64).isZr)
      (op := fun old => some ((op.apply (old.setWidth 64) (s.st.1.regs.getRegOrZr (.low (.reg rs) .W64))).setWidth 128))
      (m := fun v => { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg rt) .W64) (v.setWidth 64) })
      (ret0Words_mapped hw).1 (fun _ => next_tk hpc (by rw [hT, hT4]) _) (by rw [own_at hpc]; exact hin)
      (fun v hv => by
        rw [own_at hpc, own_at (hpc4 _), Option.getD_some, hA.regs]
        rw [own_at hpc] at hv
        exact ownUpd_of (hupd σ c hJ) v hv)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro imm h; cases h) hex hT' hown htk hO

/-- **A node at an owned word's `swp<k> Xs, Xt, [Xn]`** before the take,
its next pc before it too: the word `a` (`ha`), owned at `p` (`hin`), set to
`Xs` at the next pc (`hupd`). -/
theorem nodeW_swp_pre {n : ND} {kk : RmwKind} {rs rt b : XReg} {l : Label} {k : Nat} {p : Int64}
    {a : BitVec 64}
    (hb : blockAt ret0Prog l k
      [.instr ⟨.W64, .SWP kk .W64 (.low (.reg rs) .W64) (.low (.reg rt) .W64) (.low (.reg b) .W64)⟩] = true)
    (he : labT l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hT4 : bT (p + Int64.ofNat 4).toBitVec.toNat = true)
    (ha : ∀ σ c, n.J σ c → (σ.regs.getXReg b).toBitVec = a) (hw : a ∈ ret0Words) (hFr : ∀ m, F m → ret0F m)
    (hin : ∃ v, (⟨a, 8⟩, v) ∈ ownOf (ph p.toBitVec.toNat))
    (hupd : ∀ σ c, n.J σ c → ownUpdB (ownOf (ph p.toBitVec.toNat)) (ownOf (ph (p + Int64.ofNat 4).toBitVec.toNat))
      ⟨a, 8⟩ (fun _ => (σ.regs.getRegOrZr (.low (.reg rs) .W64)).setWidth 128) = true) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  nodeW_pre hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellT hb he hs hn hpc
    have ha' : (s.st.1.regs.getXReg b).toBitVec = a := by rw [hA.regs]; exact ha σ c hJ
    have hex := exec_swp hc (by rw [ha']; exact hFr _ hD a hw)
    rw [ha', access_agrees (agrees_of_decls hdc _ _)] at hex
    have hpc4 : ∀ m, (after s 4 m).st.2 = p + Int64.ofNat 4 := fun _ => by rw [← hpc]
    obtain ⟨hT', hown, htk⟩ := rmw_facts (Λ := ret0Λ) (own := own) (Tk := Tk) (s := s) (k := kk)
      (nr := (RegOrZr.low (.reg rt) .W64 : RegOrZr .W64).isZr)
      (op := fun _ => some ((s.st.1.regs.getRegOrZr (.low (.reg rs) .W64)).setWidth 128))
      (m := fun v => { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg rt) .W64) (v.setWidth 64) })
      (ret0Words_mapped hw).1 (fun _ => next_tk hpc (by rw [hT, hT4]) _) (by rw [own_at hpc]; exact hin)
      (fun v hv => by
        rw [own_at hpc, own_at (hpc4 _), Option.getD_some, hA.regs]
        rw [own_at hpc] at hv
        exact ownUpd_of (hupd σ c hJ) v hv)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro imm h; cases h) hex hT' hown htk hO

/-- **A node at a load `ldr Xt, [Xn, #i]` of a word of `ret0Words`**
before the take, its next pc in its phase. -/
theorem nodeW_ldr_pre {n : ND} {t b : XReg} {i : Int64} {l : Label} {k : Nat} {p : Int64} {a : BitVec 64}
    (hb : blockAt ret0Prog l k [ldrDir t b i] = true) (he : labT l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat)
    (ha : ∀ σ c, n.J σ c → rAddr σ.regs b i = a) (hw : a ∈ ret0Words) (hFr : ∀ m, F m → ret0F m) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  nodeW_pre hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellT hb he hs hn hpc
    have ha' : rAddr s.st.1.regs b i = a := by rw [hA.regs]; exact ha σ c hJ
    have hex := exec_ldr_agrees hc ha' (hFr _ hD a hw) (agrees_of_decls hdc _ _)
    obtain ⟨hT', hown, htk⟩ := load_facts (Λ := ret0Λ) (own := own) (Tk := Tk) (k := .plain) (s := s)
      (m := fun v => { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) (v.setWidth 64) })
      (ret0Words_mapped hw).2.1 (fun _ => (next_same hpc hph _).2) (fun _ => (next_same hpc hph _).1)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro imm h; cases h) hex hT' hown htk hO

/-- **A node at an owned word's release store `stlr Xt, [Xn]`** before the
take, its next pc before it too: the word `a` (`ha`), owned at `p` (`hin`),
set to `Xt` at the next pc (`hupd`). -/
theorem nodeW_stlr_pre {n : ND} {t b : XReg} {l : Label} {k : Nat} {p : Int64} {a : BitVec 64}
    (hb : blockAt ret0Prog l k [.instr ⟨.W64, .STLR .W64 (.low (.reg t) .W64) (.low (.reg b) .W64)⟩] = true)
    (he : labT l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hT4 : bT (p + Int64.ofNat 4).toBitVec.toNat = true)
    (ha : ∀ σ c, n.J σ c → (σ.regs.getXReg b).toBitVec = a) (hw : a ∈ ret0Words) (hFr : ∀ m, F m → ret0F m)
    (hin : ∃ v, (⟨a, 8⟩, v) ∈ ownOf (ph p.toBitVec.toNat))
    (hupd : ∀ σ c, n.J σ c → ownUpdB (ownOf (ph p.toBitVec.toNat)) (ownOf (ph (p + Int64.ofNat 4).toBitVec.toNat))
      ⟨a, 8⟩ (fun _ => (σ.regs.getRegOrZr (.low (.reg t) .W64)).setWidth 128) = true) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  nodeW_pre hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellT hb he hs hn hpc
    have ha' : (s.st.1.regs.getXReg b).toBitVec = a := by rw [hA.regs]; exact ha σ c hJ
    have hex := exec_stlr_agrees hc (by rw [ha']; exact hFr _ hD a hw) (agrees_of_decls hdc _ _)
    rw [ha'] at hex
    have hpc4 : (after s 4 s.st.1).st.2 = p + Int64.ofNat 4 := by rw [← hpc]
    obtain ⟨v, hv⟩ := hin
    obtain ⟨hT', hown, htk⟩ := store_facts (Λ := ret0Λ) (own := own) (Tk := Tk) (k := .rel) (s := s)
      (m := s.st.1) (V := (s.st.1.regs.getRegOrZr (.low (.reg t) .W64)).setWidth 128) (ret0Words_mapped hw).1
      (next_tk hpc (by rw [hT, hT4]) _)
      (.inr (by rw [own_at hpc, own_at hpc4, hA.regs]; exact ownUpd_of (hupd σ c hJ) v hv))
    exact sfacts_ev (hC σ c hJ) hP hc (by intro imm h; cases h) hex hT' hown htk hO

/-- **A node of the main path after the take**, at `p` off the sites: as
`nodeW_pre`, its frame condition also `StackM rS` and `rS` in the pool
(`hsub`), so its states own the range. -/
theorem nodeW_post {n : ND} {p : Int64} (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hsub : rS.Sub ret0Λ.stackPool)
    (h : ∀ s c σ, s.exe = ret0Exe → s.endPc = ret0End → s.decls = {} → s.st.2 = p → Abs R n.o s.st.1 σ →
      F s.st.1 → n.J σ c → PcOff μ0 s → (Tk s → Owned ret0Λ rS s) → Wr rS s c) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R (fun m => F m ∧ StackM rS m) n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hP := pcOff_of_okPc (rS := rS) s (by unfold pcOf; rw [hpc]; exact hok)
  refine ⟨h s c σ hs hn hdc hpc hA hD.1 hJ hP.1 fun _ => ⟨hsub, fun a h8 ha ha7 => ?_⟩, hP.2⟩
  unfold Scc.Sem.A64.privLoad
  rw [Option.isSome_map]
  exact hD.2 a h8 ha ha7

/-- **A node of the main path after the take**, in a region whose frame
condition gives the words of `rS` off it (`hFO`): as `nodeW_post`. -/
theorem nodeW_postO {n : ND} {p : Int64} (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hR : R.OK) (hb : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub ret0Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (h : ∀ s c σ, s.exe = ret0Exe → s.endPc = ret0End → s.decls = {} → s.st.2 = p → Abs R n.o s.st.1 σ →
      F s.st.1 → n.J σ c → PcOff μ0 s → (Tk s → Owned ret0Λ rS s) → Wr rS s c) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hP := pcOff_of_okPc (rS := rS) s (by unfold pcOf; rw [hpc]; exact hok)
  refine ⟨h s c σ hs hn hdc hpc hA hD hJ hP.1 fun _ => owned_off hR hb hl hh hsub (hFO _ hD) fun k hk => ?_, hP.2⟩
  obtain ⟨j, hj, -⟩ := hA.slot k hk
  rw [hj]; rfl

/-- **A node at a load `ldr Xt, [Xn, #i]` of a word of `ret0Words`** after
the take, unmapped in private memory under the frame condition (`hun`), as
`nodeW_postO`, its next pc in its phase. -/
theorem nodeW_ldr_postO {n : ND} {t b : XReg} {i : Int64} {l : Label} {k : Nat} {p : Int64} {a : BitVec 64}
    (hb : blockAt ret0Prog l k [ldrDir t b i] = true) (he : labT l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat)
    (ha : ∀ σ c, n.J σ c → rAddr σ.regs b i = a) (hw : a ∈ ret0Words)
    (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub ret0Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  nodeW_postO hp hok hR hR8 hl hh hsub hFO fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellT hb he hs hn hpc
    have ha' : rAddr s.st.1.regs b i = a := by rw [hA.regs]; exact ha σ c hJ
    have hex := exec_ldr_agrees hc ha' (hun _ hD) (agrees_of_decls hdc _ _)
    obtain ⟨hT', hown, htk⟩ := load_facts (Λ := ret0Λ) (own := own) (Tk := Tk) (k := .plain) (s := s)
      (m := fun v => { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) (v.setWidth 64) })
      (ret0Words_mapped hw).2.1 (fun _ => (next_same hpc hph _).2) (fun _ => (next_same hpc hph _).1)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro imm h; cases h) hex hT' hown htk hO

/-- `rt_sigaction`'s number is in `x8` at `scc_rt_start`'s system call. -/
theorem startS2_x8 (lab : Label → Int64) (σ : AS) : (startS2 lab σ).regs.X8.toNat = 134 := by
  simp [startS2, startArgs_run]; rfl

/-- **A node at `svc #0`** after the take, as `nodeW_postO`, its next pc in
its phase, its `x8` not `write`'s number (`hnr`). -/
theorem nodeW_svc_postO {n : ND} {l : Label} {k : Nat} {p : Int64}
    (hb : blockAt ret0Prog l k [svcDir] = true) (he : labT l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub ret0Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (hnr : ∀ σ c, n.J σ c → σ.regs.X8.toNat ≠ 64) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  nodeW_postO hp hok hR hR8 hl hh hsub hFO fun _s c σ hs hn _ hpc hA _ hJ hP hO =>
    sfacts_svc (hC σ c hJ) hP (cellT hb he hs hn hpc) (next_same hpc hph) hO
      (decode_ne_write _ (by show _s.st.1.regs.X8.toNat ≠ 64; rw [hA.regs]; exact hnr σ c hJ))

/-- **A node at a register operation** after the take, the range in private
memory, its next pc in its phase. -/
theorem nodeW_reg_post {n : ND} {w : RegWidth} {op : Operation w} {l : Label} {k : Nat} {p : Int64}
    (hop : RegOnly op = true) (hb : blockAt ret0Prog l k [.instr ⟨w, op⟩] = true)
    (he : labT l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat) (hsub : rS.Sub ret0Λ.stackPool) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R (fun m => F m ∧ StackM rS m) n :=
  nodeW_post hp hok hsub fun s c σ hs hn _ hpc _ _ hJ hP hO => by
    have hc := cellT hb he hs hn hpc
    exact sfacts_done (hC σ c hJ) hP hc (fun imm h => by cases h; simp [RegOnly] at hop) (exec_reg hop hc)
      (next_same hpc hph _).1 (next_same hpc hph _).2 hO

/-- **A node at a single instruction without an event** (`SI`) after the
take, its next pc in its phase. -/
theorem nodeW_si_post {n : ND} {si : SI} {l : Label} {k : Nat} {p : Int64}
    (hb : blockAt ret0Prog l k [si.toDir] = true) (he : labT l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat) (hsub : rS.Sub ret0Λ.stackPool) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R (fun m => F m ∧ StackM rS m) n :=
  nodeW_post hp hok hsub fun _s c σ hs hn _ hpc _ _ hJ hP hO =>
    sfacts_si (hC σ c hJ) hP (cellT hb he hs hn hpc) (next_same hpc hph) hO

/-- **A node at `svc #0`** before the take, its next pc in its phase, its
`x8` not `write`'s number (`hnr`). -/
theorem nodeW_svc_pre {n : ND} {l : Label} {k : Nat} {p : Int64}
    (hb : blockAt ret0Prog l k [svcDir] = true) (he : labT l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat)
    (hnr : ∀ σ c, n.J σ c → σ.regs.X8.toNat ≠ 64) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  nodeW_pre hp hok hT fun _s c σ hs hn _ hpc hA _ hJ hP hO =>
    sfacts_svc (hC σ c hJ) hP (cellT hb he hs hn hpc) (next_same hpc hph) hO
      (decode_ne_write _ (by show _s.st.1.regs.X8.toNat ≠ 64; rw [hA.regs]; exact hnr σ c hJ))

/-- **A node at a runtime store** `str Xt, [Xn, #i]` to a word of
`ret0Words` no phase owns, after the take, its next pc in its phase. -/
theorem nodeW_st_post {n : ND} {t b : XReg} {i : Int64} {l : Label} {k : Nat} {p : Int64} {a : BitVec 64}
    (hb : blockAt ret0Prog l k [strDir t b i] = true) (he : labT l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat)
    (ha : ∀ σ c, n.J σ c → rAddr σ.regs b i = a) (hw : a ∈ ret0Words) (hFr : ∀ m, F m → ret0F m)
    (hno : ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j) (hsub : rS.Sub ret0Λ.stackPool) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R (fun m => F m ∧ StackM rS m) n :=
  nodeW_post hp hok hsub fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellT hb he hs hn hpc
    have ha' : rAddr s.st.1.regs b i = a := by rw [hA.regs]; exact ha σ c hJ
    have hex := exec_str_agrees hc ha' (hFr _ hD a hw) (agrees_of_decls hdc _ _)
    obtain ⟨hT', hown, htk⟩ := store_facts (Λ := ret0Λ) (own := own) (Tk := Tk) (k := .plain) (s := s)
      (m := s.st.1) (V := (s.st.1.regs.getRegOrZr (.low (.reg t) .W64)).setWidth 128) (ret0Words_mapped hw).1
      (next_same hpc hph _).2 (.inl ⟨(next_same hpc hph _).1, fun w h => by rw [own_at hpc] at h; exact hno _ w h⟩)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro imm h; cases h) hex hT' hown htk hO

end Node

/-! ## `scc_rt_alloc_tcb` -/

section Tcb

open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0.Mem (ret0Exe ret0End ret0F)

variable {rS : Range} {c0 : Ctl} {F : MachineData → Prop}

theorem labT_pnA : pnA labT = 6291472#64 := by rw [← ret0_labT]; exact Mem.ret0_pnA
theorem labT_pinA : pinA labT = 134217728#64 := by rw [← ret0_labT]; exact Mem.ret0_pinA
theorem labT_lockA : lockA labT = 6291496#64 := by rw [← ret0_labT]; exact Mem.ret0_lockA
theorem labT_freeNA : freeNA labT = 6291504#64 := by rw [← ret0_labT]; exact Mem.ret0_freeNA
theorem labT_nextA : nextA labT = 6291488#64 := by rw [← ret0_labT]; exact Mem.ret0_nextA

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
(`hC0`, its facts) and the frame condition implying `ret0F`. -/
theorem tcbW (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → ret0F m) (q : TcbG)
    (hq : q.c0 = c0) (hn0 : q.n0 = 0#64) (hra : q.g.ra = (labT ".L0_scc_rt_start.sp2").toBitVec) :
    ∀ i, TcbW (Wr rS) (Kr rS) ret0Exe ret0End R F q i := by
  intro i
  cases i
  case e => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.fnL 0 AllocTcb.atPro_ok
  case entry =>
    show BlkW _ _ _ _ _ _ _ _
    rw [ret0_labT]
    exact blkW_pre (l := AllocTcb.entryL) (k := 0) (dead := fun t => t == 4195200) (ra := 0) (by decide +kernel)
      rfl AllocTcb.atChk_ok hR hal (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim)
      (fun _ _ hJ => by dsimp only [tcbN] at hJ ⊢; rw [(AllocTcb.atChk_walk labT _ hJ.2).1]; decide +kernel)
      (by decide +kernel)
  case j1 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.entryL 4 AllocTcb.atJ1_ok
  case len => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.lenL 0 AllocTcb.atLen_ok
  case adrp => show NodeW _ _ _ _ _ _ _; rw [ret0_labT]; tsi (SI.adrp .X9 "scc_rt_pinned_next") AllocTcb.lenL 32
  case add => show NodeW _ _ _ _ _ _ _; rw [ret0_labT]; tsi (SI.addLo12 .X9 .X9 "scc_rt_pinned_next") AllocTcb.lenL 33
  case arg => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.lenL 34 AllocTcb.atArg_ok
  case rmw =>
    show NodeW _ _ _ _ _ _ _
    rw [ret0_labT]
    refine nodeW_ldop_pre (op := .ADD) (kk := .acqRel) (rs := .X9) (rt := .X11) (b := .X10) (l := AllocTcb.lenL)
      (k := 37) (by decide +kernel) rfl rfl
      (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fun σ _ hJ => by show σ.regs.X10.toBitVec = _; exact hJ.2.2.2.trans labT_pnA) (by decide) hFr
      ⟨_, .head _⟩ fun σ _ hJ => ?_
    rw [Spike.Lib.A64.Alloc.getRegOrZr_x]
    simp only [Reg64s.getXReg]
    rw [hJ.2.2.1]
    decide +kernel
  case bnd => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.lenL 38 AllocTcb.atBnd_ok
  case j2 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.lenL 47 AllocTcb.atJ2_ok
  case ok => show NodeW _ _ _ _ _ _ _; rw [ret0_labT]; tsi (SI.adrp .X9 "scc_rt_pinned") AllocTcb.okL 0
  case ok1 => show NodeW _ _ _ _ _ _ _; rw [ret0_labT]; tsi (SI.addLo12 .X9 .X9 "scc_rt_pinned") AllocTcb.okL 1
  case ok2 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.okL 2 AllocTcb.atOk_ok
  case hdr =>
    show NodeW _ _ _ _ _ _ _
    rw [ret0_labT]
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
    rw [ret0_labT]
    exact blkW_pre (l := AllocTcb.okL) (k := 30) (dead := fun _ => false) (ra := labT ".L0_scc_rt_start.sp2")
      (by decide +kernel) rfl AllocTcb.atRet_ok hR hal (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0)
      (by decide +kernel)
      (hret_of_run AllocTcb.atRet_ok fun _ _ hJ => by
        dsimp only [tcbN] at hJ ⊢
        rw [(AllocTcb.atRet_walk labT _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ _ _ => rfl) (by decide +kernel)

end Tcb

/-! ## `scc_rt_stack_take` -/

section Take

open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0.Mem (ret0Exe ret0End ret0F)

variable {rS : Range} {c0 : Ctl} {F : MachineData → Prop}

set_option hygiene false in
/-- A block of `scc_rt_stack_take` before the take, no `ret`, no dead target. -/
local macro "kblk " l:term:max k:term:max ok:term:max : tactic =>
  `(tactic| exact blkW_pre (l := $l) (k := $k) (dead := fun _ => false) (ra := 0) (by decide +kernel) rfl $ok
    hR hal (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel)
    (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim) (fun _ _ _ => rfl) (by decide +kernel))

set_option hygiene false in
/-- A label address pair of `scc_rt_stack_take`: its `adrp` and its `add`. -/
local macro "kpair " L:term:max l:term:max k:term:max : tactic =>
  `(tactic| focus
    show NodeW _ _ _ _ _ _ _ ∧ NodeW _ _ _ _ _ _ _
    rw [ret0_labT]
    exact ⟨nodeW_si_pre (si := SI.adrp .X9 $L) (l := $l) (k := $k) (p := labT $l + Int64.ofNat (4 * $k))
      (by decide +kernel) rfl (by first | rfl | exact (Spike.Lib.A64.Flow.ofNat4_zero _).symm)
      (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    nodeW_si_pre (si := SI.addLo12 .X9 .X9 $L) (l := $l) (k := $k + 1)
      (p := labT $l + Int64.ofNat (4 * ($k + 1)))
      (by decide +kernel) rfl (ofNat4_succ' _ _) (fun _ _ ⟨_, hJ, _⟩ => hJ.1 ▸ hq ▸ hC0)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩)

/-- **The take site is `μ0`'s.** -/
theorem mu0_take : μ0.site .take = some (labT StackTake.siteL).toBitVec.toNat := by
  decide +kernel

/-- **The take site's states are inside `Wr`**: the `nop` at the take site,
not in the take's phase, the take landing in it with the owned words
unchanged, given the source control `c0` (`hC0`, its facts), the range
named by the site's registers (`hrS`: `x0 = stacksA + k0`, `x1 = 16384`) in
the pool (`hsub`). The `nop` as an instruction is asked off the transfer
sites only (`SFacts.tkInstr`), and this pc is `μ0`'s take site (`mu0_take`). -/
theorem takeSiteW (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region} (q : TakeG) (hq : q.c0 = c0)
    (hrS : rS = ⟨(stacksA labT + q.k0).toNat, 16384⟩) (hsub : rS.Sub ret0Λ.stackPool) :
    TakeW (Wr rS) (Kr rS) ret0Exe ret0End R F (StackM rS) q .site := by
  dsimp only [TakeW]
  rw [ret0_labT]
  rintro s c ⟨hs, hn, -, hpc, σ, hA, -, hc, -, h0, h1⟩
  have hcl := cellT (l := StackTake.siteL) (k := 0) (d := .instr ⟨.W64, .NOP⟩) (by decide +kernel) (ofNat4_zero _)
    hs hn hpc
  have hpcN : pcOf s = (labT StackTake.siteL).toBitVec.toNat := by unfold pcOf; rw [hpc]; rfl
  have hpcV : pcOf s = 4196192 := by rw [hpcN]; decide +kernel
  have hpc4 : ∀ m, (Kraken.Promising.Lower.A64.after s 4 m).st.2 = labT StackTake.siteL + Int64.ofNat 4 := fun _ => by
    show s.st.2 + Int64.ofNat 4 = _; rw [hpc]; rfl
  refine sfacts_site (hc ▸ hq ▸ hC0) (fun a ha => ?_) (fun k a ha => ?_) hcl
    (not_tk (by rw [hpcV]; decide)) ⟨?_, hsub, by rw [hrS]; show 0 < 16384; decide,
      by unfold Scc.Sem.Range.Disjoint; decide +kernel⟩ (fun m => ?_)
    (fun m => ?_) (by rw [hpcN]; exact mu0_take)
  · cases ha; rw [hpcV]; decide
  · cases k <;> cases ha <;> rw [hpcV] <;> decide
  · show (⟨s.st.1.regs.X0.toBitVec.toNat, s.st.1.regs.X1.toBitVec.toNat⟩ : Range) = rS
    rw [hA.regs, h0, h1, hrS]; rfl
  · rw [own_at (hpc4 m), own_at hpc]
    exact (by decide +kernel : ownOf (ph (labT StackTake.siteL + Int64.ofNat 4).toBitVec.toNat) =
      ownOf (ph (labT StackTake.siteL).toBitVec.toNat))
  · show ph (Scc.Sem.A64.nextPc (Scc.Sem.A64.abi.setDmem s m)).toBitVec.toNat / 8 % 2 = 0
    rw [Scc.Sem.A64.nextPc_of_cellAt (st := Scc.Sem.A64.abi.setDmem s m) ⟨hcl.valid, hcl.ne, hcl.code⟩]
    show ph (s.st.2 + Int64.ofNat 4).toBitVec.toNat / 8 % 2 = 0
    rw [hpc]
    show ph (labT StackTake.siteL + Int64.ofNat 4).toBitVec.toNat / 8 % 2 = 0
    decide +kernel

set_option maxHeartbeats 800000 in
/-- **`scc_rt_stack_take`'s states are inside `Wr`**, in any region holding
its frame, returning to `scc_rt_thread_init`'s `.sp0` (`hra`), with the
source control `c0` (`hC0`, its facts), the frame condition implying
`ret0F`, and past the take `rS` in the pool (`hsub`) and kept by the
region's writes (`hSM`). The take site's obligation is `hsite`. -/
theorem takeW (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -208) (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → ret0F m) (q : TakeG)
    (hq : q.c0 = c0) (hra : q.g.ra = (labT ".L5_scc_rt_thread_init.sp0").toBitVec)
    (hsub : rS.Sub ret0Λ.stackPool) (hSM : FStable R (StackM rS))
    (hsite : TakeW (Wr rS) (Kr rS) ret0Exe ret0End R F (StackM rS) q .site) :
    ∀ i, TakeW (Wr rS) (Kr rS) ret0Exe ret0End R F (StackM rS) q i := by
  intro i
  cases i
  case site => exact hsite
  case e => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; kblk StackTake.fnL 0 StackTake.stPro_ok
  case entry => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; kblk StackTake.entryL 0 StackTake.stInit_ok
  case cls => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; kblk StackTake.clsL 0 StackTake.stCls_ok
  case j1 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; kblk StackTake.clsL 4 StackTake.stJ1_ok
  case d0 => kpair "scc_rt_stack_free_n" StackTake.doneL 0
  case d2 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; kblk StackTake.doneL 2 StackTake.stFreeN_ok
  case d7 => kpair "scc_rt_stack_free" StackTake.doneL 7
  case d9 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; kblk StackTake.doneL 9 StackTake.stFree_ok
  case d14 => kpair "scc_rt_stack_lock" StackTake.doneL 14
  case d16 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; kblk StackTake.doneL 16 StackTake.stLock_ok
  case sp0 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; kblk StackTake.spinL 0 StackTake.stSwp_ok
  case swp =>
    show NodeW _ _ _ _ _ _ _
    rw [ret0_labT]
    refine nodeW_swp_pre (kk := .acqRel) (rs := .X9) (rt := .X11) (b := .X10) (l := StackTake.spinL) (k := 2)
      (a := 6291496#64) (by decide +kernel) rfl rfl
      (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fun σ _ hJ => by show σ.regs.X10.toBitVec = _; exact hJ.2.2.2.trans labT_lockA) (by decide) hFr
      ⟨_, .tail _ (.head _)⟩ fun σ _ hJ => ?_
    rw [Spike.Lib.A64.Alloc.getRegOrZr_x]
    simp only [Reg64s.getXReg]
    rw [hJ.2.2.1]
    decide +kernel
  case sp3 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; kblk StackTake.spinL 3 StackTake.stSpin_ok
  case lk0 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; kblk StackTake.lockedL 0 StackTake.stLdN_ok
  case ldn =>
    show NodeW _ _ _ _ _ _ _
    rw [ret0_labT]
    exact nodeW_ldr_pre (t := .X9) (b := .X10) (i := 0) (l := StackTake.lockedL) (k := 1) (a := 6291504#64)
      (by decide +kernel) rfl rfl
      (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fun σ _ hJ => by rw [rAddr_x10 hJ.2.2, labT_freeNA]; decide) (by decide) hFr
  case lk2 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; kblk StackTake.lockedL 2 StackTake.stEmpty_ok
  case b0 => kpair "scc_rt_stack_lock" StackTake.bumpL 0
  case b2 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; kblk StackTake.bumpL 2 StackTake.stUnl_ok
  case unl =>
    show NodeW _ _ _ _ _ _ _
    rw [ret0_labT]
    refine nodeW_stlr_pre (t := .X9) (b := .X10) (l := StackTake.bumpL) (k := 5) (a := 6291496#64)
      (by decide +kernel) rfl rfl
      (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fun σ _ hJ => by show σ.regs.X10.toBitVec = _; exact hJ.2.2.2.trans labT_lockA) (by decide) hFr
      ⟨_, .tail _ (.head _)⟩ fun σ _ hJ => ?_
    rw [Spike.Lib.A64.Alloc.getRegOrZr_x]
    simp only [Reg64s.getXReg]
    rw [hJ.2.2.1]
    decide +kernel
  case b6 => kpair "scc_rt_stack_next" StackTake.bumpL 6
  case b8 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; kblk StackTake.bumpL 8 StackTake.stAdd_ok
  case nxt =>
    show NodeW _ _ _ _ _ _ _
    rw [ret0_labT]
    refine nodeW_ldop_pre (op := .ADD) (kk := .acqRel) (rs := .X9) (rt := .X11) (b := .X10) (l := StackTake.bumpL)
      (k := 11) (a := 6291488#64) (by decide +kernel) rfl rfl
      (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fun σ _ hJ => by show σ.regs.X10.toBitVec = _; exact hJ.2.2.2.trans labT_nextA) (by decide +kernel) hFr
      ⟨_, .tail _ (.tail _ (.tail _ (.head _)))⟩ fun σ _ hJ => ?_
    rw [Spike.Lib.A64.Alloc.getRegOrZr_x]
    simp only [Reg64s.getXReg]
    rw [hJ.2.2.1]
    decide +kernel
  case b12 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; kblk StackTake.bumpL 12 StackTake.stBnd_ok
  case b21 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; kblk StackTake.bumpL 21 StackTake.stJ2_ok
  case ok0 => kpair "scc_rt_stacks" StackTake.okL 0
  case ok2 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; kblk StackTake.okL 2 StackTake.stOk_ok
  case tk => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; kblk StackTake.takenL 0 StackTake.stSite_ok
  case ret =>
    dsimp only [TakeW]
    rw [ret0_labT]
    exact blkW_post (l := StackTake.siteL) (k := 1) (dead := fun _ => false)
      (ra := labT ".L5_scc_rt_thread_init.sp0") (by decide +kernel) rfl StackTake.stRet_ok hR hal (by omega)
      (by omega) (fun _ _ hJ => hJ.2.1 ▸ hq ▸ hC0) (by decide +kernel)
      (hret_of_run StackTake.stRet_ok fun _ _ hJ => by
        dsimp only [takeNG] at hJ ⊢
        rw [(StackTake.stRet_walk labT _ hJ.2.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ _ _ => rfl) hsub hSM

end Take

/-! ## `scc_rt_thread_init` -/

section Ti

open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0.Mem (ret0Exe ret0End ret0F)

variable {rS : Range} {c0 : Ctl} {F : MachineData → Prop}

set_option hygiene false in
/-- A block of `scc_rt_thread_init` after the take, no `ret`, no dead target. -/
local macro "iblk " k:term:max ok:term:max : tactic =>
  `(tactic| focus
    dsimp only [TiW]
    rw [ret0_labT]
    exact blkW_post (l := ThreadInit.spL) (k := $k) (dead := fun _ => false) (ra := 0) (by decide +kernel)
      (by first | rfl | exact (Spike.Lib.A64.Flow.ofNat4_zero _)) $ok hR hal (by omega) (by omega)
      (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim) (fun _ _ _ => rfl) hsub hSM)

set_option hygiene false in
/-- A store of a TCB field of `scc_rt_thread_init`, after the take. -/
local macro "ist " j:term:max : tactic =>
  `(tactic| focus
    dsimp only [TiW]
    rw [ret0_labT]
    exact nodeW_st_post (t := .X9) (b := .X10) (i := Int64.ofNat (8 * $j)) (l := ThreadInit.spL)
      (k := 11 + 3 * $j) (a := 134217736#64 + BitVec.ofNat 64 (8 * $j)) (by decide +kernel) rfl rfl
      (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel) (by decide +kernel)
      (fun σ _ hJ => by rw [rAddr_x10 (hJ.2.2.2.trans htcb)]; decide) (by decide +kernel) hFr
      (not_own (by decide +kernel)) hsub)

set_option maxHeartbeats 800000 in
/-- **`scc_rt_thread_init`'s states are inside `Wr`**, in any region
holding its frame and the take's below, returning to `scc_rt_start`'s
`.sp3` (`hra`), with the TCB past `scc_rt_pinned`'s header (`htcb`), the source control
`c0` (`hC0`, its facts), the frame condition implying `ret0F`, and past the
take `rS` in the pool (`hsub`) and kept by the writes of both regions
(`hSM`, `hSM'`). The take site's obligation, for every ghost of the call,
is `hsite`. -/
theorem tiW (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -256) (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → ret0F m) (q : TiG)
    (hq : q.c0 = c0) (hra : q.g.ra = (labT ".L0_scc_rt_start.sp3").toBitVec) (htcb : q.tcb = 134217736#64)
    (hsub : rS.Sub ret0Λ.stackPool) (hSM : FStable R (StackM rS))
    (hSM' : FStable (R.callee ThreadInit.oI.sp (-208) 0) (StackM rS))
    (hsite : ∀ g : StackTake.G, g.ra = (labT ThreadInit.spL).toBitVec →
      TakeW (Wr rS) (Kr rS) ret0Exe ret0End (R.callee ThreadInit.oI.sp (-208) 0) F (StackM rS) (tiTake q g) .site) :
    ∀ i, TiW (Wr rS) (Kr rS) ret0Exe ret0End R F (StackM rS) q i := by
  intro i
  cases i
  case e =>
    show BlkW _ _ _ _ _ _ _ _
    rw [ret0_labT]
    exact blkW_pre (l := ThreadInit.fnL) (k := 0) (dead := fun _ => false) (ra := 0) (by decide +kernel) rfl
      ThreadInit.tiPro_ok hR hal (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim) (fun _ _ _ => rfl) (by decide +kernel)
  case entry =>
    show BlkW _ _ _ _ _ _ _ _
    rw [ret0_labT]
    exact blkW_pre (l := ThreadInit.entryL) (k := 0) (dead := fun _ => false) (ra := 0) (by decide +kernel) rfl
      ThreadInit.tiCall_ok hR hal (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim) (fun _ _ _ => rfl) (by decide +kernel)
  case call =>
    intro g hg j
    have hlo' : R.lo ≤ ThreadInit.oI.sp + -208 := by show R.lo ≤ -48 + -208; omega
    have hkc : ThreadInit.oI.sp < R.hi := by show (-48 : Int) < R.hi; omega
    have hR' := Region.callee_ok (hi' := 0) hR hlo' (by decide) hkc (by show (-48 : Int) + 0 ≤ R.hi; omega)
    have hb' := Region.callee_base (hi' := 0) hR hlo' (by decide) hkc
    have hal' : (R.callee ThreadInit.oI.sp (-208) 0).base.toNat % 16 = 0 := by
      have : (((R.callee ThreadInit.oI.sp (-208) 0).base.toNat : Int)) % 16 = 0 := by
        rw [hb']; show ((R.base.toNat : Int) + -48) % 16 = 0; omega
      omega
    rw [ret0_labT] at hg
    exact takeW hC0 hR' hal' (by show (-208 : Int) ≤ -208; omega) (by show (0 : Int) ≤ 0; omega) hFr
      (tiTake q g) hq hg hsub hSM' (hsite g hg) j
  case sp => iblk 0 ThreadInit.tiSp_ok
  case st0 => ist 0
  case f1 => iblk 12 ThreadInit.tiF1_ok
  case st1 => ist 1
  case f2 => iblk 15 ThreadInit.tiF2_ok
  case st2 => ist 2
  case f3 => iblk 18 ThreadInit.tiF3_ok
  case st3 => ist 3
  case f4 => iblk 21 ThreadInit.tiF4_ok
  case st4 => ist 4
  case f5 => iblk 24 ThreadInit.tiF5_ok
  case st5 => ist 5
  case ret =>
    dsimp only [TiW]
    rw [ret0_labT]
    exact blkW_post (l := ThreadInit.spL) (k := 27) (dead := fun _ => false)
      (ra := labT ".L0_scc_rt_start.sp3") (by decide +kernel) rfl ThreadInit.tiRet_ok hR hal (by omega)
      (by omega) (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel)
      (hret_of_run ThreadInit.tiRet_ok fun _ _ hJ => by
        dsimp only [tiN] at hJ ⊢
        rw [(ThreadInit.tiRet_walk labT _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ _ _ => rfl) hsub hSM

end Ti

/-! ## `scc_rt_start` up to the switch -/

section Start

open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0.Mem (ret0Exe ret0End ret0F)

variable {rS : Range} {c0 : Ctl} {F : MachineData → Prop}

/-- A callee's region at `kc` of a region holding it, `[lo', 0)`: its facts. -/
theorem callee_facts {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0) {kc lo' : Int}
    (hlo : R.lo ≤ kc + lo') (hlo0 : lo' ≤ 0) (hkc : kc < R.hi) (h16 : kc % 16 = 0) :
    (R.callee kc lo' 0).OK ∧ (R.callee kc lo' 0).base.toNat % 16 = 0 := by
  refine ⟨Region.callee_ok hR hlo hlo0 hkc (by omega), ?_⟩
  have hb := Region.callee_base (hi' := 0) hR hlo hlo0 hkc
  have : (((R.callee kc lo' 0).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
  omega

/-- **`scc_rt_start` up to `.sp2`: its states are inside `Wr`** (`Sp0W`),
in any region holding its frame and `scc_rt_alloc_tcb`'s below, at
`n0 = 0`, with the source control `c0` (`hC0`, its facts) and the frame
condition implying `ret0F`. -/
theorem sp0W (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -240) (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → ret0F m) {n0 : BitVec 64} (hn0 : n0 = 0#64) :
    Sp0W (Wr rS) (Kr rS) ret0Exe ret0End R F n0 c0 := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, fun g hg i => ?_⟩
  · show BlkW _ _ _ _ _ _ _ _
    rw [ret0_labT]
    exact blkW_pre (l := "scc_rt_start") (k := 0) (dead := fun _ => false) (ra := 0) (by decide +kernel)
      (ofNat4_zero _) Abort.b0_ok hR hal (by omega) (by omega) (fun _ _ hJ => hJ ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim) (fun _ _ _ => rfl) (by decide +kernel)
  · show NodeW _ _ _ _ _ _ _
    rw [ret0_labT]
    exact nodeW_si_pre (si := SI.adrp .X9 sigign) (l := startE) (k := 0) (p := labT startE + Int64.ofNat (4 * 0))
      (by decide +kernel) rfl (ofNat4_zero _).symm (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · show NodeW _ _ _ _ _ _ _
    rw [ret0_labT]
    exact nodeW_si_pre (si := SI.addLo12 .X9 .X9 sigign) (l := startE) (k := 1)
      (p := labT startE + Int64.ofNat (4 * 1)) (by decide +kernel) rfl rfl (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · show BlkW _ _ _ _ _ _ _ _
    rw [ret0_labT]
    exact blkW_pre (l := startE) (k := 2) (dead := fun _ => false) (ra := 0) (by decide +kernel)
      rfl startArgs_ok hR hal (by omega) (by omega) (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim) (fun _ _ _ => rfl) (by decide +kernel)
  · show NodeW _ _ _ _ _ _ _
    rw [ret0_labT]
    exact nodeW_svc_pre (l := startE) (k := 8) (p := labT startE + Int64.ofNat (4 * 8))
      (by decide +kernel) rfl rfl (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fun _ _ ⟨_, _, he⟩ => by rw [he, startS2_x8]; decide)
  · show BlkW _ _ _ _ _ _ _ _
    rw [ret0_labT]
    exact blkW_pre (l := startE) (k := 9) (dead := fun _ => false) (ra := 0) (by decide +kernel)
      rfl startCall_ok hR hal (by omega) (by omega) (fun _ _ hJ => hJ ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim) (fun _ _ _ => rfl) (by decide +kernel)
  · obtain ⟨hR', hal'⟩ := callee_facts (kc := Abort.oI.sp) (lo' := -192) hR hal
      (by show R.lo ≤ -48 + -192; omega) (by decide) (by show (-48 : Int) < R.hi; omega)
      (by decide)
    rw [ret0_labT] at hg
    exact tcbW hC0 hR' hal' (by show (-192 : Int) ≤ -192; omega) (by show (0 : Int) ≤ 0; omega) hFr
      ⟨g, n0, c0⟩ rfl hn0 hg i

/-- The TCB's address at `n0 = 0`. -/
theorem tcbA0 {n0 : BitVec 64} (hn0 : n0 = 0#64) : pinA labT + n0 + 8#64 = 134217736#64 := by
  rw [labT_pinA, hn0]; decide

/-- **`scc_rt_start` from `.sp2` to the switch: its states are inside
`Wr`** (`Sp2W`), in any region holding its frame and
`scc_rt_thread_init`'s and `scc_rt_stack_take`'s below, at `n0 = 0`, with
the source control `c0` (`hC0`, its facts), the frame condition implying
`ret0F`, and past the take `rS` in the pool (`hsub`) and kept by the
writes of the three regions (`hSM`, `hSMi`, `hSMt`). The take site's
obligation, for every ghost of both calls, is `hsite`. -/
theorem sp2W (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → ret0F m) {n0 k0 : BitVec 64} (hn0 : n0 = 0#64)
    (hsub : rS.Sub ret0Λ.stackPool) (hSM : FStable R (StackM rS))
    (hSMi : FStable (R.callee Abort.oI.sp (-256) 0) (StackM rS))
    (hSMt : FStable ((R.callee Abort.oI.sp (-256) 0).callee ThreadInit.oI.sp (-208) 0) (StackM rS))
    (hsite : ∀ g : ThreadInit.G, g.ra = (labT sp3L).toBitVec → ∀ g' : StackTake.G,
      g'.ra = (labT ThreadInit.spL).toBitVec →
      TakeW (Wr rS) (Kr rS) ret0Exe ret0End ((R.callee Abort.oI.sp (-256) 0).callee ThreadInit.oI.sp (-208) 0) F
        (StackM rS) (tiTake ⟨g, pinA labT + n0 + 8#64, k0, c0⟩ g') .site) :
    Sp2W (Wr rS) (Kr rS) ret0Exe ret0End R F rS n0 k0 c0 := by
  refine ⟨?_, fun g hg i => ?_, ?_, ?_⟩
  · show BlkW _ _ _ _ _ _ _ _
    rw [ret0_labT]
    exact blkW_pre (l := sp2L) (k := 0) (dead := fun _ => false) (ra := 0) (by decide +kernel)
      (ofNat4_zero _) startCall2_ok hR hal (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim) (fun _ _ _ => rfl) (by decide +kernel)
  · obtain ⟨hR', hal'⟩ := callee_facts (kc := Abort.oI.sp) (lo' := -256) hR hal
      (by show R.lo ≤ -48 + -256; omega) (by decide) (by show (-48 : Int) < R.hi; omega)
      (by decide)
    rw [ret0_labT] at hg ⊢
    exact tiW hC0 hR' hal' (by show (-256 : Int) ≤ -256; omega) (by show (0 : Int) ≤ 0; omega) hFr _ rfl hg
      (tcbA0 hn0) hsub hSMi hSMt (hsite g hg) i
  · show BlkW _ _ _ _ _ _ _ _
    rw [ret0_labT]
    exact blkW_post (l := sp3L) (k := 0) (dead := fun _ => false) (ra := 0) (by decide +kernel)
      (ofNat4_zero _) startSw0_ok hR hal (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim) (fun _ _ _ => rfl) hsub hSM
  · show NodeW _ _ _ _ _ _ _
    rw [ret0_labT]
    exact nodeW_si_post (si := SI.msr .X10) (l := sp3L) (k := 4) (p := labT sp3L + Int64.ofNat (4 * 4))
      (by decide +kernel) rfl rfl (fun _ _ hJ => hJ.1 ▸ hC0) (by decide +kernel) (by decide +kernel) hsub

end Start

/-! ## From the switch on: `scc_rt_main` and `wc_main` -/

section Main

open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0.Mem (ret0Exe ret0End ret0F)

variable {rS : Range} {c0 : Ctl}

/-- A block obligation under an unsatisfiable frame condition. -/
theorem blkW_false {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {n : ND} {blk : List Directive} (h : ∀ m, ¬ F m) :
    BlkW W K exe endPc R F n blk :=
  fun _ _ _ _ _ _ _ _ hD _ => (h _ hD).elim

/-- A node obligation under an unsatisfiable frame condition. -/
theorem nodeW_false {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {n : ND} (h : ∀ m, ¬ F m) : NodeW W K exe endPc R F n :=
  fun _ _ ⟨_, _, _, _, _, _, hD, _⟩ => (h _ hD).elim

/-- `scc_rt_main`'s obligations under an unsatisfiable frame condition. -/
theorem mainW_false {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} {g : MainG} (h : ∀ m, ¬ F m) :
    MainW W K exe endPc R F ms g :=
  have h' : ∀ m, ¬ (F m ∧ CallerCells R (-48) (-32) 0 m) := fun m hm => h m hm.1
  ⟨⟨blkW_false h, nodeW_false h, blkW_false h, blkW_false h⟩, blkW_false h,
    fun _ _ _ _ => ⟨⟨blkW_false h', nodeW_false h', blkW_false h', blkW_false h'⟩, ⟨blkW_false h', blkW_false h'⟩⟩,
    ⟨blkW_false h, nodeW_false h⟩⟩

/-- The TCB's limit word at `n0 = 0`. -/
theorem limA_tcb0 : limA (UInt64.ofBitVec 134217736#64) = 134217744#64 := by decide

/-- The limit load's address, the thread pointer the TCB. -/
theorem rAddr_lim {r : Reg64s} (Z : Int64) (h : r.TPIDR_EL0 = UInt64.ofBitVec 134217736#64) :
    rAddr (chkRegs Z r) .X10 8 = 134217744#64 := by
  rw [rAddr_chkRegs, tcbA_limA h, limA_tcb0]

/-- Closes a closed fact about the switch's region or its callee's. -/
local macro "rdec" : tactic => `(tactic| (try dsimp only [swR, Region.callee]) <;> decide)

/-- Closes a node's pc equation (or another closed fact) by evaluation. -/
local macro "pcdec" : tactic =>
  `(tactic| (try dsimp only [mainN0, mainN1, mainNR, startN6, proN1, proN2, proN3, wcN4, exitNx]) <;> decide +kernel)

set_option hygiene false in
/-- A block from the switch on, no `ret`, no dead target. -/
local macro "mblk " l:term:max k:term:max ok:term:max hC:term:max hFO:term:max : tactic =>
  `(tactic| exact blkW_postO (l := $l) (k := $k) (dead := fun _ => false) (ra := 0) (by pcdec)
    (by pcdec) $ok hR hal (by rdec) (by rdec) (by rdec) (by rdec) $hC (by pcdec)
    (fun _ _ _ k hk r hr => (noRet_false (by rdec) k hk r hr).elim) (fun _ _ _ => rfl) hsub hfit $hFO)

set_option maxHeartbeats 1600000 in
/-- **`scc_rt_main`'s states are inside `Wr`** (`MainW`), in the new
stack's region at its top `top` (16-aligned, not wrapping), the TCB at
`134217736` (`n0 = 0`), with the source control `c0` (`hC0`, its facts),
`rS` in the pool (`hsub`) and not wrapping (`hfit`). The frame condition
after the switch gives the words of `rS` off the region. -/
theorem mainW (hC0 : CFacts ret0Λ ret0Λ.static c0) {top : BitVec 64} (h16 : top.toNat % 16 = 0)
    (hok : (swR top (-80) 0).OK) (hsub : rS.Sub ret0Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (ms : MemSide isaLSE2) :
    MainW (Wr rS) (Kr rS) ret0Exe ret0End (swR top (-80) 0) (swFS rS top (limA (UInt64.ofBitVec 134217736#64)) top)
      ms ⟨top, UInt64.ofBitVec 134217736#64, c0⟩ := by
  have hR := hok
  have hal : (swR top (-80) 0).base.toNat % 16 = 0 := h16
  have hFO : ∀ m, swFS rS top (limA (UInt64.ofBitVec 134217736#64)) top m → StackOff rS (swR top (-80) 0) m :=
    fun _ h => h.2
  obtain ⟨hR', hal'⟩ := callee_facts (kc := -48) (lo' := -32) hok h16 (by rdec) (by rdec) (by rdec)
    (by rdec)
  have hFO' : ∀ m, (swFS rS top (limA (UInt64.ofBitVec 134217736#64)) top m ∧
      CallerCells (swR top (-80) 0) (-48) (-32) 0 m) → StackOff rS ((swR top (-80) 0).callee (-48) (-32) 0) m :=
    fun _ h => stackOff_callee hok (by show top.toNat % 8 = 0; omega) (by rdec) (by rdec) (by rdec)
      (by rdec) (by rdec) (by rdec) h.1.2 h.2
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, fun g' hra hc0 htp => ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨?_, ?_⟩⟩
  -- `scc_rt_main`'s prologue
  · show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
    mblk ".L1_scc_rt_main.stack_check" 0 (chkHead_ok (-48) 0 _) (fun _ _ hJ => hJ.1 ▸ hC0) hFO
  · show NodeW _ _ _ _ _ _ _; rw [ret0_labT]
    exact nodeW_ldr_postO (t := .X10) (b := .X10) (i := 8) (l := ".L1_scc_rt_main.stack_check") (k := 2)
      (p := labT "scc_rt_main" + 4 + 4) (a := 134217744#64) (by pcdec) (by pcdec) rfl
      (fun _ _ ⟨_, hJ, _⟩ => hJ.1 ▸ hC0) (by pcdec) (by pcdec)
      (fun _ _ ⟨_, hJ, he⟩ => by rw [he]; exact rAddr_lim _ hJ.2.2) (by rdec)
      (fun _ h => by rw [← limA_tcb0]; exact h.1.2) hR (by show top.toNat % 8 = 0; omega) (by rdec) (by rdec)
      hsub hFO
  · show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
    mblk ".L1_scc_rt_main.stack_check" 3 (chkBr_ok (-48) 0 _ _) (fun _ _ ⟨_, _, hJ, _⟩ => hJ.1 ▸ hC0) hFO
  · show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
    mblk ".L1_scc_rt_main.stack_check" 5 (frameSet_ok (lo := -48) (hi := 0) (by rdec) (by rdec) (by rdec) (by rdec)
      (by rdec)) (fun _ _ ⟨_, _, hJ, _⟩ => hJ.1 ▸ hC0) hFO
  -- the call of `wc_main`
  · show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
    mblk ".L1_scc_rt_main.0_entry" 0 mainCall_ok (fun _ _ hJ => hJ.1 ▸ hC0) hFO
  -- `wc_main`'s prologue
  · show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
    exact blkW_postO (l := ".L18_wc_main.stack_check") (k := 0) (dead := fun _ => false) (ra := 0)
      (by pcdec) (by pcdec) (chkHead_ok (-32) 0 _) hR' hal' (by rdec) (by rdec) (by rdec)
      (by rdec) (fun _ _ hJ => hJ.1 ▸ hc0 ▸ hC0) (by pcdec)
      (fun _ _ _ k hk r hr => (noRet_false (by rdec) k hk r hr).elim) (fun _ _ _ => rfl) hsub hfit hFO'
  · show NodeW _ _ _ _ _ _ _; rw [ret0_labT]
    exact nodeW_ldr_postO (t := .X10) (b := .X10) (i := 8) (l := ".L18_wc_main.stack_check") (k := 2)
      (p := labT "wc_main" + 4 + 4) (a := 134217744#64) (by pcdec) (by pcdec) rfl
      (fun _ _ ⟨_, hJ, _⟩ => hJ.1 ▸ hc0 ▸ hC0) (by pcdec) (by pcdec)
      (fun _ _ ⟨_, hJ, he⟩ => by rw [he]; exact rAddr_lim _ (hJ.2.2.2.2.trans htp)) (by rdec)
      (fun _ h => by rw [← limA_tcb0]; exact h.1.1.2) hR' (by omega) (by rdec) (by rdec) hsub hFO'
  · show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
    exact blkW_postO (l := ".L18_wc_main.stack_check") (k := 3) (dead := fun _ => false) (ra := 0)
      (by pcdec) (by pcdec) (chkBr_ok (-32) 0 _ _) hR' hal' (by rdec) (by rdec) (by rdec)
      (by rdec) (fun _ _ ⟨_, _, hJ, _⟩ => hJ.1 ▸ hc0 ▸ hC0) (by pcdec)
      (fun _ _ _ k hk r hr => (noRet_false (by rdec) k hk r hr).elim) (fun _ _ _ => rfl) hsub hfit hFO'
  · show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
    exact blkW_postO (l := ".L18_wc_main.stack_check") (k := 5) (dead := fun _ => false) (ra := 0)
      (by pcdec) (by pcdec)
      (frameSet_ok (lo := -32) (hi := 0) (by rdec) (by rdec) (by rdec) (by rdec) (by rdec)) hR' hal'
      (by rdec) (by rdec) (by rdec) (by rdec) (fun _ _ ⟨_, _, hJ, _⟩ => hJ.1 ▸ hc0 ▸ hC0)
      (by pcdec)
      (fun _ _ _ k hk r hr => (noRet_false (by rdec) k hk r hr).elim) (fun _ _ _ => rfl) hsub hfit hFO'
  -- `wc_main`'s body
  · show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
    exact blkW_postO (l := ".L18_wc_main.0_entry") (k := 0) (dead := fun _ => false) (ra := 0)
      (by pcdec) (ofNat4_zero _) wcAdd_ok hR' hal' (by rdec) (by rdec) (by rdec) (by rdec)
      (fun _ _ hJ => hJ.1 ▸ hc0 ▸ hC0) (by pcdec)
      (fun _ _ _ k hk r hr => (noRet_false (by rdec) k hk r hr).elim) (fun _ _ _ => rfl) hsub hfit hFO'
  · show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
    rw [ret0_labT] at hra
    exact blkW_postO (l := ".L18_wc_main.0_entry") (k := 4) (dead := fun _ => false)
      (ra := labT ".L1_scc_rt_main.0_entry" + 4) (by pcdec) (by pcdec) wcRet_ok hR' hal'
      (by rdec) (by rdec) (by rdec) (by rdec) (fun _ _ ⟨_, hJ, _⟩ => hJ.1 ▸ hc0 ▸ hC0)
      (by pcdec)
      (hret_of_run wcRet_ok fun σ _ ⟨σ0, hJ, hs, _⟩ => by
        rw [show wcRet = spStr .X9 0 :: retBlk 32 [.slot 0] from rfl, arun_cons,
          show (wcN4 labT (wcN1 labT g').J).o = ⟨-32, []⟩ from rfl, dstep_spStr0,
          (retBlk_run labT _ _ (F := 32) (by rdec) [.slot 0]).1]
        simp only [Spike.Lib.upd_apply, hs]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by rdec)), hJ.2.2, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ _ _ => rfl) hsub hfit hFO'
  -- the `exit_group` tail
  · show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
    mblk ".L1_scc_rt_main.sp0" 0 (exitTail_ok (lo := -48) (hi := 0) (by pcdec) (by pcdec))
      (fun _ _ hJ => hJ.1 ▸ hC0) hFO
  · show NodeW _ _ _ _ _ _ _; rw [ret0_labT]
    exact nodeW_svc_postO (l := ".L1_scc_rt_main.sp0") (k := 3) (p := labT ".L1_scc_rt_main.sp0" + 4 + 4 + 4)
      (by pcdec) (by pcdec) rfl (fun _ _ ⟨_, _, hJ, _⟩ => hJ.1 ▸ hC0) (by pcdec)
      (by pcdec) hR (by show top.toNat % 8 = 0; omega) (by rdec) (by rdec) hsub hFO
      (fun _ _ h => by rw [h.1]; decide)

/-- **The switch's and `scc_rt_main`'s states are inside `Wr`** (`SwW`):
the switch with the stack range in private memory, the block after it and
`scc_rt_main`'s in the new stack's region (vacuous off its top `top`), the
TCB at `134217736` (`htcb`), with the source control `c0` (`hC0`, its
facts), `rS` in the pool (`hsub`) and not wrapping (`hfit`). -/
theorem swW (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region} {F : MachineData → Prop} {tcb top : BitVec 64}
    (htcb : tcb = 134217736#64) (h16 : top.toNat % 16 = 0) (hok : (swR top (-80) 0).OK)
    (hsub : rS.Sub ret0Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (ms : MemSide isaLSE2) :
    SwW (Wr rS) (Kr rS) ret0Exe ret0End R (fun m => F m ∧ StackM rS m) ms rS tcb top c0 := by
  subst htcb
  refine ⟨?_, fun v => ?_, fun v => ?_⟩
  · show NodeW _ _ _ _ _ _ _; rw [ret0_labT]
    exact nodeW_reg_post (op := .ADD_e (.low .SP .W64) (.low (.reg .X9) .W64) (.imm ⟨.int64 0, .S0⟩)) rfl
      (l := sp3L) (k := 5) (p := labT sp3L + Int64.ofNat (4 * 5)) (by pcdec) rfl rfl
      (fun _ _ hJ => hJ.1 ▸ hC0) (by pcdec) (by pcdec) hsub
  · by_cases hv : v = top
    · subst hv
      have hR := hok
      have hal : (swR v (-80) 0).base.toNat % 16 = 0 := h16
      show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
      mblk sp3L 6 startMain_ok (fun _ _ hJ => hJ.1 ▸ hC0) (fun _ h => h.2)
    · exact blkW_false fun _ h => hv h.1.1
  · by_cases hv : v = top
    · subst hv; exact mainW hC0 h16 hok hsub hfit ms
    · exact mainW_false fun _ h => hv h.1.1

end Main

/-! ## `scc_rt_start` as a whole -/

section Exit

open Spike.Lib.A64.Flow

/-- `main`'s body in `ret0.w`: `let x = 40; let y = x + 2; ret y`. -/
def mainBody : Expr :=
  .let_ "x" (.atom (.lit 40)) (.let_ "y" (.add (.var "x") (.lit 2)) (.ret (.var "y")))

/-- The environment after both bindings. -/
def exitEnv (env : TermRun.Env) : TermRun.Env :=
  ("y", .int, [TermRun.addW (TermRun.cst (.num 40)) (TermRun.cst (.num 2))]) ::
    ("x", .intS (.lit 40), [TermRun.cst (.num 40)]) :: env

theorem mainBody_run {p : Prog} {c0 : Ctl} (h : c0.term = mainBody) :
    LocalRun p c0 ⟨.ret (.var "y"), exitEnv c0.env, none⟩ := by
  refine .step (c₁ := ⟨.let_ "y" (.add (.var "x") (.lit 2)) (.ret (.var "y")),
    ("x", .intS (.lit 40), [TermRun.cst (.num 40)]) :: c0.env, none⟩) ⟨rfl, ?_⟩ (.single ⟨rfl, ?_⟩)
  · intro g mem pairs th _ ht he _ _
    simp only [TermRun.tstep, ht, h, mainBody, TermRun.evalOp, TermRun.evalAt, TermRun.ol, Option.map,
      Option.toList, List.map, TermRun.withS, TermRun.stOf, he]
  · intro g mem pairs th _ ht he _ _
    simp only [TermRun.tstep, ht, TermRun.evalOp, TermRun.evalAt, TermRun.lookupE, TermRun.ol, he,
      List.find?, Option.map, Option.toList, TermRun.withS, TermRun.stOf]
    rfl

/-- `main`'s entry environment: its argument bound to the start's unit
(the start's `a`, no words). -/
def mainEnv (d : Decl) : TermRun.Env := [(d.arg, TermRun.close [] d.argTy, [])]

/-- **The source start's step**: its tail call into `p`'s `main` (`hd`),
whose body is `mainBody` (`hb`). -/
theorem start_step {p : Prog} {d : Decl} (hd : p.find? (·.name == "main") = some d) (hb : d.body = mainBody) :
    LocalStep p Spike.Lib.A64Consumer.c0 ⟨mainBody, mainEnv d, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th hg ht he hs _
  simp only [TermRun.tstep, ht, TermRun.enter, hg, hd, he, Spike.Lib.A64Consumer.c0, TermRun.evalAt,
    TermRun.lookupE, List.find?, TermRun.ol, Option.map, Option.toList]
  obtain ⟨⟩ := th
  simp only at hs
  subst hs
  simp [hb, mainEnv]

/-- **The source start runs to `ret y`**: `start_step`, then `main`'s two
bindings. -/
theorem start_run {p : Prog} {d : Decl} (hd : p.find? (·.name == "main") = some d) (hb : d.body = mainBody) :
    LocalRun p Spike.Lib.A64Consumer.c0 ⟨.ret (.var "y"), exitEnv (mainEnv d), none⟩ :=
  .step (start_step hd hb) (mainBody_run rfl)

/-- **The source start's `CFacts`**: a tail call, its argument `a` with no
words, so nothing to place. -/
theorem cfacts_c0 {Λ : Scc.Sem.Layout} {lbl : Lbl} : CFacts Λ lbl Spike.Lib.A64Consumer.c0 := by
  refine ⟨nofun, fun _ _ _ _ _ h => ?_, nofun, fun s => ?_⟩
  · rcases h with h | ⟨_, h⟩ <;> cases h
  refine ⟨fun _ _ => none, ?_, ?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ h; cases h
  rotate_left
  · intro _ _ _ h; cases h
  intro x hx ty ws hl k hk
  simp [Scc.Sem.exprFv, Scc.Sem.atVars, Spike.Lib.A64Consumer.c0] at hx
  subst hx
  have : ws = [] :=
    (by simpa [Spike.Lib.A64Consumer.c0, TermRun.lookupE, List.find?] using hl.symm : _ ∧ _).2
  subst this
  cases hk

/-- **`main`'s exit at the `exit_group` of `scc_rt_main`** (`hexit` of
`ret0_segW`), for any control `c0` that runs locally to `main`'s body in
some environment `env` (`hrun`): the run on to `ret y` with `y = 42`,
placed in `x0`. Nothing of `env` is needed: the run binds `x` and `y`
itself, and `ret y` reads only `y`. -/
theorem ret0_exitOf {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ls0 : Lsize}
    {ms : MemSide isaLSE2} (hms : ms = msOf ret0Λ μ0 rd G own ret0Λ.static ls0) {c0 : Ctl} {env : TermRun.Env}
    (hrun : LocalRun p c0 ⟨mainBody, env, none⟩) :
    ∀ R' F' s, At ret0Exe ret0End R' F' (mainNX labT) s c0 → ¬ ms.abortAt s → MainExit p ms s c0 42 := by
  subst hms
  rintro R' F' s ⟨-, -, -, -, σ, hA, -, hx⟩ -
  have h42 : s.st.1.regs.X0.toBitVec = 42#64 := by rw [hA.regs]; exact hx
  refine ⟨⟨.ret (.var "y"), exitEnv env, none⟩, hrun.trans (mainBody_run rfl), ?_, ?_⟩
  · refine ⟨fun x k => if x = "y" ∧ k = 0 then some (.one (.reg (.x 0))) else none, ?_, ?_, ?_⟩
    · intro x ty ws hl k wd wp hk hp
      dsimp only at hp
      split at hp
      · obtain ⟨rfl, rfl⟩ := ‹x = "y" ∧ k = 0›
        cases hp
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj
          ((show TermRun.lookupE (exitEnv env) "y" = some _ from rfl).symm.trans hl))
        cases hk
        refine ⟨42, ?_, ⟨by decide, rfl⟩⟩
        exact congrArg (fun b : BitVec 64 => some b.toNat) (h42 : Scc.Sem.A64.regVal s (.x 0) = 42#64)
      · cases hp
    · intro x hx ty ws hl k hk
      simp [Scc.Sem.exprFv, Scc.Sem.atVars] at hx
      subst hx
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj
        ((show TermRun.lookupE (exitEnv env) "y" = some _ from rfl).symm.trans hl))
      obtain rfl : k = 0 := by simpa using hk
      exact ⟨.one (.reg (.x 0)), by simp⟩
    · intro x k n h
      dsimp only at h
      split at h <;> cases h
  · intro s0 th h0 ht he hs
    unfold Scc.Sem.SrcSem.mainExit
    simp only [h0, ht, hs, he]
    rfl

/-- **`main`'s exit from the source start** `A64Consumer.c0` (the thread
at `mainStart`): `ret0_exitOf` through `start_run`, given `p`'s `main`
(`hd`) with body `mainBody` (`hb`). -/
theorem ret0_exit {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ls0 : Lsize}
    {ms : MemSide isaLSE2} (hms : ms = msOf ret0Λ μ0 rd G own ret0Λ.static ls0) {d : Decl}
    (hd : p.find? (·.name == "main") = some d) (hb : d.body = mainBody) :
    ∀ R' F' s, At ret0Exe ret0End R' F' (mainNX labT) s Spike.Lib.A64Consumer.c0 → ¬ ms.abortAt s →
      MainExit p ms s Spike.Lib.A64Consumer.c0 42 :=
  ret0_exitOf hms (.single (start_step hd hb))

end Exit

section StartAll

open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0.Mem (ret0Exe ret0End ret0F)

variable {rS : Range} {c0 : Ctl} {F : MachineData → Prop}

/-- **A range off a region is off a callee's inside it**: the callee's
region at `kc`, `[lo', 0)`, lies in the region. -/
theorem out_callee {R : Region} (hR : R.OK) {kc lo' : Int} (hlo : R.lo ≤ kc + lo') (hlo0 : lo' ≤ 0)
    (hkc : kc < R.hi)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a) :
    ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ (R.callee kc lo' 0).base.toNat + (R.callee kc lo' 0).lo ∨
        ((R.callee kc lo' 0).base.toNat : Int) + (R.callee kc lo' 0).hi ≤ a := by
  intro a h8 ha ha7
  have hb := Region.callee_base (hi' := 0) hR hlo hlo0 hkc
  have h := hout a h8 ha ha7
  rw [hb]
  show (a : Int) + 8 ≤ R.base.toNat + kc + lo' ∨ (R.base.toNat : Int) + kc + 0 ≤ a
  omega

/-- **`scc_rt_start`'s states are inside `Wr`** (`StartAllW`): `sp0W`,
`sp2W` and `swW`, at `n0 = 0` (the TCB at `134217736`, `tcbA0`), the new
stack's top `stacksA + k0 + 16384` 16-aligned (`h16`) with its region not
wrapping (`hok`), `rS` in the pool (`hsub`) and not wrapping (`hfit`). The
take site's obligation is `hsite`, the stack range's stability under the
three regions' writes from the range off the region (`houtS`,
`stackM_stable`, `out_callee`). -/
theorem startAllW (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → ret0F m) {n0 k0 : BitVec 64} (hn0 : n0 = 0#64)
    (hsub : rS.Sub ret0Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hsite : ∀ g : ThreadInit.G, g.ra = (labT sp3L).toBitVec → ∀ g' : StackTake.G,
      g'.ra = (labT ThreadInit.spL).toBitVec →
      TakeW (Wr rS) (Kr rS) ret0Exe ret0End ((R.callee Abort.oI.sp (-256) 0).callee ThreadInit.oI.sp (-208) 0) F
        (StackM rS) (tiTake ⟨g, pinA labT + n0 + 8#64, k0, c0⟩ g') .site)
    (h16 : (stacksA labT + k0 + 16384#64).toNat % 16 = 0) (hok : (swR (stacksA labT + k0 + 16384#64) (-80) 0).OK)
    (ms : MemSide isaLSE2) :
    StartAllW (Wr rS) (Kr rS) ret0Exe ret0End R F ms rS n0 k0 c0 := by
  obtain ⟨hR1, -⟩ := callee_facts (kc := Abort.oI.sp) (lo' := -256) hR hal (by show R.lo ≤ -48 + -256; omega)
    (by decide) (by show (-48 : Int) < R.hi; omega) (by decide)
  have ho1 := out_callee hR (kc := Abort.oI.sp) (lo' := -256) (by show R.lo ≤ -48 + -256; omega) (by decide)
    (by show (-48 : Int) < R.hi; omega) houtS
  have ho2 := out_callee hR1 (kc := ThreadInit.oI.sp) (lo' := -208) (by show (-256 : Int) ≤ -48 + -208; decide)
    (by decide) (by show (-48 : Int) < 0; decide) ho1
  refine ⟨sp0W hC0 hR hal (by omega) hhi hFr hn0, sp2W hC0 hR hal hlo hhi hFr hn0 hsub (stackM_stable hfit houtS)
    (stackM_stable hfit ho1) (stackM_stable hfit ho2) hsite, ?_⟩
  rw [ret0_labT]
  exact swW hC0 (tcbA0 hn0) h16 hok hsub hfit ms

/-- **`_start`'s block is inside `Wr`**: the branch, before the take, with
the source control `c0` (`hC0`, its facts). -/
theorem entryW (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ 0) (hhi : 0 ≤ R.hi) :
    BlkW (Wr rS) (Kr rS) ret0Exe ret0End R F (entryN labT c0) entryB :=
  blkW_pre (l := "_start") (k := 0) (dead := fun _ => false) (ra := 0) (by decide +kernel) (ofNat4_zero _)
    entryB_ok hR hal hlo hhi (fun _ _ hJ => hJ ▸ hC0) (by decide +kernel)
    (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim) (fun _ _ _ => rfl) (by decide +kernel)

/-- **The loaded thread's run is one segment inside `Wr`**, the take its
outside move: `entry_segW` then `start_segW`, the obligations `entryW` and
`startAllW`. The premises are `start_segW`'s at `ret0Exe` (the memory
side's facts, the layout's arithmetic, `main`'s exit `hexit`) and
`startAllW`'s (the take site's obligation `hsite`). -/
theorem ret0_segW {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region}
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → ret0F m) {n0 k0 : BitVec 64} (hn0 : n0 = 0#64)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F ret0Exe ret0End (pinA labT + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F ret0Exe ret0End n0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA labT + n0 + 8#64) (stacksA labT + k0),
      StOk ms F ret0Exe ret0End (pinA labT + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F ret0Exe ret0End k0)
    (h16 : (stacksA labT + k0 + 16384#64).toNat % 16 = 0)
    (hok : (swR (stacksA labT + k0 + 16384#64) (-80) 0).OK)
    (hsubR : ∀ k, (swR (stacksA labT + k0 + 16384#64) (-80) 0).Off k →
      ((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat + 7))
    (hfit : (limA (UInt64.ofBitVec (pinA labT + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec (pinA labT + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA labT + k0 + 16384#64).toNat + -80 ∨
      ((stacksA labT + k0 + 16384#64).toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec (pinA labT + n0 + 8#64))).toNat)
    (hlimM : LimOk ms F ret0Exe ret0End (limA (UInt64.ofBitVec (pinA labT + n0 + 8#64)))
      (stacksA labT + k0 + 16384#64 - (48 : Int64).toBitVec))
    (hlimW : LimOk ms F ret0Exe ret0End (limA (UInt64.ofBitVec (pinA labT + n0 + 8#64)))
      (stacksA labT + k0 + 16384#64 - (48 : Int64).toBitVec - (32 : Int64).toBitVec))
    (hexit : ∀ R' F' s, At ret0Exe ret0End R' F' (mainNX labT) s c0 → ¬ ms.abortAt s → MainExit p ms s c0 42)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hsub : rS.Sub ret0Λ.stackPool)
    (hsite : ∀ g : ThreadInit.G, g.ra = (labT sp3L).toBitVec → ∀ g' : StackTake.G,
      g'.ra = (labT ThreadInit.spL).toBitVec →
      TakeW (Wr rS) (Kr rS) ret0Exe ret0End ((R.callee Abort.oI.sp (-256) 0).callee ThreadInit.oI.sp (-208) 0) F
        (StackM rS) (tiTake ⟨g, pinA labT + n0 + 8#64, k0, c0⟩ g') .site)
    {Q : Frag isaLSE2} :
    SegW (Wr rS) (Kr rS) p lbl ms (At ret0Exe ret0End R F (entryN labT c0)) Q := by
  have hE := entry_segW (exe := ret0Exe) (endPc := ret0End) (p := p) (lbl := lbl) (ms := ms) (W := Wr rS)
    (K := Kr rS) (R := R) (F := F) ret0_lays rfl hF hR hal (by omega) hhi c0
  have hS := start_segW (exe := ret0Exe) (endPc := ret0End) (p := p) (lbl := lbl) (ms := ms) (W := Wr rS)
    (R := R) (F := F) (rS := rS) (Q := Q) ret0_lays rfl
  rw [ret0_labT] at hE hS
  exact (hE (entryW hC0 hR hal (by omega) hhi)).seq (hS hK hF hR hal hlo hhi n0 k0 c0 hn hhdr htcb hk hfld htk
    h16 hok hsubR hfit hout hlimM hlimW hexit hRS hfitS houtS hFt
    (startAllW hC0 hR hal hlo hhi hFr hn0 hsub hfitS houtS hsite h16 hok ms))

/-- **The consumer's obligations of `ret0`** from `ret0_segW` through
`inst_of_segW`, at the memory side `msOf` of the static placement (`hms`):
a fragment holding the loaded thread's entry node, with `Nodes`,
`TakePath` and `AbortPath` (an empty phase). The take site's states by
`takeSiteW`, the range named by its registers (`hrS`); open: `ret0_segW`'s
premises. -/
theorem ret0_inst {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ls0 : Lsize}
    {ms : MemSide isaLSE2} (hms : ms = msOf ret0Λ μ0 rd G own ret0Λ.static ls0)
    (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → ret0F m) {n0 k0 : BitVec 64} (hn0 : n0 = 0#64)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F ret0Exe ret0End (pinA labT + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F ret0Exe ret0End n0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA labT + n0 + 8#64) (stacksA labT + k0),
      StOk ms F ret0Exe ret0End (pinA labT + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F ret0Exe ret0End k0)
    (h16 : (stacksA labT + k0 + 16384#64).toNat % 16 = 0)
    (hok : (swR (stacksA labT + k0 + 16384#64) (-80) 0).OK)
    (hsubR : ∀ k, (swR (stacksA labT + k0 + 16384#64) (-80) 0).Off k →
      ((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat + 7))
    (hfit : (limA (UInt64.ofBitVec (pinA labT + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec (pinA labT + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA labT + k0 + 16384#64).toNat + -80 ∨
      ((stacksA labT + k0 + 16384#64).toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec (pinA labT + n0 + 8#64))).toNat)
    (hlimM : LimOk ms F ret0Exe ret0End (limA (UInt64.ofBitVec (pinA labT + n0 + 8#64)))
      (stacksA labT + k0 + 16384#64 - (48 : Int64).toBitVec))
    (hlimW : LimOk ms F ret0Exe ret0End (limA (UInt64.ofBitVec (pinA labT + n0 + 8#64)))
      (stacksA labT + k0 + 16384#64 - (48 : Int64).toBitVec - (32 : Int64).toBitVec))
    (hexit : ∀ R' F' s, At ret0Exe ret0End R' F' (mainNX labT) s c0 → ¬ ms.abortAt s → MainExit p ms s c0 42)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hsub : rS.Sub ret0Λ.stackPool)
    (hrS : rS = ⟨(stacksA labT + k0).toNat, 16384⟩) :
    ∃ inv : Frag isaLSE2, (∀ s c, At ret0Exe ret0End R F (entryN labT c0) s c → inv s c) ∧
      Nodes ret0Λ p μ0 rd G own (IOf ret0Λ.static ls0 inv) ∧
      TakePath ret0Λ p μ0 (IOf ret0Λ.static ls0 inv) rS Tk ∧
      AbortPath μ0 (IOf ret0Λ.static ls0 inv) (fun _ => False) ∧ NoWrite (IOf ret0Λ.static ls0 inv) := by
  subst hms
  exact inst_of_segW (ret0_segW (lbl := ret0Λ.static) hC0 rfl hF hR hal hlo hhi hFr hn0 hn hhdr htcb hk hfld htk h16 hok
    hsubR hfit hout hlimM hlimW hexit hRS hfitS houtS hFt hsub
    fun _ _ _ _ => takeSiteW hC0 _ rfl hrS hsub) mu0_take (fun _ _ h => h)

/-- **`ret0_inst` at the source start**, the control `A64Consumer.c0` that
the consumer's `hst` fixes (the runtime never steps the source, so the start
is carried unchanged to `mainNX`): `CFacts` by `cfacts_c0`, `main`'s exit by
`ret0_exit`, given `p`'s `main` (`hd`) with body `mainBody` (`hb`). -/
theorem ret0_inst' {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ls0 : Lsize}
    {ms : MemSide isaLSE2} (hms : ms = msOf ret0Λ μ0 rd G own ret0Λ.static ls0)
    {R : Region}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → ret0F m) {n0 k0 : BitVec 64} (hn0 : n0 = 0#64)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F ret0Exe ret0End (pinA labT + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F ret0Exe ret0End n0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA labT + n0 + 8#64) (stacksA labT + k0),
      StOk ms F ret0Exe ret0End (pinA labT + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F ret0Exe ret0End k0)
    (h16 : (stacksA labT + k0 + 16384#64).toNat % 16 = 0)
    (hok : (swR (stacksA labT + k0 + 16384#64) (-80) 0).OK)
    (hsubR : ∀ k, (swR (stacksA labT + k0 + 16384#64) (-80) 0).Off k →
      ((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat + 7))
    (hfit : (limA (UInt64.ofBitVec (pinA labT + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec (pinA labT + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA labT + k0 + 16384#64).toNat + -80 ∨
      ((stacksA labT + k0 + 16384#64).toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec (pinA labT + n0 + 8#64))).toNat)
    (hlimM : LimOk ms F ret0Exe ret0End (limA (UInt64.ofBitVec (pinA labT + n0 + 8#64)))
      (stacksA labT + k0 + 16384#64 - (48 : Int64).toBitVec))
    (hlimW : LimOk ms F ret0Exe ret0End (limA (UInt64.ofBitVec (pinA labT + n0 + 8#64)))
      (stacksA labT + k0 + 16384#64 - (48 : Int64).toBitVec - (32 : Int64).toBitVec))
    {d : Decl} (hd : p.find? (·.name == "main") = some d) (hb : d.body = mainBody)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hsub : rS.Sub ret0Λ.stackPool)
    (hrS : rS = ⟨(stacksA labT + k0).toNat, 16384⟩) :
    ∃ inv : Frag isaLSE2, (∀ s c, At ret0Exe ret0End R F (entryN labT Spike.Lib.A64Consumer.c0) s c → inv s c) ∧
      Nodes ret0Λ p μ0 rd G own (IOf ret0Λ.static ls0 inv) ∧
      TakePath ret0Λ p μ0 (IOf ret0Λ.static ls0 inv) rS Tk ∧
      AbortPath μ0 (IOf ret0Λ.static ls0 inv) (fun _ => False) ∧ NoWrite (IOf ret0Λ.static ls0 inv) :=
  ret0_inst hms cfacts_c0 hF hR hal hlo hhi hFr hn0 hn hhdr htcb hk hfld htk h16 hok hsubR hfit hout hlimM hlimW
    (ret0_exit hms hd hb) hRS hfitS houtS hFt hsub hrS

end StartAll

section Entry

open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0.Mem (ret0Exe ret0End ret0F ret0Words ret0Words_entry ret0Words_pool)

variable {rS : Range}

/-- The words lie below `2 ^ 32`. -/
theorem ret0Words_smallB : ret0Words.all (fun a => decide (a.toNat < 2 ^ 32)) = true := by decide +kernel

theorem ret0Words_small : ∀ a ∈ ret0Words, a.toNat < 2 ^ 32 := fun a ha => by
  simpa using List.all_eq_true.mp ret0Words_smallB a ha

/-- The stack pool fits the address space. -/
theorem pool_fit : ret0Λ.stackPool.lo + ret0Λ.stackPool.size < 2 ^ 64 := by decide +kernel

/-- A word clear of an entry stack, the stack in the address space
(`hfit`), is unmapped in the stack's private memory. -/
theorem stackMem_loadInt {E : Scc.Sem.Entry} {a : BitVec 64} (hfit : E.stack.lo + E.stack.size ≤ 2 ^ 64)
    (ha : a.toNat + 8 ≤ E.stack.lo ∨ E.stack.lo + E.stack.size ≤ a.toNat) :
    Mem.loadInt E.stackMem a 8 = none := by
  have hne : E.stackMem[a]? = none := by
    rw [← Std.ExtHashMap.get?_eq_getElem?]
    unfold Scc.Sem.Entry.stackMem
    rw [Mem.get?_storeBytes_of_not_mem]
    · simp
    · rw [mem_At_iff]
      rintro ⟨i, hi, he⟩
      rw [List.length_replicate] at hi
      have h1 := congrArg BitVec.toNat he
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h1
      rw [Nat.mod_eq_of_lt (a := E.stack.lo) (by omega), Nat.mod_eq_of_lt (a := i) (by omega),
        Nat.mod_eq_of_lt (by omega)] at h1
      omega
  unfold Mem.loadInt Mem.loadBytes
  rw [show List.range 8 = 0 :: List.range' 1 7 from rfl, List.map_cons]
  simp [List.allSome, List.mapM_cons, hne]

/-- **The entry frame condition holds of the initial private memory**: the
entry stack's zero bytes (`Entry.stackMem`) map no word of `ret0Words`,
which lie clear of the stack (`ret0Words_entry`). -/
theorem ret0F_stackMem {m : MachineData} (h : m.dmem = Scc.Sem.Entry.linux.stackMem) : ret0F m := by
  intro a ha
  rw [h]
  exact stackMem_loadInt (by decide) (ret0Words_entry a ha)

/-- **The take keeps the entry frame condition**: the taken range lies in
the stack pool (`hsub`), which `ret0Words` are clear of
(`ret0Words_pool`), so the take leaves each of them as it was
(`loadInt_takeMem`). -/
theorem ret0F_takeMem {rS : Scc.Sem.Range} (hsub : rS.Sub ret0Λ.stackPool) {pm : _root_.Mem 64}
    {m : MachineData} (h : ret0F m) : ret0F (takeMem pm rS m) := by
  intro a ha
  rw [loadInt_takeMem ?_]
  · exact h a ha
  intro i hi hm
  obtain ⟨j, hj, he⟩ := List.mem_map.mp hm
  have hj := List.mem_range.mp hj
  have hs := ret0Words_small a ha
  have hp := ret0Words_pool a ha
  have hf := pool_fit
  obtain ⟨h1, h2⟩ := hsub
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- **The whole entry stack as a region**: from its top, down by its size. -/
def entryR : Region := ⟨BitVec.ofNat 64 Scc.Sem.Entry.linux.sp, -65536, 0⟩

/-- **The entry frame condition is stable in the entry stack**: every word
of `ret0Words` lies clear of it (`ret0Words_entry`), so a write inside it
keeps each one. -/
theorem ret0F_stable : FStable entryR ret0F := by
  intro m m' h hD a ha
  rw [hD a (by have := ret0Words_small a ha; omega) ?_]
  · exact h a ha
  have hc := ret0Words_entry a ha
  simp only [entryR, Scc.Sem.Entry.sp, Scc.Sem.Entry.linux] at hc ⊢
  rw [BitVec.toNat_ofNat]
  omega

/-- The entry stack's region does not wrap. -/
theorem entryR_ok : entryR.OK := ⟨by decide, by decide⟩

/-- Its top is 16-aligned. -/
theorem entryR_al : entryR.base.toNat % 16 = 0 := by decide

/-- The stack pool lies below the entry stack. -/
theorem pool_below : ret0Λ.stackPool.lo + ret0Λ.stackPool.size ≤ Scc.Sem.Entry.linux.stack.lo := by
  decide +kernel

/-- **A range in the pool fits the address space.** -/
theorem fitS_of_sub {rS : Scc.Sem.Range} (hsub : rS.Sub ret0Λ.stackPool) : rS.lo + rS.size ≤ 2 ^ 64 := by
  have := pool_fit; obtain ⟨-, h⟩ := hsub; omega

/-- **A range in the pool is off the entry stack's region**, word by word
(`houtS` at `entryR`). -/
theorem outS_of_sub {rS : Scc.Sem.Range} (hsub : rS.Sub ret0Λ.stackPool) :
    ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ entryR.base.toNat + entryR.lo ∨ (entryR.base.toNat : Int) + entryR.hi ≤ a := by
  intro a _ _ ha7
  have := pool_below
  obtain ⟨-, h⟩ := hsub
  simp only [Scc.Sem.Range.contains] at ha7
  simp only [entryR, Scc.Sem.Entry.sp, Scc.Sem.Entry.linux] at this ⊢
  rw [BitVec.toNat_ofNat]
  omega

/-- **The entry stack's cells are off a range in the pool** (`hRS` at
`entryR`). -/
theorem rS_of_sub {rS : Scc.Sem.Range} (hsub : rS.Sub ret0Λ.stackPool) :
    ∀ k, entryR.Off k → ∀ i < 8, entryR.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS := by
  intro k hk i hi hm
  obtain ⟨j, hj, he⟩ := List.mem_map.mp hm
  have hj := List.mem_range.mp hj
  have hb := pool_below
  have hf := pool_fit
  obtain ⟨-, h⟩ := hsub
  have ha := entryR.addr_toNat entryR_ok hk
  have hfit := entryR.addr_fit entryR_ok hk
  obtain ⟨-, h3, -⟩ := hk
  have h1 := congrArg BitVec.toNat he
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
  have hbase : entryR.base.toNat = 140737488351232 := by decide
  have hlo : entryR.lo = -65536 := rfl
  rw [hbase] at ha
  rw [hlo] at h3
  simp only [Scc.Sem.Entry.linux] at hb
  omega

/-- **`ret0_inst'` at the entry stack and the entry frame condition**: the
region `entryR` (the whole entry stack) and `F := ret0F`, their facts
discharged here, the take's range only in the pool (`hsub`). -/
theorem ret0_instE {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ls0 : Lsize}
    {ms : MemSide isaLSE2} (hms : ms = msOf ret0Λ μ0 rd G own ret0Λ.static ls0)
    {n0 k0 : BitVec 64} (hn0 : n0 = 0#64)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms ret0F ret0Exe ret0End (pinA labT + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms ret0F ret0Exe ret0End n0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA labT + n0 + 8#64) (stacksA labT + k0),
      StOk ms ret0F ret0Exe ret0End (pinA labT + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms ret0F ret0Exe ret0End k0)
    (h16 : (stacksA labT + k0 + 16384#64).toNat % 16 = 0)
    (hok : (swR (stacksA labT + k0 + 16384#64) (-80) 0).OK)
    (hsubR : ∀ k, (swR (stacksA labT + k0 + 16384#64) (-80) 0).Off k →
      ((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat + 7))
    (hfit : (limA (UInt64.ofBitVec (pinA labT + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec (pinA labT + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA labT + k0 + 16384#64).toNat + -80 ∨
      ((stacksA labT + k0 + 16384#64).toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec (pinA labT + n0 + 8#64))).toNat)
    (hlimM : LimOk ms ret0F ret0Exe ret0End (limA (UInt64.ofBitVec (pinA labT + n0 + 8#64)))
      (stacksA labT + k0 + 16384#64 - (48 : Int64).toBitVec))
    (hlimW : LimOk ms ret0F ret0Exe ret0End (limA (UInt64.ofBitVec (pinA labT + n0 + 8#64)))
      (stacksA labT + k0 + 16384#64 - (48 : Int64).toBitVec - (32 : Int64).toBitVec))
    {d : Decl} (hd : p.find? (·.name == "main") = some d) (hb : d.body = mainBody)
    (hsub : rS.Sub ret0Λ.stackPool)
    (hrS : rS = ⟨(stacksA labT + k0).toNat, 16384⟩) :
    ∃ inv : Frag isaLSE2,
      (∀ s c, At ret0Exe ret0End entryR ret0F (entryN labT Spike.Lib.A64Consumer.c0) s c → inv s c) ∧
      Nodes ret0Λ p μ0 rd G own (IOf ret0Λ.static ls0 inv) ∧
      TakePath ret0Λ p μ0 (IOf ret0Λ.static ls0 inv) rS Tk ∧
      AbortPath μ0 (IOf ret0Λ.static ls0 inv) (fun _ => False) ∧ NoWrite (IOf ret0Λ.static ls0 inv) :=
  ret0_inst' hms ret0F_stable entryR_ok entryR_al (by decide) (by decide) (fun _ h => h) hn0 hn hhdr htcb hk hfld htk
    h16 hok hsubR hfit hout hlimM hlimW hd hb (rS_of_sub hsub) (fitS_of_sub hsub) (outS_of_sub hsub)
    (fun _ _ h => ret0F_takeMem hsub h) hsub hrS

theorem labT_stacksA : stacksA labT = 268435456#64 := by rw [← ret0_labT]; exact Mem.ret0_stacksA

/-- **The take's range**: the first stack, the one the site's registers
name at the first take (`k0 = 0`). -/
abbrev rS0 : Range := ⟨(stacksA labT + 0#64).toNat, 16384⟩

/-- `rS0` is in the stack pool. -/
theorem rS0_sub : rS0.Sub ret0Λ.stackPool := by
  rw [rS0, labT_stacksA]; unfold Scc.Sem.Range.Sub; decide +kernel

/-- `rS0` holds an aligned word (its first). -/
theorem rS0_word : ∃ a, a % 8 = 0 ∧ rS0.contains a ∧ rS0.contains (a + 7) :=
  ⟨rS0.lo, by rw [rS0, labT_stacksA]; unfold Scc.Sem.Range.contains; decide⟩

/-- The new stack's switch region lies in `rS0`, word by word. -/
theorem rS0_subR : ∀ k, (swR (stacksA labT + 0#64 + 16384#64) (-80) 0).Off k →
    ((swR (stacksA labT + 0#64 + 16384#64) (-80) 0).addr k).toNat % 8 = 0 ∧
    rS0.contains ((swR (stacksA labT + 0#64 + 16384#64) (-80) 0).addr k).toNat ∧
    rS0.contains (((swR (stacksA labT + 0#64 + 16384#64) (-80) 0).addr k).toNat + 7) := by
  intro k hk
  have hok : (swR (stacksA labT + 0#64 + 16384#64) (-80) 0).OK := by
    rw [labT_stacksA]; exact ⟨by decide, by decide⟩
  have ha := Region.addr_toNat hok hk
  obtain ⟨h8, h1, h2⟩ := hk
  have hb : (swR (stacksA labT + 0#64 + 16384#64) (-80) 0).base.toNat = 268451840 := by
    rw [labT_stacksA]; decide
  have hl : (stacksA labT + 0#64).toNat = 268435456 := by rw [labT_stacksA]; decide
  rw [hb] at ha
  simp only [swR] at h1 h2
  simp only [rS0, Scc.Sem.Range.contains, hl]
  omega

/-- **`ret0_instE` at the first take**: `n0 = k0 = 0` and the take's range
`rS0`, the layout's arithmetic (`Mem.ret0_hn` …) and `rS0`'s (`rS0_sub`,
`rS0_subR`) discharged here. Open: the runtime's stores and loads, and
`main`. -/
theorem ret0_instR {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ls0 : Lsize}
    {ms : MemSide isaLSE2} (hms : ms = msOf ret0Λ μ0 rd G own ret0Λ.static ls0)
    (hhdr : StOk ms ret0F ret0Exe ret0End (pinA labT + 0#64) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms ret0F ret0Exe ret0End 0#64)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA labT + 0#64 + 8#64) (stacksA labT + 0#64),
      StOk ms ret0F ret0Exe ret0End (pinA labT + 0#64 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms ret0F ret0Exe ret0End 0#64)
    (hlimM : LimOk ms ret0F ret0Exe ret0End (limA (UInt64.ofBitVec (pinA labT + 0#64 + 8#64)))
      (stacksA labT + 0#64 + 16384#64 - (48 : Int64).toBitVec))
    (hlimW : LimOk ms ret0F ret0Exe ret0End (limA (UInt64.ofBitVec (pinA labT + 0#64 + 8#64)))
      (stacksA labT + 0#64 + 16384#64 - (48 : Int64).toBitVec - (32 : Int64).toBitVec))
    {d : Decl} (hd : p.find? (·.name == "main") = some d) (hb : d.body = mainBody) :
    ∃ inv : Frag isaLSE2,
      (∀ s c, At ret0Exe ret0End entryR ret0F (entryN labT Spike.Lib.A64Consumer.c0) s c → inv s c) ∧
      Nodes ret0Λ p μ0 rd G own (IOf ret0Λ.static ls0 inv) ∧
      TakePath ret0Λ p μ0 (IOf ret0Λ.static ls0 inv) rS0 Tk ∧
      AbortPath μ0 (IOf ret0Λ.static ls0 inv) (fun _ => False) ∧ NoWrite (IOf ret0Λ.static ls0 inv) := by
  have hpin : pinA labT = 134217728#64 := labT_pinA
  have hst := labT_stacksA
  refine ret0_instE (rS := rS0) hms rfl (by decide) hhdr htcb (by decide) hfld htk
    (by rw [hst]; decide) (by rw [hst]; exact ⟨by decide, by decide⟩) rS0_subR
    (by rw [hpin]; decide) (by rw [hpin, hst]; decide) hlimM hlimW hd hb rS0_sub rfl

end Entry

end Spike.Lib.A64.Flow.Ret0.Inst
