/-
**`ret0.w` on x64: the per-state facts of the main path** (`SFacts`,
`Spike/Lib/X64SegInst.lean`) at the loaded thread, the instance side of
`inst_of_segW`: the x64 twin of `Spike/Lib/A64Ret0I.lean`.

- **The labels** (`ret0Tab`, `labT`, `ret0_labT`): the code labels of the
  main path at their addresses in the loaded thread, a table the kernel
  reads (`labIn` decided on the cells, `label_labIn`), so a block's checks
  are decided.
- **The phase index** (`ph`): four bits of the pc. The main path visits each
  of its pcs in one phase, every function on it running once: whether
  `scc_rt_pinned_next` is still `0` (up to the counter's `lock xadd` in
  `scc_rt_alloc_tcb`), whether the stack lock is held (past the `xchg`, up
  to the store releasing it on the bump path), whether `scc_rt_stack_next`
  is still `0` (up to its `lock xadd`) and whether the stack is not yet
  taken (up to the take site). A pc off the main path has whatever phase
  its range gives.
- **The owned words** (`own`): the four counters `scc_rt_pinned_next`,
  `scc_rt_stack_lock`, `scc_rt_stack_free_n`, `scc_rt_stack_next` with their
  values by phase; **the take's phase** (`Tk`): past the take site.
- **The marks** (`μ0`, `ret0_marks`): the transfer and abort sites, from
  the loader's parse of the text (the trust boundary `hpa`); `okPc`, a pc
  off all of them, gives `PcOff` (`pcOff_of_okPc`).
- **A block's and an instruction's states** before the take (`blkW_pre`,
  `nodeW_pre`, `nodeW_si_pre`, `nodeW_fi_pre`, `nodeW_st_pre`,
  `nodeW_xadd_pre`, `nodeW_xchg_pre`, `nodeW_ld_pre`, `nodeW_stown_pre`,
  `nodeW_syscall_pre`) and after it (`blkW_post`, `nodeW_post`,
  `nodeW_st_post`, `nodeW_syscall_post`) are inside `Wr`, and so are
  `scc_rt_alloc_tcb`'s (`tcbW`), `scc_rt_stack_take`'s (`takeW`, the take
  site's obligation a premise), `scc_rt_thread_init`'s (`tiW`) and
  `scc_rt_start`'s up to the switch (`st0W`, `x0W`).
- **From the switch on** the stack range is private memory but for the
  current 8-aligned region's cells (`StackOff`, `owned_off`,
  `stackOff_callee`): a block's and an instruction's states there
  (`blkW_postO`, `nodeW_postO`, `nodeW_fsld_postO`, `nodeW_syscall_postO`,
  `nodeW_fi_postO`; the switch itself `nodeW_reg_post`) are inside `Wr`, and
  so are `scc_rt_main`'s and `wc_main`'s (`mainW`) and the switch's with
  them (`swW`, vacuous off the new stack's top: `blkW_false`,
  `nodeW_false`, `mainW_false`).
- **`main`'s exit** (`ret0_exitOf`, `ret0_exit`): `main`'s body
  (`mainBody`) runs locally from the source start `X64Consumer.c0`
  (`start_step`, `start_run`) to `ret y`, `42` placed in `%rdi`; the start's
  `CFacts` (`cfacts_c0`).
- **`scc_rt_start` as one segment** (`startAllW`, `ret0_segW`) and the
  consumer's obligations through `inst_of_segW` (`ret0_inst`, and
  `ret0_inst'` at the source start). The segment starts at `scc_rt_start`
  (`startN0`), not at `_start`: `_start`'s `andq` switches to a region of
  its own before the call, so the region of `ret0_segW` has room for the
  return address above (`8 ≤ R.hi`).
- **From `_start`** (`entry_segW`, `ret0_instE`): `_start`'s `xor`, `andq`
  and call in the whole entry stack (`entryR`) with the entry frame condition
  `ret0F`, the call's callee region `entryC` holding `ret0_segW`; the
  region's and the pool's facts (`ret0F_stable`, `rS_of_sub`, `outS_of_sub`,
  their callee versions, `ret0F_takeMem`, `ret0F_stackMem`).
- **The take site's states** (`takeSiteW`) from the range its `%rdi`/`%rsi`
  name (`hrS`), the `nop` asked off the transfer sites only; at the first
  take's range `rS0` (`ret0_instR`) the layout's arithmetic and `rS0`'s facts
  are discharged.
-/
import Spike.Lib.X64SegInst
import Spike.Lib.X64Ret0Mem
import Spike.Lib.X64Ret0Own

namespace Spike.Lib.X64.Flow.Ret0.Inst

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (pcOf)
open Spike.Lib.X64Consumer
open Spike.Lib.X64
open Spike.Lib.X64.Flow.Ret0.Mem (ret0Exe ret0End ret0_lays)
open Spike.Lib.X64.OwnLimRt (labIn label_labIn)
open Scc.Cert.Rt.X64 (labelIdx blockAtB code_field)
open SccCode (ret0Λ ret0Cells ret0Asm)

/-! ## The labels -/

/-- **The main path's code labels** at their addresses in the loaded
thread. -/
def ret0Tab : List (Label × Nat) :=
  [("_start", 4194304), ("scc_rt_start", 4194317), (".Lscc_rt_start.entry", 4194325), (".Lscc_rt_start.x0", 4194391),
    (".Lscc_rt_start.x1", 4194404), ("scc_rt_main", 4194444), (".Lscc_rt_main.chk", 4194448),
    (".Lscc_rt_main.entry", 4194475), (".Lscc_rt_main.x2", 4194480), (".Lscc_rt_main.stk", 4194501),
    (".Lscc_rt_main.x3", 4194519), ("scc_rt_alloc", 4194529), (".Lscc_rt_alloc.entry", 4194552),
    (".Lscc_rt_alloc.cnt", 4194570), (".Lscc_rt_alloc.slow", 4194631), (".Lscc_rt_alloc.spin", 4194649),
    (".Lscc_rt_alloc.full", 4194651), (".Lscc_rt_alloc.x4", 4194663), (".Lscc_rt_alloc.ok", 4194665),
    ("scc_rt_alloc_tcb", 4194892), (".Lscc_rt_alloc_tcb.entry", 4194911), (".Lscc_rt_alloc_tcb.len", 4194933),
    (".Lscc_rt_alloc_tcb.full", 4195133), (".Lscc_rt_alloc_tcb.x5", 4195145), (".Lscc_rt_alloc_tcb.ok", 4195147),
    ("scc_rt_thread_reserve", 4195347), (".Lscc_rt_thread_reserve.entry", 4195355),
    (".Lscc_rt_thread_reserve.full", 4195422), (".Lscc_rt_thread_reserve.x6", 4195434),
    (".Lscc_rt_thread_reserve.ok", 4195436), ("scc_rt_thread_init", 4195445), (".Lscc_rt_thread_init.entry", 4195457),
    (".Lscc_rt_thread_init.x7", 4195469), ("scc_rt_stack_take", 4195595), (".Lscc_rt_stack_take.entry", 4195610),
    (".Lscc_rt_stack_take.cls5", 4195656), (".Lscc_rt_stack_take.clsnext6", 4195671),
    (".Lscc_rt_stack_take.clsdone7", 4195760), (".Lscc_rt_stack_take.spin14", 4195825),
    (".Lscc_rt_stack_take.locked15", 4195861), (".Lscc_rt_stack_take.pop", 4195890),
    (".Lscc_rt_stack_take.bump", 4196002), (".Lscc_rt_stack_take.full", 4196112), (".Lscc_rt_stack_take.x8", 4196124),
    (".Lscc_rt_stack_take.ok", 4196126), (".Lscc_rt_stack_take.taken", 4196166), ("scc_rt_take_site", 4196177),
    ("scc_rt_stack_release", 4196190), ("wc_main", 4198835), (".Lwc_main.chk", 4198839), (".Lwc_main.entry", 4198862),
    (".Lwc_main.ovf", 4198894), (".Lwc_main.stk", 4198906), (".Lwc_main.x12", 4198924)]

/-- Each is a label of the cells at its `labIn` address. -/
theorem ret0Tab_ok : ret0Tab.all (fun p => (labelIdx ret0Cells p.1).isSome &&
    labIn ret0Λ.code.lo ret0Cells p.1 == Int64.ofNat p.2) = true := by decide +kernel

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
its counter's `lock xadd`. -/
def bP (pc : Nat) : Bool := inN 4194304 4194391 pc || inN 4194892 4195096 pc

/-- **The stack lock is held**: past the `xchg` of `scc_rt_stack_take` up
to and including the store releasing it on its bump path. -/
def bL (pc : Nat) : Bool := inN 4195839 4196033 pc

/-- **`scc_rt_stack_next` is still `0`**: `scc_rt_start` up to the return
of its call of `scc_rt_thread_init`, `scc_rt_alloc_tcb`,
`scc_rt_thread_init` up to the return of its call, and `scc_rt_stack_take`
up to and including the `lock xadd`. -/
def bN (pc : Nat) : Bool :=
  inN 4194304 4194404 pc || inN 4194892 4195347 pc || inN 4195445 4195469 pc || inN 4195595 4196063 pc

/-- **The stack is not taken yet**: as `bN`, and `scc_rt_stack_take` up to
and including the take site. -/
def bT (pc : Nat) : Bool :=
  inN 4194304 4194404 pc || inN 4194892 4195347 pc || inN 4195445 4195469 pc || inN 4195595 4196178 pc

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

/-! ## The marks -/

/-- **The loaded program's marks**: the take and release sites, the five
abort sites. -/
def μ0 : Marks where
  site
    | .take => some 4196177
    | .release => some 4196217
  abortAt
    | .overflow => some 4198555
    | .heap => some 4198623
    | .stack => some 4198691
    | .writeErr => some 4198759
    | .threads => some 4198827

/-- **The canonical target's marks of `ret0`** are `μ0`, given the
loader's parse of the text (`hpa`, the trust boundary). -/
theorem ret0_marks (hpa : Scc.Sem.X64.cellsOf ret0Asm = some ret0Cells) : T.marks ret0Asm ret0Λ = μ0 := by
  have hr := Scc.Sem.X64.resolve_of_parsed (Scc.Sem.X64.kernel 1) Scc.Sem.Entry.linux ret0Λ hpa
  unfold Scc.Sem.Target.marks
  congr 1
  · funext k; cases k <;> exact (hr _).trans (by decide +kernel)
  · funext k; cases k <;> exact (hr _).trans (by decide +kernel)

/-- **The pcs off the marks' sites.** -/
def okPc (pc : Nat) : Bool := !([4196177, 4196217, 4198555, 4198623, 4198691, 4198759, 4198827].contains pc)

/-- A pc off the sites is off `μ0`'s, with no take there. -/
theorem pcOff_of_okPc {rS : Range} : ∀ s : State, okPc (pcOf s) = true →
    PcOff μ0 s ∧ ∀ s', ¬ TakeK (labT StackTake.siteL) rS s s' := by
  intro s h
  have hne : ∀ a ∈ [4196177, 4196217, 4198555, 4198623, 4198691, 4198759, 4198827], pcOf s ≠ a := by
    intro a ha he
    subst he
    simp only [okPc, Bool.not_eq_true', List.contains_eq_any_beq, List.any_eq_false, beq_iff_eq] at h
    exact h _ ha rfl
  refine ⟨⟨fun a ha => ?_, fun a ha => ?_, fun k a ha => ?_⟩, fun s' hk => ?_⟩
  · cases ha; exact hne _ (by simp)
  · cases ha; exact hne _ (by simp)
  · cases k <;> cases ha <;> exact hne _ (by simp)
  · have := congrArg (fun x : Int64 => x.toBitVec.toNat) (TakeK.pc hk)
    exact hne 4196177 (by simp) (by unfold pcOf; rw [this]; decide +kernel)

/-! ## A block's states -/

section Blk

variable {rS : Range}

/-- **The per-state facts of `ret0`**: `SFacts` at the loaded program's
marks and owned words, no label placed. -/
abbrev Wr (rS : Range) : Frag isa := fun s c => SFacts ret0Λ μ0 own rS Tk ret0Λ.static s c

/-- **The outside move**: the take at the take site. -/
abbrev Kr (rS : Range) : State → State → Prop := TakeK (labT StackTake.siteL) rS

/-- A state not in the take's phase, at a pc whose phase says so. -/
theorem not_tk {s : State} (h : bT (pcOf s) = true) : ¬ Tk s := by
  unfold Tk ph
  rw [h]
  cases bP (pcOf s) <;> cases bL (pcOf s) <;> cases bN (pcOf s) <;> decide

/-- A block of the cells at its label, in the loaded thread. -/
theorem codeT {l : Label} {off : Nat} {b : List (Directive × Nat)} (hb : blockAtB ret0Cells l off b = true)
    {s : State} (hs : s.exe = ret0Exe) (hn : s.endPc = ret0End) : CodeAt s (labT l + Int64.ofNat off) b :=
  code_field ret0_lays rfl hb (by rw [ret0_labT]) s hs hn

/-- **A covered block of the main path before the take** is inside `Wr`:
its code (`hb`), its cover (`hok`), the region's facts, the source
control's facts at the node (`hC`), the phase check (`hph`) and its dead
targets never reached (`hdead`), every `ret` returning to `ra` (`hret`),
and the entry not in the take's phase (`hT`). -/
theorem blkW_pre {R : Region} {F : MachineData → Prop} {n : ND} {blk : List (Directive × Nat)} {lo hi : Int}
    {dead : Nat → Bool} {ra : Int64} {l : Label} {off : Nat}
    (hb : blockAtB ret0Cells l off blk = true) (he : labT l + Int64.ofNat off = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c)
    (hph : blkPh okPc ph dead labT (labT l + Int64.ofNat off) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun labT (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun labT (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra)
    (hdead : ∀ σ c, n.J σ c → dead (arun labT blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hT : bT (labT l + Int64.ofNat off).toBitVec.toNat = true) :
    BlkW (Wr rS) (Kr rS) ret0Exe ret0End R F n blk := by
  rw [he] at hph hT
  have hcode : ∀ s : State, s.exe = ret0Exe → s.endPc = ret0End → CodeAt s n.pc blk := fun s hs hn =>
    he ▸ codeT hb hs hn
  rw [← ret0_labT] at hph hret hdead
  obtain ⟨hpc, hph', hsm⟩ := blkPh_sound (μ := μ0) (endPc := ret0End) ph_same pcOff_of_okPc hok hph hret hdead
  refine blkW_sfacts hcode hok hR hlo hhi hC hpc hph' fun s m _ _ _ k hk s' _ hpc' htk => ?_
  have := (hsm k hk { s' with st := (s'.st.1, n.pc) } s' rfl hpc').2.mp htk
  exact absurd this (not_tk (by unfold pcOf; exact hT))

/-- **A covered block of the main path after the take** is inside `Wr`: as
`blkW_pre` without the phase's entry check, its frame condition also
`StackM rS` (kept by the region's writes, `hSM`) and `rS` in the pool
(`hsub`), so its states own the range. -/
theorem blkW_post {R : Region} {F : MachineData → Prop} {n : ND} {blk : List (Directive × Nat)} {lo hi : Int}
    {dead : Nat → Bool} {ra : Int64} {l : Label} {off : Nat}
    (hb : blockAtB ret0Cells l off blk = true) (he : labT l + Int64.ofNat off = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c)
    (hph : blkPh okPc ph dead labT (labT l + Int64.ofNat off) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun labT (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun labT (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra)
    (hdead : ∀ σ c, n.J σ c → dead (arun labT blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hsub : rS.Sub ret0Λ.stackPool) (hSM : FStable R (StackM rS)) :
    BlkW (Wr rS) (Kr rS) ret0Exe ret0End R (fun m => F m ∧ StackM rS m) n blk := by
  rw [he] at hph
  have hcode : ∀ s : State, s.exe = ret0Exe → s.endPc = ret0End → CodeAt s n.pc blk := fun s hs hn =>
    he ▸ codeT hb hs hn
  rw [← ret0_labT] at hph hret hdead
  obtain ⟨hpc, hph', -⟩ := blkPh_sound (μ := μ0) (endPc := ret0End) ph_same pcOff_of_okPc hok hph hret hdead
  refine blkW_sfacts hcode hok hR hlo hhi hC hpc hph' fun s m hF hD _ k hk s' hm _ _ => ?_
  refine ⟨hsub, fun a h8 ha ha7 => ?_⟩
  unfold Scc.Sem.X64.privLoad
  rw [Option.isSome_map, hm]
  exact hSM _ _ hF.2 hD a h8 ha ha7

/-- **The range owned from a region's cells and the words off it**: every
aligned word of `rS` either lies off the 8-aligned region `R` (`hoff`) or is
one of its cells (`hc`). -/
theorem owned_off {R : Region} (hR : R.OK) (hb : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub ret0Λ.stackPool) {s : State} (hoff : StackOff rS R s.st.1)
    (hc : ∀ k, R.Off k → (Mem.loadInt s.st.1.dmem (R.addr k) 8).isSome) : Owned ret0Λ rS s := by
  refine ⟨hsub, fun a h8 ha ha7 => ?_⟩
  unfold Scc.Sem.X64.privLoad
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
    (hh : R.hi % 8 = 0) {kc lo' hi' : Int} (hlo : R.lo ≤ kc + lo') (hlo0 : lo' ≤ 0) (hkc : kc < R.hi)
    (hk8 : kc % 8 = 0) {m : MachineData} (hoff : StackOff rS R m) (hcc : CallerCells R kc lo' hi' m) :
    StackOff rS (R.callee kc lo' hi') m := by
  intro a h8 ha ha7 hout'
  have hcb := Region.callee_base (hi' := hi') hR hlo hlo0 hkc
  by_cases hout : (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a
  · exact hoff a h8 ha ha7 hout
  · have h1 := hR.lo
    have h2 := hR.hi
    have hk : R.Off ((a : Int) - R.base.toNat) := ⟨by omega, by omega, by omega⟩
    have hn : ¬ (R.callee kc lo' hi').Off ((a : Int) - R.base.toNat - kc) := by
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

/-- **A covered block of the main path after the switch**, in an 8-aligned
region whose frame condition gives the words of `rS` off it (`hFO`): as
`blkW_post`, `rS` not wrapping (`hfit`). -/
theorem blkW_postO {R : Region} {F : MachineData → Prop} {n : ND} {blk : List (Directive × Nat)} {lo hi : Int}
    {dead : Nat → Bool} {ra : Int64} {l : Label} {off : Nat}
    (hb : blockAtB ret0Cells l off blk = true) (he : labT l + Int64.ofNat off = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c)
    (hph : blkPh okPc ph dead labT (labT l + Int64.ofNat off) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun labT (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun labT (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra)
    (hdead : ∀ σ c, n.J σ c → dead (arun labT blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hsub : rS.Sub ret0Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    BlkW (Wr rS) (Kr rS) ret0Exe ret0End R F n blk := by
  rw [he] at hph
  have hcode : ∀ s : State, s.exe = ret0Exe → s.endPc = ret0End → CodeAt s n.pc blk := fun s hs hn =>
    he ▸ codeT hb hs hn
  rw [← ret0_labT] at hph hret hdead
  obtain ⟨hpc, hph', -⟩ := blkPh_sound (μ := μ0) (endPc := ret0End) ph_same pcOff_of_okPc hok hph hret hdead
  refine blkW_sfacts hcode hok hR hlo hhi hC hpc hph' fun s m hF hD hc k hk s' hm _ _ => ?_
  subst hm
  exact owned_off hR hR8 hl hh hsub (stackOff_stable hfit _ _ (hFO _ hF) hD) hc

end Blk

/-! ## A single instruction's states -/

section Node

open Kraken.Promising.Lower.X64 (CellAt after exec_store_agrees exec_load_agrees exec_xaddG_agrees
  exec_xchgG_agrees eaddr exec_movfs_load_agrees fsAddr)
open Spike.Lib.X64.Flow.Ret0.Mem (ret0Words ret0F ret0Words_mapped)

variable {rS : Range} {R : Region} {F : MachineData → Prop}

/-- An instruction of the cells at its label, in the loaded thread. -/
theorem cellT {l : Label} {off z : Nat} {d : Directive} {p : Int64} (hb : blockAtB ret0Cells l off [(d, z)] = true)
    (he : labT l + Int64.ofNat off = p) {s : State} (hs : s.exe = ret0Exe) (hn : s.endPc = ret0End)
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
    (h : ∀ s c σ, s.exe = ret0Exe → s.endPc = ret0End → s.decls = {} → s.st.2 = p → Abs R n.o s.st.1 σ →
      F s.st.1 → n.J σ c → PcOff μ0 s → (Tk s → Owned ret0Λ rS s) → Wr rS s c) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hP := pcOff_of_okPc (rS := rS) s (by unfold pcOf; rw [hpc]; exact hok)
  exact ⟨h s c σ hs hn hdc hpc hA hD hJ hP.1 fun h' => absurd h' (not_tk (by unfold pcOf; rw [hpc]; exact hT)), hP.2⟩

/-- **A node at a single instruction without an event** (`SI`) before the
take, its next pc in its phase. -/
theorem nodeW_si_pre {n : ND} {si : SI} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB ret0Cells l off [(si.toDir, z)] = true) (he : labT l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  nodeW_pre hp hok hT fun _s c σ hs hn _ hpc _ _ hJ hP hO =>
    sfacts_si (hC σ c hJ) hP (cellT hb he hs hn hpc) (next_same hpc hph) hO

/-- **A node at an instruction with undefined flags** (`FI`) before the
take, its next pc in its phase. -/
theorem nodeW_fi_pre {n : ND} {fi : FI} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB ret0Cells l off [(fi.toDir, z)] = true) (he : labT l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  nodeW_pre hp hok hT fun _s c σ hs hn _ hpc _ _ hJ hP hO =>
    sfacts_fi (hC σ c hJ) hP (cellT hb he hs hn hpc) (next_same hpc hph) hO

/-- **A node at a runtime store** `movq %r, k(%b)` to a word `a` of
`ret0Words` no phase owns, before the take, its next pc in its phase. -/
theorem nodeW_st_pre {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    {a : BitVec 64} (hb : blockAtB ret0Cells l off [(stDir b k r, z)] = true) (he : labT l + Int64.ofNat off = p)
    (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (ha : ∀ σ c, n.J σ c → bAddr σ.regs b k = a) (hw : a ∈ ret0Words) (hFr : ∀ m, F m → ret0F m)
    (hno : ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  nodeW_pre hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellT hb he hs hn hpc
    have ha' : eaddr s z (mB b k) = a := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha σ c hJ)
    have hex := exec_store_agrees hc ha' (hFr _ hD a hw) (agrees_of_decls hdc _ _)
    obtain ⟨hT', hown, htk⟩ := store_facts (Λ := ret0Λ) (own := own) (Tk := Tk) (k := .plain) (s := s)
      (m := s.st.1) (V := (s.st.1.regs.get (.low r .W64)).setWidth 128) (ret0Words_mapped hw).1
      (next_same hpc hph _).2 (.inl ⟨(next_same hpc hph _).1, fun w h => by rw [own_at hpc] at h; exact hno _ w h⟩)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hT' hown htk hO

/-- **A node at an owned counter's `lock xaddq %r, k(%b)`** before the
take, its next pc before it too: the counter's word `a` (`ha`), owned at
`p` (`hin`), updated to the sum at the next pc (`hupd`). -/
theorem nodeW_xadd_pre {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    {a : BitVec 64} (hb : blockAtB ret0Cells l off [(xaddDir b k r, z)] = true)
    (he : labT l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hT' : bT (p + Int64.ofNat z).toBitVec.toNat = true)
    (ha : ∀ σ c, n.J σ c → bAddr σ.regs b k = a) (hw : a ∈ ret0Words) (hFr : ∀ m, F m → ret0F m)
    (hin : ∃ v, (⟨a, 8⟩, v) ∈ ownOf (ph p.toBitVec.toNat))
    (hupd : ∀ σ c, n.J σ c → ownUpdB (ownOf (ph p.toBitVec.toNat)) (ownOf (ph (p + Int64.ofNat z).toBitVec.toNat))
      ⟨a, 8⟩ (fun old => (old.setWidth 64 + σ.regs.get64 r).setWidth 128) = true) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  nodeW_pre hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellT hb he hs hn hpc
    have ha' : eaddr s z (mB b k) = a := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha σ c hJ)
    have hex := exec_xaddG_agrees (w := .W64) hc ha' (hFr _ hD a hw) (agrees_of_decls hdc _ _)
    have hpc4 : ∀ m, (after s z m).st.2 = p + Int64.ofNat z := fun _ => by rw [← hpc]
    obtain ⟨hT'', hown, htk⟩ := rmw_facts (Λ := ret0Λ) (own := own) (Tk := Tk) (s := s) (k := .acqRel)
      (nr := false) (z := z)
      (op := fun old => some ((old.setWidth 64 + s.st.1.regs.get (.low r .W64)).setWidth 128))
      (m := fun v => { s.st.1 with
        regs := s.st.1.regs.set (.low r .W64) (v.setWidth 64)
        status := LockBinOp.add.status (v.setWidth 64) (s.st.1.regs.get (.low r .W64))
          (v.setWidth 64 + s.st.1.regs.get (.low r .W64)) false })
      (ret0Words_mapped hw).1 (fun _ => next_tk hpc (by rw [hT, hT']) _) (by rw [own_at hpc]; exact hin)
      (fun v hv => by
        rw [own_at hpc, own_at (hpc4 _), Option.getD_some, Reg64s.get_low64, hA.regs]
        rw [own_at hpc] at hv
        exact ownUpd_of (hupd σ c hJ) v hv)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hT'' hown htk hO

/-- **A node at an owned word's `xchgq %r, k(%b)`** before the take, its
next pc before it too: the word `a` (`ha`), owned at `p` (`hin`), set to
`%r` at the next pc (`hupd`). -/
theorem nodeW_xchg_pre {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    {a : BitVec 64} (hb : blockAtB ret0Cells l off [(xchgDir b k r, z)] = true)
    (he : labT l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hT' : bT (p + Int64.ofNat z).toBitVec.toNat = true)
    (ha : ∀ σ c, n.J σ c → bAddr σ.regs b k = a) (hw : a ∈ ret0Words) (hFr : ∀ m, F m → ret0F m)
    (hin : ∃ v, (⟨a, 8⟩, v) ∈ ownOf (ph p.toBitVec.toNat))
    (hupd : ∀ σ c, n.J σ c → ownUpdB (ownOf (ph p.toBitVec.toNat)) (ownOf (ph (p + Int64.ofNat z).toBitVec.toNat))
      ⟨a, 8⟩ (fun _ => (σ.regs.get64 r).setWidth 128) = true) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  nodeW_pre hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellT hb he hs hn hpc
    have ha' : eaddr s z (mB b k) = a := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha σ c hJ)
    have hex := exec_xchgG_agrees (w := .W64) hc ha' (hFr _ hD a hw) (agrees_of_decls hdc _ _)
    have hpc4 : ∀ m, (after s z m).st.2 = p + Int64.ofNat z := fun _ => by rw [← hpc]
    obtain ⟨hT'', hown, htk⟩ := rmw_facts (Λ := ret0Λ) (own := own) (Tk := Tk) (s := s) (k := .acqRel)
      (nr := false) (z := z)
      (op := fun _ => some ((s.st.1.regs.get (.low r .W64)).setWidth 128))
      (m := fun v => { s.st.1 with regs := s.st.1.regs.set (.low r .W64) (v.setWidth 64) })
      (ret0Words_mapped hw).1 (fun _ => next_tk hpc (by rw [hT, hT']) _) (by rw [own_at hpc]; exact hin)
      (fun v hv => by
        rw [own_at hpc, own_at (hpc4 _), Option.getD_some, Reg64s.get_low64, hA.regs]
        rw [own_at hpc] at hv
        exact ownUpd_of (hupd σ c hJ) v hv)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hT'' hown htk hO

/-- **A node at a load `movq k(%b), %r` of a word of `ret0Words`** before
the take, its next pc in its phase. -/
theorem nodeW_ld_pre {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    {a : BitVec 64} (hb : blockAtB ret0Cells l off [(ldDir b k r, z)] = true) (he : labT l + Int64.ofNat off = p)
    (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (ha : ∀ σ c, n.J σ c → bAddr σ.regs b k = a) (hw : a ∈ ret0Words) (hFr : ∀ m, F m → ret0F m) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  nodeW_pre hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellT hb he hs hn hpc
    have ha' : eaddr s z (mB b k) = a := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha σ c hJ)
    have hex := exec_load_agrees hc ha' (hFr _ hD a hw) (agrees_of_decls hdc _ _)
    obtain ⟨hT', hown, htk⟩ := load_facts (Λ := ret0Λ) (own := own) (Tk := Tk) (k := .plain) (s := s) (z := z)
      (m := fun v => { s.st.1 with regs := s.st.1.regs.set (.low r .W64) (v.setWidth 64) })
      (ret0Words_mapped hw).2.1 (fun _ => (next_same hpc hph _).2) (fun _ => (next_same hpc hph _).1)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hT' hown htk hO

/-- **A node at an owned word's plain store `movq %r, k(%b)`** before the
take, its next pc before it too: the word `a` (`ha`), owned at `p` (`hin`),
set to `%r` at the next pc (`hupd`). The lock's release on the bump path. -/
theorem nodeW_stown_pre {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    {a : BitVec 64} (hb : blockAtB ret0Cells l off [(stDir b k r, z)] = true) (he : labT l + Int64.ofNat off = p)
    (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hT' : bT (p + Int64.ofNat z).toBitVec.toNat = true)
    (ha : ∀ σ c, n.J σ c → bAddr σ.regs b k = a) (hw : a ∈ ret0Words) (hFr : ∀ m, F m → ret0F m)
    (hin : ∃ v, (⟨a, 8⟩, v) ∈ ownOf (ph p.toBitVec.toNat))
    (hupd : ∀ σ c, n.J σ c → ownUpdB (ownOf (ph p.toBitVec.toNat)) (ownOf (ph (p + Int64.ofNat z).toBitVec.toNat))
      ⟨a, 8⟩ (fun _ => (σ.regs.get64 r).setWidth 128) = true) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  nodeW_pre hp hok hT fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellT hb he hs hn hpc
    have ha' : eaddr s z (mB b k) = a := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha σ c hJ)
    have hex := exec_store_agrees hc ha' (hFr _ hD a hw) (agrees_of_decls hdc _ _)
    have hpc4 : (after s z s.st.1).st.2 = p + Int64.ofNat z := by rw [← hpc]
    obtain ⟨v, hv⟩ := hin
    obtain ⟨hT'', hown, htk⟩ := store_facts (Λ := ret0Λ) (own := own) (Tk := Tk) (k := .plain) (s := s) (z := z)
      (m := s.st.1) (V := (s.st.1.regs.get (.low r .W64)).setWidth 128) (ret0Words_mapped hw).1
      (next_tk hpc (by rw [hT, hT']) _)
      (.inr (by rw [own_at hpc, own_at hpc4, Reg64s.get_low64, hA.regs]; exact ownUpd_of (hupd σ c hJ) v hv))
    exact sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hT'' hown htk hO

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
  unfold Scc.Sem.X64.privLoad
  rw [Option.isSome_map]
  exact hD.2 a h8 ha ha7

/-- `rt_sigaction`'s number is in `%rax` at `scc_rt_start`'s system call. -/
theorem startS2_rax (lab : Label → Int64) (σ : AS) : (startS2 lab σ).regs.rax.toNat = 13 := by
  simp [startS2, xStartArgs_run]; rfl

/-- **A node at a `syscall`** (`z` bytes) before the take, its next pc in
its phase, its `%rax` not `write`'s number (`hnr`). -/
theorem nodeW_syscall_pre {n : ND} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB ret0Cells l off [(Kraken.Promising.Lower.X64.op64 .syscall, z)] = true)
    (he : labT l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (hnr : ∀ σ c, n.J σ c → σ.regs.rax.toNat ≠ 1) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  nodeW_pre hp hok hT fun _s c σ hs hn _ hpc hA _ hJ hP hO =>
    sfacts_syscall (hC σ c hJ) hP (cellT hb he hs hn hpc) (next_same hpc hph) hO
      (decode_ne_write _ (by show _s.st.1.regs.rax.toNat ≠ 1; rw [hA.regs]; exact hnr σ c hJ))

/-- **A node at a `syscall`** (`z` bytes) after the take, its next pc in
its phase, its `%rax` not `write`'s number (`hnr`). -/
theorem nodeW_syscall_post {n : ND} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB ret0Cells l off [(Kraken.Promising.Lower.X64.op64 .syscall, z)] = true)
    (he : labT l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat) (hsub : rS.Sub ret0Λ.stackPool)
    (hnr : ∀ σ c, n.J σ c → σ.regs.rax.toNat ≠ 1) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R (fun m => F m ∧ StackM rS m) n :=
  nodeW_post hp hok hsub fun _s c σ hs hn _ hpc hA _ hJ hP hO =>
    sfacts_syscall (hC σ c hJ) hP (cellT hb he hs hn hpc) (next_same hpc hph) hO
      (decode_ne_write _ (by show _s.st.1.regs.rax.toNat ≠ 1; rw [hA.regs]; exact hnr σ c hJ))

/-- **A node at a runtime store** `movq %r, k(%b)` to a word `a` of
`ret0Words` no phase owns, after the take, its next pc in its phase. -/
theorem nodeW_st_post {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    {a : BitVec 64} (hb : blockAtB ret0Cells l off [(stDir b k r, z)] = true) (he : labT l + Int64.ofNat off = p)
    (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (ha : ∀ σ c, n.J σ c → bAddr σ.regs b k = a) (hw : a ∈ ret0Words) (hFr : ∀ m, F m → ret0F m)
    (hno : ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j) (hsub : rS.Sub ret0Λ.stackPool) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R (fun m => F m ∧ StackM rS m) n :=
  nodeW_post hp hok hsub fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellT hb he hs hn hpc
    have ha' : eaddr s z (mB b k) = a := (eaddr_mB s z b k).trans (by rw [hA.regs]; exact ha σ c hJ)
    have hex := exec_store_agrees hc ha' (hFr _ hD a hw) (agrees_of_decls hdc _ _)
    obtain ⟨hT', hown, htk⟩ := store_facts (Λ := ret0Λ) (own := own) (Tk := Tk) (k := .plain) (s := s)
      (m := s.st.1) (V := (s.st.1.regs.get (.low r .W64)).setWidth 128) (ret0Words_mapped hw).1
      (next_same hpc hph _).2 (.inl ⟨(next_same hpc hph _).1, fun w h => by rw [own_at hpc] at h; exact hno _ w h⟩)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hT' hown htk hO

/-- **A node of the main path after the take**, in an 8-aligned region
whose frame condition gives the words of `rS` off it (`hFO`): as
`nodeW_post`. -/
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

/-- **A node at a thread-pointer load `movq %fs:k, %d` of a word of
`ret0Words`** after the take, unmapped in private memory under the frame
condition (`hun`), as `nodeW_postO`, its next pc in its phase. -/
theorem nodeW_fsld_postO {n : ND} {d : Reg64} {k : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    {a : BitVec 64} (hb : blockAtB ret0Cells l off [(fsDir d k, z)] = true) (he : labT l + Int64.ofNat off = p)
    (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (ha : ∀ σ c, n.J σ c → σ.regs.fsBase.toBitVec + k.toBitVec = a) (hw : a ∈ ret0Words)
    (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub ret0Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  nodeW_postO hp hok hR hR8 hl hh hsub hFO fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellT hb he hs hn hpc
    have ha' : fsAddr s z { base := none, idx := none, disp := .int64 k } = a := by
      rw [← ha σ c hJ]
      simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs]
    have hex := exec_movfs_load_agrees hc ha' (hun _ hD) (agrees_of_decls hdc _ _)
    obtain ⟨hT', hown, htk⟩ := load_facts (Λ := ret0Λ) (own := own) (Tk := Tk) (k := .plain) (s := s) (z := z)
      (m := fun v => { s.st.1 with regs := s.st.1.regs.set (.low d .W64) (v.setWidth 64) })
      (ret0Words_mapped hw).2.1 (fun _ => (next_same hpc hph _).2) (fun _ => (next_same hpc hph _).1)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hT' hown htk hO

/-- **A node at a `syscall`** (`z` bytes) after the take, as `nodeW_postO`,
its next pc in its phase, its `%rax` not `write`'s number (`hnr`). -/
theorem nodeW_syscall_postO {n : ND} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB ret0Cells l off [(Kraken.Promising.Lower.X64.op64 .syscall, z)] = true)
    (he : labT l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub ret0Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (hnr : ∀ σ c, n.J σ c → σ.regs.rax.toNat ≠ 1) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  nodeW_postO hp hok hR hR8 hl hh hsub hFO fun _s c σ hs hn _ hpc hA _ hJ hP hO =>
    sfacts_syscall (hC σ c hJ) hP (cellT hb he hs hn hpc) (next_same hpc hph) hO
      (decode_ne_write _ (by show _s.st.1.regs.rax.toNat ≠ 1; rw [hA.regs]; exact hnr σ c hJ))

/-- **A node at an instruction with undefined flags** (`FI`) after the
take, as `nodeW_postO`, its next pc in its phase. -/
theorem nodeW_fi_postO {n : ND} {fi : FI} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB ret0Cells l off [(fi.toDir, z)] = true) (he : labT l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub ret0Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  nodeW_postO hp hok hR hR8 hl hh hsub hFO fun _s c σ hs hn _ hpc _ _ hJ hP hO =>
    sfacts_fi (hC σ c hJ) hP (cellT hb he hs hn hpc) (next_same hpc hph) hO

/-- **A node at a register operation** after the take, the range in private
memory, its next pc in its phase. -/
theorem nodeW_reg_post {n : ND} {w : Width} {op : Operation w} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    (hop : RegOnly op = true) (hb : blockAtB ret0Cells l off [(.instr (.regular .W64 w op), z)] = true)
    (he : labT l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat) (hsub : rS.Sub ret0Λ.stackPool) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R (fun m => F m ∧ StackM rS m) n :=
  nodeW_post hp hok hsub fun s c σ hs hn _ hpc _ _ hJ hP hO => by
    have hc := cellT hb he hs hn hpc
    exact sfacts_done (hC σ c hJ) hP hc (fun w w' h => by cases h; simp [RegOnly] at hop) (exec_reg hop hc)
      (next_same hpc hph _).1 (next_same hpc hph _).2 hO

end Node

/-! ## `scc_rt_alloc_tcb` -/

section Tcb

open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Ret0.Mem (ret0F)

variable {rS : Range} {c0 : Ctl} {F : MachineData → Prop}

theorem labT_pnA : pnA labT = 6291472#64 := by rw [← ret0_labT]; exact Mem.ret0_pnA
theorem labT_pinA : pinA labT = 134217728#64 := by rw [← ret0_labT]; exact Mem.ret0_pinA
theorem labT_lockA : lockA labT = 6291496#64 := by rw [← ret0_labT]; exact Mem.ret0_lockA
theorem labT_freeNA : freeNA labT = 6291504#64 := by rw [← ret0_labT]; exact Mem.ret0_freeNA
theorem labT_nextA : nextA labT = 6291488#64 := by rw [← ret0_labT]; exact Mem.ret0_nextA

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
(`hC0`, its facts) and the frame condition implying `ret0F`. -/
theorem tcbW (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region} (hR : R.OK) (hlo : R.lo ≤ -184) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → ret0F m) (q : TcbG) (hq : q.c0 = c0) (hn0 : q.n0 = 0#64)
    (hra : q.g.ra = (labT ".Lscc_rt_start.x0").toBitVec) :
    ∀ i, TcbW (Wr rS) (Kr rS) ret0Exe ret0End R F q i := by
  intro i
  cases i
  case e => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.fnL 0 AllocTcb.atPro_ok
  case entry =>
    show BlkW _ _ _ _ _ _ _ _
    rw [ret0_labT]
    exact blkW_pre (l := AllocTcb.entryL) (off := 0) (dead := fun t => t == 4195133) (ra := 0)
      (by decide +kernel) (ofNat_zero' _) AllocTcb.atChk_ok hR (by omega) (by omega)
      (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk hr => (noRet_false (by decide +kernel) k hk hr).elim)
      (fun _ _ hJ => by dsimp only [tcbN] at hJ ⊢; rw [(AllocTcb.atChk_walk labT _ hJ.2).1]; decide +kernel)
      (by decide +kernel)
  case j1 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.entryL 20 AllocTcb.atJ1_ok
  case len => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.lenL 0 AllocTcb.atL0_ok
  case shr1 => show NodeW _ _ _ _ _ _ _; rw [ret0_labT]; tfi (.shr_cl .rax) 3 AllocTcb.lenL 11
  case l1 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.lenL 14 AllocTcb.atL1_ok
  case and1 => show NodeW _ _ _ _ _ _ _; rw [ret0_labT]; tfi (.and_rr .rax .rcx) 3 AllocTcb.lenL 29
  case l2 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.lenL 32 AllocTcb.atL2_ok
  case shr2 => show NodeW _ _ _ _ _ _ _; rw [ret0_labT]; tfi (.shr_cl .rax) 3 AllocTcb.lenL 47
  case l3 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.lenL 50 AllocTcb.atL3_ok
  case and2 => show NodeW _ _ _ _ _ _ _; rw [ret0_labT]; tfi (.and_rr .rax .rcx) 3 AllocTcb.lenL 65
  case l4 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.lenL 68 AllocTcb.atL4_ok
  case imul1 => show NodeW _ _ _ _ _ _ _; rw [ret0_labT]; tfi (.imul_rr .rax .rcx) 4 AllocTcb.lenL 95
  case l5 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.lenL 99 AllocTcb.atL5_ok
  case shl1 => show NodeW _ _ _ _ _ _ _; rw [ret0_labT]; tfi (.shl_cl .rax) 3 AllocTcb.lenL 132
  case l6 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.lenL 135 AllocTcb.atL6_ok
  case lea1 =>
    show NodeW _ _ _ _ _ _ _; rw [ret0_labT]; tsi (.leaRip .rax "scc_rt_pinned_next") 7 AllocTcb.lenL 139
  case arg => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.lenL 146 AllocTcb.atArg_ok
  case rmw =>
    show NodeW _ _ _ _ _ _ _
    rw [ret0_labT]
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
  case bnd => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.lenL 163 AllocTcb.atBnd_ok
  case j2 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.lenL 198 AllocTcb.atJ2_ok
  case ok => show NodeW _ _ _ _ _ _ _; rw [ret0_labT]; tsi (.leaRip .rax "scc_rt_pinned") 7 AllocTcb.okL 0
  case o1 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.okL 7 AllocTcb.atO1_ok
  case imul2 => show NodeW _ _ _ _ _ _ _; rw [ret0_labT]; tfi (.imul_rr .rax .rcx) 4 AllocTcb.okL 34
  case o2 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.okL 38 AllocTcb.atO2_ok
  case shl2 => show NodeW _ _ _ _ _ _ _; rw [ret0_labT]; tfi (.shl_cl .rax) 3 AllocTcb.okL 53
  case o3 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.okL 56 AllocTcb.atO3_ok
  case shl3 => show NodeW _ _ _ _ _ _ _; rw [ret0_labT]; tfi (.shl_cl .rax) 3 AllocTcb.okL 74
  case o4 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.okL 77 AllocTcb.atO4_ok
  case or1 => show NodeW _ _ _ _ _ _ _; rw [ret0_labT]; tfi (.or_rr .rax .rcx) 3 AllocTcb.okL 95
  case o5 => show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]; tblk AllocTcb.okL 98 AllocTcb.atO5_ok
  case hdr =>
    show NodeW _ _ _ _ _ _ _
    rw [ret0_labT]
    refine nodeW_st_pre (b := .rcx) (k := 0) (r := .rax) (z := 3) (l := AllocTcb.okL) (off := 140)
      (a := 134217728#64) (by decide +kernel) rfl rfl (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (fun σ _ hJ => ?_) (by decide) hFr (not_own (by decide))
    obtain ⟨-, -, -, hc⟩ := hJ
    rw [hn0, labT_pinA] at hc
    have h : σ.regs.rcx.toBitVec = 134217728#64 := by rw [hc]; rfl
    simp [bAddr, Reg64s.get64, h]
  case ret =>
    show BlkW _ _ _ _ _ _ _ _
    rw [ret0_labT]
    exact blkW_pre (l := AllocTcb.okL) (off := 143) (dead := fun _ => false) (ra := labT ".Lscc_rt_start.x0")
      (by decide +kernel) rfl AllocTcb.atRet_ok hR (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0)
      (by decide +kernel)
      (hret_of_run AllocTcb.atRet_ok fun _ _ hJ => by
        dsimp only [tcbN] at hJ ⊢
        rw [(AllocTcb.atRet_walk labT _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ _ _ => rfl) (by decide +kernel)

end Tcb

/-! ## `scc_rt_stack_take` -/

section Take

open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Ret0.Mem (ret0F)
open Kraken.Promising.Lower.X64 (after op64)

variable {rS : Range} {c0 : Ctl} {F : MachineData → Prop}

set_option hygiene false in
/-- A block of `scc_rt_stack_take` before the take, no `ret`, no dead target. -/
local macro "kblk " l:term:max k:term:max ok:term:max : tactic =>
  `(tactic| focus
    show BlkW _ _ _ _ _ _ _ _
    rw [ret0_labT]
    exact blkW_pre (l := $l) (off := $k) (dead := fun _ => false) (ra := 0) (by decide +kernel)
      (by first | rfl | exact ofNat_zero' _) $ok hR (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0)
      (by decide +kernel) (fun _ _ _ k hk hr => (noRet_false (by decide +kernel) k hk hr).elim)
      (fun _ _ _ => rfl) (by decide +kernel))

set_option hygiene false in
/-- A `leaq L(%rip), %rax` of `scc_rt_stack_take`. -/
local macro "ksi " L:term:max l:term:max k:term:max : tactic =>
  `(tactic| focus
    show NodeW _ _ _ _ _ _ _
    rw [ret0_labT]
    exact nodeW_si_pre (si := .leaRip .rax $L) (z := 7) (l := $l) (off := $k) (p := labT $l + Int64.ofNat $k)
      (by decide +kernel) rfl (by first | rfl | exact (ofNat_zero' _).symm)
      (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel) (by decide +kernel) (by decide +kernel))

/-- **The take site is `μ0`'s.** -/
theorem mu0_take : μ0.site .take = some (labT StackTake.siteL).toBitVec.toNat := by
  decide +kernel

/-- **The take site's states are inside `Wr`**: the 1-byte `nop` at the
take site, not in the take's phase, the take landing in it with the owned
words unchanged, given the source control `c0` (`hC0`, its facts), the range
named by the site's registers (`hrS`: `%rdi = stacksA + k0`,
`%rsi = 16384`) in the pool (`hsub`). The `nop` as an instruction is asked
off the transfer sites only (`SFacts.tkInstr`), and this pc is `μ0`'s take
site (`mu0_take`). -/
theorem takeSiteW (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region} (q : TakeG) (hq : q.c0 = c0)
    (hrS : rS = ⟨(stacksA labT + q.k0).toNat, 16384⟩) (hsub : rS.Sub ret0Λ.stackPool) :
    TakeW (Wr rS) (Kr rS) ret0Exe ret0End R F (StackM rS) q .site := by
  dsimp only [TakeW]
  rw [ret0_labT]
  rintro s c ⟨hs, hn, -, hpc, σ, hA, -, hc, -, h0, h1⟩
  have hcl := cellT (l := StackTake.siteL) (off := 0) (z := 1) (d := op64 (.nop 1)) (by decide +kernel)
    (ofNat_zero' _) hs hn hpc
  have hpcN : pcOf s = (labT StackTake.siteL).toBitVec.toNat := by unfold pcOf; rw [hpc]; rfl
  have hpcV : pcOf s = 4196177 := by rw [hpcN]; decide +kernel
  have hpc1 : ∀ m, (after s 1 m).st.2 = labT StackTake.siteL + Int64.ofNat 1 := fun _ => by
    show s.st.2 + Int64.ofNat 1 = _; rw [hpc]; rfl
  refine sfacts_site (hc ▸ hq ▸ hC0) (fun a ha => ?_) (fun k a ha => ?_) hcl
    (not_tk (by rw [hpcV]; decide)) ⟨?_, hsub, by rw [hrS]; show 0 < 16384; decide,
      by unfold Scc.Sem.Range.Disjoint; decide +kernel⟩ (fun m => ?_)
    (fun m => ?_) (by rw [hpcN]; exact mu0_take)
  · cases ha; rw [hpcV]; decide
  · cases k <;> cases ha <;> rw [hpcV] <;> decide
  · show (⟨s.st.1.regs.rdi.toBitVec.toNat, s.st.1.regs.rsi.toBitVec.toNat⟩ : Range) = rS
    rw [hA.regs, h0, h1, hrS]; rfl
  · rw [own_at (hpc1 m), own_at hpc]
    exact (by decide +kernel : ownOf (ph (labT StackTake.siteL + Int64.ofNat 1).toBitVec.toNat) =
      ownOf (ph (labT StackTake.siteL).toBitVec.toNat))
  · show ph (Scc.Sem.X64.nextPc (Scc.Sem.X64.abi.setDmem s m)).toBitVec.toNat / 8 % 2 = 0
    rw [Scc.Sem.X64.nextPc_of_cellAt (st := Scc.Sem.X64.abi.setDmem s m) ⟨hcl.valid, hcl.ne, hcl.code⟩]
    show ph (s.st.2 + Int64.ofNat 1).toBitVec.toNat / 8 % 2 = 0
    rw [hpc]
    show ph (labT StackTake.siteL + Int64.ofNat 1).toBitVec.toNat / 8 % 2 = 0
    decide +kernel

set_option maxHeartbeats 800000 in
/-- **`scc_rt_stack_take`'s states are inside `Wr`**, in any region holding
its frame, returning to `scc_rt_thread_init`'s `.x7` (`hra`), with the
source control `c0` (`hC0`, its facts), the frame condition implying
`ret0F`, and past the take `rS` in the pool (`hsub`) and kept by the
region's writes (`hSM`). The take site's obligation is `hsite`. -/
theorem takeW (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region} (hR : R.OK) (hlo : R.lo ≤ -200) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → ret0F m) (q : TakeG) (hq : q.c0 = c0)
    (hra : q.g.ra = (labT ".Lscc_rt_thread_init.x7").toBitVec)
    (hsub : rS.Sub ret0Λ.stackPool) (hSM : FStable R (StackM rS))
    (hsite : TakeW (Wr rS) (Kr rS) ret0Exe ret0End R F (StackM rS) q .site) :
    ∀ i, TakeW (Wr rS) (Kr rS) ret0Exe ret0End R F (StackM rS) q i := by
  intro i
  cases i
  case site => exact hsite
  case e => kblk StackTake.fnL 0 StackTake.stPro_ok
  case entry => kblk StackTake.entryL 0 StackTake.stInit_ok
  case cls => kblk StackTake.clsL 0 StackTake.stCls_ok
  case j1 => kblk StackTake.clsL 13 StackTake.stJ1_ok
  case d0 => ksi "scc_rt_stack_free_n" StackTake.doneL 0
  case d7 => kblk StackTake.doneL 7 StackTake.stFreeN_ok
  case d26 => ksi "scc_rt_stack_free" StackTake.doneL 26
  case d33 => kblk StackTake.doneL 33 StackTake.stFree_ok
  case d52 => ksi "scc_rt_stack_lock" StackTake.doneL 52
  case d59 => kblk StackTake.doneL 59 StackTake.stLock_ok
  case sp0 => kblk StackTake.spinL 0 StackTake.stSwp_ok
  case swp =>
    show NodeW _ _ _ _ _ _ _
    rw [ret0_labT]
    refine nodeW_xchg_pre (b := .rcx) (k := 0) (r := .rax) (z := 3) (l := StackTake.spinL) (off := 11)
      (a := 6291496#64) (by decide +kernel) rfl rfl (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (fun σ _ hJ => ?_) (by decide) hFr ⟨_, .tail _ (.head _)⟩
      fun σ _ hJ => ?_
    · have h : σ.regs.rcx.toBitVec = 6291496#64 := hJ.2.2.1.trans labT_lockA
      simp [bAddr, Reg64s.get64, h]
    · have h : σ.regs.get64 .rax = 1#64 := by rw [← hJ.2.2.2]; rfl
      rw [h]
      decide +kernel
  case sp14 => kblk StackTake.spinL 14 StackTake.stSpin_ok
  case lk0 => kblk StackTake.lockedL 0 StackTake.stLdN_ok
  case ldn =>
    show NodeW _ _ _ _ _ _ _
    rw [ret0_labT]
    refine nodeW_ld_pre (b := .rcx) (k := 0) (r := .rax) (z := 3) (l := StackTake.lockedL) (off := 4)
      (a := 6291504#64) (by decide +kernel) rfl rfl (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (fun σ _ hJ => ?_) (by decide) hFr
    have h : σ.regs.rcx.toBitVec = 6291504#64 := hJ.2.2.trans labT_freeNA
    simp [bAddr, Reg64s.get64, h]
  case lk7 => kblk StackTake.lockedL 7 StackTake.stEmpty_ok
  case b0 => ksi "scc_rt_stack_lock" StackTake.bumpL 0
  case b7 => kblk StackTake.bumpL 7 StackTake.stUnl_ok
  case unl =>
    show NodeW _ _ _ _ _ _ _
    rw [ret0_labT]
    refine nodeW_stown_pre (b := .rcx) (k := 0) (r := .rax) (z := 3) (l := StackTake.bumpL) (off := 28)
      (a := 6291496#64) (by decide +kernel) rfl rfl (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (fun σ _ hJ => ?_) (by decide) hFr ⟨_, .tail _ (.head _)⟩
      fun σ _ hJ => ?_
    · have h : σ.regs.rcx.toBitVec = 6291496#64 := hJ.2.2.1.trans labT_lockA
      simp [bAddr, Reg64s.get64, h]
    · have h : σ.regs.get64 .rax = 0#64 := by rw [← hJ.2.2.2]; rfl
      rw [h]
      decide +kernel
  case b31 => ksi "scc_rt_stack_next" StackTake.bumpL 31
  case b38 => kblk StackTake.bumpL 38 StackTake.stAdd_ok
  case nxt =>
    show NodeW _ _ _ _ _ _ _
    rw [ret0_labT]
    refine nodeW_xadd_pre (b := .rcx) (k := 0) (r := .rax) (z := 5) (l := StackTake.bumpL) (off := 56)
      (a := 6291488#64) (by decide +kernel) rfl rfl (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (fun σ _ hJ => ?_) (by decide) hFr
      ⟨_, .tail _ (.tail _ (.tail _ (.head _)))⟩ fun σ _ hJ => ?_
    · have h : σ.regs.rcx.toBitVec = 6291488#64 := hJ.2.2.1.trans labT_nextA
      simp [bAddr, Reg64s.get64, h]
    · have h : σ.regs.get64 .rax = StackTake.size0 := by rw [← hJ.2.2.2]; rfl
      rw [h]
      decide +kernel
  case b61 => kblk StackTake.bumpL 61 StackTake.stBnd_ok
  case b108 => kblk StackTake.bumpL 108 StackTake.stJ2_ok
  case ok0 => ksi "scc_rt_stacks" StackTake.okL 0
  case ok7 => kblk StackTake.okL 7 StackTake.stOk_ok
  case tk => kblk StackTake.takenL 0 StackTake.stSite_ok
  case ret =>
    dsimp only [TakeW]
    rw [ret0_labT]
    exact blkW_post (l := StackTake.siteL) (off := 1) (dead := fun _ => false)
      (ra := labT ".Lscc_rt_thread_init.x7") (by decide +kernel) rfl StackTake.stRet_ok hR (by omega)
      (by omega) (fun _ _ hJ => hJ.2.1 ▸ hq ▸ hC0) (by decide +kernel)
      (hret_of_run StackTake.stRet_ok fun _ _ hJ => by
        dsimp only [takeNG] at hJ ⊢
        rw [(StackTake.stRet_walk labT _ hJ.2.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ _ _ => rfl) hsub hSM

end Take

/-! ## `scc_rt_thread_init` -/

section Ti

open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Ret0.Mem (ret0F)

variable {rS : Range} {c0 : Ctl} {F : MachineData → Prop}

set_option hygiene false in
/-- A block of `scc_rt_thread_init` before the call, no `ret`, no dead target. -/
local macro "iblk0 " l:term:max k:term:max ok:term:max : tactic =>
  `(tactic| focus
    show BlkW _ _ _ _ _ _ _ _
    rw [ret0_labT]
    exact blkW_pre (l := $l) (off := $k) (dead := fun _ => false) (ra := 0) (by decide +kernel)
      (by first | rfl | exact ofNat_zero' _) $ok hR (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0)
      (by decide +kernel) (fun _ _ _ k hk hr => (noRet_false (by decide +kernel) k hk hr).elim)
      (fun _ _ _ => rfl) (by decide +kernel))

set_option hygiene false in
/-- A block of `scc_rt_thread_init` after the take, no `ret`, no dead target. -/
local macro "iblk " k:term:max ok:term:max : tactic =>
  `(tactic| focus
    dsimp only [TiW]
    rw [ret0_labT]
    exact blkW_post (l := ThreadInit.x7L) (off := $k) (dead := fun _ => false) (ra := 0) (by decide +kernel)
      (by first | rfl | exact ofNat_zero' _) $ok hR (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0)
      (by decide +kernel) (fun _ _ _ k hk hr => (noRet_false (by decide +kernel) k hk hr).elim)
      (fun _ _ _ => rfl) hsub hSM)

set_option hygiene false in
/-- The store of TCB field `j` (`8·j(%rcx)`, `z` bytes at `.x7 + k`) of
`scc_rt_thread_init`, after the take. -/
local macro "ist " j:term:max z:term:max k:term:max : tactic =>
  `(tactic| focus
    show NodeW _ _ _ _ _ _ _
    rw [ret0_labT]
    exact nodeW_st_post (b := .rcx) (k := Int64.ofNat (8 * $j)) (r := .rax) (z := $z) (l := ThreadInit.x7L)
      (off := $k) (a := 134217736#64 + BitVec.ofNat 64 (8 * $j)) (by decide +kernel) rfl rfl
      (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel) (by decide +kernel)
      (fun σ _ hJ => by rw [bAddr_rcx (hJ.2.2.2.trans htcb)]; decide +kernel) (by decide +kernel) hFr
      (not_own (by decide +kernel)) hsub)

set_option maxHeartbeats 800000 in
/-- **`scc_rt_thread_init`'s states are inside `Wr`**, in any region
holding its frame and the take's below, returning to `scc_rt_start`'s
`.x1` (`hra`), with the TCB past `scc_rt_pinned`'s header (`htcb`), the
source control `c0` (`hC0`, its facts), the frame condition implying
`ret0F`, and past the take `rS` in the pool (`hsub`) and kept by the writes
of both regions (`hSM`, `hSM'`). The take site's obligation, for every
ghost of the call, is `hsite`. -/
theorem tiW (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region} (hR : R.OK) (hlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → ret0F m) (q : TiG) (hq : q.c0 = c0) (hra : q.g.ra = (labT ".Lscc_rt_start.x1").toBitVec)
    (htcb : q.tcb = 134217736#64) (hsub : rS.Sub ret0Λ.stackPool) (hSM : FStable R (StackM rS))
    (hSM' : FStable (R.callee (-48 - 0) (-200) 8) (StackM rS))
    (hsite : ∀ g : AllocTcb.G, g.ra = (labT ThreadInit.x7L).toBitVec →
      TakeW (Wr rS) (Kr rS) ret0Exe ret0End (R.callee (-48 - 0) (-200) 8) F (StackM rS) (tiTake q g) .site) :
    ∀ i, TiW (Wr rS) (Kr rS) ret0Exe ret0End R F (StackM rS) q i := by
  intro i
  cases i
  case e => iblk0 ThreadInit.fnL 0 ThreadInit.tiPro_ok
  case entry => iblk0 ThreadInit.entryL 0 ThreadInit.tiArg_ok
  case c7 => iblk0 ThreadInit.entryL 7 tiCall_ok
  case call =>
    intro g hg j
    have hR' := Region.callee_ok (kc := -48 - 0) (lo' := -200) (hi' := 8) hR (by omega) (by decide) (by omega)
      (by omega)
    rw [ret0_labT] at hg
    exact takeW hC0 hR' (by show (-200 : Int) ≤ -200; omega) (by show (8 : Int) ≤ 8; omega) hFr
      (tiTake q g) hq hg hsub hSM' (hsite g hg) j
  case x7 => iblk 0 ThreadInit.tiSp_ok
  case st0 => ist 0 3 48
  case f1 => iblk 51 ThreadInit.tiF1_ok
  case st1 => ist 1 4 59
  case f2 => iblk 63 ThreadInit.tiZ_ok
  case st2 => ist 2 4 74
  case f3 => iblk 78 ThreadInit.tiZ_ok
  case st3 => ist 3 4 89
  case f4 => iblk 93 ThreadInit.tiF4_ok
  case st4 => ist 4 4 101
  case f5 => iblk 105 ThreadInit.tiF5_ok
  case st5 => ist 5 4 113
  case ret =>
    dsimp only [TiW]
    rw [ret0_labT]
    exact blkW_post (l := ThreadInit.x7L) (off := 117) (dead := fun _ => false)
      (ra := labT ".Lscc_rt_start.x1") (by decide +kernel) rfl ThreadInit.tiRet_ok hR (by omega)
      (by omega) (fun _ _ hJ => hJ.1 ▸ hq ▸ hC0) (by decide +kernel)
      (hret_of_run ThreadInit.tiRet_ok fun _ _ hJ => by
        dsimp only [tiN] at hJ ⊢
        rw [(ThreadInit.tiRet_walk labT _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ _ _ => rfl) hsub hSM

end Ti

/-! ## `scc_rt_start` up to the switch -/

section Start

open Spike.Lib.X64.Flow (ofNat_zero' startE sigign siSig xStart0 xStart0_ok xStartArgs xStartArgs_ok)
open Spike.Lib.X64.Flow.Ret0.Mem (ret0F)

variable {rS : Range} {c0 : Ctl} {F : MachineData → Prop}

/-- **`scc_rt_start` up to `.x0`: its states are inside `Wr`** (`St0W`), in
any region holding its frame and `scc_rt_alloc_tcb`'s below, at `n0 = 0`,
with the source control `c0` (`hC0`, its facts) and the frame condition
implying `ret0F`. -/
theorem st0W (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region} (hR : R.OK) (hlo : R.lo ≤ -232) (hhi : 0 ≤ R.hi)
    (hFr : ∀ m, F m → ret0F m) {n0 : BitVec 64} (hn0 : n0 = 0#64) :
    St0W (Wr rS) (Kr rS) ret0Exe ret0End R F n0 c0 := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, fun g hg i => ?_⟩
  · show BlkW _ _ _ _ _ _ _ _
    rw [ret0_labT]
    exact blkW_pre (l := "scc_rt_start") (off := 0) (dead := fun _ => false) (ra := 0) (by decide +kernel)
      (ofNat_zero' _) xStart0_ok hR (by omega) (by omega) (fun _ _ hJ => hJ ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk hr => (noRet_false (by decide +kernel) k hk hr).elim) (fun _ _ _ => rfl) (by decide +kernel)
  · show NodeW _ _ _ _ _ _ _
    rw [ret0_labT]
    exact nodeW_si_pre (si := siSig) (z := 7) (l := startE) (off := 0) (p := labT startE + Int64.ofNat 0)
      (by decide +kernel) rfl (ofNat_zero' _).symm (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · show BlkW _ _ _ _ _ _ _ _
    rw [ret0_labT]
    exact blkW_pre (l := startE) (off := 7) (dead := fun _ => false) (ra := 0) (by decide +kernel)
      rfl xStartArgs_ok hR (by omega) (by omega) (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk hr => (noRet_false (by decide +kernel) k hk hr).elim) (fun _ _ _ => rfl) (by decide +kernel)
  · show NodeW _ _ _ _ _ _ _
    rw [ret0_labT]
    exact nodeW_syscall_pre (z := 2) (l := startE) (off := 41) (p := labT startE + Int64.ofNat 41)
      (by decide +kernel) rfl (by show labT startE + 7 + 34 = _; rw [Int64.add_assoc]; rfl)
      (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fun _ _ ⟨_, _, he⟩ => by rw [he, startS2_rax]; decide)
  · show BlkW _ _ _ _ _ _ _ _
    rw [ret0_labT]
    exact blkW_pre (l := startE) (off := 43) (dead := fun _ => false) (ra := 0) (by decide +kernel)
      rfl startCall_ok hR (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk hr => (noRet_false (by decide +kernel) k hk hr).elim) (fun _ _ _ => rfl) (by decide +kernel)
  · have hR' := Region.callee_ok (kc := -48 - 0) (lo' := -184) (hi' := 8) hR (by omega) (by decide) (by omega)
      (by omega)
    rw [ret0_labT] at hg
    exact tcbW hC0 hR' (by show (-184 : Int) ≤ -184; omega) (by show (8 : Int) ≤ 8; omega) hFr
      ⟨g, n0, c0⟩ rfl hn0 hg i

/-- The TCB's address at `n0 = 0`. -/
theorem tcbA0 {n0 : BitVec 64} (hn0 : n0 = 0#64) : pinA labT + n0 + 8#64 = 134217736#64 := by
  rw [labT_pinA, hn0]; decide

/-- **`scc_rt_start` from `.x0` to the switch: its states are inside `Wr`**
(`X0W`), in any region holding its frame and `scc_rt_thread_init`'s and
`scc_rt_stack_take`'s below, at `n0 = 0`, with the source control `c0`
(`hC0`, its facts), the frame condition implying `ret0F`, and past the take
`rS` in the pool (`hsub`) and kept by the writes of the three regions
(`hSM`, `hSMi`, `hSMt`). The take site's obligation, for every ghost of
both calls, is `hsite`. -/
theorem x0W (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region} (hR : R.OK) (hlo : R.lo ≤ -296) (hhi : 0 ≤ R.hi)
    (hFr : ∀ m, F m → ret0F m) {n0 k0 : BitVec 64} (hn0 : n0 = 0#64)
    (hsub : rS.Sub ret0Λ.stackPool) (hSM : FStable R (StackM rS))
    (hSMi : FStable (R.callee (-48 - 0) (-248) 8) (StackM rS))
    (hSMt : FStable ((R.callee (-48 - 0) (-248) 8).callee (-48 - 0) (-200) 8) (StackM rS))
    (hsite : ∀ g : AllocTcb.G, g.ra = (labT x1L).toBitVec → ∀ g' : AllocTcb.G,
      g'.ra = (labT ThreadInit.x7L).toBitVec →
      TakeW (Wr rS) (Kr rS) ret0Exe ret0End ((R.callee (-48 - 0) (-248) 8).callee (-48 - 0) (-200) 8) F
        (StackM rS) (tiTake ⟨g, pinA labT + n0 + 8#64, k0, c0⟩ g') .site) :
    X0W (Wr rS) (Kr rS) ret0Exe ret0End R F rS n0 k0 c0 := by
  refine ⟨?_, fun g hg i => ?_, ?_, ?_, ?_⟩
  · show BlkW _ _ _ _ _ _ _ _
    rw [ret0_labT]
    exact blkW_pre (l := x0L) (off := 0) (dead := fun _ => false) (ra := 0) (by decide +kernel)
      (ofNat_zero' _) startCall2_ok hR (by omega) (by omega) (fun _ _ hJ => hJ.1.1.1 ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk hr => (noRet_false (by decide +kernel) k hk hr).elim) (fun _ _ _ => rfl) (by decide +kernel)
  · have hR' := Region.callee_ok (kc := -48 - 0) (lo' := -248) (hi' := 8) hR (by omega) (by decide) (by omega)
      (by omega)
    rw [ret0_labT] at hg ⊢
    exact tiW hC0 hR' (by show (-248 : Int) ≤ -248; omega) (by show (8 : Int) ≤ 8; omega) hFr _ rfl hg
      (tcbA0 hn0) hsub hSMi hSMt (hsite g hg) i
  · show BlkW _ _ _ _ _ _ _ _
    rw [ret0_labT]
    exact blkW_post (l := x1L) (off := 0) (dead := fun _ => false) (ra := 0) (by decide +kernel)
      (ofNat_zero' _) startFs_ok hR (by omega) (by omega) (fun _ _ hJ => hJ.1.1 ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk hr => (noRet_false (by decide +kernel) k hk hr).elim) (fun _ _ _ => rfl) hsub hSM
  · show NodeW _ _ _ _ _ _ _
    rw [ret0_labT]
    exact nodeW_syscall_post (z := 2) (l := x1L) (off := 18) (p := labT x1L + Int64.ofNat 18)
      (by decide +kernel) rfl rfl (fun _ _ hJ => hJ.1 ▸ hC0) (by decide +kernel) (by decide +kernel) hsub
      (fun _ _ hJ => by rw [hJ.2.1]; decide)
  · show BlkW _ _ _ _ _ _ _ _
    rw [ret0_labT]
    exact blkW_post (l := x1L) (off := 20) (dead := fun _ => false) (ra := 0) (by decide +kernel)
      rfl startSw_ok hR (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk hr => (noRet_false (by decide +kernel) k hk hr).elim) (fun _ _ _ => rfl) hsub hSM

end Start

/-! ## From the switch on: `scc_rt_main` and `wc_main` -/

section Main

open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Ret0.Mem (ret0Words)

variable {rS : Range} {c0 : Ctl}

/-- A block obligation under an unsatisfiable frame condition. -/
theorem blkW_false {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {n : ND} {blk : List (Directive × Nat)} (h : ∀ m, ¬ F m) :
    BlkW W K exe endPc R F n blk :=
  fun _ _ _ _ _ _ _ _ hD _ => (h _ hD).elim

/-- A node obligation under an unsatisfiable frame condition. -/
theorem nodeW_false {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {n : ND} (h : ∀ m, ¬ F m) : NodeW W K exe endPc R F n :=
  fun _ _ ⟨_, _, _, _, _, _, hD, _⟩ => (h _ hD).elim

/-- `scc_rt_main`'s obligations under an unsatisfiable frame condition. -/
theorem mainW_false {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {ms : MemSide isa} {g : MainG} (h : ∀ m, ¬ F m) :
    MainW W K exe endPc R F ms g :=
  have h' : ∀ m, ¬ (F m ∧ CallerCells R (-48 - 0) (-24) 8 m) := fun m hm => h m hm.1
  ⟨⟨blkW_false h, blkW_false h, nodeW_false h, blkW_false h, blkW_false h⟩, blkW_false h,
    fun _ _ _ _ => ⟨⟨blkW_false h', blkW_false h', nodeW_false h', blkW_false h', blkW_false h'⟩,
      ⟨blkW_false h', blkW_false h'⟩⟩,
    ⟨blkW_false h, nodeW_false h⟩⟩

/-- The TCB's limit word at `n0 = 0`. -/
theorem limA_tcb0 : limA (tpOf 134217736#64) = 134217744#64 := by decide

/-- Closes a closed fact about the switch's region or its callees'. -/
local macro "rdec" : tactic => `(tactic| ((try dsimp only [swR, Region.callee]) <;> omega))

/-- Closes a node's pc equation (or another closed fact) by evaluation. -/
local macro "pcdec" : tactic =>
  `(tactic| ((try dsimp only [Ret0.mainN0, Ret0.mainN1, Ret0.mainN1R, Ret0.mainNR, Ret0.mainNRR, Ret0.startN6,
    Ret0.startN7, Ret0.startN8, Ret0.wcN1, Spike.Lib.X64.Flow.wcN1, xProN1, xProN2, xProN3, xProN4,
    xExitNx]) <;> decide +kernel))

set_option hygiene false in
/-- A block from the switch on, no `ret`, no dead target. -/
local macro "mblk " l:term:max off:term:max ok:term:max hR:term:max hR8:term:max hC:term:max hFO:term:max :
    tactic =>
  `(tactic| exact blkW_postO (l := $l) (off := $off) (dead := fun _ => false) (ra := 0) (by decide +kernel)
    (by pcdec) $ok $hR (by rdec) (by rdec) $hR8 (by rdec) (by rdec) $hC (by decide +kernel)
    (fun _ _ _ k hk hr => (noRet_false (by decide +kernel) k hk hr).elim) (fun _ _ _ => rfl) hsub hfit $hFO)

set_option maxHeartbeats 1600000 in
/-- **`scc_rt_main`'s states are inside `Wr`** (`MainW`), in the callee's
region of the new stack's region at its top `top` (8-aligned, the region
not wrapping), the TCB at `134217736` (`n0 = 0`), with the source control
`c0` (`hC0`, its facts), `rS` in the pool (`hsub`) and not wrapping
(`hfit`). The frame condition after the switch gives the words of `rS` off
the new region, the caller's cells outside the callee's region the rest. -/
theorem mainW (hC0 : CFacts ret0Λ ret0Λ.static c0) {top : BitVec 64} (h8 : top.toNat % 8 = 0)
    (hok : (swR top (-80) 0).OK) (hsub : rS.Sub ret0Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (ms : MemSide isa) :
    MainW (Wr rS) (Kr rS) ret0Exe ret0End ((swR top (-80) 0).callee (-8 - 0) (-72) 8)
      (fun m => swFS rS top (limA (tpOf 134217736#64)) top m ∧ CallerCells (swR top (-80) 0) (-8 - 0) (-72) 8 m)
      ms ⟨top - 8#64, tpOf 134217736#64, c0⟩ := by
  have hR := Region.callee_ok (kc := -8 - 0) (lo' := -72) (hi' := 8) hok (by rdec) (by rdec) (by rdec) (by rdec)
  have hb0 : (((swR top (-80) 0).callee (-8 - 0) (-72) 8).base.toNat : Int) = top.toNat + (-8 - 0) :=
    Region.callee_base hok (by rdec) (by rdec) (by rdec)
  have hR8 : ((swR top (-80) 0).callee (-8 - 0) (-72) 8).base.toNat % 8 = 0 := by omega
  have hFO : ∀ m, (swFS rS top (limA (tpOf 134217736#64)) top m ∧
      CallerCells (swR top (-80) 0) (-8 - 0) (-72) 8 m) → StackOff rS ((swR top (-80) 0).callee (-8 - 0) (-72) 8) m :=
    fun _ h => stackOff_callee hok h8 (by rdec) (by rdec) (by rdec) (by rdec) (by rdec) (by rdec) h.1.2 h.2
  have hR' := Region.callee_ok (kc := -48 - 0) (lo' := -24) (hi' := 8) hR (by rdec) (by rdec) (by rdec) (by rdec)
  have hb1 : ((((swR top (-80) 0).callee (-8 - 0) (-72) 8).callee (-48 - 0) (-24) 8).base.toNat : Int) =
      ((swR top (-80) 0).callee (-8 - 0) (-72) 8).base.toNat + (-48 - 0) :=
    Region.callee_base hR (by rdec) (by rdec) (by rdec)
  have hR8' : (((swR top (-80) 0).callee (-8 - 0) (-72) 8).callee (-48 - 0) (-24) 8).base.toNat % 8 = 0 := by
    omega
  have hFO' : ∀ m, ((swFS rS top (limA (tpOf 134217736#64)) top m ∧
      CallerCells (swR top (-80) 0) (-8 - 0) (-72) 8 m) ∧
      CallerCells ((swR top (-80) 0).callee (-8 - 0) (-72) 8) (-48 - 0) (-24) 8 m) →
      StackOff rS (((swR top (-80) 0).callee (-8 - 0) (-72) 8).callee (-48 - 0) (-24) 8) m :=
    fun _ h => stackOff_callee hR hR8 (by rdec) (by rdec) (by rdec) (by rdec) (by rdec) (by rdec) (hFO _ h.1) h.2
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, fun g' hra hc0 htp => ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨?_, ?_⟩⟩
  -- `scc_rt_main`'s prologue
  · show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
    mblk "scc_rt_main" 0 (xHead_ok (lo := -72) (hi := 8) (by omega) (by omega)) hR hR8
      (fun _ _ hJ => hJ.1 ▸ hC0) hFO
  · show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
    mblk ".Lscc_rt_main.chk" 0 (xLea_ok (lo := -72) (hi := 8) 32 5) hR hR8 (fun _ _ ⟨_, hJ, _⟩ => hJ.1 ▸ hC0) hFO
  · show NodeW _ _ _ _ _ _ _; rw [ret0_labT]
    exact nodeW_fsld_postO (d := .r11) (k := 8) (z := 9) (l := ".Lscc_rt_main.chk") (off := 5)
      (p := labT "scc_rt_main" + 1 + 3 + Int64.ofNat 5) (a := 134217744#64) (by decide +kernel) (by pcdec) rfl
      (fun _ _ ⟨_, hJ, _⟩ => hJ.1 ▸ hC0) (by decide +kernel) (by decide +kernel)
      (fun _ _ ⟨σ0, hJ, he⟩ => by
        rw [he, show (xS2 32 σ0).regs.fsBase = σ0.regs.fsBase by simp [xS2, xS1, hdRegs, Reg64s.set64], hJ.2.2]
        exact limA_tcb0)
      (by decide) (fun _ h => by rw [← limA_tcb0]; exact h.1.1.2) hR hR8 (by rdec) (by rdec) hsub hFO
  · show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
    mblk ".Lscc_rt_main.chk" 14 (xCmp_ok (lo := -72) (hi := 8) _ ".Lscc_rt_main.stk" 3 2) hR hR8
      (fun _ _ ⟨_, _, hJ, _⟩ => hJ.1 ▸ hC0) hFO
  · show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
    mblk ".Lscc_rt_main.chk" 19 (xFr_ok (lo := -72) (hi := 8) 32 4 _ (by decide)) hR hR8
      (fun _ _ ⟨_, _, hJ, _⟩ => hJ.1 ▸ hC0) hFO
  -- the call of `wc_main`
  · show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
    mblk ".Lscc_rt_main.entry" 0 mainCall_ok hR hR8 (fun _ _ hJ => hJ.1.1 ▸ hC0) hFO
  -- `wc_main`'s prologue
  · show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
    mblk "wc_main" 0 (xHead_ok (lo := -24) (hi := 8) (by omega) (by omega)) hR' hR8'
      (fun _ _ hJ => by rw [hJ.1, hc0]; exact hC0) hFO'
  · show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
    mblk ".Lwc_main.chk" 0 (xLea_ok (lo := -24) (hi := 8) 16 5) hR' hR8'
      (fun _ _ ⟨_, hJ, _⟩ => by rw [hJ.1, hc0]; exact hC0) hFO'
  · show NodeW _ _ _ _ _ _ _; rw [ret0_labT]
    exact nodeW_fsld_postO (d := .r11) (k := 8) (z := 9) (l := ".Lwc_main.chk") (off := 5)
      (p := labT "wc_main" + 1 + 3 + Int64.ofNat 5) (a := 134217744#64) (by decide +kernel) (by pcdec) rfl
      (fun _ _ ⟨_, hJ, _⟩ => by rw [hJ.1, hc0]; exact hC0) (by decide +kernel) (by decide +kernel)
      (fun _ _ ⟨σ0, hJ, he⟩ => by
        rw [he, show (xS2 16 σ0).regs.fsBase = σ0.regs.fsBase by simp [xS2, xS1, hdRegs, Reg64s.set64],
          hJ.2.2.2.2, htp]
        exact limA_tcb0)
      (by decide) (fun _ h => by rw [← limA_tcb0]; exact h.1.1.1.2) hR' hR8' (by rdec) (by rdec) hsub hFO'
  · show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
    mblk ".Lwc_main.chk" 14 (xCmp_ok (lo := -24) (hi := 8) _ ".Lwc_main.stk" 3 2) hR' hR8'
      (fun _ _ ⟨_, _, hJ, _⟩ => by rw [hJ.1, hc0]; exact hC0) hFO'
  · show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
    mblk ".Lwc_main.chk" 19 (xFr_ok (lo := -24) (hi := 8) 16 4 [] (by simp)) hR' hR8'
      (fun _ _ ⟨_, _, hJ, _⟩ => by rw [hJ.1, hc0]; exact hC0) hFO'
  -- `wc_main`'s body
  · show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
    mblk ".Lwc_main.entry" 0 wcAdd_ok hR' hR8' (fun _ _ hJ => by rw [hJ.1, hc0]; exact hC0) hFO'
  · show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
    rw [ret0_labT] at hra
    exact blkW_postO (l := ".Lwc_main.entry") (off := 19) (dead := fun _ => false)
      (ra := labT ".Lscc_rt_main.x2") (by decide +kernel) (by pcdec) wcRet_ok hR' (by rdec) (by rdec) hR8'
      (by rdec) (by rdec) (fun _ _ ⟨_, hJ, _⟩ => by rw [hJ.1, hc0]; exact hC0) (by decide +kernel)
      (hret_of_run wcRet_ok fun σ _ ⟨σ0, hJ, hs, _⟩ => by
        show (arun labT wcRet ⟨_, oB, σ⟩).pc = _
        rw [wcRet_run, hs, hJ.2.2.1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ _ _ => rfl) hsub hfit hFO'
  -- the `exit_group` tail
  · show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
    mblk ".Lscc_rt_main.x2" 0 (xExit_ok (lo := -72) (hi := 8) (sp := -40) (b := -8) (-16) 4 4 5 (by decide)) hR
      hR8 (fun _ _ hJ => hJ.1 ▸ hC0) hFO
  · show NodeW _ _ _ _ _ _ _; rw [ret0_labT]
    exact nodeW_syscall_postO (z := 2) (l := ".Lscc_rt_main.x2") (off := 13)
      (p := labT ".Lscc_rt_main.x2" + Int64.ofNat 13) (by decide +kernel) rfl (by pcdec)
      (fun _ _ ⟨_, _, hJ, _⟩ => hJ.1 ▸ hC0) (by decide +kernel) (by decide +kernel) hR hR8 (by rdec) (by rdec)
      hsub hFO (fun _ _ h => by rw [h.1]; decide)

/-- **The switch's and `scc_rt_main`'s states are inside `Wr`** (`SwW`):
the switch with the stack range in private memory, `xorl %ebp, %ebp`, the
block after it and `scc_rt_main`'s in the new stack's region (vacuous off
its top `top`, 8-aligned, the region not wrapping), the TCB at `134217736`
(`htcb`), with the source control `c0` (`hC0`, its facts), `rS` in the pool
(`hsub`) and not wrapping (`hfit`). -/
theorem swW (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region} {F : MachineData → Prop} {tcb top : BitVec 64}
    (htcb : tcb = 134217736#64) (h8 : top.toNat % 8 = 0) (hok : (swR top (-80) 0).OK)
    (hsub : rS.Sub ret0Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (ms : MemSide isa) :
    SwW (Wr rS) (Kr rS) ret0Exe ret0End R (fun m => F m ∧ StackM rS m) ms rS tcb top c0 := by
  subst htcb
  refine ⟨?_, fun v => ?_, fun v => ?_, fun v => ?_⟩
  · show NodeW _ _ _ _ _ _ _; rw [ret0_labT]
    exact nodeW_reg_post (op := .mov (.reg (.low .rsp .W64)) (.regOrMem (.reg (.low .rax .W64)))) rfl
      (z := 3) (l := x1L) (off := 28) (p := labT x1L + Int64.ofNat 28) (by decide +kernel) rfl rfl
      (fun _ _ hJ => hJ.1 ▸ hC0) (by decide +kernel) (by decide +kernel) hsub
  · by_cases hv : v = top
    · subst hv
      show NodeW _ _ _ _ _ _ _; rw [ret0_labT]
      exact nodeW_fi_postO (fi := .xor_rr32_self .rbp) (z := 2) (l := x1L) (off := 31)
        (p := labT x1L + Int64.ofNat 31) (by decide +kernel) rfl rfl (fun _ _ hJ => hJ.1 ▸ hC0)
        (by decide +kernel) (by decide +kernel) hok h8 (by rdec) (by rdec) hsub (fun _ h => h.2)
    · exact nodeW_false fun _ h => hv h.1.1
  · by_cases hv : v = top
    · subst hv
      show BlkW _ _ _ _ _ _ _ _; rw [ret0_labT]
      mblk x1L 33 startMain_ok hok h8 (fun _ _ hJ => hJ.1 ▸ hC0) (fun _ h => h.2)
    · exact blkW_false fun _ h => hv h.1.1
  · by_cases hv : v = top
    · subst hv; exact mainW hC0 h8 hok hsub hfit ms
    · exact mainW_false fun _ h => hv h.1.1.1

end Main

/-! ## `main`'s exit and `scc_rt_start` as one segment -/

section Exit

open Spike.Lib.X64.Flow

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
    LocalStep p Spike.Lib.X64Consumer.c0 ⟨mainBody, mainEnv d, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th hg ht he hs _
  simp only [TermRun.tstep, ht, TermRun.enter, hg, hd, he, Spike.Lib.X64Consumer.c0, TermRun.evalAt,
    TermRun.lookupE, List.find?, TermRun.ol, Option.map, Option.toList]
  obtain ⟨⟩ := th
  simp only at hs
  subst hs
  simp [hb, mainEnv]

/-- **The source start runs to `ret y`**: `start_step`, then `main`'s two
bindings. -/
theorem start_run {p : Prog} {d : Decl} (hd : p.find? (·.name == "main") = some d) (hb : d.body = mainBody) :
    LocalRun p Spike.Lib.X64Consumer.c0 ⟨.ret (.var "y"), exitEnv (mainEnv d), none⟩ :=
  .step (start_step hd hb) (mainBody_run rfl)

/-- **The source start's `CFacts`**: a tail call, its argument `a` with no
words, so nothing to place. -/
theorem cfacts_c0 {Λ : Scc.Sem.Layout} {lbl : Lbl} : CFacts Λ lbl Spike.Lib.X64Consumer.c0 := by
  refine ⟨nofun, fun _ _ _ _ _ h => ?_, nofun, fun s => ?_⟩
  · rcases h with h | ⟨_, h⟩ <;> cases h
  refine ⟨fun _ _ => none, ?_, ?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ h; cases h
  rotate_left
  · intro _ _ _ h; cases h
  intro x hx ty ws hl k hk
  simp [Scc.Sem.exprFv, Scc.Sem.atVars, Spike.Lib.X64Consumer.c0] at hx
  subst hx
  have : ws = [] :=
    (by simpa [Spike.Lib.X64Consumer.c0, TermRun.lookupE, List.find?] using hl.symm : _ ∧ _).2
  subst this
  cases hk

/-- **`main`'s exit at the `exit_group` of `scc_rt_main`** (`hexit` of
`ret0_segW`), for any control `c0` that runs locally to `main`'s body in
some environment `env` (`hrun`): the run on to `ret y` with `y = 42`,
placed in `%rdi` (the status of `exit_group`). Nothing of `env` is needed:
the run binds `x` and `y` itself, and `ret y` reads only `y`. -/
theorem ret0_exitOf {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ls0 : Lsize}
    {ms : MemSide isa} (hms : ms = msOf ret0Λ μ0 rd G own ret0Λ.static ls0) {c0 : Ctl} {env : TermRun.Env}
    (hrun : LocalRun p c0 ⟨mainBody, env, none⟩) :
    ∀ R' F' s, At ret0Exe ret0End R' F' (mainNX labT) s c0 → ¬ ms.abortAt s → MainExit p ms s c0 42 := by
  subst hms
  rintro R' F' s ⟨-, -, -, -, σ, hA, -, hx⟩ -
  have h42 : s.st.1.regs.rdi.toBitVec = 42#64 := by rw [hA.regs]; exact hx
  refine ⟨⟨.ret (.var "y"), exitEnv env, none⟩, hrun.trans (mainBody_run rfl), ?_, ?_⟩
  · refine ⟨fun x k => if x = "y" ∧ k = 0 then some (.one (.reg (.r .rdi))) else none, ?_, ?_, ?_⟩
    · intro x ty ws hl k wd wp hk hp
      dsimp only at hp
      split at hp
      · obtain ⟨rfl, rfl⟩ := ‹x = "y" ∧ k = 0›
        cases hp
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj
          ((show TermRun.lookupE (exitEnv env) "y" = some _ from rfl).symm.trans hl))
        cases hk
        refine ⟨42, ?_, ⟨by decide, rfl⟩⟩
        exact congrArg (fun b : BitVec 64 => some b.toNat) (h42 : Scc.Sem.X64.regVal s (.r .rdi) = 42#64)
      · cases hp
    · intro x hx ty ws hl k hk
      simp [Scc.Sem.exprFv, Scc.Sem.atVars] at hx
      subst hx
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj
        ((show TermRun.lookupE (exitEnv env) "y" = some _ from rfl).symm.trans hl))
      obtain rfl : k = 0 := by simpa using hk
      exact ⟨.one (.reg (.r .rdi)), by simp⟩
    · intro x k n h
      dsimp only at h
      split at h <;> cases h
  · intro s0 th h0 ht he hs
    unfold Scc.Sem.SrcSem.mainExit
    simp only [h0, ht, hs, he]
    rfl

/-- **`main`'s exit from the source start** `X64Consumer.c0` (the thread
at `mainStart`): `ret0_exitOf` through `start_step`, given `p`'s `main`
(`hd`) with body `mainBody` (`hb`). -/
theorem ret0_exit {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ls0 : Lsize}
    {ms : MemSide isa} (hms : ms = msOf ret0Λ μ0 rd G own ret0Λ.static ls0) {d : Decl}
    (hd : p.find? (·.name == "main") = some d) (hb : d.body = mainBody) :
    ∀ R' F' s, At ret0Exe ret0End R' F' (mainNX labT) s Spike.Lib.X64Consumer.c0 → ¬ ms.abortAt s →
      MainExit p ms s Spike.Lib.X64Consumer.c0 42 :=
  ret0_exitOf hms (.single (start_step hd hb))

end Exit

section StartAll

open Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0.Mem (ret0F)

variable {rS : Range} {c0 : Ctl} {F : MachineData → Prop}

/-- **A range off a region is off a callee's inside it**: the callee's
region at `kc`, `[lo', hi')`, lies in the region. -/
theorem out_callee {R : Region} (hR : R.OK) {kc lo' hi' : Int} (hlo : R.lo ≤ kc + lo') (hlo0 : lo' ≤ 0)
    (hkc : kc < R.hi) (hhi : kc + hi' ≤ R.hi)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a) :
    ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ (R.callee kc lo' hi').base.toNat + (R.callee kc lo' hi').lo ∨
        ((R.callee kc lo' hi').base.toNat : Int) + (R.callee kc lo' hi').hi ≤ a := by
  intro a h8 ha ha7
  have hb := Region.callee_base (hi' := hi') hR hlo hlo0 hkc
  have h := hout a h8 ha ha7
  rw [hb]
  show (a : Int) + 8 ≤ R.base.toNat + kc + lo' ∨ (R.base.toNat : Int) + kc + hi' ≤ a
  omega

/-- **`scc_rt_start`'s states are inside `Wr`** (`StartAllW`): `st0W`,
`x0W` and `swW`, at `n0 = 0` (the TCB at `134217736`, `tcbA0`), the new
stack's top `stacksA + k0 + 16384` 8-aligned (`h8`) with its region not
wrapping (`hok`), `rS` in the pool (`hsub`) and not wrapping (`hfit`). The
take site's obligation is `hsite`, the stack range's stability under the
three regions' writes from the range off the region (`houtS`,
`stackM_stable`, `out_callee`). -/
theorem startAllW (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region} (hR : R.OK)
    (hlo : R.lo ≤ -296) (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → ret0F m) {n0 k0 : BitVec 64} (hn0 : n0 = 0#64)
    (hsub : rS.Sub ret0Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hsite : ∀ g : AllocTcb.G, g.ra = (labT x1L).toBitVec → ∀ g' : AllocTcb.G,
      g'.ra = (labT ThreadInit.x7L).toBitVec →
      TakeW (Wr rS) (Kr rS) ret0Exe ret0End ((R.callee (-48 - 0) (-248) 8).callee (-48 - 0) (-200) 8) F
        (StackM rS) (tiTake ⟨g, pinA labT + n0 + 8#64, k0, c0⟩ g') .site)
    (h8 : (stacksA labT + k0 + 16384#64).toNat % 8 = 0) (hok : (swR (stacksA labT + k0 + 16384#64) (-80) 0).OK)
    (ms : MemSide isa) :
    StartAllW (Wr rS) (Kr rS) ret0Exe ret0End R F ms rS n0 k0 c0 := by
  have hR1 := Region.callee_ok (kc := -48 - 0) (lo' := -248) (hi' := 8) hR (by omega) (by decide) (by omega)
    (by omega)
  have ho1 := out_callee hR (kc := -48 - 0) (lo' := -248) (hi' := 8) (by omega) (by decide) (by omega)
    (by omega) houtS
  have ho2 := out_callee hR1 (kc := -48 - 0) (lo' := -200) (hi' := 8) (by show (-248 : Int) ≤ _; omega)
    (by decide) (by show (-48 - 0 : Int) < 8; omega) (by show (-48 - 0 + 8 : Int) ≤ 8; omega) ho1
  refine ⟨st0W hC0 hR (by omega) hhi hFr hn0, x0W hC0 hR hlo hhi hFr hn0 hsub (stackM_stable hfit houtS)
    (stackM_stable hfit ho1) (stackM_stable hfit ho2) hsite, ?_⟩
  rw [ret0_labT]
  exact swW hC0 (tcbA0 hn0) h8 hok hsub hfit ms

/-- **`scc_rt_start`'s run is one segment inside `Wr`**, the take its
outside move: `start_segW`, its obligation `startAllW`. The premises are
`start_segW`'s at `ret0Exe` (the memory side's facts, the layout's
arithmetic, `main`'s exit `hexit`) and `startAllW`'s (the take site's
obligation `hsite`). Unlike A64's, it starts at `scc_rt_start` (`startN0`),
in a region with room for the return address above (`8 ≤ R.hi`): `_start`'s
`andq` switches to a region of its own before the call. -/
theorem ret0_segW {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region}
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi) (hFr : ∀ m, F m → ret0F m) {n0 k0 : BitVec 64} (hn0 : n0 = 0#64)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F (pinA labT + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F ret0Exe ret0End n0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA labT + n0 + 8#64) (stacksA labT + k0),
      StOk ms F (pinA labT + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F ret0Exe ret0End k0)
    (h8 : (stacksA labT + k0 + 16384#64).toNat % 8 = 0)
    (hok : (swR (stacksA labT + k0 + 16384#64) (-80) 0).OK)
    (hsubR : ∀ k, (swR (stacksA labT + k0 + 16384#64) (-80) 0).Off k →
      ((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat + 7))
    (hfit : (limA (tpOf (pinA labT + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf (pinA labT + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA labT + k0 + 16384#64).toNat + -80 ∨
      ((stacksA labT + k0 + 16384#64).toNat : Int) + 0 ≤ (limA (tpOf (pinA labT + n0 + 8#64))).toNat)
    (hlimM : LimOk ms F (limA (tpOf (pinA labT + n0 + 8#64)))
      (stacksA labT + k0 + 16384#64 - 8#64 - 8#64 - (32 : Int64).toBitVec))
    (hlimW : LimOk ms F (limA (tpOf (pinA labT + n0 + 8#64)))
      (stacksA labT + k0 + 16384#64 - 8#64 - 8#64 - (32 : Int64).toBitVec - 8#64 - 8#64 - (16 : Int64).toBitVec))
    (hexit : ∀ R' F' s, At ret0Exe ret0End R' F' (mainNX labT) s c0 → ¬ ms.abortAt s → MainExit p ms s c0 42)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hsub : rS.Sub ret0Λ.stackPool)
    (hsite : ∀ g : AllocTcb.G, g.ra = (labT x1L).toBitVec → ∀ g' : AllocTcb.G,
      g'.ra = (labT ThreadInit.x7L).toBitVec →
      TakeW (Wr rS) (Kr rS) ret0Exe ret0End ((R.callee (-48 - 0) (-248) 8).callee (-48 - 0) (-200) 8) F
        (StackM rS) (tiTake ⟨g, pinA labT + n0 + 8#64, k0, c0⟩ g') .site)
    {Q : Frag isa} :
    SegW (Wr rS) (Kr rS) p lbl ms (At ret0Exe ret0End R F (startN0 labT c0)) Q := by
  have hS := start_segW (exe := ret0Exe) (endPc := ret0End) (p := p) (lbl := lbl) (ms := ms) (W := Wr rS)
    (R := R) (F := F) (rS := rS) (Q := Q) ret0_lays rfl
  rw [ret0_labT] at hS
  exact hS hK hF hR hlo hhi n0 k0 c0 hn hk hhdr htcb hfld htk hok hsubR hfit hout hlimM hlimW hexit hRS hfitS
    houtS hFt (startAllW hC0 hR hlo (by omega) hFr hn0 hsub hfitS houtS hsite h8 hok ms)

/-- **The consumer's obligations of `ret0`** from `ret0_segW` through
`inst_of_segW`, at the memory side `msOf` of the static placement (`hms`):
a fragment holding `scc_rt_start`'s entry node, with `Nodes`, `TakePath`
and `AbortPath` (an empty phase). The take site's states by `takeSiteW`,
the range named by its registers (`hrS`); open: `ret0_segW`'s premises. -/
theorem ret0_inst {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ls0 : Lsize}
    {ms : MemSide isa} (hms : ms = msOf ret0Λ μ0 rd G own ret0Λ.static ls0)
    (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region}
    (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi) (hFr : ∀ m, F m → ret0F m) {n0 k0 : BitVec 64} (hn0 : n0 = 0#64)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F (pinA labT + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F ret0Exe ret0End n0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA labT + n0 + 8#64) (stacksA labT + k0),
      StOk ms F (pinA labT + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F ret0Exe ret0End k0)
    (h8 : (stacksA labT + k0 + 16384#64).toNat % 8 = 0)
    (hok : (swR (stacksA labT + k0 + 16384#64) (-80) 0).OK)
    (hsubR : ∀ k, (swR (stacksA labT + k0 + 16384#64) (-80) 0).Off k →
      ((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat + 7))
    (hfit : (limA (tpOf (pinA labT + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf (pinA labT + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA labT + k0 + 16384#64).toNat + -80 ∨
      ((stacksA labT + k0 + 16384#64).toNat : Int) + 0 ≤ (limA (tpOf (pinA labT + n0 + 8#64))).toNat)
    (hlimM : LimOk ms F (limA (tpOf (pinA labT + n0 + 8#64)))
      (stacksA labT + k0 + 16384#64 - 8#64 - 8#64 - (32 : Int64).toBitVec))
    (hlimW : LimOk ms F (limA (tpOf (pinA labT + n0 + 8#64)))
      (stacksA labT + k0 + 16384#64 - 8#64 - 8#64 - (32 : Int64).toBitVec - 8#64 - 8#64 - (16 : Int64).toBitVec))
    (hexit : ∀ R' F' s, At ret0Exe ret0End R' F' (mainNX labT) s c0 → ¬ ms.abortAt s → MainExit p ms s c0 42)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hsub : rS.Sub ret0Λ.stackPool)
    (hrS : rS = ⟨(stacksA labT + k0).toNat, 16384⟩) :
    ∃ inv : Frag isa, (∀ s c, At ret0Exe ret0End R F (startN0 labT c0) s c → inv s c) ∧
      Nodes ret0Λ p μ0 rd G own (IOf ret0Λ.static ls0 inv) ∧
      TakePath ret0Λ p μ0 (IOf ret0Λ.static ls0 inv) rS Tk ∧
      AbortPath μ0 (IOf ret0Λ.static ls0 inv) (fun _ => False) ∧ NoWrite (IOf ret0Λ.static ls0 inv) := by
  subst hms
  exact inst_of_segW (ret0_segW (lbl := ret0Λ.static) hC0 rfl hF hR hlo hhi hFr hn0 hn hhdr htcb hk hfld htk h8 hok
    hsubR hfit hout hlimM hlimW hexit hRS hfitS houtS hFt hsub
    fun _ _ _ _ => takeSiteW hC0 _ rfl hrS hsub) mu0_take (fun _ _ h => h)

/-- **`ret0_inst` at the source start**, the control `X64Consumer.c0` that
the consumer's `hst` fixes (the runtime never steps the source, so the start
is carried unchanged to `mainNX`): `CFacts` by `cfacts_c0`, `main`'s exit by
`ret0_exit`, given `p`'s `main` (`hd`) with body `mainBody` (`hb`). -/
theorem ret0_inst' {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ls0 : Lsize}
    {ms : MemSide isa} (hms : ms = msOf ret0Λ μ0 rd G own ret0Λ.static ls0)
    {R : Region}
    (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi) (hFr : ∀ m, F m → ret0F m) {n0 k0 : BitVec 64} (hn0 : n0 = 0#64)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F (pinA labT + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F ret0Exe ret0End n0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA labT + n0 + 8#64) (stacksA labT + k0),
      StOk ms F (pinA labT + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F ret0Exe ret0End k0)
    (h8 : (stacksA labT + k0 + 16384#64).toNat % 8 = 0)
    (hok : (swR (stacksA labT + k0 + 16384#64) (-80) 0).OK)
    (hsubR : ∀ k, (swR (stacksA labT + k0 + 16384#64) (-80) 0).Off k →
      ((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat + 7))
    (hfit : (limA (tpOf (pinA labT + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf (pinA labT + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA labT + k0 + 16384#64).toNat + -80 ∨
      ((stacksA labT + k0 + 16384#64).toNat : Int) + 0 ≤ (limA (tpOf (pinA labT + n0 + 8#64))).toNat)
    (hlimM : LimOk ms F (limA (tpOf (pinA labT + n0 + 8#64)))
      (stacksA labT + k0 + 16384#64 - 8#64 - 8#64 - (32 : Int64).toBitVec))
    (hlimW : LimOk ms F (limA (tpOf (pinA labT + n0 + 8#64)))
      (stacksA labT + k0 + 16384#64 - 8#64 - 8#64 - (32 : Int64).toBitVec - 8#64 - 8#64 - (16 : Int64).toBitVec))
    {d : Decl} (hd : p.find? (·.name == "main") = some d) (hb : d.body = mainBody)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hsub : rS.Sub ret0Λ.stackPool)
    (hrS : rS = ⟨(stacksA labT + k0).toNat, 16384⟩) :
    ∃ inv : Frag isa, (∀ s c, At ret0Exe ret0End R F (startN0 labT Spike.Lib.X64Consumer.c0) s c → inv s c) ∧
      Nodes ret0Λ p μ0 rd G own (IOf ret0Λ.static ls0 inv) ∧
      TakePath ret0Λ p μ0 (IOf ret0Λ.static ls0 inv) rS Tk ∧
      AbortPath μ0 (IOf ret0Λ.static ls0 inv) (fun _ => False) ∧ NoWrite (IOf ret0Λ.static ls0 inv) :=
  ret0_inst hms cfacts_c0 hF hR hlo hhi hFr hn0 hn hhdr htcb hk hfld htk h8 hok hsubR hfit hout hlimM hlimW
    (ret0_exit hms hd hb) hRS hfitS houtS hFt hsub hrS

end StartAll

section Entry

open Kraken.Promising.Lower.X64 (CellAt)
open Kraken.X64.Parser
open Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0.Mem (ret0F ret0Words ret0Words_entry ret0Words_pool)

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
theorem ret0F_takeMem (hsub : rS.Sub ret0Λ.stackPool) {pm : _root_.Mem 64}
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
theorem fitS_of_sub (hsub : rS.Sub ret0Λ.stackPool) : rS.lo + rS.size ≤ 2 ^ 64 := by
  have := pool_fit; obtain ⟨-, h⟩ := hsub; omega

/-- **A range in the pool is off the entry stack's region**, word by word
(`houtS` at `entryR`). -/
theorem outS_of_sub (hsub : rS.Sub ret0Λ.stackPool) :
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
theorem rS_of_sub (hsub : rS.Sub ret0Λ.stackPool) :
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

/-- **A 16-aligned value is kept by `and $-16`.** -/
theorem and16 {x : BitVec 64} (h : x.toNat % 16 = 0) : x &&& (-16 : Int64).toBitVec = x := by
  have hc : (-16 : Int64).toBitVec = ~~~15#64 := by decide
  have h15 : x &&& 15#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (15#64).toNat = 2 ^ 4 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
    simpa using h
  rw [hc]
  generalize (15#64) = y at h15 ⊢
  ext i hi
  have := congrArg (fun z => z[i]) h15
  simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero] at this ⊢
  cases hx : x[i] <;> simp_all

/-- **`_start`'s entry node**: at `_start`, in the entry stack's frame at
its top (offset `0`), the source at `c0`. -/
def entry0N (c0 : Ctl) : ND := ⟨labT "_start", ⟨0, []⟩, fun _ c => c = c0⟩
/-- After `_start`'s `xor %ebp, %ebp`. -/
def entry1N (c0 : Ctl) : ND := ⟨labT "_start" + Int64.ofNat 2, ⟨0, []⟩, fun _ c => c = c0⟩
/-- After `_start`'s `andq $-16, %rsp`, at the call, in a fresh region. -/
def entry2N (c0 : Ctl) : ND := ⟨labT "_start" + Int64.ofNat 2 + Int64.ofNat 4, SO.entry, fun _ c => c = c0⟩
/-- At `scc_rt_start` as seen from `_start`'s call: the return address at
offset `-8` of the entry stack's region. -/
def entryCN (c0 : Ctl) : ND := ⟨labT "scc_rt_start", ⟨-8, []⟩, fun _ c => c = c0⟩

/-- `_start`'s call of `scc_rt_start`. -/
def startCallB : List (Directive × Nat) := (parse("call scc_rt_start")).zip [5]

block_spec startCallB (-8) 0 SO.entry startCallB

/-- **An `andq $k, %rsp` node of the main path before the take** is
inside `Wr`, and no take moves it: as `nodeW_fi_pre`, at `andRsp`. -/
theorem nodeW_and_pre {R : Region} {F : MachineData → Prop} {n : ND} {k : Int64} {z : Nat} {l : Label}
    {off : Nat} {p : Int64}
    (hb : blockAtB ret0Cells l off [(andRsp k, z)] = true) (he : labT l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  nodeW_pre hp hok hT fun _s c σ hs hn _ hpc _ _ hJ hP hO => by
    have hc := cellT hb he hs hn hpc
    obtain ⟨t, hex, hst⟩ := exec_andRsp hc
    exact sfacts_silent (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hst
      (fun _ ⟨_, h⟩ => h ▸ next_same hpc hph _) hO

/-- **`_start` as one segment inside `Wr`**: `xor %ebp, %ebp`
(`flag_ndW`), `andq $-16, %rsp`, which keeps the entry stack's 16-aligned
top (`and16`) and so its region (`swand_ndW`), and the call of
`scc_rt_start` (`call_nd_FWK`, with `KC := True`: the take keeps
`ret0F` and the entry stack's cells), its callee's region `entryC` at
offset `-8`. The callee's segment is `hS`, for every frame condition
`F'` stable in `entryC`, kept by the take and implying `ret0F`. -/
theorem entry_segW {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} (c0 : Ctl)
    (hC0 : CFacts ret0Λ ret0Λ.static c0) (hsub : rS.Sub ret0Λ.stackPool) {Q : Frag isa}
    (hS : ∀ F' : MachineData → Prop, FStable (entryR.callee (-8) (-296) 8) F' → KStable (Kr rS) F' →
      (∀ m, F' m → ret0F m) → ∀ Q' : Frag isa,
      SegW (Wr rS) (Kr rS) p lbl ms (At ret0Exe ret0End (entryR.callee (-8) (-296) 8) F' (startN0 labT c0)) Q') :
    SegW (Wr rS) (Kr rS) p lbl ms (At ret0Exe ret0End entryR ret0F (entry0N c0)) Q := by
  have hb0 : blockAtB ret0Cells "_start" 0 [(FI.toDir (.xor_rr32_self .rbp), 2)] = true := by decide +kernel
  have hb1 : blockAtB ret0Cells "_start" 2 [(andRsp (-16), 4)] = true := by decide +kernel
  have hb2 : blockAtB ret0Cells "_start" 6 startCallB = true := by decide +kernel
  refine (seg_oneW (flag_ndW (n := entry0N c0) (N := fun _ : Unit => entry1N c0) (E := fun e : Empty => e.elim)
    (fi := .xor_rr32_self .rbp) (z := 2) rfl ret0F_stable
    (fun s hs hn => show CodeAt s (labT "_start") _ from (ofNat_zero' (labT "_start")) ▸ codeT hb0 hs hn)
    (nodeW_fi_pre hb0 (ofNat_zero' _) rfl (fun _ _ hJ => hJ ▸ hC0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel))
    fun σ c hJ fl => ⟨c, .refl c, .inl ⟨(), rfl, rfl, hJ⟩⟩)).seq ?_
  refine sw_seqW (lo := -65536) (hi := 0) (F' := fun v m => v = entryR.base ∧ ret0F m) (n' := entry2N c0)
    (swand_ndW (k := -16) (z := 4) (n := entry1N c0) (fun s hs hn => codeT hb1 hs hn) rfl rfl
      (nodeW_and_pre hb1 rfl rfl (fun _ _ hJ => hJ ▸ hC0) (by decide +kernel) (by decide +kernel)
        (by decide +kernel))
      fun m σ c hA hD hJ fl => ?_) fun v _ => ?_
  · have hsp : σ.regs.get64 .rsp = entryR.base := by
      rw [hA.so .rsp 0 rfl]; simp [Region.addr]
    have hv : (andRegs (-16) σ.regs).get64 .rsp = entryR.base := by
      simp only [andRegs, Reg64s.get64_set64_self]; rw [hsp]; exact and16 entryR_al
    rw [hv]
    exact ⟨entryR_ok, ⟨rfl, hD⟩, σ.slot, fun k hk => hA.slot k hk, c, .refl c, hJ⟩
  refine SegW.mono_pre (P := At ret0Exe ret0End entryR ret0F (entry2N c0)) ?_
    fun s c ⟨he, hn, hdc, hpc, σ, hA, ⟨hvb, hD⟩, hJ⟩ => ⟨he, hn, hdc, hpc, σ, by subst hvb; exact hA, hD, hJ⟩
  refine (seg_oneW (seg_ndW (N := fun _ : Unit => entryCN c0) (E := fun e : Empty => e.elim) (by simp [startCallB])
    startCallB_ok ret0F_stable entryR_ok (by decide) (by decide)
    (fun s hs hn => show CodeAt s (labT "_start" + Int64.ofNat 2 + Int64.ofNat 4) _ from
      (ofNat_add' _ 2 4) ▸ codeT hb2 hs hn)
    (blkW_pre (n := entry2N c0) (l := "_start") (off := 6) (dead := fun _ => false) (ra := 0) hb2
      (ofNat_add' _ 2 4) startCallB_ok entryR_ok (by decide) (by decide) (fun _ _ hJ => hJ ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk hr => (noRet_false (by decide +kernel) k hk hr).elim) (fun _ _ _ => rfl) (by decide +kernel))
    fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)).seq ?_
  · rw [show (entry2N c0).o = SO.entry from rfl, startCallB_run, ret0_labT]; rfl
  · rw [show (entry2N c0).o = SO.entry from rfl, startCallB_run]; rfl
  · exact hJ
  refine (call_nd_FWK (KC := True) (nC := entryCN c0) (exe := ret0Exe) (endPc := ret0End)
    (N := fun e : Empty => e.elim) (E := fun e : Empty => e.elim) (e0 := 0) (lo' := -296) (hi' := 8)
    (M := fun _ => True) (F₂ := ret0F)
    (Ne := fun _ : Unit => startN0 labT c0) (Ex := fun _ (e : Empty) => e.elim)
    entryR_ok ret0F_stable (by show (-65536 : Int) ≤ -8 - 0 + -296; decide) (by decide)
    (by show (-8 : Int) - 0 < 0; decide) (by show (-8 : Int) - 0 + 8 ≤ 0; decide)
    (by show ((-8 : Int) - 0) % 8 = 0; decide) (by decide) (by decide)
    (fun _ => TakeK.kstable fun _ _ h => ret0F_takeMem hsub h)
    (fun _ s s' hk _ k hk' _ => by obtain ⟨pm, he⟩ := hk.mem; rw [he]; exact loadInt_takeMem (rS_of_sub hsub k hk'))
    (fun _ h _ => h)
    (fun R' F' _ _ _ hF' hK' hFF hR'e _ _ _ _ => by subst hR'e; exact hS F' hF' (hK' trivial) hFF _)
    (fun _ => rfl) (fun σC c hJ => ⟨(), rfl, hJ⟩) fun _ x => x.elim).mono_post
    fun _ _ h => h.elim (fun ⟨e, _⟩ => e.elim) fun ⟨e, _⟩ => e.elim

/-- **The callee's region of `_start`'s call**: below the return address,
room for `scc_rt_start`'s frames. -/
abbrev entryC : Region := entryR.callee (-8) (-296) 8

/-- The callee's region does not wrap. -/
theorem entryC_ok : entryC.OK :=
  Region.callee_ok entryR_ok (by show (-65536 : Int) ≤ -8 + -296; decide) (by decide) (by decide) (by decide)

/-- **The callee's cells are off a range in the pool** (`hRS` at `entryC`). -/
theorem rS_of_subC (hsub : rS.Sub ret0Λ.stackPool) :
    ∀ k, entryC.Off k → ∀ i < 8, entryC.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS := by
  intro k hk
  rw [Region.callee_addr]
  exact rS_of_sub hsub _ (Region.callee_off (by show (-65536 : Int) ≤ -8 + -296; decide) (by decide) (by decide) hk)

/-- **A range in the pool is off the callee's region**, word by word
(`houtS` at `entryC`). -/
theorem outS_of_subC (hsub : rS.Sub ret0Λ.stackPool) :
    ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ entryC.base.toNat + entryC.lo ∨ (entryC.base.toNat : Int) + entryC.hi ≤ a :=
  out_callee entryR_ok (by show (-65536 : Int) ≤ -8 + -296; decide) (by decide) (by decide) (by decide)
    (outS_of_sub hsub)

/-- **The consumer's obligations of `ret0` from `_start`**, at the entry
stack (`entryR`), the entry frame condition `F := ret0F`, and the source
start `X64Consumer.c0`: `entry_segW`, then `ret0_segW` at the callee's
region `entryC` and its frame condition (the memory side's facts there by
`.mono`, the take's keeping it from `KStable`), through `inst_of_segW`.
`CFacts` by `cfacts_c0`, `main`'s exit by `ret0_exit`, given `p`'s `main`
(`hd`) with body `mainBody` (`hb`); the take's range only in the pool
(`hsub`), the take site's states by `takeSiteW` from the range named by
its registers (`hrS`). -/
theorem ret0_instE {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ls0 : Lsize}
    {ms : MemSide isa} (hms : ms = msOf ret0Λ μ0 rd G own ret0Λ.static ls0)
    {n0 k0 : BitVec 64} (hn0 : n0 = 0#64)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms ret0F (pinA labT + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms ret0F ret0Exe ret0End n0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA labT + n0 + 8#64) (stacksA labT + k0),
      StOk ms ret0F (pinA labT + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms ret0F ret0Exe ret0End k0)
    (h8 : (stacksA labT + k0 + 16384#64).toNat % 8 = 0)
    (hok : (swR (stacksA labT + k0 + 16384#64) (-80) 0).OK)
    (hsubR : ∀ k, (swR (stacksA labT + k0 + 16384#64) (-80) 0).Off k →
      ((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA labT + k0 + 16384#64) (-80) 0).addr k).toNat + 7))
    (hfit : (limA (tpOf (pinA labT + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf (pinA labT + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA labT + k0 + 16384#64).toNat + -80 ∨
      ((stacksA labT + k0 + 16384#64).toNat : Int) + 0 ≤ (limA (tpOf (pinA labT + n0 + 8#64))).toNat)
    (hlimM : LimOk ms ret0F (limA (tpOf (pinA labT + n0 + 8#64)))
      (stacksA labT + k0 + 16384#64 - 8#64 - 8#64 - (32 : Int64).toBitVec))
    (hlimW : LimOk ms ret0F (limA (tpOf (pinA labT + n0 + 8#64)))
      (stacksA labT + k0 + 16384#64 - 8#64 - 8#64 - (32 : Int64).toBitVec - 8#64 - 8#64 - (16 : Int64).toBitVec))
    {d : Decl} (hd : p.find? (·.name == "main") = some d) (hb : d.body = mainBody)
    (hsub : rS.Sub ret0Λ.stackPool)
    (hrS : rS = ⟨(stacksA labT + k0).toNat, 16384⟩) :
    ∃ inv : Frag isa, (∀ s c, At ret0Exe ret0End entryR ret0F (entry0N Spike.Lib.X64Consumer.c0) s c →
      inv s c) ∧
      Nodes ret0Λ p μ0 rd G own (IOf ret0Λ.static ls0 inv) ∧
      TakePath ret0Λ p μ0 (IOf ret0Λ.static ls0 inv) rS Tk ∧
      AbortPath μ0 (IOf ret0Λ.static ls0 inv) (fun _ => False) ∧ NoWrite (IOf ret0Λ.static ls0 inv) := by
  subst hms
  refine inst_of_segW (entry_segW _ cfacts_c0 hsub fun F' hF' hK' hFF _ => ?_) mu0_take (fun _ _ h => h)
  exact ret0_segW (lbl := ret0Λ.static) cfacts_c0 rfl hF' entryC_ok (by decide) (by decide) hFF hn0 hn
    (hhdr.mono hFF) (htcb.mono hFF) hk (fun e he => (hfld e he).mono hFF) (htk.mono hFF) h8 hok hsubR hfit hout
    (hlimM.mono hFF) (hlimW.mono hFF) (ret0_exit rfl hd hb) (rS_of_subC hsub) (fitS_of_sub hsub) (outS_of_subC hsub)
    (takeMem_of_kstable hK' ret0Exe ret0End) hsub
    fun _ _ _ _ => takeSiteW cfacts_c0 _ rfl hrS hsub

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
  simp only [Scc.Sem.Range.contains, hl]
  omega

/-- **`ret0_instE` at the first take**: `n0 = k0 = 0` and the take's range
`rS0`, the layout's arithmetic and `rS0`'s facts (`rS0_sub`, `rS0_subR`)
discharged here. Open: the runtime's stores and loads, and `main`. -/
theorem ret0_instR {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ls0 : Lsize}
    {ms : MemSide isa} (hms : ms = msOf ret0Λ μ0 rd G own ret0Λ.static ls0)
    (hhdr : StOk ms ret0F (pinA labT + 0#64) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms ret0F ret0Exe ret0End 0#64)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA labT + 0#64 + 8#64) (stacksA labT + 0#64),
      StOk ms ret0F (pinA labT + 0#64 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms ret0F ret0Exe ret0End 0#64)
    (hlimM : LimOk ms ret0F (limA (tpOf (pinA labT + 0#64 + 8#64)))
      (stacksA labT + 0#64 + 16384#64 - 8#64 - 8#64 - (32 : Int64).toBitVec))
    (hlimW : LimOk ms ret0F (limA (tpOf (pinA labT + 0#64 + 8#64)))
      (stacksA labT + 0#64 + 16384#64 - 8#64 - 8#64 - (32 : Int64).toBitVec - 8#64 - 8#64 - (16 : Int64).toBitVec))
    {d : Decl} (hd : p.find? (·.name == "main") = some d) (hb : d.body = mainBody) :
    ∃ inv : Frag isa,
      (∀ s c, At ret0Exe ret0End entryR ret0F (entry0N Spike.Lib.X64Consumer.c0) s c → inv s c) ∧
      Nodes ret0Λ p μ0 rd G own (IOf ret0Λ.static ls0 inv) ∧
      TakePath ret0Λ p μ0 (IOf ret0Λ.static ls0 inv) rS0 Tk ∧
      AbortPath μ0 (IOf ret0Λ.static ls0 inv) (fun _ => False) ∧ NoWrite (IOf ret0Λ.static ls0 inv) := by
  have hpin : pinA labT = 134217728#64 := labT_pinA
  have hst := labT_stacksA
  exact ret0_instE (rS := rS0) hms rfl (by decide) hhdr htcb (by decide) hfld htk
    (by rw [hst]; decide) (by rw [hst]; exact ⟨by decide, by decide⟩) rS0_subR
    (by rw [hpin]; decide) (by rw [hpin, hst]; decide) hlimM hlimW hd hb rS0_sub rfl

end Entry

end Spike.Lib.X64.Flow.Ret0.Inst
