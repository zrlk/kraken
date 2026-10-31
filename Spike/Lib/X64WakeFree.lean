/-
**The free pcs of wake.w's global owned-words map `ownG`** (x86-64; the
label-relative part of `Spike/Lib/A64WakeWcPreW.lean` and
`Spike/Lib/A64WakeWcPreWN.lean`): a pc where `ownG` picks the
first instance's `ownW` whatever the state (`GoodW`'s last disjunct) and
off the take site, checked by the kernel against the certificate's labels
with no absolute address in this file, and `ownG`'s agreement with `ownW`
on a block or a node at free pcs.

- `cv`, `inCv`, `freeN`: a label's address, a label range, a free pc.
- `freeAt`, `freeBlk`: the pcs at byte offsets from a label, a block's.
- `lab_cv`, `freeAt_pc`, `freeAt_lab`, `freeBlk_pc`: the checks read
  through `L.lab`.
- `freeLabs`, `goodW_of_freeN`, `site_ne_of_freeN`: `GoodW` and off the
  take site at a free pc.
- `blkAgreeW`: a block's agreement from its free pcs and free end.
- `succ_pc`, `nodeAgreeW`: a node's successors' pc; its agreement.

**Unlike AArch64**: offsets are bytes and cells are sized, so `freeAt l os`
checks the pcs `lab l + o` for the byte offsets `o ∈ os` (AArch64's
`freeAt l k n`: the `n` pcs `lab l + 4 (k + j)`), `freeBlk l k blk` a
block's pcs `lab l + k + cellOff blk j`; `ownG`'s second range is
`.Lwc_main.x20`–`.Lwc_main.stk` (AArch64's `.sp4`–`.stack_grow`); the
labels resolve by `codeLabel lo wakeCells`; `blkAgreeW` has no `hal`;
`nodeAgreeW` is at a cell of size `z` other than `syscall` (AArch64's
`svc`, `4`). The wc_main-specific rest of the A64 pair (`wcTabW`,
`blkW_wcG`, `nodeW_dmb_pre`, `c0N`, `nodeW_wcG`, `NodeW.ofAll`) is in
(x64 `WcPreW`/`WcPreWN`), which imports this file.
-/
import Spike.Lib.X64WakeOwnGAgree
import Spike.Lib.Rt.X64RtPhOfTab

namespace Spike.Lib.X64.WakePh.WcW

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq pcAt)
open Scc.Sem (Marks TreeLeaf)
open Scc.Sem.X64 (codeLabel pcOf abi)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (StSucc)
open Spike.Lib.X64 (ND BlkW NodeW At CodeAt cellOff arun okBlk)
open Spike.Lib.X64.Rt.PhOfTab (pcAt_eq)
open Kraken.Promising.Lower.X64 (CellAt)

/-! ## The label-relative checks -/

/-- A label's address in wakeCells at the canonical base (`0` if absent). -/
def cv (l : Label) : Nat := (codeLabel lo wakeCells l).getD 0

/-- `x` in `[cv l₁, cv l₂)`. -/
def inCv (l₁ l₂ : Label) (x : Nat) : Bool := cv l₁ ≤ x && x < cv l₂

/-- **A pc where `ownG` picks `ownW` whatever the state**: off `ownG`'s four
ranges, and off the take site. -/
def freeN (x : Nat) : Bool :=
  !inCv "scc_rt_alloc_tcb" "scc_rt_thread_reserve" x && !inCv "scc_rt_thread_init" "scc_rt_stack_release" x &&
    !inCv ".Lwc_main.x20" ".Lwc_main.stk" x && !inCv "scc_rt_abort" "scc_rt_thr_worker" x &&
    x != cv Spike.Lib.X64.Flow.Ret0.StackTake.siteL

/-- **The pcs `lab l + o` for the byte offsets `o ∈ os` are free.** -/
def freeAt (l : Label) (os : List Nat) : Bool :=
  os.all fun o => match pcAt (codeLabel lo wakeCells) l o with
    | some t => freeN t
    | none => false

/-- **A block's pcs from `lab l + k` are free.** -/
def freeBlk (l : Label) (k : Nat) (blk : List (Directive × Nat)) : Bool :=
  freeAt l ((List.range blk.length).map fun j => k + cellOff blk j)

variable {L : RuntimeLayout} {a : BitVec 64} {s : State}

/-- A label of wakeCells read through `L.lab`. -/
theorem lab_cv (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {l : Label}
    (hs : (codeLabel lo wakeCells l).isSome = true) (hb : cv l < 2 ^ 64) : (L.lab l).toBitVec.toNat = cv l := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
  have e : cv l = x := by simp [cv, hx]
  rw [e] at hb ⊢
  rw [hlab l x hx]
  show (BitVec.ofNat 64 x).toNat = x
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]

/-- **The pcs `freeAt` checks**, read through `L.lab`. -/
theorem freeAt_pc (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {l : Label}
    {os : List Nat} (h : freeAt l os = true) {o : Nat} (ho : o ∈ os) :
    freeN (L.lab l + Int64.ofNat o).toBitVec.toNat = true := by
  have h1 := List.all_eq_true.mp h o ho
  revert h1
  cases ht : pcAt (codeLabel lo wakeCells) l o with
  | none => intro h1; cases h1
  | some t => intro h1; rw [pcAt_eq hlab ht]; exact h1

/-- **`freeAt` at a label.** -/
theorem freeAt_lab (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {l : Label}
    (h : freeAt l [0] = true) : freeN (L.lab l).toBitVec.toNat = true := by
  have := freeAt_pc hlab h (List.mem_singleton.mpr rfl)
  rwa [show Int64.ofNat 0 = 0 from rfl, Int64.add_zero] at this

/-- **The pcs `freeBlk` checks**, read through `L.lab`. -/
theorem freeBlk_pc (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {l : Label}
    {k : Nat} {blk : List (Directive × Nat)} (h : freeBlk l k blk = true) {j : Nat} (hj : j < blk.length) :
    freeN (L.lab l + Int64.ofNat k + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true := by
  have := freeAt_pc hlab h (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  rwa [Int64.ofNat_add, ← Int64.add_assoc] at this

/-- The labels `freeN` reads are wakeCells', below `2 ^ 64`. -/
theorem freeLabs :
    [("scc_rt_alloc_tcb" : Label), "scc_rt_thread_reserve", "scc_rt_thread_init", "scc_rt_stack_release",
      ".Lwc_main.x20", ".Lwc_main.stk", "scc_rt_abort", "scc_rt_thr_worker",
      Spike.Lib.X64.Flow.Ret0.StackTake.siteL].all
      (fun l => (codeLabel lo wakeCells l).isSome && decide (cv l < 2 ^ 64)) = true := by
  unfold cv; rw [← codeT_eq]; decide +kernel

/-- **At a free pc `ownG` picks `ownW`.** -/
theorem goodW_of_freeN (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (h : freeN (pcOf s) = true) : GoodW L s := by
  have hl : ∀ l ∈ [("scc_rt_alloc_tcb" : Label), "scc_rt_thread_reserve", "scc_rt_thread_init",
      "scc_rt_stack_release", ".Lwc_main.x20", ".Lwc_main.stk", "scc_rt_abort",
      "scc_rt_thr_worker", Spike.Lib.X64.Flow.Ret0.StackTake.siteL], (L.lab l).toBitVec.toNat = cv l := by
    intro l hl
    have := List.all_eq_true.mp freeLabs l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact lab_cv hlab this.1 this.2
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hl
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, -⟩ := hl
  simp only [freeN, inCv, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    bne_iff_ne, ne_eq, Nat.not_le, Nat.not_lt] at h
  refine .inr (.inr ⟨?_, ?_, ?_, ?_⟩) <;> unfold inPc <;> simp only [e1, e2, e3, e4, e5, e6, e7, e8] <;> omega

/-- **A free pc is off the take site.** -/
theorem site_ne_of_freeN (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    {x : Nat} (h : freeN x = true) : x ≠ (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  have := List.all_eq_true.mp freeLabs Spike.Lib.X64.Flow.Ret0.StackTake.siteL (by simp)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  rw [lab_cv hlab this.1 this.2]
  simp only [freeN, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact h.2

/-! ## A block's agreement -/

section Agree

variable {μ : Marks} {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {n : ND} {blk : List (Directive × Nat)} {blo bhi : Int}

/-- **`ownG` agrees with `ownW` on a covered block at free pcs**: its pcs
(`hin`) and the pc its run ends at (`hlast`) free, the take site `L`'s. -/
theorem blkAgreeW (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hsite : μ.site .take = some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hin : ∀ k < blk.length, freeN (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat = true)
    (hlast : ∀ σ c, n.J σ c →
      freeN (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = true) :
    BlkW (fun s _ => ownG L a s = ownW L a (phW (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownG L a s' = ownW L a (phW (pcOf s'))) (fun _ _ => False) exe endPc R F n blk := by
  refine hagW hlab hcode hok hR hlo hhi (fun x hx k hk => ?_) (fun σ c _ k hk s m _ _ _ hs => ?_)
    (fun σ c hJ k hk s m _ _ _ hs => ?_)
  · rw [hsite] at hx; cases hx
    exact site_ne_of_freeN hlab (hin k hk)
  · exact goodW_of_freeN hlab (by unfold pcOf; rw [hs]; exact hin k hk)
  · refine goodW_of_freeN hlab ?_
    unfold pcOf; rw [hs]
    rcases Nat.lt_or_ge (k + 1) blk.length with hk1 | hk1
    · rw [Spike.Lib.X64.arun_pc _ (am := ⟨n.pc, n.o, σ⟩) hok hk1]; exact hin (k + 1) hk1
    · rw [List.take_of_length_le (by omega)]; exact hlast σ c hJ

end Agree

/-! ## A node's agreement -/

/-- **A successor of a cell of size `z` off `syscall`** whose tree's leaves
are `z` bytes on (`hl`), off the take site (`hns`), is `z` bytes on. -/
theorem succ_pc {μ : Marks} {s s' : State} {d : Directive} {z : Nat} {tree : EvTree State} (hc : CellAt s d z)
    (hd : ∀ w w', d ≠ .instr (.regular w w' .syscall)) (hex : isa.exec s = some tree)
    (hl : ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z)
    (hns : ∀ a, μ.site .take = some a → pcOf s ≠ a) (h : StSucc μ s s') : s'.st.2 = s.st.2 + Int64.ofNat z := by
  have hs : abi.atSys s = false := Scc.Sem.X64.atSyscall_false_of_cellAt hc hd
  rcases h with ⟨-, tree', htr, hl'⟩ | ⟨hs', -⟩ | ⟨a, ha, hpc, -⟩
  · rw [hex] at htr; cases htr; exact hl s' hl'
  · rw [hs] at hs'; cases hs'
  · exact absurd hpc (hns a ha)

section NAgree

variable {μ : Marks} {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {n : ND}

/-- **`ownG` agrees with `ownW` at a node** whose pc and next pc are free
(`hf0`, `hfz`), each of its states at a cell of size `z` off `syscall`
whose leaves are `z` bytes on (`hstep`). -/
theorem nodeAgreeW (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : μ.site .take = some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) {z : Nat}
    (hf0 : freeN n.pc.toBitVec.toNat = true) (hfz : freeN (n.pc + Int64.ofNat z).toBitVec.toNat = true)
    (hstep : ∀ s c, At exe endPc R F n s c → ∃ d tree, CellAt s d z ∧
      (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧ isa.exec s = some tree ∧
      ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z) :
    NodeW (fun s _ => ownG L a s = ownW L a (phW (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownG L a s' = ownW L a (phW (pcOf s'))) (fun _ _ => False) exe endPc R F n := by
  intro s c hAt
  have hpc : s.st.2 = n.pc := hAt.2.2.2.1
  have hp0 : pcOf s = n.pc.toBitVec.toNat := by unfold pcOf; rw [hpc]
  obtain ⟨d, tree, hc, hd, hex, hl⟩ := hstep s c hAt
  refine ⟨⟨ownG_W hlab (goodW_of_freeN hlab (by rw [hp0]; exact hf0)), fun s' h => ?_⟩, fun _ h => h⟩
  have hns : ∀ x, μ.site .take = some x → pcOf s ≠ x := by
    intro x hx; rw [hsite] at hx; cases hx; rw [hp0]; exact site_ne_of_freeN hlab hf0
  have e := succ_pc hc hd hex hl hns h
  refine ownG_W hlab (goodW_of_freeN hlab ?_)
  unfold pcOf; rw [e, hpc]; exact hfz

end NAgree

end Spike.Lib.X64.WakePh.WcW

/-- info: 'Spike.Lib.X64.WakePh.WcW.lab_cv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.lab_cv

/-- info: 'Spike.Lib.X64.WakePh.WcW.freeAt_pc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.freeAt_pc

/-- info: 'Spike.Lib.X64.WakePh.WcW.freeAt_lab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.freeAt_lab

/-- info: 'Spike.Lib.X64.WakePh.WcW.freeBlk_pc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.freeBlk_pc

/-- info: 'Spike.Lib.X64.WakePh.WcW.freeLabs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.freeLabs

/-- info: 'Spike.Lib.X64.WakePh.WcW.goodW_of_freeN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.goodW_of_freeN

/-- info: 'Spike.Lib.X64.WakePh.WcW.site_ne_of_freeN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.site_ne_of_freeN

/-- info: 'Spike.Lib.X64.WakePh.WcW.blkAgreeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.blkAgreeW

/-- info: 'Spike.Lib.X64.WakePh.WcW.succ_pc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.succ_pc

/-- info: 'Spike.Lib.X64.WakePh.WcW.nodeAgreeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcW.nodeAgreeW
