/-
**`hello.w` on x86-64, the closed run (base)**: the loaded program, its
states and the three kernel steps of the start-up path, forward.

This module fixes the concrete setting of the closed non-vacuity results
(`Spike/Test/HelloRootL0XClosed.lean`): the canonical x64 target with two
thread slots under the Linux entry state, `SccCode.helloAsm` laid out at
`Λe`; and states the forward steps of thread 0 from the load as `SegP`
segments (`Spike/Lib/X64FwdSeg.lean`) with the shared memory and the kernel
state exact.

- The load (`hload`, under the parse `hparse`, the one owned hypothesis),
  the initial configuration `t0`, memory `M0`, kernel state `X0`; `solo0`:
  thread 0 runs alone there.
- `mk R F D pc`: a state of the loaded executable; `cellM`: its cells.
- `Sg`: a segment of thread 0 on the target.
- The three kernel steps of the path, each at the state the run reaches it
  in (registers and flags as the run has them; private memory, shared
  memory and kernel state arbitrary, resp. exact for the take):
  - `sg_rtSigaction`: `rt_sigaction(SIGPIPE, scc_rt_sigign, NULL, 8)` in
    `scc_rt_start` (cell 18) returns 0;
  - `sg_take`: the take site (cell 504) takes `⟨72022848, 16384⟩`, the
    first 16 KiB of the stack pool, fresh because no range is held and every
    shared write so far lies below the pool;
  - `sg_archSetFs`: `arch_prctl(ARCH_SET_FS, 71859016)` (cell 32) sets
    `%fs` to the pinned TCB and returns 0.
-/
import Spike.Lib.X64FwdSeg
import Spike.Test.HelloLinkedX64Le
import Spike.Lib.X64Block
import Kraken.Promising.Lower.EventsX64Flags
import Kraken.Promising.Lower.EventsX64Sys
import Scc.Sem.SysX64

namespace Spike.Test.HelloRootL0XClosed

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Test.HelloLinkedX64 (Λe layoutEX_e)
open Spike.Lib.Fwd

/-! ## The loaded program -/

/-- The target: two thread slots, Linux entry state. -/
abbrev T : Target := target (kernel 2) .linux
/-- The data symbols. -/
abbrev syms : List (String × Nat) := loadSyms Λe SccCode.helloSecs.rodata
/-- Thread 0's initial state. -/
abbrev st0 : State := threadAt .linux Λe.code.lo SccCode.helloCells syms
/-- The initial shared memory (image and `.rodata` words). -/
abbrev mem0 : List (Loc × Val) :=
  imageMem Λe ++ wordsMem (rodataWords Λe SccCode.helloSecs.rodata (Scc.Cert.Link.X64.quadCode Λe SccCode.helloCells))
/-- The initial configuration. -/
abbrev t0 : (machine (kernel 2)).Cfg := loadProg (kernel 2) .linux Λe SccCode.helloCells syms mem0
/-- The marks. -/
abbrev μ0 : Marks := T.marks SccCode.helloAsm Λe
/-- The initial shared memory, as a `Memory`. -/
abbrev M0 : Memory := { init := mem0, msgs := #[] }
/-- The initial kernel state. -/
abbrev X0 : Kernel.KState := Kernel.KState.init 2 .linux Λe

/-- The parse of `hello.w`'s assembly: the one hypothesis of the closed results. -/
abbrev Parse : Prop :=
  Scc.Cert.Link.X64.parsesTo SccCode.helloAsm SccCode.helloCells SccCode.helloSecs = true

set_option maxRecDepth 100000 in
theorem hload (hparse : Parse) : T.load SccCode.helloAsm Λe = some t0 :=
  have hl : Scc.Cert.Link.X64.loadOk Λe SccCode.helloCells SccCode.helloSecs SccCode.helloAsm.labelOffs = true :=
    Spike.Lib.PlaceWX.loadOk_of_placeWX (o := Spike.Lib.X64.HelloPh.RootLit.oH) layoutEX_e.hp
  have hE : Entry.linux.clear Λe = true := Spike.Lib.PlaceWX.clear_of_placeWX layoutEX_e.hp
  Scc.Cert.Link.X64.load_of_loadOk (H := kernel 2) (E := .linux) hparse hl hE

theorem habove : ∀ p ∈ syms, Λe.code.lo ≤ p.2 := by decide +kernel

instance hvalid : Kraken.Executable.ValidLayout st0.exe :=
  Scc.Cert.Link.X64.validLayout_of_loadOk (Spike.Lib.PlaceWX.loadOk_of_placeWX layoutEX_e.hp) _

theorem hlays : Scc.Cert.Rt.X64.Lays st0.exe SccCode.helloCells 0 :=
  Scc.Cert.Link.X64.lays_threadAt _ _ _ _ habove

theorem hend : st0.endPc = Scc.Cert.Rt.X64.endOf st0.exe SccCode.helloCells 0 :=
  Scc.Cert.Link.X64.endPc_threadAt _ _ _ _ habove

set_option maxRecDepth 100000 in
/-- The `m`-th cell, at any state of the loaded executable whose pc is its address. -/
theorem cellI {s : State} (he : s.exe = st0.exe) (hn : s.endPc = st0.endPc) {m : Nat} {d : Directive} {z : Nat}
    (hm : SccCode.helloCells[m]? = some (d, z)) (hd : d.isLabel = false)
    (hp : s.st.2 = Kraken.Executable.addrOf st0.exe m) : CellAt s d z := by
  obtain ⟨h1, h2, h3⟩ := Scc.Cert.Rt.X64.cellAt_prefix (st := st0) hlays hend hm hd s.st.1
  refine ⟨he ▸ h1, ?_, ?_⟩
  · rw [hn, hp]; simpa using h2
  · rw [he, hp]; simpa using h3

/-- A state of the loaded executable: registers `R`, flags `F`, private memory `D`, pc `pc`. -/
abbrev mk (R : Reg64s) (F : StatusFlags) (D : DataMem) (pc : Nat) : State :=
  { st0 with st := ({ regs := R, status := F, dmem := D }, Int64.ofNat pc) }

/-- The `m`-th cell at pc `pc`, in every machine data. -/
theorem cellM (m pc : Nat) {d : Directive} {z : Nat} (hm : SccCode.helloCells[m]? = some (d, z))
    (hd : d.isLabel = false) (hp : Kraken.Executable.addrOf st0.exe m = Int64.ofNat pc) (R : Reg64s)
    (F : StatusFlags) (D : DataMem) : CellAt (mk R F D pc) d z :=
  cellI (s := mk R F D pc) rfl rfl hm hd hp.symm

theorem pcOf_mk (R : Reg64s) (F : StatusFlags) (D : DataMem) {pc : Nat} (hlt : pc < 2 ^ 64) :
    pcOf (mk R F D pc) = pc := by
  show (Int64.ofNat pc).toBitVec.toNat = pc
  rw [Int64.toBitVec_ofNat', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- Thread 0 runs alone in the initial configuration. -/
theorem solo0 : Solo (t0 : (machine (kernel 2)).Cfg) 0 st0 := by
  refine ⟨⟨Thread.init st0, rfl, rfl, rfl, Config.init_bnd _ _ 0 _ rfl⟩, rfl, ?_⟩
  show ¬ ((Kernel.KState.init 2 Entry.linux Λe).runs 0 = false)
  rw [show (Kernel.KState.init 2 Entry.linux Λe).runs 0 = true from rfl]
  decide

theorem t0_mem : t0.1.mem = M0 := rfl
theorem t0_ext : t0.2 = X0 := rfl

/-! ## Sites -/

/-- The site addresses (`codeLabel` of the two site labels). -/
theorem site_eq (hparse : Parse) (k : XferKind) :
    μ0.site k = codeLabel Λe.code.lo SccCode.helloCells k.label := by
  show (cellsOf SccCode.helloAsm).bind _ = _
  rw [(Scc.Cert.Link.X64.parsed_of_parsesTo hparse).1]; rfl

theorem take_at : codeLabel Λe.code.lo SccCode.helloCells XferKind.take.label = some 4200314 := by decide +kernel
theorem rel_at : codeLabel Λe.code.lo SccCode.helloCells XferKind.release.label = some 4200354 := by decide +kernel

/-- No site at a pc other than the take's (4200314) and the release's (4200354). -/
theorem hsiteOf (hparse : Parse) {s : State} (h : pcOf s ≠ 4200314 ∧ pcOf s ≠ 4200354) :
    ∀ k a, μ0.site k = some a → pcOf s ≠ a := by
  intro k a hk
  rw [site_eq hparse] at hk
  cases k
  · rw [take_at] at hk; cases hk; exact h.1
  · rw [rel_at] at hk; cases hk; exact h.2

theorem hsiteMk (hparse : Parse) (R : Reg64s) (F : StatusFlags) (D : DataMem) {pc : Nat} (hlt : pc < 2 ^ 64)
    (h : pc ≠ 4200314 ∧ pc ≠ 4200354) : ∀ k a, μ0.site k = some a → pcOf (mk R F D pc) ≠ a := by
  refine hsiteOf hparse ?_
  rw [pcOf_mk R F D hlt]; exact h

/-! ## Segments of thread 0 -/

/-- A forward segment of thread 0 on the target (`SegP`). -/
abbrev Sg (P : State → Prop) (M : Memory) (X : Kernel.KState) (P' : State → Prop) (M' : Memory)
    (X' : Kernel.KState) : Prop :=
  SegP isa Arch.tso (kernel 2) regVal privLoad pcOf μ0 0 P M X P' M' X'

/-! ## The three kernel steps -/

/-- The registers after a system call returning `r` from a cell of size `z` at `pc`. -/
def retR (R : Reg64s) (F : StatusFlags) (r : BitVec 64) (pc z : Nat) : Reg64s :=
  { R with
    rax := UInt64.ofNat r.toNat
    rcx := UInt64.ofNat (Int64.ofNat pc + Int64.ofNat z).toBitVec.toNat
    r11 := UInt64.ofNat (rflags F).toNat }

/-- A system call's return at a cell of size `z`, on `mk` states: the registers
are `retRegs64`'s (which read neither the private memory nor anything but the
pc and the flags), the pc moves past the cell. -/
theorem ret_mk {R R' : Reg64s} {F : StatusFlags} {D : DataMem} {pc : Nat} {d : Directive} {z : Nat} {r : BitVec 64}
    (hc : CellAt (mk R F D pc) d z)
    (hR : retR R F r pc z = R') :
    abi.ret (mk R F D pc) r = mk R' F D (pc + z) := by
  show { (mk R F D pc) with st := ({ (mk R F D pc).st.1 with regs := retRegs64 (mk R F D pc) r },
    nextPc (mk R F D pc)) } = _
  rw [show retRegs64 (mk R F D pc) r = R' by rw [← hR, retRegs64, nextPc_of_cellAt hc]; rfl, nextPc_of_cellAt hc]
  simp only [mk, Int64.ofNat_add]

/-- Registers at `rt_sigaction` (step 13 of the run). -/
def Rsig : Reg64s :=
  { rax := 13, rsi := 4225552, rdi := 13, rsp := 140737488351184, rbp := 140737488351216, r10 := 8 }
/-- Registers after it: `%rax := 0`, `%rcx :=` the next pc, `%r11 := RFLAGS` (0). -/
def Rsig' : Reg64s :=
  { rcx := 4198464, rsi := 4225552, rdi := 13, rsp := 140737488351184, rbp := 140737488351216, r10 := 8 }
/-- The flags there (all clear). -/
def Fsig : StatusFlags := ⟨false, false, false, false, false, false⟩

set_option maxRecDepth 100000 in
/-- **`rt_sigaction(SIGPIPE, scc_rt_sigign, NULL, 8)` returns 0** (cell 18,
`scc_rt_start`): any private memory, shared memory and kernel state. -/
theorem sg_rtSigaction (D : DataMem) (M : Memory) (X : Kernel.KState) :
    Sg (· = mk Rsig Fsig D 4198462) M X (· = mk Rsig' Fsig D 4198464) M X := by
  refine segP_rtSigaction fun s hs => ?_
  subst hs
  have hc := cellM 18 4198462 rfl rfl (by decide +kernel) Rsig Fsig D
  exact ⟨atSyscall_of_cellAt hc, rfl, ret_mk hc (by decide)⟩

/-- Registers at `arch_prctl` (step 242 of the run). -/
def Rfs : Reg64s :=
  { rax := 158, rcx := 71859016, rsi := 71859016, rdi := 4098, rsp := 140737488351184, rbp := 140737488351216,
    r10 := 8 }
/-- `Rfs` with `%fs` the TCB. -/
def RfsT : Reg64s := { Rfs with fsBase := UInt64.ofNat 71859016 }
/-- Registers after it: `%fs` the TCB, `%rax := 0`, `%rcx :=` the next pc, `%r11 := RFLAGS` (0). -/
def Rfs' : Reg64s :=
  { rcx := 4198520, rsi := 71859016, rdi := 4098, rsp := 140737488351184, rbp := 140737488351216, r10 := 8,
    fsBase := 71859016 }
/-- The flags there (all clear). -/
def Ffs : StatusFlags := ⟨false, false, false, false, false, false⟩

set_option maxRecDepth 100000 in
/-- **`arch_prctl(ARCH_SET_FS, 71859016)` sets `%fs` to the pinned TCB and
returns 0** (cell 32, `scc_rt_start`): any private memory, shared memory and
kernel state. -/
theorem sg_archSetFs (D : DataMem) (M : Memory) (X : Kernel.KState) :
    Sg (· = mk Rfs Ffs D 4198518) M X (· = mk Rfs' Ffs D 4198520) M X := by
  refine segP_archSetFs 71859016 fun s hs => ?_
  subst hs
  have hc := cellM 32 4198518 rfl rfl (by decide +kernel) Rfs Ffs D
  refine ⟨atSyscall_of_cellAt hc, rfl, ?_⟩
  rw [show abi.setTp (mk Rfs Ffs D 4198518) 71859016 = mk RfsT Ffs D 4198518 from rfl]
  exact ret_mk (cellM 32 4198518 rfl rfl (by decide +kernel) RfsT Ffs D) (by decide)

/-- Registers at the take (step 202 of the run): base `%rdi`, size `%rsi`. -/
def Rtk : Reg64s :=
  { rax := 72022848, rsi := 16384, rdi := 72022848, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
/-- The flags there (all clear). -/
def Ftk : StatusFlags := ⟨false, false, false, false, false, false⟩
/-- The range taken: the first 16 KiB of the stack pool. -/
def rTk : Range := ⟨72022848, 16384⟩
/-- The kernel state after the take. -/
def X1 : Kernel.KState := { X0 with held := (0, rTk) :: X0.held, pmem := Kernel.eraseRange X0.pmem rTk }

theorem ov_below {lo n : Nat} (h : lo + n ≤ 72022848) : Kernel.overlaps rTk lo n = false := by
  show (decide (lo < 72022848 + 16384) && decide (72022848 < lo + n)) = false
  rw [decide_eq_false (show ¬ 72022848 < lo + n by omega), Bool.and_false]

theorem init_below : mem0.all (fun p => p.1.addr.toNat + Kernel.locBytes p.1 ≤ 72022848) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The take** (cell 504, the take site in `scc_rt_stack_take`): from the
initial kernel state, at any shared memory with the initial words and every
write below the stack pool, `⟨72022848, 16384⟩` is taken; the private memory
gets the pool's (never held, so zero) bytes there. -/
theorem sg_take (hparse : Parse) (D : DataMem) (M : Memory) (hi : M.init = mem0)
    (hm : M.msgs.all (fun m => m.loc.addr.toNat + Kernel.locBytes m.loc ≤ 72022848) = true) :
    Sg (· = mk Rtk Ftk D 4200314) M X0 (· = mk Rtk Ftk (Kernel.copyRange ∅ D rTk) 4200315) M X1 := by
  refine segP_take rTk (fun c hcm hcx => ?_) fun s hs => ?_
  · have h1 : ∀ l : List (Loc × Val), l.all (fun p => p.1.addr.toNat + Kernel.locBytes p.1 ≤ 72022848) = true →
        l.all (fun p => !Kernel.overlaps rTk p.1.addr.toNat (Kernel.locBytes p.1)) = true := by
      intro l hl
      simp only [List.all_eq_true, decide_eq_true_eq] at hl ⊢
      intro p hp
      rw [ov_below (hl p hp)]; rfl
    have h2 : M.msgs.all (fun m => !Kernel.overlaps rTk m.loc.addr.toNat (Kernel.locBytes m.loc)) = true := by
      simp only [Array.all_eq_true, decide_eq_true_eq] at hm ⊢
      intro i hi
      rw [ov_below (hm i hi)]; rfl
    unfold Kernel.fresh
    rw [hcm, hcx, h2, hi, h1 _ init_below]
    decide
  · subst hs
    have hc := cellM 504 4200314 rfl rfl (by decide +kernel) Rtk Ftk D
    refine ⟨?_, atNop_of_cellAt hc, rfl, ?_⟩
    · rw [site_eq hparse, take_at, pcOf_mk _ _ _ (by decide)]
    · show { (mk Rtk Ftk (Kernel.copyRange ∅ D rTk) 4200314) with
          st := ((mk Rtk Ftk (Kernel.copyRange ∅ D rTk) 4200314).st.1,
            nextPc (mk Rtk Ftk (Kernel.copyRange ∅ D rTk) 4200314)) } = _
      rw [nextPc_of_cellAt (cellM 504 4200314 rfl rfl (by decide +kernel) Rtk Ftk _)]
      rfl

end Spike.Test.HelloRootL0XClosed

/-- info: 'Spike.Test.HelloRootL0XClosed.hload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.hload
/-- info: 'Spike.Test.HelloRootL0XClosed.solo0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.solo0
/-- info: 'Spike.Test.HelloRootL0XClosed.hsiteMk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.hsiteMk
/-- info: 'Spike.Test.HelloRootL0XClosed.ret_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.ret_mk
/-- info: 'Spike.Test.HelloRootL0XClosed.sg_rtSigaction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.sg_rtSigaction
/-- info: 'Spike.Test.HelloRootL0XClosed.sg_archSetFs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.sg_archSetFs
/-- info: 'Spike.Test.HelloRootL0XClosed.sg_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.sg_take
