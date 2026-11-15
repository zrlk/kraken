/-
**`hello.w` on x86-64, the closed run, chunk 1**: steps 0 … 35 of
thread 0 from the load (`HelloRootL0XClosedStep`), one `SegP` segment per
instruction, composed into `c1`.

Generated from the reference run of the program (the states before every
step: registers `R…`, flags `F_…` (`cf pf af zf sf of`), private memory the
entry stack after the 8-byte stores `L…` (after the take: the taken copy
`B2` after `N…`), shared memory the write chain `M…`). Every step is proved,
not trusted: the generator only chooses the lemma and the witnesses.
-/
import Spike.Test.HelloRootL0XClosedStep

namespace Spike.Test.HelloRootL0XClosed

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Test.HelloLinkedX64 (Λe)
open Spike.Lib.Fwd

set_option maxRecDepth 100000

/-! ## Labels -/

theorem lab_scc_rt_start : (_root_.Executable.labels st0.exe).label "scc_rt_start" = Int64.ofNat 4198413 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)
theorem lab_scc_rt_sigign : (_root_.Executable.labels st0.exe).label "scc_rt_sigign" = Int64.ofNat 4225552 :=
  Scc.Cert.Rt.X64.label_threadAt_of_sym (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Scc.Cert.Rt.X64.ne_label_of_codeLabel (lo := Λe.code.lo) (by decide +kernel))
theorem lab_scc_rt_alloc_tcb : (_root_.Executable.labels st0.exe).label "scc_rt_alloc_tcb" = Int64.ofNat 4199029 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)
theorem lab__Lscc_rt_alloc_tcb_full : (_root_.Executable.labels st0.exe).label ".Lscc_rt_alloc_tcb.full" = Int64.ofNat 4199270 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)
theorem lab__Lscc_rt_alloc_tcb_len : (_root_.Executable.labels st0.exe).label ".Lscc_rt_alloc_tcb.len" = Int64.ofNat 4199070 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)
theorem lab_scc_rt_pinned_next : (_root_.Executable.labels st0.exe).label "scc_rt_pinned_next" = Int64.ofNat 4225776 :=
  Scc.Cert.Rt.X64.label_threadAt_of_sym (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Scc.Cert.Rt.X64.ne_label_of_codeLabel (lo := Λe.code.lo) (by decide +kernel))
theorem lab__Lscc_rt_alloc_tcb_ok : (_root_.Executable.labels st0.exe).label ".Lscc_rt_alloc_tcb.ok" = Int64.ofNat 4199284 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)
theorem lab_scc_rt_pinned : (_root_.Executable.labels st0.exe).label "scc_rt_pinned" = Int64.ofNat 71859008 :=
  Scc.Cert.Rt.X64.label_threadAt_of_sym (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Scc.Cert.Rt.X64.ne_label_of_codeLabel (lo := Λe.code.lo) (by decide +kernel))
theorem lab_scc_rt_thread_init : (_root_.Executable.labels st0.exe).label "scc_rt_thread_init" = Int64.ofNat 4199582 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)
theorem lab_scc_rt_stack_take : (_root_.Executable.labels st0.exe).label "scc_rt_stack_take" = Int64.ofNat 4199732 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)
theorem lab__Lscc_rt_stack_take_cls5 : (_root_.Executable.labels st0.exe).label ".Lscc_rt_stack_take.cls5" = Int64.ofNat 4199793 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)
theorem lab__Lscc_rt_stack_take_clsnext6 : (_root_.Executable.labels st0.exe).label ".Lscc_rt_stack_take.clsnext6" = Int64.ofNat 4199808 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)
theorem lab__Lscc_rt_stack_take_clsdone7 : (_root_.Executable.labels st0.exe).label ".Lscc_rt_stack_take.clsdone7" = Int64.ofNat 4199897 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)
theorem lab_scc_rt_stack_free_n : (_root_.Executable.labels st0.exe).label "scc_rt_stack_free_n" = Int64.ofNat 4225808 :=
  Scc.Cert.Rt.X64.label_threadAt_of_sym (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Scc.Cert.Rt.X64.ne_label_of_codeLabel (lo := Λe.code.lo) (by decide +kernel))
theorem lab_scc_rt_stack_free : (_root_.Executable.labels st0.exe).label "scc_rt_stack_free" = Int64.ofNat 4225912 :=
  Scc.Cert.Rt.X64.label_threadAt_of_sym (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Scc.Cert.Rt.X64.ne_label_of_codeLabel (lo := Λe.code.lo) (by decide +kernel))
theorem lab_scc_rt_stack_lock : (_root_.Executable.labels st0.exe).label "scc_rt_stack_lock" = Int64.ofNat 4225800 :=
  Scc.Cert.Rt.X64.label_threadAt_of_sym (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Scc.Cert.Rt.X64.ne_label_of_codeLabel (lo := Λe.code.lo) (by decide +kernel))
theorem lab__Lscc_rt_stack_take_spin14 : (_root_.Executable.labels st0.exe).label ".Lscc_rt_stack_take.spin14" = Int64.ofNat 4199962 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)
theorem lab__Lscc_rt_stack_take_locked15 : (_root_.Executable.labels st0.exe).label ".Lscc_rt_stack_take.locked15" = Int64.ofNat 4199998 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)
theorem lab__Lscc_rt_stack_take_bump : (_root_.Executable.labels st0.exe).label ".Lscc_rt_stack_take.bump" = Int64.ofNat 4200139 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)
theorem lab_scc_rt_stack_next : (_root_.Executable.labels st0.exe).label "scc_rt_stack_next" = Int64.ofNat 4225792 :=
  Scc.Cert.Rt.X64.label_threadAt_of_sym (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Scc.Cert.Rt.X64.ne_label_of_codeLabel (lo := Λe.code.lo) (by decide +kernel))
theorem lab__Lscc_rt_stack_take_full : (_root_.Executable.labels st0.exe).label ".Lscc_rt_stack_take.full" = Int64.ofNat 4200249 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)
theorem lab__Lscc_rt_stack_take_ok : (_root_.Executable.labels st0.exe).label ".Lscc_rt_stack_take.ok" = Int64.ofNat 4200263 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)
theorem lab_scc_rt_stacks : (_root_.Executable.labels st0.exe).label "scc_rt_stacks" = Int64.ofNat 72022848 :=
  Scc.Cert.Rt.X64.label_threadAt_of_sym (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Scc.Cert.Rt.X64.ne_label_of_codeLabel (lo := Λe.code.lo) (by decide +kernel))
theorem lab__Lscc_rt_stack_take_taken : (_root_.Executable.labels st0.exe).label ".Lscc_rt_stack_take.taken" = Int64.ofNat 4200303 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)
theorem lab_scc_rt_main : (_root_.Executable.labels st0.exe).label "scc_rt_main" = Int64.ofNat 4198540 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)
theorem lab__Lscc_rt_main_stk : (_root_.Executable.labels st0.exe).label ".Lscc_rt_main.stk" = Int64.ofNat 4198638 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)
theorem lab_wc_rodata : (_root_.Executable.labels st0.exe).label "wc_rodata" = Int64.ofNat 4203169 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)
theorem lab__Lwc_rodata_stk : (_root_.Executable.labels st0.exe).label ".Lwc_rodata.stk" = Int64.ofNat 4203314 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)
theorem lab_scc_rt_alloc : (_root_.Executable.labels st0.exe).label "scc_rt_alloc" = Int64.ofNat 4198666 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)
theorem lab__Lscc_rt_alloc_full : (_root_.Executable.labels st0.exe).label ".Lscc_rt_alloc.full" = Int64.ofNat 4198788 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)
theorem lab__Lscc_rt_alloc_cnt : (_root_.Executable.labels st0.exe).label ".Lscc_rt_alloc.cnt" = Int64.ofNat 4198707 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)
theorem lab_scc_rt_heap_use : (_root_.Executable.labels st0.exe).label "scc_rt_heap_use" = Int64.ofNat 4225760 :=
  Scc.Cert.Rt.X64.label_threadAt_of_sym (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Scc.Cert.Rt.X64.ne_label_of_codeLabel (lo := Λe.code.lo) (by decide +kernel))

/-- A mapped slot, through an equation of loads. -/
theorem ex_eq {m m' : DataMem} {a b : BitVec 64} (h : Mem.loadInt m a 8 = Mem.loadInt m' b 8)
    (hb : ∃ j, Mem.loadInt m' b 8 = some j) : ∃ j, Mem.loadInt m a 8 = some j := by
  rw [h]; exact hb

/-! ## States -/

abbrev Lnil : List (BitVec 64 × BitVec 64) := []

abbrev F_000000 : StatusFlags := ⟨false, false, false, false, false, false⟩
abbrev F_010100 : StatusFlags := ⟨false, true, false, true, false, false⟩
abbrev F_010000 : StatusFlags := ⟨false, true, false, false, false, false⟩
abbrev F_100010 : StatusFlags := ⟨true, false, false, false, true, false⟩
abbrev F_110010 : StatusFlags := ⟨true, true, false, false, true, false⟩

abbrev R0 : Reg64s := { rsp := 140737488351232 }
abbrev R3 : Reg64s := { rsp := 140737488351224 }
abbrev R4 : Reg64s := { rsp := 140737488351216 }
abbrev R5 : Reg64s := { rsp := 140737488351216, rbp := 140737488351216 }
abbrev R6 : Reg64s := { rsp := 140737488351184, rbp := 140737488351216 }
abbrev R7 : Reg64s := { rax := 4225552, rsp := 140737488351184, rbp := 140737488351216 }
abbrev R9 : Reg64s := { rax := 4225552, rdi := 13, rsp := 140737488351184, rbp := 140737488351216 }
abbrev R10 : Reg64s := { rax := 4225552, rsi := 4225552, rdi := 13, rsp := 140737488351184, rbp := 140737488351216 }
abbrev R12 : Reg64s := { rax := 4225552, rsi := 4225552, rdi := 13, rsp := 140737488351184, rbp := 140737488351216, r10 := 8 }
abbrev R16 : Reg64s := { rcx := 4198464, rsi := 4225552, rdi := 3331, rsp := 140737488351184, rbp := 140737488351216, r10 := 8 }
abbrev R17 : Reg64s := { rcx := 4198464, rsi := 1, rdi := 3331, rsp := 140737488351184, rbp := 140737488351216, r10 := 8 }
abbrev R18 : Reg64s := { rcx := 4198464, rsi := 1, rdi := 3331, rsp := 140737488351176, rbp := 140737488351216, r10 := 8 }
abbrev R19 : Reg64s := { rcx := 4198464, rsi := 1, rdi := 3331, rsp := 140737488351168, rbp := 140737488351216, r10 := 8 }
abbrev R20 : Reg64s := { rcx := 4198464, rsi := 1, rdi := 3331, rsp := 140737488351168, rbp := 140737488351168, r10 := 8 }
abbrev R21 : Reg64s := { rcx := 4198464, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R24 : Reg64s := { rax := 1, rcx := 4198464, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R25 : Reg64s := { rax := 1, rcx := 268435456, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R29 : Reg64s := { rax := 3331, rcx := 268435456, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R30 : Reg64s := { rax := 3331, rcx := 8, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R31 : Reg64s := { rax := 13, rcx := 8, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R34 : Reg64s := { rax := 13, rcx := 16383, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev L2 : List (BitVec 64 × BitVec 64) := (140737488351224#64, 4198411#64) :: Lnil
abbrev L3 : List (BitVec 64 × BitVec 64) := (140737488351216#64, 0#64) :: L2
abbrev L7 : List (BitVec 64 × BitVec 64) := (140737488351208#64, 4225552#64) :: L3
abbrev L14 : List (BitVec 64 × BitVec 64) := (140737488351200#64, 0#64) :: L7
abbrev L17 : List (BitVec 64 × BitVec 64) := (140737488351176#64, 4198487#64) :: L14
abbrev L18 : List (BitVec 64 × BitVec 64) := (140737488351168#64, 140737488351216#64) :: L17
abbrev L21 : List (BitVec 64 × BitVec 64) := (140737488351160#64, 3331#64) :: L18
abbrev L22 : List (BitVec 64 × BitVec 64) := (140737488351152#64, 1#64) :: L21
abbrev L31 : List (BitVec 64 × BitVec 64) := (140737488351144#64, 13#64) :: L22
abbrev L35 : List (BitVec 64 × BitVec 64) := (140737488351136#64, 13#64) :: L31

/-! ## Steps -/

theorem s0 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R0 F_000000 (stores Ent Lnil) 4198400) M X (· = mk R0 F_010100 (stores Ent Lnil) 4198402) M X :=
  sgX hparse (cellM 2 4198400 rfl rfl (by decide +kernel) R0 F_000000 (stores Ent Lnil)) (by intro _ _ h; cases h) (by decide) (lx_xor32 (exec_xor_rr32_self (cellM 2 4198400 rfl rfl (by decide +kernel) R0 F_000000 (stores Ent Lnil))) (by decide) (by decide) rfl)

theorem s1 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R0 F_010100 (stores Ent Lnil) 4198402) M X (· = mk R0 F_010000 (stores Ent Lnil) 4198406) M X :=
  sgX hparse (cellM 3 4198402 rfl rfl (by decide +kernel) R0 F_010100 (stores Ent Lnil)) (by intro _ _ h; cases h) (by decide) (lx_logic (exec_and_ri (cellM 3 4198402 rfl rfl (by decide +kernel) R0 F_010100 (stores Ent Lnil))) (by decide) (by decide) rfl)

theorem s2 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R0 F_010000 (stores Ent Lnil) 4198406) M X (· = mk R3 F_010000 (stores Ent L2) 4198413) M X :=
  sgX hparse (cellM 4 4198406 rfl rfl (by decide +kernel) R0 F_010000 (stores Ent Lnil)) (by intro _ _ h; cases h) (by decide) (lf (hx_call (cellM 4 4198406 rfl rfl (by decide +kernel) R0 F_010000 (stores Ent Lnil)) lab_scc_rt_start (a := 140737488351224#64) (v := 4198411#64) (by decide) (ex_base (B := Ent) (L := Lnil) (b := 140737488351224#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) (by decide)))

theorem s3 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R3 F_010000 (stores Ent L2) 4198413) M X (· = mk R4 F_010000 (stores Ent L3) 4198414) M X :=
  sgX hparse (cellM 7 4198413 rfl rfl (by decide +kernel) R3 F_010000 (stores Ent L2)) (by intro _ _ h; cases h) (by decide) (lf (hx_push (cellM 7 4198413 rfl rfl (by decide +kernel) R3 F_010000 (stores Ent L2)) (a := 140737488351216#64) (v := 0#64) (by decide) (ex_base (B := Ent) (L := L2) (b := 140737488351216#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) (by decide) rfl))

theorem s4 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R4 F_010000 (stores Ent L3) 4198414) M X (· = mk R5 F_010000 (stores Ent L3) 4198417) M X :=
  sgX hparse (cellM 8 4198414 rfl rfl (by decide +kernel) R4 F_010000 (stores Ent L3)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 8 4198414 rfl rfl (by decide +kernel) R4 F_010000 (stores Ent L3)) (by decide) (by decide) rfl))

theorem s5 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R5 F_010000 (stores Ent L3) 4198417) M X (· = mk R6 F_000000 (stores Ent L3) 4198421) M X :=
  sgX hparse (cellM 9 4198417 rfl rfl (by decide +kernel) R5 F_010000 (stores Ent L3)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 9 4198417 rfl rfl (by decide +kernel) R5 F_010000 (stores Ent L3)) (by decide) (by decide) rfl))

theorem s6 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R6 F_000000 (stores Ent L3) 4198421) M X (· = mk R7 F_000000 (stores Ent L3) 4198428) M X :=
  sgX hparse (cellM 11 4198421 rfl rfl (by decide +kernel) R6 F_000000 (stores Ent L3)) (by intro _ _ h; cases h) (by decide) (lf (hx_leaRip (cellM 11 4198421 rfl rfl (by decide +kernel) R6 F_000000 (stores Ent L3)) lab_scc_rt_sigign (by decide) rfl))

theorem s7 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R7 F_000000 (stores Ent L3) 4198428) M X (· = mk R7 F_000000 (stores Ent L7) 4198432) M X :=
  sgX hparse (cellM 12 4198428 rfl rfl (by decide +kernel) R7 F_000000 (stores Ent L3)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 12 4198428 rfl rfl (by decide +kernel) R7 F_000000 (stores Ent L3)) (a := 140737488351208#64) (v := 4225552#64) (by decide) (ex_base (B := Ent) (L := L3) (b := 140737488351208#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s8 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R7 F_000000 (stores Ent L7) 4198432) M X (· = mk R9 F_000000 (stores Ent L7) 4198439) M X :=
  sgX hparse (cellM 13 4198432 rfl rfl (by decide +kernel) R7 F_000000 (stores Ent L7)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 13 4198432 rfl rfl (by decide +kernel) R7 F_000000 (stores Ent L7)) (by decide) (by decide) rfl))

theorem s9 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R9 F_000000 (stores Ent L7) 4198439) M X (· = mk R10 F_000000 (stores Ent L7) 4198443) M X :=
  sgX hparse (cellM 14 4198439 rfl rfl (by decide +kernel) R9 F_000000 (stores Ent L7)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 14 4198439 rfl rfl (by decide +kernel) R9 F_000000 (stores Ent L7)) (a := 140737488351208#64) (by decide) (loadInt_look (B := Ent) (L := L7) (b := 140737488351208#64) (v := 4225552#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s10 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R10 F_000000 (stores Ent L7) 4198443) M X (· = mk R10 F_000000 (stores Ent L7) 4198450) M X :=
  sgX hparse (cellM 15 4198443 rfl rfl (by decide +kernel) R10 F_000000 (stores Ent L7)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 15 4198443 rfl rfl (by decide +kernel) R10 F_000000 (stores Ent L7)) (by decide) (by decide) rfl))

theorem s11 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R10 F_000000 (stores Ent L7) 4198450) M X (· = mk R12 F_000000 (stores Ent L7) 4198457) M X :=
  sgX hparse (cellM 16 4198450 rfl rfl (by decide +kernel) R10 F_000000 (stores Ent L7)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 16 4198450 rfl rfl (by decide +kernel) R10 F_000000 (stores Ent L7)) (by decide) (by decide) rfl))

theorem s12 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R12 F_000000 (stores Ent L7) 4198457) M X (· = mk Rsig F_000000 (stores Ent L7) 4198462) M X :=
  sgX hparse (cellM 17 4198457 rfl rfl (by decide +kernel) R12 F_000000 (stores Ent L7)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 17 4198457 rfl rfl (by decide +kernel) R12 F_000000 (stores Ent L7)) (by decide) (by decide) rfl))

theorem s13 (_hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk Rsig F_000000 (stores Ent L7) 4198462) M X (· = mk Rsig' F_000000 (stores Ent L7) 4198464) M X :=
  sg_rtSigaction (stores Ent L7) M X

theorem s14 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk Rsig' F_000000 (stores Ent L7) 4198464) M X (· = mk Rsig' F_000000 (stores Ent L14) 4198468) M X :=
  sgX hparse (cellM 19 4198464 rfl rfl (by decide +kernel) Rsig' F_000000 (stores Ent L7)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 19 4198464 rfl rfl (by decide +kernel) Rsig' F_000000 (stores Ent L7)) (a := 140737488351200#64) (v := 0#64) (by decide) (ex_base (B := Ent) (L := L7) (b := 140737488351200#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s15 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk Rsig' F_000000 (stores Ent L14) 4198468) M X (· = mk R16 F_000000 (stores Ent L14) 4198475) M X :=
  sgX hparse (cellM 20 4198468 rfl rfl (by decide +kernel) Rsig' F_000000 (stores Ent L14)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 20 4198468 rfl rfl (by decide +kernel) Rsig' F_000000 (stores Ent L14)) (by decide) (by decide) rfl))

theorem s16 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R16 F_000000 (stores Ent L14) 4198475) M X (· = mk R17 F_000000 (stores Ent L14) 4198482) M X :=
  sgX hparse (cellM 21 4198475 rfl rfl (by decide +kernel) R16 F_000000 (stores Ent L14)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 21 4198475 rfl rfl (by decide +kernel) R16 F_000000 (stores Ent L14)) (by decide) (by decide) rfl))

theorem s17 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R17 F_000000 (stores Ent L14) 4198482) M X (· = mk R18 F_000000 (stores Ent L17) 4199029) M X :=
  sgX hparse (cellM 22 4198482 rfl rfl (by decide +kernel) R17 F_000000 (stores Ent L14)) (by intro _ _ h; cases h) (by decide) (lf (hx_call (cellM 22 4198482 rfl rfl (by decide +kernel) R17 F_000000 (stores Ent L14)) lab_scc_rt_alloc_tcb (a := 140737488351176#64) (v := 4198487#64) (by decide) (ex_base (B := Ent) (L := L14) (b := 140737488351176#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) (by decide)))

theorem s18 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R18 F_000000 (stores Ent L17) 4199029) M X (· = mk R19 F_000000 (stores Ent L18) 4199030) M X :=
  sgX hparse (cellM 184 4199029 rfl rfl (by decide +kernel) R18 F_000000 (stores Ent L17)) (by intro _ _ h; cases h) (by decide) (lf (hx_push (cellM 184 4199029 rfl rfl (by decide +kernel) R18 F_000000 (stores Ent L17)) (a := 140737488351168#64) (v := 140737488351216#64) (by decide) (ex_base (B := Ent) (L := L17) (b := 140737488351168#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) (by decide) rfl))

theorem s19 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R19 F_000000 (stores Ent L18) 4199030) M X (· = mk R20 F_000000 (stores Ent L18) 4199033) M X :=
  sgX hparse (cellM 185 4199030 rfl rfl (by decide +kernel) R19 F_000000 (stores Ent L18)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 185 4199030 rfl rfl (by decide +kernel) R19 F_000000 (stores Ent L18)) (by decide) (by decide) rfl))

theorem s20 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R20 F_000000 (stores Ent L18) 4199033) M X (· = mk R21 F_000000 (stores Ent L18) 4199040) M X :=
  sgX hparse (cellM 186 4199033 rfl rfl (by decide +kernel) R20 F_000000 (stores Ent L18)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 186 4199033 rfl rfl (by decide +kernel) R20 F_000000 (stores Ent L18)) (by decide) (by decide) rfl))

theorem s21 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R21 F_000000 (stores Ent L18) 4199040) M X (· = mk R21 F_000000 (stores Ent L21) 4199044) M X :=
  sgX hparse (cellM 187 4199040 rfl rfl (by decide +kernel) R21 F_000000 (stores Ent L18)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 187 4199040 rfl rfl (by decide +kernel) R21 F_000000 (stores Ent L18)) (a := 140737488351160#64) (v := 3331#64) (by decide) (ex_base (B := Ent) (L := L18) (b := 140737488351160#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s22 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R21 F_000000 (stores Ent L21) 4199044) M X (· = mk R21 F_000000 (stores Ent L22) 4199048) M X :=
  sgX hparse (cellM 188 4199044 rfl rfl (by decide +kernel) R21 F_000000 (stores Ent L21)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 188 4199044 rfl rfl (by decide +kernel) R21 F_000000 (stores Ent L21)) (a := 140737488351152#64) (v := 1#64) (by decide) (ex_base (B := Ent) (L := L21) (b := 140737488351152#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s23 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R21 F_000000 (stores Ent L22) 4199048) M X (· = mk R24 F_000000 (stores Ent L22) 4199052) M X :=
  sgX hparse (cellM 190 4199048 rfl rfl (by decide +kernel) R21 F_000000 (stores Ent L22)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 190 4199048 rfl rfl (by decide +kernel) R21 F_000000 (stores Ent L22)) (a := 140737488351152#64) (by decide) (loadInt_look (B := Ent) (L := L22) (b := 140737488351152#64) (v := 1#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s24 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R24 F_000000 (stores Ent L22) 4199052) M X (· = mk R25 F_000000 (stores Ent L22) 4199059) M X :=
  sgX hparse (cellM 191 4199052 rfl rfl (by decide +kernel) R24 F_000000 (stores Ent L22)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 191 4199052 rfl rfl (by decide +kernel) R24 F_000000 (stores Ent L22)) (by decide) (by decide) rfl))

theorem s25 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R25 F_000000 (stores Ent L22) 4199059) M X (· = mk R25 F_100010 (stores Ent L22) 4199062) M X :=
  sgX hparse (cellM 192 4199059 rfl rfl (by decide +kernel) R25 F_000000 (stores Ent L22)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 192 4199059 rfl rfl (by decide +kernel) R25 F_000000 (stores Ent L22)) (by decide) (by decide) rfl))

theorem s26 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R25 F_100010 (stores Ent L22) 4199062) M X (· = mk R25 F_100010 (stores Ent L22) 4199068) M X :=
  sgX hparse (cellM 193 4199062 rfl rfl (by decide +kernel) R25 F_100010 (stores Ent L22)) (by intro _ _ h; cases h) (by decide) (lf (hx_jccN (cellM 193 4199062 rfl rfl (by decide +kernel) R25 F_100010 (stores Ent L22)) (by decide) rfl))

theorem s27 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R25 F_100010 (stores Ent L22) 4199068) M X (· = mk R25 F_100010 (stores Ent L22) 4199070) M X :=
  sgX hparse (cellM 194 4199068 rfl rfl (by decide +kernel) R25 F_100010 (stores Ent L22)) (by intro _ _ h; cases h) (by decide) (lf (hx_jmp (cellM 194 4199068 rfl rfl (by decide +kernel) R25 F_100010 (stores Ent L22)) lab__Lscc_rt_alloc_tcb_len))

theorem s28 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R25 F_100010 (stores Ent L22) 4199070) M X (· = mk R29 F_100010 (stores Ent L22) 4199074) M X :=
  sgX hparse (cellM 196 4199070 rfl rfl (by decide +kernel) R25 F_100010 (stores Ent L22)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 196 4199070 rfl rfl (by decide +kernel) R25 F_100010 (stores Ent L22)) (a := 140737488351160#64) (by decide) (loadInt_look (B := Ent) (L := L22) (b := 140737488351160#64) (v := 3331#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s29 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R29 F_100010 (stores Ent L22) 4199074) M X (· = mk R30 F_100010 (stores Ent L22) 4199081) M X :=
  sgX hparse (cellM 197 4199074 rfl rfl (by decide +kernel) R29 F_100010 (stores Ent L22)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 197 4199074 rfl rfl (by decide +kernel) R29 F_100010 (stores Ent L22)) (by decide) (by decide) rfl))

theorem s30 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R30 F_100010 (stores Ent L22) 4199081) M X (· = mk R31 F_000000 (stores Ent L22) 4199084) M X :=
  sgX hparse (cellM 198 4199081 rfl rfl (by decide +kernel) R30 F_100010 (stores Ent L22)) (by intro _ _ h; cases h) (by decide) (lx_shr (cellM 198 4199081 rfl rfl (by decide +kernel) R30 F_100010 (stores Ent L22)) (by decide) (by decide) (by decide) (by decide) rfl)

theorem s31 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R31 F_000000 (stores Ent L22) 4199084) M X (· = mk R31 F_000000 (stores Ent L31) 4199088) M X :=
  sgX hparse (cellM 199 4199084 rfl rfl (by decide +kernel) R31 F_000000 (stores Ent L22)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 199 4199084 rfl rfl (by decide +kernel) R31 F_000000 (stores Ent L22)) (a := 140737488351144#64) (v := 13#64) (by decide) (ex_base (B := Ent) (L := L22) (b := 140737488351144#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s32 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R31 F_000000 (stores Ent L31) 4199088) M X (· = mk R31 F_000000 (stores Ent L31) 4199092) M X :=
  sgX hparse (cellM 200 4199088 rfl rfl (by decide +kernel) R31 F_000000 (stores Ent L31)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 200 4199088 rfl rfl (by decide +kernel) R31 F_000000 (stores Ent L31)) (a := 140737488351144#64) (by decide) (loadInt_look (B := Ent) (L := L31) (b := 140737488351144#64) (v := 13#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s33 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R31 F_000000 (stores Ent L31) 4199092) M X (· = mk R34 F_000000 (stores Ent L31) 4199099) M X :=
  sgX hparse (cellM 201 4199092 rfl rfl (by decide +kernel) R31 F_000000 (stores Ent L31)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 201 4199092 rfl rfl (by decide +kernel) R31 F_000000 (stores Ent L31)) (by decide) (by decide) rfl))

theorem s34 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R34 F_000000 (stores Ent L31) 4199099) M X (· = mk R34 F_000000 (stores Ent L31) 4199102) M X :=
  sgX hparse (cellM 202 4199099 rfl rfl (by decide +kernel) R34 F_000000 (stores Ent L31)) (by intro _ _ h; cases h) (by decide) (lx_logic (exec_and_rr (cellM 202 4199099 rfl rfl (by decide +kernel) R34 F_000000 (stores Ent L31))) (by decide) (by decide) rfl)

theorem s35 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R34 F_000000 (stores Ent L31) 4199102) M X (· = mk R34 F_000000 (stores Ent L35) 4199106) M X :=
  sgX hparse (cellM 203 4199102 rfl rfl (by decide +kernel) R34 F_000000 (stores Ent L31)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 203 4199102 rfl rfl (by decide +kernel) R34 F_000000 (stores Ent L31)) (a := 140737488351136#64) (v := 13#64) (by decide) (ex_base (B := Ent) (L := L31) (b := 140737488351136#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

/-- **Steps 0 … 35.** -/
theorem c1 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R0 F_000000 (stores Ent Lnil) 4198400) M X (· = mk R34 F_000000 (stores Ent L35) 4199106) M X :=
  SegP.trans (s0 hparse) <|
  SegP.trans (s1 hparse) <|
  SegP.trans (s2 hparse) <|
  SegP.trans (s3 hparse) <|
  SegP.trans (s4 hparse) <|
  SegP.trans (s5 hparse) <|
  SegP.trans (s6 hparse) <|
  SegP.trans (s7 hparse) <|
  SegP.trans (s8 hparse) <|
  SegP.trans (s9 hparse) <|
  SegP.trans (s10 hparse) <|
  SegP.trans (s11 hparse) <|
  SegP.trans (s12 hparse) <|
  SegP.trans (s13 hparse) <|
  SegP.trans (s14 hparse) <|
  SegP.trans (s15 hparse) <|
  SegP.trans (s16 hparse) <|
  SegP.trans (s17 hparse) <|
  SegP.trans (s18 hparse) <|
  SegP.trans (s19 hparse) <|
  SegP.trans (s20 hparse) <|
  SegP.trans (s21 hparse) <|
  SegP.trans (s22 hparse) <|
  SegP.trans (s23 hparse) <|
  SegP.trans (s24 hparse) <|
  SegP.trans (s25 hparse) <|
  SegP.trans (s26 hparse) <|
  SegP.trans (s27 hparse) <|
  SegP.trans (s28 hparse) <|
  SegP.trans (s29 hparse) <|
  SegP.trans (s30 hparse) <|
  SegP.trans (s31 hparse) <|
  SegP.trans (s32 hparse) <|
  SegP.trans (s33 hparse) <|
  SegP.trans (s34 hparse) <|
  (s35 hparse)

/-- info: 'Spike.Test.HelloRootL0XClosed.c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.c1

end Spike.Test.HelloRootL0XClosed
