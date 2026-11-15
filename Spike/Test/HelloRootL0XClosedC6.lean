/-
**`hello.w` on x86-64, the closed run, chunk 6**: steps 180 … 215 of
thread 0 from the load (`HelloRootL0XClosedStep`), one `SegP` segment per
instruction, composed into `c6`.

Generated from the reference run of the program (the states before every
step: registers `R…`, flags `F_…` (`cf pf af zf sf of`), private memory the
entry stack after the 8-byte stores `L…` (after the take: the taken copy
`B2` after `N…`), shared memory the write chain `M…`). Every step is proved,
not trusted: the generator only chooses the lemma and the witnesses.
-/
import Spike.Test.HelloRootL0XClosedC5

namespace Spike.Test.HelloRootL0XClosed

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Test.HelloLinkedX64 (Λe)
open Spike.Lib.Fwd

set_option maxRecDepth 100000

abbrev R181 : Reg64s := { rax := 4225792, rcx := 4225792, rsi := 1, rdi := 16384, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
abbrev R182 : Reg64s := { rax := 16384, rcx := 4225792, rsi := 1, rdi := 16384, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
abbrev R183 : Reg64s := { rcx := 4225792, rsi := 1, rdi := 16384, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
abbrev R186 : Reg64s := { rcx := 16384, rsi := 1, rdi := 16384, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
abbrev R190 : Reg64s := { rax := 16384, rcx := 536870912, rsi := 1, rdi := 16384, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
abbrev R194 : Reg64s := { rax := 72022848, rcx := 536870912, rsi := 1, rdi := 16384, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
abbrev R197 : Reg64s := { rax := 72022848, rsi := 1, rdi := 16384, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
abbrev R201 : Reg64s := { rax := 72022848, rsi := 1, rdi := 72022848, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
abbrev R205 : Reg64s := { rax := 72022848, rsi := 16384, rdi := 72022848, rsp := 140737488351120, rbp := 140737488351120, r10 := 8 }
abbrev R206 : Reg64s := { rax := 72022848, rsi := 16384, rdi := 72022848, rsp := 140737488351128, rbp := 140737488351168, r10 := 8 }
abbrev R207 : Reg64s := { rax := 72022848, rsi := 16384, rdi := 72022848, rsp := 140737488351136, rbp := 140737488351168, r10 := 8 }
abbrev R210 : Reg64s := { rax := 72022848, rcx := 4096, rsi := 16384, rdi := 72022848, rsp := 140737488351136, rbp := 140737488351168, r10 := 8 }
abbrev R211 : Reg64s := { rax := 72026944, rcx := 4096, rsi := 16384, rdi := 72022848, rsp := 140737488351136, rbp := 140737488351168, r10 := 8 }
abbrev R214 : Reg64s := { rax := 72022848, rcx := 16384, rsi := 16384, rdi := 72022848, rsp := 140737488351136, rbp := 140737488351168, r10 := 8 }
abbrev R215 : Reg64s := { rax := 72039232, rcx := 16384, rsi := 16384, rdi := 72022848, rsp := 140737488351136, rbp := 140737488351168, r10 := 8 }
abbrev L183 : List (BitVec 64 × BitVec 64) := (140737488350952#64, 0#64) :: L179
abbrev L187 : List (BitVec 64 × BitVec 64) := (140737488350944#64, 16384#64) :: L183
abbrev L194 : List (BitVec 64 × BitVec 64) := (140737488350936#64, 72022848#64) :: L187
abbrev L198 : List (BitVec 64 × BitVec 64) := (140737488350984#64, 72022848#64) :: L194
abbrev Llast : List (BitVec 64 × BitVec 64) := L198
/-- The private memory after the take. -/
abbrev B2 : DataMem := Kernel.copyRange ∅ (stores Ent Llast) rTk
abbrev Nnil : List (BitVec 64 × BitVec 64) := []
abbrev N207 : List (BitVec 64 × BitVec 64) := (140737488351152#64, 72022848#64) :: Nnil
abbrev N211 : List (BitVec 64 × BitVec 64) := (140737488351144#64, 72026944#64) :: N207
abbrev N215 : List (BitVec 64 × BitVec 64) := (140737488351136#64, 72039232#64) :: N211
abbrev M182 : Memory := (M177.append { loc := ⟨4225792#64, 8⟩, val := 16384#128, tid := 0 }).1

/-! ## Steps -/

theorem s180 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R179 F_010100 (stores Ent L179) 4200184) M X (· = mk R181 F_010100 (stores Ent L179) 4200191) M X :=
  sgX hparse (cellM 474 4200184 rfl rfl (by decide +kernel) R179 F_010100 (stores Ent L179)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 474 4200184 rfl rfl (by decide +kernel) R179 F_010100 (stores Ent L179)) (a := 140737488350960#64) (by decide) (loadInt_look (B := Ent) (L := L179) (b := 140737488350960#64) (v := 4225792#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s181 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R181 F_010100 (stores Ent L179) 4200191) M X (· = mk R182 F_010100 (stores Ent L179) 4200195) M X :=
  sgX hparse (cellM 475 4200191 rfl rfl (by decide +kernel) R181 F_010100 (stores Ent L179)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 475 4200191 rfl rfl (by decide +kernel) R181 F_010100 (stores Ent L179)) (a := 140737488351112#64) (by decide) (loadInt_look (B := Ent) (L := L179) (b := 140737488351112#64) (v := 16384#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s182 (hparse : Parse) {X : Kernel.KState} :
    Sg (· = mk R182 F_010100 (stores Ent L179) 4200195) M177 X (· = mk R183 F_010000 (stores Ent L179) 4200200) M182 X :=
  sgXaddSh hparse (cellM 476 4200195 rfl rfl (by decide +kernel) R182 F_010100 (stores Ent L179)) (by decide) (a := 4225792#64) ((eaddr_reg_disp _ _ _ _).trans (by decide)) ((loadInt_look_none (B := Ent) (L := L179) (b := 4225792#64) (by decide) (by decide) (by decide)).trans (ent_none (by decide))) (old := 0#128) (nv := 16384#128) (by decide) (by decide) (by decide) (by decide) rfl

theorem s183 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R183 F_010000 (stores Ent L179) 4200200) M X (· = mk R183 F_010000 (stores Ent L183) 4200207) M X :=
  sgX hparse (cellM 477 4200200 rfl rfl (by decide +kernel) R183 F_010000 (stores Ent L179)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 477 4200200 rfl rfl (by decide +kernel) R183 F_010000 (stores Ent L179)) (a := 140737488350952#64) (v := 0#64) (by decide) (ex_base (B := Ent) (L := L179) (b := 140737488350952#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s184 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R183 F_010000 (stores Ent L183) 4200207) M X (· = mk R183 F_010000 (stores Ent L183) 4200214) M X :=
  sgX hparse (cellM 478 4200207 rfl rfl (by decide +kernel) R183 F_010000 (stores Ent L183)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 478 4200207 rfl rfl (by decide +kernel) R183 F_010000 (stores Ent L183)) (a := 140737488350952#64) (by decide) (loadInt_look (B := Ent) (L := L183) (b := 140737488350952#64) (v := 0#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s185 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R183 F_010000 (stores Ent L183) 4200214) M X (· = mk R186 F_010000 (stores Ent L183) 4200218) M X :=
  sgX hparse (cellM 479 4200214 rfl rfl (by decide +kernel) R183 F_010000 (stores Ent L183)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 479 4200214 rfl rfl (by decide +kernel) R183 F_010000 (stores Ent L183)) (a := 140737488351112#64) (by decide) (loadInt_look (B := Ent) (L := L183) (b := 140737488351112#64) (v := 16384#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s186 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R186 F_010000 (stores Ent L183) 4200218) M X (· = mk R140 F_010000 (stores Ent L183) 4200221) M X :=
  sgX hparse (cellM 480 4200218 rfl rfl (by decide +kernel) R186 F_010000 (stores Ent L183)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 480 4200218 rfl rfl (by decide +kernel) R186 F_010000 (stores Ent L183)) (by decide) (by decide) rfl))

theorem s187 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R140 F_010000 (stores Ent L183) 4200221) M X (· = mk R140 F_010000 (stores Ent L187) 4200228) M X :=
  sgX hparse (cellM 481 4200221 rfl rfl (by decide +kernel) R140 F_010000 (stores Ent L183)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 481 4200221 rfl rfl (by decide +kernel) R140 F_010000 (stores Ent L183)) (a := 140737488350944#64) (v := 16384#64) (by decide) (ex_base (B := Ent) (L := L183) (b := 140737488350944#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s188 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R140 F_010000 (stores Ent L187) 4200228) M X (· = mk R140 F_010000 (stores Ent L187) 4200235) M X :=
  sgX hparse (cellM 482 4200228 rfl rfl (by decide +kernel) R140 F_010000 (stores Ent L187)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 482 4200228 rfl rfl (by decide +kernel) R140 F_010000 (stores Ent L187)) (a := 140737488350944#64) (by decide) (loadInt_look (B := Ent) (L := L187) (b := 140737488350944#64) (v := 16384#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s189 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R140 F_010000 (stores Ent L187) 4200235) M X (· = mk R190 F_010000 (stores Ent L187) 4200242) M X :=
  sgX hparse (cellM 483 4200235 rfl rfl (by decide +kernel) R140 F_010000 (stores Ent L187)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 483 4200235 rfl rfl (by decide +kernel) R140 F_010000 (stores Ent L187)) (by decide) (by decide) rfl))

theorem s190 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R190 F_010000 (stores Ent L187) 4200242) M X (· = mk R190 F_110010 (stores Ent L187) 4200245) M X :=
  sgX hparse (cellM 484 4200242 rfl rfl (by decide +kernel) R190 F_010000 (stores Ent L187)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 484 4200242 rfl rfl (by decide +kernel) R190 F_010000 (stores Ent L187)) (by decide) (by decide) rfl))

theorem s191 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R190 F_110010 (stores Ent L187) 4200245) M X (· = mk R190 F_110010 (stores Ent L187) 4200247) M X :=
  sgX hparse (cellM 485 4200245 rfl rfl (by decide +kernel) R190 F_110010 (stores Ent L187)) (by intro _ _ h; cases h) (by decide) (lf (hx_jccN (cellM 485 4200245 rfl rfl (by decide +kernel) R190 F_110010 (stores Ent L187)) (by decide) rfl))

theorem s192 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R190 F_110010 (stores Ent L187) 4200247) M X (· = mk R190 F_110010 (stores Ent L187) 4200263) M X :=
  sgX hparse (cellM 486 4200247 rfl rfl (by decide +kernel) R190 F_110010 (stores Ent L187)) (by intro _ _ h; cases h) (by decide) (lf (hx_jmp (cellM 486 4200247 rfl rfl (by decide +kernel) R190 F_110010 (stores Ent L187)) lab__Lscc_rt_stack_take_ok))

theorem s193 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R190 F_110010 (stores Ent L187) 4200263) M X (· = mk R194 F_110010 (stores Ent L187) 4200270) M X :=
  sgX hparse (cellM 493 4200263 rfl rfl (by decide +kernel) R190 F_110010 (stores Ent L187)) (by intro _ _ h; cases h) (by decide) (lf (hx_leaRip (cellM 493 4200263 rfl rfl (by decide +kernel) R190 F_110010 (stores Ent L187)) lab_scc_rt_stacks (by decide) rfl))

theorem s194 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R194 F_110010 (stores Ent L187) 4200270) M X (· = mk R194 F_110010 (stores Ent L194) 4200277) M X :=
  sgX hparse (cellM 494 4200270 rfl rfl (by decide +kernel) R194 F_110010 (stores Ent L187)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 494 4200270 rfl rfl (by decide +kernel) R194 F_110010 (stores Ent L187)) (a := 140737488350936#64) (v := 72022848#64) (by decide) (ex_base (B := Ent) (L := L187) (b := 140737488350936#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s195 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R194 F_110010 (stores Ent L194) 4200277) M X (· = mk R194 F_110010 (stores Ent L194) 4200284) M X :=
  sgX hparse (cellM 495 4200277 rfl rfl (by decide +kernel) R194 F_110010 (stores Ent L194)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 495 4200277 rfl rfl (by decide +kernel) R194 F_110010 (stores Ent L194)) (a := 140737488350936#64) (by decide) (loadInt_look (B := Ent) (L := L194) (b := 140737488350936#64) (v := 72022848#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s196 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R194 F_110010 (stores Ent L194) 4200284) M X (· = mk R197 F_110010 (stores Ent L194) 4200291) M X :=
  sgX hparse (cellM 496 4200284 rfl rfl (by decide +kernel) R194 F_110010 (stores Ent L194)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 496 4200284 rfl rfl (by decide +kernel) R194 F_110010 (stores Ent L194)) (a := 140737488350952#64) (by decide) (loadInt_look (B := Ent) (L := L194) (b := 140737488350952#64) (v := 0#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s197 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R197 F_110010 (stores Ent L194) 4200291) M X (· = mk R197 F_000000 (stores Ent L194) 4200294) M X :=
  sgX hparse (cellM 497 4200291 rfl rfl (by decide +kernel) R197 F_110010 (stores Ent L194)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 497 4200291 rfl rfl (by decide +kernel) R197 F_110010 (stores Ent L194)) (by decide) (by decide) rfl))

theorem s198 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R197 F_000000 (stores Ent L194) 4200294) M X (· = mk R197 F_000000 (stores Ent L198) 4200301) M X :=
  sgX hparse (cellM 498 4200294 rfl rfl (by decide +kernel) R197 F_000000 (stores Ent L194)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 498 4200294 rfl rfl (by decide +kernel) R197 F_000000 (stores Ent L194)) (a := 140737488350984#64) (v := 72022848#64) (by decide) (ex_base (B := Ent) (L := L194) (b := 140737488350984#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s199 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R197 F_000000 (stores Ent L198) 4200301) M X (· = mk R197 F_000000 (stores Ent L198) 4200303) M X :=
  sgX hparse (cellM 499 4200301 rfl rfl (by decide +kernel) R197 F_000000 (stores Ent L198)) (by intro _ _ h; cases h) (by decide) (lf (hx_jmp (cellM 499 4200301 rfl rfl (by decide +kernel) R197 F_000000 (stores Ent L198)) lab__Lscc_rt_stack_take_taken))

theorem s200 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R197 F_000000 (stores Ent L198) 4200303) M X (· = mk R201 F_000000 (stores Ent L198) 4200310) M X :=
  sgX hparse (cellM 501 4200303 rfl rfl (by decide +kernel) R197 F_000000 (stores Ent L198)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 501 4200303 rfl rfl (by decide +kernel) R197 F_000000 (stores Ent L198)) (a := 140737488350984#64) (by decide) (loadInt_look (B := Ent) (L := L198) (b := 140737488350984#64) (v := 72022848#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s201 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R201 F_000000 (stores Ent L198) 4200310) M X (· = mk Rtk F_000000 (stores Ent L198) 4200314) M X :=
  sgX hparse (cellM 502 4200310 rfl rfl (by decide +kernel) R201 F_000000 (stores Ent L198)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 502 4200310 rfl rfl (by decide +kernel) R201 F_000000 (stores Ent L198)) (a := 140737488351112#64) (by decide) (loadInt_look (B := Ent) (L := L198) (b := 140737488351112#64) (v := 16384#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s202 (hparse : Parse) :
    Sg (· = mk Rtk F_000000 (stores Ent L198) 4200314) M182 X0 (· = mk Rtk F_000000 (stores B2 Nnil) 4200315) M182 X1 :=
  sg_take hparse (stores Ent L198) M182 rfl (by decide +kernel)

theorem s203 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk Rtk F_000000 (stores B2 Nnil) 4200315) M X (· = mk Rtk F_000000 (stores B2 Nnil) 4200322) M X :=
  sgX hparse (cellM 505 4200315 rfl rfl (by decide +kernel) Rtk F_000000 (stores B2 Nnil)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 505 4200315 rfl rfl (by decide +kernel) Rtk F_000000 (stores B2 Nnil)) (a := 140737488350984#64) (by decide) ((loadInt_look_none (B := B2) (L := Nnil) (b := 140737488350984#64) (by decide) (by decide) (by decide)).trans ((copy_out (by decide) (by decide) (by decide)).trans (loadInt_look (B := Ent) (L := Llast) (b := 140737488350984#64) (v := 72022848#64) (by decide) (by decide) (by decide)))) (by decide) rfl))

theorem s204 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk Rtk F_000000 (stores B2 Nnil) 4200322) M X (· = mk R205 F_000000 (stores B2 Nnil) 4200325) M X :=
  sgX hparse (cellM 506 4200322 rfl rfl (by decide +kernel) Rtk F_000000 (stores B2 Nnil)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 506 4200322 rfl rfl (by decide +kernel) Rtk F_000000 (stores B2 Nnil)) (by decide) (by decide) rfl))

theorem s205 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R205 F_000000 (stores B2 Nnil) 4200325) M X (· = mk R206 F_000000 (stores B2 Nnil) 4200326) M X :=
  sgX hparse (cellM 507 4200325 rfl rfl (by decide +kernel) R205 F_000000 (stores B2 Nnil)) (by intro _ _ h; cases h) (by decide) (lf (hx_pop (cellM 507 4200325 rfl rfl (by decide +kernel) R205 F_000000 (stores B2 Nnil)) (a := 140737488351120#64) (by decide) ((loadInt_look_none (B := B2) (L := Nnil) (b := 140737488351120#64) (by decide) (by decide) (by decide)).trans ((copy_out (by decide) (by decide) (by decide)).trans (loadInt_look (B := Ent) (L := Llast) (b := 140737488351120#64) (v := 140737488351168#64) (by decide) (by decide) (by decide)))) (by decide) rfl))

theorem s206 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R206 F_000000 (stores B2 Nnil) 4200326) M X (· = mk R207 F_000000 (stores B2 Nnil) 4199606) M X :=
  sgX hparse (cellM 509 4200326 rfl rfl (by decide +kernel) R206 F_000000 (stores B2 Nnil)) (by intro _ _ h; cases h) (by decide) (lf (hx_ret (cellM 509 4200326 rfl rfl (by decide +kernel) R206 F_000000 (stores B2 Nnil)) (a := 140737488351128#64) (by decide) ((loadInt_look_none (B := B2) (L := Nnil) (b := 140737488351128#64) (by decide) (by decide) (by decide)).trans ((copy_out (by decide) (by decide) (by decide)).trans (loadInt_look (B := Ent) (L := Llast) (b := 140737488351128#64) (v := 4199606#64) (by decide) (by decide) (by decide)))) (by decide) (by decide)))

theorem s207 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R207 F_000000 (stores B2 Nnil) 4199606) M X (· = mk R207 F_000000 (stores B2 N207) 4199610) M X :=
  sgX hparse (cellM 331 4199606 rfl rfl (by decide +kernel) R207 F_000000 (stores B2 Nnil)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 331 4199606 rfl rfl (by decide +kernel) R207 F_000000 (stores B2 Nnil)) (a := 140737488351152#64) (v := 72022848#64) (by decide) (ex_eq ((loadInt_look_none (B := B2) (L := Nnil) (b := 140737488351152#64) (by decide) (by decide) (by decide)).trans (copy_out (by decide) (by decide) (by decide))) (ex_look (B := Ent) (L := Llast) (b := 140737488351152#64) (v := 1#64) (by decide) (by decide) (by decide))) (by decide) rfl))

theorem s208 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R207 F_000000 (stores B2 N207) 4199610) M X (· = mk R207 F_000000 (stores B2 N207) 4199614) M X :=
  sgX hparse (cellM 332 4199610 rfl rfl (by decide +kernel) R207 F_000000 (stores B2 N207)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 332 4199610 rfl rfl (by decide +kernel) R207 F_000000 (stores B2 N207)) (a := 140737488351152#64) (by decide) (loadInt_look (B := B2) (L := N207) (b := 140737488351152#64) (v := 72022848#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s209 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R207 F_000000 (stores B2 N207) 4199614) M X (· = mk R210 F_000000 (stores B2 N207) 4199621) M X :=
  sgX hparse (cellM 333 4199614 rfl rfl (by decide +kernel) R207 F_000000 (stores B2 N207)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 333 4199614 rfl rfl (by decide +kernel) R207 F_000000 (stores B2 N207)) (by decide) (by decide) rfl))

theorem s210 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R210 F_000000 (stores B2 N207) 4199621) M X (· = mk R211 F_000000 (stores B2 N207) 4199624) M X :=
  sgX hparse (cellM 334 4199621 rfl rfl (by decide +kernel) R210 F_000000 (stores B2 N207)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 334 4199621 rfl rfl (by decide +kernel) R210 F_000000 (stores B2 N207)) (by decide) (by decide) rfl))

theorem s211 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R211 F_000000 (stores B2 N207) 4199624) M X (· = mk R211 F_000000 (stores B2 N211) 4199628) M X :=
  sgX hparse (cellM 335 4199624 rfl rfl (by decide +kernel) R211 F_000000 (stores B2 N207)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 335 4199624 rfl rfl (by decide +kernel) R211 F_000000 (stores B2 N207)) (a := 140737488351144#64) (v := 72026944#64) (by decide) (ex_eq ((loadInt_look_none (B := B2) (L := N207) (b := 140737488351144#64) (by decide) (by decide) (by decide)).trans (copy_out (by decide) (by decide) (by decide))) (ex_look (B := Ent) (L := Llast) (b := 140737488351144#64) (v := 13#64) (by decide) (by decide) (by decide))) (by decide) rfl))

theorem s212 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R211 F_000000 (stores B2 N211) 4199628) M X (· = mk R210 F_000000 (stores B2 N211) 4199632) M X :=
  sgX hparse (cellM 336 4199628 rfl rfl (by decide +kernel) R211 F_000000 (stores B2 N211)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 336 4199628 rfl rfl (by decide +kernel) R211 F_000000 (stores B2 N211)) (a := 140737488351152#64) (by decide) (loadInt_look (B := B2) (L := N211) (b := 140737488351152#64) (v := 72022848#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s213 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R210 F_000000 (stores B2 N211) 4199632) M X (· = mk R214 F_000000 (stores B2 N211) 4199639) M X :=
  sgX hparse (cellM 337 4199632 rfl rfl (by decide +kernel) R210 F_000000 (stores B2 N211)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 337 4199632 rfl rfl (by decide +kernel) R210 F_000000 (stores B2 N211)) (by decide) (by decide) rfl))

theorem s214 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R214 F_000000 (stores B2 N211) 4199639) M X (· = mk R215 F_000000 (stores B2 N211) 4199642) M X :=
  sgX hparse (cellM 338 4199639 rfl rfl (by decide +kernel) R214 F_000000 (stores B2 N211)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 338 4199639 rfl rfl (by decide +kernel) R214 F_000000 (stores B2 N211)) (by decide) (by decide) rfl))

theorem s215 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R215 F_000000 (stores B2 N211) 4199642) M X (· = mk R215 F_000000 (stores B2 N215) 4199646) M X :=
  sgX hparse (cellM 339 4199642 rfl rfl (by decide +kernel) R215 F_000000 (stores B2 N211)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 339 4199642 rfl rfl (by decide +kernel) R215 F_000000 (stores B2 N211)) (a := 140737488351136#64) (v := 72039232#64) (by decide) (ex_eq ((loadInt_look_none (B := B2) (L := N211) (b := 140737488351136#64) (by decide) (by decide) (by decide)).trans (copy_out (by decide) (by decide) (by decide))) (ex_look (B := Ent) (L := Llast) (b := 140737488351136#64) (v := 13#64) (by decide) (by decide) (by decide))) (by decide) rfl))

/-- **Steps 180 … 215.** -/
theorem c6 (hparse : Parse) :
    Sg (· = mk R179 F_010100 (stores Ent L179) 4200184) M177 X0 (· = mk R215 F_000000 (stores B2 N215) 4199646) M182 X1 :=
  SegP.trans (s180 hparse) <|
  SegP.trans (s181 hparse) <|
  SegP.trans (s182 hparse) <|
  SegP.trans (s183 hparse) <|
  SegP.trans (s184 hparse) <|
  SegP.trans (s185 hparse) <|
  SegP.trans (s186 hparse) <|
  SegP.trans (s187 hparse) <|
  SegP.trans (s188 hparse) <|
  SegP.trans (s189 hparse) <|
  SegP.trans (s190 hparse) <|
  SegP.trans (s191 hparse) <|
  SegP.trans (s192 hparse) <|
  SegP.trans (s193 hparse) <|
  SegP.trans (s194 hparse) <|
  SegP.trans (s195 hparse) <|
  SegP.trans (s196 hparse) <|
  SegP.trans (s197 hparse) <|
  SegP.trans (s198 hparse) <|
  SegP.trans (s199 hparse) <|
  SegP.trans (s200 hparse) <|
  SegP.trans (s201 hparse) <|
  SegP.trans (s202 hparse) <|
  SegP.trans (s203 hparse) <|
  SegP.trans (s204 hparse) <|
  SegP.trans (s205 hparse) <|
  SegP.trans (s206 hparse) <|
  SegP.trans (s207 hparse) <|
  SegP.trans (s208 hparse) <|
  SegP.trans (s209 hparse) <|
  SegP.trans (s210 hparse) <|
  SegP.trans (s211 hparse) <|
  SegP.trans (s212 hparse) <|
  SegP.trans (s213 hparse) <|
  SegP.trans (s214 hparse) <|
  (s215 hparse)

/-- info: 'Spike.Test.HelloRootL0XClosed.c6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.c6

end Spike.Test.HelloRootL0XClosed
