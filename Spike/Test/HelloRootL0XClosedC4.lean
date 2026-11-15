/-
**`hello.w` on x86-64, the closed run, chunk 4**: steps 108 … 143 of
thread 0 from the load (`HelloRootL0XClosedStep`), one `SegP` segment per
instruction, composed into `c4`.

Generated from the reference run of the program (the states before every
step: registers `R…`, flags `F_…` (`cf pf af zf sf of`), private memory the
entry stack after the 8-byte stores `L…` (after the take: the taken copy
`B2` after `N…`), shared memory the write chain `M…`). Every step is proved,
not trusted: the generator only chooses the lemma and the witnesses.
-/
import Spike.Test.HelloRootL0XClosedC3

namespace Spike.Test.HelloRootL0XClosed

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Test.HelloLinkedX64 (Λe)
open Spike.Lib.Fwd

set_option maxRecDepth 100000

abbrev R110 : Reg64s := { rax := 71859008, rcx := 8, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R111 : Reg64s := { rax := 71859016, rcx := 8, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R114 : Reg64s := { rax := 71859016, rcx := 8, rsi := 1, rdi := 3331, rsp := 140737488351168, rbp := 140737488351168, r10 := 8 }
abbrev R115 : Reg64s := { rax := 71859016, rcx := 8, rsi := 1, rdi := 3331, rsp := 140737488351176, rbp := 140737488351216, r10 := 8 }
abbrev R116 : Reg64s := { rax := 71859016, rcx := 8, rsi := 1, rdi := 3331, rsp := 140737488351184, rbp := 140737488351216, r10 := 8 }
abbrev R118 : Reg64s := { rax := 71859016, rcx := 8, rsi := 1, rdi := 71859016, rsp := 140737488351184, rbp := 140737488351216, r10 := 8 }
abbrev R119 : Reg64s := { rax := 71859016, rcx := 8, rsi := 1, rdi := 71859016, rsp := 140737488351176, rbp := 140737488351216, r10 := 8 }
abbrev R120 : Reg64s := { rax := 71859016, rcx := 8, rsi := 1, rdi := 71859016, rsp := 140737488351168, rbp := 140737488351216, r10 := 8 }
abbrev R121 : Reg64s := { rax := 71859016, rcx := 8, rsi := 1, rdi := 71859016, rsp := 140737488351168, rbp := 140737488351168, r10 := 8 }
abbrev R122 : Reg64s := { rax := 71859016, rcx := 8, rsi := 1, rdi := 71859016, rsp := 140737488351136, rbp := 140737488351168, r10 := 8 }
abbrev R124 : Reg64s := { rax := 71859016, rcx := 8, rsi := 1, rdi := 16384, rsp := 140737488351136, rbp := 140737488351168, r10 := 8 }
abbrev R125 : Reg64s := { rax := 71859016, rcx := 8, rsi := 1, rdi := 16384, rsp := 140737488351128, rbp := 140737488351168, r10 := 8 }
abbrev R126 : Reg64s := { rax := 71859016, rcx := 8, rsi := 1, rdi := 16384, rsp := 140737488351120, rbp := 140737488351168, r10 := 8 }
abbrev R127 : Reg64s := { rax := 71859016, rcx := 8, rsi := 1, rdi := 16384, rsp := 140737488351120, rbp := 140737488351120, r10 := 8 }
abbrev R128 : Reg64s := { rax := 71859016, rcx := 8, rsi := 1, rdi := 16384, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
abbrev R130 : Reg64s := { rax := 16384, rcx := 8, rsi := 1, rdi := 16384, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
abbrev R132 : Reg64s := { rcx := 8, rsi := 1, rdi := 16384, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
abbrev R134 : Reg64s := { rax := 32768, rcx := 8, rsi := 1, rdi := 16384, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
abbrev R140 : Reg64s := { rax := 16384, rcx := 16384, rsi := 1, rdi := 16384, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
abbrev R144 : Reg64s := { rax := 4225808, rcx := 16384, rsi := 1, rdi := 16384, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
abbrev L111 : List (BitVec 64 × BitVec 64) := (140737488350992#64, 71859016#64) :: L107
abbrev L116 : List (BitVec 64 × BitVec 64) := (140737488351192#64, 71859016#64) :: L111
abbrev L118 : List (BitVec 64 × BitVec 64) := (140737488351176#64, 4198500#64) :: L116
abbrev L119 : List (BitVec 64 × BitVec 64) := (140737488351168#64, 140737488351216#64) :: L118
abbrev L122 : List (BitVec 64 × BitVec 64) := (140737488351160#64, 71859016#64) :: L119
abbrev L124 : List (BitVec 64 × BitVec 64) := (140737488351128#64, 4199606#64) :: L122
abbrev L125 : List (BitVec 64 × BitVec 64) := (140737488351120#64, 140737488351168#64) :: L124
abbrev L128 : List (BitVec 64 × BitVec 64) := (140737488351112#64, 16384#64) :: L125
abbrev L130 : List (BitVec 64 × BitVec 64) := (140737488351104#64, 16384#64) :: L128
abbrev L132 : List (BitVec 64 × BitVec 64) := (140737488351096#64, 0#64) :: L130
abbrev L134 : List (BitVec 64 × BitVec 64) := (140737488351088#64, 32768#64) :: L132
abbrev L136 : List (BitVec 64 × BitVec 64) := (140737488351080#64, 0#64) :: L134

/-! ## Steps -/

theorem s108 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R79 F_000000 (stores Ent L107) 4199448) M X (· = mk R79 F_000000 (stores Ent L107) 4199455) M X :=
  sgX hparse (cellM 282 4199448 rfl rfl (by decide +kernel) R79 F_000000 (stores Ent L107)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 282 4199448 rfl rfl (by decide +kernel) R79 F_000000 (stores Ent L107)) (a := 140737488351000#64) (by decide) (loadInt_look (B := Ent) (L := L107) (b := 140737488351000#64) (v := 71859008#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s109 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R79 F_000000 (stores Ent L107) 4199455) M X (· = mk R110 F_000000 (stores Ent L107) 4199462) M X :=
  sgX hparse (cellM 283 4199455 rfl rfl (by decide +kernel) R79 F_000000 (stores Ent L107)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 283 4199455 rfl rfl (by decide +kernel) R79 F_000000 (stores Ent L107)) (by decide) (by decide) rfl))

theorem s110 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R110 F_000000 (stores Ent L107) 4199462) M X (· = mk R111 F_010000 (stores Ent L107) 4199465) M X :=
  sgX hparse (cellM 284 4199462 rfl rfl (by decide +kernel) R110 F_000000 (stores Ent L107)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 284 4199462 rfl rfl (by decide +kernel) R110 F_000000 (stores Ent L107)) (by decide) (by decide) rfl))

theorem s111 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R111 F_010000 (stores Ent L107) 4199465) M X (· = mk R111 F_010000 (stores Ent L111) 4199472) M X :=
  sgX hparse (cellM 285 4199465 rfl rfl (by decide +kernel) R111 F_010000 (stores Ent L107)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 285 4199465 rfl rfl (by decide +kernel) R111 F_010000 (stores Ent L107)) (a := 140737488350992#64) (v := 71859016#64) (by decide) (ex_base (B := Ent) (L := L107) (b := 140737488350992#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s112 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R111 F_010000 (stores Ent L111) 4199472) M X (· = mk R111 F_010000 (stores Ent L111) 4199479) M X :=
  sgX hparse (cellM 286 4199472 rfl rfl (by decide +kernel) R111 F_010000 (stores Ent L111)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 286 4199472 rfl rfl (by decide +kernel) R111 F_010000 (stores Ent L111)) (a := 140737488350992#64) (by decide) (loadInt_look (B := Ent) (L := L111) (b := 140737488350992#64) (v := 71859016#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s113 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R111 F_010000 (stores Ent L111) 4199479) M X (· = mk R114 F_010000 (stores Ent L111) 4199482) M X :=
  sgX hparse (cellM 287 4199479 rfl rfl (by decide +kernel) R111 F_010000 (stores Ent L111)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 287 4199479 rfl rfl (by decide +kernel) R111 F_010000 (stores Ent L111)) (by decide) (by decide) rfl))

theorem s114 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R114 F_010000 (stores Ent L111) 4199482) M X (· = mk R115 F_010000 (stores Ent L111) 4199483) M X :=
  sgX hparse (cellM 288 4199482 rfl rfl (by decide +kernel) R114 F_010000 (stores Ent L111)) (by intro _ _ h; cases h) (by decide) (lf (hx_pop (cellM 288 4199482 rfl rfl (by decide +kernel) R114 F_010000 (stores Ent L111)) (a := 140737488351168#64) (by decide) (loadInt_look (B := Ent) (L := L111) (b := 140737488351168#64) (v := 140737488351216#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s115 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R115 F_010000 (stores Ent L111) 4199483) M X (· = mk R116 F_010000 (stores Ent L111) 4198487) M X :=
  sgX hparse (cellM 290 4199483 rfl rfl (by decide +kernel) R115 F_010000 (stores Ent L111)) (by intro _ _ h; cases h) (by decide) (lf (hx_ret (cellM 290 4199483 rfl rfl (by decide +kernel) R115 F_010000 (stores Ent L111)) (a := 140737488351176#64) (by decide) (loadInt_look (B := Ent) (L := L111) (b := 140737488351176#64) (v := 4198487#64) (by decide) (by decide) (by decide)) (by decide) (by decide)))

theorem s116 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R116 F_010000 (stores Ent L111) 4198487) M X (· = mk R116 F_010000 (stores Ent L116) 4198491) M X :=
  sgX hparse (cellM 24 4198487 rfl rfl (by decide +kernel) R116 F_010000 (stores Ent L111)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 24 4198487 rfl rfl (by decide +kernel) R116 F_010000 (stores Ent L111)) (a := 140737488351192#64) (v := 71859016#64) (by decide) (ex_base (B := Ent) (L := L111) (b := 140737488351192#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s117 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R116 F_010000 (stores Ent L116) 4198491) M X (· = mk R118 F_010000 (stores Ent L116) 4198495) M X :=
  sgX hparse (cellM 25 4198491 rfl rfl (by decide +kernel) R116 F_010000 (stores Ent L116)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 25 4198491 rfl rfl (by decide +kernel) R116 F_010000 (stores Ent L116)) (a := 140737488351192#64) (by decide) (loadInt_look (B := Ent) (L := L116) (b := 140737488351192#64) (v := 71859016#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s118 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R118 F_010000 (stores Ent L116) 4198495) M X (· = mk R119 F_010000 (stores Ent L118) 4199582) M X :=
  sgX hparse (cellM 26 4198495 rfl rfl (by decide +kernel) R118 F_010000 (stores Ent L116)) (by intro _ _ h; cases h) (by decide) (lf (hx_call (cellM 26 4198495 rfl rfl (by decide +kernel) R118 F_010000 (stores Ent L116)) lab_scc_rt_thread_init (a := 140737488351176#64) (v := 4198500#64) (by decide) (ex_look (B := Ent) (L := L116) (b := 140737488351176#64) (v := 4198487#64) (by decide) (by decide) (by decide)) (by decide) (by decide)))

theorem s119 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R119 F_010000 (stores Ent L118) 4199582) M X (· = mk R120 F_010000 (stores Ent L119) 4199583) M X :=
  sgX hparse (cellM 323 4199582 rfl rfl (by decide +kernel) R119 F_010000 (stores Ent L118)) (by intro _ _ h; cases h) (by decide) (lf (hx_push (cellM 323 4199582 rfl rfl (by decide +kernel) R119 F_010000 (stores Ent L118)) (a := 140737488351168#64) (v := 140737488351216#64) (by decide) (ex_look (B := Ent) (L := L118) (b := 140737488351168#64) (v := 140737488351216#64) (by decide) (by decide) (by decide)) (by decide) (by decide) rfl))

theorem s120 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R120 F_010000 (stores Ent L119) 4199583) M X (· = mk R121 F_010000 (stores Ent L119) 4199586) M X :=
  sgX hparse (cellM 324 4199583 rfl rfl (by decide +kernel) R120 F_010000 (stores Ent L119)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 324 4199583 rfl rfl (by decide +kernel) R120 F_010000 (stores Ent L119)) (by decide) (by decide) rfl))

theorem s121 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R121 F_010000 (stores Ent L119) 4199586) M X (· = mk R122 F_010000 (stores Ent L119) 4199590) M X :=
  sgX hparse (cellM 325 4199586 rfl rfl (by decide +kernel) R121 F_010000 (stores Ent L119)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 325 4199586 rfl rfl (by decide +kernel) R121 F_010000 (stores Ent L119)) (by decide) (by decide) rfl))

theorem s122 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R122 F_010000 (stores Ent L119) 4199590) M X (· = mk R122 F_010000 (stores Ent L122) 4199594) M X :=
  sgX hparse (cellM 326 4199590 rfl rfl (by decide +kernel) R122 F_010000 (stores Ent L119)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 326 4199590 rfl rfl (by decide +kernel) R122 F_010000 (stores Ent L119)) (a := 140737488351160#64) (v := 71859016#64) (by decide) (ex_look (B := Ent) (L := L119) (b := 140737488351160#64) (v := 3331#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s123 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R122 F_010000 (stores Ent L122) 4199594) M X (· = mk R124 F_010000 (stores Ent L122) 4199601) M X :=
  sgX hparse (cellM 328 4199594 rfl rfl (by decide +kernel) R122 F_010000 (stores Ent L122)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 328 4199594 rfl rfl (by decide +kernel) R122 F_010000 (stores Ent L122)) (by decide) (by decide) rfl))

theorem s124 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R124 F_010000 (stores Ent L122) 4199601) M X (· = mk R125 F_010000 (stores Ent L124) 4199732) M X :=
  sgX hparse (cellM 329 4199601 rfl rfl (by decide +kernel) R124 F_010000 (stores Ent L122)) (by intro _ _ h; cases h) (by decide) (lf (hx_call (cellM 329 4199601 rfl rfl (by decide +kernel) R124 F_010000 (stores Ent L122)) lab_scc_rt_stack_take (a := 140737488351128#64) (v := 4199606#64) (by decide) (ex_look (B := Ent) (L := L122) (b := 140737488351128#64) (v := 0#64) (by decide) (by decide) (by decide)) (by decide) (by decide)))

theorem s125 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R125 F_010000 (stores Ent L124) 4199732) M X (· = mk R126 F_010000 (stores Ent L125) 4199733) M X :=
  sgX hparse (cellM 364 4199732 rfl rfl (by decide +kernel) R125 F_010000 (stores Ent L124)) (by intro _ _ h; cases h) (by decide) (lf (hx_push (cellM 364 4199732 rfl rfl (by decide +kernel) R125 F_010000 (stores Ent L124)) (a := 140737488351120#64) (v := 140737488351168#64) (by decide) (ex_look (B := Ent) (L := L124) (b := 140737488351120#64) (v := 0#64) (by decide) (by decide) (by decide)) (by decide) (by decide) rfl))

theorem s126 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R126 F_010000 (stores Ent L125) 4199733) M X (· = mk R127 F_010000 (stores Ent L125) 4199736) M X :=
  sgX hparse (cellM 365 4199733 rfl rfl (by decide +kernel) R126 F_010000 (stores Ent L125)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 365 4199733 rfl rfl (by decide +kernel) R126 F_010000 (stores Ent L125)) (by decide) (by decide) rfl))

theorem s127 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R127 F_010000 (stores Ent L125) 4199736) M X (· = mk R128 F_000000 (stores Ent L125) 4199743) M X :=
  sgX hparse (cellM 366 4199736 rfl rfl (by decide +kernel) R127 F_010000 (stores Ent L125)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 366 4199736 rfl rfl (by decide +kernel) R127 F_010000 (stores Ent L125)) (by decide) (by decide) rfl))

theorem s128 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R128 F_000000 (stores Ent L125) 4199743) M X (· = mk R128 F_000000 (stores Ent L128) 4199747) M X :=
  sgX hparse (cellM 367 4199743 rfl rfl (by decide +kernel) R128 F_000000 (stores Ent L125)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 367 4199743 rfl rfl (by decide +kernel) R128 F_000000 (stores Ent L125)) (a := 140737488351112#64) (v := 16384#64) (by decide) (ex_look (B := Ent) (L := L125) (b := 140737488351112#64) (v := 13#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s129 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R128 F_000000 (stores Ent L128) 4199747) M X (· = mk R130 F_000000 (stores Ent L128) 4199754) M X :=
  sgX hparse (cellM 369 4199747 rfl rfl (by decide +kernel) R128 F_000000 (stores Ent L128)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 369 4199747 rfl rfl (by decide +kernel) R128 F_000000 (stores Ent L128)) (by decide) (by decide) rfl))

theorem s130 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R130 F_000000 (stores Ent L128) 4199754) M X (· = mk R130 F_000000 (stores Ent L130) 4199758) M X :=
  sgX hparse (cellM 370 4199754 rfl rfl (by decide +kernel) R130 F_000000 (stores Ent L128)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 370 4199754 rfl rfl (by decide +kernel) R130 F_000000 (stores Ent L128)) (a := 140737488351104#64) (v := 16384#64) (by decide) (ex_look (B := Ent) (L := L128) (b := 140737488351104#64) (v := 13#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s131 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R130 F_000000 (stores Ent L130) 4199758) M X (· = mk R132 F_000000 (stores Ent L130) 4199765) M X :=
  sgX hparse (cellM 371 4199758 rfl rfl (by decide +kernel) R130 F_000000 (stores Ent L130)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 371 4199758 rfl rfl (by decide +kernel) R130 F_000000 (stores Ent L130)) (by decide) (by decide) rfl))

theorem s132 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R132 F_000000 (stores Ent L130) 4199765) M X (· = mk R132 F_000000 (stores Ent L132) 4199769) M X :=
  sgX hparse (cellM 372 4199765 rfl rfl (by decide +kernel) R132 F_000000 (stores Ent L130)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 372 4199765 rfl rfl (by decide +kernel) R132 F_000000 (stores Ent L130)) (a := 140737488351096#64) (v := 0#64) (by decide) (ex_look (B := Ent) (L := L130) (b := 140737488351096#64) (v := 14#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s133 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R132 F_000000 (stores Ent L132) 4199769) M X (· = mk R134 F_000000 (stores Ent L132) 4199776) M X :=
  sgX hparse (cellM 373 4199769 rfl rfl (by decide +kernel) R132 F_000000 (stores Ent L132)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 373 4199769 rfl rfl (by decide +kernel) R132 F_000000 (stores Ent L132)) (by decide) (by decide) rfl))

theorem s134 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R134 F_000000 (stores Ent L132) 4199776) M X (· = mk R134 F_000000 (stores Ent L134) 4199780) M X :=
  sgX hparse (cellM 374 4199776 rfl rfl (by decide +kernel) R134 F_000000 (stores Ent L132)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 374 4199776 rfl rfl (by decide +kernel) R134 F_000000 (stores Ent L132)) (a := 140737488351088#64) (v := 32768#64) (by decide) (ex_look (B := Ent) (L := L132) (b := 140737488351088#64) (v := 112#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s135 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R134 F_000000 (stores Ent L134) 4199780) M X (· = mk R132 F_000000 (stores Ent L134) 4199787) M X :=
  sgX hparse (cellM 375 4199780 rfl rfl (by decide +kernel) R134 F_000000 (stores Ent L134)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 375 4199780 rfl rfl (by decide +kernel) R134 F_000000 (stores Ent L134)) (by decide) (by decide) rfl))

theorem s136 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R132 F_000000 (stores Ent L134) 4199787) M X (· = mk R132 F_000000 (stores Ent L136) 4199791) M X :=
  sgX hparse (cellM 376 4199787 rfl rfl (by decide +kernel) R132 F_000000 (stores Ent L134)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 376 4199787 rfl rfl (by decide +kernel) R132 F_000000 (stores Ent L134)) (a := 140737488351080#64) (v := 0#64) (by decide) (ex_look (B := Ent) (L := L134) (b := 140737488351080#64) (v := 4225776#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s137 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R132 F_000000 (stores Ent L136) 4199791) M X (· = mk R132 F_000000 (stores Ent L136) 4199793) M X :=
  sgX hparse (cellM 377 4199791 rfl rfl (by decide +kernel) R132 F_000000 (stores Ent L136)) (by intro _ _ h; cases h) (by decide) (lf (hx_jmp (cellM 377 4199791 rfl rfl (by decide +kernel) R132 F_000000 (stores Ent L136)) lab__Lscc_rt_stack_take_cls5))

theorem s138 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R132 F_000000 (stores Ent L136) 4199793) M X (· = mk R130 F_000000 (stores Ent L136) 4199797) M X :=
  sgX hparse (cellM 379 4199793 rfl rfl (by decide +kernel) R132 F_000000 (stores Ent L136)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 379 4199793 rfl rfl (by decide +kernel) R132 F_000000 (stores Ent L136)) (a := 140737488351104#64) (by decide) (loadInt_look (B := Ent) (L := L136) (b := 140737488351104#64) (v := 16384#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s139 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R130 F_000000 (stores Ent L136) 4199797) M X (· = mk R140 F_000000 (stores Ent L136) 4199801) M X :=
  sgX hparse (cellM 380 4199797 rfl rfl (by decide +kernel) R130 F_000000 (stores Ent L136)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 380 4199797 rfl rfl (by decide +kernel) R130 F_000000 (stores Ent L136)) (a := 140737488351112#64) (by decide) (loadInt_look (B := Ent) (L := L136) (b := 140737488351112#64) (v := 16384#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s140 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R140 F_000000 (stores Ent L136) 4199801) M X (· = mk R140 F_010100 (stores Ent L136) 4199804) M X :=
  sgX hparse (cellM 381 4199801 rfl rfl (by decide +kernel) R140 F_000000 (stores Ent L136)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 381 4199801 rfl rfl (by decide +kernel) R140 F_000000 (stores Ent L136)) (by decide) (by decide) rfl))

theorem s141 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R140 F_010100 (stores Ent L136) 4199804) M X (· = mk R140 F_010100 (stores Ent L136) 4199806) M X :=
  sgX hparse (cellM 382 4199804 rfl rfl (by decide +kernel) R140 F_010100 (stores Ent L136)) (by intro _ _ h; cases h) (by decide) (lf (hx_jccN (cellM 382 4199804 rfl rfl (by decide +kernel) R140 F_010100 (stores Ent L136)) (by decide) rfl))

theorem s142 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R140 F_010100 (stores Ent L136) 4199806) M X (· = mk R140 F_010100 (stores Ent L136) 4199897) M X :=
  sgX hparse (cellM 383 4199806 rfl rfl (by decide +kernel) R140 F_010100 (stores Ent L136)) (by intro _ _ h; cases h) (by decide) (lf (hx_jmp (cellM 383 4199806 rfl rfl (by decide +kernel) R140 F_010100 (stores Ent L136)) lab__Lscc_rt_stack_take_clsdone7))

theorem s143 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R140 F_010100 (stores Ent L136) 4199897) M X (· = mk R144 F_010100 (stores Ent L136) 4199904) M X :=
  sgX hparse (cellM 407 4199897 rfl rfl (by decide +kernel) R140 F_010100 (stores Ent L136)) (by intro _ _ h; cases h) (by decide) (lf (hx_leaRip (cellM 407 4199897 rfl rfl (by decide +kernel) R140 F_010100 (stores Ent L136)) lab_scc_rt_stack_free_n (by decide) rfl))

/-- **Steps 108 … 143.** -/
theorem c4 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R79 F_000000 (stores Ent L107) 4199448) M X (· = mk R144 F_010100 (stores Ent L136) 4199904) M X :=
  SegP.trans (s108 hparse) <|
  SegP.trans (s109 hparse) <|
  SegP.trans (s110 hparse) <|
  SegP.trans (s111 hparse) <|
  SegP.trans (s112 hparse) <|
  SegP.trans (s113 hparse) <|
  SegP.trans (s114 hparse) <|
  SegP.trans (s115 hparse) <|
  SegP.trans (s116 hparse) <|
  SegP.trans (s117 hparse) <|
  SegP.trans (s118 hparse) <|
  SegP.trans (s119 hparse) <|
  SegP.trans (s120 hparse) <|
  SegP.trans (s121 hparse) <|
  SegP.trans (s122 hparse) <|
  SegP.trans (s123 hparse) <|
  SegP.trans (s124 hparse) <|
  SegP.trans (s125 hparse) <|
  SegP.trans (s126 hparse) <|
  SegP.trans (s127 hparse) <|
  SegP.trans (s128 hparse) <|
  SegP.trans (s129 hparse) <|
  SegP.trans (s130 hparse) <|
  SegP.trans (s131 hparse) <|
  SegP.trans (s132 hparse) <|
  SegP.trans (s133 hparse) <|
  SegP.trans (s134 hparse) <|
  SegP.trans (s135 hparse) <|
  SegP.trans (s136 hparse) <|
  SegP.trans (s137 hparse) <|
  SegP.trans (s138 hparse) <|
  SegP.trans (s139 hparse) <|
  SegP.trans (s140 hparse) <|
  SegP.trans (s141 hparse) <|
  SegP.trans (s142 hparse) <|
  (s143 hparse)

/-- info: 'Spike.Test.HelloRootL0XClosed.c4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.c4

end Spike.Test.HelloRootL0XClosed
