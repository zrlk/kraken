/-
**`hello.w` on x86-64, the closed run, chunk 3**: steps 72 … 107 of
thread 0 from the load (`HelloRootL0XClosedStep`), one `SegP` segment per
instruction, composed into `c3`.

Generated from the reference run of the program (the states before every
step: registers `R…`, flags `F_…` (`cf pf af zf sf of`), private memory the
entry stack after the 8-byte stores `L…` (after the take: the taken copy
`B2` after `N…`), shared memory the write chain `M…`). Every step is proved,
not trusted: the generator only chooses the lemma and the witnesses.
-/
import Spike.Test.HelloRootL0XClosedC2

namespace Spike.Test.HelloRootL0XClosed

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Test.HelloLinkedX64 (Λe)
open Spike.Lib.Fwd

set_option maxRecDepth 100000

abbrev R76 : Reg64s := { rax := 71859008, rcx := 163840, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R79 : Reg64s := { rax := 71859008, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R84 : Reg64s := { rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R87 : Reg64s := { rcx := 3, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R90 : Reg64s := { rax := 1, rcx := 3, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R91 : Reg64s := { rax := 1, rcx := 36, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R92 : Reg64s := { rax := 68719476736, rcx := 36, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R94 : Reg64s := { rax := 3331, rcx := 36, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R95 : Reg64s := { rax := 3331, rcx := 68719476736, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R96 : Reg64s := { rax := 68719480067, rcx := 68719476736, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R98 : Reg64s := { rax := 71859008, rcx := 68719476736, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R102 : Reg64s := { rax := 71859008, rcx := 71859008, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R103 : Reg64s := { rax := 68719480067, rcx := 71859008, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev L76 : List (BitVec 64 × BitVec 64) := (140737488351056#64, 71859008#64) :: L69
abbrev L80 : List (BitVec 64 × BitVec 64) := (140737488351048#64, 71859008#64) :: L76
abbrev L84 : List (BitVec 64 × BitVec 64) := (140737488351040#64, 0#64) :: L80
abbrev L88 : List (BitVec 64 × BitVec 64) := (140737488351032#64, 0#64) :: L84
abbrev L92 : List (BitVec 64 × BitVec 64) := (140737488351024#64, 68719476736#64) :: L88
abbrev L96 : List (BitVec 64 × BitVec 64) := (140737488351016#64, 68719480067#64) :: L92
abbrev L100 : List (BitVec 64 × BitVec 64) := (140737488351008#64, 71859008#64) :: L96
abbrev L107 : List (BitVec 64 × BitVec 64) := (140737488351000#64, 71859008#64) :: L100
abbrev M103 : Memory := (M64.append { loc := ⟨71859008#64, 8⟩, val := 68719480067#128, tid := 0 }).1

/-! ## Steps -/

theorem s72 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R72 F_000000 (stores Ent L69) 4199263) M X (· = mk R72 F_100010 (stores Ent L69) 4199266) M X :=
  sgX hparse (cellM 240 4199263 rfl rfl (by decide +kernel) R72 F_000000 (stores Ent L69)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 240 4199263 rfl rfl (by decide +kernel) R72 F_000000 (stores Ent L69)) (by decide) (by decide) rfl))

theorem s73 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R72 F_100010 (stores Ent L69) 4199266) M X (· = mk R72 F_100010 (stores Ent L69) 4199268) M X :=
  sgX hparse (cellM 241 4199266 rfl rfl (by decide +kernel) R72 F_100010 (stores Ent L69)) (by intro _ _ h; cases h) (by decide) (lf (hx_jccN (cellM 241 4199266 rfl rfl (by decide +kernel) R72 F_100010 (stores Ent L69)) (by decide) rfl))

theorem s74 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R72 F_100010 (stores Ent L69) 4199268) M X (· = mk R72 F_100010 (stores Ent L69) 4199284) M X :=
  sgX hparse (cellM 242 4199268 rfl rfl (by decide +kernel) R72 F_100010 (stores Ent L69)) (by intro _ _ h; cases h) (by decide) (lf (hx_jmp (cellM 242 4199268 rfl rfl (by decide +kernel) R72 F_100010 (stores Ent L69)) lab__Lscc_rt_alloc_tcb_ok))

theorem s75 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R72 F_100010 (stores Ent L69) 4199284) M X (· = mk R76 F_100010 (stores Ent L69) 4199291) M X :=
  sgX hparse (cellM 249 4199284 rfl rfl (by decide +kernel) R72 F_100010 (stores Ent L69)) (by intro _ _ h; cases h) (by decide) (lf (hx_leaRip (cellM 249 4199284 rfl rfl (by decide +kernel) R72 F_100010 (stores Ent L69)) lab_scc_rt_pinned (by decide) rfl))

theorem s76 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R76 F_100010 (stores Ent L69) 4199291) M X (· = mk R76 F_100010 (stores Ent L76) 4199295) M X :=
  sgX hparse (cellM 250 4199291 rfl rfl (by decide +kernel) R76 F_100010 (stores Ent L69)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 250 4199291 rfl rfl (by decide +kernel) R76 F_100010 (stores Ent L69)) (a := 140737488351056#64) (v := 71859008#64) (by decide) (ex_base (B := Ent) (L := L69) (b := 140737488351056#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s77 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R76 F_100010 (stores Ent L76) 4199295) M X (· = mk R76 F_100010 (stores Ent L76) 4199299) M X :=
  sgX hparse (cellM 251 4199295 rfl rfl (by decide +kernel) R76 F_100010 (stores Ent L76)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 251 4199295 rfl rfl (by decide +kernel) R76 F_100010 (stores Ent L76)) (a := 140737488351056#64) (by decide) (loadInt_look (B := Ent) (L := L76) (b := 140737488351056#64) (v := 71859008#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s78 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R76 F_100010 (stores Ent L76) 4199299) M X (· = mk R79 F_100010 (stores Ent L76) 4199303) M X :=
  sgX hparse (cellM 252 4199299 rfl rfl (by decide +kernel) R76 F_100010 (stores Ent L76)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 252 4199299 rfl rfl (by decide +kernel) R76 F_100010 (stores Ent L76)) (a := 140737488351072#64) (by decide) (loadInt_look (B := Ent) (L := L76) (b := 140737488351072#64) (v := 0#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s79 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R79 F_100010 (stores Ent L76) 4199303) M X (· = mk R79 F_000000 (stores Ent L76) 4199306) M X :=
  sgX hparse (cellM 253 4199303 rfl rfl (by decide +kernel) R79 F_100010 (stores Ent L76)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 253 4199303 rfl rfl (by decide +kernel) R79 F_100010 (stores Ent L76)) (by decide) (by decide) rfl))

theorem s80 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R79 F_000000 (stores Ent L76) 4199306) M X (· = mk R79 F_000000 (stores Ent L80) 4199310) M X :=
  sgX hparse (cellM 254 4199306 rfl rfl (by decide +kernel) R79 F_000000 (stores Ent L76)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 254 4199306 rfl rfl (by decide +kernel) R79 F_000000 (stores Ent L76)) (a := 140737488351048#64) (v := 71859008#64) (by decide) (ex_base (B := Ent) (L := L76) (b := 140737488351048#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s81 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R79 F_000000 (stores Ent L80) 4199310) M X (· = mk R49 F_000000 (stores Ent L80) 4199314) M X :=
  sgX hparse (cellM 255 4199310 rfl rfl (by decide +kernel) R79 F_000000 (stores Ent L80)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 255 4199310 rfl rfl (by decide +kernel) R79 F_000000 (stores Ent L80)) (a := 140737488351152#64) (by decide) (loadInt_look (B := Ent) (L := L80) (b := 140737488351152#64) (v := 1#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s82 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R49 F_000000 (stores Ent L80) 4199314) M X (· = mk R49 F_000000 (stores Ent L80) 4199318) M X :=
  sgX hparse (cellM 256 4199314 rfl rfl (by decide +kernel) R49 F_000000 (stores Ent L80)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 256 4199314 rfl rfl (by decide +kernel) R49 F_000000 (stores Ent L80)) (a := 140737488351120#64) (by decide) (loadInt_look (B := Ent) (L := L80) (b := 140737488351120#64) (v := 0#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s83 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R49 F_000000 (stores Ent L80) 4199318) M X (· = mk R84 F_000000 (stores Ent L80) 4199322) M X :=
  sgX hparse (cellM 257 4199318 rfl rfl (by decide +kernel) R49 F_000000 (stores Ent L80)) (by intro _ _ h; cases h) (by decide) (lx_imul (exec_imul_rr (cellM 257 4199318 rfl rfl (by decide +kernel) R49 F_000000 (stores Ent L80))) (by decide) (by decide) rfl)

theorem s84 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R84 F_000000 (stores Ent L80) 4199322) M X (· = mk R84 F_000000 (stores Ent L84) 4199326) M X :=
  sgX hparse (cellM 258 4199322 rfl rfl (by decide +kernel) R84 F_000000 (stores Ent L80)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 258 4199322 rfl rfl (by decide +kernel) R84 F_000000 (stores Ent L80)) (a := 140737488351040#64) (v := 0#64) (by decide) (ex_base (B := Ent) (L := L80) (b := 140737488351040#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s85 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R84 F_000000 (stores Ent L84) 4199326) M X (· = mk R84 F_000000 (stores Ent L84) 4199330) M X :=
  sgX hparse (cellM 259 4199326 rfl rfl (by decide +kernel) R84 F_000000 (stores Ent L84)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 259 4199326 rfl rfl (by decide +kernel) R84 F_000000 (stores Ent L84)) (a := 140737488351040#64) (by decide) (loadInt_look (B := Ent) (L := L84) (b := 140737488351040#64) (v := 0#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s86 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R84 F_000000 (stores Ent L84) 4199330) M X (· = mk R87 F_000000 (stores Ent L84) 4199337) M X :=
  sgX hparse (cellM 260 4199330 rfl rfl (by decide +kernel) R84 F_000000 (stores Ent L84)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 260 4199330 rfl rfl (by decide +kernel) R84 F_000000 (stores Ent L84)) (by decide) (by decide) rfl))

theorem s87 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R87 F_000000 (stores Ent L84) 4199337) M X (· = mk R87 F_010100 (stores Ent L84) 4199340) M X :=
  sgX hparse (cellM 261 4199337 rfl rfl (by decide +kernel) R87 F_000000 (stores Ent L84)) (by intro _ _ h; cases h) (by decide) (lx_shl (cellM 261 4199337 rfl rfl (by decide +kernel) R87 F_000000 (stores Ent L84)) (by decide) (by decide) (by decide) (by decide) rfl)

theorem s88 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R87 F_010100 (stores Ent L84) 4199340) M X (· = mk R87 F_010100 (stores Ent L88) 4199347) M X :=
  sgX hparse (cellM 262 4199340 rfl rfl (by decide +kernel) R87 F_010100 (stores Ent L84)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 262 4199340 rfl rfl (by decide +kernel) R87 F_010100 (stores Ent L84)) (a := 140737488351032#64) (v := 0#64) (by decide) (ex_base (B := Ent) (L := L84) (b := 140737488351032#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s89 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R87 F_010100 (stores Ent L88) 4199347) M X (· = mk R90 F_010100 (stores Ent L88) 4199351) M X :=
  sgX hparse (cellM 263 4199347 rfl rfl (by decide +kernel) R87 F_010100 (stores Ent L88)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 263 4199347 rfl rfl (by decide +kernel) R87 F_010100 (stores Ent L88)) (a := 140737488351152#64) (by decide) (loadInt_look (B := Ent) (L := L88) (b := 140737488351152#64) (v := 1#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s90 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R90 F_010100 (stores Ent L88) 4199351) M X (· = mk R91 F_010100 (stores Ent L88) 4199358) M X :=
  sgX hparse (cellM 264 4199351 rfl rfl (by decide +kernel) R90 F_010100 (stores Ent L88)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 264 4199351 rfl rfl (by decide +kernel) R90 F_010100 (stores Ent L88)) (by decide) (by decide) rfl))

theorem s91 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R91 F_010100 (stores Ent L88) 4199358) M X (· = mk R92 F_010000 (stores Ent L88) 4199361) M X :=
  sgX hparse (cellM 265 4199358 rfl rfl (by decide +kernel) R91 F_010100 (stores Ent L88)) (by intro _ _ h; cases h) (by decide) (lx_shl (cellM 265 4199358 rfl rfl (by decide +kernel) R91 F_010100 (stores Ent L88)) (by decide) (by decide) (by decide) (by decide) rfl)

theorem s92 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R92 F_010000 (stores Ent L88) 4199361) M X (· = mk R92 F_010000 (stores Ent L92) 4199368) M X :=
  sgX hparse (cellM 266 4199361 rfl rfl (by decide +kernel) R92 F_010000 (stores Ent L88)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 266 4199361 rfl rfl (by decide +kernel) R92 F_010000 (stores Ent L88)) (a := 140737488351024#64) (v := 68719476736#64) (by decide) (ex_base (B := Ent) (L := L88) (b := 140737488351024#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s93 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R92 F_010000 (stores Ent L92) 4199368) M X (· = mk R94 F_010000 (stores Ent L92) 4199372) M X :=
  sgX hparse (cellM 267 4199368 rfl rfl (by decide +kernel) R92 F_010000 (stores Ent L92)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 267 4199368 rfl rfl (by decide +kernel) R92 F_010000 (stores Ent L92)) (a := 140737488351160#64) (by decide) (loadInt_look (B := Ent) (L := L92) (b := 140737488351160#64) (v := 3331#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s94 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R94 F_010000 (stores Ent L92) 4199372) M X (· = mk R95 F_010000 (stores Ent L92) 4199379) M X :=
  sgX hparse (cellM 268 4199372 rfl rfl (by decide +kernel) R94 F_010000 (stores Ent L92)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 268 4199372 rfl rfl (by decide +kernel) R94 F_010000 (stores Ent L92)) (a := 140737488351024#64) (by decide) (loadInt_look (B := Ent) (L := L92) (b := 140737488351024#64) (v := 68719476736#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s95 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R95 F_010000 (stores Ent L92) 4199379) M X (· = mk R96 F_010000 (stores Ent L92) 4199382) M X :=
  sgX hparse (cellM 269 4199379 rfl rfl (by decide +kernel) R95 F_010000 (stores Ent L92)) (by intro _ _ h; cases h) (by decide) (lx_logic (exec_or_rr (cellM 269 4199379 rfl rfl (by decide +kernel) R95 F_010000 (stores Ent L92))) (by decide) (by decide) rfl)

theorem s96 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R96 F_010000 (stores Ent L92) 4199382) M X (· = mk R96 F_010000 (stores Ent L96) 4199389) M X :=
  sgX hparse (cellM 270 4199382 rfl rfl (by decide +kernel) R96 F_010000 (stores Ent L92)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 270 4199382 rfl rfl (by decide +kernel) R96 F_010000 (stores Ent L92)) (a := 140737488351016#64) (v := 68719480067#64) (by decide) (ex_base (B := Ent) (L := L92) (b := 140737488351016#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s97 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R96 F_010000 (stores Ent L96) 4199389) M X (· = mk R98 F_010000 (stores Ent L96) 4199393) M X :=
  sgX hparse (cellM 271 4199389 rfl rfl (by decide +kernel) R96 F_010000 (stores Ent L96)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 271 4199389 rfl rfl (by decide +kernel) R96 F_010000 (stores Ent L96)) (a := 140737488351048#64) (by decide) (loadInt_look (B := Ent) (L := L96) (b := 140737488351048#64) (v := 71859008#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s98 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R98 F_010000 (stores Ent L96) 4199393) M X (· = mk R79 F_010000 (stores Ent L96) 4199400) M X :=
  sgX hparse (cellM 272 4199393 rfl rfl (by decide +kernel) R98 F_010000 (stores Ent L96)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 272 4199393 rfl rfl (by decide +kernel) R98 F_010000 (stores Ent L96)) (a := 140737488351032#64) (by decide) (loadInt_look (B := Ent) (L := L96) (b := 140737488351032#64) (v := 0#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s99 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R79 F_010000 (stores Ent L96) 4199400) M X (· = mk R79 F_000000 (stores Ent L96) 4199403) M X :=
  sgX hparse (cellM 273 4199400 rfl rfl (by decide +kernel) R79 F_010000 (stores Ent L96)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 273 4199400 rfl rfl (by decide +kernel) R79 F_010000 (stores Ent L96)) (by decide) (by decide) rfl))

theorem s100 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R79 F_000000 (stores Ent L96) 4199403) M X (· = mk R79 F_000000 (stores Ent L100) 4199410) M X :=
  sgX hparse (cellM 274 4199403 rfl rfl (by decide +kernel) R79 F_000000 (stores Ent L96)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 274 4199403 rfl rfl (by decide +kernel) R79 F_000000 (stores Ent L96)) (a := 140737488351008#64) (v := 71859008#64) (by decide) (ex_base (B := Ent) (L := L96) (b := 140737488351008#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s101 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R79 F_000000 (stores Ent L100) 4199410) M X (· = mk R102 F_000000 (stores Ent L100) 4199417) M X :=
  sgX hparse (cellM 275 4199410 rfl rfl (by decide +kernel) R79 F_000000 (stores Ent L100)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 275 4199410 rfl rfl (by decide +kernel) R79 F_000000 (stores Ent L100)) (a := 140737488351008#64) (by decide) (loadInt_look (B := Ent) (L := L100) (b := 140737488351008#64) (v := 71859008#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s102 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R102 F_000000 (stores Ent L100) 4199417) M X (· = mk R103 F_000000 (stores Ent L100) 4199424) M X :=
  sgX hparse (cellM 276 4199417 rfl rfl (by decide +kernel) R102 F_000000 (stores Ent L100)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 276 4199417 rfl rfl (by decide +kernel) R102 F_000000 (stores Ent L100)) (a := 140737488351016#64) (by decide) (loadInt_look (B := Ent) (L := L100) (b := 140737488351016#64) (v := 68719480067#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s103 (hparse : Parse) {X : Kernel.KState} :
    Sg (· = mk R103 F_000000 (stores Ent L100) 4199424) M64 X (· = mk R103 F_000000 (stores Ent L100) 4199427) M103 X :=
  sgStSh hparse (cellM 277 4199424 rfl rfl (by decide +kernel) R103 F_000000 (stores Ent L100)) (by decide) (a := 71859008#64) ((eaddr_reg_disp _ _ _ _).trans (by decide)) ((loadInt_look_none (B := Ent) (L := L100) (b := 71859008#64) (by decide) (by decide) (by decide)).trans (ent_none (by decide))) (val := 68719480067#128) (by decide) rfl

theorem s104 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R103 F_000000 (stores Ent L100) 4199427) M X (· = mk R102 F_000000 (stores Ent L100) 4199431) M X :=
  sgX hparse (cellM 278 4199427 rfl rfl (by decide +kernel) R103 F_000000 (stores Ent L100)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 278 4199427 rfl rfl (by decide +kernel) R103 F_000000 (stores Ent L100)) (a := 140737488351048#64) (by decide) (loadInt_look (B := Ent) (L := L100) (b := 140737488351048#64) (v := 71859008#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s105 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R102 F_000000 (stores Ent L100) 4199431) M X (· = mk R79 F_000000 (stores Ent L100) 4199438) M X :=
  sgX hparse (cellM 279 4199431 rfl rfl (by decide +kernel) R102 F_000000 (stores Ent L100)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 279 4199431 rfl rfl (by decide +kernel) R102 F_000000 (stores Ent L100)) (a := 140737488351032#64) (by decide) (loadInt_look (B := Ent) (L := L100) (b := 140737488351032#64) (v := 0#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s106 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R79 F_000000 (stores Ent L100) 4199438) M X (· = mk R79 F_000000 (stores Ent L100) 4199441) M X :=
  sgX hparse (cellM 280 4199438 rfl rfl (by decide +kernel) R79 F_000000 (stores Ent L100)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 280 4199438 rfl rfl (by decide +kernel) R79 F_000000 (stores Ent L100)) (by decide) (by decide) rfl))

theorem s107 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R79 F_000000 (stores Ent L100) 4199441) M X (· = mk R79 F_000000 (stores Ent L107) 4199448) M X :=
  sgX hparse (cellM 281 4199441 rfl rfl (by decide +kernel) R79 F_000000 (stores Ent L100)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 281 4199441 rfl rfl (by decide +kernel) R79 F_000000 (stores Ent L100)) (a := 140737488351000#64) (v := 71859008#64) (by decide) (ex_base (B := Ent) (L := L100) (b := 140737488351000#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

/-- **Steps 72 … 107.** -/
theorem c3 (hparse : Parse) {X : Kernel.KState} :
    Sg (· = mk R72 F_000000 (stores Ent L69) 4199263) M64 X (· = mk R79 F_000000 (stores Ent L107) 4199448) M103 X :=
  SegP.trans (s72 hparse) <|
  SegP.trans (s73 hparse) <|
  SegP.trans (s74 hparse) <|
  SegP.trans (s75 hparse) <|
  SegP.trans (s76 hparse) <|
  SegP.trans (s77 hparse) <|
  SegP.trans (s78 hparse) <|
  SegP.trans (s79 hparse) <|
  SegP.trans (s80 hparse) <|
  SegP.trans (s81 hparse) <|
  SegP.trans (s82 hparse) <|
  SegP.trans (s83 hparse) <|
  SegP.trans (s84 hparse) <|
  SegP.trans (s85 hparse) <|
  SegP.trans (s86 hparse) <|
  SegP.trans (s87 hparse) <|
  SegP.trans (s88 hparse) <|
  SegP.trans (s89 hparse) <|
  SegP.trans (s90 hparse) <|
  SegP.trans (s91 hparse) <|
  SegP.trans (s92 hparse) <|
  SegP.trans (s93 hparse) <|
  SegP.trans (s94 hparse) <|
  SegP.trans (s95 hparse) <|
  SegP.trans (s96 hparse) <|
  SegP.trans (s97 hparse) <|
  SegP.trans (s98 hparse) <|
  SegP.trans (s99 hparse) <|
  SegP.trans (s100 hparse) <|
  SegP.trans (s101 hparse) <|
  SegP.trans (s102 hparse) <|
  SegP.trans (s103 hparse) <|
  SegP.trans (s104 hparse) <|
  SegP.trans (s105 hparse) <|
  SegP.trans (s106 hparse) <|
  (s107 hparse)

/-- info: 'Spike.Test.HelloRootL0XClosed.c3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.c3

end Spike.Test.HelloRootL0XClosed
