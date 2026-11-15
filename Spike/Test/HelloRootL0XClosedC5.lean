/-
**`hello.w` on x86-64, the closed run, chunk 5**: steps 144 … 179 of
thread 0 from the load (`HelloRootL0XClosedStep`), one `SegP` segment per
instruction, composed into `c5`.

Generated from the reference run of the program (the states before every
step: registers `R…`, flags `F_…` (`cf pf af zf sf of`), private memory the
entry stack after the 8-byte stores `L…` (after the take: the taken copy
`B2` after `N…`), shared memory the write chain `M…`). Every step is proved,
not trusted: the generator only chooses the lemma and the witnesses.
-/
import Spike.Test.HelloRootL0XClosedC4

namespace Spike.Test.HelloRootL0XClosed

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Test.HelloLinkedX64 (Λe)
open Spike.Lib.Fwd

set_option maxRecDepth 100000

abbrev R147 : Reg64s := { rax := 4225808, rsi := 1, rdi := 16384, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
abbrev R150 : Reg64s := { rax := 4225912, rsi := 1, rdi := 16384, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
abbrev R156 : Reg64s := { rax := 4225800, rsi := 1, rdi := 16384, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
abbrev R159 : Reg64s := { rax := 4225800, rcx := 4225800, rsi := 1, rdi := 16384, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
abbrev R160 : Reg64s := { rax := 1, rcx := 4225800, rsi := 1, rdi := 16384, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
abbrev R161 : Reg64s := { rcx := 4225800, rsi := 1, rdi := 16384, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
abbrev R164 : Reg64s := { rsi := 1, rdi := 16384, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
abbrev R167 : Reg64s := { rcx := 4225808, rsi := 1, rdi := 16384, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
abbrev R179 : Reg64s := { rax := 4225792, rcx := 4225800, rsi := 1, rdi := 16384, rsp := 140737488350928, rbp := 140737488351120, r10 := 8 }
abbrev L144 : List (BitVec 64 × BitVec 64) := (140737488351064#64, 4225808#64) :: L136
abbrev L148 : List (BitVec 64 × BitVec 64) := (140737488351056#64, 4225808#64) :: L144
abbrev L150 : List (BitVec 64 × BitVec 64) := (140737488351048#64, 4225912#64) :: L148
abbrev L154 : List (BitVec 64 × BitVec 64) := (140737488351040#64, 4225912#64) :: L150
abbrev L156 : List (BitVec 64 × BitVec 64) := (140737488351032#64, 4225800#64) :: L154
abbrev L161 : List (BitVec 64 × BitVec 64) := (140737488351024#64, 0#64) :: L156
abbrev L168 : List (BitVec 64 × BitVec 64) := (140737488351016#64, 0#64) :: L161
abbrev L174 : List (BitVec 64 × BitVec 64) := (140737488350968#64, 4225800#64) :: L168
abbrev L179 : List (BitVec 64 × BitVec 64) := (140737488350960#64, 4225792#64) :: L174
abbrev M160 : Memory := (M103.append { loc := ⟨4225800#64, 8⟩, val := 1#128, tid := 0 }).1
abbrev M177 : Memory := (M160.append { loc := ⟨4225800#64, 8⟩, val := 0#128, tid := 0 }).1

/-! ## Steps -/

theorem s144 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R144 F_010100 (stores Ent L136) 4199904) M X (· = mk R144 F_010100 (stores Ent L144) 4199908) M X :=
  sgX hparse (cellM 408 4199904 rfl rfl (by decide +kernel) R144 F_010100 (stores Ent L136)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 408 4199904 rfl rfl (by decide +kernel) R144 F_010100 (stores Ent L136)) (a := 140737488351064#64) (v := 4225808#64) (by decide) (ex_look (B := Ent) (L := L136) (b := 140737488351064#64) (v := 112#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s145 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R144 F_010100 (stores Ent L144) 4199908) M X (· = mk R144 F_010100 (stores Ent L144) 4199912) M X :=
  sgX hparse (cellM 409 4199908 rfl rfl (by decide +kernel) R144 F_010100 (stores Ent L144)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 409 4199908 rfl rfl (by decide +kernel) R144 F_010100 (stores Ent L144)) (a := 140737488351064#64) (by decide) (loadInt_look (B := Ent) (L := L144) (b := 140737488351064#64) (v := 4225808#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s146 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R144 F_010100 (stores Ent L144) 4199912) M X (· = mk R147 F_010100 (stores Ent L144) 4199916) M X :=
  sgX hparse (cellM 410 4199912 rfl rfl (by decide +kernel) R144 F_010100 (stores Ent L144)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 410 4199912 rfl rfl (by decide +kernel) R144 F_010100 (stores Ent L144)) (a := 140737488351080#64) (by decide) (loadInt_look (B := Ent) (L := L144) (b := 140737488351080#64) (v := 0#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s147 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R147 F_010100 (stores Ent L144) 4199916) M X (· = mk R147 F_000000 (stores Ent L144) 4199919) M X :=
  sgX hparse (cellM 411 4199916 rfl rfl (by decide +kernel) R147 F_010100 (stores Ent L144)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 411 4199916 rfl rfl (by decide +kernel) R147 F_010100 (stores Ent L144)) (by decide) (by decide) rfl))

theorem s148 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R147 F_000000 (stores Ent L144) 4199919) M X (· = mk R147 F_000000 (stores Ent L148) 4199923) M X :=
  sgX hparse (cellM 412 4199919 rfl rfl (by decide +kernel) R147 F_000000 (stores Ent L144)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 412 4199919 rfl rfl (by decide +kernel) R147 F_000000 (stores Ent L144)) (a := 140737488351056#64) (v := 4225808#64) (by decide) (ex_look (B := Ent) (L := L144) (b := 140737488351056#64) (v := 71859008#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s149 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R147 F_000000 (stores Ent L148) 4199923) M X (· = mk R150 F_000000 (stores Ent L148) 4199930) M X :=
  sgX hparse (cellM 413 4199923 rfl rfl (by decide +kernel) R147 F_000000 (stores Ent L148)) (by intro _ _ h; cases h) (by decide) (lf (hx_leaRip (cellM 413 4199923 rfl rfl (by decide +kernel) R147 F_000000 (stores Ent L148)) lab_scc_rt_stack_free (by decide) rfl))

theorem s150 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R150 F_000000 (stores Ent L148) 4199930) M X (· = mk R150 F_000000 (stores Ent L150) 4199934) M X :=
  sgX hparse (cellM 414 4199930 rfl rfl (by decide +kernel) R150 F_000000 (stores Ent L148)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 414 4199930 rfl rfl (by decide +kernel) R150 F_000000 (stores Ent L148)) (a := 140737488351048#64) (v := 4225912#64) (by decide) (ex_look (B := Ent) (L := L148) (b := 140737488351048#64) (v := 71859008#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s151 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R150 F_000000 (stores Ent L150) 4199934) M X (· = mk R150 F_000000 (stores Ent L150) 4199938) M X :=
  sgX hparse (cellM 415 4199934 rfl rfl (by decide +kernel) R150 F_000000 (stores Ent L150)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 415 4199934 rfl rfl (by decide +kernel) R150 F_000000 (stores Ent L150)) (a := 140737488351048#64) (by decide) (loadInt_look (B := Ent) (L := L150) (b := 140737488351048#64) (v := 4225912#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s152 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R150 F_000000 (stores Ent L150) 4199938) M X (· = mk R150 F_000000 (stores Ent L150) 4199942) M X :=
  sgX hparse (cellM 416 4199938 rfl rfl (by decide +kernel) R150 F_000000 (stores Ent L150)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 416 4199938 rfl rfl (by decide +kernel) R150 F_000000 (stores Ent L150)) (a := 140737488351096#64) (by decide) (loadInt_look (B := Ent) (L := L150) (b := 140737488351096#64) (v := 0#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s153 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R150 F_000000 (stores Ent L150) 4199942) M X (· = mk R150 F_010000 (stores Ent L150) 4199945) M X :=
  sgX hparse (cellM 417 4199942 rfl rfl (by decide +kernel) R150 F_000000 (stores Ent L150)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 417 4199942 rfl rfl (by decide +kernel) R150 F_000000 (stores Ent L150)) (by decide) (by decide) rfl))

theorem s154 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R150 F_010000 (stores Ent L150) 4199945) M X (· = mk R150 F_010000 (stores Ent L154) 4199949) M X :=
  sgX hparse (cellM 418 4199945 rfl rfl (by decide +kernel) R150 F_010000 (stores Ent L150)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 418 4199945 rfl rfl (by decide +kernel) R150 F_010000 (stores Ent L150)) (a := 140737488351040#64) (v := 4225912#64) (by decide) (ex_look (B := Ent) (L := L150) (b := 140737488351040#64) (v := 0#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s155 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R150 F_010000 (stores Ent L154) 4199949) M X (· = mk R156 F_010000 (stores Ent L154) 4199956) M X :=
  sgX hparse (cellM 419 4199949 rfl rfl (by decide +kernel) R150 F_010000 (stores Ent L154)) (by intro _ _ h; cases h) (by decide) (lf (hx_leaRip (cellM 419 4199949 rfl rfl (by decide +kernel) R150 F_010000 (stores Ent L154)) lab_scc_rt_stack_lock (by decide) rfl))

theorem s156 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R156 F_010000 (stores Ent L154) 4199956) M X (· = mk R156 F_010000 (stores Ent L156) 4199960) M X :=
  sgX hparse (cellM 420 4199956 rfl rfl (by decide +kernel) R156 F_010000 (stores Ent L154)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 420 4199956 rfl rfl (by decide +kernel) R156 F_010000 (stores Ent L154)) (a := 140737488351032#64) (v := 4225800#64) (by decide) (ex_look (B := Ent) (L := L154) (b := 140737488351032#64) (v := 0#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s157 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R156 F_010000 (stores Ent L156) 4199960) M X (· = mk R156 F_010000 (stores Ent L156) 4199962) M X :=
  sgX hparse (cellM 421 4199960 rfl rfl (by decide +kernel) R156 F_010000 (stores Ent L156)) (by intro _ _ h; cases h) (by decide) (lf (hx_jmp (cellM 421 4199960 rfl rfl (by decide +kernel) R156 F_010000 (stores Ent L156)) lab__Lscc_rt_stack_take_spin14))

theorem s158 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R156 F_010000 (stores Ent L156) 4199962) M X (· = mk R159 F_010000 (stores Ent L156) 4199966) M X :=
  sgX hparse (cellM 423 4199962 rfl rfl (by decide +kernel) R156 F_010000 (stores Ent L156)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 423 4199962 rfl rfl (by decide +kernel) R156 F_010000 (stores Ent L156)) (a := 140737488351032#64) (by decide) (loadInt_look (B := Ent) (L := L156) (b := 140737488351032#64) (v := 4225800#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s159 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R159 F_010000 (stores Ent L156) 4199966) M X (· = mk R160 F_010000 (stores Ent L156) 4199973) M X :=
  sgX hparse (cellM 424 4199966 rfl rfl (by decide +kernel) R159 F_010000 (stores Ent L156)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 424 4199966 rfl rfl (by decide +kernel) R159 F_010000 (stores Ent L156)) (by decide) (by decide) rfl))

theorem s160 (hparse : Parse) {X : Kernel.KState} :
    Sg (· = mk R160 F_010000 (stores Ent L156) 4199973) M103 X (· = mk R161 F_010000 (stores Ent L156) 4199976) M160 X :=
  sgXchgSh hparse (cellM 425 4199973 rfl rfl (by decide +kernel) R160 F_010000 (stores Ent L156)) (by decide) (a := 4225800#64) ((eaddr_reg_disp _ _ _ _).trans (by decide)) ((loadInt_look_none (B := Ent) (L := L156) (b := 4225800#64) (by decide) (by decide) (by decide)).trans (ent_none (by decide))) (old := 0#128) (nv := 1#128) (by decide) (by decide) (by decide) rfl

theorem s161 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R161 F_010000 (stores Ent L156) 4199976) M X (· = mk R161 F_010000 (stores Ent L161) 4199980) M X :=
  sgX hparse (cellM 426 4199976 rfl rfl (by decide +kernel) R161 F_010000 (stores Ent L156)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 426 4199976 rfl rfl (by decide +kernel) R161 F_010000 (stores Ent L156)) (a := 140737488351024#64) (v := 0#64) (by decide) (ex_look (B := Ent) (L := L156) (b := 140737488351024#64) (v := 68719476736#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s162 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R161 F_010000 (stores Ent L161) 4199980) M X (· = mk R161 F_010000 (stores Ent L161) 4199984) M X :=
  sgX hparse (cellM 427 4199980 rfl rfl (by decide +kernel) R161 F_010000 (stores Ent L161)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 427 4199980 rfl rfl (by decide +kernel) R161 F_010000 (stores Ent L161)) (a := 140737488351024#64) (by decide) (loadInt_look (B := Ent) (L := L161) (b := 140737488351024#64) (v := 0#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s163 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R161 F_010000 (stores Ent L161) 4199984) M X (· = mk R164 F_010000 (stores Ent L161) 4199991) M X :=
  sgX hparse (cellM 428 4199984 rfl rfl (by decide +kernel) R161 F_010000 (stores Ent L161)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 428 4199984 rfl rfl (by decide +kernel) R161 F_010000 (stores Ent L161)) (by decide) (by decide) rfl))

theorem s164 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R164 F_010000 (stores Ent L161) 4199991) M X (· = mk R164 F_010100 (stores Ent L161) 4199994) M X :=
  sgX hparse (cellM 429 4199991 rfl rfl (by decide +kernel) R164 F_010000 (stores Ent L161)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 429 4199991 rfl rfl (by decide +kernel) R164 F_010000 (stores Ent L161)) (by decide) (by decide) rfl))

theorem s165 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R164 F_010100 (stores Ent L161) 4199994) M X (· = mk R164 F_010100 (stores Ent L161) 4199998) M X :=
  sgX hparse (cellM 430 4199994 rfl rfl (by decide +kernel) R164 F_010100 (stores Ent L161)) (by intro _ _ h; cases h) (by decide) (lf (hx_jccT (cellM 430 4199994 rfl rfl (by decide +kernel) R164 F_010100 (stores Ent L161)) (by decide) lab__Lscc_rt_stack_take_locked15))

theorem s166 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R164 F_010100 (stores Ent L161) 4199998) M X (· = mk R167 F_010100 (stores Ent L161) 4200002) M X :=
  sgX hparse (cellM 433 4199998 rfl rfl (by decide +kernel) R164 F_010100 (stores Ent L161)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 433 4199998 rfl rfl (by decide +kernel) R164 F_010100 (stores Ent L161)) (a := 140737488351056#64) (by decide) (loadInt_look (B := Ent) (L := L161) (b := 140737488351056#64) (v := 4225808#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s167 (hparse : Parse) {X : Kernel.KState} :
    Sg (· = mk R167 F_010100 (stores Ent L161) 4200002) M160 X (· = mk R167 F_010100 (stores Ent L161) 4200005) M160 X :=
  sgLdSh hparse (cellM 434 4200002 rfl rfl (by decide +kernel) R167 F_010100 (stores Ent L161)) (by decide) (a := 4225808#64) ((eaddr_reg_disp _ _ _ _).trans (by decide)) ((loadInt_look_none (B := Ent) (L := L161) (b := 4225808#64) (by decide) (by decide) (by decide)).trans (ent_none (by decide))) (val := 0#128) (by decide) (by decide) rfl

theorem s168 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R167 F_010100 (stores Ent L161) 4200005) M X (· = mk R167 F_010100 (stores Ent L168) 4200009) M X :=
  sgX hparse (cellM 435 4200005 rfl rfl (by decide +kernel) R167 F_010100 (stores Ent L161)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 435 4200005 rfl rfl (by decide +kernel) R167 F_010100 (stores Ent L161)) (a := 140737488351016#64) (v := 0#64) (by decide) (ex_look (B := Ent) (L := L161) (b := 140737488351016#64) (v := 68719480067#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s169 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R167 F_010100 (stores Ent L168) 4200009) M X (· = mk R167 F_010100 (stores Ent L168) 4200013) M X :=
  sgX hparse (cellM 436 4200009 rfl rfl (by decide +kernel) R167 F_010100 (stores Ent L168)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 436 4200009 rfl rfl (by decide +kernel) R167 F_010100 (stores Ent L168)) (a := 140737488351016#64) (by decide) (loadInt_look (B := Ent) (L := L168) (b := 140737488351016#64) (v := 0#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s170 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R167 F_010100 (stores Ent L168) 4200013) M X (· = mk R164 F_010100 (stores Ent L168) 4200020) M X :=
  sgX hparse (cellM 437 4200013 rfl rfl (by decide +kernel) R167 F_010100 (stores Ent L168)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 437 4200013 rfl rfl (by decide +kernel) R167 F_010100 (stores Ent L168)) (by decide) (by decide) rfl))

theorem s171 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R164 F_010100 (stores Ent L168) 4200020) M X (· = mk R164 F_010100 (stores Ent L168) 4200023) M X :=
  sgX hparse (cellM 438 4200020 rfl rfl (by decide +kernel) R164 F_010100 (stores Ent L168)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 438 4200020 rfl rfl (by decide +kernel) R164 F_010100 (stores Ent L168)) (by decide) (by decide) rfl))

theorem s172 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R164 F_010100 (stores Ent L168) 4200023) M X (· = mk R164 F_010100 (stores Ent L168) 4200139) M X :=
  sgX hparse (cellM 439 4200023 rfl rfl (by decide +kernel) R164 F_010100 (stores Ent L168)) (by intro _ _ h; cases h) (by decide) (lf (hx_jccT (cellM 439 4200023 rfl rfl (by decide +kernel) R164 F_010100 (stores Ent L168)) (by decide) lab__Lscc_rt_stack_take_bump))

theorem s173 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R164 F_010100 (stores Ent L168) 4200139) M X (· = mk R156 F_010100 (stores Ent L168) 4200146) M X :=
  sgX hparse (cellM 467 4200139 rfl rfl (by decide +kernel) R164 F_010100 (stores Ent L168)) (by intro _ _ h; cases h) (by decide) (lf (hx_leaRip (cellM 467 4200139 rfl rfl (by decide +kernel) R164 F_010100 (stores Ent L168)) lab_scc_rt_stack_lock (by decide) rfl))

theorem s174 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R156 F_010100 (stores Ent L168) 4200146) M X (· = mk R156 F_010100 (stores Ent L174) 4200153) M X :=
  sgX hparse (cellM 468 4200146 rfl rfl (by decide +kernel) R156 F_010100 (stores Ent L168)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 468 4200146 rfl rfl (by decide +kernel) R156 F_010100 (stores Ent L168)) (a := 140737488350968#64) (v := 4225800#64) (by decide) (ex_base (B := Ent) (L := L168) (b := 140737488350968#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s175 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R156 F_010100 (stores Ent L174) 4200153) M X (· = mk R159 F_010100 (stores Ent L174) 4200160) M X :=
  sgX hparse (cellM 469 4200153 rfl rfl (by decide +kernel) R156 F_010100 (stores Ent L174)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 469 4200153 rfl rfl (by decide +kernel) R156 F_010100 (stores Ent L174)) (a := 140737488350968#64) (by decide) (loadInt_look (B := Ent) (L := L174) (b := 140737488350968#64) (v := 4225800#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s176 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R159 F_010100 (stores Ent L174) 4200160) M X (· = mk R161 F_010100 (stores Ent L174) 4200167) M X :=
  sgX hparse (cellM 470 4200160 rfl rfl (by decide +kernel) R159 F_010100 (stores Ent L174)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 470 4200160 rfl rfl (by decide +kernel) R159 F_010100 (stores Ent L174)) (by decide) (by decide) rfl))

theorem s177 (hparse : Parse) {X : Kernel.KState} :
    Sg (· = mk R161 F_010100 (stores Ent L174) 4200167) M160 X (· = mk R161 F_010100 (stores Ent L174) 4200170) M177 X :=
  sgStSh hparse (cellM 471 4200167 rfl rfl (by decide +kernel) R161 F_010100 (stores Ent L174)) (by decide) (a := 4225800#64) ((eaddr_reg_disp _ _ _ _).trans (by decide)) ((loadInt_look_none (B := Ent) (L := L174) (b := 4225800#64) (by decide) (by decide) (by decide)).trans (ent_none (by decide))) (val := 0#128) (by decide) rfl

theorem s178 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R161 F_010100 (stores Ent L174) 4200170) M X (· = mk R179 F_010100 (stores Ent L174) 4200177) M X :=
  sgX hparse (cellM 472 4200170 rfl rfl (by decide +kernel) R161 F_010100 (stores Ent L174)) (by intro _ _ h; cases h) (by decide) (lf (hx_leaRip (cellM 472 4200170 rfl rfl (by decide +kernel) R161 F_010100 (stores Ent L174)) lab_scc_rt_stack_next (by decide) rfl))

theorem s179 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R179 F_010100 (stores Ent L174) 4200177) M X (· = mk R179 F_010100 (stores Ent L179) 4200184) M X :=
  sgX hparse (cellM 473 4200177 rfl rfl (by decide +kernel) R179 F_010100 (stores Ent L174)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 473 4200177 rfl rfl (by decide +kernel) R179 F_010100 (stores Ent L174)) (a := 140737488350960#64) (v := 4225792#64) (by decide) (ex_base (B := Ent) (L := L174) (b := 140737488350960#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

/-- **Steps 144 … 179.** -/
theorem c5 (hparse : Parse) {X : Kernel.KState} :
    Sg (· = mk R144 F_010100 (stores Ent L136) 4199904) M103 X (· = mk R179 F_010100 (stores Ent L179) 4200184) M177 X :=
  SegP.trans (s144 hparse) <|
  SegP.trans (s145 hparse) <|
  SegP.trans (s146 hparse) <|
  SegP.trans (s147 hparse) <|
  SegP.trans (s148 hparse) <|
  SegP.trans (s149 hparse) <|
  SegP.trans (s150 hparse) <|
  SegP.trans (s151 hparse) <|
  SegP.trans (s152 hparse) <|
  SegP.trans (s153 hparse) <|
  SegP.trans (s154 hparse) <|
  SegP.trans (s155 hparse) <|
  SegP.trans (s156 hparse) <|
  SegP.trans (s157 hparse) <|
  SegP.trans (s158 hparse) <|
  SegP.trans (s159 hparse) <|
  SegP.trans (s160 hparse) <|
  SegP.trans (s161 hparse) <|
  SegP.trans (s162 hparse) <|
  SegP.trans (s163 hparse) <|
  SegP.trans (s164 hparse) <|
  SegP.trans (s165 hparse) <|
  SegP.trans (s166 hparse) <|
  SegP.trans (s167 hparse) <|
  SegP.trans (s168 hparse) <|
  SegP.trans (s169 hparse) <|
  SegP.trans (s170 hparse) <|
  SegP.trans (s171 hparse) <|
  SegP.trans (s172 hparse) <|
  SegP.trans (s173 hparse) <|
  SegP.trans (s174 hparse) <|
  SegP.trans (s175 hparse) <|
  SegP.trans (s176 hparse) <|
  SegP.trans (s177 hparse) <|
  SegP.trans (s178 hparse) <|
  (s179 hparse)

/-- info: 'Spike.Test.HelloRootL0XClosed.c5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.c5

end Spike.Test.HelloRootL0XClosed
