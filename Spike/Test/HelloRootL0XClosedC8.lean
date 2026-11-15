/-
**`hello.w` on x86-64, the closed run, chunk 8**: steps 252 … 282 of
thread 0 from the load (`HelloRootL0XClosedStep`), one `SegP` segment per
instruction, composed into `c8`.

Generated from the reference run of the program (the states before every
step: registers `R…`, flags `F_…` (`cf pf af zf sf of`), private memory the
entry stack after the 8-byte stores `L…` (after the take: the taken copy
`B2` after `N…`), shared memory the write chain `M…`). Every step is proved,
not trusted: the generator only chooses the lemma and the witnesses.
-/
import Spike.Test.HelloRootL0XClosedC7

namespace Spike.Test.HelloRootL0XClosed

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Test.HelloLinkedX64 (Λe)
open Spike.Lib.Fwd

set_option maxRecDepth 100000

abbrev R255 : Reg64s := { rax := 72039152, rcx := 4198520, rsi := 71859016, rdi := 71859016, rsp := 72039152, rbp := 72039216, r10 := 8, r11 := 72026944, fsBase := 71859016 }
abbrev R257 : Reg64s := { rax := 72039152, rcx := 4198520, rsi := 71859016, rdi := 71859016, rsp := 72039144, rbp := 72039216, r10 := 8, r11 := 72026944, fsBase := 71859016 }
abbrev R258 : Reg64s := { rax := 72039152, rcx := 4198520, rsi := 71859016, rdi := 71859016, rsp := 72039136, rbp := 72039216, r10 := 8, r11 := 72026944, fsBase := 71859016 }
abbrev R259 : Reg64s := { rax := 72039152, rcx := 4198520, rsi := 71859016, rdi := 71859016, rsp := 72039136, rbp := 72039136, r10 := 8, r11 := 72026944, fsBase := 71859016 }
abbrev R260 : Reg64s := { rax := 72039104, rcx := 4198520, rsi := 71859016, rdi := 71859016, rsp := 72039136, rbp := 72039136, r10 := 8, r11 := 72026944, fsBase := 71859016 }
abbrev R264 : Reg64s := { rax := 72039104, rcx := 4198520, rsi := 71859016, rdi := 71859016, rsp := 72039104, rbp := 72039136, r10 := 8, r11 := 72026944, fsBase := 71859016 }
abbrev R265 : Reg64s := { rax := 72039104, rcx := 4198520, rsi := 71859016, rdi := 257, rsp := 72039104, rbp := 72039136, r10 := 8, r11 := 72026944, fsBase := 71859016 }
abbrev R266 : Reg64s := { rax := 72039104, rcx := 4198520, rsi := 2, rdi := 257, rsp := 72039104, rbp := 72039136, r10 := 8, r11 := 72026944, fsBase := 71859016 }
abbrev R267 : Reg64s := { rax := 72039104, rcx := 4198520, rdx := 3, rsi := 2, rdi := 257, rsp := 72039104, rbp := 72039136, r10 := 8, r11 := 72026944, fsBase := 71859016 }
abbrev R268 : Reg64s := { rax := 72039104, rcx := 4198520, rdx := 3, rsi := 2, rdi := 257, rsp := 72039096, rbp := 72039136, r10 := 8, r11 := 72026944, fsBase := 71859016 }
abbrev R269 : Reg64s := { rax := 72039104, rcx := 4198520, rdx := 3, rsi := 2, rdi := 257, rsp := 72039088, rbp := 72039136, r10 := 8, r11 := 72026944, fsBase := 71859016 }
abbrev R270 : Reg64s := { rax := 72039104, rcx := 4198520, rdx := 3, rsi := 2, rdi := 257, rsp := 72039088, rbp := 72039088, r10 := 8, r11 := 72026944, fsBase := 71859016 }
abbrev R271 : Reg64s := { rax := 72039104, rcx := 4198520, rdx := 3, rsi := 2, rdi := 257, rsp := 72038944, rbp := 72039088, r10 := 8, r11 := 72026944, fsBase := 71859016 }
abbrev R275 : Reg64s := { rax := 2, rcx := 4198520, rdx := 3, rsi := 2, rdi := 257, rsp := 72038944, rbp := 72039088, r10 := 8, r11 := 72026944, fsBase := 71859016 }
abbrev R276 : Reg64s := { rax := 2, rcx := 268435456, rdx := 3, rsi := 2, rdi := 257, rsp := 72038944, rbp := 72039088, r10 := 8, r11 := 72026944, fsBase := 71859016 }
abbrev R280 : Reg64s := { rax := 4225760, rcx := 268435456, rdx := 3, rsi := 2, rdi := 257, rsp := 72038944, rbp := 72039088, r10 := 8, r11 := 72026944, fsBase := 71859016 }
abbrev R282 : Reg64s := { rax := 4225760, rcx := 4225760, rdx := 3, rsi := 2, rdi := 257, rsp := 72038944, rbp := 72039088, r10 := 8, r11 := 72026944, fsBase := 71859016 }
abbrev R283 : Reg64s := { rax := 3, rcx := 4225760, rdx := 3, rsi := 2, rdi := 257, rsp := 72038944, rbp := 72039088, r10 := 8, r11 := 72026944, fsBase := 71859016 }
abbrev N255 : List (BitVec 64 × BitVec 64) := (72039208#64, 71859016#64) :: N248
abbrev N256 : List (BitVec 64 × BitVec 64) := (72039144#64, 4198576#64) :: N255
abbrev N257 : List (BitVec 64 × BitVec 64) := (72039136#64, 72039216#64) :: N256
abbrev N267 : List (BitVec 64 × BitVec 64) := (72039096#64, 4203222#64) :: N257
abbrev N268 : List (BitVec 64 × BitVec 64) := (72039088#64, 72039136#64) :: N267
abbrev N271 : List (BitVec 64 × BitVec 64) := (72039080#64, 257#64) :: N268
abbrev N272 : List (BitVec 64 × BitVec 64) := (72039072#64, 2#64) :: N271
abbrev N273 : List (BitVec 64 × BitVec 64) := (72039064#64, 3#64) :: N272
abbrev N280 : List (BitVec 64 × BitVec 64) := (72039056#64, 4225760#64) :: N273

/-! ## Steps -/

theorem s252 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R252 F_010100 (stores B2 N248) 4198558) M X (· = mk R252 F_000000 (stores B2 N248) 4198561) M X :=
  sgX hparse (cellM 45 4198558 rfl rfl (by decide +kernel) R252 F_010100 (stores B2 N248)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 45 4198558 rfl rfl (by decide +kernel) R252 F_010100 (stores B2 N248)) (by decide) (by decide) rfl))

theorem s253 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R252 F_000000 (stores B2 N248) 4198561) M X (· = mk R252 F_000000 (stores B2 N248) 4198563) M X :=
  sgX hparse (cellM 46 4198561 rfl rfl (by decide +kernel) R252 F_000000 (stores B2 N248)) (by intro _ _ h; cases h) (by decide) (lf (hx_jccN (cellM 46 4198561 rfl rfl (by decide +kernel) R252 F_000000 (stores B2 N248)) (by decide) rfl))

theorem s254 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R252 F_000000 (stores B2 N248) 4198563) M X (· = mk R255 F_010000 (stores B2 N248) 4198567) M X :=
  sgX hparse (cellM 47 4198563 rfl rfl (by decide +kernel) R252 F_000000 (stores B2 N248)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 47 4198563 rfl rfl (by decide +kernel) R252 F_000000 (stores B2 N248)) (by decide) (by decide) rfl))

theorem s255 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R255 F_010000 (stores B2 N248) 4198567) M X (· = mk R255 F_010000 (stores B2 N255) 4198571) M X :=
  sgX hparse (cellM 48 4198567 rfl rfl (by decide +kernel) R255 F_010000 (stores B2 N248)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 48 4198567 rfl rfl (by decide +kernel) R255 F_010000 (stores B2 N248)) (a := 72039208#64) (v := 71859016#64) (by decide) ⟨_, (loadInt_look_none (B := B2) (L := N248) (b := 72039208#64) (by decide) (by decide) (by decide)).trans (copy_in (by decide) (by decide))⟩ (by decide) rfl))

theorem s256 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R255 F_010000 (stores B2 N255) 4198571) M X (· = mk R257 F_010000 (stores B2 N256) 4203169) M X :=
  sgX hparse (cellM 50 4198571 rfl rfl (by decide +kernel) R255 F_010000 (stores B2 N255)) (by intro _ _ h; cases h) (by decide) (lf (hx_call (cellM 50 4198571 rfl rfl (by decide +kernel) R255 F_010000 (stores B2 N255)) lab_wc_rodata (a := 72039144#64) (v := 4198576#64) (by decide) ⟨_, (loadInt_look_none (B := B2) (L := N255) (b := 72039144#64) (by decide) (by decide) (by decide)).trans (copy_in (by decide) (by decide))⟩ (by decide) (by decide)))

theorem s257 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R257 F_010000 (stores B2 N256) 4203169) M X (· = mk R258 F_010000 (stores B2 N257) 4203170) M X :=
  sgX hparse (cellM 1262 4203169 rfl rfl (by decide +kernel) R257 F_010000 (stores B2 N256)) (by intro _ _ h; cases h) (by decide) (lf (hx_push (cellM 1262 4203169 rfl rfl (by decide +kernel) R257 F_010000 (stores B2 N256)) (a := 72039136#64) (v := 72039216#64) (by decide) ⟨_, (loadInt_look_none (B := B2) (L := N256) (b := 72039136#64) (by decide) (by decide) (by decide)).trans (copy_in (by decide) (by decide))⟩ (by decide) (by decide) rfl))

theorem s258 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R258 F_010000 (stores B2 N257) 4203170) M X (· = mk R259 F_010000 (stores B2 N257) 4203173) M X :=
  sgX hparse (cellM 1263 4203170 rfl rfl (by decide +kernel) R258 F_010000 (stores B2 N257)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 1263 4203170 rfl rfl (by decide +kernel) R258 F_010000 (stores B2 N257)) (by decide) (by decide) rfl))

theorem s259 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R259 F_010000 (stores B2 N257) 4203173) M X (· = mk R260 F_010000 (stores B2 N257) 4203178) M X :=
  sgX hparse (cellM 1265 4203173 rfl rfl (by decide +kernel) R259 F_010000 (stores B2 N257)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 1265 4203173 rfl rfl (by decide +kernel) R259 F_010000 (stores B2 N257)) (by decide) (by decide) rfl))

theorem s260 (hparse : Parse) {X : Kernel.KState} :
    Sg (· = mk R260 F_010000 (stores B2 N257) 4203178) M233 X (· = mk R260 F_010000 (stores B2 N257) 4203187) M233 X :=
  sgFsSh hparse (cellM 1266 4203178 rfl rfl (by decide +kernel) R260 F_010000 (stores B2 N257)) (by decide) (a := 71859024#64) (by decide) ((loadInt_look_none (B := B2) (L := N257) (b := 71859024#64) (by decide) (by decide) (by decide)).trans ((copy_out (by decide) (by decide) (by decide)).trans ((loadInt_look_none (B := Ent) (L := Llast) (b := 71859024#64) (by decide) (by decide) (by decide)).trans (ent_none (by decide))))) (val := 72026944#128) (by decide) (by decide) rfl

theorem s261 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R260 F_010000 (stores B2 N257) 4203187) M X (· = mk R260 F_000000 (stores B2 N257) 4203190) M X :=
  sgX hparse (cellM 1267 4203187 rfl rfl (by decide +kernel) R260 F_010000 (stores B2 N257)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 1267 4203187 rfl rfl (by decide +kernel) R260 F_010000 (stores B2 N257)) (by decide) (by decide) rfl))

theorem s262 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R260 F_000000 (stores B2 N257) 4203190) M X (· = mk R260 F_000000 (stores B2 N257) 4203192) M X :=
  sgX hparse (cellM 1268 4203190 rfl rfl (by decide +kernel) R260 F_000000 (stores B2 N257)) (by intro _ _ h; cases h) (by decide) (lf (hx_jccN (cellM 1268 4203190 rfl rfl (by decide +kernel) R260 F_000000 (stores B2 N257)) (by decide) rfl))

theorem s263 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R260 F_000000 (stores B2 N257) 4203192) M X (· = mk R264 F_010000 (stores B2 N257) 4203196) M X :=
  sgX hparse (cellM 1269 4203192 rfl rfl (by decide +kernel) R260 F_000000 (stores B2 N257)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 1269 4203192 rfl rfl (by decide +kernel) R260 F_000000 (stores B2 N257)) (by decide) (by decide) rfl))

theorem s264 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R264 F_010000 (stores B2 N257) 4203196) M X (· = mk R265 F_010000 (stores B2 N257) 4203203) M X :=
  sgX hparse (cellM 1271 4203196 rfl rfl (by decide +kernel) R264 F_010000 (stores B2 N257)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 1271 4203196 rfl rfl (by decide +kernel) R264 F_010000 (stores B2 N257)) (by decide) (by decide) rfl))

theorem s265 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R265 F_010000 (stores B2 N257) 4203203) M X (· = mk R266 F_010000 (stores B2 N257) 4203210) M X :=
  sgX hparse (cellM 1272 4203203 rfl rfl (by decide +kernel) R265 F_010000 (stores B2 N257)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 1272 4203203 rfl rfl (by decide +kernel) R265 F_010000 (stores B2 N257)) (by decide) (by decide) rfl))

theorem s266 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R266 F_010000 (stores B2 N257) 4203210) M X (· = mk R267 F_010000 (stores B2 N257) 4203217) M X :=
  sgX hparse (cellM 1273 4203210 rfl rfl (by decide +kernel) R266 F_010000 (stores B2 N257)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 1273 4203210 rfl rfl (by decide +kernel) R266 F_010000 (stores B2 N257)) (by decide) (by decide) rfl))

theorem s267 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R267 F_010000 (stores B2 N257) 4203217) M X (· = mk R268 F_010000 (stores B2 N267) 4198666) M X :=
  sgX hparse (cellM 1274 4203217 rfl rfl (by decide +kernel) R267 F_010000 (stores B2 N257)) (by intro _ _ h; cases h) (by decide) (lf (hx_call (cellM 1274 4203217 rfl rfl (by decide +kernel) R267 F_010000 (stores B2 N257)) lab_scc_rt_alloc (a := 72039096#64) (v := 4203222#64) (by decide) ⟨_, (loadInt_look_none (B := B2) (L := N257) (b := 72039096#64) (by decide) (by decide) (by decide)).trans (copy_in (by decide) (by decide))⟩ (by decide) (by decide)))

theorem s268 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R268 F_010000 (stores B2 N267) 4198666) M X (· = mk R269 F_010000 (stores B2 N268) 4198667) M X :=
  sgX hparse (cellM 87 4198666 rfl rfl (by decide +kernel) R268 F_010000 (stores B2 N267)) (by intro _ _ h; cases h) (by decide) (lf (hx_push (cellM 87 4198666 rfl rfl (by decide +kernel) R268 F_010000 (stores B2 N267)) (a := 72039088#64) (v := 72039136#64) (by decide) ⟨_, (loadInt_look_none (B := B2) (L := N267) (b := 72039088#64) (by decide) (by decide) (by decide)).trans (copy_in (by decide) (by decide))⟩ (by decide) (by decide) rfl))

theorem s269 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R269 F_010000 (stores B2 N268) 4198667) M X (· = mk R270 F_010000 (stores B2 N268) 4198670) M X :=
  sgX hparse (cellM 88 4198667 rfl rfl (by decide +kernel) R269 F_010000 (stores B2 N268)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 88 4198667 rfl rfl (by decide +kernel) R269 F_010000 (stores B2 N268)) (by decide) (by decide) rfl))

theorem s270 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R270 F_010000 (stores B2 N268) 4198670) M X (· = mk R271 F_000000 (stores B2 N268) 4198677) M X :=
  sgX hparse (cellM 89 4198670 rfl rfl (by decide +kernel) R270 F_010000 (stores B2 N268)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 89 4198670 rfl rfl (by decide +kernel) R270 F_010000 (stores B2 N268)) (by decide) (by decide) rfl))

theorem s271 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R271 F_000000 (stores B2 N268) 4198677) M X (· = mk R271 F_000000 (stores B2 N271) 4198681) M X :=
  sgX hparse (cellM 90 4198677 rfl rfl (by decide +kernel) R271 F_000000 (stores B2 N268)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 90 4198677 rfl rfl (by decide +kernel) R271 F_000000 (stores B2 N268)) (a := 72039080#64) (v := 257#64) (by decide) ⟨_, (loadInt_look_none (B := B2) (L := N268) (b := 72039080#64) (by decide) (by decide) (by decide)).trans (copy_in (by decide) (by decide))⟩ (by decide) rfl))

theorem s272 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R271 F_000000 (stores B2 N271) 4198681) M X (· = mk R271 F_000000 (stores B2 N272) 4198685) M X :=
  sgX hparse (cellM 91 4198681 rfl rfl (by decide +kernel) R271 F_000000 (stores B2 N271)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 91 4198681 rfl rfl (by decide +kernel) R271 F_000000 (stores B2 N271)) (a := 72039072#64) (v := 2#64) (by decide) ⟨_, (loadInt_look_none (B := B2) (L := N271) (b := 72039072#64) (by decide) (by decide) (by decide)).trans (copy_in (by decide) (by decide))⟩ (by decide) rfl))

theorem s273 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R271 F_000000 (stores B2 N272) 4198685) M X (· = mk R271 F_000000 (stores B2 N273) 4198689) M X :=
  sgX hparse (cellM 92 4198685 rfl rfl (by decide +kernel) R271 F_000000 (stores B2 N272)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 92 4198685 rfl rfl (by decide +kernel) R271 F_000000 (stores B2 N272)) (a := 72039064#64) (v := 3#64) (by decide) ⟨_, (loadInt_look_none (B := B2) (L := N272) (b := 72039064#64) (by decide) (by decide) (by decide)).trans (copy_in (by decide) (by decide))⟩ (by decide) rfl))

theorem s274 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R271 F_000000 (stores B2 N273) 4198689) M X (· = mk R275 F_000000 (stores B2 N273) 4198693) M X :=
  sgX hparse (cellM 94 4198689 rfl rfl (by decide +kernel) R271 F_000000 (stores B2 N273)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 94 4198689 rfl rfl (by decide +kernel) R271 F_000000 (stores B2 N273)) (a := 72039072#64) (by decide) (loadInt_look (B := B2) (L := N273) (b := 72039072#64) (v := 2#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s275 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R275 F_000000 (stores B2 N273) 4198693) M X (· = mk R276 F_000000 (stores B2 N273) 4198700) M X :=
  sgX hparse (cellM 95 4198693 rfl rfl (by decide +kernel) R275 F_000000 (stores B2 N273)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 95 4198693 rfl rfl (by decide +kernel) R275 F_000000 (stores B2 N273)) (by decide) (by decide) rfl))

theorem s276 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R276 F_000000 (stores B2 N273) 4198700) M X (· = mk R276 F_100010 (stores B2 N273) 4198703) M X :=
  sgX hparse (cellM 96 4198700 rfl rfl (by decide +kernel) R276 F_000000 (stores B2 N273)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 96 4198700 rfl rfl (by decide +kernel) R276 F_000000 (stores B2 N273)) (by decide) (by decide) rfl))

theorem s277 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R276 F_100010 (stores B2 N273) 4198703) M X (· = mk R276 F_100010 (stores B2 N273) 4198705) M X :=
  sgX hparse (cellM 97 4198703 rfl rfl (by decide +kernel) R276 F_100010 (stores B2 N273)) (by intro _ _ h; cases h) (by decide) (lf (hx_jccN (cellM 97 4198703 rfl rfl (by decide +kernel) R276 F_100010 (stores B2 N273)) (by decide) rfl))

theorem s278 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R276 F_100010 (stores B2 N273) 4198705) M X (· = mk R276 F_100010 (stores B2 N273) 4198707) M X :=
  sgX hparse (cellM 98 4198705 rfl rfl (by decide +kernel) R276 F_100010 (stores B2 N273)) (by intro _ _ h; cases h) (by decide) (lf (hx_jmp (cellM 98 4198705 rfl rfl (by decide +kernel) R276 F_100010 (stores B2 N273)) lab__Lscc_rt_alloc_cnt))

theorem s279 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R276 F_100010 (stores B2 N273) 4198707) M X (· = mk R280 F_100010 (stores B2 N273) 4198714) M X :=
  sgX hparse (cellM 100 4198707 rfl rfl (by decide +kernel) R276 F_100010 (stores B2 N273)) (by intro _ _ h; cases h) (by decide) (lf (hx_leaRip (cellM 100 4198707 rfl rfl (by decide +kernel) R276 F_100010 (stores B2 N273)) lab_scc_rt_heap_use (by decide) rfl))

theorem s280 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R280 F_100010 (stores B2 N273) 4198714) M X (· = mk R280 F_100010 (stores B2 N280) 4198718) M X :=
  sgX hparse (cellM 101 4198714 rfl rfl (by decide +kernel) R280 F_100010 (stores B2 N273)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 101 4198714 rfl rfl (by decide +kernel) R280 F_100010 (stores B2 N273)) (a := 72039056#64) (v := 4225760#64) (by decide) ⟨_, (loadInt_look_none (B := B2) (L := N273) (b := 72039056#64) (by decide) (by decide) (by decide)).trans (copy_in (by decide) (by decide))⟩ (by decide) rfl))

theorem s281 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R280 F_100010 (stores B2 N280) 4198718) M X (· = mk R282 F_100010 (stores B2 N280) 4198722) M X :=
  sgX hparse (cellM 102 4198718 rfl rfl (by decide +kernel) R280 F_100010 (stores B2 N280)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 102 4198718 rfl rfl (by decide +kernel) R280 F_100010 (stores B2 N280)) (a := 72039056#64) (by decide) (loadInt_look (B := B2) (L := N280) (b := 72039056#64) (v := 4225760#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s282 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R282 F_100010 (stores B2 N280) 4198722) M X (· = mk R283 F_100010 (stores B2 N280) 4198726) M X :=
  sgX hparse (cellM 103 4198722 rfl rfl (by decide +kernel) R282 F_100010 (stores B2 N280)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 103 4198722 rfl rfl (by decide +kernel) R282 F_100010 (stores B2 N280)) (a := 72039064#64) (by decide) (loadInt_look (B := B2) (L := N280) (b := 72039064#64) (v := 3#64) (by decide) (by decide) (by decide)) (by decide) rfl))

/-- **Steps 252 … 282.** -/
theorem c8 (hparse : Parse) {X : Kernel.KState} :
    Sg (· = mk R252 F_010100 (stores B2 N248) 4198558) M233 X (· = mk R283 F_100010 (stores B2 N280) 4198726) M233 X :=
  SegP.trans (s252 hparse) <|
  SegP.trans (s253 hparse) <|
  SegP.trans (s254 hparse) <|
  SegP.trans (s255 hparse) <|
  SegP.trans (s256 hparse) <|
  SegP.trans (s257 hparse) <|
  SegP.trans (s258 hparse) <|
  SegP.trans (s259 hparse) <|
  SegP.trans (s260 hparse) <|
  SegP.trans (s261 hparse) <|
  SegP.trans (s262 hparse) <|
  SegP.trans (s263 hparse) <|
  SegP.trans (s264 hparse) <|
  SegP.trans (s265 hparse) <|
  SegP.trans (s266 hparse) <|
  SegP.trans (s267 hparse) <|
  SegP.trans (s268 hparse) <|
  SegP.trans (s269 hparse) <|
  SegP.trans (s270 hparse) <|
  SegP.trans (s271 hparse) <|
  SegP.trans (s272 hparse) <|
  SegP.trans (s273 hparse) <|
  SegP.trans (s274 hparse) <|
  SegP.trans (s275 hparse) <|
  SegP.trans (s276 hparse) <|
  SegP.trans (s277 hparse) <|
  SegP.trans (s278 hparse) <|
  SegP.trans (s279 hparse) <|
  SegP.trans (s280 hparse) <|
  SegP.trans (s281 hparse) <|
  (s282 hparse)

/-- info: 'Spike.Test.HelloRootL0XClosed.c8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.c8

end Spike.Test.HelloRootL0XClosed
