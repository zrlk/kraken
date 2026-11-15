/-
**`hello.w` on x86-64, the closed run, chunk 7**: steps 216 … 251 of
thread 0 from the load (`HelloRootL0XClosedStep`), one `SegP` segment per
instruction, composed into `c7`.

Generated from the reference run of the program (the states before every
step: registers `R…`, flags `F_…` (`cf pf af zf sf of`), private memory the
entry stack after the 8-byte stores `L…` (after the take: the taken copy
`B2` after `N…`), shared memory the write chain `M…`). Every step is proved,
not trusted: the generator only chooses the lemma and the witnesses.
-/
import Spike.Test.HelloRootL0XClosedC6

namespace Spike.Test.HelloRootL0XClosed

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Test.HelloLinkedX64 (Λe)
open Spike.Lib.Fwd

set_option maxRecDepth 100000

abbrev R217 : Reg64s := { rax := 72039232, rcx := 71859016, rsi := 16384, rdi := 72022848, rsp := 140737488351136, rbp := 140737488351168, r10 := 8 }
abbrev R218 : Reg64s := { rax := 71859016, rcx := 71859016, rsi := 16384, rdi := 72022848, rsp := 140737488351136, rbp := 140737488351168, r10 := 8 }
abbrev R221 : Reg64s := { rax := 72026944, rcx := 71859016, rsi := 16384, rdi := 72022848, rsp := 140737488351136, rbp := 140737488351168, r10 := 8 }
abbrev R224 : Reg64s := { rcx := 71859016, rsi := 16384, rdi := 72022848, rsp := 140737488351136, rbp := 140737488351168, r10 := 8 }
abbrev R230 : Reg64s := { rax := 72022848, rcx := 71859016, rsi := 16384, rdi := 72022848, rsp := 140737488351136, rbp := 140737488351168, r10 := 8 }
abbrev R236 : Reg64s := { rax := 72039232, rcx := 71859016, rsi := 16384, rdi := 72022848, rsp := 140737488351168, rbp := 140737488351168, r10 := 8 }
abbrev R237 : Reg64s := { rax := 72039232, rcx := 71859016, rsi := 16384, rdi := 72022848, rsp := 140737488351176, rbp := 140737488351216, r10 := 8 }
abbrev R238 : Reg64s := { rax := 72039232, rcx := 71859016, rsi := 16384, rdi := 72022848, rsp := 140737488351184, rbp := 140737488351216, r10 := 8 }
abbrev R240 : Reg64s := { rax := 72039232, rcx := 71859016, rsi := 71859016, rdi := 72022848, rsp := 140737488351184, rbp := 140737488351216, r10 := 8 }
abbrev R241 : Reg64s := { rax := 72039232, rcx := 71859016, rsi := 71859016, rdi := 4098, rsp := 140737488351184, rbp := 140737488351216, r10 := 8 }
abbrev R244 : Reg64s := { rax := 72039232, rcx := 4198520, rsi := 71859016, rdi := 4098, rsp := 140737488351184, rbp := 140737488351216, r10 := 8, fsBase := 71859016 }
abbrev R245 : Reg64s := { rax := 72039232, rcx := 4198520, rsi := 71859016, rdi := 71859016, rsp := 140737488351184, rbp := 140737488351216, r10 := 8, fsBase := 71859016 }
abbrev R246 : Reg64s := { rax := 72039232, rcx := 4198520, rsi := 71859016, rdi := 71859016, rsp := 72039232, rbp := 140737488351216, r10 := 8, fsBase := 71859016 }
abbrev R247 : Reg64s := { rax := 72039232, rcx := 4198520, rsi := 71859016, rdi := 71859016, rsp := 72039232, r10 := 8, fsBase := 71859016 }
abbrev R248 : Reg64s := { rax := 72039232, rcx := 4198520, rsi := 71859016, rdi := 71859016, rsp := 72039224, r10 := 8, fsBase := 71859016 }
abbrev R249 : Reg64s := { rax := 72039232, rcx := 4198520, rsi := 71859016, rdi := 71859016, rsp := 72039216, r10 := 8, fsBase := 71859016 }
abbrev R250 : Reg64s := { rax := 72039232, rcx := 4198520, rsi := 71859016, rdi := 71859016, rsp := 72039216, rbp := 72039216, r10 := 8, fsBase := 71859016 }
abbrev R251 : Reg64s := { rax := 72039152, rcx := 4198520, rsi := 71859016, rdi := 71859016, rsp := 72039216, rbp := 72039216, r10 := 8, fsBase := 71859016 }
abbrev R252 : Reg64s := { rax := 72039152, rcx := 4198520, rsi := 71859016, rdi := 71859016, rsp := 72039216, rbp := 72039216, r10 := 8, r11 := 72026944, fsBase := 71859016 }
abbrev N238 : List (BitVec 64 × BitVec 64) := (140737488351184#64, 72039232#64) :: N215
abbrev N247 : List (BitVec 64 × BitVec 64) := (72039224#64, 4198538#64) :: N238
abbrev N248 : List (BitVec 64 × BitVec 64) := (72039216#64, 0#64) :: N247
abbrev M218 : Memory := (M182.append { loc := ⟨71859016#64, 8⟩, val := 71859016#128, tid := 0 }).1
abbrev M221 : Memory := (M218.append { loc := ⟨71859024#64, 8⟩, val := 72026944#128, tid := 0 }).1
abbrev M224 : Memory := (M221.append { loc := ⟨71859032#64, 8⟩, val := 0#128, tid := 0 }).1
abbrev M227 : Memory := (M224.append { loc := ⟨71859040#64, 8⟩, val := 0#128, tid := 0 }).1
abbrev M230 : Memory := (M227.append { loc := ⟨71859048#64, 8⟩, val := 72022848#128, tid := 0 }).1
abbrev M233 : Memory := (M230.append { loc := ⟨71859056#64, 8⟩, val := 72039232#128, tid := 0 }).1

/-! ## Steps -/

theorem s216 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R215 F_000000 (stores B2 N215) 4199646) M X (· = mk R217 F_000000 (stores B2 N215) 4199650) M X :=
  sgX hparse (cellM 340 4199646 rfl rfl (by decide +kernel) R215 F_000000 (stores B2 N215)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 340 4199646 rfl rfl (by decide +kernel) R215 F_000000 (stores B2 N215)) (a := 140737488351160#64) (by decide) ((loadInt_look_none (B := B2) (L := N215) (b := 140737488351160#64) (by decide) (by decide) (by decide)).trans ((copy_out (by decide) (by decide) (by decide)).trans (loadInt_look (B := Ent) (L := Llast) (b := 140737488351160#64) (v := 71859016#64) (by decide) (by decide) (by decide)))) (by decide) rfl))

theorem s217 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R217 F_000000 (stores B2 N215) 4199650) M X (· = mk R218 F_000000 (stores B2 N215) 4199654) M X :=
  sgX hparse (cellM 341 4199650 rfl rfl (by decide +kernel) R217 F_000000 (stores B2 N215)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 341 4199650 rfl rfl (by decide +kernel) R217 F_000000 (stores B2 N215)) (a := 140737488351160#64) (by decide) ((loadInt_look_none (B := B2) (L := N215) (b := 140737488351160#64) (by decide) (by decide) (by decide)).trans ((copy_out (by decide) (by decide) (by decide)).trans (loadInt_look (B := Ent) (L := Llast) (b := 140737488351160#64) (v := 71859016#64) (by decide) (by decide) (by decide)))) (by decide) rfl))

theorem s218 (hparse : Parse) {X : Kernel.KState} :
    Sg (· = mk R218 F_000000 (stores B2 N215) 4199654) M182 X (· = mk R218 F_000000 (stores B2 N215) 4199657) M218 X :=
  sgStSh hparse (cellM 342 4199654 rfl rfl (by decide +kernel) R218 F_000000 (stores B2 N215)) (by decide) (a := 71859016#64) ((eaddr_reg_disp _ _ _ _).trans (by decide)) ((loadInt_look_none (B := B2) (L := N215) (b := 71859016#64) (by decide) (by decide) (by decide)).trans ((copy_out (by decide) (by decide) (by decide)).trans ((loadInt_look_none (B := Ent) (L := Llast) (b := 71859016#64) (by decide) (by decide) (by decide)).trans (ent_none (by decide))))) (val := 71859016#128) (by decide) rfl

theorem s219 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R218 F_000000 (stores B2 N215) 4199657) M X (· = mk R218 F_000000 (stores B2 N215) 4199661) M X :=
  sgX hparse (cellM 343 4199657 rfl rfl (by decide +kernel) R218 F_000000 (stores B2 N215)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 343 4199657 rfl rfl (by decide +kernel) R218 F_000000 (stores B2 N215)) (a := 140737488351160#64) (by decide) ((loadInt_look_none (B := B2) (L := N215) (b := 140737488351160#64) (by decide) (by decide) (by decide)).trans ((copy_out (by decide) (by decide) (by decide)).trans (loadInt_look (B := Ent) (L := Llast) (b := 140737488351160#64) (v := 71859016#64) (by decide) (by decide) (by decide)))) (by decide) rfl))

theorem s220 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R218 F_000000 (stores B2 N215) 4199661) M X (· = mk R221 F_000000 (stores B2 N215) 4199665) M X :=
  sgX hparse (cellM 344 4199661 rfl rfl (by decide +kernel) R218 F_000000 (stores B2 N215)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 344 4199661 rfl rfl (by decide +kernel) R218 F_000000 (stores B2 N215)) (a := 140737488351144#64) (by decide) (loadInt_look (B := B2) (L := N215) (b := 140737488351144#64) (v := 72026944#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s221 (hparse : Parse) {X : Kernel.KState} :
    Sg (· = mk R221 F_000000 (stores B2 N215) 4199665) M218 X (· = mk R221 F_000000 (stores B2 N215) 4199669) M221 X :=
  sgStSh hparse (cellM 345 4199665 rfl rfl (by decide +kernel) R221 F_000000 (stores B2 N215)) (by decide) (a := 71859024#64) ((eaddr_reg_disp _ _ _ _).trans (by decide)) ((loadInt_look_none (B := B2) (L := N215) (b := 71859024#64) (by decide) (by decide) (by decide)).trans ((copy_out (by decide) (by decide) (by decide)).trans ((loadInt_look_none (B := Ent) (L := Llast) (b := 71859024#64) (by decide) (by decide) (by decide)).trans (ent_none (by decide))))) (val := 72026944#128) (by decide) rfl

theorem s222 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R221 F_000000 (stores B2 N215) 4199669) M X (· = mk R221 F_000000 (stores B2 N215) 4199673) M X :=
  sgX hparse (cellM 346 4199669 rfl rfl (by decide +kernel) R221 F_000000 (stores B2 N215)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 346 4199669 rfl rfl (by decide +kernel) R221 F_000000 (stores B2 N215)) (a := 140737488351160#64) (by decide) ((loadInt_look_none (B := B2) (L := N215) (b := 140737488351160#64) (by decide) (by decide) (by decide)).trans ((copy_out (by decide) (by decide) (by decide)).trans (loadInt_look (B := Ent) (L := Llast) (b := 140737488351160#64) (v := 71859016#64) (by decide) (by decide) (by decide)))) (by decide) rfl))

theorem s223 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R221 F_000000 (stores B2 N215) 4199673) M X (· = mk R224 F_000000 (stores B2 N215) 4199680) M X :=
  sgX hparse (cellM 347 4199673 rfl rfl (by decide +kernel) R221 F_000000 (stores B2 N215)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 347 4199673 rfl rfl (by decide +kernel) R221 F_000000 (stores B2 N215)) (by decide) (by decide) rfl))

theorem s224 (hparse : Parse) {X : Kernel.KState} :
    Sg (· = mk R224 F_000000 (stores B2 N215) 4199680) M221 X (· = mk R224 F_000000 (stores B2 N215) 4199684) M224 X :=
  sgStSh hparse (cellM 348 4199680 rfl rfl (by decide +kernel) R224 F_000000 (stores B2 N215)) (by decide) (a := 71859032#64) ((eaddr_reg_disp _ _ _ _).trans (by decide)) ((loadInt_look_none (B := B2) (L := N215) (b := 71859032#64) (by decide) (by decide) (by decide)).trans ((copy_out (by decide) (by decide) (by decide)).trans ((loadInt_look_none (B := Ent) (L := Llast) (b := 71859032#64) (by decide) (by decide) (by decide)).trans (ent_none (by decide))))) (val := 0#128) (by decide) rfl

theorem s225 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R224 F_000000 (stores B2 N215) 4199684) M X (· = mk R224 F_000000 (stores B2 N215) 4199688) M X :=
  sgX hparse (cellM 349 4199684 rfl rfl (by decide +kernel) R224 F_000000 (stores B2 N215)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 349 4199684 rfl rfl (by decide +kernel) R224 F_000000 (stores B2 N215)) (a := 140737488351160#64) (by decide) ((loadInt_look_none (B := B2) (L := N215) (b := 140737488351160#64) (by decide) (by decide) (by decide)).trans ((copy_out (by decide) (by decide) (by decide)).trans (loadInt_look (B := Ent) (L := Llast) (b := 140737488351160#64) (v := 71859016#64) (by decide) (by decide) (by decide)))) (by decide) rfl))

theorem s226 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R224 F_000000 (stores B2 N215) 4199688) M X (· = mk R224 F_000000 (stores B2 N215) 4199695) M X :=
  sgX hparse (cellM 350 4199688 rfl rfl (by decide +kernel) R224 F_000000 (stores B2 N215)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 350 4199688 rfl rfl (by decide +kernel) R224 F_000000 (stores B2 N215)) (by decide) (by decide) rfl))

theorem s227 (hparse : Parse) {X : Kernel.KState} :
    Sg (· = mk R224 F_000000 (stores B2 N215) 4199695) M224 X (· = mk R224 F_000000 (stores B2 N215) 4199699) M227 X :=
  sgStSh hparse (cellM 351 4199695 rfl rfl (by decide +kernel) R224 F_000000 (stores B2 N215)) (by decide) (a := 71859040#64) ((eaddr_reg_disp _ _ _ _).trans (by decide)) ((loadInt_look_none (B := B2) (L := N215) (b := 71859040#64) (by decide) (by decide) (by decide)).trans ((copy_out (by decide) (by decide) (by decide)).trans ((loadInt_look_none (B := Ent) (L := Llast) (b := 71859040#64) (by decide) (by decide) (by decide)).trans (ent_none (by decide))))) (val := 0#128) (by decide) rfl

theorem s228 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R224 F_000000 (stores B2 N215) 4199699) M X (· = mk R224 F_000000 (stores B2 N215) 4199703) M X :=
  sgX hparse (cellM 352 4199699 rfl rfl (by decide +kernel) R224 F_000000 (stores B2 N215)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 352 4199699 rfl rfl (by decide +kernel) R224 F_000000 (stores B2 N215)) (a := 140737488351160#64) (by decide) ((loadInt_look_none (B := B2) (L := N215) (b := 140737488351160#64) (by decide) (by decide) (by decide)).trans ((copy_out (by decide) (by decide) (by decide)).trans (loadInt_look (B := Ent) (L := Llast) (b := 140737488351160#64) (v := 71859016#64) (by decide) (by decide) (by decide)))) (by decide) rfl))

theorem s229 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R224 F_000000 (stores B2 N215) 4199703) M X (· = mk R230 F_000000 (stores B2 N215) 4199707) M X :=
  sgX hparse (cellM 353 4199703 rfl rfl (by decide +kernel) R224 F_000000 (stores B2 N215)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 353 4199703 rfl rfl (by decide +kernel) R224 F_000000 (stores B2 N215)) (a := 140737488351152#64) (by decide) (loadInt_look (B := B2) (L := N215) (b := 140737488351152#64) (v := 72022848#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s230 (hparse : Parse) {X : Kernel.KState} :
    Sg (· = mk R230 F_000000 (stores B2 N215) 4199707) M227 X (· = mk R230 F_000000 (stores B2 N215) 4199711) M230 X :=
  sgStSh hparse (cellM 354 4199707 rfl rfl (by decide +kernel) R230 F_000000 (stores B2 N215)) (by decide) (a := 71859048#64) ((eaddr_reg_disp _ _ _ _).trans (by decide)) ((loadInt_look_none (B := B2) (L := N215) (b := 71859048#64) (by decide) (by decide) (by decide)).trans ((copy_out (by decide) (by decide) (by decide)).trans ((loadInt_look_none (B := Ent) (L := Llast) (b := 71859048#64) (by decide) (by decide) (by decide)).trans (ent_none (by decide))))) (val := 72022848#128) (by decide) rfl

theorem s231 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R230 F_000000 (stores B2 N215) 4199711) M X (· = mk R230 F_000000 (stores B2 N215) 4199715) M X :=
  sgX hparse (cellM 355 4199711 rfl rfl (by decide +kernel) R230 F_000000 (stores B2 N215)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 355 4199711 rfl rfl (by decide +kernel) R230 F_000000 (stores B2 N215)) (a := 140737488351160#64) (by decide) ((loadInt_look_none (B := B2) (L := N215) (b := 140737488351160#64) (by decide) (by decide) (by decide)).trans ((copy_out (by decide) (by decide) (by decide)).trans (loadInt_look (B := Ent) (L := Llast) (b := 140737488351160#64) (v := 71859016#64) (by decide) (by decide) (by decide)))) (by decide) rfl))

theorem s232 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R230 F_000000 (stores B2 N215) 4199715) M X (· = mk R217 F_000000 (stores B2 N215) 4199719) M X :=
  sgX hparse (cellM 356 4199715 rfl rfl (by decide +kernel) R230 F_000000 (stores B2 N215)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 356 4199715 rfl rfl (by decide +kernel) R230 F_000000 (stores B2 N215)) (a := 140737488351136#64) (by decide) (loadInt_look (B := B2) (L := N215) (b := 140737488351136#64) (v := 72039232#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s233 (hparse : Parse) {X : Kernel.KState} :
    Sg (· = mk R217 F_000000 (stores B2 N215) 4199719) M230 X (· = mk R217 F_000000 (stores B2 N215) 4199723) M233 X :=
  sgStSh hparse (cellM 357 4199719 rfl rfl (by decide +kernel) R217 F_000000 (stores B2 N215)) (by decide) (a := 71859056#64) ((eaddr_reg_disp _ _ _ _).trans (by decide)) ((loadInt_look_none (B := B2) (L := N215) (b := 71859056#64) (by decide) (by decide) (by decide)).trans ((copy_out (by decide) (by decide) (by decide)).trans ((loadInt_look_none (B := Ent) (L := Llast) (b := 71859056#64) (by decide) (by decide) (by decide)).trans (ent_none (by decide))))) (val := 72039232#128) (by decide) rfl

theorem s234 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R217 F_000000 (stores B2 N215) 4199723) M X (· = mk R217 F_000000 (stores B2 N215) 4199727) M X :=
  sgX hparse (cellM 358 4199723 rfl rfl (by decide +kernel) R217 F_000000 (stores B2 N215)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 358 4199723 rfl rfl (by decide +kernel) R217 F_000000 (stores B2 N215)) (a := 140737488351136#64) (by decide) (loadInt_look (B := B2) (L := N215) (b := 140737488351136#64) (v := 72039232#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s235 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R217 F_000000 (stores B2 N215) 4199727) M X (· = mk R236 F_000000 (stores B2 N215) 4199730) M X :=
  sgX hparse (cellM 359 4199727 rfl rfl (by decide +kernel) R217 F_000000 (stores B2 N215)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 359 4199727 rfl rfl (by decide +kernel) R217 F_000000 (stores B2 N215)) (by decide) (by decide) rfl))

theorem s236 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R236 F_000000 (stores B2 N215) 4199730) M X (· = mk R237 F_000000 (stores B2 N215) 4199731) M X :=
  sgX hparse (cellM 360 4199730 rfl rfl (by decide +kernel) R236 F_000000 (stores B2 N215)) (by intro _ _ h; cases h) (by decide) (lf (hx_pop (cellM 360 4199730 rfl rfl (by decide +kernel) R236 F_000000 (stores B2 N215)) (a := 140737488351168#64) (by decide) ((loadInt_look_none (B := B2) (L := N215) (b := 140737488351168#64) (by decide) (by decide) (by decide)).trans ((copy_out (by decide) (by decide) (by decide)).trans (loadInt_look (B := Ent) (L := Llast) (b := 140737488351168#64) (v := 140737488351216#64) (by decide) (by decide) (by decide)))) (by decide) rfl))

theorem s237 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R237 F_000000 (stores B2 N215) 4199731) M X (· = mk R238 F_000000 (stores B2 N215) 4198500) M X :=
  sgX hparse (cellM 362 4199731 rfl rfl (by decide +kernel) R237 F_000000 (stores B2 N215)) (by intro _ _ h; cases h) (by decide) (lf (hx_ret (cellM 362 4199731 rfl rfl (by decide +kernel) R237 F_000000 (stores B2 N215)) (a := 140737488351176#64) (by decide) ((loadInt_look_none (B := B2) (L := N215) (b := 140737488351176#64) (by decide) (by decide) (by decide)).trans ((copy_out (by decide) (by decide) (by decide)).trans (loadInt_look (B := Ent) (L := Llast) (b := 140737488351176#64) (v := 4198500#64) (by decide) (by decide) (by decide)))) (by decide) (by decide)))

theorem s238 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R238 F_000000 (stores B2 N215) 4198500) M X (· = mk R238 F_000000 (stores B2 N238) 4198504) M X :=
  sgX hparse (cellM 28 4198500 rfl rfl (by decide +kernel) R238 F_000000 (stores B2 N215)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 28 4198500 rfl rfl (by decide +kernel) R238 F_000000 (stores B2 N215)) (a := 140737488351184#64) (v := 72039232#64) (by decide) (ex_eq ((loadInt_look_none (B := B2) (L := N215) (b := 140737488351184#64) (by decide) (by decide) (by decide)).trans (copy_out (by decide) (by decide) (by decide))) (ex_base (B := Ent) (L := Llast) (b := 140737488351184#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide)))) (by decide) rfl))

theorem s239 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R238 F_000000 (stores B2 N238) 4198504) M X (· = mk R240 F_000000 (stores B2 N238) 4198508) M X :=
  sgX hparse (cellM 29 4198504 rfl rfl (by decide +kernel) R238 F_000000 (stores B2 N238)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 29 4198504 rfl rfl (by decide +kernel) R238 F_000000 (stores B2 N238)) (a := 140737488351192#64) (by decide) ((loadInt_look_none (B := B2) (L := N238) (b := 140737488351192#64) (by decide) (by decide) (by decide)).trans ((copy_out (by decide) (by decide) (by decide)).trans (loadInt_look (B := Ent) (L := Llast) (b := 140737488351192#64) (v := 71859016#64) (by decide) (by decide) (by decide)))) (by decide) rfl))

theorem s240 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R240 F_000000 (stores B2 N238) 4198508) M X (· = mk R241 F_000000 (stores B2 N238) 4198513) M X :=
  sgX hparse (cellM 30 4198508 rfl rfl (by decide +kernel) R240 F_000000 (stores B2 N238)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 30 4198508 rfl rfl (by decide +kernel) R240 F_000000 (stores B2 N238)) (by decide) (by decide) rfl))

theorem s241 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R241 F_000000 (stores B2 N238) 4198513) M X (· = mk Rfs F_000000 (stores B2 N238) 4198518) M X :=
  sgX hparse (cellM 31 4198513 rfl rfl (by decide +kernel) R241 F_000000 (stores B2 N238)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 31 4198513 rfl rfl (by decide +kernel) R241 F_000000 (stores B2 N238)) (by decide) (by decide) rfl))

theorem s242 (_hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk Rfs F_000000 (stores B2 N238) 4198518) M X (· = mk Rfs' F_000000 (stores B2 N238) 4198520) M X :=
  sg_archSetFs (stores B2 N238) M X

theorem s243 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk Rfs' F_000000 (stores B2 N238) 4198520) M X (· = mk R244 F_000000 (stores B2 N238) 4198524) M X :=
  sgX hparse (cellM 33 4198520 rfl rfl (by decide +kernel) Rfs' F_000000 (stores B2 N238)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 33 4198520 rfl rfl (by decide +kernel) Rfs' F_000000 (stores B2 N238)) (a := 140737488351184#64) (by decide) (loadInt_look (B := B2) (L := N238) (b := 140737488351184#64) (v := 72039232#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s244 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R244 F_000000 (stores B2 N238) 4198524) M X (· = mk R245 F_000000 (stores B2 N238) 4198528) M X :=
  sgX hparse (cellM 34 4198524 rfl rfl (by decide +kernel) R244 F_000000 (stores B2 N238)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 34 4198524 rfl rfl (by decide +kernel) R244 F_000000 (stores B2 N238)) (a := 140737488351192#64) (by decide) ((loadInt_look_none (B := B2) (L := N238) (b := 140737488351192#64) (by decide) (by decide) (by decide)).trans ((copy_out (by decide) (by decide) (by decide)).trans (loadInt_look (B := Ent) (L := Llast) (b := 140737488351192#64) (v := 71859016#64) (by decide) (by decide) (by decide)))) (by decide) rfl))

theorem s245 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R245 F_000000 (stores B2 N238) 4198528) M X (· = mk R246 F_000000 (stores B2 N238) 4198531) M X :=
  sgX hparse (cellM 35 4198528 rfl rfl (by decide +kernel) R245 F_000000 (stores B2 N238)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 35 4198528 rfl rfl (by decide +kernel) R245 F_000000 (stores B2 N238)) (by decide) (by decide) rfl))

theorem s246 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R246 F_000000 (stores B2 N238) 4198531) M X (· = mk R247 F_010100 (stores B2 N238) 4198533) M X :=
  sgX hparse (cellM 36 4198531 rfl rfl (by decide +kernel) R246 F_000000 (stores B2 N238)) (by intro _ _ h; cases h) (by decide) (lx_xor32 (exec_xor_rr32_self (cellM 36 4198531 rfl rfl (by decide +kernel) R246 F_000000 (stores B2 N238))) (by decide) (by decide) rfl)

theorem s247 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R247 F_010100 (stores B2 N238) 4198533) M X (· = mk R248 F_010100 (stores B2 N247) 4198540) M X :=
  sgX hparse (cellM 37 4198533 rfl rfl (by decide +kernel) R247 F_010100 (stores B2 N238)) (by intro _ _ h; cases h) (by decide) (lf (hx_call (cellM 37 4198533 rfl rfl (by decide +kernel) R247 F_010100 (stores B2 N238)) lab_scc_rt_main (a := 72039224#64) (v := 4198538#64) (by decide) ⟨_, (loadInt_look_none (B := B2) (L := N238) (b := 72039224#64) (by decide) (by decide) (by decide)).trans (copy_in (by decide) (by decide))⟩ (by decide) (by decide)))

theorem s248 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R248 F_010100 (stores B2 N247) 4198540) M X (· = mk R249 F_010100 (stores B2 N248) 4198541) M X :=
  sgX hparse (cellM 40 4198540 rfl rfl (by decide +kernel) R248 F_010100 (stores B2 N247)) (by intro _ _ h; cases h) (by decide) (lf (hx_push (cellM 40 4198540 rfl rfl (by decide +kernel) R248 F_010100 (stores B2 N247)) (a := 72039216#64) (v := 0#64) (by decide) ⟨_, (loadInt_look_none (B := B2) (L := N247) (b := 72039216#64) (by decide) (by decide) (by decide)).trans (copy_in (by decide) (by decide))⟩ (by decide) (by decide) rfl))

theorem s249 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R249 F_010100 (stores B2 N248) 4198541) M X (· = mk R250 F_010100 (stores B2 N248) 4198544) M X :=
  sgX hparse (cellM 41 4198541 rfl rfl (by decide +kernel) R249 F_010100 (stores B2 N248)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 41 4198541 rfl rfl (by decide +kernel) R249 F_010100 (stores B2 N248)) (by decide) (by decide) rfl))

theorem s250 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R250 F_010100 (stores B2 N248) 4198544) M X (· = mk R251 F_010100 (stores B2 N248) 4198549) M X :=
  sgX hparse (cellM 43 4198544 rfl rfl (by decide +kernel) R250 F_010100 (stores B2 N248)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 43 4198544 rfl rfl (by decide +kernel) R250 F_010100 (stores B2 N248)) (by decide) (by decide) rfl))

theorem s251 (hparse : Parse) {X : Kernel.KState} :
    Sg (· = mk R251 F_010100 (stores B2 N248) 4198549) M233 X (· = mk R252 F_010100 (stores B2 N248) 4198558) M233 X :=
  sgFsSh hparse (cellM 44 4198549 rfl rfl (by decide +kernel) R251 F_010100 (stores B2 N248)) (by decide) (a := 71859024#64) (by decide) ((loadInt_look_none (B := B2) (L := N248) (b := 71859024#64) (by decide) (by decide) (by decide)).trans ((copy_out (by decide) (by decide) (by decide)).trans ((loadInt_look_none (B := Ent) (L := Llast) (b := 71859024#64) (by decide) (by decide) (by decide)).trans (ent_none (by decide))))) (val := 72026944#128) (by decide) (by decide) rfl

/-- **Steps 216 … 251.** -/
theorem c7 (hparse : Parse) {X : Kernel.KState} :
    Sg (· = mk R215 F_000000 (stores B2 N215) 4199646) M182 X (· = mk R252 F_010100 (stores B2 N248) 4198558) M233 X :=
  SegP.trans (s216 hparse) <|
  SegP.trans (s217 hparse) <|
  SegP.trans (s218 hparse) <|
  SegP.trans (s219 hparse) <|
  SegP.trans (s220 hparse) <|
  SegP.trans (s221 hparse) <|
  SegP.trans (s222 hparse) <|
  SegP.trans (s223 hparse) <|
  SegP.trans (s224 hparse) <|
  SegP.trans (s225 hparse) <|
  SegP.trans (s226 hparse) <|
  SegP.trans (s227 hparse) <|
  SegP.trans (s228 hparse) <|
  SegP.trans (s229 hparse) <|
  SegP.trans (s230 hparse) <|
  SegP.trans (s231 hparse) <|
  SegP.trans (s232 hparse) <|
  SegP.trans (s233 hparse) <|
  SegP.trans (s234 hparse) <|
  SegP.trans (s235 hparse) <|
  SegP.trans (s236 hparse) <|
  SegP.trans (s237 hparse) <|
  SegP.trans (s238 hparse) <|
  SegP.trans (s239 hparse) <|
  SegP.trans (s240 hparse) <|
  SegP.trans (s241 hparse) <|
  SegP.trans (s242 hparse) <|
  SegP.trans (s243 hparse) <|
  SegP.trans (s244 hparse) <|
  SegP.trans (s245 hparse) <|
  SegP.trans (s246 hparse) <|
  SegP.trans (s247 hparse) <|
  SegP.trans (s248 hparse) <|
  SegP.trans (s249 hparse) <|
  SegP.trans (s250 hparse) <|
  (s251 hparse)

/-- info: 'Spike.Test.HelloRootL0XClosed.c7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.c7

end Spike.Test.HelloRootL0XClosed
