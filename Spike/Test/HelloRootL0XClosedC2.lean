/-
**`hello.w` on x86-64, the closed run, chunk 2**: steps 36 … 71 of
thread 0 from the load (`HelloRootL0XClosedStep`), one `SegP` segment per
instruction, composed into `c2`.

Generated from the reference run of the program (the states before every
step: registers `R…`, flags `F_…` (`cf pf af zf sf of`), private memory the
entry stack after the 8-byte stores `L…` (after the take: the taken copy
`B2` after `N…`), shared memory the write chain `M…`). Every step is proved,
not trusted: the generator only chooses the lemma and the witnesses.
-/
import Spike.Test.HelloRootL0XClosedC1

namespace Spike.Test.HelloRootL0XClosed

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Test.HelloLinkedX64 (Λe)
open Spike.Lib.Fwd

set_option maxRecDepth 100000

abbrev R37 : Reg64s := { rax := 3331, rcx := 16383, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R38 : Reg64s := { rax := 3331, rcx := 22, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R39 : Reg64s := { rcx := 22, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R42 : Reg64s := { rcx := 16383, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R46 : Reg64s := { rax := 13, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R49 : Reg64s := { rax := 1, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R50 : Reg64s := { rax := 1, rcx := 13, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R51 : Reg64s := { rax := 13, rcx := 13, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R54 : Reg64s := { rax := 13, rcx := 1, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R55 : Reg64s := { rax := 14, rcx := 1, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R58 : Reg64s := { rax := 14, rcx := 3, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R59 : Reg64s := { rax := 112, rcx := 3, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R61 : Reg64s := { rax := 4225776, rcx := 3, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R63 : Reg64s := { rax := 4225776, rcx := 4225776, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R64 : Reg64s := { rax := 112, rcx := 4225776, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R65 : Reg64s := { rcx := 4225776, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R68 : Reg64s := { rcx := 112, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R69 : Reg64s := { rax := 112, rcx := 112, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev R72 : Reg64s := { rax := 112, rcx := 163840, rsi := 1, rdi := 3331, rsp := 140737488350992, rbp := 140737488351168, r10 := 8 }
abbrev L39 : List (BitVec 64 × BitVec 64) := (140737488351128#64, 0#64) :: L35
abbrev L43 : List (BitVec 64 × BitVec 64) := (140737488351120#64, 0#64) :: L39
abbrev L47 : List (BitVec 64 × BitVec 64) := (140737488351112#64, 13#64) :: L43
abbrev L51 : List (BitVec 64 × BitVec 64) := (140737488351104#64, 13#64) :: L47
abbrev L55 : List (BitVec 64 × BitVec 64) := (140737488351096#64, 14#64) :: L51
abbrev L59 : List (BitVec 64 × BitVec 64) := (140737488351088#64, 112#64) :: L55
abbrev L61 : List (BitVec 64 × BitVec 64) := (140737488351080#64, 4225776#64) :: L59
abbrev L65 : List (BitVec 64 × BitVec 64) := (140737488351072#64, 0#64) :: L61
abbrev L69 : List (BitVec 64 × BitVec 64) := (140737488351064#64, 112#64) :: L65
abbrev M64 : Memory := (M0.append { loc := ⟨4225776#64, 8⟩, val := 112#128, tid := 0 }).1

/-! ## Steps -/

theorem s36 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R34 F_000000 (stores Ent L35) 4199106) M X (· = mk R37 F_000000 (stores Ent L35) 4199110) M X :=
  sgX hparse (cellM 204 4199106 rfl rfl (by decide +kernel) R34 F_000000 (stores Ent L35)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 204 4199106 rfl rfl (by decide +kernel) R34 F_000000 (stores Ent L35)) (a := 140737488351160#64) (by decide) (loadInt_look (B := Ent) (L := L35) (b := 140737488351160#64) (v := 3331#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s37 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R37 F_000000 (stores Ent L35) 4199110) M X (· = mk R38 F_000000 (stores Ent L35) 4199117) M X :=
  sgX hparse (cellM 205 4199110 rfl rfl (by decide +kernel) R37 F_000000 (stores Ent L35)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 205 4199110 rfl rfl (by decide +kernel) R37 F_000000 (stores Ent L35)) (by decide) (by decide) rfl))

theorem s38 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R38 F_000000 (stores Ent L35) 4199117) M X (· = mk R39 F_010100 (stores Ent L35) 4199120) M X :=
  sgX hparse (cellM 206 4199117 rfl rfl (by decide +kernel) R38 F_000000 (stores Ent L35)) (by intro _ _ h; cases h) (by decide) (lx_shr (cellM 206 4199117 rfl rfl (by decide +kernel) R38 F_000000 (stores Ent L35)) (by decide) (by decide) (by decide) (by decide) rfl)

theorem s39 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R39 F_010100 (stores Ent L35) 4199120) M X (· = mk R39 F_010100 (stores Ent L39) 4199124) M X :=
  sgX hparse (cellM 207 4199120 rfl rfl (by decide +kernel) R39 F_010100 (stores Ent L35)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 207 4199120 rfl rfl (by decide +kernel) R39 F_010100 (stores Ent L35)) (a := 140737488351128#64) (v := 0#64) (by decide) (ex_base (B := Ent) (L := L35) (b := 140737488351128#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s40 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R39 F_010100 (stores Ent L39) 4199124) M X (· = mk R39 F_010100 (stores Ent L39) 4199128) M X :=
  sgX hparse (cellM 208 4199124 rfl rfl (by decide +kernel) R39 F_010100 (stores Ent L39)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 208 4199124 rfl rfl (by decide +kernel) R39 F_010100 (stores Ent L39)) (a := 140737488351128#64) (by decide) (loadInt_look (B := Ent) (L := L39) (b := 140737488351128#64) (v := 0#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s41 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R39 F_010100 (stores Ent L39) 4199128) M X (· = mk R42 F_010100 (stores Ent L39) 4199135) M X :=
  sgX hparse (cellM 209 4199128 rfl rfl (by decide +kernel) R39 F_010100 (stores Ent L39)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 209 4199128 rfl rfl (by decide +kernel) R39 F_010100 (stores Ent L39)) (by decide) (by decide) rfl))

theorem s42 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R42 F_010100 (stores Ent L39) 4199135) M X (· = mk R42 F_010100 (stores Ent L39) 4199138) M X :=
  sgX hparse (cellM 210 4199135 rfl rfl (by decide +kernel) R42 F_010100 (stores Ent L39)) (by intro _ _ h; cases h) (by decide) (lx_logic (exec_and_rr (cellM 210 4199135 rfl rfl (by decide +kernel) R42 F_010100 (stores Ent L39))) (by decide) (by decide) rfl)

theorem s43 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R42 F_010100 (stores Ent L39) 4199138) M X (· = mk R42 F_010100 (stores Ent L43) 4199142) M X :=
  sgX hparse (cellM 211 4199138 rfl rfl (by decide +kernel) R42 F_010100 (stores Ent L39)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 211 4199138 rfl rfl (by decide +kernel) R42 F_010100 (stores Ent L39)) (a := 140737488351120#64) (v := 0#64) (by decide) (ex_base (B := Ent) (L := L39) (b := 140737488351120#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s44 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R42 F_010100 (stores Ent L43) 4199142) M X (· = mk R34 F_010100 (stores Ent L43) 4199146) M X :=
  sgX hparse (cellM 212 4199142 rfl rfl (by decide +kernel) R42 F_010100 (stores Ent L43)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 212 4199142 rfl rfl (by decide +kernel) R42 F_010100 (stores Ent L43)) (a := 140737488351136#64) (by decide) (loadInt_look (B := Ent) (L := L43) (b := 140737488351136#64) (v := 13#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s45 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R34 F_010100 (stores Ent L43) 4199146) M X (· = mk R46 F_010100 (stores Ent L43) 4199150) M X :=
  sgX hparse (cellM 213 4199146 rfl rfl (by decide +kernel) R34 F_010100 (stores Ent L43)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 213 4199146 rfl rfl (by decide +kernel) R34 F_010100 (stores Ent L43)) (a := 140737488351120#64) (by decide) (loadInt_look (B := Ent) (L := L43) (b := 140737488351120#64) (v := 0#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s46 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R46 F_010100 (stores Ent L43) 4199150) M X (· = mk R46 F_000000 (stores Ent L43) 4199153) M X :=
  sgX hparse (cellM 214 4199150 rfl rfl (by decide +kernel) R46 F_010100 (stores Ent L43)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 214 4199150 rfl rfl (by decide +kernel) R46 F_010100 (stores Ent L43)) (by decide) (by decide) rfl))

theorem s47 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R46 F_000000 (stores Ent L43) 4199153) M X (· = mk R46 F_000000 (stores Ent L47) 4199157) M X :=
  sgX hparse (cellM 215 4199153 rfl rfl (by decide +kernel) R46 F_000000 (stores Ent L43)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 215 4199153 rfl rfl (by decide +kernel) R46 F_000000 (stores Ent L43)) (a := 140737488351112#64) (v := 13#64) (by decide) (ex_base (B := Ent) (L := L43) (b := 140737488351112#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s48 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R46 F_000000 (stores Ent L47) 4199157) M X (· = mk R49 F_000000 (stores Ent L47) 4199161) M X :=
  sgX hparse (cellM 216 4199157 rfl rfl (by decide +kernel) R46 F_000000 (stores Ent L47)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 216 4199157 rfl rfl (by decide +kernel) R46 F_000000 (stores Ent L47)) (a := 140737488351152#64) (by decide) (loadInt_look (B := Ent) (L := L47) (b := 140737488351152#64) (v := 1#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s49 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R49 F_000000 (stores Ent L47) 4199161) M X (· = mk R50 F_000000 (stores Ent L47) 4199165) M X :=
  sgX hparse (cellM 217 4199161 rfl rfl (by decide +kernel) R49 F_000000 (stores Ent L47)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 217 4199161 rfl rfl (by decide +kernel) R49 F_000000 (stores Ent L47)) (a := 140737488351112#64) (by decide) (loadInt_look (B := Ent) (L := L47) (b := 140737488351112#64) (v := 13#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s50 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R50 F_000000 (stores Ent L47) 4199165) M X (· = mk R51 F_000000 (stores Ent L47) 4199169) M X :=
  sgX hparse (cellM 218 4199165 rfl rfl (by decide +kernel) R50 F_000000 (stores Ent L47)) (by intro _ _ h; cases h) (by decide) (lx_imul (exec_imul_rr (cellM 218 4199165 rfl rfl (by decide +kernel) R50 F_000000 (stores Ent L47))) (by decide) (by decide) rfl)

theorem s51 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R51 F_000000 (stores Ent L47) 4199169) M X (· = mk R51 F_000000 (stores Ent L51) 4199173) M X :=
  sgX hparse (cellM 219 4199169 rfl rfl (by decide +kernel) R51 F_000000 (stores Ent L47)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 219 4199169 rfl rfl (by decide +kernel) R51 F_000000 (stores Ent L47)) (a := 140737488351104#64) (v := 13#64) (by decide) (ex_base (B := Ent) (L := L47) (b := 140737488351104#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s52 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R51 F_000000 (stores Ent L51) 4199173) M X (· = mk R51 F_000000 (stores Ent L51) 4199177) M X :=
  sgX hparse (cellM 220 4199173 rfl rfl (by decide +kernel) R51 F_000000 (stores Ent L51)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 220 4199173 rfl rfl (by decide +kernel) R51 F_000000 (stores Ent L51)) (a := 140737488351104#64) (by decide) (loadInt_look (B := Ent) (L := L51) (b := 140737488351104#64) (v := 13#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s53 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R51 F_000000 (stores Ent L51) 4199177) M X (· = mk R54 F_000000 (stores Ent L51) 4199184) M X :=
  sgX hparse (cellM 221 4199177 rfl rfl (by decide +kernel) R51 F_000000 (stores Ent L51)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 221 4199177 rfl rfl (by decide +kernel) R51 F_000000 (stores Ent L51)) (by decide) (by decide) rfl))

theorem s54 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R54 F_000000 (stores Ent L51) 4199184) M X (· = mk R55 F_000000 (stores Ent L51) 4199187) M X :=
  sgX hparse (cellM 222 4199184 rfl rfl (by decide +kernel) R54 F_000000 (stores Ent L51)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 222 4199184 rfl rfl (by decide +kernel) R54 F_000000 (stores Ent L51)) (by decide) (by decide) rfl))

theorem s55 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R55 F_000000 (stores Ent L51) 4199187) M X (· = mk R55 F_000000 (stores Ent L55) 4199191) M X :=
  sgX hparse (cellM 223 4199187 rfl rfl (by decide +kernel) R55 F_000000 (stores Ent L51)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 223 4199187 rfl rfl (by decide +kernel) R55 F_000000 (stores Ent L51)) (a := 140737488351096#64) (v := 14#64) (by decide) (ex_base (B := Ent) (L := L51) (b := 140737488351096#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s56 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R55 F_000000 (stores Ent L55) 4199191) M X (· = mk R55 F_000000 (stores Ent L55) 4199195) M X :=
  sgX hparse (cellM 224 4199191 rfl rfl (by decide +kernel) R55 F_000000 (stores Ent L55)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 224 4199191 rfl rfl (by decide +kernel) R55 F_000000 (stores Ent L55)) (a := 140737488351096#64) (by decide) (loadInt_look (B := Ent) (L := L55) (b := 140737488351096#64) (v := 14#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s57 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R55 F_000000 (stores Ent L55) 4199195) M X (· = mk R58 F_000000 (stores Ent L55) 4199202) M X :=
  sgX hparse (cellM 225 4199195 rfl rfl (by decide +kernel) R55 F_000000 (stores Ent L55)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 225 4199195 rfl rfl (by decide +kernel) R55 F_000000 (stores Ent L55)) (by decide) (by decide) rfl))

theorem s58 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R58 F_000000 (stores Ent L55) 4199202) M X (· = mk R59 F_000000 (stores Ent L55) 4199205) M X :=
  sgX hparse (cellM 226 4199202 rfl rfl (by decide +kernel) R58 F_000000 (stores Ent L55)) (by intro _ _ h; cases h) (by decide) (lx_shl (cellM 226 4199202 rfl rfl (by decide +kernel) R58 F_000000 (stores Ent L55)) (by decide) (by decide) (by decide) (by decide) rfl)

theorem s59 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R59 F_000000 (stores Ent L55) 4199205) M X (· = mk R59 F_000000 (stores Ent L59) 4199209) M X :=
  sgX hparse (cellM 227 4199205 rfl rfl (by decide +kernel) R59 F_000000 (stores Ent L55)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 227 4199205 rfl rfl (by decide +kernel) R59 F_000000 (stores Ent L55)) (a := 140737488351088#64) (v := 112#64) (by decide) (ex_base (B := Ent) (L := L55) (b := 140737488351088#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s60 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R59 F_000000 (stores Ent L59) 4199209) M X (· = mk R61 F_000000 (stores Ent L59) 4199216) M X :=
  sgX hparse (cellM 228 4199209 rfl rfl (by decide +kernel) R59 F_000000 (stores Ent L59)) (by intro _ _ h; cases h) (by decide) (lf (hx_leaRip (cellM 228 4199209 rfl rfl (by decide +kernel) R59 F_000000 (stores Ent L59)) lab_scc_rt_pinned_next (by decide) rfl))

theorem s61 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R61 F_000000 (stores Ent L59) 4199216) M X (· = mk R61 F_000000 (stores Ent L61) 4199220) M X :=
  sgX hparse (cellM 229 4199216 rfl rfl (by decide +kernel) R61 F_000000 (stores Ent L59)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 229 4199216 rfl rfl (by decide +kernel) R61 F_000000 (stores Ent L59)) (a := 140737488351080#64) (v := 4225776#64) (by decide) (ex_base (B := Ent) (L := L59) (b := 140737488351080#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s62 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R61 F_000000 (stores Ent L61) 4199220) M X (· = mk R63 F_000000 (stores Ent L61) 4199224) M X :=
  sgX hparse (cellM 230 4199220 rfl rfl (by decide +kernel) R61 F_000000 (stores Ent L61)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 230 4199220 rfl rfl (by decide +kernel) R61 F_000000 (stores Ent L61)) (a := 140737488351080#64) (by decide) (loadInt_look (B := Ent) (L := L61) (b := 140737488351080#64) (v := 4225776#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s63 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R63 F_000000 (stores Ent L61) 4199224) M X (· = mk R64 F_000000 (stores Ent L61) 4199228) M X :=
  sgX hparse (cellM 231 4199224 rfl rfl (by decide +kernel) R63 F_000000 (stores Ent L61)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 231 4199224 rfl rfl (by decide +kernel) R63 F_000000 (stores Ent L61)) (a := 140737488351088#64) (by decide) (loadInt_look (B := Ent) (L := L61) (b := 140737488351088#64) (v := 112#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s64 (hparse : Parse) {X : Kernel.KState} :
    Sg (· = mk R64 F_000000 (stores Ent L61) 4199228) M0 X (· = mk R65 F_000000 (stores Ent L61) 4199233) M64 X :=
  sgXaddSh hparse (cellM 232 4199228 rfl rfl (by decide +kernel) R64 F_000000 (stores Ent L61)) (by decide) (a := 4225776#64) ((eaddr_reg_disp _ _ _ _).trans (by decide)) ((loadInt_look_none (B := Ent) (L := L61) (b := 4225776#64) (by decide) (by decide) (by decide)).trans (ent_none (by decide))) (old := 0#128) (nv := 112#128) (by decide) (by decide) (by decide) (by decide) rfl

theorem s65 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R65 F_000000 (stores Ent L61) 4199233) M X (· = mk R65 F_000000 (stores Ent L65) 4199237) M X :=
  sgX hparse (cellM 233 4199233 rfl rfl (by decide +kernel) R65 F_000000 (stores Ent L61)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 233 4199233 rfl rfl (by decide +kernel) R65 F_000000 (stores Ent L61)) (a := 140737488351072#64) (v := 0#64) (by decide) (ex_base (B := Ent) (L := L61) (b := 140737488351072#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s66 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R65 F_000000 (stores Ent L65) 4199237) M X (· = mk R65 F_000000 (stores Ent L65) 4199241) M X :=
  sgX hparse (cellM 234 4199237 rfl rfl (by decide +kernel) R65 F_000000 (stores Ent L65)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 234 4199237 rfl rfl (by decide +kernel) R65 F_000000 (stores Ent L65)) (a := 140737488351072#64) (by decide) (loadInt_look (B := Ent) (L := L65) (b := 140737488351072#64) (v := 0#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s67 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R65 F_000000 (stores Ent L65) 4199241) M X (· = mk R68 F_000000 (stores Ent L65) 4199245) M X :=
  sgX hparse (cellM 235 4199241 rfl rfl (by decide +kernel) R65 F_000000 (stores Ent L65)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 235 4199241 rfl rfl (by decide +kernel) R65 F_000000 (stores Ent L65)) (a := 140737488351088#64) (by decide) (loadInt_look (B := Ent) (L := L65) (b := 140737488351088#64) (v := 112#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s68 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R68 F_000000 (stores Ent L65) 4199245) M X (· = mk R69 F_000000 (stores Ent L65) 4199248) M X :=
  sgX hparse (cellM 236 4199245 rfl rfl (by decide +kernel) R68 F_000000 (stores Ent L65)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 236 4199245 rfl rfl (by decide +kernel) R68 F_000000 (stores Ent L65)) (by decide) (by decide) rfl))

theorem s69 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R69 F_000000 (stores Ent L65) 4199248) M X (· = mk R69 F_000000 (stores Ent L69) 4199252) M X :=
  sgX hparse (cellM 237 4199248 rfl rfl (by decide +kernel) R69 F_000000 (stores Ent L65)) (by intro _ _ h; cases h) (by decide) (lf (hx_st (cellM 237 4199248 rfl rfl (by decide +kernel) R69 F_000000 (stores Ent L65)) (a := 140737488351064#64) (v := 112#64) (by decide) (ex_base (B := Ent) (L := L65) (b := 140737488351064#64) (by decide) (by decide) (by decide) (stack_some (by decide) (by decide))) (by decide) rfl))

theorem s70 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R69 F_000000 (stores Ent L69) 4199252) M X (· = mk R69 F_000000 (stores Ent L69) 4199256) M X :=
  sgX hparse (cellM 238 4199252 rfl rfl (by decide +kernel) R69 F_000000 (stores Ent L69)) (by intro _ _ h; cases h) (by decide) (lf (hx_ld (cellM 238 4199252 rfl rfl (by decide +kernel) R69 F_000000 (stores Ent L69)) (a := 140737488351064#64) (by decide) (loadInt_look (B := Ent) (L := L69) (b := 140737488351064#64) (v := 112#64) (by decide) (by decide) (by decide)) (by decide) rfl))

theorem s71 (hparse : Parse) {M : Memory} {X : Kernel.KState} :
    Sg (· = mk R69 F_000000 (stores Ent L69) 4199256) M X (· = mk R72 F_000000 (stores Ent L69) 4199263) M X :=
  sgX hparse (cellM 239 4199256 rfl rfl (by decide +kernel) R69 F_000000 (stores Ent L69)) (by intro _ _ h; cases h) (by decide) (lf (hx_reg rfl (cellM 239 4199256 rfl rfl (by decide +kernel) R69 F_000000 (stores Ent L69)) (by decide) (by decide) rfl))

/-- **Steps 36 … 71.** -/
theorem c2 (hparse : Parse) {X : Kernel.KState} :
    Sg (· = mk R34 F_000000 (stores Ent L35) 4199106) M0 X (· = mk R72 F_000000 (stores Ent L69) 4199263) M64 X :=
  SegP.trans (s36 hparse) <|
  SegP.trans (s37 hparse) <|
  SegP.trans (s38 hparse) <|
  SegP.trans (s39 hparse) <|
  SegP.trans (s40 hparse) <|
  SegP.trans (s41 hparse) <|
  SegP.trans (s42 hparse) <|
  SegP.trans (s43 hparse) <|
  SegP.trans (s44 hparse) <|
  SegP.trans (s45 hparse) <|
  SegP.trans (s46 hparse) <|
  SegP.trans (s47 hparse) <|
  SegP.trans (s48 hparse) <|
  SegP.trans (s49 hparse) <|
  SegP.trans (s50 hparse) <|
  SegP.trans (s51 hparse) <|
  SegP.trans (s52 hparse) <|
  SegP.trans (s53 hparse) <|
  SegP.trans (s54 hparse) <|
  SegP.trans (s55 hparse) <|
  SegP.trans (s56 hparse) <|
  SegP.trans (s57 hparse) <|
  SegP.trans (s58 hparse) <|
  SegP.trans (s59 hparse) <|
  SegP.trans (s60 hparse) <|
  SegP.trans (s61 hparse) <|
  SegP.trans (s62 hparse) <|
  SegP.trans (s63 hparse) <|
  SegP.trans (s64 hparse) <|
  SegP.trans (s65 hparse) <|
  SegP.trans (s66 hparse) <|
  SegP.trans (s67 hparse) <|
  SegP.trans (s68 hparse) <|
  SegP.trans (s69 hparse) <|
  SegP.trans (s70 hparse) <|
  (s71 hparse)

/-- info: 'Spike.Test.HelloRootL0XClosed.c2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.c2

end Spike.Test.HelloRootL0XClosed
