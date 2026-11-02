/-
**hello.w's owned words at the load, with main's TCB words** (x86-64 only; `X64HelloOInit` at
`X64.HelloPh.ownGHXW`, the map with main's own TCB word `ownSH` and the worker's `ownSWH`).

At the code's base the loaded thread's pc is below every label `selfOwnH` / `selfOwnWH` test
(`.Lscc_rt_start.x1`, `.Lscc_rt_thread_init.x8`, `.Lwc_main.x25`, `scc_rt_abort`), so neither TCB word is owned
there and `ownGHXW` is `ownGH`; the load's owned words are `X64HelloOInit.hown0_H`'s.

- `ownGHXW_lo`: at the code's base `ownGHXW` is `ownGH`.
- `hown0_HX`: `OwnInit` of `ownGHXW` at the loaded thread.

**Where this differs from AArch64** (forced by the x86-64 shape): AArch64 has no counterpart. Its park and
worker tail take the thread pointer from a register, so main owns no TCB word and its map stays `ownGH`; on
x86-64 the map main carries is `ownGHXW` (`X64HelloOwnSX`), which agrees with `ownGH` at the load.
-/
import Spike.Lib.X64HelloOInit
import Spike.Lib.X64HelloOwnSX

namespace Spike.Lib.X64HelloOInitX

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (helloCells)
open Spike.Lib.X64.WakePh (inPc)
open Spike.Lib.X64.HelloPh (lo ownGH ownGHX ownGHXW selfOwnH selfOwnWH ownSH_of_not ownSWH_of_not)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib (PlaceWX)

/-- **At the code's base, `ownGHXW` is `ownGH`**: neither main's TCB word (`selfOwnH`) nor the worker's
(`selfOwnWH`) is owned below `.Lscc_rt_start.x1`. -/
theorem ownGHXW_lo {L : RuntimeLayout}
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    {s : State} (hpc : pcOf s = lo) (a : BitVec 64) : ownGHXW L a s = ownGH L a s := by
  have e : ∀ l x, codeLabel lo helloCells l = some x → x < 2 ^ 64 → (L.lab l).toBitVec.toNat = x := by
    intro l x hx hlt
    rw [hlab _ _ hx]
    simp [Nat.mod_eq_of_lt hlt]
  have h1 := e ".Lscc_rt_start.x1" 4198500 (by rw [← codeT_eq]; decide +kernel) (by decide)
  have h2 := e ".Lscc_rt_thread_init.x8" 4199606 (by rw [← codeT_eq]; decide +kernel) (by decide)
  have h3 := e ".Lwc_main.x25" 4203774 (by rw [← codeT_eq]; decide +kernel) (by decide)
  have h4 := e "scc_rt_abort" 4202486 (by rw [← codeT_eq]; decide +kernel) (by decide)
  have hS : ¬ selfOwnH L s := by
    unfold selfOwnH inPc; rw [hpc, h1, h2]; simp only [lo]; omega
  have hW : ¬ selfOwnWH L s := by
    unfold selfOwnWH inPc; rw [hpc, h2, h3, h4]; simp only [lo]; omega
  unfold ownGHXW ownGHX
  rw [ownSH_of_not hS, ownSWH_of_not hW, List.append_nil, List.append_nil]

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **The loaded thread's owned words at `ownGHXW` are the load's** (`X64HelloOInit.hown0_H`'s: neither TCB
word is owned at the code's base, `ownGHXW_lo`), given the loaded `scc_rt_nthreads` word `0` (`hnt`). -/
theorem hown0_HX {asm : Scc.Sem.X64.Asm} (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some helloCells) (hlo : Λ0.code.lo = lo)
    (hnt : (Spike.Lib.X64.PhRec.m0Of (Ly).Λ o.prog o.secs).initVal
      ⟨Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab, 8⟩ = 0) (E : Scc.Sem.Entry) :
    ∀ t0, Scc.Sem.X64.loadParsed (Scc.Sem.X64.kernel 1) E (Ly).Λ o.prog o.secs o.labelOffs = some t0 →
      Spike.Lib.Consumer1.OwnInit (ownGHXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab)
        (Scc.Sem.X64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata))) t0.1.mem := by
  intro t0 hl
  rw [ownGHXW_lo (Spike.Lib.X64HelloOInit.hlab_H hp i hpa hhp hlo) (Spike.Lib.X64WakeOInit.pc_load hp i hlo E)]
  exact Spike.Lib.X64HelloOInit.hown0_H hp i hpa hhp hlo hnt E t0 hl

end Place

end Spike.Lib.X64HelloOInitX

/-- info: 'Spike.Lib.X64HelloOInitX.ownGHXW_lo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOInitX.ownGHXW_lo

/-- info: 'Spike.Lib.X64HelloOInitX.hown0_HX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOInitX.hown0_HX
