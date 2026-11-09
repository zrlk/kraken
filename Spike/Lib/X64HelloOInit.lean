/-
**hello.w's owned words at the load** (x86-64; the twin of `Spike/Lib/HelloOInit.lean`, itself the twin of
`Spike/Lib/WakeOInit.lean`'s `ownG_lo` / `hown0_W` at `helloCells` and hello's global map `ownGH`).

At the code's base the loaded thread's pc is below every label `ownGH` tests, so its owned words are `ownH`
(= wake's `ownW`) at the base's phase `13`: the four counters and `scc_rt_nthreads`, each `0` at the load (the
runtime's words by `rtInitOk`, `scc_rt_nthreads` by `hnt`, e.g. `X64WakeOInit.hnt_of` from `NtZ`).

- `phH_lo`: the phase at the code's base is `13`.
- `ownGH_lo`: at the code's base `ownGH` is `ownH` at phase `13`.
- `hlab_H`: the layout's labels are `helloCells`'s at `lo`.
- `hown0_H`: `OwnInit` of `ownGH` at the loaded thread.

**Where this differs from AArch64**: the labels are resolved by `codeLabel lo helloCells` (A64: `codeOf lo
helloProg`), the layout is `ofPlaceWX` of a `PlaceWX`, the program comes from `cellsOf asm` (A64:
`textProgram asm`), and the load takes the label offsets (`loadParsed … o.labelOffs`), all as in
`X64WakeOInit`. `ownGH` tests x86-64's labels (`.Lwc_main.x2`, `.x25`, A64's `.L22_wc_main.sp4`, `.sp6`); the
pcs are those of `X64.HelloPh.ownGH_labs`, all above `lo`.
-/
import Spike.Lib.X64WakeOInit
import Spike.Lib.X64HelloOwnG

namespace Spike.Lib.X64HelloOInit

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (helloCells)
open Spike.Lib.X64.WakePh (inPc)
open Spike.Lib.X64.HelloPh (lo ownGH ownH phH)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib (PlaceWX)

/-- **The phase at the code's base is `13`.** -/
theorem phH_lo : phH lo = 13 := by rw [Spike.Lib.X64.HelloPh.phH_eq]; decide +kernel

/-- **At the code's base, `ownGH` is `ownH` at phase `13`.** -/
theorem ownGH_lo {L : RuntimeLayout} (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    {s : State} (hpc : pcOf s = lo) (a : BitVec 64) : ownGH L a s = ownH L a 13 := by
  have e : ∀ l x, codeLabel lo helloCells l = some x → x < 2 ^ 64 → (L.lab l).toBitVec.toNat = x := by
    intro l x hx hlt
    rw [hlab _ _ hx]
    simp [Nat.mod_eq_of_lt hlt]
  have h1 := e "scc_rt_alloc_tcb" 4199029 (by rw [← codeT_eq]; decide +kernel) (by decide)
  have h2 := e "scc_rt_thread_init" 4199582 (by rw [← codeT_eq]; decide +kernel) (by decide)
  have h3 := e ".Lwc_main.x2" 4203787 (by rw [← codeT_eq]; decide +kernel) (by decide)
  have h4 := e ".Lwc_main.x3" 4203812 (by rw [← codeT_eq]; decide +kernel) (by decide)
  have h5 := e "scc_rt_abort" 4202524 (by rw [← codeT_eq]; decide +kernel) (by decide)
  unfold ownGH inPc
  simp [hpc, h1, h2, h3, h4, h5, phH_lo, lo]

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **The layout's labels are `helloCells`'s at `lo`**, of an output whose cells are `helloCells` (`hpa`, `hhp`)
placed at `lo` (`hlo`; wake's `X64WakeOAb.hlab_W`). -/
theorem hlab_H {asm : Scc.Sem.X64.Asm} (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some helloCells) (hlo : Λ0.code.lo = lo) :
    ∀ l x, codeLabel lo helloCells l = some x → (Ly).lab l = Int64.ofNat x := by
  have ho : o.prog = helloCells := Option.some.inj (hpa.symm.trans hhp)
  intro l x h
  exact Spike.Lib.PlaceWX.hlab_ofPlaceWX hp i l x (by
    show codeLabel Λ0.code.lo o.prog l = some x
    rw [hlo, ho]; exact h)

/-- **The loaded thread's owned words are the load's** (`ownGH` at phase `13`: the four counters and
`scc_rt_nthreads`, each `0`), given the loaded `scc_rt_nthreads` word `0` (`hnt`; wake's
`X64WakeOInit.hown0_W`). -/
theorem hown0_H {asm : Scc.Sem.X64.Asm} (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some helloCells) (hlo : Λ0.code.lo = lo)
    (hnt : (Spike.Lib.X64.PhRec.m0Of (Ly).Λ o.prog o.secs).initVal
      ⟨Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab, 8⟩ = 0) (E : Scc.Sem.Entry) :
    ∀ t0, Scc.Sem.X64.loadParsed (Scc.Sem.X64.kernel 1) E (Ly).Λ o.prog o.secs o.labelOffs = some t0 →
      Spike.Lib.Consumer1.OwnInit (ownGH (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab)
        (Scc.Sem.X64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata))) t0.1.mem := by
  intro t0 hl
  have hE := Spike.Lib.X64WakeOInit.clear_of_loadParsed hl
  have he : Scc.Sem.X64.loadParsed (Scc.Sem.X64.kernel 1) E (Ly).Λ o.prog o.secs o.labelOffs = _ :=
    Scc.Cert.Link.X64.loadParsed_of_loadOk (H := Scc.Sem.X64.kernel 1) (PlaceWX.loadOk_link_of_placeWX i hp) hE
  rw [he] at hl
  cases hl
  rw [ownGH_lo (hlab_H hp i hpa hhp hlo) (Spike.Lib.X64WakeOInit.pc_load hp i hlo E)]
  intro L v hm
  simp only [ownH, Spike.Lib.X64.WakePh.ownW, Spike.Lib.X64.PhRec.ownOf, Nat.reduceMod, Nat.reduceDiv, ↓reduceIte,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  have hz {a : BitVec 64} (ha : a ∈ (Ly).rtWords) :
      (Spike.Lib.X64.PhRec.m0Of (Ly).Λ o.prog o.secs).initVal ⟨a, 8⟩ = 0 :=
    Scc.Cert.Rt.X64.initVal_rt_of_rtInitOk (PlaceWX.rtInit_of_placeWX hp) rfl ha
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, (hz (Ly).pn_mem).trans (by decide)⟩
  · exact ⟨rfl, (hz (Ly).lock_mem).trans (by decide)⟩
  · exact ⟨rfl, (hz (Ly).freeN_mem).trans (by decide)⟩
  · exact ⟨rfl, (hz (Ly).next_mem).trans (by decide)⟩
  · exact ⟨rfl, hnt.trans (by decide)⟩

end Place

end Spike.Lib.X64HelloOInit

/-- info: 'Spike.Lib.X64HelloOInit.phH_lo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOInit.phH_lo

/-- info: 'Spike.Lib.X64HelloOInit.ownGH_lo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOInit.ownGH_lo

/-- info: 'Spike.Lib.X64HelloOInit.hlab_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOInit.hlab_H

/-- info: 'Spike.Lib.X64HelloOInit.hown0_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOInit.hown0_H
