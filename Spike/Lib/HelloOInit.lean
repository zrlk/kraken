/-
**hello.w's owned words at the load** (AArch64, the root's loader facts; the twin of
`Spike/Lib/WakeOInit.lean`'s `ownG_lo` / `hown0_W` at `helloProg` and hello's global map `ownGH`).

At the code's base the loaded thread's pc is outside every range `ownGH` tests, so its owned words are `ownH`
(= wake's `ownW`) at the base's phase `13`: the four counters and `scc_rt_nthreads`, each `0` at the load (the
runtime's words by `rtInitOk`, `scc_rt_nthreads` by `hnt`, e.g. `WakeOInit.hnt_of` from `NtZ`).

- `phH_lo`: the phase at the code's base is `13`.
- `ownGH_lo`: at the code's base `ownGH` is `ownH` at phase `13`.
- `hlab_H`: the layout's labels are `helloProg`'s at `lo`.
- `hown0_H`: `OwnInit` of `ownGH` at the loaded thread.
-/
import Spike.Lib.WakeOInit
import Spike.Lib.A64HelloOwnG

namespace Spike.Lib.HelloOInit

variable {asm : String}

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.WakePh (lo inPc)
open Spike.Lib.A64.HelloPh (ownGH ownH phH)
open Spike.Lib.A64.Rt (RuntimeLayout)

/-- **The phase at the code's base is `13`.** -/
theorem phH_lo : phH lo = 13 := by decide +kernel

/-- **At the code's base, `ownGH` is `ownH` at phase `13`.** -/
theorem ownGH_lo {L : RuntimeLayout}
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    {s : State} (hpc : pcOf s = lo) (a : BitVec 64) : ownGH L a s = ownH L a 13 := by
  have hn : ∀ l₁ l₂ x, codeOf lo SccCode.helloProg l₁ = some x → lo < x → ¬ inPc L l₁ l₂ s := by
    rintro l₁ l₂ x hx hlt ⟨h1, -⟩
    rw [hlab _ _ hx, hpc] at h1
    have : x < 2 ^ 64 := by
      have := Spike.Lib.A64.PhRec.le_codeEnd_of_codeOf hx
      have : Scc.Sem.A64.codeEnd lo SccCode.helloProg < 2 ^ 64 := by decide +kernel
      omega
    simp [Nat.mod_eq_of_lt this] at h1
    omega
  unfold ownGH
  simp only [hn "scc_rt_alloc_tcb" "scc_rt_thread_reserve" 2164748 (by rw [← codeT_eq]; decide +kernel) (by decide),
    hn "scc_rt_thread_init" "scc_rt_stack_release" 2165280 (by rw [← codeT_eq]; decide +kernel) (by decide),
    hn ".L22_wc_main.sp4" ".L22_wc_main.sp6" 2169716 (by rw [← codeT_eq]; decide +kernel) (by decide),
    hn ".L22_wc_main.sp6" ".L22_wc_main.stack_grow" 2169740 (by rw [← codeT_eq]; decide +kernel) (by decide),
    hn "scc_rt_abort" "scc_rt_thr_worker" 2168032 (by rw [← codeT_eq]; decide +kernel) (by decide), ↓reduceIte, hpc,
    phH_lo]

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- **The layout's labels are `helloProg`'s at `lo`**, of an output whose program is `helloProg` (`hpa`, `hhp`)
placed at `lo` (`hlo`; wake's `WakeOAb.hlab_W`). -/
theorem hlab_H (hpa : Scc.Sem.A64.textProgram asm = .ok o.prog)
    (hhp : Scc.Sem.A64.textProgram asm = .ok SccCode.helloProg) (hlo : Λ0.code.lo = lo) :
    ∀ l x, codeOf lo SccCode.helloProg l = some x → (Ly).lab l = Int64.ofNat x := by
  have ho : o.prog = SccCode.helloProg := Except.ok.inj (hpa.symm.trans hhp)
  intro l x h
  exact Spike.Lib.PlaceW.hlab_ofPlaceW hp i l x (by
    show codeOf Λ0.code.lo o.prog l = some x
    rw [hlo, ho]; exact h)

/-- **The loaded thread's owned words are the load's** (`ownGH` at phase `13`: the four counters and
`scc_rt_nthreads`, each `0`), given the loaded `scc_rt_nthreads` word `0` (`hnt`; wake's `WakeOInit.hown0_W`). -/
theorem hown0_H (hpa : Scc.Sem.A64.textProgram asm = .ok o.prog)
    (hhp : Scc.Sem.A64.textProgram asm = .ok SccCode.helloProg) (hlo : Λ0.code.lo = lo)
    (hnt : (Spike.Lib.A64.PhRec.m0Of (Ly).Λ o.prog o.secs).initVal
      ⟨Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab, 8⟩ = 0) (E : Scc.Sem.Entry) :
    ∀ t0, Scc.Sem.A64.loadParsed (Scc.Sem.A64.kernel 1) E (Ly).Λ o.prog o.secs = some t0 →
      Spike.Lib.Consumer1.OwnInit (ownGH (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab)
        (Scc.Sem.A64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata))) t0.1.mem := by
  intro t0 hl
  have hE := Spike.Lib.WakeOInit.clear_of_loadParsed hl
  have he : Scc.Sem.A64.loadParsed (Scc.Sem.A64.kernel 1) E (Ly).Λ o.prog o.secs = _ :=
    Scc.Cert.Link.A64.loadParsed_of_loadOk (H := Scc.Sem.A64.kernel 1) (PlaceW.loadOk_link_of_placeW i hp) hE
  rw [he] at hl
  cases hl
  rw [ownGH_lo (hlab_H hp i hpa hhp hlo) (Spike.Lib.WakeOInit.pc_load hp i hlo E)]
  intro L v hm
  simp only [ownH, Spike.Lib.A64.WakePh.ownW, Spike.Lib.A64.PhRec.ownOf, Nat.reduceMod, Nat.reduceDiv, ↓reduceIte,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  have hz {a : BitVec 64} (ha : a ∈ (Ly).rtWords) :
      (Spike.Lib.A64.PhRec.m0Of (Ly).Λ o.prog o.secs).initVal ⟨a, 8⟩ = 0 :=
    Scc.Cert.Rt.A64.initVal_rt_of_rtInitOk (PlaceW.rtInit_of_placeW hp) rfl ha
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, (hz (Ly).pn_mem).trans (by decide)⟩
  · exact ⟨rfl, (hz (Ly).lock_mem).trans (by decide)⟩
  · exact ⟨rfl, (hz (Ly).freeN_mem).trans (by decide)⟩
  · exact ⟨rfl, (hz (Ly).next_mem).trans (by decide)⟩
  · exact ⟨rfl, hnt.trans (by decide)⟩

end Place

end Spike.Lib.HelloOInit

/-- info: 'Spike.Lib.HelloOInit.ownGH_lo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloOInit.ownGH_lo

/-- info: 'Spike.Lib.HelloOInit.hown0_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloOInit.hown0_H
