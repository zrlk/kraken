/-
**`wake_initT`'s owned words at the load** (x86-64): at wake's loaded
thread (`_start`, the code's base `WakePh.lo`), `X64.WakeOD.wakeD`'s `own`
(`WakePh.ownGXW L (ntA L.lab)`) is `ownW` at phase `13`: the four runtime
counters at their loaded `0` and `scc_rt_nthreads` at `0`.

- `clear_of_loadParsed`: a successful parsed load is at an entry clear of
  the layout.
- `phW_lo`: the phase at the code's base is `13`.
- `ownGXW_lo`: at `WakePh.lo` the pc is below every label `ownG`, `ownS` and
  `ownSW` test (all lie above), so `ownGXW` is `ownW` at `phW lo = 13`.
- `NtZ`, `hnt_of`: `scc_rt_nthreads`'s symbol resolves and no initial word
  of the load is at it, so its loaded word is `0`.
- `hown0_W`: `wake_initT`'s `hown0` first conjunct (`OwnInit`), given the
  loaded `scc_rt_nthreads` word `0` (`hnt`, from `hnt_of`).

x86-64 twin of `Spike/Lib/WakeOInit.lean`. **Unlike AArch64**:
- `own` is `ownGXW` (`ownG` with main's TCB word `ownS` and the worker's
  `ownSW`), so `ownGXW_lo` also rules out `selfOwn`/`selfOwnW` (each needs
  a pc at or above `.Lscc_rt_start.x1`, `.Lscc_rt_thread_init.x7 + 51`,
  `.Lwc_main.x21` or `scc_rt_abort`);
- the load takes the label offsets (`loadParsed … offs`), and the layout is
  `ofPlaceWX` at `PlaceWX`; labels are `codeLabel lo wakeCells`
  (`X64WakeOAb.hlab_W`, from `cellsOf`).
-/
import Spike.Lib.X64WakeOAb
import Spike.Lib.X64WakeOwnT2
import Spike.Lib.X64PlaceWRt
import Spike.Lib.X64StartOfPlaceOK

namespace Spike.Lib.X64WakeOInit

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (wakeCells)
open Spike.Lib.X64.WakePh (lo ownG ownW phW inPc ownGX ownS ownSW ownGXW selfOwn selfOwnW)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib (PlaceWX)

/-- **A successful parsed load is at an entry clear of the layout.** -/
theorem clear_of_loadParsed {H : Scc.Sem.Hooks isa} {E : Scc.Sem.Entry} {Λ : Scc.Sem.Layout}
    {cells : List (Directive × Nat)} {secs : Scc.Sem.DataSecs} {offs : List (String × Nat)}
    {t0 : (Scc.Sem.X64.machine H).Cfg}
    (h : Scc.Sem.X64.loadParsed H E Λ cells secs offs = some t0) : E.clear Λ = true := by
  simp only [Scc.Sem.X64.loadParsed] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    exact hc.2
  · cases h

/-- **The phase at the code's base is `13`.** -/
theorem phW_lo : phW lo = 13 := by rw [Spike.Lib.X64.WakePh.phW_eq]; decide +kernel

/-- **At the code's base, `ownGXW` is `ownW` at phase `13`.** -/
theorem ownGXW_lo {L : RuntimeLayout} (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    {s : State} (hpc : pcOf s = lo) (a : BitVec 64) : ownGXW L a s = ownW L a 13 := by
  have e : ∀ l x, codeLabel lo wakeCells l = some x → x < 2 ^ 64 → (L.lab l).toBitVec.toNat = x := by
    intro l x hx hlt
    rw [hlab _ _ hx]
    simp [Nat.mod_eq_of_lt hlt]
  have h1 := e "scc_rt_alloc_tcb" 4198992 (by rw [← codeT_eq]; decide +kernel) (by decide)
  have h2 := e "scc_rt_thread_init" 4199545 (by rw [← codeT_eq]; decide +kernel) (by decide)
  have h3 := e ".Lwc_main.x20" 4203372 (by rw [← codeT_eq]; decide +kernel) (by decide)
  have h4 := e ".Lwc_main.x21" 4203397 (by rw [← codeT_eq]; decide +kernel) (by decide)
  have h5 := e "scc_rt_abort" 4202449 (by rw [← codeT_eq]; decide +kernel) (by decide)
  have h6 := e ".Lscc_rt_start.x1" 4198500 (by rw [← codeT_eq]; decide +kernel) (by decide)
  have h7 := e ".Lscc_rt_thread_init.x7" 4199569 (by rw [← codeT_eq]; decide +kernel) (by decide)
  unfold ownGXW ownGX ownG ownS ownSW selfOwn selfOwnW inPc
  simp [hpc, h1, h2, h3, h4, h5, h6, h7, phW_lo, lo]

/-- **`scc_rt_nthreads` starts at `0`** (a decided fact of the emitted
output, as `rtInitOk` for the runtime's words): its symbol resolves to a
data label and no initial word of the load (`initOf`) is at it. -/
def NtZ (Λ : Scc.Sem.Layout) (o : Scc.Cert.PlaceOK.X64.Out) : Bool :=
  (Scc.Cert.Rt.X64.symLab Λ.code.lo o.prog (Scc.Sem.loadSyms Λ o.secs.rodata) "scc_rt_nthreads").isSome &&
    ((Scc.Cert.Rt.X64.initOf Λ o.prog o.secs).find?
      (·.1 == ⟨Scc.Cert.Rt.X64.rtA Λ o.prog o.secs "scc_rt_nthreads", 8⟩)).isNone

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- The loaded thread's pc is the code's base. -/
theorem pc_load (hlo : Λ0.code.lo = lo) (E : Scc.Sem.Entry) :
    pcOf (Scc.Sem.X64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata)) = lo := by
  show (Int64.ofNat Λ0.code.lo).toBitVec.toNat = lo
  rw [hlo]; decide

/-- **`hown0_W`'s `hnt` from `NtZ`**: the loaded `scc_rt_nthreads` word
is `0`. -/
theorem hnt_of (hnz : NtZ Λ0 o = true) :
    (Spike.Lib.X64.PhRec.m0Of (Ly).Λ o.prog o.secs).initVal ⟨Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab, 8⟩ = 0 := by
  simp only [NtZ, Bool.and_eq_true, Option.isSome_iff_exists] at hnz
  obtain ⟨⟨a, ha⟩, hn⟩ := hnz
  have hl : (Ly).lab "scc_rt_nthreads" = Int64.ofNat a :=
    Scc.Cert.Rt.X64.label_threadAt_of_symLab (E := Scc.Sem.Entry.linux)
      (Scc.Cert.Link.X64.symsAround_of_loadOk (PlaceWX.loadOk_link_of_placeWX i hp)) ha
  have hr : Scc.Cert.Rt.X64.rtA Λ0 o.prog o.secs "scc_rt_nthreads" = BitVec.ofNat 64 a := by
    simp [Scc.Cert.Rt.X64.rtA, ha]
  rw [hr] at hn
  have hnt : Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab = BitVec.ofNat 64 a := by
    simp [Spike.Lib.X64.Rt.Reserve.ntA, hl]
  unfold Memory.initVal
  rw [hnt]
  show ((Scc.Cert.Rt.X64.initOf Λ0 o.prog o.secs).find? _ |>.map (·.2)).getD 0 = 0
  rw [Option.isNone_iff_eq_none.mp hn]
  rfl

/-- **`wake_initT`'s `OwnInit`**: the loaded thread's owned words (`ownW`
at phase `13`: the four counters and `scc_rt_nthreads`, each `0`) are the
load's, given the loaded `scc_rt_nthreads` word `0` (`hnt`). -/
theorem hown0_W {asm : Scc.Sem.X64.Asm} (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hwp : Scc.Sem.X64.cellsOf asm = some wakeCells) (hlo : Λ0.code.lo = lo)
    (hnt : (Spike.Lib.X64.PhRec.m0Of (Ly).Λ o.prog o.secs).initVal
      ⟨Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab, 8⟩ = 0) (E : Scc.Sem.Entry) :
    ∀ t0, Scc.Sem.X64.loadParsed (Scc.Sem.X64.kernel 1) E (Ly).Λ o.prog o.secs o.labelOffs = some t0 →
      Spike.Lib.Consumer1.OwnInit (ownGXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab)
        (Scc.Sem.X64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata))) t0.1.mem := by
  intro t0 hl
  have hE := clear_of_loadParsed hl
  have he : Scc.Sem.X64.loadParsed (Scc.Sem.X64.kernel 1) E (Ly).Λ o.prog o.secs o.labelOffs = _ :=
    Scc.Cert.Link.X64.loadParsed_of_loadOk (H := Scc.Sem.X64.kernel 1) (PlaceWX.loadOk_link_of_placeWX i hp) hE
  rw [he] at hl
  cases hl
  rw [ownGXW_lo (X64WakeOAb.hlab_W hp i hpa hwp hlo) (pc_load hp i hlo E)]
  intro L v hm
  simp only [ownW, Spike.Lib.X64.PhRec.ownOf, Nat.reduceMod, Nat.reduceDiv, ↓reduceIte, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
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

end Spike.Lib.X64WakeOInit

/-- info: 'Spike.Lib.X64WakeOInit.ownGXW_lo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOInit.ownGXW_lo

/-- info: 'Spike.Lib.X64WakeOInit.hnt_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOInit.hnt_of

/-- info: 'Spike.Lib.X64WakeOInit.hown0_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOInit.hown0_W
