/-
**`wake_init`'s owned words at the load** (AArch64): at wake's
loaded thread (`_start`, the code's base `WakePh.lo`), `WakeOD.wakeD`'s
`own` (`WakePh.ownG L (ntA L.lab)`) is `ownW` at phase `13`: the four
runtime counters at their loaded `0` and `scc_rt_nthreads` at `0`.

- `clear_of_loadParsed`: a successful parsed load is at an entry clear of
  the layout.
- `ownG_lo`: off every `inPc` range of `ownG` at `WakePh.lo` (all its labels
  lie above), so `ownG` is `ownW` at `phW lo = 13`.
- `NtZ`, `hnt_of`: `scc_rt_nthreads`'s symbol resolves and no initial word
  of the load is at it (decided at the certificate, `WakeFinalCAO.hnt_cert`),
  so its loaded word is `0`.
- `hown0_W`: `wake_init`'s `hown0` first conjunct (`OwnInit`), given the
  loaded `scc_rt_nthreads` word `0` (`hnt`, from `hnt_of`).
-/
import Spike.Lib.WakeOAb
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeOInit

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.WakePh (lo ownG ownW phW inPc)
open Spike.Lib.A64.Rt (RuntimeLayout)

/-- **A successful parsed load is at an entry clear of the layout.** -/
theorem clear_of_loadParsed {H : Scc.Sem.Hooks isaLSE2} {E : Scc.Sem.Entry} {Λ : Scc.Sem.Layout}
    {prog : Program} {secs : Scc.Sem.DataSecs} {t0 : (Scc.Sem.A64.machine H).Cfg}
    (h : Scc.Sem.A64.loadParsed H E Λ prog secs = some t0) : E.clear Λ = true := by
  simp only [Scc.Sem.A64.loadParsed] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    exact hc.2
  · cases h

/-- **The phase at the code's base is `13`.** -/
theorem phW_lo : phW lo = 13 := by rw [Spike.Lib.A64.WakePh.phW_eq]; decide +kernel

/-- **At the code's base, `ownG` is `ownW` at phase `13`.** -/
theorem ownG_lo {L : RuntimeLayout} (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    {s : State} (hpc : pcOf s = lo) (a : BitVec 64) : ownG L a s = ownW L a 13 := by
  have hn : ∀ l₁ l₂ x, codeOf lo wakeProg l₁ = some x → lo < x → ¬ inPc L l₁ l₂ s := by
    rintro l₁ l₂ x hx hlt ⟨h1, -⟩
    rw [hlab _ _ hx, hpc] at h1
    have : x < 2 ^ 64 := by
      have := Spike.Lib.A64.PhRec.le_codeEnd_of_codeOf hx
      have : Scc.Sem.A64.codeEnd lo wakeProg < 2 ^ 64 := by decide +kernel
      omega
    simp [Nat.mod_eq_of_lt this] at h1
    omega
  unfold ownG
  simp only [hn "scc_rt_alloc_tcb" "scc_rt_thread_reserve" 2164712 (by rw [← codeT_eq]; decide +kernel) (by decide),
    hn "scc_rt_thread_init" "scc_rt_stack_release" 2165244 (by rw [← codeT_eq]; decide +kernel) (by decide),
    hn ".L21_wc_main.sp4" ".L21_wc_main.sp6" 2169268 (by rw [← codeT_eq]; decide +kernel) (by decide),
    hn ".L21_wc_main.sp6" ".L21_wc_main.stack_grow" 2169292 (by rw [← codeT_eq]; decide +kernel) (by decide),
    hn "scc_rt_abort" "scc_rt_thr_worker" 2167996 (by rw [← codeT_eq]; decide +kernel) (by decide), ↓reduceIte, hpc, phW_lo]

/-- **`scc_rt_nthreads` starts at `0`** (a decided fact of the emitted
output, as `rtInitOk` for the runtime's words): its symbol resolves to a
data label and no initial word of the load (`initOf`) is at it. -/
def NtZ (Λ : Scc.Sem.Layout) (o : Scc.Cert.PlaceOK.A64.Out) : Bool :=
  (Scc.Cert.Rt.A64.symLab Λ.code.lo o.prog (Scc.Sem.loadSyms Λ o.secs.rodata) "scc_rt_nthreads").isSome &&
    ((Scc.Cert.Rt.A64.initOf Λ o.prog o.secs).find?
      (·.1 == ⟨Scc.Cert.Rt.A64.rtA Λ o.prog o.secs "scc_rt_nthreads", 8⟩)).isNone

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- The loaded thread's pc is the code's base. -/
theorem pc_load (hlo : Λ0.code.lo = lo) (E : Scc.Sem.Entry) :
    pcOf (Scc.Sem.A64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata)) = lo := by
  show (Int64.ofNat Λ0.code.lo).toBitVec.toNat = lo
  rw [hlo]; decide

/-- **`hown0_W`'s `hnt` from `NtZ`**: the loaded `scc_rt_nthreads` word
is `0`. -/
theorem hnt_of (hnz : NtZ Λ0 o = true) :
    (Spike.Lib.A64.PhRec.m0Of (Ly).Λ o.prog o.secs).initVal ⟨Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab, 8⟩ = 0 := by
  simp only [NtZ, Bool.and_eq_true, Option.isSome_iff_exists] at hnz
  obtain ⟨⟨a, ha⟩, hn⟩ := hnz
  have hl : (Ly).lab "scc_rt_nthreads" = Int64.ofNat a :=
    Scc.Cert.Rt.A64.label_threadAt_of_symLab (E := Scc.Sem.Entry.linux)
      (Scc.Cert.Link.A64.symsAround_of_loadOk (PlaceW.loadOk_link_of_placeW i hp)) ha
  have hr : Scc.Cert.Rt.A64.rtA Λ0 o.prog o.secs "scc_rt_nthreads" = BitVec.ofNat 64 a := by
    simp [Scc.Cert.Rt.A64.rtA, ha]
  rw [hr] at hn
  have hnt : Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab = BitVec.ofNat 64 a := by
    simp [Spike.Lib.A64.Rt.Reserve.ntA, hl]
  unfold Memory.initVal
  rw [hnt]
  show ((Scc.Cert.Rt.A64.initOf Λ0 o.prog o.secs).find? _ |>.map (·.2)).getD 0 = 0
  rw [Option.isNone_iff_eq_none.mp hn]
  rfl

/-- **`wake_init`'s `OwnInit`**: the loaded thread's owned words (`ownG` at
phase `13`: the four counters and `scc_rt_nthreads`, each `0`) are the
load's, given the loaded `scc_rt_nthreads` word `0` (`hnt`). -/
theorem hown0_W (hpa : Scc.Sem.A64.textProgram SccCertificate.asm = .ok o.prog)
    (hwp : Scc.Sem.A64.textProgram SccCertificate.asm = .ok wakeProg) (hlo : Λ0.code.lo = lo)
    (hnt : (Spike.Lib.A64.PhRec.m0Of (Ly).Λ o.prog o.secs).initVal
      ⟨Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab, 8⟩ = 0) (E : Scc.Sem.Entry) :
    ∀ t0, Scc.Sem.A64.loadParsed (Scc.Sem.A64.kernel 1) E (Ly).Λ o.prog o.secs = some t0 →
      Spike.Lib.Consumer1.OwnInit (ownG (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab)
        (Scc.Sem.A64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata))) t0.1.mem := by
  intro t0 hl
  have hE := clear_of_loadParsed hl
  have he : Scc.Sem.A64.loadParsed (Scc.Sem.A64.kernel 1) E (Ly).Λ o.prog o.secs = _ :=
    Scc.Cert.Link.A64.loadParsed_of_loadOk (H := Scc.Sem.A64.kernel 1) (PlaceW.loadOk_link_of_placeW i hp) hE
  rw [he] at hl
  cases hl
  rw [ownG_lo (WakeOAb.hlab_W hp i hpa hwp hlo) (pc_load hp i hlo E)]
  intro L v hm
  simp only [ownW, Spike.Lib.A64.PhRec.ownOf, Nat.reduceMod, Nat.reduceDiv, ↓reduceIte, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
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

end Spike.Lib.WakeOInit

/-- info: 'Spike.Lib.WakeOInit.hown0_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeOInit.hown0_W
