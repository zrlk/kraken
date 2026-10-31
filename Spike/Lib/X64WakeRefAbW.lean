/-
**`RefAbW`: the threads abort path's states in `scc_rt_abort`'s code**
(x86-64, wake.w; the twin of `Spike/Lib/A64WakeRefAbW.lean`), and the facts
the refusal path's pieces share.

- `labLt`, `lab_lt`, `labNe`, `lab_ne`: label order and distinctness decided
  on the certificate's code (`pcAt`), read through `hlab` (no addresses).
- `site_out`: the take site lies below `scc_rt_abort` (`abPT`'s `hsite`).
- `refAbW`: `RefAbW` by `TPathW.ofAbPT (abPT …)`, the dispatcher's and the
  threads stub's code from `Lays` (`code_disp`, `code_stubs`).

**Unlike AArch64**: the labels are `wakeCells`' (`codeLabel`); `callee_of_pre`
is in `X64WakeRefCallee` (its region `R.callee (-72 - 8) (-24) 16`, bounds
rather than alignment); wake's abort code is `SccCode.wake_abort` (A64's
`abortIn_wakeR`); the assembly is a parameter `asm`, its cells `wakeCells`
(`hwp`; A64's `textProgram`).
-/
import Spike.Lib.X64WakeRefCallee
import Spike.Lib.X64WakeOAb
import Spike.Lib.X64WakeStartEWF
import Spike.Lib.X64WakeStartPlaceLy
import Spike.Lib.X64WakeSrcCtl

namespace Spike.Lib.X64.WakeRefAbW

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Region PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh (lo)
open SccCode (wakeCells)
open Spike.Lib.X64.WakeRefStub (Pre RefAbW callee_of_pre)

/-- `l₁` below `l₂` in the certificate's code. -/
def labLt (l₁ l₂ : String) : Bool :=
  match Scc.Cert.Rt.X64.pcAt (codeLabel lo wakeCells) l₁ 0, Scc.Cert.Rt.X64.pcAt (codeLabel lo wakeCells) l₂ 0 with
  | some x, some y => decide (x < y)
  | _, _ => false

/-- `l₁` and `l₂` at distinct places of the certificate's code. -/
def labNe (l₁ l₂ : String) : Bool :=
  match Scc.Cert.Rt.X64.pcAt (codeLabel lo wakeCells) l₁ 0, Scc.Cert.Rt.X64.pcAt (codeLabel lo wakeCells) l₂ 0 with
  | some x, some y => decide (x ≠ y)
  | _, _ => false

theorem lab_lt {lab : Label → Int64} (hlab : ∀ l x, codeLabel lo wakeCells l = some x → lab l = Int64.ofNat x)
    {l₁ l₂ : String} (h : labLt l₁ l₂ = true) : (lab l₁).toBitVec.toNat < (lab l₂).toBitVec.toNat := by
  unfold labLt at h
  split at h
  · next x y hx hy =>
    rw [Spike.Lib.X64.Rt.PhOfTab.pcAt0_eq hlab hx, Spike.Lib.X64.Rt.PhOfTab.pcAt0_eq hlab hy]
    exact of_decide_eq_true h
  · cases h

theorem lab_ne {lab : Label → Int64} (hlab : ∀ l x, codeLabel lo wakeCells l = some x → lab l = Int64.ofNat x)
    {l₁ l₂ : String} (h : labNe l₁ l₂ = true) : (lab l₁).toBitVec.toNat ≠ (lab l₂).toBitVec.toNat := by
  unfold labNe at h
  split at h
  · next x y hx hy =>
    rw [Spike.Lib.X64.Rt.PhOfTab.pcAt0_eq hlab hx, Spike.Lib.X64.Rt.PhOfTab.pcAt0_eq hlab hy]
    exact of_decide_eq_true h
  · cases h

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **The take site below `scc_rt_abort`** (`abPT`'s `hsite`). -/
theorem site_out (hpL : (Ly).prog = wakeCells) (hlo : (Ly).Λ.code.lo = lo)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → (Ly).lab l = Int64.ofNat x) :
    ∀ a, (Spike.Lib.X64.PhRec.μ (Ly)).site .take = some a →
      a < ((Ly).lab "scc_rt_abort").toBitVec.toNat ∨ ((Ly).lab "scc_rt_thr_worker").toBitVec.toNat ≤ a := by
  rw [Spike.Lib.X64.WakePh.siteW hpL hlo hlab]
  rintro a ⟨⟩
  exact .inl (lab_lt hlab (by unfold labLt; rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel))

/-- **`RefAbW`**: `AbP` at every node of the threads abort path (`abPT`). -/
theorem refAbW {asm : Asm} (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo0 : Λ0.code.lo = lo) (l : WeakMem.AllocLabel) (b : Nat) : RefAbW hp i l b := by
  intro R m0 cP cA mT m1 σC c0 hpre _
  obtain ⟨hR', hlo', hhi'⟩ := callee_of_pre hp i hpre
  have hprog := Spike.Lib.X64.WakeSrcCtl.prog_W hp i hpa hwp
  have hL : Scc.Cert.Rt.X64.Lays (Ly).exe wakeCells (Ly).pfx := hprog ▸ (Ly).lays
  have hab := SccCode.wake_abort
  have hdi : Scc.Cert.Rt.X64.Abort.dispIn wakeCells = true := by
    have h := hab; simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at h; exact h.2
  have hlab := Spike.Lib.X64WakeOAb.hlab_W hp i hpa hwp hlo0
  exact Spike.Lib.X64.WakeRefTP.TPathW.ofAbPT (Spike.Lib.X64.WakePh.abPT hlab hR' (by omega) (by omega)
    (site_out hp i hprog (Spike.Lib.X64.WakePh.StartPlaceLy.hlo_W hp i hlo0) hlab)
    (Scc.Cert.Rt.X64.Abort.code_disp hL rfl hdi) (Scc.Cert.Rt.X64.Abort.code_stubs hL rfl hab .threads))

end Spike.Lib.X64.WakeRefAbW

/-- info: 'Spike.Lib.X64.WakeRefAbW.lab_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefAbW.lab_lt

/-- info: 'Spike.Lib.X64.WakeRefAbW.lab_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefAbW.lab_ne

/-- info: 'Spike.Lib.X64.WakeRefAbW.site_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefAbW.site_out

/-- info: 'Spike.Lib.X64.WakeRefAbW.refAbW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefAbW.refAbW
