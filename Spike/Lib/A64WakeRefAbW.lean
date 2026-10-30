/-
**`RefAbW`: the threads abort path's states in `scc_rt_abort`'s code**
(AArch64, wake.w), and the facts the refusal path's pieces share.

- `labLt`, `lab_lt`, `labNe`, `lab_ne`: label order and distinctness decided
  on the certificate's code (`pcAt`), read through `hlab` (no addresses).
- `callee_of_pre`: `TObl`'s region `R.callee (-80) (-48) 0` is `OK` and
  16-aligned under `Pre`.
- `site_out`: the take site lies below `scc_rt_abort` (`abPT`'s `hsite`).
- `refAbW`: `RefAbW` by `TPathW.ofAbPT (abPT …)`, the dispatcher's and the
  threads stub's code from `Lays` (`code_disp`, `code_stubs`).
-/
import Spike.Lib.A64WakeRefStub
import Spike.Lib.A64WakeStart
import Spike.Lib.A64WakeStartPlaceLy

namespace Spike.Lib.WakeRefAbW

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib (Region)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.WakeRefStub (Pre RefAbW)

/-- `l₁` below `l₂` in the certificate's code. -/
def labLt (l₁ l₂ : String) : Bool :=
  match Scc.Cert.Rt.A64.pcAt (codeOf lo wakeProg) l₁ 0, Scc.Cert.Rt.A64.pcAt (codeOf lo wakeProg) l₂ 0 with
  | some x, some y => decide (x < y)
  | _, _ => false

/-- `l₁` and `l₂` at distinct places of the certificate's code. -/
def labNe (l₁ l₂ : String) : Bool :=
  match Scc.Cert.Rt.A64.pcAt (codeOf lo wakeProg) l₁ 0, Scc.Cert.Rt.A64.pcAt (codeOf lo wakeProg) l₂ 0 with
  | some x, some y => decide (x ≠ y)
  | _, _ => false

theorem lab_lt {lab : Label → Int64} (hlab : ∀ l x, codeOf lo wakeProg l = some x → lab l = Int64.ofNat x)
    {l₁ l₂ : String} (h : labLt l₁ l₂ = true) : (lab l₁).toBitVec.toNat < (lab l₂).toBitVec.toNat := by
  unfold labLt at h
  split at h
  · next x y hx hy =>
    rw [Spike.Lib.A64.Rt.PhOfTab.pcAt0_eq hlab hx, Spike.Lib.A64.Rt.PhOfTab.pcAt0_eq hlab hy]
    exact of_decide_eq_true h
  · cases h

theorem lab_ne {lab : Label → Int64} (hlab : ∀ l x, codeOf lo wakeProg l = some x → lab l = Int64.ofNat x)
    {l₁ l₂ : String} (h : labNe l₁ l₂ = true) : (lab l₁).toBitVec.toNat ≠ (lab l₂).toBitVec.toNat := by
  unfold labNe at h
  split at h
  · next x y hx hy =>
    rw [Spike.Lib.A64.Rt.PhOfTab.pcAt0_eq hlab hx, Spike.Lib.A64.Rt.PhOfTab.pcAt0_eq hlab hy]
    exact of_decide_eq_true h
  · cases h

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- **`TObl`'s region under `Pre`**: `OK`, 16-aligned. -/
theorem callee_of_pre {l : WeakMem.AllocLabel} {b : Nat} {R : Region} {cP : Spike.Lib.Ctl} {cA mT : BitVec 64}
    (h : Pre hp i l b R cP cA mT) :
    (R.callee (-80) (-48) 0).OK ∧ (R.callee (-80) (-48) 0).base.toNat % 16 = 0 := by
  obtain ⟨-, -, -, hR, hal, hlo, hhi, -⟩ := h
  have hb := Region.callee_base (hi' := 0) (kc := -80) (lo' := -48) hR (by omega) (by decide) (by omega)
  exact ⟨Region.callee_ok hR (by omega) (by decide) (by omega) (by omega), by omega⟩

/-- **The take site below `scc_rt_abort`** (`abPT`'s `hsite`). -/
theorem site_out (hpL : (Ly).prog = wakeProg) (hlo : (Ly).Λ.code.lo = lo)
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → (Ly).lab l = Int64.ofNat x) :
    ∀ a, (Spike.Lib.A64.PhRec.μ (Ly)).site .take = some a →
      a < ((Ly).lab "scc_rt_abort").toBitVec.toNat ∨ ((Ly).lab "scc_rt_thr_worker").toBitVec.toNat ≤ a := by
  rw [Spike.Lib.A64.WakePh.siteW hpL hlo hlab]
  rintro a ⟨⟩
  exact .inl (lab_lt hlab (by unfold labLt; rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel))

/-- **`RefAbW`**: `AbP` at every node of the threads abort path (`abPT`). -/
theorem refAbW (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hlo0 : Λ0.code.lo = lo)
    (l : WeakMem.AllocLabel) (b : Nat) : RefAbW hp i l b := by
  intro R m0 cP cA mT m1 σC c0 hpre _
  obtain ⟨hR', hal'⟩ := callee_of_pre hp i hpre
  have hprog := Spike.Lib.WakeSrcCtl.prog_W hp i hpa hwp
  have hL : Scc.Cert.Rt.A64.Lays (Ly).exe wakeProg (Ly).pfx := hprog ▸ (Ly).lays
  have hab := Spike.Lib.A64.WakePh.abortIn_wakeR
  have hdi : Scc.Cert.Rt.A64.Abort.dispIn wakeProg = true := by
    have h := hab; simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at h; exact h.2
  exact Spike.Lib.WakeRefTP.TPathW.ofAbPT (Spike.Lib.A64.WakePh.abPT (Spike.Lib.WakeOAb.hlab_W hp i hpa hwp hlo0)
    hR' hal' (by simp [Region.callee]) (by simp [Region.callee])
    (site_out hp i hprog (Spike.Lib.A64.WakePh.StartPlaceLy.hlo_W hp i hlo0)
      (Spike.Lib.WakeOAb.hlab_W hp i hpa hwp hlo0))
    (Scc.Cert.Rt.A64.Abort.code_disp hL rfl hdi) (Scc.Cert.Rt.A64.Abort.code_stubs hL rfl hab .threads))

end Spike.Lib.WakeRefAbW

/-- info: 'Spike.Lib.WakeRefAbW.refAbW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeRefAbW.refAbW
