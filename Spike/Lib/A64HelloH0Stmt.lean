/-
**`H0StmtH` at hello's root** (AArch64;
assembled from the root's level-0 pieces): the level before the allocation
`RootH0.inv0H` is a closed invariant inside `W0H` (`RootH0.h0H`), contains the start pair (`RootH0.hstH`, given the
start segment `hst0`) and is never at the clone (`StartGlue.noCloneH_of`: `W0H`'s per-state facts `X0WH` are off
the clone's pc).

- `h0Stmt_root`: `H0StmtH` at `W0 := W0H`, `inv0 := inv0H`, `Start := StartPH`, the take `TakeCKS` at the site and
  `ClH`, the side `msH … (I3 … inv0H inv1 inv2)` (`HelloRootO.helloDR`'s level 0).
-/
import Spike.Lib.A64HelloRootH0
import Spike.Lib.A64HelloStartGlue

namespace Spike.Lib.A64.HelloPh.H0Stmt

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lsize)
open Spike.Lib.A64ConsumerA (I3 TakeCKS)
open Spike.Lib.A64.WakeWf (DtW)
open Spike.Lib.A64.HelloPh.StartH0B (StartPH W0H)
open Spike.Lib.A64.HelloPh.RootH0 (msH msBotH inv0H h0H hstH)
open Spike.Lib (FragS SegWS)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloPreA (H0StmtH)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw i

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw i

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL

variable (E : Entry) (rd : TermRun.Word → Prop) (Ctx : FragS isaLSE2) (ls0 ls : Lsize) (frM : TermRun.Frame)
  (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)
  (inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)

/-- **`H0StmtH` at the root** (module doc), given the start segment `hst0` (`RootH0.hstH`'s). -/
theorem h0Stmt_root
    (hst0 : SegWS (W0H (asm := asm) hpw i E DtW Ctx (ls0T ls0) frM) (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly)))
      helloSrc (LB) (msBotH (asm := asm) hpw i E rd ls inv1 inv2) (StartPH hpw i E) (fun _ _ _ => False)) :
    H0StmtH (W0H (asm := asm) hpw i E DtW Ctx (ls0T ls0) frM) (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly))) (LB)
      (msH (asm := asm) hpw i E rd ls
        (I3 (AR) (LB) (ls0T ls) (inv0H (asm := asm) hpw i E rd Ctx ls0 ls frM inv1 inv2) inv1 inv2))
      (Ly) (StartPH hpw i E) (inv0H (asm := asm) hpw i E rd Ctx ls0 ls frM inv1 inv2) :=
  ⟨h0H hpw i E rd Ctx ls0 ls frM inv1 inv2,
    fun s c fs h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact hstH hpw i E rd Ctx ls0 ls frM inv1 inv2 hst0,
    Spike.Lib.A64.HelloPh.StartGlue.noCloneH_of (h0H hpw i E rd Ctx ls0 ls frM inv1 inv2)⟩

end Spike.Lib.A64.HelloPh.H0Stmt

/-- info: 'Spike.Lib.A64.HelloPh.H0Stmt.h0Stmt_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.H0Stmt.h0Stmt_root
