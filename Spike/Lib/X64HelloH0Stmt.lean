/-
**`H0StmtH` at hello's root** (x86-64; the twin of `Spike/Lib/A64HelloH0Stmt.lean`: the level-0 statement
`HelloHClW.hClH_of` and `HelloSegEnd.hpc_ofR` take as `h0`, assembled from the root's level-0 pieces): the level
before the allocation `RootH0.inv0Hg` is a closed invariant inside `W0Hg` (`RootH0.h0Hg`), contains the start pair
(`RootH0.hstHg`, given the start segment `hst0`) and is never at the clone (`StartGlue.noCloneH_of`: `W0Hg`'s
per-state facts `X0WH` are off the clone's pc).

- `h0Stmt_rootg`: `H0StmtH` at `W0 := W0Hg own`, `inv0 := inv0Hg own`, `Start := StartPH`, the take `TakeCKS` at
  the site and `ClH`, the side `msHg … own (I3 … (inv0Hg own) inv1 inv2)`, at any own map `own`.

## Differences from the AArch64 version

- Over x86-64's `isa`, the assembly an `Asm`, the placement a `PlaceWX` (`RuntimeLayout.ofPlaceWX`), as
  `X64HelloRootH0`; the clone's pc is `X64HelloPreA.clonePcH` (the `syscall` at `.Lwc_main.x3 + 94`). The
  statement and proof are A64's.
-/
import Spike.Lib.X64HelloRootH0
import Spike.Lib.X64HelloStartGlue

namespace Spike.Lib.X64.HelloPh.H0Stmt

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib.X64ConsumerA (I3 TakeCKS)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64.HelloPh.StartH0B (StartPH W0Hg)
open Spike.Lib.X64.HelloPh.RootH0 (msHg msBotHg inv0Hg h0Hg hstHg)
open Spike.Lib (FragS SegWS PlaceWX)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloPreA (H0StmtH)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw i

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

variable (E : Entry) (rd : TermRun.Word → Prop) (Ctx : FragS isa) (ls0 ls : Lsize) (frM : TermRun.Frame)
  (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa)
  (inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa)

/-- **`H0StmtH` at the root at any own map `own`** (module doc, at `W0Hg own` and `RootH0`'s `…g` forms), given the
start segment `hst0` (`RootH0.hstHg`'s). -/
theorem h0Stmt_rootg {own : State → List (Loc × Val)}
    (hst0 : SegWS (W0Hg (asm := asm) hpw i own E DtW Ctx (ls0T ls0) frM)
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) helloSrc (LB) (msBotHg (asm := asm) hpw i E rd ls inv1 inv2 own)
      (StartPH hpw i E) (fun _ _ _ => False)) :
    H0StmtH (W0Hg (asm := asm) hpw i own E DtW Ctx (ls0T ls0) frM) (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly)))
      (LB)
      (msHg (asm := asm) hpw i E rd ls own
        (I3 (AR) (LB) (ls0T ls) (inv0Hg (asm := asm) hpw i E rd Ctx ls0 ls frM inv1 inv2 own) inv1 inv2))
      (Ly) (StartPH hpw i E) (inv0Hg (asm := asm) hpw i E rd Ctx ls0 ls frM inv1 inv2 own) :=
  ⟨h0Hg hpw i E rd Ctx ls0 ls frM inv1 inv2 own,
    fun s c fs h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact hstHg hpw i E rd Ctx ls0 ls frM inv1 inv2 own hst0,
    Spike.Lib.X64.HelloPh.StartGlue.noCloneH_of (h0Hg hpw i E rd Ctx ls0 ls frM inv1 inv2 own)⟩

end Spike.Lib.X64.HelloPh.H0Stmt

/-- info: 'Spike.Lib.X64.HelloPh.H0Stmt.h0Stmt_rootg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.H0Stmt.h0Stmt_rootg
