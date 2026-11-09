/-
**hello's start from the loaded thread: the start pair and the level before the allocation** (x86-64; the twin
of `Spike/Lib/A64HelloStartH0B.lean`): the start pair at hello's loaded thread and hello's `W0` at the entry's
marks, the definitions the root is written over.

- `StartPH`: the start pair (`WakeRoot.StartP`'s twin at `helloTh0`).
- `W0Hg`: `W0` at the entry's marks, hello's choices, at an own map (`X64.WakeOPremW.W0W`'s twin; the root takes
  `ownGHXW`).
- `pz_rS0_loadH`: `Pz rS0` at the loaded thread (`X64.WakePh.RootP.pz_rS0_load`).
- `entry_atH`: the start pair is at `_start`'s node with `F = FWN ∧ Pz rS0` (the start segment's entry).
- `takeCKS_iffH`: the take at the site label is `PhRec.K` at `X0WH`'s states.
- `frM_agree`: the two root choices of `frM` (`frH c0S.env`, `fun c => frH c.env`) agree at `c0S`.

## Differences from the AArch64 version

- The assembly is an `Asm` (`Scc.Sem.X64.Asm`, as `X64.WakeOPremW.W0W`; AArch64: a `String`); the placed output
  is a `PlaceWX` and the layout `RuntimeLayout.ofPlaceWX`.
- The threads abort phase is `Hello.ThreadsAb.AcH lab StartWf.pfxM` (`.Lwc_main`; x86-64's labels carry no
  function number, AArch64 takes `pfxM` from `Hello.Child`).
- `_start`'s node is `X64.Rt.entryN0` (offset `0`, no saved slots; AArch64: `Ret0.entryN` at `Abort.oE`), and
  `entry_atH` is `X64.WakePh.StartH0B.entry_atW` at `P := Pz rS0` (AArch64: `LowerA64.entry_atW` then the frame).
- `pz_rS0_loadH` is wake's `RootP.pz_rS0_load` directly (AArch64 derives it from `WakeOHinit.unowned_stack` and
  `pz_of_unowned`); `takeCKS_iffH`'s `r0Of = rS0` is `RootP.r0Of_rS0`.
- Not twinned (unreachable from the AArch64 root, so twins only live constants): `hst0_ofH`.
-/
import Spike.Lib.X64HelloStartGlue
import Spike.Lib.X64HelloClH
import Spike.Lib.X64HelloOwnG
import Spike.Lib.X64HelloStartWfL
import Spike.Lib.X64HelloC0S
import Spike.Lib.X64HelloSrc
import Spike.Lib.X64WakeOD
import Spike.Lib.X64WriteAb
import Spike.Lib.X64HelloThreadsAb
import Spike.Lib.X64HelloRdCf
import Spike.Lib.X64WakeStartH0B

namespace Spike.Lib.X64.HelloPh.StartH0B

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib (FragS PlaceWX)
open Spike.Lib.X64WakeLoadT (L0T)
open Spike.Lib.X64HelloSrc (helloSrc)
open Scc.Sem.X64 (pcOf)
open Spike.Lib.X64.Rt (entryR rtF)
open Spike.Lib.X64ConsumerA (TakeCKS)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.DmemPriv (WordsNoneP)

/-- **The root's two choices of `frM` agree at `c0S`**: `frH c0S.env` and `fun c => frH c.env` at `c0S`. -/
theorem frM_agree :
    (fun c : Spike.Lib.Ctl => Spike.Lib.X64HelloRdCf.frH c.env) c0S = Spike.Lib.X64HelloRdCf.frH c0S.env := rfl

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

set_option hygiene false in
local notation "RS" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
/-- The take site. -/
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

/-- **The start pair** (`WakeRoot.StartP`'s twin): the loaded thread, hello's start control `c0S` (thread 0 of
`setupStartT 2`), its stack `[]`. -/
def StartPH (E : Entry) : FragS isa := fun s c fs =>
  s = Scc.Sem.X64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata) ∧ c = c0S ∧ fs = []

/-- **hello's level before the allocation at the entry's marks, at an own map `own`**: `W0` at `own`, `arW`,
`helloSrc`, the write abort phase, `ClH`, hello's threads abort phase `AcH … pfxM`, `X0WH` at the take site.
The start with both TCB self words owned is it at `ownGHXW`. -/
abbrev W0Hg (own : State → List (Loc × Val)) (E : Entry) (Dt : State → Prop) (Ctx : FragS isa) (lsize : Lsize)
    (frM : TermRun.Frame) : FragS isa :=
  Spike.Lib.X64.WakeWf.W0 (Ly).Λ ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ)
    own (Spike.Lib.X64.WakeOD.arW hpw i)
    helloSrc Dt (Spike.Lib.X64.WriteAb.Ab (Ly).lab) (Spike.Lib.X64.HelloPh.ClH (Ly))
    (Spike.Lib.X64.Hello.ThreadsAb.AcH (Ly).lab Spike.Lib.X64.HelloPh.StartWf.pfxM) Ctx (L0T (Ly).Λ) lsize frM
    (X0WH (Ly) (AX))

/-- **`Pz rS0` at the loaded thread**: main's stack, in the pool, is off the entry stack's memory
(`X64.WakePh.RootP.pz_rS0_load`, at any base, cells and symbols). -/
theorem pz_rS0_loadH (E : Entry) (hE : E.Ok (Ly).Λ) :
    Spike.Lib.X64Consumer.Pz (RS)
      (Scc.Sem.X64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata)).st.1 :=
  Spike.Lib.X64.WakePh.RootP.pz_rS0_load hE.1 _ _ _

/-- **The start pair is at `_start`'s node** with the control `c0S`, on the entry stack, the frame condition
`FWN ∧ Pz rS0` (`X64.WakePh.StartH0B.entry_atW`, `pz_rS0_loadH`). -/
theorem entry_atH (E : Entry) (hE : E.Ok (Ly).Λ) :
    At (Ly).exe (Ly).endPc (entryR E)
      (fun m => (WordsNoneP (Ly).Λ m.dmem ∧ rtF (Ly) m) ∧ Spike.Lib.X64Consumer.Pz (RS) m)
      (Spike.Lib.X64.Rt.entryN0 (Ly).lab c0S)
      (Scc.Sem.X64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata)) c0S :=
  Spike.Lib.X64.WakePh.StartH0B.entry_atW hpw i c0S hE (pz_rS0_loadH hpw i E hE)

/-- **The take at the site label is `PhRec.K` at `X0WH`'s states**: the site's range there is main's stack
(`r0Of = rS0`), and `ClH` holds only at the clone's pc, which `X0WH` excludes. -/
theorem takeCKS_iffH {s s' : State} (hx : X0WH (Ly) (AX) s) :
    TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly)) s s' ↔ Spike.Lib.X64.PhRec.K (Ly) (RS) s s' := by
  have hr0 : Spike.Lib.X64.Rt.Ti2.r0Of (Ly).lab = RS := Spike.Lib.X64.WakePh.RootP.r0Of_rS0
  obtain ⟨hcl, hsr⟩ := hx
  constructor
  · rintro (⟨hpc, pm, rfl⟩ | ⟨⟨hc, -⟩, -⟩)
    · have hr := (hsr (by unfold pcOf; rw [hpc])).1
      exact ⟨hpc, pm, by rw [hr, hr0]⟩
    · exact (hcl hc).elim
  · rintro ⟨hpc, pm, rfl⟩
    have hr := (hsr (by unfold pcOf; rw [hpc])).1
    exact .inl ⟨hpc, pm, by rw [hr, hr0]⟩

end Place

end Spike.Lib.X64.HelloPh.StartH0B

/-- info: 'Spike.Lib.X64.HelloPh.StartH0B.frM_agree' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartH0B.frM_agree

/-- info: 'Spike.Lib.X64.HelloPh.StartH0B.pz_rS0_loadH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartH0B.pz_rS0_loadH

/-- info: 'Spike.Lib.X64.HelloPh.StartH0B.entry_atH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartH0B.entry_atH

/-- info: 'Spike.Lib.X64.HelloPh.StartH0B.takeCKS_iffH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartH0B.takeCKS_iffH
