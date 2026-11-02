/-
**hello's root base inhabited on x86-64** (the twin of `Spike/Lib/A64HelloRootBaseInh.lean`'s `restE`/`baseE`/
`premE`): at every linked layout `Λ0` with `LayoutEX Λ0`, the base `HelloRootBase` at `h2`'s side `H2RtX.ms2HX` and
the root premises `HelloRootPremX` built from the listing's parse, at `hello_root_inv`'s choices.

- `hc_H`: the counter's zeroed item in the listing's `.bss`/`.data` (`Rt.CtrZ oH`).
- `LayoutEX.restEX`: the base's rest at `hello_root_inv`'s choices (its `let R`).
- `LayoutEX.baseEX`: the base (`RootPlugX.toBaseX` of `restEX`).
- `LayoutEX.premEX`: the root premises (`HelloRootBase.toPremX` of `baseEX`); its third level is `W2Ig ownGHXW` at
  `DtW` and the root's contexts (by `rfl`).

## Unlike AArch64

- The base is at `ms2HX` and the premises are `HelloRootPremX`, both at main's owned words with the self words
  (`ownGHXW`); the contexts are `RootUL.CtxU (LandRU.CtxRdHg … ownGHXW)` (AArch64: `ms2H`, `HelloRootPrem`,
  `CtxRdU`).
- `hpin2` is `LayoutEX`'s field (AArch64 derives it from the listing's `.zero`).
- The program is the parsed `SccCode.helloAsm : Scc.Sem.X64.Asm`; the parse is `Link.X64.parsesTo`.
-/
import Spike.Lib.X64HelloLayoutE
import Spike.Lib.X64HelloCode
import Spike.Lib.X64HelloRootInstW
import Spike.Lib.X64HelloRootPlugX
import Spike.Lib.X64HelloRootOkb
import Spike.Lib.X64HelloLandRU
import Spike.Lib.X64HelloRootL1U

namespace Spike.Lib.X64.HelloPh.RootBaseInh

open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.HelloPh.RootLit (pcfgH oH)
open Spike.Lib.X64.HelloImms (i0M iRdM)
open Spike.Lib.X64WakeLoadT (L0T)
open Scc.Cert.Link.X64 (parsesTo parsed_of_parsesTo)

private theorem lookup_mem {β : Type} : ∀ {l : List (String × β)} {k : String} {b : β},
    l.lookup k = some b → (k, b) ∈ l
  | [], _, _, h => by simp at h
  | (k', b') :: l, k, b, h => by
    by_cases hk : k = k'
    · subst hk; simp [List.lookup] at h; subst h; simp
    · have hne : (k == k') = false := by simpa using hk
      simp [List.lookup, hne] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

/-- **The counter's zeroed item** (`Rt.CtrZ`, `HelloRootBase.har_W`'s premise): `scc_rt_heap_use` labels an
all-zero item of 8 bytes in `helloSecs`. -/
theorem hc_H : Spike.Lib.X64.Rt.CtrZ oH := by
  cases h : (Scc.Cert.Link.symItems (oH.secs.bss ++ oH.secs.data)).lookup Scc.Cert.PlaceOK.heapUseSym with
  | none => exact absurd h (by decide +kernel)
  | some its =>
    refine ⟨its, lookup_mem h, ?_, ?_⟩
    · have : ((Scc.Cert.Link.symItems (oH.secs.bss ++ oH.secs.data)).lookup
        Scc.Cert.PlaceOK.heapUseSym).map Scc.Cert.Link.allZero = some true := by decide +kernel
      rw [h] at this; simpa using this
    · have : ((Scc.Cert.Link.symItems (oH.secs.bss ++ oH.secs.data)).lookup
        Scc.Cert.PlaceOK.heapUseSym).map (fun its => decide (8 ≤ Scc.Cert.Link.itemLen its)) = some true := by
        decide +kernel
      rw [h] at this; simpa using this

namespace LayoutEX

variable {Λ0 : Scc.Sem.Layout} (F : LayoutEX Λ0)

set_option hygiene false in
/-- The placed layout at the root's table. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX F.hp (iRdM Λ0)

set_option hygiene false in
local notation "AW" => Spike.Lib.X64.WakeOD.arW F.hp (iRdM Λ0)

set_option hygiene false in
local notation "MS2" => Spike.Lib.X64.HelloPh.H2RtX.ms2HX SccCode.helloAsm F.hp (iRdM Λ0) E

set_option hygiene false in
local notation "OW" => Spike.Lib.X64.HelloPh.ownGHXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab)

set_option hygiene false in
local notation "CR" => Spike.Lib.X64.HelloPh.RootUL.CtxU F.hp (i0M Λ0)
  (Spike.Lib.X64.HelloPh.LandRU.CtxRdHg (asm := SccCode.helloAsm) F.hp (i0M Λ0) E (fun _ => True) ls (OW))

/-- **The base's rest at `hello_root_inv`'s choices** (its `let R`). -/
noncomputable def restEX (E : Scc.Sem.Entry) (ls : Spike.Lib.X64Consumer.Lsize) :
    RootPlug.RootRest (Ly) (L0T (Ly).Λ) (AW) (MS2) where
  W1 := fun _ _ _ => True
  Dt := Spike.Lib.X64.WakeWf.DtW
  Ctx := CR
  ls := ls
  frM := Spike.Lib.X64HelloRdCf.frH Spike.Lib.X64.HelloPh.C0S.c0S.env
  msB := RootOkb.msBH (asm := SccCode.helloAsm) F.hp (i0M Λ0) E ls
  F0 := fun m => ∃ v m1 σ1, Spike.Lib.X64.Flow.HelloM.wcF
    (Spike.Lib.X64.WakePh.MainGlue.RS Spike.Lib.X64.HelloPh.StartH0G.helloLsw v) Spike.Lib.X64.HelloPh.StartH0G.helloD
    (Spike.Lib.X64.WakePh.MainGlue.FS (Ly) (Spike.Lib.X64.Rt.rS0 (Ly)) Spike.Lib.X64.HelloPh.StartH0G.helloLsw 0#64 v)
    m1 σ1 m
  hokb := RootPlugX.hokb_HX F.hp (i0M Λ0) E ls hc_H
  hg := RootPlugX.hg_HX F.hp (i0M Λ0) E ls

/-- **The root's base** at the linked layout, from the listing's parse (`RootPlugX.toBaseX` of `restEX`). -/
noncomputable def baseEX (hparse : parsesTo SccCode.helloAsm SccCode.helloCells SccCode.helloSecs = true)
    (E : Scc.Sem.Entry) (ls : Spike.Lib.X64Consumer.Lsize) :
    HelloRootBase (Ly) (L0T (Ly).Λ) (AW) (MS2) :=
  RootPlugX.toBaseX F.hp (i0M Λ0) SccCode.helloAsm E (F.restEX E ls) (parsed_of_parsesTo hparse).1
    (parsed_of_parsesTo hparse).1 F.hlo F.hA13 hc_H

/-- **The root's premises** at the linked layout (`HelloRootBase.toPremX` of `baseEX`). -/
noncomputable def premEX (hparse : parsesTo SccCode.helloAsm SccCode.helloCells SccCode.helloSecs = true)
    (E : Scc.Sem.Entry) (ls : Spike.Lib.X64Consumer.Lsize) : HelloRootPremX (Ly) (L0T (Ly).Λ) :=
  (F.baseEX hparse E ls).toPremX F.hp (i0M Λ0) E F.hA13 F.hpin2 F.hstat

/-- `premEX`'s third level is the root's `W2Ig ownGHXW` at `DtW` and the root's contexts (by `rfl`). -/
example (hparse : parsesTo SccCode.helloAsm SccCode.helloCells SccCode.helloSecs = true)
    (E : Scc.Sem.Entry) (ls : Spike.Lib.X64Consumer.Lsize) :
    (F.premEX hparse E ls).W2 = Spike.Lib.X64.HelloPh.W2Ig (OW) (Ly) (AW) Spike.Lib.X64.WakeWf.DtW (CR)
      (L0T (Ly).Λ) (Spike.Lib.X64WakeLoadT.ls0T ls) := rfl

end LayoutEX

end Spike.Lib.X64.HelloPh.RootBaseInh

/-- info: 'Spike.Lib.X64.HelloPh.RootBaseInh.hc_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootBaseInh.hc_H

/--
info: 'Spike.Lib.X64.HelloPh.RootBaseInh.LayoutEX.premEX' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootBaseInh.LayoutEX.premEX
