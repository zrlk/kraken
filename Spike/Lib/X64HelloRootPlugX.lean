/-
**hello.w's root base at the self words** (x86-64): `X64HelloRootPlug`'s `RootRest.toBase` and `X64HelloRootOkb`'s
box-call premises with `h2`'s memory side `H2RtX.ms2HX` (main's owned words `ownGHXW`) in place of `H2Rt.ms2H`.

- `okb_own`: `Call.OKB` at `msOfA`'s side does not depend on the owned words.
- `hokb_HX`, `hg_HX`: `RootOkb.hokb_H`, `hg_H` at `ms2HX` (`WakeBoxW.okb_ms1` after `okb_own`, the geometry by
  `rfl`).
- `hK2_HX`, `hpub2_HX`: `RootPlug.hK2_H`, `hpub2_H` at `ms2HX`.
- `RootRest.toBaseX`: `RootRest.toBase` at `ms2HX`.

## Unlike AArch64

AArch64's third level owns `ownGH`, so its base is at `A64HelloH2Rt`'s side only; x86-64's main also holds its own
and the worker's TCB words up to the clone, so the root's base is at `ms2HX`.
-/
import Spike.Lib.X64HelloRootPlug
import Spike.Lib.X64HelloRootOkb
import Spike.Lib.X64HelloH2RtX

namespace Spike.Lib.X64.HelloPh.RootPlugX

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (MemSide PlaceWX)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64WakeLoadT (L0T)
open Spike.Lib.X64.HelloPh.RootPlug

variable {asm : Scc.Sem.X64.Asm}
variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "AW" => Spike.Lib.X64.WakeOD.arW hpw IH

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

section
open CoreLang CoreTerm Scc.Sem Scc.Sem.X64
open Spike.Lib.X64Consumer (Lbl)
open Spike.Lib.X64ConsumerS (OwnS InvS)
open Spike.Lib.X64ConsumerA (msOfA)

/-- **The box call's premises ignore the owned words**: `Call.OKB` at `msOfA`'s side carries to any other owned
words (`Call.OKS` reads no `own`). -/
theorem okb_own {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own own' : OwnS} {ar : Arena} {I : InvS} {L0 : Lbl} {ls0 : Lsize} {fs : List TermRun.Frame}
    {lab : Label → Int64} {q : Spike.Lib.X64.Alloc.Call} (h : q.OKB (msOfA Λ μ rd G own ar I L0 ls0 fs) lab) :
    q.OKB (msOfA Λ μ rd G own' ar I L0 ls0 fs) lab :=
  ⟨⟨h.toS.site, h.toS.hold, h.toS.n_lt, h.toS.ctr, h.toS.heap, h.toS.room, h.toS.cells, h.toS.units, h.toS.off,
    h.toS.accs, h.toS.rt, h.toS.mp, h.toS.grow, h.toS.hdr⟩, h.newOk, h.term, h.ev, h.one⟩

end

set_option hygiene false in
/-- `h2`'s memory side family at the self words. -/
local notation "MS2X" => Spike.Lib.X64.HelloPh.H2RtX.ms2HX asm hpw IH

/-- **`RootOkb.hokb_H` at `ms2HX`**: the box call's premises at level 1's side carry to `h2`'s side at the self
words, given the counter's zeroed item. -/
theorem hokb_HX (E : Scc.Sem.Entry) (ls : Lsize) (hc : Spike.Lib.X64.Rt.CtrZ o) :
    ∀ l b n l' b' n', Spike.Lib.X64.HelloPh.Fresh2H (AW) (LB) l b n l' b' n' →
      ∀ q : Spike.Lib.X64.Alloc.Call, q.OKB (RootOkb.msBH (asm := asm) hpw i0 E ls l b n) (Ly).lab →
        q.OKB (MS2X E ls l b n l' b' n' []) (Ly).lab := by
  intro l b n l' b' n' hf q h
  have h0 := Spike.Lib.X64.Rt.ArenaW.arOf_ok (PlaceWX.link (IH) hpw) hc
  have hok : (AW).OK := ⟨h0.ctr_out, h0.units, h0.off, h0.units_lt, h0.cells_lt, h0.ctr_lt⟩
  exact Spike.Lib.X64.WakeBoxW.okb_ms1 hok (Spike.Lib.X64.WakeOD.arW_newOk hpw (IH)) hf.2.2.1 hf.2.2.2 (okb_own h)

/-- **`RootOkb.hg_H` at `ms2HX`**: `h2`'s side at the self words and the box side read the arena's geometry off
`arW`. -/
theorem hg_HX (E : Scc.Sem.Entry) (ls : Lsize) :
    ∀ l b n l' b' n', Spike.Lib.X64.HelloPh.Fresh2H (AW) (LB) l b n l' b' n' →
      (MS2X E ls l b n l' b' n' []).heap = (RootOkb.msBH (asm := asm) hpw i0 E ls l b n).heap ∧
        (MS2X E ls l b n l' b' n' []).cells = (RootOkb.msBH (asm := asm) hpw i0 E ls l b n).cells ∧
        (MS2X E ls l b n l' b' n' []).off = (RootOkb.msBH (asm := asm) hpw i0 E ls l b n).off ∧
        (MS2X E ls l b n l' b' n' []).units = (RootOkb.msBH (asm := asm) hpw i0 E ls l b n).units :=
  fun _ _ _ _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩

/-- **`hK2` at `ms2HX`** (`msOfA`'s, by `rfl`). -/
theorem hK2_HX (asm : Scc.Sem.X64.Asm) (E : Scc.Sem.Entry) (ls : Lsize) :
    ∀ l b n l' b' n', Spike.Lib.X64.HelloPh.Fresh2H (AW) (LB) l b n l' b' n' →
      (Spike.Lib.X64.HelloPh.H2RtX.ms2HX asm hpw IH E ls l b n l' b' n' []).K = some Scc.Sem.X64.abi :=
  fun _ _ _ _ _ _ _ => rfl

/-- **`hpub2` at `ms2HX`** (`arW`'s `pub`). -/
theorem hpub2_HX (asm : Scc.Sem.X64.Asm) (E : Scc.Sem.Entry) (ls : Lsize) :
    ∀ l b n l' b' n', Spike.Lib.X64.HelloPh.Fresh2H (AW) (LB) l b n l' b' n' →
      (Spike.Lib.X64.HelloPh.H2RtX.ms2HX asm hpw IH E ls l b n l' b' n' []).pub :=
  fun _ _ _ _ _ _ _ => trivial

/-- **The base from its rest at the self words**: `RootRest.toBase` with `h2`'s side `ms2HX` (`hK2_HX`,
`hpub2_HX`). -/
noncomputable def toBaseX (asm : Scc.Sem.X64.Asm) (E : Scc.Sem.Entry)
    (B : RootRest (Ly) (LB) (AW) (Spike.Lib.X64.HelloPh.H2RtX.ms2HX asm hpw IH E))
    (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) (hc : Spike.Lib.X64.Rt.CtrZ o) :
    Spike.Lib.X64.HelloPh.HelloRootBase (Ly) (LB) (AW) (Spike.Lib.X64.HelloPh.H2RtX.ms2HX asm hpw IH E) where
  hp := hp_H hpw i0 hpa hhp
  hlo := hlo_H hpw i0 hlo0
  hΛ := hΛ_H hpw i0
  hlab := hlab_H hpw i0 hpa hhp hlo0
  hsite := hsite_H hpw i0 hpa hhp hlo0
  hro := hro_H hpw i0
  W1 := B.W1
  har := Spike.Lib.X64.HelloPh.HelloRootBase.har_W hpw i0 hc
  Dt := B.Dt
  Ctx := B.Ctx
  ls := B.ls
  frM := B.frM
  msB := B.msB
  F0 := B.F0
  hK2 := hK2_HX hpw i0 asm E B.ls
  hpub2 := hpub2_HX hpw i0 asm E B.ls
  hokb := B.hokb
  hg := B.hg
  hs := hs_H hpw i0 hA13
  hsub := hsub_H hpw i0 hA13
  hmF := hmF_H hpw i0 hA13
  hnoF := hnoF_H hpw i0 hA13
  hoffT := hoffT_H hpw i0 hA13
  hoffL := hoffL_H hpw i0
  hoffX := hoffX_H hpw i0

end Spike.Lib.X64.HelloPh.RootPlugX

/-- info: 'Spike.Lib.X64.HelloPh.RootPlugX.okb_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlugX.okb_own

/-- info: 'Spike.Lib.X64.HelloPh.RootPlugX.hokb_HX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlugX.hokb_HX

/-- info: 'Spike.Lib.X64.HelloPh.RootPlugX.hg_HX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlugX.hg_HX

/-- info: 'Spike.Lib.X64.HelloPh.RootPlugX.hK2_HX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlugX.hK2_HX

/-- info: 'Spike.Lib.X64.HelloPh.RootPlugX.hpub2_HX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootPlugX.hpub2_HX
