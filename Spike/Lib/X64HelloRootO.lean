/-
**hello.w's pre-spawn premises at the root** (x86-64; the twin of `Spike/Lib/HelloRootO.lean`, itself the twin of
`WakeOPremW.oPrem_W` / `WakeOD.wakeD` at hello's choices): the instance data `helloDR` of one entry and
`X64HelloO.OPremH` at it from the segments' and take facts' premises.

The data: `gWH … cTW` (`X64HelloGOf2H`), `ownGH … ntA`, `arW`, `ClH`, `DtW`, the start's labels `L0T`/`ls0T ls`,
the take site `(Ly).lab siteL`, the level before the allocation `W0H` with its invariant `RootH0.inv0H` (the
greatest closed invariant there), the ranges `r0W`/`r1W`, every word readable (`rd := ⊤`, as wake).

Discharged here: `h0` (`RootH0.h0H`), `hinit` (`X64HelloOHinit.hinit_H` with the start from `RootH0.hstH`), `ha`
(`X64HelloCompatI.hello_hμP`), `hsplit` (`X64HelloPreA.Take1X.hsplitHX`), the ranges (`X64WakeOSide.ranges_W`),
`hro`, `hwf`, `hGpl`, `hok`, `hB`, `hClc`, `hrd`, `hdt` (as wake). Left as premises: the segments `h1`/`h2` and
their per-state facts `hW0`/`hW1`/`hW2`, the take facts (`h0t`/`h0o`/`h1t`/`h2t`/`h2o`), the start segment `hst0`
(discharged at the root's table by `X64HelloCtxRdU.hst0_RdU`, consumed in `X64HelloRootInv`), and hello's source
facts `hP`/`hsafe` (`HookOK`/`SrcSafeS` at `helloSrc`) and `hti0` (the loaded thread off `Ab`/`Ac`).

- `helloDR`: the data.
- `oPremH_R`: `OPremH` at it.
- `helloDRg`, `oPremH_Rg`: the same at an own map `own` (`StartH0B.W0Hg`, `RootH0.inv0Hg`), `oPremH_Rg` with the
  start's relation at the load (`hinit`) a premise; `helloDR` and `oPremH_R` are these at `ownGH`.
- `oPremH_RX`: `oPremH_Rg` at `ownGHXW` (both TCB self words owned), `hinit` from `X64HelloOHinit.hinit_Hg` with
  `X64HelloOInitX.hown0_HX` and the start segment `hst0` at `msBotHg … ownGHXW`.

Unlike AArch64 (`isaLSE2`, the assembly a `String` parsed by `textProgram`, the placement `PlaceW`, the loaded
program `helloProg`), the instruction set is `isa`, the assembly an `Asm` whose cells (`cellsOf`) are
`helloCells`, its data sections read off `asm.text` and its label offsets the placement's (`hoffs`, which
`X64HelloOHinit.hinit_H` asks), and the placement is `PlaceWX`.
-/
import Spike.Lib.X64HelloO
import Spike.Lib.X64HelloOHinit
import Spike.Lib.X64HelloRootH0
import Spike.Lib.X64HelloWcInv3
import Spike.Lib.X64HelloCompatI
import Spike.Lib.X64WakeOPremW
import Spike.Lib.X64HelloGOf2H
import Spike.Lib.X64HelloTake1X
import Spike.Lib.X64HelloOInitX

namespace Spike.Lib.X64HelloRootO

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib.X64WakeT1 Spike.Lib.X64WakeA64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloO (ODataH OPremH IH)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64.HelloPh.StartH0B (StartPH W0H W0Hg)
open Spike.Lib.X64.HelloPh.RootH0 (inv0H inv0Hg msBotH h0H hstH)
open Spike.Lib (FragS PlaceWX)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

/-- **The root's instance data of one entry at an own map `own`** (see the module doc; wake's `WakeOD.wakeD`):
the level before the allocation `W0Hg own` with its invariant `inv0Hg own`. `helloDR` is it at `ownGH`. -/
noncomputable def helloDRg (own : State → List (Loc × Val)) (E : Entry) (Ctx : FragS isa) (ls : Lsize)
    (frM : TermRun.Frame)
    (W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa)
    (W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa) : ODataH where
  rd := fun _ => True
  G := Spike.Lib.X64HelloGOf2H.gWH hp i (Spike.Lib.X64WakeHG.cTW hp i)
  own := fun s _ => own s
  ar := Spike.Lib.X64.WakeOD.arW hp i
  Cl := Spike.Lib.X64.HelloPh.ClH (Ly)
  Dt := DtW
  L0 := L0T (Ly).Λ
  ls0 := ls0T ls
  a := AX
  W0 := W0Hg (asm := asm) hp i own E DtW Ctx (ls0T ls) frM
  inv0 := inv0Hg (asm := asm) hp i E (fun _ => True) Ctx ls ls frM inv1 inv2 own
  W1 := W1
  inv1 := inv1
  W2 := W2
  inv2 := inv2
  r0 := Spike.Lib.X64WakeOSide.r0W hp i
  r1 := Spike.Lib.X64WakeOSide.r1W hp i

set_option hygiene false in
local notation "OG" => Spike.Lib.X64.HelloPh.ownGH (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab)

/-- **The root's instance data of one entry** (see the module doc; wake's `WakeOD.wakeD`): `helloDRg` at
`ownGH`. -/
noncomputable def helloDR (E : Entry) (Ctx : FragS isa) (ls : Lsize) (frM : TermRun.Frame)
    (W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa)
    (W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa) : ODataH :=
  helloDRg (asm := asm) hp i (OG) E Ctx ls frM W1 inv1 W2 inv2

/-- `helloDR` is inhabited at any entry, context and levels. -/
example (E : Entry) (Ctx : FragS isa) (ls : Lsize) (frM : TermRun.Frame)
    (W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa)
    (W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa) :
    (helloDR (asm := asm) hp i E Ctx ls frM W1 inv1 W2 inv2).L0 = L0T (Ly).Λ := rfl

set_option hygiene false in
local notation "D" => helloDR (asm := asm) hp i E Ctx ls frM W1 inv1 W2 inv2

set_option hygiene false in
local notation "μE" => (target (kernel 2) E).marks asm (Ly).Λ

set_option hygiene false in
local notation "DG" => helloDRg (asm := asm) hp i own E Ctx ls frM W1 inv1 W2 inv2

/-- **`OPremH` at the root's data at an own map `own`** (see the module doc), given the start's relation at the
load (`hinit`; at `ownGH`, `X64HelloOHinit.hinit_H` with the start from `RootH0.hstH`). -/
theorem oPremH_Rg (own : State → List (Loc × Val)) (hpa : cellsOf asm = some o.prog)
    /- instance facts -/
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hsub1 : (Spike.Lib.X64WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (arch : WeakMem.Arch) {B : Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    {E : Entry} {Ab Ac : State → Prop}
    {Ctx : FragS isa} {ls : Lsize} {frM : TermRun.Frame}
    {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    /- the segments after the allocations -/
    (h2 : ∀ l b n l' b' n', (DG).L0 l = none → AllocLand (DG).ar.heap (DG).ar.cells b n →
      X64ConsumerA.upd (DG).L0 l b l' = none → AllocLand (DG).ar.heap (DG).ar.cells b' n' →
      SegInvS ((DG).W2 l b n l' b' n') (TakeCKS (DG).a (DG).Cl) helloSrc
        (X64ConsumerA.upd (X64ConsumerA.upd (DG).L0 l b) l' b')
        (msOfA (Ly).Λ μE (DG).rd (DG).G (DG).own (DG).ar (fun _ _ _ _ _ => False)
          (X64ConsumerA.upd (X64ConsumerA.upd (DG).L0 l b) l' b')
          (X64ConsumerA.updN (X64ConsumerA.updN (DG).ls0 l n) l' n'))
        ((DG).inv2 l b n l' b' n'))
    (h1 : ∀ l b n, (DG).L0 l = none → AllocLand (DG).ar.heap (DG).ar.cells b n →
      Spike.Lib.X64SegWPub.SegInvSP ((DG).W1 l b n) (TakeCKS (DG).a (DG).Cl) helloSrc
        (X64ConsumerA.upd (DG).L0 l b)
        (msOfA (Ly).Λ μE (DG).rd (DG).G (DG).own (DG).ar (IH (DG)) (X64ConsumerA.upd (DG).L0 l b)
          (X64ConsumerA.updN (DG).ls0 l n)) ((DG).inv1 l b n))
    /- the per-state facts -/
    (hW0 : ∀ s c fs, (DG).inv0 s c fs → (DG).W0 s c fs →
      SFactsACH (Ly).Λ μE helloSrc (DG).rd (DG).G (DG).own (DG).ar (IH (DG)) (DG).L0 (DG).ls0 s c fs (DG).Dt Ab
        (DG).Cl Ac)
    (hW1 : ∀ l b n s c fs, (DG).L0 l = none → AllocLand (DG).ar.heap (DG).ar.cells b n → (DG).W1 l b n s c fs →
      SFactsACH (Ly).Λ μE helloSrc (DG).rd (DG).G (DG).own (DG).ar (IH (DG))
        (X64ConsumerA.upd (DG).L0 l b) (X64ConsumerA.updN (DG).ls0 l n) s c fs (DG).Dt Ab (DG).Cl Ac)
    (hW2 : ∀ l b n l' b' n' s c fs, (DG).L0 l = none → AllocLand (DG).ar.heap (DG).ar.cells b n →
      X64ConsumerA.upd (DG).L0 l b l' = none → AllocLand (DG).ar.heap (DG).ar.cells b' n' →
      (DG).W2 l b n l' b' n' s c fs →
      SFactsACH (Ly).Λ μE helloSrc (DG).rd (DG).G (DG).own (DG).ar (IH (DG))
        (X64ConsumerA.upd (X64ConsumerA.upd (DG).L0 l b) l' b')
        (X64ConsumerA.updN (X64ConsumerA.updN (DG).ls0 l n) l' n') s c fs (DG).Dt Ab (DG).Cl Ac)
    /- the take facts at the three levels -/
    (h0t : Spike.Lib.X64HelloPreA.H0TakeH (Ly) (AX) (DG).inv0)
    (h0o : Spike.Lib.X64HelloPreA.H0TakeOwnH (Ly) (AX) (DG).inv0)
    (h1t : Spike.Lib.X64HelloPreA.Take1X.H1TakeXH (Ly) (AX) inv1)
    (h2t : Spike.Lib.X64HelloPreA.H2TakeH (Ly) (AX) inv2)
    (h2o : Spike.Lib.X64HelloPreA.H2TakeOwnH (Ly) (AX) inv2)
    /- hello's source facts -/
    (hP : HookOK (srcPo 2 arch helloSrc) helloSrc)
    (hsafe : SrcSafeS (srcPo 2 arch helloSrc) helloSrc (IH (DG)))
    (hti0 : ∀ d : Cfg, (target (kernel 1) E).load asm (Ly).Λ = some d → TIC Ab Ac [] d)
    /- the start's relation at the load -/
    (hinit : ∀ d : Cfg, (target (kernel 1) E).load asm (Ly).Λ = some d →
      ∃ s0, (srcS helloSrc arch).init s0 ∧ Spike.Lib.X64HelloO.R1H arch (Ly).Λ (μE) (DG) d s0) :
    OPremH arch (Ly).Λ B asm E Ab Ac (DG) := by
  obtain ⟨hs0, hs1, hz0, hz1, hdj, hw0, hw1⟩ := Spike.Lib.X64WakeOSide.ranges_W hp i hsub1
  have ha : (μE).site .take = some (AX).toBitVec.toNat :=
    (Spike.Lib.X64HelloCompatI.hello_hμP hp i (H := kernel 2) (E := E) hpa).1
  exact {
    h2 := h2
    h1 := h1
    h0 := Spike.Lib.X64.HelloPh.RootH0.h0Hg hp i E (fun _ => True) Ctx ls ls frM inv1 inv2 own
    hW0 := hW0
    hW1 := hW1
    hW2 := hW2
    ha := ha
    hsplit := fun lbl lsize s c fs hl hI hH a ha' hpc => by
      rw [ha] at ha'
      cases ha'
      exact Spike.Lib.X64HelloPreA.Take1X.hsplitHX (Spike.Lib.X64.WakeOSplit.r0W_al hp i) h0t h0o h1t h2t h2o
        lbl lsize s c fs hl hI hH hpc
    hs0 := hs0
    hs1 := hs1
    hz0 := hz0
    hz1 := hz1
    hro := Spike.Lib.X64WakeOSide.hro_W hp i
    hd := hdj
    hw0 := hw0
    hw1 := hw1
    hP := hP
    hClc := fun _ h => h.2.2
    hsafe := hsafe
    hrd := SrcRd.of_all fun _ => trivial
    hwf := Spike.Lib.X64WakeOSide.hwf_W hp i
    hGpl := Spike.Lib.X64HelloGOf2H.hGpl_gWH hp i _ hpin2
    hok := let h := Spike.Lib.X64.Rt.ArenaW.arOf_ok (PlaceWX.link i hp) hc
      ⟨h.ctr_out, h.units, h.off, h.units_lt, h.cells_lt, h.ctr_lt⟩
    hB := hB
    hdt := Spike.Lib.X64.WakeWf.hdtW
    hinit := hinit
    hti0 := hti0 }

/-- **`OPremH` at the root's data** (see the module doc): `oPremH_Rg` at `ownGH`, the start's relation by
`X64HelloOHinit.hinit_H` with the start from `RootH0.hstH`. -/
theorem oPremH_R (hpa : cellsOf asm = some o.prog)
    (hhp : cellsOf asm = some SccCode.helloCells) (hd : dataSections asm.text = some o.secs)
    (hoffs : asm.labelOffs = o.labelOffs)
    /- instance facts -/
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hsub1 : (Spike.Lib.X64WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hnz : Spike.Lib.X64WakeOInit.NtZ Λ0 o = true)
    (arch : WeakMem.Arch) {B : Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    {E : Entry} (hE : E.clear (Ly).Λ = true) {Ab Ac : State → Prop}
    {Ctx : FragS isa} {ls : Lsize} {frM : TermRun.Frame}
    {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    /- the start segment at `msBotH`, no exit -/
    (hst0 : Spike.Lib.SegWS (W0H (asm := asm) hp i E DtW Ctx (ls0T ls) frM)
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) helloSrc (L0T (Ly).Λ)
      (msBotH (asm := asm) hp i E (fun _ => True) ls inv1 inv2) (StartPH hp i E) (fun _ _ _ => False))
    /- the segments after the allocations -/
    (h2 : ∀ l b n l' b' n', (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      X64ConsumerA.upd (D).L0 l b l' = none → AllocLand (D).ar.heap (D).ar.cells b' n' →
      SegInvS ((D).W2 l b n l' b' n') (TakeCKS (D).a (D).Cl) helloSrc
        (X64ConsumerA.upd (X64ConsumerA.upd (D).L0 l b) l' b')
        (msOfA (Ly).Λ μE (D).rd (D).G (D).own (D).ar (fun _ _ _ _ _ => False)
          (X64ConsumerA.upd (X64ConsumerA.upd (D).L0 l b) l' b')
          (X64ConsumerA.updN (X64ConsumerA.updN (D).ls0 l n) l' n'))
        ((D).inv2 l b n l' b' n'))
    (h1 : ∀ l b n, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      Spike.Lib.X64SegWPub.SegInvSP ((D).W1 l b n) (TakeCKS (D).a (D).Cl) helloSrc (X64ConsumerA.upd (D).L0 l b)
        (msOfA (Ly).Λ μE (D).rd (D).G (D).own (D).ar (IH (D)) (X64ConsumerA.upd (D).L0 l b)
          (X64ConsumerA.updN (D).ls0 l n)) ((D).inv1 l b n))
    /- the per-state facts -/
    (hW0 : ∀ s c fs, (D).inv0 s c fs → (D).W0 s c fs →
      SFactsACH (Ly).Λ μE helloSrc (D).rd (D).G (D).own (D).ar (IH (D)) (D).L0 (D).ls0 s c fs (D).Dt Ab (D).Cl Ac)
    (hW1 : ∀ l b n s c fs, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n → (D).W1 l b n s c fs →
      SFactsACH (Ly).Λ μE helloSrc (D).rd (D).G (D).own (D).ar (IH (D))
        (X64ConsumerA.upd (D).L0 l b) (X64ConsumerA.updN (D).ls0 l n) s c fs (D).Dt Ab (D).Cl Ac)
    (hW2 : ∀ l b n l' b' n' s c fs, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      X64ConsumerA.upd (D).L0 l b l' = none → AllocLand (D).ar.heap (D).ar.cells b' n' →
      (D).W2 l b n l' b' n' s c fs →
      SFactsACH (Ly).Λ μE helloSrc (D).rd (D).G (D).own (D).ar (IH (D))
        (X64ConsumerA.upd (X64ConsumerA.upd (D).L0 l b) l' b')
        (X64ConsumerA.updN (X64ConsumerA.updN (D).ls0 l n) l' n') s c fs (D).Dt Ab (D).Cl Ac)
    /- the take facts at the three levels -/
    (h0t : Spike.Lib.X64HelloPreA.H0TakeH (Ly) (AX) (D).inv0)
    (h0o : Spike.Lib.X64HelloPreA.H0TakeOwnH (Ly) (AX) (D).inv0)
    (h1t : Spike.Lib.X64HelloPreA.Take1X.H1TakeXH (Ly) (AX) inv1)
    (h2t : Spike.Lib.X64HelloPreA.H2TakeH (Ly) (AX) inv2)
    (h2o : Spike.Lib.X64HelloPreA.H2TakeOwnH (Ly) (AX) inv2)
    /- hello's source facts -/
    (hP : HookOK (srcPo 2 arch helloSrc) helloSrc)
    (hsafe : SrcSafeS (srcPo 2 arch helloSrc) helloSrc (IH (D)))
    (hti0 : ∀ d : Cfg, (target (kernel 1) E).load asm (Ly).Λ = some d → TIC Ab Ac [] d) :
    OPremH arch (Ly).Λ B asm E Ab Ac (D) :=
  oPremH_Rg hp i (OG) hpa hpin2 hsub1 hc arch hB h2 h1 hW0 hW1 hW2 h0t h0o h1t h2t h2o hP hsafe hti0
    (Spike.Lib.X64HelloOHinit.hinit_H hp i hpa hhp hd hoffs hlo hstat hsub1 hc hnz hpin2 arch hE μE
      (IH (D)) ls (.inl ⟨rfl, rfl, hstH hp i E (fun _ => True) Ctx ls ls frM inv1 inv2 hst0⟩))

set_option hygiene false in
local notation "OX" => Spike.Lib.X64.HelloPh.ownGHXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab)

set_option hygiene false in
local notation "DX" => helloDRg (asm := asm) hp i (OX) E Ctx ls frM W1 inv1 W2 inv2

/-- **`OPremH` at the root's data at `ownGHXW`** (both TCB self words owned): `oPremH_Rg` at `ownGHXW … ntA`, the
start's relation by `X64HelloOHinit.hinit_Hg` with `own` initially owned by `X64HelloOInitX.hown0_HX` and the start
from `RootH0.hstHg` (the start segment `hst0` at `msBotHg … ownGHXW`). -/
theorem oPremH_RX (hpa : cellsOf asm = some o.prog)
    (hhp : cellsOf asm = some SccCode.helloCells) (hd : dataSections asm.text = some o.secs)
    (hoffs : asm.labelOffs = o.labelOffs)
    /- instance facts -/
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hsub1 : (Spike.Lib.X64WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hnz : Spike.Lib.X64WakeOInit.NtZ Λ0 o = true)
    (arch : WeakMem.Arch) {B : Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    {E : Entry} (hE : E.clear (Ly).Λ = true) {Ab Ac : State → Prop}
    {Ctx : FragS isa} {ls : Lsize} {frM : TermRun.Frame}
    {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    /- the start segment at `msBotHg … ownGHXW`, no exit -/
    (hst0 : Spike.Lib.SegWS (W0Hg (asm := asm) hp i (OX) E DtW Ctx (ls0T ls) frM)
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) helloSrc (L0T (Ly).Λ)
      (Spike.Lib.X64.HelloPh.RootH0.msBotHg (asm := asm) hp i E (fun _ => True) ls inv1 inv2 (OX)) (StartPH hp i E)
      (fun _ _ _ => False))
    /- the segments after the allocations -/
    (h2 : ∀ l b n l' b' n', (DX).L0 l = none → AllocLand (DX).ar.heap (DX).ar.cells b n →
      X64ConsumerA.upd (DX).L0 l b l' = none → AllocLand (DX).ar.heap (DX).ar.cells b' n' →
      SegInvS ((DX).W2 l b n l' b' n') (TakeCKS (DX).a (DX).Cl) helloSrc
        (X64ConsumerA.upd (X64ConsumerA.upd (DX).L0 l b) l' b')
        (msOfA (Ly).Λ μE (DX).rd (DX).G (DX).own (DX).ar (fun _ _ _ _ _ => False)
          (X64ConsumerA.upd (X64ConsumerA.upd (DX).L0 l b) l' b')
          (X64ConsumerA.updN (X64ConsumerA.updN (DX).ls0 l n) l' n'))
        ((DX).inv2 l b n l' b' n'))
    (h1 : ∀ l b n, (DX).L0 l = none → AllocLand (DX).ar.heap (DX).ar.cells b n →
      Spike.Lib.X64SegWPub.SegInvSP ((DX).W1 l b n) (TakeCKS (DX).a (DX).Cl) helloSrc
        (X64ConsumerA.upd (DX).L0 l b)
        (msOfA (Ly).Λ μE (DX).rd (DX).G (DX).own (DX).ar (IH (DX)) (X64ConsumerA.upd (DX).L0 l b)
          (X64ConsumerA.updN (DX).ls0 l n)) ((DX).inv1 l b n))
    /- the per-state facts -/
    (hW0 : ∀ s c fs, (DX).inv0 s c fs → (DX).W0 s c fs →
      SFactsACH (Ly).Λ μE helloSrc (DX).rd (DX).G (DX).own (DX).ar (IH (DX)) (DX).L0 (DX).ls0 s c fs (DX).Dt Ab
        (DX).Cl Ac)
    (hW1 : ∀ l b n s c fs, (DX).L0 l = none → AllocLand (DX).ar.heap (DX).ar.cells b n → (DX).W1 l b n s c fs →
      SFactsACH (Ly).Λ μE helloSrc (DX).rd (DX).G (DX).own (DX).ar (IH (DX))
        (X64ConsumerA.upd (DX).L0 l b) (X64ConsumerA.updN (DX).ls0 l n) s c fs (DX).Dt Ab (DX).Cl Ac)
    (hW2 : ∀ l b n l' b' n' s c fs, (DX).L0 l = none → AllocLand (DX).ar.heap (DX).ar.cells b n →
      X64ConsumerA.upd (DX).L0 l b l' = none → AllocLand (DX).ar.heap (DX).ar.cells b' n' →
      (DX).W2 l b n l' b' n' s c fs →
      SFactsACH (Ly).Λ μE helloSrc (DX).rd (DX).G (DX).own (DX).ar (IH (DX))
        (X64ConsumerA.upd (X64ConsumerA.upd (DX).L0 l b) l' b')
        (X64ConsumerA.updN (X64ConsumerA.updN (DX).ls0 l n) l' n') s c fs (DX).Dt Ab (DX).Cl Ac)
    /- the take facts at the three levels -/
    (h0t : Spike.Lib.X64HelloPreA.H0TakeH (Ly) (AX) (DX).inv0)
    (h0o : Spike.Lib.X64HelloPreA.H0TakeOwnH (Ly) (AX) (DX).inv0)
    (h1t : Spike.Lib.X64HelloPreA.Take1X.H1TakeXH (Ly) (AX) inv1)
    (h2t : Spike.Lib.X64HelloPreA.H2TakeH (Ly) (AX) inv2)
    (h2o : Spike.Lib.X64HelloPreA.H2TakeOwnH (Ly) (AX) inv2)
    /- hello's source facts -/
    (hP : HookOK (srcPo 2 arch helloSrc) helloSrc)
    (hsafe : SrcSafeS (srcPo 2 arch helloSrc) helloSrc (IH (DX)))
    (hti0 : ∀ d : Cfg, (target (kernel 1) E).load asm (Ly).Λ = some d → TIC Ab Ac [] d) :
    OPremH arch (Ly).Λ B asm E Ab Ac (DX) :=
  oPremH_Rg hp i (OX) hpa hpin2 hsub1 hc arch hB h2 h1 hW0 hW1 hW2 h0t h0o h1t h2t h2o hP hsafe hti0
    (Spike.Lib.X64HelloOHinit.hinit_Hg hp i hpa hd hoffs hstat hsub1 hc hpin2 arch hE μE (IH (DX)) ls
      (Spike.Lib.X64HelloOInitX.hown0_HX hp i hpa hhp hlo (Spike.Lib.X64WakeOInit.hnt_of hp i hnz) E)
      (.inl ⟨rfl, rfl, Spike.Lib.X64.HelloPh.RootH0.hstHg hp i E (fun _ => True) Ctx ls ls frM inv1 inv2 (OX) hst0⟩))

end Spike.Lib.X64HelloRootO

/-- info: 'Spike.Lib.X64HelloRootO.oPremH_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloRootO.oPremH_R

/-- info: 'Spike.Lib.X64HelloRootO.oPremH_Rg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloRootO.oPremH_Rg

/-- info: 'Spike.Lib.X64HelloRootO.oPremH_RX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloRootO.oPremH_RX
