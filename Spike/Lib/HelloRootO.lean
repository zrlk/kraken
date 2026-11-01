/-
**hello.w's pre-spawn premises at the root** (AArch64, the root; the twin of
`WakeOPremW.oPrem_W` / `WakeOD.wakeD` at hello's choices): the instance data `helloDR` of one entry and
`HelloO.OPremH` at it from the segments' and take facts' premises.

The data: `gWH … cTW` (`HelloGOf2H`: wake's `gW` with hello's second limit word `pinA + 120`), `ownGH … ntA`,
`arW`, `ClH`, `DtW`, the start's labels `L0T`/`ls0T ls`, the
take site `(Ly).lab siteL`, the level before the allocation `W0H` with its invariant `RootH0.inv0H` (the
greatest closed invariant there), the ranges `r0W`/`r1W`, every word readable (`rd := ⊤`, as wake).

Discharged here: `h0` (`RootH0.h0H`), `hinit` (`HelloOHinit.hinit_H` with the start from `RootH0.hstH`), `ha`
(`HelloCompatI.hello_hμP`), `hsplit` (`HelloPreA.Take1X.hsplitHX`), the ranges (`WakeOSide.ranges_W`), `hro`, `hwf`,
`hGpl`, `hok`, `hB`, `hClc`, `hrd`, `hdt` (as wake). Left as premises: the segments `h1`/`h2` and their per-state
facts `hW0`/`hW1`/`hW2`, the take facts (`h0t`/`h0o`/`h1t`/`h2t`/`h2o`), the start segment
`hst0` (`RootH0.hst0_iRd` at the root's table), and hello's source facts `hP`/`hsafe` (`HookOK`/`SrcSafeS` at
`helloSrc`, the twins of `WakeSrcOPrem.wake_hookOK`/`wake_srcSafeS`) and `hti0` (the loaded thread off `Ab`/`Ac`).

- `helloDR`: the data.
- `oPremH_R`: `OPremH` at it.
-/
import Spike.Lib.HelloO
import Spike.Lib.HelloOHinit
import Spike.Lib.A64HelloRootH0
import Spike.Lib.A64HelloWcInv3
import Spike.Lib.HelloCompatI
import Spike.Lib.WakeOPremW
import Spike.Lib.HelloGOf2H
import Spike.Lib.A64HelloTake1X

namespace Spike.Lib.HelloRootO

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib.WakeT1 Spike.Lib.WakeA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloO (ODataH OPremH IH)
open Spike.Lib.A64.WakeWf (DtW)
open Spike.Lib.A64.HelloPh.StartH0B (StartPH W0H)
open Spike.Lib.A64.HelloPh.RootH0 (inv0H msBotH h0H hstH)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL

/-- **The root's instance data of one entry** (see the module doc; wake's `WakeOD.wakeD`). -/
noncomputable def helloDR (E : Entry) (Ctx : FragS isaLSE2) (ls : Lsize) (frM : TermRun.Frame)
    (W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)
    (W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) : ODataH where
  rd := fun _ => True
  G := Spike.Lib.HelloGOf2H.gWH hp i (Spike.Lib.WakeHG.cTW hp i)
  own := fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s
  ar := Spike.Lib.WakeOD.arW hp i
  Cl := Spike.Lib.A64.HelloPh.ClH (Ly)
  Dt := DtW
  L0 := L0T (Ly).Λ
  ls0 := ls0T ls
  a := AX
  W0 := W0H (asm := asm) hp i E DtW Ctx (ls0T ls) frM
  inv0 := inv0H (asm := asm) hp i E (fun _ => True) Ctx ls ls frM inv1 inv2
  W1 := W1
  inv1 := inv1
  W2 := W2
  inv2 := inv2
  r0 := Spike.Lib.WakeOSide.r0W hp i
  r1 := Spike.Lib.WakeOSide.r1W hp i

set_option hygiene false in
local notation "D" => helloDR (asm := asm) hp i E Ctx ls frM W1 inv1 W2 inv2

set_option hygiene false in
local notation "μE" => (target (kernel 2) E).marks asm (Ly).Λ

/-- **`OPremH` at the root's data** (see the module doc). -/
theorem oPremH_R (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg) (hd : dataSections asm = some o.secs)
    /- instance facts -/
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hsub1 : (Spike.Lib.WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hnz : Spike.Lib.WakeOInit.NtZ Λ0 o = true)
    (arch : WeakMem.Arch) {B : Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    {E : Entry} (hE : E.clear (Ly).Λ = true) {Ab Ac : State → Prop}
    {Ctx : FragS isaLSE2} {ls : Lsize} {frM : TermRun.Frame}
    {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    /- open: the start segment at `msBotH`, no exit (`RootH0.hst0_iRd` at the root's table) -/
    (hst0 : Spike.Lib.SegWS (W0H (asm := asm) hp i E DtW Ctx (ls0T ls) frM)
      (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly))) helloSrc (L0T (Ly).Λ)
      (msBotH (asm := asm) hp i E (fun _ => True) ls inv1 inv2) (StartPH hp i E) (fun _ _ _ => False))
    /- open: the segments after the allocations -/
    (h2 : ∀ l b n l' b' n', (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      A64ConsumerA.upd (D).L0 l b l' = none → AllocLand (D).ar.heap (D).ar.cells b' n' →
      SegInvS ((D).W2 l b n l' b' n') (TakeCKS (D).a (D).Cl) helloSrc
        (A64ConsumerA.upd (A64ConsumerA.upd (D).L0 l b) l' b')
        (msOfA (Ly).Λ μE (D).rd (D).G (D).own (D).ar (fun _ _ _ _ _ => False)
          (A64ConsumerA.upd (A64ConsumerA.upd (D).L0 l b) l' b')
          (A64ConsumerA.updN (A64ConsumerA.updN (D).ls0 l n) l' n'))
        ((D).inv2 l b n l' b' n'))
    (h1 : ∀ l b n, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      SegInvS ((D).W1 l b n) (TakeCKS (D).a (D).Cl) helloSrc (A64ConsumerA.upd (D).L0 l b)
        (msOfA (Ly).Λ μE (D).rd (D).G (D).own (D).ar (IH (D)) (A64ConsumerA.upd (D).L0 l b)
          (A64ConsumerA.updN (D).ls0 l n)) ((D).inv1 l b n))
    /- open: the per-state facts -/
    (hW0 : ∀ s c fs, (D).inv0 s c fs → (D).W0 s c fs →
      SFactsACH (Ly).Λ μE helloSrc (D).rd (D).G (D).own (D).ar (IH (D)) (D).L0 (D).ls0 s c fs (D).Dt Ab (D).Cl Ac)
    (hW1 : ∀ l b n s c fs, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n → (D).W1 l b n s c fs →
      SFactsACH (Ly).Λ μE helloSrc (D).rd (D).G (D).own (D).ar (IH (D))
        (A64ConsumerA.upd (D).L0 l b) (A64ConsumerA.updN (D).ls0 l n) s c fs (D).Dt Ab (D).Cl Ac)
    (hW2 : ∀ l b n l' b' n' s c fs, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      A64ConsumerA.upd (D).L0 l b l' = none → AllocLand (D).ar.heap (D).ar.cells b' n' →
      (D).W2 l b n l' b' n' s c fs →
      SFactsACH (Ly).Λ μE helloSrc (D).rd (D).G (D).own (D).ar (IH (D))
        (A64ConsumerA.upd (A64ConsumerA.upd (D).L0 l b) l' b')
        (A64ConsumerA.updN (A64ConsumerA.updN (D).ls0 l n) l' n') s c fs (D).Dt Ab (D).Cl Ac)
    /- open: the take facts at the three levels -/
    (h0t : Spike.Lib.HelloPreA.H0TakeH (Ly) (AX) (D).inv0)
    (h0o : Spike.Lib.HelloPreA.H0TakeOwnH (Ly) (AX) (D).inv0)
    (h1t : Spike.Lib.HelloPreA.Take1X.H1TakeXH (Ly) (AX) inv1)
    (h2t : Spike.Lib.HelloPreA.H2TakeH (Ly) (AX) inv2)
    (h2o : Spike.Lib.HelloPreA.H2TakeOwnH (Ly) (AX) inv2)
    /- open: hello's source facts -/
    (hP : HookOK (srcPo 2 arch helloSrc) helloSrc)
    (hsafe : SrcSafeS (srcPo 2 arch helloSrc) helloSrc (IH (D)))
    (hti0 : ∀ d : Cfg, (target (kernel 1) E).load asm (Ly).Λ = some d → TIC Ab Ac [] d) :
    OPremH arch (Ly).Λ B asm E Ab Ac (D) := by
  obtain ⟨hs0, hs1, hz0, hz1, hdj, hw0, hw1⟩ := Spike.Lib.WakeOSide.ranges_W hp i hsub1
  have ho : o.prog = SccCode.helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have ha : (μE).site .take = some (AX).toBitVec.toNat := (HelloCompatI.hello_hμP hp i ho hpa).1
  exact {
    h2 := h2
    h1 := h1
    h0 := h0H hp i E (fun _ => True) Ctx ls ls frM inv1 inv2
    hW0 := hW0
    hW1 := hW1
    hW2 := hW2
    ha := ha
    hsplit := fun lbl lsize s c fs hl hI hH a ha' hpc => by
      rw [ha] at ha'
      cases ha'
      exact Spike.Lib.HelloPreA.Take1X.hsplitHX (Spike.Lib.WakeOSplit.r0W_al hp i) h0t h0o h1t h2t h2o
        lbl lsize s c fs hl hI hH hpc
    hs0 := hs0
    hs1 := hs1
    hz0 := hz0
    hz1 := hz1
    hro := Spike.Lib.WakeOSide.hro_W hp i
    hd := hdj
    hw0 := hw0
    hw1 := hw1
    hP := hP
    hClc := fun _ h => h.2.2
    hsafe := hsafe
    hrd := SrcRd.of_all fun _ => trivial
    hwf := Spike.Lib.WakeOSide.hwf_W hp i
    hGpl := Spike.Lib.HelloGOf2H.hGpl_gWH hp i _ hpin2
    hok := let h := Spike.Lib.A64.Rt.ArenaW.arOf_ok (PlaceW.link i hp) hc
      ⟨h.ctr_out, h.units, h.off, h.units_lt, h.cells_lt, h.ctr_lt⟩
    hB := hB
    hdt := Spike.Lib.A64.WakeWf.hdtW
    hinit := Spike.Lib.HelloOHinit.hinit_H hp i hpa hhp hd hlo hstat hsub1 hc hnz hpin2 arch hE μE (IH (D)) ls
      (.inl ⟨rfl, rfl, hstH hp i E (fun _ => True) Ctx ls ls frM inv1 inv2 hst0⟩)
    hti0 := hti0 }

end Spike.Lib.HelloRootO

/-- info: 'Spike.Lib.HelloRootO.oPremH_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloRootO.oPremH_R
