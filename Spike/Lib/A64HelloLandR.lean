/-
**`OpenW.hctr0`/`hnew0` at hello's root context** (AArch64; the twin of
`Spike/Lib/A64WakeLand.lean`'s `hctr0_R`/`hnew0_R` at `A64HelloLand`'s `CtxRH`): the counter row and the box
store's premises at every state of the root's context, and from them the root's per-state facts at the level
before the allocation (`HelloRootO.oPremH_R`'s `hW0`, `WakeWf.hW0`).

`CtxRH`'s three disjuncts are `wc_rodata`'s counter add (`GcRdH`, under main's frame), `wc_main`'s (`GcMH`, at no
frames), both under main's thread pointer, and the box's store (`StAt … GsH`). The counter adds' rows are
`CtrF.ctrRow_ofFT`, the store's premises `CtrF.newStM_ofSt`; the store writes no counter
(`WakeCtr.stAt_noWr`, the counter word below the heap, `HrdArena.hlt_U`), the adds do (`CtrF.ctrAtF_wr`).

What is carried is where the start continues after each write: the allocator's next node `n4` after either
counter add (`HLandRd`, `HLandM`), and the store's landings (`HLand1`), as wake's `HLand` and `hland1_R`'s.

- `hcode_H`: the allocator's code in hello's layout.
- `HLandRd`, `HLandM`, `HLand1`: the carried landings.
- `hctr0_RH`, `hnew0_RH`: `WakeWf.hW0`'s `hctr`/`hnew` at `CtxRH`, at any fragment `J`.
- `hW0_RH`: `oPremH_R`'s `hW0` at `helloDR` with `Ctx := CtxRH`, `frM := frH c0S.env`, both levels at `ls`.
-/
import Spike.Lib.A64HelloCtrF
import Spike.Lib.HelloRootO

namespace Spike.Lib.A64.HelloPh.LandR

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (textProgram abi)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (CtrRow PendA WrAt ArenaW I3 SFactsACH)
open Spike.Lib.A64ConsumerS (InvS)
open Spike.Lib (FragS Frag MemSide FrameRun)
open Spike.Lib.A64.Flow (At)
open Spike.Lib.A64.Flow.Ret0 (pinA)
open Spike.Lib.A64.Alloc (Call N)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.HelloPh.Land (CtrOkS refH GcRdH GcMH GsH CtxRH)
open Spike.Lib.A64.HelloPh.RootH0 (msH)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloRootO (helloDR)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (ls : Lsize)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0` (as `StartH0U`). -/
local notation "TI" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw TI

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw TI

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- The allocator's labels. -/
local notation "LBL" => (_root_.Executable.labels (Ly).exe).label

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)

/-- **The allocator's code** in hello's layout (wake's `hcode_R`). -/
theorem hcode_H (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg) :
    ∀ ms0 q, Spike.Lib.A64.Alloc.Code ms0 q (Ly).exe (Ly).endPc := by
  have hprog : (Ly).prog = SccCode.helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have hL : Scc.Cert.Rt.A64.Lays (Ly).exe SccCode.helloProg (Ly).pfx := hprog ▸ (Ly).lays
  have hend : (Ly).endPc = Scc.Cert.Rt.A64.endOf (Ly).exe SccCode.helloProg (Ly).pfx := by rw [← hprog]
  exact fun _ _ => Spike.Lib.A64.Flow.alloc_code_of hL hend Spike.Lib.A64.Flow.HelloRd.hello_alloc

/-! ## The carried landings -/

/-- **`wc_rodata`'s counter add's tail** (`CtrF.ctrRow_ofFT`'s `hland` at `GcRdH`): from the allocator's next node
`n4` after a counter add of `wc_rodata`'s buffer call, under main's thread pointer, `Q` at the add's frames. -/
def HLandRd (Q : FragS isaLSE2) : Prop :=
  ∀ fs (ms0 : MemSide isaLSE2) R F q, ms0 = { refH (asm := asm) hpw i0 E rd ls fs with xa := ms0.xa } →
    GcRdH hpw i0 fs ms0 R F q → CtrOkS ms0 LBL R F q →
    ∀ s c, At (Ly).exe (Ly).endPc R F (N LBL ms0 q .n4) s c → TP (TV) s → Q s c fs

/-- **`wc_main`'s counter add's tail** (`CtrF.ctrRow_ofFT`'s `hland` at `GcMH`): from `n4` after a counter add of
`wc_main`'s box call, under main's thread pointer, `Q` at the add's frames. -/
def HLandM (Q : FragS isaLSE2) : Prop :=
  ∀ fs (ms0 : MemSide isaLSE2) R F q, ms0 = { refH (asm := asm) hpw i0 E rd ls fs with xa := ms0.xa } →
    GcMH hpw i0 fs ms0 R F q → CtrOkS ms0 LBL R F q →
    ∀ s c, At (Ly).exe (Ly).endPc R F (N LBL ms0 q .n4) s c → TP (TV) s → Q s c fs

/-- **The box store's landings** (`CtrF.newStM_ofSt`'s `hland1` at `GsH`): every landing `GsH` admits is in the
allocation fragment `X`, for labels fresh at the start. -/
def HLand1 (X : WeakMem.AllocLabel → Nat → Nat → Frag isaLSE2) : Prop :=
  ∀ Lnd, GsH (asm := asm) hpw i0 E rd ls Lnd → ∀ l A s' c', LB l = none → Lnd l A 1 s' c' → X l A 1 s' c'

/-! ## The counter row and the store's premises at `CtxRH` -/

variable {J : InvS} {P : FragS isaLSE2}

/-- **`WakeWf.hW0`'s `hctr` at `CtxRH`** (wake's `hctr0_R`), at the root's memory sides `msH … J` at any fragment
`J`: the counter adds by `ctrRow_ofFT` (their tails `hR`, `hM` in `J` at the start's levels), the
store writing no counter (`stAt_noWr`). -/
theorem hctr0_RH (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hR : HLandRd (asm := asm) hpw i0 E rd ls (J LB (ls0T ls))) (hM : HLandM (asm := asm) hpw i0 E rd ls (J LB (ls0T
        ls))) :
    ∀ s c fs, P s c fs → CtxRH (asm := asm) hpw i0 E rd ls s c fs → WrAt s (AR).ctrLoc → ∀ c' fs',
      FrameRun helloSrc (c, fs) (c', fs') → abi.atSys s = false →
      CtrRow (msH (asm := asm) hpw TI E rd ls J fs') (fun s' c'' => PendA helloSrc J LB (ls0T ls) s' c'' fs') s c' := by
  intro s c fs _ hC hW c' fs' hr _
  rcases hC with ⟨h, htp⟩ | ⟨h, htp⟩ | h
  · exact Spike.Lib.A64.HelloPh.CtrF.ctrRow_ofFT (hcode_H hpw i0 hpa hhp) (fun _ => rfl) hR h htp hr
  · exact Spike.Lib.A64.HelloPh.CtrF.ctrRow_ofFT (hcode_H hpw i0 hpa hhp) (fun _ => rfl) hM h htp hr
  · exact (Spike.Lib.A64.WakeCtr.stAt_noWr (Spike.Lib.A64.HelloPh.HrdArena.hlt_U hpw i0 hc)
      (Spike.Lib.A64.HelloPh.HrdArena.h64_U hpw i0 hc) s c fs h hW).elim

/-- **`WakeWf.hW0`'s `hnew` at `CtxRH`** (wake's `hnew0_R`), at `msH … J`: the counter adds write the counter
(`ctrAtF_wr`), the store's premises by `newStM_ofSt` (its landings `h1` in `msH … J []`'s fragment). -/
theorem hnew0_RH (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg)
    (h1 : HLand1 (asm := asm) hpw i0 E rd ls (msH (asm := asm) hpw TI E rd ls J []).xa) :
    ∀ s c fs, P s c fs → CtxRH (asm := asm) hpw i0 E rd ls s c fs → ¬ WrAt s (AR).ctrLoc → ∀ c' fs',
      FrameRun helloSrc (c, fs) (c', fs') → abi.atSys s = false → ∀ L, WrAt s L → ¬ ArenaW (AR) LB (ls0T ls) c' L →
        NewStM helloSrc LB (msH (asm := asm) hpw TI E rd ls J fs') s c' := by
  intro s c fs _ hC hW c' fs' hr _ _ _ _
  rcases hC with ⟨h, -⟩ | ⟨h, -⟩ | h
  · exact (hW (Spike.Lib.A64.HelloPh.CtrF.ctrAtF_wr (hcode_H hpw i0 hpa hhp) (fun _ => rfl) s c fs h)).elim
  · exact (hW (Spike.Lib.A64.HelloPh.CtrF.ctrAtF_wr (hcode_H hpw i0 hpa hhp) (fun _ => rfl) s c fs h)).elim
  · exact Spike.Lib.A64.HelloPh.CtrF.newStM_ofSt rfl h1 h hr

/-! ## The root's per-state facts -/

variable {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
  {W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}

set_option hygiene false in
/-- The root's instance data at `Ctx := CtxRH`, `frM := frH c0S.env`, both levels at `ls`. -/
local notation "D" => helloDR (asm := asm) hpw TI E (CtxRH (asm := asm) hpw i0 E (fun _ => True) ls) ls
  (Spike.Lib.HelloRdCf.frH Spike.Lib.A64.HelloPh.C0S.c0S.env) W1 inv1 W2 inv2

set_option hygiene false in
local notation "μE" => (Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ

/-- **`oPremH_R`'s `hW0` at `Ctx := CtxRH`** (`WakeWf.hW0` with `hctr0_RH`/`hnew0_RH` at `J := IH D`, `P :=
(D).inv0`): given the counter adds' tails in `(D).inv0` (`hR`, `hM`) and the store's landings in the start's
allocation fragment (`h1`). -/
theorem hW0_RH (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hR : HLandRd (asm := asm) hpw i0 E (fun _ => True) ls (D).inv0) (hM : HLandM (asm := asm) hpw i0 E (fun _ => True)
        ls (D).inv0)
    (h1 : HLand1 (asm := asm) hpw i0 E (fun _ => True) ls (msH (asm := asm) hpw TI E (fun _ => True) ls
        (Spike.Lib.HelloO.IH (D)) []).xa) :
    ∀ s c fs, (D).inv0 s c fs → (D).W0 s c fs →
      SFactsACH (Ly).Λ (μE) helloSrc (D).rd (D).G (D).own (D).ar (Spike.Lib.HelloO.IH (D)) (D).L0 (D).ls0 s c fs
        (D).Dt (Spike.Lib.A64.WriteAb.Ab (Ly).lab) (D).Cl
        (Spike.Lib.A64.HelloWf.AcH (Ly).lab Spike.Lib.A64.Flow.Worker.Hello.Child.pfxM) :=
  Spike.Lib.A64.WakeWf.hW0
    (hctr0_RH hpw i0 E (fun _ => True) ls hpa hhp hc
      (fun fs ms0 R F q hms hG hok s c hA htp => .inl ⟨rfl, rfl, hR fs ms0 R F q hms hG hok s c hA htp⟩)
      (fun fs ms0 R F q hms hG hok s c hA htp => .inl ⟨rfl, rfl, hM fs ms0 R F q hms hG hok s c hA htp⟩))
    (hnew0_RH hpw i0 E (fun _ => True) ls hpa hhp h1)

end Spike.Lib.A64.HelloPh.LandR

/-- info: 'Spike.Lib.A64.HelloPh.LandR.hcode_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.LandR.hcode_H

/-- info: 'Spike.Lib.A64.HelloPh.LandR.hctr0_RH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.LandR.hctr0_RH

/-- info: 'Spike.Lib.A64.HelloPh.LandR.hnew0_RH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.LandR.hnew0_RH

/-- info: 'Spike.Lib.A64.HelloPh.LandR.hW0_RH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.LandR.hW0_RH
