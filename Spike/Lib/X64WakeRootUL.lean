/-
**The root's context with the child's stack unmapped** (wake.w, x86-64):
`CtxRU := CtxR ∧ U r1Of`, so the counter add's tail and the box store's
landing get the child's stack unmapped from the context itself. `hctr0` is
`Land.hctr0_R` with its tail `HLandU` (`HLand` with `U r1Of` at `c2`, kept
by the add); `hnew0` is `WakeCtr.hnew0_of`'s argument with its landing
`HLand1U` (`hnew0_R`'s `hland1` with `U r1Of` at the landing, kept by the
store). `inv0_down`/`inv0_up` move `inv0G` between `CtxR` and `CtxRU`.

- `SegInvS.keepUn`: an explicit-invariant segment carries `U r`.
- `w0_mono`: `W0` is monotone in its context.
- `un_W`: `r1Of` off `r0Of`, both below `2 ^ 64` (from `stacks_lt`).
- `takeU`: `W0W`'s outside moves keep `r1Of` unmapped.
- `CtxRU`, `HLandU`, `HLand1U`: the context and the two tails.
- `inv0_down`, `inv0_up`, `hlandU_up`: `inv0G` at `CtxRU` and at `CtxR`.
- `hctr0_U`, `hnew0_U`: `HCtrX`, `HNewX` at `CtxRU`.
- `wake_finalX_LU`: `X64WakeFinal.wake_finalX_G` at `Ctx := CtxRU`.

x86-64 twin of `Spike/Lib/A64WakeRootUL.lean` (namespace
`Spike.Lib.X64.WakePh.RootUL`). **Unlike AArch64**:
- the root's statement is `X64WakeFinal`'s (`OpenX`'s `h0`/`hctr0`/`hnew0`
  at `inv0G`), not `WakeRoot.RootOpen`: no `hst0_U` (the start's membership
  is `hinit`'s carried `hst`; `inv0_up` lifts it);
- `hnew0` takes its landing as a premise (`HLand1U`, as `Land.hnew0_R`'s
  `hland1`) instead of `Hxa.box_landing`;
- `HLandU` is at `c2` with `U` beside `TP` (`Land.HLand`'s shape; A64 at
  `n4`), generic in `inv0`;
- the ranges' bounds come from `X64WakeOSide.stacks_lt` (`un_W`), not
  `StartPlaceLy.hsub1_W`.
-/
import Spike.Lib.X64WakeFinal
import Spike.Lib.X64KeepUn

namespace Spike.Lib.X64.WakePh.RootUL

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (SegInvS TakeCKS msOfA I2)
open Spike.Lib.X64.KeepUn (U unXa out_un exec_un)
open Spike.Lib (FragS MemSide PlaceWX)
open Spike.Lib.X64.WakeOPremW (W0W)
open Spike.Lib.X64.WakeH1Inv (segInvS_weakW inv1W)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64WakeParse (certAsm)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64WakeFinal (inv0G HCtrX HNewX H0X OpenX)
open SccCertificate (outLit)

/-- **An explicit-invariant segment carries `U r`** (`SegW.keepUn`'s rows
at frames): under `ms` with `U r` at its pairs, given outside moves keeping it. -/
theorem SegInvS.keepUn {W inv : FragS isa} {K : State → State → Prop} {p : Prog} {lbl : Lbl}
    {ms : List TermRun.Frame → MemSide isa} {r : Range} (hK : ∀ fs, (ms fs).K = some abi)
    (h : SegInvS W K p lbl ms inv) (hKu : ∀ s c fs, W s c fs → ∀ s', K s s' → U r s → U r s') :
    SegInvS (fun s c fs => W s c fs ∧ U r s) K p lbl ms (fun s c fs => inv s c fs ∧ U r s) := by
  rintro s c fs ⟨hi, hu⟩
  obtain ⟨hw, ho, hk⟩ := h s c fs hi
  refine ⟨⟨hw, hu⟩, fun hn => ?_, fun s' hks => ?_⟩
  · cases ho hn with
    | pre c₁ fs₁ hr h =>
      exact .pre c₁ fs₁ hr ((out_un (hK fs₁) hu (Spike.Lib.X64ConsumerA.Out.mono_xa (ms' := unXa (ms fs₁) r) h rfl
        fun _ _ _ _ _ h _ => h)).mono fun _ _ ⟨⟨c₂, fs₂, hr₂, hi⟩, hu⟩ => ⟨c₂, fs₂, hr₂, hi, hu⟩)
    | frame s' c' fs' he hr hx =>
      obtain ⟨c₂, fs₂, hr₂, hi⟩ := hx
      exact .frame s' c' fs' he hr ⟨c₂, fs₂, hr₂, hi, exec_un hu he⟩
  · obtain ⟨c', fs', hr, hx⟩ := hk s' hks
    exact ⟨c', fs', hr, hx, hKu s c fs hw s' hks hu⟩

/-- **`W0` is monotone in its context** (`Ctx` occurs in `ArenaWr`'s second
disjunct and the counter's `WrAt → Ctx`, both positively). -/
theorem w0_mono {Λ μ own ar p Dt Ab Cl Ac L0 ls0 frM X0} {Ctx Ctx' : FragS isa} {s : State} {c fs}
    (h : Spike.Lib.X64.WakeWf.W0 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 frM X0 s c fs)
    (hC : Ctx s c fs → Ctx' s c fs) : Spike.Lib.X64.WakeWf.W0 Λ μ own ar p Dt Ab Cl Ac Ctx' L0 ls0 frM X0 s c fs :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun c' fs' hr L hw hne => (h9 c' fs' hr L hw hne).imp_right
    fun ⟨hc, hn⟩ => ⟨hC hc, hn⟩, fun hw => hC (h10 hw), h11, h12⟩

variable {pcfg : Scc.Cert.PlaceOK.Config} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 outLit) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (c0 : Ctl) (ls0 : Entry → Lsize) (frM : Entry → TermRun.Frame)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

set_option hygiene false in
/-- The child's stack range. -/
local notation "R1" => Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
/-- The root's `cT`: the dummy heap word. -/
local notation "cTR" => fun _ : Entry => Spike.Lib.X64WakeHG.cTW hp i

set_option hygiene false in
/-- The root's context at the start control `c0`. -/
local notation "CtxL" => fun E : Entry => Land.CtxR (Ly) c0 (Land.refW certAsm hp i ls0 E)

/-- **`r1Of` is off `r0Of`**, both below `2 ^ 64` (`X64WakeOSide.stacks_lt`). -/
theorem un_W : (R1).Disjoint (Spike.Lib.X64.Rt.Ti2.r0Of (Ly).lab) ∧ (R1).lo + (R1).size ≤ 2 ^ 64 ∧
    (Spike.Lib.X64.Rt.Ti2.r0Of (Ly).lab).lo + (Spike.Lib.X64.Rt.Ti2.r0Of (Ly).lab).size ≤ 2 ^ 64 := by
  have hlt := X64WakeOSide.stacks_lt hp i
  simp only at hlt
  have hbd : (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab).toNat + 32768 < 2 ^ 64 := by omega
  obtain ⟨h0l, h0s⟩ := Spike.Lib.X64.Rt.Ti2.r0Of_eq (Ly).lab
  obtain ⟨h1l, h1s⟩ := Spike.Lib.X64.Rt.Ti2.r1Of_eq hbd
  exact ⟨Spike.Lib.X64.Rt.Ti2.r01_disj hbd, by omega, by omega⟩

/-- **The root's context with the child's stack unmapped.** -/
def CtxRU (E : Entry) : FragS isa := fun s c fs => Land.CtxR (Ly) c0 (Land.refW certAsm hp i ls0 E) s c fs ∧ U R1 s

/-- **`W0W`'s outside moves keep `r1Of` unmapped**: the take of `r0Of`
(`X0W`), disjoint from it; a `clone` refusal sets registers only. -/
theorem takeU (E : Entry) (Cx : FragS isa) :
    ∀ s c fs, W0W certAsm hp i E DtW Cx (ls0 E) (frM E) s c fs → ∀ s',
      TakeCKS (X64WakeOSide.aW hp i E) (Spike.Lib.X64.WakeOD.ClW hp i) s s' → U R1 s → U R1 s' := by
  obtain ⟨hd, hw1, hw0⟩ := un_W hp i
  rintro s c fs hW s' (⟨ha, pm, rfl⟩ | ⟨-, r, -, rfl⟩) hu
  · have hX : Spike.Lib.X64.WakeWf.X0W (Ly) (X64WakeOSide.aW hp i E) s := hW.2.1
    rw [(hX.2 (congrArg (fun x : Int64 => x.toBitVec.toNat) ha)).1]
    exact Spike.Lib.X64.KeepUn.take_un pm hd hw1 hw0 hu
  · exact hu

/-- **`inv0G` at `CtxRU` is at `CtxR`** (`w0_mono`; `msBotX` reads `Ctx`
only through `W1`, which drops it). -/
theorem inv0_down (cT : Entry → Loc) (E : Entry) :
    ∀ s c fs, inv0G hp i cT ls0 (CtxRU hp i c0 ls0) frM E s c fs → inv0G hp i cT ls0 CtxL frM E s c fs :=
  fun _ _ _ ⟨inv, h, hi⟩ => ⟨inv, segInvS_weakW h fun _ _ _ h => w0_mono h (·.1), hi⟩

/-- **`inv0G` at `CtxR` with `r1Of` unmapped is at `CtxRU`** (`keepUn` on
`GfpS`, `takeU`). -/
theorem inv0_up (cT : Entry → Loc) (E : Entry) :
    ∀ s c fs, inv0G hp i cT ls0 CtxL frM E s c fs → U R1 s → inv0G hp i cT ls0 (CtxRU hp i c0 ls0) frM E s c fs :=
  fun s c fs hi hu => X64GfpS.le_gfpS (segInvS_weakW (SegInvS.keepUn (fun _ => rfl) X64GfpS.segInvS_gfpS
    (takeU hp i ls0 frM E _)) fun _ _ _ h => w0_mono h.1 fun hc => ⟨hc, h.2⟩) s c fs ⟨hi, hu⟩

/-- **The counter add's tail with `r1Of` unmapped**: `Land.HLand` but for
`U r1Of` at the `c2` state (kept from `CtxRU` by the add). -/
def HLandU (inv0 : FragS isa) (E : Entry) : Prop :=
  ∀ (ms0 : MemSide isa) R F q, ms0 = { Land.refW certAsm hp i ls0 E with xa := ms0.xa } →
    Land.GcW (Ly) c0 ms0 R F q → Spike.Lib.X64.WakeCtr.CtrOk ms0 (Ly).lab R F q →
    ∀ s c, Spike.Lib.X64.At (Ly).exe (Ly).endPc R F (Spike.Lib.X64.Alloc.N (Ly).lab ms0 q .c2) s c →
      Spike.Lib.X64.KeepTP.TP (Spike.Lib.X64.Flow.Ret0.tpOf (Spike.Lib.X64.WakePh.MainGlue.tcbS (Ly))) s →
      U R1 s → inv0 s c []

/-- **The box store's landing with `r1Of` unmapped**: `Land.hnew0_R`'s
`hland1` but for `U r1Of` at the landing (kept from `CtxRU` by the store). -/
def HLand1U (inv0 : FragS isa) (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa) (E : Entry) : Prop :=
  ∀ Lnd, Land.GsW (Ly) c0 (Land.refW certAsm hp i ls0 E) Lnd → ∀ l A s' c', L0T (Ly).Λ l = none →
    Lnd l A 1 s' c' → U R1 s' →
    (msOfA (Ly).Λ ((target (kernel 2) E).marks certAsm (Ly).Λ) (fun _ => True)
        (Spike.Lib.X64WakeOG.gW hp i (Spike.Lib.X64WakeHG.cTW hp i))
        (fun s _ => Spike.Lib.X64.WakePh.ownGXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s)
        (Spike.Lib.X64.WakeOD.arW hp i)
        (I2 (Spike.Lib.X64.WakeOD.arW hp i) (L0T (Ly).Λ) (ls0T (ls0 E)) inv0 inv1) (L0T (Ly).Λ)
        (ls0T (ls0 E)) []).xa l A 1 s' c'

/-- **`HLandU` at `inv0G`'s `CtxR` gives it at `CtxRU`** (`inv0_up`, the
`U` premise). -/
theorem hlandU_up (cT : Entry → Loc) (E : Entry) (h : HLandU hp i c0 ls0 (inv0G hp i cT ls0 CtxL frM E) E) :
    HLandU hp i c0 ls0 (inv0G hp i cT ls0 (CtxRU hp i c0 ls0) frM E) E :=
  fun ms0 R F q hms hG hok s c hj htp hu =>
    inv0_up hp i c0 ls0 frM cT E s c [] (h ms0 R F q hms hG hok s c hj htp hu) hu

/-- **`hctr0` at `CtxRU`**: `Land.hctr0_R` at `inv0 := U r1Of → inv0G`
(its tail `HLandU`), the landing's `U r1Of` kept by the add (`exec_un`). -/
theorem hctr0_U (hc : Spike.Lib.X64.Rt.CtrZ outLit) (E : Entry)
    (hland : HLandU hp i c0 ls0 (inv0G hp i cTR ls0 (CtxRU hp i c0 ls0) frM E) E) :
    HCtrX hp i cTR ls0 (CtxRU hp i c0 ls0) frM (inv0G hp i cTR ls0 (CtxRU hp i c0 ls0) frM) E := by
  intro s c fs hi hC hW c' fs' hr ha
  obtain ⟨k, op, g, x, τ, e, n, h1, h2, h3, h4, h5, h6, h7⟩ :=
    Land.hctr0_R (asm := certAsm) (hp := hp) (i := i) (c0 := c0) (ls0 := ls0)
      (inv0 := fun s c fs => U R1 s → inv0G hp i cTR ls0 (CtxRU hp i c0 ls0) frM E s c fs)
      (inv1 := inv1W certAsm hp i E (Spike.Lib.X64WakeHG.cTW hp i) DtW (CtxRU hp i c0 ls0 E) (ls0 E))
      X64WakeParse.outLit_prog hc E (fun ms0 R F q hms hG hok s c hj htp hu => hland ms0 R F q hms hG hok s c hj htp hu)
      s c fs (fun _ => hi) hC.1 hW c' fs' hr ha
  refine ⟨k, op, g, x, τ, e, n, h1, h2, h3, h4, h5, h6, fun old hG hown hle hlo => ?_⟩
  obtain ⟨hG', hP, c2, fs2, hr2, hI⟩ := h7 old hG hown hle hlo
  have hU : U R1 (g old) := exec_un hC.2 h1 old
  exact ⟨hG', hP, c2, fs2, hr2, hI.imp (fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3 hU⟩) id⟩

/-- **`hnew0` at `CtxRU`**: `WakeCtr.hnew0_of`'s argument, the landing's
`U r1Of` kept by the store (`exec_un`), its landing `HLand1U`. -/
theorem hnew0_U (E : Entry)
    (hland1 : HLand1U hp i c0 ls0 (inv0G hp i cTR ls0 (CtxRU hp i c0 ls0) frM E)
      (inv1W certAsm hp i E (Spike.Lib.X64WakeHG.cTW hp i) DtW (CtxRU hp i c0 ls0 E) (ls0 E)) E) :
    HNewX hp i cTR ls0 (CtxRU hp i c0 ls0) frM (inv0G hp i cTR ls0 (CtxRU hp i c0 ls0) frM) E := by
  haveI := (Ly).valid
  have hin : Spike.Lib.X64.Alloc.allocIn (Ly).prog = true := by
    have hpr : (Ly).prog = SccCode.wakeCells := X64WakeParse.outLit_prog
    rw [hpr]; exact Spike.Lib.X64.Flow.WakeWc.wake_alloc
  intro s c fs _ hC hW c' fs' hr _ _ _ _
  obtain ⟨rfl, Lnd, hG, kr, A, V, s', x, a, ty, e, w, wold, old, hN, hex, hmp, ht, hev, hacc, hv, hh, hold, hA,
    hcl, hX⟩ := (Spike.Lib.X64.WakeCtr.CtxT.ctxW hC.1).resolve_left fun h =>
      hW (Spike.Lib.X64.WakeCtr.ctrAt_wr (Ly).lays rfl hin rfl s c fs h)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Spike.Lib.FrameNew.FrameRun.eq_of_new hr ht.choose_spec)
  have hU : U R1 s' := exec_un hC.2 hex true
  exact ⟨kr, A, V, s', x, a, ty, e, w, wold, old, hN, hex, hmp, ht, hev, hacc, hv, hh, hold, hA, hcl,
    fun l hl => hland1 Lnd hG l _ _ _ hl (hX l hl) hU⟩

/-- **wake.w's x86-64 statement at the root's context with the child's
stack unmapped** (`cT := cTW`, `Ctx := CtxRU` at the start control `c0`,
`inv0 := inv0G`): `X64WakeFinal.wake_finalX_G` with `hctr0` by `hctr0_U`
and `hnew0` by `hnew0_U`, whose tails `hland` (`HLandU`) and `hland1`
(`HLand1U`) stay open, per entry. -/
theorem wake_finalX_LU {arch : WeakMem.Arch} {B : Budget}
    (hP : Scc.Cert.Link.X64.parsesTo certAsm outLit.prog outLit.secs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ outLit.prog outLit.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hinit2 : (Spike.Lib.X64.PhRec.m0Of (Ly).Λ outLit.prog outLit.secs).initVal
      ⟨Spike.Lib.X64WakeGOf2.lim2A (Ly), 8⟩ = 0)
    (hsub1 : (X64WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (hc : Spike.Lib.X64.Rt.CtrZ outLit)
    /- OPEN: the counter add's tail and the box store's landing, per entry -/
    (hland : ∀ E : Entry, E.Ok (Ly).Λ →
      HLandU hp i c0 ls0 (inv0G hp i cTR ls0 (CtxRU hp i c0 ls0) frM E) E)
    (hland1 : ∀ E : Entry, E.Ok (Ly).Λ →
      HLand1U hp i c0 ls0 (inv0G hp i cTR ls0 (CtxRU hp i c0 ls0) frM E)
        (inv1W certAsm hp i E (Spike.Lib.X64WakeHG.cTW hp i) DtW (CtxRU hp i c0 ls0 E) (ls0 E)) E)
    /- OPEN: the rest of `OpenX`, given `h0`, `hctr0`, `hnew0` -/
    (hO : ∀ E : Entry, E.Ok (Ly).Λ →
      H0X hp i cTR ls0 (CtxRU hp i c0 ls0) frM (inv0G hp i cTR ls0 (CtxRU hp i c0 ls0) frM) E →
      HCtrX hp i cTR ls0 (CtxRU hp i c0 ls0) frM (inv0G hp i cTR ls0 (CtxRU hp i c0 ls0) frM) E →
      HNewX hp i cTR ls0 (CtxRU hp i c0 ls0) frM (inv0G hp i cTR ls0 (CtxRU hp i c0 ls0) frM) E →
      OpenX hp i cTR ls0 (CtxRU hp i c0 ls0) frM (inv0G hp i cTR ls0 (CtxRU hp i c0 ls0) frM) arch hP E) :
    CorrectE 2 (Spike.Lib.X64WakeA64.wakeS arch) (Ly).Λ B certAsm :=
  X64WakeFinal.wake_finalX_G hp i cTR ls0 (CtxRU hp i c0 ls0) frM hP hB hlo hA13 hpin2 hinit2 hsub1 hc
    fun E hE h0 => hO E hE h0 (hctr0_U hp i c0 ls0 frM hc E (hland E hE)) (hnew0_U hp i c0 ls0 frM E (hland1 E hE))

end Spike.Lib.X64.WakePh.RootUL

/-- info: 'Spike.Lib.X64.WakePh.RootUL.SegInvS.keepUn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.RootUL.SegInvS.keepUn

/-- info: 'Spike.Lib.X64.WakePh.RootUL.inv0_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.RootUL.inv0_up

/-- info: 'Spike.Lib.X64.WakePh.RootUL.inv0_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.RootUL.inv0_down

/-- info: 'Spike.Lib.X64.WakePh.RootUL.hctr0_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.RootUL.hctr0_U

/-- info: 'Spike.Lib.X64.WakePh.RootUL.hnew0_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.RootUL.hnew0_U

/-- info: 'Spike.Lib.X64.WakePh.RootUL.wake_finalX_LU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.RootUL.wake_finalX_LU
