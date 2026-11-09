/-
**hello.w's heap abort path lifted to `ownGHXW`** (x86-64 only; the hello counterpart of
`Spike/Lib/X64WakeHabLft.lean`): on the heap abort path `Abort.Disp.HPathW` in a region whose dispatcher band
`[-32, 8]` is on the stack pool, both appended maps may be appended at every node (`CstOkH`), so `W0` at `ownGH`
there is `W0` at `ownGHXW` (`W0.liftHX`). With `HabCtlS.hpathW_hab0HS` this gives the path inside `W0` at
`ownGHXW`, the `hP0` of `HabCtlA.wc_heapAbStubKHAg` at `own := ownGHXW L a`.

- `cst_abHH`: on the heap path in a band on the pool, from a caller other than `.Lwc_main.x5`, main's word only
  (`CstH L (tM L) []`): `selfOwnH` from the pool above `.x1`, not `selfOwnWH` (past `scc_rt_stack_take`, before
  `.Lwc_main.x3`, the return address not `.x27`).
- `raAbH_ne_x27`: the heap abort's return address `.Lscc_rt_alloc.full + 12` is not `.Lwc_main.x5`'s.
- `hpathW_cstOkH`: `CstOkH` at every node of the heap abort path (`abPHH`'s `AbP`, wake's `hpathW_noW`,
  `cstOkH_of`).
- `hpathW_hab0HSX`: `HabCtlS.hpathW_hab0HS` inside `W0` at `ownGHXW`.
- `hP0X`: `hpathW_hab0HSX` in the shape of `wc_heapAbStubKHAg`'s `hP0` (`R.callee (-304 - 8) (-24) 16`).

## Differences from the AArch64 version

AArch64 has no counterpart: its level owns `ownGH` (main owns no TCB word there), so its heap abort path needs no
lift. Against x86-64 wake's `HabLft`: the code is helloCells (`abPHH`, `SccCode.hello_abort`), the classes are
`CstH` (`Spike/Lib/X64HelloOwnCstX.lean`), the worker's word is held from the abort range only under the return
address `.Lwc_main.x5` (wake `.x23`), and the region is any region with its band on the pool (`BandIn`; wake:
`wc_main`'s frame at the first stack's top), so the statement is the path fact itself rather than wake's `HabLft`.
-/
import Spike.Lib.X64HelloHabCtlS
import Spike.Lib.X64HelloOwnLft2X
import Spike.Lib.X64WakeHabLft

namespace Spike.Lib.X64.HelloPh.HabLftX

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open Scc.Sem.X64 (codeLabel pcOf abi)
open SccCode (helloCells)
open Spike.Lib (Arena FragS Region HeapAbortOblA)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64.Abort.Disp (HPathW)
open Spike.Lib.X64.WakeWf (DtW W0 RunWf)
open Spike.Lib.X64.WakePh (inPc AbP BandIn spPool_of_band raAt_iff tcbM tM)
open Spike.Lib.X64.HelloPh.StartWf (pfxM)
open Spike.Lib.X64.HelloPh (lo ownGH ownGHXW CstH CstOkH selfOwnH selfOwnWH ownSH_of_self ownSWH_of_not
  selfOwnH_iffC cstOkH_of abPHH)
open Spike.Lib.X64HelloOwnLift (tcbWH)

variable {L : RuntimeLayout} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}

/-- The heap abort's return point (`.Lscc_rt_alloc.full` plus `12`) lies below `.Lwc_main.x5` in hello's code at
`lo`. -/
def raAbChkH : Bool :=
  match codeLabel lo helloCells ".Lscc_rt_alloc.full", codeLabel lo helloCells ".Lwc_main.x5" with
  | some x, some y => decide (x + 12 < y ∧ y < 2 ^ 63)
  | _, _ => false

theorem raAbChkH_true : raAbChkH = true := by
  unfold raAbChkH; simp only [← codeT_eq]; decide +kernel

/-- **The heap abort's return address is not `.Lwc_main.x5`'s.** -/
theorem raAbH_ne_x27 (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    (L.lab Spike.Lib.X64.Alloc.fullL + 12).toBitVec ≠ (L.lab ".Lwc_main.x5").toBitVec := by
  have h := raAbChkH_true
  unfold raAbChkH at h
  split at h
  · next x y hx hy =>
    have hxy := of_decide_eq_true h
    rw [show Spike.Lib.X64.Alloc.fullL = ".Lscc_rt_alloc.full" from rfl, hlab _ _ hx, hlab _ _ hy]
    intro he
    have := congrArg BitVec.toNat he
    simp only [Int64.toBitVec_add, BitVec.toNat_add] at this
    have e1 : (Int64.ofNat x).toBitVec.toNat = x := by simp [Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega)]
    have e2 : (Int64.ofNat y).toBitVec.toNat = y := by simp [Nat.mod_eq_of_lt (show y < 2 ^ 64 by omega)]
    have e3 : BitVec.toNat (12 : Int64).toBitVec = 12 := rfl
    rw [e1, e2, e3, Nat.mod_eq_of_lt (by omega)] at this
    omega
  · cases h

/-- **Main's word only on the heap path** in a band on the pool, from a caller other than `.Lwc_main.x5`:
`selfOwnH` (on the pool, `scc_rt_abort` above `.x1`), not `selfOwnWH` (`scc_rt_abort` past `scc_rt_stack_take`,
before `.Lwc_main.x3`, the return address not `.x27`). -/
theorem cst_abHH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hb : BandIn L R) (h27 : ra ≠ (L.lab ".Lwc_main.x5").toBitVec) {s : State} (h : AbP L R ra s) :
    CstH L (tM L) [] s := by
  have eA : L.lab "scc_rt_abort" = Int64.ofNat 4202524 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have eW : L.lab "scc_rt_thr_worker" = Int64.ofNat 4203010 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have e1 : L.lab ".Lscc_rt_start.x1" = Int64.ofNat 4198500 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have eT : L.lab "scc_rt_stack_take" = Int64.ofNat 4199732 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have e25 : L.lab ".Lwc_main.x3" = Int64.ofNat 4203812 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have hin := h.1
  unfold inPc at hin
  rw [eA, eW] at hin
  have hA : (Int64.ofNat 4202524).toBitVec.toNat = 4202524 := by decide
  have hW' : (Int64.ofNat 4203010).toBitVec.toNat = 4203010 := by decide
  rw [hA, hW'] at hin
  have hsp := spPool_of_band hb h.2.2.2
  refine ⟨ownSH_of_self ((selfOwnH_iffC hlab).mpr (.inl ⟨hsp, by omega⟩)), ownSWH_of_not ?_⟩
  unfold selfOwnWH inPc
  rw [eT, e25, show (Int64.ofNat 4199732).toBitVec.toNat = 4199732 by decide,
    show (Int64.ofNat 4203812).toBitVec.toNat = 4203812 by decide]
  rintro (⟨-, -, h'⟩ | ⟨h', -⟩ | ⟨-, h'⟩)
  · omega
  · omega
  · exact h27 ((raAt_iff h _).1 h').symm

section Inst

variable (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
include hp hlo hlab

/-- **`CstOkH` at every node of the heap abort path**: `AbP` there and at the successors (`abPHH`), no write
(wake's `hpathW_noW`), main's word only at every `AbP` state (`cst_abHH`), `tcbM` off `ownGH`'s words (`hsep`,
`ha`) and `tcbWH` off `ownGHX`'s (`hW`). -/
theorem hpathW_cstOkH {a : BitVec 64} (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a)
    (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a]) (hb : BandIn L R)
    (hR : R.OK) (hlo' : R.lo ≤ -24) (hhi : 16 ≤ R.hi) (h27 : ra ≠ (L.lab ".Lwc_main.x5").toBitVec) :
    HPathW (fun s _ => CstOkH (Spike.Lib.X64.PhRec.μ L) L a s) (fun _ _ => False) L.exe L.endPc R F c0 ra := by
  have hsd := SccCode.hello_abort
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hd : Spike.Lib.X64.Abort.Disp.Code c0 L.exe L.endPc :=
    Scc.Cert.Rt.X64.Abort.code_disp L.lays rfl (by rw [hp]; exact hsd.2)
  have hst : Spike.Lib.X64.Abort.Code Spike.Lib.X64.Abort.heap c0 Spike.Lib.X64.Abort.x1Heap L.exe L.endPc :=
    Scc.Cert.Rt.X64.Abort.code_stub L.lays rfl (by rw [hp]; exact hsd.1.1.1.1.2)
  have hsite := Spike.Lib.X64.HelloPh.siteH hp hlo hlab
  obtain ⟨-, h2⟩ := Spike.Lib.X64.HelloPh.abH_labsH hlab
  have es : L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat 4200314 :=
    hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have eA : L.lab "scc_rt_abort" = Int64.ofNat 4202524 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have eW : L.lab "scc_rt_thr_worker" = Int64.ofNat 4203010 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have hP : Spike.Lib.X64.WakePh.AbPH L (Spike.Lib.X64.PhRec.μ L) L.endPc R F c0 ra :=
    abPHH hlab hR hlo' hhi (fun a' h' => by rw [hsite] at h'; cases h'; rw [es, eA, eW]; decide) hd hst
  have h := Spike.Lib.X64.Abort.Disp.HPathW.and
    (W₁ := Spike.Lib.X64.WakePh.AbW L R ra (Spike.Lib.X64.PhRec.μ L))
    ⟨hP.de, hP.dt1, hP.dj1, hP.dt2, hP.dg2, hP.se, hP.sn1, hP.sn2, hP.ssvc, hP.sn5, hP.sex⟩
    (Spike.Lib.X64.WakePh.hpathW_noW (ra := ra) (F := F) hR hlo' hhi hd hst) fun s c h₁ h₂ => And.intro h₁ h₂
  exact Spike.Lib.X64.WakePh.HPathW.map h fun s _ hw =>
    cstOkH_of hsep ha hW (cst_abHH hlab hb h27 hw.1.1) (fun s' hs' => cst_abHH hlab hb h27 (hw.1.2 s' hs'))
      (fun hns tree he => hw.2 hns tree he _)

/-- **`HabCtlS.hpathW_hab0HS` inside `W0` at `ownGHXW`**: the path at `ownGH` (`hpathW_hab0HS`) where both maps
may be appended (`hpathW_cstOkH`, `W0.liftHX`), the region's band on the pool (`hb`). -/
theorem hpathW_hab0HSX {ar : Arena} {p : Prog} {Cl : State → Prop} {Ctx : FragS isa} {L0 : Lbl} {ls0 : Lsize}
    {frM : TermRun.Frame} {X0 : State → Prop} {fs : List TermRun.Frame} (a : BitVec 64)
    (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hb : BandIn L R)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hR : R.OK) (hlo' : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hra : ra = (L.lab Spike.Lib.X64.Alloc.fullL + 12).toBitVec) (hfs : fs = [] ∨ fs = [frM])
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hc0 : (fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) (hF : Spike.Lib.X64.FStable R F)
    (hpl : ∀ s : State, F s.st.1 → PlacedSE L.Λ L0 s c0 fs)
    (hobl : HeapAbortOblA ar.cells ar.ctr c0) (hX0 : ∀ s, inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0 s) :
    HPathW (fun s c => W0 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L a) ar p DtW (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab pfxM) Ctx L0 ls0 frM X0 s c fs) (fun _ _ => False) L.exe L.endPc
      R F c0 ra :=
  Spike.Lib.X64.Abort.Disp.HPathW.and
    (Spike.Lib.X64.HelloPh.HabCtlS.hpathW_hab0HS hp hlo hlab a hΛ hR hlo' hhi hra hfs hcl hc0 hF hpl hobl hX0)
    (hpathW_cstOkH hp hlo hlab hsep ha hW hb hR hlo' hhi (by rw [hra]; exact raAbH_ne_x27 hlab))
    fun _ _ h hc => h.liftHX hc

/-- **`wc_heapAbStubKHAg`'s `hP0` at `ownGHXW`**: `hpathW_hab0HSX` in the region `R.callee (-304 - 8) (-24) 16`
below a caller's region `R` (`hR`, `hlo'`, `hhi` as `wc_heapAbStubKHAg`'s), the callee's band on the pool
(`hb`). -/
theorem hP0X {ar : Arena} {p : Prog} {Cl : State → Prop} {Ctx : FragS isa} {L0 : Lbl} {ls0 : Lsize}
    {frM : TermRun.Frame} {X0 : State → Prop} {fs : List TermRun.Frame} (a : BitVec 64)
    (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hb : BandIn L (R.callee (-304 - 8) (-24) 16))
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hR : R.OK) (hlo' : R.lo ≤ -336) (hhi : -296 ≤ R.hi)
    (hfs : fs = [] ∨ fs = [frM])
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hX0 : ∀ s, inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0 s) :
    ∀ (F' : MachineData → Prop) (c0 : Ctl), Spike.Lib.X64.FStable (R.callee (-304 - 8) (-24) 16) F' →
      ((fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) → (∀ s : State, F' s.st.1 → PlacedSE L.Λ L0 s c0 fs) →
      HeapAbortOblA ar.cells ar.ctr c0 →
      HPathW (fun s c => W0 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L a) ar p DtW (Spike.Lib.X64.WriteAb.Ab L.lab)
        Cl (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab pfxM) Ctx L0 ls0 frM X0 s c fs) (fun _ _ => False) L.exe
        L.endPc (R.callee (-304 - 8) (-24) 16) F' c0 (L.lab ".Lscc_rt_alloc.full" + 12).toBitVec :=
  fun _ _ hF hc0 hpl hobl =>
    hpathW_hab0HSX hp hlo hlab a hsep ha hW hb hΛ
      (Region.callee_ok hR (by omega) (by decide) (by omega) (by omega))
      (by simp [Region.callee]) (by simp [Region.callee]) rfl hfs hcl hc0 hF hpl hobl hX0

end Inst

end Spike.Lib.X64.HelloPh.HabLftX

/-- info: 'Spike.Lib.X64.HelloPh.HabLftX.raAbChkH_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HabLftX.raAbChkH_true

/-- info: 'Spike.Lib.X64.HelloPh.HabLftX.raAbH_ne_x27' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HabLftX.raAbH_ne_x27

/-- info: 'Spike.Lib.X64.HelloPh.HabLftX.cst_abHH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HabLftX.cst_abHH

/-- info: 'Spike.Lib.X64.HelloPh.HabLftX.hpathW_cstOkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HabLftX.hpathW_cstOkH

/-- info: 'Spike.Lib.X64.HelloPh.HabLftX.hpathW_hab0HSX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HabLftX.hpathW_hab0HSX

/-- info: 'Spike.Lib.X64.HelloPh.HabLftX.hP0X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HabLftX.hP0X
