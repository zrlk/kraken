/-
**`wc_rodata`'s heap abort at hello's root closes** (x86-64; the twin of the third part of
`Spike/Lib/A64HelloRdHAb.lean`): from `wc_rodata`'s `rX .abort` at the frames `[FR]`, a segment inside the
start's level `StartWcS.WS` under the take move, with no exit (`StartH0R`/`StartH0U`'s `hCrd`).

- `hello_rd_hab_closed`: the exit's states, under `scc_rt_main`'s frame condition at any new stack's base `v`,
  start a segment with no exit: `Abort.Disp.seg_jabort2RW_up` (the node at `-208` left to `scc_rt_main`'s region
  at `-80 - 208`) then the heap abort path (`HAbStub.heapAbStubK_at` at `k = -288`), the controls' facts from
  `HabCtlRd.HabCtlRdH`.

No absolute address appears in a statement here.

## Differences from the AArch64 version

- `scc_rt_main`'s region at the new stack's base `v` is `MainGlue.RS helloLsw v` (AArch64 `swR v (-helloLsw) 0`)
  and `wc_rodata`'s is `Hello1.mR` of it; its frame condition `FS` and `FStable` come from `Land.fstable_FS`
  (AArch64: `wordsNoneP_swFSL_fstable` and `rt_h16` in place).
- `seg_jabort2RW_up` takes the callee's region's top `hi' = 8` and the return address's slot (`hoff`, `hra`;
  AArch64 `hi' = 0` and `x30`); the dispatcher's region is `R.callee (-296) (-24) 16`, with no base alignment.
- `HelloRd.rX` and `HabCtlRdH` take `wc_rodata`'s region (unused at `.abort`); `HabCtlRdH` is asked at
  `mR (RS helloLsw (topS Ly 0))`.
- The loader's facts are the two parses `cellsOf asm = some o.prog`, `some helloCells` (AArch64 `textProgram`).
-/
import Spike.Lib.X64HelloRdHAb
import Spike.Lib.X64HelloHAbW
import Spike.Lib.X64HelloHabCtlRd
import Spike.Lib.X64HelloStartWcS
import Spike.Lib.X64HelloLand
import Spike.Lib.X64HelloRodata
import Spike.Lib.X64HelloC0S
import Spike.Lib.X64WakeAbOffW
import Spike.Lib.X64HelloClH

namespace Spike.Lib.X64.HelloPh.RdHAb

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open Scc.Sem.X64 (codeLabel pcOf abi cellsOf)
open SccCode (helloCells)
open Spike.Lib (Arena FragS Frag Region SegWS PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Flow.Hello1 (mR mF)
open Spike.Lib.X64.Flow.HelloRd (rX)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib.X64.WakePh.MainGlue (FS RS topS)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64.HelloPh.StartWcS (WS)
open Spike.Lib.X64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.X64.HelloPh.HabCtlRd (HabCtlRdH)
open Spike.Lib.X64.HelloPh.HAbStub (heapAbStubK_at x0WH_abort)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64HelloSrc (helloSrc)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
/-- The memory side at the start's labels, the entry's marks. -/
local notation "MSf" => fun fs => Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
  ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd G own
  (Spike.Lib.X64.WakeOD.arW hpw i) I (L0T (Ly).Λ) ls fs

set_option hygiene false in
/-- `rodata`'s frame at the start control. -/
local notation "FR" => Spike.Lib.X64HelloRdCf.frH Spike.Lib.X64.HelloPh.C0S.c0S.env

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => topS (Ly) 0#64

set_option maxHeartbeats 800000 in
/-- **The start's `wc_rodata` heap-abort exit closes** (`StartH0R`/`StartH0U`'s `hCrd`): from `rX .abort` in
`wc_rodata`'s region at the frames `[FR]` (any `v`, `m0`, `σC`), a segment inside `W0` at `ownGH`, `arW`, `ClH`,
`DtW`, `X0WH … (lab take_site)`, `frM := FR` under the take move, with no exit. -/
theorem hello_rd_hab_closed {asm : Scc.Sem.X64.Asm} {E : Scc.Sem.Entry} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : Spike.Lib.X64ConsumerS.OwnS} {I : Spike.Lib.X64ConsumerS.InvS} {ls : Lsize}
    {Ctx : FragS isa} {ls0 : Lsize} {J1 : FAS → FAS → Ctl → Prop}
    (hpa : cellsOf asm = some o.prog) (hhp : cellsOf asm = some helloCells) (hlo0 : Λ0.code.lo = lo)
    /- the controls' facts at `rX .abort` -/
    (hhabctlRd : ∀ σC, HabCtlRdH ((MSf) [FR]) (Ly).lab helloSrc (Ly).Λ (L0T (Ly).Λ) (mR (RS helloLsw (TOP)))
      (Spike.Lib.X64.WakeOD.arW hpw i) [FR] (J1 σC)) :
    SegWS (WS (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) (Spike.Lib.X64.WakeOD.arW hpw i) helloSrc DtW
        (Spike.Lib.X64.HelloPh.ClH (Ly)) Ctx (L0T (Ly).Λ) (ls0T ls0) FR
        (X0WH (Ly) ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL)))
      (Spike.Lib.X64.PhRec.K (Ly) (RS0)) helloSrc (L0T (Ly).Λ) (MSf)
      (Frag.at (fun s c => ∃ v m0 σC,
        At (Ly).exe (Ly).endPc (mR (RS helloLsw v)) (mF (RS helloLsw v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC)
          (rX ((MSf) [FR]) (Ly).lab (L0T (Ly).Λ) (mR (RS helloLsw v)) (J1 σC) .abort) s c) [FR])
      (fun _ _ _ => False) := by
  have hp : o.prog = helloCells := Option.some.inj (hpa.symm.trans hhp)
  have hprog : (Ly).prog = helloCells := hp
  have hlo : (Ly).Λ.code.lo = lo := hlo0
  have hlab : ∀ l x, codeLabel lo helloCells l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceWX.hlab_ofPlaceWX hpw i l x (by rw [hlo, hp]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceWX.abortLbl_of_placeWX (Spike.Lib.PlaceWX.link i hpw)
  have hab : ∀ s : State, s.st.2 = (Ly).lab Spike.Lib.X64.Abort.heap.exit → ((MSf) [FR]).abortAt s :=
    fun s hs => by
      obtain ⟨-, e9⟩ := Spike.Lib.X64.HelloPh.abH_labsH hlab (L := Ly)
      refine ⟨.heap, 4202760, ?_, by unfold pcOf; rw [hs]; erw [e9]; rfl⟩
      rw [Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpa]
      show codeLabel (Ly).Λ.code.lo (Ly).prog ((Ly).Λ.abortLbl .heap) = _
      rw [hprog, hlo, hΛ, ← codeT_eq]; decide +kernel
  refine (SegWS.exists_pre (P := fun g : BitVec 64 × MachineData × FAS =>
      Frag.at (At (Ly).exe (Ly).endPc (mR (RS helloLsw g.1))
        (mF (RS helloLsw g.1) (FS (Ly) (RS0) helloLsw 0#64 g.1) g.2.1 g.2.2)
        (rX ((MSf) [FR]) (Ly).lab (L0T (Ly).Λ) (mR (RS helloLsw g.1)) (J1 g.2.2) .abort)) [FR])
      fun ⟨v, m0, σC⟩ => ?_).mono_pre
    fun _ _ _ ⟨⟨v, m0, σC, h⟩, hf⟩ => ⟨⟨v, m0, σC⟩, h, hf⟩
  by_cases hv : v = TOP
  case neg =>
    refine SegWS.empty fun _ _ _ h => ?_
    obtain ⟨⟨-, -, -, -, _, -, hF, -⟩, -⟩ := h
    exact hv hF.1.1.2.1.1
  subst hv
  obtain ⟨-, hR, hF⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i
  refine (SegWS.liftS (Q₀ := fun _ _ => False) [FR] (Spike.Lib.X64.Abort.Disp.seg_jabort2RW_up
      (Q := fun _ _ => False) (kc := -80) (lo' := -208) (hi' := 8) (e := -208) (k := -288)
      (nX := rX ((MSf) [FR]) (Ly).lab (L0T (Ly).Λ) (mR (RS helloLsw (TOP))) (J1 σC) .abort)
      (F' := mF (RS helloLsw (TOP)) (FS (Ly) (RS0) helloLsw 0#64 (TOP)) m0 σC)
      rfl (by decide) rfl (fun σ c h => h.1) (by simp [Spike.Lib.Region.callee, Spike.Lib.Region.Off])
      (fun σ c h => h.2.1) (fun m hm => ⟨hm.1, m0, σC, _, hm.2.1, hm.2.2⟩) hF hR
      (by show (8 - helloLsw : Int) ≤ -288 - 32; decide)
      (by show (-288 : Int) + 8 ≤ 8; decide) (by decide) rfl
      (heapAbStubK_at (C := fun c0 => ∃ σx,
          (rX ((MSf) [FR]) (Ly).lab (L0T (Ly).Λ) (mR (RS helloLsw (TOP))) (J1 σC) .abort).J σx c0)
        hprog hlo hlab _ hΛ hF hR
        (by show (8 - helloLsw : Int) ≤ -288 - 32; decide)
        (by show (-288 : Int) + 8 ≤ 8; decide) (by decide) rfl
        (.inr rfl) (fun _ h => h.2) (fun c0 hx => hx.elim fun σx hJ => hhabctlRd σC σx c0 hJ) hab
        (x0WH_abort hlab rfl))) (fun _ _ h => h)).mono_post fun _ _ _ h => h.1.elim

end Spike.Lib.X64.HelloPh.RdHAb

/-- info: 'Spike.Lib.X64.HelloPh.RdHAb.hello_rd_hab_closed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdHAb.hello_rd_hab_closed
