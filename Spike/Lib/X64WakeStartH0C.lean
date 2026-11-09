/-
**The start's heap-abort exit closes** (x86-64; the twin of
`Spike/Lib/A64WakeStartH0C.lean`): from `StartH0X.wake_start_wc_h0X`'s
exit (`wc_main`'s `wX .abort` at the switched region, any `v`, `m0`, `σC`),
the heap abort runs inside wake's level before the allocation (`WakeWf.W0`
at `ownGXW`, `arW`, `ClW`, `X0W … ax`) under the take move `PhRec.K`, and
never exits (`False`): `wc_heapAbStubKX` in the region of `wc_main` after
the switch (only `v` at the first stack's top occurs, `WcWfR.v_top`),
`WakeWc.wc_heapAb_segWS`.

- `HabLft`: `SegWS`'s state facts at `ownG` lift to `ownGXW` along the heap
  abort path below `wc_main`'s frame at the first stack's top (`Lft2` at
  every node of `HPathW`).
- `wc_heapAbStubKX`: `HAbStubK.wc_heapAbStubK` at `ownGXW`, given the path's
  `Lft2` (`hlft`).
- `wake_hab_closed`: the exit's pairs at the frames `[]` start a segment
  with no exit, at the memory side `msOfA` of the entry's marks (any `rd`,
  `G`, `own`, `I`, `ls`).

**Where x86-64 differs from AArch64**:
- the level owns `ownGXW` (main's and the worker's TCB words appended to
  `ownG`; A64's `ownG`), while `HAbStubK.wc_heapAbStubK` is proved at
  `ownG`: the lift along the heap abort path is the carried premise
  `HabLft` (no producer yet; the lift layer's `CstOk` classes exclude the
  abort range);
- `wc_main`'s region is `wR (RS wcLsw v) wcD` (A64 `wR (swR v (-384) 0)
  336`), its facts at the top by `WcWfR.top_ok` (A64 inline `wR_ok`), with
  `R.lo = -328 ≤ -272`, `-232 ≤ 8 = R.hi` and no alignment premise;
- the start control `c0` inside `JW` is generic, with its box shape
  (`hbx`), facts (`hc0`) and placement (`hpl0`) premises (A64 at `c0W`;
  `HAbStubK.hctl_c0` is generic), and the take address `ax` with `hax`
  (A64 `aW E` via `aW_site`);
- the loader's facts are `hpa : cellsOf asm = some o.prog`, `hpo`, `hlo`
  (A64 `textProgram` parses);
- the pinned word is `TP (tpOf (tcbS (Ly)))` (A64 `pinA + 8`).
-/
import Spike.Lib.X64WakeHAbStubK
import Spike.Lib.X64WakeOwnLft2
import Spike.Lib.X64WakeWcTop
import Spike.Lib.X64WakeWcWfR
import Spike.Lib.X64WakeAbOffW
import Spike.Lib.X64WakeOD

namespace Spike.Lib.X64.WakePh.StartH0C

open Spike.Lib.X64.WakePh.HAbStubK (hpathW_K abort_off x0W_abort hctl_c0)
open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open Scc.Sem.X64 (codeLabel pcOf abi cellsOf)
open SccCode (wakeCells)
open Spike.Lib (Arena FragS Frag Region SegWS HeapAbortOblA PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.X64.Flow.WakeWc (WcHAbStub wX raAb)
open Spike.Lib.X64.Abort.Disp (HPathW)
open Spike.Lib.X64.WakeWf (DtW W0 RunWf X0W)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS topS)
open Spike.Lib.X64.WakePh.StartFacts (wcD wcLsw)
open Spike.Lib.X64.WakePh.StartWf (pfxM)
open Spike.Lib.X64.WakePh.StartH0 (C0Box)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.Rt.Reserve (ntA)

/-- **The heap abort path's state facts lift to `ownGXW`** below
`wc_main`'s frame at the first stack's top: `Lft2` (`SFactsSt2` at `ownG`
gives it at `ownGXW`) at every node of `HPathW` in the dispatcher's region
`R.callee (-240 - 8) (-24) 16`, for every frame condition and source
control, with the return address `raAb`. -/
def HabLft (L : RuntimeLayout) : Prop :=
  ∀ (F : MachineData → Prop) (c0 : Ctl),
    HPathW (Spike.Lib.X64.WakePh.Lft2 L.Λ L (ntA L.lab) DtW) (fun _ _ => False) L.exe L.endPc
      ((wR (RS wcLsw (topS L 0#64)) wcD).callee (-240 - 8) (-24) 16) F c0 (raAb L.lab)

section Gen

variable {L : RuntimeLayout} (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)

include hp hlo hlab in
/-- **`WcHAbStub` under the take move at `ownGXW`** (`HAbStubK.wc_heapAbStubK`
with the level's owned words `ownGXW`): the path inside `W0` at `ownG`
(`hpathW_hab0`), its state facts moved to `ownGXW` by the path's `Lft2`
(`hlft`), in `scc_rt_abort`'s code (`hpathW_hX`), off the take site. -/
theorem wc_heapAbStubKX {R : Region} {F : MachineData → Prop} {ar : Arena} {p : Prog} {Cl : State → Prop}
    {Ctx : FragS isa} {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame} {X0 : State → Prop}
    {fs : List TermRun.Frame} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
    {J0 : Spike.Lib.X64.AS → Ctl → Prop} {rS : Scc.Sem.Range} (a : BitVec 64)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hF : Spike.Lib.X64.FStable R F) (hR : R.OK) (hlo' : R.lo ≤ -272) (hhi : -232 ≤ R.hi)
    (hK : (ms fs).K = some abi) (hfs : fs = [] ∨ fs = [frM])
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hctl : ∀ σC c0, (wX (ms fs) L.lab R J0 .abort).J σC c0 →
      ((fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) ∧ (∀ s, PlacedSE L.Λ L0 s c0 fs) ∧
        HeapAbortOblA ar.cells ar.ctr c0)
    (hab : ∀ s : State, s.st.2 = L.lab "scc_rt_abort_heap_exit" → (ms fs).abortAt s)
    (hX0 : ∀ s, inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0 s)
    (hlft : ∀ (F' : MachineData → Prop) (c0 : Ctl),
      HPathW (Spike.Lib.X64.WakePh.Lft2 L.Λ L a DtW) (fun _ _ => False) L.exe L.endPc
        (R.callee (-240 - 8) (-24) 16) F' c0 (raAb L.lab)) :
    WcHAbStub (W0 L.Λ (Spike.Lib.X64.PhRec.μ L) (Spike.Lib.X64.WakePh.ownGXW L a) ar p DtW
      (Spike.Lib.X64.WriteAb.Ab L.lab) Cl (Spike.Lib.X64.ThreadsAb.Ac L.lab pfxM) Ctx L0 ls0 frM X0)
      (Spike.Lib.X64.PhRec.K L rS) p lbl ms L.exe L.endPc R F fs J0 := by
  intro m0 σC c0 hJ
  obtain ⟨hc0, hpl, hobl⟩ := hctl σC c0 hJ
  have hsite := siteW hp hlo hlab
  have hR' : (R.callee (-240 - 8) (-24) 16).OK :=
    Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)
  have h0 := hpathW_hab0 (ar := ar) (p := p) (Cl := Cl) (Ctx := Ctx) (L0 := L0) (ls0 := ls0) (frM := frM)
    (X0 := X0) (F := fun m => F m ∧ Spike.Lib.X64.CKept R (-240 - 8) (-24) 16 m0 m ∧
      Spike.Lib.X64.Abs R ⟨-240, []⟩ m0 σC) hp hlo hsite hlab a hΛ hR'
    (by simp [Region.callee]) (by simp [Region.callee]) rfl hfs hcl hc0 hpl hobl hX0
  have hX := hpathW_hX (F := fun m => F m ∧ Spike.Lib.X64.CKept R (-240 - 8) (-24) 16 m0 m ∧
      Spike.Lib.X64.Abs R ⟨-240, []⟩ m0 σC) (c0 := c0)
    (ra := Spike.Lib.X64.Flow.WakeWc.raAb L.lab) hp hlo hsite hlab hR' (by simp [Region.callee])
    (by simp [Region.callee])
  have hL := hlft (fun m => F m ∧ Spike.Lib.X64.CKept R (-240 - 8) (-24) 16 m0 m ∧
      Spike.Lib.X64.Abs R ⟨-240, []⟩ m0 σC) c0
  have h0L := Abort.Disp.HPathW.and h0 hL fun _ _ h₁ h₂ => And.intro h₁ h₂
  have hpath := Spike.Lib.X64.WakePh.HPathW.map (hpathW_K (K := Spike.Lib.X64.PhRec.K L rS)
    (Abort.Disp.HPathW.and h0L hX fun _ _ h₁ h₂ => And.intro h₁ h₂)
    fun s _ h s' hk => (abort_off hlab s h.2).2 (congrArg (fun x : Int64 => x.toBitVec.toNat) hk.1))
    (W₂ := fun s c => W0 L.Λ (Spike.Lib.X64.PhRec.μ L) (Spike.Lib.X64.WakePh.ownGXW L a) ar p DtW
      (Spike.Lib.X64.WriteAb.Ab L.lab) Cl (Spike.Lib.X64.ThreadsAb.Ac L.lab pfxM) Ctx L0 ls0 frM X0 s c fs)
    fun _ _ h =>
      let ⟨⟨⟨h1, h2, h3, h4⟩, hl⟩, _⟩ := h
      ⟨h1, h2, hl h3, h4⟩
  exact Spike.Lib.X64.StubW.stubHRW_of_code L.lays rfl (by rw [hp]; exact SccCode.wake_abort) hK
    (Spike.Lib.X64.fstable_enter hR hF (by omega) (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide)) hpath fun s _ ⟨_, _, _, hpc, _⟩ => hab s hpc

end Gen

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

set_option hygiene false in
/-- The memory side at the start's labels, the entry's marks. -/
local notation "MSf" => fun fs => Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
  ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd G own
  (Spike.Lib.X64.WakeOD.arW hpw i) I L0 ls fs

set_option hygiene false in
local notation "JW" => fun σC => wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0)).J σC

/-- **The start's heap-abort exit closes**: from `wake_start_wc_h0X`'s exit
at the frames `[]`, a segment inside `W0` at `ownGXW`, `arW`, `ClW`,
`X0W … ax` under the take move, with no exit. -/
theorem wake_hab_closed {asm : Scc.Sem.X64.Asm} {E : Scc.Sem.Entry} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : Spike.Lib.X64ConsumerS.OwnS} {I : Spike.Lib.X64ConsumerS.InvS}
    {p : Prog} {L0 : Lbl} {ls : Lsize} {Ctx : FragS isa} {ls0 : Lsize} {frM : TermRun.Frame} {ax : Int64}
    {c0 : Ctl}
    (hpa : cellsOf asm = some o.prog) (hpo : o.prog = wakeCells) (hlo : (Ly).Λ.code.lo = lo)
    (hax : ax.toBitVec.toNat = ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    /- the start control's box shape, facts and placement -/
    (hbx : C0Box c0) (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 [])
    (hpl0 : ∀ s, PlacedSE (Ly).Λ L0 s c0 [])
    /- the heap abort path's `ownG` → `ownGXW` lift (no producer yet) -/
    (hlft : HabLft (Ly)) :
    SegWS (W0 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) (Spike.Lib.X64.WakePh.ownGXW (Ly) (ntA (Ly).lab))
        (Spike.Lib.X64.WakeOD.arW hpw i) p DtW (Spike.Lib.X64.WriteAb.Ab (Ly).lab)
        (Spike.Lib.X64.WakeOD.ClW hpw i) (Spike.Lib.X64.ThreadsAb.Ac (Ly).lab pfxM) Ctx L0 ls0 frM (X0W (Ly) ax))
      (Spike.Lib.X64.PhRec.K (Ly) (Spike.Lib.X64.Rt.rS0 (Ly))) p L0 (MSf)
      (Frag.at (fun s c => ∃ v m0 σC,
        At (Ly).exe (Ly).endPc (wR (RS wcLsw v) wcD)
          (wF (RS wcLsw v) wcD (FS (Ly) (Spike.Lib.X64.Rt.rS0 (Ly)) wcLsw 0#64 v) m0 σC)
          (wX ((MSf) []) (Ly).lab (wR (RS wcLsw v) wcD) ((JW) σC) .abort) s c ∧
        TP (tpOf (tcbS (Ly))) s) [])
      (fun _ _ _ => False) := by
  have hprog : (Ly).prog = wakeCells := hpo
  have hlab : ∀ l x, codeLabel lo wakeCells l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceWX.hlab_ofPlaceWX hpw i l x (by rw [hlo, hpo]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceWX.abortLbl_of_placeWX (Spike.Lib.PlaceWX.link i hpw)
  have hwf := Spike.Lib.PlaceWX.wf_link_of_placeWX i hpw
  have hab : ∀ s : State, s.st.2 = (Ly).lab "scc_rt_abort_heap_exit" → ((MSf) []).abortAt s := fun s hs => by
    obtain ⟨-, e9⟩ := Spike.Lib.X64.WakePh.abH_labs hlab
    refine ⟨.heap, 4202761, ?_, by unfold pcOf; rw [hs, e9]; rfl⟩
    rw [Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpa]
    show codeLabel (Ly).Λ.code.lo (Ly).prog ((Ly).Λ.abortLbl .heap) = _
    rw [hprog, hlo, hΛ, ← codeT_eq]; decide +kernel
  refine (SegWS.exists_pre (P := fun g : BitVec 64 × MachineData × Spike.Lib.X64.AS =>
      Frag.at (At (Ly).exe (Ly).endPc (wR (RS wcLsw g.1) wcD)
        (wF (RS wcLsw g.1) wcD (FS (Ly) (Spike.Lib.X64.Rt.rS0 (Ly)) wcLsw 0#64 g.1) g.2.1 g.2.2)
        (wX ((MSf) []) (Ly).lab (wR (RS wcLsw g.1) wcD) ((JW) g.2.2) .abort)) []) fun ⟨v, m0, σC⟩ => ?_).mono_pre
    fun _ _ _ ⟨⟨v, m0, σC, h, _⟩, hf⟩ => ⟨⟨v, m0, σC⟩, h, hf⟩
  by_cases hv : v = topS (Ly) 0#64
  case neg =>
    refine SegWS.empty fun _ _ _ h => ?_
    obtain ⟨⟨-, -, -, -, _, -, hF, -⟩, -⟩ := h
    exact hv (Spike.Lib.X64.WakePh.WcWfR.v_top hF)
  subst hv
  obtain ⟨hR, hF⟩ := Spike.Lib.X64.WakePh.WcWfR.top_ok (Ly) hwf m0 σC
  exact Spike.Lib.X64.Flow.WakeWc.wc_heapAb_segWS hF hR (by show -wcD ≤ -272; decide)
    (by show (-232 : Int) ≤ 8; decide) rfl
    (wc_heapAbStubKX hprog hlo hlab _ hΛ hF hR (by show -wcD ≤ -272; decide)
      (by show (-232 : Int) ≤ 8; decide) rfl (.inl rfl) (fun _ h => h.2)
      (hctl_c0 rfl rfl rfl hbx hc0 hpl0) hab (x0W_abort hlab hax) hlft) _

end Place

end Spike.Lib.X64.WakePh.StartH0C

/-- info: 'Spike.Lib.X64.WakePh.StartH0C.wc_heapAbStubKX' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0C.wc_heapAbStubKX

/-- info: 'Spike.Lib.X64.WakePh.StartH0C.wake_hab_closed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0C.wake_hab_closed
