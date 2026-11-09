/-
**The start's `wc_rodata` heap-abort exit closes at hello's choices** (AArch64;
the rodata twin of `A64HelloStartH0C`): from `wc_rodata`'s heap abort
`HelloRd.rX … .abort` (at `-208` in `wc_rodata`'s region `mR R = R.callee (-80) (-208) 0`, `x0 = 2`, `x30` past
`.4_full`'s `bl scc_rt_abort`, the strengthened exit of `A64HelloRodata`) under the frame `FR`, the heap abort
runs inside hello's level before the allocation (`WakeWf.W0` at `ownGH`, `arW`, `ClH`, `HelloWf.AcH … pfxM`,
`X0WH … (lab take_site)`, `DtW`, `frM := FR`) under the take move `PhRec.K`, and never exits (`False`).

`wc_rodata`'s region ends at its node (`mR R`'s bottom is `-208`), so the dispatcher cannot run below the node
inside it: the node is left to `scc_rt_main`'s region at `-80 - 208 = -288` (`at_leaveE`, as
`Hello1.hello1_heapAb_segWS`) and the dispatcher runs at `R.callee (-288) (-48) 0` (`R.lo ≤ -336`; the root's
`swR v (-helloLsw) 0` is `480` deep).

- `Abort.Disp.seg_jabort2RW_up`: `Hello1`'s `seg_jabort2W_up` with the return address (`seg_jabort2RW`).
- `HAbStub.heapAbStubK_at`: `HAbStub.wc_heapAbStubKH` at any offset `k` and any controls `C` (with their facts
  `hctl`), not only `wXH .abort`'s at `-304`.
- `hello_rd_hab_closed`: the exit's pairs at `[FR]` start a segment with no exit, at the memory side `msOfA` of
  the entry's marks. Premises: the loader's facts (`hpa`, `hhp`, `hlo0`) and the controls' facts at
  `rX .abort` (`hhabctlRd`, `HabCtlRd.HabCtlRdH`).
-/
import Spike.Lib.A64HelloHabCtlRd
import Spike.Lib.A64HelloStartH0C
import Spike.Lib.A64Hello1SetupTail
import Spike.Lib.A64AbortHeapRW

namespace Spike.Lib.A64.Abort.Disp

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ra : BitVec 64}

/-- **A jump to `scc_rt_abort` with `x0 = 2` and the return address `ra` from a callee's region does not
return**: the node `nX` of the callee's region left to the caller's at `k = kc + e` (`at_leaveE`), then
`seg_jabort2RW` there, the dispatcher below `k` (`Hello1`'s `seg_jabort2W_up` with `x30`). -/
theorem seg_jabort2RW_up {W : Frag isaLSE2} {K : State → State → Prop} {Q : Frag isaLSE2}
    {kc lo' hi' e k : Int} {F' : MachineData → Prop} {nX : ND} (hx : nX.o = ⟨e, []⟩) (hk : kc + e = k)
    (hpc : nX.pc = (_root_.Executable.labels exe).label "scc_rt_abort")
    (hX0 : ∀ σ c, nX.J σ c → σ.regs.X0.toBitVec.toNat = 2)
    (hX30 : ∀ σ c, nX.J σ c → σ.regs.X30.toBitVec = ra)
    (hF' : ∀ m, F' m → F m ∧ ∃ m0 σC o, CKept R kc lo' hi' m0 m ∧ Flow.Abs R o m0 σC)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ k - 48)
    (hkc : k < R.hi) (h16 : k % 16 = 0) (hK : ms.K = some Scc.Sem.A64.abi)
    (hstub : ∀ m0 σC c0, (∃ σx, nX.J σx c0) → StubHRW W K p lbl ms exe endPc (R.callee k (-48) 0)
      (fun m => F m ∧ CKept R k (-48) 0 m0 m ∧ Flow.Abs R ⟨k, []⟩ m0 σC) c0 ra) :
    SegW W K p lbl ms (At exe endPc (R.callee kc lo' hi') F' nX) Q :=
  (seg_jabort2RW (nC := ⟨nX.pc, ⟨k, []⟩, fun σ c => ∃ σx σC, nX.J σx c ∧ True ∧
      σ = leave (R.callee kc lo' hi') kc σC σx⟩) hpc
    (fun σ c ⟨σx, _, hJ, _, hσ⟩ => by subst hσ; exact hX0 σx c hJ)
    (fun σ c ⟨σx, _, hJ, _, hσ⟩ => by subst hσ; exact hX30 σx c hJ) hF hR hal hlo hkc h16 hK
    (fun m0 σC c0 ⟨σx, _, hJ, _⟩ => hstub m0 σC c0 ⟨σx, hJ⟩)).mono_pre
    fun _ _ h => at_leaveE (P := fun _ => True) hx hk (fun m hm =>
      let ⟨h1, m0, σC, o, h2, h3⟩ := hF' m hm
      ⟨h1, m0, σC, o, h2, h3, trivial⟩) h

end Spike.Lib.A64.Abort.Disp

namespace Spike.Lib.A64.HelloPh.HAbStub

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (abi)
open Spike.Lib (Arena FragS Region HeapAbortOblA)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.WakeWf (DtW W0 RunWf)
open Spike.Lib.A64.Flow.Worker.Hello.Child (pfxM)

variable {L : RuntimeLayout} (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = Spike.Lib.A64.WakePh.lo)
  (hlab : ∀ l x, Scc.Cert.Link.A64.codeOf Spike.Lib.A64.WakePh.lo SccCode.helloProg l = some x →
    L.lab l = Int64.ofNat x)
include hp hlo hlab

/-- **The heap abort path's obligations under the take move at any offset `k`** (`wc_heapAbStubKH` at `k`, for
the controls `C` with their facts `hctl`): the path inside `W0` at `ownGH`/`AcH` below `k` in the caller's
region `R`, the return address past `.4_full`'s `bl scc_rt_abort`. -/
theorem heapAbStubK_at {R : Region} {F : MachineData → Prop} {ar : Arena} {p : Prog} {Cl : State → Prop}
    {Ctx : FragS isaLSE2} {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame} {X0 : State → Prop}
    {fs : List TermRun.Frame} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {rS : Scc.Sem.Range} {C : Ctl → Prop} {k : Int} (a : BitVec 64)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hF : Spike.Lib.A64.Flow.FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ k - 48)
    (hkc : k < R.hi) (hk16 : k % 16 = 0) (hK : ms.K = some abi) (hfs : fs = [] ∨ fs = [frM])
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hctl : ∀ c0, C c0 →
      ((fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) ∧ (∀ s, PlacedSE L.Λ L0 s c0 fs) ∧
        HeapAbortOblA ar.cells ar.ctr c0)
    (hab : ∀ s : State, s.st.2 = L.lab "scc_rt_abort_heap_exit" → ms.abortAt s)
    (hX0 : ∀ s, Spike.Lib.A64.WakePh.inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0 s) :
    ∀ m0 σC c0, C c0 →
      Abort.Disp.StubHRW (fun s c => W0 L.Λ (Spike.Lib.A64.PhRec.μ L) (Spike.Lib.A64.HelloPh.ownGH L a) ar p DtW
        (Spike.Lib.A64.WriteAb.Ab L.lab) Cl (Spike.Lib.A64.HelloWf.AcH L.lab pfxM) Ctx L0 ls0 frM X0 s c fs)
        (Spike.Lib.A64.PhRec.K L rS) p lbl ms L.exe L.endPc (R.callee k (-48) 0)
        (fun m => F m ∧ Spike.Lib.A64.Flow.CKept R k (-48) 0 m0 m ∧ Spike.Lib.A64.Flow.Abs R ⟨k, []⟩ m0 σC) c0
        ((L.lab ".L2_scc_rt_alloc.4_full" + 8).toBitVec) := by
  intro m0 σC c0 hC
  obtain ⟨hc0, hpl, hobl⟩ := hctl c0 hC
  have hb := Region.callee_base (hi' := 0) hR (show R.lo ≤ k + -48 by omega) (by decide) hkc
  have hal' : (R.callee k (-48) 0).base.toNat % 16 = 0 := by
    have : (((R.callee k (-48) 0).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
    omega
  have hR' := Region.callee_ok (hi' := 0) hR (show R.lo ≤ k + -48 by omega) (by decide) hkc (by omega)
  have h0 := hpathW_hab0H (ar := ar) (p := p) (Cl := Cl) (Ctx := Ctx) (L0 := L0) (ls0 := ls0) (frM := frM)
    (X0 := X0) (F := fun m => F m ∧ Spike.Lib.A64.Flow.CKept R k (-48) 0 m0 m ∧
      Spike.Lib.A64.Flow.Abs R ⟨k, []⟩ m0 σC) hp hlo hlab a hΛ hR' hal'
    (by simp [Region.callee]) (by simp [Region.callee]) rfl hfs hcl hc0 hpl hobl hX0
  have hX := hpathW_hXH (F := fun m => F m ∧ Spike.Lib.A64.Flow.CKept R k (-48) 0 m0 m ∧
      Spike.Lib.A64.Flow.Abs R ⟨k, []⟩ m0 σC) (c0 := c0)
    (ra := (L.lab ".L2_scc_rt_alloc.4_full" + 8).toBitVec) hlab hR' hal' (by simp [Region.callee])
    (by simp [Region.callee]) hp hlo
  have hpath := Spike.Lib.A64.WakePh.HPathW.map (Spike.Lib.A64.WakePh.HAbStubK.hpathW_K
    (K := Spike.Lib.A64.PhRec.K L rS)
    (Spike.Lib.A64.Abort.Disp.HPathW.and h0 hX fun _ _ h₁ h₂ => And.intro h₁ h₂)
    fun s _ h s' hk => (abort_offH hlab s h.2).2 (congrArg (fun x : Int64 => x.toBitVec.toNat) hk.1))
    fun _ _ h => h.1
  exact Spike.Lib.A64.StubW.stubHRW_of_code L.lays rfl (hp ▸ SccCode.hello_abort) hK
    (Spike.Lib.A64.Flow.fstable_enter hR hF (by omega) (by decide) hkc (by decide) (by omega) (by decide)
      (by decide)) hpath fun s _ ⟨_, _, _, hpc, _⟩ => hab s hpc

end Spike.Lib.A64.HelloPh.HAbStub

namespace Spike.Lib.A64.HelloPh.RdHAb

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf abi textProgram)
open Spike.Lib (Arena FragS Frag Region SegWS)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.Flow (At swR)
open Spike.Lib.A64.Flow.Hello1 (mR mF)
open Spike.Lib.A64.Flow.HelloRd (rX)
open Spike.Lib.A64.WakeWf (DtW)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.WakePh.MainGlue (FS)
open Spike.Lib.A64.HelloPh.StartGlue (X0WH)
open Spike.Lib.A64.HelloPh.StartWcS (WS)
open Spike.Lib.A64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.A64.HelloPh.HabCtlRd (HabCtlRdH)
open Spike.Lib.A64.HelloPh.HAbStub (heapAbStubK_at x0WH_abort)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.HelloSrc (helloSrc)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw i

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
/-- The memory side at the start's labels, the entry's marks. -/
local notation "MSf" => fun fs => Spike.Lib.A64ConsumerA.msOfA (Ly).Λ
  ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ) rd G own
  (Spike.Lib.WakeOD.arW hpw i) I (L0T (Ly).Λ) ls fs

set_option hygiene false in
/-- `rodata`'s frame at the start control. -/
local notation "FR" => Spike.Lib.HelloRdCf.frH Spike.Lib.A64.HelloPh.C0S.c0S.env

/-- **The start's `wc_rodata` heap-abort exit closes** (`StartH0R`/`StartH0U`'s `hCrd`): from `rX .abort` in
`wc_rodata`'s region at the frames `[FR]` (any `v`, `m0`, `σC`), a segment inside `W0` at `ownGH`, `arW`, `ClH`,
`DtW`, `X0WH … (lab take_site)`, `frM := FR` under the take move, with no exit. -/
theorem hello_rd_hab_closed {E : Scc.Sem.Entry} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : Spike.Lib.A64ConsumerS.OwnS} {I : Spike.Lib.A64ConsumerS.InvS} {ls : Lsize}
    {Ctx : FragS isaLSE2} {ls0 : Lsize} {J1 : FAS → FAS → Ctl → Prop}
    (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg)
    (hlo0 : Λ0.code.lo = lo)
    /- named premise: the controls' facts at `rX .abort` -/
    (hhabctlRd : ∀ σC, HabCtlRdH ((MSf) [FR]) (Ly).lab helloSrc (Ly).Λ (L0T (Ly).Λ) (Spike.Lib.WakeOD.arW hpw i)
      [FR] (J1 σC)) :
    SegWS (WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (Spike.Lib.WakeOD.arW hpw i) helloSrc DtW
        (Spike.Lib.A64.HelloPh.ClH (Ly)) Ctx (L0T (Ly).Λ) (ls0T ls0) FR
        (X0WH (Ly) ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL)))
      (Spike.Lib.A64.PhRec.K (Ly) RS) helloSrc (L0T (Ly).Λ) (MSf)
      (Frag.at (fun s c => ∃ v m0 σC,
        At (Ly).exe (Ly).endPc (mR (swR v (-helloLsw) 0))
          (mF (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v) m0 σC)
          (rX ((MSf) [FR]) (Ly).lab (L0T (Ly).Λ) (J1 σC) .abort) s c) [FR])
      (fun _ _ _ => False) := by
  have hp : o.prog = SccCode.helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have hprog : (Ly).prog = SccCode.helloProg := hp
  have hlo : (Ly).Λ.code.lo = lo := hlo0
  have hpL : textProgram asm = .ok (Ly).prog := by rw [hprog]; exact hhp
  have hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceW.hlab_ofPlaceW hpw i l x (by rw [hlo, hp]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link i hpw)
  have hwf := Spike.Lib.PlaceW.wf_link_of_placeW i hpw
  have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
  have hok : (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-helloLsw) 0).OK := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ (by decide) (by decide)
  have hab : ∀ s : State, s.st.2 = (Ly).lab "scc_rt_abort_heap_exit" → ((MSf) [FR]).abortAt s := fun s hs => by
    obtain ⟨-, -, -, -, -, -, -, -, e9, -⟩ := Spike.Lib.A64.HelloPh.abH_labsH hlab
    refine ⟨.heap, 2168400, ?_, by rw [pcOf, hs, e9]; rfl⟩
    rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpL]
    show codeOf (Ly).Λ.code.lo (Ly).prog ((Ly).Λ.abortLbl .heap) = _
    rw [hprog, hlo, hΛ, ← codeT_eq]; decide +kernel
  refine (SegWS.exists_pre (P := fun g : BitVec 64 × MachineData × FAS =>
      Frag.at (At (Ly).exe (Ly).endPc (mR (swR g.1 (-helloLsw) 0))
        (mF (swR g.1 (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 g.1) g.2.1 g.2.2)
        (rX ((MSf) [FR]) (Ly).lab (L0T (Ly).Λ) (J1 g.2.2) .abort)) [FR])
      fun ⟨v, m0, σC⟩ => ?_).mono_pre
    fun _ _ _ ⟨⟨v, m0, σC, h⟩, hf⟩ => ⟨⟨v, m0, σC⟩, h, hf⟩
  by_cases hv : v = Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64
  case neg =>
    refine SegWS.empty fun _ _ _ h => ?_
    obtain ⟨⟨-, -, -, -, _, -, hF, -⟩, -⟩ := h
    exact hv hF.1.2.1.1
  subst hv
  have hF0 := Spike.Lib.A64.Rt.wordsNoneP_swFSL_fstable
    (a := Spike.Lib.A64.Flow.Ret0.limA (UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)))
    (v := Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) hwf hsub hok (by decide) (by decide)
    (by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rS0_subRD _ (by decide) (by decide))
    (by rw [Spike.Lib.A64.Rt.pinA_lab0]; exact Spike.Lib.A64.Rt.rt_hfit _)
    (by rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.stacksA_lab0]
        exact Spike.Lib.A64.Rt.rt_houtD _ (by decide) (by decide))
    (Spike.Lib.A64.Rt.fitS_of_sub _ hsub)
  have hal : (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-helloLsw) 0).base.toNat % 16 = 0 :=
    by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _
  refine SegWS.liftS_noret [FR] (Spike.Lib.A64.Abort.Disp.seg_jabort2RW_up (Q := fun _ _ => False)
      (kc := -80) (lo' := -208) (hi' := 0) (e := -208) (k := -288)
      (nX := rX ((MSf) [FR]) (Ly).lab (L0T (Ly).Λ) (J1 σC) .abort)
      (F' := mF (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-helloLsw) 0)
        (FS (Ly) RS helloLsw 0#64 (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64)) m0 σC)
      rfl (by decide) rfl
      (fun σ c h => by obtain ⟨h2, -⟩ := h; show σ.regs.X0.toNat = 2; rw [h2]; rfl)
      (fun σ c h => h.2.1)
      (fun m hm => ⟨hm.1, m0, σC, _, hm.2.1, hm.2.2⟩) hF0 hok hal
      (by show (-helloLsw : Int) ≤ -288 - 48; decide) (by show (-288 : Int) < 0; decide) (by decide) rfl
      (heapAbStubK_at (C := fun c0 => ∃ σx, (rX ((MSf) [FR]) (Ly).lab (L0T (Ly).Λ) (J1 σC) .abort).J σx c0)
        hprog hlo hlab _ hΛ hF0 hok hal
        (by show (-helloLsw : Int) ≤ -288 - 48; decide) (by show (-288 : Int) < 0; decide) (by decide) rfl
        (.inr rfl) (fun _ h => h.2) (fun c0 hx => hx.elim fun σx hJ => hhabctlRd σC σx c0 hJ) hab
        (x0WH_abort hlab rfl)))
    (fun _ _ h => h) _

end Place

end Spike.Lib.A64.HelloPh.RdHAb

/-- info: 'Spike.Lib.A64.Abort.Disp.seg_jabort2RW_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Abort.Disp.seg_jabort2RW_up

/-- info: 'Spike.Lib.A64.HelloPh.HAbStub.heapAbStubK_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HAbStub.heapAbStubK_at

/--
info: 'Spike.Lib.A64.HelloPh.RdHAb.hello_rd_hab_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdHAb.hello_rd_hab_closed
