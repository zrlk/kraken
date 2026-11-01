/-
**`HabCtlH` with the placement asked on the heap abort's path only** (AArch64): `HabCtl.HabCtlH` (via
`HAbStub.wc_heapAbStubKH`'s `hctl`) asks the allocator's control `c0` placed at EVERY state; at level 1 `c0` is
`c0H` at rodata's slice word `loc ⟨l, 0⟩` whose base `b` is dynamic, so no placement serves every state. The
path's states only need it under the path's frame condition: the region below `-304` entered from the caller's
memory `m0` and abstraction `σC` (`F ∧ CKept R (-304) (-48) 0 m0 ∧ Abs R ⟨-304, []⟩ m0 σC`, `Flow.fstable_enter`),
where `wc_main`'s frame `[-144, 0)` is kept from `m0`.

Copies (no edit) of `HAbStub.hpathW_hab0H` and `HAbStub.wc_heapAbStubKH` with that restricted placement; the
originals stay for level 0, where `c0`'s words are immediates (`HabCtlRdI`, `HabCtlRdM`).

- `HabCtlHS`: the premise with the restricted placement (at the region `R` and frame condition `F` of the
  caller).
- `HabCtlH.toS`: `HabCtlH` gives it.
- `hpathW_FH`: every path state's memory meets a stable frame condition (`FStable`).
- `hpathW_hab0HS`: `hpathW_hab0H` with the placement at `F`'s states.
- `wc_heapAbStubKHS`: `wc_heapAbStubKH` from `HabCtlHS`.
-/
import Spike.Lib.A64HelloHAbStub
import Spike.Lib.A64HelloHabCtl

namespace Spike.Lib.A64.HelloPh.HabCtlS

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq blockAt okPcOf)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi)
open Spike.Lib (Arena FragS Frag Region HeapAbortOblA SegWS)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.Flow (ND BlkW NodeW At)
open Spike.Lib.A64.Abort.Disp (HPathW)
open Spike.Lib.A64.WakeWf (DtW Wf W0 RunWf)
open Spike.Lib.A64.Flow.HelloWc (wXH)
open Spike.Lib.A64.Flow.Worker.Hello.Child (pfxM)
open Spike.Lib.A64.HelloPh (lo ownGH instOkH abH_labsH abortPhHH hpathW_habGH)
open Spike.Lib.A64.HelloPh.HAbStub (lab_neH hpathW_hNH hpathW_hAbH hpathW_hXH abort_offH WcHAbStubH)
open Spike.Lib.A64.HelloPh.HabCtl (HabCtlH)

set_option linter.unusedSimpArgs false

/-- **The control facts at `wXH .abort` with the placement on the path** (row `5h-S-habctl-L1`): as
`HabCtlH`, but `c0` placed only at the states whose memory meets the caller's frame condition `F` and keeps the
caller's region above the callee's window (`CKept R (-304) (-48) 0 m0`) from a caller's memory `m0` abstracted
by `σ` at `-304`. -/
def HabCtlHS (ms : Spike.Lib.MemSide isaLSE2) (lab : String → Int64) (p : Prog) (Λ : Scc.Sem.Layout) (L0 : Lbl)
    (ar : Arena) (fs : List TermRun.Frame) (J1 : Spike.Lib.A64.Flow.AS → Ctl → Prop) (R : Region)
    (F : MachineData → Prop) : Prop :=
  ∀ σ c0, (wXH ms lab J1 .abort).J σ c0 →
    ((fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) ∧
      (∀ m0 (s : State), F s.st.1 → Spike.Lib.A64.Flow.CKept R (-304) (-48) 0 m0 s.st.1 →
        Spike.Lib.A64.Flow.Abs R ⟨-304, []⟩ m0 σ → PlacedSE Λ L0 s c0 fs) ∧
      HeapAbortOblA ar.cells ar.ctr c0

/-- **`HabCtlH` gives `HabCtlHS`** at every region and frame condition. -/
theorem HabCtlH.toS {ms : Spike.Lib.MemSide isaLSE2} {lab : String → Int64} {p : Prog} {Λ : Scc.Sem.Layout}
    {L0 : Lbl} {ar : Arena} {fs : List TermRun.Frame} {J1 : Spike.Lib.A64.Flow.AS → Ctl → Prop} {R : Region}
    {F : MachineData → Prop} (h : HabCtlH ms lab p Λ L0 ar fs J1) : HabCtlHS ms lab p Λ L0 ar fs J1 R F :=
  fun σ c0 hJ => ⟨(h σ c0 hJ).1, fun _ s _ _ _ => (h σ c0 hJ).2.1 s, (h σ c0 hJ).2.2⟩

variable {L : RuntimeLayout} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}

/-- **Every path state's memory meets a stable frame condition**: at a block's states (the memory outside the
region as at the node, `FStable`) and at a node's (`At`). -/
theorem hpathW_FH {exe : _root_.Executable} {endPc : Int64} (hF : Spike.Lib.A64.Flow.FStable R F) :
    HPathW (fun s _ => F s.st.1) (fun _ _ => False) exe endPc R F c0 ra := by
  have hb : ∀ {n : ND} {blk : List Directive}, BlkW (fun s _ => F s.st.1) (fun _ _ => False) exe endPc R F n blk :=
    fun _ _ _ _ _ _ _ _ hF0 _ _ _ _ _ hD => ⟨hF _ _ hF0 hD, fun _ h => h⟩
  have hn : ∀ {n : ND}, NodeW (fun s _ => F s.st.1) (fun _ _ => False) exe endPc R F n :=
    fun _ _ hA => by obtain ⟨-, -, -, -, -, -, hF0, -⟩ := hA; exact ⟨hF0, fun _ h => h⟩
  exact ⟨hb, hb, hb, hb, hb, hb, hn, hn, hb, hn, hb, hn⟩

section Inst

variable (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
include hp hlo hlab

/-- **`HAbStub.hpathW_hab0H` with the placement at `F`'s states** (`hpl`), `F` stable (`hF`). -/
theorem hpathW_hab0HS {ar : Arena} {p : Prog} {Cl : State → Prop} {Ctx : FragS isaLSE2} {L0 : Lbl} {ls0 : Lsize}
    {frM : TermRun.Frame} {X0 : State → Prop} {fs : List TermRun.Frame} (a : BitVec 64)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo' : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hra : ra = (L.lab ".L2_scc_rt_alloc.4_full" + 8).toBitVec)
    (hfs : fs = [] ∨ fs = [frM])
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hc0 : (fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) (hF : Spike.Lib.A64.Flow.FStable R F)
    (hpl : ∀ s : State, F s.st.1 → PlacedSE L.Λ L0 s c0 fs)
    (hobl : HeapAbortOblA ar.cells ar.ctr c0)
    (hX0 : ∀ s, Spike.Lib.A64.WakePh.inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0 s) :
    HPathW (fun s c => W0 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) ar p DtW (Spike.Lib.A64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.A64.HelloWf.AcH L.lab pfxM) Ctx L0 ls0 frM X0 s c fs) (fun _ _ => False) L.exe L.endPc R F
      c0 ra := by
  have hsite := Spike.Lib.A64.HelloPh.siteH hp hlo hlab
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, e12, e13, e14, -⟩ := abH_labsH hlab
  have hG := hpathW_habGH hp hlo hsite (Λ := L.Λ) (F := F) (c0 := c0) (ra := ra) a hΛ hlab hR hal hlo' hhi
    (fun h => absurd (hra.symm.trans h) (by rw [e12, e13]; decide)) (by rw [hra, e12, e14]; decide)
  have hPh := Spike.Lib.A64.HelloWf.hpathW_phH (Cl := Cl) (F := F) (c0 := c0) (ra := ra)
    (instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)) (hp ▸ SccCode.hello_abort)
    (abortPhHH (Λ := L.Λ) (lab := L.lab) hΛ hlab) hlab hR hal hlo' hhi
    (fun a' ha => by
      have h' : codeOf L.Λ.code.lo L.prog "scc_rt_take_site" = some a' := ha
      rw [hp, hlo] at h'
      exact lab_neH hlab (by decide +kernel) (by decide +kernel) h')
    (hra ▸ Spike.Lib.A64.HelloWf.hra_allocH hlab)
  have hN := hpathW_hNH (ar := ar) (p := p) (L0 := L0) (ls0 := ls0) (Ctx := Ctx) (fs := fs) (F := F) (c0 := c0)
    (ra := ra) hp hlo hlab a hR hal hlo' hhi
  have hAb := hpathW_hAbH (ar := ar) (Ab := Spike.Lib.A64.WriteAb.Ab L.lab)
    (Ac := Spike.Lib.A64.HelloWf.AcH L.lab pfxM) (fs := fs) (R := R) (F := F) (ra := ra) hp hlo hlab hΛ hobl
  have hX := hpathW_hXH (F := F) (c0 := c0) (ra := ra) hlab hR hal hlo' hhi hp hlo
  have h1 := Spike.Lib.A64.Abort.Disp.HPathW.and hG hPh fun s c h₁ h₂ => And.intro h₁ h₂
  have h2 := Spike.Lib.A64.Abort.Disp.HPathW.and h1 Spike.Lib.A64.WakePh.hpathW_hC
    fun s c h₁ h₂ => And.intro h₁ h₂
  have h3 := Spike.Lib.A64.Abort.Disp.HPathW.and h2 hN fun s c h₁ h₂ => And.intro h₁ h₂
  have h4 := Spike.Lib.A64.Abort.Disp.HPathW.and h3 hAb fun s c h₁ h₂ => And.intro h₁ h₂
  have h5 := Spike.Lib.A64.Abort.Disp.HPathW.and h4 (hpathW_FH hF) fun s c h₁ h₂ => And.intro h₁ h₂
  refine Spike.Lib.A64.Abort.Disp.HPathW.and h5 hX fun s c h hx => ?_
  obtain ⟨⟨⟨⟨⟨hst, hab, hac⟩, hc⟩, hw⟩, habt⟩, hFs⟩ := h
  subst hc
  exact ⟨hfs, hX0 s hx, Spike.Lib.A64.WakeWf.Wf.intro hst hab hac hcl hc0.1 (hpl s hFs) hw.1 hw.2 hc0.2 habt⟩


/-- **`HAbStub.wc_heapAbStubKH` from `HabCtlHS`**: the placement asked at the path's frame condition
(`Flow.fstable_enter`'s, stable in the callee's region). -/
theorem wc_heapAbStubKHS {R : Region} {F : MachineData → Prop} {ar : Arena} {p : Prog} {Cl : State → Prop}
    {Ctx : FragS isaLSE2} {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame} {X0 : State → Prop}
    {fs : List TermRun.Frame} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
    {J1 : Spike.Lib.A64.Flow.AS → Ctl → Prop} {rS : Scc.Sem.Range} (a : BitVec 64)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hF : Spike.Lib.A64.Flow.FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -352)
    (hhi : 0 ≤ R.hi) (hK : (ms fs).K = some abi) (hfs : fs = [] ∨ fs = [frM])
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hctl : HabCtlHS (ms fs) L.lab p L.Λ L0 ar fs J1 R F)
    (hab : ∀ s : State, s.st.2 = L.lab "scc_rt_abort_heap_exit" → (ms fs).abortAt s)
    (hX0 : ∀ s, Spike.Lib.A64.WakePh.inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0 s) :
    WcHAbStubH (W0 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) ar p DtW (Spike.Lib.A64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.A64.HelloWf.AcH L.lab pfxM) Ctx L0 ls0 frM X0) (Spike.Lib.A64.PhRec.K L rS) p lbl ms L.exe
      L.endPc R F fs J1 := by
  intro m0 σC c0 hJ
  obtain ⟨hc0, hpl, hobl⟩ := hctl σC c0 hJ
  have hkc0 : (-304 : Int) < R.hi := by omega
  have hF' : Spike.Lib.A64.Flow.FStable (R.callee (-304) (-48) 0) (fun m => F m ∧
      Spike.Lib.A64.Flow.CKept R (-304) (-48) 0 m0 m ∧ Spike.Lib.A64.Flow.Abs R ⟨-304, []⟩ m0 σC) :=
    Spike.Lib.A64.Flow.fstable_enter hR hF (by omega) (by decide) hkc0 (by decide) (by omega) (by decide)
      (by decide)
  have hkc : (-304 : Int) < R.hi := by omega
  have hb := Region.callee_base (hi' := 0) hR (show R.lo ≤ -304 + -48 by omega) (by decide) hkc
  have hal' : (R.callee (-304) (-48) 0).base.toNat % 16 = 0 := by
    have : (((R.callee (-304) (-48) 0).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
    omega
  have hR' := Region.callee_ok (hi' := 0) hR (show R.lo ≤ -304 + -48 by omega) (by decide) hkc (by omega)
  have h0 := hpathW_hab0HS (ar := ar) (p := p) (Cl := Cl) (Ctx := Ctx) (L0 := L0) (ls0 := ls0) (frM := frM)
    (X0 := X0) (F := fun m => F m ∧ Spike.Lib.A64.Flow.CKept R (-304) (-48) 0 m0 m ∧
      Spike.Lib.A64.Flow.Abs R ⟨-304, []⟩ m0 σC) hp hlo hlab a hΛ hR' hal'
    (by simp [Region.callee]) (by simp [Region.callee]) rfl hfs hcl hc0 hF'
    (fun s h => hpl m0 s h.1 h.2.1 h.2.2) hobl hX0
  have hX := hpathW_hXH (F := fun m => F m ∧ Spike.Lib.A64.Flow.CKept R (-304) (-48) 0 m0 m ∧
      Spike.Lib.A64.Flow.Abs R ⟨-304, []⟩ m0 σC) (c0 := c0)
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

end Inst

end Spike.Lib.A64.HelloPh.HabCtlS

/-- info: 'Spike.Lib.A64.HelloPh.HabCtlS.HabCtlH.toS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HabCtlS.HabCtlH.toS

/-- info: 'Spike.Lib.A64.HelloPh.HabCtlS.hpathW_FH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HabCtlS.hpathW_FH

/-- info: 'Spike.Lib.A64.HelloPh.HabCtlS.hpathW_hab0HS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HabCtlS.hpathW_hab0HS

/-- info: 'Spike.Lib.A64.HelloPh.HabCtlS.wc_heapAbStubKHS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HabCtlS.wc_heapAbStubKHS
