/-
**The heap abort's path in `W0` with the placement asked at the path's frame condition only** (x86-64; the
twin of `Spike/Lib/A64HelloHabCtlS.lean`): `HAbStub.hpathW_hab0H` asks the allocator's control `c0` placed at
EVERY state; at level 1 `c0` sits at rodata's slice word whose base is dynamic, so no placement serves every
state. The path's states only need it under the path's frame condition `F` (stable in the path's region,
`FStable`), e.g. the region below the allocator's call entered from the caller's memory and abstraction
(`fstable_enter`), where `wc_main`'s frame is kept.

- `hpathW_FH`: every path state's memory meets a stable frame condition (`FStable`).
- `hpathW_hab0HS`: `hpathW_hab0H` with the placement at `F`'s states.

Unlike AArch64, `HPathW` has 11 obligations (the stub's `leaq` is one node), the region is `[-24, 16)` with no
alignment premise, and the return address is `.Lscc_rt_alloc.full + 12` (as `X64HelloHAbStub.hpathW_hab0H`);
the take site is told apart from the heap exit on resolved addresses (A64's `lab_neH`).

Not twinned (unreachable from the AArch64 root `hello_linkedA`, so twins only live constants): `HabCtlHS`,
`HabCtlH.toS`, `wc_heapAbStubKHS` (and so the import of `A64HelloHabCtl`, whose module is unreachable).
-/
import Spike.Lib.X64HelloHAbStub

namespace Spike.Lib.X64.HelloPh.HabCtlS

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open Scc.Sem.X64 (codeLabel pcOf abi)
open SccCode (helloCells)
open Spike.Lib (Arena FragS Frag Region HeapAbortOblA)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64 (ND BlkW NodeW)
open Spike.Lib.X64.Abort.Disp (HPathW)
open Spike.Lib.X64.WakeWf (DtW W0 RunWf)
open Spike.Lib.X64.WakePh (inPc)
open Spike.Lib.X64.HelloPh.StartWf (pfxM)
open Spike.Lib.X64.HelloPh (lo ownGH instOkH siteH abH_labsH abortPhHH hpathW_habGH)
open Spike.Lib.X64.HelloPh.HAbStub (hpathW_hNH hpathW_hAbH hpathW_hXH)

set_option linter.unusedSimpArgs false

variable {L : RuntimeLayout} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}

/-- **Every path state's memory meets a stable frame condition**: at a block's states (the memory outside the
region as at the node, `FStable`) and at a node's (`At`). -/
theorem hpathW_FH {exe : _root_.Executable} {endPc : Int64} (hF : Spike.Lib.X64.FStable R F) :
    HPathW (fun s _ => F s.st.1) (fun _ _ => False) exe endPc R F c0 ra := by
  have hb : ∀ {n : ND} {blk : List (Directive × Nat)},
      BlkW (fun s _ => F s.st.1) (fun _ _ => False) exe endPc R F n blk :=
    fun _ _ _ _ _ _ _ _ hF0 _ _ _ _ _ hD => ⟨hF _ _ hF0 hD, fun _ h => h⟩
  have hn : ∀ {n : ND}, NodeW (fun s _ => F s.st.1) (fun _ _ => False) exe endPc R F n :=
    fun _ _ hA => by obtain ⟨-, -, -, -, -, -, hF0, -⟩ := hA; exact ⟨hF0, fun _ h => h⟩
  exact ⟨hb, hb, hb, hb, hb, hb, hn, hb, hn, hb, hn⟩

section Inst

variable (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
include hp hlo hlab

/-- **`HAbStub.hpathW_hab0H` with the placement at `F`'s states** (`hpl`), `F` stable (`hF`). -/
theorem hpathW_hab0HS {ar : Arena} {p : Prog} {Cl : State → Prop} {Ctx : FragS isa} {L0 : Lbl} {ls0 : Lsize}
    {frM : TermRun.Frame} {X0 : State → Prop} {fs : List TermRun.Frame} (a : BitVec 64)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hR : R.OK) (hlo' : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hra : ra = (L.lab Spike.Lib.X64.Alloc.fullL + 12).toBitVec) (hfs : fs = [] ∨ fs = [frM])
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hc0 : (fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) (hF : Spike.Lib.X64.FStable R F)
    (hpl : ∀ s : State, F s.st.1 → PlacedSE L.Λ L0 s c0 fs)
    (hobl : HeapAbortOblA ar.cells ar.ctr c0) (hX0 : ∀ s, inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0 s) :
    HPathW (fun s c => W0 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) ar p DtW (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab pfxM) Ctx L0 ls0 frM X0 s c fs) (fun _ _ => False) L.exe L.endPc
      R F c0 ra := by
  have hsite := siteH hp hlo hlab
  have ef : L.lab Spike.Lib.X64.Alloc.fullL = Int64.ofNat 4198788 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have e6 : L.lab ".Lscc_rt_alloc_tcb.x6" = Int64.ofNat 4199282 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have e27 : L.lab ".Lwc_main.x27" = Int64.ofNat 4203909 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have es : L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat 4200314 :=
    hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  obtain ⟨-, h2⟩ := abH_labsH hlab
  have hG := hpathW_habGH hp hlo hsite (Λ := L.Λ) (F := F) (c0 := c0) (ra := ra) a hΛ hlab hR hlo' hhi
    (fun h => absurd (hra.symm.trans h) (by rw [ef, e6]; decide)) (by rw [hra, ef, e27]; decide)
  have hPh := Spike.Lib.X64.HelloWf.hpathW_phH (Cl := Cl) (F := F) (c0 := c0) (ra := ra)
    (instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)) (by rw [hp]; exact SccCode.hello_abort)
    (abortPhHH (Λ := L.Λ) (lab := L.lab) hΛ hlab) hlab hR hlo' hhi
    (fun a' ha => by rw [hsite] at ha; cases ha; simp only [Abort.heap, h2, es]; decide)
    (by rw [hra]; exact Spike.Lib.X64.HelloWf.hra_allocH hlab)
  have hN := hpathW_hNH (ar := ar) (p := p) (L0 := L0) (ls0 := ls0) (Ctx := Ctx) (fs := fs) (F := F) (c0 := c0)
    (ra := ra) hp hlo hlab a hR hlo' hhi
  have hAb := hpathW_hAbH (ar := ar) (Ab := Spike.Lib.X64.WriteAb.Ab L.lab)
    (Ac := Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab pfxM) (fs := fs) (R := R) (F := F) (ra := ra) hp hlo hlab hΛ
    hobl
  have hX := hpathW_hXH (F := F) (c0 := c0) (ra := ra) hp hlo hlab hR hlo' hhi
  have h1 := Abort.Disp.HPathW.and hG hPh fun s c h₁ h₂ => And.intro h₁ h₂
  have h2' := Abort.Disp.HPathW.and h1 Spike.Lib.X64.WakePh.hpathW_hC fun s c h₁ h₂ => And.intro h₁ h₂
  have h3 := Abort.Disp.HPathW.and h2' hN fun s c h₁ h₂ => And.intro h₁ h₂
  have h4 := Abort.Disp.HPathW.and h3 hAb fun s c h₁ h₂ => And.intro h₁ h₂
  have h5 := Abort.Disp.HPathW.and h4 (hpathW_FH hF) fun s c h₁ h₂ => And.intro h₁ h₂
  refine Abort.Disp.HPathW.and h5 hX fun s c h hx => ?_
  obtain ⟨⟨⟨⟨⟨hst, hab, hac⟩, hc⟩, hw⟩, habt⟩, hFs⟩ := h
  subst hc
  exact ⟨hfs, hX0 s hx, Spike.Lib.X64.WakeWf.Wf.intro hst hab hac hcl hc0.1 (hpl s hFs) hw.1 hw.2 hc0.2 habt⟩

end Inst

end Spike.Lib.X64.HelloPh.HabCtlS

/-- info: 'Spike.Lib.X64.HelloPh.HabCtlS.hpathW_FH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HabCtlS.hpathW_FH

/-- info: 'Spike.Lib.X64.HelloPh.HabCtlS.hpathW_hab0HS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HabCtlS.hpathW_hab0HS
