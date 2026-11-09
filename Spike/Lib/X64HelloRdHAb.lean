/-
**`wc_rodata`'s heap abort at hello's choices, the path pieces** (x86-64; the twin of the first two parts of
`Spike/Lib/A64HelloRdHAb.lean`): the jump to `scc_rt_abort` with `%rdi = 2` and the return address from a callee's
region, and the heap abort path's obligations inside hello's level before the allocation at any offset.

`wc_rodata`'s region ends at its node (`mR R`'s bottom is `-208`), so the dispatcher cannot run below the node
inside it: the node is left to the caller's region at `kc + e` (`at_leave`, as `Hello1.hello1_heapAb_segWS`),
where the dispatcher runs at `R.callee (k - 8) (-24) 16`.

- `Abort.Disp.seg_jabort2RW_up`: `Hello1SetupTail`'s `seg_jabort2W_up` with the return address
  (`seg_jabort2RW`).
- `HAbStub.heapAbStubK_at`: the heap abort path's `StubHRW` inside `W0` at `ownGH`/`AcH` under the take move, at
  any offset `k` and any controls `C` (with their facts `hctl`), the return address `.Lscc_rt_alloc.full + 12`.

No absolute address appears in a statement here.

## Differences from the AArch64 version

- The return address is the pushed word at the node's `%rsp` (`slot e`, read through `leave` at the callee's
  offset `e`, `hoff`), not `x30`; the dispatcher's region is `R.callee (k - 8) (-24) 16` with an 8-aligned `k`
  and no base alignment (AArch64: `R.callee k (-48) 0`, `k % 16 = 0`, `R.base % 16 = 0`), as `X64AbortHeapRW`'s
  `seg_jabort2RW`.
- The return address is `.Lscc_rt_alloc.full + 12` (`Alloc.fullL`; AArch64: `.L2_scc_rt_alloc.4_full + 8`); the
  path pieces are `X64HelloHAbStub`'s and the code fact `X64AbortHeapRWCode.stubHRW_of_code`.
- AArch64's `RdHAb.hello_rd_hab_closed` is stated over the AArch64 start level (`HelloStartWcS.WS`,
  `HelloStartH0G.helloLsw`); its twin is `X64HelloRdHAbCX`'s `hello_rd_hab_closedX`, at the x86-64 start level at
  `ownGHXW`.
-/
import Spike.Lib.X64Hello1SetupTail
import Spike.Lib.X64AbortHeapRWCode
import Spike.Lib.X64HelloHAbStub
import Spike.Lib.X64WakeHAbStubK

namespace Spike.Lib.X64.Abort.Disp

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Spike.Lib.X64

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ra : BitVec 64}

/-- **A jump to `scc_rt_abort` with `%rdi = 2` and the return address `ra` from a callee's region does not
return**: the node `nX` of the callee's region (`ra` at its `%rsp`, an offset of the callee's region) left to the
caller's at `k = kc + e` (`at_leave`), then `seg_jabort2RW` there, the dispatcher below `k`. -/
theorem seg_jabort2RW_up {W : Frag isa} {K : State → State → Prop} {Q : Frag isa}
    {kc lo' hi' e k : Int} {F' : MachineData → Prop} {nX : ND} (hx : nX.o = ⟨e, []⟩) (hk : kc + e = k)
    (hpc : nX.pc = (_root_.Executable.labels exe).label "scc_rt_abort")
    (hrdi : ∀ σ c, nX.J σ c → σ.regs.get64 .rdi = 2#64)
    (hoff : (R.callee kc lo' hi').Off e) (hra : ∀ σ c, nX.J σ c → σ.slot e = ra)
    (hF' : ∀ m, F' m → F m ∧ ∃ m0 σC o, CKept R kc lo' hi' m0 m ∧ Abs R o m0 σC)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ k - 32) (hhi : k + 8 ≤ R.hi) (h8 : k % 8 = 0)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hstub : ∀ m0 σC c0, (∃ σx, nX.J σx c0) → StubHRW W K p lbl ms exe endPc (R.callee (k - 8) (-24) 16)
      (fun m => F m ∧ CKept R (k - 8) (-24) 16 m0 m ∧ Abs R ⟨k, []⟩ m0 σC) c0 ra) :
    SegW W K p lbl ms (At exe endPc (R.callee kc lo' hi') F' nX) Q := by
  subst hk
  refine (seg_jabort2RW (nC := ⟨nX.pc, ⟨kc + e, []⟩, fun σ c => ∃ σx σC, nX.J σx c ∧ True ∧
      σ = leave (R.callee kc lo' hi') kc σC σx⟩) hpc
    (fun σ c ⟨σx, _, hJ, _, hσ⟩ => by subst hσ; exact hrdi σx c hJ) ?_ hF hR hlo hhi h8 hK
    (fun m0 σC c0 ⟨σx, _, hJ, _⟩ => hstub m0 σC c0 ⟨σx, hJ⟩)).mono_pre
    fun _ _ h => at_leave (P := fun _ => True) hx (fun m hm =>
      let ⟨h1, m0, σC, o, h2, h3⟩ := hF' m hm
      ⟨h1, m0, σC, o, h2, h3, trivial⟩) h
  rintro σ c ⟨σx, σC, hJ, -, rfl⟩
  have he : kc + e - kc = e := by omega
  simp only [leave, he, hoff, ↓reduceIte]
  exact hra σx c hJ

end Spike.Lib.X64.Abort.Disp

namespace Spike.Lib.X64.HelloPh.HAbStub

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel abi)
open SccCode (helloCells)
open Spike.Lib (Arena FragS Region HeapAbortOblA)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64.WakeWf (DtW W0 RunWf)
open Spike.Lib.X64.HelloPh.StartWf (pfxM)

variable {L : RuntimeLayout} (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = Spike.Lib.X64.HelloPh.lo)
  (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x → L.lab l = Int64.ofNat x)
include hp hlo hlab

/-- **The heap abort path's obligations under the take move at any offset `k`** (for the controls `C` with
their facts `hctl`): the path inside `W0` at `ownGH`/`AcH` in the region below `k` in the caller's region `R`, the
return address past `.Lscc_rt_alloc.full`'s `call scc_rt_abort`. -/
theorem heapAbStubK_at {R : Region} {F : MachineData → Prop} {ar : Arena} {p : Prog} {Cl : State → Prop}
    {Ctx : FragS isa} {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame} {X0 : State → Prop}
    {fs : List TermRun.Frame} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    {rS : Scc.Sem.Range} {C : Ctl → Prop} {k : Int} (a : BitVec 64)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hF : Spike.Lib.X64.FStable R F) (hR : R.OK) (hlo' : R.lo ≤ k - 32) (hhi : k + 8 ≤ R.hi) (h8 : k % 8 = 0)
    (hK : ms.K = some abi) (hfs : fs = [] ∨ fs = [frM])
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hctl : ∀ c0, C c0 →
      ((fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) ∧ (∀ s, PlacedSE L.Λ L0 s c0 fs) ∧
        HeapAbortOblA ar.cells ar.ctr c0)
    (hab : ∀ s : State, s.st.2 = L.lab Spike.Lib.X64.Abort.heap.exit → ms.abortAt s)
    (hX0 : ∀ s, Spike.Lib.X64.WakePh.inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0 s) :
    ∀ m0 σC c0, C c0 →
      Spike.Lib.X64.Abort.Disp.StubHRW (fun s c => W0 L.Λ (Spike.Lib.X64.PhRec.μ L)
        (Spike.Lib.X64.HelloPh.ownGH L a) ar p DtW (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
        (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab pfxM) Ctx L0 ls0 frM X0 s c fs)
        (Spike.Lib.X64.PhRec.K L rS) p lbl ms L.exe L.endPc (R.callee (k - 8) (-24) 16)
        (fun m => F m ∧ Spike.Lib.X64.CKept R (k - 8) (-24) 16 m0 m ∧ Spike.Lib.X64.Abs R ⟨k, []⟩ m0 σC) c0
        ((L.lab Spike.Lib.X64.Alloc.fullL + 12).toBitVec) := by
  haveI := L.valid
  intro m0 σC c0 hC
  obtain ⟨hc0, hpl, hobl⟩ := hctl c0 hC
  have hR' := Region.callee_ok (hi' := 16) hR (show R.lo ≤ k - 8 + -24 by omega) (by decide) (by omega)
    (by omega)
  have h0 := hpathW_hab0H (ar := ar) (p := p) (Cl := Cl) (Ctx := Ctx) (L0 := L0) (ls0 := ls0) (frM := frM)
    (X0 := X0) (F := fun m => F m ∧ Spike.Lib.X64.CKept R (k - 8) (-24) 16 m0 m ∧
      Spike.Lib.X64.Abs R ⟨k, []⟩ m0 σC) (c0 := c0) hp hlo hlab a hΛ hR'
    (by simp [Region.callee]) (by simp [Region.callee]) rfl hfs hcl hc0 hpl hobl hX0
  have hX := hpathW_hXH (F := fun m => F m ∧ Spike.Lib.X64.CKept R (k - 8) (-24) 16 m0 m ∧
      Spike.Lib.X64.Abs R ⟨k, []⟩ m0 σC) (c0 := c0)
    (ra := (L.lab Spike.Lib.X64.Alloc.fullL + 12).toBitVec) hp hlo hlab hR' (by simp [Region.callee])
    (by simp [Region.callee])
  have hpath := Spike.Lib.X64.WakePh.HPathW.map (Spike.Lib.X64.WakePh.HAbStubK.hpathW_K
    (K := Spike.Lib.X64.PhRec.K L rS)
    (Spike.Lib.X64.Abort.Disp.HPathW.and h0 hX fun _ _ h₁ h₂ => And.intro h₁ h₂)
    fun s _ h s' hk => (abort_offH hlab s h.2).2 (congrArg (fun x : Int64 => x.toBitVec.toNat) hk.1))
    fun _ _ h => h.1
  exact Spike.Lib.X64.StubW.stubHRW_of_code L.lays rfl (hp ▸ SccCode.hello_abort) hK
    (Spike.Lib.X64.fstable_enter hR hF (by omega) (by decide) (by omega) (by omega) (by omega) (by decide)
      (by decide)) hpath fun s _ ⟨_, _, _, hpc, _⟩ => hab s hpc

end Spike.Lib.X64.HelloPh.HAbStub

/-- info: 'Spike.Lib.X64.Abort.Disp.seg_jabort2RW_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Abort.Disp.seg_jabort2RW_up

/-- info: 'Spike.Lib.X64.HelloPh.HAbStub.heapAbStubK_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HAbStub.heapAbStubK_at
