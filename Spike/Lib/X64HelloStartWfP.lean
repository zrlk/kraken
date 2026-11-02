/-
**hello.w's `scc_rt_start` inside `W0`, with the take site's frame
condition also `P`** (x86-64; twin of `X64WakeStartWfP` at
`SccCode.helloCells`, the return point `.x8`; the `P` of
`Spike/Lib/A64HelloStartWf.lean`'s `startEW_W0SH`): `StartWf.startEW_W0SH`
concluding `Rt.StartEWFP … Fw … x8L P` (`Spike/Lib/Rt/X64StartEFA.lean`),
the premise of `Rt.startEF_segWA`, with `scc_rt_thread_init`'s premise
`TiWAtP … x8L P` (`StartTi.startTi_WSPH`,
`Spike/Lib/X64HelloStartTiP.lean`).

The root's `P := ¬ StackM rS0` reaches the take site this way; the P-free
`startEW_W0SH`'s `TiWAt` premise asks the site's obligation under `F`
alone, which is unsatisfiable there (see `X64HelloStartTiP`).

- `startEWP_W0SH`: `StartEWFP` inside `W0`.

## Differences from the AArch64 version

AArch64's `StartEW` carries `P` itself and `Fw` is added by
`StartGlue.StartEW.toF`; here, as in `X64WakeStartWfP`, the proof of
`startEW_W0SH` is repeated with the conclusion `StartEWFP` at any `Fw`
(the two nodes after the switch narrowed by `Ret0.nodeW_mono` /
`Ret0.blkW_mono`), the x86-64 `StartEW` having no `P`. The rest as
`X64HelloStartWf`: byte offsets and sized cells, no `hal`/`h16`, `hout`
for the stack range, `scc_rt_thread_init` returning to `.x8` (`Rt.x8L`;
wake: `.x7`).
-/
import Spike.Lib.X64HelloStartWf
import Spike.Lib.Rt.X64StartEFA

namespace Spike.Lib.X64.HelloPh.StartWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (blockAtB okPcOf)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout InstOk)
open Spike.Lib.X64Consumer (Lbl Lsize SFacts CFacts noRetBlk)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2 AbSt AcSt)
open Spike.Lib.X64 (ND BlkW NodeW At CodeAt cellOff arun okBlk SI FI Abs)
open Spike.Lib.X64.WakeWf (Wf W0 RunWf)
open Spike.Lib.X64.HelloPh.WcW (freeNH freeAtH freeBlkH freeAt_pcH freeAt_labH freeBlk_pcH goodW_of_freeNH
  site_ne_of_freeNH cvH inCvH lab_cvH)
open Spike.Lib (Arena FragS)
open Kraken.Promising.Lower.X64 (CellAt op64)
open Spike.Lib.X64.WakePh (inPc spPool WSep start_memW)

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Range} {Tk : State → Prop} {lbl' : Lbl}
  {K : State → State → Prop} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hX0 : ∀ s, freeNH (pcOf s) = true → X0 s)

include hp hlo hlab hsite hcl hc0 hpl0 hX0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6400000 in
/-- **`startEW_W0SH` with the take site's frame condition also `P`**
(`Rt.StartEWFP`, at any `Fw`): as `startEW_W0SH`, with
`scc_rt_thread_init`'s premise `TiWAtP … x8L P` (`hti`); the nodes after
the switch at `Fw ∧ swFSL …` from theirs at `swFSL …` (`Ret0.nodeW_mono`,
`Ret0.blkW_mono`). -/
theorem startEWP_W0SH (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool) {n0 k0 : BitVec 64} {D : Int}
    (hC0 : CFacts L.Λ lbl' c0) (hR : R.OK) (hRlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) (hn0 : n0 = 0#64)
    (hrS : rS = ⟨(Spike.Lib.X64.Flow.Ret0.stacksA L.lab + k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (h8 : (Spike.Lib.X64.Flow.Ret0.stacksA L.lab + k0 + 16384#64).toNat % 8 = 0)
    (hok : (Spike.Lib.X64.swR (Spike.Lib.X64.Flow.Ret0.stacksA L.lab + k0 + 16384#64) (-D) 0).OK)
    (hL : 8 ≤ D) (hL8 : D % 8 = 0)
    (hoffP : ¬ (L.Λ.stackPool.lo < ((R.callee (-8) (-296) 8).addr (-48)).toNat ∧
      ((R.callee (-8) (-296) 8).addr (-48)).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size))
    (htcb : ∀ F' : MachineData → Prop, Spike.Lib.X64.FStable (R.callee (-8) (-296) 8) F' →
      Spike.Lib.X64.KStable (Spike.Lib.X64.PhRec.K L rS) F' → (∀ m, F' m → F m) →
      ∀ g, g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x0L).toBitVec → ∀ i,
      Spike.Lib.X64.Flow.Ret0.TcbW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
        L.endPc ((R.callee (-8) (-296) 8).callee (-48 - 0) (-184) 8) F' ⟨g, n0, c0⟩ i)
    {P : MachineData → Prop}
    (hti : ∀ F' : MachineData → Prop, Spike.Lib.X64.FStable (R.callee (-8) (-296) 8) F' →
      Spike.Lib.X64.KStable (Spike.Lib.X64.PhRec.K L rS) F' → (∀ m, F' m → F m) →
      ∀ g, g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x1L).toBitVec → ∀ i,
      Spike.Lib.X64.Rt.TiWAtP (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
        L.endPc ((R.callee (-8) (-296) 8).callee (-48 - 0) (-248) 8) F' (Spike.Lib.X64.Flow.Ret0.StackM rS)
        ⟨g, Spike.Lib.X64.Flow.Ret0.pinA L.lab + n0 + 8#64, k0, c0⟩ Spike.Lib.X64.Rt.x8L P i)
    {Fw : _root_.Mem 64 → Prop} :
    Spike.Lib.X64.Rt.StartEWFP (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
      L.endPc R F Fw rS n0 k0 c0 D Spike.Lib.X64.Rt.x8L P := by
  have hW := startEW_hello (a := a) (rS := rS) (lbl := lbl') hp hlo hΛ hlab hs hro hC0 hR hRlo hhi hFr hn0
    hrS hsub hout h8 hok hL hL8
  have hf : ∀ f ∈ Spike.Lib.X64.Rt.startPhTab, _ := fun f hf => startH_fact hΛ (f := f) (start_memW hf)
  have hn : ∀ t, Scc.Cert.Rt.X64.deadN (codeLabel lo helloCells) none t = true → (fun _ => false) t = true :=
    fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') → (0 : Int64) = L.lab r + Int64.ofNat o' :=
    fun _ _ h => nomatch h
  have okB : ∀ {okP : Nat → Bool} {phf : Nat → Nat} {d : Nat → Bool} {pc ra : Int64}
      {blk : List (Directive × Nat)},
      Spike.Lib.X64Consumer.blkPh okP phf d L.lab pc ra blk = true →
      ∀ j < blk.length, okP (pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true := fun h j hj => by
    have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
    simp only [Bool.and_eq_true] at this
    exact this.1.1
  have hrc := hello_rtCodeIn0
  have hs0 := hrc.start0
  simp only [Spike.Lib.X64.Rt.Code.Start.entryIn, Bool.and_eq_true] at hs0
  obtain ⟨⟨e0, e2⟩, e6⟩ := hs0
  have hst := hrc.start
  simp only [Spike.Lib.X64.Flow.startIn, Bool.and_eq_true] at hst
  obtain ⟨⟨⟨⟨-, cb0⟩, cbSi⟩, cbArgs⟩, cbSys⟩ := hst
  have hcl' := hrc.call
  simp only [Spike.Lib.X64.Flow.Ret0.startCallIn, Bool.and_eq_true] at hcl'
  obtain ⟨cc, -⟩ := hcl'
  have hcl2 := hrc.call2
  simp only [Spike.Lib.X64.Flow.Ret0.startCall2In, Bool.and_eq_true] at hcl2
  obtain ⟨cc2, -⟩ := hcl2
  have htl := hrc.tail
  simp only [Spike.Lib.X64.Flow.Ret0.startTailIn, Bool.and_eq_true] at htl
  obtain ⟨⟨⟨⟨⟨tFs, tSys⟩, tSw⟩, tSwDir⟩, tXor⟩, tMain⟩ := htl
  have hR' := Spike.Lib.Region.callee_ok (kc := -8) (lo' := -296) (hi' := 8) hR (by omega) (by decide)
    (by omega) (by omega)
  refine ⟨⟨?_, ?_, ?_⟩, fun F' hFs hKs hF' => ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_, htcb F' hFs hKs hF'⟩,
    ⟨?_, hti F' hFs hKs hF', ?_, ?_, ?_⟩, ⟨?_, fun v => Spike.Lib.X64.Flow.Ret0.nodeW_mono ?_ fun _ h => h.2,
      fun v => Spike.Lib.X64.Flow.Ret0.blkW_mono ?_ fun _ h => h.2⟩⟩⟩
  · -- `_start`'s `xorl %ebp, %ebp`.
    exact nodeW_W0S_fiH hp hlo hlab hsite hcl hc0 hpl0 hX0 (fi := .xor_rr32_self .rbp) (l := "_start") (k := 0)
      (z := 2) e0 (Spike.Lib.X64.Flow.ofNat_zero' _) hW.e.xor
      (Spike.Lib.X64.Rt.PhOfTab.step_of_factOk hlab
        (hf (.step "_start" 0 2) (by simp [Spike.Lib.X64.Rt.startPhTab]))).1
      (by wsfreeH_dec) (by unfold Spike.Lib.X64.HelloWf.siOffW; decide +kernel) (fun _ _ h => h)
  · -- `_start`'s `andq $-16, %rsp`.
    exact nodeW_W0S_andH hp hlo hlab hsite hcl hc0 hpl0 hX0 (i := -16) (l := "_start") (k := 2) (z := 4) e2 rfl
      hW.e.and
      (Spike.Lib.X64.Rt.PhOfTab.step_of_factOk hlab
        (hf (.step "_start" 2 4) (by simp [Spike.Lib.X64.Rt.startPhTab]))).1
      (by wsfreeH_dec) (by unfold Spike.Lib.X64.HelloWf.siOffW; decide +kernel) (fun _ _ h => h)
  · -- `_start`'s call.
    refine blkW_W0SH hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := "_start") (k := 6) e6
      (by show _ = L.lab "_start" + Int64.ofNat 2 + Int64.ofNat 4; rw [Int64.add_assoc]; rfl)
      Spike.Lib.X64.Rt.entryCallB_ok hR (by omega) hhi hW.e.call
      (okB (Spike.Lib.X64.Rt.PhOfTab.blkPh_of_factOk hlab hr hn
        (hf (.blk "_start" 6 Spike.Lib.X64.Rt.Code.Start.entryCall none none)
          (by simp [Spike.Lib.X64.Rt.startPhTab]))))
      (by wsfreeBH_dec) ?_ (by decide +kernel) rfl (fun _ _ h => h)
    intro σ c _ s m _ _ _ hs'
    dsimp only [Spike.Lib.X64.Rt.entryN2] at hs'
    rw [Spike.Lib.X64.Rt.entryCallB_run] at hs'
    exact goodW_of_freeNH hlab (by unfold pcOf; rw [hs']; exact freeAt_labH hlab (by wsfreeH_dec))
  · -- The frame's setup.
    refine blkW_W0SH hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := "scc_rt_start") (k := 0) cb0
      (Spike.Lib.X64.Flow.ofNat_zero' _) Spike.Lib.X64.Flow.xStart0_ok hR' (by show (-296 : Int) ≤ _; omega) (by show _ ≤ (8 : Int); omega)
      (hW.s F' hFs hKs hF').s1.start.w0
      (okB (Spike.Lib.X64.Rt.PhOfTab.blkPh_of_factOk hlab hr hn
        (hf (.blk "scc_rt_start" 0 Spike.Lib.X64.Flow.xStart0 none none) (by simp [Spike.Lib.X64.Rt.startPhTab]))))
      (by wsfreeBH_dec) ?_ (by decide +kernel) Spike.Lib.X64.Rt.StartU.xStart0_noRet (fun _ _ h => h)
    intro σ c _ s m _ _ _ hs'
    rw [Spike.Lib.X64.Flow.xStart0_run] at hs'
    have := freeAt_pcH hlab (l := "scc_rt_start") (os := [8]) (by wsfreeH_dec) (o := 8) (by simp)
    exact goodW_of_freeNH hlab (by unfold pcOf; rw [hs']; exact this)
  · -- The handler's `lea`.
    exact nodeW_W0SH hp hlo hlab hsite hcl hc0 hpl0 hX0 (si := Spike.Lib.X64.Flow.siSig)
      (l := Spike.Lib.X64.Flow.startE) (k := 0) (z := 7) cbSi (Spike.Lib.X64.Flow.ofNat_zero' _)
      (hW.s F' hFs hKs hF').s1.start.w1
      (Spike.Lib.X64.Rt.PhOfTab.step_of_factOk hlab
        (hf (.step Spike.Lib.X64.Flow.startE 0 7) (by simp [Spike.Lib.X64.Rt.startPhTab]))).1
      (by wsfreeH_dec) (by unfold Spike.Lib.X64.HelloWf.siOffW; decide +kernel) (fun _ _ ⟨_, h, _⟩ => h)
  · -- The arguments.
    refine blkW_W0SH hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := Spike.Lib.X64.Flow.startE) (k := 7) cbArgs
      rfl Spike.Lib.X64.Flow.xStartArgs_ok hR' (by show (-296 : Int) ≤ _; omega) (by show _ ≤ (8 : Int); omega) (hW.s F' hFs hKs hF').s1.start.w2
      (okB (Spike.Lib.X64.Rt.PhOfTab.blkPh_of_factOk hlab hr hn
        (hf (.blk Spike.Lib.X64.Flow.startE 7 Spike.Lib.X64.Flow.xStartArgs none none)
          (by simp [Spike.Lib.X64.Rt.startPhTab]))))
      (by wsfreeBH_dec) ?_ (by decide +kernel) Spike.Lib.X64.Rt.StartU.xStartArgs_noRet (fun _ _ ⟨_, h, _⟩ => h)
    intro σ c _ s m _ _ _ hs'
    dsimp only [Spike.Lib.X64.Flow.xStartN2] at hs'
    rw [Spike.Lib.X64.Flow.xStartArgs_run, Spike.Lib.X64.Rt.StartU.startE41] at hs'
    have := freeAt_pcH hlab (l := Spike.Lib.X64.Flow.startE) (os := [41]) (by wsfreeH_dec) (o := 41) (by simp)
    exact goodW_of_freeNH hlab (by unfold pcOf; rw [hs']; exact this)
  · -- `rt_sigaction`'s `syscall`.
    exact nodeW_W0S_svcH hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := Spike.Lib.X64.Flow.startE) (k := 41) (z := 2)
      cbSys (Spike.Lib.X64.Rt.StartU.startE41 _).symm (hW.s F' hFs hKs hF').s1.start.w3
      (Spike.Lib.X64.Rt.PhOfTab.step_of_factOk hlab
        (hf (.step Spike.Lib.X64.Flow.startE 41 2) (by simp [Spike.Lib.X64.Rt.startPhTab]))).1
      (by wsfreeH_dec) (by unfold Spike.Lib.X64.HelloWf.siOffW; decide +kernel) (fun _ _ ⟨_, h, _⟩ => h)
  · -- The call block of `scc_rt_alloc_tcb`.
    refine blkW_W0SH hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := Spike.Lib.X64.Flow.startE) (k := 43) cc rfl
      Spike.Lib.X64.Flow.Ret0.startCall_ok hR' (by show (-296 : Int) ≤ _; omega) (by show _ ≤ (8 : Int); omega) (hW.s F' hFs hKs hF').s1.blk
      (okB (Spike.Lib.X64.Rt.PhOfTab.blkPh_of_factOk hlab hr hn
        (hf (.blk Spike.Lib.X64.Flow.startE 43 Spike.Lib.X64.Rt.Code.Start.startCall none none)
          (by simp [Spike.Lib.X64.Rt.startPhTab]))))
      (by wsfreeBH_dec) ?_ (by decide +kernel) Spike.Lib.X64.Rt.StartU.startCall_noRet (fun _ _ h => h.1)
    intro σ c _ s m hA _ _ hs'
    dsimp only [Spike.Lib.X64.Flow.Ret0.startN1R] at hA hs'
    rw [Spike.Lib.X64.Flow.Ret0.startCall_run] at hA hs'
    refine goodW_fnH hA rfl (by rw [hs']) hoffP (.inl ?_)
    unfold inPc pcOf; rw [hs']
    refine ⟨Nat.le_refl _, ?_⟩
    show (L.lab "scc_rt_alloc_tcb").toBitVec.toNat < (L.lab "scc_rt_thread_reserve").toBitVec.toNat
    rw [labCvH hlab "scc_rt_alloc_tcb" (by rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel)
        (by unfold cvH; rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel),
      labCvH hlab "scc_rt_thread_reserve" (by rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel)
        (by unfold cvH; rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel)]
    unfold cvH; rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel
  · -- `.x0`'s block, the call of `scc_rt_thread_init`.
    refine blkW_W0SH hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := Spike.Lib.X64.Flow.Ret0.x0L) (k := 0) cc2
      (Spike.Lib.X64.Flow.ofNat_zero' _) Spike.Lib.X64.Flow.Ret0.startCall2_ok hR' (by show (-296 : Int) ≤ _; omega) (by show _ ≤ (8 : Int); omega)
      (hW.s F' hFs hKs hF').s2.b0
      (okB (Spike.Lib.X64.Rt.PhOfTab.blkPh_of_factOk hlab hr hn
        (hf (.blk Spike.Lib.X64.Rt.Code.Start.x0L 0 Spike.Lib.X64.Rt.Code.Start.startCall2 none none)
          (by simp [Spike.Lib.X64.Rt.startPhTab]))))
      (by wsfreeBH_dec) ?_ (by decide +kernel) Spike.Lib.X64.Rt.StartU.startCall2_noRet (fun _ _ h => h.1.1.1)
    intro σ c _ s m hA _ _ hs'
    dsimp only [Spike.Lib.X64.Flow.Ret0.startN2R] at hA hs'
    rw [Spike.Lib.X64.Flow.Ret0.startCall2_run] at hA hs'
    refine goodW_fnH hA rfl (by rw [hs']) hoffP (.inr ?_)
    unfold inPc pcOf; rw [hs']
    refine ⟨Nat.le_refl _, ?_⟩
    show (L.lab "scc_rt_thread_init").toBitVec.toNat < (L.lab "scc_rt_stack_release").toBitVec.toNat
    rw [labCvH hlab "scc_rt_thread_init" (by rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel)
        (by unfold cvH; rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel),
      labCvH hlab "scc_rt_stack_release" (by rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel)
        (by unfold cvH; rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel)]
    unfold cvH; rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel
  · -- `.x1`'s block.
    refine blkW_W0SH hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := Spike.Lib.X64.Flow.Ret0.x1L) (k := 0) tFs
      (Spike.Lib.X64.Flow.ofNat_zero' _) Spike.Lib.X64.Flow.Ret0.startFs_ok hR' (by show (-296 : Int) ≤ _; omega) (by show _ ≤ (8 : Int); omega)
      (hW.s F' hFs hKs hF').s2.fs
      (okB (Spike.Lib.X64.Rt.PhOfTab.blkPh_of_factOk hlab hr hn
        (hf (.blk Spike.Lib.X64.Rt.Code.Start.x1L 0 Spike.Lib.X64.Rt.Code.Start.startFs none none)
          (by simp [Spike.Lib.X64.Rt.startPhTab]))))
      (by wsfreeBH_dec) ?_ (by decide +kernel) Spike.Lib.X64.Rt.StartU.startFs_noRet (fun _ _ h => h.1.1)
    intro σ c _ s m _ _ _ hs'
    dsimp only [Spike.Lib.X64.Flow.Ret0.startN3] at hs'
    rw [Spike.Lib.X64.Flow.Ret0.startFs_run] at hs'
    have := freeAt_pcH hlab (l := Spike.Lib.X64.Flow.Ret0.x1L) (os := [18]) (by wsfreeH_dec) (o := 18) (by simp)
    exact goodW_of_freeNH hlab (by unfold pcOf; rw [hs']; exact this)
  · -- `arch_prctl`'s `syscall`.
    exact nodeW_W0S_svcH hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := Spike.Lib.X64.Flow.Ret0.x1L) (k := 18) (z := 2)
      tSys rfl (hW.s F' hFs hKs hF').s2.sys
      (Spike.Lib.X64.Rt.PhOfTab.step_of_factOk hlab
        (hf (.step Spike.Lib.X64.Rt.Code.Start.x1L 18 2) (by simp [Spike.Lib.X64.Rt.startPhTab]))).1
      (by wsfreeH_dec) (by unfold Spike.Lib.X64.HelloWf.siOffW; decide +kernel) (fun _ _ h => h.1)
  · -- The block before the switch.
    refine blkW_W0SH hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := Spike.Lib.X64.Flow.Ret0.x1L) (k := 20) tSw
      rfl Spike.Lib.X64.Flow.Ret0.startSw_ok hR' (by show (-296 : Int) ≤ _; omega) (by show _ ≤ (8 : Int); omega) (hW.s F' hFs hKs hF').s2.sw
      (okB (Spike.Lib.X64.Rt.PhOfTab.blkPh_of_factOk hlab hr hn
        (hf (.blk Spike.Lib.X64.Rt.Code.Start.x1L 20 Spike.Lib.X64.Rt.Code.Start.startSw none none)
          (by simp [Spike.Lib.X64.Rt.startPhTab]))))
      (by wsfreeBH_dec) ?_ (by decide +kernel) Spike.Lib.X64.Rt.StartU.startSw_noRet (fun _ _ h => h.1)
    intro σ c _ s m _ _ _ hs'
    dsimp only [Spike.Lib.X64.Flow.Ret0.startN5] at hs'
    rw [Spike.Lib.X64.Flow.Ret0.startSw_run, Int64.add_assoc] at hs'
    have := freeAt_pcH hlab (l := Spike.Lib.X64.Flow.Ret0.x1L) (os := [28]) (by wsfreeH_dec) (o := 28) (by simp)
    exact goodW_of_freeNH hlab (by unfold pcOf; rw [hs']; exact this)
  · -- The switch.
    exact nodeW_W0S_regH hp hlo hlab hsite hcl hc0 hpl0 hX0 (w := .W64)
      (op := .mov (.reg (.low .rsp .W64)) (.regOrMem (.reg (.low .rax .W64)))) rfl
      (l := Spike.Lib.X64.Flow.Ret0.x1L) (k := 28) (z := 3) tSwDir rfl (hW.s F' hFs hKs hF').s3.sw
      (swPhH hΛ hlab).sw.1
      (by wsfreeH_dec) (by unfold Spike.Lib.X64.HelloWf.siOffW; decide +kernel) (fun _ _ h => h.1)
  · -- After the switch: `xorl %ebp, %ebp` in the new region.
    by_cases hv : v = Spike.Lib.X64.Flow.Ret0.stacksA L.lab + k0 + 16384#64
    · subst hv
      exact nodeW_W0S_fiH hp hlo hlab hsite hcl hc0 hpl0 hX0 (fi := .xor_rr32_self .rbp)
        (l := Spike.Lib.X64.Flow.Ret0.x1L) (k := 31) (z := 2) tXor rfl ((hW.s F' hFs hKs hF').s3.xor _)
        (swPhH hΛ hlab).xor.1
        (by wsfreeH_dec) (by unfold Spike.Lib.X64.HelloWf.siOffW; decide +kernel) (fun _ _ h => h.1)
    · exact Spike.Lib.X64.Rt.nodeW_ofFalse fun _ h => hv h.1.1
  · -- `call scc_rt_main` in the new region.
    by_cases hv : v = Spike.Lib.X64.Flow.Ret0.stacksA L.lab + k0 + 16384#64
    · subst hv
      refine blkW_W0SH hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := Spike.Lib.X64.Flow.Ret0.x1L) (k := 33) tMain rfl
        (Spike.Lib.X64.Rt.startMain_okL hL) hok (Int.le_refl _) (Int.le_refl _) ((hW.s F' hFs hKs hF').s3.blk _)
        (okB (swPhH hΛ hlab).main) (by wsfreeBH_dec) ?_ (by decide +kernel)
        Spike.Lib.X64.Rt.MainU.startMain_noRet (fun _ _ h => h.1)
      intro σ c _ s m _ _ _ hs'
      dsimp only [Spike.Lib.X64.Flow.Ret0.startN8] at hs'
      rw [Spike.Lib.X64.Flow.Ret0.startMain_run] at hs'
      exact goodW_of_freeNH hlab (by unfold pcOf; rw [hs']; exact freeAt_labH hlab (by wsfreeH_dec))
    · exact Spike.Lib.X64.Rt.blkW_ofFalse fun _ h => hv h.1.1

end Gen

end Spike.Lib.X64.HelloPh.StartWf

/-- info: 'Spike.Lib.X64.HelloPh.StartWf.startEWP_W0SH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartWf.startEWP_W0SH
