/-
**`print`'s call at the worker's frames, landing in `X`** (hello.w, row 5j-wit-W; AArch64):
`Spike/Lib/A64HelloPrintTCS.lean`'s `seg_printCalleeS` and `printF_callTCS` over
`Spike/Lib/HelloSegTCSX.lean`'s `SegTCSX`, so every landing pair of a segment through hello's worker's call of
`print` is in the landing fragment `X`.

`X` at a landing comes from `Zc` (`hZX`) at every pair of `print`'s body and abort path, and from `hXR` at the
one landing outside both: `print`'s `ret` lands at the caller's return address while the source is still in
`print` at `fr :: fs` (the return's frame run is pending). The call node's pairs give `X` by `hXC`.

Release note: when the `X` chain replaces the `SegTCS` one, `seg_printCalleeS` and `printF_callTCS` become
one-line corollaries through `SegTCSX.toS` or are deleted; the release keeps one chain.

- `PrintF.seg_printCalleeSX`: `print` from its entry to its return at `fr :: fs`, the abort closed inside.
- `PrintF.printF_callTCSX`: the call node `nC` at the caller's frames `fs`, to the caller's nodes.
-/
import Spike.Lib.A64HelloPrintTCS
import Spike.Lib.A64HelloCallTCSX

namespace Spike.Lib.A64.Flow.Worker.PrintF

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.PcRuns (PcIn)
open Spike.Lib.A64.Flow.RelZ (RelZ)

section CallTCSX

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {ι κ : Sort _} {N' : ι → ND} {E' : κ → ND}

/-- **`print` at the frames `fr :: fs`, its abort closed inside, landing in `X`** (`seg_printCalleeS` over
`SegTCSX`): `X` from `Zc` at `print`'s and the abort's pairs (`hZX`), and at `print`'s return landing, the
caller's return address with `print`'s control at `fr :: fs` (`hXR`). -/
theorem seg_printCalleeSX {S X : FragS isaLSE2} {Zc : Frag isaLSE2} {fs : List TermRun.Frame} {fr : TermRun.Frame}
    {prog : List Directive} {kp : Nat} {R' : Region} {F' : MachineData → Prop} {σC : AS}
    {Pc Qc : AS → Nat → Ctl → Prop}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hR' : R'.OK) (hal' : R'.base.toNat % 16 = 0) (hlo' : R'.lo ≤ -96) (hhi' : 0 ≤ R'.hi) (hF' : FStable R' F')
    {c0' : Ctl} {x29' ra' : BitVec 64} (hcode : PrintF.Code c0' x29' ra' exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L9_scc_rt_print.0_entry" = (_root_.Executable.labels exe).label
        "scc_rt_print" + 4 + 4 + 4 + 4 + 4 + 4)
    (hK : (ms (fr :: fs)).K = some Scc.Sem.A64.abi)
    (hlen : σC.regs.X1.toBitVec.toNat < 2 ^ 63)
    (hS : ∀ s c, NNH exe endPc s → Zc s c → S s c (fr :: fs)) (hZX : ∀ s c, Zc s c → X s c (fr :: fs))
    (hXR : ∀ s c, At exe endPc R' F' ((PrintA.E (_root_.Executable.labels exe).label σC.regs.X29.toBitVec
        σC.regs.X30.toBitVec
        σC.regs.X1.toBitVec.toNat (Pc σC) (Qc σC) .ret).withTp σC.regs.TPIDR_EL0) s c → X s c (fr :: fs))
    (hZu : ∀ s c, Zc s c → ∀ x a e, c.term ≠ .let_ x (.ext .unpark a) e)
    (hsvc : SegTC (NNZP SysW1 exe endPc Zc) p lbl (ms (fr :: fs))
      (At exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc σC .svc)) (At exe endPc R' F' (cN
          (_root_.Executable.labels exe).label Pc Qc σC .n5)))
    (hZP : ∀ i, NodeZA Zc exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc σC i) (FA.blkN i))
    (hZA : ∀ (RA : Region) (FA : MachineData → Prop), RA.OK → RA.base.toNat % 16 = 0 → RA.lo ≤ -48 →
      0 ≤ RA.hi → FStable RA FA → (∀ m, FA m → F' m) → ∀ k c, Qc σC k c → AbortObl Zc exe endPc RA FA c)
    (habt : ∀ s, s.exe = exe → s.st.2 = (_root_.Executable.labels exe).label Abort.write.exit → (ms (fr ::
        fs)).abortAt s) :
    SegTCSX S X p lbl ms ((At exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc σC .e)).at (fr :: fs))
      (Frag.at (At exe endPc R' F' ((PrintA.E (_root_.Executable.labels exe).label σC.regs.X29.toBitVec
          σC.regs.X30.toBitVec
        σC.regs.X1.toBitVec.toNat (Pc σC) (Qc σC) .ret).withTp σC.regs.TPIDR_EL0)) (fr :: fs)) := by
  have h2' := seg_jabort4XA (Q := fun _ _ => False) (p := p) (lbl := lbl) (ms := ms (fr :: fs))
      (nC := (PrintA.E (_root_.Executable.labels exe).label σC.regs.X29.toBitVec σC.regs.X30.toBitVec
          σC.regs.X1.toBitVec.toNat
        (Pc σC) (Qc σC) .abort).withTp σC.regs.TPIDR_EL0)
      hp hend hprog rfl (fun σ _ h => by rw [h.1.1]; rfl) hF' hR' hal'
      (by show R'.lo ≤ -48 - 48; omega) (by show (-48 : Int) < R'.hi; omega) (by show (-48 : Int) % 16 = 0; decide) hK
      (fun m0 σ c h => by
        obtain ⟨⟨-, k, hk⟩, -⟩ := h
        obtain ⟨hRA, halA, hloA, hhiA, hFA⟩ := jabort_callee (nC := (PrintA.E (_root_.Executable.labels exe).label
            σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X1.toBitVec.toNat (Pc σC) (Qc σC) .abort).withTp
            σC.regs.TPIDR_EL0) hF' hR' hal'
          (show R'.lo ≤ -48 - 48 by omega) (show (-48 : Int) < R'.hi by omega) (show (-48 : Int) % 16 = 0 by decide)
          m0 σ
        exact hZA _ _ hRA halA hloA hhiA hFA (fun _ h => h.1) k c hk)
      (fun _ _ _ _ s _ h => habt s h.1 h.2.2.2.1)
  -- the abort's entry pairs are in its fragment, so `Zc` holds there
  have hP2 : ∀ s c, At exe endPc R' F' ((PrintA.E (_root_.Executable.labels exe).label σC.regs.X29.toBitVec
      σC.regs.X30.toBitVec
      σC.regs.X1.toBitVec.toNat (Pc σC) (Qc σC) .abort).withTp σC.regs.TPIDR_EL0) s c → Zc s c :=
    fun s c h => let ⟨_, hP, hiS, _⟩ := h2'; (hiS s c (hP s c h)).2
  have h1 := SegTCSX.liftL (S := S) (X := X) (p := p) (lbl := lbl) (ms := ms) (fr :: fs)
    (FA.seg_printFANN hF' hR' hal' (by omega) hhi' hlen (c0 := c0') hcode.ghost hentry hsvc hZP)
    (fun s c h => hS s c (NNZP.toH h).1 h.2) (fun s c h => noTop_of hK h.1 (hZu s c h.2))
    (fun s c h => hZX s c h.2) (fun s c ⟨x, h⟩ => by
      cases x
      · exact hXR s c h
      · exact hZX s c (hP2 s c h))
  have h2 := SegTCSX.liftL (S := S) (X := X) (p := p) (lbl := lbl) (ms := ms) (fr :: fs) h2'
    (fun s c h => hS s c h.toH.1 h.2) (fun s c h => noTopX hK h.1 (hZu s c h.2))
    (fun s c h => hZX s c h.2) (fun _ _ h => h.elim)
  refine ((h1.mono_post (Q' := fun s c fs' => (Frag.at (At exe endPc R' F' ((PrintA.E (_root_.Executable.labels
      exe).label
      σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X1.toBitVec.toNat (Pc σC) (Qc σC) .ret).withTp
      σC.regs.TPIDR_EL0)) (fr :: fs)) s c fs' ∨ _) ?_).seq_or h2).mono_post ?_
  · rintro s c fs' ⟨⟨x, h⟩, rfl⟩
    cases x
    · exact .inl ⟨h, rfl⟩
    · exact .inr ⟨h, rfl⟩
  · rintro s c fs' (h | ⟨⟨⟩, -⟩)
    exact h

open Classical in
/-- **A call of hello's `scc_rt_print` at the caller's frames `fs`, landing in `X`** (`printF_callTCS` over
`SegTCSX`, by `call_ndTCSX` and `seg_printCalleeSX`): `X` at the call node's pairs (`hXC`), from `Zc fr` at the
callee's frames (`hZX`), and at `print`'s return landing in every callee region its frame condition landing at
`nC` (`hXR`, `CallFC`). -/
theorem printF_callTCSX {S X : FragS isaLSE2} {nC : ND} {Pc Qc : AS → Nat → Ctl → Prop} {fs : List TermRun.Frame}
    {Zc : TermRun.Frame → Frag isaLSE2} {prog : List Directive} {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp + -96) (hhi : nC.o.sp < R.hi) (hk16 : nC.o.sp % 16 = 0)
    {c0' : Ctl} {x29' ra' : BitVec 64} (hcode : PrintF.Code c0' x29' ra' exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L9_scc_rt_print.0_entry" = (_root_.Executable.labels exe).label
        "scc_rt_print" + 4 + 4 + 4 + 4 + 4 + 4)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    (hK : ∀ fr, (ms (fr :: fs)).K = some Scc.Sem.A64.abi)
    (hlen : ∀ σ c, nC.J σ c → σ.regs.X1.toBitVec.toNat < 2 ^ 63)
    (hWC : ∀ s c, At exe endPc R F nC s c → S s c fs) (hXC : ∀ s c, At exe endPc R F nC s c → X s c fs)
    (hS : ∀ fr s c, NNH exe endPc s → Zc fr s c → S s c (fr :: fs))
    (hZX : ∀ fr s c, Zc fr s c → X s c (fr :: fs))
    (hXR : ∀ fr (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -96 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → CallFC R nC F' → ∀ σC c cE, nC.J σC c →
      CallToI p c cE fr → ∀ s c', At exe endPc R' F' ((PrintA.E (_root_.Executable.labels exe).label
          σC.regs.X29.toBitVec
        σC.regs.X30.toBitVec σC.regs.X1.toBitVec.toNat (Pc σC) (Qc σC) .ret).withTp σC.regs.TPIDR_EL0) s c' →
      X s c' (fr :: fs))
    (hZu : ∀ fr s c, Zc fr s c → ∀ x a e, c.term ≠ .let_ x (.ext .unpark a) e)
    (hcall : ∀ σ c, nC.J σ c → ∃ cE fr, CallToI p c cE fr)
    (hP0 : ∀ σ c cE fr, nC.J σ c → CallToI p c cE fr → Pc σ 0 cE)
    (hsvc : ∀ fr (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -48 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → CallFC R nC F' → ∀ σC c cE, nC.J σC c →
      CallToI p c cE fr → SegTC (NNZP SysW1 exe endPc (Zc fr)) p lbl (ms (fr :: fs))
        (At exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc σC .svc)) (At exe endPc R' F' (cN
            (_root_.Executable.labels exe).label Pc Qc σC .n5)))
    (hZP : ∀ fr (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -96 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → CallFC R nC F' → ∀ σC c cE, nC.J σC c →
      CallToI p c cE fr →
      ∀ i, NodeZA (Zc fr) exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc σC i) (FA.blkN i))
    (hZA : ∀ fr (RA : Region) (FA : MachineData → Prop), RA.OK → RA.base.toNat % 16 = 0 → RA.lo ≤ -48 →
      0 ≤ RA.hi → FStable RA FA → (∀ m, FA m → F m) → CallFC R nC FA → ∀ σC c cE, nC.J σC c →
      CallToI p c cE fr → ∀ k c', Qc σC k c' → AbortObl (Zc fr) exe endPc RA FA c')
    (habt : ∀ fr s, s.exe = exe → s.st.2 = (_root_.Executable.labels exe).label Abort.write.exit → (ms (fr ::
        fs)).abortAt s)
    (hret : ∀ σC c cE fr σR c', nC.J σC c → CallToI p c cE fr →
      σR.regs.X29.toBitVec = σC.regs.X29.toBitVec → σR.regs.X30.toBitVec = σC.regs.X30.toBitVec →
      σR.regs.TPIDR_EL0 = σC.regs.TPIDR_EL0 → Pc σC σC.regs.X1.toBitVec.toNat c' →
      (∀ k, R.Off k → ¬ (R.callee nC.o.sp (-96) 0).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      ∃ c'', FrameRun p (c', fr :: fs) (c'', fs) ∧
        Lands N' E' ⟨Int64.ofBitVec σC.regs.X30.toBitVec, ⟨nC.o.sp, []⟩, σR⟩ c'') :
    SegTCSX S X p lbl ms ((At exe endPc R F nC).at fs) ((Next exe endPc R F N' E').at fs) := by
  refine call_ndTCSX (lo' := -96) (hi' := 0) (Ne := cNe (_root_.Executable.labels exe).label Pc Qc nC)
    (Ex := fun σC (_ : Unit) => (PrintA.E (_root_.Executable.labels exe).label σC.regs.X29.toBitVec
      σC.regs.X30.toBitVec σC.regs.X1.toBitVec.toNat (Pc σC) (Qc σC) .ret).withTp σC.regs.TPIDR_EL0)
    hR hal hF hlo (by decide) hhi (by decide) hk16 (by decide) (by decide) hWC hXC
    (fun R' F' hR' hal' hlo' hhi' hF' hFF hReq _ σC fr hreal hfact => ?_) (fun _ => rfl) ?_ ?_
  · obtain ⟨σ', c, cE, hJ, hCT, -, he, -⟩ := hreal
    obtain rfl : σ' = σC := enter_inj he
    subst hReq
    have hFC : CallFC R nC F' := fun m hm => by
      obtain ⟨mC, σ0, c0, -, hA, hJ0, -, -, hk⟩ := hfact m hm
      exact ⟨mC, σ0, c0, hA, hJ0, hk⟩
    refine ((seg_printCalleeSX hp hend hprog hR' hal' hlo' hhi' hF' hcode hentry (hK fr) (hlen σ' c hJ) (hS fr)
      (hZX fr) (hXR fr _ F' hR' hal' hlo' hhi' hF' hFF hFC σ' c cE hJ hCT) (hZu fr)
      (hsvc fr _ F' hR' hal' (by omega) hhi' hF' hFF hFC σ' c cE hJ hCT)
      (hZP fr _ F' hR' hal' hlo' hhi' hF' hFF hFC σ' c cE hJ hCT)
      (fun RA FA hRA halA hloA hhiA hFA hFAF k c' hk => hZA fr RA FA hRA halA hloA hhiA hFA
        (fun m h => hFF _ (hFAF m h)) (fun m h => hFC m (hFAF m h)) σ' c cE hJ hCT k c' hk)
      (habt fr)).mono_pre ?_).mono_post ?_
    · rintro s c' fs' ⟨⟨a, b, d, e, σ, hA, hD, hJ', -, -⟩, rfl⟩
      exact ⟨⟨a, b, d, e, σ, hA, hD, hJ'⟩, rfl⟩
    · rintro s c' fs' ⟨h, rfl⟩
      exact ⟨⟨(), h⟩, rfl⟩
  · intro σC c hJ
    obtain ⟨cE, fr, hCT⟩ := hcall σC c hJ
    exact ⟨σC, cE, fr, hCT, by rw [hpc]; rfl,
      ⟨⟨hP0 σC c cE fr hJ hCT, rfl, rfl, rfl, by simp [enter]⟩, rfl⟩, rfl, c, hJ⟩
  · rintro g ⟨⟩ σC c cE fr σx c' σR hJ hCT ⟨-, he, -⟩ hx hreg - hsl
    obtain rfl : σC = g := enter_inj he
    obtain ⟨⟨h29, h30, hP⟩, htp⟩ := hx
    obtain ⟨c'', hr, h⟩ := hret σC c cE fr σR c' hJ hCT (by rw [hreg]; exact h29) (by rw [hreg]; exact h30)
      (by rw [hreg]; exact htp) hP hsl
    exact ⟨c'', hr, by simpa [PrintA.E, Print.oE, ND.withTp] using h⟩

end CallTCSX

end Spike.Lib.A64.Flow.Worker.PrintF

/-- info: 'Spike.Lib.A64.Flow.Worker.PrintF.seg_printCalleeSX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.PrintF.seg_printCalleeSX

/-- info: 'Spike.Lib.A64.Flow.Worker.PrintF.printF_callTCSX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.PrintF.printF_callTCSX
