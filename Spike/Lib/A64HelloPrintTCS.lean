/-
**`print`'s call at the worker's frames, its abort closed inside** (hello
plan (4a)/(5), AArch64): `A64HelloCallTCS.call_ndTCS` at hello's fenced
`scc_rt_print`, the callee a `SegTCS` segment at `fr :: fs` (the source's
frame `fr` pushed by the call).

The callee's body is `FA.seg_printFANN` inside `NNZP SysW1` (`print`'s one
system call a `write(1, …)`), lifted to `fr :: fs` (`SegTCS.liftL`,
`noTop_of`); `print`'s abort exit (`x0 = 4` at `scc_rt_abort`, `sp` 48
below `print`'s frame) is closed inside the callee by `seg_jabort4X`
(`NNZXH`, lifted by `noTopX`), so the callee's region reaches 96 bytes below
the call's `sp` (`lo' = -96`) and its only exit is the return. **The
abort's two system calls are still justified by `safeH`'s `AbC` branch**
(`A64HelloAbortX`'s docstring; row 5i).

`Z` at the callee's frames is a family `Zc fr` (`Frag`, at `fr :: fs`):
at `print`'s nodes (`hZP`), at every node of the abort path at the
failure's controls (`hZA`, an `AbortObl` in the dispatcher's region:
`seg_jabort4XA`), never at an `unpark` binding (`hZu`); `hS` puts
`NNH ∧ Zc fr` into the caller's fragment `S` at `fr :: fs`. Both `hZP` and
`hZA` are given the landing fact `CallFC` of their frame condition: every
memory of it comes from a caller's state at `nC` whose slots outside the
callee's 96 bytes it keeps.

- `SegTCS.seq_or`: sequencing on one branch (`SegTC.seq_or` at depth).
- `PrintF.CallFC`: the callee's frame condition lands at the call node.
- `PrintF.seg_printCalleeS`: `print` from its entry to its return at
  `fr :: fs`, the abort closed inside.
- `PrintF.printF_callTCS`: the call node `nC` at the caller's frames `fs`,
  to the caller's nodes, the return's frame run (`hret`) asked.
-/
import Spike.Lib.A64HelloCallTCS
import Spike.Lib.A64HelloAbortObl
import Spike.Lib.A64HelloPrintNN

namespace Spike.Lib.HelloSegTCS.SegTCS

open CoreLang CoreTerm Kraken.Promising
open Spike.Lib Spike.Lib.HelloSegThrS

variable {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide I}
  {S P Q X Y : FragS I}

/-- **Sequencing on one branch** (`SegTC.seq_or` at depth): a segment to
`Q ∨ X`, then one from `X` to `Y`, is one to `Q ∨ Y`. -/
theorem seq_or (h₁ : SegTCS S p lbl ms P (fun s c fs => Q s c fs ∨ X s c fs)) (h₂ : SegTCS S p lbl ms X Y) :
    SegTCS S p lbl ms P (fun s c fs => Q s c fs ∨ Y s c fs) := by
  obtain ⟨i₁, hs₁, hw₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, hw₂, ho₂⟩ := h₂
  refine ⟨fun s c fs => i₁ s c fs ∨ i₂ s c fs, fun s c fs h => .inl (hs₁ s c fs h),
    fun s c fs h => h.elim (hw₁ s c fs) (hw₂ s c fs), ?_⟩
  rintro s c fs (h | h)
  · exact (ho₁ s c fs h).mono fun s c fs h => h.mono fun s c fs h => by
      rcases h with h | h | h
      · exact .inl (.inl h)
      · exact .inr (.inl h)
      · exact .inl (.inr (hs₂ s c fs h))
  · exact (ho₂ s c fs h).mono fun s c fs h => h.mono fun s c fs h =>
      h.elim (fun h => .inl (.inr h)) fun h => .inr (.inr h)

end Spike.Lib.HelloSegTCS.SegTCS

namespace Spike.Lib.A64.Flow.Worker.PrintF

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow
open Spike.Lib.HelloSegTCS (SegTCS)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.PcRuns (PcIn)
open Spike.Lib.A64.Flow.RelZ (RelZ)

/-- **The callee's frame condition lands at the call node** `nC` in the
caller's region `R`: every memory of `F` comes from a caller's state at `nC`
(`Abs`, `nC.J`), keeping its slots outside the callee's 96 bytes below
`nC.o.sp` (`CKept`; `call_ndTCS`'s `hcallee` fact, the frame and the entry
dropped). -/
abbrev CallFC (R : Region) (nC : ND) (F : MachineData → Prop) : Prop :=
  ∀ m, F m → ∃ mC σC c, Abs R nC.o mC σC ∧ nC.J σC c ∧ CKept R nC.o.sp (-96) 0 mC m

section CallTCS

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {ι κ : Sort _} {N' : ι → ND} {E' : κ → ND}

/-- **`print` at the frames `fr :: fs`, its abort closed inside**: from the
entry (`cN … .e` of the call state `σC`) to the return, in any callee
region reaching 96 bytes down (`hlo'`). The body inside `NNZP SysW1`
(`FA.seg_printFANN`, the `write` `hsvc`), the abort inside `NNZXH`
(`seg_jabort4XA`, `Zc` at the path's nodes in any dispatcher region inside
`F'`: `hZA`; the stub's `exit_group` at an abort site: `habt`), both
lifted to `fr :: fs`; `S` from `NNH ∧ Zc` (`hS`). -/
theorem seg_printCalleeS {S : FragS isaLSE2} {Zc : Frag isaLSE2} {fs : List TermRun.Frame} {fr : TermRun.Frame}
    {prog : List Directive} {kp : Nat} {R' : Region} {F' : MachineData → Prop} {σC : AS}
    {Pc Qc : AS → Nat → Ctl → Prop}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hR' : R'.OK) (hal' : R'.base.toNat % 16 = 0) (hlo' : R'.lo ≤ -96) (hhi' : 0 ≤ R'.hi) (hF' : FStable R' F')
    {c0' : Ctl} {x29' ra' : BitVec 64} (hcode : PrintF.Code c0' x29' ra' exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L9_scc_rt_print.0_entry" = (_root_.Executable.labels exe).label "scc_rt_print" + 4 + 4 + 4 + 4 + 4 + 4)
    (hK : (ms (fr :: fs)).K = some Scc.Sem.A64.abi)
    (hlen : σC.regs.X1.toBitVec.toNat < 2 ^ 63)
    (hS : ∀ s c, NNH exe endPc s → Zc s c → S s c (fr :: fs))
    (hZu : ∀ s c, Zc s c → ∀ x a e, c.term ≠ .let_ x (.ext .unpark a) e)
    (hsvc : SegTC (NNZP SysW1 exe endPc Zc) p lbl (ms (fr :: fs))
      (At exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc σC .svc)) (At exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc σC .n5)))
    (hZP : ∀ i, NodeZA Zc exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc σC i) (FA.blkN i))
    (hZA : ∀ (RA : Region) (FA : MachineData → Prop), RA.OK → RA.base.toNat % 16 = 0 → RA.lo ≤ -48 →
      0 ≤ RA.hi → FStable RA FA → (∀ m, FA m → F' m) → ∀ k c, Qc σC k c → AbortObl Zc exe endPc RA FA c)
    (habt : ∀ s, s.exe = exe → s.st.2 = (_root_.Executable.labels exe).label Abort.write.exit → (ms (fr :: fs)).abortAt s) :
    SegTCS S p lbl ms ((At exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc σC .e)).at (fr :: fs))
      (Frag.at (At exe endPc R' F' ((PrintA.E (_root_.Executable.labels exe).label σC.regs.X29.toBitVec σC.regs.X30.toBitVec
        σC.regs.X1.toBitVec.toNat (Pc σC) (Qc σC) .ret).withTp σC.regs.TPIDR_EL0)) (fr :: fs)) := by
  have h1 := SegTCS.liftL (S := S) (p := p) (lbl := lbl) (ms := ms) (fr :: fs)
    (FA.seg_printFANN hF' hR' hal' (by omega) hhi' hlen (c0 := c0') hcode.ghost hentry hsvc hZP)
    (fun s c h => hS s c (NNZP.toH h).1 h.2) (fun s c h => noTop_of hK h.1 (hZu s c h.2))
  have h2 := SegTCS.liftL (S := S) (p := p) (lbl := lbl) (ms := ms) (fr :: fs)
    (seg_jabort4XA (Q := fun _ _ => False)
      (nC := (PrintA.E (_root_.Executable.labels exe).label σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X1.toBitVec.toNat (Pc σC) (Qc σC)
        .abort).withTp σC.regs.TPIDR_EL0)
      hp hend hprog rfl (fun σ _ h => by rw [h.1.1]; rfl) hF' hR' hal'
      (by show R'.lo ≤ -48 - 48; omega) (by show (-48 : Int) < R'.hi; omega) (by show (-48 : Int) % 16 = 0; decide) hK
      (fun m0 σ c h => by
        obtain ⟨⟨-, k, hk⟩, -⟩ := h
        obtain ⟨hRA, halA, hloA, hhiA, hFA⟩ := jabort_callee (nC := (PrintA.E (_root_.Executable.labels exe).label
            σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X1.toBitVec.toNat (Pc σC) (Qc σC) .abort).withTp
            σC.regs.TPIDR_EL0) hF' hR' hal'
          (show R'.lo ≤ -48 - 48 by omega) (show (-48 : Int) < R'.hi by omega) (show (-48 : Int) % 16 = 0 by decide) m0 σ
        exact hZA _ _ hRA halA hloA hhiA hFA (fun _ h => h.1) k c hk)
      (fun _ _ _ _ s _ h => habt s h.1 h.2.2.2.1))
    (fun s c h => hS s c h.toH.1 h.2) (fun s c h => noTopX hK h.1 (hZu s c h.2))
  refine ((h1.mono_post (Q' := fun s c fs' => (Frag.at (At exe endPc R' F' ((PrintA.E (_root_.Executable.labels exe).label
      σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X1.toBitVec.toNat (Pc σC) (Qc σC) .ret).withTp
      σC.regs.TPIDR_EL0)) (fr :: fs)) s c fs' ∨ _) ?_).seq_or h2).mono_post ?_
  · rintro s c fs' ⟨⟨x, h⟩, rfl⟩
    cases x
    · exact .inl ⟨h, rfl⟩
    · exact .inr ⟨h, rfl⟩
  · rintro s c fs' (h | ⟨⟨⟩, -⟩)
    exact h

open Classical in
/-- **A call of hello's `scc_rt_print` at the caller's frames `fs`**
(`call_ndTCS` with `seg_printCalleeS`, `lo' = -96`: `print`'s 48 bytes and
the abort dispatcher's 48 below them). The source calls at `nC` (`hcall`,
`CallTo`), `print`'s predicate `Pc` at 0 bytes of the callee's entry
control (`hP0`); at the return the source's frame run from `fr :: fs` back
to `fs` lands at the caller's nodes (`hret`). `Z` at the callee's frames
is `Zc fr` (`hZP`, `hZA`, `hZu`), into `S` by `hS`; `S` at the call node's
pairs (`hWC`). `hsvc`, `hZP`, `hZA` get their frame condition's landing at `nC`
(`CallFC`). -/
theorem printF_callTCS {S : FragS isaLSE2} {nC : ND} {Pc Qc : AS → Nat → Ctl → Prop} {fs : List TermRun.Frame}
    {Zc : TermRun.Frame → Frag isaLSE2} {prog : List Directive} {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp + -96) (hhi : nC.o.sp < R.hi) (hk16 : nC.o.sp % 16 = 0)
    {c0' : Ctl} {x29' ra' : BitVec 64} (hcode : PrintF.Code c0' x29' ra' exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L9_scc_rt_print.0_entry" = (_root_.Executable.labels exe).label "scc_rt_print" + 4 + 4 + 4 + 4 + 4 + 4)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    (hK : ∀ fr, (ms (fr :: fs)).K = some Scc.Sem.A64.abi)
    (hlen : ∀ σ c, nC.J σ c → σ.regs.X1.toBitVec.toNat < 2 ^ 63)
    (hWC : ∀ s c, At exe endPc R F nC s c → S s c fs)
    (hS : ∀ fr s c, NNH exe endPc s → Zc fr s c → S s c (fr :: fs))
    (hZu : ∀ fr s c, Zc fr s c → ∀ x a e, c.term ≠ .let_ x (.ext .unpark a) e)
    (hcall : ∀ σ c, nC.J σ c → ∃ cE fr, CallToI p c cE fr)
    (hP0 : ∀ σ c cE fr, nC.J σ c → CallToI p c cE fr → Pc σ 0 cE)
    (hsvc : ∀ fr (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -48 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → CallFC R nC F' → ∀ σC c cE, nC.J σC c →
      CallToI p c cE fr → SegTC (NNZP SysW1 exe endPc (Zc fr)) p lbl (ms (fr :: fs))
        (At exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc σC .svc)) (At exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc σC .n5)))
    (hZP : ∀ fr (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -96 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → CallFC R nC F' → ∀ σC c cE, nC.J σC c →
      CallToI p c cE fr →
      ∀ i, NodeZA (Zc fr) exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc σC i) (FA.blkN i))
    (hZA : ∀ fr (RA : Region) (FA : MachineData → Prop), RA.OK → RA.base.toNat % 16 = 0 → RA.lo ≤ -48 →
      0 ≤ RA.hi → FStable RA FA → (∀ m, FA m → F m) → CallFC R nC FA → ∀ σC c cE, nC.J σC c →
      CallToI p c cE fr → ∀ k c', Qc σC k c' → AbortObl (Zc fr) exe endPc RA FA c')
    (habt : ∀ fr s, s.exe = exe → s.st.2 = (_root_.Executable.labels exe).label Abort.write.exit → (ms (fr :: fs)).abortAt s)
    (hret : ∀ σC c cE fr σR c', nC.J σC c → CallToI p c cE fr →
      σR.regs.X29.toBitVec = σC.regs.X29.toBitVec → σR.regs.X30.toBitVec = σC.regs.X30.toBitVec →
      σR.regs.TPIDR_EL0 = σC.regs.TPIDR_EL0 → Pc σC σC.regs.X1.toBitVec.toNat c' →
      (∀ k, R.Off k → ¬ (R.callee nC.o.sp (-96) 0).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      ∃ c'', FrameRun p (c', fr :: fs) (c'', fs) ∧
        Lands N' E' ⟨Int64.ofBitVec σC.regs.X30.toBitVec, ⟨nC.o.sp, []⟩, σR⟩ c'') :
    SegTCS S p lbl ms ((At exe endPc R F nC).at fs) ((Next exe endPc R F N' E').at fs) := by
  refine call_ndTCS (lo' := -96) (hi' := 0) (Ne := cNe (_root_.Executable.labels exe).label Pc Qc nC)
    (Ex := fun σC (_ : Unit) => (PrintA.E (_root_.Executable.labels exe).label σC.regs.X29.toBitVec σC.regs.X30.toBitVec
      σC.regs.X1.toBitVec.toNat (Pc σC) (Qc σC) .ret).withTp σC.regs.TPIDR_EL0)
    hR hal hF hlo (by decide) hhi (by decide) hk16 (by decide) (by decide) hWC
    (fun R' F' hR' hal' hlo' hhi' hF' hFF hReq _ σC fr hreal hfact => ?_) (fun _ => rfl) ?_ ?_
  · obtain ⟨σ', c, cE, hJ, hCT, -, he, -⟩ := hreal
    obtain rfl : σ' = σC := enter_inj he
    subst hReq
    have hFC : CallFC R nC F' := fun m hm => by
      obtain ⟨mC, σ0, c0, -, hA, hJ0, -, -, hk⟩ := hfact m hm
      exact ⟨mC, σ0, c0, hA, hJ0, hk⟩
    refine ((seg_printCalleeS hp hend hprog hR' hal' hlo' hhi' hF' hcode hentry (hK fr) (hlen σ' c hJ) (hS fr)
      (hZu fr) (hsvc fr _ F' hR' hal' (by omega) hhi' hF' hFF hFC σ' c cE hJ hCT) (hZP fr _ F' hR' hal' hlo' hhi' hF' hFF hFC σ' c cE hJ hCT)
      (fun RA FA hRA halA hloA hhiA hFA hFAF k c' hk => hZA fr RA FA hRA halA hloA hhiA hFA
        (fun m h => hFF _ (hFAF m h)) (fun m h => hFC m (hFAF m h)) σ' c cE hJ hCT k c' hk) (habt fr)).mono_pre ?_).mono_post ?_
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

end CallTCS

end Spike.Lib.A64.Flow.Worker.PrintF

/-- info: 'Spike.Lib.A64.Flow.Worker.PrintF.printF_callTCS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.PrintF.printF_callTCS
