/-
**`print`'s call at the worker's frames, landing in `X`, on x86-64** (the twin of
`Spike/Lib/A64HelloPrintTCSX.lean`): hello's `scc_rt_print` called at the caller's frames `fs` as one
`Spike/Lib/HelloSegTCSX.lean` `SegTCSX` segment (`Spike/Lib/X64HelloCallTCSX.lean`'s `call_ndTCSX`), the callee a
segment at `fr :: fs` (the source's frame `fr` pushed by the call), so every landing pair of a segment through
hello's worker's call of `print` is in the landing fragment `X`.

The callee's body is `FA.seg_printFANN` (`Spike/Lib/X64HelloPrintNN.lean`) inside `NNZP SysW1` (`print`'s one
system call a `write(1, …)`), lifted to `fr :: fs` (`SegTCSX.liftL`, `noTop_of`); `print`'s abort exit
(`%rdi = 4` at `scc_rt_abort`) is closed inside the callee by `seg_jabort4XA`
(`Spike/Lib/X64HelloAbortObl.lean`, inside `NNZXH`, lifted by `noTopX`), so the callee's only exit is the
return. `X` at a landing comes from `Zc` (`hZX`) at every pair of `print`'s body and abort path, and from `hXR`
at the one landing outside both: `print`'s `ret` lands at the caller's return address while the source is still
in `print` at `fr :: fs` (the return's frame run is pending). The call node's pairs give `S` and `X` by `hWC`,
`hXC`. The callee obligations (`hsvc`, `hZP`, `hZA`, `hXR`) get their frame condition's landing at the call
node (`Spike/Lib/X64HelloPrintTCS.lean`'s `CallFC`).

- `PrintF.seg_printCalleeSX`: `print` from its entry to its return at `fr :: fs`, the abort closed inside.
- `PrintF.printF_callTCSX`: the call node `nC` at the caller's frames `fs`, to the caller's nodes.

**Where this differs from AArch64** (forced by the x86-64 shape): the callee's frame base is `nC.o.sp - 8`
(`call_ndTCSX` at `e0 = 8`: `call` pushes the return address at `nC.o.sp`, which `print`'s nodes read as their
cell `8`, the caller's cell `ko`), its region reaches 72 bytes below the frame base and 16 above (`print`'s
`[-40, 16)`, and the abort dispatcher's 32 bytes below `print`'s abort exit at `-40`; AArch64: `[-96, 0)`), with
no 16-byte alignment premises (`hal`, `hk16`) but `hk8`; the dispatcher's own region reaches 24 bytes down and 16
up (`jabort_callee`; AArch64: 48 down, 0 up). `print`'s nodes are `PrintF.cN`/`cE`/`cNe`
(`Spike/Lib/X64HelloPrintFramesJ.lean`): the frame pointer is `%rbp`, the return address the pushed cell, the
count `%rsi`, the thread pointer the `%fs` base (AArch64: `X29`, `X30`, `X1`, `TPIDR_EL0`); the `write` node is
`.sys` (AArch64: `.svc`), `.entry` is `scc_rt_print + 16`, the code `Print.Code`. The return lands at
`Int64.ofBitVec (σC.slot nC.o.sp)` past the popped return address (`nC.o.sp + 8`). The one-branch sequencing is
`Spike/Lib/X64HelloSegTCSXC.lean`'s `SegTCSX.seq_or`.
-/
import Spike.Lib.X64HelloPrintTCS
import Spike.Lib.X64HelloCallTCSX
import Spike.Lib.X64HelloSegTCSXC
import Spike.Lib.X64HelloAbortObl
import Spike.Lib.X64HelloPrintNN

namespace Spike.Lib.X64.Flow.Worker.PrintF

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Scc.Cert.Rt.X64 (Lays endOf)

section CallTCSX

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {ι κ : Sort _} {N' : ι → ND} {E' : κ → ND}

/-- **`print` at the frames `fr :: fs`, its abort closed inside, landing in `X`**: from the entry (`cN … .e`
of the call state `σC`, the return address in the caller's cell `ko`) to the return, in any callee region
reaching 72 bytes down and 16 up. The body inside `NNZP SysW1` (`FA.seg_printFANN`, the `write` `hsvc`), the
abort inside `NNZXH` (`seg_jabort4XA`, `Zc` at the path's nodes in any dispatcher region inside `F'`: `hZA`;
the stub's `exit_group` at an abort site: `habt`), both lifted to `fr :: fs`; `S` from `NNH ∧ Zc` (`hS`);
`X` from `Zc` at `print`'s and the abort's pairs (`hZX`), and at `print`'s return landing (`hXR`). -/
theorem seg_printCalleeSX {S X : FragS isa} {Zc : Frag isa} {fs : List TermRun.Frame} {fr : TermRun.Frame}
    {cells : List (Directive × Nat)} {kp : Nat} {R' : Region} {F' : MachineData → Prop} {σC : AS} {ko : Int}
    {Pc Qc : AS → Nat → Ctl → Prop}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hR' : R'.OK) (hlo' : R'.lo ≤ -72) (hhi' : 16 ≤ R'.hi) (hF' : FStable R' F')
    {c0' : Ctl} {rbp' ra' : BitVec 64} (hcode : Print.Code c0' rbp' ra' exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".Lscc_rt_print.entry" =
      (_root_.Executable.labels exe).label "scc_rt_print" + 16)
    (hK : (ms (fr :: fs)).K = some Scc.Sem.X64.abi)
    (hlen : (σC.regs.get64 .rsi).toNat < 2 ^ 63)
    (hS : ∀ s c, NNH exe endPc s → Zc s c → S s c (fr :: fs)) (hZX : ∀ s c, Zc s c → X s c (fr :: fs))
    (hXR : ∀ s c, At exe endPc R' F' (cE (_root_.Executable.labels exe).label Pc Qc ko σC .ret) s c →
      X s c (fr :: fs))
    (hZu : ∀ s c, Zc s c → ∀ x a e, c.term ≠ .let_ x (.ext .unpark a) e)
    (hsvc : SegTC (NNZP SysW1 exe endPc Zc) p lbl (ms (fr :: fs))
      (At exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc ko σC .sys))
      (At exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc ko σC .n5)))
    (hZP : ∀ i, NodeZA Zc exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc ko σC i) (FA.blkN i))
    (hZA : ∀ (RA : Region) (FA : MachineData → Prop), RA.OK → RA.lo ≤ -24 → 16 ≤ RA.hi → FStable RA FA →
      (∀ m, FA m → F' m) → ∀ k c, Qc σC k c → AbortObl Zc exe endPc RA FA c)
    (habt : ∀ s, s.exe = exe → s.st.2 = (_root_.Executable.labels exe).label Abort.write.exit →
      (ms (fr :: fs)).abortAt s) :
    SegTCSX S X p lbl ms ((At exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc ko σC .e)).at (fr :: fs))
      (Frag.at (At exe endPc R' F' (cE (_root_.Executable.labels exe).label Pc Qc ko σC .ret)) (fr :: fs)) := by
  have h2' := seg_jabort4XA (Q := fun _ _ => False) (p := p) (lbl := lbl) (ms := ms (fr :: fs))
      (nC := cE (_root_.Executable.labels exe).label Pc Qc ko σC .abort)
      hp hend hprog rfl (fun σ _ h => h.1.1) hF' hR'
      (by show R'.lo ≤ -40 - 32; omega) (by show (-40 : Int) + 8 ≤ R'.hi; omega)
      (by show (-40 : Int) % 8 = 0; decide) hK
      (fun m0 σ c h => by
        obtain ⟨⟨-, k, hk⟩, -⟩ := h
        obtain ⟨hRA, hloA, hhiA, hFA⟩ := jabort_callee
          (nC := cE (_root_.Executable.labels exe).label Pc Qc ko σC .abort) hF' hR'
          (show R'.lo ≤ -40 - 32 by omega) (show (-40 : Int) + 8 ≤ R'.hi by omega)
          (show (-40 : Int) % 8 = 0 by decide) m0 σ
        exact hZA _ _ hRA hloA hhiA hFA (fun _ h => h.1) k c hk)
      (fun _ _ _ _ s _ h => habt s h.1 h.2.2.2.1)
  -- the abort's entry pairs are in its fragment, so `Zc` holds there
  have hP2 : ∀ s c, At exe endPc R' F' (cE (_root_.Executable.labels exe).label Pc Qc ko σC .abort) s c → Zc s c :=
    fun s c h => let ⟨_, hP, hiS, _⟩ := h2'; (hiS s c (hP s c h)).2
  have h1 := SegTCSX.liftL (S := S) (X := X) (p := p) (lbl := lbl) (ms := ms) (fr :: fs)
    (FA.seg_printFANN hF' hR' (by omega) hhi' hlen (c0 := c0') (codeG hcode) hentry hsvc hZP)
    (fun s c h => hS s c (NNZP.toH h).1 h.2) (fun s c h => noTop_of hK h.1 (hZu s c h.2))
    (fun s c h => hZX s c h.2) (fun s c ⟨x, h⟩ => by
      cases x
      · exact hXR s c h
      · exact hZX s c (hP2 s c h))
  have h2 := SegTCSX.liftL (S := S) (X := X) (p := p) (lbl := lbl) (ms := ms) (fr :: fs) h2'
    (fun s c h => hS s c h.toH.1 h.2) (fun s c h => noTopX hK h.1 (hZu s c h.2))
    (fun s c h => hZX s c h.2) (fun _ _ h => h.elim)
  refine (Spike.Lib.X64HelloSegTCSX.SegTCSX.seq_or (h1.mono_post (Q' := fun s c fs' =>
      (Frag.at (At exe endPc R' F' (cE (_root_.Executable.labels exe).label Pc Qc ko σC .ret)) (fr :: fs)) s c fs' ∨
        _) ?_) h2).mono_post ?_
  · rintro s c fs' ⟨⟨x, h⟩, rfl⟩
    cases x
    · exact .inl ⟨h, rfl⟩
    · exact .inr ⟨h, rfl⟩
  · rintro s c fs' (h | ⟨⟨⟩, -⟩)
    exact h

open Classical in
/-- **A call of hello's `scc_rt_print` at the caller's frames `fs`, landing in `X`** (`call_ndTCSX` at
`e0 = 8`, `lo' = -72`, `hi' = 16`, with `seg_printCalleeSX`): the source calls at `nC` (`hcall`, `CallToI`),
`print`'s predicate `Pc` at 0 bytes of the callee's entry control (`hP0`); at the return (`%rbp` and the `%fs`
base restored, past the popped return address) the source's frame run from `fr :: fs` back to `fs` lands at the
caller's nodes (`hret`). `Z` at the callee's frames is `Zc fr` (`hZP`, `hZA`, `hZu`), into `S` by `hS`, into `X`
by `hZX`; `S` and `X` at the call node's pairs (`hWC`, `hXC`); `X` at `print`'s return landing (`hXR`).
`hsvc`, `hZP`, `hZA`, `hXR` get their frame condition's landing at `nC` (`CallFC`). -/
theorem printF_callTCSX {S X : FragS isa} {nC : ND} {Pc Qc : AS → Nat → Ctl → Prop} {fs : List TermRun.Frame}
    {Zc : TermRun.Frame → Frag isa} {cells : List (Directive × Nat)} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hR : R.OK) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp - 8 + -72) (hhi : nC.o.sp - 8 + 16 ≤ R.hi) (hk8 : (nC.o.sp - 8) % 8 = 0)
    {c0' : Ctl} {rbp' ra' : BitVec 64} (hcode : Print.Code c0' rbp' ra' exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".Lscc_rt_print.entry" =
      (_root_.Executable.labels exe).label "scc_rt_print" + 16)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    (hK : ∀ fr, (ms (fr :: fs)).K = some Scc.Sem.X64.abi)
    (hlen : ∀ σ c, nC.J σ c → (σ.regs.get64 .rsi).toNat < 2 ^ 63)
    (hWC : ∀ s c, At exe endPc R F nC s c → S s c fs) (hXC : ∀ s c, At exe endPc R F nC s c → X s c fs)
    (hS : ∀ fr s c, NNH exe endPc s → Zc fr s c → S s c (fr :: fs))
    (hZX : ∀ fr s c, Zc fr s c → X s c (fr :: fs))
    (hXR : ∀ fr (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -72 → 16 ≤ R'.hi → FStable R' F' →
      (∀ m, F' m → F m) → CallFC R nC F' → ∀ σC c ce, nC.J σC c → CallToI p c ce fr →
      ∀ s c', At exe endPc R' F' (cE (_root_.Executable.labels exe).label Pc Qc nC.o.sp σC .ret) s c' →
        X s c' (fr :: fs))
    (hZu : ∀ fr s c, Zc fr s c → ∀ x a e, c.term ≠ .let_ x (.ext .unpark a) e)
    (hcall : ∀ σ c, nC.J σ c → ∃ ce fr, CallToI p c ce fr)
    (hP0 : ∀ σ c ce fr, nC.J σ c → CallToI p c ce fr → Pc σ 0 ce)
    (hsvc : ∀ fr (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -40 → 16 ≤ R'.hi → FStable R' F' →
      (∀ m, F' m → F m) → CallFC R nC F' → ∀ σC c ce, nC.J σC c → CallToI p c ce fr →
      SegTC (NNZP SysW1 exe endPc (Zc fr)) p lbl (ms (fr :: fs))
        (At exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc nC.o.sp σC .sys))
        (At exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc nC.o.sp σC .n5)))
    (hZP : ∀ fr (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -72 → 16 ≤ R'.hi → FStable R' F' →
      (∀ m, F' m → F m) → CallFC R nC F' → ∀ σC c ce, nC.J σC c → CallToI p c ce fr →
      ∀ i, NodeZA (Zc fr) exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc nC.o.sp σC i) (FA.blkN i))
    (hZA : ∀ fr (RA : Region) (FA : MachineData → Prop), RA.OK → RA.lo ≤ -24 → 16 ≤ RA.hi → FStable RA FA →
      (∀ m, FA m → F m) → CallFC R nC FA → ∀ σC c ce, nC.J σC c → CallToI p c ce fr →
      ∀ k c', Qc σC k c' → AbortObl (Zc fr) exe endPc RA FA c')
    (habt : ∀ fr s, s.exe = exe → s.st.2 = (_root_.Executable.labels exe).label Abort.write.exit →
      (ms (fr :: fs)).abortAt s)
    (hret : ∀ σC c ce fr σR c', nC.J σC c → CallToI p c ce fr →
      σR.regs.get64 .rbp = σC.regs.rbp.toBitVec → σR.regs.fsBase = σC.regs.fsBase →
      Pc σC (σC.regs.get64 .rsi).toNat c' →
      (∀ k, R.Off k → ¬ (R.callee (nC.o.sp - 8) (-72) 16).Off (k - (nC.o.sp - 8)) → σR.slot k = σC.slot k) →
      ∃ c'', FrameRun p (c', fr :: fs) (c'', fs) ∧
        Lands N' E' ⟨Int64.ofBitVec (σC.slot nC.o.sp), ⟨nC.o.sp + 8, []⟩, σR⟩ c'') :
    SegTCSX S X p lbl ms ((At exe endPc R F nC).at fs) ((Next exe endPc R F N' E').at fs) := by
  refine call_ndTCSX (e0 := 8) (lo' := -72) (hi' := 16) (Ne := cNe (_root_.Executable.labels exe).label Pc Qc nC)
    (Ex := fun σC (_ : Unit) => cE (_root_.Executable.labels exe).label Pc Qc nC.o.sp σC .ret)
    hR hF hlo (by decide) (by omega) hhi hk8 (by decide) (by decide) hWC hXC
    (fun R' F' hR' hlo' hhi' hF' hFF hReq _ σC fr hreal hfact => ?_) (fun _ => rfl) ?_ ?_
  · obtain ⟨σ', c, ce, hJ, hCT, -, he, -⟩ := hreal
    obtain rfl : σ' = σC := enter_inj he
    subst hReq
    have hFC : CallFC R nC F' := fun m hm => by
      obtain ⟨mC, σ0, c0, -, hA, hJ0, -, -, hk⟩ := hfact m hm
      exact ⟨mC, σ0, c0, hA, hJ0, hk⟩
    refine ((seg_printCalleeSX hp hend hprog hR' hlo' hhi' hF' hcode hentry (hK fr) (hlen σ' c hJ) (hS fr)
      (hZX fr) (hXR fr _ F' hR' hlo' hhi' hF' hFF hFC σ' c ce hJ hCT) (hZu fr)
      (hsvc fr _ F' hR' (by omega) hhi' hF' hFF hFC σ' c ce hJ hCT)
      (hZP fr _ F' hR' hlo' hhi' hF' hFF hFC σ' c ce hJ hCT)
      (fun RA FA hRA hloA hhiA hFA hFAF k c' hk => hZA fr RA FA hRA hloA hhiA hFA
        (fun m h => hFF _ (hFAF m h)) (fun m h => hFC m (hFAF m h)) σ' c ce hJ hCT k c' hk)
      (habt fr)).mono_pre ?_).mono_post ?_
    · rintro s c' fs' ⟨⟨a, b, d, e, σ, hA, hD, hJ', -, -⟩, rfl⟩
      exact ⟨⟨a, b, d, e, σ, hA, hD, hJ'⟩, rfl⟩
    · rintro s c' fs' ⟨h, rfl⟩
      exact ⟨⟨(), h⟩, rfl⟩
  · intro σC c hJ
    obtain ⟨ce, fr, hCT⟩ := hcall σC c hJ
    exact ⟨σC, ce, fr, hCT, by rw [hpc]; rfl,
      ⟨⟨hP0 σC c ce fr hJ hCT, rfl, by simp [enter], rfl, by simp [enter]⟩, rfl⟩, rfl, c, hJ⟩
  · rintro g ⟨⟩ σC c ce fr σx c' σR hJ hCT ⟨-, he, -⟩ hx hreg - - hsl
    obtain rfl : σC = g := enter_inj he
    obtain ⟨⟨hbp, hP⟩, htp⟩ := hx
    obtain ⟨c'', hr, h⟩ := hret σC c ce fr σR c' hJ hCT (by rw [hreg]; exact hbp) (by rw [hreg]; exact htp) hP hsl
    have e : nC.o.sp - 8 + 16 = nC.o.sp + 8 := by omega
    refine ⟨c'', hr, ?_⟩
    simp only [cE, PrintA.E, ND.withTp]
    rw [e]
    exact h

end CallTCSX

end Spike.Lib.X64.Flow.Worker.PrintF

/-- info: 'Spike.Lib.X64.Flow.Worker.PrintF.seg_printCalleeSX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.PrintF.seg_printCalleeSX

/-- info: 'Spike.Lib.X64.Flow.Worker.PrintF.printF_callTCSX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.PrintF.printF_callTCSX
