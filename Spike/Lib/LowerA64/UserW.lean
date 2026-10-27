/-
**The user `main`'s own states inside the consumer's facts** (AArch64): the
prologue's obligation `ProW` of `fn0_seg` (`Spike/Lib/LowerA64/Fn.lean`)
inside `BodyW0` (`Spike/Lib/LowerA64/BodyW.lean`), for any program with an
instance's facts (`InstOk`, `Spike/Lib/Rt/A64RtW.lean`).

- `BlkW.mapC`, `NodeW.mapC`, `ProW.mapC`: a node's obligations at another
  invariant whose controls carry the predicate over (each control of the
  new invariant has one of the old with the same state, `W` there giving
  `W'` here). With `W` the consumer's facts at the control and the old
  invariant's controls the entry `c0`, it moves an obligation proven at
  `c0` (`blkW_postO`) into `BodyW0` (`proW_body0`).
- `ProPh`: the prologue's phase facts (its blocks' `blkPh` at their pcs, no
  dead target, no `ret`; the limit's load off the sites and in its next
  pc's phase), as `MainPh`'s prologue part (`Spike/Lib/Rt/A64RtMainU.lean`).
- `proW_sfactsP`: a stack-checked prologue with saved registers `ps` at
  cells of the frame (`prologueIn`, the limit at offset 8 of the TCB)
  inside the consumer's facts, every control of its invariant `c0`;
  `proW_sfacts`: without saved registers (as `mainUW_gen`'s `pro`).
- `proW_body0`: `fn0_seg`'s `hWp` inside `BodyW0`, the invariant's
  controls reached from `c0` by local runs, the thread pointer `tp`.
-/
import Spike.Lib.LowerA64.BodyW
import Spike.Lib.Rt.A64RtMainU

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (Lays endOf blockAt label_labelGap)
open Scc.Sem (Marks Range)
open Spike.Lib.A64Consumer (CFacts SFacts blkPh noRetBlk noRet_false Own Lbl)
open Spike.Lib.A64.Rt (InstOk blkW_postO nodeW_ldr_postO)
open Spike.Lib.A64.Flow.Ret0 (StackOff limA tcbA_limA)
open Spike.Lib.A64.Rt.MainU (chkHead_noRet chkBr_noRet pc2 pc3 pc5)

/-! ## Obligations at another invariant -/

section Map

variable {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {W W' : Frag isaLSE2}

/-- **A block's obligation at another invariant**: same pc and offsets,
each control of `n`'s invariant with one of `n'`'s at the same state, `W`
there giving `W'` here. -/
theorem BlkW.mapC {n n' : ND} {blk : List Directive} (hpc : n'.pc = n.pc) (ho : n'.o = n.o)
    (h : BlkW W K exe endPc R F n' blk) (hJ : ∀ σ c, n.J σ c → ∃ c', n'.J σ c' ∧ ∀ s, W s c' → W' s c) :
    BlkW W' K exe endPc R F n blk := by
  obtain ⟨pc, o, J⟩ := n
  obtain ⟨pc', o', J'⟩ := n'
  simp only at hpc ho
  subst hpc ho
  intro s σ c he hn hd hp hA hF hJn k hk m hA' hD
  obtain ⟨c', hJ', hW⟩ := hJ σ c hJn
  obtain ⟨h1, h2⟩ := h s σ c' he hn hd hp hA hF hJ' k hk m hA' hD
  exact ⟨hW _ h1, h2⟩

/-- **A node's obligation at another invariant** (as `BlkW.mapC`). -/
theorem NodeW.mapC {n n' : ND} (hpc : n'.pc = n.pc) (ho : n'.o = n.o) (h : NodeW W K exe endPc R F n')
    (hJ : ∀ σ c, n.J σ c → ∃ c', n'.J σ c' ∧ ∀ s, W s c' → W' s c) : NodeW W' K exe endPc R F n := by
  obtain ⟨pc, o, J⟩ := n
  obtain ⟨pc', o', J'⟩ := n'
  simp only at hpc ho
  subst hpc ho
  rintro s c ⟨h1, h2, h3, h4, σ, hA, hF, hJn⟩
  obtain ⟨c', hJ', hW⟩ := hJ σ c hJn
  obtain ⟨hw, hk⟩ := h s c' ⟨h1, h2, h3, h4, σ, hA, hF, hJ'⟩
  exact ⟨hW _ hw, hk⟩

/-- **A prologue's obligations at another invariant** (`BlkW.mapC`,
`NodeW.mapC` at each of its nodes). -/
theorem ProW.mapC {ms : MemSide isaLSE2} {pc0 Z lim : Int64} {L : Label} {ps : List (XReg × Int64)}
    {J J' : AS → Ctl → Prop} (h : ProW W K exe endPc R F ms pc0 Z lim L ps J')
    (hJ : ∀ σ c, J σ c → ∃ c', J' σ c' ∧ ∀ s, W s c' → W' s c) : ProW W' K exe endPc R F ms pc0 Z lim L ps J := by
  refine ⟨BlkW.mapC (n' := ⟨pc0, ⟨0, []⟩, J'⟩) rfl rfl h.w0 hJ, NodeW.mapC (n' := proN1 pc0 Z J') rfl rfl h.w1 ?_,
    BlkW.mapC (n' := proN2 ms pc0 Z lim J') rfl rfl h.w2 ?_, BlkW.mapC (n' := proN3 ms pc0 Z lim J') rfl rfl h.w3 ?_⟩
  · rintro σ1 c ⟨σ, hJσ, he⟩
    obtain ⟨c', h', hw⟩ := hJ σ c hJσ
    exact ⟨c', ⟨σ, h', he⟩, hw⟩
  · rintro σ2 c ⟨σ, v, hJσ, hg, he⟩
    obtain ⟨c', h', hw⟩ := hJ σ c hJσ
    exact ⟨c', ⟨σ, v, h', hg, he⟩, hw⟩
  · rintro σ3 c ⟨σ, v, hJσ, hg, he, hs⟩
    obtain ⟨c', h', hw⟩ := hJ σ c hJσ
    exact ⟨c', ⟨σ, v, h', hg, he, hs⟩, hw⟩

end Map

/-! ## The prologue -/

/-- **A stack-checked prologue's phase facts** at labels `lab`, phase index
`ph`, off-site pcs `okPc`: the blocks after its check label `sc` (the head,
the branch, the frame's set-up with saved registers `ps`) at their pcs, no
dead target, no `ret`; the limit's load off the sites and in its next pc's
phase. -/
structure ProPh (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (sc : Label) (Z : Int64)
    (L : Label) (ps : List (XReg × Int64)) : Prop where
  hd : blkPh okPc ph (fun _ => false) lab (lab sc + Int64.ofNat (4 * 0)) 0 (chkHead Z) = true
  ld : okPc (lab sc + Int64.ofNat (4 * 2)).toBitVec.toNat = true ∧
    ph (lab sc + Int64.ofNat (4 * 2) + Int64.ofNat 4).toBitVec.toNat = ph (lab sc + Int64.ofNat (4 * 2)).toBitVec.toNat
  br : blkPh okPc ph (fun _ => false) lab (lab sc + Int64.ofNat (4 * 3)) 0 (chkBr L) = true
  fr : blkPh okPc ph (fun _ => false) lab (lab sc + Int64.ofNat (4 * 5)) 0 (frameSet Z ps) = true

theorem frameSet_nil_noRet (Z : Int64) : noRetBlk (frameSet Z []) = true := by
  simp [noRetBlk, frameSet, frSetup, spStr, A64.Flow.classify, A64.Flow.RegOnly]

/-- The frame's set-up with saved registers `ps` has no `ret`. -/
theorem frameSet_noRet (Z : Int64) (ps : List (XReg × Int64)) : noRetBlk (frameSet Z ps) = true := by
  simp [noRetBlk, frameSet, frSetup, spStr, A64.Flow.classify, A64.Flow.RegOnly]

private theorem hnr' {lab : Label → Int64} {blk : List Directive} (hb : noRetBlk blk = true) {n : ND}
    {ra' : Int64} : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, A64.Flow.classify blk[k] = some (A64.Flow.AI.ret r) →
      Int64.ofInt ((A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra' :=
  fun _ _ _ k hk r hr => (noRet_false hb k hk r hr).elim

section Pro

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}

/-- **A stack-checked prologue is inside the consumer's facts** (for any
frame `Z`): its code (`hin`) with its saved registers `ps` at cells of the
frame (`hps`), its phase facts (`hph`), every control of its invariant `c0` with
its facts (`hJc`, `hC0`), the thread pointer `tp` (`htp`) whose limit word
is mapped (`hmr`) and unmapped in private memory under the frame condition
(`hun`), in any 16-aligned region holding the frame with 8-aligned bounds. -/
theorem proW_sfactsP {ms : MemSide isaLSE2} {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {fn sc entry : Label} {Z : Int64} {L : Label} {ps : List (XReg × Int64)}
    (hin : prologueIn prog fn sc entry Z 8 L ps = true)
    (hps : ∀ q ∈ ps, offOk (-Z.toInt) 0 (-Z.toInt + q.2.toInt) = true)
    {J : AS → Ctl → Prop} {c0 : Ctl} (hC0 : CFacts Λ lbl c0) (hJc : ∀ σ c, J σ c → c = c0) {tp : UInt64}
    (htp : ∀ σ c, J σ c → σ.regs.TPIDR_EL0 = tp) (hph : ProPh okPc ph lab sc Z L ps)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -Z.toInt) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (h16 : Z.toInt % 16 = 0) (hZ : 16 ≤ Z.toInt)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    ProW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F ms ((_root_.Executable.labels exe).label fn)
      Z 8 L ps J := by
  have h := hin
  simp only [prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hgap, bHd⟩, bLd⟩, bBr⟩, bFr⟩, -⟩ := h
  have esc := label_labelGap hI.lays hgap
  rw [hI.labOk] at esc
  have hR8 : R.base.toNat % 8 = 0 := by omega
  rw [hI.labOk]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact blkW_postO hI bHd (by rw [esc, ofNat4_zero, ofNat4_zero]) (chkHead_ok _ _ _) hR hal hlo hhi
      (fun _ _ hJ => hJc _ _ hJ ▸ hC0) hph.hd (hnr' (chkHead_noRet _)) (fun _ _ _ => rfl) hl hh hsub hfit hFO
  · exact nodeW_ldr_postO hI bLd rfl (by show _ + 4 + 4 = _; rw [esc, ofNat4_zero, pc2])
      (fun _ _ ⟨_, hJ, _⟩ => hJc _ _ hJ ▸ hC0) hph.ld.1 hph.ld.2
      (fun _ _ ⟨_, hJ, he⟩ => by rw [he, rAddr_chkRegs]; exact tcbA_limA (htp _ _ hJ)) hmr hun hR hR8 hl hh hsub hFO
  · exact blkW_postO hI bBr (by rw [esc, ofNat4_zero, pc3]; rfl) (chkBr_ok _ _ _ _) hR hal hlo hhi
      (fun _ _ ⟨_, _, hJ, _⟩ => hJc _ _ hJ ▸ hC0) hph.br (hnr' (chkBr_noRet _)) (fun _ _ _ => rfl) hl hh hsub hfit hFO
  · exact blkW_postO hI bFr (by rw [esc, ofNat4_zero, pc5]; rfl)
      (frameSet_ok (lo := -Z.toInt) (hi := 0) h16 hZ (by omega) (Int.le_refl _) hps) hR hal hlo hhi
      (fun _ _ ⟨_, _, hJ, _⟩ => hJc _ _ hJ ▸ hC0) hph.fr (hnr' (frameSet_noRet _ _)) (fun _ _ _ => rfl) hl hh
      hsub hfit hFO

/-- **A stack-checked prologue without saved registers is inside the
consumer's facts** (`mainUW_gen`'s `pro`): `proW_sfactsP` at `ps := []`. -/
theorem proW_sfacts {ms : MemSide isaLSE2} {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {fn sc entry : Label} {Z : Int64} {L : Label} (hin : prologueIn prog fn sc entry Z 8 L [] = true)
    {J : AS → Ctl → Prop} {c0 : Ctl} (hC0 : CFacts Λ lbl c0) (hJc : ∀ σ c, J σ c → c = c0) {tp : UInt64}
    (htp : ∀ σ c, J σ c → σ.regs.TPIDR_EL0 = tp) (hph : ProPh okPc ph lab sc Z L [])
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -Z.toInt) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (h16 : Z.toInt % 16 = 0) (hZ : 16 ≤ Z.toInt)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    ProW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F ms ((_root_.Executable.labels exe).label fn)
      Z 8 L [] J :=
  proW_sfactsP hI hin (by simp) hC0 hJc htp hph hR hal hlo hhi hl hh h16 hZ hmr hun hsub hfit hFO

/-- **`fn0_seg`'s `hWp` inside `BodyW0`**: a user function's prologue
(`proInC`) with its phase facts (`hph`), every control of its invariant
reached from `c0` by a local run (`hJr`) and `Quiet` there (`hQ`), the
thread pointer `tp` (`htp`, `hmr`, `hun`). -/
theorem proW_body0 {ms : MemSide isaLSE2} {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {cx : FnCtx}
    (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0) {fn entry : Label}
    (hin : proInC prog cx fn entry = true) {J : AS → Ctl → Prop} {c0 : Ctl} {p : Prog}
    (hC0 : CFacts Λ lbl c0) (hJr : ∀ σ c, J σ c → LocalRun p c0 c) (hQ : ∀ c, LocalRun p c0 c → Quiet c)
    {tp : UInt64} (htp : ∀ σ c, J σ c → σ.regs.TPIDR_EL0 = tp)
    (hph : ProPh okPc ph lab (cx.local "stack_check") (Int64.ofInt cx.frame) (proL cx) [])
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    ProW (BodyW0 Λ μ own rS Tk lbl c0) K exe endPc R F ms ((_root_.Executable.labels exe).label fn)
      (Int64.ofInt cx.frame) (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL cx) [] J := by
  have hge := frame_ge16 hf
  have hF64 : (Int64.ofInt cx.frame).toInt = cx.frame := toInt_ofInt_small (by omega) (by omega)
  have H := proW_sfacts (J := fun σ c => c = c0 ∧ ∃ c1, J σ c1) (ms := ms) hI hin hC0 (fun _ _ h => h.1)
    (fun _ _ ⟨_, _, h⟩ => htp _ _ h) hph hR hal (by rw [hF64]; exact hlo) hhi hl hh (by rw [hF64]; omega)
    (by rw [hF64]; omega) hmr hun hsub hfit hFO
  exact ProW.mapC H fun σ c hJ => ⟨c0, ⟨rfl, c, hJ⟩, fun _ hs => ⟨hQ c (hJr σ c hJ), hs⟩⟩

end Pro

end Spike.Lib.LowerA64
