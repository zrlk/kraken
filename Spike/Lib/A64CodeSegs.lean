/-
**Segments of an emitted AArch64 program from checks on its directives**:
the stack-checked prologue, the `exit_group` tail and `scc_rt_start` up to
its first call, for any valid layout of a program that passes a check
decided once per program (`blockAt`, `labelGap`: `Scc/Cert/Rt/LayoutA64.lean`).

- `prologueIn prog fn sc entry Z lim L ps`: the function's label `fn` right
  before its stack check `sc`, the prologue's four blocks after `sc`
  (`Spike/Lib/A64Prologue.lean`) and the body's first label `entry` after
  them; `prologue_seg_of` is `prologue_seg` from the function's label to a
  node at `entry`.
- `exitIn prog l k`: `exitTail k` and the system call right after `l`;
  `exitTail_seg_of` is `exitTail_seg` from a node at `l`.
- `startIn prog`: `scc_rt_start`'s frame setup (`Abort.b0`), the fall-through
  into `.L0_scc_rt_start.0_entry`, the handler's address (`adrp`, `add
  :lo12:`, through `si_nd`), the arguments (`startArgs`) and the
  `rt_sigaction(SIGPIPE, act, NULL, 8)` system call (`svc_nd`, which returns
  0: `svcCall_rtSigaction`); `start_seg_of` is a segment from the entry to
  a node at the first call (`bl scc_rt_alloc_tcb`), whose obligation holds
  of `startS`, the state there.
-/
import Spike.Lib.A64Prologue
import Spike.Lib.A64Abort
import Scc.Cert.Rt.LayoutA64

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap codeAt_blockAt label_labelGap)

set_option linter.unusedSimpArgs false

/-! ## Code from the checks -/

section Code

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {endPc : Int64}

/-- A block's code at a given address, from `blockAt`. -/
theorem code_of (hp : Lays exe prog) (hend : endPc = endOf exe prog) {l : Label} {k : Nat} {b : List Directive}
    (h : blockAt prog l k b = true) {q : Int64}
    (e : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = q) :
    ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s q b :=
  fun _ hs hn => e ▸ codeAt_blockAt hp hs (hn.trans hend) h

/-- `k + 1` instructions on: one more after `k`. -/
theorem ofNat4_succ (a : Int64) (k : Nat) : a + Int64.ofNat (4 * (k + 1)) = a + Int64.ofNat (4 * k) + 4 := by
  rw [Int64.add_assoc, show 4 * (k + 1) = 4 * k + 4 by omega, Int64.ofNat_add]; rfl

/-- No instruction on. -/
theorem ofNat4_zero (a : Int64) : a + Int64.ofNat (4 * 0) = a := by
  rw [show Int64.ofNat (4 * 0) = 0 by decide, Int64.add_zero]

/-- `k + n` instructions on: `n` more after `k`. -/
theorem ofNat4_add (a : Int64) (k n : Nat) :
    a + Int64.ofNat (4 * (k + n)) = a + Int64.ofNat (4 * k) + Int64.ofNat (4 * n) := by
  rw [Int64.add_assoc, show 4 * (k + n) = 4 * k + 4 * n by omega, Int64.ofNat_add]

end Code

/-! ## The prologue -/

/-- **A function's prologue in `prog`**: the function's label `fn` right
before its stack check `sc`, the four blocks after `sc`, and the body's
first label `entry` after them. -/
def prologueIn (prog : List Directive) (fn sc entry : Label) (Z lim : Int64) (L : Label)
    (ps : List (XReg × Int64)) : Bool :=
  labelGap prog fn sc 0 && blockAt prog sc 0 (chkHead Z) && blockAt prog sc 2 [ldrDir .X10 .X10 lim] &&
  blockAt prog sc 3 (chkBr L) && blockAt prog sc 5 (frameSet Z ps) && labelGap prog sc entry (9 + ps.length)

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **The prologue is one segment** in any valid layout of a program with
`prologueIn`: `prologue_seg` from the function's label. Its states lie in
`W`, none moved by `K` (`hW`, `ProW` at the function's label). -/
theorem prologue_seg_ofW {W : Frag isaLSE2} {K : State → State → Prop} (hp : Lays exe prog)
    (hend : endPc = endOf exe prog) {fn sc entry : Label}
    {Z lim : Int64} {L : Label} {ps : List (XReg × Int64)} (hin : prologueIn prog fn sc entry Z lim L ps = true)
    {J : AS → Ctl → Prop} {nb : ND} (h16 : Z.toInt % 16 = 0) (hZ : 16 ≤ Z.toInt) (hF : FStable R F)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -Z.toInt) (hhi : 0 ≤ R.hi)
    (hps : ∀ q ∈ ps, Spike.Lib.offOk (-Z.toInt) 0 (-Z.toInt + q.2.toInt) = true)
    (hpc : nb.pc = (_root_.Executable.labels exe).label entry)
    (ho : SO.le nb.o (oFr Z) = true)
    (hW : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label fn) Z lim L ps J)
    (hedge : ∀ σ c, J σ c →
      ms.rt (tcbA σ.regs lim).toNat ∧ ms.mp ⟨tcbA σ.regs lim, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs lim) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs lim, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - Z.toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = frRegs Z (ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs Z σ.regs }).regs →
          σ'.slot = stSlots (-Z.toInt) σ'.regs ps (frSlot σ) → nb.J σ' c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label fn, ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) := by
  simp only [prologueIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨g0, b0, b1, b2, b3, g1⟩ := hin
  have e0 := label_labelGap hp g0
  have e1 := label_labelGap hp g1
  rw [ofNat4_zero] at e0
  refine prologue_segW h16 hZ hF hR hal hlo hhi hps (code_of hp hend b0 ?_) (code_of hp hend b1 ?_)
    (code_of hp hend b2 ?_) (code_of hp hend b3 ?_) ?_ ho ?_ hedge
  · rw [e0, ofNat4_zero]
  · rw [e0]; simp only [ofNat4_succ, ofNat4_zero]
  · rw [e0]; simp only [ofNat4_succ, ofNat4_zero]
  · rw [e0]; simp only [ofNat4_succ, ofNat4_zero]
  · rw [hpc, e1, e0, ofNat4_add]; simp only [ofNat4_succ, ofNat4_zero]
  · exact hW

/-- **The prologue is one segment** in any valid layout of a program with
`prologueIn`: `prologue_seg` from the function's label. -/
theorem prologue_seg_of (hp : Lays exe prog) (hend : endPc = endOf exe prog) {fn sc entry : Label}
    {Z lim : Int64} {L : Label} {ps : List (XReg × Int64)} (hin : prologueIn prog fn sc entry Z lim L ps = true)
    {J : AS → Ctl → Prop} {nb : ND} (h16 : Z.toInt % 16 = 0) (hZ : 16 ≤ Z.toInt) (hF : FStable R F)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -Z.toInt) (hhi : 0 ≤ R.hi)
    (hps : ∀ q ∈ ps, Spike.Lib.offOk (-Z.toInt) 0 (-Z.toInt + q.2.toInt) = true)
    (hpc : nb.pc = (_root_.Executable.labels exe).label entry)
    (ho : SO.le nb.o (oFr Z) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (tcbA σ.regs lim).toNat ∧ ms.mp ⟨tcbA σ.regs lim, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs lim) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs lim, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - Z.toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = frRegs Z (ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs Z σ.regs }).regs →
          σ'.slot = stSlots (-Z.toInt) σ'.regs ps (frSlot σ) → nb.J σ' c) :
    Seg p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label fn, ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  (prologue_seg_ofW hp hend hin h16 hZ hF hR hal hlo hhi hps hpc ho ProW.triv hedge).toSeg

end Fn

/-! ## The `exit_group` tail -/

/-- **The `exit_group` tail at label `l` in `prog`**: `exitTail k` right
after `l`, the system call after it. -/
def exitIn (prog : List Directive) (l : Label) (k : Int64) : Bool :=
  blockAt prog l 0 (exitTail k) && blockAt prog l 3 [svcDir]

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **The `exit_group` tail does not return** in any valid layout of a
program with `exitIn`: `exitTail_seg` from a node at its label. Its states
lie in `W`, none moved by `K` (`hW`, `ExitW`). At the `svc`, `hok` is given `x0` unchanged from the entry. -/
theorem exitTail_seg_ofW {W : Frag isaLSE2} {K : State → State → Prop} (hp : Lays exe prog)
    (hend : endPc = endOf exe prog) {l : Label} {k : Int64}
    (hin : exitIn prog l k = true) {n : ND} {Q : Frag isaLSE2} (hpc : n.pc = (_root_.Executable.labels exe).label l)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) {lo hi : Int}
    (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hk : Spike.Lib.offOk lo hi (n.o.sp + k.toInt) = true)
    (h16 : n.o.sp % 16 = 0) (hW : ExitW W K exe endPc R F n k)
    (hok : ∀ s c σ0, n.J σ0 c →
      At exe endPc R F ⟨n.pc + 4 + 4 + 4, ⟨n.o.sp, []⟩, fun σ _ => σ.regs.X0 = σ0.regs.X0⟩ s c →
      SysOk p ms s c (.exitGroup σ0.regs.X0.toNat)) : SegW W K p lbl ms (At exe endPc R F n) Q := by
  simp only [exitIn, Bool.and_eq_true] at hin
  refine exitTail_segW hK hF hR hal hlo hhi hk h16 (code_of hp hend hin.1 ?_) (code_of hp hend hin.2 ?_) hW hok
  · rw [hpc, ofNat4_zero]
  · rw [hpc]; simp only [ofNat4_succ, ofNat4_zero]

/-- **The `exit_group` tail does not return** in any valid layout of a
program with `exitIn`: `exitTail_seg` from a node at its label. -/
theorem exitTail_seg_of (hp : Lays exe prog) (hend : endPc = endOf exe prog) {l : Label} {k : Int64}
    (hin : exitIn prog l k = true) {n : ND} {Q : Frag isaLSE2} (hpc : n.pc = (_root_.Executable.labels exe).label l)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) {lo hi : Int}
    (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hk : Spike.Lib.offOk lo hi (n.o.sp + k.toInt) = true)
    (h16 : n.o.sp % 16 = 0)
    (hok : ∀ s c σ0, n.J σ0 c →
      At exe endPc R F ⟨n.pc + 4 + 4 + 4, ⟨n.o.sp, []⟩, fun σ _ => σ.regs.X0 = σ0.regs.X0⟩ s c →
      SysOk p ms s c (.exitGroup σ0.regs.X0.toNat)) : Seg p lbl ms (At exe endPc R F n) Q :=
  (exitTail_seg_ofW hp hend hin hpc hK hF hR hal hlo hhi hk h16 ExitW.triv hok).toSeg

end Fn

/-! ## `scc_rt_start` up to its first call -/

/-- **`rt_sigaction(SIGPIPE, act, NULL, 8)` decodes.** -/
theorem svcCall_rtSigaction {r : Reg64s} (h8 : r.X8.toNat = 134) (h0 : r.X0.toNat = 13) (h2 : r.X2.toNat = 0)
    (h3 : r.X3.toNat = 8) : svcCall r = some .rtSigaction := by
  simp [svcCall, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.a64, h8, h0, h2, h3, Scc.Sem.A64.xRegs,
    Scc.Sem.Kernel.sigpipe, Scc.Sem.Kernel.sigsetSize]
  exact h3

/-- The `rt_sigaction` call's arguments: the handler's address (in `x9`)
spilled and reloaded into `x1`. -/
def startArgs : List Directive := parseAArch64("str x9, [sp]
movz x0, #13
ldr x1, [sp]
movz x2, #0
movz x3, #8
movz x8, #134")

block_spec startArgs (-48) 0 Abort.oI startArgs

/-- `scc_rt_start`'s entry label. -/
abbrev startE : Label := ".L0_scc_rt_start.0_entry"

/-- The handler's label. -/
abbrev sigign : Label := "scc_rt_sigign"

/-- **`scc_rt_start` up to its first call in `prog`**: the frame's setup,
the label's fall-through into `.0_entry`, the handler's address, the
arguments and the system call. -/
def startIn (prog : List Directive) : Bool :=
  labelGap prog "scc_rt_start" startE 4 && blockAt prog "scc_rt_start" 0 Abort.b0 &&
  blockAt prog startE 0 [(SI.adrp .X9 sigign).toDir] && blockAt prog startE 1 [(SI.addLo12 .X9 .X9 sigign).toDir] &&
  blockAt prog startE 2 startArgs && blockAt prog startE 8 [svcDir]

/-- The state after the frame's setup. -/
def startS0 (lab : Label → Int64) (σ : AS) : AS := (arun lab Abort.b0 ⟨lab "scc_rt_start", Abort.oE, σ⟩).σ

/-- The state after the handler's address. -/
def startS1 (lab : Label → Int64) (σ : AS) : AS :=
  (SI.addLo12 .X9 .X9 sigign).step lab ((SI.adrp .X9 sigign).step lab (startS0 lab σ))

/-- The state at the system call. -/
def startS2 (lab : Label → Int64) (σ : AS) : AS := (arun lab startArgs ⟨lab startE + 4 + 4, Abort.oI, startS1 lab σ⟩).σ

/-- **The state at the first call**: `rt_sigaction` returned 0. -/
def startS (lab : Label → Int64) (σ : AS) : AS := svcStep 0 (startS2 lab σ)

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- `scc_rt_start`'s node at `.0_entry`, after the frame's setup. -/
def startN1 (lab : Label → Int64) (J : AS → Ctl → Prop) : ND :=
  ⟨lab startE, Abort.oI, fun σ1 c => ∃ σ, J σ c ∧ σ1 = startS0 lab σ⟩

/-- `scc_rt_start`'s node after the `adrp`. -/
def startN2 (lab : Label → Int64) (J : AS → Ctl → Prop) : ND :=
  ⟨lab startE + 4, Abort.oI, fun σ2 c => ∃ σ, J σ c ∧ σ2 = (SI.adrp .X9 sigign).step lab (startS0 lab σ)⟩

/-- `scc_rt_start`'s node at the arguments, after the handler's address. -/
def startN3 (lab : Label → Int64) (J : AS → Ctl → Prop) : ND :=
  ⟨lab startE + 4 + 4, Abort.oI, fun σ3 c => ∃ σ, J σ c ∧ σ3 = startS1 lab σ⟩

/-- `scc_rt_start`'s node at the system call. -/
def startN4 (lab : Label → Int64) (J : AS → Ctl → Prop) : ND :=
  ⟨lab startE + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, Abort.oI, fun σ4 c => ∃ σ, J σ c ∧ σ4 = startS2 lab σ⟩

/-- **`scc_rt_start`'s states up to its first call inside `W`**, none moved
by `K`: one obligation per node (the frame's setup, the `adrp`, the `add`,
the arguments, the system call). -/
structure StartW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Spike.Lib.Region) (F : MachineData → Prop) (J : AS → Ctl → Prop) : Prop where
  w0 : BlkW W K exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_start", Abort.oE, J⟩ Abort.b0
  w1 : NodeW W K exe endPc R F (startN1 (_root_.Executable.labels exe).label J)
  w2 : NodeW W K exe endPc R F (startN2 (_root_.Executable.labels exe).label J)
  w3 : BlkW W K exe endPc R F (startN3 (_root_.Executable.labels exe).label J) startArgs
  w4 : NodeW W K exe endPc R F (startN4 (_root_.Executable.labels exe).label J)

/-- The entry is inside the trivial predicate, with no outside moves. -/
theorem StartW.triv {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {J : AS → Ctl → Prop} : StartW (fun _ _ => True) (fun _ _ => False) exe endPc R F J :=
  ⟨BlkW.triv, NodeW.triv, NodeW.triv, BlkW.triv, NodeW.triv⟩

/-- **`scc_rt_start` up to its first call is one segment** in any valid
layout of a program with `startIn`: from the entry (`sp` at offset 0) to a
node at the call whose obligation holds of `startS`. Its states lie in `W`,
none moved by `K` (`hW`, `StartW`). -/
theorem start_seg_ofW {W : Frag isaLSE2} {K : State → State → Prop} (hp : Lays exe prog)
    (hend : endPc = endOf exe prog) (hin : startIn prog = true)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} {nC : ND}
    (hpc : nC.pc = (_root_.Executable.labels exe).label startE + Int64.ofNat (4 * 9))
    (ho : SO.le nC.o Abort.oI = true) (hW : StartW W K exe endPc R F J)
    (hedge : ∀ σ c, J σ c → nC.J (startS (_root_.Executable.labels exe).label σ) c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_start", Abort.oE, J⟩)
      (At exe endPc R F nC) := by
  simp only [startIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨g0, c0, c1, c2, c3, c4⟩ := hin
  have e0 := label_labelGap hp g0
  simp only [ofNat4_succ, ofNat4_zero] at e0
  let lab := (_root_.Executable.labels exe).label
  let n1 : ND := ⟨lab startE, Abort.oI, fun σ1 c => ∃ σ, J σ c ∧ σ1 = startS0 lab σ⟩
  let n2 : ND := ⟨lab startE + 4, Abort.oI, fun σ2 c => ∃ σ, J σ c ∧
    σ2 = (SI.adrp .X9 sigign).step lab (startS0 lab σ)⟩
  let n3 : ND := ⟨lab startE + 4 + 4, Abort.oI, fun σ3 c => ∃ σ, J σ c ∧ σ3 = startS1 lab σ⟩
  let n4 : ND := ⟨lab startE + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, Abort.oI, fun σ4 c => ∃ σ, J σ c ∧
    σ4 = startS2 lab σ⟩
  have one : ∀ {P : Frag isaLSE2} {n : ND},
      SegW W K p lbl ms P (Next exe endPc R F (fun _ : Unit => n) (fun e : Empty => e.elim)) →
      SegW W K p lbl ms P (At exe endPc R F n) := fun h =>
    h.mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
  refine SegW.seq (Q := At exe endPc R F n1) ?_ (SegW.seq (Q := At exe endPc R F n2) ?_
    (SegW.seq (Q := At exe endPc R F n3) ?_ (SegW.seq (Q := At exe endPc R F n4) ?_ ?_)))
  · refine one (seg_ndW (by simp [Abort.b0]) Abort.b0_ok hF hR hal hlo hhi (code_of hp hend c0 (ofNat4_zero _))
      hW.w0 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, σ, hJ, rfl⟩⟩)
    · rw [Abort.b0_run]; exact e0
    · rw [Abort.b0_run]; rfl
  · refine one (si_ndW (si := .adrp .X9 sigign) hF (code_of hp hend c1 (ofNat4_zero _)) hW.w1
      fun σ c ⟨σ0, hJ, hσ⟩ => ⟨c, .refl c, .inl ⟨(), rfl, rfl, σ0, hJ, by rw [hσ]⟩⟩)
  · refine one (si_ndW (si := .addLo12 .X9 .X9 sigign) hF
      (code_of hp hend c2 (by simp only [ofNat4_succ, ofNat4_zero]; rfl)) hW.w2
      fun σ c ⟨σ0, hJ, hσ⟩ => ⟨c, .refl c, .inl ⟨(), rfl, rfl, σ0, hJ, by rw [hσ]; rfl⟩⟩)
  · refine one (seg_ndW (by simp [startArgs]) startArgs_ok hF hR hal hlo hhi
      (code_of hp hend c3 (by simp only [ofNat4_succ, ofNat4_zero]; rfl)) hW.w3
      fun σ c ⟨σ0, hJ, hσ⟩ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, σ0, hJ, by rw [hσ]; rfl⟩⟩)
    · rw [startArgs_run]
    · rw [startArgs_run]; rfl
  · refine (svc_ndW (n := n4) (N := fun _ : Unit => nC) (E := fun e : Empty => e.elim) hK hF
      (code_of hp hend c4 (by simp only [ofNat4_succ, ofNat4_zero]; rfl)) hW.w4
      (fun σ c ⟨σ0, hJ, hσ⟩ => ⟨.rtSigaction, ?_, fun v hv => ?_⟩) ?hok).mono_post
      fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
    case hok =>
      rintro s c σ call - ⟨σ0, -, rfl⟩ hcall
      have h : svcCall (startS2 lab σ0).regs = some .rtSigaction := by
        apply svcCall_rtSigaction <;> simp [startS2, startArgs_run] <;> rfl
      rw [h] at hcall
      cases hcall
      exact ⟨nofun, nofun, nofun, nofun⟩
    · subst hσ
      apply svcCall_rtSigaction <;> simp [startS2, startArgs_run] <;> rfl
    · simp only [Scc.Sem.Kernel.results, List.mem_singleton] at hv
      subst hv hσ
      refine ⟨c, .refl c, .inl ⟨(), ?_, ?_, hedge σ0 c hJ⟩⟩
      · rw [hpc]; simp only [ofNat4_succ, ofNat4_zero]; rfl
      · exact ho

/-- **`scc_rt_start` up to its first call is one segment** in any valid
layout of a program with `startIn`: from the entry (`sp` at offset 0) to a
node at the call whose obligation holds of `startS`. -/
theorem start_seg_of (hp : Lays exe prog) (hend : endPc = endOf exe prog) (hin : startIn prog = true)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} {nC : ND}
    (hpc : nC.pc = (_root_.Executable.labels exe).label startE + Int64.ofNat (4 * 9))
    (ho : SO.le nC.o Abort.oI = true)
    (hedge : ∀ σ c, J σ c → nC.J (startS (_root_.Executable.labels exe).label σ) c) :
    Seg p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_start", Abort.oE, J⟩)
      (At exe endPc R F nC) :=
  (start_seg_ofW hp hend hin hK hF hR hal hlo hhi hpc ho StartW.triv hedge).toSeg

end Fn

end Spike.Lib.A64.Flow
