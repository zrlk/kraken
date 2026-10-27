/-
**`hello1.w`'s compiled bodies on x64**, inside `W`, in any valid layout of
`hello1Cells` (`Spike/Lib/X64Hello1Code.lean`), from checks decided once on
the cells (`decide +kernel`): the x64 twin of
`Spike/Lib/A64Hello1Body.lean`.

- `hello1_wc_body_segW`: `wc_main`'s body, from `.Lwc_main.entry` (`%rsp`
  at the frame's base, offset `-88`, `%rbp` at the saved `%rbp`, `-8`;
  offsets from `%rsp` at `wc_main`'s entry): the block computing `print`'s
  arguments and its call of `scc_rt_print` (`call_nd_FWK`, `print`'s region
  based at its saved `%rbp`, `-104`, reaching `-144`), and `.x15`'s
  `%rax = 0` and return. Exits: the return to the saved return address
  (`%rsp` at `8`), and `print`'s abort (to `scc_rt_abort` with `%rdi = 4`,
  `%rsp` at `-144`). The source stutters up to the return block, where it
  may take a local run (`hedge`). `imulq` leaves flags undefined, so it is
  a node of its own between the block's two halves (`flag_ndW`).
- `hello1_wc_segW`: all of `wc_main`, its prologue then the body, from its
  entry invariant (the body's is `wcJ`).

`print`'s write system call stays a given segment (`hsys`, of the shape
`seg_printW` asks): a write to the output is no row's (`SysOk`); it is
discharged by the output row once the source extern lands.
-/
import Spike.Lib.X64Hello1Segs
import Spike.Lib.X64Ret0
import Spike.Lib.X64Flags
import Spike.Lib.Rt.X64WcRa

namespace Spike.Lib.X64.Flow.Hello1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (CallerCells blkW_mono)
open Spike.Lib.X64.Rt (WcRa WcFp)
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-! ## `wc_main`'s body -/

/-- `wc_main`'s `.entry` block up to its multiply: `a.1`'s low half, its sum
with `a.0`, `a.2` and the factor `8`. -/
def wcE1 : List (Directive × Nat) := (parse("movq -16(%rbp), %rax
movl %eax, %eax
movq %rax, -48(%rbp)
movq -8(%rbp), %rax
movq -48(%rbp), %rcx
addq %rcx, %rax
movq %rax, -56(%rbp)
movq -24(%rbp), %rax
movq $8, %rcx")).zip [4, 2, 4, 4, 4, 3, 4, 4, 7]

/-- The multiply `imulq %rcx, %rax` (its flags undefined: a node of its own,
`flag_ndW`). -/
abbrev wcMul : FI := .imul_rr .rax .rcx

/-- `wc_main`'s `.entry` block after its multiply: the minimum, `print`'s
arguments, the call. -/
def wcE2 : List (Directive × Nat) := (parse("movq %rax, -64(%rbp)
movq -32(%rbp), %rdx
movq -64(%rbp), %rsi
movq -32(%rbp), %rax
movq -64(%rbp), %rcx
cmpq %rcx, %rax
movq %rsi, %rax
cmovb %rdx, %rax
movq %rax, -72(%rbp)
movq -56(%rbp), %rdi
movq -72(%rbp), %rsi
call scc_rt_print")).zip [4, 4, 4, 4, 4, 3, 3, 4, 4, 4, 4, 5]

/-- `wc_main`'s `.x15` block: `%rax = 0`, the epilogue, `ret`. -/
def wcR15 : List (Directive × Nat) := (parse("movq $0, %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [7, 3, 1, 1]

/-- The body's offsets: `%rsp` at the frame's base, `%rbp` at the saved
`%rbp`. -/
abbrev oB : SO := ⟨-88, [(.rbp, -8)]⟩

block_spec wcE1 (-144) 8 oB wcE1
block_spec wcE2 (-144) 8 oB wcE2
block_spec wcR15 (-144) 8 oB wcR15

/-- **`wc_main`'s body in `cells`**: the two blocks and the multiply between
them at `.entry`, `.x15`'s block, `.x15` right after the call. -/
def wcBodyIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells ".Lwc_main.entry" 0 wcE1 && blockAtB cells ".Lwc_main.entry" 36 [(wcMul.toDir, 4)] &&
    blockAtB cells ".Lwc_main.entry" 40 wcE2 && blockAtB cells ".Lwc_main.x15" 0 wcR15 &&
    labelGapB cells ".Lwc_main.entry" ".Lwc_main.x15" 87

theorem hello1_wcBodyIn : wcBodyIn SccCode.hello1Cells = true := by decide +kernel

/-- The state after `.entry`'s first block from `σ`. -/
def wcS1 (lab : Label → Int64) (σ : AS) : AS := (arun lab wcE1 ⟨lab ".Lwc_main.entry", oB, σ⟩).σ

/-- The abstract state at `print`'s entry, after the `.entry` block from
`σ` with the multiply's flags `fl` (irreducible: the block's closed form is
large). -/
@[irreducible] def wcC (lab : Label → Int64) (σ : AS) (fl : StatusFlags) : AS :=
  (arun lab wcE2 ⟨lab ".Lwc_main.entry" + 40, oB, wcMul.step (wcS1 lab σ) fl⟩).σ

theorem wcC_eq (lab : Label → Int64) (σ : AS) (fl : StatusFlags) :
    wcC lab σ fl = (arun lab wcE2 ⟨lab ".Lwc_main.entry" + 40, oB, wcMul.step (wcS1 lab σ) fl⟩).σ := by
  unfold wcC; rfl

/-- The frame's words at `print`'s entry, after the `.entry` block from `σ`
(the multiply's flags do not reach them, `wcC_slot`). -/
def wcSl (lab : Label → Int64) (σ : AS) : Int → BitVec 64 := (wcC lab σ σ.status).slot

theorem wcC_slot (lab : Label → Int64) (σ : AS) (fl : StatusFlags) : (wcC lab σ fl).slot = wcSl lab σ := by
  rw [wcSl, wcC_eq, wcC_eq, wcE2_run, wcE2_run]; rfl

/-- The block keeps the frame record and the return address. -/
theorem wcSl_rec (lab : Label → Int64) (σ : AS) : wcSl lab σ (-8) = σ.slot (-8) ∧ wcSl lab σ 0 = σ.slot 0 := by
  simp only [wcSl, wcC_eq, wcE2_run, FI.step, wcS1, wcE1_run]
  exact ⟨by simp [Spike.Lib.upd_apply], by simp [Spike.Lib.upd_apply]⟩

/-- The block keeps `%rbp`. -/
theorem wcC_rbp (lab : Label → Int64) (σ : AS) (fl : StatusFlags) :
    (wcC lab σ fl).regs.get64 .rbp = σ.regs.get64 .rbp := by
  rw [wcC_eq, wcE2_run]
  simp [FI.step, wcS1, wcE1_run, FI.regs, Reg64s.get64_set64_ne]

/-- The call pushes `.x15`, the next instruction, `87` bytes on. -/
theorem wcC_ra (lab : Label → Int64) (σ : AS) (fl : StatusFlags)
    (e : lab ".Lwc_main.x15" = lab ".Lwc_main.entry" + Int64.ofNat 87) :
    (wcC lab σ fl).slot (-96) = (lab ".Lwc_main.x15").toBitVec := by
  rw [wcC_eq, wcE2_run, e]
  simp only [Spike.Lib.upd_apply, ↓reduceIte, Int64.toBitVec_add, BitVec.add_assoc]
  rfl

/-- `print`'s ghost: the source control, the caller's `%rbp`, the return
address. -/
abbrev PG : Type := Ctl × BitVec 64 × BitVec 64

/-- `wc_main`'s body's internal nodes. -/
inductive WN where
  | e | mul | e2 | call | x15

/-- `wc_main`'s body's exits. -/
inductive WX where
  | ret | abort

/-- The body's entry invariant with `%rbp` at the saved `%rbp`. -/
def wJ (R : Region) (J : AS → Ctl → Prop) (σ : AS) (c : Ctl) : Prop := J σ c ∧ σ.regs.get64 .rbp = R.addr (-8)

/-- **The body's nodes**, from the invariant `J` at `.entry`, in the
region `R`. -/
def wN (lab : Label → Int64) (R : Region) (J : AS → Ctl → Prop) : WN → ND
  | .e => ⟨lab ".Lwc_main.entry", oB, wJ R J⟩
  | .mul => ⟨lab ".Lwc_main.entry" + 36, oB, fun σ c => ∃ σ0, wJ R J σ0 c ∧ σ = wcS1 lab σ0⟩
  | .e2 => ⟨lab ".Lwc_main.entry" + 40, oB, fun σ c => ∃ σ0 fl, wJ R J σ0 c ∧ σ = wcMul.step (wcS1 lab σ0) fl⟩
  | .call => ⟨lab "scc_rt_print", ⟨-96, []⟩, fun σ c => ∃ σ0 fl, wJ R J σ0 c ∧ σ = wcC lab σ0 fl⟩
  | .x15 => ⟨lab ".Lwc_main.x15", ⟨-88, []⟩, fun σ c => ∃ σ0, wJ R J σ0 c ∧
      σ.regs.get64 .rbp = R.addr (-8) ∧ ∀ k, -88 ≤ k → k < 8 → k % 8 = 0 → σ.slot k = wcSl lab σ0 k⟩

/-- **The body's exits**: the caller's node `x`, and `print`'s abort. -/
def wX (lab : Label → Int64) (J : AS → Ctl → Prop) (x : ND) : WX → ND
  | .ret => x
  | .abort => ⟨lab "scc_rt_abort", ⟨-144, []⟩, fun σ c => σ.regs.get64 .rdi = 4 ∧ ∃ σ0, J σ0 c⟩

/-- `print`'s region at the call: based at its saved `%rbp` (`-104`, the
return address at `-96`), its frame of 40 below, its return address cell
above. -/
abbrev pR (R : Region) : Region := R.callee (-96 - 8) (-40) 16

/-- **`wc_main`'s body's states inside `W`**, none moved by `K`: the
blocks', and `print`'s in its region (for every ghost returning to `.x15`,
the caller's cells outside it holding values). -/
structure WcBody1W (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (J : AS → Ctl → Prop) : Prop where
  e : BlkW W K exe endPc R F (wN (_root_.Executable.labels exe).label R J .e) wcE1
  mul : NodeW W K exe endPc R F (wN (_root_.Executable.labels exe).label R J .mul)
  e2 : BlkW W K exe endPc R F (wN (_root_.Executable.labels exe).label R J .e2) wcE2
  print : ∀ g : PG, g.2.2 = ((_root_.Executable.labels exe).label ".Lwc_main.x15").toBitVec →
    Print.PrintW g.1 g.2.1 g.2.2 W K exe endPc (pR R) (fun m => F m ∧ CallerCells R (-96 - 8) (-40) 16 m)
  x15 : BlkW W K exe endPc R F
    ⟨(_root_.Executable.labels exe).label ".Lwc_main.x15", oB,
      (wN (_root_.Executable.labels exe).label R J .x15).J⟩ wcR15

/-- The body is inside the trivial predicate, with no outside moves. -/
theorem WcBody1W.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {J : AS → Ctl → Prop} : WcBody1W (fun _ _ => True) (fun _ _ => False) exe endPc R F J :=
  ⟨BlkW.triv, NodeW.triv, BlkW.triv, fun g _ => Print.PrintW.triv g.1 g.2.1 g.2.2, BlkW.triv⟩

/-- `PrintW` under a weaker frame condition holds under a stronger one. -/
theorem printW_mono {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F F' : MachineData → Prop} {c0 : Ctl} {rbp0 ra : BitVec 64}
    (h : Print.PrintW c0 rbp0 ra W K exe endPc R F) (hFF : ∀ m, F' m → F m) :
    Print.PrintW c0 rbp0 ra W K exe endPc R F' :=
  ⟨blkW_mono h.e hFF, blkW_mono h.n1 hFF, blkW_mono h.loop hFF, blkW_mono h.n3 hFF, blkW_mono h.write hFF,
    blkW_mono h.n5 hFF, blkW_mono h.n6 hFF, blkW_mono h.chk2 hFF, blkW_mono h.n8 hFF, blkW_mono h.chk3 hFF,
    blkW_mono h.n10 hFF, blkW_mono h.adv hFF, blkW_mono h.fail hFF, blkW_mono h.done hFF⟩

/-- **A register's offset as an invariant fact**: at a node whose offsets
claim `r` at `k`, its invariant may claim `r = R.addr k`. -/
theorem At.reg_addr {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {n : ND}
    {r : Reg64} {k : Int} {s : State} {c : Ctl} (hk : n.o.get r = some k) (h : At exe endPc R F n s c) :
    At exe endPc R F ⟨n.pc, n.o, fun σ c => n.J σ c ∧ σ.regs.get64 r = R.addr k⟩ s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, hJ, hA.so r k hk⟩

/-- **`%rbp`'s offset from an invariant fact**: at a node whose invariant
puts `%rbp` at `R.addr k`, `%rbp` is at offset `k`. -/
theorem At.rbp_addr {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {pc : Int64}
    {sp k : Int} {rs : List (Reg64 × Int)} {J : AS → Ctl → Prop} {s : State} {c : Ctl}
    (h : At exe endPc R F ⟨pc, ⟨sp, rs⟩, J⟩ s c) (hJ : ∀ σ c, J σ c → σ.regs.get64 .rbp = R.addr k) :
    At exe endPc R F ⟨pc, ⟨sp, (.rbp, k) :: rs⟩, J⟩ s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ'⟩ := h
  refine ⟨he, hn, hdc, hpc, σ, ⟨hA.regs, hA.zmms, hA.status, fun r k' hk => ?_, hA.slot⟩, hD, hJ'⟩
  unfold SO.get at hk
  split at hk
  · rename_i hr; subst hr; cases hk; exact hA.so .rsp sp (SO.get_rsp _)
  · rename_i hr
    simp only [lk] at hk
    split at hk
    · rename_i hb; subst hb; cases hk; exact hJ σ c hJ'
    · exact hA.so r k' (by simp only [SO.get, hr, ↓reduceIte]; exact hk)

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main`'s body is one segment inside `W`** in any valid layout of
`hello1Cells`: from `.entry` (invariant `J`, `%rsp` at the frame's base,
`%rbp` at the saved `%rbp`) to the caller's node `x` (pc the saved return
address, `hra`; offsets at most `⟨8, []⟩`) or `print`'s abort. At the
return, `x`'s invariant holds after a local run of the source of every
state with `%rax = 0`, `%rbp` the saved `%rbp`, `%rsp` past the return
address and the frame's words as the block left them (`hedge`). `print`'s
write system call is a given segment for every frame condition the call
hands it (`hsys`; discharged by the output row once the source extern
lands). Its states lie in `W`, none moved by `K` (`hW`). -/
theorem hello1_wc_body_segW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 8 ≤ R.hi)
    {J : AS → Ctl → Prop} {x : ND} (ho : SO.le x.o ⟨8, []⟩ = true)
    (hW : WcBody1W W K exe endPc R F J) (hra : ∀ σ c, J σ c → x.pc = Int64.ofBitVec (σ.slot 0))
    {fp : BitVec 64} (hfp : ∀ σ c, J σ c → σ.slot (-8) = fp)
    (hsys : ∀ F' : MachineData → Prop, FStable (pR R) F' →
      (∀ m, F' m → (F m ∧ CallerCells R (-96 - 8) (-40) 16 m) ∧ WcRa R x.pc m ∧ WcFp R fp m) →
      ∀ g : PG, g.2.2 = ((_root_.Executable.labels exe).label ".Lwc_main.x15").toBitVec → g.2.1 = R.addr (-8) →
      SegW W K p lbl ms (At exe endPc (pR R) F' (Print.N (_root_.Executable.labels exe).label g.1 g.2.1 g.2.2 .sys))
        (At exe endPc (pR R) F' (Print.N (_root_.Executable.labels exe).label g.1 g.2.1 g.2.2 .n5)))
    (hedge : ∀ σ c, J σ c → σ.regs.get64 .rbp = R.addr (-8) → ∀ σ' : AS,
      (∀ k, -88 ≤ k → k < 8 → k % 8 = 0 → σ'.slot k = wcSl (_root_.Executable.labels exe).label σ k) →
      σ'.regs.rax.toBitVec = 0#64 → σ'.regs.rbp.toBitVec = σ.slot (-8) →
      σ'.regs.rsp.toBitVec = σ.regs.rbp.toBitVec + 8#64 + 8#64 →
      ∃ c', LocalRun p c c' ∧ x.J σ' c') :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label ".Lwc_main.entry", oB, J⟩)
      (fun s c => ∃ y, At exe endPc R F (wX (_root_.Executable.labels exe).label J x y) s c) := by
  have hin := hello1_wcBodyIn
  simp only [wcBodyIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨h0, hm⟩, h2⟩, h15⟩, hgap⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have e15 : lab ".Lwc_main.x15" = lab ".Lwc_main.entry" + Int64.ofNat 87 := label_labelGapB hp hgap
  refine (fn_segW (N := wN lab R J) (E := wX lab J x) (fun i => ?_) WN.e).mono_pre
    fun _ _ h => At.reg_addr (r := .rbp) (k := -8) rfl h
  cases i
  case e =>
    refine seg_ndW (by simp [wcE1]) wcE1_ok hF hR hlo hhi (code_field hp hend h0 (ofNat_zero' _)) hW.e
      fun σ c hJ => ⟨c, .refl c, .inl ⟨WN.mul, ?_, ?_, σ, hJ, rfl⟩⟩
    · simp only [wN]; rw [wcE1_run]
    · simp only [wN]; rw [wcE1_run]; rfl
  case mul =>
    refine flag_ndW (fi := wcMul) (z := 4) rfl hF (code_field hp hend hm rfl) hW.mul
      fun σ c ⟨σ0, hJ0, hσ⟩ fl => ⟨c, .refl c, .inl ⟨WN.e2, ?_, ?_, σ0, fl, hJ0, by rw [hσ]⟩⟩
    · show lab ".Lwc_main.entry" + 40 = lab ".Lwc_main.entry" + 36 + Int64.ofNat 4
      rw [Int64.add_assoc]; rfl
    · rfl
  case e2 =>
    refine seg_ndW (by simp [wcE2]) wcE2_ok hF hR hlo hhi (code_field hp hend h2 rfl) hW.e2
      fun σ c ⟨σ0, fl, hJ0, hσ⟩ => ⟨c, .refl c, .inl ⟨WN.call, ?_, ?_, σ0, fl, hJ0, ?_⟩⟩
    · simp only [wN]; rw [wcE2_run]
    · simp only [wN]; rw [wcE2_run]; rfl
    · rw [hσ, wcC_eq]; rfl
  case call =>
    refine call_nd_FWK (KC := False) (e0 := 8) (lo' := -40) (hi' := 16) (M := fun _ => True)
      (Ne := fun g : PG => Print.N lab g.1 g.2.1 g.2.2 .e) (Ex := fun g : PG => Print.E lab g.1 g.2.1 g.2.2)
      hR hF (by show R.lo ≤ -96 - 8 + -40; omega) (by decide) (by show (-96 : Int) - 8 < R.hi; omega)
      (by show (-96 : Int) - 8 + 16 ≤ R.hi; omega) (by show ((-96 : Int) - 8) % 8 = 0; decide) (by decide)
      (by decide) (fun h => h.elim)
      (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' hlo' hhi' hF' _ hFF hR'e hcc g hg hab => by
        subst hR'e
        obtain ⟨σC, c, ⟨σ0, fl, hJ0, hσ⟩, ⟨-, hb, h8⟩⟩ := hg
        have hg2 : g.2.2 = (lab ".Lwc_main.x15").toBitVec := by
          rw [← h8]; show σC.slot (-96 - 8 + 8) = _; rw [hσ]; exact wcC_ra lab σ0 fl e15
        -- `print`'s saved `%rbp`: `wc_main`'s, at offset `-8`
        have hg1 : g.2.1 = R.addr (-8) := by
          rw [← hb]; show σC.regs.get64 .rbp = _; rw [hσ, wcC_rbp]; exact hJ0.2
        -- the return address, at offset `0`, outside `print`'s region: as at the call
        -- and the saved `%rbp`, at offset `-8`
        have hwr : ∀ m, F' m → WcRa R x.pc m ∧ WcFp R fp m := fun m hm => by
          obtain ⟨mC, σC', c', hA, ⟨σ0', fl', hJ0', hσ'⟩, -, hkept⟩ := hab m hm
          obtain ⟨j, hj, hv⟩ := hA.slot 0 ⟨by decide, by omega, by omega⟩
          obtain ⟨j8, hj8, hv8⟩ := hA.slot (-8) ⟨by decide, by omega, by omega⟩
          refine ⟨⟨j, ?_, ?_⟩, ⟨j8, ?_, ?_⟩⟩
          · rw [hkept 0 ⟨by decide, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, wN]; omega), hj]
          · rw [hv, hσ', wcC_slot, (wcSl_rec lab σ0').2]; exact (hra σ0' c' hJ0'.1).symm
          · rw [hkept (-8) ⟨by decide, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, wN]; omega),
              hj8]
          · rw [hv8, hσ', wcC_slot, (wcSl_rec lab σ0').1]; exact hfp σ0' c' hJ0'.1
        exact (seg_print_ofW hp hend SccCode.hello1_print hF' hR' hlo' hhi'
          (printW_mono (hW.print g hg2) fun m h => ⟨hFF m h, hcc m h⟩)
          (hsys F' hF' (fun m h => ⟨⟨hFF m h, hcc m h⟩, hwr m h⟩) g hg2 hg1)).mono_post
          fun _ _ ⟨y, h⟩ => ⟨y, h, trivial⟩)
      (fun _ => rfl) ?_ ?_
    · rintro σC c -
      exact ⟨(c, σC.regs.rbp.toBitVec, σC.slot (-96)), rfl, rfl, rfl, rfl⟩
    · rintro g y σC c σx c' σR ⟨σ0, fl, hJ0, hσ⟩ ⟨hc, hb, h8⟩ hx hreg - - hsl
      cases y
      · obtain ⟨rfl, hbx⟩ := hx
        refine .inl ⟨WN.x15, ?_, rfl, σ0, hc ▸ hJ0, ?_, fun k h1 h2 h3 => ?_⟩
        · show lab ".Lwc_main.x15" = Int64.ofBitVec g.2.2
          rw [← h8]
          show _ = Int64.ofBitVec (σC.slot (-96 - 8 + 8))
          rw [show (-96 : Int) - 8 + 8 = -96 by decide, hσ, wcC_ra lab σ0 fl e15, int64_ofBitVec_toBitVec]
        · show σR.regs.get64 .rbp = R.addr (-8)
          rw [hreg, hbx, ← hb]
          show σC.regs.get64 .rbp = _
          rw [hσ, wcC_rbp]; exact hJ0.2
        · rw [hsl k ⟨h3, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, wN]; omega), hσ, wcC_slot]
      · obtain ⟨rfl, h4⟩ := hx
        refine .inr ⟨WX.abort, rfl, rfl, ?_, σ0, hc ▸ hJ0.1⟩
        rw [hreg]; exact h4
  case x15 =>
    refine (seg_ndW (n := ⟨lab ".Lwc_main.x15", oB, (wN lab R J .x15).J⟩) (by simp [wcR15]) wcR15_ok hF hR hlo
      hhi (code_field hp hend h15 (ofNat_zero' _)) hW.x15 fun σ c ⟨σ0, hJ0, hb, hsl⟩ => ?_).mono_pre
      fun _ _ h => At.rbp_addr h fun _ _ ⟨_, _, hb, _⟩ => hb
    have e8 : σ.slot (-8) = σ0.slot (-8) := by rw [hsl _ (by decide) (by decide) (by decide), (wcSl_rec lab σ0).1]
    have e0 : σ.slot 0 = σ0.slot 0 := by rw [hsl _ (by decide) (by decide) (by decide), (wcSl_rec lab σ0).2]
    have hbb : σ.regs.rbp.toBitVec = σ0.regs.rbp.toBitVec := by
      show σ.regs.get64 .rbp = σ0.regs.get64 .rbp; rw [hb, hJ0.2]
    obtain ⟨c', hr, hx⟩ := hedge σ0 c hJ0.1 hJ0.2 (arun lab wcR15 ⟨lab ".Lwc_main.x15", oB, σ⟩).σ
      (by rw [wcR15_run]; exact hsl) (by rw [wcR15_run]; simp [Reg64s.set64])
      (by rw [wcR15_run]; simp [Reg64s.set64, e8]) (by rw [wcR15_run]; simp [Reg64s.set64, hbb])
    refine ⟨c', hr, .inr ⟨WX.ret, ?_, ?_, hx⟩⟩
    · show x.pc = (arun lab wcR15 ⟨lab ".Lwc_main.x15", oB, σ⟩).pc
      rw [wcR15_run, hra σ0 c hJ0.1, e0]
    · show x.o.le (arun lab wcR15 ⟨lab ".Lwc_main.x15", oB, σ⟩).so = true
      rw [wcR15_run]; exact ho

end Fn

/-! ## `wc_main` -/

/-- **`wc_main`'s body invariant** from its entry invariant `J0`: the return
address, the saved `%rbp` and the five arguments' words as some entry state
left them. -/
def wcJ (J0 : AS → Ctl → Prop) (σ : AS) (c : Ctl) : Prop :=
  ∃ σe, J0 σe c ∧ σ.slot 0 = σe.slot 0 ∧ σ.slot (-8) = σe.regs.rbp.toBitVec ∧
    σ.slot (-16) = σe.regs.rdi.toBitVec ∧ σ.slot (-24) = σe.regs.rsi.toBitVec ∧
    σ.slot (-32) = σe.regs.rdx.toBitVec ∧ σ.slot (-40) = σe.regs.rcx.toBitVec ∧ σ.slot (-48) = σe.regs.r8.toBitVec

/-- **`wc_main`'s states inside `W`**, none moved by `K`: its prologue's
(from the entry invariant `J0`) and its body's. -/
structure Wc1W (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isa) (J0 : AS → Ctl → Prop) : Prop where
  pro : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "wc_main") 80 8 ".Lwc_main.stk" 5 9 3 2 4
    [(.rdi, -8, 4), (.rsi, -16, 4), (.rdx, -24, 4), (.rcx, -32, 4), (.r8, -40, 4)] J0
  body : WcBody1W W K exe endPc R F (wcJ J0)

/-- `wc_main` is inside the trivial predicate, with no outside moves. -/
theorem Wc1W.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {J0 : AS → Ctl → Prop} : Wc1W (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J0 :=
  ⟨XProW.triv, WcBody1W.triv⟩

section WcFn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` is one segment inside `W`** in any valid layout of
`hello1Cells`: from its entry (invariant `J0`, `%rsp` at the region's
offset 0, the limit word's facts for its frame of 80 below the saved
`%rbp`, `hlim`) to the caller's node `x` (pc the return address, `hra`;
offsets at most `⟨8, []⟩`) or `print`'s abort: its prologue, then
`hello1_wc_body_segW` from `wcJ J0` (`hsys`, `hedge` as there). Its states
lie in `W`, none moved by `K` (`hW`). -/
theorem hello1_wc_segW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 8 ≤ R.hi)
    {J0 : AS → Ctl → Prop} {x : ND} (ho : SO.le x.o ⟨8, []⟩ = true)
    (hW : Wc1W W K exe endPc R F ms J0)
    (hlim : ∀ σ c, J0 σ c → Ret0.LimOk ms F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - (80 : Int64).toBitVec))
    (hra : ∀ σ c, J0 σ c → x.pc = Int64.ofBitVec (σ.slot 0))
    {fp : BitVec 64} (hfp : ∀ σ c, J0 σ c → σ.regs.rbp.toBitVec = fp)
    (hsys : ∀ F' : MachineData → Prop, FStable (pR R) F' →
      (∀ m, F' m → (F m ∧ CallerCells R (-96 - 8) (-40) 16 m) ∧ WcRa R x.pc m ∧ WcFp R fp m) →
      ∀ g : PG, g.2.2 = ((_root_.Executable.labels exe).label ".Lwc_main.x15").toBitVec → g.2.1 = R.addr (-8) →
      SegW W K p lbl ms (At exe endPc (pR R) F' (Print.N (_root_.Executable.labels exe).label g.1 g.2.1 g.2.2 .sys))
        (At exe endPc (pR R) F' (Print.N (_root_.Executable.labels exe).label g.1 g.2.1 g.2.2 .n5)))
    (hedge : ∀ σ c, wcJ J0 σ c → σ.regs.get64 .rbp = R.addr (-8) → ∀ σ' : AS,
      (∀ k, -88 ≤ k → k < 8 → k % 8 = 0 → σ'.slot k = wcSl (_root_.Executable.labels exe).label σ k) →
      σ'.regs.rax.toBitVec = 0#64 → σ'.regs.rbp.toBitVec = σ.slot (-8) →
      σ'.regs.rsp.toBitVec = σ.regs.rbp.toBitVec + 8#64 + 8#64 →
      ∃ c', LocalRun p c c' ∧ x.J σ' c') :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, J0⟩)
      (fun s c => ∃ y, At exe endPc R F (wX (_root_.Executable.labels exe).label (wcJ J0) x y) s c) := by
  refine SegW.seq (hello1_wc_prologue_segW hp hend
    (nb := ⟨(_root_.Executable.labels exe).label ".Lwc_main.entry", oB, wcJ J0⟩) hF hR (by omega) (by omega) rfl
    (by show SO.le oB (oF 80) = true; decide) hW.pro ?_)
    (hello1_wc_body_segW hp hend hF hR hlo hhi ho hW.body ?_ ?_ hsys hedge)
  · intro σ c hJ
    have hl := hlim σ c hJ
    refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs => ⟨σ, hJ, ?_⟩⟩⟩
    rw [hs, hr]
    simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64]
  · rintro σ c ⟨σe, hJ, h0, -⟩
    rw [h0]; exact hra σe c hJ
  · rintro σ c ⟨σe, hJ, -, h8, -⟩
    rw [h8]; exact hfp σe c hJ

end WcFn

end Spike.Lib.X64.Flow.Hello1
