/-
**wake's main after the spawn inside `mainW`** (x86-64): the
x64 twin of `Spike/Lib/A64WakeMainW.lean`. The per-node obligations of
`WaitLoop.seg_waitLoopW` (`LoopW`, `Spike/Lib/X64WaitLoopW.lean`) and of
the park call (`Park.ParkGW`, through `seg_parkCallW`'s `hPW`) at
`W := X64WakeInst.mainW lab exe Λ lbl`: every state of `wc_waitLoop` and
`scc_rt_park` is off the abort exits and the transfer sites (`AbOffA`, the
listing's byte runs), its source is off `wlRet`, the state is wide, and the
source's environment is placed at the spawn's placement.

The source is at the loop's load `c0` (whose term reads one variable `cv`,
the flag's locative, bound to one word `w` whose base is the flag's address
`A`, `LocRep lbl w.val A 0`) or past it (`Past`: `x` bound to a word read as
`1`). Its environment is placed by a constant map per phase (`envC`,
`envP`): `cv` at the place of `A` (`%rdi` in the prologue, before and
during its spill; the frame's cell `-16`, i.e. `-8(%rbp)` with `%rbp` at
`-8`, after it; in `scc_rt_park` that cell is in the caller's frame, kept
by the call), `x` at the place of the loaded `1`
(`%rax` in `b5`, which spills and reloads it; the cell `-24` in `.then1`).

- `placeVal_cell`, `placeVal_cell_of`, `placeVal_reg`: a target place's
  value at a frame cell and at a general register.
- `envC`, `envP`; `placed_c0`, `placed_past`: the source placed at its
  load and past it.
- `blkW_main`, `nodeW_main`: a node's states in `mainW`.
- `loopW_main`: `LoopW` at `mainW`.
- `park_cell`, `blkW_park`, `nodeW_park`, `parkGW_main`: `seg_parkCallW`'s
  `hPW` at `mainW`.
-/
import Spike.Lib.X64WaitLoopW
import Spike.Lib.X64WakeMainWDef
import Spike.Lib.X64WakeRunsOffWait

namespace Spike.Lib.X64WakeMainW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib (Region)
open Spike.Lib.X64

set_option linter.unusedSimpArgs false

/-- The placed environment's machine. -/
abbrev M1 : Scc.Sem.ExtMachine := machine (kernel 1)

/-! ## Places -/

/-- **A target place's value at a frame cell**: the cell's (`Abs.slot`). -/
theorem placeVal_cell {R : Region} {o : SO} {m : MachineData} {σ : AS} (hA : Abs R o m σ) {k : Int}
    (hk : R.Off k) (s : State) (hs : s.st.1 = m) :
    placeVal M1 s (.slot (R.addr k).toNat) = some (σ.slot k).toNat := by
  obtain ⟨j, hj, hjv⟩ := hA.slot k hk
  show (Scc.Sem.X64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, Scc.Sem.X64.privLoad, hs, hj]
  simp [hjv]

/-- **A target place's value at a frame cell**, from the memory there
(`privLoad`). -/
theorem placeVal_cell_of {a : BitVec 64} {j : Int} (s : State) (hj : Mem.loadInt s.st.1.dmem a 8 = some j) :
    placeVal M1 s (.slot a.toNat) = some (BitVec.ofInt 64 j).toNat := by
  show (Scc.Sem.X64.privLoad s (BitVec.ofNat 64 a.toNat)).map (·.toNat) = _
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, Scc.Sem.X64.privLoad, hj]
  rfl

/-- **A target place's value at a general register.** -/
theorem placeVal_reg (s : State) (r : Reg64) :
    placeVal M1 s (.reg (.r r)) = some (s.st.1.regs.get64 r).toNat := rfl

/-! ## The source's environment placed -/

/-- **At the load**: `cv` (word `0`) at `pc` as a locative with offset `0`. -/
def envC (cv : String) (pc : Place M1.I.RegId) : String → Nat → Option (WordPlace M1.I.RegId) :=
  fun y k => if y = cv ∧ k = 0 then some (.loc pc (.imm 0)) else none

/-- **Past the load**: `cv` at `pc`, `x` (word `0`) at `px`. -/
def envP (cv x : String) (pc px : Place M1.I.RegId) : String → Nat → Option (WordPlace M1.I.RegId) :=
  fun y k => if y = cv ∧ k = 0 then some (.loc pc (.imm 0))
    else if y = x ∧ k = 0 then some (.one px) else none

theorem lookupE_cons_ne {env : TermRun.Env} {x y : String} {t : Ty} {ws : List TermRun.Word} (h : x ≠ y) :
    TermRun.lookupE ((x, t, ws) :: env) y = TermRun.lookupE env y := by
  have : (x == y) = false := by simpa [beq_iff_eq] using h
  simp [TermRun.lookupE, List.find?, this]

theorem lookupE_cons_eq {env : TermRun.Env} {x : String} {t : Ty} {ws : List TermRun.Word} :
    TermRun.lookupE ((x, t, ws) :: env) x = some (t, ws) := by
  simp [TermRun.lookupE, List.find?]

variable {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {s : State}

/-- **The source at its load is placed**: its term reads only `cv`, bound
to one word whose base `A` is at `pc`. -/
theorem placed_c0 {c0 : Ctl} {cv : String} {ty : Ty} {w : TermRun.Word} {A : Nat} {pc : Place M1.I.RegId}
    (hfv : ∀ y ∈ exprFv c0.term, y = cv) (hl : TermRun.lookupE c0.env cv = some (ty, [w]))
    (hloc : LocRep lbl w.val A 0) (hpc : placeVal M1 s pc = some A) :
    Spike.Lib.X64Consumer.Placed Λ lbl s c0 := by
  refine ⟨envC cv pc, ?_, ?_, ?_⟩
  · intro y t ws hy k wd wp hwd hwp
    simp only [envC] at hwp
    split at hwp
    · obtain ⟨rfl, rfl⟩ := ‹y = cv ∧ k = 0›
      cases hwp
      rw [hl] at hy
      cases hy
      cases hwd
      exact ⟨A, 0, hpc, rfl, hloc⟩
    · cases hwp
  · intro y hy t ws hl' k hk
    obtain rfl := hfv y hy
    rw [hl] at hl'
    cases hl'
    obtain rfl : k = 0 := by simpa using hk
    exact ⟨_, ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, rfl⟩)⟩
  · intro y k n h
    simp only [envC] at h
    split at h <;> cases h

/-- **The source past its load is placed**: `cv` as at the load, `x`
(bound to a word read as `1`) at `px`, which holds `1`. -/
theorem placed_past {c0 : Ctl} {cv x : String} {e : Expr} {ty ty' : Ty} {w w' : TermRun.Word} {A : Nat}
    {pc px : Place M1.I.RegId}
    (hfv : ∀ y ∈ exprFv e, y = x ∨ y = cv) (hxc : x ≠ cv) (hl : TermRun.lookupE c0.env cv = some (ty, [w]))
    (hloc : LocRep lbl w.val A 0) (hpc : placeVal M1 s pc = some A) (hw' : ValRep lbl w'.val 1)
    (hpx : placeVal M1 s px = some 1) :
    Spike.Lib.X64Consumer.Placed Λ lbl s ⟨e, (x, ty', [w']) :: c0.env, none⟩ := by
  have hl2 : TermRun.lookupE ((x, ty', [w']) :: c0.env) cv = some (ty, [w]) := by
    rw [lookupE_cons_ne hxc]; exact hl
  refine ⟨envP cv x pc px, ?_, ?_, ?_⟩
  · intro y t ws hy k wd wp hwd hwp
    simp only [envP] at hwp
    split at hwp
    · obtain ⟨rfl, rfl⟩ := ‹y = cv ∧ k = 0›
      cases hwp
      rw [hl2] at hy
      cases hy
      cases hwd
      exact ⟨A, 0, hpc, rfl, hloc⟩
    · split at hwp
      · obtain ⟨rfl, rfl⟩ := ‹y = x ∧ k = 0›
        cases hwp
        rw [lookupE_cons_eq] at hy
        cases hy
        cases hwd
        exact ⟨1, hpx, hw'⟩
      · cases hwp
  · intro y hy t ws hl' k hk
    rcases hfv y hy with rfl | rfl
    · rw [lookupE_cons_eq] at hl'
      cases hl'
      obtain rfl : k = 0 := by simpa using hk
      exact ⟨_, by simp only [envP, hxc, false_and, ite_false, and_self, ite_true]; rfl⟩
    · rw [hl2] at hl'
      cases hl'
      obtain rfl : k = 0 := by simpa using hk
      exact ⟨_, ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, rfl⟩)⟩
  · intro y k n h
    simp only [envP] at h
    split at h
    · cases h
    · split at h <;> cases h

/-! ## Node obligations at `mainW` -/

open Spike.Lib.X64WakeOff (PcOffA RunsOffA pcOffA_add pcOffA_at)
open Spike.Lib.X64WakeInst (mainW)
open Spike.Lib.X64.WideKeep (WideX)

variable {lab : String → Int64} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop}

/-- **A block node inside `mainW`**: its pcs off the exits (`hpc`), every
state wide (`hwide`), and at each internal state the source off `wlRet`
and placed (`hrest`). -/
theorem blkW_main {n : ND} {blk : List (Directive × Nat)}
    (hpc : ∀ k < blk.length, PcOffA lab (n.pc + Int64.ofNat (cellOff blk k)))
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s)
    (hrest : ∀ (s : State) σ c, s.st.2 = n.pc → Abs R n.o s.st.1 σ → F s.st.1 → n.J σ c →
      ∀ k < blk.length, ∀ m,
        Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
          (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
        c.term ≠ WakeMLive.wlRet ∧
          Spike.Lib.X64Consumer.Placed Λ lbl { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } c) :
    BlkW (mainW lab exe Λ lbl) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he _ hd hn hA hF hJ k hk m hA' _
  obtain ⟨h1, h2⟩ := hrest s σ c hn hA hF hJ k hk m hA'
  exact ⟨⟨hpc k hk, h1, hwide _ he hd, h2⟩, fun _ h => h⟩

/-- **A node inside `mainW`** (`NodeW`): its pc off the exits, every state
wide, the source off `wlRet` and placed. -/
theorem nodeW_main {n : ND} (hpc : PcOffA lab n.pc)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s)
    (hrest : ∀ (s : State) σ c, s.st.2 = n.pc → Abs R n.o s.st.1 σ → F s.st.1 → n.J σ c →
      c.term ≠ WakeMLive.wlRet ∧ Spike.Lib.X64Consumer.Placed Λ lbl s c) :
    NodeW (mainW lab exe Λ lbl) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨he, -, hd, hn, σ, hA, hF, hJ⟩
  obtain ⟨h1, h2⟩ := hrest s σ c hn hA hF hJ
  exact ⟨⟨by show PcOffA lab s.st.2; rw [hn]; exact hpc, h1, hwide _ he hd, h2⟩, fun _ h => h⟩

/-! ## The blocks' prefixes -/

open Spike.Lib.X64.Flow (XProW xProN1 xProN2 xProN3 xProN4 xHead xLea xCmp xFr xSt xS1 xS2 xS3 hdRegs
  ofNat_zero')
open Spike.Lib.X64.WaitLoop

/-- The abstract run's simp set over concrete blocks (`x64simp` with the
branches' and the call's steps). -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [Spike.Lib.X64.arun, Spike.Lib.X64.dstep, Spike.Lib.X64.classify, Spike.Lib.X64.RegOnly,
    Spike.Lib.X64.AI.so, Spike.Lib.X64.soReg,
    Spike.Lib.X64.regDst, Spike.Lib.X64.regRes, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.set, ConstExpr.interp, AddrExpr.interp, Spike.Lib.X64.SO.get,
    Spike.Lib.X64.SO.set, Spike.Lib.X64.SO.kill, Spike.Lib.X64.SO.write, Spike.Lib.lk, Spike.Lib.rm, Reg.base, Spike.Lib.upd_apply,
    Spike.Lib.X64.Reg64s.get_low64, Spike.Lib.X64.BlockSpec.AI.step_ld',
    Spike.Lib.X64.BlockSpec.AI.step_st', Spike.Lib.X64.BlockSpec.AI.step_push',
    Spike.Lib.X64.BlockSpec.AI.step_pop', Spike.Lib.X64.BlockSpec.AI.step_reg',
    Spike.Lib.X64.BlockSpec.AI.step_jmp', Spike.Lib.X64.BlockSpec.AI.step_jcc',
    Spike.Lib.X64.BlockSpec.AI.step_call', Spike.Lib.X64.Reg64s.get64_set64_ne,
    Spike.Lib.X64.Reg64s.get64_set64_self])

/-- A one-instruction block's only prefix is empty. -/
theorem arun_one {blk : List (Directive × Nat)} (hb : blk.length = 1) {k : Nat} (hk : k < blk.length)
    (l : String → Int64) (am : AM) : arun l (blk.take k) am = am := by
  obtain rfl : k = 0 := by omega
  rfl

/-- **The prologue's prefixes keep `%rdi`** (the flag's address). -/
theorem pro_rdi (l : String → Int64) (pc : Int64) (o : SO) (σ : AS) {blk : List (Directive × Nat)}
    (hb : blk = xHead ∨ blk = xLea 16 5 ∨ blk = xCmp ".Lwc_waitLoop.stk" 3 2 ∨ blk = xFr 16 4 [(.rdi, -8, 4)])
    {k : Nat} (hk : k < blk.length) :
    (arun l (blk.take k) ⟨pc, o, σ⟩).σ.regs.get64 .rdi = σ.regs.get64 .rdi := by
  rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [xHead, xLea, xCmp, xFr, xSt, List.map_cons, List.map_nil, List.length_cons,
      List.length_nil] at hk ⊢ <;>
    rcases k with _|_|k <;> (try omega) <;> arun_simp

theorem xS1_rdi (σ : AS) : (xS1 σ).regs.get64 .rdi = σ.regs.get64 .rdi := by
  simp only [xS1, hdRegs]
  rw [Spike.Lib.X64.Reg64s.get64_set64_ne _ (by decide), Spike.Lib.X64.Reg64s.get64_set64_ne _ (by decide)]

theorem xS2_rdi (Z : Int64) (σ : AS) : (xS2 Z σ).regs.get64 .rdi = σ.regs.get64 .rdi := by
  simp only [xS2]
  rw [Spike.Lib.X64.Reg64s.get64_set64_ne _ (by decide), xS1_rdi]

theorem xS3_rdi (Z : Int64) (v : BitVec 64) (σ : AS) : (xS3 Z v σ).regs.get64 .rdi = σ.regs.get64 .rdi := by
  simp only [xS3, Spike.Lib.X64.fsStep]
  rw [Spike.Lib.X64.Reg64s.get64_set64_ne _ (by decide), xS2_rdi]

/-- **`b5`'s prefixes keep the flag's cell and `%rax`**: `%rax` is spilled to
the cell `-24` and reloaded from it. -/
theorem b5_keep (l : String → Int64) (pc : Int64) (σ : AS) {k : Nat} (hk : k < b5.length) :
    (arun l (b5.take k) ⟨pc, oI, σ⟩).σ.slot (-16) = σ.slot (-16) ∧
      (arun l (b5.take k) ⟨pc, oI, σ⟩).σ.regs.get64 .rax = σ.regs.get64 .rax := by
  simp only [b5] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|_|k <;> (try omega) <;> arun_simp

/-- **`.then1`'s prefixes keep the cells** (no store before the `ret`). -/
theorem b7_slot (l : String → Int64) (pc : Int64) (σ : AS) {k : Nat} (hk : k < b7.length) :
    (arun l (b7.take k) ⟨pc, oI, σ⟩).σ.slot = σ.slot := by
  simp only [b7] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|k <;> (try omega) <;> arun_simp

/-- **`.x16`'s prefixes keep the cells** (no store). -/
theorem b9_slot (l : String → Int64) (pc : Int64) (σ : AS) {k : Nat} (hk : k < b9.length) :
    (arun l (b9.take k) ⟨pc, oI, σ⟩).σ.slot = σ.slot := by
  simp only [b9] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|k <;> (try omega) <;> arun_simp

/-! ## `wc_waitLoop` inside `mainW` -/

open Spike.Lib.X64.WakeRunsOff (waitRuns)

set_option hygiene false in
/-- A block's pcs from `waitRuns`: the run `(l, lo, hi)`, the node's offset
`c` in it, the block. -/
local macro "pc_blk " l:term:max hi:term:max c:term:max b:term:max : tactic =>
  `(tactic| (intro k hk
             exact pcOffA_add (l := $l) (lo := 0) (hi := $hi) (c := $c) hruns (by simp [waitRuns])
               (Nat.zero_le _) ((show ∀ k < ($b).length, $c + cellOff $b k < $hi by decide) k hk)
               (by simp only [N, x16N, xProN1, xProN2, xProN3, xProN4, Int64.add_assoc]
                   first | rfl | exact (ofNat_zero' _).symm | simp)))

variable {ms : MemSide isa} {c0 : Ctl} {x cv : String} {e : Expr} {ty tyv : Ty}
  {w : TermRun.Word} {A fp ra tp sp : BitVec 64}

/-- **`wc_waitLoop`'s states are in `mainW`** (`LoopW`): the pcs off the
exits (`hruns`), the states wide (`hwide`); the source at the load reads
only `cv` (`hfv0`), bound to the flag's locative `w` with base `A`
(`hl`, `hloc`), past it only `x` and `cv` (`hfvE`, `hxc`), and its
continuation is not `wlRet` (`hE`). The region is `seg_waitLoopW`'s
(`hlo`, `hhi`): the flag's cell `-16` and the loaded word's `-24` are in it. -/
theorem loopW_main (hruns : RunsOffA (_root_.Executable.labels exe).label waitRuns)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s)
    (hlo : R.lo ≤ -88) (hhi : 8 ≤ R.hi) (hc0 : c0.term ≠ WakeMLive.wlRet) (hE : e ≠ WakeMLive.wlRet)
    (hfv0 : ∀ y ∈ exprFv c0.term, y = cv) (hfvE : ∀ y ∈ exprFv e, y = x ∨ y = cv) (hxc : x ≠ cv)
    (hl : TermRun.lookupE c0.env cv = some (tyv, [w])) (hloc : LocRep lbl w.val A.toNat 0) :
    LoopW (mainW (_root_.Executable.labels exe).label exe Λ lbl) ms exe endPc R F c0 x e ty
      (RdOne (ms := ms) lbl) A fp ra tp sp where
  pro := {
    w0 := by
      refine blkW_main (by pc_blk "wc_waitLoop" 31 0 xHead) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
      obtain ⟨rfl, hdi, -⟩ := hJ
      refine ⟨hc0, placed_c0 (pc := .reg (.r .rdi)) hfv0 hl hloc ?_⟩
      show some (m.regs.get64 .rdi).toNat = _
      rw [hA'.regs, pro_rdi _ _ _ _ (.inl rfl) hk]; exact congrArg _ (congrArg _ hdi)
    w1 := by
      refine blkW_main (by pc_blk "wc_waitLoop" 31 4 (xLea 16 5)) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
      obtain ⟨σ0, ⟨rfl, hdi, -⟩, rfl⟩ := hJ
      refine ⟨hc0, placed_c0 (pc := .reg (.r .rdi)) hfv0 hl hloc ?_⟩
      show some (m.regs.get64 .rdi).toNat = _
      rw [hA'.regs, pro_rdi _ _ _ _ (.inr (.inl rfl)) hk, xS1_rdi]; exact congrArg _ (congrArg _ hdi)
    w2 := by
      refine nodeW_main (pcOffA_at hruns (l := "wc_waitLoop") (lo := 0) (hi := 31) (c := 9) (by simp [waitRuns])
        (by omega) (by omega) (by simp only [xProN2, Int64.add_assoc]; first | rfl | simp)) hwide
        fun s σ c _ hA _ hJ => ?_
      obtain ⟨σ0, ⟨rfl, hdi, -⟩, rfl⟩ := hJ
      refine ⟨hc0, placed_c0 (pc := .reg (.r .rdi)) hfv0 hl hloc ?_⟩
      show some (s.st.1.regs.get64 .rdi).toNat = _
      rw [hA.regs, xS2_rdi]; exact congrArg _ (congrArg _ hdi)
    w3 := by
      refine blkW_main (by pc_blk "wc_waitLoop" 31 18 (xCmp ".Lwc_waitLoop.stk" 3 2)) hwide
        fun s σ c _ _ _ hJ k hk m hA' => ?_
      obtain ⟨σ0, v, ⟨rfl, hdi, -⟩, -, rfl⟩ := hJ
      refine ⟨hc0, placed_c0 (pc := .reg (.r .rdi)) hfv0 hl hloc ?_⟩
      show some (m.regs.get64 .rdi).toNat = _
      rw [hA'.regs, pro_rdi _ _ _ _ (.inr (.inr (.inl rfl))) hk, xS3_rdi]; exact congrArg _ (congrArg _ hdi)
    w4 := by
      refine blkW_main (by pc_blk "wc_waitLoop" 31 23 (xFr 16 4 [(.rdi, -8, 4)])) hwide
        fun s σ c _ _ _ hJ k hk m hA' => ?_
      obtain ⟨σ0, v, ⟨rfl, hdi, -⟩, -, hreg, -⟩ := hJ
      refine ⟨hc0, placed_c0 (pc := .reg (.r .rdi)) hfv0 hl hloc ?_⟩
      show some (m.regs.get64 .rdi).toNat = _
      rw [hA'.regs, pro_rdi _ _ _ _ (.inr (.inr (.inr rfl))) hk, hreg, xS3_rdi]
      exact congrArg _ (congrArg _ hdi) }
  entry := by
    have o16 : R.Off (-16) := ⟨by decide, by omega, by omega⟩
    refine blkW_main (by pc_blk ".Lwc_waitLoop.entry" 29 0 b4) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨rfl, ⟨-, -, h16⟩, -, -⟩ := hJ
    refine ⟨hc0, placed_c0 (pc := .slot (R.addr (-16)).toNat) hfv0 hl hloc ?_⟩
    rw [placeVal_cell hA' o16 _ rfl, arun_one (by rfl) hk, h16]
  ld := by
    have o16 : R.Off (-16) := ⟨by decide, by omega, by omega⟩
    refine nodeW_main (pcOffA_at hruns (l := ".Lwc_waitLoop.entry") (lo := 0) (hi := 29) (c := 4)
      (by simp [waitRuns]) (by omega) (by omega) (by simp only [N]; first | rfl | simp)) hwide
      fun s σ c _ hA _ hJ => ?_
    obtain ⟨⟨rfl, ⟨-, -, h16⟩, -, -⟩, -⟩ := hJ
    refine ⟨hc0, placed_c0 (pc := .slot (R.addr (-16)).toNat) hfv0 hl hloc ?_⟩
    rw [placeVal_cell hA o16 _ rfl, h16]
  n5 := by
    have o16 : R.Off (-16) := ⟨by decide, by omega, by omega⟩
    refine blkW_main (by pc_blk ".Lwc_waitLoop.entry" 29 7 b5) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨⟨⟨-, -, h16⟩, -, -⟩, ⟨h1, w', ⟨-, hw'⟩, rfl⟩ | ⟨-, rfl⟩⟩ := hJ
    · refine ⟨hE, placed_past (pc := .slot (R.addr (-16)).toNat) (px := .reg (.r .rax)) hfvE hxc hl hloc ?_ hw' ?_⟩
      · erw [placeVal_cell hA' o16 _ rfl, (b5_keep _ _ _ hk).1, h16]
      · show some (m.regs.get64 .rax).toNat = _
        erw [hA'.regs, (b5_keep _ _ _ hk).2, show σ.regs.get64 .rax = 1#64 from h1]; rfl
    · refine ⟨hc0, placed_c0 (pc := .slot (R.addr (-16)).toNat) hfv0 hl hloc ?_⟩
      erw [placeVal_cell hA' o16 _ rfl, (b5_keep _ _ _ hk).1, h16]
  n6 := by
    have o16 : R.Off (-16) := ⟨by decide, by omega, by omega⟩
    refine blkW_main (by pc_blk ".Lwc_waitLoop.entry" 29 27 b6) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨rfl, ⟨-, -, h16⟩, -, -⟩ := hJ
    refine ⟨hc0, placed_c0 (pc := .slot (R.addr (-16)).toNat) hfv0 hl hloc ?_⟩
    rw [placeVal_cell hA' o16 _ rfl, arun_one (by rfl) hk, h16]
  then1 := by
    have o16 : R.Off (-16) := ⟨by decide, by omega, by omega⟩
    have o24 : R.Off (-24) := ⟨by decide, by omega, by omega⟩
    refine blkW_main (by pc_blk ".Lwc_waitLoop.then1" 12 0 b7) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨⟨⟨-, -, h16⟩, -, -⟩, ⟨w', ⟨-, hw'⟩, rfl⟩, h24⟩ := hJ
    refine ⟨hE, placed_past (pc := .slot (R.addr (-16)).toNat) (px := .slot (R.addr (-24)).toNat) hfvE hxc hl
      hloc ?_ hw' ?_⟩
    · erw [placeVal_cell hA' o16 _ rfl, b7_slot _ _ _ hk, h16]
    · erw [placeVal_cell hA' o24 _ rfl, b7_slot _ _ _ hk, h24]; rfl
  else2 := by
    have o16 : R.Off (-16) := ⟨by decide, by omega, by omega⟩
    refine blkW_main (by pc_blk ".Lwc_waitLoop.else2" 5 0 b8) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨rfl, ⟨-, -, h16⟩, -, -⟩ := hJ
    refine ⟨hc0, placed_c0 (pc := .slot (R.addr (-16)).toNat) hfv0 hl hloc ?_⟩
    rw [placeVal_cell hA' o16 _ rfl, arun_one (by rfl) hk, h16]
  x16 := by
    have o16 : R.Off (-16) := ⟨by decide, by omega, by omega⟩
    refine blkW_main (by pc_blk ".Lwc_waitLoop.x16" 10 0 b9) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨rfl, ⟨-, -, h16⟩, -, -⟩ := hJ
    refine ⟨hc0, placed_c0 (pc := .slot (R.addr (-16)).toNat) hfv0 hl hloc ?_⟩
    erw [placeVal_cell hA' o16 _ rfl, b9_slot _ _ _ hk, h16]

/-! ## `scc_rt_park` inside `mainW` -/

/-- **The flag's cell in the park call**: a state of the routine whose
memory is, outside the callee's region (`DFrame`), that of a state of the
call's frame condition `F'` (`h0`), whose memory outside that region is the
memory at the call (`hm`), has the caller's cell `-16`, holding `A` (the
callee's region `[-88, -24)` of the caller's misses it). -/
theorem park_cell {L : String → Int64} {Rd : TermRun.Word → Prop} (hR : R.OK) (hlo : R.lo ≤ -88)
    (hhi : 8 ≤ R.hi) {F' : MachineData → Prop}
    (hm : ∀ m, F' m → ∃ (mC : MachineData) (σC : AS) (c : Ctl), Abs R ⟨-32, [(.rbp, -8)]⟩ mC σC ∧
      (N L c0 x e ty Rd A fp ra tp sp .park).J σC c ∧
      ∀ k, R.Off k → ¬ (R.callee (-32) (-56) 8).Off (k - -32) →
        Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8)
    {m0 m : MachineData} (h0 : F' m0) (hd : DFrame (R.callee (-32) (-56) 8) m0 m) (s : State)
    (hs : s.st.1 = m) : placeVal M1 s (.slot (R.addr (-16)).toNat) = some A.toNat := by
  obtain ⟨mC, σC, c, hA, ⟨⟨-, ⟨-, -, h16⟩, -, -⟩, -⟩, hk⟩ := hm m0 h0
  have hoff : R.Off (-16) := ⟨by decide, by omega, by omega⟩
  obtain ⟨j, hj, hjv⟩ := hA.slot (-16) hoff
  have e1 : Mem.loadInt m0.dmem (R.addr (-16)) 8 = some j :=
    (hk (-16) hoff fun ⟨_, _, h⟩ => by simp only [Region.callee] at h; omega).trans hj
  have ha := Region.addr_toNat_of hR (k := -16) (by omega) (by omega)
  have hb := Region.addr_toNat_of hR (k := -32) (by omega) (by omega)
  have hhi' := hR.hi
  have e2 : Mem.loadInt m.dmem (R.addr (-16)) 8 = some j := by
    rw [hd _ (by omega) (.inr (by simp only [Region.callee]; omega))]; exact e1
  rw [placeVal_cell_of s (hs ▸ e2), hjv, h16]

/-- **A block node of `scc_rt_park` inside `mainW`**: its pcs off the exits,
the routine's ghost source the loop's `c0` (`hJc`), the caller's cell `-16`
holding `A` (`park_cell`). -/
theorem blkW_park {L : String → Int64} {Rd : TermRun.Word → Prop} {n : ND} {blk : List (Directive × Nat)}
    (hpc : ∀ k < blk.length, PcOffA lab (n.pc + Int64.ofNat (cellOff blk k)))
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s) (hR : R.OK) (hlo : R.lo ≤ -88)
    (hhi : 8 ≤ R.hi) (hc0 : c0.term ≠ WakeMLive.wlRet) (hfv0 : ∀ y ∈ exprFv c0.term, y = cv)
    (hl : TermRun.lookupE c0.env cv = some (tyv, [w])) (hloc : LocRep lbl w.val A.toNat 0)
    {F' : MachineData → Prop}
    (hm : ∀ m, F' m → ∃ (mC : MachineData) (σC : AS) (c : Ctl), Abs R ⟨-32, [(.rbp, -8)]⟩ mC σC ∧
      (N L c0 x e ty Rd A fp ra tp sp .park).J σC c ∧
      ∀ k, R.Off k → ¬ (R.callee (-32) (-56) 8).Off (k - -32) →
        Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8)
    (hJc : ∀ σ c, n.J σ c → c = c0) :
    BlkW (mainW lab exe Λ lbl) (fun _ _ => False) exe endPc (R.callee (-32) (-56) 8) F' n blk := by
  intro s σ c he _ hd _ _ hF hJ k hk m _ hD
  obtain rfl := hJc σ c hJ
  exact ⟨⟨hpc k hk, hc0, hwide _ he hd,
    placed_c0 (pc := .slot (R.addr (-16)).toNat) hfv0 hl hloc (park_cell hR hlo hhi hm hF hD _ rfl)⟩,
    fun _ h => h⟩

/-- **A one-instruction node of `scc_rt_park` inside `mainW`** (`blkW_park`
for `NodeW`). -/
theorem nodeW_park {L : String → Int64} {Rd : TermRun.Word → Prop} {n : ND} (hpc : PcOffA lab n.pc)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s) (hR : R.OK) (hlo : R.lo ≤ -88)
    (hhi : 8 ≤ R.hi) (hc0 : c0.term ≠ WakeMLive.wlRet) (hfv0 : ∀ y ∈ exprFv c0.term, y = cv)
    (hl : TermRun.lookupE c0.env cv = some (tyv, [w])) (hloc : LocRep lbl w.val A.toNat 0)
    {F' : MachineData → Prop}
    (hm : ∀ m, F' m → ∃ (mC : MachineData) (σC : AS) (c : Ctl), Abs R ⟨-32, [(.rbp, -8)]⟩ mC σC ∧
      (N L c0 x e ty Rd A fp ra tp sp .park).J σC c ∧
      ∀ k, R.Off k → ¬ (R.callee (-32) (-56) 8).Off (k - -32) →
        Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8)
    (hJc : ∀ σ c, n.J σ c → c = c0) :
    NodeW (mainW lab exe Λ lbl) (fun _ _ => False) exe endPc (R.callee (-32) (-56) 8) F' n := by
  rintro s c ⟨he, -, hd, hn, σ, -, hF, hJ⟩
  obtain rfl := hJc σ c hJ
  exact ⟨⟨by show PcOffA lab s.st.2; rw [hn]; exact hpc, hc0, hwide _ he hd,
    placed_c0 (pc := .slot (R.addr (-16)).toNat) hfv0 hl hloc
      (park_cell hR hlo hhi hm hF (DFrame.refl _ _) _ rfl)⟩, fun _ h => h⟩

set_option hygiene false in
/-- A block node of `scc_rt_park`: its run `(l, lo, hi)`, offset `c`, block. -/
local macro "parkBlk " l:term:max hi:term:max c:term:max b:ident : tactic =>
  `(tactic| (refine blkW_park ?_ hwide hR hlo hhi hc0 hfv0 hl hloc hm (fun _ _ h => ?_)
             · intro k hk
               exact pcOffA_add (l := $l) (lo := 0) (hi := $hi) (c := $c) hruns
                 (by simp [Spike.Lib.X64.Flow.Park.parkRuns]) (Nat.zero_le _)
                 ((show ∀ k < ($b).length, $c + cellOff $b k < $hi by decide) k hk)
                 (by simp only [Spike.Lib.X64.Flow.Park.N, Int64.add_assoc]
                     first | rfl | exact (ofNat_zero' _).symm | simp)
             · first | exact h.1 | exact h.1.1 | exact h.1.1.1 | exact h.1.1.1.1))

set_option hygiene false in
/-- A one-instruction node of `scc_rt_park`: its run and offset. -/
local macro "parkOne " l:term:max hi:term:max c:term:max : tactic =>
  `(tactic| (refine nodeW_park ?_ hwide hR hlo hhi hc0 hfv0 hl hloc hm (fun _ _ h => ?_)
             · exact pcOffA_at (l := $l) (lo := 0) (hi := $hi) (c := $c) hruns
                 (by simp [Spike.Lib.X64.Flow.Park.parkRuns]) (Nat.zero_le _) (by omega)
                 (by simp only [Spike.Lib.X64.Flow.Park.N, Spike.Lib.X64.Flow.Park.pcSys, Int64.add_assoc]
                     first | rfl | simp)
             · first | exact h.1 | exact h.1.1 | exact h.1.1.1 | exact h.1.1.1.1))

/-- **`scc_rt_park` inside `mainW`** (`seg_parkCallW`'s `hPW` at this
instance): at every callee region and frame condition the call passes,
every node of the routine whose ghost source is the loop's `c0`. -/
theorem parkGW_main {Rd : TermRun.Word → Prop}
    (hruns : RunsOffA (_root_.Executable.labels exe).label Spike.Lib.X64.Flow.Park.parkRuns)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s) (hR : R.OK) (hlo : R.lo ≤ -88)
    (hhi : 8 ≤ R.hi) (hc0 : c0.term ≠ WakeMLive.wlRet) (hfv0 : ∀ y ∈ exprFv c0.term, y = cv)
    (hl : TermRun.lookupE c0.env cv = some (tyv, [w])) (hloc : LocRep lbl w.val A.toNat 0) :
    ∀ (R' : Region) (F' : MachineData → Prop), R' = R.callee (-32) (-56) 8 → R'.OK →
      (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ (mC : MachineData) (σC : AS) (c : Ctl), Abs R ⟨-32, [(.rbp, -8)]⟩ mC σC ∧
        (N (_root_.Executable.labels exe).label c0 x e ty Rd A fp ra tp sp .park).J σC c ∧
        ∀ k, R.Off k → ¬ R'.Off (k - -32) → Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
      ∀ g : Ctl × BitVec 64 × BitVec 64, g.1 = c0 →
        Spike.Lib.X64.Flow.Park.ParkGW (mainW (_root_.Executable.labels exe).label exe Λ lbl) exe endPc R' F'
          g.1 g.2.1 g.2.2 tp := by
  rintro R' F' rfl - - hm ⟨g1, gbp, gra⟩ rfl
  exact {
    e := by parkBlk "scc_rt_park" 8 0 Spike.Lib.X64.Flow.Park.b0
    fsl := by parkOne ".Lscc_rt_park.entry" 50 0
    n1 := by parkBlk ".Lscc_rt_park.entry" 50 9 Spike.Lib.X64.Flow.Park.b1
    xchg1 := by parkOne ".Lscc_rt_park.entry" 50 24
    n2 := by parkBlk ".Lscc_rt_park.entry" 50 28 Spike.Lib.X64.Flow.Park.b2
    n3 := by parkBlk ".Lscc_rt_park.entry" 50 48 Spike.Lib.X64.Flow.Park.b3
    wait := by parkBlk ".Lscc_rt_park.wait" 92 0 Spike.Lib.X64.Flow.Park.b4
    sys := by parkOne ".Lscc_rt_park.wait" 92 62
    n5 := by parkBlk ".Lscc_rt_park.wait" 92 64 Spike.Lib.X64.Flow.Park.b5
    xchg2 := by parkOne ".Lscc_rt_park.wait" 92 79
    n6 := by parkBlk ".Lscc_rt_park.wait" 92 83 Spike.Lib.X64.Flow.Park.b6
    done := by parkBlk ".Lscc_rt_park.done" 5 0 Spike.Lib.X64.Flow.Park.b7 }

end Spike.Lib.X64WakeMainW

/-- info: 'Spike.Lib.X64WakeMainW.loopW_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainW.loopW_main

/-- info: 'Spike.Lib.X64WakeMainW.parkGW_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainW.parkGW_main
