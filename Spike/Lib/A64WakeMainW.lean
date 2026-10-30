/-
**wake's main after the spawn inside `mainW`** (AArch64): the
per-node obligations of `WaitLoop.seg_waitLoopW` (`LoopW`) and of the park
call (`Park.ParkGW`, through `seg_parkCallW`'s `hPW`) at
`W := WakeInst.mainW lab exe Λ lbl`: every state of `wc_waitLoop` and
`scc_rt_park` is off the abort exits and the transfer sites (`AbOffA`, the
listing's runs), its source is off `wlRet`, the state is wide, and the
source's environment is placed at the spawn's placement.

The source is at the loop's load `c0` (whose term reads one variable `cv`,
the flag's locative, bound to one word `w` whose base is the flag's address
`A`, `LocRep lbl w.val A 0`) or past it (`Past`: `x` bound to a word read as
`1`). Its environment is placed by a constant map per phase (`envC`,
`envP`): `cv` at the place of `A` (`x0` before the prologue's spill, the
frame's cell `-32` after it; in `scc_rt_park` that cell is in the caller's
frame, kept by the call), `x` in `x9`.

- `placeVal_cell`, `placeVal_x`: a target place's value at a frame cell and
  at a general register.
- `envC`, `envP`; `placed_c0`, `placed_past`: the source placed at its
  load and past it.
-/
import Spike.Lib.A64WaitLoopW
import Spike.Lib.A64ArunKeep
import Spike.Lib.A64WakeOffDef
import Spike.Lib.WakeInst

namespace Spike.Lib.A64WakeMainW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Spike.Lib (Region)
open Spike.Lib.A64.Flow (AS)

/-- The placed environment's machine. -/
abbrev M1 : Scc.Sem.ExtMachine := machine (kernel 1)

/-! ## Places -/

/-- **A target place's value at a frame cell**: the cell's (`Abs.slot`). -/
theorem placeVal_cell {R : Region} {o : Spike.Lib.A64.Flow.SO} {m : MachineData} {σ : Spike.Lib.A64.Flow.AS}
    (hA : Spike.Lib.A64.Flow.Abs R o m σ) {k : Int} (hk : R.Off k) (s : State) (hs : s.st.1 = m) :
    placeVal M1 s (.slot (R.addr k).toNat) = some (σ.slot k).toNat := by
  obtain ⟨j, hj, hjv⟩ := hA.slot k hk
  show (Scc.Sem.A64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, Scc.Sem.A64.privLoad, hs, hj]
  simp [hjv]

/-- **A target place's value at a frame cell**, from the memory there
(`privLoad`). -/
theorem placeVal_cell_of {a : BitVec 64} {j : Int} (s : State) (hj : Mem.loadInt s.st.1.dmem a 8 = some j) :
    placeVal M1 s (.slot a.toNat) = some (BitVec.ofInt 64 j).toNat := by
  show (Scc.Sem.A64.privLoad s (BitVec.ofNat 64 a.toNat)).map (·.toNat) = _
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, Scc.Sem.A64.privLoad, hj]
  rfl

/-- **A target place's value at a general register.** -/
theorem placeVal_x (s : State) (r : XReg) :
    placeVal M1 s (.reg (.x r.idx)) = some (s.st.1.regs.getXReg r).toBitVec.toNat := by
  show some (Scc.Sem.A64.regVal s (.x r.idx)).toNat = _
  cases r <;> rfl

/-! ## The source's environment placed -/

/-- **At the load**: `cv` (word `0`) at `pc` as a locative with offset `0`. -/
def envC (cv : String) (pc : Place M1.I.RegId) : String → Nat → Option (WordPlace M1.I.RegId) :=
  fun y k => if y = cv ∧ k = 0 then some (.loc pc (.imm 0)) else none

/-- **Past the load**: `cv` at `pc`, `x` (word `0`) in `x9`. -/
def envP (cv x : String) (pc : Place M1.I.RegId) : String → Nat → Option (WordPlace M1.I.RegId) :=
  fun y k => if y = cv ∧ k = 0 then some (.loc pc (.imm 0))
    else if y = x ∧ k = 0 then some (.one (.reg (.x XReg.X9.idx))) else none

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
    Spike.Lib.A64Consumer.Placed Λ lbl s c0 := by
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
(bound to a word read as `1`) in `x9`, which holds `1`. -/
theorem placed_past {c0 : Ctl} {cv x : String} {e : Expr} {ty ty' : Ty} {w w' : TermRun.Word} {A : Nat}
    {pc : Place M1.I.RegId}
    (hfv : ∀ y ∈ exprFv e, y = x ∨ y = cv) (hxc : x ≠ cv) (hl : TermRun.lookupE c0.env cv = some (ty, [w]))
    (hloc : LocRep lbl w.val A 0) (hpc : placeVal M1 s pc = some A) (hw' : ValRep lbl w'.val 1)
    (h9 : (s.st.1.regs.getXReg .X9).toBitVec = 1#64) :
    Spike.Lib.A64Consumer.Placed Λ lbl s ⟨e, (x, ty', [w']) :: c0.env, none⟩ := by
  have hl2 : TermRun.lookupE ((x, ty', [w']) :: c0.env) cv = some (ty, [w]) := by
    rw [lookupE_cons_ne hxc]; exact hl
  refine ⟨envP cv x pc, ?_, ?_, ?_⟩
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
        refine ⟨1, ?_, hw'⟩
        rw [placeVal_x, h9]; rfl
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

open Spike.Lib.A64.Flow (ND At BlkW NodeW arun dstep AM SO arun_take_reg arun_take_slot arun_take_slotO)
open Spike.Lib.A64WakeOff (PcOffA RunsOffA pcOffA_add pcOffA_at)
open Spike.Lib.WakeInst (mainW)
open Spike.Lib.A64.WideKeep (WideX)

variable {lab : String → Int64} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop}

/-- **A block node inside `mainW`**: its pcs off the exits (`hpc`), every
state wide (`hwide`), and at each internal state the source off `wlRet`
and placed (`hrest`). -/
theorem blkW_main {n : ND} {blk : List Directive}
    (hpc : ∀ k < blk.length, PcOffA lab (n.pc + Int64.ofNat (4 * k)))
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s)
    (hrest : ∀ (s : State) σ c, s.st.2 = n.pc → Spike.Lib.A64.Flow.Abs R n.o s.st.1 σ → F s.st.1 → n.J σ c →
      ∀ k < blk.length, ∀ m,
        Spike.Lib.A64.Flow.Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
          (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
        c.term ≠ WakeMLive.wlRet ∧
          Spike.Lib.A64Consumer.Placed Λ lbl { s with st := (m, n.pc + Int64.ofNat (4 * k)) } c) :
    BlkW (mainW lab exe Λ lbl) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he _ hd hn hA hF hJ k hk m hA' _
  obtain ⟨h1, h2⟩ := hrest s σ c hn hA hF hJ k hk m hA'
  exact ⟨⟨hpc k hk, h1, hwide _ he hd, h2⟩, fun _ h => h⟩

/-- **A node inside `mainW`** (`NodeW`): its pc off the exits, every state
wide, the source off `wlRet` and placed. -/
theorem nodeW_main {n : ND} (hpc : PcOffA lab n.pc)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s)
    (hrest : ∀ (s : State) σ c, s.st.2 = n.pc → Spike.Lib.A64.Flow.Abs R n.o s.st.1 σ → F s.st.1 → n.J σ c →
      c.term ≠ WakeMLive.wlRet ∧ Spike.Lib.A64Consumer.Placed Λ lbl s c) :
    NodeW (mainW lab exe Λ lbl) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨he, -, hd, hn, σ, hA, hF, hJ⟩
  obtain ⟨h1, h2⟩ := hrest s σ c hn hA hF hJ
  exact ⟨⟨by show PcOffA lab s.st.2; rw [hn]; exact hpc, h1, hwide _ he hd, h2⟩, fun _ h => h⟩

/-- An internal state's register: the abstract run's (`Abs.regs`). -/
theorem reg_of_abs {R : Region} {o : SO} {m : MachineData} {σ : AS} (h : Spike.Lib.A64.Flow.Abs R o m σ)
    (s : State) (r : XReg) : ({ s with st := (m, s.st.2) } : State).st.1.regs.getXReg r = σ.regs.getXReg r := by
  show m.regs.getXReg r = _
  rw [h.regs]

/-- The pcs of a run's slice `[c, c + len)` are off the exits. -/
theorem pc_run {runs : List (String × Nat × Nat)} (hr : RunsOffA lab runs) {l : String} {lo hi c len : Nat}
    (hq : (l, lo, hi) ∈ runs) (h1 : lo ≤ c) (h2 : c + len ≤ hi) {pc : Int64}
    (hpc : pc = lab l + Int64.ofNat (4 * c)) : ∀ k < len, PcOffA lab (pc + Int64.ofNat (4 * k)) :=
  fun _ hk => pcOffA_add hr hq h1 (by omega) hpc

/-! ## `wc_waitLoop` inside `mainW` -/

open Spike.Lib.A64.WaitLoop

/-- **`wc_waitLoop`'s pcs**: the runs after its labels (the function's
label, the prologue's fall-through `.0_entry`, `.1_then1`, `.2_else2`,
`.sp3`). -/
def waitRuns (pfx : String) : List (String × Nat × Nat) :=
  [("wc_waitLoop", 0, 10), (pfx ++ ".0_entry", 0, 8), (pfx ++ ".1_then1", 0, 5), (pfx ++ ".2_else2", 0, 1),
    (pfx ++ ".sp3", 0, 5)]

set_option hygiene false in
/-- The per-directive goals of `arun_take_reg`/`arun_take_slot` on a block
(its definitions `bs`). -/
macro "keep_blk " "[" bs:ident,* "]" : tactic =>
  `(tactic| (rintro d hd ⟨pc, o, σ⟩
             simp only [$[$bs:ident],*, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, or_assoc,
               Spike.Lib.A64.Flow.bcD, Spike.Lib.A64.Flow.bD] at hd
             rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dstep_keep))

set_option hygiene false in
/-- `keep_blk` for `arun_take_slotO` (the offsets kept as well). -/
macro "keep_blkO " "[" bs:ident,* "]" : tactic =>
  `(tactic| (rintro d hd pc σ
             simp only [$[$bs:ident],*, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, or_assoc,
               Spike.Lib.A64.Flow.bcD, Spike.Lib.A64.Flow.bD] at hd
             rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dstep_keep <;> try simp [Spike.Lib.upd_apply, Spike.Lib.rm, Spike.Lib.A64.Flow.regDst] <;> try rfl))

set_option hygiene false in
/-- A block's pcs from `waitRuns`: the run `(l, lo, hi)`, the node's offset
`c` in it, the block's definitions. -/
macro "pc_blk " l:term:max hi:term:max c:term:max "[" bs:ident,* "]" : tactic =>
  `(tactic| (intro k hk
             simp only [$[$bs:ident],*, List.length_append, List.length_cons, List.length_nil] at hk
             exact pcOffA_add (l := $l) (lo := 0) (hi := $hi) (c := $c) hruns (by simp [waitRuns])
               (Nat.zero_le _) (by omega)
               (by simp only [N, Int64.add_assoc, hentry]; first | rfl | simp | decide)))


set_option linter.unusedSimpArgs false in
/-- **`b4`'s prefixes keep `x9`**: it is spilled to the cell at `sp + 8`
and reloaded from it. -/
theorem x9_b4 (lab : Label → Int64) (pfx : String) (pc : Int64) (σ : AS) :
    ∀ k < (b4 pfx).length, (arun lab ((b4 pfx).take k) ⟨pc, oI, σ⟩).σ.regs.getXReg .X9 = σ.regs.getXReg .X9 := by
  intro k hk
  simp only [b4, b4p, List.length_append, List.length_cons, List.length_nil] at hk
  rcases k with _ | _ | _ | _ | _ | k
  rotate_left 5
  · omega
  all_goals
    simp [b4, b4p, arun, Spike.Lib.A64.Flow.dstep, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly,
    Spike.Lib.A64.Flow.AI.so, Spike.Lib.A64.Flow.AI.step, Spike.Lib.A64.Flow.AI.tgt, Spike.Lib.A64.Flow.soReg,
    Spike.Lib.A64.Flow.regRes, Operation.interp, MachineData.setRegOrSp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64,
    ConstExpr.interp, Spike.Lib.A64.Flow.SO.set, ExtOrImmReg.interp, Reg64s.getRegOrSp, Reg64s.getRegOrSp64,
    RegOrSp.base, Spike.Lib.A64.Flow.SO.get, MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64,
    Spike.Lib.A64.Flow.zrB, Spike.Lib.A64.Flow.SO.write, Spike.Lib.A64.Flow.SO.kill, Spike.Lib.A64.Flow.SO.killZ,
    Reg64s.getXReg, Reg64s.setXReg, Spike.Lib.upd_apply]

variable {ms : MemSide isaLSE2} {pfx : String} {c0 : Ctl} {x cv : String} {e : Expr} {ty : Ty}
  {w : TermRun.Word} {A x29 ra tp : BitVec 64}

/-- **`wc_waitLoop`'s states are in `mainW`** (`LoopW`): the pcs off the
exits (`hruns`), the states wide (`hwide`); the source at the load reads
only `cv` (`hfv0`), bound to the flag's locative `w` with base `A`
(`hl`, `hloc`), past it only `x` and `cv` (`hfvE`, `hxc`), and its
continuation is not `wlRet` (`hE`). -/
theorem loopW_main (hruns : RunsOffA (_root_.Executable.labels exe).label (waitRuns pfx))
    (hentry : (_root_.Executable.labels exe).label (pfx ++ ".0_entry") =
      (_root_.Executable.labels exe).label "wc_waitLoop" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s)
    (hR : R.Off (-32)) (hc0 : c0.term ≠ WakeMLive.wlRet) (hE : e ≠ WakeMLive.wlRet)
    (hfv0 : ∀ y ∈ exprFv c0.term, y = cv) (hfvE : ∀ y ∈ exprFv e, y = x ∨ y = cv) (hxc : x ≠ cv)
    (hl : TermRun.lookupE c0.env cv = some (ty, [w])) (hloc : LocRep lbl w.val A.toNat 0) :
    LoopW (mainW (_root_.Executable.labels exe).label exe Λ lbl) exe endPc R F pfx c0 x e ty
      (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A x29 ra tp where
  top := by
    refine blkW_main (by pc_blk "wc_waitLoop" 10 0 [b0]) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨rfl, h0, -⟩ := hJ
    refine ⟨hc0, placed_c0 (pc := .reg (.x XReg.X0.idx)) hfv0 hl hloc ?_⟩
    rw [placeVal_x]; show some (m.regs.getXReg .X0).toBitVec.toNat = _
    rw [hA'.regs, arun_take_reg .X0 (by keep_blk [b0]) k]; exact congrArg _ (congrArg _ h0)
  n1 := by
    refine blkW_main (by pc_blk "wc_waitLoop" 10 3 [b1, b1p]) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨⟨rfl, h0, -⟩, -⟩ := hJ
    refine ⟨hc0, placed_c0 (pc := .reg (.x XReg.X0.idx)) hfv0 hl hloc ?_⟩
    rw [placeVal_x]; show some (m.regs.getXReg .X0).toBitVec.toNat = _
    rw [hA'.regs, arun_take_reg .X0 (by keep_blk [b1, b1p]) k]; exact congrArg _ (congrArg _ h0)
  n2 := by
    refine blkW_main (by pc_blk "wc_waitLoop" 10 5 [b2]) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨rfl, h0, -⟩ := hJ
    refine ⟨hc0, placed_c0 (pc := .reg (.x XReg.X0.idx)) hfv0 hl hloc ?_⟩
    rw [placeVal_x]; show some (m.regs.getXReg .X0).toBitVec.toNat = _
    rw [hA'.regs, arun_take_reg .X0 (by keep_blk [b2]) k]; exact congrArg _ (congrArg _ h0)
  entry := by
    refine blkW_main (by pc_blk (pfx ++ ".0_entry") 8 0 [b3]) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨rfl, ⟨-, -, h32⟩, -⟩ := hJ
    refine ⟨hc0, placed_c0 (pc := .slot (R.addr (-32)).toNat) hfv0 hl hloc ?_⟩
    rw [placeVal_cell hA' hR _ rfl, arun_take_slot (-32) (by keep_blk [b3]) k, h32]
  ld := by
    refine nodeW_main (pcOffA_at hruns (l := pfx ++ ".0_entry") (lo := 0) (hi := 8) (c := 1) (by simp [waitRuns])
      (by omega) (by omega) (by simp only [N]; first | rfl | simp)) hwide
      fun s σ c hn hA _ hJ => ?_
    obtain ⟨⟨rfl, ⟨-, -, h32⟩, -⟩, -⟩ := hJ
    refine ⟨hc0, placed_c0 (pc := .slot (R.addr (-32)).toNat) hfv0 hl hloc ?_⟩
    rw [placeVal_cell hA hR _ rfl, h32]
  n4 := by
    refine blkW_main (by pc_blk (pfx ++ ".0_entry") 8 2 [b4, b4p]) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨⟨-, -, h32⟩, -, ⟨h9, hP⟩ | ⟨-, rfl⟩⟩ := hJ
    · obtain ⟨w', ⟨-, hw'⟩, rfl⟩ := hP
      refine ⟨hE, placed_past (pc := .slot (R.addr (-32)).toNat) hfvE hxc hl hloc ?_ hw' ?_⟩
      · erw [placeVal_cell hA' hR _ rfl, arun_take_slotO (blk := b4 pfx) oI (-32) (by keep_blkO [b4, b4p]) k, h32]
      · show (m.regs.getXReg .X9).toBitVec = 1#64
        rw [hA'.regs]; have h := fun pc => x9_b4 (_root_.Executable.labels exe).label pfx pc σ k hk
        simp only [Reg64s.getXReg] at h ⊢; erw [h]; exact h9
    · refine ⟨hc0, placed_c0 (pc := .slot (R.addr (-32)).toNat) hfv0 hl hloc ?_⟩
      erw [placeVal_cell hA' hR _ rfl, arun_take_slotO (blk := b4 pfx) oI (-32) (by keep_blkO [b4, b4p]) k, h32]
  n5 := by
    refine blkW_main (by pc_blk (pfx ++ ".0_entry") 8 7 [b5]) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨rfl, ⟨-, -, h32⟩, -⟩ := hJ
    refine ⟨hc0, placed_c0 (pc := .slot (R.addr (-32)).toNat) hfv0 hl hloc ?_⟩
    rw [placeVal_cell hA' hR _ rfl, arun_take_slot (-32) (by keep_blk [b5]) k, h32]
  then1 := by
    refine blkW_main (by pc_blk (pfx ++ ".1_then1") 5 0 [b6]) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨⟨-, -, h32⟩, -, ⟨w', ⟨-, hw'⟩, rfl⟩, h9⟩ := hJ
    refine ⟨hE, placed_past (pc := .slot (R.addr (-32)).toNat) hfvE hxc hl hloc ?_ hw' ?_⟩
    · rw [placeVal_cell hA' hR _ rfl, arun_take_slot (-32) (by keep_blk [b6]) k, h32]
    · show (m.regs.getXReg .X9).toBitVec = 1#64
      rw [hA'.regs, arun_take_reg .X9 (by keep_blk [b6]) k]; exact h9
  else2 := by
    refine blkW_main (by pc_blk (pfx ++ ".2_else2") 1 0 [b7]) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨rfl, ⟨-, -, h32⟩, -⟩ := hJ
    refine ⟨hc0, placed_c0 (pc := .slot (R.addr (-32)).toNat) hfv0 hl hloc ?_⟩
    rw [placeVal_cell hA' hR _ rfl, arun_take_slot (-32) (by keep_blk [b7]) k, h32]
  sp3 := by
    refine blkW_main (by pc_blk (pfx ++ ".sp3") 5 0 [b8]) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨rfl, ⟨-, -, h32⟩, -⟩ := hJ
    refine ⟨hc0, placed_c0 (pc := .slot (R.addr (-32)).toNat) hfv0 hl hloc ?_⟩
    rw [placeVal_cell hA' hR _ rfl, arun_take_slot (-32) (by keep_blk [b8]) k, h32]

/-- **`wc_waitLoop`'s limit load (`.tls`) is in `mainW`** (`NodeW`): the
`hW` of `seg_waitTlsW` at this instance (`cv` still in `x0`). -/
theorem tlsW_main (hruns : RunsOffA (_root_.Executable.labels exe).label (waitRuns pfx))
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s)
    (hc0 : c0.term ≠ WakeMLive.wlRet) (hfv0 : ∀ y ∈ exprFv c0.term, y = cv)
    (hl : TermRun.lookupE c0.env cv = some (ty, [w])) (hloc : LocRep lbl w.val A.toNat 0) :
    NodeW (mainW (_root_.Executable.labels exe).label exe Λ lbl) (fun _ _ => False) exe endPc R F
      (N (_root_.Executable.labels exe).label pfx c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1)
        A x29 ra tp .tls) := by
  refine nodeW_main (pcOffA_at hruns (l := "wc_waitLoop") (lo := 0) (hi := 10) (c := 2) (by simp [waitRuns])
    (by omega) (by omega) (by simp only [N, Int64.add_assoc]; first | rfl | simp)) hwide
    fun s σ c _ hA _ hJ => ?_
  obtain ⟨⟨rfl, h0, -⟩, -⟩ := hJ
  refine ⟨hc0, placed_c0 (pc := .reg (.x XReg.X0.idx)) hfv0 hl hloc ?_⟩
  rw [placeVal_x]; show some (s.st.1.regs.getXReg .X0).toBitVec.toNat = _
  rw [hA.regs]; exact congrArg _ (congrArg _ h0)

/-! ## `scc_rt_park` inside `mainW` -/

open Spike.Lib.A64.Flow (DFrame Abs)

/-- **The flag's cell in the park call**: a state of the routine whose
memory is, outside the callee's region (`DFrame`), that of a state of the
call's frame condition `F'` (`h0`), whose memory outside that region is the
memory at the call (`hm`), has the caller's cell `-32`, holding `A`. -/
theorem park_cell {L : String → Int64} {Rd : TermRun.Word → Prop} (hR : R.OK) (hoff : R.Off (-32))
    {F' : MachineData → Prop}
    (hm : ∀ m, F' m → ∃ (mC : MachineData) (σC : AS) (c : Ctl), Abs R Spike.Lib.A64.WaitLoop.oI mC σC ∧
      (Spike.Lib.A64.WaitLoop.N L pfx c0 x e ty Rd A x29 ra tp .park).J σC c ∧
      ∀ k, R.Off k → ¬ (R.callee (-32) (-64) 0).Off (k - -32) →
        Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8)
    {m0 m : MachineData} (h0 : F' m0) (hd : DFrame (R.callee (-32) (-64) 0) m0 m) (s : State)
    (hs : s.st.1 = m) : placeVal M1 s (.slot (R.addr (-32)).toNat) = some A.toNat := by
  obtain ⟨mC, σC, c, hA, ⟨⟨-, ⟨-, -, h32⟩, -⟩, -⟩, hk⟩ := hm m0 h0
  obtain ⟨j, hj, hjv⟩ := hA.slot (-32) hoff
  have e1 : Mem.loadInt m0.dmem (R.addr (-32)) 8 = some j :=
    (hk (-32) hoff fun ⟨_, _, h⟩ => by simp only [Region.callee] at h; omega).trans hj
  have ha := Region.addr_toNat_of hR (k := -32) hoff.2.1 (by have := hoff.2.2; omega)
  have hhi := hR.hi
  have hhi' := hoff.2.2
  have e2 : Mem.loadInt m.dmem (R.addr (-32)) 8 = some j := by
    rw [hd _ (by omega) (.inr (by simp only [Region.callee]; omega))]; exact e1
  rw [placeVal_cell_of s (hs ▸ e2), hjv, h32]

/-- **A block node of `scc_rt_park` inside `mainW`**: its pcs off the exits,
the routine's ghost source the loop's `c0` (`hJc`), the caller's cell `-32`
holding `A` (`park_cell`). -/
theorem blkW_park {L : String → Int64} {Rd : TermRun.Word → Prop} {n : ND} {blk : List Directive}
    (hpc : ∀ k < blk.length, PcOffA lab (n.pc + Int64.ofNat (4 * k)))
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s) (hR : R.OK) (hoff : R.Off (-32))
    (hc0 : c0.term ≠ WakeMLive.wlRet) (hfv0 : ∀ y ∈ exprFv c0.term, y = cv)
    (hl : TermRun.lookupE c0.env cv = some (ty, [w])) (hloc : LocRep lbl w.val A.toNat 0)
    {F' : MachineData → Prop}
    (hm : ∀ m, F' m → ∃ (mC : MachineData) (σC : AS) (c : Ctl), Abs R Spike.Lib.A64.WaitLoop.oI mC σC ∧
      (Spike.Lib.A64.WaitLoop.N L pfx c0 x e ty Rd A x29 ra tp .park).J σC c ∧
      ∀ k, R.Off k → ¬ (R.callee (-32) (-64) 0).Off (k - -32) →
        Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8)
    (hJc : ∀ σ c, n.J σ c → c = c0) :
    BlkW (mainW lab exe Λ lbl) (fun _ _ => False) exe endPc (R.callee (-32) (-64) 0) F' n blk := by
  intro s σ c he _ hd _ _ hF hJ k hk m _ hD
  obtain rfl := hJc σ c hJ
  exact ⟨⟨hpc k hk, hc0, hwide _ he hd,
    placed_c0 (pc := .slot (R.addr (-32)).toNat) hfv0 hl hloc (park_cell hR hoff hm hF hD _ rfl)⟩, fun _ h => h⟩

/-- **A one-instruction node of `scc_rt_park` inside `mainW`** (`blkW_park`
for `NodeW`). -/
theorem nodeW_park {L : String → Int64} {Rd : TermRun.Word → Prop} {n : ND} (hpc : PcOffA lab n.pc)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s) (hR : R.OK) (hoff : R.Off (-32))
    (hc0 : c0.term ≠ WakeMLive.wlRet) (hfv0 : ∀ y ∈ exprFv c0.term, y = cv)
    (hl : TermRun.lookupE c0.env cv = some (ty, [w])) (hloc : LocRep lbl w.val A.toNat 0)
    {F' : MachineData → Prop}
    (hm : ∀ m, F' m → ∃ (mC : MachineData) (σC : AS) (c : Ctl), Abs R Spike.Lib.A64.WaitLoop.oI mC σC ∧
      (Spike.Lib.A64.WaitLoop.N L pfx c0 x e ty Rd A x29 ra tp .park).J σC c ∧
      ∀ k, R.Off k → ¬ (R.callee (-32) (-64) 0).Off (k - -32) →
        Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8)
    (hJc : ∀ σ c, n.J σ c → c = c0) :
    NodeW (mainW lab exe Λ lbl) (fun _ _ => False) exe endPc (R.callee (-32) (-64) 0) F' n := by
  rintro s c ⟨he, -, hd, hn, σ, -, hF, hJ⟩
  obtain rfl := hJc σ c hJ
  exact ⟨⟨by show PcOffA lab s.st.2; rw [hn]; exact hpc, hc0, hwide _ he hd,
    placed_c0 (pc := .slot (R.addr (-32)).toNat) hfv0 hl hloc
      (park_cell hR hoff hm hF (DFrame.refl _ _) _ rfl)⟩, fun _ h => h⟩

set_option hygiene false in
/-- A block node of `scc_rt_park`: its run `(l, lo, hi)`, offset `c`, block. -/
macro "parkBlk " l:term:max hi:term:max c:term:max b:ident : tactic =>
  `(tactic| (refine blkW_park ?_ hwide hR hoff hc0 hfv0 hl hloc hm (fun _ _ h => ?_)
             · intro k hk
               simp only [$b:ident, List.length_cons, List.length_nil] at hk
               exact pcOffA_add (l := $l) (lo := 0) (hi := $hi) (c := $c) hruns (by simp [Spike.Lib.A64.Flow.Park.parkRuns])
                 (Nat.zero_le _) (by omega) (by simp only [Spike.Lib.A64.Flow.Park.N, Spike.Lib.A64.Flow.Park.pcSvc, Int64.add_assoc]; first | rfl | simp)
             · first | exact h.1 | exact h.1.1 | exact h.1.1.1 | exact h.1.1.1.1))

set_option hygiene false in
/-- A one-instruction node of `scc_rt_park`: its run and offset. -/
macro "parkOne " l:term:max hi:term:max c:term:max : tactic =>
  `(tactic| (refine nodeW_park ?_ hwide hR hoff hc0 hfv0 hl hloc hm (fun _ _ h => ?_)
             · exact pcOffA_at (l := $l) (lo := 0) (hi := $hi) (c := $c) hruns (by simp [Spike.Lib.A64.Flow.Park.parkRuns])
                 (Nat.zero_le _) (by omega) (by simp only [Spike.Lib.A64.Flow.Park.N, Spike.Lib.A64.Flow.Park.pcSvc, Int64.add_assoc]; first | rfl | simp)
             · first | exact h.1 | exact h.1.1 | exact h.1.1.1 | exact h.1.1.1.1))

/-- **`scc_rt_park` inside `mainW`** (`seg_parkCallW`'s `hPW` at this
instance): at every callee region and frame condition the call passes,
every node of the routine whose ghost source is the loop's `c0`. -/
theorem parkGW_main {Rd : TermRun.Word → Prop}
    (hruns : RunsOffA (_root_.Executable.labels exe).label Spike.Lib.A64.Flow.Park.parkRuns)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s) (hR : R.OK) (hoff : R.Off (-32))
    (hc0 : c0.term ≠ WakeMLive.wlRet) (hfv0 : ∀ y ∈ exprFv c0.term, y = cv)
    (hl : TermRun.lookupE c0.env cv = some (ty, [w])) (hloc : LocRep lbl w.val A.toNat 0) :
    ∀ (R' : Region) (F' : MachineData → Prop), R' = R.callee (-32) (-64) 0 → R'.OK →
      R'.base.toNat % 16 = 0 → (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ (mC : MachineData) (σC : AS) (c : Ctl), Abs R Spike.Lib.A64.WaitLoop.oI mC σC ∧
        (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .park).J σC c ∧
        ∀ k, R.Off k → ¬ R'.Off (k - -32) → Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
      ∀ g : Ctl × BitVec 64 × BitVec 64, g.1 = c0 →
        Spike.Lib.A64.Flow.Park.ParkGW (mainW (_root_.Executable.labels exe).label exe Λ lbl) exe endPc R' F' g.1 g.2.1 g.2.2 tp := by
  rintro R' F' rfl - - - hm ⟨g1, g29, gra⟩ rfl
  exact {
    e := by parkBlk "scc_rt_park" 4 0 Spike.Lib.A64.Flow.Park.b0
    n1 := by parkBlk ".L10_scc_rt_park.0_entry" 12 0 Spike.Lib.A64.Flow.Park.b1
    swp1 := by parkOne ".L10_scc_rt_park.0_entry" 12 5
    n2 := by parkBlk ".L10_scc_rt_park.0_entry" 12 6 Spike.Lib.A64.Flow.Park.b2
    n3 := by parkBlk ".L10_scc_rt_park.0_entry" 12 11 Spike.Lib.A64.Flow.Park.b3
    wait := by parkBlk ".L10_scc_rt_park.1_wait" 22 0 Spike.Lib.A64.Flow.Park.b4
    svc := by parkOne ".L10_scc_rt_park.1_wait" 22 11
    n5 := by parkBlk ".L10_scc_rt_park.1_wait" 22 12 Spike.Lib.A64.Flow.Park.b5
    swp2 := by parkOne ".L10_scc_rt_park.1_wait" 22 16
    n6 := by parkBlk ".L10_scc_rt_park.1_wait" 22 17 Spike.Lib.A64.Flow.Park.b6
    done := by parkBlk ".L10_scc_rt_park.2_done" 4 0 Spike.Lib.A64.Flow.Park.b7 }

end Spike.Lib.A64WakeMainW
