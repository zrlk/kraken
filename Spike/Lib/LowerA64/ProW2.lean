/-
**A callee's prologue inside `W2`** (AArch64): `CalleePre2.hpro`
(`Spike/Lib/LowerA64/ProgC2.lean`) at the start's world `W2`, for the setup
call (`setupCallWS_ofFnSpec`, entry `uN0`) and `main`'s call after it
(`mainCallWSF_ofHeld`, entry `uNM`, `Spike/Lib/LowerA64/MainHeldA.lean`),
`Spike/Lib/LowerA64/SetupCallC2.lean`.

- `ArgEq`, `argEq_arun_take`, `dstep_chkHead`, `dstep_chkBr`,
  `dstep_frameSet`, `argEq_chkRegs`, `argEq_ldStep`: the prologue keeps the
  argument registers `x0`…`x7`;
- `ProW.imp`, `ProW.w2`, `ProW.w2Part`: a prologue's obligations combined,
  `W2` from `SFacts` at the source start's control and `W2Part`;
- `proW_placedS`: the states placed from the entry's argument registers;
- `proW_noWr`: nothing written, off a system call;
- `proW_w2`: the prologue inside `W2` (`SFacts` by `proW_sfactsP`), the
  abort phase's facts a premise (`hab`), the placement from the entry
  (`hPl`), `main`'s `ret` excluded and `FrOk2` at the entry (`hJ`);
- `blkW_abSt_at`, `htgt_fall`, `proW_abSt`, `proW_abStC`: the abort phase's
  facts (`hab`) from the check label off the write abort's, the overflow
  target and the body's entry positions off it;
- `placedS_of_nilWords`, `lookupE_nil_words`: a control with no words placed
  everywhere;
- `proW_w2C`: `proW_w2` at a compiled block's code facts;
- `hpro_setup`: at `uN0` and the setup call's frame (caller's environment of
  no words, `hW0`);
- `hpro_main`: at an entry invariant inside `uNM` at no frames, the
  placement from `Pre` (`hPl`, e.g. `hPl_setupArgs`).
-/
import Spike.Lib.LowerA64.W2Body
import Spike.Lib.LowerA64.UserAbC
import Spike.Lib.A64AllocGAb
import Spike.Lib.LowerA64.UserW
import Spike.Lib.Rt.A64CodeInSetup
import Spike.Lib.LowerA64.ProgC2
import Spike.Lib.Rt.A64MainS
import Spike.Lib.LowerA64.SetupCall2

namespace Spike.Lib.LowerA64

set_option linter.unusedSimpArgs false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (abi)
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64Consumer (CFacts SFacts blkPh noRetBlk Own Lbl Lsize aiTgts)
open Spike.Lib.A64ConsumerS (PlacedS InvS envsOf)
open Spike.Lib.A64ConsumerA (AbSt WrAt noWr_load wrOkA_of_noWr)
open Spike.Lib.A64.Rt (InstOk argX)
open Spike.Lib.A64.Flow.Ret0 (StackOff limA tcbA_limA)
open Spike.Lib.A64.Flow.Ret0.Inst (cfacts_c0)
open Spike.Lib.A64.Rt.MainU (chkHead_noRet chkBr_noRet pc2 pc3 pc5)
open Spike.Lib.A64.AllocG (dumN)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Scc.Cert.Rt.A64 (blockAt label_labelGap)

/-! ## The argument registers -/

/-- **The argument registers `x0`…`x7` agree** from `r` to `r'`. -/
def ArgEq (r r' : Reg64s) : Prop := ∀ i < 8, r'.getXReg (argX i) = r.getXReg (argX i)

theorem ArgEq.refl (r : Reg64s) : ArgEq r r := fun _ _ => rfl

theorem ArgEq.trans {r r' r'' : Reg64s} (h1 : ArgEq r r') (h2 : ArgEq r' r'') : ArgEq r r'' :=
  fun i hi => (h2 i hi).trans (h1 i hi)

/-- Setting a register other than `x0`…`x7` keeps them. -/
theorem argEq_setXReg {r : Reg64s} {x : XReg} (hx : ∀ i < 8, argX i ≠ x) (v : BitVec 64) :
    ArgEq r (r.setXReg x v) := by
  intro i hi
  have := hx i hi
  revert this
  generalize argX i = y
  intro h
  cases x <;> cases y <;> first | exact absurd rfl h | rfl

/-- Setting `sp` keeps `x0`…`x7`. -/
theorem argEq_sp (r : Reg64s) (v : UInt64) : ArgEq r { r with SP := v } := by
  intro i hi
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl

/-- **An abstract run keeping `x0`…`x7` at every step keeps them at every
prefix.** -/
theorem argEq_arun_take (lab : Label → Int64) {blk : List Directive}
    (h : ∀ d ∈ blk, ∀ am : AM, ArgEq am.σ.regs (dstep lab am d).σ.regs) :
    ∀ (k : Nat) (am : AM), ArgEq am.σ.regs (arun lab (blk.take k) am).σ.regs := by
  induction blk with
  | nil => intro k am; simpa [arun] using ArgEq.refl _
  | cons d ds ih =>
    intro k am
    cases k with
    | zero => simpa [arun] using ArgEq.refl _
    | succ k =>
      have h1 := h d List.mem_cons_self am
      have h2 := ih (fun d' hd' => h d' (List.mem_cons_of_mem _ hd')) k (dstep lab am d)
      simp only [List.take_succ_cons, arun, List.foldl_cons] at h2 ⊢
      exact h1.trans h2

theorem dstep_chkHead (lab : Label → Int64) (Z : Int64) : ∀ d ∈ chkHead Z, ∀ am : AM,
    ArgEq am.σ.regs (dstep lab am d).σ.regs := by
  simp only [chkHead, List.mem_cons, List.not_mem_nil, or_false]
  rintro d (rfl | rfl) ⟨pc, o, σ⟩
  all_goals
    simp [dstep, Spike.Lib.A64.Flow.classify, RegOnly, AI.so, AI.step, AI.tgt, soReg, regRes,
    Operation.interp, MachineData.setRegOrSp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64, ConstExpr.interp,
    SO.set, ExtOrImmReg.interp, Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrSp.base, SO.get,
    MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, zrB, SO.write, SO.kill, SO.killZ, rm, regDst]
  all_goals exact argEq_setXReg (by decide) _

theorem dstep_chkBr (lab : Label → Int64) (L : Label) : ∀ d ∈ chkBr L, ∀ am : AM,
    ArgEq am.σ.regs (dstep lab am d).σ.regs := by
  simp only [chkBr, List.mem_cons, List.not_mem_nil, or_false]
  rintro d (rfl | rfl) ⟨pc, o, σ⟩
  all_goals
    simp [dstep, Spike.Lib.A64.Flow.classify, RegOnly, AI.so, AI.step, AI.tgt, soReg, regRes,
    Operation.interp, MachineData.setRegOrSp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64, ConstExpr.interp,
    SO.set, ExtOrImmReg.interp, Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrSp.base, SO.get,
    MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, zrB, SO.write, SO.kill, SO.killZ, rm, regDst]
  all_goals exact ArgEq.refl _

theorem dstep_frameSet (lab : Label → Int64) (Z : Int64) (ps : List (XReg × Int64)) :
    ∀ d ∈ frameSet Z ps, ∀ am : AM, ArgEq am.σ.regs (dstep lab am d).σ.regs := by
  intro d hd am
  simp only [frameSet, List.mem_append, List.mem_map] at hd
  rcases hd with hd | ⟨q, -, rfl⟩
  · simp only [frSetup, List.mem_cons, List.not_mem_nil, or_false] at hd
    obtain ⟨pc, o, σ⟩ := am
    rcases hd with rfl | rfl | rfl | rfl
    all_goals
      simp [dstep, Spike.Lib.A64.Flow.classify, RegOnly, AI.so, AI.step, AI.tgt, soReg, regRes, spStr,
      Reg64s.getRegOrZr_X,
      Operation.interp, MachineData.setRegOrSp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64, ConstExpr.interp,
      SO.set, ExtOrImmReg.interp, Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrSp.base, SO.get,
      MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, zrB, SO.write, SO.kill, SO.killZ, rm, regDst]
    · exact argEq_sp _ _
    · exact ArgEq.refl _
    · exact ArgEq.refl _
    · exact argEq_setXReg (by decide) _
  · obtain ⟨pc, o, σ⟩ := am
    rw [dstep_spStr]
    exact ArgEq.refl _

/-- `chkRegs` keeps `x0`…`x7`. -/
theorem argEq_chkRegs (Z : Int64) (r : Reg64s) : ArgEq r (chkRegs Z r) :=
  (argEq_setXReg (by decide) _).trans (argEq_setXReg (by decide) _)

/-- The limit's load into `x10` keeps `x0`…`x7`. -/
theorem argEq_ldStep (v : BitVec 64) (σ : AS) : ArgEq σ.regs (ldStep .X10 v σ).regs := by
  simp only [ldStep, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, zrB]
  exact argEq_setXReg (by decide) _

/-! ## Obligations combined -/

section Comb

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {K : State → State → Prop} {ms : MemSide isaLSE2} {pc0 Z lim : Int64} {L : Label} {ps : List (XReg × Int64)}
  {JE : AS → Ctl → Prop}

/-- **A prologue inside `W`** from one inside `W1` not moved by `K` and one
inside `W2'`, `W1 ∧ W2'` inside `W` (`BlkW.imp`, `NodeW.imp` per node). -/
theorem ProW.imp {W W1 W2' : Frag isaLSE2} (h1 : ProW W1 K exe endPc R F ms pc0 Z lim L ps JE)
    (h2 : ProW W2' (fun _ _ => False) exe endPc R F ms pc0 Z lim L ps JE) (hw : ∀ s c, W1 s c → W2' s c → W s c) :
    ProW W K exe endPc R F ms pc0 Z lim L ps JE :=
  ⟨A64.AllocG.BlkW.imp h1.w0 h2.w0 hw, A64.AllocG.NodeW.imp h1.w1 h2.w1 hw, A64.AllocG.BlkW.imp h1.w2 h2.w2 hw,
    A64.AllocG.BlkW.imp h1.w3 h2.w3 hw⟩

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS} {Dt Ab : State → Prop} {lbl lbl0 : Lbl}
  {lsize : Lsize} {fs : List TermRun.Frame}

/-- **A prologue inside `W2`** at the frames `fs` (`BlkW.w2`, `NodeW.w2`
per node): `SFacts` at the source start's control over the invariant's
states (`hS`), `W2Part` at the states, and at every control of the entry
invariant `JE` `main`'s `ret` excluded and `FrOk2`. -/
theorem ProW.w2 (hp : ProgNoS ZBad p)
    (hS : ProW (fun s c => SFacts Λ μ own rS Tk lbl0 s c) K exe endPc R F ms pc0 Z lim L ps
      (fun σ c => c = A64Consumer.c0 ∧ ∃ c', JE σ c'))
    (hP : ProW (W2Part Λ μ p rd G own ar J Ab lbl lsize fs) (fun _ _ => False) exe endPc R F ms pc0 Z lim L ps JE)
    (hJ : ∀ σ c, JE σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    ProW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F ms pc0 Z lim L ps JE := by
  refine ⟨BlkW.w2 (lbl0 := lbl0) hp (BlkW.mapC rfl rfl hS.w0 fun σ c h => ⟨c, h, fun _ h => h⟩) hP.w0 hJ,
    NodeW.w2 (lbl0 := lbl0) hp (NodeW.mapC (n' := proN1 pc0 Z _) rfl rfl hS.w1 ?_) hP.w1 ?_,
    BlkW.w2 (lbl0 := lbl0) hp (BlkW.mapC (n' := proN2 ms pc0 Z lim _) rfl rfl hS.w2 ?_) hP.w2 ?_,
    BlkW.w2 (lbl0 := lbl0) hp (BlkW.mapC (n' := proN3 ms pc0 Z lim _) rfl rfl hS.w3 ?_) hP.w3 ?_⟩
  · rintro σ1 c ⟨rfl, c1, σ, hJ', he⟩
    exact ⟨_, ⟨σ, ⟨rfl, c1, hJ'⟩, he⟩, fun _ h => h⟩
  · rintro σ1 c ⟨σ, hJ', -⟩
    exact hJ σ c hJ'
  · rintro σ2 c ⟨rfl, c1, σ, v, hJ', hg, he⟩
    exact ⟨_, ⟨σ, v, ⟨rfl, c1, hJ'⟩, hg, he⟩, fun _ h => h⟩
  · rintro σ2 c ⟨σ, v, hJ', -⟩
    exact hJ σ c hJ'
  · rintro σ3 c ⟨rfl, c1, σ, v, hJ', hg, he, hs⟩
    exact ⟨_, ⟨σ, v, ⟨rfl, c1, hJ'⟩, hg, he, hs⟩, fun _ h => h⟩
  · rintro σ3 c ⟨σ, v, hJ', -⟩
    exact hJ σ c hJ'

/-- **`W2Part` over a prologue** from the abort phase's facts (`hab`), the
placement (`hP`), and no write and no system call (`hN`). -/
theorem ProW.w2Part (hab : ProW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F ms pc0 Z lim L ps JE)
    (hP : ProW (fun s c => PlacedS Λ lbl s c fs) (fun _ _ => False) exe endPc R F ms pc0 Z lim L ps JE)
    (hN : ProW (fun s _ => (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false) (fun _ _ => False) exe endPc R F ms pc0 Z lim
      L ps JE) :
    ProW (W2Part Λ μ p rd G own ar J Ab lbl lsize fs) (fun _ _ => False) exe endPc R F ms pc0 Z lim L ps JE :=
  ProW.imp hab (ProW.imp (W := fun s c => PlacedS Λ lbl s c fs ∧ (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false)
    hP hN fun _ _ h1 h2 => ⟨h1, h2⟩) fun _ _ h1 h2 =>
    ⟨h1, h2.1, fun _ _ _ _ => wrOkA_of_noWr h2.2.1, fun h => absurd h (by rw [h2.2.2]; decide)⟩

/-- **A prologue's states placed** at the frames `fs`: every control of
the entry invariant `JE` placed at every state agreeing with the entry's
on `x0`…`x7` (`hPl`); the prologue writes none of them (`chkRegs`, the
limit's load into `x10`, the check's branch, the frame's set-up). -/
theorem proW_placedS
    (hPl : ∀ σ c, JE σ c → ∀ s : State, (∀ i < 8, s.st.1.regs.getXReg (argX i) = σ.regs.getXReg (argX i)) →
      PlacedS Λ lbl s c fs) :
    ProW (fun s c => PlacedS Λ lbl s c fs) (fun _ _ => False) exe endPc R F ms pc0 Z lim L ps JE := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s σ c _ _ _ _ _ _ hJ k _ m hA' _
    refine ⟨hPl σ c hJ _ fun i hi => ?_, fun _ h => h⟩
    show m.regs.getXReg _ = _
    rw [hA'.regs]
    exact argEq_arun_take _ (dstep_chkHead _ Z) k _ i hi
  · rintro s c ⟨-, -, -, -, σ1, hA, -, σ, hJ, rfl⟩
    refine ⟨hPl σ c hJ _ fun i hi => ?_, fun _ h => h⟩
    rw [hA.regs]
    exact argEq_chkRegs Z σ.regs i hi
  · rintro s σ2 c _ _ _ _ _ _ ⟨σ, v, hJ, -, rfl⟩ k _ m hA' _
    refine ⟨hPl σ c hJ _ fun i hi => ?_, fun _ h => h⟩
    show m.regs.getXReg _ = _
    rw [hA'.regs]
    exact ((argEq_chkRegs Z σ.regs).trans (argEq_ldStep _ _)).trans
      (argEq_arun_take _ (dstep_chkBr _ L) k _) i hi
  · rintro s σ3 c _ _ _ _ _ _ ⟨σ, v, hJ, -, he, -⟩ k _ m hA' _
    refine ⟨hPl σ c hJ _ fun i hi => ?_, fun _ h => h⟩
    show m.regs.getXReg _ = _
    rw [hA'.regs]
    have h3 : ArgEq σ.regs σ3.regs := by
      rw [he]; exact (argEq_chkRegs Z σ.regs).trans (argEq_ldStep _ _)
    exact (h3.trans (argEq_arun_take _ (dstep_frameSet _ Z ps) k _)) i hi

end Comb

/-! ## The prologue inside `W2` -/

section Pro

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS} {Dt Ab : State → Prop}
  {lsize : Lsize} {fs : List TermRun.Frame}

/-- **A stack-checked prologue writes nothing and is off a system call**:
its blocks (`blkW_noWr`, `blkW_noSys`) and the limit's load (`noWr_load`)
of a word unmapped under the frame condition (`hun`). -/
theorem proW_noWr {ms : MemSide isaLSE2} {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {fn sc entry : Label} {Z : Int64} {L : Label} {ps : List (XReg × Int64)}
    (hin : prologueIn prog fn sc entry Z 8 L ps = true)
    (hps : ∀ q ∈ ps, offOk (-Z.toInt) 0 (-Z.toInt + q.2.toInt) = true)
    {JE : AS → Ctl → Prop} {tp : UInt64} (htp : ∀ σ c, JE σ c → σ.regs.TPIDR_EL0 = tp)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -Z.toInt) (hhi : 0 ≤ R.hi) (h16 : Z.toInt % 16 = 0) (hZ : 16 ≤ Z.toInt)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none) :
    ProW (fun s _ => (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label fn) Z 8 L ps JE := by
  have h := hin
  simp only [prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hgap, bHd⟩, bLd⟩, bBr⟩, bFr⟩, -⟩ := h
  have esc := label_labelGap hI.lays hgap
  rw [hI.labOk] at esc
  have hBN : ∀ {n : ND} {blk : List Directive} {lo hi : Int} {l : Label} {k : Nat},
      blockAt prog l k blk = true → lab l + Int64.ofNat (4 * k) = n.pc → okBlk lo hi n.o blk = true →
      R.lo ≤ lo → hi ≤ R.hi →
      BlkW (fun s _ => (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false) (fun _ _ => False) exe endPc R F n blk :=
    fun hb he hok hlo' hhi' => A64.AllocG.BlkW.imp (A64.AllocG.blkW_noWr hI hb he hok hR hal hlo' hhi')
      (blkW_noSys hI hb he hok) fun _ _ h1 h2 => ⟨h1, h2⟩
  rw [hI.labOk]
  refine ⟨hBN bHd (by rw [esc, ofNat4_zero, ofNat4_zero]) (chkHead_ok _ _ _) hlo hhi, ?_,
    hBN bBr (by rw [esc, ofNat4_zero, pc3]; rfl) (chkBr_ok _ _ _ _) hlo hhi,
    hBN bFr (by rw [esc, ofNat4_zero, pc5]; rfl)
      (frameSet_ok (lo := -Z.toInt) (hi := 0) h16 hZ (by omega) (Int.le_refl _) hps) hlo hhi⟩
  rintro s c ⟨hs, hn, hdc, hpc, σ1, hA, hD, σ, hJ, rfl⟩
  have hpc' : s.st.2 = lab sc + Int64.ofNat (4 * 2) := by
    rw [hpc]; show _ + 4 + 4 = _; rw [esc, ofNat4_zero, pc2]
  have hc := A64.Rt.cellOf hI bLd rfl hs hn hpc'
  have ha' : rAddr s.st.1.regs .X10 8 = limA tp := by
    rw [hA.regs, rAddr_chkRegs]; exact tcbA_limA (htp _ _ hJ)
  have hex := exec_ldr_agrees hc ha' (hun _ hD) (agrees_of_decls hdc _ _)
  exact ⟨⟨noWr_load hex, Scc.Sem.A64.atSvc_false_of_cellAt hc (by intro imm h; cases h)⟩, fun _ h => h⟩

/-- **A stack-checked prologue is inside `W2`** at the frames `fs` (for
any frame `Z`): `SFacts` from `proW_sfactsP` at the source start's
control, nothing written and off a system call (`proW_noWr`), the abort
phase's facts a premise (`hab`), the states placed from the entry's
argument registers (`hPl`, `proW_placedS`), and at every control of the
entry invariant `JE` `main`'s `ret` excluded and `FrOk2` (`hJ`). -/
theorem proW_w2 {ms : MemSide isaLSE2} {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {fn sc entry : Label} {Z : Int64} {L : Label} {ps : List (XReg × Int64)}
    (hin : prologueIn prog fn sc entry Z 8 L ps = true)
    (hps : ∀ q ∈ ps, offOk (-Z.toInt) 0 (-Z.toInt + q.2.toInt) = true)
    {JE : AS → Ctl → Prop} {tp : UInt64} (htp : ∀ σ c, JE σ c → σ.regs.TPIDR_EL0 = tp)
    (hph : ProPh okPc ph lab sc Z L ps)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -Z.toInt) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (h16 : Z.toInt % 16 = 0) (hZ : 16 ≤ Z.toInt)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hp : ProgNoS ZBad p)
    (hab : ProW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label fn) Z 8 L ps JE)
    (hPl : ∀ σ c, JE σ c → ∀ s : State, (∀ i < 8, s.st.1.regs.getXReg (argX i) = σ.regs.getXReg (argX i)) →
      PlacedS Λ lbl s c fs)
    (hJ : ∀ σ c, JE σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    ProW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F ms
      ((_root_.Executable.labels exe).label fn) Z 8 L ps JE := by
  have hS := proW_sfactsP (lbl := lbl) (ms := ms) (J := fun σ c => c = A64Consumer.c0 ∧ ∃ c', JE σ c') hI hin hps
    cfacts_c0 (fun _ _ h => h.1) (fun σ _ ⟨_, c', h⟩ => htp σ c' h) hph hR hal hlo hhi hl hh h16 hZ hmr hun hsub
    hfit hFO
  exact ProW.w2 hp hS (ProW.w2Part hab (proW_placedS hPl)
    (proW_noWr hI hin hps htp hR hal hlo hhi h16 hZ hun)) hJ

end Pro

/-! ## The abort phase over the prologue -/

section Ab

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat}

/-- **A block after a label off the write abort's keeps its phase**
(`blkW_abSt_pos`): `j` instructions after the label `sc` none of `abLabs`
(`hb`, `hsc`) at its node's pc (`he`), the position right after it off the
write abort (`hend`), every target but a fall-through off it (`htgt`). -/
theorem blkW_abSt_at {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habt : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {R : Region} {F : MachineData → Prop} {n : ND} {blk : List Directive} {lo hi : Int} {sc : Label} {j : Nat}
    (hb : blockAt prog sc j blk = true) (hsc : sc ∉ A64.AllocG.abLabs) (he : lab sc + Int64.ofNat (4 * j) = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo)
    (hhi : hi ≤ R.hi) (hph : blkPh okPc ph (fun _ => false) lab n.pc 0 blk = true) (hnr : noRetBlk blk = true)
    (hend : PosOff prog lab (lab sc + Int64.ofNat (4 * (j + blk.length))))
    (htgt : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, A64.Flow.classify blk[k] = some a →
      ∀ t ∈ aiTgts lab (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4) 0 a,
        t ≠ n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4 → PosOff prog lab t) :
    BlkW (fun s _ => AbSt μ (A64.WriteAb.Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  have hcode := code_of hI.lays hI.endOk hb (q := n.pc) (by rw [hI.labOk]; exact he)
  refine blkW_abSt_pos hI hpr habt hcode hok hR hal hlo hhi hph hnr ?_
  intro σ c hJ k hk a ha t ht
  by_cases hf : t = n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4
  · refine .inl ?_
    have hf' : t = lab sc + Int64.ofNat (4 * (j + (k + 1))) := by rw [hf, ofNat4_add, he, ofNat4_succ]; rfl
    rw [hf']
    rcases Nat.lt_or_ge (k + 1) blk.length with h1 | h1
    · exact posOff_of_blockAt hb hsc h1
    · rw [show k + 1 = blk.length by omega]
      exact hend
  · exact .inl (htgt σ c hJ k hk a ha t ht hf)

/-- **A block of fall-throughs has no other target.** -/
theorem htgt_fall {lab : Label → Int64} {pc : Int64} {blk : List Directive} (hf : fallBlk blk = true)
    {P : Int64 → Prop} : ∀ k (hk : k < blk.length) a, A64.Flow.classify blk[k] = some a →
      ∀ t ∈ aiTgts lab (pc + Int64.ofNat (4 * k) + Int64.ofNat 4) 0 a,
        t ≠ pc + Int64.ofNat (4 * k) + Int64.ofNat 4 → P t := by
  intro k hk a ha t ht hne
  have := fallBlk_get hf hk ha
  cases a <;> simp only [fallI, Bool.false_eq_true] at this <;>
    simp only [aiTgts, List.mem_singleton] at ht <;> exact absurd ht hne

theorem fallBlk_chkHead (Z : Int64) : fallBlk (chkHead Z) = true := by
  simp [fallBlk, chkHead, Spike.Lib.A64.Flow.classify, RegOnly, fallI]

theorem fallBlk_frameSet (Z : Int64) (ps : List (XReg × Int64)) : fallBlk (frameSet Z ps) = true := by
  simp [fallBlk, frameSet, frSetup, spStr, Spike.Lib.A64.Flow.classify, RegOnly, fallI]

/-- **A stack-checked prologue keeps the write abort's phase**: its check
label `sc` none of the write abort's (`hsc`, e.g. `local_not_abLabs`), the
overflow target `L` and the body's first position off the write abort
(`hL`, `hent`); every block by `blkW_abSt_at`, the limit's load falling
through to the branch. -/
theorem proW_abSt {ms : MemSide isaLSE2} {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habt : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {fn sc entry : Label} {Z : Int64} {L : Label} {ps : List (XReg × Int64)}
    (hin : prologueIn prog fn sc entry Z 8 L ps = true)
    (hps : ∀ q ∈ ps, offOk (-Z.toInt) 0 (-Z.toInt + q.2.toInt) = true) (hph : ProPh okPc ph lab sc Z L ps)
    (hsc : sc ∉ A64.AllocG.abLabs) (hL : PosOff prog lab (lab L))
    (hent : PosOff prog lab (lab sc + Int64.ofNat (4 * (5 + (frameSet Z ps).length))))
    {JE : AS → Ctl → Prop} {tp : UInt64} (htp : ∀ σ c, JE σ c → σ.regs.TPIDR_EL0 = tp)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -Z.toInt) (hhi : 0 ≤ R.hi) (h16 : Z.toInt % 16 = 0) (hZ : 16 ≤ Z.toInt)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none) :
    ProW (fun s _ => AbSt μ (A64.WriteAb.Ab lab) s) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label fn) Z 8 L ps JE := by
  have h := hin
  simp only [prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hgap, bHd⟩, bLd⟩, bBr⟩, bFr⟩, -⟩ := h
  have esc := label_labelGap hI.lays hgap
  rw [hI.labOk] at esc
  have hBr : PosOff prog lab (lab sc + Int64.ofNat (4 * (3 + 0))) := posOff_of_blockAt bBr hsc (by simp [chkBr])
  have hFr : PosOff prog lab (lab sc + Int64.ofNat (4 * (5 + 0))) :=
    posOff_of_blockAt bFr hsc (by simp [frameSet, frSetup])
  have hLd : PosOff prog lab (lab sc + Int64.ofNat (4 * (2 + 0))) := posOff_of_blockAt bLd hsc (by simp)
  rw [hI.labOk]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have he : lab sc + Int64.ofNat (4 * 0) = lab fn := by rw [esc, ofNat4_zero, ofNat4_zero]
    refine blkW_abSt_at hI hpr habt bHd hsc he (chkHead_ok _ _ _) hR hal hlo hhi (he ▸ hph.hd)
      (chkHead_noRet _) hLd (fun _ _ _ => htgt_fall (fallBlk_chkHead Z))
  · rintro s c ⟨hs, hn, hdc, hpc, σ1, hA, hD, σ, hJ, rfl⟩
    have hp2 : lab fn + 4 + 4 = lab sc + Int64.ofNat (4 * 2) := by rw [esc, ofNat4_zero, pc2]
    have hpc' : s.st.2 = lab sc + Int64.ofNat (4 * 2) := by rw [hpc]; exact hp2
    have hc := A64.Rt.cellOf hI bLd rfl hs hn hpc'
    have ha' : rAddr s.st.1.regs .X10 8 = limA tp := by
      rw [hA.regs, rAddr_chkRegs]; exact tcbA_limA (htp _ _ hJ)
    have hex := exec_ldr_agrees hc ha' (hun _ hD) (agrees_of_decls hdc _ _)
    have hok : okPc (Scc.Sem.A64.pcOf s) = true := by unfold Scc.Sem.A64.pcOf; rw [hpc']; exact hph.ld.1
    have hP := (hI.off s hok).1
    have hnx : lab sc + Int64.ofNat (4 * 2) + Int64.ofNat 4 ∉ A64.WriteAb.abPcs lab := by
      have := notAbPc_of_posOff hI.lays hpr habt (hI.labOk ▸ hBr)
      rw [hI.labOk] at this
      rwa [show lab sc + Int64.ofNat (4 * (3 + 0)) = lab sc + Int64.ofNat (4 * 2) + Int64.ofNat 4 by
        rw [show 3 + 0 = 2 + 1 from rfl, ofNat4_succ]; rfl] at this
    refine ⟨Spike.Lib.A64ConsumerA.AbSt.ofLeaves hP.noTake
      (Scc.Sem.A64.atSvc_false_of_cellAt hc (by intro imm h; cases h))
      fun tr ht => ?_, fun _ h => h⟩
    rw [hex] at ht
    cases ht
    exact fun _ _ => A64.AllocG.not_ab_after hpc' hnx
  · have he : lab sc + Int64.ofNat (4 * 3) = lab fn + 4 + 4 + 4 := by rw [esc, ofNat4_zero, pc3]
    refine blkW_abSt_at hI hpr habt bBr hsc he (chkBr_ok _ _ _ _) hR hal hlo hhi
      (by show blkPh _ _ _ _ (lab fn + 4 + 4 + 4) _ _ = true; rw [← he]; exact hph.br)
      (chkBr_noRet _) hFr ?_
    intro σ c _ k hk a ha t ht hne
    match k, hk with
    | 0, _ =>
      simp [chkBr, Spike.Lib.A64.Flow.classify, RegOnly] at ha
      subst ha
      simp only [aiTgts, List.mem_singleton] at ht
      exact absurd ht hne
    | 1, _ =>
      simp [chkBr, Spike.Lib.A64.Flow.classify] at ha
      subst ha
      simp only [aiTgts, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | ht
      · exact hL
      · exact absurd ht hne
  · have he : lab sc + Int64.ofNat (4 * 5) = lab fn + 4 + 4 + 4 + 4 + 4 := by rw [esc, ofNat4_zero, pc5]
    exact blkW_abSt_at hI hpr habt bFr hsc he
      (frameSet_ok (lo := -Z.toInt) (hi := 0) h16 hZ (by omega) (Int.le_refl _) hps) hR hal hlo hhi
      (by show blkPh _ _ _ _ (lab fn + 4 + 4 + 4 + 4 + 4) _ _ = true; rw [← he]; exact hph.fr)
      (frameSet_noRet _ _) hent (fun _ _ _ => htgt_fall (fallBlk_frameSet Z ps))

end Ab

/-! ## At a compiled block's prologue -/

/-- **A control with no words is placed** at every state: every
environment of the control and its frames binds no word. -/
theorem placedS_of_nilWords {Λ : Scc.Sem.Layout} {lbl : Lbl} {c : Ctl} {fs : List TermRun.Frame}
    (h : ∀ env ∈ envsOf c fs, ∀ x ty ws, TermRun.lookupE env x = some (ty, ws) → ws = []) (s : State) :
    PlacedS Λ lbl s c fs := by
  refine ⟨fun _ _ _ => none, fun _ _ _ _ _ _ _ _ _ _ _ h => by simp at h, ?_, fun _ _ _ _ _ _ h => by simp at h⟩
  intro d env xs hd _ x _ ty ws hl k hk
  rw [h env (List.mem_of_getElem? hd) x ty ws hl] at hk
  exact absurd hk (Nat.not_lt_zero _)

/-- A one-binding environment of no words binds no word. -/
theorem lookupE_nil_words {a : String} {t : Ty} {x : String} {ty : Ty} {ws : List TermRun.Word}
    (h : TermRun.lookupE [(a, t, [])] x = some (ty, ws)) : ws = [] := by
  simp only [TermRun.lookupE, List.find?] at h
  split at h <;> simp_all

section Code

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS} {Dt Ab : State → Prop}
  {lsize : Lsize} {fs : List TermRun.Frame}
  {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
  {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}

/-- **A compiled block's prologue inside `W2`** (`CalleePre2.hpro` at
`W2`, `proW_w2` at its frame `cx.frame` and spill `ps`): as `proW_w2`,
the frame's bounds from the block's code facts `c`. -/
theorem proW_w2C (c : FnCode2 exe prog endPc RaOk Cd i T d) {ms : MemSide isaLSE2} {kp : Nat}
    (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {JE : AS → Ctl → Prop} {tp : UInt64} (htp : ∀ σ c, JE σ c → σ.regs.TPIDR_EL0 = tp)
    (hph : ProPh okPc ph lab (c.cx.local "stack_check") (Int64.ofInt c.cx.frame) (proL c.cx) c.ps)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -(c.cx.frame : Int)) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hp : ProgNoS ZBad p)
    (hab : ProW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.cx.frame) (Int64.ofNat Scc.IR.Tcb.stackLimit)
      (proL c.cx) c.ps JE)
    (hPl : ∀ σ c, JE σ c → ∀ s : State, (∀ i < 8, s.st.1.regs.getXReg (argX i) = σ.regs.getXReg (argX i)) →
      PlacedS Λ lbl s c fs)
    (hJ : ∀ σ c, JE σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    ProW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F ms
      ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.cx.frame) (Int64.ofNat Scc.IR.Tcb.stackLimit)
      (proL c.cx) c.ps JE := by
  have hge := frame_ge16 c.hf
  have h1 := c.h1
  have h16 := c.h16
  have hF64 : (Int64.ofInt c.cx.frame).toInt = c.cx.frame := toInt_ofInt_small (by omega) (by omega)
  exact proW_w2 hI c.hpro c.hps htp hph hR hal (by rw [hF64]; exact hlo) hhi hl hh (by rw [hF64]; omega)
    (by rw [hF64]; omega) hmr hun hsub hfit hFO hp hab hPl hJ

/-- **A compiled block's prologue keeps the write abort's phase**
(`proW_abSt` at its frame and spill): its function index none of the
runtime's (`hfi`, so its check label is off the write abort's,
`local_not_abLabs`), the overflow target and the body's entry positions off
the write abort (`hL`, `hent`). -/
theorem proW_abStC (c : FnCode2 exe prog endPc RaOk Cd i T d) {ms : MemSide isaLSE2} {kp : Nat}
    (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habt : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : ProPh okPc ph lab (c.cx.local "stack_check") (Int64.ofInt c.cx.frame) (proL c.cx) c.ps)
    (hfi : c.cx.fi ≠ 9 ∧ c.cx.fi ≠ 12 ∧ c.cx.fi ≠ 16) (hL : PosOff prog lab (lab (proL c.cx)))
    (hent : PosOff prog lab (lab c.entry))
    {JE : AS → Ctl → Prop} {tp : UInt64} (htp : ∀ σ c, JE σ c → σ.regs.TPIDR_EL0 = tp)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -(c.cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none) :
    ProW (fun s _ => AbSt μ (A64.WriteAb.Ab lab) s) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.cx.frame) (Int64.ofNat Scc.IR.Tcb.stackLimit)
      (proL c.cx) c.ps JE := by
  have hge := frame_ge16 c.hf
  have h1 := c.h1
  have h16 := c.h16
  have hF64 : (Int64.ofInt c.cx.frame).toInt = c.cx.frame := toInt_ofInt_small (by omega) (by omega)
  have h := c.hpro
  simp only [prologueIn, Bool.and_eq_true] at h
  obtain ⟨-, hgap⟩ := h
  have hen := label_labelGap hI.lays hgap
  rw [hI.labOk] at hen
  have hlen : 5 + (frameSet (Int64.ofInt c.cx.frame) c.ps).length = 9 + c.ps.length := by
    simp [frameSet, frSetup]; omega
  exact proW_abSt hI hpr habt c.hpro c.hps hph (local_not_abLabs hfi _) hL (by rw [hlen, ← hen]; exact hent)
    htp hR hal (by rw [hF64]; exact hlo) hhi (by rw [hF64]; omega) (by rw [hF64]; omega) hun

/-- **The setup function's prologue inside `W2`** at the setup call's
frame `fr` (`setupCallWS_ofFnSpec`'s `CalleePre2.hpro`, at the entry
`uN0`): as `proW_w2C`; the callee's control `g.c0` the call's (`hct`)
binding the unit parameter to no word (`hcE`), the caller's environment
binding no word (`hW0`), so every state is placed (`placedS_of_nilWords`);
`FrOk2` at the call a premise (`hfo`). -/
theorem hpro_setup (c : FnCode2 exe prog endPc RaOk Cd i T d) {ms : MemSide isaLSE2} {kp : Nat}
    (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {ms0 : MemSide isaLSE2} {F0 : MachineData → Prop} {fn : Label} {ZU : Int64} {g : Spike.Lib.A64.Flow.Ret0.WcG}
    {c0 : Ctl} {fr : TermRun.Frame}
    (hph : ProPh okPc ph lab (c.cx.local "stack_check") (Int64.ofInt c.cx.frame) (proL c.cx) c.ps)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -(c.cx.frame : Int)) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) false ⟨limA g.tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA g.tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hp : ProgNoS ZBad p)
    (hab : ProW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.cx.frame) (Int64.ofNat Scc.IR.Tcb.stackLimit)
      (proL c.cx) c.ps (Spike.Lib.A64.Rt.uN0 (_root_.Executable.labels exe).label ms0 F0 exe endPc fn ZU g).J)
    (hct : CallTo p c0 g.c0 fr) (hcE : g.c0 = ⟨d.body, [(d.arg, d.argTy, [])], none⟩)
    (hW0 : ∀ x ty ws, TermRun.lookupE c0.env x = some (ty, ws) → ws = []) (hfo : FrOk2 g.c0 [fr]) :
    ProW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c [fr]) K exe endPc R F ms
      ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.cx.frame) (Int64.ofNat Scc.IR.Tcb.stackLimit)
      (proL c.cx) c.ps (Spike.Lib.A64.Rt.uN0 (_root_.Executable.labels exe).label ms0 F0 exe endPc fn ZU g).J := by
  have hfr : fr.env = c0.env := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, -, rfl⟩ := hct
    rfl
  have hpl : ∀ s, PlacedS Λ lbl s g.c0 [fr] := placedS_of_nilWords fun env henv x ty ws hl => by
    simp only [envsOf, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at henv
    rcases henv with rfl | rfl
    · rw [hcE] at hl; exact lookupE_nil_words hl
    · rw [hfr] at hl; exact hW0 x ty ws hl
  refine proW_w2C c hI (fun _ _ h => h.1.2.2.2.2) hph hR hal hlo hhi hl hh hmr hun hsub hfit hFO hp hab
    (fun _ _ h s _ => h.1.1 ▸ hpl s) fun _ _ h => ⟨fun h' => (List.cons_ne_nil _ _ h').elim, h.1.1 ▸ hfo⟩

/-- **`main`'s prologue inside `W2`** after the setup block, at no frames
(`mainCallWSF_ofHeld`'s `CalleePre2.hpro`): as `proW_w2C` at an entry
invariant `JE` inside the entry `uNM` with its arguments `Pre` (`hJE`); a
control and registers of `Pre` placed at every state agreeing on
`x0`…`x7` (`hPl`, e.g. `hPl_setupArgs`), not at a `ret` (`hnr`) and free of
`ZBad` (`hfo`). -/
theorem hpro_main (c : FnCode2 exe prog endPc RaOk Cd i T d) {ms : MemSide isaLSE2} {kp : Nat}
    (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {ms0 : MemSide isaLSE2} {F0 : MachineData → Prop} {fn : Label} {ZU : Int64} {g : Spike.Lib.A64.Flow.Ret0.WcG}
    {Pre : Ctl → Reg64s → Prop} {JE : AS → Ctl → Prop}
    (hJE : ∀ σ c, JE σ c →
      (Spike.Lib.A64.Rt.uNM (_root_.Executable.labels exe).label ms0 F0 exe endPc fn ZU Pre g).J σ c)
    (hph : ProPh okPc ph lab (c.cx.local "stack_check") (Int64.ofInt c.cx.frame) (proL c.cx) c.ps)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -(c.cx.frame : Int)) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) false ⟨limA g.tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA g.tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hp : ProgNoS ZBad p)
    (hab : ProW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.cx.frame) (Int64.ofNat Scc.IR.Tcb.stackLimit)
      (proL c.cx) c.ps JE)
    (hPl : ∀ c (regs : Reg64s), Pre c regs → ∀ s : State,
      (∀ i < 8, s.st.1.regs.getXReg (argX i) = regs.getXReg (argX i)) → PlacedS Λ lbl s c [])
    (hnr : ∀ c regs, Pre c regs → ∀ a, c.term ≠ .ret a) (hfo : ∀ c regs, Pre c regs → FrOk2 c []) :
    ProW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c []) K exe endPc R F ms
      ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.cx.frame) (Int64.ofNat Scc.IR.Tcb.stackLimit)
      (proL c.cx) c.ps JE :=
  proW_w2C c hI (fun σ c h => (hJE σ c h).1.2.2.2.2) hph hR hal hlo hhi hl hh hmr hun hsub hfit hFO hp hab
    (fun σ c h => hPl c σ.regs (hJE σ c h).1.1)
    fun σ c h => ⟨fun _ => hnr c σ.regs (hJE σ c h).1.1, hfo c σ.regs (hJE σ c h).1.1⟩

end Code

/-! ## `main`'s entry not at a `ret` -/

/-- **A body ending in a held call is not a `ret`** (`heldRetOk`, the
narrowed `mainRetOk`'s). -/
theorem heldRetOk_not_ret {e : Expr} (h : Scc.Lower.heldRetOk e = true) : ∀ a, e ≠ .ret a := by
  rintro a rfl
  simp [Scc.Lower.heldRetOk] at h

/-- **`hpro_main`'s `hnr` at the setup block's arguments** (`Pre :=
SetupArgs (SPostC p lbl ty c0) sw x0`): the control after the setup call
is the call's rest, not a `ret` when every call `c0` makes continues off a
`ret` (`hE`, e.g. by `heldRetOk_not_ret`). -/
theorem hnr_setupArgs {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ty : Ty} {c0 : Ctl} {sw : Nat}
    {x0 : BitVec 64} (hE : ∀ x f a e, c0.term = .let_ x (.call f [] a []) e → ∀ b, e ≠ .ret b) :
    ∀ c regs, Spike.Lib.A64.Rt.SetupArgs (SPostC p lbl ty c0) sw x0 c regs → ∀ a, c.term ≠ .ret a := by
  rintro c regs ⟨rs, ⟨cE, fr, cr, a', t, ws, ⟨x, f, a, e, d, t', ws', ht, -, -, -, rfl⟩, -, -, -, rfl⟩, -, -⟩
  exact hE x f a e ht

/-- **At the program's start before a setup block the setup call's rest is
no `ret`** (`hnr_setupArgs`'s `hE`): the rest of `setupTerm`'s call of
`rodata` pairs its result with `me` before entering `main`. The start's
control (`th02` under `setupOf p = some _`) has this term. -/
theorem hE_setupTerm {c0 : Ctl} (hc : c0.term = Scc.Sem.SrcSem.setupTerm) :
    ∀ x f a e, c0.term = .let_ x (.call f [] a []) e → ∀ b, e ≠ .ret b := by
  intro x f a e ht b he
  rw [hc, he] at ht
  simp [Scc.Sem.SrcSem.setupTerm] at ht

/-- **`hpro_main`'s `hnr` at the program's start before a setup block**
(`hnr_setupArgs` at `hE_setupTerm`). -/
theorem hnr_setupTerm {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ty : Ty} {c0 : Ctl} {sw : Nat}
    {x0 : BitVec 64} (hc : c0.term = Scc.Sem.SrcSem.setupTerm) :
    ∀ c regs, Spike.Lib.A64.Rt.SetupArgs (SPostC p lbl ty c0) sw x0 c regs → ∀ a, c.term ≠ .ret a :=
  hnr_setupArgs (hE_setupTerm hc)

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.ArgEq.trans' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.ArgEq.trans
/-- info: 'Spike.Lib.LowerA64.argEq_arun_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.argEq_arun_take
/-- info: 'Spike.Lib.LowerA64.dstep_chkHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.dstep_chkHead
/-- info: 'Spike.Lib.LowerA64.dstep_chkBr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.dstep_chkBr
/-- info: 'Spike.Lib.LowerA64.dstep_frameSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.dstep_frameSet
/-- info: 'Spike.Lib.LowerA64.ProW.imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.ProW.imp
/-- info: 'Spike.Lib.LowerA64.ProW.w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.ProW.w2
/-- info: 'Spike.Lib.LowerA64.ProW.w2Part' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.ProW.w2Part
/-- info: 'Spike.Lib.LowerA64.proW_placedS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.proW_placedS
/-- info: 'Spike.Lib.LowerA64.proW_noWr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.proW_noWr
/-- info: 'Spike.Lib.LowerA64.proW_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.proW_w2
/-- info: 'Spike.Lib.LowerA64.blkW_abSt_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.blkW_abSt_at
/-- info: 'Spike.Lib.LowerA64.proW_abSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.proW_abSt
/-- info: 'Spike.Lib.LowerA64.proW_abStC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.proW_abStC
/-- info: 'Spike.Lib.LowerA64.placedS_of_nilWords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.placedS_of_nilWords
/-- info: 'Spike.Lib.LowerA64.proW_w2C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.proW_w2C
/-- info: 'Spike.Lib.LowerA64.hpro_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hpro_setup
/-- info: 'Spike.Lib.LowerA64.hpro_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hpro_main

/-- info: 'Spike.Lib.LowerA64.heldRetOk_not_ret' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.heldRetOk_not_ret

/-- info: 'Spike.Lib.LowerA64.hnr_setupArgs' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hnr_setupArgs

/-- info: 'Spike.Lib.LowerA64.hE_setupTerm' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hE_setupTerm

/-- info: 'Spike.Lib.LowerA64.hnr_setupTerm' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hnr_setupTerm
