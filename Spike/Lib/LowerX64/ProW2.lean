import Spike.Lib.LowerX64.W2Body
import Spike.Lib.LowerX64.UserW
import Spike.Lib.Rt.X64CodeInSetup
import Spike.Lib.LowerX64.ProgC2
import Spike.Lib.Rt.X64MainS
import Spike.Lib.LowerX64.SetupCall2
import Spike.Lib.LowerX64.UserAbC
import Spike.Lib.LowerX64.StubAbW2
import Spike.Lib.X64AllocGAb
import Spike.Lib.LowerX64.UserLabs

namespace Spike.Lib.LowerX64

set_option linter.unusedSimpArgs false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (abi)
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow (XProW xProN1 xProN2 xProN3 xProN4 xHead xLea xCmp xFr xHead_ok xLea_ok xCmp_ok xFr_ok
  xS1 xS2 xS3 hdRegs prologueIn ofNat_add' xSt CallTo)
open Spike.Lib.X64Consumer (CFacts SFacts blkPh noRetBlk Own Lbl Lsize K0)
open Spike.Lib.X64ConsumerS (PlacedS InvS envsOf)
open Spike.Lib.X64ConsumerA (AbSt WrAt noWr_load wrOkA_of_noWr)
open Spike.Lib.X64.Rt (InstOk argXs)
open Spike.Lib.X64.Flow.Ret0 (StackOff limA)
open Spike.Lib.X64.Flow.Ret0.Inst (cfacts_c0)
open Spike.Lib.X64.Rt.MainU (xHead_noRet xLea_noRet xCmp_noRet xFr_noRet)
open Spike.Lib.X64.AllocG (dumN)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Scc.Cert.Rt.X64 (blockAtB label_labelGapB)

/-! ## The argument registers -/

/-- **The argument registers `%rdi`…`%r9` agree** from `r` to `r'`. -/
def ArgEq (r r' : Reg64s) : Prop := ∀ i < 6, r'.get64 (argXs.getD i .rdi) = r.get64 (argXs.getD i .rdi)

theorem ArgEq.refl (r : Reg64s) : ArgEq r r := fun _ _ => rfl

theorem ArgEq.trans {r r' r'' : Reg64s} (h1 : ArgEq r r') (h2 : ArgEq r' r'') : ArgEq r r'' :=
  fun i hi => (h2 i hi).trans (h1 i hi)

/-- Setting a register other than the argument registers keeps them. -/
theorem argEq_set64 {r : Reg64s} {x : Reg64} (hx : ∀ i < 6, argXs.getD i .rdi ≠ x) (v : BitVec 64) :
    ArgEq r (r.set64 x v) := by
  intro i hi
  have := hx i hi
  revert this
  generalize argXs.getD i .rdi = y
  intro h
  cases x <;> cases y <;> first | exact absurd rfl h | rfl

/-- **An abstract run keeping the argument registers at every step keeps
them at every prefix.** -/
theorem argEq_arun_take (lab : Label → Int64) {blk : List (Directive × Nat)}
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

theorem dstep_xHead (lab : Label → Int64) : ∀ d ∈ xHead, ∀ am : AM,
    ArgEq am.σ.regs (dstep lab am d).σ.regs := by
  simp only [xHead, List.mem_cons, List.not_mem_nil, or_false]
  rintro d (rfl | rfl) ⟨pc, o, σ⟩
  all_goals
    simp [dstep, Spike.Lib.X64.classify, RegOnly, AI.so, soReg, regDst, regRes,
    Operation.interp, Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg,
    Reg64s.set, ConstExpr.interp, AddrExpr.interp, SO.get, SO.set, SO.kill, SO.write, lk, rm,
    Reg.base, BlockSpec.AI.step_ld', BlockSpec.AI.step_st', BlockSpec.AI.step_push',
    BlockSpec.AI.step_pop', BlockSpec.AI.step_reg', upd_apply, Reg64s.get_low64]
  all_goals first | exact ArgEq.refl _ | exact argEq_set64 (by decide) _

theorem dstep_xLea (lab : Label → Int64) (Z : Int64) (z : Nat) : ∀ d ∈ xLea Z z, ∀ am : AM,
    ArgEq am.σ.regs (dstep lab am d).σ.regs := by
  simp only [xLea, List.mem_cons, List.not_mem_nil, or_false]
  rintro d rfl ⟨pc, o, σ⟩
  simp [dstep, Spike.Lib.X64.classify, RegOnly, AI.so, soReg, regDst, regRes,
    Operation.interp, Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg,
    Reg64s.set, ConstExpr.interp, AddrExpr.interp, SO.get, SO.set, SO.kill, SO.write, lk, rm,
    Reg.base, BlockSpec.AI.step_ld', BlockSpec.AI.step_st', BlockSpec.AI.step_push',
    BlockSpec.AI.step_pop', BlockSpec.AI.step_reg', upd_apply, Reg64s.get_low64]
  exact argEq_set64 (by decide) _

theorem dstep_xCmp (lab : Label → Int64) (L : Label) (z1 z2 : Nat) : ∀ d ∈ xCmp L z1 z2, ∀ am : AM,
    ArgEq am.σ.regs (dstep lab am d).σ.regs := by
  simp only [xCmp, List.mem_cons, List.not_mem_nil, or_false]
  rintro d (rfl | rfl) ⟨pc, o, σ⟩
  all_goals
    simp [dstep, Spike.Lib.X64.classify, RegOnly, AI.so, soReg, regDst, regRes,
    Operation.interp, Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg,
    Reg64s.set, ConstExpr.interp, AddrExpr.interp, SO.get, SO.set, SO.kill, SO.write, lk, rm,
    Reg.base, BlockSpec.AI.step_ld', BlockSpec.AI.step_st', BlockSpec.AI.step_push',
    BlockSpec.AI.step_pop', BlockSpec.AI.step_reg', BlockSpec.AI.step_jcc', upd_apply, Reg64s.get_low64]
  all_goals first | exact ArgEq.refl _ | exact argEq_set64 (by decide) _

theorem dstep_xFr (lab : Label → Int64) (Z : Int64) (z : Nat) (ps : List (Reg64 × Int64 × Nat)) :
    ∀ d ∈ xFr Z z ps, ∀ am : AM, ArgEq am.σ.regs (dstep lab am d).σ.regs := by
  intro d hd ⟨pc, o, σ⟩
  simp only [xFr, List.mem_cons, List.mem_map] at hd
  rcases hd with rfl | ⟨q, -, rfl⟩
  all_goals
    simp [dstep, xSt, Spike.Lib.X64.classify, RegOnly, AI.so, soReg, regDst, regRes,
    Operation.interp, Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg,
    Reg64s.set, ConstExpr.interp, AddrExpr.interp, SO.get, SO.set, SO.kill, SO.write, lk, rm,
    Reg.base, BlockSpec.AI.step_ld', BlockSpec.AI.step_st', BlockSpec.AI.step_push',
    BlockSpec.AI.step_pop', BlockSpec.AI.step_reg', upd_apply, Reg64s.get_low64]
  all_goals first | exact ArgEq.refl _ | exact argEq_set64 (by decide) _

/-- The head keeps the argument registers. -/
theorem argEq_xS1 (σ : AS) : ArgEq σ.regs (xS1 σ).regs :=
  (argEq_set64 (by decide) _).trans (argEq_set64 (by decide) _)

/-- The check's address keeps the argument registers. -/
theorem argEq_xS2 (Z : Int64) (σ : AS) : ArgEq σ.regs (xS2 Z σ).regs :=
  (argEq_xS1 σ).trans (argEq_set64 (by decide) _)

/-- The limit's load into `%r11` keeps the argument registers. -/
theorem argEq_xS3 (Z : Int64) (v : BitVec 64) (σ : AS) : ArgEq σ.regs (xS3 Z v σ).regs :=
  (argEq_xS2 Z σ).trans (argEq_set64 (by decide) _)

/-! ## Obligations combined -/

section Comb

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {K : State → State → Prop} {ms : MemSide isa} {pc0 Z lim : Int64} {L : Label} {zl zf z1 z2 zs : Nat}
  {ps : List (Reg64 × Int64 × Nat)} {JE : AS → Ctl → Prop}

/-- **A prologue inside `W`** from one inside `W1` not moved by `K` and one
inside `W2'`, `W1 ∧ W2'` inside `W` (`BlkW.imp`, `NodeW.imp` per node). -/
theorem XProW.imp {W W1 W2' : Frag isa} (h1 : XProW W1 K exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps JE)
    (h2 : XProW W2' (fun _ _ => False) exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps JE)
    (hw : ∀ s c, W1 s c → W2' s c → W s c) : XProW W K exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps JE :=
  ⟨X64.AllocG.BlkW.imp h1.w0 h2.w0 hw, X64.AllocG.BlkW.imp h1.w1 h2.w1 hw, X64.AllocG.NodeW.imp h1.w2 h2.w2 hw,
    X64.AllocG.BlkW.imp h1.w3 h2.w3 hw, X64.AllocG.BlkW.imp h1.w4 h2.w4 hw⟩

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS} {Dt Ab : State → Prop} {lbl lbl0 : Lbl}
  {lsize : Lsize} {fs : List TermRun.Frame}

/-- **A prologue inside `W2`** at the frames `fs` (`BlkW.w2`, `NodeW.w2`
per node): `SFacts` at the source start's control over the invariant's
states (`hS`), `W2Part` at the states, and at every control of the entry
invariant `JE` `main`'s `ret` excluded and `FrOk2`. -/
theorem XProW.w2 (hp : ProgNoS ZBad p)
    (hS : XProW (fun s c => SFacts Λ μ own rS Tk lbl0 s c) K exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps
      (fun σ c => c = X64Consumer.c0 ∧ ∃ c', JE σ c'))
    (hP : XProW (W2Part Λ μ p rd G own ar J Ab lbl lsize fs) (fun _ _ => False) exe endPc R F ms pc0 Z lim L
      zl zf z1 z2 zs ps JE)
    (hJ : ∀ σ c, JE σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    XProW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F ms pc0 Z lim L
      zl zf z1 z2 zs ps JE := by
  refine ⟨BlkW.w2 (lbl0 := lbl0) hp (BlkW.mapC rfl rfl hS.w0 fun σ c h => ⟨c, h, fun _ h => h⟩) hP.w0 hJ,
    BlkW.w2 (lbl0 := lbl0) hp (BlkW.mapC (n' := xProN1 pc0 _) rfl rfl hS.w1 ?_) hP.w1 ?_,
    NodeW.w2 (lbl0 := lbl0) hp (NodeW.mapC (n' := xProN2 pc0 zl Z _) rfl rfl hS.w2 ?_) hP.w2 ?_,
    BlkW.w2 (lbl0 := lbl0) hp (BlkW.mapC (n' := xProN3 ms pc0 zl zf Z lim _) rfl rfl hS.w3 ?_) hP.w3 ?_,
    BlkW.w2 (lbl0 := lbl0) hp (BlkW.mapC (n' := xProN4 ms pc0 zl zf z1 z2 Z lim _) rfl rfl hS.w4 ?_) hP.w4 ?_⟩
  · rintro σ1 c ⟨rfl, c1, σ, hJ', he⟩
    exact ⟨_, ⟨σ, ⟨rfl, c1, hJ'⟩, he⟩, fun _ h => h⟩
  · rintro σ1 c ⟨σ, hJ', -⟩
    exact hJ σ c hJ'
  · rintro σ2 c ⟨rfl, c1, σ, hJ', he⟩
    exact ⟨_, ⟨σ, ⟨rfl, c1, hJ'⟩, he⟩, fun _ h => h⟩
  · rintro σ2 c ⟨σ, hJ', -⟩
    exact hJ σ c hJ'
  · rintro σ3 c ⟨rfl, c1, σ, v, hJ', hg, he⟩
    exact ⟨_, ⟨σ, v, ⟨rfl, c1, hJ'⟩, hg, he⟩, fun _ h => h⟩
  · rintro σ3 c ⟨σ, v, hJ', -⟩
    exact hJ σ c hJ'
  · rintro σ4 c ⟨rfl, c1, σ, v, hJ', hg, he, hs⟩
    exact ⟨_, ⟨σ, v, ⟨rfl, c1, hJ'⟩, hg, he, hs⟩, fun _ h => h⟩
  · rintro σ4 c ⟨σ, v, hJ', -⟩
    exact hJ σ c hJ'

/-- **`W2Part` over a prologue** from the abort phase's facts (`hab`), the
placement (`hP`), and no write and no system call (`hN`). -/
theorem XProW.w2Part
    (hab : XProW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps JE)
    (hP : XProW (fun s c => PlacedS Λ lbl s c fs) (fun _ _ => False) exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs
      ps JE)
    (hN : XProW (fun s _ => (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false) (fun _ _ => False) exe endPc R F ms pc0 Z lim
      L zl zf z1 z2 zs ps JE) :
    XProW (W2Part Λ μ p rd G own ar J Ab lbl lsize fs) (fun _ _ => False) exe endPc R F ms pc0 Z lim L
      zl zf z1 z2 zs ps JE :=
  XProW.imp hab (XProW.imp (W := fun s c => PlacedS Λ lbl s c fs ∧ (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false)
    hP hN fun _ _ h1 h2 => ⟨h1, h2⟩) fun _ _ h1 h2 =>
    ⟨h1, h2.1, fun _ _ _ _ => wrOkA_of_noWr h2.2.1, fun h => absurd h (by rw [h2.2.2]; decide)⟩

/-- **A prologue's states placed** at the frames `fs`: every control of
the entry invariant `JE` placed at every state agreeing with the entry's
on the argument registers (`hPl`); the prologue writes none of them. -/
theorem proW_placedS
    (hPl : ∀ σ c, JE σ c → ∀ s : State,
      (∀ i < 6, s.st.1.regs.get64 (argXs.getD i .rdi) = σ.regs.get64 (argXs.getD i .rdi)) →
      PlacedS Λ lbl s c fs) :
    XProW (fun s c => PlacedS Λ lbl s c fs) (fun _ _ => False) exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps JE := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s σ c _ _ _ _ _ _ hJ k _ m hA' _
    refine ⟨hPl σ c hJ _ fun i hi => ?_, fun _ h => h⟩
    show m.regs.get64 _ = _
    rw [hA'.regs]
    exact argEq_arun_take _ (dstep_xHead _) k _ i hi
  · rintro s σ1 c _ _ _ _ _ _ ⟨σ, hJ, rfl⟩ k _ m hA' _
    refine ⟨hPl σ c hJ _ fun i hi => ?_, fun _ h => h⟩
    show m.regs.get64 _ = _
    rw [hA'.regs]
    exact ((argEq_xS1 σ).trans (argEq_arun_take _ (dstep_xLea _ Z zl) k _)) i hi
  · rintro s c ⟨-, -, -, -, σ2, hA, -, σ, hJ, rfl⟩
    refine ⟨hPl σ c hJ _ fun i hi => ?_, fun _ h => h⟩
    rw [hA.regs]
    exact argEq_xS2 Z σ i hi
  · rintro s σ3 c _ _ _ _ _ _ ⟨σ, v, hJ, -, rfl⟩ k _ m hA' _
    refine ⟨hPl σ c hJ _ fun i hi => ?_, fun _ h => h⟩
    show m.regs.get64 _ = _
    rw [hA'.regs]
    exact ((argEq_xS3 Z _ σ).trans (argEq_arun_take _ (dstep_xCmp _ L z1 z2) k _)) i hi
  · rintro s σ4 c _ _ _ _ _ _ ⟨σ, v, hJ, -, he, -⟩ k _ m hA' _
    refine ⟨hPl σ c hJ _ fun i hi => ?_, fun _ h => h⟩
    show m.regs.get64 _ = _
    rw [hA'.regs]
    have h4 : ArgEq σ.regs σ4.regs := by rw [he]; exact argEq_xS3 Z _ σ
    exact (h4.trans (argEq_arun_take _ (dstep_xFr _ Z zs ps) k _)) i hi

end Comb

/-! ## The prologue inside `W2` -/

section Pro

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS} {Dt Ab : State → Prop}
  {lsize : Lsize} {fs : List TermRun.Frame}

/-- **A stack-checked prologue writes nothing and is off a system call**:
its blocks (`blkW_noWr'`, `blkW_noSys'`) and the limit's load
(`noWr_load`) of a word unmapped under the frame condition (`hun`). -/
theorem proW_noWr {ms : MemSide isa} {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {fn sc entry : Label} {Z : Int64} {L : Label} {zl zf z1 z2 zs : Nat} {ps : List (Reg64 × Int64 × Nat)}
    (hin : prologueIn cells fn sc entry Z 8 L zl zf z1 z2 zs ps = true)
    (hps : ∀ q ∈ ps, offOk (-8 - Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    {JE : AS → Ctl → Prop} {tp : UInt64} (htp : ∀ σ c, JE σ c → σ.regs.fsBase = tp)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -8 - Z.toInt) (hhi : 0 ≤ R.hi)
    (hZ : 0 ≤ Z.toInt) (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none) :
    XProW (fun s _ => (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label fn) Z 8 L zl zf z1 z2 zs ps JE := by
  have h := hin
  simp only [prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, bLd⟩, bCmp⟩, bFr⟩, -⟩ := h
  have esc := label_labelGapB hI.lays hgap
  rw [hI.labOk] at esc
  have h4 : lab fn + 1 + 3 = lab sc := by rw [esc, Int64.add_assoc]; rfl
  have hBN : ∀ {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {l : Label} {off : Nat},
      blockAtB cells l off blk = true → lab l + Int64.ofNat off = n.pc → okBlk lo hi n.o blk = true →
      R.lo ≤ lo → hi ≤ R.hi →
      BlkW (fun s _ => (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false) (fun _ _ => False) exe endPc R F n blk :=
    fun hb he hok hlo' hhi' =>
      have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s _ _ := fun s hs hn =>
        he ▸ X64.Rt.codeOf hI hb hs hn
      X64.AllocG.BlkW.imp (blkW_noWr' hcode hok hR hlo' hhi') (blkW_noSys' hcode hok) fun _ _ h1 h2 => ⟨h1, h2⟩
  rw [hI.labOk]
  refine ⟨hBN bHd (Spike.Lib.X64.Flow.ofNat_zero' _)
      (xHead_ok (lo := -8 - Z.toInt) (hi := 0) (by omega) (Int.le_refl _)) hlo hhi,
    hBN bLea (by show _ = _ + 1 + 3; rw [h4, Spike.Lib.X64.Flow.ofNat_zero'])
      (xLea_ok (lo := -8 - Z.toInt) (hi := 0) _ _) hlo hhi, ?_,
    hBN bCmp (by show _ = _ + 1 + 3 + _ + _; rw [h4, ofNat_add'])
      (xCmp_ok (lo := -8 - Z.toInt) (hi := 0) _ _ _ _) hlo hhi,
    hBN bFr (by show _ = _ + 1 + 3 + _ + _ + _ + _; rw [h4, ofNat_add', ofNat_add', ofNat_add'])
      (xFr_ok (lo := -8 - Z.toInt) (hi := 0) _ _ _ hps) hlo hhi⟩
  rintro s c ⟨hs, hn, hdc, hpc, σ2, hA, hD, σ, hJ, rfl⟩
  have hpc' : s.st.2 = lab sc + Int64.ofNat zl := by
    rw [hpc]; show _ + 1 + 3 + _ = _; rw [h4]
  have hc := X64.Rt.cellOf hI bLd rfl hs hn hpc'
  have ha : (xS2 Z σ).regs.fsBase.toBitVec + (8 : Int64).toBitVec = limA tp := by
    rw [show (xS2 Z σ).regs.fsBase = σ.regs.fsBase by simp [xS2, xS1, hdRegs, Reg64s.set64], htp _ _ hJ]
    rfl
  have ha' : fsAddr s zf { base := none, idx := none, disp := .int64 8 } = limA tp := by
    rw [← ha]
    simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs]
  have hex := exec_movfs_load_agrees hc ha' (hun _ hD) (agrees_of_decls hdc _ _)
  exact ⟨⟨noWr_load hex, Scc.Sem.X64.atSyscall_false_of_cellAt hc (by intro w w' h; cases h)⟩, fun _ h => h⟩

/-- **A stack-checked prologue is inside `W2`** at the frames `fs` (for
any frame `Z`): `SFacts` from `proW_sfactsP` at the source start's
control, nothing written and off a system call (`proW_noWr`), the abort
phase's facts a premise (`hab`), the states placed from the entry's
argument registers (`hPl`, `proW_placedS`), and at every control of the
entry invariant `JE` `main`'s `ret` excluded and `FrOk2` (`hJ`). -/
theorem proW_w2 {ms : MemSide isa} {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {fn sc entry : Label} {Z : Int64} {L : Label} {zl zf z1 z2 zs : Nat} {ps : List (Reg64 × Int64 × Nat)}
    (hin : prologueIn cells fn sc entry Z 8 L zl zf z1 z2 zs ps = true)
    (hps : ∀ q ∈ ps, offOk (-8 - Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    {JE : AS → Ctl → Prop} {tp : UInt64} (htp : ∀ σ c, JE σ c → σ.regs.fsBase = tp)
    (hph : ProPh okPc ph lab fn sc Z L zl zf z1 z2 zs ps)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hlo : R.lo ≤ -8 - Z.toInt) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hZ : 0 ≤ Z.toInt)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hp : ProgNoS ZBad p)
    (hab : XProW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label fn) Z 8 L zl zf z1 z2 zs ps JE)
    (hPl : ∀ σ c, JE σ c → ∀ s : State,
      (∀ i < 6, s.st.1.regs.get64 (argXs.getD i .rdi) = σ.regs.get64 (argXs.getD i .rdi)) →
      PlacedS Λ lbl s c fs)
    (hJ : ∀ σ c, JE σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    XProW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F ms
      ((_root_.Executable.labels exe).label fn) Z 8 L zl zf z1 z2 zs ps JE := by
  have hS := proW_sfactsP (lbl := lbl) (ms := ms) (J := fun σ c => c = X64Consumer.c0 ∧ ∃ c', JE σ c') hI hin hps
    cfacts_c0 (fun _ _ h => h.1) (fun σ _ ⟨_, c', h⟩ => htp σ c' h) hph hR hR8 hlo hhi hl hh hZ hmr hun hsub
    hfit hFO
  exact XProW.w2 hp hS (XProW.w2Part hab (proW_placedS hPl) (proW_noWr hI hin hps htp hR hlo hhi hZ hun)) hJ

end Pro

/-! ## The abort phase over the prologue -/

section Ab

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat}

/-- **A user function's name is none of the write abort's labels.** -/
theorem user_not_abLabs (f : String) : Scc.Lower.Names.user f ∉ X64.AllocG.abLabs := by
  intro h
  have hall : X64.AllocG.abLabs.all (fun a => a.toList.take 3 != "wc_".toList) = true := by decide
  have := List.all_eq_true.mp hall _ h
  rw [show Scc.Lower.Names.user f = "wc_" ++ Scc.Lower.Names.mangle f from rfl, String.toList_append,
    List.take_append_of_le_length (by decide)] at this
  simp at this

/-- **A cell of a block after a label off the write abort's** is a position
off it. -/
theorem posOff_blockAtB {l : Label} {off : Nat} {b : List (Directive × Nat)} (hb : blockAtB cells l off b = true)
    (hl : l ∉ X64.AllocG.abLabs) {i : Nat} (hi : i < b.length) :
    PosOff cells lab (lab l + Int64.ofNat (off + cellOff b i)) :=
  ⟨l, _, inRunB_of_blockAtB hb hi, hl, rfl⟩

/-- **A block after a label off the write abort's keeps its phase**
(`blkW_abSt_pos`): `off` bytes after the label `sc` none of `abLabs`
(`hb`, `hsc`) at its node's pc (`he`), the position right after it off the
write abort (`hend`), every target but a fall-through off it (`htgt`). -/
theorem blkW_abSt_at {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habt : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {R : Region} {F : MachineData → Prop} {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {sc : Label}
    {off : Nat} (hb : blockAtB cells sc off blk = true) (hsc : sc ∉ X64.AllocG.abLabs)
    (he : lab sc + Int64.ofNat off = n.pc) (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo)
    (hhi : hi ≤ R.hi) (hph : blkPh okPc ph (fun _ => false) lab (lab sc + Int64.ofNat off) 0 blk = true)
    (hnr : noRetBlk blk = true)
    (hend : PosOff cells lab (lab sc + Int64.ofNat (off + cellOff blk blk.length)))
    (htgt : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, Spike.Lib.X64.classify blk[k].1 = some a →
      ∀ t ∈ X64Consumer.aiTgts lab (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) 0 a,
        t ≠ n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2 → PosOff cells lab t) :
    BlkW (fun s _ => AbSt μ (X64.WriteAb.Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk := fun s hs hn =>
    he ▸ X64.Rt.codeOf hI hb hs hn
  rw [he] at hph
  refine blkW_abSt_pos hI hpr habt hcode hok hR hlo hhi hph hnr ?_
  intro σ c hJ k hk a ha t ht
  by_cases hf : t = n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2
  · refine .inl ?_
    have hf' : t = lab sc + Int64.ofNat (off + cellOff blk (k + 1)) := by
      rw [hf, ← he, cellOff_succ hk, Int64.ofNat_add, Int64.ofNat_add, Int64.add_assoc, Int64.add_assoc]
    rw [hf']
    rcases Nat.lt_or_ge (k + 1) blk.length with h1 | h1
    · exact posOff_blockAtB hb hsc h1
    · rw [show k + 1 = blk.length by omega]
      exact hend
  · exact .inl (htgt σ c hJ k hk a ha t ht hf)

/-- **A block of fall-throughs has no other target.** -/
theorem htgt_fall {lab : Label → Int64} {pc : Int64} {blk : List (Directive × Nat)} (hf : fallBlk blk = true)
    {P : Int64 → Prop} : ∀ k (hk : k < blk.length) a, Spike.Lib.X64.classify blk[k].1 = some a →
      ∀ t ∈ X64Consumer.aiTgts lab (pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) 0 a,
        t ≠ pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2 → P t := by
  intro k hk a ha t ht hne
  have := fallBlk_get hf hk ha
  cases a <;> simp only [fallI, Bool.false_eq_true] at this <;>
    simp only [X64Consumer.aiTgts, List.mem_singleton] at ht <;> exact absurd ht hne

theorem fallBlk_xHead : fallBlk xHead = true := by
  simp [fallBlk, xHead, Spike.Lib.X64.classify, RegOnly, fallI]

theorem fallBlk_xLea (Z : Int64) (z : Nat) : fallBlk (xLea Z z) = true := by
  simp [fallBlk, xLea, Spike.Lib.X64.classify, RegOnly, fallI]

theorem fallBlk_xFr (Z : Int64) (z : Nat) (ps : List (Reg64 × Int64 × Nat)) : fallBlk (xFr Z z ps) = true := by
  simp [fallBlk, xFr, xSt, Spike.Lib.X64.classify, RegOnly, fallI]

/-- **A stack-checked prologue keeps the write abort's phase**: its
function's label `fn` and check label `sc` none of the write abort's
(`hfn`, `hsc`), the overflow target `L` and the body's entry off the write
abort (`hL`, `hent`); every block by `blkW_abSt_at`, the limit's load
falling through to the compare. -/
theorem proW_abSt {ms : MemSide isa} {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habt : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {fn sc entry : Label} {Z : Int64} {L : Label} {zl zf z1 z2 zs : Nat} {ps : List (Reg64 × Int64 × Nat)}
    (hin : prologueIn cells fn sc entry Z 8 L zl zf z1 z2 zs ps = true)
    (hps : ∀ q ∈ ps, offOk (-8 - Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hph : ProPh okPc ph lab fn sc Z L zl zf z1 z2 zs ps)
    (hfn : fn ∉ X64.AllocG.abLabs) (hsc : sc ∉ X64.AllocG.abLabs) (hL : PosOff cells lab (lab L))
    (hent : PosOff cells lab (lab entry))
    {JE : AS → Ctl → Prop} {tp : UInt64} (htp : ∀ σ c, JE σ c → σ.regs.fsBase = tp)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -8 - Z.toInt) (hhi : 0 ≤ R.hi)
    (hZ : 0 ≤ Z.toInt) (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none) :
    XProW (fun s _ => AbSt μ (X64.WriteAb.Ab lab) s) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label fn) Z 8 L zl zf z1 z2 zs ps JE := by
  have h := hin
  simp only [prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, bLd⟩, bCmp⟩, bFr⟩, hgap2⟩ := h
  have esc := label_labelGapB hI.lays hgap
  have een := label_labelGapB hI.lays hgap2
  rw [hI.labOk] at esc een
  have h4 : lab fn + 1 + 3 = lab sc := by rw [esc, Int64.add_assoc]; rfl
  have hCmp : PosOff cells lab (lab sc + Int64.ofNat (zl + zf)) :=
    posOff_blockAtB (i := 0) bCmp hsc (by simp [xCmp])
  rw [hI.labOk]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine blkW_abSt_at hI hpr habt bHd hfn (Spike.Lib.X64.Flow.ofNat_zero' _)
      (xHead_ok (lo := -8 - Z.toInt) (hi := 0) (by omega) (Int.le_refl _)) hR hlo hhi hph.hd xHead_noRet ?_
      (fun _ _ _ => htgt_fall fallBlk_xHead)
    have := posOff_blockAtB (lab := lab) (i := 0) bLea hsc (by simp [xLea])
    rwa [show lab sc + Int64.ofNat (0 + cellOff (xLea Z zl) 0) = lab fn + Int64.ofNat (0 + cellOff xHead xHead.length)
      by rw [esc, Int64.add_assoc]; rfl] at this
  · refine blkW_abSt_at hI hpr habt bLea hsc (by show _ = _ + 1 + 3; rw [h4, Spike.Lib.X64.Flow.ofNat_zero'])
      (xLea_ok (lo := -8 - Z.toInt) (hi := 0) _ _) hR hlo hhi hph.lea (xLea_noRet _ _) ?_
      (fun _ _ _ => htgt_fall (fallBlk_xLea _ _))
    have := posOff_blockAtB (lab := lab) (i := 0) bLd hsc (by simp)
    simpa [cellOff, xLea] using this
  · rintro s c ⟨hs, hn, hdc, hpc, σ2, hA, hD, σ, hJ, rfl⟩
    have hpc' : s.st.2 = lab sc + Int64.ofNat zl := by
      rw [hpc]; show _ + 1 + 3 + _ = _; rw [h4]
    have hc := X64.Rt.cellOf hI bLd rfl hs hn hpc'
    have ha : (xS2 Z σ).regs.fsBase.toBitVec + (8 : Int64).toBitVec = limA tp := by
      rw [show (xS2 Z σ).regs.fsBase = σ.regs.fsBase by simp [xS2, xS1, hdRegs, Reg64s.set64], htp _ _ hJ]
      rfl
    have ha' : fsAddr s zf { base := none, idx := none, disp := .int64 8 } = limA tp := by
      rw [← ha]
      simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs]
    have hex := exec_movfs_load_agrees hc ha' (hun _ hD) (agrees_of_decls hdc _ _)
    have hok : okPc (Scc.Sem.X64.pcOf s) = true := by unfold Scc.Sem.X64.pcOf; rw [hpc']; exact hph.ld.1
    have hP := (hI.off s hok).1
    have hnx : lab sc + Int64.ofNat zl + Int64.ofNat zf ∉ X64.WriteAb.abPcs lab := by
      have := notAbPc_of_posOff hI.lays hpr habt (hI.labOk ▸ hCmp)
      rw [hI.labOk] at this
      rwa [Int64.ofNat_add, ← Int64.add_assoc] at this
    refine ⟨Spike.Lib.X64ConsumerA.AbSt.ofLeaves hP.noTake
      (Scc.Sem.X64.atSyscall_false_of_cellAt hc (by intro w w' h; cases h)) fun t ht => ?_, fun _ h => h⟩
    rw [hex] at ht
    cases ht
    exact fun _ _ => X64.AllocG.not_ab_after hpc' hnx
  · refine blkW_abSt_at hI hpr habt bCmp hsc (by show _ = _ + 1 + 3 + _ + _; rw [h4, ofNat_add'])
      (xCmp_ok (lo := -8 - Z.toInt) (hi := 0) _ _ _ _) hR hlo hhi hph.cmp (xCmp_noRet _ _ _) ?_ ?_
    · have := posOff_blockAtB (lab := lab) (i := 0) bFr hsc (by simp [xFr])
      have e : zl + zf + cellOff (xCmp L z1 z2) (xCmp L z1 z2).length =
          zl + zf + z1 + z2 + cellOff (xFr Z zs ps) 0 := by
        simp [cellOff, xCmp]; omega
      rwa [e]
    intro σ c _ k hk a ha t ht hne
    match k, hk with
    | 0, _ =>
      simp [xCmp, Spike.Lib.X64.classify, RegOnly] at ha
      subst ha
      simp only [X64Consumer.aiTgts, List.mem_singleton] at ht
      exact absurd ht hne
    | 1, _ =>
      simp [xCmp, Spike.Lib.X64.classify] at ha
      subst ha
      simp only [X64Consumer.aiTgts, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | ht
      · exact hL
      · exact absurd ht hne
  · refine blkW_abSt_at hI hpr habt bFr hsc
      (by show _ = _ + 1 + 3 + _ + _ + _ + _; rw [h4, ofNat_add', ofNat_add', ofNat_add'])
      (xFr_ok (lo := -8 - Z.toInt) (hi := 0) _ _ _ hps) hR hlo hhi hph.fr (xFr_noRet _ _ _) ?_
      (fun _ _ _ => htgt_fall (fallBlk_xFr _ _ _))
    have e : zl + zf + z1 + z2 + cellOff (xFr Z zs ps) (xFr Z zs ps).length =
        zl + zf + z1 + z2 + zs + Spike.Lib.X64.Flow.szSum ps := by
      have hk : (ps.map fun x => x.2.2).take ps.length = ps.map fun x => x.2.2 :=
        List.take_of_length_le (by simp)
      simp [cellOff, xFr, xSt, Spike.Lib.X64.Flow.szSum, List.map_map, Function.comp_def, hk]; omega
    rw [e, ← een]
    exact hent

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

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS} {Dt Ab : State → Prop}
  {lsize : Lsize} {fs : List TermRun.Frame}
  {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
  {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}

/-- **A compiled block's prologue inside `W2`** (`CalleePre2.hpro` at
`W2`, `proW_w2` at its frame `fr.size` and spill `ps`): as `proW_w2`, the
frame's bounds from the block's code facts `c`. -/
theorem proW_w2C (c : FnCode2 exe cells endPc RaOk Cd i T d) {ms : MemSide isa} {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {JE : AS → Ctl → Prop} {tp : UInt64} (htp : ∀ σ c, JE σ c → σ.regs.fsBase = tp)
    (hph : ProPh okPc ph lab c.fn (Scc.Emit.X64.labelOf c.fr.fn "chk") (Int64.ofInt c.fr.size) (proL c.fr)
      c.zl c.zf c.z1 c.z2 c.zs c.ps)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hlo : R.lo ≤ -8 - (c.fr.size : Int)) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hp : ProgNoS ZBad p)
    (hab : XProW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.fr.size) (Int64.ofNat Scc.IR.Tcb.stackLimit)
      (proL c.fr) c.zl c.zf c.z1 c.z2 c.zs c.ps JE)
    (hPl : ∀ σ c, JE σ c → ∀ s : State,
      (∀ i < 6, s.st.1.regs.get64 (argXs.getD i .rdi) = σ.regs.get64 (argXs.getD i .rdi)) →
      PlacedS Λ lbl s c fs)
    (hJ : ∀ σ c, JE σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    XProW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F ms
      ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.fr.size) (Int64.ofNat Scc.IR.Tcb.stackLimit)
      (proL c.fr) c.zl c.zf c.z1 c.z2 c.zs c.ps JE := by
  have h1 := c.h1
  have hZ : (Int64.ofInt c.fr.size).toInt = c.fr.size := toInt_ofInt_small (by omega) (by omega)
  exact proW_w2 hI c.hpro c.hps htp hph hR hR8 (by rw [hZ]; exact hlo) hhi hl hh (by rw [hZ]; omega) hmr hun
    hsub hfit hFO hp hab hPl hJ

/-- **A compiled block's prologue keeps the write abort's phase**
(`proW_abSt` at its frame `fr.size` and spill `ps`): its label `fn` a user
function's name (`c.hfn`), its check label a user function's block label
(`hfr`), the overflow target and the body's entry off the write abort
(`hL`, `hent`). -/
theorem proW_abStC (c : FnCode2 exe cells endPc RaOk Cd i T d) {ms : MemSide isa} {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habt : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : ProPh okPc ph lab c.fn (Scc.Emit.X64.labelOf c.fr.fn "chk") (Int64.ofInt c.fr.size) (proL c.fr)
      c.zl c.zf c.z1 c.z2 c.zs c.ps)
    (hfr : c.fr.fn = Scc.Lower.Names.user d.name) (hL : PosOff cells lab (lab (proL c.fr)))
    (hent : PosOff cells lab (lab c.entry))
    {JE : AS → Ctl → Prop} {tp : UInt64} (htp : ∀ σ c, JE σ c → σ.regs.fsBase = tp)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -8 - (c.fr.size : Int)) (hhi : 0 ≤ R.hi)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none) :
    XProW (fun s _ => AbSt μ (X64.WriteAb.Ab lab) s) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.fr.size) (Int64.ofNat Scc.IR.Tcb.stackLimit)
      (proL c.fr) c.zl c.zf c.z1 c.z2 c.zs c.ps JE := by
  have h1 := c.h1
  have hZ : (Int64.ofInt c.fr.size).toInt = c.fr.size := toInt_ofInt_small (by omega) (by omega)
  exact proW_abSt hI hpr habt c.hpro c.hps hph (by rw [c.hfn]; exact user_not_abLabs _)
    (by rw [hfr]; exact labelOf_user_not_abLabs _ _) hL hent htp hR (by rw [hZ]; exact hlo) hhi
    (by rw [hZ]; omega) hun

/-- **The setup function's prologue inside `W2`** at the setup call's
frame `fr` (`setupCallWS_ofFnSpec`'s `CalleePre2.hpro`, at the entry
`uN0`): as `proW_w2C`; the callee's control `g.c0` the call's (`hct`)
binding the unit parameter to no word (`hcE`), the caller's environment
binding no word (`hW0`), so every state is placed (`placedS_of_nilWords`);
`FrOk2` at the call a premise (`hfo`). -/
theorem hpro_setup (c : FnCode2 exe cells endPc RaOk Cd i T d) {ms : MemSide isa} {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {ms0 : MemSide isa} {F0 : MachineData → Prop} {fn : Label} {ZU : Int64} {g : Spike.Lib.X64.Flow.Ret0.WcG}
    {c0 : Ctl} {fr : TermRun.Frame}
    (hph : ProPh okPc ph lab c.fn (Scc.Emit.X64.labelOf c.fr.fn "chk") (Int64.ofInt c.fr.size) (proL c.fr)
      c.zl c.zf c.z1 c.z2 c.zs c.ps)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hlo : R.lo ≤ -8 - (c.fr.size : Int)) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA g.tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA g.tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hp : ProgNoS ZBad p)
    (hab : XProW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.fr.size) (Int64.ofNat Scc.IR.Tcb.stackLimit)
      (proL c.fr) c.zl c.zf c.z1 c.z2 c.zs c.ps
      (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels exe).label ms0 F0 fn ZU g).J)
    (hct : CallTo p c0 g.c0 fr) (hcE : g.c0 = ⟨d.body, [(d.arg, d.argTy, [])], none⟩)
    (hW0 : ∀ x ty ws, TermRun.lookupE c0.env x = some (ty, ws) → ws = []) (hfo : FrOk2 g.c0 [fr]) :
    XProW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c [fr]) K exe endPc R F ms
      ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.fr.size) (Int64.ofNat Scc.IR.Tcb.stackLimit)
      (proL c.fr) c.zl c.zf c.z1 c.z2 c.zs c.ps
      (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels exe).label ms0 F0 fn ZU g).J := by
  have hfr : fr.env = c0.env := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, -, rfl⟩ := hct
    rfl
  have hpl : ∀ s, PlacedS Λ lbl s g.c0 [fr] := placedS_of_nilWords fun env henv x ty ws hl => by
    simp only [envsOf, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at henv
    rcases henv with rfl | rfl
    · rw [hcE] at hl; exact lookupE_nil_words hl
    · rw [hfr] at hl; exact hW0 x ty ws hl
  refine proW_w2C c hI (fun _ _ h => h.1.2.2.2.2) hph hR hR8 hlo hhi hl hh hmr hun hsub hfit hFO hp hab
    (fun _ _ h s _ => h.1.1 ▸ hpl s) fun _ _ h => ⟨fun h' => (List.cons_ne_nil _ _ h').elim, h.1.1 ▸ hfo⟩

/-- **`main`'s prologue inside `W2`** after the setup block, at no frames
(`mainCallWSF_ofHeld`'s `CalleePre2.hpro`): as `proW_w2C` at an entry
invariant `JE` inside the entry `uNM` with its arguments `Pre` (`hJE`); a
control and registers of `Pre` placed at every state agreeing on the
argument registers (`hPl`, e.g. `hPl_setupArgs`), not at a `ret` (`hnr`,
e.g. `hnr_setupArgs`) and free of `ZBad` (`hfo`). -/
theorem hpro_main (c : FnCode2 exe cells endPc RaOk Cd i T d) {ms : MemSide isa} {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {ms0 : MemSide isa} {F0 : MachineData → Prop} {fn : Label} {ZU : Int64} {g : Spike.Lib.X64.Flow.Ret0.WcG}
    {Pre : Ctl → Reg64s → Prop} {JE : AS → Ctl → Prop}
    (hJE : ∀ σ c, JE σ c → (Spike.Lib.X64.Rt.uNM (_root_.Executable.labels exe).label ms0 F0 fn ZU Pre g).J σ c)
    (hph : ProPh okPc ph lab c.fn (Scc.Emit.X64.labelOf c.fr.fn "chk") (Int64.ofInt c.fr.size) (proL c.fr)
      c.zl c.zf c.z1 c.z2 c.zs c.ps)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hlo : R.lo ≤ -8 - (c.fr.size : Int)) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA g.tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA g.tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hp : ProgNoS ZBad p)
    (hab : XProW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.fr.size) (Int64.ofNat Scc.IR.Tcb.stackLimit)
      (proL c.fr) c.zl c.zf c.z1 c.z2 c.zs c.ps JE)
    (hPl : ∀ c (regs : Reg64s), Pre c regs → ∀ s : State,
      (∀ i < 6, s.st.1.regs.get64 (argXs.getD i .rdi) = regs.get64 (argXs.getD i .rdi)) → PlacedS Λ lbl s c [])
    (hnr : ∀ c regs, Pre c regs → ∀ a, c.term ≠ .ret a) (hfo : ∀ c regs, Pre c regs → FrOk2 c []) :
    XProW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c []) K exe endPc R F ms
      ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.fr.size) (Int64.ofNat Scc.IR.Tcb.stackLimit)
      (proL c.fr) c.zl c.zf c.z1 c.z2 c.zs c.ps JE :=
  proW_w2C c hI (fun σ c h => (hJE σ c h).1.2.2.2.2) hph hR hR8 hlo hhi hl hh hmr hun hsub hfit hFO hp hab
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
    ∀ c regs, Spike.Lib.X64.Rt.SetupArgs (SPostC p lbl ty c0) sw x0 c regs → ∀ a, c.term ≠ .ret a := by
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
    ∀ c regs, Spike.Lib.X64.Rt.SetupArgs (SPostC p lbl ty c0) sw x0 c regs → ∀ a, c.term ≠ .ret a :=
  hnr_setupArgs (hE_setupTerm hc)

/-- info: 'Spike.Lib.LowerX64.ArgEq.refl' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.ArgEq.refl

/-- info: 'Spike.Lib.LowerX64.ArgEq.trans' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.ArgEq.trans

/-- info: 'Spike.Lib.LowerX64.argEq_set64' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.argEq_set64

/-- info: 'Spike.Lib.LowerX64.argEq_arun_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.argEq_arun_take

/-- info: 'Spike.Lib.LowerX64.dstep_xHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.dstep_xHead

/-- info: 'Spike.Lib.LowerX64.dstep_xLea' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.dstep_xLea

/-- info: 'Spike.Lib.LowerX64.dstep_xCmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.dstep_xCmp

/-- info: 'Spike.Lib.LowerX64.dstep_xFr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.dstep_xFr

/-- info: 'Spike.Lib.LowerX64.argEq_xS1' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.argEq_xS1

/-- info: 'Spike.Lib.LowerX64.argEq_xS2' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.argEq_xS2

/-- info: 'Spike.Lib.LowerX64.argEq_xS3' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.argEq_xS3

/-- info: 'Spike.Lib.LowerX64.XProW.imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.XProW.imp

/-- info: 'Spike.Lib.LowerX64.XProW.w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.XProW.w2

/-- info: 'Spike.Lib.LowerX64.XProW.w2Part' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.XProW.w2Part

/-- info: 'Spike.Lib.LowerX64.proW_placedS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.proW_placedS

/-- info: 'Spike.Lib.LowerX64.proW_noWr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.proW_noWr

/-- info: 'Spike.Lib.LowerX64.proW_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.proW_w2

/-- info: 'Spike.Lib.LowerX64.placedS_of_nilWords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.placedS_of_nilWords

/-- info: 'Spike.Lib.LowerX64.lookupE_nil_words' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.lookupE_nil_words

/-- info: 'Spike.Lib.LowerX64.proW_w2C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.proW_w2C

/-- info: 'Spike.Lib.LowerX64.hpro_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hpro_setup

/-- info: 'Spike.Lib.LowerX64.hpro_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hpro_main

/-- info: 'Spike.Lib.LowerX64.heldRetOk_not_ret' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.heldRetOk_not_ret

/-- info: 'Spike.Lib.LowerX64.hnr_setupArgs' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hnr_setupArgs

/-- info: 'Spike.Lib.LowerX64.user_not_abLabs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.user_not_abLabs

/-- info: 'Spike.Lib.LowerX64.posOff_blockAtB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.posOff_blockAtB

/-- info: 'Spike.Lib.LowerX64.blkW_abSt_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.blkW_abSt_at

/-- info: 'Spike.Lib.LowerX64.htgt_fall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.htgt_fall

/-- info: 'Spike.Lib.LowerX64.fallBlk_xHead' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.fallBlk_xHead

/-- info: 'Spike.Lib.LowerX64.fallBlk_xLea' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.fallBlk_xLea

/-- info: 'Spike.Lib.LowerX64.fallBlk_xFr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.fallBlk_xFr

/-- info: 'Spike.Lib.LowerX64.proW_abSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.proW_abSt

/-- info: 'Spike.Lib.LowerX64.proW_abStC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.proW_abStC

/-- info: 'Spike.Lib.LowerX64.hE_setupTerm' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hE_setupTerm

/-- info: 'Spike.Lib.LowerX64.hnr_setupTerm' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hnr_setupTerm

end Spike.Lib.LowerX64
