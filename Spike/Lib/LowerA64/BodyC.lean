/-
**A lowered `Accepted1` body with calls is one segment at the caller's
frames** (AArch64), symbolic in the body, the frame, the IR registers'
slots and the pcs; next to `Spike/Lib/LowerA64/Body1.lean`'s call-free
`body1_seg`.

`bodyC_segS`: by induction on the lowering's closed form without the depth
counter (`lowerC` at `frames = none`, every call plain), at the caller's
frames `fs`, from the node at the body's start to the return's exit
(`retN`) or the overflow abort label (`abortN`), given the code of the open
block at `pc` (`CodeC`, `Spike/Lib/LowerA64/BlocksC1Code.lean`) and of each
later block not ending in `unreachable` at its label (`BlocksCodeC`), and
the plain call as a premise (`CallC`).

The ghost `c0` ranges over controls of a predicate `G0` closed under the
caller's frame runs (in practice: reached by the program, no hold); the
aborts (the body's own overflow abort label, and any abort inside a callee at
deeper frames) all exit to one given fragment `Ab`.

- `let x = a`, `let x = a + b`, `let x = a - b`, `if a = b then yes else
  no`, `ret a`: `Body1`'s per-construct segments (`add_seg`, `store_seg`,
  `sub_seg`, `br_seg`, `jmp_seg`, `ret_seg`) at the memory side of `fs`,
  lifted to the frames (`SegWS.liftS`); their code is a part of the code of
  an instruction (`SubCd`).
- `let x = g(a)`: the plain call (`CallC`: from the node at the call to the
  node at `e` past the call's code, `w`'s load into `x0`, `bl g`, `x0`'s
  store into `r%n`, or to `Ab`), the ghost `c0` (the function's entry
  control, `bodyN`'s `LocalRun c0 c`) re-anchored at the return: the exit
  `ExitC` has a frame run from `c0` to the ghost of the exit node.
-/
import Spike.Lib.LowerA64.BlocksC1Code
import Spike.Lib.LowerA64.NodeTp
import Spike.Lib.LowerEnvImmC1
import Spike.Lib.LowerEnvImmC1Of
import Spike.Lib.LowerCallC1
import Spike.Lib.SegS

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64 (CodeAt)
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl WordsRep WordRep SRep)
open Spike.Lib.LowerNode
open Spike.Lib.LowerShape (lowerC_atom_inv lowerC_add_inv lowerC_sub_inv lowerC_call_inv lowerC_ifeq_inv
  lowerC_ret_inv)
open Scc.Lower.Inv (lowerC atomV Res1 scalar1 regName labName depthPre depthTerm deepBlock callPost cntC
  lowerC_next)

set_option linter.unusedSimpArgs false

/-! ## Parts of an instruction's code -/

/-- **A part of a code block**: `blk` at `pc` is a part of a block `Cd`
gives (some code before it, some after). -/
def SubCd (Cd : Int64 → List Directive → Prop) (pc : Int64) (blk : List Directive) : Prop :=
  ∃ pc0 pre suf, Cd pc0 (pre ++ blk ++ suf) ∧ pc0 + Int64.ofNat (4 * pre.length) = pc

theorem SubCd.cdOf {Cd : Int64 → List Directive → Prop} {exe : _root_.Executable} {endPc : Int64}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk) {pc : Int64} {blk : List Directive}
    (h : SubCd Cd pc blk) : CdOf exe endPc pc blk := by
  obtain ⟨pc0, pre, suf, h, rfl⟩ := h
  intro s he hp
  have := ((hCd _ _ h s he hp).drop pre.length).take blk.length
  simpa [List.append_assoc] using this

theorem SubCd.whole {Cd : Int64 → List Directive → Prop} {pc : Int64} {blk : List Directive}
    (h : Cd pc blk) : SubCd Cd pc blk :=
  ⟨pc, [], [], by simpa using h, by simp⟩

theorem SubCd.left {Cd : Int64 → List Directive → Prop} {pc : Int64} {a b : List Directive}
    (h : Cd pc (a ++ b)) : SubCd Cd pc a :=
  ⟨pc, [], b, by simpa using h, by simp⟩

theorem SubCd.right {Cd : Int64 → List Directive → Prop} {pc : Int64} {a b : List Directive}
    (h : Cd pc (a ++ b)) : SubCd Cd (pc + Int64.ofNat (4 * a.length)) b :=
  ⟨pc, a, [], by simpa using h, rfl⟩

theorem add_ofNat_four_succ (pc : Int64) (n : Nat) :
    pc + Int64.ofNat (4 * (n + 1)) = pc + Int64.ofNat (4 * n) + 4 := by
  rw [Nat.mul_add, Int64.ofNat_add, Int64.add_assoc]; rfl

/-! ## `CodeC`'s arms -/

section Arms

variable {cx : FnCtx} {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}

/-- **A checked `+`'s code**: the add's block, then the store's, then the rest. -/
theorem codeC_addChk (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) {k : Nat} {pc : Int64} {d : Scc.IR.Reg}
    {a b : Scc.IR.Operand} {is : List Scc.IR.Inst} {tm : Scc.IR.Term}
    (h : CodeC cx Cd Bl k pc (.addChk d a b :: is) tm) :
    ∃ la lb off, cx.getOp .X9 a = .ok la ∧ cx.getOp .X10 b = .ok lb ∧ cx.slotOff d = .ok off ∧
      SubCd Cd pc (addDirs cx la lb) ∧ SubCd Cd (pc + Int64.ofNat (4 * (addDirs cx la lb).length)) (strDirs off) ∧
      CodeC cx Cd Bl (k + 1) (pc + Int64.ofNat (4 * (addDirs cx la lb).length) + 4) is tm := by
  rcases h with ⟨-, l, hl, hc, hrest⟩ | ⟨d', g, w, lw, ls, he, -⟩
  · obtain ⟨la, lb, off, ha, hb, hd, hds⟩ := inst_addChk_inv hf h1 hl
    rw [hds] at hc hrest
    refine ⟨la, lb, off, ha, hb, hd, SubCd.left hc, SubCd.right hc, ?_⟩
    rw [List.length_append, show (strDirs off).length = 1 from rfl, add_ofNat_four_succ] at hrest
    exact hrest
  · cases he

/-- **A saturating `-`'s code**: the subtraction's block, then the store's,
then the rest. -/
theorem codeC_subSat (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) {k : Nat} {pc : Int64} {d : Scc.IR.Reg}
    {a b : Scc.IR.Operand} {is : List Scc.IR.Inst} {tm : Scc.IR.Term}
    (h : CodeC cx Cd Bl k pc (.subSat d a b :: is) tm) :
    ∃ la lb off, cx.getOp .X9 a = .ok la ∧ cx.getOp .X10 b = .ok lb ∧ cx.slotOff d = .ok off ∧
      SubCd Cd pc (subDirs la lb) ∧ SubCd Cd (pc + Int64.ofNat (4 * (subDirs la lb).length)) (strDirs off) ∧
      CodeC cx Cd Bl (k + 1) (pc + Int64.ofNat (4 * (subDirs la lb).length) + 4) is tm := by
  rcases h with ⟨-, l, hl, hc, hrest⟩ | ⟨d', g, w, lw, ls, he, -⟩
  · obtain ⟨la, lb, off, ha, hb, hd, hds⟩ := inst_subSat_inv hf h1 hl
    rw [hds] at hc hrest
    refine ⟨la, lb, off, ha, hb, hd, SubCd.left hc, SubCd.right hc, ?_⟩
    rw [List.length_append, show (strDirs off).length = 1 from rfl, add_ofNat_four_succ] at hrest
    exact hrest
  · cases he

/-- **An `if`'s code**: the compare-and-branch's block, then the `b` to the
`else` label. -/
theorem codeC_br {k : Nat} {pc : Int64} {a b : Scc.IR.Operand} {t f : Scc.IR.Label}
    (h : CodeC cx Cd Bl k pc [] (.br .eq a b t f)) :
    ∃ la lb T Fl, cx.getOp .X9 a = .ok la ∧ cx.getOp .X10 b = .ok lb ∧
      cx.blockLabel t = .ok T ∧ cx.blockLabel f = .ok Fl ∧ SubCd Cd pc (brDirs la lb T) ∧
      SubCd Cd (pc + Int64.ofNat (4 * (brDirs la lb T).length)) (jmpDirs Fl) := by
  rcases h with h | ⟨l, hl, hc⟩
  · cases h
  · obtain ⟨la, lb, T, Fl, ha, hb, hT, hF, hds⟩ := term_br_inv hl
    rw [hds] at hc
    exact ⟨la, lb, T, Fl, ha, hb, hT, hF, SubCd.left hc, SubCd.right hc⟩

/-- **A one-word `ret`'s code**: the word's load, the frame's exit, `ret`. -/
theorem codeC_ret {k : Nat} {pc : Int64} {w : Scc.IR.Operand} (h : CodeC cx Cd Bl k pc [] (.ret [w])) :
    ∃ l, cx.getOp .X0 w = .ok l ∧ SubCd Cd pc (directives (l ++ cx.leave ++ [ret])) := by
  rcases h with h | ⟨l, hl, hc⟩
  · cases h
  · obtain ⟨lw, hw, rfl⟩ := term_ret_inv hl
    exact ⟨lw, hw, SubCd.whole hc⟩

end Arms

/-! ## The closed form's facts -/

/-- **`lowerC`'s terminator is never `unreachable`** (only the bracket's
abort block `deepBlock` ends in it). -/
theorem lowerC_term_ne (lcx : Scc.Lower.Ctx) :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (l : Label) (k : Nat) (r : Res1),
      lowerC lcx env n l k e = some r → r.term ≠ .unreachable := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n l k r hr
    cases op with
    | atom a =>
      obtain ⟨t, w, r', -, -, hr', rfl⟩ := lowerC_atom_inv hr
      exact ih _ _ _ _ r' hr'
    | add a b =>
      obtain ⟨_, _, _, _, r', -, -, hr', rfl⟩ := lowerC_add_inv hr
      exact ih _ _ _ _ r' hr'
    | sub a b =>
      obtain ⟨_, _, _, _, r', -, -, hr', rfl⟩ := lowerC_sub_inv hr
      exact ih _ _ _ _ r' hr'
    | call g is a ts =>
      obtain ⟨_, _, _, -, -, -, -, h⟩ := lowerC_call_inv hr
      rcases h with ⟨-, r', hr', rfl⟩ | ⟨fr, r', -, -, rfl⟩
      · exact ih _ _ _ _ r' hr'
      · simp [depthTerm]
    | _ => simp [lowerC] at hr
  | ifeq a b yes no _ _ =>
    intro env n l k r hr
    obtain ⟨_, _, _, _, _, _, -, -, -, -, rfl⟩ := lowerC_ifeq_inv hr
    simp
  | ret a =>
    intro env n l k r hr
    obtain ⟨_, _, -, rfl⟩ := lowerC_ret_inv hr
    simp
  | _ => intro env n l k r hr; simp [lowerC] at hr

/-- A call's result register is fresh past itself. -/
theorem Fresh.callC1 {env : Scc.Lower.Env} {n : Nat} (h : Fresh env n) (x : String) :
    Fresh ((x, .int, [.reg (regName "r" n)]) :: env) (n + 1) := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · intro o ho r hr y k hk
    simp only [List.mem_singleton] at ho
    subst ho; cases hr
    exact Scc.Lower.Inv.regName_ne (by omega)
  · intro o ho r hr y k hk
    exact h v hv o ho r hr y k (by omega)

/-- **A `ret` of one word**: at a point of the walk at `ret a`, `a` is one
word (an `Int`; `Accepted1`'s return type). -/
def RetOne (q : Expr × Scc.Lower.Env × Nat) : Prop :=
  ∀ a, q.1 = .ret a → ∃ t w, atomV q.2.1 a = some (t, [w])

/-! ## Segments with an exit kept -/

namespace SegWS

variable {I : ISA} {W : FragS I} {K : I.State → I.State → Prop} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
  {ms : List TermRun.Frame → MemSide I} {P Q R E : FragS I}

/-- Continue the normal exit `Q` with a segment to `R`, keeping a second
exit `E` as it is (`SegW.seq_left` at depth). -/
theorem seq_left (h₁ : SegWS W K p lbl ms P (fun s c fs => Q s c fs ∨ E s c fs)) (h₂ : SegWS W K p lbl ms Q R) :
    SegWS W K p lbl ms P (fun s c fs => R s c fs ∨ E s c fs) := by
  obtain ⟨i₁, hs₁, hw₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, hw₂, ho₂⟩ := h₂
  refine ⟨fun s c fs => i₁ s c fs ∨ i₂ s c fs, fun s c fs h => .inl (hs₁ s c fs h),
    fun s c fs h => h.elim (hw₁ s c fs) (hw₂ s c fs), ?_⟩
  have hX₁ : ∀ s c fs, (i₁ s c fs ∨ (Q s c fs ∨ E s c fs)) →
      ((i₁ s c fs ∨ i₂ s c fs) ∨ (R s c fs ∨ E s c fs)) := by
    rintro s c fs (h | h | h)
    · exact .inl (.inl h)
    · exact .inl (.inr (hs₂ s c fs h))
    · exact .inr (.inr h)
  have hX₂ : ∀ s c fs, (i₂ s c fs ∨ R s c fs) → ((i₁ s c fs ∨ i₂ s c fs) ∨ (R s c fs ∨ E s c fs)) :=
    fun s c fs h => h.elim (fun h => .inl (.inr h)) fun h => .inr (.inl h)
  rintro s c fs (h | h)
  · obtain ⟨ho, hk⟩ := ho₁ s c fs h
    exact ⟨fun hK => (ho hK).mono fun s c fs h => h.mono hX₁, hk.mono hX₁⟩
  · obtain ⟨ho, hk⟩ := ho₂ s c fs h
    exact ⟨fun hK => (ho hK).mono fun s c fs h => h.mono hX₂, hk.mono hX₂⟩

end SegWS

/-! ## The body -/

section BodyC

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : FragS isaLSE2} {K : State → State → Prop}

/-- **The body's exits at the frames `fs`**, the ghost re-anchored after
the calls: the function's entry control `c0` runs (with calls) to `c0'`, and
the pair is at the return's exit from `c0'`, the thread pointer `tp` in
`tpidr_el0`; or an abort (`Ab`: the body's own overflow abort label, or an
abort at deeper frames inside a callee). -/
def ExitC (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (fs : List TermRun.Frame)
    (Ab : FragS isaLSE2) : FragS isaLSE2 := fun s c fs' =>
  (fs' = fs ∧ ∃ c0', FrameRun p (c0, fs) (c0', fs) ∧ At exe endPc R F ((retN p lbl fp ra c0').withTp tp) s c) ∨
    Ab s c fs'

/-- **The plain call**: from the node at `let x = g(a)` (its code at `pc`:
`w`'s load `lw` into `x0`, `bl g` with the return label `spK` after it, `x0`'s
store `ls` into the result register `r%n`; the ghost `c0` in `G0`, the term in
`T`, the continuation's free variables bound and its immediates `i`'s with
`x` the call's result) to the node at `e` past the call's code, at the same
frames, the ghost re-anchored at the return, `x` bound to `r%n`; or to an
abort inside the callee (`Ab`). The nodes have the thread pointer `tp`
(`ND.withTp`). -/
def CallC (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lcx : Scc.Lower.Ctx) (cx : FnCtx)
    (Cd : Int64 → List Directive → Prop) (Bl : Int64 → Label → Nat → Prop) (exe : _root_.Executable)
    (endPc : Int64) (R : Region) (F : MachineData → Prop) (W : FragS isaLSE2) (K : State → State → Prop)
    (ms : List TermRun.Frame → MemSide isaLSE2) (fp ra : BitVec 64) (tp : UInt64) (fs : List TermRun.Frame)
    (G0 : Ctl → Prop) (i : Expr → String → Nat → Option Nat) (T : Expr → Prop) (Ab : FragS isaLSE2) : Prop :=
  ∀ (c0 : Ctl) (pc : Int64) (kk : Nat) (env : Scc.Lower.Env) (n : Nat) (x g : String) (is : List String)
    (a : At) (ts : List Ty) (e : Expr) (t : Ty) (w : Scc.IR.Operand) (lw ls : List Item),
    G0 c0 → T (.let_ x (.call g is a ts) e) →
    lcx.frames = none → Spike.Lib.LowerCall.Callee lcx g → atomV env a = some (t, [w]) → Fresh env n →
    cx.getOp .X0 w = .ok lw → cx.setReg (regName "r" n) .X0 = .ok ls → Cd pc (directives lw) →
    Bl (pc + Int64.ofNat (4 * (directives lw).length)) (Scc.Lower.Names.user g) kk →
    Cd (pc + Int64.ofNat (4 * (directives lw).length) + 4) (directives ls) →
    (∀ y ∈ Scc.Sem.exprFv e, (lookupS (ofEnv ((x, .int, [.reg (regName "r" n)]) :: env)) y).isSome) →
    ImmIn i (ofEnv ((x, .int, [.reg (regName "r" n)]) :: env)) e →
    SegWS W K p lbl ms
      ((At exe endPc R F ((bodyN p lbl cx fp ra c0 pc (.let_ x (.call g is a ts) e) (ofEnv env)).withTp tp)).at fs)
      (fun s c fs' => (fs' = fs ∧ ∃ c0', FrameRun p (c0, fs) (c0', fs) ∧
        At exe endPc R F ((bodyN p lbl cx fp ra c0'
          (pc + Int64.ofNat (4 * (directives lw).length) + 4 + Int64.ofNat (4 * (directives ls).length)) e
          (ofEnv ((x, .int, [.reg (regName "r" n)]) :: env))).withTp tp) s c) ∨
        Ab s c fs')

/-- **A lowered `Accepted1` body with calls is one segment at the frames
`fs`**: from the node at the body (the lowering's environment `env` placed
in the frame, the ghost `c0`, the thread pointer `tp`) to the body's exits
(`ExitC`). The code
predicate `Cd` gives the code (`hCd`): the open block's at `pc` (`CodeC`),
the later blocks' at their labels (`BlocksCodeC`); the blocks' states are
inside `W₀` (inside `W` at `fs`, `hW₀`) at the body's nodes (`hW`) and
pending stores (`hWp`) over every part of a code block (`SubCd`) that is a
construct's block (`Kind1`; the call's pieces are `CallC`'s), for every
ghost in `G0` (closed under the frame runs at `fs`, `hG0`); the body's own
overflow abort label is an abort (`hab`); the plain calls (`hcl`, the
lowering without the depth counter, `hfrm`); at each
point of the lowering's walk (`lowerEnvsC`) its environment's immediates are
`i`'s (`hImm`), the point satisfies `T`, and a `ret` there is of one word
(`hOne`). -/
theorem bodyC_segS {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {Cd : Int64 → List Directive → Prop}
    {Bl : Int64 → Label → Nat → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isaLSE2} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRun p (c, fs) (c', fs) → G0 c')
    (hW : ∀ c0, G0 c0 → ∀ pc t s blk, SubCd Cd pc blk → Kind1 cx blk →
      BlkW W₀ K exe endPc R F (bodyN p lbl cx fp ra c0 pc t s) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s k blk, SubCd Cd pc blk → Kind1 cx blk →
      BlkW W₀ K exe endPc R F (pendN p lbl cx fp ra c0 pc t s k) blk)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isaLSE2}
    (hab : ∀ c0, G0 c0 → ∀ s c,
      At exe endPc R F (abortN i T p lbl cx (_root_.Executable.labels exe).label fp ra c0) s c → Ab s c fs)
    {lcx : Scc.Lower.Ctx} (hfrm : lcx.frames = none) {tp : UInt64}
    (hcl : CallC p lbl lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab) :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (l : Label) (k : Nat) (r : Res1) (kk : Nat) (pc : Int64),
      lowerC lcx env n l k e = some r → Fresh env n →
      CodeC cx Cd Bl kk pc r.insts r.term →
      BlocksCodeC cx Cd Bl (_root_.Executable.labels exe).label r.blocks →
      (∀ q ∈ lowerEnvsC lcx.frames env n e, ImmIn i (ofEnv q.2.1) q.1 ∧ T q.1) →
      (∀ q ∈ lowerEnvsC lcx.frames env n e, RetOne q) →
      ∀ c0, G0 c0 → SegWS W K p lbl ms ((At exe endPc R F ((bodyN p lbl cx fp ra c0 pc e (ofEnv env)).withTp tp)).at fs)
        (ExitC p lbl exe endPc R F fp ra tp c0 fs Ab) := by
  have hCd' : ∀ {pc blk}, SubCd Cd pc blk → CdOf exe endPc pc blk := fun h => SubCd.cdOf hCd h
  -- the exits of a segment at the ghost itself
  have hexit : ∀ c0 s c fs', At exe endPc R F ((retN p lbl fp ra c0).withTp tp) s c → fs' = fs →
      ExitC p lbl exe endPc R F fp ra tp c0 fs Ab s c fs' :=
    fun c0 _ _ _ h e => .inl ⟨e, c0, .refl _, h⟩
  have habx : ∀ c0, G0 c0 → ∀ s c fs', At exe endPc R F ((abortN i T p lbl cx (_root_.Executable.labels exe).label
      fp ra c0).withTp tp) s c → fs' = fs → ExitC p lbl exe endPc R F fp ra tp c0 fs Ab s c fs' :=
    fun c0 hg s c _ ⟨he, hn, hd, hpc, σ, hA, hFm, hJ, _⟩ e => .inr (e ▸ hab c0 hg s c ⟨he, hn, hd, hpc, σ, hA, hFm, hJ⟩)
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n l k r kk pc hr hfr hcode hbl hImm hOne c0 hg0
    cases op with
    | atom a =>
      obtain ⟨t, w, r', ha, -, hr', rfl⟩ := lowerC_atom_inv hr
      have ih' := ih _ n l k r' kk pc hr' (hfr.atom ha x) hcode hbl (immIn_tailC_atom ha hImm)
        (immIn_tailC_atom ha hOne) c0 hg0
      refine ih'.mono_pre fun s c fs' ⟨⟨he, hn, hd, hpc, σ, hA, hFm, ⟨hJ, hfj, hc0⟩, htp⟩, hfs⟩ =>
        ⟨⟨he, hn, hd, hpc, σ, hA, hFm, ⟨?_, hfj, hc0⟩, htp⟩, hfs⟩
      rw [ofEnv_cons]
      exact hJ.atom (sevalAt_ofEnv ha)
    | add a b =>
      obtain ⟨ta, pa, tb, pb, r', ha, hb, hr', rfl⟩ := lowerC_add_inv hr
      obtain ⟨la, lb, off, hla, hlb, hd, hc1, hc2, hrest⟩ := codeC_addChk hf h1 hcode
      have hfv := lowerC_fv lcx (.let_ x (.add a b) e) env n l k _ hr
      have hadd := ((add_edge (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0) (x := x) (e := e)
        hf h1 h16 hla hlb hd (_root_.Executable.labels exe).label
        (sevalAt_ofEnv ha) (sevalAt_ofEnv hb) (hfr.ofEnv x)
        (fun y hy => isSome_lookupS_ofEnv (hfv y hy)) (immIn_headC hImm).1 (immIn_headC hImm).2).tp tp).seg
        (W := W₀) (K := K) (lbl := lbl) (ms := ms fs) hF hR hal hlo hhi (hCd' hc1) (BlkW.withTp (hW c0 hg0 _ _ _ _ hc1 (.inl ⟨pa, pb, la, lb, hla, hlb, .inl rfl⟩)) tp)
      have hst := ((store_edge (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0) (t := e)
        (s := (x, .int, [.one (.reg (regName x n))]) :: ofEnv env) hf h1 h16 hd
        (_root_.Executable.labels exe).label).tp tp).seg (W := W₀) (K := K) (lbl := lbl) (ms := ms fs)
        hF hR hal hlo hhi (hCd' hc2) (BlkW.withTp (hWp c0 hg0 _ _ _ _ _ hc2 (.inr (.inl ⟨_, off, hd, rfl⟩))) tp)
      have h0 := SegW.seq_left (hadd.mono_post fun s c h => h.elim (fun ⟨_, h⟩ => .inl h)
        fun ⟨_, h⟩ => .inr h) (hst.mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim)
      have ih' := ih _ (n + 1) l (k + 1) r' (kk + 1) _ hr' (hfr.add x) hrest hbl (immIn_tailC_add hImm)
        (immIn_tailC_add hOne) c0 hg0
      rw [ofEnv_cons] at ih'
      refine (SegWS.seq_left
        (E := (At exe endPc R F ((abortN i T p lbl cx (_root_.Executable.labels exe).label fp ra c0).withTp tp)).at fs)
        ?_ ih').mono_post ?_
      · exact (SegWS.liftS fs h0 hW₀).mono_post fun s c fs' ⟨h, e⟩ => h.imp (fun h => ⟨h, e⟩) (fun h => ⟨h, e⟩)
      · rintro s c fs' (h | ⟨h, rfl⟩)
        · exact h
        · exact habx c0 hg0 s c _ h rfl
    | sub a b =>
      obtain ⟨ta, pa, tb, pb, r', ha, hb, hr', rfl⟩ := lowerC_sub_inv hr
      obtain ⟨la, lb, off, hla, hlb, hd, hc1, hc2, hrest⟩ := codeC_subSat hf h1 hcode
      have hsub := (((sub_edge (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0) (x := x) (e := e)
        hf h1 h16 hla hlb hd (_root_.Executable.labels exe).label
        (sevalAt_ofEnv ha) (sevalAt_ofEnv hb) (hfr.ofEnv x)).tp tp).seg
        (W := W₀) (K := K) (lbl := lbl) (ms := ms fs) hF hR hal hlo hhi (hCd' hc1) (BlkW.withTp (hW c0 hg0 _ _ _ _ hc1 (.inl ⟨pa, pb, la, lb, hla, hlb, .inr (.inl rfl)⟩)) tp)).mono_post
        fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
      have hst := (((store_edge (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0) (t := e)
        (s := (x, .int, [.one (.reg (regName x n))]) :: ofEnv env) hf h1 h16 hd
        (_root_.Executable.labels exe).label).tp tp).seg (W := W₀) (K := K) (lbl := lbl) (ms := ms fs)
        hF hR hal hlo hhi (hCd' hc2) (BlkW.withTp (hWp c0 hg0 _ _ _ _ _ hc2 (.inr (.inl ⟨_, off, hd, rfl⟩))) tp)).mono_post
        fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
      have ih' := ih _ (n + 1) l (k + 1) r' (kk + 1) _ hr' (hfr.add x) hrest hbl (immIn_tailC_sub hImm)
        (immIn_tailC_sub hOne) c0 hg0
      rw [ofEnv_cons] at ih'
      exact (SegWS.liftS fs (hsub.seq hst) hW₀).seq ih'
    | call g is a ts =>
      obtain ⟨dg, t, w, hx, hd, hrt, ha, h⟩ := lowerC_call_inv hr
      rcases h with ⟨-, r', hr', rfl⟩ | ⟨fr', r', hfr', -, -⟩
      rotate_left
      · rw [hfrm] at hfr'; cases hfr'
      rcases hcode with ⟨hc, -⟩ | ⟨d', g', w', lw, ls, he, hw, hs, hcw, hb, hcs, hrest⟩
      · simp [Spike.Lib.LowerShape.isCall] at hc
      simp only [Scc.IR.Inst.call.injEq, List.cons.injEq, and_true] at he
      obtain ⟨rfl, hg, rfl⟩ := he
      rw [← hg] at hb
      have h1' : (n + if lcx.frames.isSome then 7 else 1) = n + 1 := by simp [hfrm]
      have hImm' := immIn_tailC_call hImm
      have hOne' := immIn_tailC_call hOne
      rw [h1'] at hImm' hOne'
      have hseg := hcl c0 pc kk env n x g is a ts e t w lw ls hg0 (immIn_headC hImm).2 hfrm
        ⟨hx, dg, hd, hrt⟩ ha hfr hw hs hcw hb hcs
        (fun y hy => isSome_lookupS_ofEnv (lowerC_fv lcx e _ _ _ _ _ hr' y hy)) (immIn_headC hImm').1
      refine (SegWS.seq_left (E := Ab) (R := ExitC p lbl exe endPc R F fp ra tp c0 fs Ab) hseg ((SegWS.exists_pre
        (P := fun c0' s c fs' => FrameRun p (c0, fs) (c0', fs) ∧
          (At exe endPc R F ((bodyN p lbl cx fp ra c0'
            (pc + Int64.ofNat (4 * (directives lw).length) + 4 + Int64.ofNat (4 * (directives ls).length)) e
            (ofEnv ((x, .int, [.reg (regName "r" n)]) :: env))).withTp tp)).at fs s c fs') fun c0' => ?_).mono_pre ?_)).mono_post
        ?_
      · by_cases hrun : FrameRun p (c0, fs) (c0', fs)
        · exact ((ih _ (n + 1) _ (k + 1) r' (kk + 1) _ hr' (Fresh.callC1 hfr x) hrest hbl hImm' hOne' c0'
            (hG0 _ _ hg0 hrun)).mono_pre fun s c fs' h => h.2).mono_post fun s c fs' h =>
              h.imp_left fun ⟨hfs, c1, hr1, hx1⟩ => ⟨hfs, c1, hrun.trans hr1, hx1⟩
        · exact SegWS.empty fun s c fs' h => hrun h.1
      · rintro s c fs' ⟨hfs, c0', hrun, hA⟩
        exact ⟨c0', hrun, hA, hfs⟩
      · rintro s c fs' (h | h)
        · exact h
        · exact .inr h
    | _ => simp [lowerC] at hr
  | ifeq a b yes no ihy ihn =>
    intro env n l k r kk pc hr hfr hcode hbl hImm hOne c0 hg0
    obtain ⟨ta, pa, tb, pb, ry, rn, ha, hb, hy, hn, rfl⟩ := lowerC_ifeq_inv hr
    obtain ⟨la, lb, Tl, Fl, hla, hlb, hT, hFl, hc1, hc2⟩ := codeC_br hcode
    obtain ⟨Ly, ky, hLy, hcy⟩ := hbl ⟨labName "then" n, ry.insts, ry.term⟩ (List.mem_cons_self ..)
      (lowerC_term_ne lcx _ _ _ _ _ _ hy)
    obtain ⟨Ln, kn, hLn, hcn⟩ := hbl ⟨labName "else" (n + 1), rn.insts, rn.term⟩ (by simp)
      (lowerC_term_ne lcx _ _ _ _ _ _ hn)
    simp only [hT, Except.ok.injEq] at hLy
    simp only [hFl, Except.ok.injEq] at hLn
    subst hLy hLn
    have hbly : BlocksCodeC cx Cd Bl (_root_.Executable.labels exe).label ry.blocks :=
      fun b hb => hbl b (by simp [hb])
    have hbln : BlocksCodeC cx Cd Bl (_root_.Executable.labels exe).label rn.blocks :=
      fun b hb => hbl b (by simp [hb])
    have hnext := lowerC_next lcx yes env (n + 2) _ 0 ry hy
    have segy := ihy env (n + 2) _ 0 ry ky _ hy (hfr.mono (by omega)) hcy hbly (immIn_tailC_yes hImm)
      (immIn_tailC_yes hOne) c0 hg0
    have segn := ihn env ry.next _ 0 rn kn _ hn (hfr.mono (by omega)) hcn hbln
      (by rw [hnext]; exact immIn_tailC_no hImm) (by rw [hnext]; exact immIn_tailC_no hOne) c0 hg0
    have hbr' := (((br_edge (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0) (yes := yes) (no := no)
      hf h1 h16 hla hlb Tl (_root_.Executable.labels exe).label (sevalAt_ofEnv ha) (sevalAt_ofEnv hb)).tp tp).seg
      (W := W₀) (K := K) (lbl := lbl) (ms := ms fs) hF hR hal hlo hhi (hCd' hc1) (BlkW.withTp (hW c0 hg0 _ _ _ _ hc1 (.inl ⟨pa, pb, la, lb, hla, hlb, .inr (.inr ⟨Tl, rfl⟩)⟩)) tp)).mono_post
      fun st c h => show At exe endPc R F ((bodyN p lbl cx fp ra c0 ((_root_.Executable.labels exe).label Tl) yes
          (ofEnv env)).withTp tp) st c ∨ At exe endPc R F ((bodyN p lbl cx fp ra c0
          (pc + Int64.ofNat (4 * (brDirs la lb Tl).length)) no (ofEnv env)).withTp tp) st c from by
        rcases h with ⟨bb, h⟩ | ⟨e, _⟩
        · cases bb
          · exact .inr h
          · exact .inl h
        · exact e.elim
    have hj := (((jmp_edge (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0) (t := no) (s := ofEnv env)
      (cx := cx) Fl (_root_.Executable.labels exe).label).tp tp).seg (W := W₀) (K := K) (lbl := lbl) (ms := ms fs)
      hF hR hal hlo hhi (hCd' hc2) (BlkW.withTp (hW c0 hg0 _ _ _ _ hc2 (.inr (.inr (.inl ⟨Fl, rfl⟩)))) tp)).mono_post
      fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
    refine ((SegWS.liftS fs hbr' hW₀).mono_post fun s c fs' ⟨h, e⟩ =>
      h.imp (fun h => ⟨h, e⟩) (fun h => ⟨h, e⟩)).seq (SegWS.or_pre segy ((SegWS.liftS fs hj hW₀).seq segn))
  | ret a =>
    intro env n l k r kk pc hr hfr hcode _ _ hOne c0 hg0
    obtain ⟨t, ws, ha, rfl⟩ := lowerC_ret_inv hr
    obtain ⟨t', w, ha'⟩ := immIn_headC hOne a rfl
    rw [ha] at ha'
    cases ha'
    obtain ⟨l', hl, hc⟩ := codeC_ret hcode
    have hret := (((ret_edge (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0) hf h1 h16 hl
      (_root_.Executable.labels exe).label (sevalAt_ofEnv ha)).tp tp).seg (W := W₀) (K := K) (lbl := lbl) (ms := ms fs)
      hF hR hal hlo hhi (hCd' hc) (BlkW.withTp (hW c0 hg0 _ _ _ _ hc (.inr (.inr (.inr ⟨_, l', hl, rfl⟩)))) tp)).mono_post
      fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
    exact ((SegWS.liftS fs hret hW₀)).mono_post fun s c fs' ⟨h, e⟩ => hexit c0 s c fs' h e
  | _ => intro env n l k r kk pc hr; simp [lowerC] at hr

end BodyC

end Spike.Lib.LowerA64
