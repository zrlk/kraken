/-
**A lowered `Accepted1` body with calls is one segment at fixed frames**
(x86-64), the twin of `Spike/Lib/LowerA64/BodyC.lean`, next to
`Spike/Lib/LowerX64/Body1.lean`'s call-free `body1_seg`.

- `SubCd`: a sized block inside a block the code predicate `Cd` holds of
  (`cdOf_sub`: its cells are in the code when the whole block's are);
- `ExitC`: the body's exits at frames `fs`, the ghost entry control
  re-anchored after the calls (`FrameRun` from `c0` at the same frames);
- `CallC`: a plain call's obligation (from the node at
  `let x = call g a in e`, the call `call [r%n] g [w]` first in the code, to
  the node at `e` past it, the ghost re-anchored at the return; proved by
  `callC_of`, `Spike/Lib/LowerX64/CallC.lean`);
- `bodyC_segS`: by induction on `lowerC`: atom/add/sub/if/ret by the
  per-construct edges (`add_edge`, `store_edge`, `sub_edge`, `br_edge`,
  `jmp_edge`, `ret_edge`) between nodes with the thread pointer
  (`BlkEdge.tp`, `Spike/Lib/LowerX64/NodeTp.lean`) lifted with
  `SegWS.liftS fs`, the call by `CallC`.

Where x86-64 differs from AArch64: an instruction's code is the items it
emits from every state (`Emits`), split here into the per-construct blocks
(`emits_add`, `emits_sub`, `emits_br`, `emits_ret`) and their sized cells
(`subCd_split`).
-/
import Spike.Lib.LowerX64.BlocksC1Code
import Spike.Lib.LowerX64.NodeTp
import Spike.Lib.SegS
import Spike.Lib.LowerCallC1
import Spike.Lib.LowerEnvImmC1Of
import Spike.Lib.LowerEnvImmC1

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 (S E Item emitInst emitTerm labelOf ld)
open Spike.Lib.Form (sevalAt SEnv)
open Spike.Lib.LowerNode
open Spike.Lib.LowerShape (lowerC_atom_inv lowerC_add_inv lowerC_sub_inv lowerC_call_inv
  lowerC_ifeq_inv lowerC_ret_inv isCall)
open Spike.Lib.LowerCall (Callee)
open Scc.Lower.Inv (lowerC atomV Res1 regName labName depthTerm lowerC_next)

set_option linter.unusedSimpArgs false

/-! ## Sub-blocks of the code predicate -/

/-- **A sized block inside a block of `Cd`**: `blk` is the middle of a
block `Cd` holds of at `pc0`, at the pc past the cells before it. -/
def SubCd (Cd : Int64 → List (Directive × Nat) → Prop) (pc : Int64) (blk : List (Directive × Nat)) : Prop :=
  ∃ pc0 pre post, Cd pc0 (pre ++ blk ++ post) ∧ pc = pc0 + Int64.ofNat (pre.map (·.2)).sum

theorem SubCd.whole {Cd : Int64 → List (Directive × Nat) → Prop} {pc : Int64} {blk : List (Directive × Nat)}
    (h : Cd pc blk) : SubCd Cd pc blk :=
  ⟨pc, [], [], by simpa using h, by simp⟩

/-- **A sub-block's cells are in the code** when the whole block's are. -/
theorem cdOf_sub {exe : _root_.Executable} {endPc pc0 : Int64} {pre blk post : List (Directive × Nat)}
    (h : CdOf exe endPc pc0 (pre ++ blk ++ post)) :
    CdOf exe endPc (pc0 + Int64.ofNat (pre.map (·.2)).sum) blk := by
  intro s he hn j d z hj
  have hjl : j < blk.length := by
    rcases Nat.lt_or_ge j blk.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hj; cases hj
  have hj' : (pre ++ blk ++ post)[pre.length + j]? = some (d, z) := by
    rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left hjl]
    exact hj
  have hc := h s he hn _ _ _ hj'
  have hoff : cellOff (pre ++ blk ++ post) (pre.length + j) = (pre.map (·.2)).sum + cellOff blk j := by
    unfold cellOff
    rw [List.append_assoc, List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
      List.take_append_of_le_length (by omega), List.map_append, List.sum_append]
  rwa [hoff, Int64.ofNat_add, ← Int64.add_assoc] at hc

/-- **`hCd` at sub-blocks.** -/
theorem cdOf_subCd {exe : _root_.Executable} {endPc : Int64} {Cd : Int64 → List (Directive × Nat) → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk) :
    ∀ pc blk, SubCd Cd pc blk → CdOf exe endPc pc blk := by
  rintro _ _ ⟨pc0, pre, post, h, rfl⟩
  exact cdOf_sub (hCd _ _ h)

/-- **A construct's directives at any sizes of their length are a
construct's block** (`Kind1`). -/
theorem kind1_zip {fr : Scc.Emit.X64.Frame} {ds : List Directive} (hk : KindD fr ds) {zs : List Nat}
    (hz : zs.length = ds.length) : Kind1 fr (ds.zip zs) := by
  unfold Kind1
  rwa [List.map_fst_zip (by omega)]

/-- **Splitting a sized block** of `Cd` at the end of `A`: both parts are
sub-blocks, the second at the pc past the first's sizes. -/
theorem subCd_split {Cd : Int64 → List (Directive × Nat) → Prop} {pc : Int64} {A B : List Directive}
    {zs : List Nat} (hz : zs.length = (A ++ B).length) (h : SubCd Cd pc ((A ++ B).zip zs)) :
    ∃ zs1 zs2, zs = zs1 ++ zs2 ∧ zs1.length = A.length ∧ zs2.length = B.length ∧
      SubCd Cd pc (A.zip zs1) ∧ SubCd Cd (pc + Int64.ofNat zs1.sum) (B.zip zs2) := by
  obtain ⟨pc0, pre, post, hc, rfl⟩ := h
  rw [List.length_append] at hz
  have h1 : (zs.take A.length).length = A.length := by rw [List.length_take]; omega
  have h2 : (zs.drop A.length).length = B.length := by rw [List.length_drop]; omega
  have hzip : (A ++ B).zip zs = A.zip (zs.take A.length) ++ B.zip (zs.drop A.length) := by
    conv => lhs; rw [← List.take_append_drop A.length zs]
    exact List.zip_append h1.symm
  rw [hzip] at hc
  refine ⟨_, _, (List.take_append_drop _ _).symm, h1, h2, ⟨pc0, pre, B.zip (zs.drop A.length) ++ post, ?_, rfl⟩,
    ⟨pc0, pre ++ A.zip (zs.take A.length), post, ?_, ?_⟩⟩
  · simpa [List.append_assoc] using hc
  · simpa [List.append_assoc] using hc
  · rw [List.map_append, List.sum_append, List.map_snd_zip (by omega), Int64.ofNat_add, Int64.add_assoc]

/-! ## The constructs' items -/

theorem emits_out {x : E Unit} {l l' : List Item} (h : Emits x l) (h' : x {} = .ok ((), { ({} : S) with
    out := l'.reverse ++ ({} : S).out })) : l = l' := by
  have := h {}
  rw [h'] at this
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at this
  have ho := congrArg S.out this
  simpa using ho.symm

theorem dirs_d (x : Directive) : dirs [Item.d x] = [x] := rfl

/-- **The items of a checked `+`.** -/
theorem emits_add {fr : Scc.Emit.X64.Frame} {sm} {d : Scc.IR.Reg} {a b : Scc.IR.Operand} {l : List Item}
    (h : Emits (emitInst fr sm (.addChk d a b)) l) :
    ∃ la lb off, getOp fr .rax a = .ok la ∧ getOp fr .rcx b = .ok lb ∧ rsOf fr d = some off ∧
      dirs l = addDirs fr la lb ++ [stDir off] := by
  obtain ⟨la, lb, off, ha, hb, hd, hs⟩ := emitInst_add_cases fr sm d a b {} (h {})
  refine ⟨la, lb, off, ha, hb, hd, ?_⟩
  rw [emits_out h (by rw [← hs]; exact h {}), dirs_append, dirs_d, addDirs]

/-- **The items of a saturating `-`.** -/
theorem emits_sub {fr : Scc.Emit.X64.Frame} {sm} {d : Scc.IR.Reg} {a b : Scc.IR.Operand} {l : List Item}
    (h : Emits (emitInst fr sm (.subSat d a b)) l) :
    ∃ la lb off, getOp fr .rax a = .ok la ∧ getOp fr .rcx b = .ok lb ∧ rsOf fr d = some off ∧
      dirs l = subDirs la lb ++ [stDir off] := by
  obtain ⟨la, lb, off, ha, hb, hd, hs⟩ := emitInst_sub_cases fr sm d a b {} (h {})
  refine ⟨la, lb, off, ha, hb, hd, ?_⟩
  rw [emits_out h (by rw [← hs]; exact h {}), dirs_append, dirs_d, subDirs]

/-- **The items of a one-word `ret`.** -/
theorem emits_ret {fr : Scc.Emit.X64.Frame} {w : Scc.IR.Operand} {l : List Item}
    (h : Emits (emitTerm fr (.ret [w])) l) :
    ∃ lw, getOp fr .rax w = .ok lw ∧ dirs l = retDirs lw := by
  rcases ld_cases fr w .rax {} with ⟨lw, hw, -⟩ | ⟨e, he⟩
  · exact ⟨lw, hw, by rw [emits_out h (emitTerm_ret hw {}), retDirs]⟩
  · have h0 := h {}
    rw [Scc.Lower.InvX64.emitTerm_ret1, bind_err he] at h0
    cases h0

theorem ld_err {fr : Scc.Emit.X64.Frame} {a : Scc.IR.Operand} {t : Reg64} {e : String}
    (hg : getOp fr t a = .error e) (s : S) : ∃ e', ld fr a t s = .error e' := by
  rcases ld_cases fr a t s with ⟨l, hl, -⟩ | h
  · rw [hg] at hl; cases hl
  · exact h

/-- **The items of an `if`'s compare-and-branch.** -/
theorem emits_br {fr : Scc.Emit.X64.Frame} {a b : Scc.IR.Operand} {t f : Scc.IR.Label} {l : List Item}
    (h : Emits (emitTerm fr (.br .eq a b t f)) l) :
    ∃ la lb, getOp fr .rax a = .ok la ∧ getOp fr .rcx b = .ok lb ∧
      dirs l = brDirs la lb (labelOf fr.fn t) ++ jmpDirs (labelOf fr.fn f) := by
  have h0 := h {}
  simp only [emitTerm] at h0
  obtain ⟨_, s1, h1, -⟩ := bind_inv h0
  simp only [Scc.Emit.X64.cmpAB] at h1
  obtain ⟨_, s2, h2, h3⟩ := bind_inv h1
  obtain ⟨_, s3, h4, -⟩ := bind_inv h3
  cases ha : getOp fr .rax a with
  | error e => obtain ⟨e', he⟩ := ld_err ha {}; rw [he] at h2; cases h2
  | ok la =>
    cases hb : getOp fr .rcx b with
    | error e => obtain ⟨e', he⟩ := ld_err hb s2; rw [he] at h4; cases h4
    | ok lb =>
      refine ⟨la, lb, rfl, rfl, ?_⟩
      rw [emits_out h (emitTerm_br_eq ha hb t f {}), dirs_append, dirs_d, brDirs, jmpDirs]

/-! ## The closed form's terminators -/

/-- **`lowerC`'s open block never ends in `unreachable`.** -/
theorem lowerC_term_ne (cx : Scc.Lower.Ctx) :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (l : Scc.IR.Label) (k : Nat) (r : Res1),
      lowerC cx env n l k e = some r → r.term ≠ .unreachable := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n l k r hr
    cases op with
    | atom a =>
      obtain ⟨t, w, r', -, -, hr', rfl⟩ := lowerC_atom_inv hr
      exact ih _ _ _ _ r' hr'
    | add a b =>
      obtain ⟨-, -, -, -, r', -, -, hr', rfl⟩ := lowerC_add_inv hr
      exact ih _ _ _ _ r' hr'
    | sub a b =>
      obtain ⟨-, -, -, -, r', -, -, hr', rfl⟩ := lowerC_sub_inv hr
      exact ih _ _ _ _ r' hr'
    | call g is a ts =>
      obtain ⟨-, -, -, -, -, -, -, ⟨-, r', hr', rfl⟩ | ⟨fr, r', -, -, rfl⟩⟩ := lowerC_call_inv hr
      · exact ih _ _ _ _ r' hr'
      · simp [depthTerm]
    | _ => simp [lowerC] at hr
  | ifeq a b yes no =>
    intro env n l k r hr
    obtain ⟨-, -, -, -, ry, rn, -, -, -, -, rfl⟩ := lowerC_ifeq_inv hr
    simp
  | ret a =>
    intro env n l k r hr
    obtain ⟨-, -, -, rfl⟩ := lowerC_ret_inv hr
    simp
  | _ => intro env n l k r hr; simp [lowerC] at hr

/-- A call's result register is fresh past itself. -/
theorem fresh_callC1 {env : Scc.Lower.Env} {n : Nat} (h : Fresh env n) (x : String) :
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

/-- **`hCd` at sub-blocks.** -/
theorem SubCd.cdOf {exe : _root_.Executable} {endPc : Int64} {Cd : Int64 → List (Directive × Nat) → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk) {pc : Int64} {blk : List (Directive × Nat)}
    (h : SubCd Cd pc blk) : CdOf exe endPc pc blk :=
  cdOf_subCd hCd pc blk h

/-! ## Segments at frames -/

/-- Continue the normal exit `Q` with a segment to `R`, keeping a second
exit `E` as it is (`SegW.seq_left` at depth). -/
theorem SegWS.seq_left {I : ISA} {W : FragS I} {K : I.State → I.State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide I} {P Q R E : FragS I}
    (h₁ : SegWS W K p lbl ms P (fun s c fs => Q s c fs ∨ E s c fs)) (h₂ : SegWS W K p lbl ms Q R) :
    SegWS W K p lbl ms P (fun s c fs => R s c fs ∨ E s c fs) := by
  obtain ⟨i₁, hs₁, hw₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, hw₂, ho₂⟩ := h₂
  refine ⟨fun s c fs => i₁ s c fs ∨ i₂ s c fs, fun s c fs h => .inl (hs₁ s c fs h),
    fun s c fs h => h.elim (hw₁ s c fs) (hw₂ s c fs), ?_⟩
  have m₁ : ∀ s c fs, (i₁ s c fs ∨ Q s c fs ∨ E s c fs) →
      (i₁ s c fs ∨ i₂ s c fs) ∨ R s c fs ∨ E s c fs := fun s c fs h => by
    rcases h with h | h | h
    · exact .inl (.inl h)
    · exact .inl (.inr (hs₂ s c fs h))
    · exact .inr (.inr h)
  have m₂ : ∀ s c fs, (i₂ s c fs ∨ R s c fs) → (i₁ s c fs ∨ i₂ s c fs) ∨ R s c fs ∨ E s c fs :=
    fun s c fs h => h.elim (fun h => .inl (.inr h)) fun h => .inr (.inl h)
  rintro s c fs (h | h)
  · obtain ⟨ho, hk⟩ := ho₁ s c fs h
    exact ⟨fun hK => (ho hK).mono fun s c fs h => h.mono m₁, hk.mono m₁⟩
  · obtain ⟨ho, hk⟩ := ho₂ s c fs h
    exact ⟨fun hK => (ho hK).mono fun s c fs h => h.mono m₂, hk.mono m₂⟩

/-- **A two-exit segment at fixed frames** (`SegWS.liftS` keeping the
exits apart). -/
theorem SegWS.liftS_or {I : ISA} {W : FragS I} {K : I.State → I.State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide I} {W₀ P₀ Q₀ E₀ : Frag I}
    (fs : List TermRun.Frame) (h : SegW W₀ K p lbl (ms fs) P₀ (fun s c => Q₀ s c ∨ E₀ s c))
    (hW : ∀ s c, W₀ s c → W s c fs) :
    SegWS W K p lbl ms (P₀.at fs) (fun s c fs' => Q₀.at fs s c fs' ∨ E₀.at fs s c fs') :=
  (SegWS.liftS fs h hW).mono_post fun _ _ _ ⟨h, e⟩ => h.imp (fun h => ⟨h, e⟩) (fun h => ⟨h, e⟩)

section BodyC

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : FragS isa} {K : State → State → Prop}

/-- **The body's exits at frames `fs`**: the return's exit (`retN`) at
`fs`, the ghost re-anchored after the calls (the entry control `c0` runs,
with calls, `FrameRun`, to `c0'` at the same frames), or an abort (`Ab`:
the body's own overflow abort label at `fs`, or an abort inside a callee
at deeper frames). The return's exit has the thread pointer `tp` in the
`%fs` base. -/
def ExitC (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (fs : List TermRun.Frame)
    (Ab : FragS isa) : FragS isa := fun s c fs' =>
  (fs' = fs ∧ ∃ c0', FrameRun p (c0, fs) (c0', fs) ∧ At exe endPc R F ((retN p lbl fp ra c0').withTp tp) s c) ∨
    Ab s c fs'

/-- **A plain call**: from the node at `let x = call g a in e` (the call
`call [r%n] g [w]` first in the code at `pc`, label counter `kk`; the ghost
`c0` in `G0`, the term in `T`, the continuation's free variables bound and
its immediates `i`'s with `x` the call's result) to the node at `e` at the
code of the rest `is'` past the call (counter `kk + 1`), at the same
frames, the ghost re-anchored at the return, or to an abort (`Ab`, inside
the callee). The nodes have the thread pointer `tp` (`ND.withTp`). -/
def CallC (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lcx : Scc.Lower.Ctx) (fr : Scc.Emit.X64.Frame)
    (Cd : Int64 → List (Directive × Nat) → Prop) (Bl : Int64 → Nat → Label → Nat → Prop)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (W : FragS isa)
    (K : State → State → Prop) (ms : List TermRun.Frame → MemSide isa) (fp ra : BitVec 64) (tp : UInt64)
    (fs : List TermRun.Frame) (G0 : Ctl → Prop) (i : Expr → String → Nat → Option Nat) (T : Expr → Prop)
    (Ab : FragS isa) : Prop :=
  ∀ (c0 : Ctl) (pc : Int64) (kk : Nat) (env : Scc.Lower.Env) (n : Nat) (x g : String) (is : List String)
    (a : At) (ts : List Ty) (e : Expr) (t : Ty) (w : Scc.IR.Operand) (is' : List Scc.IR.Inst)
    (tm : Scc.IR.Term),
    G0 c0 → T (.let_ x (.call g is a ts) e) →
    Callee lcx g → atomV env a = some (t, [w]) → Fresh env n →
    CodeC fr Cd Bl kk pc (.call [regName "r" n] (Scc.Lower.Names.user g) [w] :: is') tm →
    (∀ y ∈ Scc.Sem.exprFv e, (Spike.Lib.Form.lookupS (ofEnv ((x, .int, [.reg (regName "r" n)]) :: env)) y).isSome) →
    ImmIn i (ofEnv ((x, .int, [.reg (regName "r" n)]) :: env)) e →
    ∃ pc', CodeC fr Cd Bl (kk + 1) pc' is' tm ∧
      SegWS W K p lbl ms ((At exe endPc R F ((bodyN p lbl fr fp ra c0 pc (.let_ x (.call g is a ts) e)
          (ofEnv env)).withTp tp)).at fs)
        (fun s c fs' => (fs' = fs ∧ ∃ c0', FrameRun p (c0, fs) (c0', fs) ∧
          At exe endPc R F ((bodyN p lbl fr fp ra c0' pc' e
            (ofEnv ((x, .int, [.reg (regName "r" n)]) :: env))).withTp tp) s c) ∨
          Ab s c fs')

theorem exitC_of_ret {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {fs : List TermRun.Frame} {Ab : FragS isa} :
    ∀ s c fs', (At exe endPc R F ((retN p lbl fp ra c0).withTp tp)).at fs s c fs' →
      ExitC p lbl exe endPc R F fp ra tp c0 fs Ab s c fs' :=
  fun _ _ _ ⟨h, e⟩ => .inl ⟨e, c0, .refl _, h⟩

theorem ExitC.trans {fp ra : BitVec 64} {tp : UInt64} {c0 c0' : Ctl} {fs : List TermRun.Frame} {Ab : FragS isa}
    (hr : FrameRun p (c0, fs) (c0', fs)) :
    ∀ s c fs', ExitC p lbl exe endPc R F fp ra tp c0' fs Ab s c fs' →
      ExitC p lbl exe endPc R F fp ra tp c0 fs Ab s c fs' :=
  fun _ _ _ h => h.imp_left fun ⟨e, c1, hr', h⟩ => ⟨e, c1, hr.trans hr', h⟩

/-- **A lowered `Accepted1` body with calls is one segment at frames
`fs`**: from the node at the body (the lowering's environment `env` placed
in the frame, the ghost entry control `c0` in `G0`, closed under the
caller's frame runs, `hG0`, the thread pointer `tp`) to the body's exits (`ExitC`). The code
predicate `Cd` gives the code (`hCd`): the open block's at `pc` (`CodeC`),
the later blocks' at their labels (`BlocksCodeC`); the blocks' states are
inside `W₀` (inside `W` at `fs`, `hW₀`) at the body's nodes (`hW`) and
pending stores (`hWp`) at every sub-block of a block of `Cd` (`SubCd`) of a
construct's kind (`Kind1`) from
every ghost in `G0`; the body's overflow abort label is an abort exit
(`hab`); the calls are segments (`hcall`, the lowering's calls plain, `hfrm`); at each point of the lowering's walk
(`lowerEnvsC`) its environment's immediates are `i`'s (`hImm`), the point
satisfies `T`, and a `ret` there is of one word (`RetOne`; `CodeC`'s
terminator arm holds of any `ret` the emitter accepts). -/
theorem bodyC_segS {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int))
    (hhi : 16 ≤ R.hi) {fp ra : BitVec 64} {Cd : Int64 → List (Directive × Nat) → Prop}
    {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isa} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRun p (c, fs) (c', fs) → G0 c')
    (hW : ∀ c0, G0 c0 → ∀ pc t s blk, SubCd Cd pc blk → Kind1 fr blk →
      BlkW W₀ K exe endPc R F (bodyN p lbl fr fp ra c0 pc t s) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s k blk, SubCd Cd pc blk → Kind1 fr blk →
      BlkW W₀ K exe endPc R F (pendN p lbl fr fp ra c0 pc t s k) blk)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isa}
    (hab : ∀ c0, G0 c0 → ∀ s c,
      At exe endPc R F (abortN i T p lbl fr (_root_.Executable.labels exe).label fp ra c0) s c → Ab s c fs)
    {lcx : Scc.Lower.Ctx} (hfrm : lcx.frames = none) {tp : UInt64}
    (hcall : CallC p lbl lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab) :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (l : Scc.IR.Label) (k : Nat) (r : Res1) (kk : Nat) (pc : Int64),
      lowerC lcx env n l k e = some r → Fresh env n →
      CodeC fr Cd Bl kk pc r.insts r.term →
      BlocksCodeC fr Cd Bl (_root_.Executable.labels exe).label r.blocks →
      (∀ q ∈ lowerEnvsC lcx.frames env n e, ImmIn i (ofEnv q.2.1) q.1 ∧ T q.1) →
      (∀ q ∈ lowerEnvsC lcx.frames env n e, RetOne q) →
      ∀ c0, G0 c0 → SegWS W K p lbl ms ((At exe endPc R F ((bodyN p lbl fr fp ra c0 pc e (ofEnv env)).withTp tp)).at fs)
        (ExitC p lbl exe endPc R F fp ra tp c0 fs Ab) := by
  have hCd' := cdOf_subCd hCd
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n l k r kk pc hr hfr hcode hbl hImm hOne c0 hG
    cases op with
    | atom a =>
      obtain ⟨t, w, r', ha, -, hr', rfl⟩ := lowerC_atom_inv hr
      have ih' := ih _ n l k r' kk pc hr' (hfr.atom ha x) hcode hbl (immIn_tailC_atom ha hImm)
        (immIn_tailC_atom ha hOne) c0 hG
      refine ih'.mono_pre fun s c fs' ⟨⟨he, hn, hd, hpc, σ, hA, hFm, ⟨hJ, hfj, hc0⟩, htp⟩, hfs⟩ =>
        ⟨⟨he, hn, hd, hpc, σ, hA, hFm, ⟨?_, hfj, hc0⟩, htp⟩, hfs⟩
      rw [ofEnv_cons]
      exact hJ.atom (sevalAt_ofEnv ha)
    | add a b =>
      have hr0 := hr
      obtain ⟨ta, pa, tb, pb, r', ha, hb, hr', rfl⟩ := lowerC_add_inv hr
      obtain ⟨-, l1, zs, hE, hz, hc, hrest⟩ :=
        hcode.resolve_right fun ⟨_, _, _, _, _, _, _, _, hi, _⟩ => by cases hi
      obtain ⟨la, lb, off, hla, hlb, hd, hl⟩ := emits_add hE
      rw [hl] at hz hc
      obtain ⟨zs1, zs2, rfl, hz1, hz2, hc1, hc2⟩ := subCd_split hz (SubCd.whole hc)
      match zs2, hz2 with
      | [z], _ =>
      have hfv := lowerC_fv lcx (.let_ x (.add a b) e) env n l k _ hr0
      have hadd := ((add_edge (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0) (x := x) (e := e)
        hf h1 hla hlb hd hz1 (_root_.Executable.labels exe).label
        (sevalAt_ofEnv ha) (sevalAt_ofEnv hb) (hfr.ofEnv x)
        (fun y hy => isSome_lookupS_ofEnv (hfv y hy)) (immIn_headC hImm).1 (immIn_headC hImm).2).tp tp).seg
        (W := W₀) (K := K) (lbl := lbl) (ms := ms fs) hF hR hlo hhi (hCd' _ _ hc1)
        (BlkW.withTp (hW c0 hG _ _ _ _ hc1 (kind1_zip (.inl ⟨_, _, la, lb, hla, hlb, .inl rfl⟩) hz1)) tp)
      have hst := SegW.of_next1E (((store_edge (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0)
        (t := e) (s := (x, .int, [.one (.reg (regName x n))]) :: ofEnv env)
        hf h1 hd (_root_.Executable.labels exe).label).tp tp).seg (W := W₀) (K := K) (lbl := lbl) (ms := ms fs)
        hF hR hlo hhi (hCd' _ _ hc2)
        (BlkW.withTp (hWp c0 hG _ _ _ _ _ hc2 (kind1_zip (.inr (.inl ⟨_, off, hd, rfl⟩)) rfl)) tp))
      have hseg := SegW.seq_left (hadd.mono_post fun s c h => h.elim (fun ⟨_, h⟩ => .inl h)
        fun ⟨_, h⟩ => .inr h) hst
      have hpc : pc + Int64.ofNat (zs1 ++ [z]).sum = pc + Int64.ofNat zs1.sum + Int64.ofNat z := by
        rw [List.sum_append, Int64.ofNat_add, Int64.add_assoc]; simp
      rw [hpc] at hrest
      have ih' := ih _ (n + 1) l (k + 1) r' kk _ hr' (hfr.add x)
        hrest hbl (immIn_tailC_add hImm) (immIn_tailC_add hOne) c0 hG
      rw [ofEnv_cons] at ih'
      refine (SegWS.seq_left (SegWS.liftS_or fs hseg hW₀) ih').mono_post fun s c fs' h => ?_
      rcases h with h | h
      · exact h
      · obtain ⟨h, rfl⟩ := h
        exact .inr (hab c0 hG s c (At.of_withTp h))
    | sub a b =>
      obtain ⟨ta, pa, tb, pb, r', ha, hb, hr', rfl⟩ := lowerC_sub_inv hr
      obtain ⟨-, l1, zs, hE, hz, hc, hrest⟩ :=
        hcode.resolve_right fun ⟨_, _, _, _, _, _, _, _, hi, _⟩ => by cases hi
      obtain ⟨la, lb, off, hla, hlb, hd, hl⟩ := emits_sub hE
      rw [hl] at hz hc
      obtain ⟨zs1, zs2, rfl, hz1, hz2, hc1, hc2⟩ := subCd_split hz (SubCd.whole hc)
      match zs2, hz2 with
      | [z], _ =>
      have hsub := SegW.of_next1E (((sub_edge (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0) (x := x)
        (e := e) hf h1 hla hlb hd hz1 (_root_.Executable.labels exe).label
        (sevalAt_ofEnv ha) (sevalAt_ofEnv hb) (hfr.ofEnv x)).tp tp).seg
        (W := W₀) (K := K) (lbl := lbl) (ms := ms fs) hF hR hlo hhi (hCd' _ _ hc1)
        (BlkW.withTp (hW c0 hG _ _ _ _ hc1 (kind1_zip (.inl ⟨_, _, la, lb, hla, hlb, .inr (.inl rfl)⟩) hz1)) tp))
      have hst := SegW.of_next1E (((store_edge (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0)
        (t := e) (s := (x, .int, [.one (.reg (regName x n))]) :: ofEnv env)
        hf h1 hd (_root_.Executable.labels exe).label).tp tp).seg (W := W₀) (K := K) (lbl := lbl) (ms := ms fs)
        hF hR hlo hhi (hCd' _ _ hc2)
        (BlkW.withTp (hWp c0 hG _ _ _ _ _ hc2 (kind1_zip (.inr (.inl ⟨_, off, hd, rfl⟩)) rfl)) tp))
      have hpc : pc + Int64.ofNat (zs1 ++ [z]).sum = pc + Int64.ofNat zs1.sum + Int64.ofNat z := by
        rw [List.sum_append, Int64.ofNat_add, Int64.add_assoc]; simp
      rw [hpc] at hrest
      have ih' := ih _ (n + 1) l (k + 1) r' kk _ hr' (hfr.add x)
        hrest hbl (immIn_tailC_sub hImm) (immIn_tailC_sub hOne) c0 hG
      rw [ofEnv_cons] at ih'
      exact (SegWS.liftS fs (hsub.seq hst) hW₀).seq ih'
    | call g is a ts =>
      obtain ⟨dg, t, w, hx, hdg, hret, ha, hcase⟩ := lowerC_call_inv hr
      obtain ⟨-, r', hr', rfl⟩ := hcase.resolve_right fun ⟨_, _, h, _⟩ => by rw [hfrm] at h; cases h
      have h1' : (n + if lcx.frames.isSome then 7 else 1) = n + 1 := by simp [hfrm]
      have hImm' := immIn_tailC_call hImm
      have hOne' := immIn_tailC_call hOne
      rw [h1'] at hImm' hOne'
      obtain ⟨pc', hcode', hseg⟩ := hcall c0 pc kk env n x g is a ts e t w r'.insts r'.term hG
        (immIn_headC hImm).2 ⟨hx, dg, hdg, hret⟩ ha hfr hcode
        (fun y hy => isSome_lookupS_ofEnv (lowerC_fv lcx e _ _ _ _ _ hr' y hy)) (immIn_headC hImm').1
      have ih' : ∀ g : {c0' // FrameRun p (c0, fs) (c0', fs)},
          SegWS W K p lbl ms ((At exe endPc R F ((bodyN p lbl fr fp ra g.1 pc' e
            (ofEnv ((x, .int, [.reg (regName "r" n)]) :: env))).withTp tp)).at fs)
            (ExitC p lbl exe endPc R F fp ra tp c0 fs Ab) := fun g =>
        (ih _ (n + 1) l (k + 1) r' (kk + 1) pc' hr' (fresh_callC1 hfr x) hcode' hbl hImm' hOne' g.1
          (hG0 _ _ hG g.2)).mono_post
          (ExitC.trans g.2)
      refine (SegWS.seq_left hseg ((SegWS.exists_pre ih').mono_pre
        fun s c fs' ⟨he, c0', hrun, h⟩ => ⟨⟨c0', hrun⟩, h, he⟩)).mono_post fun s c fs' h => ?_
      rcases h with h | h
      · exact h
      · exact .inr h
    | _ => simp [lowerC] at hr
  | ifeq a b yes no ihy ihn =>
    intro env n l k r kk pc hr hfr hcode hbl hImm hOne c0 hG
    obtain ⟨ta, pa, tb, pb, ry, rn, ha, hb, hy, hn, rfl⟩ := lowerC_ifeq_inv hr
    rcases hcode with hu | ⟨l1, zs, hE, hz, hc⟩
    · cases hu
    obtain ⟨la, lb, hla, hlb, hl⟩ := emits_br hE
    rw [hl] at hz hc
    obtain ⟨zs1, zs2, rfl, hz1, hz2, hc1, hc2⟩ := subCd_split hz (SubCd.whole hc)
    match zs2, hz2 with
    | [z], _ =>
    have hmy : (⟨labName "then" n, ry.insts, ry.term⟩ : Scc.IR.Block) ∈
        ⟨labName "then" n, ry.insts, ry.term⟩ :: ry.blocks ++
          ⟨labName "else" (n + 1), rn.insts, rn.term⟩ :: rn.blocks := by simp
    have hmn : (⟨labName "else" (n + 1), rn.insts, rn.term⟩ : Scc.IR.Block) ∈
        ⟨labName "then" n, ry.insts, ry.term⟩ :: ry.blocks ++
          ⟨labName "else" (n + 1), rn.insts, rn.term⟩ :: rn.blocks := by simp
    obtain ⟨ky, hcy⟩ := hbl _ hmy (lowerC_term_ne lcx _ _ _ _ _ _ hy)
    obtain ⟨kn, hcn⟩ := hbl _ hmn (lowerC_term_ne lcx _ _ _ _ _ _ hn)
    have hnext := lowerC_next lcx yes env (n + 2) _ 0 ry hy
    have segy := ihy env (n + 2) _ 0 ry ky _ hy (hfr.mono (by omega))
      hcy (fun b hb => hbl b (by simp [hb])) (immIn_tailC_yes hImm) (immIn_tailC_yes hOne) c0 hG
    have segn := ihn env ry.next _ 0 rn kn _ hn (hfr.mono (by omega))
      hcn (fun b hb => hbl b (by simp [hb])) (by rw [hnext]; exact immIn_tailC_no hImm)
      (by rw [hnext]; exact immIn_tailC_no hOne) c0 hG
    have hbrs := SegW.of_nextBTp (((br_edge (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0)
      (yes := yes) (no := no) hf h1 hla hlb _ hz1 (_root_.Executable.labels exe).label
      (sevalAt_ofEnv ha) (sevalAt_ofEnv hb)).tp tp).seg (W := W₀) (K := K) (lbl := lbl) (ms := ms fs)
      hF hR hlo hhi (hCd' _ _ hc1)
      (BlkW.withTp (hW c0 hG _ _ _ _ hc1 (kind1_zip (.inl ⟨_, _, la, lb, hla, hlb, .inr (.inr ⟨_, rfl⟩)⟩) hz1)) tp))
    have hj := SegW.of_next1E (((jmp_edge (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0) (t := no)
      (s := ofEnv env) (fr := fr) _ (z := z) (_root_.Executable.labels exe).label).tp tp).seg
      (W := W₀) (K := K) (lbl := lbl) (ms := ms fs) hF hR hlo hhi (hCd' _ _ hc2)
      (BlkW.withTp (hW c0 hG _ _ _ _ hc2 (kind1_zip (.inr (.inr (.inl ⟨_, rfl⟩))) rfl)) tp))
    exact (SegWS.liftS_or fs hbrs hW₀).seq (SegWS.or_pre segy ((SegWS.liftS fs hj hW₀).seq segn))
  | ret a =>
    intro env n l k r kk pc hr hfr hcode _ _ hOne c0 hG
    obtain ⟨t, ws, ha, rfl⟩ := lowerC_ret_inv hr
    obtain ⟨t', w, ha'⟩ := immIn_headC hOne a rfl
    rw [ha] at ha'
    cases ha'
    rcases hcode with hu | ⟨l1, zs, hE, hz, hc⟩
    · cases hu
    obtain ⟨lw, hlw, hl⟩ := emits_ret hE
    rw [hl] at hz hc
    exact (SegWS.liftS fs (SegW.of_next1E (((ret_edge (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0)
      hf h1 hlw hz (_root_.Executable.labels exe).label (sevalAt_ofEnv ha)).tp tp).seg (W := W₀) (K := K)
      (lbl := lbl) (ms := ms fs) hF hR hlo hhi (hCd _ _ hc)
      (BlkW.withTp (hW c0 hG _ _ _ _ (SubCd.whole hc) (kind1_zip (.inr (.inr (.inr ⟨_, lw, hlw, rfl⟩))) hz)) tp)))
      hW₀).mono_post
      exitC_of_ret
  | _ => intro env n l k r kk pc hr; simp [lowerC] at hr

end BodyC

end Spike.Lib.LowerX64
