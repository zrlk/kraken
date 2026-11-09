/-
**An `Accepted2` block's code after its label gives `CodeC2`** (AArch64):
the `Accepted2` twin of `Spike/Lib/LowerA64/BlocksC1Code.lean`'s
`codeC_of_seg`, over `lowerC2`'s block shape (`InstC2`, `TermC2`,
`Spike/Lib/LowerShapeC2Shape.lean`).

- `inst2_allIns`, `term2_allIns`: the code of every non-call `InstC2`
  instruction but a checked `+` and of every `TermC2` terminator but a
  `ret` is instructions only (those two carry fresh labels `x{k}`, P5).
- `BlC2`: `BlC` with the `bl`'s pc in the phase of `ra` and an instruction
  after the return label `spK` (`InRun`): what a callee's return-address
  facts need (`Spike/Lib/LowerA64/AllocRa.lean`); `CodeC2.mono` weakens it.
- `headIns`, `insts2_head`: the code of an `Accepted2` block's instructions
  and terminator begins with an instruction.
- `callSeg`: a call's code `lw`, `bl g`, the return label `spK`, `ls` in a
  segment gives `lw`'s and `ls`'s pieces at `CdC`, the `bl` at `BlC2`, and the
  segment and phase facts after `spK` (`codeC_of_seg`'s call arm).
- `codeC2_of_seg`, `codeC2_block`: at `BlC2`; a checked `+`'s fall-through
  label and a `ret`'s return site label start new runs, as in `codeC_of_seg`.
-/
import Spike.Lib.LowerA64.BlocksC2Code
import Spike.Lib.LowerA64.Body2Arms
import Spike.Lib.LowerShapeC2Shape
import Spike.Lib.A64RunPc

namespace Spike.Lib.LowerA64

open Kraken Kraken.AArch64.Parser
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.A64.Flow (classify ofNat4_add ofNat4_succ ofNat4_zero)
open Scc.Cert.Rt.A64 (blockAt labelGap isIns)
open Scc.Cert.Code1A64 (instsItems segIn blockAt_of_segIn segIn_label labelGap_of_segIn)
open Scc.Cert.Ph1A64 (runsAux runPhB blkPh_of_runPhB runsAux_label)
open Spike.Lib.A64Consumer (blkPh)
open Spike.Lib.LowerShape (InstC2 TermC2 newBufCall xchgLoad xchgStore)

set_option linter.unusedSimpArgs false

/-! ## Instructions only -/

section Emit

variable {cx : FnCtx}

/-- **The code of every non-call `InstC2` instruction but a checked `+` is
instructions only** (a checked `+`'s has its fall-through's label, P5). -/
theorem inst2_allIns {k : Nat} {i : Scc.IR.Inst} (hi : InstC2 i) (hc : Spike.Lib.LowerShape.isCall i = false)
    (ha : ∀ d a b, i ≠ .addChk d a b) {ci : List Item} (h : cx.inst k i = .ok ci) : AllIns ci := by
  cases hi with
  | addChk d p q => exact absurd rfl (ha d p q)
  | subSat d p q =>
    simp only [FnCtx.inst] at h
    obtain ⟨la, ha, h⟩ := bind_eq_ok h
    obtain ⟨lb, hb, h⟩ := bind_eq_ok h
    obtain ⟨ls, hs, h⟩ := bind_eq_ok h
    cases ok_inj h
    refine allIns_append (allIns_append (allIns_append (allIns_getOp ha) (allIns_getOp hb)) ?_)
      (allIns_setReg hs)
    simp [AllIns, subSat, directives, ins, isIns]
  | load d a => exact inst_allIns (.load d a) hc (fun _ _ _ h => by cases h) h
  | store a w =>
    simp only [xchgStore, FnCtx.inst] at h
    obtain ⟨lv, hv, h⟩ := bind_eq_ok h
    obtain ⟨rel, hrel, h⟩ := bind_eq_ok h
    cases ok_inj hrel
    obtain ⟨lb, hb, h⟩ := bind_eq_ok h
    cases ok_inj h
    exact allIns_append (allIns_append (allIns_getOp hv) (allIns_getReg hb)) (allIns_strOff _ _ _ _)
  | ext d o =>
    simp only [FnCtx.inst] at h
    obtain ⟨la, ha, h⟩ := bind_eq_ok h
    obtain ⟨ls, hs, h⟩ := bind_eq_ok h
    cases ok_inj h
    refine allIns_append (allIns_append (allIns_getOp ha) ?_) (allIns_setReg hs)
    simp [AllIns, extOp, directives, ins, isIns]
  | add d b s =>
    simp only [FnCtx.inst] at h
    obtain ⟨la, ha, h⟩ := bind_eq_ok h
    obtain ⟨lb, hb, h⟩ := bind_eq_ok h
    obtain ⟨ls, hs, h⟩ := bind_eq_ok h
    cases ok_inj h
    refine allIns_append (allIns_append (allIns_append (allIns_getOp ha) (allIns_getOp hb)) ?_)
      (allIns_setReg hs)
    simp [AllIns, binOp, addReg, directives, ins, isIns]
  | mul8 d m =>
    simp only [FnCtx.inst] at h
    obtain ⟨la, ha, h⟩ := bind_eq_ok h
    obtain ⟨lb, hb, h⟩ := bind_eq_ok h
    obtain ⟨ls, hs, h⟩ := bind_eq_ok h
    cases ok_inj h
    refine allIns_append (allIns_append (allIns_append (allIns_getOp ha) (allIns_getOp hb)) ?_)
      (allIns_setReg hs)
    simp [AllIns, binOp, directives, ins, isIns]
  | minU d c s =>
    simp only [FnCtx.inst] at h
    obtain ⟨la, ha, h⟩ := bind_eq_ok h
    obtain ⟨lb, hb, h⟩ := bind_eq_ok h
    obtain ⟨lt, ht, h⟩ := bind_eq_ok h
    obtain ⟨lf, hf, h⟩ := bind_eq_ok h
    obtain ⟨ls, hs, h⟩ := bind_eq_ok h
    cases ok_inj h
    refine allIns_append (allIns_append (allIns_append (allIns_append (allIns_append
      (allIns_append (allIns_getOp ha) (allIns_getOp hb)) ?_) (allIns_getOp ht)) (allIns_getOp hf)) ?_)
      (allIns_setReg hs)
    · simp [AllIns, cmpReg, directives, ins, isIns]
    · simp [AllIns, directives, ins, isIns]
  | call d g w => simp [Spike.Lib.LowerShape.isCall] at hc
  | newBuf p h kv u => simp [Spike.Lib.LowerShape.isCall, newBufCall] at hc
  | print a0 a1 => simp [Spike.Lib.LowerShape.isCall] at hc

/-- The loads of a `ret`'s words are instructions only. -/
theorem allIns_retLoads : ∀ {ps : List (Scc.IR.Operand × XReg)} {c : List Item}, retLoads cx ps = .ok c → AllIns c
  | [], c, h => by cases ok_inj h; exact allIns_nil
  | (v, r) :: ps, c, h => by
    simp only [retLoads] at h
    obtain ⟨l, hl, h⟩ := bind_eq_ok h
    obtain ⟨ls, hls, h⟩ := bind_eq_ok h
    cases ok_inj h
    exact allIns_append (allIns_getOp hl) (allIns_retLoads hls)

/-- The frame's exit and `ret` are instructions only. -/
theorem allIns_leave_ret : AllIns (cx.leave ++ [ret]) := by
  refine allIns_append ?_ (allIns_ins _)
  unfold AllIns FnCtx.leave
  rw [directives_append, directives_append, List.all_append, List.all_append]
  have := allIns_ldrOff .W64 .X29 spW64 ((cx.frame : Int) - 16)
  have := allIns_ldrOff .W64 .X30 spW64 ((cx.frame : Int) - 8)
  unfold AllIns at *
  simp only [*, Bool.true_and]
  unfold addImm
  split
  · simp [directives, ins, isIns]
  · simp [directives, ins, isIns]
  · exact allIns_append (allIns_movImm _ _) (allIns_ins _)

/-- **The code of a `TermC2` terminator but a `ret` is instructions only**
(a `ret`'s has its return site's label, P5). -/
theorem term2_allIns {k : Nat} {t : Scc.IR.Term} (ht : TermC2 t) (hr : ∀ ws, t ≠ .ret ws) {c2 : List Item}
    (h : cx.term k t = .ok c2) : AllIns c2 := by
  cases ht with
  | ret ws => exact absurd rfl (hr ws)
  | br p q l l' =>
    simp only [FnCtx.term] at h
    obtain ⟨la, ha, h⟩ := bind_eq_ok h
    obtain ⟨lb, hb, h⟩ := bind_eq_ok h
    obtain ⟨T, -, h⟩ := bind_eq_ok h
    obtain ⟨F, -, h⟩ := bind_eq_ok h
    cases ok_inj h
    refine allIns_append (allIns_append (allIns_getOp ha) (allIns_getOp hb)) ?_
    simp [AllIns, cmpReg, jcc, jmp, directives, ins, isIns]

end Emit

/-! ## The call instance and the code's first instruction -/

/-- **A call's `bl g` at `pc` for a callee's return-address facts**: `BlC`,
the `bl`'s pc in the phase of `ra` (so the callee's label, `blkPh`'s target,
is too), and an instruction after the return label `spK` (`InRun`, so the
return address is a position in a run, told apart from the runtime's by
`pc_ne_of_inRun`). -/
def BlC2 (prog : List Directive) (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (cx : FnCtx)
    (ra : Int64) (pc : Int64) (g : Label) (k : Nat) : Prop :=
  BlC prog okPc ph lab cx ra pc g k ∧ ph pc.toBitVec.toNat = ph ra.toBitVec.toNat ∧
    Scc.Cert.Rt.A64.InRun prog (cx.local s!"sp{k}") 0

theorem BlC2.toBlC {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
    {cx : FnCtx} {ra pc : Int64} {g : Label} {k : Nat} (h : BlC2 prog okPc ph lab cx ra pc g k) :
    BlC prog okPc ph lab cx ra pc g k := h.1

/-- **`CodeC2` is monotone in its call predicate.** -/
theorem CodeC2.mono {cx : FnCtx} {Cd : Int64 → List Directive → Prop} {Bl Bl' : Int64 → Label → Nat → Prop}
    (hB : ∀ pc g k, Bl pc g k → Bl' pc g k) :
    ∀ {k : Nat} {pc : Int64} {is : List Scc.IR.Inst} {tm : Scc.IR.Term},
      CodeC2 cx Cd Bl k pc is tm → CodeC2 cx Cd Bl' k pc is tm
  | _, _, [], _, h => h
  | _, _, _ :: _, _, .inl ⟨hc, hn, l, hl, hcd, h⟩ => .inl ⟨hc, hn, l, hl, hcd, CodeC2.mono hB h⟩
  | _, _, _ :: _, _, .inr (.inl ⟨d, g, w, lw, ls, hi, hw, hs, h1, h2, h3, h⟩) =>
    .inr (.inl ⟨d, g, w, lw, ls, hi, hw, hs, h1, hB _ _ _ h2, h3, CodeC2.mono hB h⟩)
  | _, _, _ :: _, _, .inr (.inr (.inl ⟨p, h, kv, u, la, ls, hi, ha, hs, h1, h2, h3, h'⟩)) =>
    .inr (.inr (.inl ⟨p, h, kv, u, la, ls, hi, ha, hs, h1, hB _ _ _ h2, h3, CodeC2.mono hB h'⟩))
  | _, _, _ :: _, _, .inr (.inr (.inr (.inl ⟨a0, a1, la, hi, ha, h1, h2, h⟩))) =>
    .inr (.inr (.inr (.inl ⟨a0, a1, la, hi, ha, h1, hB _ _ _ h2, CodeC2.mono hB h⟩)))
  | _, _, _ :: _, _, .inr (.inr (.inr (.inr ⟨d, a, b, la, lb, ls, hi, ha, hb, hs, h1, h2, h⟩))) =>
    .inr (.inr (.inr (.inr ⟨d, a, b, la, lb, ls, hi, ha, hb, hs, h1, h2, CodeC2.mono hB h⟩)))

/-- A directive list beginning with an instruction. -/
def HeadIns (D : List Directive) : Prop := ∃ x r, D = .instr x :: r

theorem headIns_of_all {D : List Directive} (h : D.all isIns = true) (hne : D ≠ []) : HeadIns D := by
  cases D with
  | nil => exact absurd rfl hne
  | cons d r =>
    cases d with
    | instr x => exact ⟨x, r, rfl⟩
    | _ => simp [isIns] at h

theorem headIns_append {A P : List Directive} (h : HeadIns A) : HeadIns (A ++ P) := by
  obtain ⟨x, r, rfl⟩ := h
  exact ⟨x, r ++ P, rfl⟩

theorem headIns_append_all {A P : List Directive} (hA : A.all isIns = true) (hP : HeadIns P) :
    HeadIns (A ++ P) := by
  cases A with
  | nil => simpa using hP
  | cons a A => exact headIns_append (P := P) (headIns_of_all hA (List.cons_ne_nil _ _))

/-- **A load from the stack begins with an instruction** (the frame's exit's
first, `term2_head`). -/
theorem headIns_ldrOff {w : RegWidth} {rt : XReg} {base : RegOrSp .W64} {off : Int} {P : List Directive} :
    HeadIns (directives (ldrOff w rt base off) ++ P) := by
  unfold ldrOff
  split
  · exact ⟨_, _, rfl⟩
  split
  · exact ⟨_, _, rfl⟩
  rw [directives_append, List.append_assoc]
  exact headIns_append_all (allIns_movImm _ _) ⟨_, _, rfl⟩

section Emit

variable {cx : FnCtx}

/-- **A `TermC2` terminator's code begins with an instruction.** -/
theorem term2_head {k : Nat} {t : Scc.IR.Term} (ht : TermC2 t) {c2 : List Item} (h : cx.term k t = .ok c2) :
    HeadIns (directives c2) := by
  cases ht with
  | ret ws =>
    -- its loads, then the frame's exit (P5: the return site's label after it)
    obtain ⟨-, ls, hls, rfl⟩ := term_retN_inv h
    rw [directives_append, directives_append]
    unfold FnCtx.leave
    rw [directives_append, directives_append, List.append_assoc, List.append_assoc, List.append_assoc]
    exact headIns_append_all (allIns_retLoads hls) headIns_ldrOff
  | br p q l l' =>
    refine headIns_of_all (term2_allIns (.br p q l l') (fun _ h => by cases h) h) ?_
    simp only [FnCtx.term] at h
    obtain ⟨la, -, h⟩ := bind_eq_ok h
    obtain ⟨lb, -, h⟩ := bind_eq_ok h
    obtain ⟨T, -, h⟩ := bind_eq_ok h
    obtain ⟨F, -, h⟩ := bind_eq_ok h
    cases ok_inj h
    simp [directives_append, cmpReg, ins, directives]

/-- **An `InstC2` instruction's code keeps a following instruction first**:
instructions only, or a call's (its arguments' loads, then the `bl`). -/
theorem inst2_head (hm : cx.maps = true) {k : Nat} {i : Scc.IR.Inst} (hi : InstC2 i) {ci : List Item}
    (h : cx.inst k i = .ok ci) {P : List Directive} (hP : HeadIns P) : HeadIns (directives ci ++ P) := by
  by_cases hac : ∃ d a b, i = .addChk d a b
  · -- a checked `+`: its add, then its fall-through's label (P5)
    obtain ⟨d, a, b, rfl⟩ := hac
    obtain ⟨la, lb, ls, ha, hb, -, hds⟩ := inst_addChk_items h
    rw [hds, List.append_assoc]
    refine headIns_append (headIns_of_all (allIns_addDirs ha hb) ?_)
    simp [addDirs, directives_append, directives_addChecked]
  by_cases hc : Spike.Lib.LowerShape.isCall i = false
  · exact headIns_append_all (inst2_allIns hi hc (fun d a b h => hac ⟨d, a, b, h⟩) h) hP
  · have hbl : ∀ (A : List Item) (g : Label) (rest : List Directive), AllIns A →
        directives ci = directives A ++ blD g :: rest → HeadIns (directives ci ++ P) := by
      intro A g rest hA hd
      rw [hd]
      exact headIns_append (headIns_append_all hA ⟨_, rest, rfl⟩)
    cases hi with
    | call d g w =>
      obtain ⟨lw, ls, -, -, hAw, -, hd⟩ := inst_call1_inv hm h
      exact hbl lw _ _ hAw hd
    | newBuf p h' kv u =>
      obtain ⟨ca, sr, hca, -, hd⟩ := inst_call_inv hm h
      rw [callArgs_eq (by simp)] at hca
      rw [getArgs_eq (by simp)] at hca
      exact hbl ca _ _ (allIns_getOps hca) hd
    | print a0 a1 =>
      obtain ⟨ca, sr, hca, -, hd⟩ := inst_call_inv hm h
      rw [callArgs_eq (by simp)] at hca
      rw [getArgs_eq (by simp)] at hca
      exact hbl ca _ _ (allIns_getOps hca) hd
    | _ => exact absurd rfl hc

/-- **An `Accepted2` block's code from an instruction on begins with an
instruction**: its instructions' code `c1`, then a code beginning with one. -/
theorem insts2_head (hm : cx.maps = true) {c2 : List Item} (h2 : HeadIns (directives c2)) :
    ∀ (is : List Scc.IR.Inst) (k : Nat) (c1 : List Item), (∀ i ∈ is, InstC2 i) →
      instsItems cx k is = .ok c1 → HeadIns (directives (c1 ++ c2))
  | [], k, c1, _, hi => by
    simp only [instsItems] at hi
    cases hi
    simpa using h2
  | i :: is, k, c1, hs, hi => by
    have hs' := List.forall_mem_cons.mp hs
    simp only [instsItems] at hi
    cases hci : cx.inst k i with
    | error e => simp [hci, bind, Except.bind] at hi
    | ok ci =>
      cases hc1 : instsItems cx (k + 1) is with
      | error e => simp [hci, hc1, bind, Except.bind] at hi
      | ok c1' =>
        simp [hci, hc1, bind, Except.bind, pure, Except.pure] at hi
        subst hi
        rw [List.append_assoc, directives_append]
        exact inst2_head hm hs'.1 hci (insts2_head hm h2 is (k + 1) c1' hs'.2 hc1)

end Emit

/-- **A segment beginning with an instruction makes its label's run
non-empty.** -/
theorem inRun0_of_segIn {prog : List Directive} {l : Label} {D zs : List Directive}
    (h : segIn prog l (D ++ zs) = true) (hD : HeadIns D) : Scc.Cert.Rt.A64.InRun prog l 0 := by
  obtain ⟨x, r, rfl⟩ := hD
  unfold segIn at h
  split at h
  · next i hi =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨by simp [hi], ?_⟩
    simp only [Scc.Cert.Rt.A64.run, hi]
    have h1 := h.1
    generalize prog.drop (i + 1) = P at h1 ⊢
    cases P with
    | nil => simp at h1
    | cons d P =>
      simp only [List.cons_append, List.length_cons, List.take_succ_cons, List.cons.injEq] at h1
      rw [h1.1, List.takeWhile_cons_of_pos (by rfl)]
      simp
  · cases h

/-! ## A call in a segment -/

section Code

variable {cx : FnCtx} {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
  {ra : Int64}

/-- **A call in a segment** (`codeC_of_seg`'s call arm): the code `lw`,
`bl g`, the return label `spK`, `ls`, then `D` after the instructions `xs`
in the code after `l`: `lw`'s piece at `CdC`, the `bl` at `BlC2` (`ls ++ D`
beginning with an instruction, `hD`), `ls`'s piece
at `CdC` after it, the return label's address, and the segment and phase
facts after `spK` for the rest `D`. -/
theorem callSeg (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    {l : Label} {xs zs D : List Directive} {lw ls : List Item} {g : Label} {k : Nat}
    (hseg : segIn prog l (xs ++ (directives lw ++ blD g :: .label (cx.local s!"sp{k}") :: directives ls) ++ D ++ zs)
      = true)
    (hx : xs.all isIns = true) (hAw : AllIns lw) (hAs : AllIns ls) (hD : HeadIns (directives ls ++ D))
    (hph : ∀ r ∈ runsAux l xs.reverse
      ((directives lw ++ blD g :: .label (cx.local s!"sp{k}") :: directives ls) ++ D ++ zs),
      runPhB okPc ph lab (lab r.1) ra r.2 = true)
    (hrl : ∀ r ∈ runsAux l xs.reverse
      ((directives lw ++ blD g :: .label (cx.local s!"sp{k}") :: directives ls) ++ D ++ zs),
      ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat) :
    CdC prog okPc ph lab ra (lab l + Int64.ofNat (4 * xs.length)) (directives lw) ∧
    BlC2 prog okPc ph lab cx ra (lab l + Int64.ofNat (4 * xs.length) + Int64.ofNat (4 * (directives lw).length)) g k ∧
    CdC prog okPc ph lab ra
      (lab l + Int64.ofNat (4 * xs.length) + Int64.ofNat (4 * (directives lw).length) + 4) (directives ls) ∧
    lab (cx.local s!"sp{k}") =
      lab l + Int64.ofNat (4 * xs.length) + Int64.ofNat (4 * (directives lw).length) + 4 ∧
    segIn prog (cx.local s!"sp{k}") (directives ls ++ D ++ zs) = true ∧
    (∀ r ∈ runsAux (cx.local s!"sp{k}") (directives ls).reverse (D ++ zs),
      runPhB okPc ph lab (lab r.1) ra r.2 = true) ∧
    (∀ r ∈ runsAux (cx.local s!"sp{k}") (directives ls).reverse (D ++ zs),
      ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat) := by
  have hAw' : (directives lw).all isIns = true := hAw
  have hAs' : (directives ls).all isIns = true := hAs
  generalize hK : cx.local s!"sp{k}" = spK at hseg hph hrl ⊢
  generalize hB : blD g = B at hseg hph hrl
  have hBi : isIns B = true := by subst hB; rfl
  have e : ∀ X : List Directive, (directives lw ++ B :: .label spK :: directives ls) ++ D ++ X =
      (directives lw ++ [B]) ++ .label spK :: (directives ls ++ D ++ X) := by
    intro X; simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
  have hseg' : segIn prog l ((xs ++ directives lw ++ [B]) ++ .label spK :: (directives ls ++ D ++ zs))
      = true := by
    simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using hseg
  have hph' : ∀ r ∈ runsAux l xs.reverse ((directives lw ++ [B]) ++ .label spK ::
      (directives ls ++ D ++ zs)), runPhB okPc ph lab (lab r.1) ra r.2 = true := by
    rw [← e]; simpa only [List.append_assoc] using hph
  have hrl' : ∀ r ∈ runsAux l xs.reverse ((directives lw ++ [B]) ++ .label spK ::
      (directives ls ++ D ++ zs)), ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat := by
    rw [← e]; simpa only [List.append_assoc] using hrl
  have hwb : (directives lw ++ [B]).all isIns = true := by
    rw [List.all_append, hAw']; simp [hBi]
  rw [runsAux_label _ _ _ _ _ (noLabel_of_isIns hwb), List.reverse_reverse] at hph' hrl'
  have hr0 := hph' _ (List.mem_cons_self ..)
  have hrs : ∀ r ∈ runsAux spK [] (directives ls ++ D ++ zs),
      runPhB okPc ph lab (lab r.1) ra r.2 = true :=
    fun r hr => hph' r (List.mem_cons_of_mem _ hr)
  have hrlS : ∀ r ∈ runsAux spK [] (directives ls ++ D ++ zs),
      ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat :=
    fun r hr => hrl' r (List.mem_cons_of_mem _ hr)
  have hspk : ph (lab spK).toBitVec.toNat = ph ra.toBitVec.toNat := by
    obtain ⟨P, hP⟩ := runsAux_run0 spK [] (directives ls ++ D ++ zs)
    exact hrlS _ hP
  have hxw : (xs ++ directives lw).all isIns = true := by rw [List.all_append, hx, hAw']; rfl
  have hxwb : (xs ++ directives lw ++ [B]).all isIns = true := by
    rw [List.append_assoc, List.all_append, hx, hwb]; rfl
  have hsp : lab spK =
      lab l + Int64.ofNat (4 * xs.length) + Int64.ofNat (4 * (directives lw).length) + 4 := by
    have := hgap _ _ _ (labelGap_of_segIn hseg' hxwb)
    rwa [List.length_append, List.length_append, List.length_singleton, ofNat4_succ, ofNat4_add] at this
  have hseg2 : segIn prog spK (directives ls ++ D ++ zs) = true := segIn_label hseg'
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, hsp, hseg2, ?_, ?_⟩
  · -- the arguments' loads
    refine ⟨hAw', .inl ⟨l, xs.length, trivial, rfl, ?_⟩, ?_⟩
    · exact blockAt_of_segIn (zs := [B] ++ .label spK :: (directives ls ++ D ++ zs))
        (by simpa only [List.append_assoc] using hseg') hx hAw'
    · exact runPhB_sub (zs := [B]) (by simpa only [List.append_assoc] using hr0)
  · -- the `bl` and its return label
    subst hB hK
    refine ⟨l, xs.length + (directives lw).length, (ofNat4_add _ _ _), ?_, ?_, ?_, ?_⟩
    · have := blockAt_of_segIn (xs := xs ++ directives lw) (ys := [blD g])
        (zs := .label (cx.local s!"sp{k}") :: (directives ls ++ D ++ zs)) hseg' hxw rfl
      rwa [List.length_append] at this
    · have := labelGap_of_segIn hseg' hxwb
      rwa [List.length_append, List.length_append, List.length_singleton] at this
    · have := blkPh_of_runPhB (xs := xs ++ directives lw) (ys := [blD g])
        (zs := []) (by simpa using hr0) (by simp [classify])
      rwa [List.length_append, ofNat4_add] at this
    · rw [← hsp]; exact hspk
  · -- the `bl`'s pc in the phase of `ra`
    have hr0' : runPhB okPc ph lab (lab l) ra (xs ++ directives lw ++ [B]) = true := by
      simpa only [List.append_assoc] using hr0
    have hl : ph (lab l).toBitVec.toNat = ph ra.toBitVec.toNat := hrl' _ (List.mem_cons_self ..)
    have hlen : xs.length + (directives lw).length < (xs ++ directives lw ++ [B]).length := by simp
    have := (Scc.Cert.Ph1A64.runPhB_get hr0' hlen).2.1
    rw [Int64.add_assoc, ← Int64.ofNat_add, ← Nat.mul_add, this, hl]
  · -- an instruction after the return label
    rw [hK]
    exact inRun0_of_segIn (D := directives ls ++ D) (zs := zs)
      (by simpa only [List.append_assoc] using hseg2) hD
  · -- the results' stores
    have := cdC_at (l := spK) (xs := []) (zs := D ++ zs)
      (by simpa only [List.append_assoc, List.nil_append] using hseg2) rfl hAs'
      (by simpa only [List.append_assoc, List.reverse_nil] using hrs)
    rwa [List.length_nil, ofNat4_zero, hsp] at this
  · rw [← List.append_nil (directives ls).reverse, ← runsAux_shift _ _ _ _ (noLabel_of_isIns hAs')]
    simpa only [List.append_assoc] using hrs
  · rw [← List.append_nil (directives ls).reverse, ← runsAux_shift _ _ _ _ (noLabel_of_isIns hAs')]
    simpa only [List.append_assoc] using hrlS

/-- No results: no stores. -/
theorem setResults_nil : cx.setResults [] = .ok [] := by
  simp [FnCtx.setResults, Scc.IR.maxRets, bind, Except.bind, pure, Except.pure, forIn, ForIn.forIn]

/-- **An `Accepted2` block's code after its label gives `CodeC2`**: the code
`c1` of its instructions numbered from `k` (`instsItems`, `InstC2`) and `c2`
of its terminator (`TermC2`), after the instructions `xs` and before `zs` in
the code after `l` (`segIn`), every run from there passing `runPhB` at `lab`
(`hph`) and in the phase of `ra` (`hrl`); the stack maps on (`hm`), and
`lab` following the labels' gaps (`hgap`). -/
theorem codeC2_of_seg (hm : cx.maps = true)
    (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    {tm : Scc.IR.Term} (htm : TermC2 tm) :
    ∀ (is : List Scc.IR.Inst) (k : Nat) (l : Label) (c1 c2 : List Item) (xs zs : List Directive),
      (∀ i ∈ is, InstC2 i) → instsItems cx k is = .ok c1 →
      cx.term (k + is.length) tm = .ok c2 →
      segIn prog l (xs ++ directives (c1 ++ c2) ++ zs) = true → xs.all isIns = true →
      (∀ r ∈ runsAux l xs.reverse (directives (c1 ++ c2) ++ zs), runPhB okPc ph lab (lab r.1) ra r.2 = true) →
      (∀ r ∈ runsAux l xs.reverse (directives (c1 ++ c2) ++ zs), ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat) →
      CodeC2 cx (CdC prog okPc ph lab ra) (BlC2 prog okPc ph lab cx ra) k (lab l + Int64.ofNat (4 * xs.length))
        is tm
  | [], k, l, c1, c2, xs, zs, _, hi, ht, hseg, hx, hph, hrl => by
    simp only [instsItems] at hi
    cases hi
    simp only [List.nil_append, List.length_nil, Nat.add_zero] at hseg hph hrl ht
    by_cases hr : ∀ ws, tm ≠ .ret ws
    · exact Or.inr (Or.inl ⟨c2, hr, ht, cdC_at hseg hx (term2_allIns htm hr ht) hph⟩)
    -- a `ret`: its return site's label between the frame exit and `ret` (P5)
    obtain ⟨ws, rfl⟩ : ∃ ws, tm = .ret ws := by
      cases htm with
      | ret ws => exact ⟨ws, rfl⟩
      | br => exact absurd (fun _ h => by cases h) hr
    obtain ⟨hn, lw, hg, rfl⟩ := term_retN_inv ht
    generalize hX : cx.local s!"x{k}" = X at hseg hph hrl
    generalize hT : directives (lw ++ cx.leave) = T
    have hTi : T.all isIns = true := by rw [← hT]; exact allIns_append (allIns_retLoads hg) (allIns_leave cx)
    have hRi : (directives [ret]).all isIns = true := allIns_ins _
    have hTR : directives (lw ++ cx.leave ++ [ret]) = T ++ directives [ret] := by rw [← hT, directives_append]
    have hD : directives (lw ++ cx.leave ++ [lbl X, ret]) = T ++ .label X :: directives [ret] := by
      rw [← hT, show lw ++ cx.leave ++ [lbl X, ret] = (lw ++ cx.leave) ++ [lbl X] ++ [ret] by simp,
        directives_append, directives_append, List.append_assoc]; rfl
    rw [hD] at hseg hph hrl
    -- the loads and frame exit
    have hseg1 : segIn prog l (xs ++ T ++ (.label X :: directives [ret] ++ zs)) = true := by
      simpa only [List.append_assoc, List.cons_append] using hseg
    have hph1 : ∀ r ∈ runsAux l xs.reverse (T ++ (.label X :: directives [ret] ++ zs)),
        runPhB okPc ph lab (lab r.1) ra r.2 = true := by
      simpa only [List.append_assoc, List.cons_append] using hph
    obtain ⟨hat1, hr1, hp1⟩ := cdCQ_at1 (Q := fun _ => True) trivial hseg1 hx hTi hph1
    have hxT : (xs ++ T).all isIns = true := by rw [List.all_append, hx, hTi]; rfl
    obtain ⟨hseg2, hsp⟩ := label_at hgap (P := xs ++ T) (R := directives [ret] ++ zs)
      (by simpa only [List.append_assoc, List.cons_append] using hseg) hxT
    rw [List.cons_append, runs_label l xs hTi X] at hph1
    have hrl1 := hrl
    rw [List.append_assoc, List.cons_append, runs_label l xs hTi X] at hrl1
    -- `ret`, after the return site's label
    obtain ⟨hat2, hr2, -⟩ := cdCQ_at1 (Q := fun _ => True) (l := X) (xs := []) trivial (by simpa using hseg2) rfl
      hRi (fun r hr => hph1 r (List.mem_cons_of_mem _ hr))
    rw [List.length_nil, ofNat4_zero] at hat2 hr2
    have hphX : ph (lab X).toBitVec.toNat = ph ra.toBitVec.toNat := by
      obtain ⟨P, hP⟩ := runsAux_run0 X [] (directives [ret] ++ zs)
      exact hrl1 _ (List.mem_cons_of_mem _ hP)
    have hphl : ph (lab l).toBitVec.toNat = ph ra.toBitVec.toNat := hrl1 _ (List.mem_cons_self ..)
    have hsp' : lab X = lab l + Int64.ofNat (4 * xs.length) + Int64.ofNat (4 * T.length) := by
      rw [hsp, pc_app]
    refine Or.inr (Or.inr ⟨ws, lw, rfl, hn, hg, ?_⟩)
    rw [hTR]
    refine ⟨by rw [List.all_append, hTi, hRi]; rfl, .inr ⟨T, _, rfl, hat1, by rw [← hsp']; exact hat2⟩, ?_⟩
    refine runPhB_append hr1 (by rw [← hsp']; exact hr2) ?_
    by_cases hTe : T = []
    · subst hTe; simp only [List.length_nil, ofNat4_zero]
    · rw [← hsp', hphX, hp1 hTe, hphl]
  | i :: is, k, l, c1, c2, xs, zs, hs, hi, ht, hseg, hx, hph, hrl => by
    have hs' := List.forall_mem_cons.mp hs
    simp only [instsItems] at hi
    rw [show k + (i :: is).length = k + 1 + is.length by simp; omega] at ht
    cases hci : cx.inst k i with
    | error e => simp [hci, bind, Except.bind] at hi
    | ok ci =>
      cases hc1 : instsItems cx (k + 1) is with
      | error e => simp [hci, hc1, bind, Except.bind] at hi
      | ok c1' =>
        simp [hci, hc1, bind, Except.bind, pure, Except.pure] at hi
        subst hi
        have hD : directives (ci ++ c1' ++ c2) = directives ci ++ directives (c1' ++ c2) := by
          rw [List.append_assoc, directives_append]
        rw [hD] at hseg hph hrl
        -- the rest after a call, from its return label
        have hcall : ∀ {lw ls : List Item} {g : Label}, AllIns lw → AllIns ls →
            directives ci = directives lw ++ blD g :: .label (cx.local s!"sp{k}") :: directives ls →
            CdC prog okPc ph lab ra (lab l + Int64.ofNat (4 * xs.length)) (directives lw) ∧
            BlC2 prog okPc ph lab cx ra
              (lab l + Int64.ofNat (4 * xs.length) + Int64.ofNat (4 * (directives lw).length)) g k ∧
            CdC prog okPc ph lab ra
              (lab l + Int64.ofNat (4 * xs.length) + Int64.ofNat (4 * (directives lw).length) + 4)
              (directives ls) ∧
            CodeC2 cx (CdC prog okPc ph lab ra) (BlC2 prog okPc ph lab cx ra) (k + 1)
              (lab l + Int64.ofNat (4 * xs.length) + Int64.ofNat (4 * (directives lw).length) + 4 +
                Int64.ofNat (4 * (directives ls).length)) is tm := by
          intro lw ls g hAw hAs hd
          rw [hd] at hseg hph hrl
          obtain ⟨h1, h2, h3, hsp, hseg2, hrs, hrl2⟩ := callSeg (D := directives (c1' ++ c2)) hgap
            (by simpa only [List.append_assoc, List.cons_append] using hseg) hx hAw hAs
            (headIns_append_all hAs (insts2_head hm (term2_head htm ht) is (k + 1) c1' hs'.2 hc1))
            (by simpa only [List.append_assoc, List.cons_append] using hph)
            (by simpa only [List.append_assoc, List.cons_append] using hrl)
          refine ⟨h1, h2, h3, ?_⟩
          have := codeC2_of_seg hm hgap htm is (k + 1) _ c1' c2 (directives ls) zs hs'.2 hc1 ht hseg2 hAs hrs hrl2
          rwa [hsp] at this
        by_cases hac : ∃ d a b, i = .addChk d a b
        · -- a checked `+`: its fall-through's label before the store (P5)
          obtain ⟨d, a, b, rfl⟩ := hac
          obtain ⟨la, lb, ls, ha, hb, hs, hds⟩ := inst_addChk_items hci
          rw [hds] at hseg hph hrl
          generalize hDd : directives (c1' ++ c2) = D at hseg hph hrl
          generalize hX : cx.local s!"x{k}" = X at hseg hph hrl
          have hAi := allIns_addDirs ha hb
          have hSi : (directives ls).all isIns = true := allIns_setReg hs
          -- the checked add
          have hseg1 : segIn prog l (xs ++ addDirs cx la lb ++ (.label X :: (directives ls ++ D ++ zs))) = true := by
            simpa only [List.append_assoc, List.cons_append] using hseg
          have hph1 : ∀ r ∈ runsAux l xs.reverse (addDirs cx la lb ++ .label X :: (directives ls ++ D ++ zs)),
              runPhB okPc ph lab (lab r.1) ra r.2 = true := by
            simpa only [List.append_assoc, List.cons_append] using hph
          have hrl1 : ∀ r ∈ runsAux l xs.reverse (addDirs cx la lb ++ .label X :: (directives ls ++ D ++ zs)),
              ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat := by
            simpa only [List.append_assoc, List.cons_append] using hrl
          have cA := cdC_at hseg1 hx hAi hph1
          have hxA : (xs ++ addDirs cx la lb).all isIns = true := by rw [List.all_append, hx, hAi]; rfl
          obtain ⟨hseg2, hsp⟩ := label_at hgap (P := xs ++ addDirs cx la lb) (R := directives ls ++ D ++ zs)
            (by simpa only [List.append_assoc] using hseg1) hxA
          rw [runs_label l xs hAi X] at hph1 hrl1
          have hsp' : lab X = lab l + Int64.ofNat (4 * xs.length) + Int64.ofNat (4 * (addDirs cx la lb).length) := by
            rw [hsp, pc_app]
          have hphX : ∀ r ∈ runsAux X [] (directives ls ++ D ++ zs), runPhB okPc ph lab (lab r.1) ra r.2 = true :=
            fun r hr => hph1 r (List.mem_cons_of_mem _ hr)
          have hrlX : ∀ r ∈ runsAux X [] (directives ls ++ D ++ zs),
              ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat :=
            fun r hr => hrl1 r (List.mem_cons_of_mem _ hr)
          -- the store, after the fall-through's label
          have cS := cdC_at (l := X) (xs := []) (zs := D ++ zs)
            (by simpa only [List.append_assoc, List.nil_append] using hseg2) rfl hSi
            (by simpa only [List.append_assoc, List.reverse_nil] using hphX)
          rw [List.length_nil, ofNat4_zero, hsp'] at cS
          -- the rest of the block
          have c3 := codeC2_of_seg hm hgap htm is (k + 1) X c1' c2 (directives ls) zs hs'.2 hc1 ht
            (by rw [hDd]; simpa only [List.append_assoc] using hseg2) hSi
            (by
              rw [hDd, ← List.append_nil (directives ls).reverse, ← runsAux_shift _ _ _ _ (noLabel_of_isIns hSi)]
              simpa only [List.append_assoc] using hphX)
            (by
              rw [hDd, ← List.append_nil (directives ls).reverse, ← runsAux_shift _ _ _ _ (noLabel_of_isIns hSi)]
              simpa only [List.append_assoc] using hrlX)
          rw [hsp'] at c3
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨d, a, b, la, lb, ls, rfl, ha, hb, hs, cA, cS, c3⟩)))
        by_cases hc : Spike.Lib.LowerShape.isCall i = false
        · -- an instruction other than a call or a checked `+`: instructions only
          have hna : ∀ d a b, i ≠ .addChk d a b := fun d a b h => hac ⟨d, a, b, h⟩
          have hA : (directives ci).all isIns = true := inst2_allIns hs'.1 hc hna hci
          refine Or.inl ⟨hc, hna, ci, hci, ?_, ?_⟩
          · exact cdC_at (zs := directives (c1' ++ c2) ++ zs) (by simpa only [List.append_assoc] using hseg) hx hA
              (by simpa only [List.append_assoc] using hph)
          · have hxA : (xs ++ directives ci).all isIns = true := by rw [List.all_append, hx, hA]; rfl
            have := codeC2_of_seg hm hgap htm is (k + 1) l c1' c2 (xs ++ directives ci) zs hs'.2 hc1 ht
              (by simpa only [List.append_assoc] using hseg) hxA
              (by
                rw [List.reverse_append, ← runsAux_shift _ _ _ _ (noLabel_of_isIns hA)]
                simpa only [List.append_assoc] using hph)
              (by
                rw [List.reverse_append, ← runsAux_shift _ _ _ _ (noLabel_of_isIns hA)]
                simpa only [List.append_assoc] using hrl)
            rwa [List.length_append, ofNat4_add] at this
        · cases hs'.1 with
          | call d g w =>
            obtain ⟨lw, ls, hw, hsr, hAw, hAs, hd⟩ := inst_call1_inv hm hci
            obtain ⟨h1, h2, h3, h4⟩ := hcall hAw hAs hd
            exact .inr (.inl ⟨d, g, w, lw, ls, rfl, hw, hsr, h1, h2, h3, h4⟩)
          | newBuf p h kv u =>
            obtain ⟨ca, sr, hca, hsr, hd⟩ := inst_call_inv hm hci
            rw [callArgs_eq (by simp)] at hca
            rw [setResults_one] at hsr
            have hAa : AllIns ca := by rw [getArgs_eq (by simp)] at hca; exact allIns_getOps hca
            obtain ⟨h1, h2, h3, h4⟩ := hcall hAa (allIns_setReg hsr) hd
            exact .inr (.inr (.inl ⟨p, h, kv, u, ca, sr, rfl, hca, hsr, h1, h2, h3, h4⟩))
          | print a0 a1 =>
            obtain ⟨ca, sr, hca, hsr, hd⟩ := inst_call_inv hm hci
            rw [callArgs_eq (by simp)] at hca
            rw [setResults_nil] at hsr
            cases hsr
            have hAa : AllIns ca := by rw [getArgs_eq (by simp)] at hca; exact allIns_getOps hca
            obtain ⟨h1, h2, -, h4⟩ := hcall hAa allIns_nil hd
            refine .inr (.inr (.inr (.inl ⟨a0, a1, ca, rfl, hca, h1, h2, ?_⟩)))
            simpa [directives] using h4
          | _ => exact absurd rfl hc

end Code

section Place

variable {cx : FnCtx} {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
  {ra : Int64} {lo : Nat}

/-- **A placed block of `lowerC2`'s shape gives `CodeC2`** at its label
(`codeC_block`'s twin): its code after the label (`segIn`) and its runs'
phase facts at the code labels (`labC`), every label read resolving, which
`lab` agrees with (`hlab`). -/
theorem codeC2_block (hm : cx.maps = true)
    (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    (hlab : ∀ l a, Scc.Cert.Link.A64.codeOf lo prog l = some a → lab l = Int64.ofNat a)
    {b : Scc.IR.Block} (hs : Spike.Lib.LowerShape.BlockC2 b) {k : Nat} {l : Label} {code : List Item}
    (hc : Scc.Cert.Code1A64.blockItems cx k b = .ok code) (hseg : segIn prog l (directives code) = true)
    (hph : ∀ r ∈ Scc.Cert.Ph1A64.runs l (directives code),
      Scc.Cert.Ph1A64.runPh okPc ph (labC lo prog)
          (fun l => (Scc.Cert.Link.A64.codeOf lo prog l).isSome) ra r = true ∧
        ph (labC lo prog r.1).toBitVec.toNat = ph ra.toBitVec.toNat) :
    CodeC2 cx (CdC prog okPc ph lab ra) (BlC2 prog okPc ph lab cx ra) k (lab l) b.insts b.term := by
  cases hi : instsItems cx k b.insts with
  | error e => simp [Scc.Cert.Code1A64.blockItems, hi, bind, Except.bind] at hc
  | ok c1 =>
    cases ht : cx.term (k + b.insts.length) b.term with
    | error e => simp [Scc.Cert.Code1A64.blockItems, hi, ht, bind, Except.bind] at hc
    | ok c2 =>
      simp [Scc.Cert.Code1A64.blockItems, hi, ht, bind, Except.bind, pure, Except.pure] at hc
      subst hc
      have := codeC2_of_seg (okPc := okPc) (ph := ph) (ra := ra) hm hgap hs.2 b.insts k l c1 c2 [] []
        hs.1 hi ht (by simpa using hseg) rfl
        (fun r hr => by
          have h' := (hph r (by simpa [Scc.Cert.Ph1A64.runs] using hr)).1
          simp only [Scc.Cert.Ph1A64.runPh, Bool.and_eq_true] at h'
          obtain ⟨⟨hres, hlabs⟩, hrun⟩ := h'
          rw [labC_eq hlab hres, runPhB_congr fun L hL => labC_eq hlab (List.all_eq_true.mp hlabs L hL)] at hrun
          exact hrun)
        (fun r hr => by
          have h' := hph r (by simpa [Scc.Cert.Ph1A64.runs] using hr)
          simp only [Scc.Cert.Ph1A64.runPh, Bool.and_eq_true] at h'
          obtain ⟨⟨⟨hres, -⟩, -⟩, hp⟩ := h'
          rw [labC_eq hlab hres] at hp
          exact hp)
      simpa [ofNat4_zero] using this

end Place

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.codeC2_of_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms codeC2_of_seg

end Spike.Lib.LowerA64
