/-
**The code of an `Accepted1` block with calls** (AArch64): the code
predicate of a block of the closed form `lowerC` emits with the depth
counter (`InstC`, `TermC`, `Spike/Lib/LowerShapeC1.lean`), one arm per
instruction, a one-word user call split at its `bl`; next to
`Spike/Lib/LowerA64/Body1.lean`'s call-free `Code1`.

- `CodeC`: the code of the instructions `is` numbered from `k` at `pc`, then
  the terminator's: each non-call instruction's code (`Cd`), or a call's
  argument load (`Cd`), its `bl` and return label (`Bl`) and its result's
  store (`Cd`); the instruction number `k` goes up by one per instruction
  (`instsItems`), and the return label of the call numbered `k` is `spK`;
- `BlC`: the `Bl` instance: the `bl` is code `j` instructions after a label
  `L` (`blockAt`), the label `spK` follows `L` after `j + 1` instructions
  (`labelGap`), the `bl` passes its phase check (`blkPh`), as
  `call_blockAt` gives, and the return label is in the phase of `ra`
  (`blC_ph`; `cdOf_blC` puts the `bl` in the code of a laid-out program);
- `BlocksCodeC`: every block not ending in `unreachable` (the bracket's dead
  abort block `deepBlock`) is at its label, at some instruction number;
- `CdC`: the `Cd` instance: an instruction-only piece of code after a label
  (`blockAt`) passing its run's phase check (`runPhB`); `cdOf_cdC` puts it in
  the code of a laid-out program;
- `codeC_of_seg`: a block's code after its label (`segIn`), every run from
  there passing `runPhB`, gives `CodeC` at `CdC` and `BlC` (each call's return
  label `spK` starting a new run, at the address `labelGap` gives, `hgap`;
  `hgap_of_lays` on a laid-out program);
- `codeC_block`, `blocksCodeC`, `entryCodeC`: from a block's `blocksOk` and
  `blocksPh` (as `Blocks1.lean`'s `code1_block`), a block of `lowerC`'s
  shape (`BlockC`) without the stack abort's call (`abortI`; none without
  the depth counter, `lowerC_noStackAbort`; with it only in the `unreachable`
  block `deepBlock`, `ne_abortI_of_callBlk`);
- `fnCodeC`: a code block's function `func1 …`: its entry block at `CodeC`
  from 0 and its later blocks at `BlocksCodeC`; `fnCodeC_ofPlaceOK`: for
  every code block of an `Accepted1` program passing `PlaceOK`, as
  `fnPh1_ofPlaceOK` numbers them, with its `lowerC` (`LowC`) and `maps`;
  `fnCodeC_of_fnPh1` at `fnPh1_ofPlaceOK`'s own witnesses.
-/
import Spike.Lib.LowerA64.BlocksC1

namespace Spike.Lib.LowerA64

open Kraken Kraken.AArch64.Parser
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.A64.Flow (classify ofNat4_add ofNat4_succ ofNat4_zero)
open Scc.Cert.Rt.A64 (blockAt labelGap isIns)
open Scc.Cert.Code1A64 (instsItems segIn blockAt_of_segIn segIn_label labelGap_of_segIn blocksOk blockItems
  blocksOk_block ctxOf)
open Scc.Cert.Ph1A64 (runs runsAux runPhB runPhB_get blkPh_of_runPhB runsAux_label runPh blocksPh blocksPh_block
  blocksPh_blockPh)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Lower.Inv (Res1 func1 params1R)
open CoreTerm (Decl)
open Spike.Lib.A64Consumer (blkPh)
open Spike.Lib.LowerShape (InstC TermC)

set_option linter.unusedSimpArgs false

/-! ## The code predicate -/

/-- **The code of a block's instructions `is` numbered from `k` at `pc`,
then of its terminator `tm`**. A non-call instruction: its code `l` is at
`pc` (`Cd`). A one-word user call `call [d] g [w]`: `w`'s load `lw` into
`x0` at `pc` (`Cd`), the `bl g` after it with the return label `spK`
(`Bl`), then `x0`'s store `ls` into `d` (`Cd`). The terminator: an
`unreachable` (no claim), or its code at `pc` (`Cd`).
`Cd pc blk`: `blk` is the code at `pc`; `Bl pc g k`: `bl g` is the code at
`pc`, followed by the label `spK`. -/
def CodeC (cx : FnCtx) (Cd : Int64 → List Directive → Prop) (Bl : Int64 → Label → Nat → Prop) :
    Nat → Int64 → List Scc.IR.Inst → Scc.IR.Term → Prop
  | k, pc, [], tm => tm = .unreachable ∨ ∃ l, cx.term k tm = .ok l ∧ Cd pc (directives l)
  | k, pc, i :: is, tm =>
    (Spike.Lib.LowerShape.isCall i = false ∧ ∃ l, cx.inst k i = .ok l ∧ Cd pc (directives l) ∧
      CodeC cx Cd Bl (k + 1) (pc + Int64.ofNat (4 * (directives l).length)) is tm) ∨
    (∃ d g w lw ls, i = .call [d] (Scc.Lower.Names.user g) [w] ∧ cx.getOp .X0 w = .ok lw ∧
      cx.setReg d .X0 = .ok ls ∧ Cd pc (directives lw) ∧
      Bl (pc + Int64.ofNat (4 * (directives lw).length)) (Scc.Lower.Names.user g) k ∧
      Cd (pc + Int64.ofNat (4 * (directives lw).length) + 4) (directives ls) ∧
      CodeC cx Cd Bl (k + 1)
        (pc + Int64.ofNat (4 * (directives lw).length) + 4 + Int64.ofNat (4 * (directives ls).length)) is tm)

/-- **A call's `bl g` at `pc` with the return label `spK` after it**: `j`
instructions after a label `L` (`blockAt`), with `spK` after `L` at
`j + 1` instructions (`labelGap`), passing the phase check at `pc` with no
dead target and the return address `ra`, the return label in the phase of
`ra` (the callee's return address of `ra`'s phase). -/
def BlC (prog : List Directive) (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (cx : FnCtx)
    (ra : Int64) (pc : Int64) (g : Label) (k : Nat) : Prop :=
  ∃ L j, lab L + Int64.ofNat (4 * j) = pc ∧ blockAt prog L j [.instr ⟨.W64, .BL (.label g)⟩] = true ∧
    labelGap prog L (cx.local s!"sp{k}") (j + 1) = true ∧
    blkPh okPc ph (fun _ => false) lab pc ra [.instr ⟨.W64, .BL (.label g)⟩] = true ∧
    ph (pc + 4).toBitVec.toNat = ph ra.toBitVec.toNat

/-- **The code of a function's blocks**: each block not ending in
`unreachable` at its assembler label (`lab`), as `CodeC` from some
instruction number. -/
def BlocksCodeC (cx : FnCtx) (Cd : Int64 → List Directive → Prop) (Bl : Int64 → Label → Nat → Prop)
    (lab : Label → Int64) (bs : List Scc.IR.Block) : Prop :=
  ∀ b ∈ bs, b.term ≠ .unreachable →
    ∃ L k, cx.blockLabel b.label = .ok L ∧ CodeC cx Cd Bl k (lab L) b.insts b.term

/-! ## The code predicate instance -/

/-- **A piece of a block's code at `pc`**: instructions only, `j`
instructions after a label `L` (`blockAt`), passing the run's phase check
from `pc` (`runPhB`: an instruction `classify` does not cover, a load or
store off `x10`, falls through) with the return address `ra`. -/
def CdC (prog : List Directive) (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (ra : Int64)
    (pc : Int64) (blk : List Directive) : Prop :=
  blk.all isIns = true ∧ ∃ L j, lab L + Int64.ofNat (4 * j) = pc ∧ blockAt prog L j blk = true ∧
    runPhB okPc ph lab pc ra blk = true

/-- The stack abort's call (the deep block's). -/
abbrev abortI : Scc.IR.Inst :=
  .call [] Scc.Lower.Names.abort [Scc.Lower.imm Scc.IR.AbortKind.stack.code]

/-- The `bl g` directive of a call. -/
abbrev blD (g : String) : Directive := .instr ⟨.W64, .BL (.label g)⟩

/-! ## Runs -/

theorem noLabel_of_isIns {c : List Directive} (h : c.all isIns = true) : ∀ d ∈ c, ∀ l', d ≠ .label l' := by
  intro d hd l' he
  subst he
  have := List.all_eq_true.mp h _ hd
  simp [isIns] at this

/-- **A label-free prefix joins the current run.** -/
theorem runsAux_shift : ∀ (l : Label) (acc c S : List Directive), (∀ d ∈ c, ∀ l', d ≠ .label l') →
    runsAux l acc (c ++ S) = runsAux l (c.reverse ++ acc) S
  | l, acc, [], S, _ => by simp
  | l, acc, d :: c, S, h => by
    have hd : ∀ l', d ≠ .label l' := h d (List.mem_cons_self ..)
    have ih := runsAux_shift l (d :: acc) c S fun d' hd' => h d' (List.mem_cons_of_mem _ hd')
    cases d with
    | label l'' => exact absurd rfl (hd l'')
    | instr i => simp only [List.cons_append, runsAux]; rw [ih]; simp
    | byteArray a => simp only [List.cons_append, runsAux]; rw [ih]; simp

/-- **The current run** of `runsAux l acc S`: `acc` (reversed) and the
directives of `S` up to its first label. -/
theorem runsAux_run0 : ∀ (l : Label) (acc S : List Directive), ∃ P, (l, acc.reverse ++ P) ∈ runsAux l acc S
  | l, acc, [] => ⟨[], by simp [runsAux]⟩
  | l, acc, .label _ :: _ => ⟨[], by simp [runsAux]⟩
  | l, acc, .instr i :: S => by
    obtain ⟨P, hP⟩ := runsAux_run0 l (.instr i :: acc) S
    exact ⟨.instr i :: P, by simpa [runsAux] using hP⟩
  | l, acc, .byteArray a :: S => by
    obtain ⟨P, hP⟩ := runsAux_run0 l (.byteArray a :: acc) S
    exact ⟨.byteArray a :: P, by simpa [runsAux] using hP⟩

/-- **`runPhB` of a sub-run**: in a run `xs ++ ys ++ zs` passing `runPhB`,
`ys` at its pc passes `runPhB` (every pc and target in the same phase). -/
theorem runPhB_sub {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {pc ra : Int64}
    {xs ys zs : List Directive} (h : runPhB okPc ph lab pc ra (xs ++ ys ++ zs) = true) :
    runPhB okPc ph lab (pc + Int64.ofNat (4 * xs.length)) ra ys = true := by
  have hpc : ∀ k, pc + Int64.ofNat (4 * xs.length) + Int64.ofNat (4 * k) =
      pc + Int64.ofNat (4 * (xs.length + k)) := fun k => (ofNat4_add pc _ _).symm
  unfold runPhB
  rw [List.all_eq_true]
  intro k hk
  have hk' := List.mem_range.mp hk
  have hlen : xs.length + k < (xs ++ ys ++ zs).length := by simp; omega
  have hlen0 : xs.length + 0 < (xs ++ ys ++ zs).length := by simp; omega
  have h0 : ph (pc + Int64.ofNat (4 * xs.length)).toBitVec.toNat = ph pc.toBitVec.toNat := by
    simpa using (runPhB_get h hlen0).2.1
  obtain ⟨h1, h2, h3⟩ := runPhB_get h hlen
  have hget : (xs ++ ys ++ zs)[xs.length + k] = ys[k] := by
    simp only [List.append_assoc]
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    exact List.getElem_append_left hk'
  rw [hget] at h3
  rw [List.getElem?_eq_getElem hk', hpc]
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, h0]
  exact ⟨⟨h1, h2⟩, h3⟩

section Code

variable {cx : FnCtx} {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
  {ra : Int64}

/-- **A piece `c` of a run is at `CdC`**: after the instructions `xs` in the
code after `l` (`segIn`), the runs from there passing `runPhB`. -/
theorem cdC_at {l : Label} {xs c zs : List Directive} (hseg : segIn prog l (xs ++ c ++ zs) = true)
    (hx : xs.all isIns = true) (hc : c.all isIns = true)
    (hph : ∀ r ∈ runsAux l xs.reverse (c ++ zs), runPhB okPc ph lab (lab r.1) ra r.2 = true) :
    CdC prog okPc ph lab ra (lab l + Int64.ofNat (4 * xs.length)) c := by
  obtain ⟨P, hP⟩ := runsAux_run0 l (c.reverse ++ xs.reverse) zs
  rw [← runsAux_shift _ _ _ _ (noLabel_of_isIns hc)] at hP
  have hr := hph _ hP
  simp only [List.reverse_append, List.reverse_reverse] at hr
  exact ⟨hc, l, xs.length, rfl, blockAt_of_segIn hseg hx hc, runPhB_sub hr⟩

/-- **A block's code after its label gives `CodeC`**: the code `c1` of its
instructions numbered from `k` (`instsItems`, `InstC` but the stack abort's
call) and `c2` of its terminator (`TermC`), after the instructions `xs` and
before `zs` in the code after `l` (`segIn`), every run from there passing
`runPhB` at `lab` (`hph`); the stack maps on (`hm`), and `lab` following the
labels' gaps (`hgap`). -/
theorem codeC_of_seg (hm : cx.maps = true)
    (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    {frames : Option Nat} {tm : Scc.IR.Term} (htm : TermC frames tm) :
    ∀ (is : List Scc.IR.Inst) (k : Nat) (l : Label) (c1 c2 : List Item) (xs zs : List Directive),
      (∀ i ∈ is, InstC i ∧ i ≠ abortI) → instsItems cx k is = .ok c1 →
      cx.term (k + is.length) tm = .ok c2 →
      segIn prog l (xs ++ directives (c1 ++ c2) ++ zs) = true → xs.all isIns = true →
      (∀ r ∈ runsAux l xs.reverse (directives (c1 ++ c2) ++ zs), runPhB okPc ph lab (lab r.1) ra r.2 = true) →
      (∀ r ∈ runsAux l xs.reverse (directives (c1 ++ c2) ++ zs), ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat) →
      CodeC cx (CdC prog okPc ph lab ra) (BlC prog okPc ph lab cx ra) k (lab l + Int64.ofNat (4 * xs.length))
        is tm
  | [], k, l, c1, c2, xs, zs, _, hi, ht, hseg, hx, hph, _ => by
    simp only [instsItems] at hi
    cases hi
    simp only [List.nil_append, List.length_nil, Nat.add_zero] at hseg hph ht
    by_cases hu : tm = .unreachable
    · exact Or.inl hu
    · exact Or.inr ⟨c2, ht, cdC_at hseg hx (term_allIns htm hu ht) hph⟩
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
        by_cases hc : Spike.Lib.LowerShape.isCall i = false
        · -- an instruction other than a call: instructions only
          have hA : (directives ci).all isIns = true := inst_allIns hs'.1.1 hc hci
          refine Or.inl ⟨hc, ci, hci, ?_, ?_⟩
          · exact cdC_at (zs := directives (c1' ++ c2) ++ zs) (by simpa only [List.append_assoc] using hseg) hx hA
              (by simpa only [List.append_assoc] using hph)
          · have hxA : (xs ++ directives ci).all isIns = true := by rw [List.all_append, hx, hA]; rfl
            have := codeC_of_seg hm hgap htm is (k + 1) l c1' c2 (xs ++ directives ci) zs hs'.2 hc1 ht
              (by simpa only [List.append_assoc] using hseg) hxA
              (by
                rw [List.reverse_append, ← runsAux_shift _ _ _ _ (noLabel_of_isIns hA)]
                simpa only [List.append_assoc] using hph)
              (by
                rw [List.reverse_append, ← runsAux_shift _ _ _ _ (noLabel_of_isIns hA)]
                simpa only [List.append_assoc] using hrl)
            rwa [List.length_append, ofNat4_add] at this
        · obtain ⟨hI, hnA⟩ := hs'.1
          cases hI with
          | call d g w _ =>
            obtain ⟨lw, ls, hw, hsr, hAw, hAs, hd⟩ := inst_call1_inv hm hci
            have hAw' : (directives lw).all isIns = true := hAw
            have hAs' : (directives ls).all isIns = true := hAs
            change directives ci = directives lw ++ blD (Scc.Lower.Names.user g) :: _ at hd
            rw [hd] at hseg hph hrl
            generalize hDd : directives (c1' ++ c2) = D at hseg hph hrl
            generalize hK : cx.local s!"sp{k}" = spK at hseg hph hrl
            generalize hB : blD (Scc.Lower.Names.user g) = B at hseg hph hrl
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
            -- the return label in the phase of `ra`
            have hspk : ph (lab spK).toBitVec.toNat = ph ra.toBitVec.toNat := by
              obtain ⟨P, hP⟩ := runsAux_run0 spK [] (directives ls ++ D ++ zs)
              exact hrlS _ hP
            have hxw : (xs ++ directives lw).all isIns = true := by rw [List.all_append, hx, hAw']; rfl
            have hxwb : (xs ++ directives lw ++ [B]).all isIns = true := by
              rw [List.append_assoc, List.all_append, hx, hwb]; rfl
            -- the return label's address
            have hsp : lab spK =
                lab l + Int64.ofNat (4 * xs.length) + Int64.ofNat (4 * (directives lw).length) + 4 := by
              have := hgap _ _ _ (labelGap_of_segIn hseg' hxwb)
              rwa [List.length_append, List.length_append, List.length_singleton, ofNat4_succ, ofNat4_add] at this
            have hseg2 : segIn prog spK (directives ls ++ D ++ zs) = true := segIn_label hseg'
            refine Or.inr ⟨d, g, w, lw, ls, rfl, hw, hsr, ?_, ?_, ?_, ?_⟩
            · -- the argument's load
              refine ⟨hAw', l, xs.length, rfl, ?_, ?_⟩
              · exact blockAt_of_segIn (zs := [B] ++ .label spK :: (directives ls ++ D ++ zs))
                  (by simpa only [List.append_assoc] using hseg') hx hAw'
              · exact runPhB_sub (zs := [B]) (by simpa only [List.append_assoc] using hr0)
            · -- the `bl` and its return label
              subst hB hK
              refine ⟨l, xs.length + (directives lw).length, (ofNat4_add _ _ _), ?_, ?_, ?_, ?_⟩
              · have := blockAt_of_segIn (xs := xs ++ directives lw) (ys := [blD (Scc.Lower.Names.user g)])
                  (zs := .label (cx.local s!"sp{k}") :: (directives ls ++ D ++ zs)) hseg' hxw rfl
                rwa [List.length_append] at this
              · have := labelGap_of_segIn hseg' hxwb
                rwa [List.length_append, List.length_append, List.length_singleton] at this
              · have := blkPh_of_runPhB (xs := xs ++ directives lw) (ys := [blD (Scc.Lower.Names.user g)])
                  (zs := []) (by simpa using hr0) (by simp [classify])
                rwa [List.length_append, ofNat4_add] at this
              · rw [← hsp]; exact hspk
            · -- the result's store
              have := cdC_at (l := spK) (xs := []) (zs := D ++ zs)
                (by simpa only [List.append_assoc, List.nil_append] using hseg2) rfl hAs'
                (by simpa only [List.append_assoc, List.reverse_nil] using hrs)
              rwa [List.length_nil, ofNat4_zero, hsp] at this
            · -- the rest of the block, after the return label
              subst hDd hK
              have := codeC_of_seg hm hgap htm is (k + 1) _ c1' c2 (directives ls) zs hs'.2 hc1 ht
                (by simpa only [List.append_assoc] using hseg2) hAs'
                (by
                  rw [← List.append_nil (directives ls).reverse, ← runsAux_shift _ _ _ _ (noLabel_of_isIns hAs')]
                  simpa only [List.append_assoc] using hrs)
                (by
                  rw [← List.append_nil (directives ls).reverse, ← runsAux_shift _ _ _ _ (noLabel_of_isIns hAs')]
                  simpa only [List.append_assoc] using hrlS)
              rwa [hsp] at this
          | abort => exact absurd rfl hnA
          | _ => exact absurd rfl hc

end Code

/-! ## On a laid-out program -/

section Lays

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {kp : Nat}

/-- **`codeC_of_seg`'s `hgap`** at the labels of a laid-out program. -/
theorem hgap_of_lays (hp : Scc.Cert.Rt.A64.Lays exe prog kp) :
    ∀ a b n, labelGap prog a b n = true →
      (_root_.Executable.labels exe).label b = (_root_.Executable.labels exe).label a + Int64.ofNat (4 * n) :=
  fun _ _ _ h => Scc.Cert.Rt.A64.label_labelGap hp h

/-- **A piece at `CdC` is in the code** of a laid-out program, at its
labels. -/
theorem cdOf_cdC (hp : Scc.Cert.Rt.A64.Lays exe prog kp) {endPc : Int64}
    (hend : endPc = Scc.Cert.Rt.A64.endOf exe prog kp) {okPc : Nat → Bool} {ph : Nat → Nat} {ra : Int64} :
    ∀ pc blk, CdC prog okPc ph (_root_.Executable.labels exe).label ra pc blk → CdOf exe endPc pc blk :=
  fun _ _ ⟨_, _, _, hpc, hb, _⟩ => Spike.Lib.A64.Flow.code_of hp hend hb hpc

/-- **A call at `BlC` is in the code** of a laid-out program, at its
labels (`callPre_of`'s `hBl`). -/
theorem cdOf_blC (hp : Scc.Cert.Rt.A64.Lays exe prog kp) {endPc : Int64}
    (hend : endPc = Scc.Cert.Rt.A64.endOf exe prog kp) {okPc : Nat → Bool} {ph : Nat → Nat} {cx : FnCtx}
    {ra : Int64} :
    ∀ pc g k, BlC prog okPc ph (_root_.Executable.labels exe).label cx ra pc g k → CdOf exe endPc pc [blD g] :=
  fun _ _ _ ⟨_, _, hpc, hb, _⟩ => Spike.Lib.A64.Flow.code_of hp hend hb hpc

end Lays

/-- **A call's return address at `BlC` is in the phase of `ra`**. -/
theorem blC_ph {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {cx : FnCtx}
    {ra pc : Int64} {g : Label} {k : Nat} (h : BlC prog okPc ph lab cx ra pc g k) :
    ph (pc + 4).toBitVec.toNat = ph ra.toBitVec.toNat :=
  h.choose_spec.choose_spec.2.2.2.2

/-! ## From the placement checks -/

/-- **`runPhB` reads the labels at the run's targets only.** -/
theorem runPhB_congr {okPc : Nat → Bool} {ph : Nat → Nat} {lab lab' : Label → Int64} {pc ra : Int64}
    {blk : List Directive} (h : ∀ L ∈ blkLabs blk, lab L = lab' L) :
    runPhB okPc ph lab pc ra blk = runPhB okPc ph lab' pc ra blk := by
  unfold runPhB
  congr 1
  funext k
  congr 1
  cases hk : blk[k]? with
  | none => rfl
  | some d =>
    simp only
    cases hc : classify d with
    | none => rfl
    | some a =>
      simp only
      rw [aiTgts_congr fun L hL => h L ?_]
      exact List.mem_filterMap.mpr ⟨d, List.mem_of_getElem? hk, by rw [hc]; exact hL⟩

/-- An instruction other than a call is not the stack abort's call. -/
theorem ne_abortI_of_isCall {i : Scc.IR.Inst} (h : Spike.Lib.LowerShape.isCall i = false) : i ≠ abortI := by
  rintro rfl
  simp [Spike.Lib.LowerShape.isCall] at h

/-- **A block of `lowerC`'s shape not ending in `unreachable` has no stack
abort's call**: only the bracket's abort block `deepBlock` has one. -/
theorem ne_abortI_of_callBlk {lcx : Scc.Lower.Ctx} {b : Scc.IR.Block} (hb : Spike.Lib.LowerCall.CallBlk lcx b)
    (ht : b.term ≠ .unreachable) : ∀ i ∈ b.insts, i ≠ abortI := by
  cases hb with
  | deep n => exact absurd rfl ht
  | plain b hn => exact fun i hi => ne_abortI_of_isCall (hn i hi)
  | call n g w rest t _ _ hn =>
    intro i hi
    simp only [Spike.Lib.LowerCall.callBlk, List.mem_append] at hi
    rcases hi with hi | hi
    · rintro rfl
      simp [Scc.Lower.Inv.callPost] at hi
    · exact ne_abortI_of_isCall (hn i hi)

section Place

variable {cx : FnCtx} {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
  {ra : Int64} {lo : Nat}

/-- **A placed block's code gives `CodeC`** at its label: its code after
the label (`segIn`) and its runs' phase facts at the code labels (`labC`),
every label read resolving, which `lab` agrees with (`hlab`); the block of
`lowerC`'s shape (`BlockC`) without the stack abort's call. -/
theorem codeC_block (hm : cx.maps = true)
    (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a)
    {frames : Option Nat} {b : Scc.IR.Block} (hs : Spike.Lib.LowerShape.BlockC frames b)
    (hna : ∀ i ∈ b.insts, i ≠ abortI) {k : Nat} {l : Label} {code : List Item}
    (hc : blockItems cx k b = .ok code) (hseg : segIn prog l (directives code) = true)
    (hph : ∀ r ∈ runs l (directives code),
      runPh okPc ph (labC lo prog) (fun l => (codeOf lo prog l).isSome) ra r = true ∧
        ph (labC lo prog r.1).toBitVec.toNat = ph ra.toBitVec.toNat) :
    CodeC cx (CdC prog okPc ph lab ra) (BlC prog okPc ph lab cx ra) k (lab l) b.insts b.term := by
  cases hi : instsItems cx k b.insts with
  | error e => simp [blockItems, hi, bind, Except.bind] at hc
  | ok c1 =>
    cases ht : cx.term (k + b.insts.length) b.term with
    | error e => simp [blockItems, hi, ht, bind, Except.bind] at hc
    | ok c2 =>
      simp [blockItems, hi, ht, bind, Except.bind, pure, Except.pure] at hc
      subst hc
      have := codeC_of_seg (okPc := okPc) (ph := ph) (ra := ra) hm hgap hs.2 b.insts k l c1 c2 [] []
        (fun i hi => ⟨hs.1 i hi, hna i hi⟩) hi ht (by simpa using hseg) rfl
        (fun r hr => by
          have h' := (hph r (by simpa [runs] using hr)).1
          simp only [runPh, Bool.and_eq_true] at h'
          obtain ⟨⟨hres, hlabs⟩, hrun⟩ := h'
          rw [labC_eq hlab hres, runPhB_congr fun L hL => labC_eq hlab (List.all_eq_true.mp hlabs L hL)] at hrun
          exact hrun)
        (fun r hr => by
          have h' := hph r (by simpa [runs] using hr)
          simp only [runPh, Bool.and_eq_true] at h'
          obtain ⟨⟨⟨hres, -⟩, -⟩, hp⟩ := h'
          rw [labC_eq hlab hres] at hp
          exact hp)
      simpa [ofNat4_zero] using this

/-- **The later blocks' code** (`BlocksCodeC`) at `CdC` and `BlC`, from the
function's `blocksOk` and `blocksPh` (the blocks `bs` after `pre`). -/
theorem blocksCodeC (hm : cx.maps = true)
    (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a)
    {frames : Option Nat} {pre bs : List Scc.IR.Block} (hok : blocksOk prog cx 0 (pre ++ bs) = true)
    (hph : blocksPh okPc ph (labC lo prog) (fun l => (codeOf lo prog l).isSome) cx ra 0 (pre ++ bs) = true)
    (hs : ∀ b ∈ bs, Spike.Lib.LowerShape.BlockC frames b)
    (hna : ∀ b ∈ bs, b.term ≠ .unreachable → ∀ i ∈ b.insts, i ≠ abortI) :
    BlocksCodeC cx (CdC prog okPc ph lab ra) (BlC prog okPc ph lab cx ra) lab bs := by
  intro b hb hu
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hb
  have e : pre ++ (s ++ b :: t) = (pre ++ s) ++ b :: t := by simp only [List.append_assoc]
  rw [e] at hok hph
  obtain ⟨l, code, hl, hc, hseg⟩ := blocksOk_block hok
  obtain ⟨l', code', hl', hc', hr⟩ := blocksPh_blockPh hph
  rw [hl] at hl'; cases hl'
  rw [hc] at hc'; cases hc'
  exact ⟨l, _, hl, codeC_block hm hgap hlab (hs b hb) (hna b hb hu) hc hseg hr⟩

/-- **The entry block's code** (`CodeC` at the entry's label, numbered from
0) from the function's `blocksOk` and `blocksPh`. -/
theorem entryCodeC (hm : cx.maps = true)
    (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a)
    {frames : Option Nat} {b : Scc.IR.Block} {bs : List Scc.IR.Block} {entry : Label}
    (hent : cx.blockLabel b.label = .ok entry) (hok : blocksOk prog cx 0 (b :: bs) = true)
    (hph : blocksPh okPc ph (labC lo prog) (fun l => (codeOf lo prog l).isSome) cx ra 0 (b :: bs) = true)
    (hs : Spike.Lib.LowerShape.BlockC frames b) (hna : ∀ i ∈ b.insts, i ≠ abortI) :
    CodeC cx (CdC prog okPc ph lab ra) (BlC prog okPc ph lab cx ra) 0 (lab entry) b.insts b.term := by
  obtain ⟨l, code, hl, hc, hseg⟩ := blocksOk_block (pre := []) hok
  obtain ⟨l', code', hl', hc', hr⟩ := blocksPh_blockPh (pre := []) hph
  rw [hl] at hl'; cases hl'
  rw [hc] at hc'; cases hc'
  rw [hent] at hl; cases hl
  exact codeC_block hm hgap hlab hs hna hc hseg hr

/-- **A code block's function's code** (`bodyC_segS`'s two code premises):
the function `func1 name (params1R d) r` of the closed form `r` of an
`Accepted1` code block `d` (`lowerC` without the depth counter), its entry
block at `CodeC` from 0 and its later blocks at `BlocksCodeC`, from its
`blocksOk` and `blocksPh`. -/
theorem fnCodeC (hm : cx.maps = true)
    (hgap : ∀ a b n, labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    (hlab : ∀ l a, codeOf lo prog l = some a → lab l = Int64.ofNat a)
    {lcx : Scc.Lower.Ctx} (hf : lcx.frames = none) {earlier : List String} {d : Decl}
    (hd : Scc.Lower.decl1 earlier d = true) {r : Res1}
    (hr : Scc.Lower.Inv.lowerC lcx (Scc.Lower.Inv.env1 d) 0 "entry" 0 d.body = some r) {name : Scc.IR.Sym}
    {entry : Label} (hent : cx.blockLabel "entry" = .ok entry)
    (hok : blocksOk prog cx 0 (func1 name (params1R d) r).blocks = true)
    (hph : blocksPh okPc ph (labC lo prog) (fun l => (codeOf lo prog l).isSome) cx ra 0
      (func1 name (params1R d) r).blocks = true) :
    CodeC cx (CdC prog okPc ph lab ra) (BlC prog okPc ph lab cx ra) 0 (lab entry) r.insts r.term ∧
      BlocksCodeC cx (CdC prog okPc ph lab ra) (BlC prog okPc ph lab cx ra) lab r.blocks := by
  have hsh := Spike.Lib.LowerShape.func1_shape lcx hd hr name
  have hna := Spike.Lib.LowerCall.lowerC_noStackAbort lcx hf d.body _ _ _ _ r hr
  refine ⟨entryCodeC (b := ⟨"entry", r.insts, r.term⟩) (bs := r.blocks) hm hgap hlab hent hok hph
    (hsh _ (List.mem_cons_self ..)) hna.1, ?_⟩
  exact blocksCodeC (pre := [⟨"entry", r.insts, r.term⟩]) hm hgap hlab hok hph
    (fun b hb => hsh b (List.mem_cons_of_mem _ hb))
    fun b hb _ => hna.2 b hb

end Place

/-- **A code block's function's code from `PlaceOK`, at `fnPh1_ofPlaceOK`'s
witnesses**: for the closed forms `rs` and runtime functions `rt` and the
`j`th declaration's entry label, blocks and phase facts as
`fnPh1_ofPlaceOK` gives them, at the layout `RuntimeLayout.ofPlaceOK h i`,
the function's context places stack-map labels (`maps`), its entry block is
at `CodeC` from 0 and its later blocks are at `BlocksCodeC`. -/
theorem fnCodeC_of_fnPh1 {cfg : Scc.Config} {p : CoreTerm.Prog} (hp : Scc.Lower.Accepted1 p = true)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.A64.placeOKAt pcfg Λ
      (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) {rs : List Res1} {rt : List Scc.IR.Func}
    (hir : (Scc.Lower.A64.lowerAll cfg p).low.ir =
      Scc.Lower.Inv.progOf cfg.layout rt (Spike.Lib.LowerNode.funcs1 p rs))
    {j : Nat} {d : Decl} {r : Res1} (hd : p[j]? = some d)
    (hL : Spike.Lib.LowerNode.LowC p cfg.layout.obj none d r) {entry : Label}
    (hent : (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir (rt.length + j)
      (func1 (Scc.Lower.Names.user d.name) (params1R d) r)).blockLabel "entry" = .ok entry)
    (hbo : blocksOk (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog
      (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir (rt.length + j)
        (func1 (Scc.Lower.Names.user d.name) (params1R d) r)) 0
      (func1 (Scc.Lower.Names.user d.name) (params1R d) r).blocks = true)
    {ra : Int64}
    (hbp : blocksPh (Spike.Lib.A64.PhRec.okPc (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h i))
      (Spike.Lib.A64.PhRec.ph (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h i))
      (labC Λ.code.lo (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog)
      (fun l => (codeOf Λ.code.lo (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog l).isSome)
      (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir (rt.length + j)
        (func1 (Scc.Lower.Names.user d.name) (params1R d) r)) ra 0
      (func1 (Scc.Lower.Names.user d.name) (params1R d) r).blocks = true) :
    let o := Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)
    let Ly := Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h i
    let cx := ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir (rt.length + j)
      (func1 (Scc.Lower.Names.user d.name) (params1R d) r)
    cx.maps = true ∧
      CodeC cx (CdC o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab ra)
          (BlC o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab cx ra) 0
          (Ly.lab entry) r.insts r.term ∧
        BlocksCodeC cx (CdC o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab ra)
          (BlC o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab cx ra) Ly.lab r.blocks := by
  intro o Ly cx
  have hm : cx.maps = true := by
    show (Scc.Lower.A64.lowerAll cfg p).low.ir.growth.isSome = true
    rw [hir]; rfl
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h i (rS := Spike.Lib.A64.Rt.rS0 Ly)
  have hgap : ∀ a b n, labelGap o.prog a b n = true → Ly.lab b = Ly.lab a + Int64.ofNat (4 * n) :=
    fun _ _ _ hg => by rw [← hI.labOk]; exact Scc.Cert.Rt.A64.label_labelGap hI.lays hg
  obtain ⟨earlier, hd1⟩ := Spike.Lib.LowerNode.decl1_of_decls1 p [] (Spike.Lib.LowerNode.decls1_of_accepted1 hp)
    d (List.mem_of_getElem? hd)
  exact ⟨hm, fnCodeC hm hgap (lab_ofPlaceOK h i) rfl hd1 hL hent hbo hbp⟩

/-- **Each code block's function's code from `PlaceOK`** on an `Accepted1`
program, at the layout `RuntimeLayout.ofPlaceOK h i` (any immediates `i`),
as `fnPh1_ofPlaceOK` numbers them: the `j`th declaration `d` with its closed
form `r` (`lowerC` without the depth counter) is the function `func1 (user
d.name) (params1R d) r`, whose context places stack-map labels (`maps`),
whose entry block is at `CodeC` from 0 and whose later blocks are at
`BlocksCodeC`, at every return address of the phase of the one after
`scc_rt_main`'s `bl`. With `fnPh1_ofPlaceOK`'s other facts, use
`fnCodeC_of_fnPh1` at its witnesses. -/
theorem fnCodeC_ofPlaceOK {cfg : Scc.Config} {p : CoreTerm.Prog} (hp : Scc.Lower.Accepted1 p = true)
    {em : Scc.Lower.A64.Emitted} (hlow : Scc.Lower.A64.lowerAll? cfg p = .ok em)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.A64.placeOKAt pcfg Λ
      (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) :
    let o := Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)
    let ir := (Scc.Lower.A64.lowerAll cfg p).low.ir
    let Ly := Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h i
    let ra := Int64.ofBitVec (Ly.lab Spike.Lib.A64.Rt.bareMC.e0 + 4).toBitVec
    ∃ (rs : List Res1) (rt : List Scc.IR.Func),
      Spike.Lib.LowerNode.Pairwise2 (Spike.Lib.LowerNode.LowC p cfg.layout.obj none) p rs ∧
      ir = Scc.Lower.Inv.progOf cfg.layout rt (Spike.Lib.LowerNode.funcs1 p rs) ∧
      ∀ (j : Nat) (d : Decl) (r : Res1), p[j]? = some d → rs[j]? = some r →
        let f := func1 (Scc.Lower.Names.user d.name) (params1R d) r
        let cx := ctxOf ir (rt.length + j) f
        Spike.Lib.LowerNode.LowC p cfg.layout.obj none d r ∧ cx.maps = true ∧
        ∃ entry : Label, cx.blockLabel "entry" = .ok entry ∧
          ∀ ra' : Int64,
            Spike.Lib.A64.PhRec.ph Ly ra'.toBitVec.toNat = Spike.Lib.A64.PhRec.ph Ly ra.toBitVec.toNat →
            CodeC cx (CdC o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab ra')
                (BlC o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab cx ra') 0
                (Ly.lab entry) r.insts r.term ∧
              BlocksCodeC cx (CdC o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab ra')
                (BlC o.prog (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) Ly.lab cx ra') Ly.lab
                r.blocks := by
  intro o ir Ly ra
  obtain ⟨rs, rt, hrs, hir, -, H⟩ := fnPh1_ofPlaceOK hp hlow h i
  refine ⟨rs, rt, hrs, hir, fun j d r hd hr => ?_⟩
  obtain ⟨hL, -, -, -, -, entry, -, hent, -, -, hbo, hbp, -⟩ := H j d r hd hr
  have H' := fun ra' hra => fnCodeC_of_fnPh1 hp h i hir hd hL hent hbo (hbp ra' hra)
  exact ⟨hL, (H' ra rfl).1, entry, hent, fun ra' hra => (H' ra' hra).2⟩

end Spike.Lib.LowerA64
