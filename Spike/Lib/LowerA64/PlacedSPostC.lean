/-
**The setup call's continuation placed in registers** (AArch64): at the
post `SPostC` of the setup call (`Spike/Lib/LowerA64/SetupCall2.lean`), the
control the setup function's `ret` pops its frame into is placed (`Placed`,
and with no suspended frame `PlacedS`) in every target state whose
registers `ρ j` hold the result registers' words (`argRegs[j]` at the
`ret`'s registers), as many as the returned operands, the rest of the
caller's environment placed off immediates. The returned words are placed
in the registers `ρ` by their placements (`RetJS`); the caller's words where
the premise has them.

- `SPostC.placed`: the operands' count (at most the result registers', the
  result type's word count at a simple type), and
  `Placed` at every state agreeing with the result registers through `ρ`;
- `SPostC.placedP`: the same at any places `ρ` holding the result registers'
  words (a register or a frame slot);
- `SPostC.placedS`: the same at `PlacedS` with no suspended frame.
-/
import Spike.Lib.LowerA64.SetupCall2
import Spike.Lib.A64PlacedSlot
import Spike.Lib.Src.NJLS
import Spike.Lib.Src.GroupShape

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (WordPlace WordPlaceRep Place placeVal)
open Scc.Sem.A64 (machine kernel)
open Spike.Lib.A64Consumer
open Spike.Lib.Form (WordPl WordRep WordsRep)
open Spike.Lib.Form (group)
open Spike.Lib.LowerNode (group_opds group_grp group_grpL groupL_erase compat_shapeOf_self valWords_opLen)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ty : Ty} {c0 c : Ctl} {rs : Reg64s}

/-- A bound variable of an environment extended by another variable is the
environment's. -/
theorem lookupE_cons_ne {env : TermRun.Env} {x y : String} {t : Ty} {ws : List TermRun.Word} (h : y ≠ x) :
    TermRun.lookupE ((x, t, ws) :: env) y = TermRun.lookupE env y := by
  have : (x == y) = false := by simpa [beq_iff_eq] using Ne.symm h
  simp [TermRun.lookupE, List.find?, this]

/-- The variable an environment was extended by is bound to its words. -/
theorem lookupE_cons_eq {env : TermRun.Env} {x : String} {t : Ty} {ws : List TermRun.Word} :
    TermRun.lookupE ((x, t, ws) :: env) x = some (t, ws) := by
  simp [TermRun.lookupE, List.find?]

/-- The value of a general register's target id is the register's. -/
theorem regVal_idx (s : State) (r : XReg) : Scc.Sem.A64.regVal s (.x r.idx) = (s.st.1.regs.getXReg r).toBitVec := by
  cases r <;> rfl

/-- **A word with a target place off immediates**: `wp` represents `w` in
`s`, and is no immediate. -/
def OffImm (lbl : Lbl) (s : State) (w : TermRun.Word) (wp : WordPlace (machine (kernel 1)).I.RegId) : Prop :=
  (∀ n, wp ≠ .imm n) ∧ WordPlaceRep (machine (kernel 1)) lbl s wp w.val

open Classical in
/-- **The setup call's continuation is placed through result places**:
at `SPostC` at the `ret`'s registers `rs`, some operands `ops`, at most the
result registers, such that at every state `s` whose place `ρ j` holds
result register `j`'s word of `rs` for each operand `j` (`hρ`), and whose
places represent every word of the caller's environment off immediates
(`h0`), the continuation is placed (`Placed`); at a simple result type
with a runtime layout, the operands are as many as its words. -/
theorem SPostC.placedP (h : SPostC p lbl ty c0 c rs) :
    ∃ ops : List Scc.IR.Operand, ops.length ≤ Scc.Emit.A64.argRegs.length ∧
      (Scc.Lower.simpleTy ty = true → ∀ n, Scc.Obj.valWords ty = some n → ops.length = n) ∧
      ∀ (Λ : Scc.Sem.Layout) (s : State) (ρ : Nat → Place (machine (kernel 1)).I.RegId),
        (∀ j (_hj : j < ops.length) (hr : j < Scc.Emit.A64.argRegs.length),
          placeVal (machine (kernel 1)) s (ρ j) = some (rs.getXReg Scc.Emit.A64.argRegs[j]).toBitVec.toNat) →
        (∀ y t ws, TermRun.lookupE c0.env y = some (t, ws) → ∀ k (hk : k < ws.length), ∃ wp, OffImm lbl s ws[k] wp) →
        Placed Λ lbl s c := by
  obtain ⟨cE, fr, cr, a, t, ws, hct, ⟨σ, hσ, hJ, hL⟩, hra, hev, rfl⟩ := h
  obtain ⟨a', t', ws', ops, pls, val, hra', -, hev', hg, hn, hv, hW, -⟩ := hJ
  rw [hra] at hra'
  cases hra'
  rw [hev] at hev'
  cases hev'
  have hfe : fr.env = c0.env := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, rfl⟩ := hct
    rfl
  refine ⟨ops, hn, fun hs n hk => ?_, fun Λ s ρ hρ h0 => ?_⟩
  · -- the operands' count at the result type: `a`'s layout is `ty`'s (`RetL`)
    obtain ⟨a2, lc, ha2, hEL, hsc, hlit, hr, -⟩ := hL
    rw [hra] at ha2
    cases ha2
    have hc := (hEL.evalAt' hsc hlit hev).1
    have hgt : group ty ops = some pls := by
      rw [group_grpL (compat_shapeOf_self hs hk), ← hr, groupL_erase, ← group_grpL hc, hg]
    have h1 := (group_grp hgt).1
    rw [valWords_opLen hk] at h1
    exact (Option.some.inj h1).symm
  -- the index of an operand among `ops`
  let pick : Scc.IR.Operand → Nat := fun o =>
    if hx : ∃ j, ∃ hj : j < ops.length, ops[j] = o then Classical.choose hx else 0
  have hpick : ∀ o ∈ ops, ∃ hj : pick o < ops.length, ops[pick o] = o := by
    intro o ho
    have hx : ∃ j, ∃ hj : j < ops.length, ops[j] = o := List.getElem_of_mem ho
    simp only [pick, dite_eq_left hx]
    exact Classical.choose_spec hx
  let opPl : Scc.IR.Operand → Place (machine (kernel 1)).I.RegId := fun o => ρ (pick o)
  have hopPl : ∀ o ∈ ops, ∀ v, val o = some v → placeVal (machine (kernel 1)) s (opPl o) = some v := by
    intro o ho v hvo
    obtain ⟨hj, hoj⟩ := hpick o ho
    have hr : pick o < Scc.Emit.A64.argRegs.length := Nat.lt_of_lt_of_le hj hn
    have h1 := hv (pick o) hj hr
    rw [hoj, hvo, hσ] at h1
    rw [Option.some.inj h1]
    exact hρ (pick o) hj hr
  let wpR : WordPl → WordPlace (machine (kernel 1)).I.RegId
    | .one o => .one (opPl o)
    | .loc b off => .loc (opPl b) (.at (opPl off))
  let envm : String → Nat → Option (WordPlace (machine (kernel 1)).I.RegId) := fun x k =>
    if x = fr.x then pls[k]?.map wpR
    else ((TermRun.lookupE c0.env x).bind fun b => b.2[k]?).bind fun wd =>
      if hx : ∃ wp, OffImm lbl s wd wp then some (Classical.choose hx) else none
  have hlen := hW.length
  refine ⟨envm, fun x ty' ws' hl k wd wp hwd hem => ?_, fun x _ ty' ws' hl k hk => ?_, fun x k n hem => ?_⟩
  · simp only [envm] at hem
    split at hem
    · subst x
      rw [lookupE_cons_eq] at hl
      cases hl
      obtain ⟨pl, hpl, rfl⟩ := Option.map_eq_some_iff.mp hem
      have hR := wordsRep_get hW hwd hpl
      have hmem : ∀ o ∈ pl.opds, o ∈ ops := fun o ho => by
        rw [← group_opds hg]
        exact List.mem_flatMap.mpr ⟨pl, List.mem_of_getElem? hpl, ho⟩
      cases pl with
      | one o =>
        obtain ⟨v, hvo, hvr⟩ := hR
        exact ⟨v, hopPl o (hmem o (by simp [WordPl.opds])) v hvo, hvr⟩
      | loc b off =>
        obtain ⟨vb, vo, hvb, hvo, hlr⟩ := hR
        exact ⟨vb, vo, hopPl b (hmem b (by simp [WordPl.opds])) vb hvb,
          hopPl off (hmem off (by simp [WordPl.opds])) vo hvo, Spike.Lib.A64ConsumerS.locRep_of_form hlr⟩
    · rename_i hne
      rw [lookupE_cons_ne hne, hfe] at hl
      rw [hl] at hem
      simp only [Option.bind_some, hwd] at hem
      split at hem
      · rename_i hx
        cases hem
        exact (Classical.choose_spec hx).2
      · cases hem
  · by_cases hx : x = fr.x
    · subst x
      rw [lookupE_cons_eq] at hl
      cases hl
      refine ⟨wpR pls[k], ?_⟩
      simp only [envm, ite_eq_left rfl, List.getElem?_eq_getElem (show k < pls.length by omega), Option.map_some]
    · rw [lookupE_cons_ne hx, hfe] at hl
      have hex := h0 x ty' ws' hl k hk
      refine ⟨Classical.choose hex, ?_⟩
      simp only [envm, ite_eq_right hx, hl, Option.bind_some, List.getElem?_eq_getElem hk, dite_eq_left hex]
  · simp only [envm] at hem
    split at hem
    · obtain ⟨pl, -, hpl⟩ := Option.map_eq_some_iff.mp hem
      cases pl <;> cases hpl
    · obtain ⟨wd, -, hem⟩ := Option.bind_eq_some_iff.mp hem
      split at hem
      · rename_i hx
        exact absurd (Option.some.inj hem) ((Classical.choose_spec hx).1 n)
      · cases hem

/-- **The setup call's continuation is placed through result registers**:
at `SPostC` at the `ret`'s registers `rs`, some operands `ops`, at most the
result registers, such that at every state `s` whose register `ρ j` holds
result register `j`'s word of `rs` for each operand `j` (`hρ`), and whose
places represent every word of the caller's environment off immediates
(`h0`), the continuation is placed (`Placed`); at a simple result type
with a runtime layout, the operands are as many as its words. -/
theorem SPostC.placed (h : SPostC p lbl ty c0 c rs) :
    ∃ ops : List Scc.IR.Operand, ops.length ≤ Scc.Emit.A64.argRegs.length ∧
      (Scc.Lower.simpleTy ty = true → ∀ n, Scc.Obj.valWords ty = some n → ops.length = n) ∧
      ∀ (Λ : Scc.Sem.Layout) (s : State) (ρ : Nat → XReg),
        (∀ j (_hj : j < ops.length) (hr : j < Scc.Emit.A64.argRegs.length),
          s.st.1.regs.getXReg (ρ j) = rs.getXReg Scc.Emit.A64.argRegs[j]) →
        (∀ y t ws, TermRun.lookupE c0.env y = some (t, ws) → ∀ k (hk : k < ws.length), ∃ wp, OffImm lbl s ws[k] wp) →
        Placed Λ lbl s c := by
  obtain ⟨ops, hn, hw, hP⟩ := h.placedP
  exact ⟨ops, hn, hw, fun Λ s ρ hρ h0 => hP Λ s (fun j => .reg (.x (ρ j).idx)) (fun j hj hr => by
      show some (Scc.Sem.A64.regVal s (.x (ρ j).idx)).toNat = _
      rw [regVal_idx, hρ j hj hr]) h0⟩

/-- **The setup call's continuation is placed at no suspended frame**
(`SPostC.placed`, `PlacedS.ofNil`). -/
theorem SPostC.placedS (h : SPostC p lbl ty c0 c rs) :
    ∃ ops : List Scc.IR.Operand, ops.length ≤ Scc.Emit.A64.argRegs.length ∧
      (Scc.Lower.simpleTy ty = true → ∀ n, Scc.Obj.valWords ty = some n → ops.length = n) ∧
      ∀ (Λ : Scc.Sem.Layout) (s : State) (ρ : Nat → XReg),
        (∀ j (_hj : j < ops.length) (hr : j < Scc.Emit.A64.argRegs.length),
          s.st.1.regs.getXReg (ρ j) = rs.getXReg Scc.Emit.A64.argRegs[j]) →
        (∀ y t ws, TermRun.lookupE c0.env y = some (t, ws) → ∀ k (hk : k < ws.length), ∃ wp, OffImm lbl s ws[k] wp) →
        Placed Λ lbl s c ∧ Spike.Lib.A64ConsumerS.PlacedS Λ lbl s c [] := by
  obtain ⟨ops, hn, hw, hP⟩ := h.placed
  exact ⟨ops, hn, hw, fun Λ s ρ hρ h0 =>
    ⟨hP Λ s ρ hρ h0, Spike.Lib.A64ConsumerS.PlacedS.ofNil (hP Λ s ρ hρ h0)⟩⟩

/--
info: 'Spike.Lib.LowerA64.SPostC.placedP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SPostC.placedP

/--
info: 'Spike.Lib.LowerA64.SPostC.placed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SPostC.placed

/--
info: 'Spike.Lib.LowerA64.SPostC.placedS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SPostC.placedS

end Spike.Lib.LowerA64
