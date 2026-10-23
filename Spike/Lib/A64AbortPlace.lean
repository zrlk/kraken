/-
**The places of the overflow abort's source** (AArch64): the consumer's
`Placed` (`Spike/Lib/A64Consumer.lean`) at a state `s`, from the lowering's
symbolic environment at the abort label (`AbSrc`'s `SRep`,
`Spike/Lib/LowerNode.lean`), with the frame cells the operands are valued in
loading in `s` (`hcell`, for a stub's state: the caller's cells kept by the
callee's frame condition).

* `envmOf`: the place map: an immediate word at its immediate, a register's
  word at its cell's address; a numeric environment has no locative words;
* `placed_of_srepAb`: `Placed`, given the immediates' table (`himm`, the
  layout's `imms` at the control's term);
* `placed_of_abSrc`: the same from `AbSrc`.
-/
import Spike.Lib.A64StubFacts
import Spike.Lib.LowerNode

namespace Spike.Lib.A64Consumer

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Spike.Lib.Form (opdVal SEnv lookupS WordPl WordRep WordsRep SRep)
open Spike.Lib.LowerNode (EnvNum AbSrc)

/-- **The words of a binding at their placements**, one at a time. -/
theorem wordsRep_get {lbl : Lbl} {val : Scc.IR.Operand → Option Nat} {ws : List TermRun.Word} {pls : List WordPl}
    (h : WordsRep lbl val ws pls) {k : Nat} {w : TermRun.Word} {pl : WordPl} (hw : ws[k]? = some w)
    (hp : pls[k]? = some pl) : WordRep lbl val w pl := by
  induction ws generalizing pls k with
  | nil => simp at hw
  | cons w' ws ih =>
    cases pls with
    | nil => simp at hp
    | cons pl' pls =>
      cases k with
      | zero => simp at hw hp; subst hw; subst hp; exact h.1
      | succ k => exact ih h.2 (by simpa using hw) (by simpa using hp)

/-- A bound binding is in the environment. -/
theorem mem_of_lookupE {env : TermRun.Env} {x : String} {t : Ty} {ws : List TermRun.Word}
    (h : TermRun.lookupE env x = some (t, ws)) : (x, t, ws) ∈ env := by
  unfold TermRun.lookupE at h
  obtain ⟨b, hb, hbe⟩ := Option.map_eq_some_iff.mp h
  have hm := List.mem_of_find?_eq_some hb
  have hx := List.find?_some hb
  obtain ⟨x', t', ws'⟩ := b
  simp only [beq_iff_eq] at hx
  simp only at hbe
  cases hbe; subst hx; exact hm

/-- **The place map** of a symbolic environment: an immediate word at its
immediate, a register's word at its cell's address (`addr`), nothing
else. -/
def envmOf (rs : Scc.IR.Reg → Option Int) (addr : Int → BitVec 64) (senv : SEnv) (x : String) (k : Nat) :
    Option (WordPlace (machine (kernel 1)).I.RegId) :=
  match (lookupS senv x).bind (·.2[k]?) with
  | some (.one (.imm v)) => some (.imm v.toNat)
  | some (.one (.reg r)) => (rs r).map fun k' => .one (.slot (addr k').toNat)
  | _ => none

/-- **The abort's source is placed at `s`**: the symbolic environment
represents the source's in the slot file `sl`, every bound word is a
number, every free variable of the term is placed, each register's cell
loads its slot in `s` (`hcell`), and the immediates are the layout's
(`himm`). -/
theorem placed_of_srepAb {Λ : Scc.Sem.Layout} {lbl : Lbl} {rs : Scc.IR.Reg → Option Int} {senv : SEnv}
    {sl : Int → BitVec 64} {c : Ctl} {s : State} {addr : Int → BitVec 64}
    (hsr : SRep lbl (opdVal rs sl) senv c.env) (hnum : EnvNum c.env)
    (htot : ∀ y ∈ exprFv c.term, (lookupS senv y).isSome)
    (hcell : ∀ r k, rs r = some k → privLoad s (addr k) = some (sl k))
    (himm : ∀ x k v, (lookupS senv x).bind (·.2[k]?) = some (.one (.imm v)) → Λ.imms c.term x k = some v.toNat) :
    Placed Λ lbl s c := by
  refine ⟨envmOf rs addr senv, fun x ty ws hl k wd wp hwd hem => ?_, fun x hx ty ws hl k hk => ?_,
    fun x k n hem => ?_⟩
  · unfold envmOf at hem
    split at hem
    · next v hb =>
      cases hem
      obtain ⟨t, pls, hs, hpk⟩ : ∃ t pls, lookupS senv x = some (t, pls) ∧ pls[k]? = some (.one (.imm v)) := by
        cases h : lookupS senv x with
        | none => rw [h] at hb; cases hb
        | some p => rw [h] at hb; exact ⟨p.1, p.2, rfl, hb⟩
      obtain ⟨ws', hl', hW⟩ := hsr x t pls hs
      rw [hl] at hl'; cases hl'
      obtain ⟨v', hv', hR⟩ := wordsRep_get hW hwd hpk
      cases hv'; exact hR
    · next r hb =>
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hem
      obtain ⟨t, pls, hs, hpk⟩ : ∃ t pls, lookupS senv x = some (t, pls) ∧ pls[k]? = some (.one (.reg r)) := by
        cases h : lookupS senv x with
        | none => rw [h] at hb; cases hb
        | some p => rw [h] at hb; exact ⟨p.1, p.2, rfl, hb⟩
      obtain ⟨ws', hl', hW⟩ := hsr x t pls hs
      rw [hl] at hl'; cases hl'
      obtain ⟨v', hv', hR⟩ := wordsRep_get hW hwd hpk
      simp only [opdVal, hk', Option.map_some] at hv'
      cases hv'
      refine ⟨(sl k').toNat, ?_, hR⟩
      show (privLoad s (BitVec.ofNat 64 (addr k').toNat)).map (·.toNat) = _
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, hcell r k' hk']; rfl
    · cases hem
  · obtain ⟨⟨t, pls⟩, hs⟩ := Option.isSome_iff_exists.mp (htot x hx)
    obtain ⟨ws', hl', hW⟩ := hsr x t pls hs
    rw [hl] at hl'; cases hl'
    have hlen := hW.length
    obtain ⟨pl, hpk⟩ : ∃ pl, pls[k]? = some pl := ⟨pls[k], List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨wd, hwd⟩ : ∃ wd, ws[k]? = some wd := ⟨ws[k], List.getElem?_eq_getElem hk⟩
    have hR := wordsRep_get hW hwd hpk
    obtain ⟨n, hn, -⟩ := hnum _ (mem_of_lookupE hl) wd (List.mem_of_getElem? hwd)
    unfold envmOf
    rw [hs]
    simp only [Option.bind_some, hpk]
    cases pl with
    | one o =>
      cases o with
      | imm v => exact ⟨_, rfl⟩
      | reg r =>
        obtain ⟨v, hv, -⟩ := hR
        simp only [opdVal] at hv
        obtain ⟨k', hk', -⟩ := Option.map_eq_some_iff.mp hv
        simp only [hk', Option.map_some]
        exact ⟨_, rfl⟩
    | loc b off =>
      obtain ⟨vb, vo, -, -, hL⟩ := hR
      rw [hn] at hL
      cases hL
  · unfold envmOf at hem
    split at hem
    · next v hb => cases hem; exact himm x k v hb
    · next r hb =>
      obtain ⟨k', -, he⟩ := Option.map_eq_some_iff.mp hem
      cases he
    · cases hem

/-- **The abort's source is placed at `s`**, from the node invariant at the
abort label (`AbSrc`) in the slot file `sl`. -/
theorem placed_of_abSrc {Λ : Scc.Sem.Layout} {lbl : Lbl} {rs : Scc.IR.Reg → Option Int} {senv : SEnv}
    {sl : Int → BitVec 64} {c : Ctl} {s : State} {addr : Int → BitVec 64} (h : AbSrc lbl rs senv sl c)
    (hcell : ∀ r k, rs r = some k → privLoad s (addr k) = some (sl k))
    (himm : ∀ x k v, (lookupS senv x).bind (·.2[k]?) = some (.one (.imm v)) → Λ.imms c.term x k = some v.toNat) :
    Placed Λ lbl s c :=
  placed_of_srepAb h.2.2.1 h.2.1 h.2.2.2 hcell himm

end Spike.Lib.A64Consumer
