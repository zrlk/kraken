/-
**A control placed from its slot representation** (x86-64): `Placed` and
`SlotPlacedI` (`Spike/Lib/X64ConsumerS.lean`, `X64FramesPlacedI.lean`) at a
control whose words a symbolic environment places in a slot file
(`SlotRepAt`, `Spike/Lib/SlotRepAt.lean`), locatives included: the
generalization of `slotPlacedI_of_srep` from numbers (`EnvNum`) to every
word the lowering places (a register's word, an immediate, a locative's
register base with its offset in a register or folded).

Each slot `k` of the file is at a target place `pf k` holding its value
(`hcell`): a stack slot's cell, or, at a pending store, a register.

- `wpOf`: a word's placement as a target word place (`envmPf`: the map);
- `wpOf_rep`, `wpOf_some`, `wpOf_places`, `wpOf_imm`: represented,
  defined at a register base, places among `pf`'s, an immediate only from
  an immediate operand;
- `placedPf_of_slotRep`: the place map's facts;
- `placed_of_slotRep`, `slotPlacedI_of_slotRep` (every slot a cell of `A`),
  `placedS_of_slotPlacedI` (with the suspended frames), `SlotPlacedI.of_eq`
  (kept by a state agreeing on `A`).
-/
import Spike.Lib.X64FramesPlacedI
import Spike.Lib.SlotRepAt

namespace Spike.Lib.X64ConsumerS

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib.X64Consumer
open Spike.Lib.Form (opdVal SEnv lookupS WordPl SRep WordRep WordsRep)
open Spike.Lib.LowerNode (SlotRepAt LocBaseRegAt ImmIn)

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {s s' : State} {c : Ctl} {fs : List TermRun.Frame}

/-- The place of a target register id. -/
abbrev PlX := Place (machine (kernel 1)).I.RegId

/-- **A word's placement as a target word place**, slot `k` at `pf k`: an
immediate operand at its immediate, a register's word at its slot's place,
a locative's register base at its slot's place with its offset at its
slot's place or folded; nothing at an immediate base. -/
def wpOf (rs : Scc.IR.Reg → Option Int) (pf : Int → PlX) : WordPl → Option (WordPlace (machine (kernel 1)).I.RegId)
  | .one (.imm v) => some (.imm v.toNat)
  | .one (.reg r) => (rs r).map fun k => .one (pf k)
  | .loc (.reg rb) (.reg ro) => (rs rb).bind fun kb => (rs ro).map fun ko => .loc (pf kb) (.at (pf ko))
  | .loc (.reg rb) (.imm v) => (rs rb).map fun kb => .loc (pf kb) (.imm v.toNat)
  | .loc (.imm _) _ => none

/-- **The place map of a symbolic environment** (`wpOf` at each word). -/
def envmPf (rs : Scc.IR.Reg → Option Int) (pf : Int → PlX) (senv : SEnv) (x : String) (k : Nat) :
    Option (WordPlace (machine (kernel 1)).I.RegId) :=
  ((lookupS senv x).bind (·.2[k]?)).bind (wpOf rs pf)

variable {rs : Scc.IR.Reg → Option Int} {pf : Int → PlX} {sl : Int → BitVec 64}

theorem locRep_of_form {x : WeakMem.Val} {vb vo : Nat} (h : Spike.Lib.Form.LocRep lbl x vb vo) :
    Scc.Sem.LocRep lbl x vb vo := by
  cases x <;> simp_all [Spike.Lib.Form.LocRep, Scc.Sem.LocRep]

/-- **A placed word is represented** at its target word place. -/
theorem wpOf_rep (hcell : ∀ r k, rs r = some k → placeVal (machine (kernel 1)) s (pf k) = some (sl k).toNat)
    {w : TermRun.Word} {pl : WordPl} (h : WordRep lbl (opdVal rs sl) w pl)
    {wp : WordPlace (machine (kernel 1)).I.RegId} (hw : wpOf rs pf pl = some wp) :
    WordPlaceRep (machine (kernel 1)) lbl s wp w.val := by
  match pl, h, hw with
  | .one (.imm v), ⟨v', hv, hr⟩, hw =>
    simp only [wpOf, Option.some.injEq] at hw; subst hw
    simp only [opdVal, Option.some.injEq] at hv; subst hv
    exact hr
  | .one (.reg r), ⟨v', hv, hr⟩, hw =>
    obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp hw
    simp only [opdVal, hk, Option.map_some, Option.some.injEq] at hv; subst hv
    exact ⟨_, hcell r k hk, hr⟩
  | .loc (.reg rb) (.reg ro), ⟨vb, vo, hb, ho, hr⟩, hw =>
    obtain ⟨kb, hkb, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨ko, hko, rfl⟩ := Option.map_eq_some_iff.mp hw
    simp only [opdVal, hkb, hko, Option.map_some, Option.some.injEq] at hb ho; subst hb ho
    exact ⟨_, _, hcell rb kb hkb, hcell ro ko hko, locRep_of_form hr⟩
  | .loc (.reg rb) (.imm v), ⟨vb, vo, hb, ho, hr⟩, hw =>
    obtain ⟨kb, hkb, rfl⟩ := Option.map_eq_some_iff.mp hw
    simp only [opdVal, hkb, Option.map_some, Option.some.injEq] at hb ho; subst hb ho
    exact ⟨_, _, hcell rb kb hkb, rfl, locRep_of_form hr⟩
  | .loc (.imm _) _, _, hw => cases hw

/-- **A represented word with a register base has a target word place.** -/
theorem wpOf_some {w : TermRun.Word} {pl : WordPl} (h : WordRep lbl (opdVal rs sl) w pl)
    (hb : ∀ b o, pl = .loc b o → ∃ r, b = .reg r) : ∃ wp, wpOf rs pf pl = some wp := by
  match pl, h, hb with
  | .one (.imm v), _, _ => exact ⟨_, rfl⟩
  | .one (.reg r), ⟨v', hv, _⟩, _ =>
    obtain ⟨k, hk, -⟩ := Option.map_eq_some_iff.mp hv
    exact ⟨.one (pf k), by simp [wpOf, hk]⟩
  | .loc (.reg rb) (.reg ro), ⟨vb, vo, hb', ho, _⟩, _ =>
    obtain ⟨kb, hkb, -⟩ := Option.map_eq_some_iff.mp hb'
    obtain ⟨ko, hko, -⟩ := Option.map_eq_some_iff.mp ho
    exact ⟨.loc (pf kb) (.at (pf ko)), by simp [wpOf, hkb, hko]⟩
  | .loc (.reg rb) (.imm v), ⟨vb, vo, hb', _, _⟩, _ =>
    obtain ⟨kb, hkb, -⟩ := Option.map_eq_some_iff.mp hb'
    exact ⟨.loc (pf kb) (.imm v.toNat), by simp [wpOf, hkb]⟩
  | .loc (.imm v) o, _, hb =>
    obtain ⟨r, hr⟩ := hb _ _ rfl
    cases hr

/-- **A target word place's places are slots' places.** -/
theorem wpOf_places {pl : WordPl} {wp : WordPlace (machine (kernel 1)).I.RegId} (hw : wpOf rs pf pl = some wp) :
    ∀ q ∈ wp.places, ∃ r k, rs r = some k ∧ q = pf k := by
  match pl, hw with
  | .one (.imm v), hw =>
    simp only [wpOf, Option.some.injEq] at hw; subst hw
    simp [WordPlace.places]
  | .one (.reg r), hw =>
    obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp hw
    intro q hq
    simp only [WordPlace.places, List.mem_singleton] at hq
    exact ⟨r, k, hk, hq⟩
  | .loc (.reg rb) (.reg ro), hw =>
    obtain ⟨kb, hkb, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨ko, hko, rfl⟩ := Option.map_eq_some_iff.mp hw
    intro q hq
    simp only [WordPlace.places, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨rb, kb, hkb, rfl⟩
    · exact ⟨ro, ko, hko, rfl⟩
  | .loc (.reg rb) (.imm v), hw =>
    obtain ⟨kb, hkb, rfl⟩ := Option.map_eq_some_iff.mp hw
    intro q hq
    simp only [WordPlace.places, List.mem_singleton] at hq
    exact ⟨rb, kb, hkb, hq⟩
  | .loc (.imm _) _, hw => cases hw

/-- **A whole-word immediate place only from an immediate operand.** -/
theorem wpOf_imm {pl : WordPl} {n : Nat} (hw : wpOf rs pf pl = some (.imm n)) :
    ∃ v, pl = .one (.imm v) ∧ n = v.toNat := by
  match pl, hw with
  | .one (.imm v), hw =>
    simp only [wpOf, Option.some.injEq, WordPlace.imm.injEq] at hw
    exact ⟨v, rfl, hw.symm⟩
  | .one (.reg r), hw =>
    obtain ⟨k, -, hk⟩ := Option.map_eq_some_iff.mp hw; cases hk
  | .loc (.reg rb) (.reg ro), hw =>
    obtain ⟨kb, -, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨ko, -, hk⟩ := Option.map_eq_some_iff.mp hw; cases hk
  | .loc (.reg rb) (.imm v), hw =>
    obtain ⟨kb, -, hk⟩ := Option.map_eq_some_iff.mp hw; cases hk
  | .loc (.imm _) _, hw => cases hw

/-- **The place map's facts at a control placed in a slot file**: each
placed word represented at `s` (every slot at its place, `hcell`), every
word of a free variable placed, every place a slot's, an immediate the
table's at the control's term. -/
theorem placedPf_of_slotRep {i : Expr → String → Nat → Option Nat} (h : SlotRepAt i lbl rs sl c)
    (hcell : ∀ r k, rs r = some k → placeVal (machine (kernel 1)) s (pf k) = some (sl k).toNat) :
    ∃ envm : String → Nat → Option (WordPlace (machine (kernel 1)).I.RegId),
      (∀ x ty ws, TermRun.lookupE c.env x = some (ty, ws) → ∀ k wd wp, ws[k]? = some wd → envm x k = some wp →
        WordPlaceRep (machine (kernel 1)) lbl s wp wd.val) ∧
      (∀ x ∈ exprFv c.term, ∀ ty ws, TermRun.lookupE c.env x = some (ty, ws) → ∀ k < ws.length,
        ∃ pl, envm x k = some pl) ∧
      (∀ x k wp, envm x k = some wp → ∀ q ∈ wp.places, ∃ r k, rs r = some k ∧ q = pf k) ∧
      (∀ x k n, envm x k = some (.imm n) → i c.term x k = some n) := by
  obtain ⟨senv, hsr, htot, hbase, himm⟩ := h
  -- a placed word's placement, its binding and its representation
  have hget : ∀ x k wp, envmPf rs pf senv x k = some wp → ∃ t pls pl, lookupS senv x = some (t, pls) ∧
      pls[k]? = some pl ∧ wpOf rs pf pl = some wp := by
    intro x k wp hem
    obtain ⟨pl, hpl, hw⟩ := Option.bind_eq_some_iff.mp hem
    obtain ⟨⟨t, pls⟩, hs, hk⟩ := Option.bind_eq_some_iff.mp hpl
    exact ⟨t, pls, pl, hs, hk, hw⟩
  refine ⟨envmPf rs pf senv, fun x ty ws hl k wd wp hwd hem => ?_, fun x hx ty ws hl k hk => ?_,
    fun x k wp hem => ?_, fun x k n hem => ?_⟩
  · obtain ⟨t, pls, pl, hs, hpk, hw⟩ := hget x k wp hem
    obtain ⟨ws', hl', hW⟩ := hsr x t pls hs
    rw [hl] at hl'; cases hl'
    exact wpOf_rep hcell (wordsRep_get hW hwd hpk) hw
  · obtain ⟨⟨t, pls⟩, hs⟩ := Option.isSome_iff_exists.mp (htot x hx)
    obtain ⟨ws', hl', hW⟩ := hsr x t pls hs
    rw [hl] at hl'; cases hl'
    have hlen := hW.length
    obtain ⟨pl, hpk⟩ : ∃ pl, pls[k]? = some pl := ⟨pls[k], List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨wd, hwd⟩ : ∃ wd, ws[k]? = some wd := ⟨ws[k], List.getElem?_eq_getElem hk⟩
    have hR := wordsRep_get hW hwd hpk
    obtain ⟨wp, hw⟩ := wpOf_some (pf := pf) hR fun b o he =>
      hbase x hx _ pls hs b o (he ▸ List.mem_of_getElem? hpk)
    exact ⟨wp, by simp only [envmPf, hs, Option.bind_some, hpk, hw]⟩
  · obtain ⟨t, pls, pl, -, -, hw⟩ := hget x k wp hem
    exact wpOf_places hw
  · obtain ⟨t, pls, pl, hs, hpk, hw⟩ := hget x k _ hem
    obtain ⟨v, rfl, rfl⟩ := wpOf_imm hw
    exact himm x k v (by simp only [hs, Option.bind_some, hpk])

/-- **A control placed in a slot file is placed** (`Placed`), the
immediates the layout's. -/
theorem placed_of_slotRep (h : SlotRepAt Λ.imms lbl rs sl c)
    (hcell : ∀ r k, rs r = some k → placeVal (machine (kernel 1)) s (pf k) = some (sl k).toNat) :
    Placed Λ lbl s c :=
  let ⟨envm, hrep, htot, _, himm⟩ := placedPf_of_slotRep h hcell
  ⟨envm, hrep, htot, himm⟩

/-- **A control placed in a slot file whose slots are cells of `A`** is
placed in the slots of `A` (`SlotPlacedI` at its term): slot `k` the cell
at `addr k`, loading `sl k` (`hcell`). -/
theorem slotPlacedI_of_slotRep {A : Nat → Prop} {addr : Int → BitVec 64} (h : SlotRepAt Λ.imms lbl rs sl c)
    (hcell : ∀ r k, rs r = some k → privLoad s (addr k) = some (sl k))
    (hA : ∀ r k, rs r = some k → A (addr k).toNat) :
    SlotPlacedI Λ lbl s c A c.term := by
  obtain ⟨envm, hrep, htot, hpl, himm⟩ := placedPf_of_slotRep (pf := fun k => .slot (addr k).toNat) h
    (fun r k hk => by
      show (privLoad s (BitVec.ofNat 64 (addr k).toNat)).map (·.toNat) = _
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, hcell r k hk]; rfl)
  refine ⟨envm, hrep, htot, fun x k wp hem q hq => ?_, himm⟩
  obtain ⟨r, k', hk', rfl⟩ := hpl x k wp hem q hq
  exact ⟨_, rfl, hA r k' hk'⟩

/-- **Placed in the slots of `A` is kept** by a state whose private memory
agrees on `A`. -/
theorem SlotPlacedI.of_eq {A : Nat → Prop} {t : Expr} (h : SlotPlacedI Λ lbl s c A t)
    (hA : ∀ a, A a → (machine (kernel 1)).privLoad s' (BitVec.ofNat 64 a) =
      (machine (kernel 1)).privLoad s (BitVec.ofNat 64 a)) :
    SlotPlacedI Λ lbl s' c A t :=
  let ⟨envm, hrep, htot, hin, himm⟩ := h
  ⟨envm, fun x ty ws hx k wd wp hwd hwp =>
    wordPlaceRep_of_eqI hA (hin x k wp hwp) (hrep x ty ws hx k wd wp hwd hwp), htot, hin, himm⟩

/-- **The control placed at its term and the suspended frames placed** is
every frame placed. -/
theorem placedS_of_slotPlacedI {A B : Nat → Prop} (h : SlotPlacedI Λ lbl s c A c.term)
    (hf : FramesPlacedInI Λ lbl s fs B) : PlacedS Λ lbl s c fs :=
  let ⟨envm, hrep, htot, _, himm⟩ := h
  PlacedS.ofFrames ⟨envm, hrep, htot, himm⟩ hf.toFramesPlaced

/--
info: 'Spike.Lib.X64ConsumerS.placedPf_of_slotRep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms placedPf_of_slotRep

end Spike.Lib.X64ConsumerS
