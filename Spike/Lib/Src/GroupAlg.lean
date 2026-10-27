import Spike.Lib.Src.Walk21

/-!
**The placements' algebra** (`Form.grp`, `Form.group`): how grouping a
value's runtime operands into placements commutes with the lowering's
operand lists at a pair, an index unpack and a split, so that the symbolic
environment `ofEnv2` of the lowering's environment after these constructs
is the one `Form.sstep` computes.

- `opLen t`, `plLen t`: the operands a value of type `t` takes and the
  placements it groups into (a locative: two operands, one placement);
- `grp_spec`: `grp t` consumes `opLen t` operands, gives `plLen t`
  placements, and depends only on its prefix (`grp t (pre ++ e)`);
- `slots_opLen`, `valWords_opLen`: `opLen` is the layout's word count;
- `group_grp`: a grouping of exactly `ws` groups `ws ++ e` leaving `e`;
- `group_pair`: a pair's operands `ws ++ vs` group as the components'
  placements, appended (the lowering's and `sstep`'s `pair`);
- `group_iex`: an index package groups as its body (the lowering's and
  `sstep`'s `unpack`);
- `group_split`: a product's grouping splits at `valWords u` operands
  (the lowering's `let (x, y)`) into the components' groupings, the first
  `plLen u` placements long (`sstep`'s split takes `nWords (accs u)`
  placements: equal where `accs_plLen` holds).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.IR
open Spike.Lib.Form (WordPl grp group)

/-! ## Operand and placement counts -/

/-- **The operands a value of type `t` takes** (as `Form.grp` consumes
them); `none` off the layout fragment. -/
def opLen : Ty → Option Nat
  | .unit | .void => some 0
  | .int | .intS _ | .fix _ _ | .lanes _ _ | .ptr _ _ | .tid => some 1
  | .loc _ _ => some 2
  | .prod a b => do pure ((← opLen a) + (← opLen b))
  | .refine t _ | .iall t | .mu t => opLen t
  | t@(.iex b) | t@(.tex _ b) => if Scc.Obj.coupledPair t then none else opLen b
  | _ => none

/-- **The placements a value of type `t` groups into** (a locative's two
operands are one placement). -/
def plLen : Ty → Option Nat
  | .unit | .void => some 0
  | .int | .intS _ | .fix _ _ | .lanes _ _ | .ptr _ _ | .tid | .loc _ _ => some 1
  | .prod a b => do pure ((← plLen a) + (← plLen b))
  | .refine t _ | .iall t | .mu t => plLen t
  | t@(.iex b) | t@(.tex _ b) => if Scc.Obj.coupledPair t then none else plLen b
  | _ => none

/-- **`grp t` consumes `opLen t` operands into `plLen t` placements and
reads only them.** -/
theorem grp_spec : ∀ (t : Ty) (os : List Operand) (p : List WordPl) (r : List Operand),
    grp t os = some (p, r) → ∃ k, opLen t = some k ∧ plLen t = some p.length ∧ k ≤ os.length ∧
      r = os.drop k ∧ ∀ e, grp t (os.take k ++ e) = some (p, e) := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro os p r h
    simp only [grp] at h
    cases ha : grp a os with
    | none => simp [ha] at h
    | some x =>
      obtain ⟨p1, os1⟩ := x
      cases hb : grp b os1 with
      | none => simp [ha, hb] at h
      | some y =>
        obtain ⟨p2, os2⟩ := y
        simp only [ha, hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨k1, h1, l1, le1, rfl, e1⟩ := iha os p1 os1 ha
        obtain ⟨k2, h2, l2, le2, rfl, e2⟩ := ihb _ p2 _ hb
        simp only [List.length_drop] at le2
        refine ⟨k1 + k2, by simp [opLen, h1, h2], by simp [plLen, l1, l2], by omega,
          by rw [List.drop_drop], fun e => ?_⟩
        rw [List.take_add, List.append_assoc]
        simp [grp, e1, e2]
  | refine t _ ih => intro os p r h; simpa [grp, opLen, plLen] using ih os p r h
  | iall t ih => intro os p r h; simpa [grp, opLen, plLen] using ih os p r h
  | mu t ih => intro os p r h; simpa [grp, opLen, plLen] using ih os p r h
  | iex b ih =>
    intro os p r h
    simp only [grp] at h
    split at h
    · simp at h
    · rename_i hc
      simpa [grp, opLen, plLen, hc] using ih os p r h
  | tex k b ih =>
    intro os p r h
    simp only [grp] at h
    split at h
    · simp at h
    · rename_i hc
      simpa [grp, opLen, plLen, hc] using ih os p r h
  | _ =>
    intro os p r h
    rcases os with _ | ⟨o, _ | ⟨o2, os⟩⟩
    all_goals simp only [grp, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    all_goals obtain ⟨rfl, rfl⟩ := h
    all_goals exact ⟨_, rfl, rfl, by simp, by simp, fun e => by simp [grp]⟩

/-- **`opLen` is the layout's word count.** -/
theorem slots_opLen : ∀ (t : Ty) (s r : Nat) (l : List (Bool × Nat)), Scc.Obj.slots t s r = some l →
    opLen t = some l.length := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro s r l h
    simp only [Scc.Obj.slots] at h
    cases ha : Scc.Obj.slots a s r with
    | none => simp [ha] at h
    | some la =>
      cases hb : Scc.Obj.slots b (s + la.countP (!·.1)) (r + la.countP (·.1)) with
      | none => simp [ha, hb] at h
      | some lb =>
        simp only [ha, hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        simp [opLen, iha s r la ha, ihb _ _ lb hb]
  | refine t _ ih => intro s r l h; simpa [opLen] using ih s r l h
  | iall t ih => intro s r l h; simpa [opLen] using ih s r l h
  | mu t ih => intro s r l h; simpa [opLen] using ih s r l h
  | iex b ih =>
    intro s r l h
    simp only [Scc.Obj.slots] at h
    split at h
    · simp at h
    · rename_i hc
      simpa [opLen, hc] using ih s r l h
  | tex k b ih =>
    intro s r l h
    simp only [Scc.Obj.slots] at h
    split at h
    · simp at h
    · rename_i hc
      simpa [opLen, hc] using ih s r l h
  | _ =>
    intro s r l h
    simp only [Scc.Obj.slots, Option.some.injEq, reduceCtorEq] at h
    all_goals subst h
    all_goals rfl

theorem valWords_opLen {t : Ty} {n : Nat} (h : Scc.Obj.valWords t = some n) : opLen t = some n := by
  simp only [Scc.Obj.valWords] at h
  cases hs : Scc.Obj.slots t 0 0 with
  | none => simp [hs] at h
  | some l =>
    simp only [hs, Option.map_some, Option.some.injEq] at h
    rw [slots_opLen t 0 0 l hs, h]

/-! ## Groupings -/

/-- A grouping of exactly `ws` groups `ws ++ e` leaving `e`, and takes all
of `ws`. -/
theorem group_grp {t : Ty} {ws : List Operand} {p : List WordPl} (h : group t ws = some p) :
    opLen t = some ws.length ∧ plLen t = some p.length ∧ ∀ e, grp t (ws ++ e) = some (p, e) := by
  have hg : grp t ws = some (p, []) := by
    simp only [group] at h
    split at h
    · rename_i pls hg; simp only [Option.some.injEq] at h; subst h; exact hg
    · simp at h
  obtain ⟨k, hk, hl, hle, hr, he⟩ := grp_spec t ws p [] hg
  have hk' : k = ws.length := by
    have := congrArg List.length hr
    simp at this
    omega
  subst hk'
  refine ⟨hk, hl, fun e => ?_⟩
  simpa using he e

/-- **A pair's operands group as its components' placements, appended.** -/
theorem group_pair {t u : Ty} {ws vs : List Operand} {p q : List WordPl} (ht : group t ws = some p)
    (hu : group u vs = some q) : group (.prod t u) (ws ++ vs) = some (p ++ q) := by
  have h1 := (group_grp ht).2.2 vs
  have h2 := (group_grp hu).2.2 []
  simp only [List.append_nil] at h2
  simp [group, grp, h1, h2]

/-- **An index package groups as its body.** -/
theorem group_iex {b : Ty} {ws : List Operand} {p : List WordPl} (h : group (.iex b) ws = some p) :
    group b ws = some p := by
  simp only [group, grp] at h
  by_cases hc : Scc.Obj.coupledPair (.iex b) = true
  · simp [hc] at h
  · simpa [group, hc] using h

/-- **A product's grouping splits at its first component's operands**:
`valWords u` operands into `plLen u` placements, the rest into the second
component's. -/
theorem group_split {u w : Ty} {ws : List Operand} {pls : List WordPl} {n : Nat}
    (h : group (.prod u w) ws = some pls) (hn : Scc.Obj.valWords u = some n) :
    ∃ pu pw, plLen u = some pu.length ∧ group u (ws.take n) = some pu ∧ group w (ws.drop n) = some pw ∧
      pls = pu ++ pw := by
  have hg : grp (.prod u w) ws = some (pls, []) := by
    simp only [group] at h
    split at h
    · rename_i pls' hg; simp only [Option.some.injEq] at h; subst h; exact hg
    · simp at h
  simp only [grp] at hg
  cases ha : grp u ws with
  | none => simp [ha] at hg
  | some x =>
    obtain ⟨pu, os1⟩ := x
    cases hb : grp w os1 with
    | none => simp [ha, hb] at hg
    | some y =>
      obtain ⟨pw, os2⟩ := y
      simp only [ha, hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      obtain ⟨k, hk, hl, hle, rfl, he⟩ := grp_spec u ws pu os1 ha
      have hkn : k = n := by
        have := valWords_opLen hn
        rw [hk] at this
        exact Option.some.inj this
      subst hkn
      refine ⟨pu, pw, hl, ?_, ?_, rfl⟩
      · have := he []
        simp only [List.append_nil] at this
        simp [group, this]
      · simp [group, hb]

/-! ## `sstep`'s split count -/

/-- **`sstep`'s split count is the placements'** where the source's
accesses count one per placement (`accs`, a locative one access): checked
per type. -/
def accsPl (t : Ty) : Bool := (TermRun.accs t).map TermRun.nWords == plLen t

theorem accs_plLen {t : Ty} (h : accsPl t = true) {us : List TermRun.Acc} (hu : TermRun.accs t = some us) :
    plLen t = some (TermRun.nWords us) := by
  simp only [accsPl, hu, Option.map_some, beq_iff_eq] at h
  exact h.symm

/-! ## Tests: `hello1L.w`'s `main` -/

/-- The slice type of `hello1L.w`'s `print`: a locative to `i` lane words
initialised, its index, the byte count. -/
private def sliceTyT : Ty :=
  .prod (.prod (.refine (.loc .own (.array (.var 0) (.lanes false .w8))) (.ini (.var 0)))
    (.intS (.var 0))) .int

-- `main`'s split of its argument: the package takes four operands in three placements,
-- `sstep`'s count agrees, and the thread id is one of each.
#guard opLen (.iex sliceTyT) == some 4 && plLen (.iex sliceTyT) == some 3
#guard accsPl (.iex sliceTyT) && accsPl (.ptr .pub .void) && accsPl sliceTyT
#guard Scc.Obj.valWords (.iex sliceTyT) == some 4
#guard (group (.prod (.iex sliceTyT) (.ptr .pub .void)) [.reg "b", .reg "o", .reg "m", .reg "n", .reg "t"]).map
  List.length == some 4

end Spike.Lib.LowerNode
