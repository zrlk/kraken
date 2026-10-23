/-
**The lowering's placements as `Components`' word places**: the bridge
from the symbolic environment of `Spike.Lib.Form` (`SEnv`, `SRep`: each
source word at a placement of IR operands) to the witness's register
environment of `Scc.Sem.Components` (`WordPlace`: a target place, a
locative's base and offset, or an immediate the layout's table names).

Given where each IR register lives on the target (`plr`: a register or a
stack slot, `Scc.Sem.Place`):

* `wordPlace`: a placement's word place; an immediate operand is the
  immediate `WordPlace.imm` (A′), a locative's immediate offset the
  immediate `OffPlace.imm`; a locative with an immediate base has none;
* `envMap`: the register environment of a symbolic environment, variable
  and word index ↦ word place (the first binding, as `lookupS`);
* `SRep.env_rep`: with every register operand valued at its place, every
  placed word is represented there (`WordPlaceRep`: `env_rep` of one
  frame);
* `SRep.env_total`: every word of every variable of a list some binding
  of `s` places (each placement with a word place) is placed (`env_total`
  of one frame, for the frame's free variables);
* `envMap_imm`: a word placed at an immediate is one the immediate table
  gives for it (`env_imm` of one frame), from the table agreeing with
  every immediate operand of `s`.

The hypotheses on concrete data (the generator's per-node environments,
`Scc/Cert/Place.lean`, and its immediate table, `renderImms`) are decided
by `simp`/`decide` (the tests at the end, on the `wc_rodata` return point
of `hello1.w`).
-/
import Spike.Lib.Form
import Scc.Sem.Correct

namespace Spike.Lib.Form

open CoreLang CoreTerm
open Scc.Sem (ValRep Place OffPlace WordPlace WordPlaceRep placeVal offVal)
open Scc.IR (Operand)

variable {R : Type}

/-! ## Word places of placements -/

/-- **An offset operand's place**: an immediate is the immediate offset, a
register its place. -/
def offPlace (plr : Scc.IR.Reg → Option (Place R)) : Operand → Option (OffPlace R)
  | .imm c => some (.imm c.toNat)
  | .reg r => (plr r).map .at

/-- **A placement's word place**: an immediate operand is the immediate
word place, a register its place; a locative its base's place (a register)
and its offset's. -/
def wordPlace (plr : Scc.IR.Reg → Option (Place R)) : WordPl → Option (WordPlace R)
  | .one (.imm c) => some (.imm c.toNat)
  | .one (.reg r) => (plr r).map .one
  | .loc (.reg b) off => do
      let pb ← plr b
      let po ← offPlace plr off
      pure (.loc pb po)
  | .loc (.imm _) _ => none

/-- **The register environment of a symbolic environment**: word `k` of
`x` at the word place of its placement (the first binding of `x`). -/
def envMap (plr : Scc.IR.Reg → Option (Place R)) (s : SEnv) : String → Nat → Option (WordPlace R) :=
  fun x k => (lookupS s x).bind fun b => b.2[k]?.bind (wordPlace plr)

variable {lbl : WeakMem.AllocLabel → Option Nat} {val : Operand → Option Nat}
  {plr : Scc.IR.Reg → Option (Place R)}

/-- A word at an immediate word place comes from an immediate operand. -/
theorem wordPlace_imm {pl : WordPl} {n : Nat} (h : wordPlace plr pl = some (.imm n)) :
    ∃ c : UInt64, pl = .one (.imm c) ∧ c.toNat = n := by
  match pl, h with
  | .one (.imm c), h => exact ⟨c, rfl, by simpa [wordPlace] using h⟩
  | .one (.reg r), h => simp [wordPlace] at h
  | .loc (.reg b) off, h =>
    simp only [wordPlace, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, -, _, -, h⟩ := h
    cases h
  | .loc (.imm _) _, h => simp [wordPlace] at h

/-- The scalar reading of a locative is `Components`' (`Scc.Sem.LocRep`). -/
theorem locRep_eq : LocRep lbl = Scc.Sem.LocRep lbl := by
  funext v vb vo
  cases v <;> rfl

variable {M : Scc.Sem.ExtMachine} {st : M.I.State}

/-- **A placed word is represented at its word place**, every register
operand valued at its place and every immediate at itself. -/
theorem wordPlace_rep (hi : ∀ c : UInt64, val (.imm c) = some c.toNat) {w : TermRun.Word} {pl : WordPl}
    {wp : WordPlace M.I.RegId}
    {plr : Scc.IR.Reg → Option (Place M.I.RegId)}
    (hv : ∀ r p, plr r = some p → val (.reg r) = placeVal M st p) (h : WordRep lbl val w pl)
    (hw : wordPlace plr pl = some wp) : WordPlaceRep M lbl st wp w.val := by
  match pl, h, hw with
  | .one (.imm c), ⟨v, hval, hr⟩, hw =>
    simp only [wordPlace, Option.some.injEq] at hw
    subst hw
    rw [hi c, Option.some.injEq] at hval
    subst hval
    exact hr
  | .one (.reg r), ⟨v, hval, hr⟩, hw =>
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hw
    exact ⟨v, (hv r p hp) ▸ hval, hr⟩
  | .loc (.reg b) off, ⟨vb, vo, hb, ho, hr⟩, hw =>
    simp only [wordPlace, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hw
    obtain ⟨pb, hpb, po, hpo, rfl⟩ := hw
    refine ⟨vb, vo, (hv b pb hpb) ▸ hb, ?_, locRep_eq ▸ hr⟩
    cases off with
    | imm c =>
      simp only [offPlace, Option.some.injEq] at hpo
      subst hpo
      rw [hi c, Option.some.injEq] at ho
      subst ho
      rfl
    | reg r =>
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hpo
      show placeVal M st p = some vo
      rw [← hv r p hp]; exact ho
  | .loc (.imm _) _, _, hw => simp [wordPlace] at hw

/-- Word `k` of a placement list. -/
theorem WordsRep.getElem? {ws : List TermRun.Word} {pls : List WordPl} (h : WordsRep lbl val ws pls) {k : Nat}
    {w : TermRun.Word} {pl : WordPl} (hw : ws[k]? = some w) (hp : pls[k]? = some pl) : WordRep lbl val w pl := by
  induction ws generalizing pls k with
  | nil => simp at hw
  | cons w' ws ih =>
    cases pls with
    | nil => simp [WordsRep] at h
    | cons pl' pls =>
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hw hp
        subst hw hp
        exact h.1
      | succ k => exact ih h.2 hw hp

namespace SRep

variable {s : SEnv} {env : TermRun.Env} {plr' : Scc.IR.Reg → Option (Place M.I.RegId)}

/-- **`env_rep` of one frame**: every word `envMap` places is represented
at its word place. -/
theorem env_rep (h : SRep lbl val s env) (hv : ∀ r p, plr' r = some p → val (.reg r) = placeVal M st p)
    (hi : ∀ c : UInt64, val (.imm c) = some c.toNat) :
    ∀ x ty ws, TermRun.lookupE env x = some (ty, ws) → ∀ k wd wp, ws[k]? = some wd → envMap plr' s x k = some wp →
      WordPlaceRep M lbl st wp wd.val := by
  intro x ty ws hl k wd wp hk hm
  simp only [envMap, Option.bind_eq_some_iff] at hm
  obtain ⟨⟨t, pls⟩, hs, pl, hpl, hw⟩ := hm
  obtain ⟨ws', hl', hr⟩ := h.lookup hs
  rw [hl] at hl'
  cases hl'
  exact wordPlace_rep hi hv (hr.getElem? hk hpl) hw

/-- **`env_total` of one frame**: every word of every variable of `xs` is
placed, when each is bound in `s` with a word place for each placement. -/
theorem env_total (h : SRep lbl val s env) {xs : List String}
    (hall : ∀ x ∈ xs, ∃ t pls, lookupS s x = some (t, pls) ∧ ∀ pl ∈ pls, (wordPlace plr pl).isSome) :
    ∀ x ∈ xs, ∀ ty ws, TermRun.lookupE env x = some (ty, ws) → ∀ k < ws.length, ∃ wp, envMap plr s x k = some wp := by
  intro x hx ty ws hl k hk
  obtain ⟨t, pls, hs, hpl⟩ := hall x hx
  obtain ⟨ws', hl', hr⟩ := h.lookup hs
  rw [hl] at hl'
  cases hl'
  have hk' : k < pls.length := hr.length ▸ hk
  obtain ⟨wp, hwp⟩ := Option.isSome_iff_exists.mp (hpl _ (List.getElem_mem hk'))
  exact ⟨wp, by simp [envMap, hs, List.getElem?_eq_getElem hk', hwp]⟩

end SRep

/-- **`env_imm` of one frame**: a word `envMap` places at an immediate is
one the table `imm` gives that constant for, when the table agrees with
every immediate operand of `s`. -/
theorem envMap_imm {s : SEnv} {imm : String → Nat → Option Nat}
    (himm : ∀ b ∈ s, ∀ k (c : UInt64), b.2.2[k]? = some (.one (.imm c)) → imm b.1 k = some c.toNat) :
    ∀ x k n, envMap plr s x k = some (.imm n) → imm x k = some n := by
  intro x k n hm
  simp only [envMap, Option.bind_eq_some_iff] at hm
  obtain ⟨⟨t, pls⟩, hs, pl, hpl, hw⟩ := hm
  obtain ⟨c, rfl, rfl⟩ := wordPlace_imm hw
  simp only [lookupS, Option.map_eq_some_iff] at hs
  obtain ⟨b, hb, hbe⟩ := hs
  have hbx : b.1 = x := by simpa using List.find?_some hb
  have := himm b (List.mem_of_find?_eq_some hb) k c (by rw [hbe]; exact hpl)
  rwa [hbx] at this

/-! ## Tests: the `wc_rodata` return point of `hello1.w`

At the return point of `newBuf`'s allocation call (`sp0`), the generator's
environment has `m` and `two` at the immediate `2` (`scc --blocks`'s
`wc_rodata_env`), and its immediate table (`hello1Imms`) has `m` and `two`
at `2` at the term that remains there (here any term `T`). -/

/-- The symbolic environment at `sp0`. -/
def rodataS : SEnv :=
  [("m", .intS (.lit 2), [.one (.imm 2)]), ("two", .intS (.lit 2), [.one (.imm 2)]), ("u", .unit, [])]

open Classical in
/-- The immediate table's shape (`renderImms`): one term `T`. -/
noncomputable def rodataImms (T : Expr) : Expr → String → Nat → Option Nat := fun e x k =>
  if e = T then
    match x, k with
    | "m", 0 => some 2
    | "two", 0 => some 2
    | _, _ => none
  else none

/-- `m`'s word is at the immediate `2`. -/
example : envMap (R := Nat) (fun _ => none) rodataS "m" 0 = some (.imm 2) := rfl

/-- The table agrees with every immediate of the environment, so `env_imm`
holds (`envMap_imm`). -/
example (T : Expr) : ∀ x k n, envMap (R := Nat) (fun _ => none) rodataS x k = some (.imm n) →
    rodataImms T T x k = some n := by
  refine envMap_imm ?_
  intro b hb k c h
  simp only [rodataS, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  all_goals
    match k with
    | 0 =>
      simp only [List.getElem?_cons_zero, List.getElem?_nil, Option.some.injEq, WordPl.one.injEq,
        Operand.imm.injEq, reduceCtorEq] at h
      try (subst h; simp [rodataImms])
    | k + 1 => simp at h

/-- Every word of `m` (`newBuf`'s argument) has a word place, so
`env_total` holds for it (`SRep.env_total`). -/
example : ∀ x ∈ ["m"], ∃ t pls, lookupS rodataS x = some (t, pls) ∧
    ∀ pl ∈ pls, (wordPlace (R := Nat) (fun _ => none) pl).isSome := by
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨_, _, rfl, by simp [wordPlace]⟩

end Spike.Lib.Form
