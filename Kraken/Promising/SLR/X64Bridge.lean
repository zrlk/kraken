/-
The x64 bridge for SLR program proofs: the event tree of the
instruction at a thread's pc, as an equation, so that an instruction rule of
the SLR-adapted model (over `EvTree.EraseWP`/`EvTree.EraseWPR`) can be applied
to it. The x64 twin of `SLR/AArch64Bridge.lean` (which cannot be imported
next to the x64 syntax: the two ISAs' syntax modules clash).

## Contents

- (`SLR/TreeMap.lean`, ISA-generic: `EvTree.eraseWP_map`,
  `EvTree.eraseWPR_map`, the WP of the adapter's mapped tree.)
- `X64.exec_eq_of_codeAt`: at a thread state whose code is `e` (validly laid
  out), with no declarations and away from its end address, `isa.exec` is the
  adapter's tree (`toEv {}`) of the cell `codeAt` finds at the pc, run with
  fall-through and jump continuations that stop (`.done`) at the next
  machine state. The same reduction as the invariant environment's `exec_allInv_of_instrStepEnv`
  (`InvLinkX64.lean`) and `exec_of_instrStepEnv` (`EnvLinkTermX64.lean`), as
  an equation.
-/
import Kraken.Promising.SLR.TreeMap
import Kraken.Promising.InvLinkX64

open Kraken

namespace Kraken.Promising.X64

-- TODO(F2): generalise `hds : st.decls = {}` to declarations under which every
-- access of the instruction resolves as under `{}` (e.g. `st.decls.resolve a n =
-- .ok ⟨a, n⟩` for the instruction's shared accesses), via a lemma
-- `toEv D t = toEv {} t` for such trees. With `Frame.decls` weakened to
-- "`decls.resolve a 4 = .ok ⟨a, 4⟩` for `a ∈ {l, c}`", the runner's configuration
-- with sized `.kl` declarations is covered (review_statements.md, F2).
/-- **The tree of one instruction.** -/
theorem exec_eq_of_codeAt {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State}
    (he : st.exe = e) (hds : st.decls = {}) (hne : (st.st.2 == st.endPc) = false) {d : Directive} {sz : Nat}
    {rest : List (Directive × Nat)} (hcode : e.codeAt st.st.2 = (d, sz) :: rest) :
    isa.exec st = some ((toEv {} (@Directive.interp (_root_.Executable.labels e) d st.st.1
      (.mk st.st.2 (st.st.2 + .ofNat sz)) (fun s' => .done (s', st.st.2 + .ofNat sz))
      (fun pc s' => .done (s', pc)))).map fun s => { st with st := s }) := by
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  obtain ⟨exe, endPc, ⟨s, pc⟩, showPc, decls⟩ := st
  simp only at he hds hcode hat hne ⊢
  subst he hds
  have hdir : ({ exe, endPc, st := (s, pc), showPc, decls := {} } : State).directive = some d := by
    unfold State.directive
    simp only
    rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) = Kraken.Executable.codeAt exe pc from by
      unfold Kraken.Executable.codeAt
      congr 1, hcode]
    rfl
  simp only [isa, exec, hdir, Option.isNone_some, Bool.or_false, hne, Bool.false_eq_true, ↓reduceIte]
  congr 2
  unfold Executable.step
  letI := Executable.labels exe
  simp only
  rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
  simp only [Directives.interp]

end Kraken.Promising.X64
