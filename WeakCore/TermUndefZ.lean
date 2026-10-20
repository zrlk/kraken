import WeakCore.TermCut

/-!
# TermUndefZ: the `SysInvN` clause `undefAt`

`UndefAtG Eg mem`: every protocol-word unit of every cell of `Eg` has an `undef` allocation
placeholder in `mem`.  The per-step fact for freshly allocated cells is `TermStep.UndefNew`
(from `EFoot`, `TermStep.UndefNew_of_EFootM`), with the zeroability lemmas (`zero_unfold1`,
`atOff_word_nz`, `alloc_undef`, `allocBuf_undef`, `newBuf_z_none`) in `TermStep`.
-/

namespace TermUndefZ
open CoreLang CoreTerm TermRun TermClose TermSound TermStep

/-- The `SysInvN` clause `undefAt`: every protocol-word unit of every cell of `Eg` has an `undef`
message. -/
def UndefAtG (Eg : TermCut.GEnv) (mem : WeakMem.Memory) : Prop :=
  ∀ (l : WeakMem.AllocLabel) (c : Cell), Eg.sto l = some c →
    ∀ (o n : Nat) (P : Proto), AtOff c.ty o (.word (.lit n) P) → P.ghost = false →
      ∃ (t : Nat) (m : WeakMem.Msg), mem[t]? = some m ∧ m.loc = ⟨l, o⟩ ∧ m.val = .undef

end TermUndefZ
