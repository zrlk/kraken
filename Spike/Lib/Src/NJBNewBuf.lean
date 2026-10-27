import Spike.Lib.Src.EnvBGhost
import Spike.Lib.Src.NJBXchg2
import Spike.Lib.LowerShapeC2

/-!
**The node invariant past a buffer allocation** (ISA-neutral). `let x =
newBuf cn τ` is not a local step: the allocator picks a label `l` and the
source binds `x` to `l`'s locative (the control `allocCtl` of either ISA's
allocator nodes, written out here). The node after it binds `x` at the
lowering's type `newBufTy τ` (the source's up to the buffers' literal
lengths, `eraseLen_newBuf`), placed as the locative of the register `d` the
lowering stores the allocator's result into and offset `0`
(`group_newBufTy`), at the walk's layout `.loc` (`opLit_newBuf`).

`NJB`'s labels, memory and bound are a ghost: the new buffer's are
`EnvB.newBufG`'s (`L ∨ (· = l)`, `ghostMem`, `max B (l + 1)`), at the same
sizes `lsize`, which hold the count at `l` (`hkz`).

- `group_newBufTy`, `opLit_newBuf`: the placements and layout of the new
  binding;
- `NodeJE.newBuf2`: the node part;
- `NJB.newBuf2`: from the node's parts at the allocation site `c1` to `NJB`
  at `e` with `x` bound to the new buffer in `d`.
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib
open Spike.Lib.Form (opdVal NodeJE SEnv WordsRep LocRep)
open Spike.Lib.LowerShape (newBufTy)
open Scc.Sem (ValRep)
open Scc.Lower (LitV csAfter bufsAfter elem2)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {rs : Scc.IR.Reg → Option Int}
  {lits : List (String × LitV)} {cs bufs : List (String × Nat)} {L : WeakMem.AllocLabel → Prop}
  {sm : WeakMem.Memory} {lsize : WeakMem.AllocLabel → Nat} {B : Nat}

/-- **A new buffer's words `[d, 0]` are one locative.** -/
theorem group_newBufTy (τ : Ty) (d : Scc.IR.Reg) :
    Spike.Lib.Form.group (newBufTy τ) [.reg d, Scc.Lower.imm 0] = some [.loc (.reg d) (Scc.Lower.imm 0)] := rfl

/-- **A new buffer's layout is a locative.** -/
theorem opLit_newBuf (pp : Prog) (lits : List (String × LitV)) (cn : At) (τ : Ty) :
    Scc.Lower.opLit pp lits (.newBuf cn τ) = .loc := rfl

/-- **`let x = newBuf cn τ`, the node part**: `NodeJE` at the allocation
site `c1`, the new buffer's locative at `l` represented by `r` (`hr`),
which the slot `k` of the register `d` takes (`upd sl k r`, no other
binding's operand at `k`, `hfr`). Then `NodeJE` at `e` with `x` bound to
`l`'s locative, at `newBufTy τ` placed as `d`'s locative. -/
theorem NodeJE.newBuf2 {x : String} {cn : At} {τ : Ty} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c1 : Ctl}
    (hj : NodeJE lbl rs (.let_ x (.newBuf cn τ) e) s sl c1) (he2 : elem2 τ = true) (kk : Nat)
    (l : WeakMem.AllocLabel) (ini : Nat) {d : Scc.IR.Reg} {k : Int} (hd : rs d = some k)
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r k', o = .reg r → rs r = some k' → k' ≠ k)
    {r : BitVec 64} (hr : ValRep lbl (.loc ⟨l, 0⟩ 0) r.toNat) :
    NodeJE lbl rs e ((x, newBufTy τ, [.loc (.reg d) (Scc.Lower.imm 0)]) :: s) (upd sl k r)
      ⟨e, (x, .refine (.loc .own (.array (.lit kk) (TermRun.close [] τ))) (.ini (.lit ini)),
        [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: c1.env, none⟩ := by
  have hwr : WordsRep lbl (opdVal rs (upd sl k r)) [TermRun.cst (.loc ⟨l, 0⟩ 0)]
      [.loc (.reg d) (Scc.Lower.imm 0)] := by
    obtain ⟨-, v, hv, hrv⟩ := hr
    simp only [Scc.Sem.wordAddr, Option.map_eq_some_iff] at hv
    obtain ⟨b, hb, rfl⟩ := hv
    refine ⟨⟨r.toNat, 0, ?_, ?_, ?_⟩, trivial⟩
    · simp [opdVal, hd, upd_apply]
    · simp [opdVal, Scc.Lower.imm]
    · refine ⟨rfl, ?_, rfl⟩
      rw [hb, hrv]; simp
  have hsl : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, opdVal rs (upd sl k r) o = opdVal rs sl o :=
    fun q hq pl hpl o ho => Spike.Lib.Form.opdVal_upd fun r' k' hor hr' => by
      simp [upd_apply, hfr q hq pl hpl o ho r' k' hor hr']
  exact ⟨rfl, rfl, (hj.2.2.congr hsl).bind x (eraseLen_newBuf he2 [] kk ini) hwr⟩

/-- **`let x = newBuf cn τ`**: the node's parts at the allocation site `c1`
(`NodeJE`, `EnvLit`, `EnvB`, `MemB`, `EnvSmall`), an `elem2` element, the
count `kk` (`cn`'s number, `hev`, `hk`) held by the sizes at the new label
`l` (`hkz`), the new buffer's locative represented by `r` (`hr`), which the
slot `k` of the register `d` takes (`upd sl k r`, `hfr`). Then `NJB` at `e`
with `x` bound to the new buffer (the source's control past its allocation
at `l`, `ini` of it initialised), the walk's next state (`opLit`,
`csAfter`, `bufsAfter`), at `EnvB.newBufG`'s ghost labels, memory and
bound. -/
theorem NJB.newBuf2 (pp : Prog) {x : String} {cn : At} {τ : Ty} {e : Expr} {s : SEnv} {sl : Int → BitVec 64}
    {c1 : Ctl} {ta : Ty} {ws : List TermRun.Word} {kk : Nat}
    (hj : NodeJE lbl rs (.let_ x (.newBuf cn τ) e) s sl c1) (hn : EnvLit lits c1.env)
    (hb : EnvB lits cs bufs L sm lsize c1.env) (hm : MemB L sm B) (hS : EnvSmall c1.env)
    (he2 : elem2 τ = true) (hev : TermRun.evalAt c1.env cn = some (ta, ws)) (hk : TermRun.numOf ws = some kk)
    (l : WeakMem.AllocLabel) (ini : Nat) (hkz : kk ≤ lsize l)
    {d : Scc.IR.Reg} {k : Int} (hd : rs d = some k)
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r k', o = .reg r → rs r = some k' → k' ≠ k)
    {r : BitVec 64} (hr : ValRep lbl (.loc ⟨l, 0⟩ 0) r.toNat) :
    NJB p lbl rs ((x, Scc.Lower.opLit pp lits (.newBuf cn τ)) :: lits) (csAfter x cs (.newBuf cn τ))
      (bufsAfter x cs bufs (.newBuf cn τ)) (fun l' => L l' ∨ l' = l) (ghostMem L sm l kk) lsize (max B (l + 1)) e
      ((x, newBufTy τ, [.loc (.reg d) (Scc.Lower.imm 0)]) :: s) (upd sl k r)
      ⟨e, (x, .refine (.loc .own (.array (.lit kk) (TermRun.close [] τ))) (.ini (.lit ini)),
        [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: c1.env, none⟩ := by
  obtain ⟨hb', hm'⟩ := hb.newBufG (σs := []) hm hev hk he2 l ini (fun _ _ => Nat.le_refl _) hkz
  have hnl : NumL LitV.loc [TermRun.cst (.loc ⟨l, 0⟩ 0)] := by
    intro i w _ hmk
    have h0 : litMask LitV.loc = [false] := rfl
    rw [h0] at hmk
    rcases i with _ | i <;> simp at hmk
  have hws : WordsSmall [TermRun.cst (.loc ⟨l, 0⟩ 0)] := by
    intro w hw m hm0
    simp only [List.mem_singleton] at hw
    subst hw
    simp [TermRun.cst, Promises.TVal.mk0] at hm0
  exact ⟨_, .refl _, NodeJE.newBuf2 hj he2 kk l ini hd hfr hr,
    hn.cons (by rw [opLit_newBuf]; simp [Compat]) hnl, hb', hm',
    EnvSmall.cons hS hws⟩

/-! ## Tests -/

/-- info: 'Spike.Lib.LowerNode.NJB.newBuf2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NJB.newBuf2

end Spike.Lib.LowerNode
