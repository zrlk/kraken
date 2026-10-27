/-
**`hello1`'s per-allocation premises of `allocW2At_of`** (AArch64; the twin
of `Spike/Test/X64Hello1AllocPt.lean`): at the setup frame's allocation of
`rodata` (`let b = newBuf m LanesU8`, the only allocation of `hello1o`'s
blocks), the premises `AllocPtW` (`Spike/Lib/LowerA64/AllocW2AtOf.lean`)
decided at `hello1o`, for `Spike/Test/A64Hello1HAWNone.lean`.

- `hello1_rodata_compiled2A`: the first compiled block is `rodata`'s body;
- `hello1_rodata_nbTailA`: every allocation on the walk of a compiled block
  of `hello1o` is `rodata`'s `eB` (decided over `tailsL`);
- `hello1_rodata_packLeafA`: the count's literal layout a leaf (`hleaf`);
- `hello1_rodata_count2A`: the count's immediate `2`;
- `hello1_hnrA`, `hello1_haccA`: the continuation no `main` return at the
  setup frame, the element's accesses;
- `hello1_rodata_hdrA`: the allocation's header has no trace words (`mOf = 0`);
- `hello1_rodata_huA`: the units' operand is the arena's units at `msOfAX`.
-/
import Spike.Test.A64Hello1H1Of
import Spike.Test.Hello1MainFacts
import Spike.Lib.LowerA64.ArCallMs
import Spike.Lib.LowerA64.FnSpecLaneBuf2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Spike.Lib.LowerNode (compiled2 TailAt2)
open Spike.Lib.Hello1RodataSrc (rdBody eM eB eW0 eO0 eW1 eO1 eN eSm eSl0 ePack eRet τ8)

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

/-- `hello1o`'s first compiled block is `rodata`, of body `rdBody`. -/
theorem hello1_rodata_compiled2A : ((compiled2 P1A)[0]?).map (·.body) = some rdBody := rfl

/-- **`hello1o`'s allocations are `rodata`'s `eB`**: at every compiled block
in range, an allocation on the walk (`TailAt2`) binds `b` to a buffer of
`m` `LanesU8` elements and continues at `eW0` (`rodata`'s points listed;
`main`'s, at the second block, allocation-free; no third block). -/
theorem hello1_rodata_nbTailA {j : Nat} {d : Decl} (hd : (compiled2 P1A)[j]? = some d) {x : String} {cn : At}
    {τ : Ty} {e : Expr} (ht : TailAt2 P1A j (.let_ x (.newBuf cn τ) e)) :
    x = "b" ∧ cn = .var "m" ∧ τ = τ8 ∧ e = eW0 := by
  have hm := tailOf_mem_tailsL (ht d hd)
  match j, hd with
  | 0, hd =>
    have hb : d.body = rdBody := by
      have := hello1_rodata_compiled2A; rw [hd] at this; exact Option.some.inj this
    rw [hb] at hm
    simp only [tailsL, rdBody, eM, eB, eW0, eO0, eW1, eO1, eN, eSm, eSl0, ePack, eRet, List.mem_cons,
      List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h <;> (try simp_all) <;> rfl
  | 1, hd =>
    have hc : (tailsL d.body).all (fun t => match t with
        | .let_ _ (.newBuf _ _) _ => false
        | _ => true) = true := by
      have := Spike.Test.Hello1MainSrc.hello1_main_compiled2; rw [hd] at this
      cases this; decide
    simpa using List.all_eq_true.mp hc _ hm
  | k + 2, hd =>
    have h2 : (compiled2 P1A)[k + 2]? = none := by
      rw [List.getElem?_eq_none_iff]
      have hl : (compiled2 P1A).length = 2 := rfl
      omega
    rw [h2] at hd; cases hd

/-- **The count's literal words are one word** (`AllocPtW.hleaf` at
`rodata`'s allocation): at the literal walk from `eB` with the layouts
`lits`, the slice's `pack` at `ePack` packs `sl0`, laid out as
`((b, m), n)`, at the slice's type (`LitPt`'s `Compat`), so `m`'s layout,
unchanged since `eB` (no later binding of `m`), is a leaf. -/
theorem hello1_rodata_packLeafA {lits : List (String × Scc.Lower.LitV)}
    (hL : ∀ q ∈ Scc.Lower.litWalk2 P1A lits eB, Spike.Lib.LowerNode.LitPt q) :
    ∃ o, Scc.Lower.litAt lits (.var "m") = .leaf o := by
  have hlen : 8 < (Scc.Lower.litWalk2 P1A lits eB).length := by
    simp [Scc.Lower.litWalk2, eB, eW0, eO0, eW1, eO1, eN, eSm, eSl0, ePack, eRet]
  have hP := (hL _ (List.getElem_mem hlen)).2.1 "sl" (.var "sl0") "m" (.iex Spike.Lib.Hello1Src.sliceTy) eRet rfl
  revert hP
  simp only [Scc.Lower.litWalk2, eB, eW0, eO0, eW1, eO1, eN, eSm, eSl0, ePack, List.getElem_cons_succ,
    List.getElem_cons_zero, Scc.Lower.litAt, Scc.Lower.opLit, List.lookup, Spike.Lib.Hello1Src.sliceTy]
  cases hm : lits.lookup "m" with
  | none => intro _; exact ⟨none, rfl⟩
  | some v =>
    cases v with
    | leaf o => intro _; exact ⟨o, rfl⟩
    | _ => simp (config := { decide := true }) [Spike.Lib.LowerNode.Compat, Scc.Obj.coupledPair]

/-- **The count is the immediate `2`** at `rodata`'s allocation: `m`'s word
an immediate `kv` in the lowering's environment (`atomV`), grouped
(`GrpL`, one word: `group_one`), so placed as `.one (.imm kv)` and `kv` the
theorem's table's entry at `eB` (`ImmIn`), `imms2Of hello1o`'s there
(`imms2Me_tailAt2`), `2`. -/
theorem hello1_rodata_count2A {Λ : Scc.Sem.Layout} {j : Nat} {d : Decl} (hd : (compiled2 P1A)[j]? = some d)
    (ht : TailAt2 P1A j eB) {env : Scc.Lower.Env} (hg : Spike.Lib.LowerNode.GrpL env)
    (hi : Spike.Lib.LowerNode.ImmIn (Spike.Lib.LowerNode.imms2Me Λ P1A) (Spike.Lib.LowerNode.ofEnv2 env) eB)
    {tk : Ty} {kv : UInt64} (hat : Scc.Lower.Inv.atomV env (.var "m") = some (tk, [.imm kv])) :
    kv.toNat = 2 := by
  obtain ⟨b, hb, hv⟩ := Spike.Lib.LowerShape.atomV_var hat
  obtain ⟨rfl, hw⟩ := Prod.mk.inj hv.symm
  obtain ⟨pls, hp⟩ := Option.isSome_iff_exists.mp (hg _ _ hb)
  rw [hw] at hp
  have hpl := Spike.Lib.LowerNode.group_one hp
  have hl : Spike.Lib.Form.lookupS (Spike.Lib.LowerNode.ofEnv2 env) "m" = some (b.2.1, [.one (.imm kv)]) := by
    rw [Spike.Lib.LowerNode.lookupS_ofEnv2, hb]; simp [hw, hp, hpl]
  have h1 := hi "m" 0 kv (by rw [hl]; rfl)
  rw [Spike.Lib.LowerNode.imms2Me_tailAt2 Spike.Lib.LowerNode.hello1o_accepted2 hd ht] at h1
  have h2 : Scc.Lower.imms2Of P1A eB "m" 0 = some 2 := by decide
  rw [h2] at h1
  exact (Option.some.inj h1).symm

/-- **No `main` return past the setup frame's allocation** (`AllocPtW.hnr`):
the frames `[fr]` are not empty. -/
theorem hello1_hnrA {fr : TermRun.Frame} {e : Expr} : [fr] = [] → ∀ a, e ≠ .ret a := nofun

/-- **`LanesU8`'s accesses** (`AllocPtW.hacc` at `rodata`'s element type). -/
theorem hello1_haccA : ∃ us, TermRun.accs (TermRun.close [] τ8) = some us := ⟨_, rfl⟩

/-- **`rodata`'s allocation's header has no trace words** (`callMsOK_arOf`'s
`hm`): `LanesU8`'s counts at the configuration's object layout are
`(1, 0)`, whose array header's trace count (`mOf`) is `0`. -/
theorem hello1_rodata_hdrA {en em h : Nat}
    (hco : Spike.Lib.LowerShape.countsO SccCertificate.config.layout.obj τ8 = some (en, em))
    (hhd : Scc.Obj.header0 SccCertificate.config.layout.obj .array en em = some h) :
    (Spike.Lib.A64.Alloc.mOf (BitVec.ofNat 64 h)).toNat = 0 := by
  have h10 : Spike.Lib.LowerShape.countsO SccCertificate.config.layout.obj τ8 = some (1, 0) := by decide
  rw [h10] at hco
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hco).symm
  have hv : Scc.Obj.header0 SccCertificate.config.layout.obj .array 1 0 = some 257 := by decide
  rw [hv] at hhd
  cases Option.some.inj hhd
  decide

/-- **The units' operand at `rodata`'s allocation** (`AllocPtW.hu`): at the
count `2` (`hk`) and `LanesU8`'s counts (`hco`, `(1, 0)`: one word an
element), the operand `unitsOf 1 kv` is the immediate `3`, the arena's
units of `2` elements of `LanesU8` (`Arena.ofWords`: `2 · 1 + 1`) at the
rows' memory side at either abort phase, at any arena layout `Λ'`. -/
theorem hello1_rodata_huA {Λ Λ' : Scc.Sem.Layout} {μ : Scc.Sem.Marks} {p : Prog} {rd : TermRun.Word → Prop}
    {G : Kraken.Promising.Loc → Kraken.Promising.Val → Prop} {own : Spike.Lib.A64ConsumerS.OwnS}
    {I : Spike.Lib.A64ConsumerS.InvS}
    {ab : Option (Kraken.Promising.AArch64.State → Prop)} {lbl : Spike.Lib.A64Consumer.Lbl}
    {lsize : Spike.Lib.A64Consumer.Lsize} {fs : List TermRun.Frame} (cx : Scc.Emit.A64.FnCtx) {en em : Nat}
    {kv : UInt64} (hk : kv.toNat = 2)
    (hco : Spike.Lib.LowerShape.countsO SccCertificate.config.layout.obj τ8 = some (en, em)) :
    ∀ sl, Spike.Lib.Form.opdVal (Spike.Lib.LowerA64.rsOf cx) sl
        (Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ8).getD (en + em)) kv) =
      some ((Spike.Lib.A64ConsumerA.msOfAX Λ μ p rd G own (Spike.Lib.A64.Rt.arOf Λ') I ab lbl lsize fs).units
        kv.toNat τ8) := by
  intro sl
  have h10 : Spike.Lib.LowerShape.countsO SccCertificate.config.layout.obj τ8 = some (1, 0) := by decide
  rw [h10] at hco
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hco).symm
  rw [hk]
  have hw : (Scc.Frontend.words τ8).getD (1 + 0) = 1 := by decide
  rw [hw]
  have hu : (Spike.Lib.A64.Rt.arOf Λ').units 2 τ8 = 3 := by
    simp only [Spike.Lib.A64.Rt.arOf, Spike.Lib.Arena.ofWords]; decide
  cases ab <;>
  · show Spike.Lib.Form.opdVal _ sl (Spike.Lib.LowerShape.unitsOf 1 kv) = some ((Spike.Lib.A64.Rt.arOf Λ').units 2 τ8)
    rw [hu]
    simp [Spike.Lib.LowerShape.unitsOf, Spike.Lib.Form.opdVal, Scc.Lower.imm, hk]

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hello1_rodata_compiled2A' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_rodata_compiled2A

/-- info: 'Spike.Lib.LowerA64.hello1_rodata_nbTailA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_rodata_nbTailA

/-- info: 'Spike.Lib.LowerA64.hello1_rodata_packLeafA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_rodata_packLeafA

/-- info: 'Spike.Lib.LowerA64.hello1_rodata_count2A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_rodata_count2A

/-- info: 'Spike.Lib.LowerA64.hello1_hnrA' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_hnrA

/-- info: 'Spike.Lib.LowerA64.hello1_haccA' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_haccA

/-- info: 'Spike.Lib.LowerA64.hello1_rodata_hdrA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_rodata_hdrA

/-- info: 'Spike.Lib.LowerA64.hello1_rodata_huA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_rodata_huA
