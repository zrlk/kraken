/-
**An allocation's returned base's store** (x86-64): `AllocW2At`'s last
field alone, the block storing the allocator's result into the `let`'s slot
inside `W₀` at every placement extending the call's. The landings' segment
(`landStk_seg`, `Spike/Lib/LowerX64/H1Of2.lean`) reads only this field at
every reachable placement, where `AllocW2At`'s size field `hsz` need not
hold (a placed label's size is not tied to a call).

- `AllocStoreAt`: at every allocation of a body (`AllocW2At`'s data), the
  store block at its argument block, slot and `callq`;
- `AllocW2At.store`: `AllocW2At` gives it.
-/
import Spike.Lib.LowerX64.NewBufC2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Emit.X64 (Item i64 rel)
open Scc.Lower.InvX64
open Spike.Lib.LowerNode
open Scc.Lower.Inv (regName atomV)
open Spike.Lib.LowerShape (unitsOf)
open Spike.Lib.X64.Flow.NewBuf (nbJc)

/-- **Every allocation's returned base's store** (`AllocW2At`'s data, its
`AllocW2`'s last field): at each `let x = newBuf cn τ in e` at `pc` with
the ghost `c0` in `G0`, the term in `T`, `env` fresh at `n`, the count the
immediate `kv`, the header `h` and the resumption facts (`PtC2`), at the
argument block `lw` (sizes `zs`), `x%n`'s slot `off`, the `callq` of `zc`
bytes and the store of `z` bytes after it, the store block inside `W₀` at
every placement `lbl'`, `lsize'` extending `lbl`, `lsize`, from the call's
landing invariant `nbJS`. -/
def AllocStoreAt (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (lcx : Scc.Lower.Ctx) (fr : Scc.Emit.X64.Frame) (Cd : Int64 → List (Directive × Nat) → Prop)
    (Bl : Int64 → Nat → Label → Nat → Prop)
    (W₀ : (WeakMem.AllocLabel → Option Nat) → (WeakMem.AllocLabel → Nat) → Frag isa)
    (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (ms : MemSide isa) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop)
    (i : Expr → String → Nat → Option Nat) (T : Expr → Prop) (Lk : Expr × List (String × Scc.Lower.LitV) → Prop) :
    Prop :=
  ∀ (c0 : Ctl) (pc : Int64) (kk : Nat) (x : String) (cn : CoreTerm.At) (τ : Ty) (e : Expr) (env : Scc.Lower.Env)
    (n : Nat) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)) (tk : Ty) (kv : UInt64)
    (en em h : Nat), G0 c0 → T (.let_ x (.newBuf cn τ) e) → Fresh env n →
    atomV env cn = some (tk, [.imm kv]) → Spike.Lib.LowerShape.countsO lcx.obj τ = some (en, em) →
    Scc.Obj.header0 lcx.obj .array en em = some h →
    PtC2 lcx fr Cd Bl (_root_.Executable.labels exe).label i T Lk kk pc env n lits cs bufs
      (.let_ x (.newBuf cn τ) e) →
    ∀ (lw : List Item) (off : Int) (zs : List Nat) (zc z k : Nat),
      getOps fr ([Scc.Lower.imm h, .imm kv, unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv].zip
        Scc.Emit.X64.argRegs) = .ok lw → rsOf fr (regName x n) = some off →
      zs.length = (dirs lw).length →
      Cd pc ((dirs lw).zip zs) → Bl (pc + Int64.ofNat zs.sum) zc Scc.Lower.Names.alloc k →
      Cd (pc + Int64.ofNat zs.sum + Int64.ofNat zc) [(stDir off, z)] →
      ∀ (lbl' : WeakMem.AllocLabel → Option Nat) (lsize' : WeakMem.AllocLabel → Nat),
        (∀ l b, lbl l = some b → lbl' l = some b) → (∀ l, lsize l ≤ lsize' l) →
        BlkW (W₀ lbl' lsize') K exe endPc R F
          ⟨pc + Int64.ofNat zs.sum + Int64.ofNat zc, oB fr,
            nbJS ms (_root_.Executable.labels exe).label lbl' lsize' R fr.size tp
              (nbJc (_root_.Executable.labels exe).label [(i64 (.call (rel Scc.Lower.Names.alloc)), zc)]
                (pc + Int64.ofNat zs.sum) (oB fr)
                (nbJ1 p lbl lsize fr R fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs (Scc.Lower.imm h)
                  (.imm kv) (unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv)))⟩
          [(stDir off, z)]

/-- **`AllocW2At` gives the stores** (its `AllocW2`'s last field). -/
theorem AllocW2At.store {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {lcx : Scc.Lower.Ctx} {fr : Scc.Emit.X64.Frame} {Cd : Int64 → List (Directive × Nat) → Prop}
    {Bl : Int64 → Nat → Label → Nat → Prop}
    {W₀ : (WeakMem.AllocLabel → Option Nat) → (WeakMem.AllocLabel → Nat) → Frag isa}
    {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    (H : AllocW2At p lbl lsize lcx fr Cd Bl W₀ K exe endPc R F ms fp ra tp G0 i T Lk) :
    AllocStoreAt p lbl lsize lcx fr Cd Bl W₀ K exe endPc R F ms fp ra tp G0 i T Lk :=
  fun c0 pc kk x cn τ e env n lits cs bufs tk kv en em h hc0 hT hfr hat hco hhd hpc lw off zs zc z k hlw hoff hz
    hCd hBl hCd' =>
  (H c0 pc kk x cn τ e env n lits cs bufs tk kv en em h hc0 hT hfr hat hco hhd hpc lw off zs zc z k hlw hoff hz
    hCd hBl hCd').2.2.2.2.2.2.2

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.AllocW2At.store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.AllocW2At.store
