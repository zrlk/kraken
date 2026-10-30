/-
**The source's label words are mapped** (`WakeMappedRow.LabMapped`, the
per-node premise of `hM_of`/`hW_of`): at a control accessing no label word
through an untagged locative (`LabPtr`) it holds vacuously; at one whose
only such access is to the flag `cS`, whose target word `cT` is shared
(`GhOK`'s last conjunct), it holds in `K0`.

- `labOp`: the operations `LabPtr` reads (load, store, exchange);
- `noPtr_of_term`: a control whose term binds no `labOp` has no `LabPtr`;
- `labMapped_of_noPtr`: `LabMapped` with no `LabPtr`;
- `ptr_of_store`, `ptr_of_load`: at a store (a load) through `a`, `a` one
  word `.loc sa 0`, every `LabPtr` is to `sa`;
- `mapped_K0_of_shared`: a shared location is mapped in `K0`;
- `labMapped_flag`: `LabMapped` in `K0` when every `LabPtr` is to `cS`,
  `cS`'s word under `lbl` being `cT`, shared; `labMapped_flagB` at
  `GhOK`'s shape (`cS` in the label placed at `b`).
-/
import Spike.Lib.WakeMappedRow

namespace Spike.Lib.WakeLabMapped

open CoreLang CoreTerm
open Kraken.Promising
open Scc.Sem (ValRep)
open Spike.Lib.WakeMappedRow (LabPtr LabMapped)
open Spike.Lib.A64Consumer (K0)

/-- **The operations `LabPtr` reads**: a load, a store, an exchange. -/
def labOp : Op → Bool
  | .load .. | .store .. | .xchg .. | .xchgAt .. => true
  | _ => false

/-- **No `LabPtr`** at a control whose term binds no `labOp`. -/
theorem noPtr_of_term {c : Ctl} (h : ∀ x op e, c.term = .let_ x op e → labOp op = false) :
    ∀ sa, ¬ LabPtr c sa := by
  rintro sa (⟨x, a, e, -, -, (ht | ⟨b, ht⟩), -⟩ | ⟨x, u, v, e, -, (⟨a, -, -, -, ht, -⟩ | ⟨b, i, -, -, -, -, -, -, -, ht, -⟩)⟩) <;>
    exact absurd (h _ _ _ ht) (by simp [labOp])

/-- **`LabMapped` with no `LabPtr`.** -/
theorem labMapped_of_noPtr {lbl : WeakMem.AllocLabel → Option Nat} {K : Scc.Sem.Kernel.KState} {c : Ctl}
    (h : ∀ sa, ¬ LabPtr c sa) : LabMapped lbl K c :=
  fun sa _ hp => (h sa hp).elim

/-- **At a store through `a`**, `a` one word `.loc sa 0`, every `LabPtr` is
to `sa`. -/
theorem ptr_of_store {c : Ctl} {x : String} {a b : At} {e : Expr} {ty : Ty} {w : TermRun.Word}
    {sa : WeakMem.Address} (ht : c.term = .let_ x (.store true a b none) e)
    (hev : TermRun.evalAt c.env a = some (ty, [w])) (hw : w.val = .loc sa 0) :
    ∀ sa', LabPtr c sa' → sa' = sa := by
  rintro sa' (⟨x', a', e', ty', w', (ht' | ⟨b', ht'⟩), hev', hw'⟩ | ⟨x', u, v, e', -, (⟨a', -, -, -, ht', -⟩ |
      ⟨b', i, -, -, -, -, -, -, -, ht', -⟩)⟩) <;> rw [ht] at ht' <;> simp at ht'
  obtain ⟨-, ⟨rfl, -⟩, -⟩ := ht'
  rw [hev] at hev'
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hev'
  obtain ⟨-, rfl⟩ := hev'
  rw [hw] at hw'
  cases hw'
  rfl

/-- **At a load through `a`**, `a` one word `.loc sa 0`, every `LabPtr` is
to `sa`. -/
theorem ptr_of_load {c : Ctl} {x : String} {a : At} {e : Expr} {ty : Ty} {w : TermRun.Word}
    {sa : WeakMem.Address} (ht : c.term = .let_ x (.load true a) e)
    (hev : TermRun.evalAt c.env a = some (ty, [w])) (hw : w.val = .loc sa 0) :
    ∀ sa', LabPtr c sa' → sa' = sa := by
  rintro sa' (⟨x', a', e', ty', w', (ht' | ⟨b', ht'⟩), hev', hw'⟩ | ⟨x', u, v, e', -, (⟨a', -, -, -, ht', -⟩ |
      ⟨b', i, -, -, -, -, -, -, -, ht', -⟩)⟩) <;> rw [ht] at ht' <;> simp at ht'
  obtain ⟨-, rfl, -⟩ := ht'
  rw [hev] at hev'
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hev'
  obtain ⟨-, rfl⟩ := hev'
  rw [hw] at hw'
  cases hw'
  rfl

/-- **A shared location is mapped in `K0`**, for reading and writing (the
shared regions, `data`, `heap`, `pinned`, are read-write in `K0`). -/
theorem mapped_K0_of_shared {Λ : Scc.Sem.Layout} {l : Loc} (h : Consumer1.LocIn Λ.shared l) (wr : Bool) :
    Scc.Sem.Kernel.mapped (K0 Λ) wr l = true := by
  unfold Scc.Sem.Kernel.mapped
  simp only [List.all_eq_true, List.any_eq_true, List.mem_range, decide_eq_true_eq]
  intro i hi
  have hb : i < Scc.Sem.Kernel.locBytes l := by unfold Scc.Sem.Kernel.locBytes; split <;> omega
  rcases h i hb with h | h | h
  · exact ⟨Λ.data, by simp [Scc.Sem.Kernel.mappedRegions, K0], h⟩
  · exact ⟨Λ.heap, by simp [Scc.Sem.Kernel.mappedRegions, K0], h⟩
  · exact ⟨Λ.pinned, by simp [Scc.Sem.Kernel.mappedRegions, K0], h⟩

/-- **`LabMapped` in `K0` at a control accessing only the flag**: every
`LabPtr` is to `cS` (`hc`), whose word under `lbl` is at `a` (`hA`), the
target word `cT = wordLoc a` (`hT`) shared (`hsh`). -/
theorem labMapped_flag {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {c : Ctl}
    {cS : WeakMem.Address} {cT : Loc} {a : Nat} (hc : ∀ sa, LabPtr c sa → sa = cS)
    (hA : Scc.Sem.wordAddr lbl cS = some a) (hT : cT = Scc.Sem.wordLoc a) (hsh : Consumer1.LocIn Λ.shared cT) :
    LabMapped lbl (K0 Λ) c := by
  intro sa A hp hv wr
  cases hc sa hp
  obtain ⟨-, x, hx, hAx⟩ := hv
  rw [hA] at hx
  cases hx
  have hA' : A = BitVec.ofNat 64 a := by
    apply BitVec.eq_of_toNat_eq
    rw [hAx, BitVec.toNat_ofNat, Nat.add_zero, Nat.mod_eq_of_lt (by have := A.isLt; omega)]
  have := mapped_K0_of_shared hsh wr
  rw [hT] at this
  rw [hA']
  exact this

/-- **`labMapped_flag` at `GhOK`'s shape**: `cS` a word of the label
placed at `b`, `cT` its target word, shared. -/
theorem labMapped_flagB {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {c : Ctl}
    {cS : WeakMem.Address} {cT : Loc} {b : Nat} (hc : ∀ sa, LabPtr c sa → sa = cS)
    (hl : lbl cS.label = some b) (hT : cT = Scc.Sem.wordLoc (b + 8 * cS.offset))
    (hsh : Consumer1.LocIn Λ.shared cT) : LabMapped lbl (K0 Λ) c :=
  labMapped_flag hc (by simp [Scc.Sem.wordAddr, hl]) hT hsh

/-- info: 'Spike.Lib.WakeLabMapped.labMapped_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms labMapped_flag

/-- info: 'Spike.Lib.WakeLabMapped.ptr_of_store' depends on axioms: [propext] -/
#guard_msgs in #print axioms ptr_of_store

/-- info: 'Spike.Lib.WakeLabMapped.noPtr_of_term' depends on axioms: [propext] -/
#guard_msgs in #print axioms noPtr_of_term

end Spike.Lib.WakeLabMapped
