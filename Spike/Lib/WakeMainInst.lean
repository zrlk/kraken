/-
**wake.w on AArch64: main's instance facts past the clone**: the instance-level fields of `WakeSpawnR.MainWS`
(`A64WakeMainClosedWS.main_closed_ws`'s hypotheses) that follow from the
placed layout `L := RuntimeLayout.ofPlaceW hp i` and the record's
`GhOK`, each its own lemma:

- `hwide_I` (`hwide`): every state on `L.exe` with no declarations is
  `WideX`, from `ExeWide L.exe` (`WideSt` is `DeclsWide decls ∧ ExeWide exe`,
  `declsWide_empty`);
- `htop_I` (`htop`): a range in `L.Λ`'s stack pool (the child's `r1Of`, by
  `ClonePre`'s `Owned`) ends in the address space (`PlaceW.wf_of_placeW`);
- `htp4_I` (`htp4`): main's permit word `tp + 16` 4-aligned, `tp` main's
  TCB `pinA + 0 + 8` (`WakeChildSt.childSt_al`);
- `hmA_I` (`hmA`): the flag's word mapped in `K0` for reading and writing,
  `A` the address `GhOK`'s `cS` represents (its target word `cT` shared,
  `WakeLabMapped.mapped_K0_of_shared`);
- `hmP_I` (`hmP`) and `hmE_I` (`hmE`): `LabMapped` at main's tail call
  `mTail` and at the controls past the wait loop's load (term `wlIf`), both
  with no `LabPtr` (`WakeLabMapped.labMapped_of_noPtr`).

The premises are the instance's (`hp`, `ExeWide`, `GhOK`, the record's
`Owned` range, main's TCB) or the fields' own shapes.
-/
import Spike.Lib.WakeSpawnR
import Spike.Lib.WakeLabMapped
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeMainInst

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (ValRep Range)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.WakeInst (Gh)
open Spike.Lib.WakeInstFields (GhOK)
open Spike.Lib.WakeMappedRow (LabPtr LabMapped)
open Spike.Lib.A64Consumer (K0)
open Spike.Lib.A64.WideKeep (WideX)
open Spike.Lib.WakeM0 (mTail wlIf)

/-! ## Controls with no label access -/

/-- **No `LabPtr` at a control whose term is no `let`** (a load, a store
and an exchange are `let`s). -/
theorem noPtr_of_term {c : Ctl} (h : ∀ x a e, c.term ≠ .let_ x a e) (sa : WeakMem.Address) : ¬ LabPtr c sa := by
  rintro (⟨x, a, e, -, -, (ht | ⟨b, ht⟩), -, -⟩ | ⟨x, u, v, e, -, (⟨a, -, -, -, ht, -⟩ |
      ⟨b, j, -, -, -, -, -, -, -, ht, -⟩)⟩) <;> exact h _ _ _ ht

/-- **`hmP`**: `LabMapped` at main's control at the tail call `mTail`. -/
theorem hmP_I {lbl : WeakMem.AllocLabel → Option Nat} {Λ : Scc.Sem.Layout} {cP : Ctl} (htP : cP.term = mTail) :
    LabMapped lbl (K0 Λ) cP :=
  Spike.Lib.WakeLabMapped.labMapped_of_noPtr (noPtr_of_term (by intro x a e h; rw [htP] at h; cases h))

/-- **`hmE`**: `LabMapped` at every control past the wait loop's load (its
term `wlIf`). -/
theorem hmE_I {lbl : WeakMem.AllocLabel → Option Nat} {Λ : Scc.Sem.Layout} {c0 : Ctl} {x : String} {ty : Ty}
    {Rd : TermRun.Word → Prop} :
    ∀ c, Spike.Lib.A64.WaitLoop.Past c0 x wlIf ty Rd c → LabMapped lbl (K0 Λ) c := by
  rintro c ⟨w', -, rfl⟩
  exact Spike.Lib.WakeLabMapped.labMapped_of_noPtr (noPtr_of_term (by intro x a e h; cases h))

/-! ## The flag's word -/

/-- **`hmA`**: the address `A` that `GhOK`'s flag word `cS` represents
under the record's placement is mapped in `K0`, for reading and writing. -/
theorem hmA_I {Λ : Scc.Sem.Layout} {g : Gh} (hg : GhOK Λ g) {A : BitVec 64}
    (hv : ValRep g.lbl (.loc g.cS 0) A.toNat) : ∀ wr, Scc.Sem.Kernel.mapped (K0 Λ) wr ⟨A, 8⟩ = true := by
  obtain ⟨-, -, -, ⟨b, hl, -, hT⟩, hsh⟩ := hg
  intro wr
  obtain ⟨-, x, hx, hAx⟩ := hv
  rw [show Scc.Sem.wordAddr g.lbl g.cS = some (b + 8 * g.cS.offset) by simp [Scc.Sem.wordAddr, hl]] at hx
  cases hx
  have hA' : A = BitVec.ofNat 64 (b + 8 * g.cS.offset) := by
    apply BitVec.eq_of_toNat_eq
    rw [hAx, BitVec.toNat_ofNat, Nat.add_zero, Nat.mod_eq_of_lt (by have := A.isLt; omega)]
  have := Spike.Lib.WakeLabMapped.mapped_K0_of_shared hsh wr
  rw [hT] at this
  rw [hA']
  exact this

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-! ## The layout's facts -/

/-- **`hwide`**: every state on the layout's executable with no
declarations is `WideX`. -/
theorem hwide_I (hw : Scc.Cert.WideA64.ExeWide (RuntimeLayout.ofPlaceW hp i).exe) :
    ∀ s : State, s.exe = (RuntimeLayout.ofPlaceW hp i).exe → s.decls = {} →
      WideX (RuntimeLayout.ofPlaceW hp i).exe s :=
  fun _ he hd => ⟨⟨hd ▸ Scc.Cert.WideA64.declsWide_empty, he ▸ hw⟩, he⟩

/-- **`htop`**: a range in the layout's stack pool ends in the address
space. -/
theorem htop_I {r : Range} (hsub : r.Sub (RuntimeLayout.ofPlaceW hp i).Λ.stackPool) : r.lo + r.size ≤ 2 ^ 64 :=
  Nat.le_trans hsub.2
    ((PlaceW.wf_of_placeW hp).inSpace _ (by simp only [Scc.Sem.Layout.regions, List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))).2

/-- **`htp4`**: main's permit word `tp + 16` is 4-aligned, `tp` main's TCB
`pinA + 0 + 8`. -/
theorem htp4_I {tp : BitVec 64} (htp : tp = (RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64) :
    (tp + 16#64).toNat % 4 = 0 := by
  subst htp
  rw [BitVec.add_zero, BitVec.add_assoc]
  exact Spike.Lib.WakeChildSt.childSt_al hp i

end Inst

/-- info: 'Spike.Lib.WakeMainInst.hmP_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hmP_I

/-- info: 'Spike.Lib.WakeMainInst.hmE_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hmE_I

/-- info: 'Spike.Lib.WakeMainInst.hmA_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hmA_I

/-- info: 'Spike.Lib.WakeMainInst.hwide_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hwide_I

/-- info: 'Spike.Lib.WakeMainInst.htop_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms htop_I

/-- info: 'Spike.Lib.WakeMainInst.htp4_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms htp4_I

end Spike.Lib.WakeMainInst
