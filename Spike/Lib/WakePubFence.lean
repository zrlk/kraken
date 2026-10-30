/-
**wake's publication at `wc_main`'s `dmb ishst` is a row** (non-vacuity of
`Arena.pub`; wake.w, AArch64): at the fence node past the box's store
(`WakeWc.bX`, the pair `h0`'s segment hands to `h1`'s, `A64WakeBox.Box`)
with the source at `boxTerm` (`let c = publish o in …`, `o` bound to the
box's owned locative, no hold), the target's `dmb ishst` is an `Out.fence`
row whose source run is the publication step (`FenceRun.pub`) under any
memory side admitting it, in particular wake's (`msOfA` at `WakeOD.arW`,
`arW_pub`). Under hello1's memory sides (`pub := False`) that fence has no
such row.

- `boxPub`: the publication step at `boxTerm` (`PubStep .st`), landing at
  `let p = pair c me in spawnTerm` with `c` the box's published locative.
- `wake_pub_fence`: the fence node's row is `Out.fence` with
  `FenceRun.pub`, the target at `pc + 4`.
- `wake_pub_fence_arW`: the same under wake's memory side.
-/
import Spike.Lib.A64WakeWcRes
import Spike.Lib.A64WakeBox
import Spike.Lib.WakeOD

namespace Spike.Lib.A64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Cert.Rt.A64 (Lays endOf)

/-- The source past the publication at `boxTerm`: `let p = pair c me in
spawnTerm`, `c` bound to the box's published locative. -/
def boxPubCtl (c : Ctl) (ty : Ty) (l : WeakMem.AllocLabel) : Ctl :=
  ⟨.let_ "p" (.pair (.var "c") (.var "me")) Spike.Lib.WakePreA.spawnTerm,
    ("c", .ptr .pub ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: c.env, none⟩

/-- **The publication step at `boxTerm`** (`PubStep .st`): `o` bound to the
box's owned locative, no hold. -/
theorem boxPub {c : Ctl} {ty : Ty} {l : WeakMem.AllocLabel} (ht : c.term = boxTerm) (hh : c.hold = none)
    (ho : TermRun.evalAt c.env (.var "o") = some (.ptr .own ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)])) :
    PubStep .st c (boxPubCtl c ty l) :=
  ⟨.inl rfl, hh, "c", .var "o", _, .ptr .own ty, .ptr .pub ty, _, .inl ⟨ht, rfl⟩, ho, rfl⟩

/-- **wake's fence row with the publication**: in a valid layout of
`wakeProg`, at the fence node past the box's store (`bX`) with the source at
`boxTerm`, under a memory side admitting the publication (`ms.pub`), the
target's `dmb ishst` is an `Out.fence` row whose source run is the
publication step (`FenceRun.pub`, no local run after it), the target at
`pc + 4`. -/
theorem wake_pub_fence {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {kp : Nat} (hp : Lays exe SccCode.wakeProg kp)
    (hend : endPc = endOf exe SccCode.wakeProg kp) {J0 : AS → Ctl → Prop} {l : WeakMem.AllocLabel} {A : Nat}
    {s : State} {c : Ctl} (hA : At exe endPc R F (bX ms (_root_.Executable.labels exe).label J0 l A) s c)
    {ty : Ty} (ht : c.term = boxTerm) (hh : c.hold = none)
    (ho : TermRun.evalAt c.env (.var "o") = some (.ptr .own ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)]))
    (hP : ms.pub) :
    Out p lbl ms (fun s' c' => s' = after s 4 s.st.1 ∧ c' = boxPubCtl c ty l) s c := by
  have hin := wake_wcResIn
  simp only [wcResIn, Bool.and_eq_true] at hin
  obtain ⟨⟨h4, -⟩, -⟩ := hin
  obtain ⟨he, hn, -, hpc, -⟩ := hA
  have hc : CellAt s (.instr ⟨.W64, .DMB .st⟩) 4 :=
    (code_of hp hend (pubF_eq ▸ h4) rfl s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp [bX])
  exact .fence .st _ _ (exec_dmb hc) (.pub hP (boxPub ht hh ho) (.refl _)) ⟨rfl, rfl⟩

/-- **wake's fence row with the publication, under wake's memory side**
(`msOfA` at `WakeOD.arW`, whose `pub` holds: `arW_pub`). -/
theorem wake_pub_fence_arW {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out}
    {Λ0 : Scc.Sem.Layout} (hpw : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : A64ConsumerS.OwnS} {I : A64ConsumerS.InvS} {lbl' : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {fs : List TermRun.Frame}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {kp : Nat} (hp : Lays exe SccCode.wakeProg kp)
    (hend : endPc = endOf exe SccCode.wakeProg kp) {J0 : AS → Ctl → Prop} {l : WeakMem.AllocLabel} {A : Nat}
    {s : State} {c : Ctl}
    (hA : At exe endPc R F (bX (A64ConsumerA.msOfA (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hpw i).Λ μ rd G own
      (WakeOD.arW hpw i) I lbl' lsize fs) (_root_.Executable.labels exe).label J0 l A) s c)
    {ty : Ty} (ht : c.term = boxTerm) (hh : c.hold = none)
    (ho : TermRun.evalAt c.env (.var "o") = some (.ptr .own ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)])) :
    Out p lbl (A64ConsumerA.msOfA (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hpw i).Λ μ rd G own (WakeOD.arW hpw i) I lbl' lsize fs)
      (fun s' c' => s' = after s 4 s.st.1 ∧ c' = boxPubCtl c ty l) s c :=
  wake_pub_fence hp hend hA ht hh ho (WakeOD.arW_pub hpw i)

end Spike.Lib.A64.Flow.WakeWc

/-- info: 'Spike.Lib.A64.Flow.WakeWc.boxPub' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.boxPub

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wake_pub_fence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wake_pub_fence

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wake_pub_fence_arW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wake_pub_fence_arW
