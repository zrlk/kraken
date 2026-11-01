/-
**The threads abort phase on AArch64, generic in the spawn's pcs** (hello
plan B4c-pre): `Spike/Lib/A64ThreadsAb.lean`'s `Ac` with the three things
that are wake.w's there made parameters, and hello.w's instance.

A spawn's lowering is, for `wc_main`'s local label prefix `pfx`,

```
pfx.sp6:   … n instructions …; svc #0       (pfx.sp6 + 4·n)
           cbz x0, pfx.child…                (pcRet)
pfx.cl:    str x0, [sp, #off]; ldr x9, [sp, #off]; movz x10, #0
           subs xzr, x9, x10; b.lt pfx.1_spawnfail5; b pfx.2_spawned6
pfx.1_spawnfail5:
           movz x0, #5; bl scc_rt_abort
```

wake.w's is `n = 13`, `cl = ".clone9"`, `off = 48` (frame 80); hello.w's
(`SccCode.helloProg`, `.L22_wc_main`) is `n = 25`, `cl = ".clone13"`,
`off = 112` (frame 144). The fail block, the dispatcher's and the threads
stub's pcs and the return address `raT` do not depend on them and are
wake's (`ThreadsAb.failPcs`, `dispTPcs`, `g5Pcs`, `stubPcs`, `raT`,
`WriteAb.dispEPcs`), as is `CloneRef`.

- `pcRet`, `pcSt`, `tailPcs`, `Ac`, `acPcs`: as wake's, at `n cl off`.
- `pc_of_ac`, `not_ac_of_pc`, `ac_ret`, `ac_fail`, `ac_g5`, `ac_stub`,
  `ac_x30`: as wake's.
- `ac_wake`: wake's `ThreadsAb.Ac` is the instance at `13 ".clone9" 48`.
- `AcH`, `acPcsH`, `pcRetH`, `tailPcsH`: hello.w's instance.

Deferred: wake's consumers of `ThreadsAb.Ac` by name, `A64StubTAC`'s
threads-stub section (`stubTW_threads…`, `ac_g5A`, `ac_stubA`) and
`A64ThreadsAcSt` (`blkAc`, `acPcsNE`, `ac_dispE_of`), are restated at `AcH`
with the child's and the stub's segments (B4c).
-/
import Spike.Lib.A64ThreadsAb

namespace Spike.Lib.A64.Hello.ThreadsAb

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.WriteAb (spLoad dispEPcs)
open Spike.Lib.A64.ThreadsAb (CloneRef failPcs dispTPcs g5Pcs stubPcs raT)

variable (lab : Label → Int64) (pfx : String) (n : Nat) (cl : String) (off : BitVec 64)

/-- The pc after the spawn's `clone` call (`pfx.sp6`'s instruction `n`):
`cbz x0, pfx.child…`. -/
abbrev pcRet : Int64 := lab (pfx ++ ".sp6") + Int64.ofNat (4 * n) + 4

/-- The store of the result: `pfx ++ cl`. -/
abbrev pcSt : Int64 := lab (pfx ++ cl)

/-- The tests of the stored result up to the `b.lt`. -/
def tailPcs : List Int64 :=
  [lab (pfx ++ cl) + 4, lab (pfx ++ cl) + 8, lab (pfx ++ cl) + 12, lab (pfx ++ cl) + 16]

/-- **The threads abort phase**, the stored result at `[sp + off]`. -/
def Ac (s : State) : Prop :=
  (s.st.2 = pcRet lab pfx n ∧ CloneRef s.st.1.regs.X0.toBitVec) ∨
  (s.st.2 = pcSt lab pfx cl ∧ CloneRef s.st.1.regs.X0.toBitVec) ∨
  (s.st.2 ∈ tailPcs lab pfx cl ∧ ∃ r, spLoad s off = some r ∧ CloneRef r) ∨
  s.st.2 ∈ failPcs lab pfx ∨
  (s.st.2 ∈ dispEPcs lab ∧ s.st.1.regs.X0 = 5 ∧ s.st.1.regs.X30.toBitVec = raT lab pfx) ∨
  (s.st.2 ∈ dispTPcs lab ∧ spLoad s 0 = some 5#64 ∧ s.st.1.regs.X30.toBitVec = raT lab pfx) ∨
  (s.st.2 ∈ g5Pcs lab ∧ s.st.1.regs.X30.toBitVec = raT lab pfx) ∨
  (s.st.2 ∈ stubPcs lab ∧ s.st.1.regs.X30.toBitVec = raT lab pfx)

/-- Every pc of `Ac`. -/
def acPcs : List Int64 :=
  pcRet lab pfx n :: pcSt lab pfx cl :: tailPcs lab pfx cl ++ failPcs lab pfx ++ dispEPcs lab ++
    dispTPcs lab ++ g5Pcs lab ++ stubPcs lab

/-- hello.w's pc after the call (`.sp6 + 4·25 + 4`). -/
abbrev pcRetH : Int64 := pcRet lab pfx 25
/-- hello.w's tests of the stored result (`.clone13 + 4 … + 16`). -/
abbrev tailPcsH : List Int64 := tailPcs lab pfx ".clone13"
/-- **hello.w's threads abort phase** (`.clone13`, the result at `[sp + 112]`). -/
abbrev AcH (s : State) : Prop := Ac lab pfx 25 ".clone13" 112 s
/-- hello.w's pcs of `AcH`. -/
abbrev acPcsH : List Int64 := acPcs lab pfx 25 ".clone13"

variable {lab pfx n cl off}

/-- **A state in `Ac` is at one of its pcs.** -/
theorem pc_of_ac {s : State} (h : Ac lab pfx n cl off s) : s.st.2 ∈ acPcs lab pfx n cl := by
  unfold acPcs
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp_all

/-- **A state at none of `Ac`'s pcs is not in it.** -/
theorem not_ac_of_pc {s : State} (h : s.st.2 ∉ acPcs lab pfx n cl) : ¬ Ac lab pfx n cl off s :=
  fun h' => h (pc_of_ac h')

/-- The return of a refused `clone` is in `Ac`. -/
theorem ac_ret {s : State} (hp : s.st.2 = pcRet lab pfx n) (hr : CloneRef s.st.1.regs.X0.toBitVec) :
    Ac lab pfx n cl off s := .inl ⟨hp, hr⟩

/-- `.1_spawnfail5` is in `Ac`. -/
theorem ac_fail {s : State} (h : s.st.2 ∈ failPcs lab pfx) : Ac lab pfx n cl off s :=
  .inr (.inr (.inr (.inl h)))

/-- The jump to the threads stub is in `Ac`. -/
theorem ac_g5 {s : State} (h : s.st.2 ∈ g5Pcs lab) (hr : s.st.1.regs.X30.toBitVec = raT lab pfx) :
    Ac lab pfx n cl off s :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h, hr⟩))))))

/-- `scc_rt_abort_threads` is in `Ac`. -/
theorem ac_stub {s : State} (h : s.st.2 ∈ stubPcs lab) (hr : s.st.1.regs.X30.toBitVec = raT lab pfx) :
    Ac lab pfx n cl off s :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨h, hr⟩))))))

/-- **A state in `Ac` at none of the spawn's own pcs** has `x30 = raT lab pfx`. -/
theorem ac_x30 {s : State} (h : Ac lab pfx n cl off s)
    (hn : s.st.2 ∉ pcRet lab pfx n :: pcSt lab pfx cl :: tailPcs lab pfx cl ++ failPcs lab pfx) :
    s.st.1.regs.X30.toBitVec = raT lab pfx := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h | ⟨-, -, hr⟩ | ⟨-, -, hr⟩ | ⟨-, hr⟩ | ⟨-, hr⟩
  all_goals first | exact hr | (exfalso; apply hn; simp_all)

/-- **wake.w's phase is the instance at `13 ".clone9" 48`.** -/
theorem ac_wake {s : State} : Ac lab pfx 13 ".clone9" 48 s ↔ Spike.Lib.A64.ThreadsAb.Ac lab pfx s :=
  Iff.rfl

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.Hello.ThreadsAb.ac_x30' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ac_x30

end Spike.Lib.A64.Hello.ThreadsAb
