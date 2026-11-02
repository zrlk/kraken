/-
**The threads abort phase on x86-64, generic in the spawn's pcs** (the
x86-64 twin of `Spike/Lib/A64HelloThreadsAb.lean`): `Spike/Lib/X64ThreadsAb.lean`'s
`Ac` with the things that are wake.w's there made parameters, and hello.w's
instance.

A spawn's lowering is, for `wc_main`'s local label prefix `pfx`,

```
pfx.cl:    … the clone's argument setup …; syscall      (pfx.cl + n)
           testq %rax, %rax                              (pcRet = pfx.cl + n + 2)
           je pfx.child.scc_rt_thr_worker                (pcJe  = pfx.cl + n + 5)
pfx.st:    movq %rax, off(%rbp); movq off(%rbp), %rax; movq $0, %rcx
           cmpq %rcx, %rax; jl pfx.spawnfail5; jmp pfx.spawned6
pfx.spawnfail5:
           movq $5, %rdi; call scc_rt_abort
```

wake.w's is `cl = ".x21"`, `n = 46`, `st = ".x22"`, `off = -56`; hello.w's
(`.Lwc_main`, five arguments moved to the clone's registers) is
`cl = ".x25"`, `n = 94`, `st = ".x26"`, `off = -120`. The fail block, the
dispatcher's and the threads stub's pcs, the return address `raT` (its
`call`'s pc + 12, from `.spawnfail5`) and `RaW` do not depend on them and are
wake's (`ThreadsAb.failPcs`, `dispTPcs`, `g5Pcs`, `stubPcs`, `raT`, `RaW`,
`WriteAb.dispEPcs`), as is `CloneRef`.

- `cloneAt`, `pcRet`, `pcJe`, `pcSt`, `tailPcs`, `Ac`, `acPcs`: as wake's,
  at `cl n st off`.
- `pc_of_ac`, `not_ac_of_pc`, `ac_ret`, `ac_je`, `ac_fail`, `ac_g5`,
  `ac_stub`, `ac_x30`: as wake's.
- `AcH`, `acPcsH`, `tailPcsH`: hello.w's instance.

The wake instance is `X64ThreadsAb`'s `Ac` by `Iff.rfl` (the `example` at
the end).

**Deviation from the A64 file.** The A64 parameters are `n cl off` (the
`svc`'s index from `.sp6`, the store's label, the stored result's offset from
`sp`); on x86-64 the call is a byte offset from its own label and the store
has a label of its own, so the parameters are `cl n st off` (`off` from
`%rbp`). As in `X64ThreadsAb`, the `je` after the test (`pcJe`, `ac_je`) has
no A64 counterpart and `ac_x30` concludes `RaW`.
-/
import Spike.Lib.X64ThreadsAb

namespace Spike.Lib.X64.Hello.ThreadsAb

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.WriteAb (bpLoad dispEPcs)
open Spike.Lib.X64.ThreadsAb (CloneRef failPcs dispTPcs g5Pcs stubPcs raT RaW)

variable (lab : Label → Int64) (pfx : String) (cl : String) (n : Nat) (st : String) (off : BitVec 64)

/-- The spawn's `clone` call: the `syscall` at `pfx.cl + n`. -/
abbrev cloneAt : Int64 := lab (pfx ++ cl) + Int64.ofNat n

/-- The pc after the call: `testq %rax, %rax`. -/
abbrev pcRet : Int64 := cloneAt lab pfx cl n + 2

/-- The `je` after the test. -/
abbrev pcJe : Int64 := cloneAt lab pfx cl n + 5

/-- The store of the result: `pfx ++ st`. -/
abbrev pcSt : Int64 := lab (pfx ++ st)

/-- The tests of the stored result up to the `jl`. -/
def tailPcs : List Int64 :=
  [lab (pfx ++ st) + 4, lab (pfx ++ st) + 8, lab (pfx ++ st) + 15, lab (pfx ++ st) + 18]

/-- **The threads abort phase**, the stored result at `off(%rbp)`. -/
def Ac (s : State) : Prop :=
  ((s.st.2 = pcRet lab pfx cl n ∨ s.st.2 = pcJe lab pfx cl n) ∧ CloneRef (s.st.1.regs.get64 .rax)) ∨
  (s.st.2 = pcSt lab pfx st ∧ CloneRef (s.st.1.regs.get64 .rax)) ∨
  (s.st.2 ∈ tailPcs lab pfx st ∧ ∃ r, bpLoad s off = some r ∧ CloneRef r) ∨
  s.st.2 ∈ failPcs lab pfx ∨
  (s.st.2 ∈ dispEPcs lab ∧ s.st.1.regs.get64 .rdi = 5#64 ∧ RaW lab s (raT lab pfx)) ∨
  (s.st.2 ∈ dispTPcs lab ∧ bpLoad s (-8) = some 5#64 ∧ RaW lab s (raT lab pfx)) ∨
  (s.st.2 ∈ g5Pcs lab ∧ RaW lab s (raT lab pfx)) ∨
  (s.st.2 ∈ stubPcs lab ∧ RaW lab s (raT lab pfx))

/-- Every pc of `Ac`. -/
def acPcs : List Int64 :=
  pcRet lab pfx cl n :: pcJe lab pfx cl n :: pcSt lab pfx st :: tailPcs lab pfx st ++ failPcs lab pfx ++
    dispEPcs lab ++ dispTPcs lab ++ g5Pcs lab ++ stubPcs lab

/-- hello.w's tests of the stored result (`.x26 + 4 … + 18`). -/
abbrev tailPcsH : List Int64 := tailPcs lab pfx ".x26"
/-- **hello.w's threads abort phase** (`.x25 + 94`, `.x26`, the result at
`-120(%rbp)`). -/
abbrev AcH (s : State) : Prop := Ac lab pfx ".x25" 94 ".x26" (-120) s
/-- hello.w's pcs of `AcH`. -/
abbrev acPcsH : List Int64 := acPcs lab pfx ".x25" 94 ".x26"

variable {lab pfx cl n st off}

/-- **A state in `Ac` is at one of its pcs.** -/
theorem pc_of_ac {s : State} (h : Ac lab pfx cl n st off s) : s.st.2 ∈ acPcs lab pfx cl n st := by
  unfold acPcs
  rcases h with ⟨h | h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp_all

/-- **A state at none of `Ac`'s pcs is not in it.** -/
theorem not_ac_of_pc {s : State} (h : s.st.2 ∉ acPcs lab pfx cl n st) : ¬ Ac lab pfx cl n st off s :=
  fun h' => h (pc_of_ac h')

/-- The return of a refused `clone` is in `Ac`. -/
theorem ac_ret {s : State} (hp : s.st.2 = pcRet lab pfx cl n) (hr : CloneRef (s.st.1.regs.get64 .rax)) :
    Ac lab pfx cl n st off s := .inl ⟨.inl hp, hr⟩

/-- The `je` after the test of a refused `clone`'s result is in `Ac`. -/
theorem ac_je {s : State} (hp : s.st.2 = pcJe lab pfx cl n) (hr : CloneRef (s.st.1.regs.get64 .rax)) :
    Ac lab pfx cl n st off s := .inl ⟨.inr hp, hr⟩

/-- `.spawnfail5` is in `Ac`. -/
theorem ac_fail {s : State} (h : s.st.2 ∈ failPcs lab pfx) : Ac lab pfx cl n st off s :=
  .inr (.inr (.inr (.inl h)))

/-- The jump to the threads stub is in `Ac`. -/
theorem ac_g5 {s : State} (h : s.st.2 ∈ g5Pcs lab) (hr : RaW lab s (raT lab pfx)) :
    Ac lab pfx cl n st off s :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h, hr⟩))))))

/-- `scc_rt_abort_threads` is in `Ac`. -/
theorem ac_stub {s : State} (h : s.st.2 ∈ stubPcs lab) (hr : RaW lab s (raT lab pfx)) :
    Ac lab pfx cl n st off s :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨h, hr⟩))))))

/-- **A state in `Ac` at none of the spawn's own pcs** has the return
address `raT lab pfx`. -/
theorem ac_x30 {s : State} (h : Ac lab pfx cl n st off s)
    (hn : s.st.2 ∉ pcRet lab pfx cl n :: pcJe lab pfx cl n :: pcSt lab pfx st :: tailPcs lab pfx st ++
      failPcs lab pfx) :
    RaW lab s (raT lab pfx) := by
  rcases h with ⟨h | h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h | ⟨-, -, hr⟩ | ⟨-, -, hr⟩ | ⟨-, hr⟩ | ⟨-, hr⟩
  all_goals first | exact hr | (exfalso; apply hn; simp_all)

/-- wake.w's phase is the instance at `".x21" 46 ".x22" (-56)`. -/
example {s : State} : Ac lab pfx ".x21" 46 ".x22" (-56) s ↔ Spike.Lib.X64.ThreadsAb.Ac lab pfx s :=
  Iff.rfl

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.Hello.ThreadsAb.ac_x30' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ac_x30

end Spike.Lib.X64.Hello.ThreadsAb
