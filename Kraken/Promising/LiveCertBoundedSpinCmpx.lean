/-
**Bounded certification for the x64 `lock cmpxchg`
spinlock** (`CmpxAbs.cmpxImageV`, valid layout, `Arch.tso`):
`CertBoundedFrom Arch.tso c0 18` for every `SpinX64.CmpxStart`
configuration, and the fuel-free liveness theorems
`spin_cmpx_live{,_oneShot}_semU{,_concrete}`. The x64 counterpart of
`LiveCertBoundedSpinCas.lean`.

**The iteration cut** (`LiveCertCut`, generic in the ISA and the
architecture, used unchanged): a certifying solo run longer than `F = 18`
instructions is not the shortest one. Before its first write (a successful
`lock cmpxchg`, which leaves the loop) the run stays in the acquire loop
`xorl; movl $1,%ecx; lock cmpxchgl; jne`, where only `%rax`, `%rcx` and the
flags change; its scalar views only grow (`stepOne_grow`). The repetition
that shortens it: **two visits of the `lock cmpxchg` cell (position 3),
both reached through `xorl; movl` after a failed `lock cmpxchg`, with the
same `AF`**. `xorl %eax,%eax` leaves `AF` undefined, a two-way choice
(`SpinX64CmpxTrees.exec_xor`); every other part of the machine state at
position 3 is fixed (`%rax = 0`, `%rcx = 1`, the flags of `0`, the rest the
run's start's), so the two states are equal (`st3`), and the earlier
dominates (`Thread.Dom`) the later: the loop between them is cut
(`ThreadNPn.dom`).

**TSO views.** A failed locked `cmpxchg` is `fence; read; fence` (no write): the
read's post-view `ν` is at least the thread's
`vrNew` before it (`readPre`), and at most its `vrNew` after the trailing
`mfence`-like fence (the read raises `vrOld`). No `vrOld` split or read
replay is needed (unlike `LiveCertBoundedSpinCas`'s `cut_7`).

**Register views.** `xorl %eax,%eax` reads `%rax` (its dependency on
itself, `X64/Deps.lean`), so `%rax`'s and the flags' register views at
position 3 carry the post-view `ν` of the last failed read, and `%rcx`'s is
`0` (`PR`); the start's `%rax` view is arbitrary, which is why only states
after a failed read are compared. For two such visits `q` (earlier) and `t`,
`ν_q ≤ vrNew(q) ≤ ν_t`.

**The potential** `Φ` (from the loop automaton: at most one cut-free visit
per `AF` value, after a first failed read): at most `18` instructions from
`jne` with `ZF` clear, `17` from `xorl`, then `7` for a successful
`lock cmpxchg` and the critical section; the tail alone is at most `6`
(`Ψ`). `F` depends on the program only: not on the fuel, the thread count or
the layout.

Names: `exec_cmpxchg'`, `Core`, `st3`, `Agree`, `PR`, `LInv`, `W3`, `Φ`,
`Ψ`, `tail_bound`, `loop_bound`, `certOkN_bound`, `cmpx_certBounded`,
`CmpxSpinLiveSemU`, `CmpxSpinLiveOneShotSemU`, `spin_cmpx_live_semU`,
`spin_cmpx_live_oneShot_semU` and their `_concrete` forms.
-/
import Kraken.Promising.LiveCertBounded
import Kraken.Promising.LiveCertCut
import Kraken.Promising.LiveSpinX64SemCmpx

namespace Kraken.Promising.Live.CertBoundedSpinCmpx

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live
open Kraken.Promising.Live.SpinX64CmpxTrees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep
open Kraken.Promising.Live.Sem Kraken.Promising.Live.SpinX64SemCmpxSolo Kraken.Promising.Live.SpinX64SemCmpxInv
open Kraken.Promising.Live.CertBounded Kraken.Promising.Live.CertCut
open Kraken.Promising.Live.SpinX64CmpxInv (LkL CtL Static stepOne_end s4 s5 s6 s9)
open Kraken.Promising.X64.EnvG.CmpxAbs (cmpxImageV symC)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout cmpxImageV)]

set_option hygiene false in
local notation "pcA" => (layout cmpxImageV).addrOf

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## The cells, refined -/

omit layout hv in
theorem set64_rax_self (r : Reg64s) : r.set64 .rax (r.get64 .rax) = r := by
  cases r; rfl

omit layout hv in
theorem set64_rax_rcx_rax (r : Reg64s) (x y z : BitVec 64) :
    ((r.set64 .rax x).set64 .rcx y).set64 .rax z = (r.set64 .rax z).set64 .rcx y := by
  cases r; rfl

omit layout hv in
theorem set64_rcx_rcx (r : Reg64s) (y z : BitVec 64) : (r.set64 .rcx y).set64 .rcx z = r.set64 .rcx z := by
  cases r; rfl

omit layout hv in
theorem set64_rax_rax (r : Reg64s) (y z : BitVec 64) : (r.set64 .rax y).set64 .rax z = r.set64 .rax z := by
  cases r; rfl

omit layout hv in
theorem set64_rcx_self (r : Reg64s) : r.set64 .rcx (r.get64 .rcx) = r := by
  cases r; rfl

/-- `lock cmpxchgl %ecx,(lock)` (position 3) as `SpinX64CmpxTrees.exec_cmpxchg`,
with the shape of the machine state after it: only `%rax` and the flags
change. -/
theorem exec_cmpxchg' (st : State) (h : At st 3) (hdm : Mem.loadInt st.st.1.dmem (symC "lock") 4 = none) :
    ∃ g : Val → MachineData, (∀ v, ∃ x S, g v = { st.st.1 with regs := st.st.1.regs.set64 .rax x, status := S }) ∧
      (∀ v, (g v).status.zf = true ↔ BitVec.setWidth 32 v = eax st.st.1) ∧
      isa.exec st = some (.rmw .acqRel false ⟨symC "lock", 4⟩
        (fun old => if BitVec.setWidth 32 old = eax st.st.1 then
          some (BitVec.setWidth 128 (st.st.1.regs.get (.low .rcx .W32))) else none)
        fun v => .done (goto st (g v) (pcA 4))) := by
  rw [show pcA 4 = st.st.2 + .ofNat (Kraken.Layout.size Directive 3) from by rw [h.pc]; exact addrOf_step (by decide)]
  refine ⟨_, ?_, ?_, by
    x64cell h 3 cmpxImageV [cmpxImageV, Kraken.Promising.X64.EnvG.CmpxAbs.cmpxWorkerV]
      [label_worker, label_done, hdm, symC]; rfl⟩
  · intro v
    by_cases e : BitVec.setWidth 32 v = st.st.1.regs.get (.low .rax .W32)
    · refine ⟨st.st.1.regs.get64 .rax, ?_, ?_⟩
      rotate_left
      · simp only [e, ↓reduceIte, set64_rax_self]
        rfl
    · refine ⟨BitVec.setWidth 64 (BitVec.setWidth 32 v), ?_, ?_⟩
      rotate_left
      · simp only [e, ↓reduceIte]
        rfl
  · intro v
    change (eax st.st.1 - BitVec.setWidth 32 v == 0#32) = true ↔ _
    simp only [beq_iff_eq]
    constructor <;> intro e <;> bv_omega

/-! ## The dependencies of the loop cells -/

omit hv in
/-- A thread state's directive is its code's first cell (the x64 form of
`CertBoundedSpinCas.directive_of_codeAt`). -/
theorem directive_of_codeAt {st : State} {d : Directive} {z : Nat} {rest : List (Directive × Nat)}
    (hcode : Kraken.Executable.codeAt st.exe st.st.2 = (d, z) :: rest) : st.directive = some d := by
  obtain ⟨exe, endPc, ⟨s, pc⟩, showPc, decls⟩ := st
  unfold State.directive
  simp only at hcode ⊢
  rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) = Kraken.Executable.codeAt exe pc from by
    unfold Kraken.Executable.codeAt
    congr 1, hcode]
  rfl

/-- Read the dependencies of the cell at position `i`. -/
local macro "x64deps" h:ident i:num : tactic => `(tactic| (
  have hc := Kraken.Executable.codeAt_addrOf (p := cmpxImageV) (i := $i) (d := cmpxImageV[$i])
    (by decide) (by decide)
  rw [← ($h).pc] at hc
  generalize hd : cmpxImageV[$i] = d at hc
  simp only [cmpxImageV, Kraken.Promising.X64.EnvG.CmpxAbs.cmpxWorkerV, List.cons_append, List.getElem_cons_succ,
    List.getElem_cons_zero] at hd
  subst hd
  have hdir := directive_of_codeAt (by rw [($h).exe]; exact hc)
  show X64.deps _ = _
  unfold X64.deps
  rw [hdir]
  rfl))

/-- The loop cells' dependencies: `xorl %eax,%eax` reads `%rax` and writes
`%rax` and the flags; `movl $1,%ecx` writes `%rcx`; `lock cmpxchgl` reads
`%rax`, `%rcx`, loads into `%rax` and writes the flags; `jne` reads the
flags. -/
theorem deps_1 (st : State) (h : At st 1) :
    isa.deps st = { dataRegs := [.r .rax, .r .rax], defs := [.r .rax, .rflags] } := by x64deps h 1
theorem deps_2 (st : State) (h : At st 2) : isa.deps st = { defs := [.r .rcx] } := by x64deps h 2
theorem deps_3 (st : State) (h : At st 3) :
    isa.deps st = { dataRegs := [.r .rax, .r .rcx], loadDefs := [.r .rax], defs := [.rflags] } := by x64deps h 3
theorem deps_4 (st : State) (h : At st 4) : isa.deps st = { condRegs := [.rflags], isBranch := true } := by
  x64deps h 4

/-! ## The machine state in the loop -/

/-- `s0` with `%rax := x`, `%rcx := y`, flags `S`, at `pc`. -/
abbrev cst (s0 : State) (x y : BitVec 64) (S : StatusFlags) (pc : Int64) : State :=
  goto s0 { s0.st.1 with regs := (s0.st.1.regs.set64 .rax x).set64 .rcx y, status := S } pc

/-- The machine state of a loop state: `s0`'s with `%rax`, `%rcx` and the
flags replaced, at some pc. -/
def Core (s0 s : State) : Prop := ∃ x y S pc, s = cst s0 x y S pc

/-- The flags `xorl %eax,%eax` leaves, with `AF = b`. -/
abbrev xorS (b : Bool) : StatusFlags := StatusFlags.from_result 0#32 { cf := false, af := b, of := false }

/-- **The state at the `lock cmpxchg` reached through `xorl; movl`**: all
but `AF` fixed. -/
abbrev st3 (s0 : State) (b : Bool) : State := cst s0 0#64 1#64 (xorS b) (pcA 3)

omit hv in
theorem Core.self (s0 : State) : Core s0 s0 :=
  ⟨s0.st.1.regs.get64 .rax, s0.st.1.regs.get64 .rcx, s0.st.1.status, s0.st.2, by
    simp only [cst, set64_rax_self, set64_rcx_self]⟩

omit hv in
theorem cst_rax (s0 : State) (x y z : BitVec 64) (S S' : StatusFlags) (pc pc' : Int64) :
    goto (cst s0 x y S pc) { (cst s0 x y S pc).st.1 with
      regs := (cst s0 x y S pc).st.1.regs.set64 .rax z
      status := S' } pc' = cst s0 z y S' pc' := by
  simp only [goto, set64_rax_rcx_rax]

omit hv in
theorem cst_rcx (s0 : State) (x y z : BitVec 64) (S : StatusFlags) (pc pc' : Int64) :
    goto (cst s0 x y S pc) { (cst s0 x y S pc).st.1 with regs := (cst s0 x y S pc).st.1.regs.set64 .rcx z } pc' =
      cst s0 x z S pc' := by
  simp only [goto, set64_rcx_rcx]

omit hv in
theorem cst_goto (s0 : State) (x y : BitVec 64) (S : StatusFlags) (pc pc' : Int64) :
    goto (cst s0 x y S pc) (cst s0 x y S pc).st.1 pc' = cst s0 x y S pc' := rfl

/-! ## Register views -/

/-- Register-view arrays equal to `base` except at `%rax`, `%rcx` and the
flags (indices `0`, `2`, `16`). -/
def Agree (base a : Array View) : Prop := a.size = base.size ∧ ∀ j, j ≠ 0 → j ≠ 2 → j ≠ 16 → a[j]! = base[j]!

/-- `v` at index `j`, if in bounds. -/
def cap (a : Array View) (j : Nat) (v : View) : View := if j < a.size then v else 0

omit layout hv in
theorem get_set (a : Array View) (i j : Nat) (v : View) :
    (a.setIfInBounds i v)[j]! = if i = j ∧ i < a.size then v else a[j]! := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h1 : i = j
  · subst h1; by_cases h2 : i < a.size <;> simp [h2]
  · simp [h1]

/-- **The register views after a failed read**, at position `i`: `%rax` (and,
from `xorl` on, the flags) carry the read's post-view `ν`, `%rcx` (from
`movl` on) carries `0`. -/
def PRA (i : Nat) (ν : View) (a : Array View) : Prop :=
  a[0]! = cap a 0 ν ∧ (i = 2 ∨ i = 3 → a[16]! = cap a 16 ν) ∧ (i = 3 → a[2]! = 0)

omit layout hv in
theorem Agree.set {base a : Array View} (h : Agree base a) {i : Nat} (hi : i = 0 ∨ i = 2 ∨ i = 16) (v : View) :
    Agree base (a.setIfInBounds i v) := by
  refine ⟨by rw [Array.size_setIfInBounds]; exact h.1, fun j h0 h2 h16 => ?_⟩
  rw [get_set, ite_eq_right_iff.mpr (fun h => absurd h.1 (by omega))]
  exact h.2 j h0 h2 h16

omit layout hv in
/-- **Two flagged arrays**: the earlier is below the later. -/
theorem Agree.arrLe {base a b : Array View} (ha : Agree base a) (hb : Agree base b) {νa νb : View} (hν : νa ≤ νb)
    (hpa : PRA 3 νa a) (hpb : PRA 3 νb b) : ArrLe a b := by
  refine ⟨ha.1.trans hb.1.symm, fun j => ?_⟩
  have hs := ha.1.trans hb.1.symm
  by_cases h0 : j = 0
  · subst h0; rw [hpa.1, hpb.1]; unfold cap; rw [hs]; split <;> omega_t
  by_cases h16 : j = 16
  · subst h16; rw [hpa.2.1 (.inr rfl), hpb.2.1 (.inr rfl)]; unfold cap; rw [hs]; split <;> omega_t
  by_cases h2 : j = 2
  · subst h2; rw [hpa.2.2 rfl, hpb.2.2 rfl]; exact Nat.le_refl _
  rw [ha.2 j h0 h2 h16, hb.2 j h0 h2 h16]; exact Nat.le_refl _

omit layout hv in
theorem get_oob {a : Array View} {j : Nat} (h : ¬ j < a.size) : a[j]! = 0 := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt h),
    Option.getD_none]
  rfl

omit layout hv in
theorem get_set_ne (a : Array View) {i j : Nat} (h : i ≠ j) (v : View) : (a.setIfInBounds i v)[j]! = a[j]! := by
  rw [get_set]; simp [h]

omit layout hv in
theorem get_set_eq (a : Array View) (i : Nat) (v : View) : (a.setIfInBounds i v)[i]! = cap a i v := by
  rw [get_set]; unfold cap
  by_cases h : i < a.size
  · simp [h]
  · simp [h]

omit layout hv in
theorem cap_set (a : Array View) (i j : Nat) (v ν : View) : cap (a.setIfInBounds i v) j ν = cap a j ν := by
  simp [cap]

omit layout hv in
theorem cap_cap (a : Array View) (i j : Nat) (hij : j ≤ i) (ν : View) : cap a i (cap a j ν) = cap a i ν := by
  unfold cap
  by_cases hi : i < a.size
  · simp only [hi, show j < a.size by omega, ↓reduceIte]
  · simp only [hi, ↓reduceIte]

omit layout hv in
/-- A failed `lock cmpxchg`: `%rax := ν` (after the flags). -/
theorem PRA.fail (a : Array View) (ν X : View) : PRA 4 ν ((a.setIfInBounds 16 X).setIfInBounds 0 ν) :=
  ⟨by simp only [get_set_eq, cap_set], fun h => by omega, fun h => by omega⟩

omit layout hv in
theorem PRA.jne {ν : View} {a : Array View} (h : PRA 4 ν a) : PRA 1 ν a :=
  ⟨h.1, fun h => by omega, fun h => by omega⟩

omit layout hv in
/-- `xorl %eax,%eax`: `%rax` and the flags get `%rax`'s view. -/
theorem PRA.xor {ν X : View} {a : Array View} (h : PRA 1 ν a) (hX : X = a[0]!) :
    PRA 2 ν ((a.setIfInBounds 0 X).setIfInBounds 16 X) := by
  refine ⟨?_, fun _ => ?_, fun h => by omega⟩
  · rw [get_set_ne _ (by decide), get_set_eq, cap_set, cap_set, hX, h.1, cap_cap _ _ _ (Nat.le_refl _)]
  · rw [get_set_eq, cap_set, cap_set, cap_set, hX, h.1, cap_cap _ _ _ (by decide)]

omit layout hv in
/-- `movl $1,%ecx`: `%rcx`'s view `0`. -/
theorem PRA.movc {ν Z : View} {a : Array View} (h : PRA 2 ν a) (hZ : Z = 0) : PRA 3 ν (a.setIfInBounds 2 Z) := by
  refine ⟨?_, fun _ => ?_, fun _ => ?_⟩
  · rw [get_set_ne _ (by decide), cap_set, h.1]
  · rw [get_set_ne _ (by decide), cap_set, h.2.1 (.inl rfl)]
  · rw [get_set_eq, hZ]; unfold cap; split <;> rfl

/-! ## The loop invariant and the witnesses -/

variable {tid : Nat}

/-- **The loop invariant**, relative to the thread `s0` at the start of the
write-free stretch: a loop cell, `SInv`, `Core`, only `%rax`'s, `%rcx`'s and
the flags' register views changed, scalar views grown, the forwarding table,
promises and memory unchanged, no pending load exclusive. -/
structure LInv (s0 t : Thread isa) : Prop where
  pos : ∃ i ∈ [1, 2, 3, 4], t.st.st.2 = pcA i
  sinv : SInv t.st
  core : Core s0.st t.st
  rv : Agree s0.rview t.rview
  wv : Agree s0.wview t.wview
  grow : s0.views.Grow t.views
  fwd : t.views.fwdb = s0.views.fwdb
  xclb : t.views.xclb = none
  prom : t.prom = s0.prom

/-- **After a failed read**, at position `i`, with the read's post-view `ν`:
`ν ≤ vrNew`, the register views of `PRA`, and the machine state from
`xorl` on. -/
structure PR (s0 : Thread isa) (i : Nat) (ν : View) (t : Thread isa) : Prop where
  le : ν ≤ t.views.vrNew
  rv : PRA i ν t.rview
  wv : PRA i ν t.wview
  st2 : i = 2 → ∃ y b, t.st = cst s0.st 0#64 y (xorS b) (pcA 2)
  st3 : i = 3 → t.st = st3 s0.st t.st.st.1.status.af

/-- An earlier flagged `lock cmpxchg` state `q` (reached in `a₁ < a` steps)
with `AF = b`, its views grown up to the current thread, its `vrNew` below
the current post-view `ν`. -/
def W3 (tid : Nat) (s0 : Thread isa) (mem : Memory) (a : Nat) (b : Bool) (ν : View) (cur : Thread isa) : Prop :=
  ∃ (q : Thread isa) (a₁ : Nat) (νq : View), a₁ < a ∧ ThreadNPn Arch.tso tid a₁ (s0, mem) (q, mem) ∧ LInv s0 q ∧
    PR s0 3 νq q ∧ q.st.st.1.status.af = b ∧ q.views.Grow cur.views ∧ q.views.vrNew ≤ ν

/-! ## The potential -/

/-- The number of `AF` values without a flagged visit yet. -/
def unseen (h0 h1 : Bool) : Nat := (if h0 then 0 else 1) + (if h1 then 0 else 1)

/-- The bound at `jne`, at `xorl` and at an unflagged (or new) `lock cmpxchg`,
by whether a failed read was seen and the number of unseen `AF` values. -/
def P4 : Bool → Nat → Nat | true, 0 => 6 | true, 1 => 10 | true, _ => 14 | false, 0 => 10 | false, 1 => 14 | false, _ => 18
def P1 : Bool → Nat → Nat | true, 0 => 2 | true, 1 => 9 | true, _ => 13 | false, 0 => 9 | false, 1 => 13 | false, _ => 17
def P3 : Bool → Nat → Nat | true, 0 => 7 | true, 1 => 7 | true, _ => 11 | false, 0 => 7 | false, 1 => 11 | false, _ => 15

/-- At the `lock cmpxchg`: `0` at a repeated flagged visit (cut). -/
def F3 (pr h0 h1 af : Bool) : Nat := if pr && (if af then h1 else h0) then 0 else P3 pr (unseen h0 h1)

/-- **The potential**: the longest run without a repetition from a loop
cell, given whether a failed read was seen (`pr`), which `AF` values have a
flagged visit (`h0`, `h1`), and the current `AF`. -/
def Φ : Nat → Bool → Bool → Bool → Bool → Nat
  | 1, pr, h0, h1, _ => P1 pr (unseen h0 h1)
  | 2, pr, h0, h1, af => 1 + F3 pr h0 h1 af
  | 3, pr, h0, h1, af => F3 pr h0 h1 af
  | 4, pr, h0, h1, _ => P4 pr (unseen h0 h1)
  | _, _, _, _, _ => 0

omit layout hv in
theorem Φ_le (i : Nat) (af : Bool) : Φ i false false false af ≤ 18 := by
  rcases i with _ | _ | _ | _ | _ | i <;> cases af <;> simp [Φ, F3, P1, P3, P4, unseen]

/-! ## The straight line after the loop -/

/-- The remaining steps from `jne` with `ZF` set, and from the critical
section on. -/
def Ψ : Nat → Nat
  | 4 => 6 | 5 => 5 | 6 => 4 | 7 => 3 | 8 => 2 | 9 => 1 | _ => 0

/-- **The tail**: from `jne` with `ZF` set, or from the critical section on,
a solo run (any promises) has at most `Ψ i ≤ 6` instructions. -/
theorem tail_bound : ∀ (n : Nat) (p r : Thread isa × Memory), ThreadRun Arch.tso tid n p r → SInv p.1.st →
    ∀ i ∈ [4, 5, 6, 7, 8, 9, 10], p.1.st.st.2 = pcA i → (i = 4 → p.1.st.st.1.status.zf = true) →
    n ≤ Ψ i := by
  intro n p r h
  induction h with
  | refl p => intro _ i _ _ _; exact Nat.zero_le _
  | @step n p q r hs _ ih =>
    intro hS i hi hpc hz
    obtain ⟨outs, oc, hs, ho, rfl⟩ := hs
    have hS' := (step_sinv hS hs ho).1
    have no4 : ∀ j, j ≠ 4 → (j = 4 → oc.thread.st.st.1.status.zf = true) := fun j hj h => absurd h hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨-, hst, -⟩ := s4 hS.st hs ho hpc
      rw [ite_eq_left (hz rfl)] at hst
      have := ih hS' 5 (by decide) (by rw [hst]) (no4 5 (by decide))
      simp only [Ψ] at this ⊢; omega
    · obtain ⟨md, -, hst, -⟩ := s5 hS.st hs ho hpc
      have := ih hS' 6 (by decide) (by rw [hst]) (no4 6 (by decide))
      simp only [Ψ] at this ⊢; omega
    · obtain ⟨md, -, hst, -⟩ := s6 hS.st hs ho hpc
      have := ih hS' 7 (by decide) (by rw [hst]) (no4 7 (by decide))
      simp only [Ψ] at this ⊢; omega
    · obtain ⟨md, -, hst, -⟩ := s7p hS.st hs ho hpc
      have := ih hS' 8 (by decide) (by rw [hst]) (no4 8 (by decide))
      simp only [Ψ] at this ⊢; omega
    · obtain ⟨hst, -⟩ := s8p hS.st hs ho hpc
      have := ih hS' 9 (by decide) (by rw [hst]) (no4 9 (by decide))
      simp only [Ψ] at this ⊢; omega
    · obtain ⟨-, hst, -⟩ := s9 hS.st hs ho hpc
      have := ih hS' 10 (by decide) (by rw [hst]) (no4 10 (by decide))
      simp only [Ψ] at this ⊢; omega
    · rw [stepOne_end hS.st hpc] at hs; cases hs

/-! ## One loop step -/

/-- No cell of the worker performs a load exclusive. -/
theorem noXcl {t : Thread isa} (hS : SInv t.st) : ∀ tree, isa.exec t.st = some tree → tree.NoXclLoad := by
  intro tree hex
  obtain ⟨hSt, p, hp, hpc, -⟩ := hS
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [exec_xor _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; exact fun _ => trivial
  · rw [exec_movc _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; trivial
  · obtain ⟨g, -, h⟩ := exec_cmpxchg _ (hSt.at (by decide) (by decide) hpc) hSt.dl
    rw [h] at hex; cases hex; exact fun _ => trivial
  · rw [exec_jne _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; trivial
  · obtain ⟨g, -, h⟩ := exec_ldc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    rw [h] at hex; cases hex; exact ⟨rfl, fun _ => trivial⟩
  · obtain ⟨md, -, h⟩ := exec_add _ (hSt.at (by decide) (by decide) hpc)
    rw [h] at hex; cases hex; trivial
  · obtain ⟨v, md, -, h⟩ := exec_stc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    rw [h] at hex; cases hex; exact fun _ => trivial
  · rw [exec_unlock _ (hSt.at (by decide) (by decide) hpc) hSt.dl] at hex; cases hex; exact fun _ => trivial
  · rw [exec_jmp _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; trivial
  · have := stepOne_end hSt hpc Arch.tso 0 default
    simp [stepOne, hex] at this

omit layout hv in
/-- `finishInstr` with two ALU destinations, no load and no branch (as
`CertCut.finishInstr_def1`). -/
theorem finishInstr_def2 {I : ISA} {t : Thread I} {d : InstrDeps I.RegId} {iv : InstrViews} {st : I.State} {c : Ctx}
    {r₁ r₂ : I.RegId} (hd : d.defs = [r₁, r₂]) (hl : d.loadDefs = []) (hs : d.statusDefs = [])
    (hc : d.casLike = false) (hb : d.isBranch = false) (hp : d.isPick = false) {th : Thread I}
    (h : th ∈ finishInstr t d iv st c) :
    th = ({ t with st := st, views := c.views, prom := c.prom }.setRegView r₁
      (max (max iv.addrR iv.dataR) iv.condW) (max (max iv.addrW iv.dataW) iv.condW)).setRegView r₂
      (max (max iv.addrR iv.dataR) iv.condW) (max (max iv.addrW iv.dataW) iv.condW) := by
  unfold finishInstr at h
  simp only [hd, hl, hs, hc, hb, hp, List.foldl_nil, List.foldl_cons, List.zip_nil_left, List.length_nil,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.mem_singleton, ite_self] at h
  exact h

omit layout hv in
/-- `finishInstr` with one ALU destination, one load destination, no write
performed and no branch. -/
theorem finishInstr_defload {I : ISA} {t : Thread I} {d : InstrDeps I.RegId} {iv : InstrViews} {st : I.State}
    {c : Ctx} {r₁ r₂ : I.RegId} (hd : d.defs = [r₁]) (hl : d.loadDefs = [r₂]) (hs : d.statusDefs = [])
    (hw : c.rmwWrote = false) (hb : d.isBranch = false) (hp : d.isPick = false) {ν : View}
    (hlv : c.loadViews = [ν]) {th : Thread I} (h : th ∈ finishInstr t d iv st c) :
    th = ({ t with st := st, views := c.views, prom := c.prom }.setRegView r₁
      (max (max iv.addrR iv.dataR) iv.condW) (max (max iv.addrW iv.dataW) iv.condW)).setRegView r₂ ν ν := by
  unfold finishInstr at h
  simp only [hd, hl, hs, hw, hb, hp, hlv, List.foldl_nil, List.foldl_cons, List.zip_cons_cons, List.zip_nil_right,
    List.length_cons, List.length_nil, Bool.and_false, Bool.false_eq_true, ↓reduceIte, List.mem_singleton,
    beq_self_eq_true] at h
  exact h

omit layout hv in
theorem setRegView_rv {I : ISA} (t : Thread I) (r : I.RegId) (rv wv : View) :
    (t.setRegView r rv wv).rview = t.rview.setIfInBounds (I.regIndex r).val rv := by
  simp [Thread.setRegView, Array.set!_eq_setIfInBounds]

omit layout hv in
theorem setRegView_wv {I : ISA} (t : Thread I) (r : I.RegId) (rv wv : View) :
    (t.setRegView r rv wv).wview = t.wview.setIfInBounds (I.regIndex r).val wv := by
  simp [Thread.setRegView, Array.set!_eq_setIfInBounds]

/-- `xorl`'s dependencies. -/
abbrev d1 : InstrDeps isa.RegId := { dataRegs := [RegId.r .rax, RegId.r .rax], defs := [RegId.r .rax, RegId.rflags] }

/-- The read-ordering input view of an ALU instruction. -/
abbrev inR (t : Thread isa) (d : InstrDeps isa.RegId) : View :=
  max (max (instrViews t d).addrR (instrViews t d).dataR) (instrViews t d).condW

/-- The write-ordering input view of an ALU instruction. -/
abbrev inW (t : Thread isa) (d : InstrDeps isa.RegId) : View :=
  max (max (instrViews t d).addrW (instrViews t d).dataW) (instrViews t d).condW

omit layout hv in
theorem inR_d1 (t : Thread isa) : inR t d1 = t.rview[0]! := by
  show max (max 0 (max (max 0 t.rview[0]!) t.rview[0]!)) 0 = _
  omega_t

omit layout hv in
theorem inW_d1 (t : Thread isa) : inW t d1 = t.wview[0]! := by
  show max (max 0 (max (max 0 t.wview[0]!) t.wview[0]!)) 0 = _
  omega_t

omit layout hv in
theorem fenceStep_loadViews (c : Ctx) (k : FenceKind) : (fenceStep c k).loadViews = c.loadViews := by
  unfold fenceStep; split <;> rfl

section Steps

variable {t : Thread isa} {mem : Memory} {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
  (hS : SInv t.st) (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok oc ∈ outs)

include hS hs ho

/-- The generic facts of a step: `SInv`, views grown, no pending exclusive,
and, without a write, forwarding unchanged. -/
theorem step_gen (hx : t.views.xclb = none) :
    SInv oc.thread.st ∧ t.views.Grow oc.thread.views ∧ oc.thread.views.xclb = none ∧
      (oc.mem = mem → oc.thread.prom = t.prom → oc.thread.views.fwdb = t.views.fwdb) := by
  obtain ⟨tree, -, -, hex, -⟩ := stepOne_fi Arch.tso hs ho
  obtain ⟨hg, -, hnw⟩ := stepOne_grow Arch.tso hs ho
  refine ⟨(step_sinv hS hs ho).1, hg, stepOne_xclb_none Arch.tso hex (noXcl hS tree hex) hs ho hx, fun hm hp => ?_⟩
  exact ((hnw (by rw [hm])).2 (by rw [hp])).1

/-- `xorl %eax,%eax` (position 1): `%rax := 0`, flags `xorS b`; `%rax`'s and
the flags' register views become the instruction's input views. -/
theorem step_1 (hpc : t.st.st.2 = pcA 1) : oc.mem = mem ∧ ∃ b : Bool, oc.thread =
    ({ t with
      st := goto t.st { t.st.st.1 with regs := t.st.st.1.regs.set64 .rax 0#64, status := xorS b } (pcA 2)
      views := t.views
      prom := t.prom }.setRegView (RegId.r .rax) (inR t d1) (inW t d1)).setRegView RegId.rflags
        (inR t d1) (inW t d1) := by
  have hat := hS.st.at (by decide) (by decide) hpc
  obtain ⟨tree, st, c', hex, hr, hfi, hm⟩ := stepOne_fi Arch.tso hs ho
  rw [exec_xor _ hat] at hex
  obtain rfl := Option.some.inj hex
  obtain ⟨⟨i, rfl⟩, rfl⟩ := SpinX64Step.run_choose Arch.tso tid _ hr
  rw [deps_1 _ hat] at hfi
  exact ⟨hm, i.val == 1, finishInstr_def2 rfl rfl rfl rfl rfl rfl hfi⟩

/-- `movl $1,%ecx` (position 2): `%rcx := 1`, with register view `0`. -/
theorem step_2 (hpc : t.st.st.2 = pcA 2) : oc.mem = mem ∧ oc.thread =
    { t with
      st := goto t.st { t.st.st.1 with regs := t.st.st.1.regs.set64 .rcx 1#64 } (pcA 3)
      views := t.views
      prom := t.prom }.setRegView (RegId.r .rcx) (max (max 0 0) 0) (max (max 0 0) 0) := by
  have hat := hS.st.at (by decide) (by decide) hpc
  obtain ⟨tree, st, c', hex, hr, hfi, hm⟩ := stepOne_fi Arch.tso hs ho
  rw [exec_movc _ hat] at hex
  obtain rfl := Option.some.inj hex
  obtain ⟨rfl, rfl⟩ := run_done Arch.tso tid _ hr
  rw [deps_2 _ hat] at hfi
  exact ⟨hm, finishInstr_def1 rfl rfl rfl rfl rfl rfl hfi⟩

/-- `jne worker` (position 4): register views unchanged. -/
theorem step_4 (hpc : t.st.st.2 = pcA 4) : oc.thread.rview = t.rview ∧ oc.thread.wview = t.wview := by
  obtain ⟨tree, st, c', hex, hr, hfi, hm⟩ := stepOne_fi Arch.tso hs ho
  rw [deps_4 _ (hS.st.at (by decide) (by decide) hpc)] at hfi
  exact finishInstr_regs_nil rfl rfl rfl hfi

/-- `lock cmpxchgl` (position 3): failing, no write, `%rax`'s views the
read's post-view `ν` with `vrNew ≤ ν ≤ vrNew'`, only `%rax` and the flags
changed in the machine state; succeeding, `jne` with `ZF` set. -/
theorem step_3 (hpc : t.st.st.2 = pcA 3) :
    (∃ ν x S X Y, oc.mem = mem ∧ oc.thread.prom = t.prom ∧ t.views.vrNew ≤ ν ∧ ν ≤ oc.thread.views.vrNew ∧
      oc.thread.st = goto t.st { t.st.st.1 with regs := t.st.st.1.regs.set64 .rax x, status := S } (pcA 4) ∧
      oc.thread.rview = (t.rview.setIfInBounds 16 X).setIfInBounds 0 ν ∧
      oc.thread.wview = (t.wview.setIfInBounds 16 Y).setIfInBounds 0 ν) ∨
    (oc.thread.st.st.2 = pcA 4 ∧ oc.thread.st.st.1.status.zf = true) := by
  have hat := hS.st.at (by decide) (by decide) hpc
  obtain ⟨g, hg, hz, hex'⟩ := exec_cmpxchg' _ hat hS.st.dl
  obtain ⟨tree, st, c', hex, hr, hfi, hm⟩ := stepOne_fi Arch.tso hs ho
  rw [hex'] at hex
  obtain rfl := Option.some.inj hex
  rw [deps_3 _ hat] at hr hfi
  simp only [runTree, show Arch.tso.rmwFence = true from rfl, ↓reduceIte, List.mem_flatMap] at hr
  obtain ⟨⟨tr, old, c1⟩, hx, h⟩ := hr
  by_cases e : BitVec.setWidth 32 old = eax t.st.st.1
  · right
    simp only [e, ↓reduceIte, List.mem_flatMap] at h
    obtain ⟨c2, -, h⟩ := h
    simp only [List.mem_singleton, Except.ok.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rw [finishInstr_st hfi]
    exact ⟨rfl, (hz old).mpr e⟩
  · left
    simp only [e, ↓reduceIte, List.mem_singleton, Except.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨tr', v', hxe, -, -, -, -⟩ := (mem_readSuccs Arch.tso).mp hx
    simp only [Prod.mk.injEq] at hxe
    obtain ⟨rfl, rfl, rfl⟩ := hxe
    obtain ⟨x, S, hgx⟩ := hg old
    have hoc := finishInstr_defload rfl rfl rfl rfl rfl rfl (by rw [fenceStep_loadViews, readNext_loadViews]; rfl) hfi
    refine ⟨_, x, S, _, _, by rw [hm]; rfl, by rw [hoc]; rfl, ?_, ?_, by rw [hoc, hgx]; rfl,
      by rw [hoc]; simp only [Thread.setRegView, Array.set!_eq_setIfInBounds]; rfl,
      by rw [hoc]; simp only [Thread.setRegView, Array.set!_eq_setIfInBounds]; rfl⟩
    · simp only [readPre, fenceStep]; omega_t
    · rw [hoc]; simp only [Thread.setRegView, readNext, fenceStep, Bool.false_eq_true, ↓reduceIte]; omega_t

end Steps

/-! ## The potential along the loop -/

section Pot

variable {n : Nat} {pr h0 h1 b b' : Bool}

omit layout hv

theorem Φ_1 (h : n ≤ Φ 2 pr h0 h1 b) : n + 1 ≤ Φ 1 pr h0 h1 b' := by
  cases pr <;> cases h0 <;> cases h1 <;> cases b <;> simp [Φ, F3, P1, P3, unseen] at h ⊢ <;> omega

theorem Φ_2 (h : n ≤ Φ 3 pr h0 h1 b) : n + 1 ≤ Φ 2 pr h0 h1 b := by
  simp only [Φ] at h ⊢; omega

theorem Φ_3 (hc : (pr && (if b then h1 else h0)) = false)
    (h : n ≤ Φ 4 true (h0 || (pr && !b)) (h1 || (pr && b)) b') : n + 1 ≤ Φ 3 pr h0 h1 b := by
  cases pr <;> cases h0 <;> cases h1 <;> cases b <;> simp [Φ, F3, P3, P4, unseen] at hc h ⊢ <;> omega

theorem Φ_3s (hc : (pr && (if b then h1 else h0)) = false) (h : n ≤ 6) : n + 1 ≤ Φ 3 pr h0 h1 b := by
  cases pr <;> cases h0 <;> cases h1 <;> cases b <;> simp [Φ, F3, P3, unseen] at hc ⊢ <;> omega

theorem Φ_4 (h : n ≤ Φ 1 pr h0 h1 b') : n + 1 ≤ Φ 4 pr h0 h1 b := by
  cases pr <;> cases h0 <;> cases h1 <;> simp [Φ, P1, P4, unseen] at h ⊢ <;> omega

theorem Φ_4s (h : n ≤ 5) : n + 1 ≤ Φ 4 pr h0 h1 b := by
  cases pr <;> cases h0 <;> cases h1 <;> simp [Φ, P4, unseen] <;> omega

end Pot

/-! ## The loop: a long run has a repetition -/

section Loop

variable {s0 : Thread isa} {mem : Memory}

/-- **The cut at a second flagged `lock cmpxchg` state with the same `AF`**:
`q` (reached in `a₁` steps) dominates the current `t`. -/
theorem cut_3 {a₁ n : Nat} {q t : Thread isa} {r : Thread isa × Memory} {νq νt : View}
    (hq : ThreadNPn Arch.tso tid a₁ (s0, mem) (q, mem)) (hqi : LInv s0 q) (hqp : PR s0 3 νq q)
    (ht : LInv s0 t) (htp : PR s0 3 νt t) (haf : q.st.st.1.status.af = t.st.st.1.status.af)
    (hg : q.views.Grow t.views) (hν : q.views.vrNew ≤ νt)
    (hrun : ThreadNPn Arch.tso tid n (t, mem) r) (hp : r.1.prom = []) :
    ∃ m, m ≤ a₁ + n ∧ CertOkN Arch.tso tid s0 mem m := by
  have hνq : νq ≤ νt := Nat.le_trans hqp.le hν
  have hd : q.Dom t := ⟨(hqp.st3 rfl).trans (haf ▸ (htp.st3 rfl).symm), hqi.rv.arrLe ht.rv hνq hqp.rv htp.rv,
    hqi.wv.arrLe ht.wv hνq hqp.wv htp.wv, hg.dom (hqi.fwd.trans ht.fwd.symm) (hqi.xclb.trans ht.xclb.symm),
    hqi.prom.trans ht.prom.symm⟩
  obtain ⟨r', hr', hdr, -⟩ := hrun.dom (q, mem) hd rfl
  exact ⟨a₁ + n, Nat.le_refl _, r'.1, r'.2, hq.trans hr', hdr.prom.trans hp⟩

theorem W3.grow {a : Nat} {b : Bool} {ν : View} {t t' : Thread isa} (h : W3 tid s0 mem a b ν t)
    (hg : t.views.Grow t'.views) : W3 tid s0 mem (a + 1) b ν t' :=
  let ⟨q, a₁, νq, ha, hq, hqi, hqp, hqb, hgq, hν⟩ := h
  ⟨q, a₁, νq, by omega, hq, hqi, hqp, hqb, hgq.trans hg, hν⟩

theorem W3.read {a : Nat} {b : Bool} {ν ν' : View} {t t' : Thread isa} (h : W3 tid s0 mem a b ν t)
    (hg : t.views.Grow t'.views) (hν : t.views.vrNew ≤ ν') : W3 tid s0 mem (a + 1) b ν' t' :=
  let ⟨q, a₁, νq, ha, hq, hqi, hqp, hqb, hgq, _⟩ := h
  ⟨q, a₁, νq, by omega, hq, hqi, hqp, hqb, hgq.trans hg, Nat.le_trans hgq.vrNew hν⟩

/-- **A write-free loop run is bounded by `Φ`, or a shorter certification
exists**: induction along the run, carrying the prefix length `a`, whether a
failed read was seen (`pr`, with its post-view `ν`) and the witnesses of the
flagged visits. -/
theorem loop_bound : ∀ (n : Nat) (p r : Thread isa × Memory), ThreadRun Arch.tso tid n p r → r.1.prom = [] →
    p.2 = mem → ∀ (a : Nat) (pr h0 h1 : Bool) (ν : View), ThreadNPn Arch.tso tid a (s0, mem) p → LInv s0 p.1 →
    (pr = true → ∀ i ∈ [1, 2, 3, 4], p.1.st.st.2 = pcA i → PR s0 i ν p.1) →
    (h0 = true → W3 tid s0 mem a false ν p.1) → (h1 = true → W3 tid s0 mem a true ν p.1) →
    (∀ i ∈ [1, 2, 3, 4], p.1.st.st.2 = pcA i → n ≤ Φ i pr h0 h1 p.1.st.st.1.status.af) ∨
      ∃ m, m < a + n ∧ CertOkN Arch.tso tid s0 mem m := by
  intro n p r h
  induction h with
  | refl p => intro _ _ _ _ _ _ _ _ _ _ _ _; exact .inl fun _ _ _ => Nat.zero_le _
  | @step n p q r hs rest ih =>
    intro hp hpm a pr h0 h1 ν hpre hI hPR hW0 hW1
    obtain ⟨t, mem'⟩ := p
    simp only at hpm hI hPR hW0 hW1 hpre
    subst mem'
    obtain ⟨outs, oc, hs, ho, rfl⟩ := hs
    obtain ⟨i, hi, hpc⟩ := hI.pos
    have hpos : ∀ j ∈ [1, 2, 3, 4], t.st.st.2 = pcA j → j = i := fun j hj hj' =>
      addrOf_inj (by simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)
        (by simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega) (hj'.symm.trans hpc)
    have hpos' : ∀ j ∈ [1, 2, 3, 4], ∀ k, oc.thread.st.st.2 = pcA k → k ∈ [1, 2, 3, 4] → oc.thread.st.st.2 = pcA j →
        j = k := fun j hj k hk hk' hk'' =>
      addrOf_inj (by simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)
        (by simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hk' ⊢; omega) (hk''.symm.trans hk)
    obtain ⟨hS', hg, hx', hfw⟩ := step_gen hI.sinv hs ho hI.xclb
    have hpre' : ThreadNPn Arch.tso tid (a + 1) (s0, mem) (oc.thread, oc.mem) := hpre.tail ⟨outs, oc, hs, ho, rfl⟩
    have hpre'' : ∀ hm : oc.mem = mem, ThreadNPn Arch.tso tid (a + 1) (s0, mem) (oc.thread, mem) := fun hm => by
      have e : (oc.thread, mem) = (oc.thread, oc.mem) := by rw [hm]
      rw [e]; exact hpre'
    have mk : ∀ (j : Nat), j ∈ [1, 2, 3, 4] → oc.thread.st.st.2 = pcA j → oc.mem = mem →
        oc.thread.prom = t.prom → Core s0.st oc.thread.st → Agree s0.rview oc.thread.rview →
        Agree s0.wview oc.thread.wview → LInv s0 oc.thread := fun j hj hjpc hm hpr hc hr hw =>
      ⟨⟨j, hj, hjpc⟩, hS', hc, hr, hw, hI.grow.trans hg, (hfw hm hpr).trans hI.fwd, hx', hpr.trans hI.prom⟩
    obtain ⟨x0, y0, S0, pc0, hc0⟩ := hI.core
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · -- 1: `xorl %eax,%eax`
      obtain ⟨hm, b, hoc⟩ := step_1 hI.sinv hs ho hpc
      have hst : oc.thread.st = cst s0.st 0#64 y0 (xorS b) (pcA 2) := by
        rw [hoc]; show goto t.st _ _ = _; rw [hc0]; exact cst_rax _ _ _ _ _ _ _ _
      have hrv : oc.thread.rview = (t.rview.setIfInBounds 0 (inR t d1)).setIfInBounds 16 (inR t d1) := by
        rw [hoc]; simp only [Thread.setRegView, Array.set!_eq_setIfInBounds]; rfl
      have hwv : oc.thread.wview = (t.wview.setIfInBounds 0 (inW t d1)).setIfInBounds 16 (inW t d1) := by
        rw [hoc]; simp only [Thread.setRegView, Array.set!_eq_setIfInBounds]; rfl
      have hvs : oc.thread.views = t.views := by rw [hoc]; rfl
      have hI' : LInv s0 oc.thread := mk 2 (by decide) (by rw [hst]) hm (by rw [hoc]; rfl) ⟨_, _, _, _, hst⟩
        (hrv ▸ (hI.rv.set (.inl rfl) _).set (.inr (.inr rfl)) _)
        (hwv ▸ (hI.wv.set (.inl rfl) _).set (.inr (.inr rfl)) _)
      have hPR' : pr = true → ∀ j ∈ [1, 2, 3, 4], oc.thread.st.st.2 = pcA j → PR s0 j ν oc.thread := by
        intro hpr j hj hj'
        obtain rfl := hpos' j hj 2 (by rw [hst]) (by decide) hj'
        have h1 := hPR hpr 1 (by decide) hpc
        exact ⟨hvs ▸ h1.le, hrv ▸ h1.rv.xor (inR_d1 t), hwv ▸ h1.wv.xor (inW_d1 t), fun _ => ⟨y0, b, hst⟩,
          fun h => absurd h (by decide)⟩
      rcases ih hp hm (a + 1) pr h0 h1 ν hpre' hI' hPR' (fun h => (hW0 h).grow hg) (fun h => (hW1 h).grow hg) with
        hb | ⟨m, hm', hc⟩
      · refine .inl fun j hj hj' => ?_
        obtain rfl := hpos j hj hj'
        exact Φ_1 (hb 2 (by decide) (by rw [hst]))
      · exact .inr ⟨m, by omega, hc⟩
    · -- 2: `movl $1,%ecx`
      obtain ⟨hm, hoc⟩ := step_2 hI.sinv hs ho hpc
      have hst' : oc.thread.st = goto t.st { t.st.st.1 with regs := t.st.st.1.regs.set64 .rcx 1#64 } (pcA 3) := by
        rw [hoc]; rfl
      have hst : oc.thread.st = cst s0.st x0 1#64 S0 (pcA 3) := by
        rw [hst', hc0]; exact cst_rcx _ _ _ _ _ _ _
      have hrv : oc.thread.rview = t.rview.setIfInBounds 2 (max (max 0 0) 0) := by
        rw [hoc]; simp only [Thread.setRegView, Array.set!_eq_setIfInBounds]; rfl
      have hwv : oc.thread.wview = t.wview.setIfInBounds 2 (max (max 0 0) 0) := by
        rw [hoc]; simp only [Thread.setRegView, Array.set!_eq_setIfInBounds]; rfl
      have hvs : oc.thread.views = t.views := by rw [hoc]; rfl
      have haf : oc.thread.st.st.1.status.af = t.st.st.1.status.af :=
        (congrArg (fun s : State => s.st.1.status.af) hst').trans rfl
      have hI' : LInv s0 oc.thread := mk 3 (by decide) (by rw [hst]) hm (by rw [hoc]; rfl) ⟨_, _, _, _, hst⟩
        (hrv ▸ hI.rv.set (.inr (.inl rfl)) _) (hwv ▸ hI.wv.set (.inr (.inl rfl)) _)
      have hPR' : pr = true → ∀ j ∈ [1, 2, 3, 4], oc.thread.st.st.2 = pcA j → PR s0 j ν oc.thread := by
        intro hpr j hj hj'
        obtain rfl := hpos' j hj 3 (by rw [hst]) (by decide) hj'
        have h2 := hPR hpr 2 (by decide) hpc
        obtain ⟨y, b, hb⟩ := h2.st2 rfl
        refine ⟨hvs ▸ h2.le, hrv ▸ h2.rv.movc rfl, hwv ▸ h2.wv.movc rfl, fun h => absurd h (by decide), fun _ => ?_⟩
        have e : oc.thread.st = st3 s0.st b := by rw [hst', hb]; exact cst_rcx _ _ _ _ _ _ _
        rw [e]; rfl
      rcases ih hp hm (a + 1) pr h0 h1 ν hpre' hI' hPR' (fun h => (hW0 h).grow hg) (fun h => (hW1 h).grow hg) with
        hb | ⟨m, hm', hc⟩
      · refine .inl fun j hj hj' => ?_
        obtain rfl := hpos j hj hj'
        have := hb 3 (by decide) (by rw [hst])
        rw [haf] at this
        exact Φ_2 this
      · exact .inr ⟨m, by omega, hc⟩
    · -- 3: `lock cmpxchgl`
      by_cases hcut : (pr && (if t.st.st.1.status.af then h1 else h0)) = true
      · -- a repeated flagged visit: cut
        simp only [Bool.and_eq_true] at hcut
        obtain ⟨hpr, hseen⟩ := hcut
        have htp := hPR hpr 3 (by decide) hpc
        obtain ⟨q, a₁, νq, ha, hq, hqi, hqp, hqb, hgq, hν⟩ : W3 tid s0 mem a t.st.st.1.status.af ν t := by
          revert hseen; cases t.st.st.1.status.af <;> intro hseen
          · exact hW0 hseen
          · exact hW1 hseen
        obtain ⟨m, hm', hc⟩ := cut_3 hq hqi hqp hI htp hqb hgq hν (ThreadRun.step ⟨outs, oc, hs, ho, rfl⟩ rest).toNPn hp
        exact .inr ⟨m, by omega, hc⟩
      have hcut' : (pr && (if t.st.st.1.status.af then h1 else h0)) = false := by simpa using hcut
      rcases step_3 hI.sinv hs ho hpc with ⟨ν', x, S, X, Y, hm, hpr, hle1, hle2, hst', hrv, hwv⟩ | ⟨hpc4, hz⟩
      · -- failing: to `jne` with `ZF` clear, after a read
        have hst : oc.thread.st = cst s0.st x y0 S (pcA 4) := by
          rw [hst', hc0]; exact cst_rax _ _ _ _ _ _ _ _
        have hI' : LInv s0 oc.thread := mk 4 (by decide) (by rw [hst]) hm hpr ⟨_, _, _, _, hst⟩
          (hrv ▸ (hI.rv.set (.inr (.inr rfl)) _).set (.inl rfl) _)
          (hwv ▸ (hI.wv.set (.inr (.inr rfl)) _).set (.inl rfl) _)
        have hPR' : true = true → ∀ j ∈ [1, 2, 3, 4], oc.thread.st.st.2 = pcA j → PR s0 j ν' oc.thread := by
          intro _ j hj hj'
          obtain rfl := hpos' j hj 4 (by rw [hst]) (by decide) hj'
          exact ⟨hle2, hrv ▸ PRA.fail _ _ _, hwv ▸ PRA.fail _ _ _, fun h => absurd h (by decide),
            fun h => absurd h (by decide)⟩
        -- the new witness: `t` itself, if flagged
        have hnew : ∀ b : Bool, pr = true → t.st.st.1.status.af = b → W3 tid s0 mem (a + 1) b ν' oc.thread :=
          fun b hpr hb => ⟨t, a, ν, Nat.lt_succ_self _, hpre, hI, hPR hpr 3 (by decide) hpc, hb, hg, hle1⟩
        have hW0' : (h0 || (pr && !t.st.st.1.status.af)) = true → W3 tid s0 mem (a + 1) false ν' oc.thread := by
          intro h
          by_cases e : h0 = true
          · exact (hW0 e).read hg hle1
          · simp only [e, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at h
            exact hnew false h.1 h.2
        have hW1' : (h1 || (pr && t.st.st.1.status.af)) = true → W3 tid s0 mem (a + 1) true ν' oc.thread := by
          intro h
          by_cases e : h1 = true
          · exact (hW1 e).read hg hle1
          · simp only [e, Bool.false_or, Bool.and_eq_true] at h
            exact hnew true h.1 h.2
        rcases ih hp hm (a + 1) true _ _ ν' hpre' hI' hPR' hW0' hW1' with hb | ⟨m, hm', hc⟩
        · refine .inl fun j hj hj' => ?_
          obtain rfl := hpos j hj hj'
          exact Φ_3 hcut' (hb 4 (by decide) (by rw [hst]))
        · exact .inr ⟨m, by omega, hc⟩
      · -- succeeding: the tail
        have := tail_bound n _ r rest hS' 4 (by decide) hpc4 (fun _ => hz)
        refine .inl fun j hj hj' => ?_
        obtain rfl := hpos j hj hj'
        exact Φ_3s hcut' this
    · -- 4: `jne`
      obtain ⟨hm, hst', hpr, -⟩ := s4 hI.sinv.st hs ho hpc
      obtain ⟨hrv, hwv⟩ := step_4 hI.sinv hs ho hpc
      by_cases hz : t.st.st.1.status.zf = true
      · rw [ite_eq_left hz] at hst'
        have := tail_bound n _ r rest hS' 5 (by decide) (by rw [hst']) (fun h => absurd h (by decide))
        refine .inl fun j hj hj' => ?_
        obtain rfl := hpos j hj hj'
        exact Φ_4s this
      · rw [ite_eq_right (by simpa using hz)] at hst'
        have hst : oc.thread.st = cst s0.st x0 y0 S0 (pcA 1) := by
          rw [hst', hc0]
        have hI' : LInv s0 oc.thread := mk 1 (by decide) (by rw [hst]) hm hpr ⟨_, _, _, _, hst⟩
          (hrv ▸ hI.rv) (hwv ▸ hI.wv)
        have hPR' : pr = true → ∀ j ∈ [1, 2, 3, 4], oc.thread.st.st.2 = pcA j → PR s0 j ν oc.thread := by
          intro hpr' j hj hj'
          obtain rfl := hpos' j hj 1 (by rw [hst]) (by decide) hj'
          have h4 := hPR hpr' 4 (by decide) hpc
          exact ⟨Nat.le_trans h4.le hg.vrNew, hrv ▸ h4.rv.jne, hwv ▸ h4.wv.jne, fun h => absurd h (by decide),
            fun h => absurd h (by decide)⟩
        rcases ih hp hm (a + 1) pr h0 h1 ν hpre' hI' hPR' (fun h => (hW0 h).grow hg) (fun h => (hW1 h).grow hg)
          with hb | ⟨m, hm', hc⟩
        · refine .inl fun j hj hj' => ?_
          obtain rfl := hpos j hj hj'
          exact Φ_4 (hb 1 (by decide) (by rw [hst]))
        · exact .inr ⟨m, by omega, hc⟩

end Loop

/-! ## The bound -/

/-- `LInv` of a loop state relative to itself. -/
theorem linv_self {t : Thread isa} (hS : SInv t.st) (hx : t.views.xclb = none) {i : Nat}
    (hi : i ∈ [1, 2, 3, 4]) (hpc : t.st.st.2 = pcA i) : LInv t t :=
  ⟨⟨i, hi, hpc⟩, hS, Core.self _, ⟨rfl, fun _ _ _ _ => rfl⟩, ⟨rfl, fun _ _ _ _ => rfl⟩, Views.Grow.refl _, rfl, hx,
   rfl⟩

/-- **Every certification of a worker is within `18` instructions.** -/
theorem certOkN_bound {t : Thread isa} {mem : Memory} (hS : SInv t.st) (hx : t.views.xclb = none) {n : Nat}
    (h : CertOkN Arch.tso tid t mem n) : CertOkN Arch.tso tid t mem 18 := by
  refine CertOkN.bound_of_shorter 18 (fun n r hr hp hn => ?_) h
  obtain ⟨hSt, i, hi, hpc, -⟩ := id hS
  have loop : i ∈ [1, 2, 3, 4] → ∃ m, m < n ∧ CertOkN Arch.tso tid t mem m := fun hi' => by
    rcases loop_bound n (t, mem) r hr hp rfl 0 false false false 0 (.refl _ _) (linv_self hS hx hi' hpc)
        (fun h => Bool.noConfusion h) (fun h => Bool.noConfusion h) (fun h => Bool.noConfusion h) with
      hb | ⟨m, hm, hc⟩
    · exact absurd (hb i hi' hpc) (Nat.not_le_of_lt (Nat.lt_of_le_of_lt (Φ_le i _) hn))
    · exact ⟨m, by omega, hc⟩
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  iterate 4 exact loop (by decide)
  all_goals
    exact absurd (tail_bound n _ r hr hS _ (by decide) hpc (fun h => absurd h (by decide))) (by simp only [Ψ]; omega)

/-! ## Reachable configurations -/

/-- No thread has a pending load exclusive (none of the worker's cells
performs one). -/
def XclbNone (cfg : Config isa) : Prop := ∀ (i : Nat) u, cfg.threads[i]? = some u → u.views.xclb = none

theorem xclbNone_step {fuel : Nat} {cfg cfg' : Config isa} (hI : InvS fuel cfg) (h : XclbNone cfg) {tid : Nat}
    (hst : StepSem Arch.tso fuel tid cfg cfg') : XclbNone cfg' := by
  rcases hst with ⟨t, outs, oc, ht, hs, ho, -, rfl⟩ | ⟨t, w, ht, -, -, rfl⟩
  · intro i u hu
    rcases wt_get ht hu with ⟨rfl, rfl⟩ | ⟨-, hu⟩
    · have hS := (hI.thr _ t ht).sinv
      exact stepOne_xclb_none Arch.tso (stepOne_fi Arch.tso hs ho).choose_spec.choose_spec.choose_spec.1
        (noXcl hS _ (stepOne_fi Arch.tso hs ho).choose_spec.choose_spec.choose_spec.1) hs ho (h _ t ht)
    · exact h i u hu
  · intro i u hu
    rcases wt_get ht hu with ⟨rfl, rfl⟩ | ⟨-, hu⟩
    · exact h _ t ht
    · exact h i u hu

theorem xclbNone_init (states : List isa.State) (initMem : List (Loc × Val)) :
    XclbNone (Config.init states initMem) := by
  intro i u hu
  simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at hu
  obtain ⟨s, -, rfl⟩ := hu
  rfl

/-- **Bounded certification from every start configuration**: `F = 18`. -/
theorem cmpx_certBounded {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : SpinX64.CmpxStart states initMem) : CertBoundedFrom Arch.tso (Config.init states initMem) 18 := by
  intro fuel cfg hr tid t n ht hc
  have hinv := NoStuck.reachableSem_inv (fun cfg => InvS fuel cfg ∧ XclbNone cfg)
    (fun tid cfg cfg' ⟨hI, hX⟩ hst => by
      obtain ⟨t, ht⟩ : ∃ t, cfg.threads[tid]? = some t := by
        rcases hst with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact ⟨t, ht⟩
      exact ⟨inv_step hI ht hst, xclbNone_step hI hX hst⟩) hr ⟨inv_init hs, xclbNone_init _ _⟩
  exact certOkN_bound (hinv.1.thr tid t ht).sinv (hinv.2 tid t ht) hc

/-! ## The fuel-free theorems -/

/-- `SpinX64Sem.CmpxSpinLiveSem` on the fuel-free semantic machine. -/
def CmpxSpinLiveSemU : Prop :=
  ∀ states initMem, SpinX64.CmpxStart states initMem →
    ProgressFromSemU Arch.tso (Config.init states initMem)
      (fun cfg => WeakFairSemU Arch.tso cfg ∧ MemFair Arch.tso cfg) SpinX64.CmpxWaiting SpinX64.CmpxDone

/-- `SpinX64Sem.CmpxSpinLiveOneShotSem` on the fuel-free semantic machine. -/
def CmpxSpinLiveOneShotSemU : Prop :=
  ∀ states initMem, SpinX64.CmpxStart states initMem →
    LiveFromSemU Arch.tso (Config.init states initMem)
      (fun cfg => WeakFairSemU Arch.tso cfg ∧ MemFair Arch.tso cfg) SpinX64.CmpxWaiting SpinX64.CmpxDone

/-- **Deadlock-freedom of the x64 `lock cmpxchg` spinlock, fuel-free**
(semantic machine, `MemFair` a modelling assumption on x86):
`spin_cmpx_live_sem` at fuel `18` through `progressTransfer`. -/
theorem spin_cmpx_live_semU : CmpxSpinLiveSemU := fun states initMem hs =>
  progressTransfer (cmpx_certBounded hs) (SpinX64SemCmpx.spin_cmpx_live_sem 18 states initMem hs)

/-- **Per-thread liveness of the one-shot x64 `lock cmpxchg` workers,
fuel-free.** A property of these one-shot programs, not starvation-freedom
of the lock. -/
theorem spin_cmpx_live_oneShot_semU : CmpxSpinLiveOneShotSemU := fun states initMem hs =>
  liveTransfer (cmpx_certBounded hs) (SpinX64SemCmpx.spin_cmpx_live_oneShot_sem 18 states initMem hs)

end Kraken.Promising.Live.CertBoundedSpinCmpx

namespace Kraken.Promising.Live.CertBoundedSpinCmpx

open Kraken.Promising.X64.EnvG.CmpxAbs.Concrete

/-- `spin_cmpx_live_semU` at the `.kl` runner's layout `cmpxLayoutV`: no
hypothesis left. -/
theorem spin_cmpx_live_semU_concrete : @CmpxSpinLiveSemU cmpxLayoutV :=
  @spin_cmpx_live_semU cmpxLayoutV cmpxValidV

/-- `spin_cmpx_live_oneShot_semU` at the runner's layout. -/
theorem spin_cmpx_live_oneShot_semU_concrete : @CmpxSpinLiveOneShotSemU cmpxLayoutV :=
  @spin_cmpx_live_oneShot_semU cmpxLayoutV cmpxValidV

end Kraken.Promising.Live.CertBoundedSpinCmpx
