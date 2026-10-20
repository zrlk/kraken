/-
**`msqueue2.kl` and `msqueue3.kl` never fault at the runner's declarations**
`x64_msqueue2_envG_runner_faultFree`,
`x64_msqueue3_envG_runner_faultFree` and their `_concrete` instances,
program-level `Config.FaultFree` from the runner's start states under any
architecture (promises included).

The enqueuer and the dequeuers read `(%rbx)` at a `head`/`tail` value and
write node values they read; their purity specifications sit at `sAll`.
Here every thread gets a **value specification** (`MemValsX64.ValSpecX`) at
the layout `msqS` (`head`, `tail`, the null word `0`, `s`, `n1`, `n2`), with
the value invariant

- `L` (`MsqValL`): the 8-byte words `head`, `tail` and every node word;
- `V` (`MsqValV`): the node values `0`, `s`, `n1`, `n2` (`MsqVQ`).

Every write is a `lock cmpxchgq` of `%rsi` (`n1` or `n2`) or of a `next`
the thread read, so `MemVals L V` holds at every reachable configuration and
every dereference is at a node value. The null word is in the layout: a
value invariant cannot exclude a dequeuer's `deq_pop` reading a stale `0`
`next` and swinging `head` to it (the queue invariant `head ≠ tail ⇒
head.next ≠ 0` is relational), so the proof covers a dereference of `0` too;
it is an undeclared 8-byte footprint that overlaps no declaration, at which
the runner's declarations agree (no fault). The initial memory must hold
node values at `L` (`decide` at the runner's `msq2InitMemV`,
`msq3InitMemV`).

The VC script `msq_val_cases` is shared by the four runs: `msq_vals`
collects the node values of the loads in order, `msq_addr`/`msq_vq` place
the accesses and the written values, `cnt_all` the counts.

Phase-1 limit: single-access trees (`msq2ImageV_phase1FX`,
`msq3ImageV_phase1FX`).
-/
import Kraken.Promising.SLR.EnvG.MemValsX64
import Kraken.Promising.SLR.EnvG.X64MsQueue2Runner
import Kraken.Promising.SLR.EnvG.X64MsQueue3Runner

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG

namespace Kraken.Promising.X64.EnvG.MsQueueX

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The value invariant and the case script -/

/-- A node value: `0`, the sentinel `s`, `n1` or `n2`. -/
def MsqVQ (s n1 n2 x : BitVec 64) : Prop := x = 0 ∨ x = s ∨ x = n1 ∨ x = n2
/-- The locations of the value invariant: the 8-byte words `head`, `tail` and
every node word, `0`'s included. -/
def MsqValL (h t s n1 n2 : BitVec 64) : Loc → Prop := fun l =>
  l.bytes = 8 ∧ (l.addr = h ∨ l.addr = t ∨ MsqVQ s n1 n2 l.addr)
/-- The values of the value invariant: the node values. -/
def MsqValV (s n1 n2 : BitVec 64) : Val → Prop := fun v => MsqVQ s n1 n2 (v.setWidth 64)
/-- The layout: `head`, `tail`, the null word `0` and the nodes. -/
abbrev msqS (h t s n1 n2 : BitVec 64) : SharedEnv.Layout := [(h, 8), (t, 8), (0, 8), (s, 8), (n1, 8), (n2, 8)]
/-- The threads' environment: the value environment at `msqS`. -/
abbrev msqValEnv (h t s n1 n2 : BitVec 64) : SharedEnv :=
  (SharedEnv.valEnv (MsqValL h t s n1 n2) (MsqValV s n1 n2)).within (msqS h t s n1 n2)

/-- A shared 8-byte load at a `head`, `tail` or node word returns a node
value. -/
theorem msqVal_load {h t s n1 n2 : BitVec 64} {d : DataMem} {σ : BitVec 64}
    {g g' : (SharedEnv.counted (msqValEnv h t s n1 n2)).State} {a : BitVec 64}
    (ha : a = h ∨ a = t ∨ MsqVQ s n1 n2 a) (hd8 : ∀ a, Mem.loadInt d a 8 = none)
    (hl : (∃ v, Mem.loadInt d a 8 = some v ∧ σ = BitVec.ofInt 64 v ∧ g' = g) ∨
      (Mem.loadInt d a 8 = none ∧ ∃ v, (SharedEnv.counted (msqValEnv h t s n1 n2)).step (.load .plain false a 8) g v g' ∧
        σ = v.setWidth 64)) : MsqVQ s n1 n2 σ := by
  rcases hl with ⟨w, hm, -, -⟩ | ⟨-, w, hst, rfl⟩
  · rw [hd8] at hm; cases hm
  · exact hst.1 ⟨rfl, ha⟩

/-- A `head`, `tail` or node word is in the layout. -/
theorem msqS_mem {h t s n1 n2 a : BitVec 64} (ha : a = h ∨ a = t ∨ MsqVQ s n1 n2 a) :
    (a, 8) ∈ msqS h t s n1 n2 := by
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- A `lock cmpxchgq` whose source is a node value writes a node value. -/
theorem msqVal_cmpx {s n1 n2 x y : BitVec 64} (hy : MsqVQ s n1 n2 y) :
    ∀ old new, (rmwOp128 Width.W64 fun o => if (o == x) = true then some y else none) old = some new →
      MsqValV s n1 n2 new := by
  intro old new h
  simp only [rmwOp128, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, rfl⟩ := h
  split at ha
  · cases ha
    simpa [MsqValV] using hy
  · cases ha

/-- The enqueuer's `rsi` after its entry is a node. -/
theorem msq_rsiV {s n1 n2 x : BitVec 64} {lb : Label} (hne : lb ≠ "enqueuer")
    (h : lb = "enqueuer" ∨ x = n1 ∨ x = n2) : MsqVQ s n1 n2 x := by
  rcases h with h | h | h
  · exact absurd h hne
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

open Lean Elab Tactic in
/-- Close `MsqVQ s n1 n2 x` from a `MsqVQ` hypothesis (up to `simp`). -/
scoped elab "msq_vq" : tactic => withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOf ``MsqVQ then
      let e ← Term.exprToSyntax d.toExpr
      try
        evalTactic (← `(tactic| simpa using $e))
        return
      catch _ => pure ()
  throwError "msq_vq: no hypothesis"

/-- The address of a `head`, `tail` or node-word access. -/
scoped macro "msq_addr" : tactic => `(tactic|
  first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | (refine Or.inr (Or.inr ?_); msq_vq))

open Lean Elab Tactic in
/-- The node values of the run's loads (`hd8` the `dmem` frame), in order. -/
scoped elab "msq_vals" : tactic => withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOf ``Or && (ty.find? (·.isConstOf ``SharedEnv.step)).isSome then
      let e ← Term.exprToSyntax d.toExpr
      try evalTactic (← `(tactic| have := msqVal_load (by msq_addr) $(mkIdent `hd8) $e)) catch _ => pure ()

/-- The frame at a cut: `dmem`, the enqueuer's `rsi`, `rcx` at the swing
labels. -/
scoped macro "msq_frame" : tactic => `(tactic| (
  first
    | refine ⟨fun a => by simpa using $(Lean.mkIdent `hd8) a, fun h => ?_⟩
    | refine ⟨fun a => by simpa using $(Lean.mkIdent `hd8) a, ?_, fun h => ?_⟩
      first
        | trivial
        | exact .inl rfl
        | (refine .inr ?_; first | (left; simp; done) | (right; simp; done))
        | (refine .inr ?_; rcases $(Lean.mkIdent `hrsi):ident with h | h | h <;>
            first | exact absurd h (by decide) | (left; simpa using h) | (right; simpa using h))
  all_goals first | exact absurd h (by decide) | msq_vq))

set_option hygiene false in
/-- **The value run's case script** (after `cfg_cases_env`), with `sv` the
sentinel `s`: the frame `hd8`/`hrsi`/`hrcx`, the node values of the loads
(`msq_vals`), the accesses in `msqS`, the `lock cmpxchgq`s' node values, the
cut frames and the counts (`cnt_all`). -/
scoped macro "msq_val_cases" sv:term : tactic => `(tactic| (
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals have hx : _ ∧ _ = _ ∧ _ = _ := (by with_reducible assumption)
  all_goals obtain ⟨⟨hd8, hrsi, hrcx⟩, rfl, rfl⟩ := hx
  all_goals try have hrsiV := msq_rsiV (s := $sv) (by decide) hrsi
  all_goals try have hrcxV := hrcx rfl
  all_goals try have hrcxV := hrcx trivial
  all_goals msq_vals
  all_goals first
    | exact hd8 _
    | (simpa using hd8 _)
    | (refine ⟨trivial, msqS_mem (by msq_addr)⟩)
    | (refine ⟨fun old new hop _ _ => msqVal_cmpx (by msq_vq) old new hop, msqS_mem (by msq_addr)⟩)
    | msq_frame
    | (try dsimp only
       refine Table.ofLabelsEnv_at ⟨by decide, ?_, ?_⟩
       · msq_frame
       · first | exact .inl (by decide) | exact .inr fun ⟨_, hg⟩ => by subst hg; cnt_all; omega)))


/-- Every location of `msqS` is 8 bytes wide. -/
theorem msqS_le16 (h t s n1 n2 : BitVec 64) : Le16 (msqS h t s n1 n2) := fun x hx => by
  simp only [msqS, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact (by decide : 8 ≤ 16)

/-- The initial memory of `Config.init` satisfies the value invariant when
its initial values at `L` are in `V` (no messages yet). -/
theorem memVals_init_of {L : Loc → Prop} {V : Val → Prop} {states : List isa.State} {initMem : List (Loc × Val)}
    (h : ∀ l, L l → V ((Config.init states initMem).mem.initVal l)) :
    MemVals L V (Config.init states initMem).mem :=
  ⟨h, fun ts w hg _ => by simp [Memory.get?] at hg⟩

/-! ## `msqueue2.kl` -/

section Msq2

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msq2ImageV)]

local instance msq2ImageV.envMemVals : CodeEnv := ⟨layout msq2ImageV⟩

/-- The environment at `msqueue2.kl`'s symbols. -/
abbrev msq2ValEnv : SharedEnv := msqValEnv (symV "head") (symV "tail") (symV "s") (symV "n1") (symV "n2")

set_option maxHeartbeats 1000000 in
set_option linter.unnecessarySimpa false in
/-- **The verbatim enqueuer in the value environment** (counted, partial). -/
theorem enqV_memVals :
    ∀ s g, (∀ a, Mem.loadInt s.dmem a 8 = none) →
      Safely (cenv.instrStepEnv (SharedEnv.counted msq2ValEnv))
        (fun x => (x.1.2 = labV "edone" ∧ True) ∨ False) ((s, labV "enqueuer"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted msq2ValEnv) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (fun (lb : Label) s (_ : (SharedEnv.counted msq2ValEnv).State) =>
      (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
        (lb = "enqueuer" ∨ s.regs.get64 .rsi = symV "n1" ∨ s.regs.get64 .rsi = symV "n2") ∧
        (lb = "enq_swing" → MsqVQ (symV "s") (symV "n1") (symV "n2") (s.regs.get64 .rcx)))
    ?_ rfl (by decide) enqFragV_placedIn enqFragV_last s g ⟨hs, .inl rfl, fun h => absurd h (by decide)⟩
  cfg_cases_env [enqFragV]
  msq_val_cases (symV "s")

set_option maxHeartbeats 1000000 in
set_option linter.unnecessarySimpa false in
/-- **The verbatim dequeuer in the value environment** (counted, partial). -/
theorem deqV_memVals :
    ∀ s g, (∀ a, Mem.loadInt s.dmem a 8 = none) →
      Safely (cenv.instrStepEnv (SharedEnv.counted msq2ValEnv))
        (fun x => (x.1.2 = labV "ddone" ∧ True) ∨ False) ((s, labV "dequeuer"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted msq2ValEnv) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (fun (lb : Label) s (_ : (SharedEnv.counted msq2ValEnv).State) =>
      (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ True ∧
        (lb = "deq_pop" → MsqVQ (symV "s") (symV "n1") (symV "n2") (s.regs.get64 .rcx)))
    ?_ rfl (by decide) deqFragV_placedIn deqFragV_last s g ⟨hs, trivial, fun h => absurd h (by decide)⟩
  cfg_cases_env [deqFragV]
  msq_val_cases (symV "s")

/-- The verbatim threads' value specifications (`msqueue2.kl`). -/
noncomputable def msq2ValSpec :
    Nat → ValSpecX (MsqValL (symV "head") (symV "tail") (symV "s") (symV "n1") (symV "n2"))
      (MsqValV (symV "s") (symV "n1") (symV "n2"))
  | 0 =>
    { S := msqS (symV "head") (symV "tail") (symV "s") (symV "n1") (symV "n2")
      le16 := msqS_le16 _ _ _ _ _
      e := layout msq2ImageV
      valid := inferInstance
      endPc := labV "edone"
      post := fun x => ∃ _ : Nat, (x.1.2 = labV "edone" ∧ True) ∨ False
      post_end := fun _ h => h.elim fun _ h => h.elim And.left False.elim }
  | _ + 1 =>
    { S := msqS (symV "head") (symV "tail") (symV "s") (symV "n1") (symV "n2")
      le16 := msqS_le16 _ _ _ _ _
      e := layout msq2ImageV
      valid := inferInstance
      endPc := labV "ddone"
      post := fun x => ∃ _ : Nat, (x.1.2 = labV "ddone" ∧ True) ∨ False
      post_end := fun _ h => h.elim fun _ h => h.elim And.left False.elim }

/-- **The value specifications hold at the start states with
declarations** (`msqueue2.kl`). -/
theorem msq2ValSpec_initD {ds : Decls} {s0 s1 : State} (h0 : StartEVD ds s0) (h1 : StartDVD ds s1) :
    ∀ (tid : Nat) s, [s0, s1][tid]? = some s → (msq2ValSpec tid).HoldsD ds s
  | 0, s, hs => by
    cases hs
    refine ⟨h0.exe, h0.endPc, h0.decls, fun k _ => h0.dmem k, ?_⟩
    rw [show s0.st = (s0.st.1, labV "enqueuer") from Prod.ext rfl h0.pc]
    exact TreiberAbs.Safely.uncountT (enqV_memVals _ ((), 0) (d8_of_dmem h0.dmem))
  | 1, s, hs => by
    cases hs
    refine ⟨h1.exe, h1.endPc, h1.decls, fun k _ => h1.dmem k, ?_⟩
    rw [show s1.st = (s1.st.1, labV "dequeuer") from Prod.ext rfl h1.pc]
    exact TreiberAbs.Safely.uncountT (deqV_memVals _ ((), 0) (d8_of_dmem h1.dmem))
  | _ + 2, _, hs => by cases hs

/-- **No reachable configuration of the verbatim `msqueue2` threads with the
runner's declarations has a faulting step**, for `ds` agreeing on `msqS`
and an initial memory with node values at `L`. -/
theorem x64_msqueue2_envG_runner_faultFree {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (hag : ds.AgreesOn (msqS (symV "head") (symV "tail") (symV "s") (symV "n1") (symV "n2")))
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartEVD ds s0) (h1 : StartDVD ds s1)
    (hinit : ∀ l, MsqValL (symV "head") (symV "tail") (symV "s") (symV "n1") (symV "n2") l →
      MsqValV (symV "s") (symV "n1") (symV "n2") ((Config.init [s0, s1] initMem).mem.initVal l)) :
    Config.FaultFree A fuel (Config.init [s0, s1] initMem) :=
  x64_faultFree_of_valSpecs msq2ValSpec (fun _ => ds) (fun _ => hsz)
    (fun tid => by rcases tid with _ | _ <;> exact hag)
    (fun tid => by rcases tid with _ | _ <;> exact msq2ImageV_noFaultCode)
    (fun tid => by rcases tid with _ | _ <;> exact rootOnlyD_of_phase1TreeFX msq2ImageV_phase1FX)
    (memVals_init_of hinit) (init_threads_of (msq2ValSpec_initD h0 h1))

end Msq2

/-! ## `msqueue3.kl` -/

section Msq3

open Kraken.Promising.X64.EnvG.MsQueue3X

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msq3ImageV)]

local instance msq3ImageV.envMemVals : CodeEnv := ⟨layout msq3ImageV⟩

/-- The environment at `msqueue3.kl`'s symbols. -/
abbrev msq3ValEnv : SharedEnv := msqValEnv (symV3 "head") (symV3 "tail") (symV3 "s") (symV3 "n1") (symV3 "n2")

set_option maxHeartbeats 1000000 in
set_option linter.unnecessarySimpa false in
/-- **The verbatim enqueuer in the value environment** (counted, partial). -/
theorem enq3V_memVals :
    ∀ s g, (∀ a, Mem.loadInt s.dmem a 8 = none) →
      Safely (cenv.instrStepEnv (SharedEnv.counted msq3ValEnv))
        (fun x => (x.1.2 = labV3 "edone" ∧ True) ∨ False) ((s, labV3 "enqueuer"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted msq3ValEnv) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (fun (lb : Label) s (_ : (SharedEnv.counted msq3ValEnv).State) =>
      (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
        (lb = "enqueuer" ∨ s.regs.get64 .rsi = symV3 "n1" ∨ s.regs.get64 .rsi = symV3 "n2") ∧
        (lb = "enq_swing" → MsqVQ (symV3 "s") (symV3 "n1") (symV3 "n2") (s.regs.get64 .rcx)))
    ?_ rfl (by decide) enqFragV3_placedIn enqFragV3_last s g ⟨hs, .inl rfl, fun h => absurd h (by decide)⟩
  cfg_cases_env [enqFragV]
  msq_val_cases (symV3 "s")

set_option maxHeartbeats 1000000 in
set_option linter.unnecessarySimpa false in
/-- **The verbatim dequeuer in the value environment** (counted, partial). -/
theorem deq3V_memVals :
    ∀ s g, (∀ a, Mem.loadInt s.dmem a 8 = none) →
      Safely (cenv.instrStepEnv (SharedEnv.counted msq3ValEnv))
        (fun x => (x.1.2 = labV3 "ddone" ∧ True) ∨ False) ((s, labV3 "dequeuer"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted msq3ValEnv) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (fun (lb : Label) s (_ : (SharedEnv.counted msq3ValEnv).State) =>
      (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ True ∧
        (lb = "deq_pop" → MsqVQ (symV3 "s") (symV3 "n1") (symV3 "n2") (s.regs.get64 .rcx)))
    ?_ rfl (by decide) deqFragV3_placedIn deqFragV3_last s g ⟨hs, trivial, fun h => absurd h (by decide)⟩
  cfg_cases_env [deqFragV3]
  msq_val_cases (symV3 "s")

/-- The verbatim threads' value specifications (`msqueue3.kl`). -/
noncomputable def msq3ValSpec :
    Nat → ValSpecX (MsqValL (symV3 "head") (symV3 "tail") (symV3 "s") (symV3 "n1") (symV3 "n2"))
      (MsqValV (symV3 "s") (symV3 "n1") (symV3 "n2"))
  | 0 =>
    { S := msqS (symV3 "head") (symV3 "tail") (symV3 "s") (symV3 "n1") (symV3 "n2")
      le16 := msqS_le16 _ _ _ _ _
      e := layout msq3ImageV
      valid := inferInstance
      endPc := labV3 "edone"
      post := fun x => ∃ _ : Nat, (x.1.2 = labV3 "edone" ∧ True) ∨ False
      post_end := fun _ h => h.elim fun _ h => h.elim And.left False.elim }
  | _ + 1 =>
    { S := msqS (symV3 "head") (symV3 "tail") (symV3 "s") (symV3 "n1") (symV3 "n2")
      le16 := msqS_le16 _ _ _ _ _
      e := layout msq3ImageV
      valid := inferInstance
      endPc := labV3 "ddone"
      post := fun x => ∃ _ : Nat, (x.1.2 = labV3 "ddone" ∧ True) ∨ False
      post_end := fun _ h => h.elim fun _ h => h.elim And.left False.elim }

/-- **The value specifications hold at the start states with
declarations** (`msqueue3.kl`). -/
theorem msq3ValSpec_initD {ds : Decls} {s0 s1 s2 : State} (h0 : StartEV3D ds s0) (h1 : StartDV3D ds s1)
    (h2 : StartDV3D ds s2) : ∀ (tid : Nat) s, [s0, s1, s2][tid]? = some s → (msq3ValSpec tid).HoldsD ds s
  | 0, s, hs => by
    cases hs
    refine ⟨h0.exe, h0.endPc, h0.decls, fun k _ => h0.dmem k, ?_⟩
    rw [show s0.st = (s0.st.1, labV3 "enqueuer") from Prod.ext rfl h0.pc]
    exact TreiberAbs.Safely.uncountT (enq3V_memVals _ ((), 0) (d8_of_dmem h0.dmem))
  | 1, s, hs => by
    cases hs
    refine ⟨h1.exe, h1.endPc, h1.decls, fun k _ => h1.dmem k, ?_⟩
    rw [show s1.st = (s1.st.1, labV3 "dequeuer") from Prod.ext rfl h1.pc]
    exact TreiberAbs.Safely.uncountT (deq3V_memVals _ ((), 0) (d8_of_dmem h1.dmem))
  | 2, s, hs => by
    cases hs
    refine ⟨h2.exe, h2.endPc, h2.decls, fun k _ => h2.dmem k, ?_⟩
    rw [show s2.st = (s2.st.1, labV3 "dequeuer") from Prod.ext rfl h2.pc]
    exact TreiberAbs.Safely.uncountT (deq3V_memVals _ ((), 0) (d8_of_dmem h2.dmem))
  | _ + 3, _, hs => by cases hs

/-- **No reachable configuration of the verbatim `msqueue3` threads with the
runner's declarations has a faulting step**, for `ds` agreeing on `msqS`
and an initial memory with node values at `L`. -/
theorem x64_msqueue3_envG_runner_faultFree {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (hag : ds.AgreesOn (msqS (symV3 "head") (symV3 "tail") (symV3 "s") (symV3 "n1") (symV3 "n2")))
    {s0 s1 s2 : isa.State} {initMem : List (Loc × Val)} (h0 : StartEV3D ds s0) (h1 : StartDV3D ds s1)
    (h2 : StartDV3D ds s2)
    (hinit : ∀ l, MsqValL (symV3 "head") (symV3 "tail") (symV3 "s") (symV3 "n1") (symV3 "n2") l →
      MsqValV (symV3 "s") (symV3 "n1") (symV3 "n2") ((Config.init [s0, s1, s2] initMem).mem.initVal l)) :
    Config.FaultFree A fuel (Config.init [s0, s1, s2] initMem) :=
  x64_faultFree_of_valSpecs msq3ValSpec (fun _ => ds) (fun _ => hsz)
    (fun tid => by rcases tid with _ | _ <;> exact hag)
    (fun tid => by rcases tid with _ | _ <;> exact msq3ImageV_noFaultCode)
    (fun tid => by rcases tid with _ | _ <;> exact rootOnlyD_of_phase1TreeFX msq3ImageV_phase1FX)
    (memVals_init_of hinit) (init_threads_of (msq3ValSpec_initD h0 h1 h2))

end Msq3

end Kraken.Promising.X64.EnvG.MsQueueX

namespace Kraken.Promising.X64.EnvG.MsQueueX.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG Kraken.Promising.SLR.EnvG

section
attribute [local instance] msq2LayoutV

/-- **`msqueue2.kl` never faults**, from the runner's exact configuration
(threads `msq2P0D`, `msq2P1D` with the runner's declarations, initial memory
`msq2InitMemV`). -/
theorem x64_msqueue2_envG_runner_faultFree_concrete {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init [msq2P0D, msq2P1D] msq2InitMemV) :=
  x64_msqueue2_envG_runner_faultFree msq2DeclsD_sized
    (by rw [symV_head, symV_tail, symV_s, symV_n1, symV_n2]; decls_agrees_on) msq2P0D_start msq2P1D_start
    (by
      rintro ⟨a, b⟩ ⟨hb, ha⟩
      simp only at hb ha; subst hb
      rw [symV_head, symV_tail, symV_s, symV_n1, symV_n2] at ha
      rw [symV_s, symV_n1, symV_n2]
      simp only [MsqVQ] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [MsqValV, MsqVQ, Config.init_mem] <;> decide)

end

end Kraken.Promising.X64.EnvG.MsQueueX.Concrete

namespace Kraken.Promising.X64.EnvG.MsQueue3X.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG.MsQueueX

section
attribute [local instance] msq3LayoutV

/-- **`msqueue3.kl` never faults**, from the runner's exact configuration
(threads `msq3P0D`, `msq3PDD`, `msq3PDD` with the runner's declarations,
initial memory `msq3InitMemV`). -/
theorem x64_msqueue3_envG_runner_faultFree_concrete {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init [msq3P0D, msq3PDD, msq3PDD] msq3InitMemV) :=
  x64_msqueue3_envG_runner_faultFree msq3DeclsD_sized
    (by rw [symV3_head, symV3_tail, symV3_s, symV3_n1, symV3_n2]; decls_agrees_on) msq3P0D_start msq3PDD_start
    msq3PDD_start
    (by
      rintro ⟨a, b⟩ ⟨hb, ha⟩
      simp only at hb ha; subst hb
      rw [symV3_head, symV3_tail, symV3_s, symV3_n1, symV3_n2] at ha
      rw [symV3_s, symV3_n1, symV3_n2]
      simp only [MsqVQ] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [MsqValV, MsqVQ, Config.init_mem] <;> decide)

end

end Kraken.Promising.X64.EnvG.MsQueue3X.Concrete

#print axioms Kraken.Promising.X64.EnvG.MsQueueX.x64_msqueue2_envG_runner_faultFree
#print axioms Kraken.Promising.X64.EnvG.MsQueueX.x64_msqueue3_envG_runner_faultFree
#print axioms Kraken.Promising.X64.EnvG.MsQueueX.Concrete.x64_msqueue2_envG_runner_faultFree_concrete
#print axioms Kraken.Promising.X64.EnvG.MsQueue3X.Concrete.x64_msqueue3_envG_runner_faultFree_concrete
