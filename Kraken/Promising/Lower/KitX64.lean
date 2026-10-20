/-
**The x64 lowering assembly kit** (the `Arch.tso` twin
of the lowering kit's AArch64 kit `Lower/Kit.lean`). ISA: x64
(`isa`); machine: the executable Promising machine (`Reachable Arch.tso`),
through Theorem 1′ for `NPSafeF` (`theorem1FChain`, via
`CmpxPublic.final_of_relPureSafelyQX_tsoF'`).

Per thread, on one shared layout `S` (`Le16 S`):

- `LowerCoreX`: what both variants share: the laid-out image `e`, the plan,
  `Phase1TreeFX`, the entry and end addresses, no step at the end in any
  environment, the counted post `Q` (at the end) read as the shared
  postcondition `B` (`hB`), and the all-release purity judgment `pure` of the
  thread in counted `(relPureQ Arch.tso ⊥).within S` (gives `NTFree` and
  purity, `RelPureSpecQX`).
- `LowerThreadX` (frameless): `LowerCoreX` and `main`, a `Safely` judgment
  of the thread from its entry in counted `EnvGCAdjX Arch.tso tid pl S`.
  **`lower_promising_x64`**: per-thread `LowerThreadX`s at their `Start`s and
  a final reading `hfin` give `Φ c` for every final `c` reachable under
  `Arch.tso`.
- `LowerThreadXV` (frame + value bridge): `main` in counted
  `EnvGCAdjXV Arch.tso tid pl S G` and the value judgment `vals` in counted
  `inv S G`. **`lower_promising_x64_vals`**: the same conclusion from
  `MemInv G` of the initial memory in addition (`Vals.envGValsBridgeX_ofSpecs`).

**Deviation from the AArch64 kit's shape.** The AArch64 kit takes each
judgment as a `PartialTripleEnv` of a whole text `p` under a layout `l`, so
the thread starts at `(l p).addrOf 0` and ends at `(l p).addrOf p.length`.
Here every judgment is a `Safely` judgment of the laid-out image `e` from an
entry address `entry`, with an end address `endPc` and a counted post `Q`
holding only at `endPc`. This is a generalisation: it covers images run from
a label of a larger image (the `.kl` runners, e.g. `x64_treiber2_envG_verbatim`,
whose worker starts at `worker` and ends at `done` before the data trailer)
as well as whole texts; `safely_of_partialTripleEnvX` turns a whole-text
partial triple into the kit's form (`entry := (layout p).addrOf 0`,
`endPc := (layout p).addrOf p.length`, `Q` the triple's post at the end).
The same generalisation would let the AArch64 kit take runner images
(not done; `Kit.lean` is unchanged).

**Scope of the purity judgment.** `pure` is the unrestricted x64
all-release judgment: every shared access of the thread is an `S`-access
admitted by `(relPureQ Arch.tso ⊥).within S`. The x64 pilot found the matching
judgment false for a program whose pop loads through a pointer read from
shared memory (`Lower/PilotX64*.lean`; KNOWN_GAPS "x64 lowering pilot with a
stack"): such a program needs the guarded (value-restricted) purity copy,
not provided here. Both kits apply only to programs whose shared accesses all
stay within `S` under the unrestricted environment.

Phase-1 limits apply (`Phase1TreeFX`: single-access trees, read-side acquire
only, `lock cmpxchg` admitted; a release RMW cannot forward what it claims).
-/
import Kraken.Promising.SLR.EnvG.ValsX64
import Kraken.EnvCfgAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64 Kraken.Promising.X64.EnvG

namespace Kraken.Promising.Lower.KitX

/-! ## Per-thread contracts -/

/-- **What a lowered x64 thread provides, in both variants**, on the shared
layout `S`: the image `e` (validly laid out), plan `pl`, `Phase1TreeFX`, the
entry and end addresses, no step at the end in any environment, the counted
post `Q` (only at the end, `Q_end`) read as the shared postcondition `B`
(`hB`), and the all-release judgment `pure` from the entry in counted
`(relPureQ Arch.tso ⊥).within S` to `QR` (only at the end). -/
structure LowerCoreX (tid : Nat) (S : SharedEnv.Layout) (B : Config isa → Res → Ghost → Prop) where
  e : Kraken.Executable Directive
  valid : Kraken.Executable.ValidLayout e
  pl : Plan
  hpl : pl.Valid
  shape : Phase1TreeFX e
  entry : Int64
  endPc : Int64
  stuck : ∀ (env : SharedEnv) x R, x.1.2 = endPc → ¬ e.instrStepEnv env x R
  Q : MachineState × (EStateX × Nat) → Prop
  Q_end : ∀ y, Q y → y.1.2 = endPc
  hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    (∃ n, Q (t.st.st, (σ, n))) → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g
  PreR : MachineData → (SharedEnv.counted ((SharedEnv.relPureQ Arch.tso fun _ _ => False).within S)).State → Prop
  QR : MachineState × (Unit × Nat) → Prop
  QR_end : ∀ y, QR y → y.1.2 = endPc
  pure : ∀ s g, PreR s g →
    Safely (e.instrStepEnv (SharedEnv.counted ((SharedEnv.relPureQ Arch.tso fun _ _ => False).within S))) QR
      ((s, entry), g)

/-- The thread's (uncounted) postcondition. -/
def LowerCoreX.post {tid : Nat} {S : SharedEnv.Layout} {B : Config isa → Res → Ghost → Prop}
    (T : LowerCoreX tid S B) : MachineState × EStateX → Prop :=
  fun y => ∃ n, T.Q (y.1, (y.2, n))

theorem LowerCoreX.post_end {tid : Nat} {S : SharedEnv.Layout} {B : Config isa → Res → Ghost → Prop}
    (T : LowerCoreX tid S B) : ∀ y, T.post y → y.1.2 = T.endPc :=
  fun _ ⟨_, h⟩ => T.Q_end _ h

/-- **A frameless lowered x64 thread**: `LowerCoreX` and `main` from the
entry in counted `EnvGCAdjX Arch.tso tid pl S` to `Q`. -/
structure LowerThreadX (tid : Nat) (S : SharedEnv.Layout) (B : Config isa → Res → Ghost → Prop)
    extends LowerCoreX tid S B where
  Pre : MachineData → (SharedEnv.counted (EnvGCAdjX Arch.tso tid pl S)).State → Prop
  main : ∀ s g, Pre s g → Safely (e.instrStepEnv (SharedEnv.counted (EnvGCAdjX Arch.tso tid pl S))) Q ((s, entry), g)

/-- **A thread's start state**: `T`'s image, no declarations, at its entry
with its end, the shared layout off `dmem`, the purity precondition. -/
structure LowerCoreX.StartC {tid : Nat} {S : SharedEnv.Layout} {B : Config isa → Res → Ghost → Prop}
    (T : LowerCoreX tid S B) (s : isa.State) : Prop where
  exe : s.exe = T.e
  decls : s.decls = {}
  endPc : s.endPc = T.endPc
  pc : s.st.2 = T.entry
  split : Split S s.st.1.dmem
  preR : ∃ n, T.PreR s.st.1 ((), n)

/-- `LowerCoreX.StartC` and `Pre` at `σ`. -/
structure LowerThreadX.Start {tid : Nat} {S : SharedEnv.Layout} {B : Config isa → Res → Ghost → Prop}
    (T : LowerThreadX tid S B) (σ : EStateX) (s : isa.State) : Prop extends T.StartC s where
  pre : ∃ n, T.Pre s.st.1 (σ, n)

/-! ## The frameless kit -/

/-- An empty executable: validly laid out (fills out-of-range thread ids). -/
def emptyExe : Kraken.Executable Directive := (0, [])

instance emptyExe_valid : Kraken.Executable.ValidLayout emptyExe where
  label_size _ _ _ h := by simp [emptyExe] at h
  instr_size _ _ _ h := by simp [emptyExe] at h
  no_wrap := by simp [emptyExe]
  align_addr _ _ _ _ _ _ h := by simp [emptyExe] at h

/-- The all-release specification of a lowered thread. -/
def LowerCoreX.pureSpec {tid : Nat} {S : SharedEnv.Layout} {B : Config isa → Res → Ghost → Prop}
    (hS : Le16 S) (T : LowerCoreX tid S B) : RelPureSpecQX Arch.tso fun _ _ => False where
  S := S
  le16 := hS
  e := T.e
  valid := T.valid
  endPc := T.endPc
  post y := ∃ n, T.QR (y.1, (y.2, n))
  post_end _ h := h.elim fun _ h => T.QR_end _ h

/-- The all-release specifications of a family of threads (`emptyExe`
beyond `k`). -/
def pureSpecs {S : SharedEnv.Layout} {B : Config isa → Res → Ghost → Prop} (hS : Le16 S) {k : Nat}
    (T : ∀ tid, tid < k → LowerCoreX tid S B) (tid : Nat) : RelPureSpecQX Arch.tso fun _ _ => False :=
  if h : tid < k then (T tid h).pureSpec hS
  else ⟨S, hS, emptyExe, inferInstance, 0, fun _ => False, fun _ h => h.elim⟩

theorem LowerCoreX.pureSpec_holds {tid : Nat} {S : SharedEnv.Layout} {B : Config isa → Res → Ghost → Prop}
    (hS : Le16 S) (T : LowerCoreX tid S B) {s : isa.State} (h : T.StartC s) : (T.pureSpec hS).Holds s := by
  obtain ⟨he, hds, hend, hpc, hsp, n, hR⟩ := h
  refine ⟨he, hend, hds, hsp, ?_⟩
  rw [show s.st = (s.st.1, T.entry) from Prod.ext rfl hpc]
  exact Safely.uncountEnv (T.pure _ ((), n) hR)

theorem pureSpecs_holds {S : SharedEnv.Layout} {B : Config isa → Res → Ghost → Prop} (hS : Le16 S)
    {states : List isa.State} (T : ∀ tid, tid < states.length → LowerCoreX tid S B)
    (hT : ∀ tid (h : tid < states.length), (T tid h).StartC states[tid]) :
    ∀ tid s, states[tid]? = some s → (pureSpecs hS T tid).Holds s := by
  intro tid s hs
  obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hs
  rw [show pureSpecs hS T tid = (T tid h).pureSpec hS from dite_eq_left_of_eq_true (eq_true h)]
  exact (T tid h).pureSpec_holds hS (hT tid h)

/-- **`QX64CAdj` of a frameless thread at its start.** -/
theorem LowerThreadX.qx64CAdj {tid : Nat} {S : SharedEnv.Layout} {B : Config isa → Res → Ghost → Prop}
    (T : LowerThreadX tid S B) {σ : EStateX} {s : isa.State} (h : T.Start σ s) :
    QX64CAdj Arch.tso tid T.pl S T.e T.endPc T.post s σ := by
  obtain ⟨⟨he, hds, hend, hpc, hsp, -⟩, n, hP⟩ := h
  refine ⟨he, hds, hend, hsp, ?_⟩
  rw [show s.st = (s.st.1, T.entry) from Prod.ext rfl hpc]
  exact Safely.uncountEnv (T.main _ (σ, n) hP)

/-- **The frameless x64 lowering kit**: x64 programs on one shared layout
`S` (`Le16 S`), each thread a `LowerThreadX` started at its `Start` (in
`σInitX` of the initial configuration, resource `rF tid`, ghost `g₀`); with
`Erase` of the initial configuration and no pending ghost mark, every final
configuration `c` reachable under `Arch.tso` satisfies `Φ` as soon as the
final reading `hfin` turns the done threads' shared postconditions into `Φ`.
`NTFree` and purity come from the threads' all-release judgments. -/
theorem lower_promising_x64 (fuel : Nat) {states : List isa.State} {initMem : List (Loc × Val)}
    {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop} {Φ : Config isa → Prop}
    {S : SharedEnv.Layout} (hS : Le16 S)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : g₀.pend = [])
    (T : ∀ tid, tid < states.length → LowerThreadX tid S B)
    (hT : ∀ tid (h : tid < states.length),
      (T tid h).Start (σInitX (Config.init states initMem) (rF tid) g₀) states[tid])
    {c : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c := by
  refine CmpxPublic.final_of_relPureSafelyQX_tsoF' hE (by simp [hpend])
    (pureSpecs hS fun tid h => (T tid h).toLowerCoreX) (pureSpecs_holds hS _ fun tid h => (hT tid h).toStartC)
    ?_ hc hf hfin
  intro tid h n m
  let Tt := T tid h
  letI := Tt.valid
  exact npSafeF_of_safelyEnvGFCAdjX Tt.hpl hS Tt.shape Tt.post_end (Tt.stuck _) Tt.hB n m
    (invGFCAdjX_init (List.getElem?_eq_getElem h) hpend (Tt.qx64CAdj (hT tid h)))

/-- **A whole-text partial triple in the kit's form**: from the start of `p`
(`(layout p).addrOf 0`), a `PartialTripleEnv` with no exceptional exit gives
the `Safely` judgment to the end of the text with the triple's post. -/
theorem safely_of_partialTripleEnvX [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {env : SharedEnv} {P Q : MachineData → env.State → Prop}
    (ht : MachineWP.PartialTripleEnv env P p Q fun _ _ _ => False) (henv : cenv = layout p) :
    ∀ s g, P s g → Safely ((layout p).instrStepEnv env)
      (fun x => (x.1.2 = (layout p).addrOf p.length ∧ Q x.1.1 x.2) ∨ False) ((s, (layout p).addrOf 0), g) := by
  intro s g hP
  rw [Executable.addrOf_zero, Layout.apply_fst]
  exact Program.instrStepEnv_of_partialTripleEnv ht hP henv

/-! ## The thread rule and its no-fault rule -/

/-- **A frameless lowered x64 thread's rule**
(`ThreadRuleRXF.ofSafelyEnvGFCAdjX`). -/
noncomputable def LowerThreadX.rule {tid : Nat} {S : SharedEnv.Layout} {B : Config isa → Res → Ghost → Prop}
    (hS : Le16 S) (T : LowerThreadX tid S B) : ThreadRuleRXF (I := isa) Arch.tso B tid :=
  letI := T.valid
  ThreadRuleRXF.ofSafelyEnvGFCAdjX (S := S) (post := T.post) T.hpl hS T.shape T.post_end (T.stuck _) T.hB

/-- **The rule's invariant at the initial configuration** from the thread's
`Start`. -/
theorem LowerThreadX.rule_init {tid : Nat} {S : SharedEnv.Layout} {B : Config isa → Res → Ghost → Prop}
    (hS : Le16 S) (T : LowerThreadX tid S B) {ss : List isa.State} {m : List (Loc × Val)} {s : isa.State}
    (hs : ss[tid]? = some s) {r : Res} {g : Ghost} (hpend : g.pend = [])
    (h : T.Start (σInitX (Config.init ss m) r g) s) : (T.rule hS).Inv True (Config.init ss m) r g :=
  invGFCAdjX_init hs hpend (T.qx64CAdj h)

/-- **The rule excludes faults** for fault-free code. -/
theorem LowerThreadX.rule_noFault {tid : Nat} {S : SharedEnv.Layout} {B : Config isa → Res → Ghost → Prop}
    (hS : Le16 S) (T : LowerThreadX tid S B) (hnf : DirsNoFault T.e) : NoFaultRuleF (T.rule hS) :=
  letI := T.valid
  noFaultRuleF_ofSafelyEnvGFCAdjX_struct _ _ _ _ _ _ hnf

/-! ## The frame + value-bridge kit

**Scope.** The value bridge `Vals.envGValsBridgeX_ofSpecs` takes the
*unrestricted* purity specifications (`RelPureSpecQX.Holds`, judgments in
`(relPureQ Arch.tso ⊥).within S`: the kit's `pure`), not value-restricted
ones. They are false for a program whose shared accesses leave `S` under the
unrestricted environment, e.g. one loading through a pointer read from shared
memory (the x64 pilot's pop, `Lower/PilotX64*.lean`; KNOWN_GAPS "x64 lowering pilot
with a stack"); such a program needs the guarded purity copy (not here). The
variant applies to programs whose shared accesses all stay within `S`. -/

/-- **A lowered x64 thread with a `dmem` frame**: `LowerCoreX`, `main` from
the entry in the value-restricted counted `EnvGCAdjXV Arch.tso tid pl S G`
(load answers satisfy `G`), and the value judgment `vals` in counted
`inv S G` (every shared write satisfies `G`, every access is an
`S`-access) to `QV` (only at the end). Its purity judgment `pure` is the
unrestricted one (see the section docstring). -/
structure LowerThreadXV (tid : Nat) (S : SharedEnv.Layout) (B : Config isa → Res → Ghost → Prop)
    (G : Loc → Val → Prop) extends LowerCoreX tid S B where
  Pre : MachineData → (SharedEnv.counted (Vals.EnvGCAdjXV Arch.tso tid pl S G)).State → Prop
  main : ∀ s g, Pre s g →
    Safely (e.instrStepEnv (SharedEnv.counted (Vals.EnvGCAdjXV Arch.tso tid pl S G))) Q ((s, entry), g)
  PreV : MachineData → (SharedEnv.counted (SharedEnv.inv S G)).State → Prop
  QV : MachineState × (Unit × Nat) → Prop
  QV_end : ∀ y, QV y → y.1.2 = endPc
  vals : ∀ s g, PreV s g → Safely (e.instrStepEnv (SharedEnv.counted (SharedEnv.inv S G))) QV ((s, entry), g)

/-- `LowerCoreX.StartC`, `Pre` at `σ` and `PreV`. -/
structure LowerThreadXV.Start {tid : Nat} {S : SharedEnv.Layout} {B : Config isa → Res → Ghost → Prop}
    {G : Loc → Val → Prop} (T : LowerThreadXV tid S B G) (σ : EStateX) (s : isa.State) : Prop
    extends T.StartC s where
  pre : ∃ n, T.Pre s.st.1 (σ, n)
  preV : ∃ n, T.PreV s.st.1 ((), n)

/-- The value specification of a lowered thread. -/
def LowerThreadXV.valSpec {tid : Nat} {S : SharedEnv.Layout} {B : Config isa → Res → Ghost → Prop}
    {G : Loc → Val → Prop} (T : LowerThreadXV tid S B G) : ThreadSpec S G :=
  @ThreadSpec.ofSafely S G T.e T.valid T.endPc (fun y => ∃ n, T.QV (y.1, (y.2, n)))
    (fun _ h => h.elim fun _ h => T.QV_end _ h)

/-- The value specifications of a family of threads (`emptyExe` beyond `k`). -/
def valSpecs {S : SharedEnv.Layout} {B : Config isa → Res → Ghost → Prop} {G : Loc → Val → Prop} {k : Nat}
    (T : ∀ tid, tid < k → LowerThreadXV tid S B G) (tid : Nat) : ThreadSpec S G :=
  if h : tid < k then (T tid h).valSpec
  else ⟨emptyExe, inferInstance, 0, fun _ => False, fun _ => False, fun _ h => h.elim, fun _ h => h.elim⟩

theorem LowerThreadXV.valSpec_holds {tid : Nat} {S : SharedEnv.Layout} {B : Config isa → Res → Ghost → Prop}
    {G : Loc → Val → Prop} (T : LowerThreadXV tid S B G) {σ : EStateX} {s : isa.State} (h : T.Start σ s) :
    T.valSpec.Holds s := by
  obtain ⟨⟨he, hds, hend, hpc, hsp, -⟩, -, n, hV⟩ := h
  refine ⟨he, hend, hds, hsp, ?_⟩
  show Safely _ _ (s.st, ())
  rw [show s.st = (s.st.1, T.entry) from Prod.ext rfl hpc]
  exact Safely.uncountEnv (T.vals _ ((), n) hV)

/-- **`QX64CAdjV` of a framed thread at its start.** -/
theorem LowerThreadXV.qx64CAdjV {tid : Nat} {S : SharedEnv.Layout} {B : Config isa → Res → Ghost → Prop}
    {G : Loc → Val → Prop} (T : LowerThreadXV tid S B G) {σ : EStateX} {s : isa.State} (h : T.Start σ s) :
    Vals.QX64CAdjV Arch.tso tid T.pl S G T.e T.endPc T.post s σ := by
  obtain ⟨⟨he, hds, hend, hpc, hsp, -⟩, ⟨n, hP⟩, -⟩ := h
  refine ⟨he, hds, hend, hsp, ?_⟩
  rw [show s.st = (s.st.1, T.entry) from Prod.ext rfl hpc]
  exact Safely.uncountEnv (T.main _ (σ, n) hP)

/-- **The frame + value-bridge x64 lowering kit**: `lower_promising_x64` for
threads in the value-restricted env (`LowerThreadXV`), given in addition
`MemInv G` of the initial memory; the value bridge is
`Vals.envGValsBridgeX_ofSpecs`, fed by the threads' value judgments. Same
conclusion. **Only for programs whose shared accesses all stay within `S`
under the unrestricted purity environment**: the purity side is the
unrestricted `RelPureSpecQX.Holds`, false e.g. for programs loading through
shared pointers outside `S` (the x64 pilot); see the section docstring. -/
theorem lower_promising_x64_vals (fuel : Nat) {states : List isa.State} {initMem : List (Loc × Val)}
    {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop} {Φ : Config isa → Prop}
    {S : SharedEnv.Layout} (hS : Le16 S) (G : Loc → Val → Prop)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : g₀.pend = [])
    (hm0 : MemInv G (Config.init states initMem).mem)
    (T : ∀ tid, tid < states.length → LowerThreadXV tid S B G)
    (hT : ∀ tid (h : tid < states.length),
      (T tid h).Start (σInitX (Config.init states initMem) (rF tid) g₀) states[tid])
    {c : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c := by
  classical
  let pl : Nat → Plan := fun tid => if h : tid < states.length then (T tid h).pl else ⟨[]⟩
  let e : Nat → Kraken.Executable Directive := fun tid =>
    if h : tid < states.length then (T tid h).e else emptyExe
  let endPc : Nat → Int64 := fun tid => if h : tid < states.length then (T tid h).endPc else 0
  let post : Nat → MachineState × EStateX → Prop := fun tid =>
    if h : tid < states.length then (T tid h).post else fun _ => False
  refine Vals.envGValsBridgeX_ofSpecs (pl := pl) (e := e) (endPc := endPc) (post := post) hS G (valSpecs T) hE
    (by simp [hpend]) (pureSpecs hS fun tid h => (T tid h).toLowerCoreX)
    (pureSpecs_holds hS _ fun tid h => (hT tid h).toStartC) hm0 ?_ ?_ hc hf hfin
  · intro tid t ht
    simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hs
    rw [show valSpecs T tid = (T tid h).valSpec from dite_eq_left_of_eq_true (eq_true h)]
    exact (T tid h).valSpec_holds (hT tid h)
  · intro tid h
    have hpl : pl tid = (T tid h).pl := dite_eq_left_of_eq_true (eq_true h)
    have he : e tid = (T tid h).e := dite_eq_left_of_eq_true (eq_true h)
    have hend : endPc tid = (T tid h).endPc := dite_eq_left_of_eq_true (eq_true h)
    have hpost : post tid = (T tid h).post := dite_eq_left_of_eq_true (eq_true h)
    rw [hpl, he, hend, hpost]
    let Tt := T tid h
    exact ⟨Tt.valid, Tt.hpl, Tt.shape, Tt.post_end, Tt.stuck _, Tt.hB, states[tid],
      List.getElem?_eq_getElem h, Tt.qx64CAdjV (hT tid h)⟩

end Kraken.Promising.Lower.KitX

#print axioms Kraken.Promising.Lower.KitX.lower_promising_x64
#print axioms Kraken.Promising.Lower.KitX.lower_promising_x64_vals
#print axioms Kraken.Promising.Lower.KitX.LowerThreadX.rule_noFault
#print axioms Kraken.Promising.Lower.KitX.LowerThreadX.rule_init
#print axioms Kraken.Promising.Lower.KitX.safely_of_partialTripleEnvX
