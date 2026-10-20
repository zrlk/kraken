/-
**Dekker with `mfence` on x64, proved on
`EnvG`** (the shape of
`EnvG/X64MpPublic.lean`).

`Kraken/Examples/LockFree/X64/dekker_mfence.kl`'s property
`~exists (0:edx=1 /\ 1:edx=1 /\ [counter]=1)` for the two-thread program
whose threads both run `worker` (`EnvG/DekkerVCGenX.lean`; the counter
addressed through `%rbx`), thread `0` with own flag `F0`, thread `1` with own
flag `F1`.

- **Initial ghost and resources**: nothing is released or acquired
  (`dkGhost`, every release predicate `Pred.emp`); thread `j` holds all of its
  flag and half of the counter at their initial messages (`dkRes`);
  `erase_dkInit` by `erase_initGhost`.
- **`NPSafe`**: `dkRule` (`EnvG/DekkerLinkX.lean`) per thread, its invariant
  at the start from `worker_envG`.
- **Scope and purity**: `worker_noNT` (`EnvG/DekkerRelPureX.lean`).
- **Final argument** (`dk_final`): both threads with `edx = 1` give two
  `DkEnd`s, for different flags (one holder of each flag:
  `Erase.q_add_le_one`), hence the histories (`flagHist_of_erase`,
  `cntHist_of_erase`) and `dekker_final`: the counter ends at `2`.
-/
import Kraken.Promising.SLR.EnvG.DekkerLinkX
import Kraken.Promising.SLR.EnvG.DekkerRelPureX
import Kraken.Promising.SLR.InitGhost
import Kraken.Promising.SLR.SpinInitRes

namespace Kraken.Promising.X64.EnvG.Dekker

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvG.Dekker
open Kraken.Promising.X64.EnvG

/-! ## The initial ghost and resources -/

/-- **Dekker's initial ghost**: nothing released, no acquire predicate. -/
abbrev dkGhost : Ghost := initGhost (fun _ => Pred.emp) [] []

theorem pend_dkGhost : ∀ ts, ts ∉ dkGhost.pend := initGhost_pend

/-- A thread's initial fractions: all of its flag `F`, half of the counter `C`. -/
def dkFrac (F C : Loc) (x : Loc) : Rat := if x = F then 1 else if x = C then 1 / 2 else 0

theorem dkFrac_nonneg (F C : Loc) (x : Loc) : 0 ≤ dkFrac F C x := by
  unfold dkFrac; split
  · decide
  · split
    · decide +kernel
    · decide

/-- The initial thread resources: thread `0` owns `F0`, thread `1` owns `F1`. -/
def dkRes (m : Memory) (F0 F1 C : Loc) (i : Nat) : Res :=
  if i = 0 then Res.initOf m (dkFrac F0 C) (dkFrac_nonneg F0 C)
  else if i = 1 then Res.initOf m (dkFrac F1 C) (dkFrac_nonneg F1 C) else Res.unit

section Init

variable {s0 s1 : isa.State} {initMem : List (Loc × Val)}

theorem total_dkInit (m : Memory) (F0 F1 C : Loc) :
    total (dkRes m F0 F1 C) dkGhost (Config.init [s0, s1] initMem) =
      (Res.initOf m (dkFrac F0 C) (dkFrac_nonneg F0 C)).op (Res.initOf m (dkFrac F1 C) (dkFrac_nonneg F1 C)) := by
  simp only [total, Config.init_size, threadsRes, Ghost.slotsRes, dkGhost, initGhost, List.map_nil, Res.prod_nil,
    Res.op_unit, List.length_cons, List.length_nil]
  show Res.prod [dkRes m F0 F1 C 0, dkRes m F0 F1 C 1] = _
  simp [dkRes, Res.op_unit]

/-- **Initial erasure of Dekker** (three distinct words). -/
theorem erase_dkInit {F0 F1 C : BitVec 64} (T : Nat → Prop) (hL : Locs F0 F1 C) :
    Erase (dkRes (Config.init [s0, s1] initMem).mem ⟨F0, 4⟩ ⟨F1, 4⟩ ⟨C, 4⟩) dkGhost T
      (Config.init [s0, s1] initMem) := by
  have ht := total_dkInit (s0 := s0) (s1 := s1) (initMem := initMem) (Config.init [s0, s1] initMem).mem
    ⟨F0, 4⟩ ⟨F1, 4⟩ ⟨C, 4⟩
  have hI : (total (dkRes (Config.init [s0, s1] initMem).mem ⟨F0, 4⟩ ⟨F1, 4⟩ ⟨C, 4⟩) dkGhost
      (Config.init [s0, s1] initMem)).IsInit (Config.init [s0, s1] initMem).mem := by
    rw [ht]; exact (Res.IsInit.initOf _ _).op (Res.IsInit.initOf _ _)
  refine erase_initGhost T List.nodup_nil ⟨fun x => ?_, fun x ι => by rw [hI.2]; decide⟩
    (fun x ι h => by rw [hI.2] at h; exact absurd h (by decide)) (fun x v m V r h => h)
    (fun x hpos p => by rw [hI.1 x p]; exact ⟨fun h => h.2, fun h => ⟨hpos, h⟩⟩)
    (fun x _ => Pred.emp_pure _) (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
  rw [ht]
  show dkFrac ⟨F0, 4⟩ ⟨C, 4⟩ x + dkFrac ⟨F1, 4⟩ ⟨C, 4⟩ x ≤ 1
  unfold dkFrac
  by_cases h0 : x = ⟨F0, 4⟩
  · subst h0
    simp only [↓reduceIte, hL.fo, hL.fc]
    decide +kernel
  · by_cases h1 : x = ⟨F1, 4⟩
    · subst h1
      simp only [↓reduceIte, h0, hL.oc]
      decide +kernel
    · by_cases hc : x = ⟨C, 4⟩
      · subst hc
        simp only [↓reduceIte, h0, h1]
        decide +kernel
      · simp only [h0, h1, hc, ↓reduceIte]
        decide +kernel

end Init

/-! ## The start -/

section Start

/-- A worker at its start in the layout `lay`, own flag `f`, other flag `o`,
counter `c` (the layout explicit: both threads run `worker`). -/
structure StartD (lay : _root_.Layout) (f o c : BitVec 64) (s : State) : Prop where
  exe : s.exe = lay worker
  decls : s.decls = {}
  endPc : s.endPc = (lay worker).addrOf worker.length
  pc : s.st.2 = (lay worker).addrOf 0
  rsi : s.st.1.regs.get64 .rsi = f
  rdi : s.st.1.regs.get64 .rdi = o
  rbx : s.st.1.regs.get64 .rbx = c
  split : Split (dkS f o c) s.st.1.dmem

theorem frame_of_split {f o c : BitVec 64} {s : MachineData} (h0 : s.regs.get64 .rsi = f)
    (h1 : s.regs.get64 .rdi = o) (h2 : s.regs.get64 .rbx = c) (h : Split (dkS f o c) s.dmem) : Frame f o c s :=
  ⟨h0, h1, h2, h.loadInt_none (by simp) (by decide) (by decide), h.loadInt_none (by simp) (by decide) (by decide),
    h.loadInt_none (by simp) (by decide) (by decide)⟩

/-- `D0` at a thread's start: its initial resource (all of `f`, half of
`c`, initial values `0`). -/
theorem d0_init {f o c : BitVec 64} (hL : Locs f o c) {cfg : Config isa} {g : Ghost}
    (hrel : ∀ x, g.rel x = Pred.emp) (hf0 : cfg.mem.initVal ⟨f, 4⟩ = 0) (hc0 : cfg.mem.initVal ⟨c, 4⟩ = 0) :
    D0 f o c (σInitX cfg (Res.initOf cfg.mem (dkFrac ⟨f, 4⟩ ⟨c, 4⟩) (dkFrac_nonneg _ _)) g) := by
  refine ⟨⟨fun x v => by show Pred.Pure (g.rel x) v; rw [hrel]; exact Pred.emp_pure v, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · show dkFrac _ _ _ = 1; simp [dkFrac]
  · rintro p ⟨-, rfl⟩; exact ⟨rfl, hf0⟩
  · show dkFrac _ _ _ = 1 / 2; simp [dkFrac, Ne.symm hL.fc]
  · rintro p ⟨-, rfl⟩; exact ⟨rfl, hc0⟩
  · simp [σInitX, Views.getFwd]
  · simp [σInitX, Views.getFwd]

variable [layout : _root_.Layout]

/-- **A worker's initial invariant**. -/
theorem invD_init [Executable.ValidLayout (layout worker)] (tid : Nat) {f o c : BitVec 64} (hL : Locs f o c)
    {B : Config isa → Res → Ghost → Prop} (hB : ∀ cfg r g, DkThreadEnd tid f o c cfg r → B cfg r g)
    {ss : List isa.State} {initMem : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    (hS : StartD layout f o c s) (hf0 : (Config.init ss initMem).mem.initVal ⟨f, 4⟩ = 0)
    (hc0 : (Config.init ss initMem).mem.initVal ⟨c, 4⟩ = 0) :
    (dkRule tid f o c hB).Inv True (Config.init ss initMem)
      (Res.initOf (Config.init ss initMem).mem (dkFrac ⟨f, 4⟩ ⟨c, 4⟩) (dkFrac_nonneg _ _)) dkGhost := by
  letI : CodeEnv := ⟨layout worker⟩
  exact invGX_init (s := s) hs rfl (qx64_of_partialTripleEnv (worker_envG tid f o c hL).uncount rfl hS.exe
    hS.decls hS.endPc hS.pc hS.split
    ⟨0, frame_of_split hS.rsi hS.rdi hS.rbx hS.split, d0_init hL (fun _ => rfl) hf0 hc0⟩)

end Start

/-! ## `NPSafe` -/

/-- **The `NPSafe` side of Theorem 1′ for x64 Dekker on `EnvG`.** -/
theorem x64_dekker_npSafe (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 worker)]
    [Executable.ValidLayout (l1 worker)] {F0 F1 C : BitVec 64} (hL : Locs F0 F1 C) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : StartD l0 F0 F1 C s0) (h1 : StartD l1 F1 F0 C s1)
    (hF0 : (Config.init [s0, s1] initMem).mem.initVal ⟨F0, 4⟩ = 0)
    (hF1 : (Config.init [s0, s1] initMem).mem.initVal ⟨F1, 4⟩ = 0)
    (hC : (Config.init [s0, s1] initMem).mem.initVal ⟨C, 4⟩ = 0) :
    ∀ tid, tid < [s0, s1].length → ∀ n m, NPSafe (model isa) Arch.tso (DkB F0 F1 C) tid n m True
      (Config.init [s0, s1] initMem) (dkRes (Config.init [s0, s1] initMem).mem ⟨F0, 4⟩ ⟨F1, 4⟩ ⟨C, 4⟩ tid)
      dkGhost := by
  intro tid htid n m
  rcases tid with _ | _ | k
  · exact NPSafe.of_ruleRX _ n m _ _ _ _
      (invD_init (layout := l0) 0 hL (fun _ _ _ h => .inl h) rfl h0 hF0 hC)
  · exact NPSafe.of_ruleRX _ n m _ _ _ _
      (invD_init (layout := l1) 1 ⟨Ne.symm hL.fo, hL.oc, hL.fc⟩ (fun _ _ _ h => .inr h) rfl h1 hF1 hC)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-! ## Scope and purity -/

/-- Dekker's all-release specifications: thread `0` (layout `l0`, own flag
`F0`), thread `1` (layout `l1`, own flag `F1`). -/
def dkNoNTSpec (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 worker)]
    [Executable.ValidLayout (l1 worker)] (F0 F1 C : BitVec 64) : Nat → RelPureSpecQX Arch.tso fun _ _ => False
  | 0 => RelPureSpecQX.ofProgram (layout := l0) (dkS F0 F1 C) (dkS_le16 _ _ _) worker fun _ _ => ∃ _ : Nat, True
  | _ + 1 => RelPureSpecQX.ofProgram (layout := l1) (dkS F1 F0 C) (dkS_le16 _ _ _) worker fun _ _ => ∃ _ : Nat, True

/-- **The all-release specifications hold at the start states.** -/
theorem dkNoNTSpec_init (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 worker)]
    [Executable.ValidLayout (l1 worker)] {F0 F1 C : BitVec 64} {s0 s1 : isa.State}
    (h0 : StartD l0 F0 F1 C s0) (h1 : StartD l1 F1 F0 C s1) :
    ∀ tid s, [s0, s1][tid]? = some s → (dkNoNTSpec l0 l1 F0 F1 C tid).Holds s
  | 0, s, hs => by
    cases hs
    letI : CodeEnv := ⟨l0 worker⟩
    exact RelPureSpecQX.holds_of_partialTripleEnv (layout := l0) (worker_noNT (layout := l0) F0 F1 C).uncount rfl
      h0.exe h0.decls h0.endPc h0.pc h0.split ⟨0, frame_of_split h0.rsi h0.rdi h0.rbx h0.split⟩
  | 1, s, hs => by
    cases hs
    letI : CodeEnv := ⟨l1 worker⟩
    exact RelPureSpecQX.holds_of_partialTripleEnv (layout := l1) (worker_noNT (layout := l1) F1 F0 C).uncount rfl
      h1.exe h1.decls h1.endPc h1.pc h1.split ⟨0, frame_of_split h1.rsi h1.rdi h1.rbx h1.split⟩
  | _ + 2, _, hs => by cases hs

/-! ## The final argument -/

section Final

variable {c : Config isa} {rF : Nat → Res} {g : Ghost} {F0 F1 C : BitVec 64}

/-- The counter's history is symmetric in the two increments. -/
theorem CntHist.swap {m : Memory} {L : Loc} {w0 w1 : Val × Time} (h : CntHist m L w0 w1) : CntHist m L w1 w0 :=
  fun ts v hr => by rcases h ts v hr with h | h | h <;> simp_all

/-- **Two end facts for the two flags**, held by the resources of threads
`a` and `b` (`{a, b} = {0, 1}`), give the counter's final value `≠ 1`. -/
theorem final_of_ends (hL : Locs F0 F1 C) (E : Erase rF g (fun _ => False) c) (hf : c.final = true)
    (hsize : c.threads.size = 2) {a b : Nat} (hab : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0))
    (e0 : DkEnd 0 F0 F1 C c (rF a)) (e1 : DkEnd 1 F1 F0 C c (rF b)) : c.mem.finalVal ⟨C, 4⟩ ≠ 1 := by
  obtain ⟨t0, r0, trc0, a0, tc0, u0, en0, q0, x0, qc0, xc0⟩ := e0
  obtain ⟨t1, r1, trc1, a1, tc1, u1, en1, q1, x1, qc1, xc1⟩ := e1
  have ha : a < c.threads.size := by rw [hsize]; omega
  have hb : b < c.threads.size := by rw [hsize]; omega
  have hF0 := flagHist_of_erase E hf ha q0 (t := t0) (u := some u0) x0
  have hF1 := flagHist_of_erase E hf hb q1 (t := t1) (u := some u1) x1
  have hC : CntHist c.mem ⟨C, 4⟩ (inc a0, tc0) (inc a1, tc1) := by
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact cntHist_of_erase E hf hsize qc0 qc1 xc0 xc1
    · exact CntHist.swap (cntHist_of_erase E hf hsize qc1 qc0 xc1 xc0)
  exact dekker_final hL.fo en0 en1 hF0 hF1 hC

/-- **Dekker's final argument**: at a final configuration of the two
threads, both with `edx = 1`, the counter's final value is not `1`. -/
theorem dk_final (hL : Locs F0 F1 C) (E : Erase rF g (fun _ => False) c) (hf : c.final = true)
    (hsize : c.threads.size = 2) (hB : ∀ tid, c.Done tid → DkB F0 F1 C c (rF tid) g)
    (h0 : ∃ t, c.threads[0]? = some t ∧ (t.st.st.1.regs.get64 .rdx).setWidth 32 = 1)
    (h1 : ∃ t, c.threads[1]? = some t ∧ (t.st.st.1.regs.get64 .rdx).setWidth 32 = 1) :
    c.mem.finalVal ⟨C, 4⟩ ≠ 1 := by
  have i0 : (0 : Nat) < c.threads.size := by rw [hsize]; decide
  have i1 : (1 : Nat) < c.threads.size := by rw [hsize]; decide
  obtain ⟨t0, ht0, he0⟩ := h0
  obtain ⟨t1, ht1, he1⟩ := h1
  have hq := E.q_add_le_one i0 i1 (by decide)
  rcases hB 0 (Config.final_done hf i0) with h00 | h01 <;>
    rcases hB 1 (Config.final_done hf i1) with h10 | h11
  · -- both hold `F0`
    obtain ⟨-, -, -, -, -, -, -, q0, -⟩ := h00 t0 ht0 he0
    obtain ⟨-, -, -, -, -, -, -, q1, -⟩ := h10 t0 ht0 he0
    have := hq ⟨F0, 4⟩
    rw [q0, q1] at this
    exact absurd this (by decide +kernel)
  · exact final_of_ends hL E hf hsize (.inl ⟨rfl, rfl⟩) (h00 t0 ht0 he0) (h11 t1 ht1 he1)
  · exact final_of_ends hL E hf hsize (.inr ⟨rfl, rfl⟩) (h10 t0 ht0 he0) (h01 t1 ht1 he1)
  · -- both hold `F1`
    obtain ⟨-, -, -, -, -, -, -, q0, -⟩ := h01 t1 ht1 he1
    obtain ⟨-, -, -, -, -, -, -, q1, -⟩ := h11 t1 ht1 he1
    have := hq ⟨F1, 4⟩
    rw [q0, q1] at this
    exact absurd this (by decide +kernel)

end Final

/-! ## The theorem -/

/-- **Dekker with `mfence` for x64 under `Arch.tso`, proved on `EnvG`**
(`dekker_mfence.kl`: `~exists (0:edx=1 /\ 1:edx=1 /\ [counter]=1)`).

For valid layouts `l0`, `l1` of `worker` and three distinct words `F0`,
`F1`, `C` (`Locs`): if thread `0` runs `worker` with own flag `F0` and
thread `1` with own flag `F1` (each at its start with `rsi` its flag, `rdi`
the other flag, `rbx` the counter, none of the words in its private memory:
`StartD`), and the three words are initially `0`, then no final
configuration `Reachable` under `Arch.tso` has both threads' `edx` at `1`
and the counter at `1`.

As for `x64_mp_public`: only final configurations are constrained; faults are
not covered (`dkRule_noFault` is the rule's no-fault fact). -/
theorem x64_dekker_public {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 worker)]
    [Executable.ValidLayout (l1 worker)] (F0 F1 C : BitVec 64) (hL : Locs F0 F1 C)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartD l0 F0 F1 C s0) (h1 : StartD l1 F1 F0 C s1)
    (hF0 : (Config.init [s0, s1] initMem).mem.initVal ⟨F0, 4⟩ = 0)
    (hF1 : (Config.init [s0, s1] initMem).mem.initVal ⟨F1, 4⟩ = 0)
    (hC : (Config.init [s0, s1] initMem).mem.initVal ⟨C, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) :
    ¬ ((∃ t, cfg.threads[0]? = some t ∧ (t.st.st.1.regs.get64 .rdx).setWidth 32 = 1) ∧
      (∃ t, cfg.threads[1]? = some t ∧ (t.st.st.1.regs.get64 .rdx).setWidth 32 = 1) ∧
      cfg.mem.finalVal ⟨C, 4⟩ = 1) :=
  final_of_relPureSafelyQX_tso fuel (B := DkB F0 F1 C)
    (Φ := fun c => ¬ ((∃ t, c.threads[0]? = some t ∧ (t.st.st.1.regs.get64 .rdx).setWidth 32 = 1) ∧
      (∃ t, c.threads[1]? = some t ∧ (t.st.st.1.regs.get64 .rdx).setWidth 32 = 1) ∧ c.mem.finalVal ⟨C, 4⟩ = 1))
    (erase_dkInit _ hL) pend_dkGhost (dkNoNTSpec l0 l1 F0 F1 C) (dkNoNTSpec_init l0 l1 h0 h1)
    (x64_dekker_npSafe l0 l1 hL h0 h1 hF0 hF1 hC) hc hf
    fun _ _ E' _ hsize hB ⟨e0, e1, hv⟩ => dk_final hL E' hf hsize hB e0 e1 hv

end Kraken.Promising.X64.EnvG.Dekker

#print axioms Kraken.Promising.X64.EnvG.Dekker.x64_dekker_public
#print axioms Kraken.Promising.X64.EnvG.Dekker.dkRule_noFault
